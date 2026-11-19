//! Random simulation: TLC's `-simulate` mode. Instead of enumerating every reachable state it generates
//! random behaviours of bounded length and checks each of them, which is how models too large to
//! enumerate are explored.
//!
//! One behaviour is generated the way TLC's `SimulationWorker` does it: pick an initial state at random;
//! then repeatedly pick an action at random, compute all its successors, check every one of them
//! (invariants, action properties), drop those outside the state and action constraints, and move to one
//! of the remaining ones at random. An action without admissible successors is replaced by the next one
//! (in a random stride) until every action has been tried; if none has one the behaviour ends there. A
//! behaviour that ends without an error is checked against the temporal properties.
//!
//! One deliberate difference: TLC's simulator reports "Deadlock reached" whenever no action has an
//! admissible successor, also when successors exist and the CONSTRAINTs merely exclude them, which
//! makes it report deadlocks on models that exhaustive checking passes. Here a deadlock is a state
//! without any successor, as in exhaustive checking; a behaviour that runs into the constraints just ends.
//!
//! The random choices come from a small seeded generator (no operating-system randomness, so the
//! WebAssembly build behaves the same): a run is reproduced by passing the seed it printed. The numbers
//! differ from Java TLC's, whose generator is not reproduced.
use crate::ast::{Res, E};
use crate::checker::*;
use crate::cli::{exit_code, report, result_json_with, state_text, Reporter};
use crate::eval::*;
use crate::intern::*;
use crate::liveness::{check_postconditions, PreparedLiveness};
use crate::model::*;
use crate::modules::{def_level, Sym};
use crate::value::*;
use std::cell::RefCell;
use std::collections::HashMap;

/// The number of behaviours generated when no bound is given and the caller cannot be interrupted
/// (`-json`, the WebAssembly API). The plain command line runs until an error is found, as TLC does.
pub const DEFAULT_TRACES: u64 = 1000;
/// TLC's default for `-depth`.
pub const DEFAULT_DEPTH: u32 = 100;

#[derive(Clone)]
pub struct SimOptions {
    /// Number of behaviours to generate; `None`: until an error is found.
    pub num: Option<u64>,
    /// Maximal number of steps of a behaviour; `None`: unbounded (`-depth -1`).
    pub depth: Option<u32>,
    pub seed: i64,
    pub aril: i64,
    pub check_deadlock: bool,
    /// `file=PREFIX`: every behaviour is written to `PREFIX_0_<n>` as a TLA+ module.
    pub trace_file: Option<String>,
}

/// splitmix64: small, seedable and identical on every target.
pub struct Rng(u64);
impl Rng {
    pub fn new(seed: i64, aril: i64) -> Rng {
        let mut r = Rng((seed as u64) ^ (aril as u64).wrapping_mul(0xD6E8_FEB8_6659_FD93).rotate_left(29));
        r.next();
        r
    }
    pub fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    /// A number in `0..n` (`n > 0`).
    pub fn below(&mut self, n: usize) -> usize {
        ((self.next() as u128 * n as u128) >> 64) as usize
    }
}

/// A seed for a run that was not given one: derived from the clock, and small enough to survive a
/// round trip through a JSON number.
pub fn clock_seed(now_ms: f64) -> i64 {
    let mut r = Rng::new(now_ms.to_bits() as i64, 0);
    (r.next() >> 11) as i64
}

#[derive(Clone, Default)]
pub struct SimStats {
    /// States generated: the initial states plus every successor computed.
    pub generated: u64,
    /// Behaviours started.
    pub traces: u64,
    /// Running mean of the behaviour lengths and sum of squared differences (Welford's algorithm in
    /// integer arithmetic, as in TLC).
    pub mean: i64,
    pub m2: i64,
    /// Number of states of the longest behaviour.
    pub longest: u32,
}
impl SimStats {
    fn record(&mut self, len: i64) {
        let delta = len - self.mean;
        self.mean += delta / (self.traces.max(1) as i64);
        self.m2 += delta * (len - self.mean);
    }
    pub fn variance(&self) -> i64 {
        (self.m2 as f64 / (self.traces as f64 + 1.0) + 0.5).floor() as i64
    }
    pub fn sd(&self) -> i64 {
        ((self.m2 as f64 / (self.traces as f64 + 1.0)).sqrt() + 0.5).floor() as i64
    }
}

pub trait SimEvents {
    fn branches(&mut self, _n: usize) {}
    fn init_computed(&mut self, _generated: u64) {}
    fn init_done(&mut self, _usable: u64) {}
    fn progress(&mut self, _stats: &SimStats) {}
}
pub struct NoSimEvents;
impl SimEvents for NoSimEvents {}

pub struct SimOutcome {
    pub result: CheckResult,
    pub stats: SimStats,
    /// Whether TLC prints the simulation statistics after this result, ...
    pub summary: bool,
    /// ... and the closing progress line.
    pub final_progress: bool,
}

/// The label TLC's simulator prints for the first state of a trace: the initial predicate by name
/// with the location of its definition body.
pub fn init_label(model: &Model) -> String {
    let p = match model.inits.last() {
        Some(p) => p,
        None => return "<Initial predicate>".to_string(),
    };
    let root = &model.root_name;
    let mut at = (p.e.loc, p.e.module_str().unwrap_or_else(|| root.clone()));
    if let E::App { name: n, args, r, .. } = &p.e.e {
        if let (true, Res::Def(d)) = (args.is_empty() && n.to_string() == p.name, r.get()) {
            at = body_loc(Sym::Def(d));
        }
    }
    // an initial predicate written inside the specification formula has no name of its own
    let named = matches!(model.root.syms.get(name(&p.name)), Some(Sym::Def(d)) if def_level(d) <= 1);
    format!("<{} {}>", if named { p.name.as_str() } else { "Initial predicate" }, loc_str(&at.0, &at.1))
}

struct Sim<'a, 'o> {
    model: &'a Model,
    ck: Checker<'a>,
    ev: &'static Evaluator,
    opts: &'o SimOptions,
    rng: Rng,
    stats: SimStats,
    nvars: usize,
    /// the successor an action left incompletely specified (shown as the last state of the trace)
    partial: RefCell<Option<StateRef>>,
    live: Option<PreparedLiveness>,
}

/// Strides for trying the other actions when the chosen one has no successor.
const PRIMES: [usize; 24] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89];

fn same_state(a: &StateRef, b: &StateRef, n: usize) -> bool {
    (0..n).all(|i| !a.is_undef(i) && !b.is_undef(i) && matches!(val_eq(&a.get(i), &b.get(i)), Ok(true)))
}

impl<'a, 'o> Sim<'a, 'o> {
    fn result(&self, status: &'static str) -> CheckResult {
        self.fix(self.ck.result(status))
    }
    /// A result of the checker with the counters of this run.
    fn fix(&self, mut r: CheckResult) -> CheckResult {
        r.generated = self.stats.generated;
        r.distinct = 0;
        r.queue = 0;
        r.depth = self.stats.longest;
        r.init_generated = 0;
        r.init_distinct = 0;
        r.print_summary = false;
        r.outdegree = None;
        r
    }
    fn error(&self, message: String, trace: Option<Vec<TraceStep>>) -> CheckResult {
        self.fix(self.ck.error(message, trace))
    }
    fn outcome(&self, mut result: CheckResult, summary: bool, final_progress: bool) -> SimOutcome {
        let mut stats = self.stats.clone();
        // the behaviour that ends in the error counts towards the longest one
        stats.longest = stats.longest.max(result.trace.as_ref().map_or(0, |t| t.len().min(u32::MAX as usize) as u32));
        result.depth = stats.longest;
        SimOutcome { result, stats, summary, final_progress }
    }

    /// The behaviour as TLC reports it: finite stuttering (a step that changes nothing) is left out.
    fn compress(&self, trace: &[TraceStep], last: Option<(&StateRef, usize)>) -> Vec<TraceStep> {
        let mut out: Vec<TraceStep> = Vec::with_capacity(trace.len() + 1);
        let extra = last.map(|(s, a)| TraceStep { state: s.clone(), action: Some(a), id: 0 });
        for t in trace.iter().chain(extra.iter()) {
            if let Some(prev) = out.last() {
                if same_state(&prev.state, &t.state, self.nvars) {
                    continue;
                }
            }
            out.push(TraceStep { state: t.state.clone(), action: t.action, id: out.len() as i64 });
        }
        out
    }

    /// The successors of `s` by one action, in enumeration order.
    fn action_successors(&self, s: &StateRef, ai: usize, out: &mut Vec<StateRef>) -> R<()> {
        let ev = self.ev;
        let n = self.nvars;
        let actions = &self.model.actions;
        let a = &actions[ai];
        let nxt = StateData::blank(n);
        let nxt = &nxt;
        ev.set_state(s, Some(nxt));
        ev.init_mode.set(false);
        ev.prime_depth.set(0);
        ev.call_depth.set(0);
        ev.n_assigned.set(0);
        ev.enumerate(a.e, &a.ctx, &mut || {
            for k in 0..n {
                if nxt.is_undef(k) {
                    let missing = self.ck.missing(nxt);
                    *self.partial.borrow_mut() = Some(StateData::new(nxt.snapshot(n)));
                    let which = if actions.len() == 1 { "the next-state action".to_string() } else { format!("action {} of the next-state relation", a.name) };
                    return Err(Box::new(Fail::Check {
                        status: "incomplete",
                        message: format!(
                            "Successor state is not completely specified by {}. The following variable{} not defined: {}.",
                            which,
                            if missing.len() > 1 { "s are" } else { " is" },
                            missing.join(", ")
                        ),
                    }));
                }
            }
            out.push(StateData::new(nxt.snapshot(n)));
            Ok(())
        })
    }

    /// One step from the last state of `trace`: the chosen successor and its action, `None` when no
    /// action has an admissible successor and deadlock is not an error, or the error to report.
    fn step(&mut self, trace: &[TraceStep], succs: &mut Vec<StateRef>, keep: &mut Vec<StateRef>) -> Result<Option<(StateRef, usize)>, SimOutcome> {
        let m = self.model;
        let ev = self.ev;
        let s = trace[trace.len() - 1].state.clone();
        let lvl = trace.len() as i64;
        let n = m.actions.len();
        let mut index = self.rng.below(n);
        // a prime that does not divide the number of actions visits every action
        let mut pi = self.rng.below(PRIMES.len());
        let mut stride = 1;
        for _ in 0..PRIMES.len() {
            if n % PRIMES[pi] != 0 {
                stride = PRIMES[pi];
                break;
            }
            pi = (pi + 1) % PRIMES.len();
        }
        let mut has_successor = false;
        for _ in 0..n {
            succs.clear();
            keep.clear();
            ev.stats.level.set(lvl);
            self.partial.borrow_mut().take();
            if let Err(e) = self.action_successors(&s, index, succs) {
                self.stats.generated += ev.extra_generated.replace(0);
                return Err(match *e {
                    Fail::Check { status, message } => {
                        let mut r = self.result(status);
                        r.message = Some(message);
                        let partial = self.partial.borrow_mut().take();
                        r.trace = Some(self.compress(trace, partial.as_ref().map(|p| (p, index))));
                        self.outcome(r, true, true)
                    }
                    // TLC reports an exception thrown by the next-state relation without the statistics
                    ref other => self.outcome(self.error(self.ck.describe_err(other, true), Some(self.compress(trace, None))), false, true),
                });
            }
            self.stats.generated += ev.extra_generated.replace(0);
            has_successor |= !succs.is_empty();
            for t in succs.iter() {
                self.stats.generated += 1;
                ev.stats.generated.set(self.stats.generated as i64);
                let with = |sim: &Sim| Some(sim.compress(trace, Some((t, index))));
                ev.stats.level.set(lvl + 1);
                for inv in &m.invariants {
                    match self.ck.eval_pred(inv, t, None) {
                        Err(e) => {
                            let mut r = self.error(format!("Evaluating invariant {} failed.\n{}", inv.name, self.ck.describe_err(&e, false)), with(self));
                            r.code = Some(2111);
                            return Err(self.outcome(r, true, true));
                        }
                        Ok(false) => {
                            let mut r = self.result("invariant");
                            r.name = Some(inv.name.clone());
                            r.trace = with(self);
                            return Err(self.outcome(r, true, true));
                        }
                        Ok(true) => {}
                    }
                }
                ev.stats.level.set(lvl);
                for p in &m.implied_actions {
                    match self.ck.eval_pred(p, &s, Some(t)) {
                        Err(e) => {
                            let mut r = self.error(format!("Evaluating action property {} failed.\n{}", p.name, self.ck.describe_err(&e, false)), with(self));
                            r.code = Some(2113);
                            return Err(self.outcome(r, true, true));
                        }
                        Ok(false) => {
                            let mut r = self.result("action-property");
                            r.name = Some(p.name.clone());
                            r.trace = with(self);
                            return Err(self.outcome(r, true, true));
                        }
                        Ok(true) => {}
                    }
                }
                let admissible: R<bool> = (|| {
                    ev.stats.level.set(lvl + 1);
                    for c in &m.constraints {
                        if !self.ck.eval_pred(c, t, None)? {
                            return Ok(false);
                        }
                    }
                    ev.stats.level.set(lvl);
                    for c in &m.action_constraints {
                        if !self.ck.eval_pred(c, &s, Some(t))? {
                            return Ok(false);
                        }
                    }
                    Ok(true)
                })();
                match admissible {
                    Err(e) => return Err(self.outcome(self.error(self.ck.describe_err(&e, true), with(self)), false, true)),
                    Ok(true) => keep.push(t.clone()),
                    Ok(false) => {}
                }
            }
            if !keep.is_empty() {
                let t = keep[self.rng.below(keep.len())].clone();
                return Ok(Some((t, index)));
            }
            index = (index + stride) % n;
        }
        if self.opts.check_deadlock && !has_successor {
            let mut r = self.result("deadlock");
            r.trace = Some(self.compress(trace, None));
            return Err(self.outcome(r, true, true));
        }
        Ok(None)
    }

    /// Checks the temporal properties on one behaviour: on the graph of its states, with the steps it
    /// took and stuttering at every state, exactly as TLC does for a simulated behaviour.
    fn check_liveness(&mut self, trace: &[TraceStep]) -> Option<CheckResult> {
        self.live.as_ref()?;
        let tr = self.compress(trace, None);
        let n = self.nvars;
        self.ck.states.clear();
        self.ck.succ.clear();
        self.ck.succ_act.clear();
        self.ck.inits.clear();
        let mut index: HashMap<u64, Vec<u32>> = HashMap::new();
        let mut ids: Vec<u32> = Vec::with_capacity(tr.len());
        for t in &tr {
            let mut h = Hasher::new();
            let hashed: R<()> = t.state.with(|vals| {
                for v in &vals[..n] {
                    h.value(v)?;
                }
                Ok(())
            });
            if let Err(e) = hashed {
                let msg = self.ck.describe_err(&e, true);
                return Some(self.error(msg, None));
            }
            let bucket = index.entry(h.finish()).or_default();
            let id = match bucket.iter().find(|&&i| same_state(&self.ck.states[i as usize], &t.state, n)) {
                Some(&i) => i,
                None => {
                    let i = self.ck.states.len() as u32;
                    self.ck.states.push(t.state.clone());
                    self.ck.succ.push(vec![]);
                    self.ck.succ_act.push(vec![]);
                    bucket.push(i);
                    i
                }
            };
            ids.push(id);
        }
        self.ck.inits.push(ids[0]);
        for i in 1..tr.len() {
            let (a, b) = (ids[i - 1] as usize, ids[i]);
            if !self.ck.succ[a].contains(&b) {
                self.ck.succ[a].push(b);
                self.ck.succ_act[a].push(tr[i].action.unwrap_or(0) as u32);
            }
        }
        let live = self.live.as_mut().unwrap();
        match live.check(self.model, &self.ck) {
            Ok(None) => None,
            Ok(Some(r)) => Some(self.fix(r)),
            Err(e) => Some(self.error(self.ck.describe_err(&e, true), None)),
        }
    }

    /// Replays the trace of a result with the exhaustive checker's functions: the first state must be
    /// one of its initial states and every step (the step back to the start of a liveness loop
    /// included) one of the successors it computes, by the action the trace names.
    fn replay(&self, r: &CheckResult) -> Result<(), String> {
        let tr = match &r.trace {
            Some(t) if !t.is_empty() => t,
            _ => return Ok(()),
        };
        let n = self.nvars;
        let describe = |e: Box<Fail>| self.ck.describe_err(&e, true);
        let inits = self.ck.init_states().map_err(|r| r.message.unwrap_or_default())?;
        if !inits.iter().any(|s| same_state(s, &tr[0].state, n)) {
            return Err("state 1 is not an initial state".into());
        }
        let (mut succs, mut acts) = (vec![], vec![]);
        let mut steps: Vec<(usize, usize, Option<usize>)> = (1..tr.len()).map(|i| (i - 1, i, tr[i].action)).collect();
        if let Some(l) = r.loop_to {
            if l >= 0 {
                steps.push((tr.len() - 1, l as usize, r.loop_action));
            }
        }
        for (i, j, action) in steps {
            let (s, t) = (&tr[i].state, &tr[j].state);
            if (0..n).any(|k| t.is_undef(k)) {
                continue; // the incompletely specified successor that the error is about
            }
            succs.clear();
            acts.clear();
            self.ck.successors(s, &mut succs, &mut acts).map_err(describe)?;
            if !succs.iter().zip(acts.iter()).any(|(u, a)| same_state(u, t, n) && Some(*a as usize) == action) {
                return Err(format!("state {} is not a successor of state {} by the action named", j + 1, i + 1));
            }
        }
        Ok(())
    }

    /// `file=PREFIX`: the behaviour as a TLA+ module, in TLC's layout.
    fn write_trace(&self, prefix: &str, number: u64, trace: &[TraceStep], first: &str) -> Result<(), String> {
        let file = format!("{}_0_{}", prefix, number);
        let mut out = format!("---------------- MODULE {} -----------------\n", file);
        for (i, t) in self.compress(trace, None).iter().enumerate() {
            let label = match t.action {
                Some(a) if i > 0 => crate::cli::action_label(Some(&self.model.actions[a])),
                _ => first.to_string(),
            };
            out += &format!("\\* {}\nSTATE_{} == \n{}\n\n", label, i + 1, state_text(self.model, &t.state));
        }
        out += "=================================================\n";
        let host = self.ev.host.borrow().clone();
        host.write_file(&file, out.as_bytes())
    }
}

/// Generates random behaviours of `model` and checks them.
pub fn simulate(model: &Model, opts: &SimOptions, events: &mut dyn SimEvents) -> SimOutcome {
    let ev = model.ev;
    let ck = Checker::new(model, CheckOptions { check_deadlock: opts.check_deadlock, record_graph: true, par: None });
    let mut rng = Rng::new(opts.seed, opts.aril);
    // RandomElement and the Randomization module follow the seed too
    ev.rng.set(rng.next() | 1);
    ev.stats.sim.set(Some((opts.depth.map_or(-1, |d| d as i64), opts.num.map_or(-1, |n| n.min(i64::MAX as u64) as i64), opts.seed, opts.aril)));
    ev.stats.traces.set(0);
    let mut sim = Sim { model, ck, ev, opts, rng, stats: SimStats::default(), nvars: model.vars.len(), partial: RefCell::new(None), live: None };
    let mut out = run(&mut sim, events);
    // Self-check for the test suite (EVERYSTATE_SIM_REPLAY=1): a reported trace must be a behaviour
    // according to the functions the exhaustive checker explores the state space with.
    let host = ev.host.borrow().clone();
    if host.env().iter().any(|(k, v)| k == "EVERYSTATE_SIM_REPLAY" && v == "1") {
        if let Err(why) = sim.replay(&out.result) {
            out.result = sim.error(format!("Internal error: the trace reported by the simulation is not a behavior of the specification ({}).", why), out.result.trace.take());
            out.result.status = "replay-failed";
        }
    }
    out
}

fn run(sim: &mut Sim, events: &mut dyn SimEvents) -> SimOutcome {
    let (model, opts, ev) = (sim.model, sim.opts, sim.ev);
    match PreparedLiveness::new(model, &sim.ck) {
        Err(r) => return sim.outcome(sim.fix(r), false, false),
        Ok(l) => sim.live = l,
    }
    if let Some(l) = &sim.live {
        events.branches(l.branches);
    }
    if let Some(r) = sim.ck.check_assumptions() {
        return sim.outcome(sim.fix(r), false, false);
    }
    if model.inits.is_empty() {
        // a specification without behaviours: only the assumptions are checked
        return sim.outcome(sim.result("ok"), true, false);
    }

    // ---- initial states ----
    let inits = match sim.ck.init_states() {
        Ok(v) => v,
        Err(r) => return sim.outcome(sim.fix(r), true, false),
    };
    sim.stats.generated = inits.len() as u64;
    sim.stats.longest = inits.len().min(1) as u32;
    ev.stats.generated.set(inits.len() as i64);
    ev.stats.level.set(1);
    events.init_computed(sim.stats.generated);
    let mut start: Vec<StateRef> = vec![];
    for s in inits {
        let one = |id: i64| Some(vec![TraceStep { state: s.clone(), action: None, id }]);
        for inv in &model.invariants {
            match sim.ck.eval_pred(inv, &s, None) {
                Err(e) => {
                    let mut r = sim.error(format!("Evaluating invariant {} failed.\n{}", inv.name, sim.ck.describe_err(&e, true)), one(0));
                    r.code = Some(2111);
                    return sim.outcome(r, true, false);
                }
                Ok(false) => {
                    let mut r = sim.result("invariant-init");
                    r.name = Some(inv.name.clone());
                    r.trace = one(0);
                    return sim.outcome(r, false, false);
                }
                Ok(true) => {}
            }
        }
        // TLC's simulator does not check state predicates given as PROPERTY; they are checked here so
        // that no property of the configuration is silently skipped
        for p in &model.implied_inits {
            match sim.ck.eval_pred(p, &s, None) {
                Err(e) => return sim.outcome(sim.error(format!("Evaluating property {} failed.\n{}", p.name, sim.ck.describe_err(&e, true)), one(-1)), true, false),
                Ok(false) => {
                    let mut r = sim.result("implied-init");
                    r.name = Some(p.name.clone());
                    r.trace = one(0);
                    return sim.outcome(r, false, false);
                }
                Ok(true) => {}
            }
        }
        let in_model: R<bool> = (|| {
            for c in &model.constraints {
                if !sim.ck.eval_pred(c, &s, None)? {
                    return Ok(false);
                }
            }
            Ok(true)
        })();
        match in_model {
            Err(e) => return sim.outcome(sim.error(sim.ck.describe_err(&e, true), one(-1)), true, false),
            Ok(true) => start.push(s),
            Ok(false) => {}
        }
    }
    if sim.stats.generated == 0 || start.is_empty() {
        let mut r = if sim.stats.generated == 0 {
            sim.error("There is no state satisfying the initial state predicate.".into(), None)
        } else {
            sim.error("There is no state satisfying the initial state predicate and the state-constraint(s).".into(), None)
        };
        r.code = Some(if sim.stats.generated == 0 { 2118 } else { 2256 });
        return sim.outcome(r, false, false);
    }
    events.init_done(start.len() as u64);
    if model.actions.is_empty() {
        let mut r = sim.error("No next state actions defined to generate successor states from.".into(), None);
        r.code = Some(2115);
        return sim.outcome(r, false, false);
    }

    // ---- behaviours ----
    let first = init_label(model);
    let mut last_progress = ev.host.borrow().now_ms();
    let mut trace: Vec<TraceStep> = vec![];
    let (mut succs, mut keep): (Vec<StateRef>, Vec<StateRef>) = (vec![], vec![]);
    let limit = opts.num.map(|n| n.max(1));
    while limit.map_or(true, |n| sim.stats.traces < n) && !ev.stats.stop_requested.get() {
        sim.stats.traces += 1;
        ev.stats.traces.set(sim.stats.traces as i64);
        trace.clear();
        trace.push(TraceStep { state: start[sim.rng.below(start.len())].clone(), action: None, id: 0 });
        let mut steps: u32 = 0;
        while opts.depth.map_or(true, |d| steps < d) && !ev.stats.stop_requested.get() {
            steps = steps.saturating_add(1);
            match sim.step(&trace, &mut succs, &mut keep) {
                Err(out) => return out,
                Ok(None) => break,
                Ok(Some((t, a))) => trace.push(TraceStep { state: t, action: Some(a), id: trace.len() as i64 }),
            }
            sim.stats.longest = sim.stats.longest.max(trace.len().min(u32::MAX as usize) as u32);
            if steps & 255 == 0 {
                let now = ev.host.borrow().now_ms();
                if now - last_progress > 60000.0 {
                    last_progress = now;
                    events.progress(&sim.stats);
                }
            }
        }
        ev.stats.level.set(trace.len() as i64);
        if let Some(r) = sim.check_liveness(&trace) {
            let summary = r.status == "liveness";
            return sim.outcome(r, summary, true);
        }
        if let Some(prefix) = &opts.trace_file {
            if let Err(e) = sim.write_trace(prefix, sim.stats.traces - 1, &trace, &first) {
                return sim.outcome(sim.error(format!("Failed to write the trace file: {}", e), None), true, true);
            }
        }
        let len = trace.len() as i64;
        sim.stats.record(opts.depth.map_or(len, |d| len.min(d as i64)));
        let now = ev.host.borrow().now_ms();
        if now - last_progress > 60000.0 {
            last_progress = now;
            events.progress(&sim.stats);
        }
    }
    if let Some(r) = check_postconditions(model, &sim.ck) {
        return sim.outcome(sim.fix(r), false, true);
    }
    sim.outcome(sim.result("ok"), true, true)
}

// ---------------------------------------------------------------------------------------------
// command line

/// The simulation options of TLC's command line, collected while the arguments are read.
#[derive(Default)]
pub struct SimArgs {
    on: bool,
    num: Option<u64>,
    file: Option<String>,
    depth: Option<i64>,
    seed: Option<i64>,
    aril: Option<i64>,
}
impl SimArgs {
    /// Handles `argv[*i]`, one of `-simulate`, `-generate`, `-depth`, `-seed` and `-aril`, and leaves
    /// `*i` on the last argument it consumed. Errors are worded as TLC words them.
    pub fn parse(&mut self, argv: &[String], i: &mut usize) -> Result<(), String> {
        let flag = argv[*i].as_str();
        if flag == "-generate" {
            return Err("Error: -generate (TLC's probabilistic generation mode) is not supported by everystate; use -simulate.".into());
        }
        if flag == "-simulate" {
            self.on = true;
            if let Some(a) = argv.get(*i + 1) {
                if a.contains("stats=") || a.contains("file=") || a.contains("num=") || a.contains("sched") {
                    *i += 1;
                    for part in a.split(',') {
                        if let Some(n) = part.strip_prefix("num=") {
                            self.num = Some(n.parse::<i64>().map_err(|_| format!("Error: An integer for the number of traces required. But encountered {}", n))?.max(0) as u64);
                        } else if let Some(f) = part.strip_prefix("file=") {
                            self.file = Some(f.to_string());
                        }
                        // stats=... and sched=... select reports and schedulers everystate does not have
                    }
                    if self.num.is_none() && self.file.is_some() {
                        return Err("Error: You need to specify a 'num' argument when using the 'file' argument, for example: '\"num=5,file=test.txt\"'.".into());
                    }
                }
            }
            return Ok(());
        }
        let (what, slot) = match flag {
            "-depth" => ("trace length", &mut self.depth),
            "-seed" => ("seed", &mut self.seed),
            _ => ("aril", &mut self.aril),
        };
        *i += 1;
        match argv.get(*i) {
            None => Err(format!("Error: {} required.", what)),
            Some(a) => {
                let ok = if flag == "-depth" { a.parse::<i32>().map(|v| v as i64).ok() } else { a.parse::<i64>().ok() };
                *slot = Some(ok.ok_or_else(|| format!("Error: An integer for {} required. But encountered {}", what, a))?);
                Ok(())
            }
        }
    }

    /// The options of the run, or `None` without `-simulate`. A run without `num=` goes on until it
    /// finds an error, as in TLC, except with `-json`, whose single result needs the run to end.
    pub fn options(&self, json: bool, now_ms: f64) -> Option<SimOptions> {
        if !self.on {
            return None;
        }
        Some(SimOptions {
            num: self.num.or(if json { Some(DEFAULT_TRACES) } else { None }),
            depth: match self.depth {
                None => Some(DEFAULT_DEPTH),
                Some(-1) => None,
                Some(d) => Some(d.max(0) as u32),
            },
            seed: self.seed.unwrap_or_else(|| clock_seed(now_ms)),
            aril: self.aril.unwrap_or(0),
            check_deadlock: true,
            trace_file: self.file.clone(),
        })
    }
}

struct CliSim<'r> {
    rep: &'r Reporter,
    json: bool,
}
fn progress_line(rep: &Reporter, st: &SimStats) {
    if rep.tool {
        // the layout of model checking, which is what tools parse
        rep.msg(2209, 0, &format!("Progress({}) at {}: {} states generated, -1 distinct states found, -1 states left on queue.", st.traces, rep.now(), st.generated));
    } else {
        rep.msg(
            2209,
            0,
            &format!("Progress: {} states checked, {} traces generated (trace length: mean={}, var(x)={}, sd={})", st.generated, st.traces, st.mean, st.variance(), st.sd()),
        );
    }
}
impl SimEvents for CliSim<'_> {
    fn branches(&mut self, n: usize) {
        if !self.json {
            self.rep.msg(2212, 0, &format!("Implied-temporal checking--satisfiability problem has {} branches.", n));
        }
    }
    fn init_computed(&mut self, generated: u64) {
        if !self.json {
            self.rep.msg(2269, 0, &format!("Computed {} initial states...", generated));
        }
    }
    fn init_done(&mut self, usable: u64) {
        if !self.json {
            self.rep.msg(2190, 0, &format!("Finished computing initial states: {} distinct state generated at {}.", usable, self.rep.now()));
        }
    }
    fn progress(&mut self, stats: &SimStats) {
        if !self.json {
            progress_line(self.rep, stats);
        }
    }
}

/// The `-json` result of a simulation: the fields of a model-checking result, with `mode`, the number
/// of behaviours and the seed added. `distinct` and `queue` do not apply and are -1 (as in TLC's
/// `-tool` progress lines); `depth` is the number of states of the longest behaviour.
pub fn sim_json(model: &Model, out: &SimOutcome, opts: &SimOptions, extended: bool) -> String {
    let st = &out.stats;
    let counts = format!(
        ",\"mode\":\"simulate\",\"generated\":{},\"distinct\":-1,\"queue\":-1,\"depth\":{},\"traces\":{},\"seed\":{},\"aril\":{}",
        st.generated, st.longest, st.traces, opts.seed, opts.aril
    );
    result_json_with(model, &out.result, extended, &counts)
}

/// Runs a simulation for the command line and prints TLC's output; returns the exit status.
pub(crate) fn run_cli(rep: &Reporter, model: &Model, opts: &SimOptions, deadlock: bool, json: bool, t0: f64) -> i32 {
    let mut opts = opts.clone();
    opts.check_deadlock = deadlock && model.check_deadlock;
    *rep.init_label.borrow_mut() = Some(init_label(model));
    let out = simulate(model, &opts, &mut CliSim { rep, json });
    let res = &out.result;
    let code = if res.call_stack.is_some() {
        75
    } else if res.code == Some(2111) {
        76
    } else if res.code == Some(2404) {
        10 // a false POSTCONDITION: TLC's exit status for it
    } else if res.code == Some(2105) {
        10 // an assumption whose evaluation fails: TLC's exit status for it
    } else {
        exit_code(res.status)
    };
    if json {
        rep.host.print(&format!("{}\n", sim_json(model, &out, &opts, false)));
        return code;
    }
    let summary = || {
        if rep.tool {
            progress_line(rep, &out.stats);
        }
        rep.msg(2210, 0, &format!("The number of states generated: {}\nSimulation using seed {} and aril {}", out.stats.generated, opts.seed, opts.aril));
    };
    if res.status == "ok" {
        if out.final_progress {
            progress_line(rep, &out.stats);
        }
        summary();
        return code;
    }
    report(rep, model, res, t0);
    if out.summary {
        summary();
    }
    if out.final_progress {
        progress_line(rep, &out.stats);
    }
    code
}
