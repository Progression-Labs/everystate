//! Explicit-state breadth-first model checker (port of checker.ts).
use crate::ast::{E, N};
use crate::eval::*;
use crate::intern::*;
use crate::model::*;
use crate::value::*;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Clone)]
pub struct TraceStep {
    pub state: StateRef,
    pub action: Option<usize>,
    pub id: i64,
}
#[derive(Clone, Copy)]
pub struct Outdegree {
    pub min: u32,
    pub avg: u32,
    pub p95: u32,
    pub max: u32,
}
pub struct CheckResult {
    pub status: &'static str,
    pub name: Option<String>,
    pub message: Option<String>,
    pub trace: Option<Vec<TraceStep>>,
    /// liveness: index (0-based) of the state the lasso returns to; -1 = stuttering
    pub loop_to: Option<i64>,
    pub loop_action: Option<usize>,
    pub live_branches: usize,
    /// TLC-style list of nested expression positions for evaluation errors
    pub call_stack: Option<String>,
    /// TLC message code for `message`, when it is not a generic error
    pub code: Option<u32>,
    pub generated: u64,
    pub distinct: u64,
    pub queue: u64,
    pub depth: u32,
    pub init_generated: u64,
    pub init_distinct: u64,
    pub print_summary: bool,
    pub outdegree: Option<Outdegree>,
}

/// Progress notifications (the CLI prints TLC's progress messages from these).
pub trait Events {
    fn init_done(&mut self, _init_generated: u64, _init_distinct: u64) {}
    fn progress(&mut self, _depth: u32, _generated: u64, _distinct: u64, _queue: u64) {}
    /// phase: "branches" | "start" | "end"
    fn liveness(&mut self, _phase: &str, _branches: usize, _depth: u32, _generated: u64, _distinct: u64) {}
}
pub struct NoEvents;
impl Events for NoEvents {}

pub struct CheckOptions {
    pub check_deadlock: bool,
    pub record_graph: bool,
}

/// Open-addressing hash set of 64-bit fingerprints mapping to state ids.
pub struct FpSet {
    keys: Vec<u64>, // 0 = empty
    ids: Vec<u32>,
    size: usize,
    mask: usize,
}
impl FpSet {
    pub fn new() -> FpSet {
        let cap = 1 << 16;
        FpSet { keys: vec![0; cap], ids: vec![0; cap], size: 0, mask: cap - 1 }
    }
    /// Returns the existing id, or None after inserting `id`.
    #[inline]
    pub fn put(&mut self, fp: u64, id: u32) -> Option<u32> {
        if self.size * 2 >= self.keys.len() {
            self.grow();
        }
        let fp = if fp == 0 { 0x9E37_79B9_7F4A_7C15 } else { fp };
        let mut i = (fp as usize) & self.mask;
        loop {
            let k = self.keys[i];
            if k == 0 {
                self.keys[i] = fp;
                self.ids[i] = id;
                self.size += 1;
                return None;
            }
            if k == fp {
                return Some(self.ids[i]);
            }
            i = (i + 1) & self.mask;
        }
    }
    fn grow(&mut self) {
        let cap = self.keys.len() * 2;
        let ok = std::mem::replace(&mut self.keys, vec![0; cap]);
        let oi = std::mem::replace(&mut self.ids, vec![0; cap]);
        self.mask = cap - 1;
        for (j, &k) in ok.iter().enumerate() {
            if k == 0 {
                continue;
            }
            let mut i = (k as usize) & self.mask;
            while self.keys[i] != 0 {
                i = (i + 1) & self.mask;
            }
            self.keys[i] = k;
            self.ids[i] = oi[j];
        }
    }
}

/// Applies a model-value permutation; None when the value is unchanged.
pub fn permute(v: &Value, m: &HashMap<StrId, StrId>) -> R<Option<Value>> {
    fn all(vs: &[Value], m: &HashMap<StrId, StrId>) -> R<Option<Vec<Value>>> {
        let mut out: Option<Vec<Value>> = None;
        for (i, x) in vs.iter().enumerate() {
            if let Some(y) = permute(x, m)? {
                let o = out.get_or_insert_with(|| vs.to_vec());
                o[i] = y;
            }
        }
        Ok(out)
    }
    Ok(match v {
        Value::Model(x) => m.get(x).map(|y| Value::Model(*y)),
        Value::Tuple(t) => all(t, m)?.map(|e| Value::Tuple(Rc::new(e))),
        Value::Record(r) => all(&r.vals, m)?.map(|vals| Value::Record(Rc::new(RecordV { names: r.names.clone(), vals }))),
        Value::Fcn(f) => {
            let d = all(&f.dom, m)?;
            let vs = all(&f.vals, m)?;
            match (d, vs) {
                (None, None) => None,
                (None, Some(vals)) => Some(Value::Fcn(Rc::new(FcnV { dom: f.dom.clone(), vals }))),
                (Some(d), vs) => {
                    let vals = vs.unwrap_or_else(|| f.vals.clone());
                    Some(make_fcn_from_pairs(d.into_iter().zip(vals).collect())?)
                }
            }
        }
        Value::Set(s) => match &s.k {
            SetK::Interval(..) => None,
            _ => match all(s.elems()?, m)? {
                None => None,
                Some(e) => Some(mk_set(e)?),
            },
        },
        _ => None,
    })
}

pub struct Checker<'a> {
    pub model: &'a Model,
    pub ev: &'static Evaluator,
    pub opts: CheckOptions,
    pub states: Vec<StateRef>,
    pub parent: Vec<u32>,
    pub level: Vec<u32>,
    pub act: Vec<i32>,
    /// recorded graph: successor ids / actions per state (if record_graph)
    pub succ: Vec<Vec<u32>>,
    pub succ_act: Vec<Vec<u32>>,
    /// actual successor states per edge (only with VIEW/SYMMETRY + liveness)
    pub succ_state: Option<Vec<Vec<StateRef>>>,
    pub inits: Vec<u32>,
    fps: FpSet,
    pub generated: u64,
    pub init_generated: u64,
    pub init_distinct: u64,
    pub head: usize,
    pub depth: u32,
    nvars: usize,
    outdeg: Vec<u32>,
    cur_level: u32,
    empty: StateRef,
}

pub const NO_PARENT: u32 = u32::MAX;

impl<'a> Checker<'a> {
    pub fn new(model: &'a Model, opts: CheckOptions) -> Checker<'a> {
        let ev = model.ev;
        ev.stats.active.set(true);
        ev.stats.check_deadlock.set(opts.check_deadlock);
        Checker {
            model,
            ev,
            opts,
            states: vec![],
            parent: vec![],
            level: vec![],
            act: vec![],
            succ: vec![],
            succ_act: vec![],
            succ_state: None,
            inits: vec![],
            fps: FpSet::new(),
            generated: 0,
            init_generated: 0,
            init_distinct: 0,
            head: 0,
            depth: 0,
            nvars: model.vars.len(),
            outdeg: vec![],
            cur_level: 0,
            empty: StateData::blank(0),
        }
    }

    fn sync_stats(&self) {
        let st = &self.ev.stats;
        st.level.set(self.cur_level as i64);
        st.distinct.set(self.states.len() as i64);
        st.generated.set(self.generated as i64);
        st.queue.set(self.states.len() as i64 - self.head as i64);
        st.diameter.set(self.depth as i64);
    }
    fn set_level(&mut self, l: u32) {
        self.cur_level = l;
        self.ev.stats.level.set(l as i64);
    }

    /// The values that identify a state: the VIEW value, or all variables, of the symmetry-canonical state.
    pub fn fingerprint_input(&self, s: &StateRef) -> R<Vec<Value>> {
        let m = self.model;
        let mut canon: Option<Vec<Value>> = None;
        if let Some(sym) = &m.symmetry {
            let base = s.snapshot(self.nvars);
            for p in sym {
                // Lexicographic comparison with the best candidate so far, variable by variable: most
                // permutations lose on the first variable and the rest of the state is never permuted.
                let mut u: Vec<Value> = Vec::new();
                let mut wins = false;
                for (i, v) in base.iter().enumerate() {
                    let x = permute(v, p)?.unwrap_or_else(|| v.clone());
                    if !wins {
                        match compare(&x, &canon.as_ref().unwrap_or(&base)[i])? {
                            Ordering::Greater => break,
                            Ordering::Less => wins = true,
                            Ordering::Equal => {}
                        }
                    }
                    u.push(x);
                }
                if wins {
                    canon = Some(u);
                }
            }
        }
        if let Some(view) = &m.view {
            let t = match canon {
                Some(c) => StateData::new(c),
                None => s.clone(),
            };
            self.ev.set_state(&t, None);
            self.ev.init_mode.set(false);
            return Ok(vec![self.ev.eval(view.e, &view.ctx)?]);
        }
        Ok(match canon {
            Some(c) => c,
            None => s.snapshot(self.nvars),
        })
    }

    pub fn fingerprint(&self, s: &StateRef) -> R<u64> {
        let mut h = Hasher::new();
        if self.model.symmetry.is_none() && self.model.view.is_none() {
            s.with(|vals| -> R<()> {
                for v in &vals[..self.nvars] {
                    h.value(v)?;
                }
                Ok(())
            })?;
        } else {
            for v in self.fingerprint_input(s)? {
                h.value(&v)?;
            }
        }
        Ok(h.finish())
    }

    pub fn result(&self, status: &'static str) -> CheckResult {
        CheckResult {
            status,
            name: None,
            message: None,
            trace: None,
            loop_to: None,
            loop_action: None,
            live_branches: 0,
            call_stack: None,
            code: None,
            generated: self.generated,
            distinct: self.states.len() as u64,
            queue: (self.states.len() - self.head.min(self.states.len())) as u64,
            depth: self.depth,
            init_generated: self.init_generated,
            init_distinct: self.init_distinct,
            print_summary: true,
            outdegree: self.outdegree(),
        }
    }
    pub fn error(&self, message: String, trace: Option<Vec<TraceStep>>) -> CheckResult {
        let mut r = self.result("error");
        r.message = Some(message);
        r.trace = trace;
        r
    }

    fn outdegree(&self) -> Option<Outdegree> {
        if self.outdeg.is_empty() {
            return None;
        }
        let mut d = self.outdeg.clone();
        d.sort_unstable();
        let sum: u64 = d.iter().map(|x| *x as u64).sum();
        let avg = (sum as f64 / d.len() as f64 + 0.5).floor() as u32;
        let p = ((d.len() as f64 * 0.95).ceil() as usize).saturating_sub(1).min(d.len() - 1);
        Some(Outdegree { min: d[0], avg, p95: d[p], max: d[d.len() - 1] })
    }

    pub fn trace_to(&self, id: usize) -> Vec<TraceStep> {
        let mut out = vec![];
        let mut i = id as u32;
        loop {
            let a = self.act[i as usize];
            out.push(TraceStep { state: self.states[i as usize].clone(), action: if a >= 0 { Some(a as usize) } else { None }, id: i as i64 });
            i = self.parent[i as usize];
            if i == NO_PARENT {
                break;
            }
        }
        out.reverse();
        out
    }
    fn trace_plus(&self, sid: usize, t: &StateRef, a: usize, id: i64) -> Vec<TraceStep> {
        let mut tr = self.trace_to(sid);
        tr.push(TraceStep { state: t.clone(), action: Some(a), id });
        tr
    }

    pub fn eval_pred(&self, p: &Pred, s: &StateRef, t: Option<&StateRef>) -> R<bool> {
        self.eval_pred_at(p.e, &p.ctx, s, t)
    }
    pub fn eval_pred_at(&self, e: N, ctx: &C, s: &StateRef, t: Option<&StateRef>) -> R<bool> {
        let ev = self.ev;
        ev.set_state(s, t);
        ev.init_mode.set(false);
        ev.prime_depth.set(0);
        ev.call_depth.set(0);
        ev.n_assigned.set(0);
        ev.eval_bool(e, ctx)
    }

    /// Re-run a failing evaluation while recording the chain of nested expressions being evaluated.
    fn nested_expressions(&self, p: &Pred, s: &StateRef, t: Option<&StateRef>) -> String {
        let ev = self.ev;
        ev.trace_stack.borrow_mut().clear();
        ev.tracing.set(true);
        let _ = self.eval_pred(p, s, t);
        ev.tracing.set(false);
        let stack = std::mem::take(&mut *ev.trace_stack.borrow_mut());
        let mut lines: Vec<String> = vec![];
        let mut last: Option<N> = None;
        for n in stack {
            if std::ptr::eq(n, p.e) || last.map_or(false, |l| std::ptr::eq(l, n)) || n.loc[0] == 0 || matches!(n.e, E::Num(_) | E::Str(..)) {
                continue;
            }
            last = Some(n);
            lines.push(format!(
                "{}. Line {}, column {} to line {}, column {} in {}",
                lines.len(),
                n.loc[0],
                n.loc[1],
                n.loc[2],
                n.loc[3],
                n.module_str().unwrap_or_else(|| self.model.root_name.clone())
            ));
        }
        if lines.is_empty() { "    The error call stack is empty.\n".to_string() } else { lines.join("\n") + "\n" }
    }

    fn check_assumptions(&self) -> Option<CheckResult> {
        let ev = self.ev;
        for a in &self.model.root.assumes {
            ev.set_state(&self.empty, None);
            ev.init_mode.set(false);
            let at = loc_str(&a.e.loc, &a.module.to_string());
            match ev.eval(a.e, &None) {
                Err(e) => {
                    let mut r = match *e {
                        Fail::Tla(t) => self.error(format!("Evaluating assumption {} failed.\n{}", at, t.msg), None),
                        _ => self.error(format!("Evaluating assumption {} failed.", at), None),
                    };
                    r.code = Some(2105);
                    r.print_summary = false;
                    return Some(r);
                }
                Ok(Value::Bool(true)) => {}
                Ok(Value::Bool(false)) => {
                    let mut r = self.result("assumption");
                    r.message = Some(format!("Assumption {} is false.", at));
                    r.print_summary = false;
                    return Some(r);
                }
                Ok(_) => {
                    let mut r = self.error(format!("The assumption {} was not a boolean.", at), None);
                    r.print_summary = false;
                    return Some(r);
                }
            }
        }
        None
    }

    pub fn describe_err(&self, e: &Fail, with_loc: bool) -> String {
        match e {
            Fail::Tla(t) => {
                if t.kind == "stack" {
                    return "Stack overflow while evaluating the specification (recursion too deep). Re-run with a larger stack.".into();
                }
                let mut m = t.msg.clone();
                if with_loc {
                    if let Some(l) = t.loc {
                        if l[0] > 0 {
                            m += &format!("\n(evaluating the expression at line {}, col {} to line {}, col {} of module {})", l[0], l[1], l[2], l[3], t.module.as_deref().unwrap_or("?"));
                        }
                    }
                }
                m
            }
            Fail::Found => "internal error: unexpected control flow".into(),
            Fail::Check { message, .. } => message.clone(),
        }
    }

    fn missing(&self, s: &StateData) -> Vec<String> {
        let mut v: Vec<String> = self.model.vars.iter().enumerate().filter(|(j, _)| s.is_undef(*j)).map(|(_, d)| d.name.to_string()).collect();
        v.sort();
        v
    }

    // Enumerate initial states.
    fn compute_init(&mut self) -> Option<CheckResult> {
        let ev = self.ev;
        let m = self.model;
        let nv = self.nvars;
        let mut found: Vec<StateRef> = vec![];
        let buf = StateData::blank(nv);
        ev.set_state(&buf, None);
        ev.init_mode.set(true);
        ev.prime_depth.set(0);
        ev.n_assigned.set(0);
        let preds = &m.inits;
        if preds.is_empty() {
            return None;
        }
        fn go(ck: &Checker, preds: &[Pred], i: usize, buf: &StateRef, found: &mut Vec<StateRef>) -> R<()> {
            if i == preds.len() {
                for k in 0..ck.nvars {
                    if buf.is_undef(k) {
                        let missing = ck.missing(buf);
                        let many = missing.len() > 1;
                        return Err(Box::new(Fail::Check {
                            status: "init-error",
                            message: format!(
                                "current state is not a legal state\nWhile working on the initial state:\nThe variable{} {} {} not assigned a value by the initial predicate.",
                                if many { "s" } else { "" },
                                missing.join(", "),
                                if many { "are" } else { "is" }
                            ),
                        }));
                    }
                }
                found.push(StateData::new(buf.snapshot(ck.nvars)));
                return Ok(());
            }
            ck.ev.enumerate(preds[i].e, &preds[i].ctx, &mut || go(ck, preds, i + 1, buf, found))
        }
        let r = go(self, preds, 0, &buf, &mut found);
        ev.init_mode.set(false);
        if let Err(e) = r {
            return Some(match *e {
                Fail::Check { status, message } => {
                    let mut r = self.result(status);
                    r.message = Some(message);
                    r
                }
                ref other => self.error(self.describe_err(other, true), None),
            });
        }
        self.set_level(1);
        for s in found {
            self.generated += 1;
            self.init_generated += 1;
            let mut unseen = true;
            let mut id: i64 = -1;
            let step: R<()> = (|| {
                let mut in_model = true;
                for c in &m.constraints {
                    if !self.eval_pred(c, &s, None)? {
                        in_model = false;
                        break;
                    }
                }
                if in_model {
                    let fp = self.fingerprint(&s)?;
                    let nid = self.states.len();
                    id = nid as i64;
                    unseen = self.fps.put(fp, nid as u32).is_none();
                    if unseen {
                        self.states.push(s.clone());
                        self.parent.push(NO_PARENT);
                        self.level.push(1);
                        self.act.push(-1);
                        self.inits.push(nid as u32);
                        if self.opts.record_graph {
                            self.succ.push(vec![]);
                            self.succ_act.push(vec![]);
                            if let Some(ss) = &mut self.succ_state {
                                ss.push(vec![]);
                            }
                        }
                        self.depth = self.depth.max(1);
                        self.init_distinct += 1;
                    }
                }
                Ok(())
            })();
            self.sync_stats();
            let one = |id: i64| Some(vec![TraceStep { state: s.clone(), action: None, id }]);
            if let Err(e) = step {
                return Some(self.error(self.describe_err(&e, true), one(-1)));
            }
            if unseen {
                for inv in &m.invariants {
                    match self.eval_pred(inv, &s, None) {
                        Err(e) => {
                            let mut r = self.error(format!("Evaluating invariant {} failed.\n{}", inv.name, self.describe_err(&e, true)), one(-1));
                            r.code = Some(2111);
                            return Some(r);
                        }
                        Ok(false) => {
                            let mut r = self.result("invariant-init");
                            r.name = Some(inv.name.clone());
                            r.trace = one(id);
                            r.print_summary = false;
                            return Some(r);
                        }
                        Ok(true) => {}
                    }
                }
                for p in &m.implied_inits {
                    match self.eval_pred(p, &s, None) {
                        Err(e) => {
                            return Some(self.error(format!("Evaluating property {} failed.\n{}", p.name, self.describe_err(&e, true)), one(-1)));
                        }
                        Ok(false) => {
                            let mut r = self.result("implied-init");
                            r.name = Some(p.name.clone());
                            r.trace = one(id);
                            r.print_summary = false;
                            return Some(r);
                        }
                        Ok(true) => {}
                    }
                }
            }
        }
        None
    }

    // Successors of one state, as (state, action index) pairs in action order.
    fn successors(&self, s: &StateRef, out: &mut Vec<StateRef>, out_act: &mut Vec<u32>) -> R<()> {
        let ev = self.ev;
        let m = self.model;
        let n = self.nvars;
        let actions = &m.actions;
        for (ai, a) in actions.iter().enumerate() {
            let nxt = StateData::blank(n);
            ev.set_state(s, Some(&nxt));
            ev.init_mode.set(false);
            ev.prime_depth.set(0);
            ev.call_depth.set(0);
            ev.n_assigned.set(0);
            ev.enumerate(a.e, &a.ctx, &mut || {
                for k in 0..n {
                    if nxt.is_undef(k) {
                        let missing = self.missing(&nxt);
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
                out_act.push(ai as u32);
                Ok(())
            })?;
        }
        Ok(())
    }

    pub fn run(&mut self, events: &mut dyn Events) -> CheckResult {
        let m = self.model;
        if let Some(r) = self.check_assumptions() {
            return r;
        }
        if let Some(r) = self.compute_init() {
            return r;
        }
        events.init_done(self.init_generated, self.init_distinct);
        let mut succs: Vec<StateRef> = vec![];
        let mut succ_act: Vec<u32> = vec![];
        let record = self.opts.record_graph;
        let ev = self.ev;
        let mut last_progress = ev.host.borrow().now_ms();
        if m.inits.is_empty() {
            return self.result("ok");
        }
        if m.actions.is_empty() {
            let mut r = self.error("No next state actions defined to generate successor states from.".into(), None);
            r.code = Some(2115);
            r.print_summary = false;
            return r;
        }
        while self.head < self.states.len() && !ev.stats.stop_requested.get() {
            let sid = self.head;
            self.head += 1;
            let s = self.states[sid].clone();
            let lvl = self.level[sid];
            self.cur_level = lvl;
            self.sync_stats();
            succs.clear();
            succ_act.clear();
            if let Err(e) = self.successors(&s, &mut succs, &mut succ_act) {
                return match *e {
                    Fail::Check { status, message } => {
                        let mut r = self.result(status);
                        r.message = Some(message);
                        r.trace = Some(self.trace_to(sid));
                        r.queue = (self.states.len() - self.head) as u64;
                        r
                    }
                    ref other => self.error(self.describe_err(other, true), Some(self.trace_to(sid))),
                };
            }
            let extra = ev.extra_generated.replace(0);
            self.generated += extra;
            let mut fresh = 0u32;
            for i in 0..succs.len() {
                let t = succs[i].clone();
                let ai = succ_act[i] as usize;
                self.generated += 1;
                ev.stats.generated.set(self.generated as i64);
                let mut in_model = true;
                let mut unseen = true;
                let mut id: i64 = -1;
                let step: R<()> = (|| {
                    self.set_level(lvl + 1);
                    for c in &m.constraints {
                        if !self.eval_pred(c, &t, None)? {
                            in_model = false;
                            break;
                        }
                    }
                    self.set_level(lvl);
                    if in_model {
                        for c in &m.action_constraints {
                            if !self.eval_pred(c, &s, Some(&t))? {
                                in_model = false;
                                break;
                            }
                        }
                    }
                    self.set_level(lvl + 1);
                    if in_model {
                        let fp = self.fingerprint(&t)?;
                        let nid = self.states.len();
                        match self.fps.put(fp, nid as u32) {
                            None => {
                                id = nid as i64;
                                self.states.push(t.clone());
                                self.parent.push(sid as u32);
                                self.level.push(lvl + 1);
                                self.act.push(ai as i32);
                                if record {
                                    self.succ.push(vec![]);
                                    self.succ_act.push(vec![]);
                                    if let Some(ss) = &mut self.succ_state {
                                        ss.push(vec![]);
                                    }
                                }
                                if lvl + 1 > self.depth {
                                    self.depth = lvl + 1;
                                    ev.stats.diameter.set(self.depth as i64);
                                }
                                fresh += 1;
                                ev.stats.distinct.set(self.states.len() as i64);
                                ev.stats.queue.set(self.states.len() as i64 - self.head as i64);
                            }
                            Some(ex) => {
                                unseen = false;
                                id = ex as i64;
                            }
                        }
                        if record {
                            self.succ[sid].push(id as u32);
                            self.succ_act[sid].push(ai as u32);
                            if let Some(ss) = &mut self.succ_state {
                                ss[sid].push(t.clone());
                            }
                        }
                    }
                    Ok(())
                })();
                if let Err(e) = step {
                    return self.error(self.describe_err(&e, true), Some(self.trace_plus(sid, &t, ai, -1)));
                }
                if unseen {
                    for inv in &m.invariants {
                        match self.eval_pred(inv, &t, None) {
                            Err(e) => {
                                let mut r = self.error(format!("Evaluating invariant {} failed.\n{}", inv.name, self.describe_err(&e, false)), Some(self.trace_plus(sid, &t, ai, id)));
                                r.code = Some(2111);
                                if !in_model {
                                    r.call_stack = Some(self.nested_expressions(inv, &t, None));
                                }
                                if in_model {
                                    r.queue = r.queue.saturating_sub(1); // the new state has not been enqueued yet
                                }
                                return r;
                            }
                            Ok(false) => {
                                let mut r = self.result("invariant");
                                r.name = Some(inv.name.clone());
                                r.trace = Some(self.trace_plus(sid, &t, ai, id));
                                if in_model {
                                    r.queue = r.queue.saturating_sub(1);
                                }
                                return r;
                            }
                            Ok(true) => {}
                        }
                    }
                }
                self.set_level(lvl);
                for p in &m.implied_actions {
                    match self.eval_pred(p, &s, Some(&t)) {
                        Err(e) => {
                            return self.error(format!("Evaluating action property {} failed.\n{}", p.name, self.describe_err(&e, true)), Some(self.trace_plus(sid, &t, ai, id)));
                        }
                        Ok(false) => {
                            let mut r = self.result("action-property");
                            r.name = Some(p.name.clone());
                            r.trace = Some(self.trace_plus(sid, &t, ai, id));
                            if in_model && unseen {
                                r.queue = r.queue.saturating_sub(1);
                            }
                            return r;
                        }
                        Ok(true) => {}
                    }
                }
            }
            self.outdeg.push(fresh);
            if succs.is_empty() && self.opts.check_deadlock {
                let mut r = self.result("deadlock");
                r.trace = Some(self.trace_to(sid));
                return r;
            }
            if sid & 1023 == 0 {
                let now = ev.host.borrow().now_ms();
                if now - last_progress > 60000.0 {
                    last_progress = now;
                    events.progress(self.depth, self.generated, self.states.len() as u64, (self.states.len() - self.head) as u64);
                }
            }
        }
        self.sync_stats();
        self.result("ok")
    }
}
