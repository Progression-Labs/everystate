//! Explicit-state breadth-first model checker (port of checker.ts).
use crate::eval::*;
use crate::intern::*;
use crate::model::*;
use crate::value::*;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::rc::Rc;

pub struct TraceStep {
    pub state: StateRef,
    pub action: Option<usize>,
}
pub struct CheckResult {
    pub status: &'static str,
    pub name: Option<String>,
    pub message: Option<String>,
    pub trace: Option<Vec<TraceStep>>,
    pub generated: u64,
    pub distinct: u64,
    pub queue: u64,
    pub depth: u32,
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
    ev: &'static Evaluator,
    check_deadlock: bool,
    pub states: Vec<StateRef>,
    parent: Vec<u32>,
    level: Vec<u32>,
    act: Vec<i32>,
    fps: FpSet,
    pub generated: u64,
    head: usize,
    depth: u32,
    nvars: usize,
    cur_level: u32,
    empty: StateRef,
}

const NO_PARENT: u32 = u32::MAX;

impl<'a> Checker<'a> {
    pub fn new(model: &'a Model, check_deadlock: bool) -> Checker<'a> {
        let ev = model.ev;
        ev.stats.active.set(true);
        ev.stats.check_deadlock.set(check_deadlock);
        Checker {
            model,
            ev,
            check_deadlock,
            states: vec![],
            parent: vec![],
            level: vec![],
            act: vec![],
            fps: FpSet::new(),
            generated: 0,
            head: 0,
            depth: 0,
            nvars: model.vars.len(),
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

    fn state_less(&self, a: &[Value], b: &[Value]) -> R<bool> {
        for i in 0..a.len() {
            let c = compare(&a[i], &b[i])?;
            if c != Ordering::Equal {
                return Ok(c == Ordering::Less);
            }
        }
        Ok(false)
    }

    pub fn fingerprint(&self, s: &StateRef) -> R<u64> {
        let m = self.model;
        let mut h = Hasher::new();
        let mut canon: Option<Vec<Value>> = None;
        if let Some(sym) = &m.symmetry {
            let base = s.snapshot(self.nvars);
            for p in sym {
                let mut u: Option<Vec<Value>> = None;
                for (i, v) in base.iter().enumerate() {
                    if let Some(x) = permute(v, p)? {
                        u.get_or_insert_with(|| base.clone())[i] = x;
                    }
                }
                if let Some(u) = u {
                    if self.state_less(&u, canon.as_deref().unwrap_or(&base))? {
                        canon = Some(u);
                    }
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
            h.value(&self.ev.eval(view.e, &view.ctx)?)?;
        } else {
            match &canon {
                Some(c) => {
                    for v in c {
                        h.value(v)?;
                    }
                }
                None => s.with(|vals| -> R<()> {
                    for v in &vals[..self.nvars] {
                        h.value(v)?;
                    }
                    Ok(())
                })?,
            }
        }
        Ok(h.finish())
    }

    fn result(&self, status: &'static str) -> CheckResult {
        CheckResult {
            status,
            name: None,
            message: None,
            trace: None,
            generated: self.generated,
            distinct: self.states.len() as u64,
            queue: (self.states.len() - self.head.min(self.states.len())) as u64,
            depth: self.depth,
        }
    }
    fn error(&self, message: String, trace: Option<Vec<TraceStep>>) -> CheckResult {
        let mut r = self.result("error");
        r.message = Some(message);
        r.trace = trace;
        r
    }

    fn trace_to(&self, id: usize) -> Vec<TraceStep> {
        let mut out = vec![];
        let mut i = id as u32;
        loop {
            let a = self.act[i as usize];
            out.push(TraceStep { state: self.states[i as usize].clone(), action: if a >= 0 { Some(a as usize) } else { None } });
            i = self.parent[i as usize];
            if i == NO_PARENT {
                break;
            }
        }
        out.reverse();
        out
    }
    fn trace_plus(&self, sid: usize, t: &StateRef, a: usize) -> Vec<TraceStep> {
        let mut tr = self.trace_to(sid);
        tr.push(TraceStep { state: t.clone(), action: Some(a) });
        tr
    }

    fn eval_pred(&self, p: &Pred, s: &StateRef, t: Option<&StateRef>) -> R<bool> {
        let ev = self.ev;
        ev.set_state(s, t);
        ev.init_mode.set(false);
        ev.prime_depth.set(0);
        ev.call_depth.set(0);
        ev.n_assigned.set(0);
        ev.eval_bool(p.e, &p.ctx)
    }

    fn check_assumptions(&self) -> Option<CheckResult> {
        let ev = self.ev;
        for a in &self.model.root.assumes {
            ev.set_state(&self.empty, None);
            ev.init_mode.set(false);
            let at = loc_str(&a.e.loc, &a.module.to_string());
            match ev.eval(a.e, &None) {
                Err(e) => match *e {
                    Fail::Tla(t) => return Some(self.error(format!("Evaluating assumption {} failed.\n{}", at, t.msg), None)),
                    _ => return Some(self.error(format!("Evaluating assumption {} failed.", at), None)),
                },
                Ok(Value::Bool(true)) => {}
                Ok(Value::Bool(false)) => {
                    let mut r = self.result("assumption");
                    r.message = Some(format!("Assumption {} is false.", at));
                    return Some(r);
                }
                Ok(_) => return Some(self.error(format!("The assumption {} was not a boolean.", at), None)),
            }
        }
        None
    }

    pub fn describe_err(&self, e: &Fail, with_loc: bool) -> String {
        match e {
            Fail::Tla(t) => {
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
            let mut unseen = true;
            let mut id: Option<usize> = None;
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
                    unseen = self.fps.put(fp, nid as u32).is_none();
                    id = Some(nid);
                    if unseen {
                        self.states.push(s.clone());
                        self.parent.push(NO_PARENT);
                        self.level.push(1);
                        self.act.push(-1);
                        self.depth = self.depth.max(1);
                    }
                }
                Ok(())
            })();
            self.sync_stats();
            if let Err(e) = step {
                return Some(self.error(self.describe_err(&e, true), Some(vec![TraceStep { state: s, action: None }])));
            }
            if unseen {
                for inv in &m.invariants {
                    match self.eval_pred(inv, &s, None) {
                        Err(e) => {
                            return Some(self.error(format!("Evaluating invariant {} failed.\n{}", inv.name, self.describe_err(&e, true)), Some(vec![TraceStep { state: s, action: None }])));
                        }
                        Ok(false) => {
                            let mut r = self.result("invariant-init");
                            r.name = Some(inv.name.clone());
                            r.trace = Some(vec![TraceStep { state: s, action: None }]);
                            return Some(r);
                        }
                        Ok(true) => {}
                    }
                }
                for p in &m.implied_inits {
                    match self.eval_pred(p, &s, None) {
                        Err(e) => {
                            return Some(self.error(format!("Evaluating property {} failed.\n{}", p.name, self.describe_err(&e, true)), Some(vec![TraceStep { state: s, action: None }])));
                        }
                        Ok(false) => {
                            let mut r = self.result("implied-init");
                            r.name = Some(p.name.clone());
                            r.trace = Some(vec![TraceStep { state: s, action: None }]);
                            return Some(r);
                        }
                        Ok(true) => {}
                    }
                }
            }
            let _ = id;
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

    pub fn run(&mut self) -> CheckResult {
        let m = self.model;
        if let Some(r) = self.check_assumptions() {
            return r;
        }
        if let Some(r) = self.compute_init() {
            return r;
        }
        let mut succs: Vec<StateRef> = vec![];
        let mut succ_act: Vec<u32> = vec![];
        if m.actions.is_empty() || m.inits.is_empty() {
            return self.result("ok");
        }
        let ev = self.ev;
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
                        r
                    }
                    ref other => self.error(self.describe_err(other, true), Some(self.trace_to(sid))),
                };
            }
            let extra = ev.extra_generated.replace(0);
            self.generated += extra;
            for i in 0..succs.len() {
                let t = succs[i].clone();
                let ai = succ_act[i] as usize;
                self.generated += 1;
                ev.stats.generated.set(self.generated as i64);
                let mut in_model = true;
                let mut unseen = true;
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
                        if self.fps.put(fp, nid as u32).is_none() {
                            self.states.push(t.clone());
                            self.parent.push(sid as u32);
                            self.level.push(lvl + 1);
                            self.act.push(ai as i32);
                            if lvl + 1 > self.depth {
                                self.depth = lvl + 1;
                                ev.stats.diameter.set(self.depth as i64);
                            }
                            ev.stats.distinct.set(self.states.len() as i64);
                            ev.stats.queue.set(self.states.len() as i64 - self.head as i64);
                        } else {
                            unseen = false;
                        }
                    }
                    Ok(())
                })();
                if let Err(e) = step {
                    return self.error(self.describe_err(&e, true), Some(self.trace_plus(sid, &t, ai)));
                }
                if unseen {
                    for inv in &m.invariants {
                        match self.eval_pred(inv, &t, None) {
                            Err(e) => {
                                return self.error(format!("Evaluating invariant {} failed.\n{}", inv.name, self.describe_err(&e, false)), Some(self.trace_plus(sid, &t, ai)));
                            }
                            Ok(false) => {
                                let mut r = self.result("invariant");
                                r.name = Some(inv.name.clone());
                                r.trace = Some(self.trace_plus(sid, &t, ai));
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
                            return self.error(format!("Evaluating action property {} failed.\n{}", p.name, self.describe_err(&e, true)), Some(self.trace_plus(sid, &t, ai)));
                        }
                        Ok(false) => {
                            let mut r = self.result("action-property");
                            r.name = Some(p.name.clone());
                            r.trace = Some(self.trace_plus(sid, &t, ai));
                            if in_model && unseen {
                                r.queue = r.queue.saturating_sub(1);
                            }
                            return r;
                        }
                        Ok(true) => {}
                    }
                }
            }
            if succs.is_empty() && self.check_deadlock {
                let mut r = self.result("deadlock");
                r.trace = Some(self.trace_to(sid));
                return r;
            }
        }
        self.sync_stats();
        self.result("ok")
    }
}

/// Runs the checker and, on success, the POSTCONDITIONs.
pub fn model_check(model: &Model, check_deadlock: bool) -> CheckResult {
    let mut checker = Checker::new(model, check_deadlock);
    let mut result = checker.run();
    if result.status == "ok" {
        let ev = model.ev;
        for pc in &model.postconditions {
            let at = format!("{} at {}", pc.pred.name, loc_str(&pc.loc, &pc.module));
            ev.set_state(&StateData::blank(0), None);
            ev.init_mode.set(false);
            ev.prime_depth.set(0);
            ev.call_depth.set(0);
            match ev.eval(pc.pred.e, &pc.pred.ctx) {
                Err(e) => {
                    let msg = match &*e {
                        Fail::Tla(t) => t.msg.clone(),
                        _ => String::new(),
                    };
                    result = checker.error(format!("Evaluating postcondition {} failed.\n{}", at, msg), None);
                    break;
                }
                Ok(Value::Bool(true)) => {}
                Ok(_) => {
                    result = checker.error(format!("Postcondition {} is false.", at), None);
                    break;
                }
            }
        }
    }
    result
}
