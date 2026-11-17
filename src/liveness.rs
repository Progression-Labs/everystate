//! Liveness checking (port of liveness.ts): temporal formula normalisation, tableau construction, and
//! SCC search over the product of the state graph and the tableau (same approach as TLC: possible
//! error models made of []<> (AE) and <>[] (EA) constraints plus a particle tableau for the rest).
use crate::ast::*;
use crate::checker::*;
use crate::eval::*;
use crate::intern::*;
use crate::model::*;
use crate::value::Value;
use std::collections::HashMap;
use std::rc::Rc;

// ---- live expressions ----
enum LE {
    Bool(bool),
    Atom { id: usize, lvl: u8 },
    Not(L, u8),
    And(Vec<L>, u8),
    Or(Vec<L>, u8),
    Always(L),
    Eventually(L),
}
type L = Rc<LE>;

fn lvl(x: &LE) -> u8 {
    match x {
        LE::Bool(_) => 0,
        LE::Atom { lvl, .. } | LE::Not(_, lvl) | LE::And(_, lvl) | LE::Or(_, lvl) => *lvl,
        LE::Always(_) | LE::Eventually(_) => 3,
    }
}
fn mk_bool(b: bool) -> L {
    Rc::new(LE::Bool(b))
}
fn mk_not(a: &L) -> L {
    match &**a {
        LE::Bool(v) => mk_bool(!v),
        LE::Not(x, _) => x.clone(),
        _ => Rc::new(LE::Not(a.clone(), lvl(a))),
    }
}
fn mk_junc(and: bool, items: Vec<L>) -> L {
    let mut out: Vec<L> = vec![];
    for x in items {
        match &*x {
            LE::Bool(v) => {
                if *v == !and {
                    return x; // TRUE in or / FALSE in and
                }
            }
            LE::And(xs, _) if and => out.extend(xs.iter().cloned()),
            LE::Or(xs, _) if !and => out.extend(xs.iter().cloned()),
            _ => out.push(x),
        }
    }
    if out.is_empty() {
        return mk_bool(and);
    }
    if out.len() == 1 {
        return out.pop().unwrap();
    }
    let l = out.iter().map(|x| lvl(x)).max().unwrap();
    Rc::new(if and { LE::And(out, l) } else { LE::Or(out, l) })
}

enum AtomKind {
    Expr(N),
    /// <<A>>_v built from WF_v(A) / SF_v(A)
    Angle(N, N),
    EnabledAngle(N, N),
}
struct Atom {
    kind: AtomKind,
    ctx: C,
}

struct Pem {
    ae_state: Vec<L>,
    ae_action: Vec<L>,
    ea: Vec<L>,
}
struct Group {
    tf: L,
    pems: Vec<Pem>,
}

struct Part {
    preds: Vec<L>,
    succ: Vec<usize>,
    // insertion-ordered sets (JS Set semantics): the order decides the numbering of particles
    set: Vec<usize>,
    next: Vec<usize>,
}
struct Tableau {
    init: Vec<usize>,
    parts: Vec<Part>,
    promises: Vec<(usize, usize)>, // (eventually formula, its body)
}

fn config_err<T>(msg: String) -> R<T> {
    err("config", msg)
}

pub struct Liveness<'a, 'b> {
    model: &'a Model,
    checker: &'b Checker<'a>,
    atom_ids: HashMap<(usize, usize), usize>,
    atoms: Vec<Atom>,
    /// TLC does not fold constants through temporal operators when it decides whether a property is a
    /// tautology ([]TRUE stays a temporal formula); switched off for that test only.
    fold_temporal: bool,
    // graph
    s: usize,
    e_start: Vec<u32>,
    e_to: Vec<u32>,
    e_act: Vec<i32>,
    e_state: Option<Vec<Option<StateRef>>>,
    state_cache: HashMap<usize, Vec<u8>>,
    edge_cache: HashMap<usize, Vec<u8>>,
    groups: Option<Vec<Group>>,
    pub tautology: bool,
}

impl<'a, 'b> Liveness<'a, 'b> {
    pub fn new(model: &'a Model, checker: &'b Checker<'a>) -> Self {
        Liveness {
            model,
            checker,
            atom_ids: HashMap::new(),
            atoms: vec![],
            fold_temporal: true,
            s: 0,
            e_start: vec![],
            e_to: vec![],
            e_act: vec![],
            e_state: None,
            state_cache: HashMap::new(),
            edge_cache: HashMap::new(),
            groups: None,
            tautology: false,
        }
    }

    fn mk_always(&self, a: L) -> L {
        if matches!(&*a, LE::Bool(_)) && self.fold_temporal { a } else { Rc::new(LE::Always(a)) }
    }
    fn mk_eventually(&self, a: L) -> L {
        if matches!(&*a, LE::Bool(_)) && self.fold_temporal { a } else { Rc::new(LE::Eventually(a)) }
    }

    fn atom(&mut self, e: N, ctx: &C, l: i8) -> L {
        let key = (e as *const Node as usize, ctx.as_ref().map_or(0, |c| Rc::as_ptr(c) as usize));
        let id = match self.atom_ids.get(&key) {
            Some(id) => *id,
            None => {
                let id = self.atoms.len();
                self.atom_ids.insert(key, id);
                self.atoms.push(Atom { kind: AtomKind::Expr(e), ctx: ctx.clone() });
                id
            }
        };
        Rc::new(LE::Atom { id, lvl: (l.max(1)) as u8 })
    }
    fn fresh_atom(&mut self, kind: AtomKind, ctx: &C, l: u8) -> L {
        let id = self.atoms.len();
        self.atoms.push(Atom { kind, ctx: ctx.clone() });
        Rc::new(LE::Atom { id, lvl: l })
    }

    fn const_eval(&self, e: N, ctx: &C) -> Option<bool> {
        let ev = self.model.ev;
        ev.set_state(&StateData::blank(0), None);
        ev.init_mode.set(false);
        match ev.eval(e, ctx) {
            Ok(Value::Bool(b)) => Some(b),
            _ => None,
        }
    }

    fn to_live(&mut self, e: N, ctx: &C) -> R<L> {
        check_stack()?;
        let ev = self.model.ev;
        let l = expr_level(ev, e, ctx);
        if l == 0 {
            if let Some(v) = self.const_eval(e, ctx) {
                return Ok(mk_bool(v));
            }
            return Ok(self.atom(e, ctx, 1));
        }
        if l <= 2 {
            return Ok(self.atom(e, ctx, l));
        }
        match &e.e {
            E::App { .. } => {
                if let Some((b, c)) = ev.expand_app(e, ctx)? {
                    return self.to_live(b, &c);
                }
            }
            E::Let { defs, body } => return self.to_live(body, &ev.bind_let(defs, ctx)),
            E::Quant { forall, bounds, body } => {
                let mut ctxs: Vec<C> = vec![];
                ev.set_state(&StateData::blank(0), None);
                ev.for_bindings(bounds, ctx, &mut |c| {
                    ctxs.push(c.clone());
                    Ok(false)
                })?;
                let mut parts = vec![];
                for c in &ctxs {
                    parts.push(self.to_live(body, c)?);
                }
                return Ok(mk_junc(*forall, parts));
            }
            E::Op(k, a) => match k {
                K::And | K::Or => {
                    let mut parts = vec![];
                    for x in a {
                        parts.push(self.to_live(x, ctx)?);
                    }
                    return Ok(mk_junc(*k == K::And, parts));
                }
                K::Not => return Ok(mk_not(&self.to_live(&a[0], ctx)?)),
                K::Imp => {
                    let x = mk_not(&self.to_live(&a[0], ctx)?);
                    let y = self.to_live(&a[1], ctx)?;
                    return Ok(mk_junc(false, vec![x, y]));
                }
                K::Eqv => {
                    let (x, y) = (self.to_live(&a[0], ctx)?, self.to_live(&a[1], ctx)?);
                    return Ok(mk_junc(false, vec![mk_junc(true, vec![x.clone(), y.clone()]), mk_junc(true, vec![mk_not(&x), mk_not(&y)])]));
                }
                K::If => {
                    if expr_level(ev, &a[0], ctx) == 0 {
                        // constant guard: translate only the chosen branch (lets recursive temporal operators terminate)
                        if let Some(gv) = self.const_eval(&a[0], ctx) {
                            return self.to_live(if gv { &a[1] } else { &a[2] }, ctx);
                        }
                    }
                    let g = self.to_live(&a[0], ctx)?;
                    let t = self.to_live(&a[1], ctx)?;
                    let f = self.to_live(&a[2], ctx)?;
                    return Ok(mk_junc(false, vec![mk_junc(true, vec![g.clone(), t]), mk_junc(true, vec![mk_not(&g), f])]));
                }
                K::Always => {
                    let x = self.to_live(&a[0], ctx)?;
                    return Ok(self.mk_always(x));
                }
                K::Eventually => {
                    let x = self.to_live(&a[0], ctx)?;
                    return Ok(self.mk_eventually(x));
                }
                K::LeadsTo => {
                    let x = mk_not(&self.to_live(&a[0], ctx)?);
                    let y = self.to_live(&a[1], ctx)?;
                    let y = self.mk_eventually(y);
                    return Ok(self.mk_always(mk_junc(false, vec![x, y])));
                }
                K::Wf | K::Sf => {
                    let en = self.fresh_atom(AtomKind::EnabledAngle(&a[1], &a[0]), ctx, 1);
                    let act = self.fresh_atom(AtomKind::Angle(&a[1], &a[0]), ctx, 2);
                    if *k == K::Wf {
                        let x = self.mk_eventually(mk_junc(false, vec![mk_not(&en), act]));
                        return Ok(self.mk_always(x));
                    }
                    let x = self.mk_always(mk_not(&en));
                    let x = self.mk_eventually(x);
                    let y = self.mk_eventually(act);
                    let y = self.mk_always(y);
                    return Ok(mk_junc(false, vec![x, y]));
                }
                _ => {}
            },
            _ => {}
        }
        config_err(format!(
            "TLC cannot handle the temporal formula at line {}, col {} to line {}, col {} of module {}",
            e.loc[0],
            e.loc[1],
            e.loc[2],
            e.loc[3],
            e.module_str().unwrap_or_else(|| "?".into())
        ))
    }

    // Push negations inward; non-temporal subtrees stay as (possibly negated) predicates.
    fn push_neg(&self, x: &L, neg: bool) -> L {
        if lvl(x) <= 2 {
            return if neg { mk_not(x) } else { x.clone() };
        }
        match &**x {
            LE::Not(a, _) => self.push_neg(a, !neg),
            LE::And(xs, _) | LE::Or(xs, _) => {
                let is_and = matches!(&**x, LE::And(..));
                mk_junc(is_and != neg, xs.iter().map(|y| self.push_neg(y, neg)).collect())
            }
            LE::Always(a) => {
                if neg {
                    self.mk_eventually(self.push_neg(a, true))
                } else {
                    self.mk_always(self.push_neg(a, false))
                }
            }
            LE::Eventually(a) => {
                if neg {
                    self.mk_always(self.push_neg(a, true))
                } else {
                    self.mk_eventually(self.push_neg(a, false))
                }
            }
            _ => x.clone(),
        }
    }

    fn simp(&self, x: &L) -> L {
        if lvl(x) <= 2 {
            return x.clone();
        }
        match &**x {
            LE::And(xs, _) => mk_junc(true, xs.iter().map(|y| self.simp(y)).collect()),
            LE::Or(xs, _) => mk_junc(false, xs.iter().map(|y| self.simp(y)).collect()),
            LE::Always(a0) => {
                let a = self.simp(a0);
                match &*a {
                    LE::Always(_) => return a,
                    LE::And(ys, 3) => return mk_junc(true, ys.iter().map(|y| self.simp(&self.mk_always(y.clone()))).collect()),
                    LE::Eventually(b) => match &**b {
                        LE::Always(_) => return a, // []<>[]p = <>[]p
                        LE::Or(ys, 3) => return mk_junc(false, ys.iter().map(|y| self.simp(&self.mk_always(self.mk_eventually(y.clone())))).collect()),
                        _ => {}
                    },
                    _ => {}
                }
                self.mk_always(a)
            }
            LE::Eventually(a0) => {
                let a = self.simp(a0);
                match &*a {
                    LE::Eventually(_) => return a,
                    LE::Or(ys, 3) => return mk_junc(false, ys.iter().map(|y| self.simp(&self.mk_eventually(y.clone()))).collect()),
                    LE::Always(b) => match &**b {
                        LE::Eventually(_) => return a, // <>[]<>p = []<>p
                        LE::And(ys, 3) => return mk_junc(true, ys.iter().map(|y| self.simp(&self.mk_eventually(self.mk_always(y.clone())))).collect()),
                        _ => {}
                    },
                    _ => {}
                }
                self.mk_eventually(a)
            }
            _ => x.clone(),
        }
    }

    fn dnf(&self, x: &L) -> R<Vec<Vec<L>>> {
        match &**x {
            LE::Or(xs, 3) => {
                let mut out = vec![];
                for y in xs {
                    out.extend(self.dnf(y)?);
                }
                Ok(out)
            }
            LE::And(xs, 3) => {
                let mut acc: Vec<Vec<L>> = vec![vec![]];
                for y in xs {
                    let d = self.dnf(y)?;
                    let mut next = Vec::with_capacity(acc.len() * d.len());
                    for a in &acc {
                        for b in &d {
                            let mut v = a.clone();
                            v.extend(b.iter().cloned());
                            next.push(v);
                        }
                    }
                    acc = next;
                    if acc.len() > 100000 {
                        return config_err("The temporal formula is too large to check (DNF blow-up).".into());
                    }
                }
                Ok(acc)
            }
            LE::Bool(v) => Ok(if *v { vec![vec![]] } else { vec![] }),
            _ => Ok(vec![vec![x.clone()]]),
        }
    }

    fn key(&self, x: &LE) -> String {
        match x {
            LE::Bool(v) => (if *v { "T" } else { "F" }).to_string(),
            LE::Atom { id, .. } => format!("a{}", id),
            LE::Not(a, _) => format!("!{}", self.key(a)),
            LE::Always(a) => format!("[]{}", self.key(a)),
            LE::Eventually(a) => format!("<>{}", self.key(a)),
            LE::And(xs, _) => format!("&({})", xs.iter().map(|y| self.key(y)).collect::<Vec<_>>().join(",")),
            LE::Or(xs, _) => format!("|({})", xs.iter().map(|y| self.key(y)).collect::<Vec<_>>().join(",")),
        }
    }

    // ---- graph ----
    fn build_graph(&mut self) {
        let c = self.checker;
        let s_count = c.states.len();
        self.s = s_count;
        let mut e_count = s_count;
        for i in 0..s_count {
            e_count += c.succ[i].len();
        }
        let with_states = c.succ_state.is_some();
        let mut e_state: Vec<Option<StateRef>> = vec![];
        self.e_start = Vec::with_capacity(s_count + 1);
        self.e_to = Vec::with_capacity(e_count);
        self.e_act = Vec::with_capacity(e_count);
        for i in 0..s_count {
            self.e_start.push(self.e_to.len() as u32);
            let (su, sa) = (&c.succ[i], &c.succ_act[i]);
            let mut seen: Vec<u32> = Vec::with_capacity(su.len());
            let real = c.succ_state.as_ref().map(|ss| &ss[i]);
            for j in 0..su.len() {
                if real.is_none() && seen.contains(&su[j]) {
                    continue;
                }
                seen.push(su[j]);
                if let Some(r) = real {
                    e_state.push(Some(r[j].clone()));
                }
                self.e_to.push(su[j]);
                self.e_act.push(sa[j] as i32);
            }
            if !seen.contains(&(i as u32)) || real.is_some() {
                // stuttering self-loop
                if with_states {
                    e_state.push(None);
                }
                self.e_to.push(i as u32);
                self.e_act.push(-1);
            }
        }
        self.e_start.push(self.e_to.len() as u32);
        if with_states {
            self.e_state = Some(e_state);
        }
    }

    fn eval_atom(&self, id: usize, s: &StateRef, t: Option<&StateRef>) -> R<bool> {
        let a = &self.atoms[id];
        let c = self.checker;
        match &a.kind {
            AtomKind::Expr(e) => c.eval_pred_at(e, &a.ctx, s, t),
            AtomKind::Angle(act, v) => {
                // prepare the evaluator exactly as for a predicate, then evaluate <<A>>_v
                self.prime(s, t);
                c.ev.eval_angle(act, v, &a.ctx)
            }
            AtomKind::EnabledAngle(act, v) => {
                self.prime(s, t);
                c.ev.enabled_angle(act, v, &a.ctx)
            }
        }
    }
    fn prime(&self, s: &StateRef, t: Option<&StateRef>) {
        let ev = self.checker.ev;
        ev.set_state(s, t);
        ev.init_mode.set(false);
        ev.prime_depth.set(0);
        ev.call_depth.set(0);
        ev.n_assigned.set(0);
    }

    // Evaluate a non-temporal live expression at a state (and, for action level, along edge `e`).
    fn eval_le(&mut self, x: &LE, s: usize, e: i64) -> R<bool> {
        match x {
            LE::Bool(v) => Ok(*v),
            LE::Not(a, _) => Ok(!self.eval_le(a, s, e)?),
            LE::And(xs, _) => {
                for y in xs {
                    if !self.eval_le(y, s, e)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            LE::Or(xs, _) => {
                for y in xs {
                    if self.eval_le(y, s, e)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            LE::Atom { id, lvl } => {
                let c = self.checker;
                if *lvl <= 1 {
                    let n = self.s;
                    let hit = self.state_cache.entry(*id).or_insert_with(|| vec![0; n])[s];
                    if hit != 0 {
                        return Ok(hit == 2);
                    }
                    let v = self.eval_atom(*id, &c.states[s], None)?;
                    self.state_cache.get_mut(id).unwrap()[s] = if v { 2 } else { 1 };
                    return Ok(v);
                }
                if e < 0 {
                    return config_err("TLC cannot handle a temporal formula with an action in a state-level position.".into());
                }
                let e = e as usize;
                let n = self.e_to.len();
                let hit = self.edge_cache.entry(*id).or_insert_with(|| vec![0; n])[e];
                if hit != 0 {
                    return Ok(hit == 2);
                }
                let next = match self.e_state.as_ref().and_then(|es| es[e].clone()) {
                    Some(t) => t,
                    None => c.states[self.e_to[e] as usize].clone(),
                };
                let v = self.eval_atom(*id, &c.states[s], Some(&next))?;
                self.edge_cache.get_mut(id).unwrap()[e] = if v { 2 } else { 1 };
                Ok(v)
            }
            _ => err("error", "temporal operator in evalLE".into()),
        }
    }

    fn has_action(&self, x: &LE) -> bool {
        match x {
            LE::Atom { lvl, .. } => *lvl == 2,
            LE::Not(a, _) | LE::Always(a) | LE::Eventually(a) => self.has_action(a),
            LE::And(xs, _) | LE::Or(xs, _) => xs.iter().any(|y| self.has_action(y)),
            LE::Bool(_) => false,
        }
    }

    fn whole_formula(&mut self) -> R<L> {
        let m = self.model;
        let mut fair = vec![];
        for f in &m.fairness {
            fair.push(self.to_live(f.e, &f.ctx)?);
        }
        let fair = mk_junc(true, fair);
        let mut props = vec![];
        for p in &m.live_props {
            props.push(self.to_live(p.e, &p.ctx)?);
        }
        Ok(mk_junc(true, vec![fair, mk_junc(false, props.iter().map(mk_not).collect())]))
    }

    /// Normalise the temporal formulas; returns the number of tableau branches (0 = nothing to check).
    pub fn prepare(&mut self) -> R<usize> {
        let mut groups: Vec<Group> = vec![];
        let mut index: HashMap<String, usize> = HashMap::new();
        if self.model.live_props.is_empty() {
            self.groups = Some(groups);
            return Ok(0);
        }
        self.groups = Some(vec![]);
        let formula = self.whole_formula()?;
        let nf = self.simp(&self.push_neg(&formula, false));
        let disjuncts = self.dnf(&nf)?;
        for d in disjuncts {
            let mut pem = Pem { ae_state: vec![], ae_action: vec![], ea: vec![] };
            let mut tfs: Vec<L> = vec![];
            for c in d {
                let mut handled = false;
                match &*c {
                    LE::Always(a) => {
                        if let LE::Eventually(b) = &**a {
                            if lvl(b) <= 2 {
                                if lvl(b) <= 1 {
                                    pem.ae_state.push(b.clone());
                                } else {
                                    pem.ae_action.push(b.clone());
                                }
                                handled = true;
                            }
                        }
                    }
                    LE::Eventually(a) => {
                        if let LE::Always(b) = &**a {
                            if lvl(b) <= 2 {
                                pem.ea.push(b.clone());
                                handled = true;
                            }
                        }
                    }
                    _ => {}
                }
                if !handled {
                    if self.has_action(&c) {
                        return config_err("TLC cannot handle the temporal formula: an action appears outside of a []<> or <>[] context.".into());
                    }
                    tfs.push(c);
                }
            }
            let tf = mk_junc(true, tfs);
            let k = self.key(&tf);
            let gi = *index.entry(k).or_insert_with(|| {
                groups.push(Group { tf: tf.clone(), pems: vec![] });
                groups.len() - 1
            });
            groups[gi].pems.push(pem);
        }
        if groups.is_empty() {
            self.fold_temporal = false;
            let f2 = self.whole_formula();
            self.fold_temporal = true;
            self.tautology = matches!(&*f2?, LE::Bool(false));
        }
        let n = groups.len();
        self.groups = Some(groups);
        Ok(n)
    }

    pub fn check(&mut self) -> R<Option<CheckResult>> {
        if self.groups.is_none() {
            self.prepare()?;
        }
        let groups = self.groups.take().unwrap();
        if groups.is_empty() {
            return Ok(None);
        }
        self.build_graph();
        for g in &groups {
            if let Some(r) = self.check_group(&g.tf, &g.pems)? {
                return Ok(Some(r));
            }
        }
        Ok(None)
    }

    // ---- tableau ----
    fn build_tableau(&self, tf: &L) -> R<Tableau> {
        #[derive(PartialEq, Clone, Copy)]
        enum Kind {
            Pred,
            And,
            Or,
            Always,
            Eventually,
        }
        struct Form {
            le: L,
            kind: Kind,
            kids: Vec<usize>,
        }
        struct Interner<'x, 'a, 'b> {
            ids: HashMap<String, usize>,
            forms: Vec<Form>,
            lv: &'x Liveness<'a, 'b>,
        }
        impl Interner<'_, '_, '_> {
            fn intern(&mut self, x: &L) -> usize {
                let k = self.lv.key(x);
                if let Some(id) = self.ids.get(&k) {
                    return *id;
                }
                let id = self.forms.len();
                self.ids.insert(k, id);
                self.forms.push(Form { le: x.clone(), kind: Kind::Pred, kids: vec![] });
                if lvl(x) == 3 {
                    match &**x {
                        LE::And(xs, _) | LE::Or(xs, _) => {
                            let kids: Vec<usize> = xs.iter().map(|y| self.intern(y)).collect();
                            self.forms[id].kind = if matches!(&**x, LE::And(..)) { Kind::And } else { Kind::Or };
                            self.forms[id].kids = kids;
                        }
                        LE::Always(a) | LE::Eventually(a) => {
                            let kid = self.intern(a);
                            self.forms[id].kind = if matches!(&**x, LE::Always(_)) { Kind::Always } else { Kind::Eventually };
                            self.forms[id].kids = vec![kid];
                        }
                        _ => {}
                    }
                }
                id
            }
        }
        let mut it = Interner { ids: HashMap::new(), forms: vec![], lv: self };
        let root = it.intern(tf);
        let forms = it.forms;
        let mut promises = vec![];
        for (i, f) in forms.iter().enumerate() {
            if f.kind == Kind::Eventually {
                promises.push((i, f.kids[0]));
            }
        }
        // particles: closed sets of formula ids plus the set of formulas required in the next state
        type P = (Vec<usize>, Vec<usize>);
        fn plus(v: &[usize], f: usize) -> Vec<usize> {
            let mut o = v.to_vec();
            if !o.contains(&f) {
                o.push(f);
            }
            o
        }
        fn rec(forms: &[Form], todo: &[usize], set: Vec<usize>, next: Vec<usize>, out: &mut Vec<P>) {
            let f = match todo.last() {
                None => {
                    out.push((set, next));
                    return;
                }
                Some(f) => *f,
            };
            let rest = &todo[..todo.len() - 1];
            if set.contains(&f) {
                rec(forms, rest, set, next, out);
                return;
            }
            let s2 = plus(&set, f);
            let ff = &forms[f];
            let with = |extra: &[usize]| -> Vec<usize> {
                let mut v = rest.to_vec();
                v.extend_from_slice(extra);
                v
            };
            match ff.kind {
                Kind::Pred => rec(forms, rest, s2, next, out),
                Kind::And => rec(forms, &with(&ff.kids), s2, next, out),
                Kind::Or => {
                    for k in &ff.kids {
                        rec(forms, &with(&[*k]), s2.clone(), next.clone(), out);
                    }
                }
                Kind::Always => {
                    let n2 = plus(&next, f);
                    rec(forms, &with(&[ff.kids[0]]), s2, n2, out);
                }
                Kind::Eventually => {
                    rec(forms, &with(&[ff.kids[0]]), s2.clone(), next.clone(), out);
                    let n2 = plus(&next, f);
                    rec(forms, rest, s2, n2, out);
                }
            }
        }
        let cover = |start: &[usize]| -> Vec<P> {
            let mut out = vec![];
            rec(&forms, start, Vec::new(), Vec::new(), &mut out);
            out
        };
        let mut part_ids: HashMap<P, usize> = HashMap::new();
        let mut parts: Vec<Part> = vec![];
        let mut add = |p: P, parts: &mut Vec<Part>| -> usize {
            let mut key = p.clone();
            key.0.sort_unstable();
            key.1.sort_unstable();
            if let Some(id) = part_ids.get(&key) {
                return *id;
            }
            let id = parts.len();
            let preds = p.0.iter().filter(|f| forms[**f].kind == Kind::Pred).map(|f| forms[*f].le.clone()).collect();
            parts.push(Part { preds, succ: vec![], set: p.0, next: p.1 });
            part_ids.insert(key, id);
            id
        };
        let dedup = |v: Vec<usize>| -> Vec<usize> {
            let mut out: Vec<usize> = vec![];
            for x in v {
                if !out.contains(&x) {
                    out.push(x);
                }
            }
            out
        };
        // the todo list is consumed from its end, so the start list is given in insertion order
        let init = dedup(cover(&[root]).into_iter().map(|p| add(p, &mut parts)).collect());
        let mut i = 0;
        while i < parts.len() {
            let start: Vec<usize> = parts[i].next.clone();
            let succ = dedup(cover(&start).into_iter().map(|p| add(p, &mut parts)).collect());
            parts[i].succ = succ;
            if parts.len() > 20000 {
                return config_err("The temporal formula is too large to check (tableau blow-up).".into());
            }
            i += 1;
        }
        Ok(Tableau { init, parts, promises })
    }

    fn check_group(&mut self, tf: &L, pems: &[Pem]) -> R<Option<CheckResult>> {
        let c = self.checker;
        let tb = self.build_tableau(tf)?;
        let p_count = tb.parts.len();
        let s_count = self.s;
        // product nodes: reachable (state, particle) pairs
        let mut node_id: HashMap<u64, u32> = HashMap::new();
        let mut n_state: Vec<u32> = vec![];
        let mut n_part: Vec<u32> = vec![];
        let mut adj: Vec<Vec<u32>> = vec![];
        let mut adj_edge: Vec<Vec<u32>> = vec![];
        let mut cons_cache: Vec<u8> = vec![0; s_count * p_count];
        macro_rules! cons {
            ($s:expr, $p:expr) => {{
                let k = $s * p_count + $p;
                if cons_cache[k] == 0 {
                    let mut ok = true;
                    for pr in &tb.parts[$p].preds {
                        if !self.eval_le(pr, $s, -1)? {
                            ok = false;
                            break;
                        }
                    }
                    cons_cache[k] = if ok { 2 } else { 1 };
                }
                cons_cache[k] == 2
            }};
        }
        macro_rules! get_node {
            ($s:expr, $p:expr) => {{
                let k = ($s * p_count + $p) as u64;
                match node_id.get(&k) {
                    Some(id) => *id,
                    None => {
                        let id = n_state.len() as u32;
                        node_id.insert(k, id);
                        n_state.push($s as u32);
                        n_part.push($p as u32);
                        adj.push(vec![]);
                        adj_edge.push(vec![]);
                        id
                    }
                }
            }};
        }
        let mut init_nodes: Vec<u32> = vec![];
        for &s in &c.inits {
            for &p in &tb.init {
                if cons!(s as usize, p) {
                    init_nodes.push(get_node!(s as usize, p));
                }
            }
        }
        let mut n = 0;
        while n < n_state.len() {
            let (s, p) = (n_state[n] as usize, n_part[n] as usize);
            for e in self.e_start[s]..self.e_start[s + 1] {
                let t = self.e_to[e as usize] as usize;
                for &q in &tb.parts[p].succ {
                    if !cons!(t, q) {
                        continue;
                    }
                    let id = get_node!(t, q);
                    adj[n].push(id);
                    adj_edge[n].push(e);
                }
            }
            n += 1;
        }
        let n_count = n_state.len();
        // group PEMs by their EA constraints
        let mut by_ea: Vec<(String, Vec<usize>)> = vec![];
        for (pi, pem) in pems.iter().enumerate() {
            let mut ks: Vec<String> = pem.ea.iter().map(|x| self.key(x)).collect();
            ks.sort();
            let k = ks.join(";");
            match by_ea.iter_mut().find(|g| g.0 == k) {
                Some(g) => g.1.push(pi),
                None => by_ea.push((k, vec![pi])),
            }
        }
        for (_, pem_ids) in &by_ea {
            let ea: &[L] = &pems[pem_ids[0]].ea;
            // iterative Tarjan
            let mut index: Vec<i32> = vec![-1; n_count];
            let mut low: Vec<i32> = vec![0; n_count];
            let mut on_stack: Vec<bool> = vec![false; n_count];
            let mut comp: Vec<i32> = vec![-1; n_count];
            let mut stack: Vec<u32> = vec![];
            let (mut idx, mut ncomp) = (0i32, 0i32);
            let mut call_n: Vec<u32> = vec![];
            let mut call_j: Vec<usize> = vec![];
            for root in 0..n_count {
                if index[root] != -1 {
                    continue;
                }
                call_n.push(root as u32);
                call_j.push(0);
                index[root] = idx;
                low[root] = idx;
                idx += 1;
                stack.push(root as u32);
                on_stack[root] = true;
                while let Some(&nn) = call_n.last() {
                    let n = nn as usize;
                    let mut j = *call_j.last().unwrap();
                    let mut pushed = false;
                    while j < adj[n].len() {
                        let w = adj[n][j] as usize;
                        if !self.edge_ok(ea, &n_state, &adj_edge, n, j)? {
                            j += 1;
                            continue;
                        }
                        if index[w] == -1 {
                            *call_j.last_mut().unwrap() = j + 1;
                            index[w] = idx;
                            low[w] = idx;
                            idx += 1;
                            stack.push(w as u32);
                            on_stack[w] = true;
                            call_n.push(w as u32);
                            call_j.push(0);
                            pushed = true;
                            break;
                        }
                        if on_stack[w] && index[w] < low[n] {
                            low[n] = index[w];
                        }
                        j += 1;
                    }
                    if pushed {
                        continue;
                    }
                    call_n.pop();
                    call_j.pop();
                    if let Some(&par) = call_n.last() {
                        if low[n] < low[par as usize] {
                            low[par as usize] = low[n];
                        }
                    }
                    if low[n] == index[n] {
                        let mut members: Vec<u32> = vec![];
                        loop {
                            let w = stack.pop().unwrap();
                            on_stack[w as usize] = false;
                            comp[w as usize] = ncomp;
                            members.push(w);
                            if w as usize == n {
                                break;
                            }
                        }
                        let g = Graph { comp: &comp, cid: ncomp, n_state: &n_state, n_part: &n_part, adj: &adj, adj_edge: &adj_edge, init_nodes: &init_nodes, ea };
                        let r = self.check_component(&members, pems, pem_ids, &tb, &g)?;
                        ncomp += 1;
                        if r.is_some() {
                            return Ok(r);
                        }
                    }
                }
            }
        }
        Ok(None)
    }

    fn edge_ok(&mut self, ea: &[L], n_state: &[u32], adj_edge: &[Vec<u32>], n: usize, j: usize) -> R<bool> {
        for x in ea {
            if !self.eval_le(x, n_state[n] as usize, adj_edge[n][j] as i64)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn check_component(&mut self, members: &[u32], pems: &[Pem], pem_ids: &[usize], tb: &Tableau, g: &Graph) -> R<Option<CheckResult>> {
        // must contain at least one internal edge
        let mut has_edge = false;
        'outer: for &n in members {
            let n = n as usize;
            for j in 0..g.adj[n].len() {
                if g.comp[g.adj[n][j] as usize] == g.cid && self.edge_ok(g.ea, g.n_state, g.adj_edge, n, j)? {
                    has_edge = true;
                    break 'outer;
                }
            }
        }
        if !has_edge {
            return Ok(None);
        }
        // promises
        let mut promise_nodes: Vec<u32> = vec![];
        for (pev, pbody) in &tb.promises {
            let mut found: Option<u32> = None;
            for &n in members {
                let set = &tb.parts[g.n_part[n as usize] as usize].set;
                if !set.contains(pev) || set.contains(pbody) {
                    found = Some(n);
                    break;
                }
            }
            match found {
                None => return Ok(None),
                Some(n) => promise_nodes.push(n),
            }
        }
        for &pi in pem_ids {
            let pem = &pems[pi];
            let mut targets: Vec<(u32, i64)> = promise_nodes.iter().map(|n| (*n, -1)).collect();
            let mut ok = true;
            for x in &pem.ae_state {
                let mut found: Option<u32> = None;
                for &n in members {
                    if self.eval_le(x, g.n_state[n as usize] as usize, -1)? {
                        found = Some(n);
                        break;
                    }
                }
                match found {
                    None => {
                        ok = false;
                        break;
                    }
                    Some(n) => targets.push((n, -1)),
                }
            }
            if !ok {
                continue;
            }
            for x in &pem.ae_action {
                let mut found: Option<(u32, i64)> = None;
                'find: for &n in members {
                    let nu = n as usize;
                    for j in 0..g.adj[nu].len() {
                        if g.comp[g.adj[nu][j] as usize] == g.cid
                            && self.edge_ok(g.ea, g.n_state, g.adj_edge, nu, j)?
                            && self.eval_le(x, g.n_state[nu] as usize, g.adj_edge[nu][j] as i64)?
                        {
                            found = Some((n, j as i64));
                            break 'find;
                        }
                    }
                }
                match found {
                    None => {
                        ok = false;
                        break;
                    }
                    Some(t) => targets.push(t),
                }
            }
            if !ok {
                continue;
            }
            return Ok(Some(self.counterexample(&targets, g)?));
        }
        Ok(None)
    }

    // BFS helper: shortest path from `from` to a node satisfying `goal`; `inside` restricts to the component.
    fn bfs(&mut self, g: &Graph, from: &[u32], goal: &dyn Fn(u32) -> bool, inside: bool, min_len: usize) -> R<Option<(Vec<u32>, Vec<u32>)>> {
        let n_count = g.n_state.len();
        let mut prev: Vec<i64> = vec![-2; n_count];
        let mut prev_e: Vec<i64> = vec![-1; n_count];
        let mut q: Vec<u32> = vec![];
        if min_len == 0 {
            for &f in from {
                if prev[f as usize] == -2 {
                    prev[f as usize] = -1;
                    q.push(f);
                }
            }
        } else {
            // paths of length >= 1: seed with successors
            for &f in from {
                let fu = f as usize;
                for j in 0..g.adj[fu].len() {
                    let w = g.adj[fu][j] as usize;
                    if inside && (g.comp[w] != g.cid || !self.edge_ok(g.ea, g.n_state, g.adj_edge, fu, j)?) {
                        continue;
                    }
                    if prev[w] == -2 {
                        prev[w] = -3 - f as i64;
                        prev_e[w] = g.adj_edge[fu][j] as i64;
                        q.push(w as u32);
                    }
                }
            }
        }
        let mut h = 0;
        while h < q.len() {
            let n = q[h];
            h += 1;
            if goal(n) {
                let mut nodes: Vec<u32> = vec![];
                let mut edges: Vec<u32> = vec![];
                let mut x = n;
                loop {
                    nodes.push(x);
                    let p = prev[x as usize];
                    if p == -1 {
                        break;
                    }
                    edges.push(prev_e[x as usize] as u32);
                    if p <= -3 {
                        nodes.push((-3 - p) as u32);
                        break;
                    }
                    x = p as u32;
                }
                nodes.reverse();
                edges.reverse();
                return Ok(Some((nodes, edges)));
            }
            let nu = n as usize;
            for j in 0..g.adj[nu].len() {
                let w = g.adj[nu][j] as usize;
                if inside && (g.comp[w] != g.cid || !self.edge_ok(g.ea, g.n_state, g.adj_edge, nu, j)?) {
                    continue;
                }
                if prev[w] == -2 {
                    prev[w] = n as i64;
                    prev_e[w] = g.adj_edge[nu][j] as i64;
                    q.push(w as u32);
                }
            }
        }
        Ok(None)
    }

    fn counterexample(&mut self, targets: &[(u32, i64)], g: &Graph) -> R<CheckResult> {
        let c = self.checker;
        let internal = || err::<(Vec<u32>, Vec<u32>)>("error", "internal error: no path while building a liveness counterexample".into());
        let comp = g.comp;
        let cid = g.cid;
        let (pre_nodes, pre_edges) = match self.bfs(g, g.init_nodes, &|n| comp[n as usize] == cid, false, 0)? {
            Some(p) => p,
            None => internal()?,
        };
        let entry = *pre_nodes.last().unwrap();
        // cycle through all targets and back to entry
        let mut cyc_nodes: Vec<u32> = vec![entry];
        let mut cyc_edges: Vec<u32> = vec![];
        let mut cur = entry;
        for &(tn, te) in targets {
            if cur != tn {
                let (pn, pe) = match self.bfs(g, &[cur], &|n| n == tn, true, 0)? {
                    Some(p) => p,
                    None => internal()?,
                };
                cyc_nodes.extend_from_slice(&pn[1..]);
                cyc_edges.extend_from_slice(&pe);
                cur = tn;
            }
            if te >= 0 {
                let w = g.adj[cur as usize][te as usize];
                cyc_nodes.push(w);
                cyc_edges.push(g.adj_edge[cur as usize][te as usize]);
                cur = w;
            }
        }
        if cur != entry || cyc_edges.is_empty() {
            let (pn, pe) = match self.bfs(g, &[cur], &|n| n == entry, true, if cur == entry { 1 } else { 0 })? {
                Some(p) => p,
                None => internal()?,
            };
            cyc_nodes.extend_from_slice(&pn[1..]);
            cyc_edges.extend_from_slice(&pe);
        }
        // project onto states
        let act_of = |e: u32| -> Option<usize> {
            let a = self.e_act[e as usize];
            if a >= 0 { Some(a as usize) } else { None }
        };
        let mut steps: Vec<TraceStep> = vec![];
        let mut last: i64 = -1;
        for (i, &n) in pre_nodes.iter().enumerate() {
            let s = g.n_state[n as usize] as i64;
            if s == last {
                continue;
            }
            steps.push(TraceStep { state: c.states[s as usize].clone(), action: if i == 0 { None } else { act_of(pre_edges[i - 1]) }, id: s });
            last = s;
        }
        let loop_start = steps.len() - 1;
        let mut loop_action: Option<usize> = None;
        let mut have_loop_action = false;
        for i in 1..cyc_nodes.len() {
            let s = g.n_state[cyc_nodes[i] as usize] as i64;
            if s == last {
                continue;
            }
            if i == cyc_nodes.len() - 1 {
                // returns to the entry state
                loop_action = act_of(cyc_edges[i - 1]);
                have_loop_action = loop_action.is_some();
                break;
            }
            steps.push(TraceStep { state: c.states[s as usize].clone(), action: act_of(cyc_edges[i - 1]), id: s });
            last = s;
        }
        if !have_loop_action && steps.len() - 1 > loop_start && steps[steps.len() - 1].id == steps[loop_start].id {
            loop_action = steps.pop().unwrap().action;
            have_loop_action = loop_action.is_some();
        }
        let stutter = steps.len() - 1 == loop_start && !have_loop_action;
        let names: Vec<&String> = self.model.live_props.iter().map(|p| &p.name).collect();
        let mut r = c.result("liveness");
        r.name = if names.len() == 1 { Some(names[0].clone()) } else { None };
        r.trace = Some(steps);
        r.loop_to = Some(if stutter { -1 } else { loop_start as i64 });
        r.loop_action = loop_action;
        Ok(r)
    }
}

struct Graph<'g> {
    comp: &'g [i32],
    cid: i32,
    n_state: &'g [u32],
    n_part: &'g [u32],
    adj: &'g [Vec<u32>],
    adj_edge: &'g [Vec<u32>],
    init_nodes: &'g [u32],
    ea: &'g [L],
}

fn describe(e: &Fail) -> String {
    match e {
        Fail::Tla(t) => t.msg.clone(),
        Fail::Check { message, .. } => message.clone(),
        Fail::Found => String::new(),
    }
}

/// Run safety checking, then (if there are temporal properties) liveness checking, then POSTCONDITIONs.
pub fn model_check<'a>(model: &'a Model, opts: CheckOptions, events: &mut dyn Events) -> (CheckResult, Checker<'a>) {
    let need_live = !model.live_props.is_empty();
    let record = opts.record_graph || need_live;
    let mut checker = Checker::new(model, CheckOptions { check_deadlock: opts.check_deadlock, record_graph: record, par: opts.par });
    if need_live && (model.view.is_some() || model.symmetry.is_some()) {
        checker.succ_state = Some(vec![]);
    }
    let mut branches = 0;
    // The temporal formulas are normalised before the search starts (errors in them are reported first),
    // on a checker that has no states yet.
    let mut prepared: Option<(Vec<Atom>, HashMap<(usize, usize), usize>, Vec<Group>)> = None;
    if need_live {
        let mut live = Liveness::new(model, &checker);
        match live.prepare() {
            Err(e) => {
                let mut r = checker.error(describe(&e), None);
                r.print_summary = false;
                return (r, checker);
            }
            Ok(n) => branches = n,
        }
        if branches == 0 && live.tautology {
            let mut r = checker.error("Temporal formula is a tautology (its negation is unsatisfiable).".into(), None);
            r.code = Some(2253);
            r.print_summary = false;
            return (r, checker);
        }
        prepared = Some((live.atoms, live.atom_ids, live.groups.take().unwrap_or_default()));
        events.liveness("branches", branches, checker.depth, checker.generated, checker.states.len() as u64);
    }
    let mut result = checker.run(events);
    if result.status == "ok" && branches > 0 {
        events.liveness("start", branches, checker.depth, checker.generated, checker.states.len() as u64);
        let (atoms, atom_ids, groups) = prepared.take().unwrap();
        let mut live = Liveness::new(model, &checker);
        live.atoms = atoms;
        live.atom_ids = atom_ids;
        live.groups = Some(groups);
        match live.check() {
            Ok(Some(r)) => result = r,
            Ok(None) => {}
            Err(e) => result = checker.error(checker.describe_err(&e, true), None),
        }
        if result.status == "ok" {
            events.liveness("end", branches, checker.depth, checker.generated, checker.states.len() as u64);
        }
    }
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
                    result = checker.error(format!("Evaluating postcondition {} failed.\n{}", at, describe(&e)), None);
                    result.code = Some(2405);
                    break;
                }
                Ok(Value::Bool(true)) => {}
                Ok(_) => {
                    if pc.possible {
                        result = checker.error(
                            format!("The _POSSIBLE predicate {} was never witnessed.\nOthers may be unwitnessed too; only witnessed predicates appear with a\nnon-zero count in the record printed above.\nSee https://explain.tlapl.us/possible-conditions for additional details.", at),
                            None,
                        );
                        result.code = Some(2780);
                    } else {
                        result = checker.error(format!("Postcondition {} is false.", at), None);
                        result.code = Some(2404);
                    }
                    break;
                }
            }
        }
    }
    result.live_branches = branches;
    (result, checker)
}
