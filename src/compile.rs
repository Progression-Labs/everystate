//! A compiled form of actions and invariants (EVERYSTATE_EVAL=compiled); the tree-walker of eval.rs stays
//! the reference.
//!
//! Before the search each top-level action and each invariant is turned into a tree of closures:
//! identifiers are resolved to what they denote (a state variable's index, a slot of a frame, a constant),
//! applications of definitions with value parameters are inlined, and the enumerator's work (which
//! conjunct assigns which primed variable, which leave variables unchanged, where the branches are) is
//! decided once instead of being rediscovered for every state. Nothing is memoised across states.
//!
//! The rules that keep it equal to the tree-walker:
//! * Whatever the compiler does not handle is compiled to a *fallback*: the expression is evaluated by the
//!   tree-walker in a context rebuilt from the frame. Coverage is a matter of speed only.
//! * A parameter of an inlined definition is bound by name: every use evaluates the argument where it is
//!   used (so an unused argument is never evaluated, as with the tree-walker's thunks); the value is kept
//!   for the rest of the call when the argument is a state-level expression.
//! * The compiled code only has to be right when it succeeds. If it fails in any way, what it produced
//!   for the action (or invariant) is discarded and the tree-walker evaluates it again from the start, so
//!   error messages, locations and precedence are the tree-walker's by construction. For that to be
//!   sound, an action that may reach an operator with an effect (printing, TLCSet, random choice, I/O, a
//!   new string) is not compiled at all.
use crate::ast::*;
use crate::eval::*;
use crate::intern::*;
use crate::modules::{for_children, level_of, tail_fn, BFn, Builtin, Def};
use crate::value::*;
use std::cell::{Cell, OnceCell, RefCell};
use std::collections::HashSet;
use std::rc::Rc;

pub struct Cx<'a> {
    pub ev: &'a Evaluator,
    /// the frame: bound variables, values of by-name parameters and LET definitions, `@`
    pub f: &'a StateData,
    pub cur: &'a StateData,
    /// the next state being assigned (the blank state for an invariant)
    pub nxt: &'a StateData,
    pub nv: i64,
    pub fallbacks: &'a Cell<u64>,
}
type CE = Box<dyn Fn(&Cx) -> R<Value>>;
type AE = Box<dyn Fn(&Cx, &mut dyn FnMut() -> R<()>) -> R<()>>;

#[cold]
fn bail<T>() -> R<T> {
    // any failure: the caller discards the compiled attempt and asks the tree-walker
    eval_err(String::new())
}

// ---------- scopes: what the tree-walker's context would be ----------
struct Sc {
    k: ScK,
    next: Option<Rc<Sc>>,
}
enum ScK {
    /// the bottom: the context the tree-walker starts from (an action's own context, or none)
    Root(C),
    Slot { name: Name, slot: usize },
    At { slot: usize },
    /// a value parameter of an inlined definition, bound to an argument of the call
    Arg { name: Name, node: N, sc: Rc<Sc>, bd: ArgBd },
    /// one definition of a LET group; `below` is the scope under the whole group
    /// (`root`: the definition is part of the context the action starts from, see `root_scope`)
    Let { d: &'static DefNode, defs: &'static [LetDef], below: Rc<Sc>, head: bool, cache: usize, ce: RefCell<Option<(Rc<CE>, bool)>>, root: bool },
    /// a value bound in the context the action starts from
    RootVal { name: Name, v: Value },
}
enum ArgBd {
    Const(Value),
    /// `stable`: the value cannot change while the binding lives (no dependence on the next state)
    ByName { ce: Rc<CE>, cache: Option<usize>, stable: bool },
}

/// The tree-walker's context for a scope, from the current frame.
fn build(sc: &Rc<Sc>, cx: &Cx) -> R<C> {
    let below = |cx: &Cx| -> R<C> {
        match &sc.next {
            Some(n) => build(n, cx),
            None => Ok(None),
        }
    };
    Ok(match &sc.k {
        ScK::Root(c) => c.clone(),
        ScK::Slot { name, slot } => cons(*name, cx.f.get(*slot), &below(cx)?),
        ScK::At { slot } => cons(cx.ev.at, cx.f.get(*slot), &below(cx)?),
        ScK::Arg { name, node, sc: asc, .. } => {
            let actx = build(asc, cx)?;
            cons(*name, cx.ev.mk_arg(node, &actx)?, &below(cx)?)
        }
        ScK::Let { root: true, .. } | ScK::RootVal { .. } => below(cx)?,
        ScK::Let { defs, below: b, head, .. } => {
            debug_assert!(*head);
            cx.ev.bind_let(defs, &build(b, cx)?)
        }
    })
}

/// EVERYSTATE_EVAL_DEBUG: each fallback site reports itself the first time it runs.
fn debug_fb(seen: &Cell<bool>, what: &str, node: N) {
    if !seen.replace(true) && std::env::var_os("EVERYSTATE_EVAL_DEBUG").is_some() {
        eprintln!("fallback {} at line {} col {} to line {} col {}", what, node.loc[0], node.loc[1], node.loc[2], node.loc[3]);
    }
}
fn fb(node: N, sc: &Rc<Sc>) -> CE {
    let sc = sc.clone();
    let seen = Cell::new(false);
    Box::new(move |cx| {
        debug_fb(&seen, "expression", node);
        cx.fallbacks.set(cx.fallbacks.get() + 1);
        let ctx = build(&sc, cx)?;
        cx.ev.eval(node, &ctx)
    })
}
fn fb_act(node: N, sc: &Rc<Sc>) -> AE {
    let sc = sc.clone();
    let seen = Cell::new(false);
    Box::new(move |cx, k| {
        debug_fb(&seen, "action", node);
        cx.fallbacks.set(cx.fallbacks.get() + 1);
        let ctx = build(&sc, cx)?;
        cx.ev.enumerate(node, &ctx, k)
    })
}

#[inline]
fn truth(v: Value) -> R<bool> {
    match v {
        Value::Bool(b) => Ok(b),
        _ => bail(),
    }
}
#[inline]
fn as_set(v: Value) -> R<Rc<SetV>> {
    match v {
        Value::Set(s) => Ok(s),
        _ => bail(),
    }
}
fn plain(v: &Value) -> bool {
    match v {
        Value::Int(_) | Value::Bool(_) | Value::Str(_) | Value::Model(_) | Value::Tuple(_) | Value::Record(_) | Value::Fcn(_) => true,
        Value::Set(s) => s.reducible(),
        _ => false,
    }
}

/// Builtin operators of these modules have no effect and read nothing but their arguments.
fn pure_module(m: Name) -> bool {
    thread_local! {
        static PURE: Vec<Name> = ["Naturals", "Integers", "Reals", "Sequences", "FiniteSets", "Bags"].iter().map(|s| name(s)).collect();
    }
    PURE.with(|p| p.contains(&m))
}
fn pure_builtin(d: &'static Def) -> bool {
    if pure_module(d.module) {
        return true;
    }
    let n = name_str(d.name);
    name_str(d.module).as_ref() == "TLC" && matches!(n.as_ref(), ":>" | "@@")
}

/// May evaluating `n` reach an operator with an effect? (Conservative: anything not understood counts.)
fn impure(n: N, seen: &mut HashSet<usize>) -> bool {
    if let E::App { r, sel, .. } = &n.e {
        if sel.is_some() {
            return true;
        }
        match r.get() {
            Res::Def(d) => {
                let d = d.over.get().unwrap_or(d);
                if seen.insert(d as *const Def as usize) {
                    if d.builtin.get().is_some() {
                        if !pure_builtin(d) {
                            if std::env::var_os("EVERYSTATE_EVAL_DEBUG").is_some() {
                                eprintln!("not compiled: builtin {} of module {}", d.name, d.module);
                            }
                            return true;
                        }
                    } else if d.inst.is_some() {
                        return true;
                    } else if let Some(b) = d.body.get() {
                        if impure(b, seen) {
                            return true;
                        }
                    } else {
                        return true;
                    }
                }
            }
            Res::Decl(d) => {
                if d.subst.get().is_some() {
                    return true;
                }
            }
            Res::Local => {}
            Res::None => return true,
        }
    }
    if matches!(n.e, E::Let { .. }) {
        if let E::Let { defs, .. } = &n.e {
            if defs.iter().any(|d| matches!(d, LetDef::Inst(_))) {
                return true;
            }
        }
    }
    let mut bad = false;
    for_children(n, &mut |c| {
        if !bad && impure(c, seen) {
            bad = true;
        }
    });
    bad
}

// ---------- the compiler ----------
struct Comp {
    nslots: usize,
    /// definitions and LET definitions being inlined (recursion guard)
    stack: Vec<usize>,
    budget: i64,
    /// set while compiling an expression whose value may depend on the next state
    unstable: bool,
}

enum Found {
    Slot(usize),
    Const(Value),
    ByName(Rc<CE>, Option<usize>),
    /// a LET definition: its scope node and the head of its group
    Let(Rc<Sc>, Rc<Sc>),
    Arg(Rc<Sc>),
    No,
}

fn lookup(sc: &Rc<Sc>, nm: Name) -> Found {
    let mut cur = Some(sc);
    let mut head: Option<&Rc<Sc>> = None;
    while let Some(s) = cur {
        match &s.k {
            ScK::Slot { name, slot } if *name == nm => return Found::Slot(*slot),
            ScK::Arg { name, .. } if *name == nm => return Found::Arg(s.clone()),
            ScK::Let { d, head: h, .. } => {
                if *h {
                    head = Some(s);
                }
                if d.name == nm {
                    return match head {
                        Some(h) => Found::Let(s.clone(), h.clone()),
                        None => Found::No,
                    };
                }
            }
            ScK::RootVal { name, v } if *name == nm => return Found::Const(v.clone()),
            ScK::Root(_) => return Found::No,
            _ => {}
        }
        cur = s.next.as_ref();
    }
    Found::No
}
fn lookup_at(sc: &Rc<Sc>) -> Option<usize> {
    let mut cur = Some(sc);
    while let Some(s) = cur {
        if let ScK::At { slot } = &s.k {
            return Some(*slot);
        }
        cur = s.next.as_ref();
    }
    None
}
fn push(sc: &Rc<Sc>, k: ScK) -> Rc<Sc> {
    Rc::new(Sc { k, next: Some(sc.clone()) })
}
fn simple_bound(bounds: &'static [Bound]) -> Option<(Name, N)> {
    if bounds.len() != 1 {
        return None;
    }
    one_bound(&bounds[0])
}
fn one_bound(b: &'static Bound) -> Option<(Name, N)> {
    match (&b.names, &b.tuple, &b.set) {
        (Some(ns), None, Some(set)) if ns.len() == 1 => Some((ns[0], set)),
        _ => None,
    }
}
fn var_of(n: N) -> Option<usize> {
    if let E::App { args, sel: None, r, .. } = &n.e {
        if let Res::Decl(d) = r.get() {
            if d.is_var && d.idx.get() >= 0 && args.is_empty() {
                return Some(d.idx.get() as usize);
            }
        }
    }
    None
}

impl Comp {
    fn slot(&mut self) -> usize {
        self.nslots += 1;
        self.nslots - 1
    }
    fn fallback(&mut self, n: N, sc: &Rc<Sc>) -> CE {
        if level_of(n) >= 2 {
            self.unstable = true;
        }
        fb(n, sc)
    }

    /// The scope and prologue for inlining a definition: its parameters bound by name to the arguments.
    /// `base` is the scope the body sees under its parameters. None when the call cannot be inlined.
    fn bind_args(&mut self, params: &'static [Param], args: &'static [Node], base: Rc<Sc>, sc: &Rc<Sc>) -> Option<(Rc<Sc>, Vec<usize>)> {
        if params.len() != args.len() || params.iter().any(|p| p.arity != 0) {
            return None;
        }
        let mut inner = base;
        let mut clear = vec![];
        for (p, a) in params.iter().zip(args.iter()) {
            if matches!(a.e, E::Lambda { .. }) {
                return None;
            }
            let bd = match &a.e {
                E::Num(v) => ArgBd::Const(Value::Int(*v)),
                E::Bool(b) => ArgBd::Const(Value::Bool(*b)),
                _ => {
                    let was = std::mem::replace(&mut self.unstable, false);
                    let ce = self.expr(a, sc);
                    let stable = !self.unstable;
                    self.unstable |= was;
                    // a value that cannot change during the call is kept in a slot after its first use
                    // (not worth it for a string or a name that is itself a slot or a constant)
                    let trivial = matches!(a.e, E::Str(..))
                        || matches!(&a.e, E::App { name, args, sel: None, r, .. } if args.is_empty() && matches!(r.get(), Res::Local) && matches!(lookup(sc, *name), Found::Slot(_) | Found::Const(_)));
                    let cache = if stable && !trivial {
                        let s = self.slot();
                        clear.push(s);
                        Some(s)
                    } else {
                        None
                    };
                    ArgBd::ByName { ce: Rc::new(ce), cache, stable }
                }
            };
            inner = push(&inner, ScK::Arg { name: p.name, node: a, sc: sc.clone(), bd });
        }
        Some((inner, clear))
    }

    /// What a use of a by-name binding evaluates.
    fn by_name(ce: Rc<CE>, cache: Option<usize>) -> CE {
        match cache {
            None => Box::new(move |cx| ce(cx)),
            Some(slot) => Box::new(move |cx| {
                let v = cx.f.get(slot);
                if !matches!(v, Value::Undef) {
                    return Ok(v);
                }
                let v = ce(cx)?;
                cx.f.set(slot, v.clone());
                Ok(v)
            }),
        }
    }

    /// The compiled body of a LET definition without parameters (compiled once, on first use).
    fn let_value(&mut self, def_sc: &Rc<Sc>, head: &Rc<Sc>) -> Option<CE> {
        if let ScK::Let { d, cache, ce, .. } = &def_sc.k {
            if !d.params.is_empty() {
                return None;
            }
            if ce.borrow().is_none() {
                let id = *d as *const DefNode as usize;
                if self.stack.contains(&id) {
                    return None;
                }
                self.stack.push(id);
                let was = std::mem::replace(&mut self.unstable, false);
                let body = self.expr(&d.body, head);
                let stable = !self.unstable;
                self.unstable |= was;
                self.stack.pop();
                *ce.borrow_mut() = Some((Rc::new(body), stable));
            }
            let (c, stable) = ce.borrow().as_ref().unwrap().clone();
            if !stable {
                self.unstable = true;
            }
            return Some(Comp::by_name(c, if stable { Some(*cache) } else { None }));
        }
        None
    }

    /// The scope of a LET body: one node per definition, as the tree-walker's `bind_let`.
    fn let_scope(&mut self, defs: &'static [LetDef], sc: &Rc<Sc>) -> Option<(Rc<Sc>, Vec<usize>)> {
        let mut inner = sc.clone();
        let mut clear = vec![];
        let n = defs.len();
        for (i, d) in defs.iter().enumerate() {
            let d = match d {
                LetDef::Def(d) => d,
                LetDef::Inst(_) => return None,
            };
            let cache = self.slot();
            clear.push(cache);
            inner = push(&inner, ScK::Let { d, defs, below: sc.clone(), head: i + 1 == n, cache, ce: RefCell::new(None), root: false });
        }
        if n == 0 {
            return None;
        }
        Some((inner, clear))
    }

    /// Can the function operand of `f[x]` / `DOMAIN f` be evaluated as an ordinary value? (The tree-walker
    /// keeps a function constructor unevaluated there.)
    fn operand_ok(&self, f: N, sc: &Rc<Sc>) -> bool {
        if tail_fn(f) {
            return false;
        }
        match &f.e {
            E::App { name, args, sel: None, r, .. } if args.is_empty() => match r.get() {
                Res::Local => match lookup(sc, *name) {
                    Found::Slot(_) | Found::Const(_) => true,
                    Found::Arg(a) => match &a.k {
                        ScK::Arg { node, sc: asc, .. } => self.operand_ok(node, asc),
                        _ => false,
                    },
                    _ => false,
                },
                Res::Decl(d) => d.subst.get().is_none(),
                Res::Def(_) => false,
                Res::None => false,
            },
            E::Dot { .. } | E::FnApp { .. } | E::Except { .. } | E::Rec(..) => true,
            E::Op(K::Tuple, _) => true,
            _ => false,
        }
    }

    fn expr(&mut self, n: N, sc: &Rc<Sc>) -> CE {
        self.budget -= 1;
        if self.budget < 0 {
            return self.fallback(n, sc);
        }
        match &n.e {
            E::Num(v) => {
                let v = *v;
                Box::new(move |_| Ok(Value::Int(v)))
            }
            E::Bool(b) => {
                let b = *b;
                Box::new(move |_| Ok(Value::Bool(b)))
            }
            E::Str(s, id) => Box::new(move |cx| Ok(Value::Str(cx.ev.str_node(s, id)))),
            E::At => match lookup_at(sc) {
                Some(slot) => Box::new(move |cx| Ok(cx.f.get(slot))),
                None => self.fallback(n, sc),
            },
            E::App { name, args, sel, r, .. } => {
                if sel.is_some() {
                    return self.fallback(n, sc);
                }
                match r.get() {
                    Res::Local => match lookup(sc, *name) {
                        Found::Slot(slot) if args.is_empty() => Box::new(move |cx| Ok(cx.f.get(slot))),
                        Found::Const(v) if args.is_empty() => Box::new(move |_| Ok(v.clone())),
                        Found::Arg(a) if args.is_empty() => match &a.k {
                            ScK::Arg { bd: ArgBd::Const(v), .. } => {
                                let v = v.clone();
                                Box::new(move |_| Ok(v.clone()))
                            }
                            ScK::Arg { bd: ArgBd::ByName { ce, cache, stable }, .. } => {
                                if !*stable {
                                    self.unstable = true;
                                }
                                Comp::by_name(ce.clone(), *cache)
                            }
                            _ => self.fallback(n, sc),
                        },
                        Found::Let(def_sc, head) => {
                            let d = match &def_sc.k {
                                ScK::Let { d, .. } => *d,
                                _ => unreachable!(),
                            };
                            if d.params.is_empty() {
                                if !args.is_empty() {
                                    return self.fallback(n, sc);
                                }
                                match self.let_value(&def_sc, &head) {
                                    Some(ce) => ce,
                                    None => self.fallback(n, sc),
                                }
                            } else {
                                // a LET operator applied to arguments: its body, inlined
                                let id = d as *const DefNode as usize;
                                if self.stack.contains(&id) || self.stack.len() > 40 {
                                    return self.fallback(n, sc);
                                }
                                match self.bind_args(&d.params, args, head.clone(), sc) {
                                    Some((inner, clear)) => {
                                        self.stack.push(id);
                                        let body = self.expr(&d.body, &inner);
                                        self.stack.pop();
                                        with_clear(clear, body)
                                    }
                                    None => self.fallback(n, sc),
                                }
                            }
                        }
                        _ => self.fallback(n, sc),
                    },
                    Res::Decl(d) => {
                        if !args.is_empty() || d.subst.get().is_some() {
                            return self.fallback(n, sc);
                        }
                        if d.is_var {
                            let idx = d.idx.get();
                            if idx < 0 {
                                return self.fallback(n, sc);
                            }
                            let idx = idx as usize;
                            return Box::new(move |cx| {
                                let v = cx.cur.get(idx);
                                if matches!(v, Value::Undef) {
                                    return bail();
                                }
                                Ok(v)
                            });
                        }
                        let v = d.value.borrow().clone();
                        match v {
                            Some(v) if plain(&v) => Box::new(move |_| Ok(v.clone())),
                            _ => self.fallback(n, sc),
                        }
                    }
                    Res::Def(d) => self.def_app(n, d, args, sc),
                    Res::None => self.fallback(n, sc),
                }
            }
            E::Op(k, a) => self.op(n, *k, a, sc),
            E::Case { arms, other } => {
                let arms: Vec<(CE, CE)> = arms.iter().map(|(c, e)| (self.expr(c, sc), self.expr(e, sc))).collect();
                let other = other.as_ref().map(|o| self.expr(o, sc));
                Box::new(move |cx| {
                    for (c, e) in &arms {
                        if truth(c(cx)?)? {
                            return e(cx);
                        }
                    }
                    match &other {
                        Some(o) => o(cx),
                        None => bail(),
                    }
                })
            }
            E::Let { defs, body } => match self.let_scope(defs, sc) {
                Some((inner, clear)) => {
                    let body = self.expr(body, &inner);
                    with_clear(clear, body)
                }
                None => self.fallback(n, sc),
            },
            E::Quant { forall, bounds, body } => {
                let (nm, set) = match simple_bound(bounds) {
                    Some(x) => x,
                    None => return self.fallback(n, sc),
                };
                let set = self.expr(set, sc);
                let slot = self.slot();
                let body = self.expr(body, &push(sc, ScK::Slot { name: nm, slot }));
                let forall = *forall;
                Box::new(move |cx| {
                    let s = as_set(set(cx)?)?;
                    if let SetK::Interval(lo, hi) = &s.k {
                        for i in *lo..=*hi {
                            cx.f.set(slot, Value::Int(i));
                            if truth(body(cx)?)? != forall {
                                return Ok(Value::Bool(!forall));
                            }
                        }
                        return Ok(Value::Bool(forall));
                    }
                    for x in s.elems()? {
                        cx.f.set(slot, x.clone());
                        if truth(body(cx)?)? != forall {
                            return Ok(Value::Bool(!forall));
                        }
                    }
                    Ok(Value::Bool(forall))
                })
            }
            E::Choose { bound, body } => {
                let (nm, set) = match one_bound(bound) {
                    Some(x) => x,
                    None => return self.fallback(n, sc),
                };
                let set = self.expr(set, sc);
                let slot = self.slot();
                let always = matches!(body.e, E::Bool(true));
                let body = self.expr(body, &push(sc, ScK::Slot { name: nm, slot }));
                Box::new(move |cx| {
                    let s = as_set(set(cx)?)?;
                    let es = s.elems()?;
                    if always {
                        if let Some(x) = es.first() {
                            return Ok(x.clone());
                        }
                    }
                    for x in es {
                        cx.f.set(slot, x.clone());
                        if truth(body(cx)?)? {
                            return Ok(x.clone());
                        }
                    }
                    bail()
                })
            }
            E::SetFilter { bound, pred } => {
                let (nm, set) = match one_bound(bound) {
                    Some(x) => x,
                    None => return self.fallback(n, sc),
                };
                let set = self.expr(set, sc);
                let slot = self.slot();
                let pred = self.expr(pred, &push(sc, ScK::Slot { name: nm, slot }));
                // over a set that is not explicit the tree-walker builds a lazy set that keeps its context
                let lazy = self.fallback(n, sc);
                Box::new(move |cx| {
                    let s = as_set(set(cx)?)?;
                    if !s.reducible() {
                        return lazy(cx);
                    }
                    let mut out = Vec::new();
                    for x in s.elems()? {
                        cx.f.set(slot, x.clone());
                        if truth(pred(cx)?)? {
                            out.push(x.clone());
                        }
                    }
                    Ok(SetV::of(out))
                })
            }
            E::SetMap { e, bounds } => {
                let (nm, set) = match simple_bound(bounds) {
                    Some(x) => x,
                    None => return self.fallback(n, sc),
                };
                let set = self.expr(set, sc);
                let slot = self.slot();
                let e = self.expr(e, &push(sc, ScK::Slot { name: nm, slot }));
                Box::new(move |cx| {
                    let s = as_set(set(cx)?)?;
                    let mut out: Vec<Value> = Vec::new();
                    if let SetK::Interval(lo, hi) = &s.k {
                        for i in *lo..=*hi {
                            cx.f.set(slot, Value::Int(i));
                            out.push(e(cx)?);
                        }
                    } else {
                        for x in s.elems()? {
                            cx.f.set(slot, x.clone());
                            out.push(e(cx)?);
                        }
                    }
                    mk_set(out)
                })
            }
            E::FnDef { bounds, body, is_rec, .. } => {
                let (nm, set) = match simple_bound(bounds) {
                    Some(x) if !is_rec.get() => x,
                    _ => return self.fallback(n, sc),
                };
                let set = self.expr(set, sc);
                let slot = self.slot();
                let body = self.expr(body, &push(sc, ScK::Slot { name: nm, slot }));
                let lazy = self.fallback(n, sc);
                Box::new(move |cx| {
                    let s = as_set(set(cx)?)?;
                    if !s.enumerable() {
                        return lazy(cx);
                    }
                    if let SetK::Interval(1, hi) = &s.k {
                        let mut vals = Vec::with_capacity((*hi).max(0) as usize);
                        for i in 1..=*hi {
                            cx.f.set(slot, Value::Int(i));
                            vals.push(body(cx)?);
                        }
                        return Ok(if vals.is_empty() { empty_tuple() } else { Value::Tuple(TupleV::rc(vals)) });
                    }
                    let dom = s.elems()?;
                    let mut vals = Vec::with_capacity(dom.len());
                    for d in dom {
                        cx.f.set(slot, d.clone());
                        vals.push(body(cx)?);
                    }
                    Ok(s.fcn_shape()?.make(vals))
                })
            }
            E::Rec(fields, shape) => {
                let ces: Vec<CE> = fields.iter().map(|(_, e)| self.expr(e, sc)).collect();
                Box::new(move |cx| {
                    let mut vals = Vec::with_capacity(ces.len());
                    for c in &ces {
                        vals.push(c(cx)?);
                    }
                    let sh = shape.get_or_init(|| {
                        let mut idx: Vec<usize> = (0..fields.len()).collect();
                        idx.sort_by_key(|&i| fields[i].0 .0);
                        let sorted = idx.iter().enumerate().all(|(i, &j)| i == j);
                        RecShape { names: Rc::new(idx.iter().map(|&i| fields[i].0).collect()), order: if sorted { None } else { Some(idx) } }
                    });
                    let vals = match &sh.order {
                        None => vals,
                        Some(idx) => {
                            let mut slots: Vec<Option<Value>> = vals.into_iter().map(Some).collect();
                            idx.iter().map(|&i| slots[i].take().unwrap()).collect()
                        }
                    };
                    Ok(Value::Record(Rc::new(RecordV::new(sh.names.clone(), vals))))
                })
            }
            E::Except { base, updates } => {
                let base = self.expr(base, sc);
                let at = self.slot();
                let inner = push(sc, ScK::At { slot: at });
                let ups: Vec<(Vec<CE>, CE)> = updates.iter().map(|(path, val)| (path.iter().map(|x| self.expr(x, sc)).collect(), self.expr(val, &inner))).collect();
                Box::new(move |cx| {
                    let mut f = base(cx)?;
                    for (path, val) in &ups {
                        let mut p = Vec::with_capacity(path.len());
                        for x in path {
                            p.push(x(cx)?);
                        }
                        f = cx.ev.except_with(
                            f,
                            &p,
                            0,
                            &mut |old| {
                                cx.f.set(at, old);
                                val(cx)
                            },
                            n,
                        )?;
                    }
                    Ok(f)
                })
            }
            E::FnApp { f, args } => {
                if !self.operand_ok(f, sc) {
                    return self.fallback(n, sc);
                }
                let fce = self.expr(f, sc);
                let args: Vec<CE> = args.iter().map(|a| self.expr(a, sc)).collect();
                Box::new(move |cx| {
                    let fv = fce(cx)?;
                    let arg = if args.len() == 1 {
                        args[0](cx)?
                    } else {
                        let mut t = Vec::with_capacity(args.len());
                        for a in &args {
                            t.push(a(cx)?);
                        }
                        Value::Tuple(TupleV::rc(t))
                    };
                    let v = cx.ev.apply_fcn(&fv, &arg, Some(n))?;
                    if let Value::LazyFcn(lf) = &v {
                        return lf.force(cx.ev);
                    }
                    Ok(v)
                })
            }
            E::Dot { e, field } => {
                let e = self.expr(e, sc);
                let field = *field;
                Box::new(move |cx| match e(cx)? {
                    Value::Record(rec) => match rec.get(field) {
                        Some(v) => Ok(v.clone()),
                        None => bail(),
                    },
                    _ => bail(),
                })
            }
            _ => self.fallback(n, sc),
        }
    }

    fn def_app(&mut self, n: N, d: &'static Def, args: &'static [Node], sc: &Rc<Sc>) -> CE {
        let d = d.over.get().unwrap_or(d);
        if let Some(bi) = d.builtin.get() {
            return self.builtin(n, bi, args, sc);
        }
        let body = match d.body.get() {
            Some(b) if d.inst.is_none() => b,
            _ => return self.fallback(n, sc),
        };
        let id = d as *const Def as usize;
        if self.stack.contains(&id) || self.stack.len() > 40 {
            return self.fallback(n, sc);
        }
        if d.params.is_empty() && args.is_empty() && crate::modules::def_level(d) == 0 {
            // a constant definition: the tree-walker evaluates it once and keeps the value on the definition
            let cell: OnceCell<Value> = OnceCell::new();
            return Box::new(move |cx| {
                if let Some(v) = cell.get() {
                    return Ok(v.clone());
                }
                let v = cx.ev.eval(n, &None)?;
                if d.cache.borrow().is_some() && plain(&v) {
                    let _ = cell.set(v.clone());
                }
                Ok(v)
            });
        }
        let root = Rc::new(Sc { k: ScK::Root(None), next: None });
        match self.bind_args(&d.params, args, root, sc) {
            Some((inner, clear)) => {
                self.stack.push(id);
                let b = self.expr(body, &inner);
                self.stack.pop();
                with_clear(clear, b)
            }
            None => self.fallback(n, sc),
        }
    }

    fn builtin(&mut self, n: N, bi: &'static Builtin, args: &'static [Node], sc: &Rc<Sc>) -> CE {
        if bi.lazy || bi.ops != 0 {
            return self.fallback(n, sc);
        }
        if let BFn::Const(v) = &bi.f {
            if args.is_empty() && plain(v) {
                return Box::new(move |_| Ok(v.clone()));
            }
        }
        let ces: Vec<CE> = args.iter().map(|a| self.expr(a, sc)).collect();
        if bi.arith != 0 && ces.len() == 2 {
            let mut it = ces.into_iter();
            let (x, y) = (it.next().unwrap(), it.next().unwrap());
            let arith = bi.arith;
            return Box::new(move |cx| {
                let x = x(cx)?;
                let y = y(cx)?;
                if let (Value::Int(a), Value::Int(b)) = (&x, &y) {
                    let (a, b) = (*a, *b);
                    match arith {
                        1 | 2 => {
                            let r = if arith == 1 { a.checked_add(b) } else { a.checked_sub(b) };
                            if let Some(r) = r {
                                if (-2147483648..=2147483647).contains(&r) {
                                    return Ok(Value::Int(r));
                                }
                            }
                        }
                        3 => return Ok(Value::Bool(a < b)),
                        4 => return Ok(Value::Bool(a > b)),
                        5 => return Ok(Value::Bool(a <= b)),
                        _ => return Ok(Value::Bool(a >= b)),
                    }
                }
                cx.ev.call_builtin(bi, &[x, y])
            });
        }
        match ces.len() {
            1 => {
                let a = ces.into_iter().next().unwrap();
                Box::new(move |cx| cx.ev.call_builtin(bi, &[a(cx)?]))
            }
            2 => {
                let mut it = ces.into_iter();
                let (a, b) = (it.next().unwrap(), it.next().unwrap());
                Box::new(move |cx| {
                    let x = a(cx)?;
                    let y = b(cx)?;
                    cx.ev.call_builtin(bi, &[x, y])
                })
            }
            _ => Box::new(move |cx| {
                let mut v = Vec::with_capacity(ces.len());
                for c in &ces {
                    v.push(c(cx)?);
                }
                cx.ev.call_builtin(bi, &v)
            }),
        }
    }

    fn op(&mut self, n: N, k: K, a: &'static [Node], sc: &Rc<Sc>) -> CE {
        match k {
            K::And | K::Or => {
                let ces: Vec<CE> = a.iter().map(|x| self.expr(x, sc)).collect();
                let stop = k == K::Or;
                Box::new(move |cx| {
                    for c in &ces {
                        if truth(c(cx)?)? == stop {
                            return Ok(Value::Bool(stop));
                        }
                    }
                    Ok(Value::Bool(!stop))
                })
            }
            K::Not => {
                let x = self.expr(&a[0], sc);
                Box::new(move |cx| Ok(Value::Bool(!truth(x(cx)?)?)))
            }
            K::Imp => {
                let (x, y) = (self.expr(&a[0], sc), self.expr(&a[1], sc));
                Box::new(move |cx| Ok(Value::Bool(!truth(x(cx)?)? || truth(y(cx)?)?)))
            }
            K::Eqv => {
                let (x, y) = (self.expr(&a[0], sc), self.expr(&a[1], sc));
                Box::new(move |cx| Ok(Value::Bool(truth(x(cx)?)? == truth(y(cx)?)?)))
            }
            K::Eq | K::Ne => {
                let want = k == K::Eq;
                let x = self.expr(&a[0], sc);
                if matches!(&a[1].e, E::Op(K::SetEnum, e) if e.is_empty()) {
                    return Box::new(move |cx| {
                        let x = x(cx)?;
                        let eq = match &x {
                            Value::Set(s) if matches!(s.k, SetK::Enum(_)) => match &s.k {
                                SetK::Enum(el) => el.is_empty(),
                                _ => unreachable!(),
                            },
                            _ => val_eq(&x, &Value::Set(empty_set()))?,
                        };
                        Ok(Value::Bool(eq == want))
                    });
                }
                let y = self.expr(&a[1], sc);
                Box::new(move |cx| {
                    let (x, y) = (x(cx)?, y(cx)?);
                    let eq = match scalar_cmp(&x, &y) {
                        Some(c) => c == std::cmp::Ordering::Equal,
                        None => val_eq(&x, &y)?,
                    };
                    Ok(Value::Bool(eq == want))
                })
            }
            K::If => {
                let (c, t, e) = (self.expr(&a[0], sc), self.expr(&a[1], sc), self.expr(&a[2], sc));
                Box::new(move |cx| if truth(c(cx)?)? { t(cx) } else { e(cx) })
            }
            K::In | K::NotIn => {
                let want = k == K::In;
                let (x, s) = (self.expr(&a[0], sc), self.expr(&a[1], sc));
                Box::new(move |cx| {
                    let x = x(cx)?;
                    Ok(Value::Bool(as_set(s(cx)?)?.contains(&x)? == want))
                })
            }
            K::Cup => {
                let (x, y) = (self.expr(&a[0], sc), self.expr(&a[1], sc));
                Box::new(move |cx| {
                    let x = as_set(x(cx)?)?;
                    let y = as_set(y(cx)?)?;
                    cx.ev.set_union(x, y)
                })
            }
            K::Diff | K::Cap => {
                let (x, y) = (self.expr(&a[0], sc), self.expr(&a[1], sc));
                let diff = k == K::Diff;
                Box::new(move |cx| {
                    let x = as_set(x(cx)?)?;
                    let y = as_set(y(cx)?)?;
                    if x.reducible() && (diff || y.reducible()) {
                        let mut out = Vec::new();
                        for e in x.elems()? {
                            if y.contains(e)? != diff {
                                out.push(e.clone());
                            }
                        }
                        return Ok(SetV::of(out));
                    }
                    Ok(Value::Set(Rc::new(SetV::new(if diff { SetK::Diff(x, y) } else { SetK::Cap(x, y) }))))
                })
            }
            K::SetEnum => {
                let ces: Vec<CE> = a.iter().map(|x| self.expr(x, sc)).collect();
                Box::new(move |cx| {
                    let mut out = Vec::with_capacity(ces.len());
                    for c in &ces {
                        out.push(c(cx)?);
                    }
                    mk_set(out)
                })
            }
            K::Tuple => {
                let ces: Vec<CE> = a.iter().map(|x| self.expr(x, sc)).collect();
                Box::new(move |cx| {
                    let mut out = Vec::with_capacity(ces.len());
                    for c in &ces {
                        out.push(c(cx)?);
                    }
                    Ok(Value::Tuple(TupleV::rc(out)))
                })
            }
            K::Domain => {
                if !self.operand_ok(&a[0], sc) {
                    return self.fallback(n, sc);
                }
                let f = self.expr(&a[0], sc);
                Box::new(move |cx| {
                    let f = f(cx)?;
                    if let Value::LazyFcn(lf) = &f {
                        return Ok(Value::Set(lf.domain(cx.ev)?));
                    }
                    match domain_of(&f) {
                        Some(d) => Ok(Value::Set(d)),
                        None => bail(),
                    }
                })
            }
            _ => self.fallback(n, sc),
        }
    }

    // ---------- actions ----------
    /// The variables of `UNCHANGED e` when `e` is a variable, a tuple of such, or a name for one.
    fn unchanged_vars(&self, e: N, out: &mut Vec<u32>, depth: u32) -> bool {
        if depth > 16 {
            return false;
        }
        if let Some(i) = var_of(e) {
            out.push(i as u32);
            return true;
        }
        match &e.e {
            E::Op(K::Tuple, items) => items.iter().all(|x| self.unchanged_vars(x, out, depth + 1)),
            E::App { args, sel: None, r, .. } if args.is_empty() => match r.get() {
                Res::Def(d) => {
                    let d = d.over.get().unwrap_or(d);
                    match d.body.get() {
                        Some(b) if d.builtin.get().is_none() && d.inst.is_none() && d.params.is_empty() && matches!(b.e, E::Op(K::Tuple, _)) => self.unchanged_vars(b, out, depth + 1),
                        _ => false,
                    }
                }
                _ => false,
            },
            _ => false,
        }
    }

    fn act(&mut self, n: N, sc: &Rc<Sc>) -> AE {
        let inner = self.act_inner(n, sc);
        // once every variable is assigned the tree-walker treats what follows as a plain predicate
        let sc = sc.clone();
        Box::new(move |cx, k| {
            if cx.ev.n_assigned.get() == cx.nv {
                if std::env::var_os("EVERYSTATE_EVAL_DEBUG").is_some() {
                    eprintln!("fallback all-assigned at line {} col {}", n.loc[0], n.loc[1]);
                }
                cx.fallbacks.set(cx.fallbacks.get() + 1);
                let ctx = build(&sc, cx)?;
                return cx.ev.enumerate(n, &ctx, k);
            }
            inner(cx, k)
        })
    }

    fn guard(&mut self, n: N, sc: &Rc<Sc>) -> AE {
        let ce = self.expr(n, sc);
        Box::new(move |cx, k| if truth(ce(cx)?)? { k() } else { Ok(()) })
    }

    fn act_inner(&mut self, n: N, sc: &Rc<Sc>) -> AE {
        self.budget -= 1;
        if self.budget < 0 {
            return fb_act(n, sc);
        }
        match &n.e {
            E::Op(k, a) => match k {
                K::And => {
                    let items: Vec<AE> = a.iter().map(|x| self.act(x, sc)).collect();
                    if items.is_empty() {
                        return Box::new(|_, k| k());
                    }
                    fn conj(items: &[AE], i: usize, cx: &Cx, k: &mut dyn FnMut() -> R<()>) -> R<()> {
                        if i + 1 == items.len() {
                            return items[i](cx, k);
                        }
                        items[i](cx, &mut || conj(items, i + 1, cx, &mut *k))
                    }
                    Box::new(move |cx, k| conj(&items, 0, cx, k))
                }
                K::Or => {
                    let items: Vec<AE> = a.iter().map(|x| self.act(x, sc)).collect();
                    Box::new(move |cx, k| {
                        for it in &items {
                            it(cx, k)?;
                        }
                        Ok(())
                    })
                }
                K::If => {
                    let c = self.expr(&a[0], sc);
                    let (t, e) = (self.act(&a[1], sc), self.act(&a[2], sc));
                    Box::new(move |cx, k| if truth(c(cx)?)? { t(cx, k) } else { e(cx, k) })
                }
                K::Eq | K::In => {
                    // x' = e / x' \in S with x' a variable named directly
                    let tgt = match &a[0].e {
                        E::Op(K::Prime, p) => var_of(&p[0]),
                        _ => None,
                    };
                    match tgt {
                        Some(idx) => {
                            let rhs = self.expr(&a[1], sc);
                            let assigned = fb_act(n, sc);
                            let is_eq = *k == K::Eq;
                            Box::new(move |cx, k| {
                                if !cx.nxt.is_undef(idx) {
                                    // already assigned: a condition on the next state
                                    return assigned(cx, k);
                                }
                                let ev = cx.ev;
                                if is_eq {
                                    let v = rhs(cx)?;
                                    cx.nxt.set(idx, v);
                                    ev.n_assigned.set(ev.n_assigned.get() + 1);
                                    let r = k();
                                    cx.nxt.clear(idx);
                                    ev.n_assigned.set(ev.n_assigned.get() - 1);
                                    return r;
                                }
                                let s = as_set(rhs(cx)?)?;
                                let es = s.elems()?;
                                ev.n_assigned.set(ev.n_assigned.get() + 1);
                                let mut r = Ok(());
                                for x in es {
                                    cx.nxt.set(idx, x.clone());
                                    r = k();
                                    if r.is_err() {
                                        break;
                                    }
                                }
                                cx.nxt.clear(idx);
                                ev.n_assigned.set(ev.n_assigned.get() - 1);
                                r
                            })
                        }
                        None => match &a[0].e {
                            // the left side may still denote a primed variable (a parameter, a definition)
                            E::Op(K::Prime, _) | E::Let { .. } => fb_act(n, sc),
                            E::App { name, args, sel, r, .. } if args.is_empty() => match r.get() {
                                Res::Local if sel.is_none() && matches!(lookup(sc, *name), Found::Slot(_) | Found::Const(_)) => self.guard(n, sc),
                                Res::Decl(d) if sel.is_none() && d.subst.get().is_none() => self.guard(n, sc),
                                _ => fb_act(n, sc),
                            },
                            _ => self.guard(n, sc),
                        },
                    }
                }
                K::Unchanged => {
                    let mut idxs = vec![];
                    if !self.unchanged_vars(&a[0], &mut idxs, 0) || idxs.len() > 32 {
                        return fb_act(n, sc);
                    }
                    let mut seen: u64 = 0;
                    let distinct = idxs.iter().all(|&i| {
                        let fresh = i < 64 && seen & (1 << i) == 0;
                        seen |= 1 << (i & 63);
                        fresh
                    });
                    Box::new(move |cx, k| {
                        let ev = cx.ev;
                        if distinct && cx.nxt.can_fill(cx.cur, &idxs) {
                            cx.nxt.fill(cx.cur, &idxs);
                            ev.n_assigned.set(ev.n_assigned.get() + idxs.len() as i64);
                            let r = k();
                            for &i in idxs.iter().rev() {
                                cx.nxt.clear(i as usize);
                            }
                            ev.n_assigned.set(ev.n_assigned.get() - idxs.len() as i64);
                            return r;
                        }
                        let mut set: u32 = 0;
                        let mut r: R<()> = Ok(());
                        let mut go_on = true;
                        for (j, &i) in idxs.iter().enumerate() {
                            let i = i as usize;
                            if cx.nxt.is_undef(i) {
                                let v = cx.cur.get(i);
                                if matches!(v, Value::Undef) {
                                    r = bail();
                                    go_on = false;
                                    break;
                                }
                                cx.nxt.set(i, v);
                                ev.n_assigned.set(ev.n_assigned.get() + 1);
                                set |= 1 << j;
                            } else {
                                match val_eq(&cx.nxt.get(i), &cx.cur.get(i)) {
                                    Ok(true) => {}
                                    Ok(false) => {
                                        go_on = false;
                                        break;
                                    }
                                    Err(e) => {
                                        r = Err(e);
                                        go_on = false;
                                        break;
                                    }
                                }
                            }
                        }
                        if go_on {
                            r = k();
                        }
                        for j in (0..idxs.len()).rev() {
                            if set & (1 << j) != 0 {
                                cx.nxt.clear(idxs[j] as usize);
                            }
                        }
                        ev.n_assigned.set(ev.n_assigned.get() - set.count_ones() as i64);
                        r
                    })
                }
                // the enumerator has its own rules for these
                K::Imp | K::Subseteq | K::BoxAct | K::AngleAct | K::Cdot => fb_act(n, sc),
                _ => self.guard(n, sc),
            },
            E::Quant { forall: false, bounds, body } => {
                let (nm, set) = match simple_bound(bounds) {
                    Some(x) => x,
                    None => return fb_act(n, sc),
                };
                let set = self.expr(set, sc);
                let slot = self.slot();
                let body = self.act(body, &push(sc, ScK::Slot { name: nm, slot }));
                Box::new(move |cx, k| {
                    let s = as_set(set(cx)?)?;
                    if let SetK::Interval(lo, hi) = &s.k {
                        for i in *lo..=*hi {
                            cx.f.set(slot, Value::Int(i));
                            body(cx, k)?;
                        }
                        return Ok(());
                    }
                    for x in s.elems()? {
                        cx.f.set(slot, x.clone());
                        body(cx, k)?;
                    }
                    Ok(())
                })
            }
            E::Quant { .. } => fb_act(n, sc),
            E::Case { arms, other } => {
                let arms: Vec<(CE, AE)> = arms.iter().map(|(c, e)| (self.expr(c, sc), self.act(e, sc))).collect();
                let other = other.as_ref().map(|o| self.act(o, sc));
                Box::new(move |cx, k| {
                    for (c, e) in &arms {
                        if truth(c(cx)?)? {
                            return e(cx, k);
                        }
                    }
                    match &other {
                        Some(o) => o(cx, k),
                        None => bail(),
                    }
                })
            }
            E::Let { defs, body } => match self.let_scope(defs, sc) {
                Some((inner, clear)) => {
                    let body = self.act(body, &inner);
                    Box::new(move |cx, k| {
                        for &s in &clear {
                            cx.f.clear(s);
                        }
                        body(cx, k)
                    })
                }
                None => fb_act(n, sc),
            },
            E::App { name, args, sel, r, .. } => {
                if sel.is_some() {
                    return fb_act(n, sc);
                }
                match r.get() {
                    Res::Def(d) => {
                        let d = d.over.get().unwrap_or(d);
                        if d.builtin.get().is_some() {
                            return self.guard(n, sc);
                        }
                        let body = match d.body.get() {
                            Some(b) if d.inst.is_none() => b,
                            _ => return fb_act(n, sc),
                        };
                        let id = d as *const Def as usize;
                        if self.stack.contains(&id) || self.stack.len() > 40 {
                            return fb_act(n, sc);
                        }
                        let root = Rc::new(Sc { k: ScK::Root(None), next: None });
                        match self.bind_args(&d.params, args, root, sc) {
                            Some((inner, clear)) => {
                                self.stack.push(id);
                                let b = self.act(body, &inner);
                                self.stack.pop();
                                Box::new(move |cx, k| {
                                    for &s in &clear {
                                        cx.f.clear(s);
                                    }
                                    b(cx, k)
                                })
                            }
                            None => fb_act(n, sc),
                        }
                    }
                    Res::Decl(d) => {
                        if d.subst.get().is_some() {
                            fb_act(n, sc)
                        } else {
                            self.guard(n, sc)
                        }
                    }
                    Res::Local => match lookup(sc, *name) {
                        // a bound variable or a constant: a plain condition
                        Found::Slot(_) | Found::Const(_) if args.is_empty() => self.guard(n, sc),
                        // a parameter or a LET definition: the enumerator enters the expression it stands for
                        _ => fb_act(n, sc),
                    },
                    Res::None => fb_act(n, sc),
                }
            }
            // the enumerator enters the body of a lazily evaluated function
            E::FnApp { .. } => fb_act(n, sc),
            _ => self.guard(n, sc),
        }
    }
}

fn with_clear(clear: Vec<usize>, body: CE) -> CE {
    if clear.is_empty() {
        return body;
    }
    Box::new(move |cx| {
        for &s in &clear {
            cx.f.clear(s);
        }
        body(cx)
    })
}

/// The scope for the context a top-level action or invariant starts from: plain values and LET
/// definitions (an action that was split out of a LET). None when the context holds anything else, or a
/// LET definition that may reach an operator with an effect. Also the slots to clear at each evaluation.
fn root_scope(ctx: &C, c: &mut Comp, seen: &mut HashSet<usize>) -> Option<(Rc<Sc>, Vec<usize>)> {
    let mut nodes: Vec<&Rc<Ctx>> = vec![];
    let mut cur = ctx.as_ref();
    while let Some(node) = cur {
        if node.env || node.base.is_some() {
            return None;
        }
        nodes.push(node);
        cur = node.next.as_ref();
    }
    let mut sc = Rc::new(Sc { k: ScK::Root(ctx.clone()), next: None });
    let mut clear = vec![];
    for node in nodes.iter().rev() {
        let k = match &node.val {
            Bind::Val(v) if plain(v) => ScK::RootVal { name: node.name, v: v.clone() },
            Bind::LetLazy { d, .. } | Bind::LetOp(d) => {
                if impure(&d.body, seen) {
                    return None;
                }
                let cache = c.slot();
                clear.push(cache);
                ScK::Let { d, defs: &[], below: sc.clone(), head: node.let_head, cache, ce: RefCell::new(None), root: true }
            }
            _ => return None,
        };
        sc = push(&sc, k);
    }
    Some((sc, clear))
}

pub struct ActPlan {
    run: AE,
    frame: StateRef,
}
pub struct PredPlan {
    run: CE,
    frame: StateRef,
}
#[derive(Default)]
pub struct Counters {
    /// actions / invariants evaluated by compiled code, by the tree-walker because they are not compiled,
    /// and by the tree-walker after the compiled attempt failed
    pub compiled: Cell<u64>,
    pub uncompiled: Cell<u64>,
    pub redone: Cell<u64>,
    /// fallback expressions evaluated inside compiled code
    pub fallbacks: Cell<u64>,
}
pub struct Plans {
    pub actions: Vec<Option<ActPlan>>,
    pub invariants: Vec<Option<PredPlan>>,
    pub n: Counters,
    blank: StateRef,
}

/// EVERYSTATE_EVAL=compiled
pub fn enabled() -> bool {
    matches!(std::env::var("EVERYSTATE_EVAL").as_deref(), Ok("compiled"))
}

pub fn compile(model: &crate::model::Model) -> Plans {
    let mut actions = vec![];
    for a in &model.actions {
        let mut seen = HashSet::new();
        let mut c = Comp { nslots: 0, stack: vec![], budget: 20_000, unstable: false };
        let root = if impure(a.e, &mut seen) { None } else { root_scope(&a.ctx, &mut c, &mut seen) };
        let (root, clear) = match root {
            Some(x) => x,
            None => {
                if std::env::var_os("EVERYSTATE_EVAL_DEBUG").is_some() {
                    eprintln!("action {}{} is not compiled (an operator with an effect, or a context that is not plain values and LET definitions)", a.name, a.params);
                }
                actions.push(None);
                continue;
            }
        };
        let body = c.act(a.e, &root);
        let run: AE = if clear.is_empty() {
            body
        } else {
            Box::new(move |cx, k| {
                for &s in &clear {
                    cx.f.clear(s);
                }
                body(cx, k)
            })
        };
        actions.push(Some(ActPlan { run, frame: StateData::blank(c.nslots.max(1)) }));
    }
    let mut invariants = vec![];
    for p in &model.invariants {
        let mut seen = HashSet::new();
        let mut c = Comp { nslots: 0, stack: vec![], budget: 20_000, unstable: false };
        let root = if impure(p.e, &mut seen) || level_of(p.e) > 1 { None } else { root_scope(&p.ctx, &mut c, &mut seen) };
        let (root, clear) = match root {
            Some(x) => x,
            None => {
                invariants.push(None);
                continue;
            }
        };
        let run = with_clear(clear, c.expr(p.e, &root));
        invariants.push(Some(PredPlan { run, frame: StateData::blank(c.nslots.max(1)) }));
    }
    Plans { actions, invariants, n: Counters::default(), blank: StateData::blank(model.vars.len()) }
}

impl Plans {
    /// Runs the compiled form of action `ai` (the evaluator's current and next state are set as for
    /// `enumerate`). None: the action is not compiled. Some(Err): the attempt failed and must be redone
    /// by the tree-walker after discarding what it produced.
    pub fn run_action(&self, ev: &Evaluator, ai: usize, cur: &StateData, nxt: &StateData, nv: usize, k: &mut dyn FnMut() -> R<()>) -> Option<R<()>> {
        let p = match &self.actions[ai] {
            Some(p) => p,
            None => {
                self.n.uncompiled.set(self.n.uncompiled.get() + 1);
                return None;
            }
        };
        let cx = Cx { ev, f: &p.frame, cur, nxt, nv: nv as i64, fallbacks: &self.n.fallbacks };
        let r = (p.run)(&cx, k);
        if r.is_err() {
            self.n.redone.set(self.n.redone.get() + 1);
        } else {
            self.n.compiled.set(self.n.compiled.get() + 1);
        }
        Some(r)
    }
    /// The value of invariant `i` in `s` (the evaluator's current state), or None for the tree-walker to decide.
    pub fn run_invariant(&self, ev: &Evaluator, i: usize, s: &StateData, nv: usize) -> Option<bool> {
        let p = match &self.invariants[i] {
            Some(p) => p,
            None => {
                self.n.uncompiled.set(self.n.uncompiled.get() + 1);
                return None;
            }
        };
        let cx = Cx { ev, f: &p.frame, cur: s, nxt: &self.blank, nv: nv as i64, fallbacks: &self.n.fallbacks };
        match (p.run)(&cx) {
            Ok(Value::Bool(b)) => {
                self.n.compiled.set(self.n.compiled.get() + 1);
                Some(b)
            }
            _ => {
                self.n.redone.set(self.n.redone.get() + 1);
                None
            }
        }
    }
    pub fn report(&self) -> String {
        let c = &self.n;
        format!(
            "compiled evaluator: {} of {} actions and {} of {} invariants compiled; evaluations: {} compiled, {} by the tree-walker (not compiled), {} redone by the tree-walker after a failed attempt; {} fallback expressions evaluated inside compiled code\n",
            self.actions.iter().filter(|a| a.is_some()).count(),
            self.actions.len(),
            self.invariants.iter().filter(|a| a.is_some()).count(),
            self.invariants.len(),
            c.compiled.get(),
            c.uncompiled.get(),
            c.redone.get(),
            c.fallbacks.get()
        )
    }
}
