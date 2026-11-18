//! Measurement only, behind EVERYSTATE_CACHE_STATS=1: how often would a cache of local steps hit?
//!
//! Nothing here changes what is computed. Each top-level action is walked as usual; the walk is cut into
//! *units* (an action instance: the body reached through the disjunctions, existential quantifiers and
//! definitions at the top of the action, with the values bound on the way), and while a unit is evaluated
//! every read of the current state is noted: the variable, the element when the read is `f[k]`,
//! `DOMAIN f`, `x \in S`, `BagIn(x, B)`, `B (+) X`, `B (-) X` or the `@` of an EXCEPT on a variable, and
//! the value read. The hash of (unit, bound values, reads in order) is the key a transition cache with
//! dynamic read tracking would use; a key seen before is a hit.
//!
//! The estimate is an upper bound: a value derived from part of a variable (`net (-) one`) is assumed to
//! be used only as the new value of that variable, which a real cache would have to check.
use crate::ast::*;
use crate::eval::*;
use crate::intern::*;
use crate::modules::Def;
use crate::value::*;
use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};

#[derive(Default)]
struct Unit {
    loc: Loc,
    calls: u64,
    hits: u64,
    uncacheable: u64,
    reads: u64,
    keys: HashSet<u64>,
}

pub struct StepStats {
    /// EVERYSTATE_CACHE_STATS is set
    pub enabled: Cell<bool>,
    /// a unit is being evaluated: reads are noted
    pub on: Cell<bool>,
    h: Cell<u64>,
    nreads: Cell<u64>,
    uncacheable: Cell<bool>,
    units: RefCell<HashMap<(usize, usize), Unit>>,
    keys: Cell<usize>,
    names: [Name; 3],
}

const MAX_KEYS: usize = 8 << 20;
const DOMAIN_TAG: u64 = 0x5D0D_0A11;

#[inline]
fn mix(h: u64, x: u64) -> u64 {
    let m = ((h ^ x) as u128).wrapping_mul(0xD6E8_FEB8_6659_FD93u128);
    ((m as u64) ^ ((m >> 64) as u64)).wrapping_add(0x9E37_79B9_7F4A_7C15)
}

impl StepStats {
    pub fn new() -> StepStats {
        StepStats {
            enabled: Cell::new(false),
            on: Cell::new(false),
            h: Cell::new(0),
            nreads: Cell::new(0),
            uncacheable: Cell::new(false),
            units: RefCell::new(HashMap::new()),
            keys: Cell::new(0),
            names: [name("BagIn"), name("\\oplus"), name("\\ominus")],
        }
    }
    fn add(&self, x: u64) {
        self.h.set(mix(self.h.get(), x));
    }
    /// A read of a whole variable.
    #[cold]
    pub fn var(&self, idx: usize, v: &Value, primed: bool) {
        if primed {
            // the value of a primed variable depends on the step being taken
            self.uncacheable.set(true);
            return;
        }
        match value_word(v) {
            Ok(w) => {
                self.add(idx as u64 + 1);
                self.add(w);
                self.nreads.set(self.nreads.get() + 1);
            }
            Err(_) => self.uncacheable.set(true),
        }
    }
    /// A read of one element of a variable: `key` identifies the element, `val` what was found there.
    #[cold]
    pub fn elem(&self, idx: usize, key: R<u64>, val: R<u64>) {
        match (key, val) {
            (Ok(k), Ok(v)) => {
                self.add((idx as u64 + 1) << 32);
                self.add(k);
                self.add(v);
                self.nreads.set(self.nreads.get() + 1);
            }
            _ => self.uncacheable.set(true),
        }
    }
    /// The table, one row per unit, for the checker to print when the run ends.
    pub fn report(&self, action_name: &dyn Fn(usize) -> String) -> String {
        let units = self.units.borrow();
        let mut rows: Vec<(&(usize, usize), &Unit)> = units.iter().collect();
        rows.sort_by_key(|(k, u)| (k.0, u.loc));
        let mut o = String::from("step-cache estimate (EVERYSTATE_CACHE_STATS): action instance, calls, distinct keys, hit rate, uncacheable, reads per call\n");
        let (mut calls, mut hits, mut keys, mut unc) = (0u64, 0u64, 0usize, 0u64);
        for (k, u) in rows {
            o += &format!(
                "  {:<34} line {:>4} col {:>3} {:>10} {:>9} {:>6.2}% {:>6.2}% {:>5.1}\n",
                action_name(k.0),
                u.loc[0],
                u.loc[1],
                u.calls,
                u.keys.len(),
                100.0 * u.hits as f64 / u.calls.max(1) as f64,
                100.0 * u.uncacheable as f64 / u.calls.max(1) as f64,
                u.reads as f64 / u.calls.max(1) as f64
            );
            calls += u.calls;
            hits += u.hits;
            keys += u.keys.len();
            unc += u.uncacheable;
        }
        o += &format!(
            "  total: {} calls, {} distinct keys ({} MB of keys), hit rate {:.2}%, uncacheable {:.2}%{}\n",
            calls,
            keys,
            keys * 16 >> 20,
            100.0 * hits as f64 / calls.max(1) as f64,
            100.0 * unc as f64 / calls.max(1) as f64,
            if self.keys.get() >= MAX_KEYS { " (key table full: later misses are not recorded, hit rate understated)" } else { "" }
        );
        o
    }
}

/// The expression branches at its top: a disjunction or an existential quantifier, possibly behind
/// definitions, LETs and conjunctions.
fn branchy(e: N, depth: u32) -> bool {
    if depth > 8 {
        return false;
    }
    match &e.e {
        E::Op(K::Or, _) => true,
        E::Quant { forall: false, .. } => true,
        E::Op(K::And, a) => a.iter().any(|x| branchy(x, depth + 1)),
        E::Let { body, .. } => branchy(body, depth + 1),
        E::App { args, sel: None, r, .. } => match r.get() {
            Res::Def(d) => {
                let d: &Def = d.over.get().unwrap_or(d);
                d.builtin.get().is_none() && d.inst.is_none() && d.params.len() == args.len() && d.body.get().map_or(false, |b| branchy(b, depth + 1))
            }
            _ => false,
        },
        _ => false,
    }
}

impl Evaluator {
    /// `enumerate` for a top-level action, with the units measured.
    pub fn enumerate_units(&self, ai: usize, e: N, ctx: &C, k: &mut dyn FnMut() -> R<()>) -> R<()> {
        if self.n_assigned.get() == self.nvars.get() as i64 {
            return self.unit(ai, e, ctx, k);
        }
        match &e.e {
            E::Op(K::Or, a) => {
                for d in a {
                    self.enumerate_units(ai, d, ctx, k)?;
                }
                Ok(())
            }
            E::Quant { forall: false, bounds, body } => {
                let body: N = body;
                self.for_bindings(bounds, ctx, &mut |c| {
                    self.enumerate_units(ai, body, c, k)?;
                    Ok(false)
                })?;
                Ok(())
            }
            E::Let { defs, body } => self.enumerate_units(ai, body, &self.bind_let(defs, ctx), k),
            E::App { .. } => match self.expand_app(e, ctx)? {
                Some((b, c)) => self.enumerate_units(ai, b, &c, k),
                None => self.unit(ai, e, ctx, k),
            },
            E::Op(K::And, items) => match items.iter().position(|x| branchy(x, 0)) {
                // guards and assignments, then a branching conjunct: the units are inside it
                Some(j) => self.units_conj(ai, items, 0, j, ctx, k),
                None => self.unit(ai, e, ctx, k),
            },
            _ => self.unit(ai, e, ctx, k),
        }
    }
    fn units_conj(&self, ai: usize, items: &'static [Node], i: usize, j: usize, ctx: &C, k: &mut dyn FnMut() -> R<()>) -> R<()> {
        if i < j {
            return self.enumerate(&items[i], ctx, &mut || self.units_conj(ai, items, i + 1, j, ctx, &mut *k));
        }
        if j + 1 == items.len() {
            return self.enumerate_units(ai, &items[j], ctx, k);
        }
        self.enumerate_units(ai, &items[j], ctx, &mut || self.enum_conj(items, j + 1, ctx, &mut *k))
    }

    fn unit(&self, ai: usize, e: N, ctx: &C, k: &mut dyn FnMut() -> R<()>) -> R<()> {
        let st = &self.steps;
        // the key starts with what the unit is: the expression, the values bound around it, how much of
        // the next state is already assigned
        let mut h = mix(e as *const Node as usize as u64, self.n_assigned.get() as u64);
        let mut c = ctx.as_ref();
        while let Some(node) = c {
            h = mix(h, node.name.0 as u64);
            h = mix(
                h,
                match &node.val {
                    Bind::Val(Value::Thunk(lz)) => lz.e as *const Node as usize as u64,
                    Bind::Val(v) => value_word(v).unwrap_or(0xBAD),
                    Bind::LetLazy { body, .. } => *body as *const Node as usize as u64,
                    Bind::LetOp(d) => *d as *const DefNode as usize as u64,
                    Bind::LetInst(d) => *d as *const Def as usize as u64,
                },
            );
            c = node.next.as_ref();
        }
        st.h.set(h);
        st.nreads.set(0);
        st.uncacheable.set(false);
        st.on.set(true);
        let r = self.enumerate(e, ctx, &mut || {
            // what follows the unit is not part of it
            st.on.set(false);
            let r = k();
            st.on.set(true);
            r
        });
        st.on.set(false);
        r?;
        let mut units = st.units.borrow_mut();
        let u = units.entry((ai, e as *const Node as usize)).or_default();
        u.loc = e.loc;
        u.calls += 1;
        u.reads += st.nreads.get();
        if st.uncacheable.get() {
            u.uncacheable += 1;
        } else if u.keys.contains(&st.h.get()) {
            u.hits += 1;
        } else if st.keys.get() < MAX_KEYS {
            u.keys.insert(st.h.get());
            st.keys.set(st.keys.get() + 1);
        }
        Ok(())
    }

    /// Evaluates `n`, a variable named directly, without noting the read (the caller notes an element).
    pub(crate) fn steps_quiet(&self, n: N, ctx: &C) -> R<Value> {
        if self.prime_depth.get() > 0 {
            self.steps.uncacheable.set(true);
        }
        self.steps.on.set(false);
        let r = self.eval(n, ctx);
        self.steps.on.set(true);
        r
    }

    /// While a unit is evaluated: the bag operators applied to a variable read elements of it, not all of
    /// it. None when this is not such an application.
    #[cold]
    pub(crate) fn steps_builtin(&self, def: &'static Def, args: &'static [Node], ctx: &C) -> R<Option<Value>> {
        let st = &self.steps;
        let which = match st.names.iter().position(|n| *n == def.name) {
            Some(w) if args.len() == 2 => w,
            _ => return Ok(None),
        };
        let bi = def.builtin.get().unwrap();
        if which == 0 {
            // BagIn(x, B)
            let idx = match plain_var(&args[1], ctx) {
                Some(i) => i as usize,
                None => return Ok(None),
            };
            let x = self.eval(&args[0], ctx)?;
            let b = self.steps_quiet(&args[1], ctx)?;
            let r = self.call_builtin(bi, &[x.clone(), b])?;
            st.elem(idx, value_word(&x), value_word(&r));
            return Ok(Some(r));
        }
        // B (+) X, B (-) X: the counts in B of the elements of X
        let idx = match plain_var(&args[0], ctx) {
            Some(i) => i as usize,
            None => return Ok(None),
        };
        let b = self.steps_quiet(&args[0], ctx)?;
        let x = self.eval(&args[1], ctx)?;
        if is_fcn(&x) && is_fcn(&b) {
            for d in domain_elems(&x)?.iter() {
                let n = match bsearch(&domain_elems(&b)?, d) {
                    Ok(Some(i)) => value_word(&fcn_values(&b)?[i]),
                    Ok(None) => Ok(0),
                    Err(e) => Err(e),
                };
                st.elem(idx, value_word(d), n);
            }
        } else {
            st.var(idx, &b, false);
        }
        Ok(Some(self.call_builtin(bi, &[b, x])?))
    }

    /// `DOMAIN f` of a variable read as one element.
    #[cold]
    pub(crate) fn steps_domain(&self, idx: usize, dom: &Value) {
        self.steps.elem(idx, Ok(DOMAIN_TAG), value_word(dom));
    }
}
