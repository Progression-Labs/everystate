//! Builds a checkable model from a root module and a configuration (port of model.ts).
use crate::ast::*;
use crate::cfg::Config;
use crate::eval::*;
use crate::intern::*;
use crate::modules::*;
use crate::stdlib::{apply_overrides, build_stdlib, global_defs};
use crate::value::*;
use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

pub struct Pred {
    pub name: String,
    pub e: N,
    pub ctx: C,
}
pub struct Action {
    pub name: String,
    pub params: String,
    pub loc: Loc,
    pub module: String,
    pub e: N,
    pub ctx: C,
}
pub struct PostCond {
    pub possible: bool,
    pub pred: Pred,
    pub loc: Loc,
    pub module: String,
}
pub struct Model {
    pub root_name: String,
    pub root: Rc<ModuleInfo>,
    pub loader: Loader,
    pub ev: &'static Evaluator,
    pub vars: Vec<&'static Decl>,
    pub inits: Vec<Pred>,
    pub actions: Vec<Action>,
    pub invariants: Vec<Pred>,
    pub implied_inits: Vec<Pred>,
    pub implied_actions: Vec<Pred>,
    pub constraints: Vec<Pred>,
    pub action_constraints: Vec<Pred>,
    pub fairness: Vec<Pred>,
    pub live_props: Vec<Pred>,
    pub symmetry: Option<Vec<HashMap<StrId, StrId>>>,
    pub view: Option<Pred>,
    pub alias: Option<Pred>,
    pub postconditions: Vec<PostCond>,
    pub check_deadlock: bool,
}

fn config_err<T>(msg: String) -> R<T> {
    err("config", msg)
}

pub fn loc_str(loc: &Loc, module: &str) -> String {
    format!("line {}, col {} to line {}, col {} of module {}", loc[0], loc[1], loc[2], loc[3], module)
}

pub(crate) fn body_loc(d: Sym) -> (Loc, String) {
    match d {
        Sym::Def(dd) => {
            let mut o = dd.resolved();
            while let Some(inst) = &o.inst {
                o = inst.orig;
            }
            match o.body.get() {
                Some(bd) => (bd.loc, bd.module.get().unwrap_or(o.module).to_string()),
                None => (o.loc, o.module.to_string()),
            }
        }
        Sym::Decl(dd) => ([0; 4], dd.module.to_string()),
    }
}

fn mk_app(nm: &str, sym: Sym) -> N {
    let (loc, r) = match sym {
        Sym::Def(d) => (d.loc, Res::Def(d)),
        Sym::Decl(d) => ([0; 4], Res::Decl(d)),
    };
    leak(Node::new(loc, E::App { name: name(nm), args: vec![], sel: None, r: Cell::new(r), implicit: false }))
}

struct Builder {
    ev: &'static Evaluator,
    inits: Vec<Pred>,
    actions: Vec<Action>,
    invariants: Vec<Pred>,
    implied_inits: Vec<Pred>,
    implied_actions: Vec<Pred>,
    fairness: Vec<Pred>,
    live_props: Vec<Pred>,
    next_pred: Option<(N, C, String)>,
}

fn is_tla(e: &Fail) -> bool {
    matches!(e, Fail::Tla(_))
}

fn app_parts(e: N) -> Option<(Name, &'static [Node], Res, bool)> {
    match &e.e {
        E::App { name, args, r, sel, .. } => Some((*name, &args[..], r.get(), sel.is_some())),
        _ => None,
    }
}

impl Builder {
    fn lvl(&self, e: N, ctx: &C) -> i8 {
        expr_level(self.ev, e, ctx)
    }

    fn process_spec(&mut self, e: N, ctx: &C, nm: &str) -> R<()> {
        let ev = self.ev;
        match &e.e {
            E::Let { defs, body } => return self.process_spec(body, &ev.bind_let(defs, ctx), nm),
            E::App { .. } => {
                if let Some((b, c)) = ev.expand_app(e, ctx)? {
                    let (an, args, r, _) = app_parts(e).unwrap();
                    let nm2 = if args.is_empty() && !matches!(r, Res::Local) { an.to_string() } else { nm.to_string() };
                    if self.lvl(b, &c) <= 1 {
                        self.inits.push(Pred { name: nm2, e: b, ctx: c });
                        return Ok(());
                    }
                    return self.process_spec(b, &c, &nm2);
                }
            }
            E::Op(K::And, a) => {
                for c in a {
                    self.process_spec(c, ctx, nm)?;
                }
                return Ok(());
            }
            E::Op(K::Always, a) => {
                let arg = &a[0];
                if let E::Op(K::BoxAct, ba) = &arg.e {
                    if self.next_pred.is_some() {
                        return config_err("TLC cannot handle a specification with more than one next-state relation ([][Next]_v conjunct).".into());
                    }
                    self.next_pred = Some((&ba[0], ctx.clone(), String::new()));
                    return Ok(());
                }
                if self.lvl(arg, ctx) <= 1 {
                    return config_err(format!(
                        "TLC cannot handle the temporal formula {}: a []P conjunct with a state predicate P in a specification is not supported (use an INVARIANT instead).",
                        nm
                    ));
                }
                self.fairness.push(Pred { name: nm.to_string(), e, ctx: ctx.clone() });
                return Ok(());
            }
            _ => {}
        }
        let l = self.lvl(e, ctx);
        if l <= 1 {
            self.inits.push(Pred { name: nm.to_string(), e, ctx: ctx.clone() });
        } else if l == 3 {
            self.fairness.push(Pred { name: nm.to_string(), e, ctx: ctx.clone() });
        } else {
            return config_err("TLC cannot handle a conjunct of the specification that is an action formula outside [][...]_v.".into());
        }
        Ok(())
    }

    fn param_str(&self, def: Option<&'static Def>, ctx: &C) -> String {
        let def = match def {
            Some(d) if !d.params.is_empty() => d,
            _ => return String::new(),
        };
        let mut vals = vec![];
        for p in &def.params {
            let s = self.ev.lookup_value(ctx, p.name, None).and_then(|b| self.ev.unthunk(&b)).map(|v| fmt(&v)).unwrap_or_else(|_| "?".to_string());
            vals.push(s);
        }
        format!("({})", vals.join(","))
    }

    fn split(&mut self, e: N, ctx: &C, nm: &str, def: Option<&'static Def>, module: &str) -> R<()> {
        let ev = self.ev;
        match &e.e {
            E::Let { defs, body } => return self.split(body, &ev.bind_let(defs, ctx), nm, def, module),
            E::App { .. } => {
                let (an, args, r, has_sel) = app_parts(e).unwrap();
                if let (Res::Def(rd), false) = (r, has_sel) {
                    let d = rd.resolved();
                    if d.builtin.get().is_none() {
                        if args.iter().all(|a| self.lvl(a, ctx) == 0) {
                            let attempt: R<bool> = (|| {
                                if let Some((b, c)) = ev.expand_app(e, ctx)? {
                                    let mut orig = d;
                                    while let Some(inst) = &orig.inst {
                                        orig = inst.orig;
                                    }
                                    self.split(b, &c, &an.to_string(), Some(orig), &orig.module.to_string())?;
                                    return Ok(true);
                                }
                                Ok(false)
                            })();
                            match attempt {
                                Ok(true) => return Ok(()),
                                Ok(false) => {}
                                Err(x) if is_tla(&x) => {}
                                Err(x) => return Err(x),
                            }
                        }
                        self.actions.push(Action { name: an.to_string(), params: String::new(), loc: e.loc, module: module.to_string(), e, ctx: ctx.clone() });
                        return Ok(());
                    }
                }
            }
            E::Quant { forall: false, bounds, body } => {
                let attempt: R<bool> = (|| {
                    let mut ctxs: Vec<C> = vec![];
                    ev.for_bindings(bounds, ctx, &mut |c| {
                        ctxs.push(c.clone());
                        Ok(false)
                    })?;
                    if !ctxs.is_empty() {
                        for c in &ctxs {
                            self.split(body, c, nm, def, module)?;
                        }
                        return Ok(true);
                    }
                    Ok(false)
                })();
                match attempt {
                    Ok(true) => return Ok(()),
                    Ok(false) => {}
                    Err(x) if is_tla(&x) => {}
                    Err(x) => return Err(x),
                }
            }
            E::Op(K::Or, a) => {
                for d in a {
                    self.split(d, ctx, nm, def, module)?;
                }
                return Ok(());
            }
            _ => {}
        }
        let params = self.param_str(def, ctx);
        self.actions.push(Action { name: nm.to_string(), params, loc: e.loc, module: module.to_string(), e, ctx: ctx.clone() });
        Ok(())
    }

    fn process_prop(&mut self, e: N, ctx: &C, nm: &str) -> R<()> {
        let ev = self.ev;
        match &e.e {
            E::Let { defs, body } => return self.process_prop(body, &ev.bind_let(defs, ctx), nm),
            E::App { .. } => {
                if let Some((b, c)) = ev.expand_app(e, ctx)? {
                    let (an, args, r, _) = app_parts(e).unwrap();
                    let nm2 = if args.is_empty() && !matches!(r, Res::Local) { an.to_string() } else { nm.to_string() };
                    return self.process_prop(b, &c, &nm2);
                }
            }
            E::Quant { forall: true, bounds, body } => {
                if self.lvl(e, ctx) == 3 {
                    let attempt: R<()> = (|| {
                        let mut ctxs: Vec<C> = vec![];
                        ev.for_bindings(bounds, ctx, &mut |c| {
                            ctxs.push(c.clone());
                            Ok(false)
                        })?;
                        for c in &ctxs {
                            self.process_prop(body, c, nm)?;
                        }
                        Ok(())
                    })();
                    match attempt {
                        Ok(()) => return Ok(()),
                        Err(x) if is_tla(&x) => {}
                        Err(x) => return Err(x),
                    }
                }
            }
            E::Op(K::And, a) => {
                for c in a {
                    self.process_prop(c, ctx, nm)?;
                }
                return Ok(());
            }
            E::Op(K::Always, a) => {
                let arg: N = &a[0];
                if arg.is_k(K::BoxAct) {
                    self.implied_actions.push(Pred { name: nm.to_string(), e: arg, ctx: ctx.clone() });
                    return Ok(());
                }
                if self.lvl(arg, ctx) < 2 {
                    let nm2 = match app_parts(arg) {
                        Some((an, args, r, _)) if args.is_empty() && !matches!(r, Res::Local) => an.to_string(),
                        _ => nm.to_string(),
                    };
                    self.invariants.push(Pred { name: nm2, e: arg, ctx: ctx.clone() });
                    return Ok(());
                }
                self.live_props.push(Pred { name: nm.to_string(), e, ctx: ctx.clone() });
                return Ok(());
            }
            _ => {}
        }
        let l = self.lvl(e, ctx);
        if l <= 1 {
            self.implied_inits.push(Pred { name: nm.to_string(), e, ctx: ctx.clone() });
        } else if l == 3 {
            self.live_props.push(Pred { name: nm.to_string(), e, ctx: ctx.clone() });
        } else {
            return config_err(format!("The property {} is an action-level formula; TLC can only check action properties of the form [][A]_v.", nm));
        }
        Ok(())
    }
}

pub fn build_model(root_name: &str, resolve: SourceResolver, cfg: &Config, host: crate::host::HostRef) -> R<Model> {
    let mut loader = Loader::new(resolve, build_stdlib());
    loader.globals = global_defs();
    let root = loader.load(name(root_name), None)?;
    // native overrides for bundled modules
    apply_overrides(&loader);
    let ev = Evaluator::create();
    *ev.host.borrow_mut() = host;
    let vars = tlc_variable_order(&root);
    for (i, v) in vars.iter().enumerate() {
        v.idx.set(i as i32);
    }
    ev.nvars.set(vars.len());
    *ev.var_names.borrow_mut() = vars.iter().map(|v| v.name).collect();

    let get_def = |nm: &str, what: &str| -> R<Sym> {
        match root.syms.get(name(nm)) {
            None => config_err(format!("The {} {} specified in the configuration file\nis not defined in the specification.", what, nm)),
            Some(Sym::Decl(d)) if d.is_var => config_err(format!("The {} {} specified in the configuration file\nis not a defined operator.", what, nm)),
            Some(s) => Ok(s),
        }
    };

    // ---- constants ----
    for c in &cfg.constants {
        let scope = match &c.module {
            Some(m) => loader.modules.get(&name(m)).cloned(),
            None => Some(root.clone()),
        };
        let s = match scope.and_then(|sc| sc.syms.get(name(&c.name))) {
            Some(s) => s,
            None => {
                if c.subst.is_some() {
                    return config_err(format!("The constant parameter {} is not a constant or operator of the specification.", c.name));
                }
                continue; // e.g. `a = a` just declares a model value
            }
        };
        if let Some(args) = &c.args {
            // F(v1, ..., vn) = value lines define a constant operator by a table
            let d = match s {
                Sym::Decl(d) if !d.is_var => d,
                _ => return config_err(format!("The constant parameter {} is not a constant operator of the specification.", c.name)),
            };
            let existing = d.subst.get().and_then(|sd| sd.builtin.get()).and_then(|b| if let BFn::Table(rows, _) = &b.f { Some(rows) } else { None });
            let rows = match existing {
                Some(rows) => {
                    if rows.borrow()[0].0.len() != args.len() {
                        return config_err(format!("The constant {} is given values with inconsistent arities in the configuration file.", c.name));
                    }
                    rows
                }
                None => {
                    let params = (0..args.len()).map(|i| Param { name: name(&format!("p{}", i)), arity: 0 }).collect();
                    let def = Def::new(d.name, params, None, d.module, false, [0; 4]);
                    let bi: &'static Builtin = leak(Builtin { f: BFn::Table(RefCell::new(vec![]), d.name), ops: 0, lazy: false, arith: 0 });
                    def.builtin.set(Some(bi));
                    d.subst.set(Some(leak(def)));
                    match &bi.f {
                        BFn::Table(rows, _) => rows,
                        _ => unreachable!(),
                    }
                }
            };
            rows.borrow_mut().push((args.clone(), c.value.clone().unwrap()));
            continue;
        }
        if let Some(sub) = &c.subst {
            let target = match root.syms.get(name(sub)) {
                Some(Sym::Def(t)) => t,
                _ => return config_err(format!("The configuration file substitutes for {} with the undefined identifier {}.", c.name, sub)),
            };
            match s {
                Sym::Decl(d) if !d.is_var => d.subst.set(Some(target)),
                Sym::Def(d) => d.over.set(Some(target)),
                _ => {}
            }
        } else {
            match s {
                Sym::Decl(d) if !d.is_var => {
                    if d.arity > 0 {
                        return config_err(format!("The constant operator {} cannot be assigned a value; use <- to substitute an operator.", c.name));
                    }
                    *d.value.borrow_mut() = c.value.clone();
                }
                Sym::Def(d) => {
                    let o = Def::new(d.name, vec![], None, d.module, false, d.loc);
                    o.builtin.set(Some(leak(Builtin { f: BFn::Const(c.value.clone().unwrap()), ops: 0, lazy: false, arith: 0 })));
                    d.over.set(Some(leak(o)));
                }
                _ => {}
            }
        }
    }
    // A constant replaced by a definition that is not constant-level (TLC evaluates the replacement at startup).
    for c in &cfg.constants {
        let sub = match &c.subst {
            Some(s) => s,
            None => continue,
        };
        let scope = match &c.module {
            Some(m) => loader.modules.get(&name(m)).cloned(),
            None => Some(root.clone()),
        };
        let sd = match scope.and_then(|sc| sc.syms.get(name(&c.name))) {
            Some(Sym::Decl(d)) if !d.is_var => match d.subst.get() {
                Some(sd) if sd.params.is_empty() && sd.builtin.get().is_none() => sd,
                _ => continue,
            },
            _ => continue,
        };
        let s0 = ev.st_touch.get();
        ev.set_state(&StateData::blank(0), None);
        ev.init_mode.set(false);
        if let Err(e) = ev.eval(mk_app(sub, Sym::Def(sd)), &None) {
            match &*e {
                Fail::Tla(t) if t.kind == "stack" => continue,
                Fail::Tla(t) => {
                    if def_level(sd) > 0 || ev.st_touch.get() != s0 {
                        return config_err(format!("The configuration file substitutes constant {} with non-constant {} - specifically: {}", c.name, sub, t.msg));
                    }
                }
                _ => return Err(e),
            }
        }
    }
    for c in &root.consts {
        if c.value.borrow().is_none() && c.subst.get().is_none() {
            return config_err(format!("The constant parameter {} is not assigned a value by the configuration file.", c.name));
        }
    }

    // SANY's level check: a temporal operator may not be applied to an action (no "raw TLA")
    {
        let mut errs: Vec<String> = vec![];
        fn walk(x: N, root_name: &str, errs: &mut Vec<String>) {
            if let E::Op(K::Always | K::Eventually | K::LeadsTo | K::Guarantee, a) = &x.e {
                for arg in a {
                    if !arg.is_k(K::BoxAct) && !arg.is_k(K::AngleAct) && level_of(arg) == 2 {
                        let l = arg.loc;
                        errs.push(format!(
                            "line {}, col {} to line {}, col {} of module {}\n\nAction used where only temporal formula or state predicate allowed.",
                            l[0],
                            l[1],
                            l[2],
                            l[3],
                            arg.module_str().unwrap_or_else(|| root_name.to_string())
                        ));
                    }
                }
            }
            for_children(x, &mut |c| walk(c, root_name, errs));
        }
        for mname in &loader.load_order {
            for d in &loader.modules[mname].own_defs {
                if let Some(b) = d.body.get() {
                    walk(b, root_name, &mut errs);
                }
            }
        }
        if !errs.is_empty() {
            return Err(Box::new(Fail::Tla(TlaError {
                msg: format!("Semantic errors:\n\n*** Errors: {}\n\n{}", errs.len(), errs.join("\n\n\n")),
                loc: None,
                module: Some(root_name.to_string()),
                kind: "semantic",
            })));
        }
    }

    let mut b = Builder { ev, inits: vec![], actions: vec![], invariants: vec![], implied_inits: vec![], implied_actions: vec![], fairness: vec![], live_props: vec![], next_pred: None };
    let mut constraints = vec![];
    let mut action_constraints = vec![];
    let mut postconditions = vec![];

    // ---- invariants / constraints ----
    for n in &cfg.invariants {
        let d = get_def(n, "invariant")?;
        if let Sym::Def(dd) = d {
            if !dd.params.is_empty() {
                return config_err(format!("The invariant {} cannot take arguments.", n));
            }
            if def_level(dd) >= 2 {
                return config_err(format!("The invariant {} is not a state predicate (it has primed variables or temporal operators).", n));
            }
        }
        b.invariants.push(Pred { name: n.clone(), e: mk_app(n, d), ctx: None });
    }
    for n in &cfg.constraints {
        constraints.push(Pred { name: n.clone(), e: mk_app(n, get_def(n, "constraint")?), ctx: None });
    }
    for n in &cfg.action_constraints {
        action_constraints.push(Pred { name: n.clone(), e: mk_app(n, get_def(n, "action constraint")?), ctx: None });
    }
    let view = match &cfg.view {
        Some(v) => Some(Pred { name: v.clone(), e: mk_app(v, get_def(v, "view")?), ctx: None }),
        None => None,
    };
    let alias = match &cfg.alias {
        Some(a) => Some(Pred { name: a.clone(), e: mk_app(a, get_def(a, "alias")?), ctx: None }),
        None => None,
    };
    for n in &cfg.postconditions {
        let d = get_def(n, "post condition")?;
        let (loc, module) = body_loc(d);
        postconditions.push(PostCond { possible: false, pred: Pred { name: n.clone(), e: mk_app(n, d), ctx: None }, loc, module });
    }
    // _POSSIBLE P: count how often P holds (state predicates: per generated state; actions: per transition) and
    // require a non-zero count once model checking has finished.
    if !cfg.possible.is_empty() {
        let pm = loader.load(name("_Possible"), None)?;
        let (track, check) = match (pm.syms.get(name("_Track")), pm.syms.get(name("_CheckName"))) {
            (Some(Sym::Def(t)), Some(Sym::Def(c))) => (t, c),
            _ => unreachable!(),
        };
        let strn = |v: &str| -> Node { Node::new([0; 4], E::Str(Rc::from(v), Cell::new(None))) };
        for n in &cfg.possible {
            let sd = match root.syms.get(name(n)) {
                None => return config_err(format!("The possible {} specified in the configuration file\nis not defined in the specification.", n)),
                Some(Sym::Def(d)) => d,
                Some(_) => return config_err(format!("The possible {} specified in the configuration file\nis not a defined operator.", n)),
            };
            if !sd.params.is_empty() {
                return config_err(format!("The possible {} specified in the configuration file\nrequires arguments.", n));
            }
            let lv = def_level(sd);
            if lv >= 3 {
                return config_err(format!("The possible {} specified in the configuration file\nis a temporal formula; only state- and action-level predicates are supported.", n));
            }
            str_id(n);
            let arg0 = Node::new(sd.loc, E::App { name: name(n), args: vec![], sel: None, r: Cell::new(Res::Def(sd)), implicit: false });
            let e: N = leak(Node::new(sd.loc, E::App { name: name("_Track"), args: vec![arg0, strn(n)], sel: None, r: Cell::new(Res::Def(track)), implicit: false }));
            let p = Pred { name: n.clone(), e, ctx: None };
            if lv <= 1 {
                constraints.push(p);
            } else {
                action_constraints.push(p);
            }
            let ce: N = leak(Node::new(sd.loc, E::App { name: name("_CheckName"), args: vec![strn(n)], sel: None, r: Cell::new(Res::Def(check)), implicit: false }));
            let (loc, module) = body_loc(Sym::Def(sd));
            postconditions.push(PostCond { possible: true, pred: Pred { name: n.clone(), e: ce, ctx: None }, loc, module });
        }
    }

    // ---- behaviour spec ----
    if let Some(spec) = &cfg.spec {
        if cfg.init.is_some() || cfg.next.is_some() {
            return config_err("The configuration file cannot specify both INIT/NEXT and SPECIFICATION fields.".into());
        }
        let d = get_def(spec, "specification")?;
        b.process_spec(mk_app(spec, d), &None, spec)?;
    } else {
        if let Some(i) = &cfg.init {
            let d = get_def(i, "initial predicate")?;
            b.inits.push(Pred { name: i.clone(), e: mk_app(i, d), ctx: None });
        }
        if let Some(nx) = &cfg.next {
            let d = get_def(nx, "next state action")?;
            b.next_pred = Some((mk_app(nx, d), None, nx.clone()));
        }
    }
    // a specification without variables has no behaviours to explore: TLC only checks the assumptions
    if vars.is_empty() {
        b.inits.clear();
        b.next_pred = None;
    }
    let no_behavior = (cfg.spec.is_none() && cfg.init.is_none() && cfg.next.is_none()) || vars.is_empty();
    if b.inits.is_empty() && !no_behavior {
        return config_err("The configuration file did not specify the initial state predicate.".into());
    }
    if b.next_pred.is_none() && cfg.spec.is_none() && !no_behavior {
        return config_err("The configuration file did not specify the next state predicate.".into());
    }

    // ---- split Next into actions ----
    if let Some((e, ctx, nm)) = b.next_pred.take() {
        let nm = if nm.is_empty() { "Action".to_string() } else { nm };
        b.split(e, &ctx, &nm, None, root_name)?;
    }

    // ---- properties ----
    for n in &cfg.properties {
        b.process_prop(mk_app(n, get_def(n, "property")?), &None, n)?;
    }

    // ---- symmetry ----
    let mut symmetry = None;
    if let Some(sy) = &cfg.symmetry {
        let d = get_def(sy, "symmetry function")?;
        ev.set_state(&StateData::blank(0), None);
        let v = ev.eval(mk_app(sy, d), &None)?;
        let s = match &v {
            Value::Set(s) => s,
            _ => return config_err(format!("The symmetry operator {} must evaluate to a set of permutations.", sy)),
        };
        type Perm = Vec<(StrId, StrId)>;
        let mut perms: Vec<Perm> = vec![];
        for f in s.elems()? {
            if !is_fcn(f) {
                return config_err("Symmetry function must have model values as domain and range.".into());
            }
            let (dom, rng) = (domain_elems(f)?, fcn_values(f)?);
            let mut m: Perm = vec![];
            let mut identity = true;
            for i in 0..dom.len() {
                match (&dom[i], &rng[i]) {
                    (Value::Model(x), Value::Model(y)) => {
                        m.push((*x, *y));
                        if x != y {
                            identity = false;
                        }
                    }
                    _ => return config_err("Symmetry function must have model values as domain and range.".into()),
                }
            }
            if !identity {
                perms.push(m);
            }
        }
        // close the generators under composition (TLC computes the generated group)
        let key = |m: &Perm| -> Vec<(u32, u32)> {
            let mut k: Vec<(u32, u32)> = m.iter().filter(|(a, b)| a != b).map(|(a, b)| (a.0, b.0)).collect();
            k.sort();
            k
        };
        let mut seen: HashSet<Vec<(u32, u32)>> = HashSet::new();
        seen.insert(vec![]);
        let mut group: Vec<Perm> = vec![];
        for g in perms {
            if seen.insert(key(&g)) {
                group.push(g);
            }
        }
        let gens = group.clone();
        let mut i = 0;
        while i < group.len() {
            for g in &gens {
                let mut c: Perm = vec![];
                for (a, bb) in &group[i] {
                    let t = g.iter().find(|x| x.0 == *bb).map(|x| x.1).unwrap_or(*bb);
                    c.push((*a, t));
                }
                for (a, bb) in g {
                    if !c.iter().any(|x| x.0 == *a) {
                        c.push((*a, *bb));
                    }
                }
                if seen.insert(key(&c)) {
                    group.push(c);
                }
            }
            i += 1;
        }
        if !group.is_empty() {
            symmetry = Some(group.into_iter().map(|p| p.into_iter().filter(|(a, b)| a != b).collect::<HashMap<_, _>>()).collect());
        }
    }

    Ok(Model {
        root_name: root_name.to_string(),
        root,
        loader,
        ev,
        vars,
        inits: b.inits,
        actions: b.actions,
        invariants: b.invariants,
        implied_inits: b.implied_inits,
        implied_actions: b.implied_actions,
        constraints,
        action_constraints,
        fairness: b.fairness,
        live_props: b.live_props,
        symmetry,
        view,
        alias,
        postconditions,
        check_deadlock: cfg.check_deadlock.unwrap_or(true),
    })
}

/// Level of an expression in a context: like level_of, but looks through locally bound thunks.
pub fn expr_level(ev: &Evaluator, e: N, ctx: &C) -> i8 {
    let mut seen: HashSet<*const Node> = HashSet::new();
    fn go(ev: &Evaluator, n: N, c: &C, seen: &mut HashSet<*const Node>) -> i8 {
        let mut l = level_of(n);
        if l >= 3 {
            return l;
        }
        visit(ev, n, c, seen, &mut l);
        l
    }
    fn visit(ev: &Evaluator, x: N, cc: &C, seen: &mut HashSet<*const Node>, l: &mut i8) {
        if *l >= 3 {
            return;
        }
        if let E::App { name, r, .. } = &x.e {
            let base = base_of(cc);
            match r.get() {
                Res::Local => {
                    if let Ok(Value::Thunk(lz)) = ev.lookup_value(cc, *name, None) {
                        if seen.insert(lz.e as *const Node) {
                            *l = (*l).max(go(ev, lz.e, &lz.ctx, seen));
                        }
                    }
                }
                Res::Decl(_) if base.is_some() => {
                    if let Some(Value::Thunk(lz)) = ev.env_lookup(&base, *name) {
                        if seen.insert(lz.e as *const Node) {
                            *l = (*l).max(go(ev, lz.e, &lz.ctx, seen));
                        }
                    }
                }
                Res::Def(d) if base.is_some() && d.builtin.get().is_none() => {
                    if let Some(body) = d.body.get() {
                        if seen.insert(body as *const Node) {
                            visit(ev, body, &base, seen, l);
                        }
                    }
                }
                _ => {}
            }
        }
        for_children(x, &mut |c| visit(ev, c, cc, seen, l));
    }
    go(ev, e, ctx, &mut seen)
}

// TLC lists variables in the iteration order of SANY's symbol Hashtable for the root module, so the
// order depends on Java's String.hashCode of each name and on the table capacity, which in turn
// depends on how many symbols the module context holds. Reproduced here so that printed states match.
fn std_symbols(m: &str) -> Option<usize> {
    Some(match m {
        "Naturals" => 12,
        "Integers" => 2,
        "Reals" => 3,
        "Sequences" => 8,
        "FiniteSets" => 2,
        "TLC" => 14,
        "Bags" => 12,
        "TLCExt" => 14,
        "Randomization" => 4,
        _ => return None,
    })
}
fn java_hash(s: &str) -> i64 {
    let mut h: i32 = 0;
    for u in s.encode_utf16() {
        h = h.wrapping_mul(31).wrapping_add(u as i32);
    }
    (h & 0x7fffffff) as i64
}
pub fn tlc_variable_order(root: &ModuleInfo) -> Vec<&'static Decl> {
    let mut count = 72usize; // built-in operators in SANY's initial context
    let mut std: Vec<Name> = vec![];
    let mut seen: HashSet<usize> = HashSet::new();
    for (_, sym) in &root.syms.items {
        let key = match sym {
            Sym::Decl(d) => *d as *const Decl as usize,
            Sym::Def(d) => *d as *const Def as usize,
        };
        if !seen.insert(key) {
            continue;
        }
        match sym {
            Sym::Def(d) if d.builtin.get().is_some() && std_symbols(&d.module.to_string()).is_some() => {
                if !std.contains(&d.module) {
                    std.push(d.module);
                }
            }
            _ => count += 1,
        }
    }
    for m in std {
        count += std_symbols(&m.to_string()).unwrap();
    }
    let mut cap = 11usize;
    while count > cap * 3 / 4 {
        cap = cap * 2 + 1;
    }
    let mut v: Vec<(i64, usize, &'static Decl)> = root.vars.iter().enumerate().map(|(i, d)| (java_hash(&d.name.to_string()) % cap as i64, i, *d)).collect();
    v.sort_by_key(|x| (x.0, x.1));
    v.into_iter().map(|x| x.2).collect()
}
