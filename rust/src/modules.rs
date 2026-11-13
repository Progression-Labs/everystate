//! Module loading, symbol tables and static name resolution (port of modules.ts).
use crate::ast::*;
use crate::eval::{Ctx, Evaluator};
use crate::intern::*;
use crate::parser::parse_module;
use crate::value::Value;
use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

pub struct Decl {
    pub is_var: bool,
    pub name: Name,
    pub arity: usize,
    pub idx: Cell<i32>, // variable index (vars only; assigned for the root module)
    pub module: Name,
    pub value: RefCell<Option<Value>>,     // constants: value from the config
    pub subst: Cell<Option<&'static Def>>, // constants: replaced by a definition (C <- Def)
}

pub type NativeFn = fn(&Evaluator, &[Value]) -> R<Value>;
pub enum BFn {
    Native(NativeFn),
    Const(Value),
    /// constant operator defined by `F(v1, ..., vn) = value` lines in the config
    Table(RefCell<Vec<(Vec<Value>, Value)>>, Name),
}
pub struct Builtin {
    pub f: BFn,
    pub ops: u32,   // bit i set: argument i is operator-valued
    pub lazy: bool, // receives unevaluated thunks
}

pub struct Inst {
    pub orig: &'static Def,
    pub substs: Rc<Vec<InstSubst>>,
    pub nparams: usize,
    pub env_cache: RefCell<Option<Option<Rc<Ctx>>>>,
}

pub struct Def {
    pub name: Name,
    pub params: Vec<Param>,
    pub body: Cell<Option<N>>,
    pub module: Name,
    pub local: bool,
    pub loc: Loc,
    pub builtin: Cell<Option<&'static Builtin>>,
    pub inst: Option<Inst>,
    pub cache: RefCell<Option<Value>>,
    pub level: Cell<i8>,
    pub over: Cell<Option<&'static Def>>, // config replacement (Op <- Other)
    pub over_scoped: Cell<bool>,           // the replacement was given with a module scope (Op = [M]v)
    pub refs: RefCell<Option<Rc<RefCell<HashSet<Name>>>>>,
    pub enabled_only: RefCell<Vec<Option<bool>>>,
}
impl Def {
    pub fn new(name: Name, params: Vec<Param>, body: Option<N>, module: Name, local: bool, loc: Loc) -> Def {
        Def {
            name,
            params,
            body: Cell::new(body),
            module,
            local,
            loc,
            builtin: Cell::new(None),
            inst: None,
            cache: RefCell::new(None),
            level: Cell::new(-1),
            over: Cell::new(None),
            over_scoped: Cell::new(false),
            refs: RefCell::new(None),
            enabled_only: RefCell::new(Vec::new()),
        }
    }
    #[inline]
    pub fn resolved(&'static self) -> &'static Def {
        match self.over.get() {
            Some(d) => d,
            None => self,
        }
    }
}
pub fn leak<T>(x: T) -> &'static T {
    Box::leak(Box::new(x))
}

#[derive(Copy, Clone)]
pub enum Sym {
    Decl(&'static Decl),
    Def(&'static Def),
}
impl Sym {
    fn same(&self, o: &Sym) -> bool {
        match (self, o) {
            (Sym::Decl(a), Sym::Decl(b)) => std::ptr::eq(*a, *b),
            (Sym::Def(a), Sym::Def(b)) => std::ptr::eq(*a, *b),
            _ => false,
        }
    }
    pub fn module(&self) -> Name {
        match self {
            Sym::Decl(d) => d.module,
            Sym::Def(d) => d.module,
        }
    }
    fn is_inst(&self) -> bool {
        matches!(self, Sym::Def(d) if d.inst.is_some())
    }
}

/// Insertion-ordered map (JS Map semantics: re-setting a key keeps its position).
#[derive(Default, Clone)]
pub struct OrdMap {
    idx: HashMap<Name, usize>,
    pub items: Vec<(Name, Sym)>,
}
impl OrdMap {
    pub fn get(&self, k: Name) -> Option<Sym> {
        self.idx.get(&k).map(|&i| self.items[i].1)
    }
    pub fn set(&mut self, k: Name, v: Sym) {
        match self.idx.get(&k) {
            Some(&i) => self.items[i].1 = v,
            None => {
                self.idx.insert(k, self.items.len());
                self.items.push((k, v));
            }
        }
    }
}

pub struct Assume {
    pub e: N,
    pub name: Option<Name>,
    pub module: Name,
}

#[derive(Default)]
pub struct ModuleInfo {
    pub name: Option<Name>,
    pub syms: OrdMap,
    pub exports: OrdMap,
    pub consts: Vec<&'static Decl>,
    pub vars: Vec<&'static Decl>,
    pub assumes: Vec<&'static Assume>,
    pub own_defs: Vec<&'static Def>,
}

pub type SourceResolver = Box<dyn Fn(&str) -> Option<String>>;

type Scope = Vec<(Name, bool, Option<LocalDef>)>;

pub struct Loader {
    pub modules: HashMap<Name, Rc<ModuleInfo>>,
    pub builtins: HashMap<Name, Rc<ModuleInfo>>,
    pub resolve_source: SourceResolver,
    pub load_order: Vec<Name>,
    loading: HashSet<Name>,
    pub globals: OrdMap,
    extra_sources: HashMap<String, String>,
}

fn sem_err<T>(msg: String, loc: Option<Loc>, module: Name) -> R<T> {
    Err(Box::new(Fail::Tla(TlaError { msg, loc, module: Some(name_str(module).to_string()), kind: "semantic" })))
}

fn contains_ptr<T>(v: &[&'static T], x: &'static T) -> bool {
    v.iter().any(|y| std::ptr::eq(*y, x))
}

impl Loader {
    pub fn new(resolve_source: SourceResolver, builtins: HashMap<Name, Rc<ModuleInfo>>) -> Loader {
        Loader { modules: HashMap::new(), builtins, resolve_source, load_order: vec![], loading: HashSet::new(), globals: OrdMap::default(), extra_sources: HashMap::new() }
    }

    fn scan_extra_modules(&mut self, src: &str) {
        // /^[ \t]*-{4,}[ \t]*MODULE[ \t]+(\w+)[ \t]*-{4,}/gm
        let mut first = true;
        let mut offset = 0usize;
        let mut nl = 0usize;
        for line in src.split('\n') {
            let b = line.as_bytes();
            let mut i = 0;
            let ws = |i: &mut usize| {
                while *i < b.len() && (b[*i] == b' ' || b[*i] == b'\t') {
                    *i += 1;
                }
            };
            let dashes = |i: &mut usize| -> bool {
                let s = *i;
                while *i < b.len() && b[*i] == b'-' {
                    *i += 1;
                }
                *i - s >= 4
            };
            ws(&mut i);
            let mut found: Option<String> = None;
            if dashes(&mut i) {
                ws(&mut i);
                if line[i..].starts_with("MODULE") {
                    i += 6;
                    let s = i;
                    ws(&mut i);
                    if i > s {
                        let w = i;
                        while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                            i += 1;
                        }
                        if i > w {
                            let word = &line[w..i];
                            ws(&mut i);
                            if dashes(&mut i) {
                                found = Some(word.to_string());
                            }
                        }
                    }
                }
            }
            if let Some(w) = found {
                if first {
                    first = false;
                } else if !self.extra_sources.contains_key(&w) {
                    self.extra_sources.insert(w, "\n".repeat(nl) + &src[offset..]);
                }
            }
            offset += line.len() + 1;
            nl += 1;
        }
    }

    pub fn load(&mut self, name: Name, from: Option<Name>) -> R<Rc<ModuleInfo>> {
        if let Some(m) = self.modules.get(&name) {
            return Ok(m.clone());
        }
        if let Some(b) = self.builtins.get(&name) {
            let b = b.clone();
            self.modules.insert(name, b.clone());
            return Ok(b);
        }
        if self.loading.contains(&name) {
            return sem_err(format!("Circular dependency among modules involving {}", name), None, name);
        }
        let mut src = (self.resolve_source)(&name_str(name));
        // A file may hold several top-level modules; the later ones are found by name when no file exists.
        match &src {
            None => src = self.extra_sources.get(&*name_str(name)).cloned(),
            Some(s) => {
                let s = s.clone();
                self.scan_extra_modules(&s)
            }
        }
        let src = match src {
            Some(s) => s,
            None => {
                let msg = format!("Cannot find source file for module {}{}.", name, from.map(|f| format!(" imported in module {}", f)).unwrap_or_default());
                return Err(Box::new(Fail::Tla(TlaError { msg, loc: None, module: from.map(|f| name_str(f).to_string()), kind: "semantic" })));
            }
        };
        self.loading.insert(name);
        let ast: &'static ModuleNode = leak(parse_module(&src, &name_str(name))?);
        if ast.name != name {
            return sem_err(format!("File name '{}' does not match the name '{}' of the top level module it contains.", name, ast.name), None, name);
        }
        let info = Rc::new(self.process(ast, None)?);
        self.loading.remove(&name);
        self.modules.insert(name, info.clone());
        self.load_order.push(name);
        Ok(info)
    }

    fn process(&mut self, ast: &'static ModuleNode, outer: Option<&ModuleInfo>) -> R<ModuleInfo> {
        let mut info = ModuleInfo { name: Some(ast.name), ..Default::default() };
        if let Some(o) = outer {
            for (k, v) in &o.syms.items {
                info.syms.set(*k, *v);
            }
        }
        let mut inner: HashMap<Name, Rc<ModuleInfo>> = HashMap::new();
        fn add(info: &mut ModuleInfo, outer: Option<&ModuleInfo>, me: Name, name: Name, sym: Sym, local: bool, loc: Loc) -> R<()> {
            if let Some(prev) = info.syms.get(name) {
                if !prev.same(&sym) {
                    let own = sym.module() == me && !sym.is_inst();
                    let prev_own = prev.module() == me && !prev.is_inst();
                    if !own {
                        return Ok(()); // imported symbols: first one wins
                    }
                    if prev_own && !outer.map_or(false, |o| o.syms.get(name).map_or(false, |x| x.same(&prev))) {
                        return sem_err(format!("Multiply-defined symbol '{}' in module {}", name, me), Some(loc), me);
                    }
                }
            }
            info.syms.set(name, sym);
            if !local {
                info.exports.set(name, sym);
            }
            Ok(())
        }
        let me = ast.name;
        for m in &ast.extends {
            let ext = self.load(*m, Some(me))?;
            for (k, v) in &ext.exports.items {
                add(&mut info, outer, me, *k, *v, false, [0; 4])?;
            }
            for c in &ext.consts {
                if !contains_ptr(&info.consts, c) {
                    info.consts.push(c);
                }
            }
            for v in &ext.vars {
                if !contains_ptr(&info.vars, v) {
                    info.vars.push(v);
                }
            }
            for a in &ext.assumes {
                if !contains_ptr(&info.assumes, a) {
                    info.assumes.push(a);
                }
            }
        }
        let mut resolve_later: Vec<(&'static InstNode, Rc<Vec<InstSubst>>)> = vec![];
        let mut theorem_defs: Vec<&'static Def> = vec![];
        for u in &ast.units {
            match u {
                Unit::Variables(names) => {
                    for n in names {
                        let d = leak(Decl { is_var: true, name: *n, arity: 0, idx: Cell::new(-1), module: me, value: RefCell::new(None), subst: Cell::new(None) });
                        info.vars.push(d);
                        add(&mut info, outer, me, *n, Sym::Decl(d), false, [0; 4])?;
                    }
                }
                Unit::Constants(decls) => {
                    for p in decls {
                        let d = leak(Decl { is_var: false, name: p.name, arity: p.arity, idx: Cell::new(-1), module: me, value: RefCell::new(None), subst: Cell::new(None) });
                        info.consts.push(d);
                        add(&mut info, outer, me, p.name, Sym::Decl(d), false, [0; 4])?;
                    }
                }
                Unit::Def(dn) => {
                    let def = leak(Def::new(dn.name, dn.params.clone(), Some(&dn.body), me, dn.local, dn.loc));
                    add(&mut info, outer, me, dn.name, Sym::Def(def), dn.local, dn.loc)?;
                    info.own_defs.push(def);
                }
                Unit::Instance(u) => {
                    // importInstance
                    let m = match inner.get(&u.module) {
                        Some(m) => m.clone(),
                        None => self.load(u.module, Some(me))?,
                    };
                    let mut explicit: HashMap<Name, N> = HashMap::new();
                    for (sn, se) in &u.substs {
                        if !m.consts.iter().any(|c| c.name == *sn) && !m.vars.iter().any(|v| v.name == *sn) {
                            return sem_err(format!("Substitution target '{}' is not a CONSTANT or VARIABLE of module {}", sn, u.module), Some(u.loc), me);
                        }
                        explicit.insert(*sn, se);
                    }
                    let mut substs: Vec<InstSubst> = vec![];
                    for d in m.consts.iter().chain(m.vars.iter()) {
                        let e: N = match explicit.get(&d.name) {
                            Some(e) => e,
                            None => leak(Node::new(u.loc, E::App { name: d.name, args: vec![], sel: None, r: Cell::new(Res::None), implicit: true })),
                        };
                        substs.push(InstSubst { name: d.name, e, arity: d.arity });
                    }
                    let substs = Rc::new(substs);
                    let prefix = u.name;
                    for (nm, sym) in &m.exports.items {
                        let sd = match sym {
                            Sym::Def(d) => *d,
                            _ => continue,
                        };
                        if sd.builtin.get().is_some() && prefix.is_none() {
                            add(&mut info, outer, me, *nm, *sym, u.local, sd.loc)?;
                            continue;
                        }
                        if substs.is_empty() && u.params.is_empty() && prefix.is_none() {
                            add(&mut info, outer, me, *nm, *sym, u.local, sd.loc)?;
                            continue;
                        }
                        let dname = match prefix {
                            Some(p) => name(&format!("{}!{}", p, nm)),
                            None => *nm,
                        };
                        let mut params = u.params.clone();
                        params.extend(sd.params.iter().cloned());
                        let mut def = Def::new(dname, params, None, me, u.local, sd.loc);
                        def.inst = Some(Inst { orig: sd, substs: substs.clone(), nparams: u.params.len(), env_cache: RefCell::new(None) });
                        let def = leak(def);
                        add(&mut info, outer, me, dname, Sym::Def(def), u.local, sd.loc)?;
                    }
                    resolve_later.push((u, substs));
                }
                Unit::Assume { name: nm, e, loc } => {
                    info.assumes.push(leak(Assume { e, name: *nm, module: me }));
                    if let Some(nm) = nm {
                        let def = leak(Def::new(*nm, vec![], Some(e), me, false, *loc));
                        add(&mut info, outer, me, *nm, Sym::Def(def), false, *loc)?;
                    }
                }
                Unit::Theorem { name: nm, e, loc } => {
                    if let Some(nm) = nm {
                        if !matches!(e.e, E::AssumeProve) {
                            let def = leak(Def::new(*nm, vec![], Some(e), me, false, *loc));
                            add(&mut info, outer, me, *nm, Sym::Def(def), false, *loc)?;
                            info.own_defs.push(def);
                            theorem_defs.push(def);
                        }
                    }
                }
                Unit::Module(m) => {
                    let i = self.process(m, Some(&info))?;
                    inner.insert(m.name, Rc::new(i));
                }
                Unit::Recursive => {}
            }
        }
        // pass 2: resolve names
        for d in info.own_defs.clone() {
            let mut scope: Scope = d.params.iter().map(|p| (p.name, false, None)).collect();
            let body = d.body.get().unwrap();
            if let Err(e) = self.resolve(body, &mut scope, &info) {
                // Theorems may mention things we do not model (proof-only constructs); ignore them.
                if !matches!(*e, Fail::Tla(_)) || !contains_ptr(&theorem_defs, d) {
                    return Err(e);
                }
                d.body.set(Some(leak(Node::new(d.loc, E::Bool(true)))));
            }
        }
        for a in info.assumes.clone() {
            if a.module == me {
                self.resolve(a.e, &mut vec![], &info)?;
            }
        }
        for (u, substs) in resolve_later {
            let mut scope: Scope = u.params.iter().map(|p| (p.name, false, None)).collect();
            for s in substs.iter() {
                if matches!(s.e.e, E::App { .. }) {
                    s.e.op_arg.set(true);
                }
                self.resolve(s.e, &mut scope, &info)?;
            }
        }
        for s in &ast.strings {
            str_id(s);
        }
        Ok(info)
    }

    fn resolve_bounds(&mut self, bs: &'static [Bound], scope: &mut Scope, m: &ModuleInfo) -> R<()> {
        for b in bs {
            if let Some(s) = &b.set {
                self.resolve(s, scope, m)?;
            }
        }
        Ok(())
    }

    fn resolve(&mut self, n: N, scope: &mut Scope, m: &ModuleInfo) -> R<()> {
        n.module.set(m.name);
        let mark = scope.len();
        fn push_bound(scope: &mut Scope, b: &Bound) {
            if let Some(ns) = &b.names {
                scope.extend(ns.iter().map(|x| (*x, false, None)));
            } else if let Some(t) = &b.tuple {
                scope.extend(t.iter().map(|x| (*x, false, None)));
            }
        }
        match &n.e {
            E::Num(_) | E::Str(..) | E::Bool(_) | E::At | E::StepRef | E::AssumeProve => {}
            E::App { name: nm, args, sel, r, .. } => {
                if let Some(e) = scope.iter_mut().rev().find(|e| e.0 == *nm) {
                    e.1 = true;
                    r.set(Res::Local);
                    if e.2.is_some() {
                        n.ld.set(e.2);
                    }
                } else {
                    let sym = match m.syms.get(*nm).or_else(|| self.globals.get(*nm)) {
                        Some(s) => s,
                        None => return sem_err(format!("Unknown operator: `{}'.", nm), Some(n.loc), m.name.unwrap()),
                    };
                    let want = match sym {
                        Sym::Decl(d) => {
                            r.set(Res::Decl(d));
                            if d.is_var { 0 } else { d.arity }
                        }
                        Sym::Def(d) => {
                            r.set(Res::Def(d));
                            d.resolved().params.len()
                        }
                    };
                    // arity check (a bare operator name is fine where an operator argument is expected)
                    if sel.is_none() && args.len() != want && !(args.is_empty() && n.op_arg.get()) {
                        let l = n.loc;
                        return sem_err(
                            format!("line {}, col {} to line {}, col {} of module {}\n\nThe operator {} requires {} arguments.", l[0], l[1], l[2], l[3], m.name.unwrap(), nm, want),
                            Some(n.loc),
                            m.name.unwrap(),
                        );
                    }
                }
                for a in args {
                    if let E::App { args: aa, .. } = &a.e {
                        if aa.is_empty() {
                            a.op_arg.set(true);
                        }
                    }
                    self.resolve(a, scope, m)?;
                }
                if let Some(sel) = sel {
                    for s in sel {
                        if let Sel::Args(a) = s {
                            for x in a {
                                self.resolve(x, scope, m)?;
                            }
                        }
                    }
                }
            }
            E::Quant { bounds, body, .. } => {
                self.resolve_bounds(bounds, scope, m)?;
                for b in bounds {
                    push_bound(scope, b);
                }
                self.resolve(body, scope, m)?;
            }
            E::SetMap { e, bounds } => {
                self.resolve_bounds(bounds, scope, m)?;
                for b in bounds {
                    push_bound(scope, b);
                }
                self.resolve(e, scope, m)?;
            }
            E::FnDef { bounds, body, recname, is_rec } => {
                self.resolve_bounds(bounds, scope, m)?;
                for b in bounds {
                    push_bound(scope, b);
                }
                if let Some(rn) = recname {
                    scope.push((*rn, false, Some(LocalDef::Fn)));
                }
                self.resolve(body, scope, m)?;
                if let Some(rn) = recname {
                    // the innermost entry with that name within this frame
                    let used = scope[mark..].iter().rev().find(|e| e.0 == *rn).map_or(false, |e| e.1);
                    is_rec.set(used);
                }
            }
            E::Choose { bound, body } => {
                if let Some(s) = &bound.set {
                    self.resolve(s, scope, m)?;
                }
                push_bound(scope, bound);
                self.resolve(body, scope, m)?;
            }
            E::SetFilter { bound, pred } => {
                if let Some(s) = &bound.set {
                    self.resolve(s, scope, m)?;
                }
                push_bound(scope, bound);
                self.resolve(pred, scope, m)?;
            }
            E::TQuant { names, body } => {
                scope.extend(names.iter().map(|x| (*x, false, None)));
                self.resolve(body, scope, m)?;
            }
            E::Lambda { params, body } => {
                scope.extend(params.iter().map(|p| (p.name, false, None)));
                self.resolve(body, scope, m)?;
            }
            E::Let { defs, body } => {
                let mut names: Vec<Name> = vec![];
                for d in defs {
                    match d {
                        LetDef::Def(d) => names.push(d.name),
                        LetDef::Inst(d) => {
                            if d.inst_defs.get().is_none() {
                                let im = self.load(d.module, m.name)?;
                                let mut substs = vec![];
                                for c in im.consts.iter().chain(im.vars.iter()) {
                                    let e: N = match d.substs.iter().find(|x| x.0 == c.name) {
                                        Some(x) => &x.1,
                                        None => leak(Node::new(d.loc, E::App { name: c.name, args: vec![], sel: None, r: Cell::new(Res::None), implicit: true })),
                                    };
                                    substs.push(InstSubst { name: c.name, arity: c.arity, e });
                                }
                                let substs = Rc::new(substs);
                                let mut idefs: Vec<&'static Def> = vec![];
                                let prefix = d.name.map(|x| name_str(x).to_string()).unwrap_or_else(|| "null".into());
                                for (nm, sym) in &im.exports.items {
                                    if let Sym::Def(sd) = sym {
                                        let mut params = d.params.clone();
                                        params.extend(sd.params.iter().cloned());
                                        let mut def = Def::new(name(&format!("{}!{}", prefix, nm)), params, None, m.name.unwrap(), true, sd.loc);
                                        def.inst = Some(Inst { orig: sd, substs: substs.clone(), nparams: d.params.len(), env_cache: RefCell::new(None) });
                                        idefs.push(leak(def));
                                    }
                                }
                                let _ = d.inst_substs.set(substs);
                                let _ = d.inst_defs.set(idefs);
                            }
                            for x in d.inst_defs.get().unwrap() {
                                names.push(x.name);
                            }
                        }
                    }
                }
                let let_start = scope.len();
                scope.extend(names.iter().map(|x| (*x, false, None)));
                for d in defs {
                    if let LetDef::Def(d) = d {
                        if d.params.is_empty() {
                            if let Some(e) = scope[let_start..].iter_mut().rev().find(|e| e.0 == d.name) {
                                e.2 = Some(LocalDef::Let(d));
                            }
                        }
                    }
                }
                let s = scope.len();
                for d in defs {
                    match d {
                        LetDef::Inst(d) => {
                            scope.extend(d.params.iter().map(|p| (p.name, false, None)));
                            for x in d.inst_substs.get().unwrap().iter() {
                                if matches!(x.e.e, E::App { .. }) {
                                    x.e.op_arg.set(true);
                                }
                                self.resolve(x.e, scope, m)?;
                            }
                            scope.truncate(s);
                        }
                        LetDef::Def(d) => {
                            scope.extend(d.params.iter().map(|p| (p.name, false, None)));
                            self.resolve(&d.body, scope, m)?;
                            // keep `used` marks of outer names; drop the parameter frame
                            scope.truncate(s);
                        }
                    }
                }
                self.resolve(body, scope, m)?;
            }
            E::Case { arms, other } => {
                for (c, e) in arms {
                    self.resolve(c, scope, m)?;
                    self.resolve(e, scope, m)?;
                }
                if let Some(o) = other {
                    self.resolve(o, scope, m)?;
                }
            }
            E::Rec(fields, _) | E::RecSet(fields) => {
                for (_, e) in fields {
                    self.resolve(e, scope, m)?;
                }
            }
            E::Except { base, updates } => {
                self.resolve(base, scope, m)?;
                for (path, val) in updates {
                    for p in path {
                        self.resolve(p, scope, m)?;
                    }
                    self.resolve(val, scope, m)?;
                }
            }
            E::FnApp { f, args } => {
                self.resolve(f, scope, m)?;
                for a in args {
                    self.resolve(a, scope, m)?;
                }
            }
            E::Dot { e, .. } => self.resolve(e, scope, m)?,
            E::Op(_, a) => {
                for x in a {
                    self.resolve(x, scope, m)?;
                }
            }
        }
        scope.truncate(mark);
        Ok(())
    }
}

// ---- expression levels: 0 constant, 1 state, 2 action, 3 temporal ----
pub fn level_of(n: N) -> i8 {
    let c = n.lvl.get();
    if c >= 0 {
        return c;
    }
    let mut l: i8 = 0;
    macro_rules! up {
        ($x:expr) => {{
            let v = level_of($x);
            if v > l {
                l = v;
            }
        }};
    }
    match &n.e {
        E::Num(_) | E::Str(..) | E::Bool(_) | E::At | E::StepRef | E::AssumeProve => {}
        E::App { args, r, .. } => {
            match r.get() {
                Res::Decl(d) => {
                    if d.is_var {
                        l = 1;
                    } else if let Some(s) = d.subst.get() {
                        l = def_level(s);
                    }
                }
                Res::Def(d) => l = def_level(d),
                _ => {}
            }
            for (i, a) in args.iter().enumerate() {
                // an action argument that the operator only uses under ENABLED contributes state level
                let only_enabled = level_of(a) == 2 && l < 2 && matches!(r.get(), Res::Def(d) if param_only_enabled(d, i));
                if only_enabled {
                    if l < 1 {
                        l = 1;
                    }
                } else {
                    up!(a);
                }
            }
        }
        E::Op(k, a) => match k {
            K::Prime | K::Unchanged | K::BoxAct | K::AngleAct | K::Cdot => l = 2,
            K::Enabled => l = 1,
            K::Always | K::Eventually | K::LeadsTo | K::Guarantee | K::Wf | K::Sf => l = 3,
            _ => {
                for x in a {
                    up!(x);
                }
            }
        },
        E::TQuant { .. } => l = 3,
        E::Quant { bounds, body, .. } | E::FnDef { bounds, body, .. } => {
            for b in bounds {
                if let Some(s) = &b.set {
                    up!(s);
                }
            }
            up!(body);
        }
        E::SetMap { e, bounds } => {
            for b in bounds {
                if let Some(s) = &b.set {
                    up!(s);
                }
            }
            up!(e);
        }
        E::Choose { bound, body } => {
            if let Some(s) = &bound.set {
                up!(s);
            }
            up!(body);
        }
        E::SetFilter { bound, pred } => {
            if let Some(s) = &bound.set {
                up!(s);
            }
            up!(pred);
        }
        E::Lambda { body, .. } => up!(body),
        E::Let { defs, body } => {
            for d in defs {
                if let LetDef::Def(d) = d {
                    up!(&d.body);
                }
            }
            up!(body);
        }
        E::Case { arms, other } => {
            for (c, e) in arms {
                up!(c);
                up!(e);
            }
            if let Some(o) = other {
                up!(o);
            }
        }
        E::Rec(f, _) | E::RecSet(f) => {
            for (_, e) in f {
                up!(e);
            }
        }
        E::Except { base, updates } => {
            up!(base);
            for (path, val) in updates {
                for p in path {
                    up!(p);
                }
                up!(val);
            }
        }
        E::FnApp { f, args } => {
            up!(f);
            for a in args {
                up!(a);
            }
        }
        E::Dot { e, .. } => up!(e),
    }
    n.lvl.set(l);
    l
}

pub fn def_level(d: &'static Def) -> i8 {
    if let Some(o) = d.over.get() {
        return def_level(o);
    }
    if d.level.get() >= 0 {
        return d.level.get();
    }
    d.level.set(0); // recursion guard
    let mut l = 0;
    if let Some(inst) = &d.inst {
        l = def_level(inst.orig);
        let refs = decl_refs(inst.orig);
        let refs = refs.borrow().clone();
        for s in inst.substs.iter() {
            if refs.contains(&s.name) {
                l = l.max(level_of(s.e));
            }
        }
    } else if let Some(b) = d.body.get() {
        l = level_of(b);
    }
    d.level.set(l);
    l
}

/// Names of CONSTANT/VARIABLE declarations a definition (transitively) depends on.
pub fn decl_refs(d: &'static Def) -> Rc<RefCell<HashSet<Name>>> {
    if let Some(r) = d.refs.borrow().as_ref() {
        return r.clone();
    }
    let out = Rc::new(RefCell::new(HashSet::new()));
    *d.refs.borrow_mut() = Some(out.clone());
    if let Some(inst) = &d.inst {
        let inner = decl_refs(inst.orig).borrow().clone();
        for s in inst.substs.iter() {
            if inner.contains(&s.name) {
                collect_refs(s.e, &out);
            }
        }
    } else if let Some(b) = d.body.get() {
        collect_refs(b, &out);
    }
    out
}

fn collect_refs(n: N, out: &Rc<RefCell<HashSet<Name>>>) {
    if let E::App { r, .. } = &n.e {
        match r.get() {
            Res::Def(d) => {
                let inner = decl_refs(d);
                if !Rc::ptr_eq(&inner, out) {
                    let items: Vec<Name> = inner.borrow().iter().copied().collect();
                    out.borrow_mut().extend(items);
                }
            }
            Res::Decl(d) => {
                out.borrow_mut().insert(d.name);
            }
            _ => {}
        }
    }
    for_children(n, &mut |c| collect_refs(c, out));
}

/// Calls `f` on every direct child expression of `n` (including LET definitions and instance substitutions).
pub fn for_children(n: N, f: &mut dyn FnMut(N)) {
    let mut bounds = |bs: &'static [Bound], f: &mut dyn FnMut(N)| {
        for b in bs {
            if let Some(s) = &b.set {
                f(s);
            }
        }
    };
    match &n.e {
        E::Num(_) | E::Str(..) | E::Bool(_) | E::At | E::StepRef | E::AssumeProve => {}
        E::App { args, sel, .. } => {
            for a in args {
                f(a);
            }
            if let Some(sel) = sel {
                for s in sel {
                    if let Sel::Args(a) = s {
                        for x in a {
                            f(x);
                        }
                    }
                }
            }
        }
        E::Op(_, a) => {
            for x in a {
                f(x);
            }
        }
        E::Case { arms, other } => {
            for (c, e) in arms {
                f(c);
                f(e);
            }
            if let Some(o) = other {
                f(o);
            }
        }
        E::Let { defs, body } => {
            for d in defs {
                match d {
                    LetDef::Def(d) => f(&d.body),
                    LetDef::Inst(d) => match d.inst_substs.get() {
                        Some(ss) => {
                            for s in ss.iter() {
                                f(s.e);
                            }
                        }
                        None => {
                            for s in &d.substs {
                                f(&s.1);
                            }
                        }
                    },
                }
            }
            f(body);
        }
        E::Quant { bounds: bs, body, .. } | E::FnDef { bounds: bs, body, .. } => {
            bounds(bs, f);
            f(body);
        }
        E::SetMap { e, bounds: bs } => {
            f(e);
            bounds(bs, f);
        }
        E::Choose { bound, body } => {
            if let Some(s) = &bound.set {
                f(s);
            }
            f(body);
        }
        E::SetFilter { bound, pred } => {
            if let Some(s) = &bound.set {
                f(s);
            }
            f(pred);
        }
        E::Rec(fs, _) | E::RecSet(fs) => {
            for (_, e) in fs {
                f(e);
            }
        }
        E::Except { base, updates } => {
            f(base);
            for (path, val) in updates {
                for p in path {
                    f(p);
                }
                f(val);
            }
        }
        E::FnApp { f: fun, args } => {
            f(fun);
            for a in args {
                f(a);
            }
        }
        E::Dot { e, .. } => f(e),
        E::Lambda { body, .. } | E::TQuant { body, .. } => f(body),
    }
}

/// Can evaluating `n` yield a function constructor directly (through IF/CASE/LET/definitions)? TLC keeps such a
/// function unevaluated when it is immediately applied (f[x]) or is the body of a recursive function.
pub fn tail_fn(n: N) -> bool {
    let c = n.tf.get();
    if c >= 0 {
        return c == 1;
    }
    n.tf.set(0); // recursion guard
    let r = match &n.e {
        E::FnDef { .. } => true,
        E::Op(K::If, a) => tail_fn(&a[1]) || tail_fn(&a[2]),
        E::Case { arms, other } => arms.iter().any(|(_, e)| tail_fn(e)) || other.as_ref().map_or(false, |o| tail_fn(o)),
        E::Let { body, .. } => tail_fn(body),
        E::FnApp { f, .. } => tail_fn(f),
        E::App { args, sel, r, .. } if sel.is_none() => match r.get() {
            Res::Local => match n.ld.get() {
                Some(LocalDef::Fn) if args.is_empty() => true,
                Some(LocalDef::Let(d)) if args.is_empty() => tail_fn(&d.body),
                _ => false,
            },
            Res::Def(x) => {
                let mut d = x.resolved();
                while let Some(inst) = &d.inst {
                    d = inst.orig.resolved();
                }
                match d.body.get() {
                    Some(b) if d.builtin.get().is_none() => tail_fn(b),
                    _ => false,
                }
            }
            _ => false,
        },
        _ => false,
    };
    n.tf.set(r as i8);
    r
}

/// Does definition `d0` use its i-th parameter only inside ENABLED?
fn param_only_enabled(d0: &'static Def, i: usize) -> bool {
    let mut d = d0.resolved();
    let mut skip = 0;
    while let Some(inst) = &d.inst {
        skip += inst.nparams;
        d = inst.orig.resolved();
    }
    if i < skip {
        return false;
    }
    let i = i - skip;
    let body = match d.body.get() {
        Some(b) if i < d.params.len() => b,
        _ => return false,
    };
    if let Some(Some(v)) = d.enabled_only.borrow().get(i) {
        return *v;
    }
    let pname = d.params[i].name;
    let mut used = false;
    fn walk(x: N, pname: Name, used: &mut bool) -> bool {
        if x.is_k(K::Enabled) {
            *used = true;
            return true;
        }
        if let E::App { name, r, .. } = &x.e {
            if *name == pname && matches!(r.get(), Res::Local) {
                return false;
            }
        }
        let mut ok = true;
        for_children(x, &mut |c| {
            if ok && !walk(c, pname, used) {
                ok = false;
            }
        });
        ok
    }
    let v = walk(body, pname, &mut used) && used;
    let mut c = d.enabled_only.borrow_mut();
    if c.len() <= i {
        c.resize(i + 1, None);
    }
    c[i] = Some(v);
    v
}
