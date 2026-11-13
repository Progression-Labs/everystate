//! AST. Modules are parsed into owned trees and then leaked, so that the evaluator can hold
//! `&'static Node` references freely.
use crate::intern::*;
use crate::modules::{Decl, Def};
use std::cell::{Cell, OnceCell};
use std::rc::Rc;

pub type N = &'static Node;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum K {
    And,
    Or,
    Not,
    Imp,
    Eqv,
    Eq,
    Ne,
    In,
    NotIn,
    Subseteq,
    Cup,
    Cap,
    Diff,
    Powerset,
    BigUnion,
    Domain,
    Prime,
    Enabled,
    Unchanged,
    Cross,
    If,
    SetEnum,
    FnSet,
    Tuple,
    BoxAct,
    AngleAct,
    Always,
    Eventually,
    LeadsTo,
    Guarantee,
    Wf,
    Sf,
    Cdot,
}

#[derive(Copy, Clone)]
pub enum Res {
    None,
    Local,
    Decl(&'static Decl),
    Def(&'static Def),
}

#[derive(Clone, Debug)]
pub struct Param {
    pub name: Name,
    pub arity: usize,
}

pub struct Bound {
    pub names: Option<Vec<Name>>,
    pub tuple: Option<Vec<Name>>,
    pub set: Option<Box<Node>>,
}

pub enum Sel {
    Num(i64),
    Sym(Rc<str>),
    Args(Vec<Node>),
}

pub struct DefNode {
    pub name: Name,
    pub params: Vec<Param>,
    pub body: Node,
    pub local: bool,
    pub loc: Loc,
}

pub struct InstSubst {
    pub name: Name,
    pub e: N,
    pub arity: usize,
}

pub struct InstNode {
    pub module: Name,
    pub substs: Vec<(Name, Node)>,
    pub local: bool,
    pub name: Option<Name>,
    pub params: Vec<Param>,
    pub loc: Loc,
    // filled in by name resolution when the instance appears in a LET
    pub inst_defs: OnceCell<Vec<&'static Def>>,
    pub inst_substs: OnceCell<Rc<Vec<InstSubst>>>,
}

pub struct RecShape {
    pub names: Rc<Vec<StrId>>,
    pub order: Option<Vec<usize>>,
}

pub enum LetDef {
    Def(DefNode),
    Inst(InstNode),
}

pub enum E {
    Num(i64),
    Str(Rc<str>, Cell<Option<StrId>>),
    Bool(bool),
    At,
    StepRef,
    AssumeProve,
    App { name: Name, args: Vec<Node>, sel: Option<Vec<Sel>>, r: Cell<Res>, implicit: bool },
    Op(K, Vec<Node>),
    Case { arms: Vec<(Node, Node)>, other: Option<Box<Node>> },
    Let { defs: Vec<LetDef>, body: Box<Node> },
    Quant { forall: bool, bounds: Vec<Bound>, body: Box<Node> },
    Choose { bound: Bound, body: Box<Node> },
    SetFilter { bound: Bound, pred: Box<Node> },
    SetMap { e: Box<Node>, bounds: Vec<Bound> },
    FnDef { bounds: Vec<Bound>, body: Box<Node>, recname: Option<Name>, is_rec: Cell<bool> },
    Rec(Vec<(StrId, Node)>, OnceCell<RecShape>),
    RecSet(Vec<(StrId, Node)>),
    Except { base: Box<Node>, updates: Vec<(Vec<Node>, Node)> },
    FnApp { f: Box<Node>, args: Vec<Node> },
    Dot { e: Box<Node>, field: StrId },
    Lambda { params: Vec<Param>, body: Box<Node> },
    TQuant { names: Vec<Name>, body: Box<Node> },
}

/// What a locally resolved name refers to, when that is a function definition or a zero-argument LET definition.
#[derive(Copy, Clone)]
pub enum LocalDef {
    Fn,                      // the enclosing recursive function itself
    Let(&'static DefNode), // a LET definition without parameters
}

pub struct Node {
    pub loc: Loc,
    pub module: Cell<Option<Name>>,
    pub lvl: Cell<i8>,
    pub tf: Cell<i8>,                    // cache of modules::tail_fn (-1 unknown)
    pub op_arg: Cell<bool>,              // a bare operator name where an operator argument is expected
    pub ld: Cell<Option<LocalDef>>,      // App resolved to a local definition
    pub junction: bool,
    pub paren: bool,
    pub e: E,
}

impl Node {
    pub fn new(loc: Loc, e: E) -> Node {
        Node { loc, module: Cell::new(None), lvl: Cell::new(-1), tf: Cell::new(-1), op_arg: Cell::new(false), ld: Cell::new(None), junction: false, paren: false, e }
    }
    pub fn is_k(&self, k: K) -> bool {
        matches!(&self.e, E::Op(k2, _) if *k2 == k)
    }
    pub fn module_str(&self) -> Option<String> {
        self.module.get().map(|m| name_str(m).to_string())
    }
}

pub enum Unit {
    Variables(Vec<Name>),
    Constants(Vec<Param>),
    Recursive,
    Def(DefNode),
    Instance(InstNode),
    Assume { name: Option<Name>, e: Node, loc: Loc, axiom: bool },
    Theorem { name: Option<Name>, e: Node, loc: Loc },
    Module(ModuleNode),
}

pub struct ModuleNode {
    pub name: Name,
    pub extends: Vec<Name>,
    pub units: Vec<Unit>,
    pub strings: Vec<Rc<str>>,
}
