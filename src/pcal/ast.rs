//! The PlusCal abstract syntax tree (port of pcal.AST).  The Java translator shares and mutates
//! nodes and vectors freely (and the checksum of the algorithm is computed from the tree after
//! those mutations), so nodes and vectors are reference-counted, interior-mutable objects here.
use super::expr::{jlen, new_expr, Expr};
use std::cell::{Cell, RefCell};
use std::rc::Rc;

/// A `java.util.Vector`: a shared, growable list.
pub struct V<T>(pub Rc<RefCell<Vec<T>>>);
impl<T> Clone for V<T> {
    fn clone(&self) -> Self {
        V(self.0.clone())
    }
}
impl<T: Clone> V<T> {
    pub fn new() -> Self {
        V(Rc::new(RefCell::new(Vec::new())))
    }
    pub fn of(v: Vec<T>) -> Self {
        V(Rc::new(RefCell::new(v)))
    }
    pub fn len(&self) -> usize {
        self.0.borrow().len()
    }
    pub fn is_empty(&self) -> bool {
        self.0.borrow().is_empty()
    }
    pub fn get(&self, i: usize) -> T {
        self.0.borrow()[i].clone()
    }
    pub fn try_get(&self, i: usize) -> Option<T> {
        self.0.borrow().get(i).cloned()
    }
    pub fn last(&self) -> Option<T> {
        self.0.borrow().last().cloned()
    }
    pub fn push(&self, x: T) {
        self.0.borrow_mut().push(x)
    }
    pub fn insert(&self, i: usize, x: T) {
        self.0.borrow_mut().insert(i, x)
    }
    pub fn remove(&self, i: usize) -> T {
        self.0.borrow_mut().remove(i)
    }
    pub fn set(&self, i: usize, x: T) {
        self.0.borrow_mut()[i] = x
    }
    pub fn clear(&self) {
        self.0.borrow_mut().clear()
    }
    pub fn to_vec(&self) -> Vec<T> {
        self.0.borrow().clone()
    }
    /// `new Vector(v)`: a fresh vector with the same elements.
    pub fn copy(&self) -> Self {
        V::of(self.to_vec())
    }
    pub fn add_all(&self, other: &V<T>) {
        let items = other.to_vec();
        self.0.borrow_mut().extend(items);
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum K {
    Uniprocess,
    Multiprocess,
    Procedure,
    Process,
    VarDecl,
    PVarDecl,
    LabeledStmt,
    While,
    Assign,
    SingleAssign,
    Lhs,
    If,
    Either,
    With,
    When,
    PrintS,
    Assert,
    Skip,
    LabelIf,
    LabelEither,
    Clause,
    Call,
    Return,
    CallReturn,
    CallGoto,
    Goto,
    Macro,
    MacroCall,
}

pub const UNFAIR_PROC: i32 = 0;
pub const WF_PROC: i32 = 1;
pub const SF_PROC: i32 = 2;
const FAIRNESS_STRING: [&str; 3] = ["unfair", "wf", "sf"];

pub type Ast = Rc<Node>;
type Slot<T> = RefCell<Option<T>>;

macro_rules! node {
    ($( $f:ident / $set:ident / $opt:ident : $t:ty ),* $(,)?) => {
        /// One node of the tree.  Which fields are meaningful depends on `k`; the field names are
        /// those of the Java classes (`name` also stands for `var` and `label`, `e` for the single
        /// expression of a node: `test`, `exp`, `val`, `id`, `rhs` or `sub`).
        pub struct Node {
            pub k: K,
            pub col: Cell<i32>,
            pub line: Cell<i32>,
            pub macro_col: Cell<i32>,
            pub macro_line: Cell<i32>,
            pub lbl: RefCell<String>,
            pub name: RefCell<String>,
            pub to: RefCell<String>,
            pub from: RefCell<Option<String>>,
            pub after: RefCell<String>,
            pub return_to: RefCell<String>,
            pub is_eq: Cell<bool>,
            pub fairness: Cell<i32>,
            pub has_origin: Cell<bool>,
            $( pub $f: Slot<$t>, )*
        }
        impl Node {
            pub fn new(k: K) -> Ast {
                Rc::new(Node {
                    k,
                    col: Cell::new(0),
                    line: Cell::new(0),
                    macro_col: Cell::new(0),
                    macro_line: Cell::new(-1),
                    lbl: RefCell::new(String::new()),
                    name: RefCell::new(String::new()),
                    to: RefCell::new(String::new()),
                    from: RefCell::new(None),
                    after: RefCell::new(String::new()),
                    return_to: RefCell::new(String::new()),
                    is_eq: Cell::new(true),
                    fairness: Cell::new(UNFAIR_PROC),
                    has_origin: Cell::new(false),
                    $( $f: RefCell::new(None), )*
                })
            }
            $(
                #[allow(dead_code)]
                pub fn $f(&self) -> $t { self.$f.borrow().clone().expect(concat!("null ", stringify!($f))) }
                #[allow(dead_code)]
                pub fn $opt(&self) -> Option<$t> { self.$f.borrow().clone() }
                #[allow(dead_code)]
                pub fn $set(&self, v: $t) { *self.$f.borrow_mut() = Some(v); }
            )*
        }
    };
}

node! {
    e / set_e / e_opt: Expr,
    defs / set_defs / defs_opt: Expr,
    lhs / set_lhs / lhs_opt: Ast,
    decls / set_decls / decls_opt: V<Ast>,
    macros / set_macros / macros_opt: V<Ast>,
    prcds / set_prcds / prcds_opt: V<Ast>,
    procs / set_procs / procs_opt: V<Ast>,
    body / set_body / body_opt: V<Ast>,
    params / set_params / params_opt: V<Ast>,
    sparams / set_sparams / sparams_opt: V<String>,
    stmts / set_stmts / stmts_opt: V<Ast>,
    unlab_do / set_unlab_do / unlab_do_opt: V<Ast>,
    lab_do / set_lab_do / lab_do_opt: V<Ast>,
    ass / set_ass / ass_opt: V<Ast>,
    then / set_then / then_opt: V<Ast>,
    els / set_els / els_opt: V<Ast>,
    ors / set_ors / ors_opt: V<V<Ast>>,
    do_ / set_do / do_opt: V<Ast>,
    unlab_then / set_unlab_then / unlab_then_opt: V<Ast>,
    lab_then / set_lab_then / lab_then_opt: V<Ast>,
    unlab_else / set_unlab_else / unlab_else_opt: V<Ast>,
    lab_else / set_lab_else / lab_else_opt: V<Ast>,
    clauses / set_clauses / clauses_opt: V<Ast>,
    unlab_or / set_unlab_or / unlab_or_opt: V<Ast>,
    lab_or / set_lab_or / lab_or_opt: V<Ast>,
    args / set_args / args_opt: V<Expr>,
    minus_labels / set_minus_labels / minus_labels_opt: V<String>,
    plus_labels / set_plus_labels / plus_labels_opt: V<String>,
    procedures_called / set_procedures_called / procedures_called_opt: V<String>,
}

/// The default initial value of a declared variable (`PcalParams.DefaultVarInit`).
pub fn default_var_init() -> Expr {
    super::expr::make_expr(vec![vec![super::expr::tok("defaultInitValue", 0, 0)]])
}

/// `new AST.X()` with the field initialisers of the Java class.
pub fn new_node(k: K) -> Ast {
    let n = Node::new(k);
    match k {
        K::Procedure | K::Process => {
            n.set_minus_labels(V::new());
            n.set_plus_labels(V::new());
            n.set_procedures_called(V::new());
        }
        K::VarDecl | K::PVarDecl => n.set_e(default_var_init()),
        K::SingleAssign => n.set_lhs(Node::new(K::Lhs)),
        _ => {}
    }
    n
}

impl Node {
    pub fn name(&self) -> String {
        self.name.borrow().clone()
    }
    pub fn set_name(&self, s: &str) {
        *self.name.borrow_mut() = s.to_string();
    }
    pub fn lbl(&self) -> String {
        self.lbl.borrow().clone()
    }
    pub fn to(&self) -> String {
        self.to.borrow().clone()
    }
    pub fn from(&self) -> Option<String> {
        self.from.borrow().clone()
    }
    pub fn location(&self) -> String {
        if self.macro_line.get() < 0 {
            format!("line {}, column {}", self.line.get(), self.col.get())
        } else {
            format!("line {}, column {} of macro called at line {}, column {}", self.line.get(), self.col.get(), self.macro_line.get(), self.macro_col.get())
        }
    }
    /// `PVarDecl.toVarDecl()`
    pub fn to_var_decl(&self) -> Ast {
        let r = Node::new(K::VarDecl);
        r.set_name(&self.name());
        r.set_e(self.e());
        r.has_origin.set(self.has_origin.get());
        r.is_eq.set(true);
        r
    }
}

/// The state of `AST.toString()`: indentation bookkeeping plus the two parameters it reads.
pub struct Printer {
    pub debug: bool,
    pub old_version: bool,
    depth: usize,
    cur: [i32; 256],
}

impl Printer {
    pub fn new(debug: bool, old_version: bool) -> Self {
        Printer { debug, old_version, depth: 0, cur: [0; 256] }
    }
    fn indent(&mut self, s: &str) -> String {
        self.cur[self.depth + 1] = self.cur[self.depth] + jlen(s);
        self.depth += 1;
        s.to_string()
    }
    fn end_indent(&mut self) {
        self.depth -= 1;
    }
    fn new_line(&self) -> String {
        format!("\n{}", " ".repeat(self.cur[self.depth].max(0) as usize))
    }
    fn line_col(&self, n: &Node) -> String {
        if self.debug { format!("(*{}, {}*)", n.line.get(), n.col.get()) } else { String::new() }
    }
    fn seq(&mut self, v: Option<V<Ast>>) -> String {
        let v = match v {
            None => return "null".to_string(),
            Some(v) => v,
        };
        let mut r = self.indent("<<");
        for i in 0..v.len() {
            if i > 0 {
                r += ", ";
                r += &self.new_line();
            }
            let x = v.get(i);
            r += &self.print(&x);
        }
        r += ">>";
        self.end_indent();
        r
    }
    fn expr_seq(&mut self, v: Option<V<Expr>>) -> String {
        let v = match v {
            None => return "null".to_string(),
            Some(v) => v,
        };
        let mut r = self.indent("<<");
        for i in 0..v.len() {
            if i > 0 {
                r += ", ";
                r += &self.new_line();
            }
            r += &v.get(i).borrow().java_to_string();
        }
        r += ">>";
        self.end_indent();
        r
    }
    fn quoted(&mut self, v: Option<V<String>>) -> String {
        let v = match v {
            None => return "null".to_string(),
            Some(v) => v,
        };
        let mut r = self.indent("<<");
        for i in 0..v.len() {
            if i > 0 {
                r += ", ";
            }
            r += &format!("\"{}\"", v.get(i));
        }
        r += ">>";
        self.end_indent();
        r
    }
    fn seq_of_seqs(&mut self, vv: V<V<Ast>>) -> String {
        let mut r = self.indent("<< ");
        for i in 0..vv.len() {
            if i > 0 {
                r += ", ";
                r += &self.new_line();
            }
            r += &self.seq(Some(vv.get(i)));
        }
        r += " >>";
        self.end_indent();
        r
    }
    fn eq_or_in(b: bool) -> &'static str {
        if b { "\"=\"" } else { "\"\\\\in\"" }
    }
    fn ex(e: Option<Expr>) -> String {
        match e {
            Some(e) => e.borrow().java_to_string(),
            None => new_expr().borrow().java_to_string(),
        }
    }
    /// A field introduced by `Indent(label) + VectorToSeqString(v) + close + EndIndent()`.
    fn field(&mut self, label: &str, v: Option<V<Ast>>, close: &str) -> String {
        let mut s = self.indent(label);
        s += &self.seq(v);
        s += close;
        self.end_indent();
        s
    }

    pub fn print(&mut self, n: &Node) -> String {
        let lc = self.line_col(n);
        let name = n.name();
        match n.k {
            K::Uniprocess => {
                let mut s = self.indent(&lc);
                s += "[type     |-> \"uniprocess\", ";
                s += &self.new_line();
                s += &format!(" name  |-> \"{}\", ", name);
                s += &self.new_line();
                s += &self.field(" decls  |-> ", n.decls_opt(), ",");
                s += &self.new_line();
                s += &self.indent(" defs   |-> ");
                s += &Self::ex(n.defs_opt());
                s += ",";
                self.end_indent();
                s += &self.new_line();
                s += &self.field(" prcds  |-> ", n.prcds_opt(), ",");
                s += &self.new_line();
                s += &self.field(" body  |-> ", n.body_opt(), "]");
                self.end_indent();
                s
            }
            K::Multiprocess => {
                let mut s = self.indent(&lc);
                s += "[type    |-> \"multiprocess\", ";
                s += &self.new_line();
                s += &format!(" name  |-> \"{}\", ", name);
                s += &self.new_line();
                s += &self.field(" decls |-> ", n.decls_opt(), ",");
                s += &self.new_line();
                s += &self.indent(" defs  |-> ");
                s += &Self::ex(n.defs_opt());
                s += ",";
                self.end_indent();
                s += &self.new_line();
                s += &self.field(" prcds |-> ", n.prcds_opt(), ",");
                s += &self.new_line();
                s += &self.field(" procs |-> ", n.procs_opt(), "]");
                self.end_indent();
                s
            }
            K::Procedure => {
                let mut s = self.indent(&lc);
                s += &format!("[name   |-> \"{}\", ", name);
                s += &self.new_line();
                if !self.old_version {
                    s += "minusLabels |-> ";
                    s += &self.quoted(n.minus_labels_opt());
                    s += ", plusLabels |->";
                    s += &self.quoted(n.plus_labels_opt());
                    s += ", proceduresCalled |->";
                    s += &self.quoted(n.procedures_called_opt());
                    s += ",";
                    s += &self.new_line();
                }
                s += &self.field(" params |-> ", n.params_opt(), ",");
                s += &self.new_line();
                s += &self.field(" decls  |-> ", n.decls_opt(), ",");
                s += &self.new_line();
                s += &self.field(" body   |-> ", n.body_opt(), "]");
                self.end_indent();
                s
            }
            K::Process => {
                let mut s = self.indent(&lc);
                if self.old_version {
                    s += &format!("[name   |-> \"{}\", ", name);
                    s += &self.new_line();
                } else {
                    s += &format!("[name   |-> \"{}\",", name);
                    s += &self.new_line();
                    s += &format!(" fairness |-> \"{}\", minusLabels |-> ", FAIRNESS_STRING[n.fairness.get() as usize]);
                    s += &self.quoted(n.minus_labels_opt());
                    s += ", plusLabels |->";
                    s += &self.quoted(n.plus_labels_opt());
                    s += ", proceduresCalled |->";
                    s += &self.quoted(n.procedures_called_opt());
                    s += ",";
                    s += &self.new_line();
                }
                s += &format!(" eqOrIn |-> {},", Self::eq_or_in(n.is_eq.get()));
                s += &self.new_line();
                s += &format!(" id     |-> {},", Self::ex(n.e_opt()));
                s += &self.new_line();
                s += &self.field(" decls  |-> ", n.decls_opt(), ",");
                s += &self.new_line();
                s += &self.field(" body   |-> ", n.body_opt(), "]");
                self.end_indent();
                s
            }
            K::VarDecl => {
                let mut s = self.indent(&lc);
                s += &format!("[var |-> \"{}\", eqOrIn |-> {}, val |-> {}]", name, Self::eq_or_in(n.is_eq.get()), Self::ex(n.e_opt()));
                self.end_indent();
                s
            }
            K::PVarDecl => {
                let mut s = self.indent(&lc);
                s += &format!("[var |-> \"{}\", eqOrIn |-> \"=\", val |-> {}]", name, Self::ex(n.e_opt()));
                self.end_indent();
                s
            }
            K::LabeledStmt => {
                let mut s = self.indent(&lc);
                s += &format!("[label |-> \"{}\",", name);
                s += &self.new_line();
                s += &self.field(" stmts |-> ", n.stmts_opt(), "]");
                self.end_indent();
                s
            }
            K::While => {
                let mut s = self.indent(&lc);
                s += "[type    |-> \"while\", ";
                s += &self.new_line();
                s += &format!(" test    |-> {},", Self::ex(n.e_opt()));
                s += &self.new_line();
                s += &self.field(" labDo   |-> ", n.lab_do_opt(), ",");
                s += &self.new_line();
                s += &self.field(" unlabDo |-> ", n.unlab_do_opt(), "]");
                self.end_indent();
                s
            }
            K::Assign => {
                let mut s = self.indent(&lc);
                s += "[type |-> \"assignment\",";
                s += &self.new_line();
                s += &self.field(" ass  |-> ", n.ass_opt(), "]");
                self.end_indent();
                s
            }
            K::SingleAssign => {
                let mut s = self.indent(&lc);
                s += "[lhs |-> ";
                s += &self.print(&n.lhs());
                s += ",";
                s += &self.new_line();
                s += &format!(" rhs |-> {}]", Self::ex(n.e_opt()));
                self.end_indent();
                s
            }
            K::Lhs => format!("{}[var |-> \"{}\", sub |-> {}]", lc, name, Self::ex(n.e_opt())),
            K::If => {
                let mut s = self.indent(&lc);
                s += "[type    |-> \"if\", ";
                s += &self.new_line();
                s += &format!(" test    |-> {},", Self::ex(n.e_opt()));
                s += &self.new_line();
                s += &self.field(" then |-> ", n.then_opt(), ",");
                s += &self.new_line();
                s += &self.field(" else |-> ", n.els_opt(), "]");
                self.end_indent();
                s
            }
            K::Either => {
                let mut s = self.indent(&lc);
                s += "[type |-> \"either\", ";
                s += &self.new_line();
                s += &self.indent(" ors  |-> ");
                s += &self.seq_of_seqs(n.ors());
                s += "]";
                self.end_indent();
                self.end_indent();
                s
            }
            K::With => {
                let mut s = self.indent(&lc);
                s += "[type   |-> \"with\", ";
                s += &self.new_line();
                s += &format!(" var    |-> \"{}\",", name);
                s += &self.new_line();
                s += &format!(" eqOrIn |-> {},", Self::eq_or_in(n.is_eq.get()));
                s += &self.new_line();
                s += &format!(" exp    |-> {},", Self::ex(n.e_opt()));
                s += &self.new_line();
                s += &self.field(" do     |-> ", n.do_opt(), "]");
                self.end_indent();
                s
            }
            K::When | K::PrintS | K::Assert => {
                let t = match n.k {
                    K::When => "when",
                    K::PrintS => "print",
                    _ => "assert",
                };
                let mut s = self.indent(&lc);
                s += &format!("[type |-> \"{}\", ", t);
                s += &self.new_line();
                s += &format!(" exp |-> {}]", Self::ex(n.e_opt()));
                self.end_indent();
                s
            }
            K::Skip => format!("{}[type |-> \"skip\"]", lc),
            K::LabelIf => {
                let mut s = self.indent(&lc);
                s += "[type      |-> \"labelIf\",";
                s += &self.new_line();
                s += &format!(" test      |-> {},", Self::ex(n.e_opt()));
                s += &self.new_line();
                s += &self.field(" unlabThen |-> ", n.unlab_then_opt(), ",");
                s += &self.new_line();
                s += &self.field(" labThen   |-> ", n.lab_then_opt(), ",");
                s += &self.new_line();
                s += &self.field(" unlabElse |-> ", n.unlab_else_opt(), ",");
                s += &self.new_line();
                s += &self.field(" labElse   |-> ", n.lab_else_opt(), "]");
                s += &self.new_line();
                self.end_indent();
                s
            }
            K::LabelEither => {
                let mut s = self.indent(&lc);
                s += "[type    |-> \"labelEither\",";
                s += &self.new_line();
                s += &self.field(" clauses |-> ", n.clauses_opt(), "]");
                s += &self.new_line();
                self.end_indent();
                s
            }
            K::Clause => {
                let mut s = self.indent(&lc);
                s += &self.field("[unlabOr |-> ", n.unlab_or_opt(), ",");
                s += &self.new_line();
                s += &self.field(" labOr   |-> ", n.lab_or_opt(), "]");
                s += &self.new_line();
                self.end_indent();
                s
            }
            K::Call => {
                let mut s = self.indent(&lc);
                s += "[type     |-> \"call\",";
                s += &self.new_line();
                s += &format!(" returnTo |-> \"{}\",", n.return_to.borrow());
                s += &self.new_line();
                s += &format!(" to       |-> \"{}\",", n.to());
                s += &self.new_line();
                s += &self.indent(" args     |-> ");
                s += &self.expr_seq(n.args_opt());
                s += "]";
                self.end_indent();
                self.end_indent();
                s
            }
            K::Return => format!("{}[type |-> \"return\", from |-> \"{}\"]", lc, n.from().unwrap_or_else(|| "null".to_string())),
            K::CallReturn | K::CallGoto => {
                let mut s = self.indent(&lc);
                if n.k == K::CallReturn {
                    s += "[type     |-> \"callReturn\",";
                    s += &self.new_line();
                    s += &format!(" from     |-> \"{}\",", n.from().unwrap_or_else(|| "null".to_string()));
                } else {
                    s += "[type     |-> \"callGoto\",";
                    s += &self.new_line();
                    s += &format!(" after    |-> \"{}\",", n.after.borrow());
                }
                s += &self.new_line();
                s += &format!(" to       |-> \"{}\",", n.to());
                s += &self.new_line();
                s += &self.indent("args     |-> ");
                s += &self.expr_seq(n.args_opt());
                s += "]";
                s += &self.new_line();
                self.end_indent();
                self.end_indent();
                s
            }
            K::Goto => format!("{}[type |-> \"goto\",  to |-> \"{}\"]", lc, n.to()),
            K::Macro => {
                let mut s = self.indent(&lc);
                s += &format!("[name   |-> \"{}\", ", name);
                s += &self.new_line();
                s += &self.indent(" params |-> ");
                s += &self.quoted_plain(n.sparams_opt());
                s += ",";
                self.end_indent();
                s += &self.new_line();
                s += &self.field(" body   |-> ", n.body_opt(), "]");
                self.end_indent();
                s
            }
            K::MacroCall => {
                let mut s = self.indent(&lc);
                s += "[type |-> \"macrocall\",";
                s += &self.new_line();
                s += &format!(" name |-> \"{}\",", name);
                s += &self.new_line();
                s += &self.indent(" args     |-> ");
                s += &self.expr_seq(n.args_opt());
                s += "]";
                self.end_indent();
                self.end_indent();
                s
            }
        }
    }
    /// `VectorToSeqString` of a vector of plain strings (macro parameters).
    fn quoted_plain(&mut self, v: Option<V<String>>) -> String {
        let v = match v {
            None => return "null".to_string(),
            Some(v) => v,
        };
        let mut r = self.indent("<<");
        for i in 0..v.len() {
            if i > 0 {
                r += ", ";
                r += &self.new_line();
            }
            r += &v.get(i);
        }
        r += ">>";
        self.end_indent();
        r
    }
}
