//! TLA+ parser: tokens -> AST. Recursive descent with precedence climbing and column-sensitive
//! junction lists. A direct port of parser.ts.
use crate::ast::*;
use crate::intern::*;
use crate::lexer::{lex, Tok, T};
use std::cell::{Cell, OnceCell};
use std::rc::Rc;

// (lo, hi)
fn infix(op: &str) -> Option<(i32, i32)> {
    Some(match op {
        "=>" => (1, 1),
        "-+->" | "<=>" | "~>" => (2, 2),
        "\\/" | "/\\" => (3, 3),
        "\\cdot" => (5, 14),
        "@@" => (6, 6),
        ":>" | "<:" => (7, 7),
        "\\" | "\\cap" | "\\cup" => (8, 8),
        ".." | "..." => (9, 9),
        "!!" | "##" | "$" | "$$" | "??" | "\\sqcap" | "\\sqcup" | "\\uplus" => (9, 13),
        "\\wr" => (9, 14),
        "\\oplus" | "+" | "++" => (10, 10),
        "%" | "%%" | "|" | "||" => (10, 11),
        "\\X" => (10, 13),
        "-" | "--" | "\\ominus" => (11, 11),
        "&" | "&&" | "*" | "**" | "/" | "//" | "\\div" | "\\odot" | "\\oslash" | "\\otimes" | "\\bigcirc" | "\\bullet"
        | "\\o" | "\\star" => (13, 13),
        "^" | "^^" => (14, 14),
        "=" | "/=" | "<" | ">" | "<=" | ">=" | "\\in" | "\\notin" | "\\subseteq" | "\\subset" | "\\supseteq"
        | "\\supset" | "\\prec" | "\\preceq" | "\\succ" | "\\succeq" | "\\ll" | "\\gg" | "\\sim" | "\\simeq"
        | "\\approx" | "\\cong" | "\\doteq" | "\\asymp" | "\\propto" | "\\sqsubset" | "\\sqsubseteq" | "\\sqsupset"
        | "\\sqsupseteq" | "::=" | ":=" | "|-" | "|=" | "-|" | "=|" => (5, 5),
        _ => return None,
    })
}
fn prefix(op: &str) -> Option<(i32, i32)> {
    Some(match op {
        "~" => (4, 4),
        "[]" | "<>" | "ENABLED" | "UNCHANGED" => (4, 15),
        "SUBSET" | "UNION" => (8, 8),
        "DOMAIN" => (9, 9),
        "-" => (12, 12),
        _ => return None,
    })
}
fn postfix(op: &str) -> bool {
    matches!(op, "'" | "^+" | "^*" | "^#")
}
fn fixed(op: &str) -> Option<K> {
    Some(match op {
        "/\\" => K::And,
        "\\/" => K::Or,
        "~" => K::Not,
        "=>" => K::Imp,
        "<=>" => K::Eqv,
        "=" => K::Eq,
        "/=" => K::Ne,
        "\\in" => K::In,
        "\\notin" => K::NotIn,
        "\\subseteq" => K::Subseteq,
        "\\cup" => K::Cup,
        "\\cap" => K::Cap,
        "\\" => K::Diff,
        "SUBSET" => K::Powerset,
        "UNION" => K::BigUnion,
        "DOMAIN" => K::Domain,
        "'" => K::Prime,
        "ENABLED" => K::Enabled,
        "UNCHANGED" => K::Unchanged,
        "[]" => K::Always,
        "<>" => K::Eventually,
        "~>" => K::LeadsTo,
        "-+->" => K::Guarantee,
        "\\cdot" => K::Cdot,
        _ => return None,
    })
}
fn theorem_kw(s: &str) -> bool {
    matches!(s, "THEOREM" | "LEMMA" | "PROPOSITION" | "COROLLARY")
}
fn unit_start_kw(s: &str) -> bool {
    matches!(
        s,
        "VARIABLE" | "VARIABLES" | "CONSTANT" | "CONSTANTS" | "RECURSIVE" | "LOCAL" | "INSTANCE" | "ASSUME" | "ASSUMPTION"
            | "AXIOM" | "THEOREM" | "LEMMA" | "PROPOSITION" | "COROLLARY" | "USE" | "HIDE"
    )
}

struct Parser {
    toks: Vec<Tok>,
    p: usize,
    js: Vec<i64>, // junction column stack; -1 = unconstrained
    last: Tok,
    module: String,
    stop: Tok,
}

fn is_op(t: &Tok, v: &str) -> bool {
    t.t == T::Op && &*t.v == v
}
fn is_kw(t: &Tok, v: &str) -> bool {
    t.t == T::Kw && &*t.v == v
}

impl Parser {
    fn new(toks: Vec<Tok>, module: &str) -> Parser {
        let last = toks[0].clone();
        Parser {
            toks,
            p: 0,
            js: vec![],
            last,
            module: module.to_string(),
            stop: Tok { t: T::Eof, v: Rc::from("<end of junction item>"), line: 0, col: 0, ec: 0, n: 0, stop: true },
        }
    }
    fn raw(&self) -> &Tok {
        &self.toks[self.p]
    }
    fn peek(&self) -> &Tok {
        let t = &self.toks[self.p];
        if let Some(&top) = self.js.last() {
            if (t.col as i64) <= top && t.t != T::Eof {
                return &self.stop;
            }
        }
        t
    }
    fn peek_at(&self, k: usize) -> &Tok {
        &self.toks[(self.p + k).min(self.toks.len() - 1)]
    }
    fn next(&mut self) -> R<Tok> {
        let t = self.peek().clone();
        if t.stop {
            return self.fail("Unexpected end of junction list item");
        }
        self.last = t.clone();
        self.p += 1;
        Ok(t)
    }
    fn isop(&self, v: &str) -> bool {
        is_op(self.peek(), v)
    }
    fn iskw(&self, v: &str) -> bool {
        is_kw(self.peek(), v)
    }
    fn eat_op(&mut self, v: &str) -> R<bool> {
        if self.isop(v) {
            self.next()?;
            return Ok(true);
        }
        Ok(false)
    }
    fn eat_kw(&mut self, v: &str) -> R<bool> {
        if self.iskw(v) {
            self.next()?;
            return Ok(true);
        }
        Ok(false)
    }
    fn expect_op(&mut self, v: &str) -> R<Tok> {
        if !self.isop(v) {
            return self.fail(&format!("Expected '{}'", v));
        }
        self.next()
    }
    fn expect_kw(&mut self, v: &str) -> R<Tok> {
        if !self.iskw(v) {
            return self.fail(&format!("Expected {}", v));
        }
        self.next()
    }
    fn expect_id(&mut self) -> R<Tok> {
        if self.peek().t != T::Id {
            return self.fail("Expected identifier");
        }
        self.next()
    }
    fn fail<X>(&self, msg: &str) -> R<X> {
        let t = self.raw();
        Err(Box::new(Fail::Tla(TlaError {
            msg: format!("{} but found '{}' at line {}, col {} of module {}", msg, t.v, t.line, t.col, self.module),
            loc: Some([t.line, t.col, t.line, t.ec]),
            module: Some(self.module.clone()),
            kind: "parse",
        })))
    }
    fn mk(&self, bl: u32, bc: u32, e: E) -> Node {
        Node::new([bl, bc, self.last.line, self.last.ec], e)
    }
    fn mk_t(&self, t: &Tok, e: E) -> Node {
        self.mk(t.line, t.col, e)
    }

    // ---------- module level ----------
    fn parse_module(&mut self) -> R<ModuleNode> {
        if self.raw().t != T::Sep {
            return self.fail("Expected module header");
        }
        self.next()?;
        self.expect_kw("MODULE")?;
        let name = self.expect_id()?.v;
        self.module = name.to_string();
        if self.raw().t != T::Sep {
            return self.fail("Expected ---- after module name");
        }
        self.next()?;
        let mut ext = vec![];
        if self.eat_kw("EXTENDS")? {
            loop {
                ext.push(crate::intern::name(&self.expect_id()?.v));
                if !self.eat_op(",")? {
                    break;
                }
            }
        }
        let mut units = vec![];
        loop {
            let t = self.raw().clone();
            if t.t == T::End {
                self.next()?;
                break;
            }
            if t.t == T::Eof {
                return self.fail("Unexpected end of file; module not terminated by ====");
            }
            if t.t == T::Sep {
                if is_kw(self.peek_at(1), "MODULE") {
                    let inner = self.parse_module()?;
                    self.module = name.to_string();
                    units.push(Unit::Module(inner));
                } else {
                    self.next()?;
                }
                continue;
            }
            if let Some(u) = self.parse_unit()? {
                units.push(u);
            }
        }
        Ok(ModuleNode { name: crate::intern::name(&name), extends: ext, units, strings: vec![] })
    }

    fn parse_unit(&mut self) -> R<Option<Unit>> {
        let t = self.peek().clone();
        if t.t == T::Kw {
            match &*t.v {
                "VARIABLE" | "VARIABLES" => {
                    self.next()?;
                    let mut names = vec![];
                    loop {
                        names.push(name(&self.expect_id()?.v));
                        if !self.eat_op(",")? {
                            break;
                        }
                    }
                    return Ok(Some(Unit::Variables(names)));
                }
                "CONSTANT" | "CONSTANTS" => {
                    self.next()?;
                    let mut decls = vec![];
                    loop {
                        decls.push(self.parse_op_decl()?);
                        if !self.eat_op(",")? {
                            break;
                        }
                    }
                    return Ok(Some(Unit::Constants(decls)));
                }
                "RECURSIVE" => {
                    self.next()?;
                    loop {
                        self.parse_op_decl()?;
                        if !self.eat_op(",")? {
                            break;
                        }
                    }
                    return Ok(Some(Unit::Recursive));
                }
                "LOCAL" => {
                    self.next()?;
                    if self.iskw("INSTANCE") {
                        let mut i = self.parse_instance()?;
                        i.local = true;
                        return Ok(Some(Unit::Instance(i)));
                    }
                    return Ok(Some(match self.parse_def()? {
                        LetDef::Def(mut d) => {
                            d.local = true;
                            Unit::Def(d)
                        }
                        LetDef::Inst(mut i) => {
                            i.local = true;
                            Unit::Instance(i)
                        }
                    }));
                }
                "INSTANCE" => return Ok(Some(Unit::Instance(self.parse_instance()?))),
                "ASSUME" | "ASSUMPTION" | "AXIOM" => {
                    let axiom = &*t.v == "AXIOM";
                    self.next()?;
                    let mut nm = None;
                    if self.peek().t == T::Id && is_op(self.peek_at(1), "==") {
                        nm = Some(name(&self.next()?.v));
                        self.next()?;
                    }
                    let e = self.parse_expr()?;
                    let loc = [t.line, t.col, self.last.line, self.last.ec];
                    return Ok(Some(Unit::Assume { name: nm, e, loc, axiom }));
                }
                "USE" | "HIDE" => {
                    self.next()?;
                    self.parse_use_body()?;
                    return Ok(None);
                }
                _ => {}
            }
            if theorem_kw(&t.v) {
                self.next()?;
                let mut nm = None;
                if self.peek().t == T::Id && is_op(self.peek_at(1), "==") {
                    nm = Some(name(&self.next()?.v));
                    self.next()?;
                }
                let e = if self.iskw("ASSUME") { self.parse_assume_prove()? } else { self.parse_expr()? };
                let loc = [t.line, t.col, self.last.line, self.last.ec];
                self.parse_proof_opt()?;
                return Ok(Some(Unit::Theorem { name: nm, e, loc }));
            }
        }
        Ok(Some(match self.parse_def()? {
            LetDef::Def(d) => Unit::Def(d),
            LetDef::Inst(i) => Unit::Instance(i),
        }))
    }

    fn parse_op_decl(&mut self) -> R<Param> {
        let t = self.peek().clone();
        if t.t == T::Id {
            self.next()?;
            let mut arity = 0;
            if self.eat_op("(")? {
                loop {
                    self.expect_op("_")?;
                    arity += 1;
                    if !self.eat_op(",")? {
                        break;
                    }
                }
                self.expect_op(")")?;
            }
            return Ok(Param { name: name(&t.v), arity });
        }
        if is_op(&t, "_") {
            self.next()?;
            let op = self.next()?;
            if self.eat_op("_")? {
                return Ok(Param { name: name(&op.v), arity: 2 });
            }
            return Ok(Param { name: name(&op.v), arity: 1 });
        }
        if t.t == T::Op || t.t == T::Kw {
            self.next()?;
            self.expect_op("_")?;
            return Ok(Param { name: name(if &*t.v == "-" { "-." } else { &t.v }), arity: 1 });
        }
        self.fail("Expected operator declaration")
    }

    fn parse_instance(&mut self) -> R<InstNode> {
        let t = self.expect_kw("INSTANCE")?;
        let module = name(&self.expect_id()?.v);
        let mut substs = vec![];
        if self.eat_kw("WITH")? {
            loop {
                let nt = self.next()?;
                if nt.t != T::Id && nt.t != T::Op {
                    return self.fail("Expected substitution target");
                }
                self.expect_op("<-")?;
                substs.push((name(&nt.v), self.parse_op_arg()?));
                if !self.eat_op(",")? {
                    break;
                }
            }
        }
        Ok(InstNode {
            module,
            substs,
            local: false,
            name: None,
            params: vec![],
            loc: [t.line, t.col, self.last.line, self.last.ec],
            inst_defs: OnceCell::new(),
            inst_substs: OnceCell::new(),
        })
    }

    // Definition: operator, function, or module (instance) definition.
    fn parse_def(&mut self) -> R<LetDef> {
        let t = self.peek().clone();
        let nm: Rc<str>;
        let mut params: Vec<Param> = vec![];
        let mut fn_bounds: Option<Vec<Bound>> = None;
        let nx = self.peek_at(1).clone();
        if t.t == T::Op && (prefix(&t.v).is_some() || &*t.v == "-.") && nx.t == T::Id {
            self.next()?;
            nm = if &*t.v == "-" { Rc::from("-.") } else { t.v.clone() };
            params = vec![Param { name: name(&self.expect_id()?.v), arity: 0 }];
        } else if t.t == T::Kw && prefix(&t.v).is_some() && nx.t == T::Id {
            return self.fail(&format!("Cannot redefine {}", t.v));
        } else if t.t == T::Id {
            self.next()?;
            let mut nm2 = t.v.clone();
            let n1 = self.peek().clone();
            if is_op(&n1, "(") {
                self.next()?;
                loop {
                    params.push(self.parse_op_decl()?);
                    if !self.eat_op(",")? {
                        break;
                    }
                }
                self.expect_op(")")?;
            } else if is_op(&n1, "[") {
                self.next()?;
                self.js.push(-1);
                fn_bounds = Some(self.parse_bounds()?);
                self.js.pop();
                self.expect_op("]")?;
            } else if n1.t == T::Op && infix(&n1.v).is_some() && self.peek_at(1).t == T::Id {
                self.next()?;
                params = vec![Param { name: name(&t.v), arity: 0 }, Param { name: name(&self.expect_id()?.v), arity: 0 }];
                nm2 = n1.v.clone();
            } else if n1.t == T::Op && postfix(&n1.v) {
                self.next()?;
                params = vec![Param { name: name(&t.v), arity: 0 }];
                nm2 = n1.v.clone();
            }
            nm = nm2;
        } else {
            return self.fail("Expected a definition or declaration");
        }
        self.expect_op("==")?;
        if self.iskw("INSTANCE") {
            let mut inst = self.parse_instance()?;
            inst.name = Some(name(&nm));
            inst.params = params;
            inst.loc = [t.line, t.col, self.last.line, self.last.ec];
            return Ok(LetDef::Inst(inst));
        }
        let mut body = self.parse_expr()?;
        if let Some(b) = fn_bounds {
            let loc = body.loc;
            body = Node::new(loc, E::FnDef { bounds: b, body: Box::new(body), recname: Some(name(&nm)), is_rec: Cell::new(false) });
        }
        Ok(LetDef::Def(DefNode { name: name(&nm), params, body, local: false, loc: [t.line, t.col, self.last.line, self.last.ec], closed: Cell::new(-1), cval: Default::default() }))
    }

    // ---------- proofs (parsed and discarded) ----------
    fn parse_assume_prove(&mut self) -> R<Node> {
        let t = self.expect_kw("ASSUME")?;
        loop {
            if self.iskw("ASSUME") {
                self.parse_assume_prove()?;
            } else if self.iskw("NEW") || self.iskw("CONSTANT") || self.iskw("VARIABLE") || self.iskw("STATE") || self.iskw("ACTION") || self.iskw("TEMPORAL") {
                self.eat_kw("NEW")?;
                let lvl = self.peek().clone();
                if lvl.t == T::Kw && matches!(&*lvl.v, "CONSTANT" | "VARIABLE" | "STATE" | "ACTION" | "TEMPORAL") {
                    self.next()?;
                }
                self.parse_op_decl()?;
                if self.eat_op("\\in")? {
                    self.parse_expr()?;
                }
            } else {
                self.parse_expr()?;
            }
            if !self.eat_op(",")? {
                break;
            }
        }
        self.expect_kw("PROVE")?;
        self.parse_expr()?;
        Ok(self.mk_t(&t, E::AssumeProve))
    }

    fn parse_use_body(&mut self) -> R<()> {
        self.eat_kw("ONLY")?;
        if !(self.iskw("DEF") || self.iskw("DEFS")) {
            loop {
                if self.eat_kw("MODULE")? {
                    self.expect_id()?;
                } else {
                    self.parse_expr()?;
                }
                if !self.eat_op(",")? {
                    break;
                }
            }
        }
        if self.iskw("DEF") || self.iskw("DEFS") {
            self.next()?;
            loop {
                if self.eat_kw("MODULE")? {
                    self.expect_id()?;
                } else if self.peek().t == T::Op && &*self.peek().v != "(" {
                    self.next()?;
                } else {
                    self.parse_op_arg()?;
                }
                if !self.eat_op(",")? {
                    break;
                }
            }
        }
        Ok(())
    }

    fn parse_proof_opt(&mut self) -> R<()> {
        let t = self.peek().clone();
        if t.t == T::Kw {
            match &*t.v {
                "PROOF" => {
                    self.next()?;
                    return self.parse_proof_opt();
                }
                "OBVIOUS" | "OMITTED" => {
                    self.next()?;
                    return Ok(());
                }
                "BY" => {
                    self.next()?;
                    return self.parse_use_body();
                }
                _ => {}
            }
        }
        if t.t == T::Step {
            self.parse_steps()?;
        }
        Ok(())
    }

    fn parse_steps(&mut self) -> R<()> {
        loop {
            if self.peek().t != T::Step {
                return Ok(());
            }
            self.next()?;
            let k = self.peek().clone();
            if k.t == T::Kw {
                match &*k.v {
                    "QED" => {
                        self.next()?;
                        return self.parse_proof_opt();
                    }
                    "USE" | "HIDE" => {
                        self.next()?;
                        self.parse_use_body()?;
                        continue;
                    }
                    "DEFINE" => {
                        self.next()?;
                        self.parse_step_defs()?;
                        continue;
                    }
                    "HAVE" => {
                        self.next()?;
                        self.parse_expr()?;
                        continue;
                    }
                    "WITNESS" => {
                        self.next()?;
                        loop {
                            self.parse_expr()?;
                            if !self.eat_op(",")? {
                                break;
                            }
                        }
                        continue;
                    }
                    "TAKE" => {
                        self.next()?;
                        self.parse_take_bounds()?;
                        continue;
                    }
                    "PICK" => {
                        self.next()?;
                        self.parse_take_bounds()?;
                        self.expect_op(":")?;
                        self.parse_expr()?;
                        self.parse_proof_opt()?;
                        continue;
                    }
                    "CASE" => {
                        self.next()?;
                        self.parse_expr()?;
                        self.parse_proof_opt()?;
                        continue;
                    }
                    "SUFFICES" => {
                        self.next()?;
                        if self.iskw("ASSUME") {
                            self.parse_assume_prove()?;
                        } else {
                            self.parse_expr()?;
                        }
                        self.parse_proof_opt()?;
                        continue;
                    }
                    "ASSUME" => {
                        self.parse_assume_prove()?;
                        self.parse_proof_opt()?;
                        continue;
                    }
                    "INSTANCE" => {
                        self.parse_instance()?;
                        continue;
                    }
                    _ => {}
                }
            }
            if self.looks_like_def() {
                self.parse_step_defs()?;
                continue;
            }
            self.parse_expr()?;
            self.parse_proof_opt()?;
        }
    }

    fn looks_like_def(&mut self) -> bool {
        let save = self.p;
        let save_last = self.last.clone();
        let js = self.js.clone();
        let t = self.peek().clone();
        let r = if t.t != T::Id && !(t.t == T::Op && prefix(&t.v).is_some()) { false } else { self.parse_def().is_ok() };
        self.p = save;
        self.last = save_last;
        self.js = js;
        r
    }

    fn parse_step_defs(&mut self) -> R<()> {
        loop {
            self.parse_def()?;
            if !(self.peek().t == T::Id && self.looks_like_def()) {
                break;
            }
        }
        Ok(())
    }

    fn parse_take_bounds(&mut self) -> R<()> {
        let save = self.p;
        if let Ok(b) = self.parse_bounds() {
            if !b.is_empty() {
                return Ok(());
            }
        }
        self.p = save;
        loop {
            self.expect_id()?;
            if !self.eat_op(",")? {
                break;
            }
        }
        Ok(())
    }

    // ---------- expressions ----------
    fn parse_expr(&mut self) -> R<Node> {
        self.parse_bin(0)
    }

    fn parse_bin(&mut self, min_prec: i32) -> R<Node> {
        let mut left = self.parse_prefix()?;
        loop {
            let t = self.peek().clone();
            if t.t != T::Op {
                break;
            }
            let info = match infix(&t.v) {
                Some(i) => i,
                None => break,
            };
            if info.0 < min_prec {
                break;
            }
            self.next()?;
            let op = &*t.v;
            // SANY's second conflict rule: unary minus (12-12) as the right operand of an infix operator
            // that binds tighter (`a * -b`, `2 ^ -x`, `s \o -t`).  Other prefix operators are accepted there.
            if info.0 > 12 && self.isop("-") {
                return Err(Box::new(Fail::Tla(TlaError {
                    msg: format!(
                        "***Parse Error***\n  Precedence conflict between ops {} in block line {}, col {} to line {}, col {} of module {} and -..",
                        t.v, t.line, t.col, t.line, t.ec, self.module
                    ),
                    loc: Some([t.line, t.col, self.peek().line, self.peek().ec]),
                    module: Some(self.module.clone()),
                    kind: "parse",
                })));
            }
            let (bl, bc) = (left.loc[0], left.loc[1]);
            if op == "\\X" {
                let mut items = vec![left, self.parse_bin(info.1 + 1)?];
                while self.isop("\\X") {
                    self.next()?;
                    items.push(self.parse_bin(info.1 + 1)?);
                }
                left = self.mk(bl, bc, E::Op(K::Cross, items));
                continue;
            }
            let right = self.parse_bin(info.1 + 1)?;
            match fixed(op) {
                Some(f) if f == K::And || f == K::Or => {
                    if left.is_k(f) && !left.junction && !left.paren {
                        if let E::Op(_, a) = &mut left.e {
                            a.push(right);
                        }
                        left.loc = [bl, bc, self.last.line, self.last.ec];
                    } else {
                        left = self.mk(bl, bc, E::Op(f, vec![left, right]));
                    }
                }
                Some(f) => left = self.mk(bl, bc, E::Op(f, vec![left, right])),
                None => left = self.mk(bl, bc, E::App { name: name(op), args: vec![left, right], sel: None, r: Cell::new(Res::None), implicit: false }),
            }
        }
        Ok(left)
    }

    fn parse_prefix(&mut self) -> R<Node> {
        let t = self.peek().clone();
        if t.t == T::Op || t.t == T::Kw {
            if let Some(info) = prefix(&t.v) {
                self.next()?;
                let arg = self.parse_bin(info.1 + 1)?;
                // SANY rejects a prefix operator followed by an infix operator of overlapping precedence
                // (e.g. `SUBSET S \cup T`, `[]x = 1`): neither grouping is preferred.
                let nt = self.peek().clone();
                if nt.t == T::Op {
                    if let Some((lo2, hi2)) = infix(&nt.v) {
                        if lo2 <= info.1 && hi2 >= info.0 {
                            return Err(Box::new(Fail::Tla(TlaError {
                                msg: format!(
                                    "***Parse Error***\n  Precedence conflict between ops {} in block line {}, col {} to line {}, col {} of module {} and {}.",
                                    t.v, t.line, t.col, t.line, t.ec, self.module, nt.v
                                ),
                                loc: Some([t.line, t.col, nt.line, nt.ec]),
                                module: Some(self.module.clone()),
                                kind: "parse",
                            })));
                        }
                    }
                }
                let e = if &*t.v == "-" {
                    self.mk_t(&t, E::App { name: name("-."), args: vec![arg], sel: None, r: Cell::new(Res::None), implicit: false })
                } else {
                    self.mk_t(&t, E::Op(fixed(&t.v).unwrap(), vec![arg]))
                };
                return self.parse_postfix_ops(e);
            }
        }
        let p = self.parse_primary()?;
        self.parse_postfix_ops(p)
    }

    fn parse_postfix_ops(&mut self, mut e: Node) -> R<Node> {
        loop {
            let t = self.peek().clone();
            if t.t != T::Op {
                break;
            }
            let (bl, bc) = (e.loc[0], e.loc[1]);
            if &*t.v == "[" {
                self.next()?;
                self.js.push(-1);
                let mut args = vec![self.parse_expr()?];
                while self.eat_op(",")? {
                    args.push(self.parse_expr()?);
                }
                self.js.pop();
                self.expect_op("]")?;
                e = self.mk(bl, bc, E::FnApp { f: Box::new(e), args });
            } else if &*t.v == "." {
                self.next()?;
                let f = self.next()?;
                if f.t != T::Id && f.t != T::Kw {
                    return self.fail("Expected field name");
                }
                e = self.mk(bl, bc, E::Dot { e: Box::new(e), field: str_id(&f.v) });
            } else if &*t.v == "'" {
                self.next()?;
                e = self.mk(bl, bc, E::Op(K::Prime, vec![e]));
            } else if postfix(&t.v) {
                self.next()?;
                e = self.mk(bl, bc, E::App { name: name(&t.v), args: vec![e], sel: None, r: Cell::new(Res::None), implicit: false });
            } else {
                break;
            }
        }
        Ok(e)
    }

    // An operator argument: expression, or a bare operator symbol (e.g. F(+, 1)), or LAMBDA.
    fn parse_op_arg(&mut self) -> R<Node> {
        let t = self.peek().clone();
        if (t.t == T::Op && (infix(&t.v).is_some() || postfix(&t.v) || &*t.v == "-." || prefix(&t.v).is_some())) || (t.t == T::Kw && prefix(&t.v).is_some()) {
            let n = self.peek_at(1).clone();
            if (n.t == T::Op && (&*n.v == "," || &*n.v == ")")) || n.t == T::Eof || n.t == T::End || n.t == T::Sep || (n.t == T::Kw && unit_start_kw(&n.v)) {
                self.next()?;
                return Ok(self.op_ref(&t));
            }
        }
        self.parse_expr()
    }

    fn op_ref(&self, t: &Tok) -> Node {
        let app = |nm: &str, loc: Loc| Node::new(loc, E::App { name: name(nm), args: vec![], sel: None, r: Cell::new(Res::None), implicit: false });
        let f = match fixed(&t.v) {
            None => return self.mk_t(t, E::App { name: name(&t.v), args: vec![], sel: None, r: Cell::new(Res::None), implicit: false }),
            Some(f) => f,
        };
        let loc: Loc = [t.line, t.col, t.line, t.ec];
        if prefix(&t.v).is_some() || &*t.v == "'" {
            return Node::new(loc, E::Lambda { params: vec![Param { name: name("_a"), arity: 0 }], body: Box::new(Node::new(loc, E::Op(f, vec![app("_a", loc)]))) });
        }
        Node::new(
            loc,
            E::Lambda {
                params: vec![Param { name: name("_a"), arity: 0 }, Param { name: name("_b"), arity: 0 }],
                body: Box::new(Node::new(loc, E::Op(f, vec![app("_a", loc), app("_b", loc)]))),
            },
        )
    }

    // Non-fix application of an infix/postfix operator symbol: +(a, b), \in(x, S), ^+(a), -.(a)
    fn prefix_apply(&mut self, t: &Tok) -> R<Node> {
        self.next()?;
        self.next()?;
        let args = self.parse_args()?;
        let want = if postfix(&t.v) || &*t.v == "-." { 1 } else { 2 };
        if args.len() != want {
            return self.fail(&format!("The operator {} requires {} arguments", t.v, want));
        }
        if let Some(f) = fixed(&t.v) {
            return Ok(self.mk_t(t, E::Op(f, args)));
        }
        Ok(self.mk_t(t, E::App { name: name(&t.v), args, sel: None, r: Cell::new(Res::None), implicit: false }))
    }

    fn parse_args(&mut self) -> R<Vec<Node>> {
        self.js.push(-1);
        let mut args = vec![];
        loop {
            args.push(self.parse_op_arg()?);
            if !self.eat_op(",")? {
                break;
            }
        }
        self.js.pop();
        self.expect_op(")")?;
        Ok(args)
    }

    fn parse_junction(&mut self, bullet: &str) -> R<Node> {
        let first = self.peek().clone();
        let col = first.col;
        let mut items: Vec<Node> = vec![];
        loop {
            let r = self.raw();
            if !(r.t == T::Op && &*r.v == bullet && r.col == col) {
                break;
            }
            if self.peek().stop {
                break;
            }
            self.next()?;
            self.js.push(col as i64);
            items.push(self.parse_expr()?);
            self.js.pop();
        }
        let kind = if bullet == "/\\" { K::And } else { K::Or };
        if items.len() == 1 {
            let mut it = items.pop().unwrap();
            if it.is_k(K::And) || it.is_k(K::Or) {
                it.junction = true;
            }
            return Ok(it);
        }
        let mut n = self.mk_t(&first, E::Op(kind, items));
        n.junction = true;
        Ok(n)
    }

    // names (\in set)? groups separated by commas.
    fn parse_bounds(&mut self) -> R<Vec<Bound>> {
        let mut out = vec![];
        loop {
            if self.isop("<<") {
                self.next()?;
                let mut tuple = vec![];
                if !self.isop(">>") {
                    loop {
                        tuple.push(name(&self.expect_id()?.v));
                        if !self.eat_op(",")? {
                            break;
                        }
                    }
                }
                self.expect_op(">>")?;
                self.expect_op("\\in")?;
                out.push(Bound { names: None, tuple: Some(tuple), set: Some(Box::new(self.parse_expr()?)) });
            } else {
                let mut names = vec![name(&self.expect_id()?.v)];
                while self.eat_op(",")? {
                    names.push(name(&self.expect_id()?.v));
                }
                if self.eat_op("\\in")? {
                    out.push(Bound { names: Some(names), tuple: None, set: Some(Box::new(self.parse_expr()?)) });
                } else {
                    out.push(Bound { names: Some(names), tuple: None, set: None });
                }
            }
            if !self.eat_op(",")? {
                break;
            }
        }
        Ok(out)
    }

    fn attempt<X>(&mut self, f: impl FnOnce(&mut Parser) -> R<X>) -> Option<X> {
        let save = self.p;
        let save_last = self.last.clone();
        let js = self.js.clone();
        match f(self) {
            Ok(x) => Some(x),
            Err(_) => {
                self.p = save;
                self.last = save_last;
                self.js = js;
                None
            }
        }
    }

    fn parse_primary(&mut self) -> R<Node> {
        let t = self.peek().clone();
        match t.t {
            T::Num => {
                self.next()?;
                return Ok(self.mk_t(&t, E::Num(t.n)));
            }
            T::Str => {
                self.next()?;
                return Ok(self.mk_t(&t, E::Str(t.v.clone(), Cell::new(None))));
            }
            T::Step => {
                self.next()?;
                while self.isop("!") {
                    self.next()?;
                    // <1>4!1!(v): a selector may carry arguments
                    if self.isop("(") {
                        self.next()?;
                        self.parse_args()?;
                    } else {
                        self.next()?;
                    }
                }
                return Ok(self.mk_t(&t, E::StepRef));
            }
            T::Id => return self.parse_ident(),
            T::Kw => return self.parse_keyword_expr(&t),
            T::Op => {}
            _ => return self.fail("Expected expression"),
        }
        match &*t.v {
            "(" => {
                self.next()?;
                self.js.push(-1);
                let mut e = self.parse_expr()?;
                self.js.pop();
                self.expect_op(")")?;
                if e.is_k(K::And) || e.is_k(K::Or) {
                    e.paren = true;
                }
                return Ok(e);
            }
            "/\\" | "\\/" => return self.parse_junction(&t.v),
            "<<" => {
                self.next()?;
                self.js.push(-1);
                let mut items = vec![];
                if !self.isop(">>") && !self.isop(">>_") {
                    loop {
                        items.push(self.parse_expr()?);
                        if !self.eat_op(",")? {
                            break;
                        }
                    }
                }
                self.js.pop();
                if self.eat_op(">>_")? {
                    let v = self.parse_subscript()?;
                    if items.len() != 1 {
                        return self.fail("<<A>>_v requires exactly one action");
                    }
                    let a = items.pop().unwrap();
                    return Ok(self.mk_t(&t, E::Op(K::AngleAct, vec![a, v])));
                }
                self.expect_op(">>")?;
                return Ok(self.mk_t(&t, E::Op(K::Tuple, items)));
            }
            "{" => return self.parse_set(&t),
            "[" => return self.parse_bracket(&t),
            "\\A" | "\\E" => {
                self.next()?;
                let bounds = self.parse_bounds()?;
                self.expect_op(":")?;
                let body = self.parse_expr()?;
                return Ok(self.mk_t(&t, E::Quant { forall: &*t.v == "\\A", bounds, body: Box::new(body) }));
            }
            "\\AA" | "\\EE" => {
                self.next()?;
                let mut names = vec![name(&self.expect_id()?.v)];
                while self.eat_op(",")? {
                    names.push(name(&self.expect_id()?.v));
                }
                self.expect_op(":")?;
                let body = self.parse_expr()?;
                return Ok(self.mk_t(&t, E::TQuant { names, body: Box::new(body) }));
            }
            "@" => {
                self.next()?;
                return Ok(self.mk_t(&t, E::At));
            }
            _ => {}
        }
        if (infix(&t.v).is_some() || postfix(&t.v) || &*t.v == "-.") && &*t.v != "-" && is_op(self.peek_at(1), "(") {
            return self.prefix_apply(&t);
        }
        self.fail("Expected expression")
    }

    fn parse_subscript(&mut self) -> R<Node> {
        let mut e;
        if self.peek().t == T::Id {
            let t = self.next()?;
            let mut nm = t.v.to_string();
            while self.isop("!") && self.peek_at(1).t == T::Id {
                self.next()?;
                nm.push('!');
                nm.push_str(&self.next()?.v);
            }
            e = self.mk_t(&t, E::App { name: name(&nm), args: vec![], sel: None, r: Cell::new(Res::None), implicit: false });
        } else {
            e = self.parse_primary()?;
        }
        while self.isop(".") || self.isop("[") {
            let (bl, bc) = (e.loc[0], e.loc[1]);
            if self.eat_op(".")? {
                let f = self.next()?;
                e = self.mk(bl, bc, E::Dot { e: Box::new(e), field: str_id(&f.v) });
            } else {
                self.next()?;
                self.js.push(-1);
                let mut args = vec![self.parse_expr()?];
                while self.eat_op(",")? {
                    args.push(self.parse_expr()?);
                }
                self.js.pop();
                self.expect_op("]")?;
                e = self.mk(bl, bc, E::FnApp { f: Box::new(e), args });
            }
        }
        Ok(e)
    }

    fn parse_ident(&mut self) -> R<Node> {
        let t = self.next()?;
        let mut nm = t.v.to_string();
        let mut args: Vec<Node> = vec![];
        if self.isop("(") {
            self.next()?;
            args = self.parse_args()?;
        }
        // label:  lab:: expr
        if self.isop("::") {
            self.next()?;
            return self.parse_expr();
        }
        // instance path: A!B(x)!C, and subexpression selectors Op!2, Op!<<, Op!(x)
        let mut sel: Option<Vec<Sel>> = None;
        while self.isop("!") {
            let n1 = self.peek_at(1).clone();
            let n2 = self.peek_at(2).clone();
            let n2_paren = is_op(&n2, "(");
            let c1 = n1.t == T::Id
                || (n1.t == T::Op && infix(&n1.v).is_some() && ((&*n1.v != "<" && &*n1.v != ":>") || n2_paren))
                || (n1.t == T::Op && (&*n1.v == "-." || (postfix(&n1.v) && &*n1.v != "'")) && n2_paren);
            if sel.is_none() && c1 && !is_op(&n1, "<<") {
                self.next()?;
                let part = self.next()?;
                nm.push('!');
                nm.push_str(&part.v);
                if self.isop("(") {
                    self.next()?;
                    let more = self.parse_args()?;
                    args.extend(more);
                }
            } else if n1.t == T::Num || (n1.t == T::Op && matches!(&*n1.v, "<<" | ">>" | ":" | "@" | "(")) {
                self.next()?;
                let s1 = self.next()?;
                let item = if &*s1.v == "(" && s1.t == T::Op {
                    Sel::Args(self.parse_args()?)
                } else if s1.t == T::Num {
                    Sel::Num(s1.n)
                } else {
                    Sel::Sym(s1.v.clone())
                };
                sel.get_or_insert_with(Vec::new).push(item);
            } else {
                break;
            }
        }
        Ok(self.mk_t(&t, E::App { name: name(&nm), args, sel, r: Cell::new(Res::None), implicit: false }))
    }

    fn parse_keyword_expr(&mut self, t: &Tok) -> R<Node> {
        match &*t.v {
            "TRUE" => {
                self.next()?;
                Ok(self.mk_t(t, E::Bool(true)))
            }
            "FALSE" => {
                self.next()?;
                Ok(self.mk_t(t, E::Bool(false)))
            }
            "IF" => {
                self.next()?;
                let c = self.parse_expr()?;
                self.expect_kw("THEN")?;
                let a = self.parse_expr()?;
                self.expect_kw("ELSE")?;
                let b = self.parse_expr()?;
                Ok(self.mk_t(t, E::Op(K::If, vec![c, a, b])))
            }
            "CASE" => {
                self.next()?;
                let mut arms = vec![];
                let mut other = None;
                loop {
                    if self.eat_kw("OTHER")? {
                        self.expect_op("->")?;
                        other = Some(Box::new(self.parse_expr()?));
                        break; // OTHER is always the last arm; a following [] belongs to an enclosing CASE
                    } else {
                        let c = self.parse_expr()?;
                        self.expect_op("->")?;
                        let e = self.parse_expr()?;
                        arms.push((c, e));
                    }
                    if !self.eat_op("[]")? {
                        break;
                    }
                }
                Ok(self.mk_t(t, E::Case { arms, other }))
            }
            "LET" => {
                self.next()?;
                let mut defs = vec![];
                self.js.push(-1);
                while !self.iskw("IN") {
                    if self.iskw("RECURSIVE") {
                        self.next()?;
                        loop {
                            self.parse_op_decl()?;
                            if !self.eat_op(",")? {
                                break;
                            }
                        }
                        continue;
                    }
                    defs.push(self.parse_def()?);
                }
                self.js.pop();
                self.expect_kw("IN")?;
                let body = self.parse_expr()?;
                Ok(self.mk_t(t, E::Let { defs, body: Box::new(body) }))
            }
            "CHOOSE" => {
                self.next()?;
                let mut b = self.parse_bounds()?;
                if b.len() != 1 || b[0].names.as_ref().map_or(false, |n| n.len() != 1) {
                    return self.fail("CHOOSE takes one bound variable");
                }
                self.expect_op(":")?;
                let body = self.parse_expr()?;
                Ok(self.mk_t(t, E::Choose { bound: b.pop().unwrap(), body: Box::new(body) }))
            }
            "LAMBDA" => {
                self.next()?;
                let mut params = vec![];
                loop {
                    params.push(Param { name: name(&self.expect_id()?.v), arity: 0 });
                    if !self.eat_op(",")? {
                        break;
                    }
                }
                self.expect_op(":")?;
                let body = self.parse_expr()?;
                Ok(self.mk_t(t, E::Lambda { params, body: Box::new(body) }))
            }
            "WF_" | "SF_" => {
                self.next()?;
                let v = self.parse_subscript()?;
                self.expect_op("(")?;
                self.js.push(-1);
                let a = self.parse_expr()?;
                self.js.pop();
                self.expect_op(")")?;
                Ok(self.mk_t(t, E::Op(if &*t.v == "WF_" { K::Wf } else { K::Sf }, vec![v, a])))
            }
            _ => self.fail("Expected expression"),
        }
    }

    fn parse_set(&mut self, t: &Tok) -> R<Node> {
        self.next()?;
        self.js.push(-1);
        let r = self.parse_set_inner(t);
        self.js.pop();
        r
    }
    fn parse_set_inner(&mut self, t: &Tok) -> R<Node> {
        if self.eat_op("}")? {
            return Ok(self.mk_t(t, E::Op(K::SetEnum, vec![])));
        }
        let p0 = self.peek().clone();
        let p1 = self.peek_at(1).clone();
        if (p0.t == T::Id && is_op(&p1, "\\in")) || is_op(&p0, "<<") {
            let r = self.attempt(|s| {
                let bound;
                if p0.t == T::Id {
                    s.next()?;
                    s.next()?;
                    bound = Bound { names: Some(vec![name(&p0.v)]), tuple: None, set: Some(Box::new(s.parse_expr()?)) };
                } else {
                    s.next()?;
                    let mut tuple = vec![];
                    loop {
                        tuple.push(name(&s.expect_id()?.v));
                        if !s.eat_op(",")? {
                            break;
                        }
                    }
                    s.expect_op(">>")?;
                    s.expect_op("\\in")?;
                    bound = Bound { names: None, tuple: Some(tuple), set: Some(Box::new(s.parse_expr()?)) };
                }
                s.expect_op(":")?;
                let pred = s.parse_expr()?;
                s.expect_op("}")?;
                Ok(s.mk_t(t, E::SetFilter { bound, pred: Box::new(pred) }))
            });
            if let Some(r) = r {
                return Ok(r);
            }
        }
        let first = self.parse_expr()?;
        if self.eat_op(":")? {
            let bounds = self.parse_bounds()?;
            self.expect_op("}")?;
            return Ok(self.mk_t(t, E::SetMap { e: Box::new(first), bounds }));
        }
        let mut items = vec![first];
        while self.eat_op(",")? {
            items.push(self.parse_expr()?);
        }
        self.expect_op("}")?;
        Ok(self.mk_t(t, E::Op(K::SetEnum, items)))
    }

    fn parse_bracket(&mut self, t: &Tok) -> R<Node> {
        self.next()?;
        self.js.push(-1);
        let r = self.parse_bracket_inner(t);
        self.js.pop();
        r
    }
    fn parse_bracket_inner(&mut self, t: &Tok) -> R<Node> {
        let p0 = self.peek().clone();
        let p1 = self.peek_at(1).clone();
        if (p0.t == T::Id || p0.t == T::Kw) && p1.t == T::Op && (&*p1.v == "|->" || &*p1.v == ":") {
            let is_rec = &*p1.v == "|->";
            let mut fields = vec![];
            loop {
                let f = self.next()?;
                self.expect_op(if is_rec { "|->" } else { ":" })?;
                let e = self.parse_expr()?;
                fields.push((str_id(&f.v), e));
                if !self.eat_op(",")? {
                    break;
                }
            }
            self.expect_op("]")?;
            for (i, f) in fields.iter().enumerate() {
                if fields[..i].iter().any(|g| g.0 == f.0) {
                    let l = f.1.loc;
                    return Err(Box::new(Fail::Tla(TlaError {
                        msg: format!("line {}, col {} to line {}, col {} of module {}\n\nNon-unique fields in constructor.", l[0], l[1], l[2], l[3], self.module),
                        loc: Some(l),
                        module: Some(self.module.clone()),
                        kind: "semantic",
                    })));
                }
            }
            return Ok(self.mk_t(t, if is_rec { E::Rec(fields, OnceCell::new()) } else { E::RecSet(fields) }));
        }
        // [x \in S |-> e]
        if p0.t == T::Id || is_op(&p0, "<<") {
            let r = self.attempt(|s| {
                let bounds = s.parse_bounds()?;
                if bounds.iter().any(|b| b.set.is_none()) {
                    return s.fail("Expected bound");
                }
                s.expect_op("|->")?;
                let body = s.parse_expr()?;
                s.expect_op("]")?;
                Ok(s.mk_t(t, E::FnDef { bounds, body: Box::new(body), recname: None, is_rec: Cell::new(false) }))
            });
            if let Some(r) = r {
                return Ok(r);
            }
        }
        let e = self.parse_expr()?;
        if self.eat_op("->")? {
            let rng = self.parse_expr()?;
            self.expect_op("]")?;
            return Ok(self.mk_t(t, E::Op(K::FnSet, vec![e, rng])));
        }
        if self.eat_kw("EXCEPT")? {
            let mut updates = vec![];
            loop {
                self.expect_op("!")?;
                let mut path: Vec<Node> = vec![];
                loop {
                    if self.eat_op(".")? {
                        let f = self.next()?;
                        path.push(Node::new([f.line, f.col, f.line, f.ec], E::Str(f.v.clone(), Cell::new(None))));
                    } else if self.isop("[") {
                        self.next()?;
                        let mut idx = vec![self.parse_expr()?];
                        while self.eat_op(",")? {
                            idx.push(self.parse_expr()?);
                        }
                        self.expect_op("]")?;
                        if idx.len() == 1 {
                            path.push(idx.pop().unwrap());
                        } else {
                            let loc = idx[0].loc;
                            path.push(Node::new(loc, E::Op(K::Tuple, idx)));
                        }
                    } else {
                        break;
                    }
                }
                if path.is_empty() {
                    return self.fail("Expected EXCEPT path");
                }
                self.expect_op("=")?;
                let val = self.parse_expr()?;
                updates.push((path, val));
                if !self.eat_op(",")? {
                    break;
                }
            }
            self.expect_op("]")?;
            return Ok(self.mk_t(t, E::Except { base: Box::new(e), updates }));
        }
        if self.eat_op("]_")? {
            self.js.pop();
            let top = self.js.last().copied().unwrap_or(-1);
            self.js.push(top);
            let v = self.parse_subscript()?;
            return Ok(self.mk_t(t, E::Op(K::BoxAct, vec![e, v])));
        }
        self.fail("Expected ']', '->', 'EXCEPT' or ']_'")
    }
}

pub fn parse_module(src: &str, name_hint: &str) -> R<ModuleNode> {
    let toks = lex(src, name_hint, true)?;
    let strings: Vec<Rc<str>> = toks.iter().filter(|t| t.t == T::Str).map(|t| t.v.clone()).collect();
    let mut p = Parser::new(toks, name_hint);
    let mut m = p.parse_module()?;
    m.strings = strings;
    Ok(m)
}
