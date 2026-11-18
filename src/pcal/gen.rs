//! Generates the TLA+ translation of the exploded algorithm, line by line (port of
//! pcal.PcalTLAGen and pcal.Changed).  Lengths are Java string lengths, since the wrapping
//! decisions of the original are made on them.
use super::ast::*;
use super::expr::{clone_and_normalize, expr_from, jlen, make_expr, new_expr, spaces as nspaces, tok, Expr, ADDED, BUILTIN, IDENT};
use super::symtab::{SymTab, PROCEDURE};
use super::{err, err_at, Ctx, PErr, PR};
use std::rc::Rc;

/// Which variables a step has assigned so far.
#[derive(Clone)]
struct Changed {
    count: Vec<i32>,
    vars: Rc<Vec<String>>,
}
impl Changed {
    fn new(vars: Rc<Vec<String>>) -> Self {
        Changed { count: vec![0; vars.len()], vars }
    }
    fn is_changed(&self, s: &str) -> bool {
        match self.vars.iter().position(|v| v == s) {
            Some(i) => self.count[i] > 0,
            None => false,
        }
    }
    fn merge(&mut self, c: &Changed) {
        for i in 0..self.count.len() {
            self.count[i] = self.count[i].max(c.count[i]);
        }
    }
    fn set(&mut self, v: &str) -> i32 {
        match self.vars.iter().position(|x| x == v) {
            Some(i) => {
                self.count[i] += 1;
                self.count[i]
            }
            None => 0,
        }
    }
    fn unchanged_idx(&self, c: Option<&Changed>) -> Vec<usize> {
        (0..self.count.len()).filter(|i| self.count[*i] == 0 && c.map(|c| c.count[*i] > 0).unwrap_or(true)).collect()
    }
    fn unchanged(&self, c: Option<&Changed>) -> String {
        self.unchanged_idx(c).iter().map(|i| self.vars[*i].as_str()).collect::<Vec<_>>().join(", ")
    }
    fn num_unchanged(&self, c: Option<&Changed>) -> usize {
        self.unchanged_idx(c).len()
    }
    /// The unchanged variables as lines of at most about `ch` characters.
    fn unchanged_lines(&self, c: Option<&Changed>, ch: i32) -> Vec<String> {
        let mut sv = vec![];
        let mut s = String::new();
        let mut have_one = false;
        for i in self.unchanged_idx(c) {
            let one = &self.vars[i];
            if have_one {
                s += ", ";
            } else {
                have_one = true;
            }
            if jlen(&s) + jlen(one) > ch {
                if !s.is_empty() {
                    sv.push(s);
                }
                s = one.clone();
            } else {
                s += one;
            }
        }
        if !s.is_empty() {
            sv.push(s);
        }
        sv
    }
}

fn empty_expr(e: &Option<Expr>) -> bool {
    match e {
        None => true,
        Some(e) => e.borrow().tokens.is_empty(),
    }
}
fn substr(s: &str, from: usize, to: Option<usize>) -> String {
    let c: Vec<char> = s.chars().collect();
    let to = to.unwrap_or(c.len()).min(c.len());
    if from >= to { String::new() } else { c[from..to].iter().collect() }
}
/// Java's `String.split("\n")`: trailing empty strings are dropped.
fn java_split_lines(s: &str) -> Vec<String> {
    let mut v: Vec<String> = s.split('\n').map(|x| x.to_string()).collect();
    while v.len() > 1 && v.last().map(|x| x.is_empty()).unwrap_or(false) {
        v.pop();
    }
    if v.len() == 1 && v[0].is_empty() && !s.is_empty() {
        v.clear();
    }
    v
}
fn self_as_expr() -> Expr {
    make_expr(vec![vec![tok("self", 0, IDENT)]])
}
fn sub_expr(sub: Option<Expr>) -> Option<Expr> {
    let sub = sub?;
    let expr = clone_and_normalize(&sub);
    {
        let mut e = expr.borrow_mut();
        for i in 0..e.tokens.len() {
            for t in &e.tokens[i] {
                t.borrow_mut().column += 1;
            }
            if i == 0 {
                e.tokens[i].insert(0, tok("[", 0, BUILTIN));
            }
        }
        if e.tokens.is_empty() {
            e.add_line();
        }
        e.add_token_offset(tok("]", 0, BUILTIN), 0);
    }
    Some(expr)
}

fn sort_sass(v: &V<Ast>) -> V<Ast> {
    let mut v = v.to_vec();
    let mut r = vec![];
    while !v.is_empty() {
        let mut index_c = 0;
        for i in 1..v.len() {
            if v[index_c].lhs().name() > v[i].lhs().name() {
                index_c = i;
            }
        }
        r.push(v.remove(index_c));
    }
    V::of(r)
}

/// `PcalTLAGen.NeedsParentheses` (including its habit of only ever looking at the first line).
pub fn needs_parentheses(vec: &[String]) -> bool {
    if vec.is_empty() {
        return false;
    }
    let cur_line: Vec<char> = vec[0].chars().collect();
    let mut paren_depth = 0;
    let mut in_string = false;
    let mut need_paren = false;
    let mut cur_line_num = 0;
    while cur_line_num < vec.len() && !need_paren {
        let mut i = 0;
        while i < cur_line.len() && !need_paren {
            let c = cur_line[i];
            if in_string {
                match c {
                    '"' => in_string = false,
                    '\\' => i += 1,
                    _ => {}
                }
            } else {
                let (mut left, mut right, mut may) = (false, false, false);
                let next = if i + 1 < cur_line.len() { cur_line[i + 1] } else { ' ' };
                match c {
                    '"' => in_string = true,
                    '=' | '#' => may = true,
                    '<' => {
                        if next == '<' {
                            i += 1;
                            left = true;
                        } else {
                            may = true;
                        }
                    }
                    '>' => {
                        if next == '>' {
                            i += 1;
                            right = true;
                        } else {
                            may = true;
                        }
                    }
                    '|' => {
                        if next == '-' || (i > 0 && cur_line[i - 1] == '-') {
                            may = true;
                        }
                    }
                    '\\' => {
                        if !(next == ' ' || next == 'o' || next == 'X') {
                            may = true;
                        }
                    }
                    '/' => {
                        if next == '\\' {
                            may = true;
                        }
                    }
                    '(' | '[' | '{' => left = true,
                    ')' | ']' | '}' => right = true,
                    _ => {}
                }
                if may && paren_depth == 0 {
                    need_paren = true;
                }
                if left {
                    paren_depth += 1;
                }
                if right {
                    if paren_depth == 0 {
                        need_paren = true;
                    }
                    paren_depth -= 1;
                }
            }
            i += 1;
        }
        if in_string {
            need_paren = true;
        }
        cur_line_num += 1;
    }
    need_paren
}

struct FormulaPair {
    wf: String,
    sf: Option<String>,
}
impl FormulaPair {
    fn single_line(&self) -> String {
        match &self.sf {
            None => self.wf.clone(),
            Some(sf) => format!("{} /\\ {}", self.wf, sf),
        }
    }
    fn single_line_width(&self) -> i32 {
        match &self.sf {
            None => jlen(&self.wf),
            Some(sf) => jlen(&self.wf) + 4 + jlen(sf),
        }
    }
    fn multi_line(&self, col: i32) -> String {
        let val = format!("/\\ {}", self.wf);
        match &self.sf {
            None => val,
            Some(sf) => format!("{}\n{}/\\ {}", val, nspaces(col), sf),
        }
    }
}
struct ProcessFairness {
    prefix: Vec<String>,
    body: FormulaPair,
    prcd: Vec<FormulaPair>,
}
impl ProcessFairness {
    fn single_line_width(&self) -> i32 {
        let mut max_prefix = 0;
        let mut width = 0;
        if !self.prefix.is_empty() {
            for i in 0..self.prefix.len() - 1 {
                max_prefix = max_prefix.max(jlen(&self.prefix[i]));
                width = jlen(&self.prefix[self.prefix.len() - 1]);
            }
        }
        width += jlen(&self.body.wf);
        if let Some(sf) = &self.body.sf {
            width += jlen(sf);
        }
        for p in &self.prcd {
            width += p.single_line_width();
        }
        max_prefix.max(width)
    }
    fn prefix_string(&self, col: i32) -> String {
        let mut val = String::new();
        for (i, line) in self.prefix.iter().enumerate() {
            if i != 0 {
                val += &nspaces(col);
            }
            val += line;
            if i != self.prefix.len() - 1 {
                val += "\n";
            }
        }
        val
    }
    fn format(&self, col: i32, wrap_column: i32) -> String {
        if col + self.single_line_width() <= wrap_column || (self.body.sf.is_none() && self.prcd.is_empty()) {
            let mut val = self.prefix_string(col);
            val += &self.body.wf;
            if let Some(sf) = &self.body.sf {
                val += " /\\ ";
                val += sf;
            }
            for p in &self.prcd {
                val += " /\\ ";
                val += &p.single_line();
            }
            return val;
        }
        let mut val = self.prefix_string(col);
        let prefix_width = self.prefix.last().map(|l| jlen(l)).unwrap_or(0);
        let cur_col = col + prefix_width;
        let line = self.body.single_line();
        if cur_col + jlen(&line) + 3 <= wrap_column {
            val += &format!("/\\ {}", line);
        } else {
            val += &self.body.multi_line(cur_col);
        }
        for (i, form) in self.prcd.iter().enumerate() {
            let line = form.single_line();
            if i == 0 {
                val += "\n";
            }
            val += &nspaces(cur_col);
            if cur_col + jlen(&line) + 3 <= wrap_column {
                val += &format!("/\\ {}\n", line);
            } else {
                val += &form.multi_line(cur_col);
            }
        }
        val
    }
}

struct Gen<'a> {
    ctx: &'a Ctx,
    st: &'a SymTab,
    tlacode: Vec<String>,
    next_line: String,
    self_: Option<Expr>,
    self_is_self: bool,
    vars: Vec<String>,
    vars_rc: Rc<Vec<String>>,
    pc_v: Vec<String>,
    ps_v: Vec<String>,
    mp: bool,
    next_step: Vec<String>,
    current_proc_name: String,
}

/// `PcalTLAGen.generate`: the lines of the translation, after the `report` lines.
pub fn generate(ast: &Ast, st: &SymTab, ctx: &Ctx, report: &[String]) -> PR<Vec<String>> {
    let mut g = Gen {
        ctx,
        st,
        tlacode: vec![],
        next_line: String::new(),
        self_: None,
        self_is_self: false,
        vars: vec![],
        vars_rc: Rc::new(vec![]),
        pc_v: vec![],
        ps_v: vec![],
        mp: false,
        next_step: vec![],
        current_proc_name: String::new(),
    };
    for r in report {
        g.line(r);
    }
    if ast.k == K::Uniprocess {
        g.mp = false;
        g.current_proc_name = "Next".to_string();
        g.gen_vars_and_defs(&ast.decls(), &ast.prcds(), None, ast.defs_opt())?;
        g.gen_init(&ast.decls(), &ast.prcds(), None)?;
        for p in ast.prcds().to_vec() {
            g.gen_procedure(&p)?;
        }
        for ls in ast.body().to_vec() {
            g.next_step.push(ls.name());
            g.gen_labeled_stmt(&ls, "")?;
        }
    } else {
        g.mp = true;
        g.gen_vars_and_defs(&ast.decls(), &ast.prcds(), Some(&ast.procs()), ast.defs_opt())?;
        g.gen_proc_set();
        g.gen_init(&ast.decls(), &ast.prcds(), Some(&ast.procs()))?;
        for p in ast.prcds().to_vec() {
            g.gen_procedure(&p)?;
        }
        for p in ast.procs().to_vec() {
            g.gen_process(&p)?;
        }
    }
    g.gen_next();
    g.gen_spec();
    g.gen_termination();
    Ok(g.tlacode)
}

impl Gen<'_> {
    // ---- output ----
    fn token(&mut self, t: &str) {
        self.next_line.push_str(t);
    }
    fn end_line(&mut self) {
        if !self.next_line.is_empty() {
            let l = std::mem::take(&mut self.next_line);
            self.tlacode.push(l);
        }
    }
    fn line(&mut self, l: &str) {
        self.end_line();
        if l.is_empty() {
            self.tlacode.push(String::new());
            return;
        }
        self.token(l);
        self.end_line();
    }
    fn expr(&mut self, e: &Expr) {
        let sv = e.borrow().to_string_vector();
        if sv.is_empty() {
            return;
        }
        let indent = jlen(&self.next_line);
        let mut next = 0;
        if indent != 0 {
            self.next_line.push_str(&sv[0]);
            next = 1;
            if sv.len() > 1 {
                self.end_line();
            }
        }
        if sv.len() > 1 {
            let sp = nspaces(indent);
            while next < sv.len() - 1 {
                self.tlacode.push(format!("{}{}", sp, sv[next]));
                next += 1;
            }
            self.next_line = format!("{}{}", sp, sv[next]);
        } else if indent == 0 {
            self.next_line.push_str(&sv[0]);
        }
    }
    fn nl(&self) -> i32 {
        jlen(&self.next_line)
    }
    fn wrap(&self) -> i32 {
        self.ctx.wrap_column
    }

    fn is_procedure_var(&self, v: &str) -> bool {
        self.pc_v.iter().any(|x| x == v)
    }
    fn is_process_set_var(&self, v: &str) -> bool {
        self.ps_v.iter().any(|x| x == v)
    }
    fn self_for(&self, context: &str) -> Option<Expr> {
        if !self.mp {
            return None;
        }
        if context == "procedure" { Some(self_as_expr()) } else { self.self_.clone() }
    }
    fn sub_self(&self, context: &str) -> Option<Expr> {
        sub_expr(self.self_for(context))
    }

    fn add_subscripts(&self, exprn: &Expr, sub: Option<&Expr>, c: &Changed) -> PR<Expr> {
        let expr = clone_and_normalize(exprn);
        let mut expr_vec: Vec<Expr> = vec![];
        let mut string_vec: Vec<String> = vec![];
        for line in &expr.borrow().tokens {
            for t in line {
                let (typ, string) = {
                    let b = t.borrow();
                    (b.typ, b.string.clone())
                };
                let prime = typ == IDENT && c.is_changed(&string);
                let subr = sub.is_some() && (typ == ADDED || (self.mp && typ == IDENT && (self.is_procedure_var(&string) || self.is_process_set_var(&string))));
                if (subr || prime) && !string_vec.contains(&string) {
                    string_vec.push(string.clone());
                    let mut exp = expr_from(vec![vec![tok(&string, 0, typ)]]);
                    if prime {
                        exp.borrow_mut().add_token_offset(tok("'", 0, BUILTIN), 0);
                    }
                    if subr {
                        let subexp = clone_and_normalize(sub.unwrap());
                        exp.borrow_mut().normalize();
                        let r = subexp.borrow_mut().prepend(&exp.borrow(), 0);
                        r.map_err(PErr::Msg)?;
                        exp = subexp;
                    }
                    expr_vec.push(exp);
                }
            }
        }
        if !expr_vec.is_empty() {
            expr.borrow_mut().substitute_for_all(&expr_vec, &string_vec, false).map_err(PErr::Msg)?;
        }
        Ok(expr)
    }
    fn subscripted(&self, e: &Expr, context: &str, c: &Changed) -> PR<Expr> {
        self.add_subscripts(e, self.sub_self(context).as_ref(), c)
    }

    // ---- processes, procedures and steps ----
    fn gen_disjuncts(&mut self, name: &str, argument: &str, body: &V<Ast>) {
        let buf = format!("{}{} == ", name, argument);
        self.token(&buf);
        let indent_spaces = nspaces(jlen(&buf) + 2);
        for (i, stmt) in body.to_vec().iter().enumerate() {
            let disjunct = format!("{}{}", stmt.name(), argument);
            if i != 0 && self.nl() + 7 + jlen(&disjunct) > self.wrap() {
                self.end_line();
            }
            if i != 0 {
                let t = format!("{} \\/ ", if self.next_line.is_empty() { indent_spaces.as_str() } else { "" });
                self.token(&t);
            }
            self.token(&disjunct);
        }
        self.line("");
    }
    fn gen_procedure(&mut self, ast: &Ast) -> PR<()> {
        if self.mp {
            self.self_ = Some(self_as_expr());
            self.self_is_self = true;
        } else {
            self.next_step.push(ast.name());
        }
        for stmt in ast.body().to_vec() {
            self.gen_labeled_stmt(&stmt, "procedure")?;
        }
        let argument = if self.mp { "(self)" } else { "" };
        self.gen_disjuncts(&ast.name(), argument, &ast.body());
        Ok(())
    }
    fn gen_process(&mut self, ast: &Ast) -> PR<()> {
        self.current_proc_name = ast.name();
        let is_set = !ast.is_eq.get();
        if is_set {
            self.self_ = Some(self_as_expr());
            self.self_is_self = true;
        } else {
            self.self_ = Some(ast.e());
            self.self_is_self = false;
            self.next_step.push(ast.name());
        }
        for stmt in ast.body().to_vec() {
            self.gen_labeled_stmt(&stmt, "process")?;
        }
        if !self.ctx.omit_pc {
            self.gen_disjuncts(&ast.name(), if is_set { "(self)" } else { "" }, &ast.body());
        }
        Ok(())
    }

    fn gen_labeled_stmt(&mut self, ast: &Ast, context: &str) -> PR<()> {
        let action_name = if self.ctx.omit_pc { self.current_proc_name.clone() } else { ast.name() };
        let mut sb = action_name;
        let mut c = Changed::new(self.vars_rc.clone());
        if self.mp && (context == "procedure" || self.self_is_self) {
            sb += "(self)";
        }
        sb += " == ";
        let col = jlen(&sb);
        sb += "/\\ ";
        let def_start_line = self.tlacode.len();
        let col_after_and = jlen(&sb) as usize;
        let stmts = ast.stmts().to_vec();
        for stmt in &stmts {
            let l = jlen(&sb);
            self.gen_stmt(stmt, &mut c, context, &sb, l)?;
            sb = format!("{}/\\ ", nspaces(col));
        }
        let unc = c.unchanged_lines(None, self.wrap() - col - 16);
        let n = c.num_unchanged(None);
        if n > 1 {
            sb = format!("{}/\\ UNCHANGED << ", nspaces(col));
            let here = jlen(&sb);
            sb += &unc[0];
            for u in &unc[1..] {
                self.line(&sb);
                sb = format!("{}{}", nspaces(here), u);
            }
            sb += " >>";
            self.token(&sb);
        } else if n == 1 {
            let u = c.unchanged(None);
            let t = if jlen(&u) > 5 { format!("{}/\\ UNCHANGED {}", nspaces(col), u) } else { format!("{}/\\ {}' = {}", nspaces(col), u, u) };
            self.token(&t);
        } else if stmts.len() == 1 {
            for i in def_start_line..self.tlacode.len() {
                let line = self.tlacode[i].clone();
                if i == def_start_line {
                    self.tlacode[i] = format!("{}{}", substr(&line, 0, Some(col_after_and - 3)), substr(&line, col_after_and, None));
                } else if jlen(&line) > 3 {
                    self.tlacode[i] = substr(&line, 3, None);
                }
            }
        }
        self.line("");
        Ok(())
    }

    fn gen_stmt(&mut self, ast: &Ast, c: &mut Changed, context: &str, prefix: &str, col: i32) -> PR<()> {
        match ast.k {
            K::Assign => self.gen_assign(ast, c, context, prefix),
            K::If => self.gen_if(ast, c, context, prefix),
            K::Either => self.gen_either(ast, c, context, prefix),
            K::With => self.gen_with(ast, c, context, prefix, col),
            K::When => {
                self.token(prefix);
                let exp = self.subscripted(&ast.e(), context, c)?;
                self.expr(&exp);
                self.end_line();
                Ok(())
            }
            K::PrintS => {
                let exp = self.subscripted(&ast.e(), context, c)?;
                self.token(&format!("{}PrintT(", prefix));
                self.expr(&exp);
                self.token(")");
                self.end_line();
                Ok(())
            }
            K::Assert => {
                let exp = self.subscripted(&ast.e(), context, c)?;
                let sb = format!("{}Assert(", prefix);
                self.token(&sb);
                self.expr(&exp);
                let here = jlen(&sb);
                let sc = format!("\"Failure of assertion at {}.\")", ast.location());
                if self.nl() + 2 + jlen(&sc) < self.wrap() {
                    self.token(&format!(", {}", sc));
                } else {
                    self.token(", ");
                    self.end_line();
                    self.token(&format!("{}{}", nspaces(here), sc));
                }
                self.end_line();
                Ok(())
            }
            K::Skip => {
                self.token(prefix);
                self.token("TRUE");
                self.end_line();
                Ok(())
            }
            _ => Err(PErr::Bug(format!("Unexpected AST type {:?}", ast.k))),
        }
    }

    fn gen_assign(&mut self, ast: &Ast, c: &mut Changed, context: &str, prefix: &str) -> PR<()> {
        let mut c_this = c.clone();
        let mut sb = String::new();
        let sorted = sort_sass(&ast.ass());
        ast.set_ass(sorted.clone());
        let ass = sorted.to_vec();
        self.token(prefix);
        let mut i = 0;
        let mut has_multiple_vars = false;
        while i < ass.len() {
            let s_f = &ass[i];
            let var = s_f.lhs().name();
            if !self.vars.contains(&var) {
                return err_at(format!("Assignment to undeclared variable {}", var), s_f);
            }
            let mut i_first = i;
            let mut i_last = i;
            let mut has_assignment_with_no_subscript = false;
            let mut last_assignment_has_no_subscript = empty_expr(&s_f.lhs().e_opt());
            let mut s_l = &ass[i];
            while i_last < ass.len() && var == s_l.lhs().name() {
                if last_assignment_has_no_subscript {
                    has_assignment_with_no_subscript = true;
                }
                i_last += 1;
                if i_last < ass.len() {
                    s_l = &ass[i_last];
                    if empty_expr(&s_l.lhs().e_opt()) {
                        last_assignment_has_no_subscript = true;
                    }
                }
            }
            if i_last != ass.len() {
                has_multiple_vars = true;
            }
            i_last -= 1;
            if c_this.set(&var) > 1 || (i_last > i_first && has_assignment_with_no_subscript) {
                return err_at(format!("Multiple assignment to {}", var), ast);
            }
            if has_multiple_vars {
                sb += "/\\ ";
            }
            if i_first == i_last {
                let sass = s_f;
                let lhs_sub = sass.lhs().e_opt().unwrap_or_else(new_expr);
                let sub = self.subscripted(&lhs_sub, context, c)?;
                let rhs = self.subscripted(&sass.e(), context, c)?;
                if self.mp && (var == "pc" || self.is_procedure_var(&var) || self.is_process_set_var(&var) || var == "stack") {
                    sb += &format!("{}' = [", var);
                    let wrap_col = jlen(&sb) + 2;
                    sb += &format!("{} EXCEPT ", var);
                    let self_e = self.self_.clone().ok_or(PErr::Runtime)?;
                    if jlen(&sb) + jlen(prefix) > self.ctx.ss_wrap_column && self_e.borrow().tokens.is_empty() {
                        self.line(&sb);
                        sb = nspaces(wrap_col);
                    }
                    sb += "![";
                    self.token(&sb);
                    self.expr(&self_e);
                    self.token("]");
                    if !sub.borrow().tokens.is_empty() {
                        self.expr(&sub);
                    }
                    self.token(" = ");
                    self.expr(&rhs);
                    self.token("]");
                } else if !empty_expr(&sass.lhs().e_opt()) {
                    sb += &format!("{}' = [{} EXCEPT !", var, var);
                    self.token(&sb);
                    self.expr(&sub);
                    self.token(" = ");
                    self.expr(&rhs);
                    self.token("]");
                } else {
                    sb += &format!("{}' = ", var);
                    let needs_parens = needs_parentheses(&rhs.borrow().to_string_vector());
                    if needs_parens {
                        sb += "(";
                    }
                    self.token(&sb);
                    self.expr(&rhs);
                    if needs_parens {
                        self.token(")");
                    }
                }
                sb = String::new();
            } else {
                sb += &format!("{}' = [{} EXCEPT ", var, var);
                let mut cc = jlen(&sb);
                if i == 0 {
                    cc += jlen(prefix);
                }
                let subscript = self.mp && (self.is_procedure_var(&var) || self.is_process_set_var(&var));
                while i_first <= i_last {
                    let sass = &ass[i_first];
                    let lhs_sub = sass.lhs().e_opt().unwrap_or_else(new_expr);
                    let sub = self.subscripted(&lhs_sub, context, c)?;
                    let rhs = self.subscripted(&sass.e(), context, c)?;
                    sb += "!";
                    if subscript {
                        sb += "[";
                        self.token(&sb);
                        let s = self.self_for(context).ok_or(PErr::Runtime)?;
                        self.expr(&s);
                        self.token("]");
                    } else {
                        self.token(&sb);
                    }
                    self.expr(&sub);
                    self.token(" = ");
                    self.expr(&rhs);
                    self.token(if i_first == i_last { "]" } else { "," });
                    sb = String::new();
                    if i_first < i_last {
                        self.end_line();
                        sb = nspaces(cc);
                    }
                    i_first += 1;
                }
            }
            i = i_last + 1;
            if i < ass.len() {
                self.end_line();
                sb += &nspaces(jlen(prefix));
            }
        }
        self.end_line();
        c.merge(&c_this);
        Ok(())
    }

    /// Appends the UNCHANGED conjunct for the variables changed in the other branch only.
    fn unchanged_tail(&self, sb: &mut String, own: &Changed, other: &Changed) -> Option<Vec<String>> {
        let n = own.num_unchanged(Some(other));
        if n > 1 {
            let unc = own.unchanged_lines(Some(other), self.wrap() - jlen(sb) - 13);
            *sb += "UNCHANGED << ";
            let cc = jlen(sb);
            *sb += &unc[0];
            let mut lines = vec![];
            for u in &unc[1..] {
                lines.push(std::mem::take(sb));
                *sb = format!("{}{}", nspaces(cc), u);
            }
            *sb += " >>";
            lines.push(sb.clone());
            Some(lines)
        } else if n == 1 {
            let uc = own.unchanged(Some(other));
            if jlen(&uc) > 5 {
                *sb += &format!("UNCHANGED {}", uc);
            } else {
                *sb += &format!("{}' = {}", uc, uc);
            }
            Some(vec![sb.clone()])
        } else {
            None
        }
    }

    fn gen_if(&mut self, ast: &Ast, c: &mut Changed, context: &str, prefix: &str) -> PR<()> {
        let mut c_then = c.clone();
        let mut c_else = c.clone();
        let test = self.subscripted(&ast.e(), context, c)?;
        let mut sb = format!("{}IF ", prefix);
        let mut here = jlen(&sb);
        self.token(&sb);
        self.expr(&test);
        self.end_line();
        sb = format!("{}THEN ", nspaces(here));
        here = jlen(&sb);
        sb += "/\\ ";
        for s in ast.then().to_vec() {
            self.gen_stmt(&s, &mut c_then, context, &sb, here + 3)?;
            sb = format!("{}/\\ ", nspaces(here));
        }
        let mut line_unc_then = self.tlacode.len();
        self.line(&sb);
        sb = format!("{}ELSE ", nspaces(here - 5));
        here = jlen(&sb);
        let els = ast.els().to_vec();
        if els.is_empty() {
            sb += "/\\ TRUE";
            self.line(&sb);
            sb = format!("{}/\\ ", nspaces(here));
        } else {
            sb += "/\\ ";
            for s in els {
                self.gen_stmt(&s, &mut c_else, context, &sb, here + 3)?;
                sb = format!("{}/\\ ", nspaces(here));
            }
        }
        if let Some(lines) = self.unchanged_tail(&mut sb, &c_else, &c_then) {
            let n = lines.len();
            for (i, l) in lines.into_iter().enumerate() {
                if i + 1 < n {
                    self.line(&l);
                } else {
                    self.token(&l);
                    self.end_line();
                }
            }
        }
        sb = self.tlacode.remove(line_unc_then);
        if let Some(lines) = self.unchanged_tail(&mut sb, &c_then, &c_else) {
            for l in lines {
                self.tlacode.insert(line_unc_then, l);
                line_unc_then += 1;
            }
        }
        c.merge(&c_then);
        c.merge(&c_else);
        Ok(())
    }

    fn gen_either(&mut self, ast: &Ast, c: &mut Changed, context: &str, prefix: &str) -> PR<()> {
        let mut all_c = c.clone();
        let mut c_ors: Vec<Changed> = vec![];
        let mut uc_locs: Vec<usize> = vec![];
        let prefix_indent = jlen(prefix);
        let mut sb = format!("{}\\/ ", prefix);
        let here = jlen(&sb);
        for (i, or_clause) in ast.ors().to_vec().iter().enumerate() {
            if i != 0 {
                sb = format!("{}\\/ ", nspaces(prefix_indent));
            }
            sb += "/\\ ";
            let mut c_c = c.clone();
            for s in or_clause.to_vec() {
                self.gen_stmt(&s, &mut c_c, context, &sb, here + 3)?;
                sb = format!("{}/\\ ", nspaces(here));
            }
            all_c.merge(&c_c);
            c_ors.push(c_c);
            uc_locs.push(self.tlacode.len());
            self.line("Replace by UNCHANGED");
        }
        for i in (0..c_ors.len()).rev() {
            self.tlacode.remove(uc_locs[i]);
            let num = c_ors[i].num_unchanged(Some(&all_c));
            let not_changed = c_ors[i].unchanged(Some(&all_c));
            if num > 1 {
                self.tlacode.insert(uc_locs[i], format!("{}/\\ UNCHANGED <<{}>>", nspaces(here), not_changed));
            } else if num == 1 {
                let l = if jlen(&not_changed) > 5 { format!("{}/\\ UNCHANGED {}", nspaces(here), not_changed) } else { format!("{}/\\ {}' = {}", nspaces(here), not_changed, not_changed) };
                self.tlacode.insert(uc_locs[i], l);
            }
        }
        c.merge(&all_c);
        Ok(())
    }

    fn gen_with(&mut self, ast: &Ast, c: &mut Changed, context: &str, prefix: &str, col: i32) -> PR<()> {
        let exp = self.subscripted(&ast.e(), context, c)?;
        let do_ = ast.do_().to_vec();
        if ast.is_eq.get() {
            self.token(&format!("{}LET {} == ", prefix, ast.name()));
            self.expr(&exp);
            self.token(" IN");
        } else {
            self.token(&format!("{}\\E {} \\in ", prefix, ast.name()));
            self.expr(&exp);
            self.token(":");
        }
        self.end_line();
        let mut sb = nspaces(col + 2);
        if do_.len() > 1 {
            sb += "/\\ ";
        }
        for s in do_ {
            let l = jlen(&sb);
            self.gen_stmt(&s, c, context, &sb, l)?;
            sb = format!("{}/\\ ", nspaces(col + 2));
        }
        Ok(())
    }

    // ---- declarations ----
    fn gen_vars_and_defs(&mut self, globals: &V<Ast>, procs: &V<Ast>, processes: Option<&V<Ast>>, defs: Option<Expr>) -> PR<()> {
        let mut l_vars: Vec<String> = vec![];
        let mut g_vars: Vec<String> = vec![];
        if !self.ctx.omit_pc {
            g_vars.push("pc".to_string());
            self.vars.push("pc".to_string());
        }
        for d in globals.to_vec() {
            g_vars.push(d.name());
            self.vars.push(d.name());
        }
        if !procs.is_empty() {
            g_vars.push("stack".to_string());
            self.vars.push("stack".to_string());
        }
        for proc in procs.to_vec() {
            for d in proc.params().to_vec().into_iter().chain(proc.decls().to_vec()) {
                l_vars.push(d.name());
                self.vars.push(d.name());
                self.pc_v.push(d.name());
            }
        }
        if let Some(processes) = processes {
            for proc in processes.to_vec() {
                for d in proc.decls().to_vec() {
                    l_vars.push(d.name());
                    self.vars.push(d.name());
                    if !proc.is_eq.get() {
                        self.ps_v.push(d.name());
                    }
                }
            }
        }
        self.vars_rc = Rc::new(self.vars.clone());
        if self.ctx.has_default_initialization {
            self.line("CONSTANT defaultInitValue");
        }
        if empty_expr(&defs) {
            g_vars.extend(l_vars);
            self.gen_var_decl(&g_vars);
        } else {
            self.gen_var_decl(&g_vars);
            self.line("");
            self.line("(* define statement *)");
            self.expr(&defs.unwrap());
            self.line("");
            self.gen_var_decl(&l_vars);
            g_vars.extend(l_vars);
        }
        self.line("");
        if g_vars.is_empty() {
            return err("The algorithm has no variables.");
        }
        self.token("vars == << ");
        let indent = self.nl();
        for (i, vbl) in g_vars.iter().enumerate() {
            if i > 0 {
                self.token(", ");
            }
            if self.nl() + jlen(vbl) + 1 > self.wrap() {
                self.end_line();
                self.next_line = nspaces(indent);
            }
            self.token(vbl);
        }
        if self.nl() + 3 + 1 > self.wrap() {
            self.end_line();
            self.next_line = nspaces(7);
        }
        self.token(" >>");
        self.line("");
        Ok(())
    }
    fn gen_var_decl(&mut self, vars: &[String]) {
        if vars.is_empty() {
            return;
        }
        let kw = if vars.len() > 1 { "VARIABLES " } else { "VARIABLE " };
        self.token(kw);
        for (i, vbl) in vars.iter().enumerate() {
            if i > 0 {
                self.token(", ");
            }
            if self.nl() + jlen(vbl) + 1 > self.wrap() {
                self.end_line();
                self.next_line.push_str(&nspaces(jlen(kw)));
            }
            self.token(vbl);
        }
        self.end_line();
    }
    fn gen_proc_set(&mut self) {
        if self.st.processes.is_empty() {
            return;
        }
        self.token("ProcSet == ");
        for i in 0..self.st.processes.len() {
            let (is_eq, id) = (self.st.processes[i].is_eq, self.st.processes[i].id.clone());
            if i > 0 {
                self.token(" \\cup ");
            }
            self.token(if is_eq { "{" } else { "(" });
            self.expr(&id);
            self.token(if is_eq { "}" } else { ")" });
        }
        self.end_line();
        self.line("");
    }

    fn var_decl(&mut self, name: &str, is_eq: bool, val: &Expr, is: &str) {
        self.token(&format!("{}/\\ ", is));
        self.token(&format!("{}{}", name, if is_eq { " = " } else { " \\in " }));
        let needs_parens = needs_parentheses(&val.borrow().to_string_vector());
        if needs_parens {
            self.token("(");
        }
        self.expr(val);
        if needs_parens {
            self.token(")");
        }
        self.end_line();
    }

    fn gen_init(&mut self, globals: &V<Ast>, procs: &V<Ast>, processes: Option<&V<Ast>>) -> PR<()> {
        let col = 8;
        let pad = nspaces(col);
        let no_change = Changed::new(Rc::new(vec![]));
        let mut is = "Init == ".to_string();
        if !globals.is_empty() {
            is += "(* Global variables *)";
            self.line(&is);
            for d in globals.to_vec() {
                self.var_decl(&d.name(), d.is_eq.get(), &d.e(), &pad);
            }
            is = pad.clone();
        }
        for proc in procs.to_vec() {
            if proc.params().is_empty() && proc.decls().is_empty() {
                continue;
            }
            is += &format!("(* Procedure {} *)", proc.name());
            self.line(&is);
            is = pad.clone();
            for d in proc.params().to_vec().into_iter().chain(proc.decls().to_vec()) {
                if !self.mp {
                    self.var_decl(&d.name(), true, &d.e(), &pad);
                } else {
                    self.token(&format!("{}/\\ ", pad));
                    self.token(&format!("{} = [ self \\in ProcSet |-> ", d.name()));
                    let e = self.add_subscripts(&d.e(), sub_expr(self.self_for("procedure")).as_ref(), &no_change)?;
                    self.expr(&e);
                    self.token("]");
                    self.end_line();
                }
            }
        }
        if let Some(processes) = processes {
            for proc in processes.to_vec() {
                if proc.decls().is_empty() {
                    continue;
                }
                is += &format!("(* Process {} *)", proc.name());
                self.line(&is);
                is = pad.clone();
                let id = proc.e();
                for d in proc.decls().to_vec() {
                    self.token(&format!("{}/\\ ", pad));
                    if proc.is_eq.get() {
                        self.token(&format!("{}{}", d.name(), if d.is_eq.get() { " = " } else { " \\in " }));
                        self.expr(&d.e());
                    } else if d.is_eq.get() {
                        self.token(&format!("{} = [self \\in ", d.name()));
                        self.expr(&id);
                        self.token(" |-> ");
                        let e = self.add_subscripts(&d.e(), sub_expr(self.self_for("procedure")).as_ref(), &no_change)?;
                        self.expr(&e);
                        self.token("]");
                    } else {
                        let subexpr = clone_and_normalize(&id);
                        let expr = make_expr(vec![vec![tok("[", 0, BUILTIN), tok("CHOOSE", 1, BUILTIN), tok("self", 8, IDENT), tok("\\in ", 13, BUILTIN)]]);
                        let r = subexpr.borrow_mut().prepend(&expr.borrow(), 1);
                        r.map_err(PErr::Msg)?;
                        let expr = expr_from(vec![vec![tok(":", 0, BUILTIN), tok("TRUE", 2, BUILTIN), tok("]", 6, BUILTIN)]]);
                        let r = expr.borrow_mut().prepend(&subexpr.borrow(), 1);
                        r.map_err(PErr::Msg)?;
                        self.token(&format!("{} \\in [", d.name()));
                        self.expr(&id);
                        self.token(" -> ");
                        let e = self.add_subscripts(&d.e(), Some(&expr), &no_change)?;
                        self.expr(&e);
                        self.token("]");
                    }
                    self.end_line();
                }
            }
        }
        if !procs.is_empty() {
            is += if self.mp { "/\\ stack = [self \\in ProcSet |-> << >>]" } else { "/\\ stack = << >>" };
            self.line(&is);
            is = pad.clone();
        }
        if !self.ctx.omit_pc {
            if self.mp {
                let n = self.st.processes.len();
                let use_case = n != 1;
                is += if use_case { "/\\ pc = [self \\in ProcSet |-> CASE " } else { "/\\ pc = [self \\in ProcSet |-> " };
                let col_pc = jlen(&is) - 3;
                for p in 0..n {
                    let (is_eq, id, ipc) = {
                        let pe = &self.st.processes[p];
                        (pe.is_eq, pe.id.clone(), pe.i_pc.clone().unwrap_or_else(|| "null".to_string()))
                    };
                    if use_case {
                        is += if is_eq { "self = " } else { "self \\in " };
                        self.token(&is);
                        self.expr(&id);
                        is = format!(" -> \"{}{}", ipc, if p == n - 1 { "\"]" } else { "\"" });
                    } else {
                        is += &format!("\"{}\"]", ipc);
                    }
                    self.token(&is);
                    self.end_line();
                    is = nspaces(col_pc);
                    if p + 1 < n {
                        is += "[] ";
                    }
                }
            } else {
                is += &format!("/\\ pc = \"{}\"", self.st.i_pc.clone().unwrap_or_else(|| "null".to_string()));
                self.line(&is);
            }
        }
        self.line("");
        Ok(())
    }

    // ---- Next, Spec, Termination ----
    fn gen_next(&mut self) {
        let (omit_pc, mp) = (self.ctx.omit_pc, self.mp);
        if omit_pc && !mp {
            return;
        }
        let terminating = !(self.ctx.no_done_disjunct || self.ctx.omit_stuttering_when_done);
        if terminating {
            self.line("(* Allow infinite stuttering to prevent deadlock on termination. *)");
            if mp {
                self.line("Terminating == /\\ \\A self \\in ProcSet: pc[self] = \"Done\"");
                self.line(&format!("{}/\\ UNCHANGED vars", nspaces(15)));
            } else {
                self.line("Terminating == pc = \"Done\" /\\ UNCHANGED vars");
            }
            self.line("");
        }
        let mut next_s: Vec<String> = vec![];
        let mut sb = String::new();
        let max = self.wrap() - 11;
        for a in &self.next_step {
            if jlen(a) + 4 + jlen(&sb) > max {
                next_s.push(std::mem::take(&mut sb));
            }
            if !sb.is_empty() {
                sb += " \\/ ";
            }
            sb += a;
        }
        if !sb.is_empty() {
            next_s.push(sb);
        }
        let mut next_ss: Vec<String> = vec![];
        let mut sb = String::new();
        let max = self.wrap() - jlen("Next == \\/ (\\E self \\in ProcSet: \\/ ");
        if mp && !self.st.procs.is_empty() {
            for p in &self.st.procs {
                if jlen(&p.name) + 10 + jlen(&sb) > max {
                    next_ss.push(std::mem::take(&mut sb));
                }
                if !sb.is_empty() {
                    sb += " \\/ ";
                }
                sb += &p.name;
                sb += "(self)";
            }
            if !sb.is_empty() {
                next_ss.push(format!("{})", sb));
            }
        }
        let mut next_ssp: Vec<Vec<String>> = vec![];
        if mp {
            for p in &self.st.processes {
                if p.is_eq {
                    continue;
                }
                let mut vec = vec![];
                let mut sb = "(\\E self \\in ".to_string();
                let sv = p.id.borrow().to_string_vector();
                let col = jlen(&sb);
                sb += sv.first().map(|s| s.as_str()).unwrap_or("");
                for s in sv.iter().skip(1) {
                    vec.push(std::mem::take(&mut sb));
                    sb = format!("{}{}", nspaces(col), s);
                }
                sb += &format!(": {}(self))", p.name);
                vec.push(sb);
                next_ssp.push(vec);
            }
        }
        let mut sb = "Next == ".to_string();
        let col = jlen(&sb) + 2;
        let or_line = format!("{} \\/ ", nspaces(col));
        for s in &next_s {
            sb += s;
            self.line(&sb);
            sb = or_line.clone();
        }
        if !next_ss.is_empty() {
            sb += "(\\E self \\in ProcSet: ";
            let col2 = jlen(&sb);
            if next_ss.len() > 1 {
                sb += " \\/ ";
            }
            for s in &next_ss {
                sb += s;
                self.line(&sb);
                sb = format!("{} \\/ ", nspaces(col2));
            }
            sb = or_line.clone();
        }
        for (i, v) in next_ssp.iter().enumerate() {
            for l in v {
                sb += l;
                self.line(&sb);
                sb = if next_s.is_empty() && next_ss.is_empty() && i == 0 { nspaces(col - 2) } else { nspaces(col + 4) };
            }
            sb = or_line.clone();
        }
        if terminating {
            sb += "Terminating";
            self.line(&sb);
        }
        self.line("");
    }

    fn minus_labels_test(xf: &str, q_self: &str, minus: &[String]) -> String {
        let mut s = format!("{}_vars(", xf);
        if !minus.is_empty() {
            s += &format!("(pc[{}", q_self);
            if minus.len() == 1 {
                s += &format!("] # \"{}\"", minus[0]);
            } else {
                s += &format!("] \\notin {{\"{}\"}}", minus.join("\", \""));
            }
            s += ") /\\ ";
        }
        s
    }

    fn gen_spec(&mut self) {
        let safety = "Init /\\ [][Next]_vars";
        let fo = self.ctx.fairness_option.as_str();
        let mp = self.mp;
        if fo == "nof" || (!mp && fo.is_empty()) {
            self.line(&format!("Spec == {}", safety));
            self.line("");
            return;
        }
        let wf_next = fo == "wfNext" || self.ctx.fair_algorithm || (!mp && (fo == "wf" || fo == "sf"));
        let mut formulas: Vec<ProcessFairness> = vec![];
        if mp {
            for p in &self.st.processes {
                let p_ast = &p.ast;
                let fairness = p_ast.fairness.get();
                if fairness == UNFAIR_PROC {
                    continue;
                }
                let xf = if fairness == WF_PROC { "WF" } else { "SF" };
                let p_self = p.id.borrow().to_string_vector();
                let mut make_let_in = false;
                let mut q_self = "self".to_string();
                if p.is_eq {
                    if p_self.len() > 1 {
                        make_let_in = true;
                    } else {
                        q_self = p_self.first().cloned().unwrap_or_default();
                    }
                }
                let mut prefix: Vec<String> = vec![];
                if make_let_in || !p.is_eq {
                    let (begin, end) = if p.is_eq { ("LET self == ", "") } else { ("\\A self \\in ", " : ") };
                    let padding = nspaces(jlen(begin));
                    let n = p_self.len();
                    for (j, l) in p_self.iter().enumerate() {
                        let mut line = format!("{}{}", if j == 0 { begin } else { padding.as_str() }, l);
                        if j == n - 1 {
                            line += end;
                        }
                        prefix.push(line);
                    }
                    if make_let_in {
                        prefix.push("IN ".to_string());
                    }
                }
                let minus = p_ast.minus_labels_opt().map(|v| v.to_vec()).unwrap_or_default();
                let plus = p_ast.plus_labels_opt().map(|v| v.to_vec()).unwrap_or_default();
                let mut wf = Self::minus_labels_test(xf, &q_self, &minus);
                wf += &p.name;
                if !p.is_eq {
                    wf += "(self)";
                }
                wf += ")";
                let mut sf = None;
                if xf == "WF" && !plus.is_empty() {
                    let arg = if p.is_eq { "" } else { "(self)" };
                    sf = Some(plus.iter().map(|l| format!("SF_vars({}{})", l, arg)).collect::<Vec<_>>().join(" /\\ "));
                }
                let mut prcd: Vec<FormulaPair> = vec![];
                for original in p_ast.procedures_called().to_vec() {
                    let name = self.st.use_this(PROCEDURE, &original, "");
                    let pe = match self.st.procs.get(self.st.find_proc(&name)) {
                        Some(pe) => pe,
                        None => continue,
                    };
                    let prc = &pe.ast;
                    let minus = prc.minus_labels_opt().map(|v| v.to_vec()).unwrap_or_default();
                    let plus = prc.plus_labels_opt().map(|v| v.to_vec()).unwrap_or_default();
                    let mut wfp = Self::minus_labels_test(xf, &q_self, &minus);
                    wfp += &format!("{}({}))", pe.name, q_self);
                    let mut sfp = None;
                    if xf == "WF" && !plus.is_empty() {
                        sfp = Some(plus.iter().map(|l| format!("SF_vars({}({}))", l, q_self)).collect::<Vec<_>>().join(" /\\ "));
                    }
                    prcd.push(FormulaPair { wf: wfp, sf: sfp });
                }
                formulas.push(ProcessFairness { prefix, body: FormulaPair { wf, sf }, prcd });
            }
        }
        if !wf_next && formulas.is_empty() {
            self.line(&format!("Spec == {}", safety));
            self.line("");
            return;
        }
        self.line(&format!("Spec == /\\ {}", safety));
        let indent = jlen("Spec == /\\ ");
        if wf_next {
            self.line("        /\\ WF_vars(Next)");
        }
        let wrap = self.wrap();
        for f in &formulas {
            let s = format!("        /\\ {}", f.format(indent, wrap));
            for l in java_split_lines(&s) {
                self.line(&l);
            }
        }
        self.line("");
    }

    fn gen_termination(&mut self) {
        if self.ctx.omit_pc || self.ctx.omit_stuttering_when_done {
            return;
        }
        let s = format!("Termination == <>({} = \"Done\")", if self.mp { "\\A self \\in ProcSet: pc[self]" } else { "pc" });
        self.line(&s);
        self.line("");
    }
}
