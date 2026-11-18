//! Turns the parsed algorithm into a flat list of labeled steps whose statements have no labels
//! inside them, adding the reads and writes of `pc` and `stack` (port of pcal.PcalTranslate).
use super::ast::*;
use super::expr::{expr_from, make_expr, new_expr, tok, Expr, Tok, ADDED, BUILTIN, IDENT, STRING};
use super::symtab::{SymTab, LABEL};
use super::{err, err_at, Ctx, PErr, PR};

fn string_token(s: &str) -> Tok {
    tok(s, 0, STRING)
}
fn added_token(s: &str) -> Tok {
    tok(s, 0, ADDED)
}
fn builtin_token(s: &str) -> Tok {
    tok(s, 0, BUILTIN)
}
fn ident_token(s: &str) -> Tok {
    tok(s, 0, IDENT)
}

/// `TokVectorToExpr`: one line of copies of the tokens, `spaces` apart.
fn tok_vector_to_expr(toks: Vec<Tok>, spaces: i32) -> Expr {
    let mut line = vec![];
    let mut next_col = 0;
    for t in toks {
        let c = tok(&t.borrow().string, next_col, t.borrow().typ);
        next_col += c.borrow().get_width() + spaces;
        line.push(c);
    }
    make_expr(vec![line])
}

fn make_new_stack_top_expr_pretty(expr: &Expr) {
    let e = expr.borrow();
    let n = e.tokens.len();
    for (i, line) in e.tokens.iter().enumerate() {
        let mut next_col = if i == 0 || i == n - 1 { 1 } else { 6 };
        for t in line {
            let mut t = t.borrow_mut();
            t.column = next_col;
            next_col += t.get_width();
            if t.typ != BUILTIN {
                continue;
            }
            match t.string.as_str() {
                "|->" | "\u{21A6}" => {
                    t.column += 1;
                    if t.column < 16 {
                        t.column = 16;
                    }
                    next_col = t.column + 5;
                }
                "[" | "<<" => next_col += 1,
                "]" | ">>" => {
                    t.column += 1;
                    next_col += 1;
                }
                "\\o" => {
                    t.column += 1;
                    next_col += 2;
                }
                _ => {}
            }
        }
    }
}

fn make_assign(id: &str, exp: Expr) -> Ast {
    let sass = new_node(K::SingleAssign);
    sass.lhs().set_name(id);
    sass.lhs().set_e(make_expr(vec![]));
    sass.set_e(exp);
    let result = new_node(K::Assign);
    result.set_ass(V::of(vec![sass]));
    result
}

fn is_true(expr: &Expr) -> PR<bool> {
    let e = expr.borrow();
    if e.tokens.len() > 1 {
        return Ok(false);
    }
    let line = e.tokens.first().ok_or(PErr::Runtime)?;
    let s = |i: usize| line[i].borrow().string.clone();
    Ok(match line.len() {
        1 => s(0) == "TRUE",
        3 => s(0) == "(" && s(1) == "TRUE" && s(2) == ")",
        _ => false,
    })
}

fn check_pc(label: &str) -> Ast {
    let w = new_node(K::When);
    w.set_e(tok_vector_to_expr(vec![added_token("pc"), builtin_token("="), string_token(label)], 1));
    w
}
fn update_pc(next: &str) -> Ast {
    make_assign("pc", make_expr(vec![vec![string_token(next)]]))
}

struct Exploder<'a> {
    st: &'a SymTab,
    omit_pc: bool,
    current_procedure: Option<String>,
}

/// `PcalTranslate.Explode`
pub fn explode(ast: &Ast, st: &SymTab, ctx: &Ctx) -> PR<Ast> {
    let mut x = Exploder { st, omit_pc: ctx.omit_pc, current_procedure: None };
    let newast = new_node(ast.k);
    newast.col.set(ast.col.get());
    newast.line.set(ast.line.get());
    newast.set_name(&ast.name());
    newast.set_decls(ast.decls());
    newast.set_defs(ast.defs());
    newast.has_origin.set(ast.has_origin.get());
    let prcds = V::new();
    newast.set_prcds(prcds.clone());
    for p in ast.prcds().to_vec() {
        prcds.push(x.explode_procedure(&p)?);
    }
    if ast.k == K::Uniprocess {
        newast.set_body(x.explode_body(&ast.body(), "Done")?);
    } else {
        let procs = V::new();
        newast.set_procs(procs.clone());
        for p in ast.procs().to_vec() {
            let np = new_node(K::Process);
            np.has_origin.set(p.has_origin.get());
            np.col.set(p.col.get());
            np.line.set(p.line.get());
            np.set_name(&p.name());
            np.is_eq.set(p.is_eq.get());
            np.set_e(p.e());
            np.set_decls(p.decls());
            np.set_body(x.explode_body(&p.body(), "Done")?);
            procs.push(np);
        }
    }
    Ok(newast)
}

type Pair = (V<Ast>, V<Ast>);

impl Exploder<'_> {
    /// The loop shared by ExplodeUniprocess, ExplodeProcedure and ExplodeProcess.
    fn explode_body(&mut self, body: &V<Ast>, last: &str) -> PR<V<Ast>> {
        let result = V::new();
        let b = body.to_vec();
        for (i, ls) in b.iter().enumerate() {
            let next = match b.get(i + 1) {
                Some(n) => n.name(),
                None => last.to_string(),
            };
            result.add_all(&self.explode_labeled_stmt(ls, &next)?);
        }
        Ok(result)
    }
    fn explode_procedure(&mut self, ast: &Ast) -> PR<Ast> {
        let newast = new_node(K::Procedure);
        newast.has_origin.set(ast.has_origin.get());
        newast.col.set(ast.col.get());
        newast.line.set(ast.line.get());
        newast.set_name(&ast.name());
        self.current_procedure = Some(ast.name());
        newast.set_params(ast.params());
        newast.set_decls(ast.decls());
        let last = self.st.use_this(LABEL, "Error", "");
        newast.set_body(self.explode_body(&ast.body(), &last)?);
        self.current_procedure = None;
        Ok(newast)
    }

    /// Returns (statements, exploded labeled statements, needsGoto).
    fn copy_and_explode_last_stmt(&mut self, stmts: Option<V<Ast>>, next: &str) -> PR<(V<Ast>, V<Ast>, bool)> {
        let mut result1 = V::new();
        let result2 = V::new();
        let mut needs_goto = false;
        match stmts {
            Some(stmts) if !stmts.is_empty() => {
                let last = stmts.get(stmts.len() - 1);
                result1 = stmts;
                let pop = |r: &V<Ast>| {
                    r.remove(r.len() - 1);
                };
                match last.k {
                    K::LabelIf => {
                        let pair = self.explode_label_if(&last, next)?;
                        pop(&result1);
                        result1.add_all(&pair.0);
                        result2.add_all(&pair.1);
                    }
                    K::LabelEither => {
                        let pair = self.explode_label_either(&last, next)?;
                        pop(&result1);
                        result1.add_all(&pair.0);
                        result2.add_all(&pair.1);
                    }
                    K::Goto => {
                        pop(&result1);
                        result1.push(update_pc(&last.to()));
                    }
                    K::Call => {
                        pop(&result1);
                        result1.add_all(&self.explode_call(&last, next)?);
                    }
                    K::Return => {
                        pop(&result1);
                        result1.add_all(&self.explode_return(&last)?);
                    }
                    K::CallReturn => {
                        pop(&result1);
                        result1.add_all(&self.explode_call_return(&last)?);
                    }
                    K::CallGoto => {
                        pop(&result1);
                        let call = new_node(K::Call);
                        *call.to.borrow_mut() = last.to();
                        call.set_args(last.args());
                        call.line.set(last.line.get());
                        call.col.set(last.col.get());
                        call.has_origin.set(last.has_origin.get());
                        let after = last.after.borrow().clone();
                        result1.add_all(&self.explode_call(&call, &after)?);
                    }
                    K::If => {
                        let p1 = self.copy_and_explode_last_stmt(last.then_opt(), next)?;
                        let p2 = self.copy_and_explode_last_stmt(last.els_opt(), next)?;
                        result2.add_all(&p1.1);
                        result2.add_all(&p2.1);
                        last.set_then(p1.0.clone());
                        last.set_els(p2.0.clone());
                        if !self.omit_pc {
                            needs_goto = p1.2 && p2.2;
                            if !needs_goto {
                                if p1.2 {
                                    p1.0.push(update_pc(next));
                                }
                                if p2.2 {
                                    p2.0.push(update_pc(next));
                                }
                            }
                        }
                    }
                    K::Either => {
                        needs_goto = true;
                        let mut needs: Vec<bool> = vec![];
                        let ors = last.ors();
                        for i in 0..ors.len() {
                            let p = self.copy_and_explode_last_stmt(Some(ors.get(i)), next)?;
                            ors.set(i, p.0);
                            result2.add_all(&p.1);
                            needs_goto = needs_goto && p.2;
                            needs.push(p.2);
                        }
                        if !self.omit_pc && !needs_goto {
                            for i in 0..ors.len() {
                                if needs[i] {
                                    ors.get(i).push(update_pc(next));
                                }
                            }
                        }
                    }
                    K::With => {
                        let p = self.copy_and_explode_last_stmt(last.do_opt(), next)?;
                        last.set_do(p.0);
                        result2.add_all(&p.1);
                        needs_goto = p.2;
                    }
                    _ => needs_goto = true,
                }
            }
            _ => needs_goto = true,
        }
        if self.omit_pc {
            needs_goto = false;
        }
        Ok((result1, result2, needs_goto))
    }

    fn copy_and_explode_last_stmt_with_goto(&mut self, stmts: V<Ast>, next: &str) -> PR<Pair> {
        let res = self.copy_and_explode_last_stmt(Some(stmts), next)?;
        if res.2 {
            res.0.push(update_pc(next));
        }
        Ok((res.0, res.1))
    }

    fn explode_labeled_stmt(&mut self, ast: &Ast, next: &str) -> PR<V<Ast>> {
        let stmts = ast.stmts();
        if !stmts.is_empty() && stmts.get(0).k == K::While {
            return self.explode_while(ast, next);
        }
        let newast = new_node(K::LabeledStmt);
        let pair = self.copy_and_explode_last_stmt_with_goto(stmts.copy(), next)?;
        let result = V::new();
        newast.has_origin.set(ast.has_origin.get());
        newast.col.set(ast.col.get());
        newast.line.set(ast.line.get());
        newast.set_name(&ast.name());
        newast.set_stmts(pair.0.clone());
        if !self.omit_pc {
            pair.0.insert(0, check_pc(&newast.name()));
            result.push(newast);
        }
        result.add_all(&pair.1);
        Ok(result)
    }

    fn explode_labeled_stmt_seq(&mut self, seq: &V<Ast>, next: &str) -> PR<V<Ast>> {
        let result = V::new();
        let s = seq.to_vec();
        for (i, stmt) in s.iter().enumerate() {
            let nxt = match s.get(i + 1) {
                Some(n) => n.name(),
                None => next.to_string(),
            };
            result.add_all(&self.explode_labeled_stmt(stmt, &nxt)?);
        }
        Ok(result)
    }

    fn explode_while(&mut self, ast: &Ast, next: &str) -> PR<V<Ast>> {
        let result = V::new();
        let stmts = ast.stmts();
        let w = stmts.get(0);
        let newast = new_node(K::LabeledStmt);
        newast.has_origin.set(true);
        newast.col.set(ast.col.get());
        newast.line.set(ast.line.get());
        newast.set_name(&ast.name());
        let new_stmts = V::new();
        newast.set_stmts(new_stmts.clone());
        if !self.omit_pc {
            new_stmts.push(check_pc(&ast.name()));
        }
        let lab_do = w.lab_do();
        let unlab_do_next = match lab_do.try_get(0) {
            Some(ls) => ls.name(),
            None => ast.name(),
        };
        let pair1 = self.copy_and_explode_last_stmt_with_goto(w.unlab_do().copy(), &unlab_do_next)?;
        let rest = stmts.copy();
        rest.remove(0);
        let pair2 = self.copy_and_explode_last_stmt_with_goto(rest, next)?;
        let test_is_true = is_true(&w.e())?;
        if test_is_true {
            new_stmts.add_all(&pair1.0);
        } else {
            let if_s = new_node(K::If);
            if_s.set_e(w.e());
            if_s.set_then(pair1.0.clone());
            if_s.set_els(pair2.0.clone());
            if_s.has_origin.set(true);
            new_stmts.push(if_s);
        }
        result.push(newast);
        let l = lab_do.to_vec();
        for (i, ls) in l.iter().enumerate() {
            let next_lsl = match l.get(i + 1) {
                Some(n) => n.name(),
                None => ast.name(),
            };
            result.add_all(&self.explode_labeled_stmt(ls, &next_lsl)?);
        }
        result.add_all(&pair1.1);
        if !test_is_true {
            result.add_all(&pair2.1);
        }
        Ok(result)
    }

    fn explode_label_if(&mut self, ast: &Ast, next: &str) -> PR<Pair> {
        let result1 = V::new();
        let result2 = V::new();
        let newif = new_node(K::If);
        let (lab_then, lab_else) = (ast.lab_then(), ast.lab_else());
        let first_then = lab_then.try_get(0).map(|l| l.name()).unwrap_or_else(|| next.to_string());
        let first_else = lab_else.try_get(0).map(|l| l.name()).unwrap_or_else(|| next.to_string());
        let exploded_then = self.copy_and_explode_last_stmt_with_goto(ast.unlab_then(), &first_then)?;
        let exploded_else = self.copy_and_explode_last_stmt_with_goto(ast.unlab_else(), &first_else)?;
        newif.set_e(ast.e());
        newif.col.set(ast.col.get());
        newif.line.set(ast.line.get());
        newif.set_then(exploded_then.0);
        newif.set_els(exploded_else.0);
        newif.has_origin.set(ast.has_origin.get());
        result1.push(newif);
        result2.add_all(&self.explode_labeled_stmt_seq(&lab_then, next)?);
        result2.add_all(&self.explode_labeled_stmt_seq(&lab_else, next)?);
        result2.add_all(&exploded_then.1);
        result2.add_all(&exploded_else.1);
        Ok((result1, result2))
    }

    fn explode_label_either(&mut self, ast: &Ast, next: &str) -> PR<Pair> {
        let result1 = V::new();
        let result2 = V::new();
        let new_either = new_node(K::Either);
        new_either.col.set(ast.col.get());
        new_either.line.set(ast.line.get());
        new_either.has_origin.set(ast.has_origin.get());
        let ors = V::new();
        new_either.set_ors(ors.clone());
        for clause in ast.clauses().to_vec() {
            let lab_or = clause.lab_or();
            let nxt = lab_or.try_get(0).map(|l| l.name()).unwrap_or_else(|| next.to_string());
            let res = self.copy_and_explode_last_stmt_with_goto(clause.unlab_or(), &nxt)?;
            ors.push(res.0);
            result2.add_all(&res.1);
            result2.add_all(&self.explode_labeled_stmt_seq(&lab_or, next)?);
        }
        result1.push(new_either);
        Ok((result1, result2))
    }

    fn single(&self, ast: &Ast, var: &str, sub: Expr, rhs: Expr) -> Ast {
        let sass = new_node(K::SingleAssign);
        sass.line.set(ast.line.get());
        sass.col.set(ast.col.get());
        sass.lhs().set_name(var);
        sass.lhs().set_e(sub);
        sass.set_e(rhs);
        sass
    }
    fn assign(&self, ast: &Ast, ass: Vec<Ast>) -> Ast {
        let a = new_node(K::Assign);
        a.line.set(ast.line.get());
        a.col.set(ast.col.get());
        a.set_ass(V::of(ass));
        a
    }

    fn explode_call(&mut self, ast: &Ast, next: &str) -> PR<V<Ast>> {
        let result = V::new();
        let to = self.st.find_proc(&ast.to());
        if to == self.st.procs.len() {
            return err_at(format!("Call of non-existent procedure {}", ast.to()), ast);
        }
        let pe = &self.st.procs[to];
        let expr = new_expr();
        {
            let mut e = expr.borrow_mut();
            e.add_line();
            e.add_token(builtin_token("<<"));
            e.add_token(builtin_token("["));
            e.add_token(ident_token("procedure"));
            e.add_token(builtin_token("|->"));
            e.add_token(string_token(&ast.to()));
            e.add_token(builtin_token(","));
            e.add_line();
            e.add_token(ident_token("pc"));
            e.add_token(builtin_token("|->"));
            e.add_token(string_token(next));
            for decl in pe.decls.to_vec().into_iter().chain(pe.params.to_vec()) {
                e.add_token(builtin_token(","));
                e.add_line();
                e.add_token(ident_token(&decl.name()));
                e.add_token(builtin_token("|->"));
                e.add_token(ident_token(&decl.name()));
            }
            e.add_token(builtin_token("]"));
            e.add_token(builtin_token(">>"));
            e.add_line();
            e.add_token(builtin_token("\\o"));
            e.add_token(added_token("stack"));
        }
        make_new_stack_top_expr_pretty(&expr);
        expr.borrow_mut().normalize();
        let mut ass = vec![self.single(ast, "stack", make_expr(vec![]), expr)];
        let params = pe.params.to_vec();
        let args = ast.args();
        if params.len() != args.len() {
            return err_at(format!("Procedure {} called with wrong number of arguments", ast.to()), ast);
        }
        for (i, decl) in params.iter().enumerate() {
            let sass = self.single(ast, &decl.name(), make_expr(vec![]), args.get(i));
            sass.has_origin.set(decl.has_origin.get());
            ass.push(sass);
        }
        let a = self.assign(ast, ass);
        a.has_origin.set(!params.is_empty());
        result.push(a);
        self.init_decls(ast, &pe.decls, &result);
        result.push(update_pc(pe.i_pc.as_deref().unwrap_or("null")));
        Ok(result)
    }
    /// The assignments that reset the local variables of a called procedure.
    fn init_decls(&self, ast: &Ast, decls: &V<Ast>, result: &V<Ast>) {
        for decl in decls.to_vec() {
            let sass = self.single(ast, &decl.name(), make_expr(vec![]), decl.e());
            sass.has_origin.set(decl.has_origin.get());
            let a = self.assign(ast, vec![sass]);
            a.has_origin.set(decl.has_origin.get());
            result.push(a);
        }
    }

    fn head_stack(&self, field: &str) -> Expr {
        let e = expr_from(vec![vec![ident_token("Head"), builtin_token("("), added_token("stack"), builtin_token(")"), builtin_token("."), ident_token(field)]]);
        e.borrow_mut().normalize();
        e
    }

    fn explode_return(&mut self, ast: &Ast) -> PR<V<Ast>> {
        let result = V::new();
        if ast.from().is_none() {
            *ast.from.borrow_mut() = self.current_procedure.clone();
        }
        let from_name = match ast.from() {
            Some(f) => f,
            None => return err_at("`return' statement not in procedure", ast),
        };
        let from = self.st.find_proc(&from_name);
        if from >= self.st.procs.len() {
            return err_at("Error in procedure (perhaps name used elsewhere)", ast);
        }
        let pe = &self.st.procs[from];
        result.push(self.assign(ast, vec![self.single(ast, "pc", new_expr(), self.head_stack("pc"))]));
        for decl in pe.decls.to_vec().into_iter().chain(pe.params.to_vec()) {
            let sass = self.single(ast, &decl.name(), new_expr(), self.head_stack(&decl.name()));
            sass.has_origin.set(ast.has_origin.get());
            let a = self.assign(ast, vec![sass]);
            a.has_origin.set(ast.has_origin.get());
            result.push(a);
        }
        let tail = expr_from(vec![vec![ident_token("Tail"), builtin_token("("), added_token("stack"), builtin_token(")")]]);
        tail.borrow_mut().normalize();
        let sass = self.single(ast, "stack", new_expr(), tail);
        sass.has_origin.set(ast.has_origin.get());
        let a = self.assign(ast, vec![sass]);
        a.has_origin.set(ast.has_origin.get());
        result.push(a);
        Ok(result)
    }

    fn explode_call_return(&mut self, ast: &Ast) -> PR<V<Ast>> {
        let result = V::new();
        let from_name = match ast.from() {
            Some(f) => f,
            None => return err(format!("`return' statement following `call' at {} not in a procedure", ast.location())),
        };
        let from = self.st.find_proc(&from_name);
        if from >= self.st.procs.len() {
            return Err(PErr::Runtime);
        }
        let pe_from = &self.st.procs[from];
        let to = self.st.find_proc(&ast.to());
        if to == self.st.procs.len() {
            return err_at(format!("Call of non-existent procedure {}", ast.to()), ast);
        }
        let pe_to = &self.st.procs[to];
        let mut ass: Vec<Ast> = vec![];
        if from_name != ast.to() {
            for decl in pe_from.decls.to_vec() {
                ass.push(self.single(ast, &decl.name(), new_expr(), self.head_stack(&decl.name())));
            }
            let expr = new_expr();
            {
                let mut e = expr.borrow_mut();
                e.add_line();
                e.add_token(builtin_token("<<"));
                e.add_token(builtin_token("["));
                e.add_token(ident_token("procedure"));
                e.add_token(builtin_token("|->"));
                e.add_token(string_token(&ast.to()));
                e.add_token(builtin_token(","));
                e.add_line();
                e.add_token(ident_token("pc"));
                e.add_token(builtin_token("|->"));
                e.add_token(ident_token("Head"));
                e.add_token(builtin_token("("));
                e.add_token(added_token("stack"));
                e.add_token(builtin_token(")"));
                e.add_token(builtin_token("."));
                e.add_token(ident_token("pc"));
                for decl in pe_to.decls.to_vec().into_iter().chain(pe_to.params.to_vec()) {
                    e.add_token(builtin_token(","));
                    e.add_line();
                    e.add_token(ident_token(&decl.name()));
                    e.add_token(builtin_token("|->"));
                    e.add_token(ident_token(&decl.name()));
                }
                e.add_token(builtin_token("]"));
                e.add_token(builtin_token(">>"));
                e.add_line();
                e.add_token(builtin_token("\\o"));
                e.add_token(ident_token("Tail"));
                e.add_token(builtin_token("("));
                e.add_token(added_token("stack"));
                e.add_token(builtin_token(")"));
            }
            make_new_stack_top_expr_pretty(&expr);
            expr.borrow_mut().normalize();
            ass.push(self.single(ast, "stack", make_expr(vec![]), expr));
        }
        let params = pe_to.params.to_vec();
        let args = ast.args();
        if params.len() != args.len() {
            return err_at(format!("Procedure {} called with wrong number of arguments", ast.to()), ast);
        }
        for (i, decl) in params.iter().enumerate() {
            ass.push(self.single(ast, &decl.name(), make_expr(vec![]), args.get(i)));
        }
        let a = self.assign(ast, ass);
        a.has_origin.set(!params.is_empty());
        result.push(a);
        self.init_decls(ast, &pe_to.decls, &result);
        result.push(update_pc(pe_to.i_pc.as_deref().unwrap_or("null")));
        Ok(result)
    }
}
