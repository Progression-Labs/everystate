//! The PlusCal parser (port of pcal.ParseAlgorithm): reads an algorithm in p-syntax or c-syntax
//! into an AST, expands macros, adds missing labels and groups statements into labeled steps.
use super::ast::*;
use super::expr::{clone_and_normalize, Expr, IDENT};
use super::tokenize::CharReader;
use super::{err, err_at, version_to_number, Ctx, PErr, PR};

fn msg<T>(r: Result<T, String>) -> PR<T> {
    r.map_err(PErr::Msg)
}
fn is_in(elt: &str, set: &[String]) -> bool {
    set.iter().any(|s| s == elt)
}
fn has_empty_intersection(s: &[String], t: &[String]) -> bool {
    !t.iter().any(|x| is_in(x, s))
}
fn union(s: &[String], t: &[String]) -> Vec<String> {
    let mut r = s.to_vec();
    for x in t {
        if !is_in(x, &r) {
            r.push(x.clone());
        }
    }
    r
}
fn expr_is_empty(e: &Expr) -> bool {
    e.borrow().tokens.is_empty()
}

impl Ctx {
    fn rd(&mut self) -> &mut CharReader {
        self.reader.as_mut().expect("the parser has no input")
    }
    fn parsing_error<T>(&self, m: &str) -> PR<T> {
        err(format!("{}\n    line {}, column {}", m, self.last_tok_line, self.last_tok_col))
    }

    // ---- token stream ----
    fn next_token_from_reader(&mut self) -> PR<String> {
        let mut r = self.reader.take().expect("the parser has no input");
        let t = self.tokenizer.get_algorithm_token(&mut r);
        self.reader = Some(r);
        msg(t)
    }
    pub(crate) fn get_alg_token(&mut self) -> PR<String> {
        if self.lat.is_empty() {
            self.rd().peek();
            self.last_tok_col = self.rd().column_number() + 1;
            self.last_tok_line = self.rd().line_number() + 1;
            let t = self.next_token_from_reader()?;
            self.last_tok_string = t.clone();
            return Ok(t);
        }
        self.last_tok_col = self.cur_tok_col[0] + 1;
        self.last_tok_line = self.cur_tok_line[0] + 1;
        let result = self.lat.remove(0);
        for i in 1..=self.lat.len() {
            self.cur_tok_col[i - 1] = self.cur_tok_col[i];
            self.cur_tok_line[i - 1] = self.cur_tok_line[i];
        }
        self.last_tok_string = result.clone();
        Ok(result)
    }
    fn peek_at_alg_token(&mut self, n: usize) -> PR<String> {
        while self.lat.len() < n {
            let k = self.lat.len();
            if self.rd().peek() == "\t" {
                return err(format!("Premature end of file, perhaps because of unclosed comment, near\n    line {}, column {}", self.cur_tok_line[k] + 1, self.cur_tok_col[k] + 1));
            }
            self.cur_tok_col[k] = self.rd().column_number();
            self.cur_tok_line[k] = self.rd().line_number();
            let t = self.next_token_from_reader()?;
            self.lat.push(t);
        }
        Ok(self.lat[n - 1].clone())
    }
    fn peek_is(&mut self, s: &str) -> PR<bool> {
        Ok(self.peek_at_alg_token(1)? == s)
    }
    fn peek_past_alg_token(&mut self, n: usize) -> PR<String> {
        if n < self.lat.len() {
            return Err(PErr::Bug("ParseAlgorithm.PeekPastAlgToken called to peek after a token\n    it has already peeked at".into()));
        }
        while n > self.lat.len() {
            let t = self.next_token_from_reader()?;
            self.lat.push(t);
        }
        Ok(self.rd().peek())
    }
    fn gobble_this(&mut self, s: &str) -> PR<()> {
        self.gobble_this_or(s, "")
    }
    fn gobble_this_or(&mut self, s: &str, alternate: &str) -> PR<()> {
        if s == ";" {
            let nxt = self.peek_at_alg_token(1)?;
            if matches!(nxt.as_str(), "end" | "begin" | "else" | "elsif" | "or" | "do" | "macro" | "procedure" | "process" | "fair" | "define" | "}" | "{") {
                return Ok(());
            }
            if matches!(nxt.as_str(), "if" | "either" | "while" | "with" | "call" | "return" | "goto" | "print" | "assert" | "skip") {
                return err(format!("Missing `;' before line {}, column {}", self.cur_tok_line[0] + 1, self.cur_tok_col[0] + 1));
            }
        }
        let t = self.get_alg_token()?;
        if t != s && !(!alternate.is_empty() && t == alternate) {
            return self.parsing_error(&format!("Expected \"{}\" but found \"{}\"", s, t));
        }
        Ok(())
    }
    fn must_gobble_this(&mut self, s: &str) -> PR<()> {
        let t = self.get_alg_token()?;
        if t != s {
            return self.parsing_error(&format!("Expected \"{}\" but found \"{}\"", s, t));
        }
        Ok(())
    }
    fn gobble_equal_or_if(&mut self) -> PR<bool> {
        let t = self.get_alg_token()?;
        if t == "=" {
            return Ok(true);
        }
        if t == "\\in" || t == "\u{2208}" {
            return Ok(false);
        }
        self.parsing_error(&format!("Expected \"=\" or \"\\in\"  but found \"{}\"", t))
    }
    fn gobble_comma_or_semicolon(&mut self) -> PR<()> {
        if self.peek_is(",")? { self.gobble_this(",") } else { self.gobble_this(";") }
    }
    fn gobble_begin_or_left_brace(&mut self) -> PR<()> {
        if self.p_syntax {
            self.gobble_this("begin")
        } else if self.c_syntax {
            self.gobble_this("{")
        } else {
            Err(PErr::Bug("Syntax not initialized.".into()))
        }
    }
    fn gobble_end_or_right_brace(&mut self, s: &str) -> PR<()> {
        if self.p_syntax {
            self.gobble_this("end")?;
            self.gobble_this(s)
        } else if self.c_syntax {
            self.gobble_this("}")
        } else {
            Err(PErr::Bug("Bad call of GobbleEndRightBrace".into()))
        }
    }

    // ---- expressions ----
    fn get_expr(&mut self) -> PR<Expr> {
        self.get_expr_internal(false)
    }
    fn get_expr_internal(&mut self, define_block: bool) -> PR<Expr> {
        if !self.lat.is_empty() {
            return Err(PErr::Bug("ParseAlgorithm: GetExpr called after lookahead".into()));
        }
        let mut r = self.reader.take().expect("the parser has no input");
        let res = if define_block { self.tokenizer.tokenize_define_block(&mut r) } else { self.tokenizer.tokenize_expr(&mut r) };
        self.reader = Some(r);
        let result = msg(res)?;
        self.lat.push(self.tokenizer.delimiter.clone());
        self.cur_tok_col[0] = self.tokenizer.delimiter_col;
        self.cur_tok_line[0] = self.tokenizer.delimiter_line;
        let nonempty = !result.borrow().tokens.is_empty();
        result.borrow_mut().has_origin = nonempty;
        Ok(result)
    }
    fn positioned(&self, k: K) -> Ast {
        let n = new_node(k);
        n.col.set(self.last_tok_col);
        n.line.set(self.last_tok_line);
        n.has_origin.set(true);
        n
    }

    // ---- the algorithm ----
    pub fn get_algorithm(&mut self, reader: CharReader, fair_algorithm: bool) -> PR<Ast> {
        match self.get_algorithm_inner(reader, fair_algorithm) {
            Err(PErr::Runtime) => self.parsing_error("Unknown error at or before"),
            r => r,
        }
    }

    fn init(&mut self, reader: CharReader) {
        self.added_labels = vec![];
        self.added_labels_locs = vec![];
        self.next_label_num = 1;
        self.reader = Some(reader);
        self.all_labels.clear();
        self.has_label = false;
        self.has_default_initialization = false;
        self.current_procedure = None;
        self.procedures = V::new();
        self.p_syntax = false;
        self.c_syntax = false;
        self.plus_labels = V::new();
        self.minus_labels = V::new();
        self.procedures_called = V::new();
        self.goto_used = false;
        self.goto_done_used = false;
        self.omit_pc = true;
        self.omit_stuttering_when_done = true;
        if self.input_version_number < version_to_number("1.5") {
            self.omit_pc = false;
            self.omit_stuttering_when_done = false;
        }
        self.lat.clear();
    }

    fn get_algorithm_inner(&mut self, reader: CharReader, fair_algorithm: bool) -> PR<Ast> {
        self.init(reader);
        if fair_algorithm {
            let next = self.get_alg_token()?;
            if next != "algorithm" {
                return self.parsing_error("`--fair' not followed by `algorithm'");
            }
            self.fair_algorithm = true;
        }
        let name = self.get_alg_token()?;
        if self.peek_is("{")? {
            self.c_syntax = true;
            self.must_gobble_this("{")?;
        } else {
            self.p_syntax = true;
        }
        let mut vdecls = V::new();
        if self.peek_is("variable")? || self.peek_is("variables")? {
            vdecls = self.get_var_decls()?;
        }
        let mut defs = super::expr::new_expr();
        if self.peek_is("define")? {
            self.must_gobble_this("define")?;
            if self.c_syntax {
                self.gobble_this("{")?;
            }
            defs = self.get_expr_internal(true)?;
            if self.p_syntax {
                self.gobble_this("end")?;
                self.gobble_this("define")?;
            } else {
                self.gobble_this("}")?;
            }
            self.gobble_this(";")?;
        }
        let macros: V<Ast> = V::new();
        while self.peek_is("macro")? {
            let m = self.get_macro(&macros)?;
            macros.push(m);
        }
        while self.peek_is("procedure")? {
            let p = self.get_procedure()?;
            self.procedures.push(p);
            self.omit_pc = false;
        }
        let is_multi = (self.peek_is("fair")? && (self.peek_at_alg_token(2)? == "process" || (self.peek_at_alg_token(2)? == "+" && self.peek_at_alg_token(3)? == "process"))) || self.peek_is("process")?;
        if is_multi {
            let multiproc = new_node(K::Multiprocess);
            multiproc.set_name(&name);
            multiproc.set_decls(vdecls);
            multiproc.set_defs(defs);
            multiproc.set_macros(macros.clone());
            multiproc.set_prcds(self.procedures.clone());
            multiproc.set_procs(V::new());
            while self.peek_is("fair")? || self.peek_is("process")? {
                let mut fairness = UNFAIR_PROC;
                if self.peek_is("fair")? {
                    self.must_gobble_this("fair")?;
                    if self.peek_is("+")? {
                        self.must_gobble_this("+")?;
                        fairness = SF_PROC;
                    } else {
                        fairness = WF_PROC;
                    }
                } else if self.fairness_option == "wf" {
                    fairness = WF_PROC;
                } else if self.fairness_option == "sf" {
                    fairness = SF_PROC;
                }
                let proc = self.get_process()?;
                proc.fairness.set(fairness);
                multiproc.procs().push(proc);
            }
            if self.p_syntax {
                self.gobble_this("end")?;
                self.gobble_this("algorithm")?;
            } else {
                self.gobble_this("}")?;
            }
            check_for_duplicate_macros(&macros)?;
            let mut omit_stuttering_value = false;
            let procs = multiproc.procs();
            for i in 0..procs.len() {
                let proc = procs.get(i);
                self.expand_macros_in_stmt_seq(&proc.body(), &macros)?;
                self.add_labels_to_stmt_seq(&proc.body())?;
                let b = self.make_labeled_stmt_seq(&proc.body())?;
                proc.set_body(b);
                self.omit_stuttering_when_done = true;
                self.check_body(&proc.body());
                omit_stuttering_value = omit_stuttering_value || self.omit_stuttering_when_done;
            }
            self.omit_stuttering_when_done = omit_stuttering_value;
            let prcds = multiproc.prcds();
            for i in 0..prcds.len() {
                let prcd = prcds.get(i);
                self.current_procedure = Some(prcd.name());
                self.expand_macros_in_stmt_seq(&prcd.body(), &macros)?;
                self.add_labels_to_stmt_seq(&prcd.body())?;
                let b = self.make_labeled_stmt_seq(&prcd.body())?;
                prcd.set_body(b);
            }
            if !self.added_labels.is_empty() {
                if !self.label_flag {
                    return self.added_messages_error();
                }
                self.report_added_labels();
            }
            if self.goto_done_used {
                self.omit_pc = false;
                self.omit_stuttering_when_done = false;
            }
            if self.goto_used {
                self.omit_pc = false;
            }
            multiproc.has_origin.set(true);
            Ok(multiproc)
        } else {
            let uniproc = new_node(K::Uniprocess);
            uniproc.set_name(&name);
            uniproc.set_decls(vdecls);
            uniproc.set_defs(defs);
            uniproc.set_macros(macros.clone());
            uniproc.set_prcds(self.procedures.clone());
            if self.input_version_number == version_to_number("1.5") && self.peek_is("fair")? {
                self.gobble_this("fair")?;
                if self.peek_is("+")? {
                    self.gobble_this("+")?;
                }
                self.fairness_option = "wf".to_string();
            }
            if fair_algorithm {
                if !self.fairness_option.is_empty() && self.fairness_option != "wf" && self.fairness_option != "wfNext" {
                    let w = format!("Option `{}' specified for --fair algorithm.", self.fairness_option);
                    self.report_warning(&w);
                }
                self.fairness_option = "wf".to_string();
            }
            self.gobble_begin_or_left_brace()?;
            let body = self.get_stmt_seq()?;
            uniproc.set_body(body);
            check_for_duplicate_macros(&macros)?;
            self.expand_macros_in_stmt_seq(&uniproc.body(), &macros)?;
            let prcds = uniproc.prcds();
            for i in 0..prcds.len() {
                let prcd = prcds.get(i);
                self.current_procedure = Some(prcd.name());
                self.expand_macros_in_stmt_seq(&prcd.body(), &macros)?;
                self.add_labels_to_stmt_seq(&prcd.body())?;
                let b = self.make_labeled_stmt_seq(&prcd.body())?;
                prcd.set_body(b);
            }
            if self.c_syntax {
                self.gobble_this("}")?;
                self.gobble_this("}")?;
            } else {
                self.gobble_this("end")?;
                self.gobble_this("algorithm")?;
            }
            self.add_labels_to_stmt_seq(&uniproc.body())?;
            let b = self.make_labeled_stmt_seq(&uniproc.body())?;
            uniproc.set_body(b);
            if !self.added_labels.is_empty() {
                if self.has_label && !self.label_flag {
                    return self.added_messages_error();
                }
                self.report_added_labels();
            }
            if self.goto_used {
                self.omit_pc = false;
            }
            if self.goto_done_used {
                self.omit_pc = false;
                self.omit_stuttering_when_done = false;
            } else {
                self.check_body(&uniproc.body());
            }
            uniproc.has_origin.set(true);
            Ok(uniproc)
        }
    }

    fn report_added_labels(&mut self) {
        if self.report_labels_flag {
            self.report_info(if self.added_labels.len() > 1 { "The following labels were added:" } else { "The following label was added:" });
            for i in 0..self.added_labels.len() {
                let l = format!("  {} at {}", self.added_labels[i], self.added_labels_locs[i]);
                self.report_info(&l);
            }
        } else {
            self.report_info("Labels added.");
        }
    }

    fn no_pc(&mut self) {
        self.omit_pc = false;
        self.omit_stuttering_when_done = false;
    }
    fn check_body(&mut self, body: &V<Ast>) {
        if body.is_empty() {
            return;
        }
        if body.len() > 1 || body.get(0).k != K::LabeledStmt {
            return self.no_pc();
        }
        let stmts = body.get(0).stmts();
        if stmts.is_empty() {
            return;
        }
        if stmts.len() > 1 || stmts.get(0).k != K::While {
            return self.no_pc();
        }
        let w = stmts.get(0);
        {
            let test = w.e();
            let t = test.borrow();
            if t.tokens.len() != 1 || t.tokens[0].len() != 1 || t.tokens[0][0].borrow().string != "TRUE" {
                drop(t);
                return self.no_pc();
            }
        }
        if w.lab_do_opt().map(|v| !v.is_empty()).unwrap_or(false) {
            self.omit_pc = false;
        }
        if let Some(u) = w.unlab_do_opt() {
            for s in u.to_vec() {
                if matches!(s.k, K::LabelIf | K::LabelEither | K::LabeledStmt) {
                    self.omit_pc = false;
                    return;
                }
            }
        }
    }

    fn added_messages_error<T>(&self) -> PR<T> {
        let mut m = if self.added_labels.len() > 1 { "Missing labels at the following locations:" } else { "Missing label at the following location:" }.to_string();
        for l in &self.added_labels_locs {
            m += "\n     ";
            m += l;
        }
        err(m)
    }

    fn get_procedure(&mut self) -> PR<Ast> {
        self.gobble_this("procedure")?;
        let result = self.positioned(K::Procedure);
        let name = self.get_alg_token()?;
        result.set_name(&name);
        self.current_procedure = Some(name);
        self.plus_labels = V::new();
        self.minus_labels = V::new();
        self.procedures_called = V::new();
        self.gobble_this("(")?;
        let params = V::new();
        result.set_params(params.clone());
        let mut look_for_comma = false;
        while !self.peek_is(")")? {
            if look_for_comma {
                self.gobble_this(",")?;
            }
            params.push(self.get_pvar_decl()?);
            look_for_comma = true;
        }
        self.must_gobble_this(")")?;
        if self.peek_is("begin")? || self.peek_is("{")? {
            result.set_decls(V::new());
        } else {
            let d = self.get_pvar_decls()?;
            result.set_decls(d);
        }
        self.gobble_begin_or_left_brace()?;
        let body = self.get_stmt_seq()?;
        result.set_body(body);
        self.gobble_end_or_right_brace("procedure")?;
        if self.peek_is(";")? {
            self.get_alg_token()?;
        }
        self.current_procedure = None;
        result.set_plus_labels(self.plus_labels.clone());
        result.set_minus_labels(self.minus_labels.clone());
        result.set_procedures_called(self.procedures_called.clone());
        Ok(result)
    }

    fn get_process(&mut self) -> PR<Ast> {
        self.gobble_this("process")?;
        let result = self.positioned(K::Process);
        if self.c_syntax {
            self.gobble_this("(")?;
        }
        let name = self.get_alg_token()?;
        result.set_name(&name);
        result.is_eq.set(self.gobble_equal_or_if()?);
        let id = self.get_expr()?;
        result.set_e(id.clone());
        self.plus_labels = V::new();
        self.minus_labels = V::new();
        self.procedures_called = V::new();
        if self.c_syntax {
            self.gobble_this(")")?;
        }
        if expr_is_empty(&id) {
            return self.parsing_error("Empty process id at ");
        }
        if self.peek_is("begin")? || self.peek_is("{")? {
            result.set_decls(V::new());
        } else {
            let d = self.get_var_decls()?;
            result.set_decls(d);
        }
        self.gobble_begin_or_left_brace()?;
        let body = self.get_stmt_seq()?;
        result.set_body(body);
        self.gobble_end_or_right_brace("process")?;
        if self.peek_is(";")? {
            self.get_alg_token()?;
        }
        result.set_plus_labels(self.plus_labels.clone());
        result.set_minus_labels(self.minus_labels.clone());
        result.set_procedures_called(self.procedures_called.clone());
        Ok(result)
    }

    fn gobble_variables(&mut self) -> PR<()> {
        if self.peek_is("variables")? { self.must_gobble_this("variables") } else { self.gobble_this("variable") }
    }
    fn get_pvar_decls(&mut self) -> PR<V<Ast>> {
        self.gobble_variables()?;
        let result = V::new();
        while !(self.peek_is("begin")? || self.peek_is("{")?) {
            result.push(self.get_pvar_decl()?);
            self.gobble_comma_or_semicolon()?;
        }
        Ok(result)
    }
    fn get_pvar_decl(&mut self) -> PR<Ast> {
        let name = self.get_alg_token()?;
        let pv = self.positioned(K::PVarDecl);
        pv.set_name(&name);
        if self.peek_is("=")? {
            self.gobble_this("=")?;
            let val = self.get_expr()?;
            pv.set_e(val.clone());
            if !val.borrow().has_origin {
                return Err(PErr::Runtime);
            }
        } else {
            self.has_default_initialization = true;
        }
        Ok(pv)
    }
    fn get_var_decls(&mut self) -> PR<V<Ast>> {
        self.gobble_variables()?;
        let result = V::new();
        loop {
            let t = self.peek_at_alg_token(1)?;
            if matches!(t.as_str(), "begin" | "{" | "procedure" | "process" | "fair" | "define" | "macro") {
                break;
            }
            result.push(self.get_var_decl()?);
        }
        Ok(result)
    }
    fn get_var_decl(&mut self) -> PR<Ast> {
        let name = self.get_alg_token()?;
        let pv = self.positioned(K::VarDecl);
        pv.set_name(&name);
        let t = self.peek_at_alg_token(1)?;
        if t == "=" || t == "\\in" || t == "\u{2208}" {
            pv.is_eq.set(self.gobble_equal_or_if()?);
            let val = self.get_expr()?;
            pv.set_e(val.clone());
            if !val.borrow().has_origin {
                return Err(PErr::Runtime);
            }
        } else {
            self.has_default_initialization = true;
        }
        self.gobble_comma_or_semicolon()?;
        Ok(pv)
    }

    fn get_while(&mut self) -> PR<Ast> {
        self.must_gobble_this("while")?;
        let result = self.positioned(K::While);
        if self.c_syntax {
            self.gobble_this("(")?;
        }
        let test = self.get_expr()?;
        result.set_e(test.clone());
        if self.c_syntax {
            self.gobble_this(")")?;
        }
        if expr_is_empty(&test) {
            return self.parsing_error("Empty while test at ");
        }
        if self.p_syntax {
            self.gobble_this("do")?;
            let d = self.get_stmt_seq()?;
            result.set_unlab_do(d);
            self.gobble_this("end")?;
            self.gobble_this("while")?;
            self.gobble_this(";")?;
        } else {
            let d = self.get_c_stmt()?;
            result.set_unlab_do(d);
        }
        if result.unlab_do().is_empty() {
            return self.parsing_error("Missing body of while statement at");
        }
        result.set_lab_do(V::new());
        Ok(result)
    }

    fn is_label_next(&mut self) -> PR<bool> {
        let t = self.peek_at_alg_token(1)?;
        if matches!(t.as_str(), "while" | "if" | "assert" | "print" | "else" | "elsif" | "either" | "or" | "end" | "with" | "when" | "await" | "skip" | "call" | "return" | "goto") {
            return Ok(false);
        }
        let p: Vec<char> = self.rd().peek().chars().collect();
        if p.is_empty() || p[0] != ':' || (p.len() > 1 && p[1] == '=') {
            return Ok(false);
        }
        Ok(true)
    }
    fn get_label(&mut self) -> PR<String> {
        let mut next_label = String::new();
        if self.is_label_next()? {
            next_label = self.get_alg_token()?;
            if self.in_get_macro {
                return self.parsing_error("A label may not appear in a macro.");
            }
            if next_label == "Done" {
                return self.parsing_error("Cannot use `Done' as a label.");
            }
            if next_label == "Error" {
                return self.parsing_error("Cannot use `Error' as a label.");
            }
            self.gobble_this(":")?;
            self.has_label = true;
            self.all_labels.insert(next_label.clone());
            if self.peek_is("+")? {
                self.gobble_this("+")?;
                self.plus_labels.push(next_label.clone());
                self.omit_pc = false;
            } else if self.peek_is("-")? {
                self.gobble_this("-")?;
                self.minus_labels.push(next_label.clone());
                self.omit_pc = false;
            }
        }
        Ok(next_label)
    }

    fn get_stmt_seq(&mut self) -> PR<V<Ast>> {
        let result: V<Ast> = V::new();
        let mut t = self.peek_at_alg_token(1)?;
        while !((self.p_syntax && matches!(t.as_str(), "end" | "else" | "elsif" | "or")) || (self.c_syntax && t == "}")) {
            let next_label = self.get_label()?;
            if self.c_syntax && self.peek_is("{")? {
                let seq = self.get_c_stmt_seq(&next_label)?;
                result.add_all(&seq);
            } else {
                let stmt = self.get_stmt()?;
                *stmt.lbl.borrow_mut() = next_label;
                result.push(stmt);
            }
            t = self.peek_at_alg_token(1)?;
        }
        if self.c_syntax && result.is_empty() {
            return self.parsing_error("Empty statement list");
        }
        Ok(result)
    }

    fn get_stmt(&mut self) -> PR<Ast> {
        let next = self.peek_at_alg_token(1)?;
        match next.as_str() {
            "if" => return self.get_if(0),
            "either" => return self.get_either(),
            "with" => return self.get_with(0),
            "when" => return self.get_when(true),
            "await" => return self.get_when(false),
            "print" => return self.get_print_s(),
            "assert" => return self.get_assert(),
            "skip" => return self.get_skip(),
            "call" => return self.get_call_or_call_return_or_call_goto(),
            "return" => return self.get_return(),
            "goto" => return self.get_goto(),
            "while" => return self.get_while(),
            _ => {}
        }
        if self.peek_past_alg_token(1)?.starts_with('(') {
            return self.get_macro_call();
        }
        self.get_assign()
    }

    fn get_c_stmt_seq(&mut self, lbl: &str) -> PR<V<Ast>> {
        self.must_gobble_this("{")?;
        let sseq = self.get_stmt_seq()?;
        self.gobble_this("}")?;
        self.gobble_this(";")?;
        if !lbl.is_empty() {
            let first = sseq.try_get(0).ok_or(PErr::Runtime)?;
            if !first.lbl().is_empty() {
                return err_at("Duplicate labeling of statement", &first);
            }
            *first.lbl.borrow_mut() = lbl.to_string();
        }
        Ok(sseq)
    }
    fn get_c_stmt(&mut self) -> PR<V<Ast>> {
        let label = self.get_label()?;
        if self.peek_is("{")? {
            return self.get_c_stmt_seq(&label);
        }
        let stmt = self.get_stmt()?;
        *stmt.lbl.borrow_mut() = label;
        Ok(V::of(vec![stmt]))
    }

    fn get_if(&mut self, depth: i32) -> PR<Ast> {
        self.must_gobble_this(if depth == 0 { "if" } else { "elsif" })?;
        let result = self.positioned(K::LabelIf);
        if self.c_syntax {
            self.gobble_this("(")?;
        }
        let test = self.get_expr()?;
        result.set_e(test.clone());
        if self.c_syntax {
            self.gobble_this(")")?;
        }
        if expr_is_empty(&test) {
            return self.parsing_error("Empty if test at ");
        }
        if self.p_syntax {
            self.gobble_this("then")?;
            let t = self.get_stmt_seq()?;
            result.set_unlab_then(t);
        } else {
            let t = self.get_c_stmt()?;
            result.set_unlab_then(t);
        }
        let next = self.peek_at_alg_token(1)?;
        if self.p_syntax {
            if next == "else" {
                self.must_gobble_this("else")?;
                let e = self.get_stmt_seq()?;
                result.set_unlab_else(e);
            } else if next == "elsif" {
                let inner = self.get_if(depth + 1)?;
                result.set_unlab_else(V::of(vec![inner]));
            } else if next == "end" {
                result.set_unlab_else(V::new());
            } else {
                return self.parsing_error("Expecting \"else\", \"elsif\", or \"end\"");
            }
            if depth == 0 {
                self.gobble_this("end")?;
                self.gobble_this("if")?;
                self.gobble_this(";")?;
            }
        } else if next == "else" {
            self.must_gobble_this("else")?;
            let e = self.get_c_stmt()?;
            result.set_unlab_else(e);
        } else {
            result.set_unlab_else(V::new());
        }
        result.set_lab_then(V::new());
        result.set_lab_else(V::new());
        if result.unlab_else().is_empty() && result.unlab_then().is_empty() {
            return Err(PErr::Runtime);
        }
        Ok(result)
    }

    fn get_either(&mut self) -> PR<Ast> {
        self.must_gobble_this("either")?;
        let result = self.positioned(K::LabelEither);
        let clauses = V::new();
        result.set_clauses(clauses.clone());
        let mut has_or = false;
        loop {
            let clause = new_node(K::Clause);
            clause.set_lab_or(V::new());
            let u = if self.p_syntax { self.get_stmt_seq()? } else { self.get_c_stmt()? };
            clause.set_unlab_or(u.clone());
            if u.is_empty() {
                return err_at("`either' statement with empty `or' clause", &result);
            }
            clause.has_origin.set(true);
            clauses.push(clause);
            if self.peek_is("or")? {
                self.must_gobble_this("or")?;
                has_or = true;
            } else {
                break;
            }
        }
        if self.p_syntax {
            self.must_gobble_this("end")?;
            self.gobble_this("either")?;
            self.gobble_this(";")?;
        }
        if !has_or {
            return err_at("`either' statement has no `or'", &result);
        }
        Ok(result)
    }

    fn get_with(&mut self, depth: i32) -> PR<Ast> {
        if depth == 0 {
            self.gobble_this("with")?;
            if self.c_syntax {
                self.gobble_this("(")?;
            }
        }
        let result = self.positioned(K::With);
        let var = self.get_alg_token()?;
        result.set_name(&var);
        result.is_eq.set(self.gobble_equal_or_if()?);
        let exp = self.get_expr()?;
        result.set_e(exp.clone());
        if self.p_syntax || !self.peek_is(")")? {
            self.gobble_comma_or_semicolon()?;
        }
        if expr_is_empty(&exp) {
            return self.parsing_error("Empty with expression at ");
        }
        if self.p_syntax && self.peek_is("do")? {
            self.gobble_this("do")?;
            let d = self.get_stmt_seq()?;
            result.set_do(d);
            self.gobble_this("end")?;
            self.gobble_this("with")?;
            self.gobble_this(";")?;
        } else if self.c_syntax && self.peek_is(")")? {
            self.must_gobble_this(")")?;
            let d = self.get_c_stmt()?;
            result.set_do(d);
        } else {
            let inner = self.get_with(depth + 1)?;
            result.set_do(V::of(vec![inner]));
        }
        if result.do_().is_empty() {
            return err_at("Missing body of with statement", &result);
        }
        Ok(result)
    }

    fn get_assign(&mut self) -> PR<Ast> {
        let result = new_node(K::Assign);
        result.col.set(self.cur_tok_col[0] + 1);
        result.line.set(self.cur_tok_line[0] + 1);
        result.has_origin.set(true);
        let ass = V::new();
        result.set_ass(ass.clone());
        ass.push(self.get_single_assign()?);
        while self.peek_is("||")? || self.peek_is("\u{2016}")? {
            self.get_alg_token()?;
            match self.get_single_assign() {
                Ok(a) => ass.push(a),
                Err(PErr::Msg(_)) => return self.parsing_error("Bad assignment statement at "),
                Err(e) => return Err(e),
            }
        }
        self.gobble_this(";")?;
        Ok(result)
    }
    fn get_single_assign(&mut self) -> PR<Ast> {
        let result = new_node(K::SingleAssign);
        result.col.set(self.cur_tok_col[0] + 1);
        result.line.set(self.cur_tok_line[0] + 1);
        result.has_origin.set(true);
        let lhs = self.get_lhs()?;
        result.set_lhs(lhs);
        self.gobble_this_or(":=", "\u{2254}")?;
        let rhs = self.get_expr()?;
        result.set_e(rhs.clone());
        if expr_is_empty(&rhs) {
            return self.parsing_error("Empty right-hand side of assignment at ");
        }
        Ok(result)
    }
    fn get_lhs(&mut self) -> PR<Ast> {
        let result = new_node(K::Lhs);
        result.col.set(self.cur_tok_col[0] + 1);
        result.line.set(self.cur_tok_line[0] + 1);
        result.has_origin.set(true);
        let var = self.get_alg_token()?;
        result.set_name(&var);
        let sub = self.get_expr()?;
        result.set_e(sub);
        Ok(result)
    }

    fn get_print_s(&mut self) -> PR<Ast> {
        self.must_gobble_this("print")?;
        let result = self.positioned(K::PrintS);
        let exp = self.get_expr()?;
        result.set_e(exp.clone());
        if expr_is_empty(&exp) {
            return self.parsing_error("Empty expression in print statement at ");
        }
        self.gobble_this(";")?;
        Ok(result)
    }
    fn get_assert(&mut self) -> PR<Ast> {
        self.must_gobble_this("assert")?;
        let result = self.positioned(K::Assert);
        let exp = self.get_expr()?;
        result.set_e(exp.clone());
        if expr_is_empty(&exp) {
            return self.parsing_error("Empty expression in assert statement at ");
        }
        self.gobble_this(";")?;
        Ok(result)
    }
    fn get_skip(&mut self) -> PR<Ast> {
        self.must_gobble_this("skip")?;
        let result = self.positioned(K::Skip);
        self.gobble_this(";")?;
        Ok(result)
    }
    fn get_when(&mut self, is_when: bool) -> PR<Ast> {
        self.must_gobble_this(if is_when { "when" } else { "await" })?;
        let result = self.positioned(K::When);
        let exp = self.get_expr()?;
        result.set_e(exp.clone());
        if !exp.borrow().has_origin {
            return Err(PErr::Runtime);
        }
        self.gobble_this(";")?;
        Ok(result)
    }

    fn get_args(&mut self) -> PR<V<Expr>> {
        let args: V<Expr> = V::new();
        let mut more = !self.peek_past_alg_token(0)?.starts_with(')');
        while more {
            let a = self.get_expr()?;
            args.push(a.clone());
            if expr_is_empty(&a) {
                return self.parsing_error("Empty argument in call statement at ");
            }
            if !self.peek_is(")")? {
                self.gobble_this(",")?;
            } else {
                more = false;
            }
        }
        Ok(args)
    }
    fn get_call(&mut self) -> PR<Ast> {
        self.must_gobble_this("call")?;
        let result = self.positioned(K::Call);
        *result.to.borrow_mut() = self.get_alg_token()?;
        self.gobble_this("(")?;
        let args = self.get_args()?;
        result.set_args(args);
        self.gobble_this(")")?;
        self.gobble_this(";")?;
        let to = result.to();
        if !self.procedures_called.to_vec().contains(&to) {
            self.procedures_called.push(to);
        }
        Ok(result)
    }
    fn get_return(&mut self) -> PR<Ast> {
        self.must_gobble_this("return")?;
        let result = self.positioned(K::Return);
        *result.from.borrow_mut() = self.current_procedure.clone();
        self.gobble_this(";")?;
        Ok(result)
    }
    fn get_call_or_call_return_or_call_goto(&mut self) -> PR<Ast> {
        let call = self.get_call()?;
        if self.peek_is("return")? {
            self.must_gobble_this("return")?;
            self.gobble_this(";")?;
            let result = new_node(K::CallReturn);
            result.col.set(call.col.get());
            result.line.set(call.line.get());
            *result.to.borrow_mut() = call.to();
            *result.from.borrow_mut() = self.current_procedure.clone();
            result.set_args(call.args());
            result.has_origin.set(true);
            Ok(result)
        } else if self.peek_is("goto")? {
            self.must_gobble_this("goto")?;
            let result = new_node(K::CallGoto);
            result.col.set(call.col.get());
            result.line.set(call.line.get());
            *result.to.borrow_mut() = call.to();
            *result.after.borrow_mut() = self.get_alg_token()?;
            result.set_args(call.args());
            result.has_origin.set(true);
            self.goto_used = true;
            if result.to() == "Done" || result.to() == "\"Done\"" {
                self.goto_done_used = true;
            }
            self.gobble_this(";")?;
            Ok(result)
        } else {
            Ok(call)
        }
    }
    fn get_goto(&mut self) -> PR<Ast> {
        self.must_gobble_this("goto")?;
        let result = self.positioned(K::Goto);
        *result.to.borrow_mut() = self.get_alg_token()?;
        self.goto_used = true;
        if result.to() == "Done" || result.to() == "\"Done\"" {
            self.goto_done_used = true;
        }
        self.gobble_this(";")?;
        Ok(result)
    }

    fn get_macro(&mut self, macros: &V<Ast>) -> PR<Ast> {
        self.in_get_macro = true;
        self.must_gobble_this("macro")?;
        let result = self.positioned(K::Macro);
        let name = self.get_alg_token()?;
        result.set_name(&name);
        self.gobble_this("(")?;
        let params: V<String> = V::new();
        result.set_sparams(params.clone());
        let mut look_for_comma = false;
        while !self.peek_is(")")? {
            if look_for_comma {
                self.gobble_this(",")?;
            }
            params.push(self.get_alg_token()?);
            look_for_comma = true;
        }
        self.must_gobble_this(")")?;
        self.gobble_begin_or_left_brace()?;
        let body = self.get_stmt_seq()?;
        result.set_body(body.clone());
        self.gobble_end_or_right_brace("macro")?;
        if self.peek_is(";")? {
            self.get_alg_token()?;
        }
        self.expand_macros_in_stmt_seq(&body, macros)?;
        self.in_get_macro = false;
        Ok(result)
    }
    fn get_macro_call(&mut self) -> PR<Ast> {
        let name = self.get_alg_token()?;
        let result = self.positioned(K::MacroCall);
        result.set_name(&name);
        self.must_gobble_this("(")?;
        let args = self.get_args()?;
        result.set_args(args);
        self.gobble_this(")")?;
        self.gobble_this(";")?;
        Ok(result)
    }

    // ---- adding labels ----
    fn add_labels_to_stmt_seq(&mut self, stmtseq: &V<Ast>) -> PR<()> {
        let mut out = vec![];
        self.inner_add_labels(stmtseq, true, false, &[], &mut out)?;
        Ok(())
    }

    fn inner_add_labels(&mut self, stmtseq: &V<Ast>, first_labeled: bool, in_with: bool, in_assigned: &[String], out_assigned: &mut Vec<String>) -> PR<bool> {
        *out_assigned = in_assigned.to_vec();
        let mut next_step_needs_label = first_labeled;
        let mut had_or_added_label = false;
        let mut i = 0;
        while i < stmtseq.len() {
            let stmt = stmtseq.get(i);
            if !stmt.lbl().is_empty() {
                had_or_added_label = true;
                out_assigned.clear();
                if in_with {
                    return err_at("Label in `with' statement", &stmt);
                }
            }
            if next_step_needs_label {
                if in_with {
                    return err_at("Statement follows `call' or `return' inside a `with' statement.", &stmt);
                }
                self.needs_label(&stmt);
                next_step_needs_label = false;
                had_or_added_label = true;
                out_assigned.clear();
            }
            match stmt.k {
                K::LabelIf => {
                    let (mut then_assigned, mut else_assigned) = (vec![], vec![]);
                    let cur = out_assigned.clone();
                    next_step_needs_label = self.inner_add_labels(&stmt.unlab_then(), false, in_with, &cur, &mut then_assigned)?;
                    next_step_needs_label = self.inner_add_labels(&stmt.unlab_else(), false, in_with, &cur, &mut else_assigned)? || next_step_needs_label;
                    *out_assigned = union(&then_assigned, &else_assigned);
                }
                K::LabelEither => {
                    let mut new_out: Vec<String> = vec![];
                    let cur = out_assigned.clone();
                    for clause in stmt.clauses().to_vec() {
                        let mut or_assigned = vec![];
                        next_step_needs_label = self.inner_add_labels(&clause.unlab_or(), false, in_with, &cur, &mut or_assigned)? || next_step_needs_label;
                        new_out = union(&or_assigned, &new_out);
                    }
                    *out_assigned = new_out;
                }
                K::While => {
                    if in_with {
                        return err_at("`while' inside a `with' statement", &stmt);
                    }
                    self.needs_label(&stmt);
                    had_or_added_label = true;
                    out_assigned.clear();
                    let mut new_out = vec![];
                    self.inner_add_labels(&stmt.unlab_do(), false, false, &[], &mut new_out)?;
                    next_step_needs_label = false;
                }
                K::With => {
                    let new_in: Vec<String> = if in_with { in_assigned.to_vec() } else { vec![] };
                    let mut new_out = vec![];
                    next_step_needs_label = self.inner_add_labels(&stmt.do_(), false, true, &new_in, &mut new_out)?;
                    *out_assigned = new_out;
                    if !in_with && !has_empty_intersection(in_assigned, out_assigned) {
                        self.needs_label(&stmt);
                        had_or_added_label = true;
                        out_assigned.clear();
                    }
                }
                K::Assign => {
                    let mut assigned: Vec<String> = vec![];
                    for a in stmt.ass().to_vec() {
                        let v = a.lhs().name();
                        if !is_in(&v, &assigned) {
                            assigned.push(v);
                        }
                    }
                    if has_empty_intersection(out_assigned, &assigned) {
                        *out_assigned = union(out_assigned, &assigned);
                    } else {
                        if in_with {
                            return err_at("Second assignment to same variable inside a `with' statement", &stmt);
                        }
                        self.needs_label(&stmt);
                        had_or_added_label = true;
                        *out_assigned = assigned;
                    }
                    next_step_needs_label = false;
                }
                _ => {
                    next_step_needs_label = false;
                    let mut assigned: Vec<String> = vec![];
                    let mut is_call_or_return = false;
                    let mut sets_prcd_vbls = false;
                    match stmt.k {
                        K::Call | K::CallGoto => {
                            is_call_or_return = true;
                            if Some(stmt.to()) == self.current_procedure {
                                sets_prcd_vbls = true;
                            }
                        }
                        K::Return | K::CallReturn => {
                            is_call_or_return = true;
                            sets_prcd_vbls = true;
                        }
                        K::Goto => next_step_needs_label = true,
                        _ => {}
                    }
                    if is_call_or_return {
                        next_step_needs_label = true;
                        assigned.push("stack".to_string());
                        if sets_prcd_vbls {
                            for prcd in self.procedures.to_vec() {
                                for d in prcd.params().to_vec() {
                                    assigned.push(d.name());
                                }
                                for d in prcd.decls().to_vec() {
                                    assigned.push(d.name());
                                }
                            }
                        }
                    }
                    if has_empty_intersection(out_assigned, &assigned) {
                        *out_assigned = union(out_assigned, &assigned);
                    } else {
                        if in_with {
                            return err_at("Call or return makes second assignment to a variable inside a `with' statement", &stmt);
                        }
                        self.needs_label(&stmt);
                        had_or_added_label = true;
                        *out_assigned = assigned;
                    }
                }
            }
            i += 1;
        }
        Ok(had_or_added_label || next_step_needs_label)
    }

    fn needs_label(&mut self, stmt: &Ast) {
        if stmt.lbl().is_empty() {
            let mut lbl = format!("{}{}", self.label_root, self.next_label_num);
            self.next_label_num += 1;
            while self.all_labels.contains(&lbl) {
                lbl = format!("{}{}", self.label_root, self.next_label_num);
                self.next_label_num += 1;
            }
            *stmt.lbl.borrow_mut() = lbl.clone();
            self.added_labels.push(lbl);
            self.added_labels_locs.push(stmt.location());
        }
    }

    // ---- grouping into labeled statements ----
    fn make_labeled_stmt_seq(&mut self, stmtseq: &V<Ast>) -> PR<V<Ast>> {
        let result = inner_make_labeled_stmt_seq(stmtseq)?;
        self.check_labeled_stmt_seq(&result)?;
        Ok(result)
    }
    fn check_labeled_stmt_seq(&mut self, stmtseq: &V<Ast>) -> PR<()> {
        for s in stmtseq.to_vec() {
            self.classify_stmt_seq(&s.stmts())?;
        }
        Ok(())
    }
    fn classify_stmt_seq(&mut self, stmtseq: &V<Ast>) -> PR<i32> {
        let mut result = 0;
        let mut i = 0;
        while i < stmtseq.len() {
            let node = stmtseq.get(i);
            match node.k {
                K::LabelIf => {
                    result = self.classify_if(&node)?;
                    if result < 2 {
                        let new_if = new_node(K::If);
                        new_if.set_e(node.e());
                        new_if.set_then(node.unlab_then());
                        new_if.set_els(node.unlab_else());
                        new_if.has_origin.set(node.has_origin.get());
                        stmtseq.set(i, new_if);
                    }
                }
                K::LabelEither => {
                    result = self.classify_either(&node)?;
                    if result < 2 {
                        let new_either = new_node(K::Either);
                        let ors: V<V<Ast>> = V::new();
                        for c in node.clauses().to_vec() {
                            ors.push(c.unlab_or());
                        }
                        new_either.set_ors(ors);
                        new_either.has_origin.set(node.has_origin.get());
                        stmtseq.set(i, new_either);
                    }
                }
                K::With => {
                    result = self.classify_stmt_seq(&node.do_())?;
                    if result == 2 {
                        return err(format!("with statement at {} contains a labeled statement", node.location()));
                    }
                }
                K::While => {
                    if i != 0 {
                        return Err(PErr::Bug("ParseAlgorithm.ClassifyStmtSeq encountered `while' not at beginning of StmtSeq.".into()));
                    }
                    self.classify_stmt_seq(&node.unlab_do())?;
                    self.check_labeled_stmt_seq(&node.lab_do())?;
                }
                K::Call => {
                    if !(i + 1 < stmtseq.len() && stmtseq.get(i + 1).k == K::Return) {
                        result = 1;
                    }
                }
                K::Return | K::CallReturn => {
                    if self.current_procedure.is_none() {
                        return err(format!("return statement not in a procedure at {}", node.location()));
                    }
                    result = 1;
                }
                K::Goto | K::CallGoto => result = 1,
                K::Assign | K::When | K::PrintS | K::Assert | K::Skip | K::MacroCall => {}
                _ => return Err(PErr::Bug(format!("ParseAlgorithm.ClassifyStmtSeq encountered the unexpected statement type {:?}", node.k))),
            }
            if result > 0 {
                if i == stmtseq.len() - 1 {
                    return Ok(result);
                }
                let next = stmtseq.get(i + 1);
                return Err(PErr::Bug(format!("Translator discovered later than it should have  that\n  Statement at {} must have a label", next.location())));
            }
            i += 1;
        }
        Ok(result)
    }
    fn classify_if(&mut self, node: &Ast) -> PR<i32> {
        let then_class = self.classify_stmt_seq(&node.unlab_then())?;
        let mut is_labeled = false;
        if !node.lab_then().is_empty() {
            is_labeled = true;
            self.check_labeled_stmt_seq(&node.lab_then())?;
        }
        let else_class = self.classify_stmt_seq(&node.unlab_else())?;
        if !node.lab_else().is_empty() {
            is_labeled = true;
            self.check_labeled_stmt_seq(&node.lab_else())?;
        }
        if is_labeled || then_class == 2 || else_class == 2 {
            return Ok(2);
        }
        Ok(if then_class + else_class > 0 { 1 } else { 0 })
    }
    fn classify_either(&mut self, node: &Ast) -> PR<i32> {
        let mut the_class = 0;
        for c in node.clauses().to_vec() {
            let unlab = self.classify_stmt_seq(&c.unlab_or())?;
            if unlab > the_class {
                the_class = unlab;
            }
            if !c.lab_or().is_empty() {
                the_class = 2;
                self.check_labeled_stmt_seq(&c.lab_or())?;
            }
        }
        Ok(the_class)
    }

    // ---- macros ----
    fn expand_macros_in_stmt_seq(&mut self, stmtseq: &V<Ast>, macros: &V<Ast>) -> PR<()> {
        let mut i = 0;
        while i < stmtseq.len() {
            let node = stmtseq.get(i);
            match node.k {
                K::LabelIf => {
                    self.expand_macros_in_stmt_seq(&node.unlab_then(), macros)?;
                    self.expand_macros_in_stmt_seq(&node.unlab_else(), macros)?;
                }
                K::LabelEither => {
                    for c in node.clauses().to_vec() {
                        self.expand_macros_in_stmt_seq(&c.unlab_or(), macros)?;
                    }
                }
                K::With => self.expand_macros_in_stmt_seq(&node.do_(), macros)?,
                K::While => self.expand_macros_in_stmt_seq(&node.unlab_do(), macros)?,
                K::MacroCall => {
                    let expansion = expand_macro_call(&node, macros)?;
                    stmtseq.remove(i);
                    let n = expansion.len();
                    for (j, s) in expansion.to_vec().into_iter().enumerate() {
                        stmtseq.insert(i + j, s);
                    }
                    // Java: i = i + expansion.size() - 1 (then the common i = i + 1)
                    if n == 0 {
                        continue;
                    }
                    i += n - 1;
                }
                _ => {}
            }
            i += 1;
        }
        Ok(())
    }
}

fn inner_make_labeled_stmt_seq(stmtseq: &V<Ast>) -> PR<V<Ast>> {
    let result = V::new();
    let mut next_stmt = 0;
    while next_stmt < stmtseq.len() {
        let lstmt = new_node(K::LabeledStmt);
        let mut stmt = stmtseq.get(next_stmt);
        lstmt.col.set(stmt.col.get());
        lstmt.line.set(stmt.line.get());
        lstmt.macro_col.set(stmt.macro_col.get());
        lstmt.macro_line.set(stmt.macro_line.get());
        if stmt.lbl().is_empty() {
            return Err(PErr::Bug("Failure of assertion: Missing Label in MakeLabeledStmtSeq".into()));
        }
        lstmt.set_name(&stmt.lbl());
        let stmts = V::new();
        lstmt.set_stmts(stmts.clone());
        let mut first_time = true;
        while next_stmt < stmtseq.len() && (first_time || stmt.lbl().is_empty()) {
            first_time = false;
            stmts.push(stmt.clone());
            next_stmt += 1;
            if next_stmt < stmtseq.len() {
                stmt = stmtseq.get(next_stmt);
            }
        }
        fix_stmt_seq(&stmts)?;
        lstmt.has_origin.set(true);
        result.push(lstmt);
    }
    Ok(result)
}

/// Moves the leading unlabeled statements of `curr` into a new vector; what remains starts with a label.
fn split_unlabeled(curr: &V<Ast>) -> V<Ast> {
    let unlab = V::new();
    while !curr.is_empty() && curr.get(0).lbl().is_empty() {
        unlab.push(curr.remove(0));
    }
    unlab
}

fn fix_stmt_seq(stmtseq: &V<Ast>) -> PR<()> {
    for stmt in stmtseq.to_vec() {
        match stmt.k {
            K::LabelIf => {
                let curr = stmt.unlab_then();
                let u = split_unlabeled(&curr);
                stmt.set_unlab_then(u.clone());
                fix_stmt_seq(&u)?;
                stmt.set_lab_then(inner_make_labeled_stmt_seq(&curr)?);
                let curr = stmt.unlab_else();
                let u = split_unlabeled(&curr);
                stmt.set_unlab_else(u.clone());
                fix_stmt_seq(&u)?;
                stmt.set_lab_else(inner_make_labeled_stmt_seq(&curr)?);
            }
            K::LabelEither => {
                for clause in stmt.clauses().to_vec() {
                    let curr = clause.unlab_or();
                    let u = split_unlabeled(&curr);
                    clause.set_unlab_or(u.clone());
                    fix_stmt_seq(&u)?;
                    clause.set_lab_or(inner_make_labeled_stmt_seq(&curr)?);
                }
            }
            K::While => {
                let curr = stmt.unlab_do();
                let u = split_unlabeled(&curr);
                stmt.set_unlab_do(u.clone());
                fix_stmt_seq(&u)?;
                stmt.set_lab_do(inner_make_labeled_stmt_seq(&curr)?);
            }
            _ => {}
        }
    }
    Ok(())
}

fn check_for_duplicate_macros(macros: &V<Ast>) -> PR<()> {
    let ms = macros.to_vec();
    for i in 0..ms.len() {
        for j in i + 1..ms.len() {
            if ms[i].name() == ms[j].name() {
                return err(format!("Multiple definitions of macro name `{}'", ms[i].name()));
            }
        }
    }
    Ok(())
}

fn expand_macro_call(call: &Ast, macros: &V<Ast>) -> PR<V<Ast>> {
    let mut def: Option<Ast> = None;
    for m in macros.to_vec() {
        if m.name() == call.name() {
            def = Some(m);
        }
    }
    let def = match def {
        Some(d) => d,
        None => return err(format!("Macro {} undefined,\n    at {}", call.name(), call.location())),
    };
    let args = call.args().to_vec();
    let params = def.sparams().to_vec();
    if params.len() != args.len() {
        return err(format!("Macro {} called with wrong number of arguments at \n    {}", call.name(), call.location()));
    }
    let result = substitute_in_stmt_seq(&def.body(), &args, &params, call.line.get(), call.col.get())?;
    if let Some(first) = result.try_get(0) {
        *first.lbl.borrow_mut() = call.lbl();
    }
    Ok(result)
}

fn substitute_in_labeled_stmt_seq(stmts: &V<Ast>, args: &[Expr], params: &[String]) -> PR<V<Ast>> {
    let result = V::new();
    for s in stmts.to_vec() {
        let r = new_node(K::LabeledStmt);
        r.set_name(&s.name());
        r.set_stmts(substitute_in_stmt_seq(&s.stmts(), args, params, -1, 0)?);
        r.has_origin.set(s.has_origin.get());
        result.push(r);
    }
    Ok(result)
}

fn substitute_in_stmt_seq(stmts: &V<Ast>, args: &[Expr], params: &[String], macro_line: i32, macro_col: i32) -> PR<V<Ast>> {
    let result = V::new();
    for s in stmts.to_vec() {
        result.push(substitute_in_stmt(&s, args, params, macro_line, macro_col)?);
    }
    Ok(result)
}

fn subst_expr(e: &Expr, args: &[Expr], params: &[String]) -> PR<Expr> {
    let r = clone_and_normalize(e);
    msg(r.borrow_mut().substitute_for_all(args, params, true))?;
    Ok(r)
}
fn subst_exprs(v: &V<Expr>, args: &[Expr], params: &[String]) -> PR<V<Expr>> {
    let r = V::new();
    for e in v.to_vec() {
        r.push(subst_expr(&e, args, params)?);
    }
    Ok(r)
}

fn substitute_in_stmt(stmt: &Ast, args: &[Expr], params: &[String], macro_line: i32, macro_col: i32) -> PR<Ast> {
    let result = new_node(stmt.k);
    result.col.set(stmt.col.get());
    result.line.set(stmt.line.get());
    if stmt.k != K::Skip {
        result.macro_col.set(stmt.macro_col.get());
        result.macro_line.set(stmt.macro_line.get());
    }
    result.has_origin.set(stmt.has_origin.get());
    if macro_line > 0 {
        result.macro_line.set(macro_line);
        result.macro_col.set(macro_col);
    }
    let seq = |v: V<Ast>| substitute_in_stmt_seq(&v, args, params, macro_line, macro_col);
    let lseq = |v: V<Ast>| substitute_in_labeled_stmt_seq(&v, args, params);
    match stmt.k {
        K::Assign => {
            let ass = V::new();
            for a in stmt.ass().to_vec() {
                ass.push(substitute_in_single_assign(&a, args, params, macro_line, macro_col)?);
            }
            result.set_ass(ass);
        }
        K::If => {
            result.set_e(subst_expr(&stmt.e(), args, params)?);
            result.set_then(seq(stmt.then())?);
            result.set_els(seq(stmt.els())?);
        }
        K::Either => {
            let ors = V::new();
            for o in stmt.ors().to_vec() {
                ors.push(seq(o)?);
            }
            result.set_ors(ors);
        }
        K::With => {
            result.set_name(&stmt.name());
            result.is_eq.set(stmt.is_eq.get());
            result.set_e(subst_expr(&stmt.e(), args, params)?);
            result.set_do(seq(stmt.do_())?);
        }
        K::When | K::Assert | K::PrintS => result.set_e(subst_expr(&stmt.e(), args, params)?),
        K::Skip => {}
        K::While => {
            result.set_e(subst_expr(&stmt.e(), args, params)?);
            result.set_unlab_do(seq(stmt.unlab_do())?);
            result.set_lab_do(lseq(stmt.lab_do())?);
        }
        K::LabelIf => {
            result.set_e(subst_expr(&stmt.e(), args, params)?);
            result.set_unlab_then(seq(stmt.unlab_then())?);
            result.set_lab_then(lseq(stmt.lab_then())?);
            result.set_unlab_else(seq(stmt.unlab_else())?);
            result.set_lab_else(lseq(stmt.lab_else())?);
        }
        K::LabelEither => {
            let clauses = V::new();
            for old in stmt.clauses().to_vec() {
                let c = new_node(K::Clause);
                c.has_origin.set(old.has_origin.get());
                c.set_lab_or(lseq(old.lab_or())?);
                c.set_unlab_or(seq(old.unlab_or())?);
                clauses.push(c);
            }
            result.set_clauses(clauses);
        }
        K::Call => {
            *result.to.borrow_mut() = stmt.to();
            *result.return_to.borrow_mut() = stmt.return_to.borrow().clone();
            result.set_args(subst_exprs(&stmt.args(), args, params)?);
        }
        K::Return => *result.from.borrow_mut() = stmt.from(),
        K::CallReturn => {
            *result.to.borrow_mut() = stmt.to();
            *result.from.borrow_mut() = stmt.from();
            result.set_args(subst_exprs(&stmt.args(), args, params)?);
        }
        K::CallGoto => {
            *result.to.borrow_mut() = stmt.to();
            *result.after.borrow_mut() = stmt.after.borrow().clone();
            result.set_args(subst_exprs(&stmt.args(), args, params)?);
        }
        K::Goto => *result.to.borrow_mut() = stmt.to(),
        _ => return Err(PErr::Bug(format!("Found unexpected statement type in macro at{}", stmt.location()))),
    }
    Ok(result)
}

fn substitute_in_single_assign(assgn: &Ast, args: &[Expr], params: &[String], macro_line: i32, macro_col: i32) -> PR<Ast> {
    let result = new_node(K::SingleAssign);
    result.has_origin.set(assgn.has_origin.get());
    result.col.set(assgn.col.get());
    result.line.set(assgn.line.get());
    result.macro_col.set(assgn.macro_col.get());
    result.macro_line.set(assgn.macro_line.get());
    if macro_line > 0 {
        result.macro_line.set(macro_line);
        result.macro_col.set(macro_col);
    }
    result.set_e(subst_expr(&assgn.e(), args, params)?);
    let lhs = new_node(K::Lhs);
    result.set_lhs(lhs.clone());
    lhs.has_origin.set(assgn.has_origin.get());
    let old_lhs = assgn.lhs();
    let old_sub = old_lhs.e();
    if expr_is_empty(&old_sub) {
        lhs.set_e(old_sub);
    } else {
        lhs.set_e(subst_expr(&old_sub, args, params)?);
    }
    lhs.set_name(&old_lhs.name());
    if let Some(i) = params.iter().position(|p| *p == lhs.name()) {
        let sub_for_var = args[i].clone();
        let (typ, string) = {
            let e = sub_for_var.borrow();
            let t = e.token_at((0, 0));
            let b = t.borrow();
            (b.typ, b.string.clone())
        };
        if typ != IDENT {
            return err(format!("Macro expansion substitutes `{}' for assignment variable\n    at {}", string, result.location()));
        }
        lhs.set_name(&string);
        let more = sub_for_var.borrow().step_coord((0, 0), 1).is_some();
        if more {
            let copy = clone_and_normalize(&sub_for_var);
            {
                let mut c = copy.borrow_mut();
                c.tokens[0].remove(0);
                c.normalize();
            }
            if expr_is_empty(&lhs.e()) {
                lhs.set_e(copy);
            } else {
                let sub = lhs.e();
                let r = sub.borrow_mut().prepend(&copy.borrow(), 0);
                msg(r)?;
            }
        }
    }
    Ok(result)
}
