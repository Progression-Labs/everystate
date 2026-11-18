//! The symbol table and identifier disambiguation (ports of pcal.PcalSymTab and pcal.PcalFixIDs).
use super::ast::*;
use super::expr::{make_expr, tok, Expr, IDENT};
use super::{err, Ctx, PErr, PR};

pub const GLOBAL: usize = 0;
pub const LABEL: usize = 1;
pub const PROCEDURE: usize = 2;
pub const PROCESS: usize = 3;
pub const PROCESSVAR: usize = 4;
pub const PROCEDUREVAR: usize = 5;
pub const PARAMETER: usize = 6;
const NUM_VTYPES: usize = 7;
const VTYPE_NAME: [&str; 7] = ["Global variable", "Label", "Procedure", "Process", "Process variable", "Procedure variable", "Parameter"];

pub struct SymTabEntry {
    pub typ: usize,
    pub id: String,
    pub context: String,
    pub c_type: String,
    pub line: i32,
    pub col: i32,
    pub use_this: String,
}
pub struct ProcedureEntry {
    pub name: String,
    pub params: V<Ast>,
    pub decls: V<Ast>,
    pub i_pc: Option<String>,
    pub ast: Ast,
}
pub struct ProcessEntry {
    pub name: String,
    pub is_eq: bool,
    pub id: Expr,
    pub decls: V<Ast>,
    pub i_pc: Option<String>,
    pub ast: Ast,
}
fn initial_label(body: &V<Ast>) -> Option<String> {
    body.try_get(0).map(|ls| ls.name())
}

pub struct SymTab {
    pub symtab: Vec<SymTabEntry>,
    pub procs: Vec<ProcedureEntry>,
    pub processes: Vec<ProcessEntry>,
    pub disambiguate_report: Vec<String>,
    pub error_report: String,
    pub i_pc: Option<String>,
}

impl SymTab {
    pub fn new(ast: &Ast) -> PR<SymTab> {
        let mut st = SymTab { symtab: vec![], procs: vec![], processes: vec![], disambiguate_report: vec![], error_report: String::new(), i_pc: None };
        st.insert_sym(GLOBAL, "pc", "", "", 0, 0);
        st.extract(ast);
        if !st.error_report.is_empty() {
            return err(st.error_report.clone());
        }
        Ok(st)
    }

    fn insert_sym(&mut self, typ: usize, id: &str, context: &str, c_type: &str, line: i32, col: i32) -> bool {
        let n = self.symtab.len();
        if typ == PROCEDUREVAR || typ == PROCESSVAR || typ == PARAMETER {
            if self.find_sym_typed(GLOBAL, id, "") < n || self.find_sym(id, context) < n {
                return false;
            }
        } else if self.find_sym_typed(typ, id, context) < n {
            return false;
        }
        self.symtab.push(SymTabEntry { typ, id: id.to_string(), context: context.to_string(), c_type: c_type.to_string(), line, col, use_this: id.to_string() });
        true
    }
    pub fn find_sym_typed(&self, typ: usize, id: &str, context: &str) -> usize {
        self.symtab.iter().position(|se| se.id == id && se.context == context && se.typ == typ).unwrap_or(self.symtab.len())
    }
    pub fn find_sym(&self, id: &str, context: &str) -> usize {
        self.symtab.iter().position(|se| se.id == id && se.context == context).unwrap_or(self.symtab.len())
    }
    pub fn find_proc(&self, id: &str) -> usize {
        self.procs.iter().position(|p| p.name == id).unwrap_or(self.procs.len())
    }
    pub fn find_process(&self, id: &str) -> usize {
        self.processes.iter().position(|p| p.name == id).unwrap_or(self.processes.len())
    }
    pub fn use_this(&self, typ: usize, id: &str, context: &str) -> String {
        match self.symtab.get(self.find_sym_typed(typ, id, context)) {
            Some(se) => se.use_this.clone(),
            None => id.to_string(),
        }
    }
    pub fn use_this_var(&self, id: &str, context: &str) -> String {
        match self.symtab.get(self.find_sym(id, context)) {
            Some(se) if matches!(se.typ, GLOBAL | PROCESSVAR | PROCEDUREVAR | PARAMETER) => se.use_this.clone(),
            _ => id.to_string(),
        }
    }
    fn ambiguous(&self, id: &str) -> bool {
        self.symtab.iter().filter(|se| se.use_this == id).count() > 1
    }
    pub fn disambiguate(&mut self) {
        for vtype in 0..=NUM_VTYPES {
            for i in 0..self.symtab.len() {
                if self.symtab[i].typ != vtype {
                    continue;
                }
                self.symtab[i].use_this = self.symtab[i].id.clone();
                let mut suffix_length = 0;
                while vtype > 0 && self.ambiguous(&self.symtab[i].use_this) {
                    suffix_length += 1;
                    let se = &mut self.symtab[i];
                    let context: Vec<char> = se.context.chars().collect();
                    if suffix_length == 1 {
                        se.use_this.push('_');
                    } else if suffix_length > context.len() + 1 {
                        se.use_this.push_str(&vtype.to_string());
                    } else {
                        se.use_this.push(context[suffix_length - 2]);
                    }
                }
                let se = &self.symtab[i];
                if se.id != se.use_this {
                    let of = if se.context.is_empty() { String::new() } else { format!(" of {} {}", se.c_type, se.context) };
                    self.disambiguate_report.push(format!("\\* {} {}{} at line {} col {} changed to {}", VTYPE_NAME[se.typ], se.id, of, se.line, se.col, se.use_this));
                }
            }
        }
    }

    fn extract(&mut self, ast: &Ast) {
        if !ast.prcds().is_empty() {
            self.insert_sym(GLOBAL, "stack", "", "", 0, 0);
        }
        for d in ast.decls().to_vec() {
            self.extract_var_decl(&d, "");
        }
        for p in ast.prcds().to_vec() {
            self.extract_procedure(&p);
        }
        if ast.k == K::Uniprocess {
            let body = ast.body();
            self.i_pc = initial_label(&body);
            for ls in body.to_vec() {
                self.extract_labeled_stmt(&ls, "", "");
            }
        } else {
            for p in ast.procs().to_vec() {
                self.extract_process(&p);
            }
        }
    }
    fn extract_procedure(&mut self, ast: &Ast) {
        let name = ast.name();
        if self.find_proc(&name) < self.procs.len() {
            self.error_report += &format!("\nProcedure {} redefined at line {}, column {}", name, ast.line.get(), ast.col.get());
        } else {
            self.procs.push(ProcedureEntry { name: name.clone(), params: ast.params(), decls: ast.decls(), i_pc: initial_label(&ast.body()), ast: ast.clone() });
        }
        self.insert_sym(PROCEDURE, &name, "", "procedure", ast.line.get(), ast.col.get());
        for d in ast.decls().to_vec() {
            if !self.insert_sym(PROCEDUREVAR, &d.name(), &name, "procedure", d.line.get(), d.col.get()) {
                self.error_report += &format!("\nProcedure variable {} redefined at line {}, column {}", d.name(), d.line.get(), d.col.get());
            }
        }
        for d in ast.params().to_vec() {
            if !self.insert_sym(PARAMETER, &d.name(), &name, "procedure", d.line.get(), d.col.get()) {
                self.error_report += &format!("\nParameter {} redefined at line {}, column {}", d.name(), d.line.get(), d.col.get());
            }
        }
        for ls in ast.body().to_vec() {
            self.extract_labeled_stmt(&ls, &name, "procedure");
        }
    }
    fn extract_process(&mut self, ast: &Ast) {
        let name = ast.name();
        if self.find_process(&name) < self.processes.len() {
            self.error_report += &format!("\nProcess {} redefined at line {}, column {}", name, ast.line.get(), ast.col.get());
        } else {
            self.processes.push(ProcessEntry { name: name.clone(), is_eq: ast.is_eq.get(), id: ast.e(), decls: ast.decls(), i_pc: initial_label(&ast.body()), ast: ast.clone() });
        }
        self.insert_sym(PROCESS, &name, "", "process", ast.line.get(), ast.col.get());
        for d in ast.decls().to_vec() {
            self.extract_var_decl(&d, &name);
        }
        for ls in ast.body().to_vec() {
            self.extract_labeled_stmt(&ls, &name, "process");
        }
    }
    fn extract_var_decl(&mut self, ast: &Ast, context: &str) {
        let vtype = if context.is_empty() { GLOBAL } else { PROCESSVAR };
        if !self.insert_sym(vtype, &ast.name(), context, "process", ast.line.get(), ast.col.get()) {
            self.error_report += &format!("\n{} {} redefined at line {}, column {}", VTYPE_NAME[vtype], ast.name(), ast.line.get(), ast.col.get());
        }
    }
    fn extract_labeled_stmt(&mut self, ast: &Ast, context: &str, c_type: &str) {
        if !self.insert_sym(LABEL, &ast.name(), context, c_type, ast.line.get(), ast.col.get()) {
            self.error_report += &format!("\nLabel {} redefined at line {}, column {}", ast.name(), ast.line.get(), ast.col.get());
        }
        self.extract_stmts(&ast.stmts(), context, c_type);
    }
    fn extract_stmts(&mut self, v: &V<Ast>, context: &str, c_type: &str) {
        for s in v.to_vec() {
            self.extract_stmt(&s, context, c_type);
        }
    }
    fn extract_labeled(&mut self, v: &V<Ast>, context: &str, c_type: &str) {
        for s in v.to_vec() {
            self.extract_labeled_stmt(&s, context, c_type);
        }
    }
    fn extract_stmt(&mut self, ast: &Ast, context: &str, c_type: &str) {
        match ast.k {
            K::While => {
                self.extract_stmts(&ast.unlab_do(), context, c_type);
                self.extract_labeled(&ast.lab_do(), context, c_type);
            }
            K::If => {
                self.extract_stmts(&ast.then(), context, c_type);
                self.extract_stmts(&ast.els(), context, c_type);
            }
            K::With => self.extract_stmts(&ast.do_(), context, c_type),
            K::LabelIf => {
                self.extract_stmts(&ast.unlab_then(), context, c_type);
                self.extract_labeled(&ast.lab_then(), context, c_type);
                self.extract_stmts(&ast.unlab_else(), context, c_type);
                self.extract_labeled(&ast.lab_else(), context, c_type);
            }
            K::Either => {
                for o in ast.ors().to_vec() {
                    self.extract_stmts(&o, context, c_type);
                }
            }
            K::LabelEither => {
                for c in ast.clauses().to_vec() {
                    self.extract_stmts(&c.unlab_or(), context, c_type);
                    self.extract_labeled(&c.lab_or(), context, c_type);
                }
            }
            _ => {}
        }
    }

    pub fn check_for_default_init_value(&self) -> PR<()> {
        let mut errors = String::new();
        for se in &self.symtab {
            if se.id == "defaultInitValue" {
                if errors.is_empty() {
                    errors = "Cannot use `defaultInitValue' as ".to_string();
                } else {
                    errors += " or ";
                }
                errors += VTYPE_NAME[se.typ];
                errors += " name";
            }
        }
        if errors.is_empty() { Ok(()) } else { err(errors) }
    }

    // ---- PcalFixIDs ----
    pub fn fix(&mut self, ast: &Ast, ctx: &mut Ctx) -> PR<()> {
        for d in ast.decls().to_vec() {
            self.fix_var_decl(&d, "")?;
        }
        if ast.k == K::Uniprocess {
            for p in ast.prcds().to_vec() {
                self.fix_procedure(&p)?;
            }
            for ls in ast.body().to_vec() {
                self.fix_labeled_stmt(&ls, "")?;
            }
        } else {
            self.fix_multiprocess(ast, ctx)?;
        }
        if let Some(ipc) = &self.i_pc {
            self.i_pc = Some(self.use_this(LABEL, ipc, ""));
        }
        Ok(())
    }
    fn fix_multiprocess(&mut self, ast: &Ast, ctx: &mut Ctx) -> PR<()> {
        let mut names: Vec<String> = vec![];
        let mut called: Vec<V<String>> = vec![];
        let prcds = ast.prcds().to_vec();
        for prcd in &prcds {
            self.fix_procedure(prcd)?;
            names.push(prcd.name());
            called.push(prcd.procedures_called());
        }
        let n = names.len();
        let mut path = vec![vec![false; n]; n];
        for i in 0..n {
            let c = called[i].to_vec();
            for j in 0..n {
                path[i][j] = c.contains(&names[j]);
            }
        }
        for k in 0..n {
            for i in 0..n {
                for j in 0..n {
                    path[i][j] = path[i][j] || (path[i][k] && path[k][j]);
                }
            }
        }
        for (i, prcd) in prcds.iter().enumerate() {
            let p: Vec<String> = (0..n).filter(|j| path[i][*j]).map(|j| names[j].clone()).collect();
            prcd.set_procedures_called(V::of(p));
        }
        for proc in ast.procs().to_vec() {
            self.fix_process(&proc)?;
            let p_called = proc.procedures_called();
            let mut j = 0;
            while j < p_called.len() {
                let p_name = p_called.get(j);
                let p_num = match names.iter().position(|x| *x == p_name) {
                    Some(x) => x,
                    None => {
                        ctx.report_error(&format!("Could not find procedure name `{}'", p_name));
                        return Ok(());
                    }
                };
                for k in 0..n {
                    if path[p_num][k] && !p_called.to_vec().contains(&names[k]) {
                        p_called.push(names[k].clone());
                    }
                }
                j += 1;
            }
        }
        Ok(())
    }
    fn fix_labels(&self, v: &V<String>, context: &str) {
        for i in 0..v.len() {
            v.set(i, self.use_this(LABEL, &v.get(i), context));
        }
    }
    fn fix_procedure(&mut self, ast: &Ast) -> PR<()> {
        let name = ast.name();
        for d in ast.decls().to_vec() {
            self.fix_var_decl(&d, &name)?;
        }
        for d in ast.params().to_vec() {
            self.fix_var_decl(&d, &name)?;
        }
        for ls in ast.body().to_vec() {
            self.fix_labeled_stmt(&ls, &name)?;
        }
        let p = self.find_proc(&name);
        self.fix_labels(&ast.plus_labels(), &name);
        self.fix_labels(&ast.minus_labels(), &name);
        if p >= self.procs.len() {
            return Err(PErr::Runtime);
        }
        if let Some(ipc) = self.procs[p].i_pc.clone() {
            self.procs[p].i_pc = Some(self.use_this(LABEL, &ipc, &name));
        }
        let new_name = self.use_this(PROCEDURE, &name, "");
        ast.set_name(&new_name);
        self.procs[p].name = new_name;
        Ok(())
    }
    fn fix_process(&mut self, ast: &Ast) -> PR<()> {
        let name = ast.name();
        for d in ast.decls().to_vec() {
            self.fix_var_decl(&d, &name)?;
        }
        for ls in ast.body().to_vec() {
            self.fix_labeled_stmt(&ls, &name)?;
        }
        let p = self.find_process(&name);
        self.fix_labels(&ast.plus_labels(), &name);
        self.fix_labels(&ast.minus_labels(), &name);
        if p >= self.processes.len() {
            return Err(PErr::Runtime);
        }
        if let Some(ipc) = self.processes[p].i_pc.clone() {
            self.processes[p].i_pc = Some(self.use_this(LABEL, &ipc, &name));
        }
        let new_name = self.use_this(PROCESS, &name, "");
        ast.set_name(&new_name);
        self.processes[p].name = new_name;
        Ok(())
    }
    fn fix_var_decl(&self, ast: &Ast, context: &str) -> PR<()> {
        ast.set_name(&self.use_this_var(&ast.name(), context));
        self.fix_expr(&ast.e(), context)
    }
    fn fix_labeled_stmt(&self, ast: &Ast, context: &str) -> PR<()> {
        ast.set_name(&self.use_this(LABEL, &ast.name(), context));
        self.fix_stmts(&ast.stmts(), context)
    }
    fn fix_stmts(&self, v: &V<Ast>, context: &str) -> PR<()> {
        for s in v.to_vec() {
            self.fix_sym(&s, context)?;
        }
        Ok(())
    }
    fn fix_labeled(&self, v: &V<Ast>, context: &str) -> PR<()> {
        for s in v.to_vec() {
            self.fix_labeled_stmt(&s, context)?;
        }
        Ok(())
    }
    fn fix_args(&self, ast: &Ast, context: &str) -> PR<()> {
        for a in ast.args().to_vec() {
            self.fix_expr(&a, context)?;
        }
        Ok(())
    }
    fn fix_sym(&self, ast: &Ast, context: &str) -> PR<()> {
        let proc_name = |s: &str| self.use_this(PROCEDURE, s, context);
        match ast.k {
            K::LabeledStmt => self.fix_labeled_stmt(ast, context)?,
            K::While => {
                self.fix_stmts(&ast.unlab_do(), context)?;
                self.fix_labeled(&ast.lab_do(), context)?;
                self.fix_expr(&ast.e(), context)?;
            }
            K::Assign => {
                for a in ast.ass().to_vec() {
                    self.fix_sym(&a, context)?;
                }
            }
            K::SingleAssign => {
                self.fix_sym(&ast.lhs(), context)?;
                self.fix_expr(&ast.e(), context)?;
            }
            K::Lhs => {
                ast.set_name(&self.use_this_var(&ast.name(), context));
                self.fix_expr(&ast.e(), context)?;
            }
            K::If => {
                self.fix_stmts(&ast.then(), context)?;
                self.fix_stmts(&ast.els(), context)?;
                self.fix_expr(&ast.e(), context)?;
            }
            K::With => {
                self.fix_expr(&ast.e(), context)?;
                self.fix_stmts(&ast.do_(), context)?;
            }
            K::When | K::PrintS | K::Assert => self.fix_expr(&ast.e(), context)?,
            K::Skip => {}
            K::LabelIf => {
                self.fix_expr(&ast.e(), context)?;
                self.fix_stmts(&ast.unlab_then(), context)?;
                self.fix_labeled(&ast.lab_then(), context)?;
                self.fix_stmts(&ast.unlab_else(), context)?;
                self.fix_labeled(&ast.lab_else(), context)?;
            }
            K::Call => {
                let r = proc_name(&ast.return_to.borrow());
                *ast.return_to.borrow_mut() = r;
                let t = proc_name(&ast.to());
                *ast.to.borrow_mut() = t;
                self.fix_args(ast, context)?;
            }
            K::Return => {
                if let Some(f) = ast.from() {
                    *ast.from.borrow_mut() = Some(proc_name(&f));
                }
            }
            K::CallReturn => {
                if let Some(f) = ast.from() {
                    *ast.from.borrow_mut() = Some(proc_name(&f));
                }
                let t = proc_name(&ast.to());
                *ast.to.borrow_mut() = t;
                self.fix_args(ast, context)?;
            }
            K::CallGoto => {
                let a = proc_name(&ast.after.borrow());
                *ast.after.borrow_mut() = a;
                let t = proc_name(&ast.to());
                *ast.to.borrow_mut() = t;
                self.fix_args(ast, context)?;
            }
            K::Goto => {
                let to = ast.to();
                if self.find_sym_typed(LABEL, &to, context) == self.symtab.len() && to != "Done" {
                    return err(format!("goto to non-existent label `{}' at line {}, column {}", to, ast.line.get(), ast.col.get()));
                }
                *ast.to.borrow_mut() = self.use_this(LABEL, &to, context);
            }
            K::Either => {
                for o in ast.ors().to_vec() {
                    self.fix_stmts(&o, context)?;
                }
            }
            K::LabelEither => {
                for c in ast.clauses().to_vec() {
                    self.fix_stmts(&c.unlab_or(), context)?;
                    self.fix_labeled(&c.lab_or(), context)?;
                }
            }
            _ => return Err(PErr::Bug("Unexpected AST type".into())),
        }
        Ok(())
    }
    fn fix_expr(&self, expr: &Expr, context: &str) -> PR<()> {
        let mut expr_vec: Vec<Expr> = vec![];
        let mut string_vec: Vec<String> = vec![];
        for line in &expr.borrow().tokens {
            for t in line {
                let b = t.borrow();
                if b.typ == IDENT {
                    let use_me = self.use_this_var(&b.string, context);
                    if string_vec.contains(&b.string) || use_me == b.string {
                        continue;
                    }
                    string_vec.push(b.string.clone());
                    expr_vec.push(make_expr(vec![vec![tok(&use_me, 0, IDENT)]]));
                }
            }
        }
        if !expr_vec.is_empty() {
            expr.borrow_mut().substitute_for_all(&expr_vec, &string_vec, false).map_err(PErr::Msg)?;
        }
        Ok(())
    }
}
