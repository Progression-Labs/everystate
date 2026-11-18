//! TLA+ expressions as the PlusCal translator sees them: lines of tokens with columns
//! (port of pcal.TLAToken and pcal.TLAExpr).  Tokens are shared, mutable objects, exactly as in
//! the Java translator, because the layout algorithm (anchor tokens) depends on token identity.
use std::cell::RefCell;
use std::rc::Rc;

pub const BUILTIN: i32 = 1;
pub const NUMBER: i32 = 2;
pub const STRING: i32 = 3;
pub const IDENT: i32 = 4;
pub const ADDED: i32 = 5;

/// Length of a string as Java's `String.length()` reports it (UTF-16 code units).
pub fn jlen(s: &str) -> i32 {
    if s.is_ascii() { s.len() as i32 } else { s.encode_utf16().count() as i32 }
}
pub fn spaces(n: i32) -> String {
    " ".repeat(n.max(0) as usize)
}

#[derive(Clone)]
pub struct TLAToken {
    pub string: String,
    pub column: i32,
    pub typ: i32,
}
impl TLAToken {
    pub fn get_width(&self) -> i32 {
        if self.typ == STRING { jlen(&self.string) + 2 } else { jlen(&self.string) }
    }
}
pub type Tok = Rc<RefCell<TLAToken>>;
pub fn tok(s: &str, col: i32, typ: i32) -> Tok {
    Rc::new(RefCell::new(TLAToken { string: s.to_string(), column: col, typ }))
}
fn copy_tok(t: &Tok) -> Tok {
    Rc::new(RefCell::new(t.borrow().clone()))
}
fn width(t: &Tok) -> i32 {
    t.borrow().get_width()
}
fn column(t: &Tok) -> i32 {
    t.borrow().column
}

#[derive(Default)]
pub struct TLAExpr {
    pub tokens: Vec<Vec<Tok>>,
    pub anchor_tokens: Vec<Option<Tok>>,
    pub anchor_tok_col: Vec<i32>,
    /// Whether the Java object has a non-null origin region (only that matters here).
    pub has_origin: bool,
}
pub type Expr = Rc<RefCell<TLAExpr>>;
pub type Coord = (usize, usize);

pub fn new_expr() -> Expr {
    Rc::new(RefCell::new(TLAExpr::default()))
}
pub fn expr_from(tokens: Vec<Vec<Tok>>) -> Expr {
    Rc::new(RefCell::new(TLAExpr { tokens, ..Default::default() }))
}
/// `new TLAExpr(vec)` followed by `normalize()`.
pub fn make_expr(tokens: Vec<Vec<Tok>>) -> Expr {
    let e = expr_from(tokens);
    e.borrow_mut().normalize();
    e
}
pub fn clone_and_normalize(e: &Expr) -> Expr {
    Rc::new(RefCell::new(e.borrow().clone_and_normalize()))
}

impl TLAExpr {
    pub fn add_token(&mut self, t: Tok) {
        self.tokens.last_mut().expect("addToken on an expression without lines").push(t);
    }
    pub fn add_token_offset(&mut self, t: Tok, offset: i32) {
        let last_line = self.tokens.last_mut().expect("addTokenOffset on an expression without lines");
        let mut new_col = offset;
        if let Some(last) = last_line.last() {
            let l = last.borrow();
            new_col += l.column + jlen(&l.string);
        }
        t.borrow_mut().column = new_col;
        last_line.push(t);
    }
    pub fn add_line(&mut self) {
        self.tokens.push(vec![]);
    }

    pub fn normalize(&mut self) {
        while !self.tokens.is_empty() && self.tokens[0].is_empty() {
            self.tokens.remove(0);
        }
        while !self.tokens.is_empty() && self.tokens[self.tokens.len() - 1].is_empty() {
            self.tokens.pop();
        }
        let mut min_col = 999999;
        for line in &self.tokens {
            if let Some(t) = line.first() {
                min_col = min_col.min(column(t));
            }
        }
        for line in &self.tokens {
            for t in line {
                t.borrow_mut().column -= min_col;
            }
        }
        let n = self.tokens.len();
        self.anchor_tokens = vec![None; n];
        self.anchor_tok_col = vec![0; n];
        for i in 0..n {
            let cur = &self.tokens[i];
            if cur.is_empty() {
                continue;
            }
            let first_col = column(&cur[0]);
            let mut j = i as isize - 1;
            while j >= 0 {
                let anc = &self.tokens[j as usize];
                if !anc.is_empty() && column(&anc[0]) <= first_col {
                    let mut k = 0;
                    while k + 1 < anc.len() && column(&anc[k + 1]) <= first_col {
                        k += 1;
                    }
                    self.anchor_tok_col[i] = column(&anc[k]);
                    self.anchor_tokens[i] = Some(anc[k].clone());
                    break;
                }
                j -= 1;
            }
        }
    }

    pub fn renormalize(&mut self) -> Result<(), String> {
        for i in 0..self.tokens.len() {
            let anchor = match self.anchor_tokens.get(i) {
                Some(Some(a)) => a.clone(),
                _ => continue,
            };
            let k = column(&anchor) - self.anchor_tok_col[i];
            self.anchor_tok_col[i] = column(&anchor);
            if k < 0 {
                return Err("TLAExpr.renormalize() found anchor has moved to left.".to_string());
            }
            for t in &self.tokens[i] {
                t.borrow_mut().column += k;
            }
        }
        Ok(())
    }

    pub fn to_string_vector(&self) -> Vec<String> {
        let mut result = Vec::with_capacity(self.tokens.len());
        for (i, line) in self.tokens.iter().enumerate() {
            let mut cur = String::new();
            if let Some(Some(a)) = self.anchor_tokens.get(i) {
                cur.push_str(&spaces(column(a) - self.anchor_tok_col[i]));
            }
            let mut last: Option<&Tok> = None;
            for t in line {
                match last {
                    None => cur.push_str(&spaces(column(t))),
                    Some(l) => cur.push_str(&spaces(column(t) - column(l) - width(l))),
                }
                let b = t.borrow();
                if b.typ == STRING {
                    cur.push('"');
                    cur.push_str(&b.string);
                    cur.push('"');
                } else {
                    cur.push_str(&b.string);
                }
                last = Some(t);
            }
            result.push(cur);
        }
        result
    }

    /// `TLAExpr.toString()`: the token sequence as a TLA+ tuple of strings (used in the AST dump
    /// whose checksum is stored in the BEGIN TRANSLATION line).
    pub fn java_to_string(&self) -> String {
        let mut result = String::from("<< ");
        let mut nonempty = false;
        for (i, line) in self.tokens.iter().enumerate() {
            if i > 0 {
                result.push('\n');
            }
            for t in line {
                if nonempty {
                    result.push_str(", ");
                }
                nonempty = true;
                let b = t.borrow();
                if b.typ == STRING {
                    result.push_str("\"\\\"\", \"");
                    result.push_str(&b.string);
                    result.push_str("\", \"\\\"\"");
                } else if b.string == "\\/" {
                    result.push_str(&format!("\"(col{}) \\\\/\"", b.column));
                } else if b.string.starts_with('\\') {
                    result.push_str("\"\\");
                    result.push_str(&b.string);
                    result.push('"');
                } else if b.string == "/\\" {
                    result.push_str(&format!("\"(col{}) /\\\\\"", b.column));
                } else {
                    result.push('"');
                    result.push_str(&b.string);
                    result.push('"');
                }
            }
        }
        result + " >>"
    }

    pub fn clone_and_normalize(&self) -> TLAExpr {
        let mut r = TLAExpr { tokens: self.tokens.iter().map(|l| l.iter().map(copy_tok).collect()).collect(), has_origin: self.has_origin, ..Default::default() };
        r.normalize();
        r
    }

    pub fn prepend(&mut self, expr: &TLAExpr, spaces: i32) -> Result<(), String> {
        let en = expr.tokens.len();
        let mut i = 0;
        while i + 1 < en {
            self.tokens.insert(i, expr.tokens[i].clone());
            i += 1;
        }
        let expr_line = &expr.tokens[i];
        let last = expr_line.last().expect("prepend of an expression with an empty last line");
        let incr = column(last) + width(last) + spaces;
        let this_line = &mut self.tokens[i];
        for t in this_line.iter() {
            t.borrow_mut().column += incr;
        }
        for (j, t) in expr_line.iter().enumerate() {
            this_line.insert(j, t.clone());
        }
        let n = self.tokens.len();
        let mut new_a: Vec<Option<Tok>> = vec![None; n];
        let mut new_c = vec![0; n];
        for j in 0..en.min(n) {
            new_a[j] = expr.anchor_tokens.get(j).cloned().flatten();
            new_c[j] = expr.anchor_tok_col.get(j).copied().unwrap_or(0);
        }
        for j in en..n {
            new_a[j] = self.anchor_tokens.get(j + 1 - en).cloned().flatten();
            new_c[j] = self.anchor_tok_col.get(j + 1 - en).copied().unwrap_or(0);
        }
        self.anchor_tokens = new_a;
        self.anchor_tok_col = new_c;
        self.renormalize()
    }

    pub fn substitute_for_all(&mut self, exprs: &[Expr], strs: &[String], parenthesize: bool) -> Result<(), String> {
        let n = exprs.len();
        let mut next: Vec<Option<Coord>> = (0..n).map(|i| self.find_next_instance_in(&strs[i], (0, 0))).collect();
        loop {
            let mut next_pos: Option<Coord> = None;
            let mut next_idx = 0;
            for (i, p) in next.iter().enumerate() {
                if let Some(pos) = p {
                    match next_pos {
                        None => {
                            next_pos = Some(*pos);
                            next_idx = i;
                        }
                        Some(np) => {
                            if pos.0 < np.0 || (pos.0 == np.0 && pos.1 < np.1) {
                                next_pos = Some(*pos);
                                next_idx = i;
                            }
                        }
                    }
                }
            }
            let next_pos = match next_pos {
                None => return Ok(()),
                Some(p) => p,
            };
            let after = self.step_coord(next_pos, 1);
            let e = exprs[next_idx].clone();
            let new_pos = self.substitute_at(&e.borrow(), next_pos, parenthesize)?;
            next[next_idx] = match new_pos {
                None => None,
                Some(p) => self.find_next_instance_in(&strs[next_idx], p),
            };
            for i in 0..n {
                if i == next_idx {
                    continue;
                }
                if let Some(ni) = next[i].as_mut() {
                    // Java asserts that the two positions exist here ("Doing substitutions in wrong order")
                    let (np, an) = match (new_pos, after) {
                        (Some(a), Some(b)) => (a, b),
                        _ => return Err("Doing substitutions in wrong order.".to_string()),
                    };
                    if an.0 == np.0 {
                        if ni.0 == next_pos.0 {
                            ni.1 = (ni.1 as isize + (np.1 as isize - an.1 as isize)) as usize;
                        }
                    } else if ni.0 == next_pos.0 {
                        ni.0 = (ni.0 as isize + (np.0 as isize - an.0 as isize)) as usize;
                        ni.1 = (ni.1 as isize + (np.1 as isize - an.1 as isize)) as usize;
                    } else {
                        ni.0 = (ni.0 as isize + (np.0 as isize - an.0 as isize)) as usize;
                    }
                }
            }
        }
    }

    pub fn substitute_at(&mut self, expr: &TLAExpr, coord: Coord, par: bool) -> Result<Option<Coord>, String> {
        let tok = self.token_at(coord);
        if self.is_one_token() {
            let cloned = expr.clone_and_normalize();
            self.tokens = cloned.tokens;
            self.anchor_tokens = cloned.anchor_tokens;
            self.anchor_tok_col = cloned.anchor_tok_col;
            return Ok(None);
        }
        let mut spaces = 0;
        if coord.1 + 1 < self.tokens[coord.0].len() {
            let next = &self.tokens[coord.0][coord.1 + 1];
            spaces = column(next) - (column(&tok) + width(&tok));
        }
        let rest_of_line: Vec<Tok> = self.tokens[coord.0].split_off(coord.1 + 1);
        let mut cur_line = coord.0;
        if expr.tokens.len() == 1 && expr.tokens[0].len() == 1 {
            let e = expr.tokens[0][0].borrow();
            let mut t = tok.borrow_mut();
            t.string = e.string.clone();
            t.typ = e.typ;
        } else {
            let mut indent = (if par { 1 } else { 0 }) + column(&tok);
            let mut do_insert = true;
            if par {
                let mut t = tok.borrow_mut();
                t.string = "(".to_string();
                t.typ = BUILTIN;
                do_insert = false;
            }
            let new_expr = expr.clone_and_normalize();
            let mut i = 0;
            while i < new_expr.tokens.len() {
                for next_tok in &new_expr.tokens[i] {
                    next_tok.borrow_mut().column += indent;
                    if do_insert {
                        let n = next_tok.borrow();
                        let mut t = tok.borrow_mut();
                        t.string = n.string.clone();
                        t.typ = n.typ;
                        do_insert = false;
                    } else {
                        self.tokens[cur_line].push(next_tok.clone());
                    }
                }
                i += 1;
                if i < new_expr.tokens.len() {
                    indent = 0;
                    cur_line += 1;
                    self.tokens.insert(cur_line, vec![]);
                    while self.anchor_tokens.len() < self.tokens.len() - 1 {
                        self.anchor_tokens.push(None);
                        self.anchor_tok_col.push(0);
                    }
                    self.anchor_tokens.insert(cur_line, new_expr.anchor_tokens[i].clone());
                    self.anchor_tok_col.insert(cur_line, new_expr.anchor_tok_col[i]);
                }
            }
            if par {
                let last = self.tokens[cur_line].last().expect("substitution produced an empty line").clone();
                let r = crate::pcal::expr::tok(")", column(&last) + width(&last), BUILTIN);
                self.tokens[cur_line].push(r);
            }
        }
        let result = (cur_line, self.tokens[cur_line].len() - 1);
        if !rest_of_line.is_empty() {
            let prev = self.tokens[cur_line].last().unwrap().clone();
            let indent = column(&prev) + width(&prev) + spaces - column(&rest_of_line[0]);
            for t in rest_of_line {
                t.borrow_mut().column += indent;
                self.tokens[cur_line].push(t);
            }
        }
        self.renormalize()?;
        Ok(self.step_coord(result, 1))
    }

    pub fn find_next_instance_in(&self, id: &str, start: Coord) -> Option<Coord> {
        let mut result = if self.is_empty() { None } else { Some(start) };
        while let Some(r) = result {
            let t = self.token_at(r);
            let (typ, s) = {
                let b = t.borrow();
                (b.typ, b.string.clone())
            };
            if typ == STRING {
                result = self.step_coord(r, 1);
            } else if s == "." {
                result = self.step_coord(r, 2);
            } else if (s == "[" || s == ",") && {
                match self.step_coord(r, 2) {
                    None => false,
                    Some(c2) => {
                        let t2 = self.token_at(c2);
                        let b2 = t2.borrow();
                        b2.typ != STRING && (b2.string == ":" || b2.string == "|->" || b2.string == "\u{21A6}")
                    }
                }
            } {
                result = self.step_coord(r, 3);
            } else if s == id {
                return Some(r);
            } else {
                result = self.step_coord(r, 1);
            }
        }
        None
    }

    pub fn token_at(&self, c: Coord) -> Tok {
        self.tokens[c.0][c.1].clone()
    }

    pub fn step_coord(&self, coord: Coord, incr: usize) -> Option<Coord> {
        let mut r = coord;
        for _ in 0..incr {
            r.1 += 1;
            if self.tokens[r.0].len() == r.1 {
                r.1 = 0;
                r.0 += 1;
                while r.0 < self.tokens.len() && self.tokens[r.0].is_empty() {
                    r.0 += 1;
                }
                if r.0 == self.tokens.len() {
                    return None;
                }
            }
        }
        Some(r)
    }

    pub fn is_empty(&self) -> bool {
        self.tokens.is_empty()
    }
    pub fn is_one_token(&self) -> bool {
        self.tokens.len() == 1 && self.tokens[0].len() == 1
    }
}
