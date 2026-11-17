//! The character reader and the tokenizer of the PlusCal translator (ports of
//! pcal.PcalCharReader, pcal.Tokenize and pcal.PcalBuiltInSymbols).
use super::expr::{expr_from, tok, Expr, Tok, BUILTIN, IDENT, NUMBER, STRING};
use super::symbols::SYMBOLS;

const TAB: char = '\t';
const NL: char = '\n';

// token classes of tla2tex.Token that the tokenizer distinguishes
const T_DASHES: i32 = 6;
const T_END_MODULE: i32 = 7;

pub fn is_letter(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}
pub fn is_digit(c: char) -> bool {
    c.is_ascii_digit()
}
fn is_space(c: char) -> bool {
    c == ' ' || c == '\x0c' || c == '\r'
}
pub fn builtin_kind(s: &str) -> Option<u8> {
    SYMBOLS.iter().find(|(t, _)| *t == s).map(|(_, k)| *k)
}
pub fn is_builtin_symbol(s: &str) -> bool {
    builtin_kind(s).is_some()
}
fn is_builtin_prefix(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }
    SYMBOLS.iter().any(|(t, _)| {
        let mut cs = t.chars();
        let c0 = cs.next().unwrap_or(' ');
        let c1 = cs.next();
        let word = is_letter(c0) || (c0 == '\\' && c1.map(is_letter).unwrap_or(false));
        !word && t.starts_with(s)
    })
}
fn is_string_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || " ~!@#$%^&*()_-+={}[]|:;<,>.?/`'".contains(c)
}

/// Reads the input character by character; `\t` signals the end of the input.
pub struct CharReader {
    vec: Vec<Vec<char>>,
    current: Option<Vec<char>>,
    line: usize,
    column: usize,
    vcolumn: usize,
    last_line: usize,
    last_column: usize,
    tab_to_spaces: bool,
}

impl CharReader {
    pub fn new(vec: Vec<Vec<char>>, first_line: usize, first_col: usize, last_line: usize, last_col: usize) -> Self {
        let mut vcolumn = 0;
        let mut current = None;
        if first_line < vec.len() {
            let ln = &vec[first_line];
            for i in 0..first_col {
                if ln.get(i) == Some(&TAB) {
                    vcolumn = (vcolumn / 8 + 1) * 8;
                } else {
                    vcolumn += 1;
                }
            }
            current = Some(ln.clone());
        }
        CharReader { vec, current, line: first_line, column: first_col, vcolumn, last_line, last_column: last_col, tab_to_spaces: false }
    }
    pub fn line_number(&self) -> i32 {
        self.line as i32
    }
    pub fn column_number(&self) -> i32 {
        self.vcolumn as i32
    }
    pub fn next_char(&mut self) -> char {
        let len = match &self.current {
            None => return TAB,
            Some(c) => c.len(),
        };
        if self.tab_to_spaces {
            self.vcolumn += 1;
            if self.vcolumn % 8 == 0 {
                self.tab_to_spaces = false;
            }
            return ' ';
        }
        if self.line > self.last_line || (self.line == self.last_line && self.column >= self.last_column) {
            return TAB;
        }
        if len == self.column {
            self.line += 1;
            self.column = 0;
            self.vcolumn = 0;
            self.current = self.vec.get(self.line).cloned();
            return NL;
        }
        let c = self.current.as_ref().unwrap()[self.column];
        self.column += 1;
        self.vcolumn += 1;
        if c == TAB {
            if self.vcolumn % 8 != 0 {
                self.tab_to_spaces = true;
            }
            return ' ';
        }
        c
    }
    pub fn backspace(&mut self) {
        if self.column == 0 {
            if self.line == 0 {
                return;
            }
            self.line -= 1;
            self.current = self.vec.get(self.line).cloned();
            self.column = 0;
            self.vcolumn = 0;
            let len = self.current.as_ref().map(|c| c.len()).unwrap_or(0);
            while self.column + 1 < len {
                let before = self.column;
                self.next_char();
                if self.column == before && !self.tab_to_spaces {
                    break;
                }
            }
        } else {
            self.column -= 1;
            self.vcolumn -= 1;
        }
    }
    /// The rest of the current line after skipping white space and line ends, or "\t" at the end
    /// of the input.
    pub fn peek(&mut self) -> String {
        let mut next = self.next_char();
        while next == ' ' || next == NL {
            next = self.next_char();
        }
        if next == TAB {
            return "\t".to_string();
        }
        self.backspace();
        let cur = self.current.as_ref().unwrap();
        let mut s: String = cur[self.column.min(cur.len())..].iter().collect();
        s.push('\n');
        s
    }
}

#[derive(Clone, Copy, PartialEq)]
enum St {
    Start,
    Id,
    NumOrId,
    Bs,
    Num,
    NumOrBi,
    BsBuiltIn,
    BuiltIn,
    Dash1,
    Dash2,
    Dash3,
    Dashes,
    Eq1,
    Eq2,
    Eq3,
    Eqs,
    LeftParen,
    Str,
    EscStr,
    LineComment,
    LineComParen,
    LineComStar,
    Comment,
    CommentStar,
    CommentParen,
    OrComment,
    OrCommentStar,
    OrCommentParen,
    Done,
}

/// The tokenizer state that survives from one call to the next (the Java class keeps it in
/// static fields), plus the delimiter found by the last call.
pub struct Tokenizer {
    pub delimiter: String,
    pub delimiter_line: i32,
    pub delimiter_col: i32,
    cdepth: i32,
    in_define_block: bool,
}

struct Run<'a> {
    reader: &'a mut CharReader,
    vspec: Vec<Vec<Tok>>,
    linev: Vec<Tok>,
    next_char: char,
    token: String,
    paren_depth: i32,
    in_quantifier: bool,
    col: i32,
    ncol: i32,
    parse_expression: bool,
    in_define_block: bool,
    prev_token: String,
    expr_end: bool,
    delimiter: String,
    delimiter_line: i32,
    delimiter_col: i32,
}

fn is_delimiter(t: &str) -> bool {
    matches!(
        t,
        ";" | "do" | "then" | ":=" | "\u{2254}" | "begin" | "variable" | "variables" | "||" | "\u{2016}" | "end" | "else" | "elsif" | "if" | "either" | "or" | "while" | "with" | "call" | "return" | "goto" | "print" | "assert"
            | "skip" | "procedure" | "define" | "process" | "fair"
    )
}

impl Run<'_> {
    fn skip_next_char(&mut self) {
        self.ncol = self.reader.column_number();
        self.next_char = self.reader.next_char();
    }
    fn add_next_char(&mut self) {
        self.token.push(self.next_char);
        self.skip_next_char();
    }
    fn start_new_line(&mut self) {
        let l = std::mem::take(&mut self.linev);
        self.vspec.push(l);
        self.col = 0;
    }
    fn error(&self, msg: &str) -> String {
        format!("{} `{}' found at\n    line {}, column {}", msg, self.token, self.reader.line_number() + 1, self.col + 1)
    }
    fn set_delimiter(&mut self) {
        self.expr_end = true;
        self.delimiter = self.token.clone();
        self.delimiter_col = self.col;
        self.delimiter_line = self.reader.line_number();
        if self.next_char == NL {
            self.delimiter_line -= 1;
        }
    }
    fn token_out(&mut self, typ: i32) -> Result<(), String> {
        if !self.parse_expression {
            self.set_delimiter();
            self.token.clear();
            return Ok(());
        }
        if !(typ == BUILTIN || typ == NUMBER || typ == STRING || typ == IDENT) {
            return Err(self.error("Illegal token in an expression"));
        }
        let t = self.token.as_str();
        let ends = typ != STRING
            && ((is_delimiter(t) && !(typ == IDENT && (self.prev_token == "." || self.prev_token == "[" || self.prev_token == ",")))
                || (((t == "," && !self.in_quantifier && !self.in_define_block) || t == ")" || t == "}") && self.paren_depth == 0));
        if ends {
            if self.paren_depth != 0 {
                return Err(self.error("Expression with an unmatched (, [, {, or << followed by"));
            }
            if self.in_quantifier {
                return Err(self.error("Expression with \\A or \\E but no following `:` followed by"));
            }
            self.set_delimiter();
            if !self.linev.is_empty() {
                self.start_new_line();
            }
            return Ok(());
        }
        if typ == BUILTIN {
            match builtin_kind(t) {
                Some(1) => self.paren_depth += 1,
                Some(2) => {
                    self.paren_depth -= 1;
                    if self.paren_depth < 0 {
                        return Err(self.error("Extra (unmatching)"));
                    }
                }
                _ => {}
            }
        }
        self.prev_token = if typ == STRING { " ".to_string() } else { self.token.clone() };
        if (self.token == "\\A" || self.token == "\u{2200}" || self.token == "\\E" || self.token == "\u{2203}") && self.paren_depth == 0 {
            self.in_quantifier = true;
        }
        if self.in_quantifier && self.token == ":" && self.paren_depth == 0 {
            self.in_quantifier = false;
        }
        if !self.token.is_empty() || typ == STRING {
            self.linev.push(tok(&self.token, self.col, typ));
        }
        self.token.clear();
        Ok(())
    }
    fn goto_start(&mut self) -> St {
        self.col = self.ncol;
        St::Start
    }
}

impl Tokenizer {
    pub fn new() -> Self {
        Tokenizer { delimiter: String::new(), delimiter_line: 0, delimiter_col: 0, cdepth: 0, in_define_block: false }
    }
    pub fn tokenize_expr(&mut self, r: &mut CharReader) -> Result<Expr, String> {
        self.inner(r, true)
    }
    pub fn tokenize_define_block(&mut self, r: &mut CharReader) -> Result<Expr, String> {
        let saved = self.in_define_block;
        self.in_define_block = true;
        let res = self.inner(r, true);
        self.in_define_block = saved;
        res
    }
    pub fn get_algorithm_token(&mut self, r: &mut CharReader) -> Result<String, String> {
        self.inner(r, false)?;
        Ok(self.delimiter.clone())
    }

    fn inner(&mut self, reader: &mut CharReader, is_expr: bool) -> Result<Expr, String> {
        let ncol = reader.column_number();
        let first = reader.next_char();
        let mut x = Run {
            reader,
            vspec: vec![],
            linev: vec![],
            next_char: first,
            token: String::new(),
            paren_depth: 0,
            in_quantifier: false,
            col: ncol,
            ncol,
            parse_expression: is_expr,
            in_define_block: self.in_define_block,
            prev_token: " ".to_string(),
            expr_end: false,
            delimiter: self.delimiter.clone(),
            delimiter_line: self.delimiter_line,
            delimiter_col: self.delimiter_col,
        };
        let mut cdepth = self.cdepth;
        let mut state = St::Start;
        let res: Result<(), String> = (|| {
            while state != St::Done && !x.expr_end {
                let c = x.next_char;
                match state {
                    St::Start => {
                        if is_space(c) {
                            x.skip_next_char();
                            state = x.goto_start();
                        } else if is_letter(c) {
                            x.add_next_char();
                            state = St::Id;
                        } else if c == '\u{2115}' || c == '\u{2124}' || c == '\u{211D}' {
                            x.add_next_char();
                            x.token_out(IDENT)?;
                            state = x.goto_start();
                        } else if is_digit(c) {
                            x.add_next_char();
                            state = St::NumOrId;
                        } else if c == '\\' {
                            x.add_next_char();
                            state = St::Bs;
                        } else if c == '-' {
                            x.add_next_char();
                            state = St::Dash1;
                        } else if c == '=' {
                            x.add_next_char();
                            state = St::Eq1;
                        } else if c == '(' {
                            x.skip_next_char();
                            state = St::LeftParen;
                        } else if c == '"' {
                            x.skip_next_char();
                            state = St::Str;
                        } else if c == NL {
                            x.skip_next_char();
                            x.start_new_line();
                            state = x.goto_start();
                        } else if is_builtin_prefix(&c.to_string()) {
                            x.add_next_char();
                            state = St::BuiltIn;
                        } else if c == TAB {
                            state = St::Done;
                        } else {
                            x.add_next_char();
                            return Err(x.error("Illegal lexeme"));
                        }
                    }
                    St::Id => {
                        if x.token == "WF_" || x.token == "SF_" {
                            x.token_out(BUILTIN)?;
                            state = x.goto_start();
                        } else if is_letter(c) || is_digit(c) {
                            x.add_next_char();
                        } else if is_builtin_symbol(&x.token) {
                            x.token_out(BUILTIN)?;
                            state = x.goto_start();
                        } else {
                            x.token_out(IDENT)?;
                            state = x.goto_start();
                        }
                    }
                    St::NumOrId => {
                        if is_digit(c) {
                            x.add_next_char();
                        } else if is_letter(c) {
                            x.add_next_char();
                            state = St::Id;
                        } else {
                            x.token_out(NUMBER)?;
                            state = x.goto_start();
                        }
                    }
                    St::Bs => {
                        if matches!(c, 'b' | 'B' | 'o' | 'O' | 'h' | 'H') {
                            x.add_next_char();
                            state = St::NumOrBi;
                        } else if is_letter(c) {
                            state = St::BsBuiltIn;
                        } else if c == '*' {
                            x.skip_next_char();
                            x.token.clear();
                            state = St::LineComment;
                        } else {
                            state = St::BuiltIn;
                        }
                    }
                    St::NumOrBi => {
                        state = if is_digit(c) { St::Num } else { St::BsBuiltIn };
                    }
                    St::Num => {
                        if is_digit(c) {
                            x.add_next_char();
                        } else if is_letter(c) {
                            x.add_next_char();
                            if x.token.starts_with('\\') {
                                return Err(x.error("Illegal lexeme"));
                            }
                            state = St::Id;
                        } else {
                            x.token_out(NUMBER)?;
                            state = x.goto_start();
                        }
                    }
                    St::BsBuiltIn => {
                        if is_letter(c) && c != '_' {
                            x.add_next_char();
                        } else if is_builtin_symbol(&x.token) {
                            x.token_out(BUILTIN)?;
                            state = x.goto_start();
                        } else {
                            return Err(x.error("Illegal lexeme "));
                        }
                    }
                    St::BuiltIn => {
                        let mut longer = x.token.clone();
                        longer.push(c);
                        if is_builtin_prefix(&longer) {
                            x.add_next_char();
                        } else {
                            if !is_builtin_symbol(&x.token) {
                                x.reader.backspace();
                                while !is_builtin_symbol(&x.token) {
                                    x.reader.backspace();
                                    if x.token.is_empty() {
                                        return Err(x.error("Illegal lexeme"));
                                    }
                                    x.token.pop();
                                }
                                x.skip_next_char();
                            }
                            x.token_out(BUILTIN)?;
                            state = x.goto_start();
                        }
                    }
                    St::Dash1 | St::Dash2 => {
                        if c == '-' {
                            x.add_next_char();
                            state = if state == St::Dash1 { St::Dash2 } else { St::Dash3 };
                        } else {
                            state = St::BuiltIn;
                        }
                    }
                    St::Dash3 => {
                        if c == '-' {
                            x.add_next_char();
                            state = St::Dashes;
                        } else {
                            return Err(x.error("Illegal lexeme"));
                        }
                    }
                    St::Dashes => {
                        if c == '-' {
                            x.add_next_char();
                        } else {
                            x.token_out(T_DASHES)?;
                            state = x.goto_start();
                        }
                    }
                    St::Eq1 | St::Eq2 => {
                        if c == '=' {
                            x.add_next_char();
                            state = if state == St::Eq1 { St::Eq2 } else { St::Eq3 };
                        } else {
                            state = St::BuiltIn;
                        }
                    }
                    St::Eq3 => {
                        if c == '=' {
                            x.add_next_char();
                            state = St::Eqs;
                        } else {
                            return Err(x.error("Illegal lexeme"));
                        }
                    }
                    St::Eqs => {
                        if c == '=' {
                            x.add_next_char();
                        } else {
                            x.token_out(T_END_MODULE)?;
                            state = x.goto_start();
                        }
                    }
                    St::LeftParen => {
                        if c == '*' {
                            x.skip_next_char();
                            cdepth = 1;
                            state = St::Comment;
                        } else {
                            x.token = "(".to_string();
                            state = St::BuiltIn;
                        }
                    }
                    St::Str => {
                        if c == '\\' {
                            x.add_next_char();
                            state = St::EscStr;
                        } else if c == '"' {
                            x.skip_next_char();
                            x.token_out(STRING)?;
                            state = x.goto_start();
                        } else if is_string_char(c) {
                            x.add_next_char();
                        } else {
                            x.add_next_char();
                            return Err(x.error("Illegal character in string"));
                        }
                    }
                    St::EscStr => {
                        if matches!(c, '"' | '\\' | 't' | 'n' | 'f' | 'r') {
                            x.add_next_char();
                            state = St::Str;
                        } else {
                            x.add_next_char();
                            return Err(x.error("Illegal character following \\ in string"));
                        }
                    }
                    St::LineComment => {
                        if c == '(' {
                            x.skip_next_char();
                            state = St::LineComParen;
                        } else if c == '*' && cdepth > 0 {
                            x.skip_next_char();
                            state = St::LineComStar;
                        } else if c == NL || c == TAB {
                            x.token.clear();
                            cdepth = 0;
                            state = x.goto_start();
                        } else if cdepth == 0 {
                            x.add_next_char();
                        } else {
                            x.skip_next_char();
                        }
                    }
                    St::LineComParen => {
                        if c == '*' {
                            x.skip_next_char();
                            cdepth += 1;
                        } else if cdepth == 0 {
                            x.token.push('(');
                        }
                        state = St::LineComment;
                    }
                    St::LineComStar => {
                        if c == ')' {
                            x.skip_next_char();
                            cdepth -= 1;
                        } else if cdepth == 0 {
                            x.token.push('*');
                        }
                        state = St::LineComment;
                    }
                    St::Comment | St::OrComment => {
                        if c == '*' {
                            x.skip_next_char();
                            state = if state == St::Comment { St::CommentStar } else { St::OrCommentStar };
                        } else if c == '(' {
                            x.skip_next_char();
                            state = if state == St::Comment { St::CommentParen } else { St::OrCommentParen };
                        } else if c == NL {
                            x.token.clear();
                            x.skip_next_char();
                            x.start_new_line();
                            state = St::OrComment;
                        } else if c == TAB {
                            return Err(if state == St::Comment { "Input ended in the middle of a comment" } else { "Input ended in the middle of a multi-line comment" }.to_string());
                        } else if cdepth == 1 {
                            x.add_next_char();
                        } else {
                            x.skip_next_char();
                        }
                    }
                    St::CommentStar | St::OrCommentStar => {
                        let back = if state == St::CommentStar { St::Comment } else { St::OrComment };
                        if c == ')' {
                            x.skip_next_char();
                            cdepth -= 1;
                            if cdepth == 0 {
                                x.token.clear();
                                state = x.goto_start();
                            } else {
                                state = back;
                            }
                        } else {
                            if cdepth == 1 {
                                x.token.push('*');
                            }
                            state = back;
                        }
                    }
                    St::CommentParen | St::OrCommentParen => {
                        let back = if state == St::CommentParen { St::Comment } else { St::OrComment };
                        if c == '*' {
                            x.skip_next_char();
                            cdepth += 1;
                        } else if cdepth == 1 {
                            x.token.push('(');
                        }
                        state = back;
                    }
                    St::Done => {}
                }
            }
            Ok(())
        })();
        self.cdepth = cdepth;
        self.delimiter = x.delimiter.clone();
        self.delimiter_line = x.delimiter_line;
        self.delimiter_col = x.delimiter_col;
        res?;
        if x.next_char != NL {
            x.reader.backspace();
        }
        let e = expr_from(std::mem::take(&mut x.vspec));
        e.borrow_mut().normalize();
        Ok(e)
    }
}
