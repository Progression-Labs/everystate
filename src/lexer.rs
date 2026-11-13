//! TLA+ lexer: produces a flat token array for one source file.
use crate::intern::*;
use std::rc::Rc;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum T {
    Id,
    Num,
    Str,
    Op,
    Kw,
    Step,
    Sep,
    End,
    Eof,
    Bad,
}

#[derive(Clone, Debug)]
pub struct Tok {
    pub t: T,
    pub v: Rc<str>,
    pub line: u32,
    pub col: u32,
    pub ec: u32,
    pub n: i64,
    pub stop: bool,
}

const KEYWORDS: &[&str] = &[
    "ASSUME", "ASSUMPTION", "AXIOM", "CASE", "CHOOSE", "CONSTANT", "CONSTANTS", "DOMAIN", "ELSE", "ENABLED", "EXCEPT",
    "EXTENDS", "IF", "IN", "INSTANCE", "LET", "LOCAL", "MODULE", "OTHER", "SUBSET", "THEN", "THEOREM", "UNCHANGED",
    "UNION", "VARIABLE", "VARIABLES", "WITH", "LAMBDA", "RECURSIVE", "PROPOSITION", "LEMMA", "COROLLARY", "BY",
    "OBVIOUS", "OMITTED", "PROOF", "QED", "HAVE", "TAKE", "WITNESS", "PICK", "SUFFICES", "PROVE", "DEFINE", "DEF",
    "DEFS", "USE", "HIDE", "ONLY", "NEW", "STATE", "ACTION", "TEMPORAL", "TRUE", "FALSE",
];

// Symbol tokens, longest first.
const SYMBOLS: &[&str] = &[
    "-+->", "(\\X)", "<=>", "...", "::=", "|->", "(+)", "(-)", "(.)", "(/)", ">>_", "=>", "~>", "->", "<-", "==", "=<",
    "<=", ">=", "/=", "/\\", "..", ":=", "::", ":>", "<:", "@@", "!!", "##", "$$", "??", "%%", "&&", "**", "++", "--",
    "//", "^^", "||", "|-", "|=", "-|", "=|", "<<", ">>", "]_", "[]", "<>", "^+", "^*", "^#", "-.", "~", "=", "<", ">",
    "#", "$", "%", "&", "*", "+", "-", "/", "^", "|", "(", ")", "[", "]", "{", "}", ",", ":", ";", ".", "!", "@", "_",
    "'",
];

fn canon(s: &str) -> &str {
    match s {
        "\\land" => "/\\",
        "\\lor" => "\\/",
        "\\lnot" | "\\neg" => "~",
        "\\equiv" => "<=>",
        "#" | "\\neq" => "/=",
        "=<" | "\\leq" => "<=",
        "\\geq" => ">=",
        "\\union" => "\\cup",
        "\\intersect" => "\\cap",
        "\\times" => "\\X",
        "\\circ" => "\\o",
        "(+)" => "\\oplus",
        "(-)" => "\\ominus",
        "(.)" => "\\odot",
        "(/)" => "\\oslash",
        "(\\X)" => "\\otimes",
        "\\forall" => "\\A",
        "\\exists" => "\\E",
        _ => s,
    }
}

fn unicode(c: char) -> Option<&'static str> {
    Some(match c {
        '∧' => "/\\",
        '∨' => "\\/",
        '¬' => "~",
        '∈' => "\\in",
        '∉' => "\\notin",
        '⇒' => "=>",
        '≡' | '⇔' => "<=>",
        '≠' => "/=",
        '≤' => "<=",
        '≥' => ">=",
        '∪' => "\\cup",
        '∩' => "\\cap",
        '⊆' => "\\subseteq",
        '×' => "\\X",
        '∀' => "\\A",
        '∃' => "\\E",
        '□' => "[]",
        '◇' => "<>",
        '↦' => "|->",
        '→' => "->",
        '←' => "<-",
        '≜' => "==",
        '⟨' => "<<",
        '⟩' => ">>",
        '∘' => "\\o",
        '÷' => "\\div",
        '⊂' => "\\subset",
        '⊃' => "\\supset",
        '⊇' => "\\supseteq",
        '↝' => "~>",
        '‥' => "..",
        '⋅' => "\\cdot",
        _ => return None,
    })
}

fn is_alpha(c: char) -> bool {
    c.is_ascii_alphabetic()
}
fn is_digit(c: char) -> bool {
    c.is_ascii_digit()
}
fn is_id_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

fn starts_with(src: &[char], i: usize, s: &str) -> bool {
    let mut k = i;
    for ch in s.chars() {
        if k >= src.len() || src[k] != ch {
            return false;
        }
        k += 1;
    }
    true
}

/// `intern`: whether identifier / keyword tokens are interned as strings (TLC interns every token image).
pub fn lex(src0: &str, module_name: &str, intern: bool) -> R<Vec<Tok>> {
    let expanded;
    let src_str: &str = if src0.contains('\t') {
        let mut out = String::with_capacity(src0.len() + 64);
        let mut first = true;
        for l in src0.split('\n') {
            if !first {
                out.push('\n');
            }
            first = false;
            if !l.contains('\t') {
                out.push_str(l);
                continue;
            }
            let mut n = 0usize;
            for ch in l.chars() {
                if ch == '\t' {
                    let k = 8 - (n % 8);
                    for _ in 0..k {
                        out.push(' ');
                    }
                    n += k;
                } else {
                    out.push(ch);
                    n += ch.len_utf16();
                }
            }
        }
        expanded = out;
        &expanded
    } else {
        src0
    };
    let src: Vec<char> = src_str.chars().collect();
    let n = src.len();
    let at = |i: usize| -> char { if i < n { src[i] } else { '\0' } };
    let mut toks: Vec<Tok> = Vec::with_capacity(n / 4 + 8);
    let mut i = 0usize;
    let mut line: u32 = 1;
    let mut line_start = 0usize;
    // Skip any prelude before the first module header.
    {
        let mut k = 0;
        'outer: while k < n {
            if src[k] == '-' {
                let s = k;
                while k < n && src[k] == '-' {
                    k += 1;
                }
                if k - s >= 4 {
                    let mut j = k;
                    while j < n && (src[j] == ' ' || src[j] == '\t') {
                        j += 1;
                    }
                    if starts_with(&src, j, "MODULE") && !is_id_char(at(j + 6)) {
                        for (q, ch) in src.iter().enumerate().take(s) {
                            if *ch == '\n' {
                                line += 1;
                                line_start = q + 1;
                            }
                        }
                        i = s;
                        break 'outer;
                    }
                }
            } else {
                k += 1;
            }
        }
    }
    let kw: std::collections::HashSet<&str> = KEYWORDS.iter().copied().collect();
    macro_rules! push {
        ($t:expr, $v:expr, $start:expr, $end:expr, $num:expr) => {
            toks.push(Tok { t: $t, v: Rc::from($v), line, col: ($start - line_start + 1) as u32, ec: ($end - line_start) as u32, n: $num, stop: false })
        };
    }
    while i < n {
        let c = src[i];
        if c == '\n' {
            i += 1;
            line += 1;
            line_start = i;
            continue;
        }
        if c == ' ' || c == '\t' || c == '\r' || c == '\x0c' {
            i += 1;
            continue;
        }
        // comments
        if c == '\\' && at(i + 1) == '*' {
            while i < n && src[i] != '\n' {
                i += 1;
            }
            continue;
        }
        if c == '(' && at(i + 1) == '*' {
            let mut depth = 1;
            i += 2;
            while i < n && depth > 0 {
                let d = src[i];
                if d == '\n' {
                    line += 1;
                    line_start = i + 1;
                    i += 1;
                } else if d == '(' && at(i + 1) == '*' {
                    depth += 1;
                    i += 2;
                } else if d == '*' && at(i + 1) == ')' {
                    depth -= 1;
                    i += 2;
                } else {
                    i += 1;
                }
            }
            continue;
        }
        let start = i;
        if c == '-' && starts_with(&src, i, "----") {
            while i < n && src[i] == '-' {
                i += 1;
            }
            push!(T::Sep, "----", start, i, 0);
            continue;
        }
        if c == '=' && starts_with(&src, i, "====") {
            while i < n && src[i] == '=' {
                i += 1;
            }
            push!(T::End, "====", start, i, 0);
            continue;
        }
        if c == '"' {
            i += 1;
            let mut s = String::new();
            while i < n && src[i] != '"' {
                if src[i] == '\\' {
                    let e = at(i + 1);
                    s.push(match e {
                        'n' => '\n',
                        't' => '\t',
                        'r' => '\r',
                        'f' => '\x0c',
                        _ => e,
                    });
                    i += 2;
                } else if src[i] == '\n' {
                    return Err(Box::new(Fail::Tla(TlaError {
                        msg: "Unterminated string".into(),
                        loc: Some([line, (start - line_start + 1) as u32, line, (i - line_start) as u32]),
                        module: Some(module_name.to_string()),
                        kind: "parse",
                    })));
                } else {
                    s.push(src[i]);
                    i += 1;
                }
            }
            i += 1;
            push!(T::Str, s.as_str(), start, i, 0);
            continue;
        }
        if is_id_char(c) {
            while i < n && is_id_char(src[i]) {
                i += 1;
            }
            let mut word: String = src[start..i].iter().collect();
            if word.chars().all(is_digit) {
                if at(i) == '.' && is_digit(at(i + 1)) {
                    i += 1;
                    while i < n && is_digit(src[i]) {
                        i += 1;
                    }
                    word = src[start..i].iter().collect();
                    let f: f64 = word.parse().unwrap_or(0.0);
                    push!(T::Num, word.as_str(), start, i, f as i64);
                } else {
                    let v: i64 = word.parse().unwrap_or(i64::MAX);
                    push!(T::Num, word.as_str(), start, i, v);
                }
                continue;
            }
            if word.starts_with("WF_") || word.starts_with("SF_") {
                i = start + 3;
                push!(T::Kw, &word[0..3], start, i, 0);
                continue;
            }
            if word == "_" {
                push!(T::Op, "_", start, i, 0);
                continue;
            }
            if intern {
                str_id(&word);
            }
            let t = if kw.contains(word.as_str()) { T::Kw } else { T::Id };
            push!(t, word.as_str(), start, i, 0);
            continue;
        }
        if c == '\\' {
            let nx = at(i + 1);
            if nx == '/' {
                i += 2;
                push!(T::Op, "\\/", start, i, 0);
                continue;
            }
            if matches!(nx, 'b' | 'B' | 'o' | 'O' | 'h' | 'H') && at(i + 2).is_ascii_hexdigit() {
                let radix = match nx {
                    'b' | 'B' => 2,
                    'o' | 'O' => 8,
                    _ => 16,
                };
                let mut j = i + 2;
                while j < n && src[j].is_digit(radix) {
                    j += 1;
                }
                if j > i + 2 && !is_id_char(at(j)) {
                    let digits: String = src[i + 2..j].iter().collect();
                    let v = i64::from_str_radix(&digits, radix).unwrap_or(i64::MAX);
                    i = j;
                    push!(T::Num, v.to_string().as_str(), start, i, v);
                    continue;
                }
            }
            if is_alpha(nx) {
                i += 1;
                while i < n && is_alpha(src[i]) {
                    i += 1;
                }
                let w: String = src[start..i].iter().collect();
                push!(T::Op, canon(&w), start, i, 0);
                continue;
            }
            i += 1;
            push!(T::Op, "\\", start, i, 0);
            continue;
        }
        // proof step tokens: <1>, <1>2., <*>, <+>
        if c == '<' {
            let mut j = i + 1;
            let mut ok = false;
            if at(j) == '*' || at(j) == '+' {
                j += 1;
                ok = true;
            } else if is_digit(at(j)) {
                while is_digit(at(j)) {
                    j += 1;
                }
                ok = true;
            }
            if ok && at(j) == '>' {
                j += 1;
                while is_id_char(at(j)) {
                    j += 1;
                }
                while at(j) == '.' {
                    j += 1;
                }
                let s: String = src[i..j].iter().collect();
                i = j;
                push!(T::Step, s.as_str(), start, i, 0);
                continue;
            }
        }
        let mut matched = false;
        for s in SYMBOLS {
            if s.starts_with(c) && starts_with(&src, i, s) {
                i += s.chars().count();
                push!(T::Op, canon(s), start, i, 0);
                matched = true;
                break;
            }
        }
        if matched {
            continue;
        }
        if let Some(u) = unicode(c) {
            i += 1;
            push!(T::Op, u, start, i, 0);
            continue;
        }
        i += 1;
        let s: String = c.to_string();
        push!(T::Bad, s.as_str(), start, i, 0);
    }
    toks.push(Tok { t: T::Eof, v: Rc::from("<EOF>"), line, col: 0, ec: 0, n: 0, stop: false });
    Ok(toks)
}
