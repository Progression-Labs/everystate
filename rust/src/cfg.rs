//! TLC configuration (.cfg) file parser (port of cfg.ts).
use crate::intern::*;
use crate::value::*;

pub struct ConstDef {
    pub name: String,
    pub value: Option<Value>,
    pub subst: Option<String>,
    pub module: Option<String>,
    pub args: Option<Vec<Value>>,
}

#[derive(Default)]
pub struct Config {
    pub constants: Vec<ConstDef>,
    pub init: Option<String>,
    pub next: Option<String>,
    pub spec: Option<String>,
    pub invariants: Vec<String>,
    pub properties: Vec<String>,
    pub constraints: Vec<String>,
    pub action_constraints: Vec<String>,
    pub symmetry: Option<String>,
    pub view: Option<String>,
    pub alias: Option<String>,
    pub postconditions: Vec<String>,
    pub possible: Vec<String>,
    pub check_deadlock: Option<bool>,
}

fn is_section(s: &str) -> bool {
    matches!(
        s,
        "CONSTANT" | "CONSTANTS" | "INIT" | "NEXT" | "SPECIFICATION" | "INVARIANT" | "INVARIANTS" | "PROPERTY" | "PROPERTIES" | "CONSTRAINT"
            | "CONSTRAINTS" | "ACTION_CONSTRAINT" | "ACTION_CONSTRAINTS" | "SYMMETRY" | "VIEW" | "CHECK_DEADLOCK" | "ALIAS" | "POSTCONDITION"
            | "POSTCONDITIONS" | "_POSSIBLE" | "_PERIODIC" | "_RL_REWARD" | "TYPE" | "TYPE_CONSTRAINT"
    )
}

const OPCHARS: &str = "+-*/^&|%$#?@<>:.~=";
fn opcanon(s: &str) -> &str {
    match s {
        "\\circ" => "\\o",
        "\\leq" | "=<" => "<=",
        "\\geq" => ">=",
        "#" | "\\neq" => "/=",
        "\\union" => "\\cup",
        "\\intersect" => "\\cap",
        "\\mod" => "%",
        _ => s,
    }
}

#[derive(PartialEq, Clone, Copy)]
enum CT {
    Id,
    Num,
    Str,
    Sym,
    Eof,
}
struct CTok {
    t: CT,
    v: String,
    line: u32,
}

fn tokenize(src: &str) -> Vec<CTok> {
    let s: Vec<char> = src.chars().collect();
    let n = s.len();
    let at = |i: usize| -> char { if i < n { s[i] } else { '\0' } };
    let mut out = vec![];
    let (mut i, mut line) = (0usize, 1u32);
    while i < n {
        let c = s[i];
        if c == '\n' {
            line += 1;
            i += 1;
            continue;
        }
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        if c == '\\' && at(i + 1) == '*' {
            while i < n && s[i] != '\n' {
                i += 1;
            }
            continue;
        }
        if c == '(' && at(i + 1) == '*' {
            let mut depth = 1;
            i += 2;
            while i < n && depth > 0 {
                if s[i] == '\n' {
                    line += 1;
                }
                if s[i] == '(' && at(i + 1) == '*' {
                    depth += 1;
                    i += 2;
                } else if s[i] == '*' && at(i + 1) == ')' {
                    depth -= 1;
                    i += 2;
                } else {
                    i += 1;
                }
            }
            continue;
        }
        if c == '"' {
            let mut j = i + 1;
            let mut st = String::new();
            while j < n && s[j] != '"' {
                if s[j] == '\\' {
                    j += 1;
                }
                if j < n {
                    st.push(s[j]);
                }
                j += 1;
            }
            out.push(CTok { t: CT::Str, v: st, line });
            i = j + 1;
            continue;
        }
        // /^-?\d+(?![A-Za-z_])/
        {
            let mut j = i;
            if at(j) == '-' {
                j += 1;
            }
            let ds = j;
            while at(j).is_ascii_digit() {
                j += 1;
            }
            if j > ds {
                let follow = at(j);
                if follow.is_ascii_alphabetic() || follow == '_' {
                    j -= 1; // backtrack one digit: the lookahead then sees a digit
                }
                if j > ds {
                    out.push(CTok { t: CT::Num, v: s[i..j].iter().collect(), line });
                    i = j;
                    continue;
                }
            }
        }
        if c.is_ascii_alphanumeric() || c == '_' || c == '!' {
            let mut j = i;
            while at(j).is_ascii_alphanumeric() || at(j) == '_' || at(j) == '!' {
                j += 1;
            }
            out.push(CTok { t: CT::Id, v: s[i..j].iter().collect(), line });
            i = j;
            continue;
        }
        if c == '<' && at(i + 1) == '-' {
            out.push(CTok { t: CT::Sym, v: "<-".into(), line });
            i += 2;
            continue;
        }
        // operator symbols (e.g. `++ <- PlusPlus`, `\o <- +`)
        if c == '\\' && at(i + 1).is_ascii_alphabetic() {
            let mut j = i + 1;
            while at(j).is_ascii_alphabetic() {
                j += 1;
            }
            let w: String = s[i..j].iter().collect();
            out.push(CTok { t: CT::Id, v: opcanon(&w).to_string(), line });
            i = j;
            continue;
        }
        if c != '=' && OPCHARS.contains(c) {
            let mut j = i;
            while j < n && OPCHARS.contains(s[j]) && !(s[j] == '<' && at(j + 1) == '-' && j > i) {
                j += 1;
            }
            let sym: String = s[i..j].iter().collect();
            if sym != "<" || at(j) != '-' {
                out.push(CTok { t: CT::Id, v: opcanon(&sym).to_string(), line });
                i = j;
                continue;
            }
        }
        out.push(CTok { t: CT::Sym, v: c.to_string(), line });
        i += 1;
    }
    out.push(CTok { t: CT::Eof, v: "<EOF>".into(), line });
    out
}

struct P {
    toks: Vec<CTok>,
    p: usize,
}
impl P {
    fn fail<T>(&self, msg: String) -> R<T> {
        err("config", format!("TLC found an error in the configuration file at line {}\n{}", self.toks[self.p.min(self.toks.len() - 1)].line, msg))
    }
    fn t(&self) -> &CTok {
        &self.toks[self.p.min(self.toks.len() - 1)]
    }
    fn is_sym(&self, v: &str) -> bool {
        self.t().t == CT::Sym && self.t().v == v
    }
    fn is_sec(&self) -> bool {
        self.t().t == CT::Id && is_section(&self.t().v)
    }
    fn parse_value(&mut self) -> R<Value> {
        let (t, v) = (self.t().t, self.t().v.clone());
        self.p += 1;
        match t {
            CT::Num => return Ok(Value::Int(v.parse().unwrap_or(0))),
            CT::Str => return Ok(Value::Str(str_id(&v))),
            CT::Id => {
                return Ok(match v.as_str() {
                    "TRUE" => Value::Bool(true),
                    "FALSE" => Value::Bool(false),
                    _ => Value::Model(str_id(&v)),
                })
            }
            CT::Sym if v == "{" => {
                let mut items = vec![];
                if self.is_sym("}") {
                    self.p += 1;
                    return mk_set(items);
                }
                loop {
                    items.push(self.parse_value()?);
                    if self.is_sym("}") {
                        self.p += 1;
                        break;
                    }
                    if !self.is_sym(",") {
                        return self.fail(format!("Expected ',' or '}}' but found '{}'", self.t().v));
                    }
                    self.p += 1;
                }
                return mk_set(items);
            }
            _ => {}
        }
        self.p -= 1;
        self.fail(format!("Unexpected token '{}' in a constant value", v))
    }
    fn names(&mut self, into: &mut Vec<String>) {
        while self.t().t == CT::Id && !self.is_sec() {
            into.push(self.t().v.clone());
            self.p += 1;
        }
    }
    fn one(&mut self, what: &str) -> R<String> {
        if self.t().t != CT::Id || self.is_sec() {
            return self.fail(format!("Expected an identifier after {}", what));
        }
        let v = self.t().v.clone();
        self.p += 1;
        Ok(v)
    }
    fn module_opt(&mut self) -> Option<String> {
        if self.is_sym("[") {
            self.p += 1;
            let m = self.t().v.clone();
            self.p += 2;
            return Some(m);
        }
        None
    }
}

pub fn parse_config(src: &str) -> R<Config> {
    let mut p = P { toks: tokenize(src), p: 0 };
    let mut cfg = Config::default();
    while p.t().t != CT::Eof {
        let kw = p.t().v.clone();
        if !p.is_sec() {
            return p.fail(format!("Unexpected token '{}'; expected a configuration keyword", kw));
        }
        p.p += 1;
        match kw.as_str() {
            "CONSTANT" | "CONSTANTS" => {
                while p.t().t == CT::Id && !p.is_sec() {
                    let name = p.t().v.clone();
                    p.p += 1;
                    let mut args = None;
                    if p.is_sym("(") {
                        p.p += 1;
                        let mut a = vec![];
                        loop {
                            a.push(p.parse_value()?);
                            if p.is_sym(")") {
                                p.p += 1;
                                break;
                            }
                            if !p.is_sym(",") {
                                return p.fail(format!("Expected ',' or ')' but found '{}'", p.t().v));
                            }
                            p.p += 1;
                        }
                        args = Some(a);
                    }
                    if p.is_sym("=") {
                        p.p += 1;
                        let module = p.module_opt();
                        let value = p.parse_value()?;
                        cfg.constants.push(ConstDef { name, value: Some(value), subst: None, module, args });
                    } else if p.is_sym("<-") {
                        p.p += 1;
                        let module = p.module_opt();
                        let subst = p.t().v.clone();
                        p.p += 1;
                        cfg.constants.push(ConstDef { name, value: None, subst: Some(subst), module, args: None });
                    } else {
                        return p.fail(format!("Expected '=' or '<-' after constant {} but found '{}'", name, p.t().v));
                    }
                }
            }
            "INIT" => cfg.init = Some(p.one("INIT")?),
            "NEXT" => cfg.next = Some(p.one("NEXT")?),
            "SPECIFICATION" => cfg.spec = Some(p.one("SPECIFICATION")?),
            "INVARIANT" | "INVARIANTS" => p.names(&mut cfg.invariants),
            "PROPERTY" | "PROPERTIES" => p.names(&mut cfg.properties),
            "CONSTRAINT" | "CONSTRAINTS" => p.names(&mut cfg.constraints),
            "ACTION_CONSTRAINT" | "ACTION_CONSTRAINTS" => p.names(&mut cfg.action_constraints),
            "SYMMETRY" => cfg.symmetry = Some(p.one("SYMMETRY")?),
            "VIEW" => cfg.view = Some(p.one("VIEW")?),
            "ALIAS" => cfg.alias = Some(p.one("ALIAS")?),
            "POSTCONDITION" | "POSTCONDITIONS" => p.names(&mut cfg.postconditions),
            "_POSSIBLE" => p.names(&mut cfg.possible),
            "CHECK_DEADLOCK" => {
                let v = p.one("CHECK_DEADLOCK")?;
                cfg.check_deadlock = Some(v == "TRUE");
            }
            _ => p.names(&mut vec![]),
        }
    }
    Ok(cfg)
}
