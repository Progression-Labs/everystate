//! Trace conformance: is a recorded run of the real system a behaviour of the specification?
//!
//! `everystate conform -trace run.jsonl Spec.tla` reads observations (one JSON object per line, or one
//! JSON array of them) and tracks the set of all spec states that are consistent with the observations
//! so far: the initial states matching the first observation, then, for every further observation, the
//! `Next`-successors of the current set that match it. The trace conforms when the set is not empty at
//! the end. Observations may leave variables out (they are then unconstrained), and may name the action
//! that happened.
//!
//! An observation is `{"action": "Handle", "params": [..], "state": {"var": value, ..}}`; every key is
//! optional and other keys (timestamps, messages) are ignored. JSON values are matched against the
//! candidate state's actual TLA+ value (see `matches`), never converted on a guess.
use crate::checker::{CheckOptions, Checker};
use crate::cli::{action_label, basename, dirname, file_resolver, path_join, path_resolve, setup_error_json, state_text};
use crate::eval::StateRef;
use crate::host::HostRef;
use crate::intern::*;
use crate::model::*;
use crate::value::*;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

/// Exit status when the trace is not a behaviour of the spec.
pub const EXIT_MISMATCH: i32 = 20;
/// Exit status when the trace file cannot be read or is malformed.
pub const EXIT_TRACE_ERROR: i32 = 21;
/// Exit status when too many spec states are consistent with the trace to continue (see `-limit`).
pub const EXIT_LIMIT: i32 = 22;

// ---------------------------------------------------------------------------------------------
// JSON
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    /// A number with an integral value that fits in 64 bits.
    Int(i64),
    /// Any other number (it matches no TLA+ value).
    Num(f64),
    Str(String),
    Arr(Vec<Json>),
    Obj(Vec<(String, Json)>),
}

impl Json {
    pub fn write(&self, o: &mut String) {
        match self {
            Json::Null => o.push_str("null"),
            Json::Bool(b) => o.push_str(if *b { "true" } else { "false" }),
            Json::Int(i) => o.push_str(&i.to_string()),
            Json::Num(n) => o.push_str(&if n.is_finite() { format!("{}", n) } else { "null".to_string() }),
            Json::Str(s) => json_str(s, o),
            Json::Arr(a) => {
                o.push('[');
                for (i, x) in a.iter().enumerate() {
                    if i > 0 {
                        o.push(',');
                    }
                    x.write(o);
                }
                o.push(']');
            }
            Json::Obj(a) => {
                o.push('{');
                for (i, (k, x)) in a.iter().enumerate() {
                    if i > 0 {
                        o.push(',');
                    }
                    json_str(k, o);
                    o.push(':');
                    x.write(o);
                }
                o.push('}');
            }
        }
    }
    pub fn text(&self) -> String {
        let mut o = String::new();
        self.write(&mut o);
        o
    }
    fn get(&self, key: &str) -> Option<&Json> {
        match self {
            Json::Obj(a) => a.iter().find(|(k, _)| k == key).map(|(_, v)| v),
            _ => None,
        }
    }
}

fn json_str(s: &str, o: &mut String) {
    o.push('"');
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            '\n' => o.push_str("\\n"),
            '\r' => o.push_str("\\r"),
            '\t' => o.push_str("\\t"),
            c if (c as u32) < 0x20 => o.push_str(&format!("\\u{:04x}", c as u32)),
            c => o.push(c),
        }
    }
    o.push('"');
}

/// A JSON syntax error: message and 1-based line.
#[derive(Debug, Clone)]
pub struct JsonError {
    pub message: String,
    pub line: usize,
}

struct JsonParser<'a> {
    b: &'a [u8],
    pos: usize,
    line: usize,
}

impl<'a> JsonParser<'a> {
    fn new(text: &'a str, line: usize) -> Self {
        JsonParser { b: text.as_bytes(), pos: 0, line }
    }
    fn fail<T>(&self, message: &str) -> Result<T, JsonError> {
        Err(JsonError { message: message.to_string(), line: self.line })
    }
    fn ws(&mut self) {
        while self.pos < self.b.len() {
            match self.b[self.pos] {
                b'\n' => self.line += 1,
                b' ' | b'\t' | b'\r' => {}
                _ => break,
            }
            self.pos += 1;
        }
    }
    fn peek(&self) -> Option<u8> {
        self.b.get(self.pos).copied()
    }
    fn lit(&mut self, word: &str, v: Json) -> Result<Json, JsonError> {
        if self.b[self.pos..].starts_with(word.as_bytes()) {
            self.pos += word.len();
            Ok(v)
        } else {
            self.fail("invalid JSON value")
        }
    }
    fn value(&mut self, depth: u32) -> Result<Json, JsonError> {
        if depth > 256 {
            return self.fail("JSON is nested too deeply");
        }
        self.ws();
        match self.peek() {
            None => self.fail("unexpected end of JSON"),
            Some(b'n') => self.lit("null", Json::Null),
            Some(b't') => self.lit("true", Json::Bool(true)),
            Some(b'f') => self.lit("false", Json::Bool(false)),
            Some(b'"') => Ok(Json::Str(self.string()?)),
            Some(b'[') => {
                self.pos += 1;
                let mut items = vec![];
                self.ws();
                if self.peek() == Some(b']') {
                    self.pos += 1;
                    return Ok(Json::Arr(items));
                }
                loop {
                    items.push(self.value(depth + 1)?);
                    self.ws();
                    match self.peek() {
                        Some(b',') => self.pos += 1,
                        Some(b']') => {
                            self.pos += 1;
                            return Ok(Json::Arr(items));
                        }
                        _ => return self.fail("expected ',' or ']' in a JSON array"),
                    }
                }
            }
            Some(b'{') => {
                self.pos += 1;
                let mut items = vec![];
                self.ws();
                if self.peek() == Some(b'}') {
                    self.pos += 1;
                    return Ok(Json::Obj(items));
                }
                loop {
                    self.ws();
                    if self.peek() != Some(b'"') {
                        return self.fail("expected a string key in a JSON object");
                    }
                    let k = self.string()?;
                    self.ws();
                    if self.peek() != Some(b':') {
                        return self.fail("expected ':' after a JSON object key");
                    }
                    self.pos += 1;
                    let v = self.value(depth + 1)?;
                    items.push((k, v));
                    self.ws();
                    match self.peek() {
                        Some(b',') => self.pos += 1,
                        Some(b'}') => {
                            self.pos += 1;
                            return Ok(Json::Obj(items));
                        }
                        _ => return self.fail("expected ',' or '}' in a JSON object"),
                    }
                }
            }
            Some(c) if c == b'-' || c.is_ascii_digit() => self.number(),
            Some(_) => self.fail("invalid JSON value"),
        }
    }
    fn number(&mut self) -> Result<Json, JsonError> {
        let start = self.pos;
        let mut integral = true;
        if self.peek() == Some(b'-') {
            self.pos += 1;
        }
        while let Some(c) = self.peek() {
            match c {
                b'0'..=b'9' => {}
                b'.' | b'e' | b'E' | b'+' | b'-' => integral = false,
                _ => break,
            }
            self.pos += 1;
        }
        let t = std::str::from_utf8(&self.b[start..self.pos]).unwrap_or("");
        if integral {
            if let Ok(i) = t.parse::<i64>() {
                return Ok(Json::Int(i));
            }
        }
        match t.parse::<f64>() {
            // 1.0 and 1e3 are integers; anything larger than 2^53 written as a float has lost digits
            Ok(f) if !integral && f.fract() == 0.0 && f.abs() <= 9007199254740992.0 => Ok(Json::Int(f as i64)),
            Ok(f) => Ok(Json::Num(f)),
            Err(_) => self.fail("invalid JSON number"),
        }
    }
    fn hex4(&mut self) -> Result<u32, JsonError> {
        if self.pos + 4 > self.b.len() {
            return self.fail("invalid \\u escape in a JSON string");
        }
        let t = std::str::from_utf8(&self.b[self.pos..self.pos + 4]).unwrap_or("");
        match u32::from_str_radix(t, 16) {
            Ok(v) => {
                self.pos += 4;
                Ok(v)
            }
            Err(_) => self.fail("invalid \\u escape in a JSON string"),
        }
    }
    fn string(&mut self) -> Result<String, JsonError> {
        self.pos += 1; // opening quote
        let mut out: Vec<u8> = vec![];
        loop {
            let c = match self.peek() {
                Some(c) => c,
                None => return self.fail("unterminated JSON string"),
            };
            self.pos += 1;
            match c {
                b'"' => break,
                b'\n' => return self.fail("unterminated JSON string"),
                b'\\' => {
                    let e = match self.peek() {
                        Some(e) => e,
                        None => return self.fail("unterminated JSON string"),
                    };
                    self.pos += 1;
                    let ch = match e {
                        b'"' => '"',
                        b'\\' => '\\',
                        b'/' => '/',
                        b'b' => '\x08',
                        b'f' => '\x0c',
                        b'n' => '\n',
                        b'r' => '\r',
                        b't' => '\t',
                        b'u' => {
                            let mut cp = self.hex4()?;
                            if (0xD800..0xDC00).contains(&cp) && self.b[self.pos..].starts_with(b"\\u") {
                                self.pos += 2;
                                let lo = self.hex4()?;
                                if (0xDC00..0xE000).contains(&lo) {
                                    cp = 0x10000 + ((cp - 0xD800) << 10) + (lo - 0xDC00);
                                }
                            }
                            char::from_u32(cp).unwrap_or('\u{FFFD}')
                        }
                        _ => return self.fail("invalid escape in a JSON string"),
                    };
                    let mut buf = [0u8; 4];
                    out.extend_from_slice(ch.encode_utf8(&mut buf).as_bytes());
                }
                c => out.push(c),
            }
        }
        Ok(String::from_utf8_lossy(&out).into_owned())
    }
}

/// Parses one complete JSON document.
pub fn parse_json(text: &str) -> Result<Json, JsonError> {
    let mut p = JsonParser::new(text, 1);
    let v = p.value(0)?;
    p.ws();
    if p.pos < p.b.len() {
        return p.fail("unexpected text after the JSON value");
    }
    Ok(v)
}

/// Splits a trace into its entries with the line each starts on. A document whose first character is
/// `[` is one JSON array; anything else is JSON Lines (blank lines are skipped).
pub fn parse_trace_entries(text: &str) -> Result<Vec<(usize, Json)>, JsonError> {
    let text = text.strip_prefix('\u{feff}').unwrap_or(text);
    let mut out = vec![];
    if text.trim_start().starts_with('[') {
        let mut p = JsonParser::new(text, 1);
        p.ws();
        p.pos += 1;
        p.ws();
        if p.peek() == Some(b']') {
            p.pos += 1;
        } else {
            loop {
                p.ws();
                let line = p.line;
                out.push((line, p.value(1)?));
                p.ws();
                match p.peek() {
                    Some(b',') => p.pos += 1,
                    Some(b']') => {
                        p.pos += 1;
                        break;
                    }
                    _ => return p.fail("expected ',' or ']' in the trace array"),
                }
            }
        }
        p.ws();
        if p.pos < p.b.len() {
            return p.fail("unexpected text after the trace array");
        }
        return Ok(out);
    }
    for (i, l) in text.split('\n').enumerate() {
        if l.trim().is_empty() {
            continue;
        }
        let mut p = JsonParser::new(l, i + 1);
        let v = p.value(0)?;
        p.ws();
        if p.pos < p.b.len() {
            return p.fail("unexpected text after the JSON value (JSON Lines: one object per line)");
        }
        out.push((i + 1, v));
    }
    Ok(out)
}

// ---------------------------------------------------------------------------------------------
// Matching JSON against TLA+ values
// ---------------------------------------------------------------------------------------------

/// The JSON object key that stands for a function-domain element: a string, the name of a model value,
/// or the decimal form of an integer.
fn key_of(v: &Value) -> Option<String> {
    match v {
        Value::Str(s) | Value::Model(s) => Some(str_of(*s).to_string()),
        Value::Int(i) => Some(i.to_string()),
        _ => None,
    }
}

/// Key in a JSON object meaning "the record or function may have further keys".
pub const REST_KEY: &str = "...";

fn obj_match(o: &[(String, Json)], n: usize, key: &dyn Fn(usize) -> Option<String>, val: &dyn Fn(usize) -> Value) -> bool {
    let partial = o.iter().any(|(k, _)| k == REST_KEY);
    let entries = o.len() - o.iter().filter(|(k, _)| k == REST_KEY).count();
    if entries > n || (!partial && entries != n) {
        return false;
    }
    let mut used = vec![false; n];
    'entry: for (k, jv) in o {
        if k == REST_KEY {
            continue;
        }
        for i in 0..n {
            if !used[i] && key(i).as_deref() == Some(k.as_str()) && matches(jv, &val(i)) {
                used[i] = true;
                continue 'entry;
            }
        }
        return false;
    }
    true
}

/// Is there a one-to-one pairing of the JSON elements with the set's elements?
fn set_match(a: &[Json], elems: &[Value]) -> bool {
    let n = a.len();
    if n != elems.len() {
        return false;
    }
    // Greedy first: when every JSON element matches exactly one set element (the usual case) this is
    // already the answer.
    let mut owner: Vec<Option<usize>> = vec![None; n]; // set element -> JSON element
    let mut greedy = true;
    for (i, j) in a.iter().enumerate() {
        match (0..n).find(|&e| owner[e].is_none() && matches(j, &elems[e])) {
            Some(e) => owner[e] = Some(i),
            None => {
                greedy = false;
                break;
            }
        }
    }
    if greedy {
        return true;
    }
    // Ambiguous matches (a string that is both a string and a model value in the set, nested
    // collections): augmenting paths.
    let adj: Vec<Vec<usize>> = a.iter().map(|j| (0..n).filter(|&e| matches(j, &elems[e])).collect()).collect();
    let mut owner: Vec<Option<usize>> = vec![None; n];
    fn augment(i: usize, adj: &[Vec<usize>], owner: &mut [Option<usize>], seen: &mut [bool]) -> bool {
        for &e in &adj[i] {
            if seen[e] {
                continue;
            }
            seen[e] = true;
            if owner[e].is_none() || augment(owner[e].unwrap(), adj, owner, seen) {
                owner[e] = Some(i);
                return true;
            }
        }
        false
    }
    for i in 0..n {
        let mut seen = vec![false; n];
        if !augment(i, &adj, &mut owner, &mut seen) {
            return false;
        }
    }
    true
}

/// Does the JSON value denote the TLA+ value? The TLA+ value decides how the JSON is read:
///
/// | JSON | matches |
/// |---|---|
/// | `true` / `false` | the boolean |
/// | number | the integer of that value (`1.0` is 1; `1.5` matches nothing) |
/// | string | the string, or the model value of that name |
/// | array | a sequence / tuple (same length, element by element), or a set (same size, elements paired one to one in any order) |
/// | object | a record (same fields), or a function whose domain elements are strings, model values or integers written as keys; a sequence is a function with keys `"1"`, `"2"`, .. |
/// | `null` | nothing |
///
/// An object with the key `"..."` matches when the keys it does give match; other keys of the record or
/// function are unconstrained.
pub fn matches(j: &Json, v: &Value) -> bool {
    match (j, v) {
        (Json::Bool(a), Value::Bool(b)) => a == b,
        (Json::Int(a), Value::Int(b)) => a == b,
        (Json::Str(s), Value::Str(id)) | (Json::Str(s), Value::Model(id)) => &*str_of(*id) == s.as_str(),
        (Json::Arr(a), Value::Tuple(t)) => a.len() == t.len() && a.iter().zip(t.iter()).all(|(x, y)| matches(x, y)),
        (Json::Arr(a), Value::Set(s)) => {
            if !s.enumerable() || !matches!(s.size(), Ok(n) if n == a.len() as i64) {
                return false;
            }
            match s.elems() {
                Ok(e) => set_match(a, e),
                Err(_) => false,
            }
        }
        (Json::Obj(o), Value::Record(r)) => obj_match(o, r.names.len(), &|i| Some(str_of(r.names[i]).to_string()), &|i| r.vals[i].clone()),
        (Json::Obj(o), Value::Fcn(f)) => obj_match(o, f.dom.len(), &|i| key_of(&f.dom[i]), &|i| f.vals[i].clone()),
        (Json::Obj(o), Value::Tuple(t)) => obj_match(o, t.len(), &|i| Some((i + 1).to_string()), &|i| t[i].clone()),
        _ => false,
    }
}

/// The JSON a logger would write for a TLA+ value (sets as arrays, records and functions as objects,
/// model values as strings). `matches(&to_json(v), v)` holds for every value made of booleans, integers,
/// strings, model values, sequences, finite sets, records and functions keyed by scalars.
pub fn to_json(v: &Value) -> Json {
    match v {
        Value::Bool(b) => Json::Bool(*b),
        Value::Int(i) => Json::Int(*i),
        Value::Str(s) | Value::Model(s) => Json::Str(str_of(*s).to_string()),
        Value::Tuple(t) => Json::Arr(t.iter().map(to_json).collect()),
        Value::Record(r) => Json::Obj(r.names.iter().zip(r.vals.iter()).map(|(n, x)| (str_of(*n).to_string(), to_json(x))).collect()),
        Value::Fcn(f) => Json::Obj(f.dom.iter().zip(f.vals.iter()).map(|(d, x)| (key_of(d).unwrap_or_else(|| fmt(d)), to_json(x))).collect()),
        Value::Set(s) if s.enumerable() => match s.elems() {
            Ok(e) => Json::Arr(e.iter().map(to_json).collect()),
            Err(_) => Json::Str(fmt(v)),
        },
        _ => Json::Str(fmt(v)),
    }
}

// ---------------------------------------------------------------------------------------------
// Observations
// ---------------------------------------------------------------------------------------------

pub struct Observation {
    /// 1-based position among the observations.
    pub index: usize,
    /// 1-based line of the trace file it starts on.
    pub line: usize,
    pub action: Option<String>,
    pub params: Option<Json>,
    /// (variable index, observed value)
    pub state: Vec<(usize, Json)>,
}

impl Observation {
    fn json(&self, model: &Model) -> Json {
        let mut o = vec![];
        if let Some(a) = &self.action {
            o.push(("action".to_string(), Json::Str(a.clone())));
        }
        if let Some(p) = &self.params {
            o.push(("params".to_string(), p.clone()));
        }
        if !self.state.is_empty() || self.action.is_none() {
            o.push(("state".to_string(), Json::Obj(self.state.iter().map(|(i, j)| (model.vars[*i].name.to_string(), j.clone())).collect())));
        }
        Json::Obj(o)
    }
}

/// A problem with the trace itself (not with the system it records).
pub struct TraceError {
    pub message: String,
    pub line: Option<usize>,
}

fn names_list(mut names: Vec<String>) -> String {
    names.sort();
    names.dedup();
    names.join(", ")
}

/// Reads the observations of a trace. Entries without `action` and `state` are counted as ignored.
pub fn read_observations(model: &Model, text: &str) -> Result<(Vec<Observation>, usize), TraceError> {
    let entries = parse_trace_entries(text).map_err(|e| TraceError { message: format!("not valid JSON: {}", e.message), line: Some(e.line) })?;
    let mut out: Vec<Observation> = vec![];
    let mut ignored = 0;
    for (line, j) in entries {
        let bad = |message: String| TraceError { message, line: Some(line) };
        if !matches!(j, Json::Obj(_)) {
            return Err(bad("an observation must be a JSON object such as {\"action\": \"Send\", \"state\": {\"sent\": 1}}".into()));
        }
        let action = match j.get("action") {
            None | Some(Json::Null) => None,
            Some(Json::Str(s)) => Some(s.clone()),
            Some(_) => return Err(bad("\"action\" must be a string (the name of an action of the spec)".into())),
        };
        let st = match j.get("state") {
            None | Some(Json::Null) => None,
            Some(Json::Obj(o)) => Some(o),
            Some(_) => return Err(bad("\"state\" must be a JSON object mapping variable names to values".into())),
        };
        if action.is_none() && st.is_none() {
            ignored += 1;
            continue;
        }
        let mut state: Vec<(usize, Json)> = vec![];
        for (k, v) in st.map(|o| &o[..]).unwrap_or(&[]) {
            let idx = match model.vars.iter().position(|d| &*name_str(d.name) == k.as_str()) {
                Some(i) => i,
                None => {
                    return Err(bad(format!(
                        "\"{}\" is not a variable of {}. Its variables are: {}.",
                        k,
                        model.root_name,
                        names_list(model.vars.iter().map(|d| d.name.to_string()).collect())
                    )))
                }
            };
            if state.iter().any(|(i, _)| *i == idx) {
                return Err(bad(format!("variable \"{}\" is given twice in one observation", k)));
            }
            state.push((idx, v.clone()));
        }
        let params = match j.get("params") {
            None | Some(Json::Null) => None,
            Some(p @ (Json::Arr(_) | Json::Obj(_))) => Some(p.clone()),
            Some(_) => return Err(bad("\"params\" must be an array (in the order of the action's parameters) or an object (by parameter name)".into())),
        };
        if let Some(a) = &action {
            let named: Vec<&Action> = model.actions.iter().filter(|x| &x.name == a).collect();
            if named.is_empty() {
                return Err(bad(format!(
                    "\"{}\" is not an action of {}. Its actions are: {}.",
                    a,
                    model.root_name,
                    names_list(model.actions.iter().map(|x| x.name.clone()).collect())
                )));
            }
            if let Some(p) = &params {
                if named.iter().all(|x| x.param_vals.is_empty()) {
                    return Err(bad(format!(
                        "\"params\" cannot be checked for action {}: in the model it has no parameters with fixed values (it is not an operator with parameters, or its arguments depend on the state). Remove \"params\" and observe the affected variables instead.",
                        a
                    )));
                }
                if let Json::Obj(o) = p {
                    for (k, _) in o {
                        if !named.iter().any(|x| x.param_vals.iter().any(|(n, _)| n == k)) {
                            return Err(bad(format!(
                                "\"{}\" is not a parameter of action {}. Its parameters are: {}.",
                                k,
                                a,
                                named.iter().flat_map(|x| x.param_vals.iter().map(|(n, _)| n.clone())).collect::<Vec<_>>().join(", ")
                            )));
                        }
                    }
                }
            }
        } else if params.is_some() {
            return Err(bad("\"params\" needs an \"action\"".into()));
        }
        out.push(Observation { index: out.len() + 1, line, action, params, state });
    }
    Ok((out, ignored))
}

fn params_match(p: &Json, a: &Action) -> bool {
    match p {
        Json::Arr(items) => items.len() == a.param_vals.len() && items.iter().zip(a.param_vals.iter()).all(|(j, (_, v))| matches(j, v)),
        Json::Obj(o) => o.iter().all(|(k, j)| a.param_vals.iter().any(|(n, v)| n == k && matches(j, v))),
        _ => false,
    }
}

// ---------------------------------------------------------------------------------------------
// The check
// ---------------------------------------------------------------------------------------------

#[derive(Clone)]
pub struct ConformOptions {
    /// Up to this many unobserved steps may happen before each observation.
    pub hidden: u32,
    /// An observation without an action may also be matched by no step at all.
    pub stutter: bool,
    /// Maximum number of spec states tracked for one observation.
    pub limit: usize,
    /// Report one full-state behaviour that matches the trace.
    pub behavior: bool,
    /// Apply the CONSTRAINT / ACTION_CONSTRAINT bounds of the configuration.
    pub constraints: bool,
}
impl Default for ConformOptions {
    fn default() -> Self {
        ConformOptions { hidden: 0, stutter: false, limit: 100_000, behavior: false, constraints: true }
    }
}

const NONE: u32 = u32::MAX;
const ACT_INIT: i32 = -1;
const ACT_STUTTER: i32 = -2;

struct Node {
    state: StateRef,
    parent: u32,
    /// index into `model.actions`, or ACT_INIT / ACT_STUTTER
    action: i32,
    /// index of the observation this state was matched to (NONE: an unobserved state)
    obs: u32,
}

/// One state of a behaviour that matches the trace.
pub struct BehaviorStep {
    pub state: StateRef,
    /// index into `model.actions`, None for the initial state
    pub action: Option<usize>,
    pub stutter: bool,
    /// line of the observation matched by this state (None: an unobserved state)
    pub line: Option<usize>,
}

pub struct Differs {
    pub var: String,
    pub observed: Json,
    pub expected: Json,
}
/// A step the spec allows that is close to the observation.
pub struct Nearest {
    /// None: an initial state
    pub action: Option<String>,
    pub differs: Vec<Differs>,
}
/// A step the spec allows at the point of failure, with the observed variables after it.
pub struct Enabled {
    pub action: String,
    pub produces: Vec<(String, Json)>,
    /// The observed variables all match after this step (so only the action is different).
    pub matches_state: bool,
}

pub struct Report {
    /// "conforms" | "mismatch" | "invariant" | "limit" | "trace-error" | "assumption" | "error"
    pub status: &'static str,
    pub message: String,
    pub observations: usize,
    pub ignored: usize,
    /// Number of observations matched before the check stopped.
    pub matched: usize,
    /// Number of spec states consistent with the matched observations.
    pub candidates: usize,
    /// (index, line, the observation) of the observation that could not be matched or hit the limit
    pub failed: Option<(usize, usize, Json)>,
    /// (index, line, candidates) of the last matched observation
    pub last_matched: Option<(usize, usize, usize)>,
    /// The observed variables in the states before the failing step (at most 3)
    pub before: Vec<Vec<(String, Json)>>,
    pub nearest: Vec<Nearest>,
    pub enabled: Vec<Enabled>,
    pub enabled_more: usize,
    pub hints: Vec<String>,
    pub notes: Vec<String>,
    /// status "invariant": its name
    pub name: Option<String>,
    pub line: Option<usize>,
    pub behavior: Option<Vec<BehaviorStep>>,
}

impl Report {
    fn new(status: &'static str, message: String) -> Report {
        Report {
            status,
            message,
            observations: 0,
            ignored: 0,
            matched: 0,
            candidates: 0,
            failed: None,
            last_matched: None,
            before: vec![],
            nearest: vec![],
            enabled: vec![],
            enabled_more: 0,
            hints: vec![],
            notes: vec![],
            name: None,
            line: None,
            behavior: None,
        }
    }
    pub fn exit_code(&self) -> i32 {
        match self.status {
            "conforms" => 0,
            "mismatch" => EXIT_MISMATCH,
            "trace-error" => EXIT_TRACE_ERROR,
            "limit" => EXIT_LIMIT,
            "invariant" => 12,
            "assumption" => 10,
            _ => 255,
        }
    }
}

struct Engine<'a> {
    model: &'a Model,
    ck: Checker<'a>,
    opts: ConformOptions,
    obs: Vec<Observation>,
    nodes: Vec<Node>,
    /// states that matched an observation but were excluded by a CONSTRAINT, and the constraint
    cut: usize,
    cut_name: Option<String>,
}

enum Zero {
    /// the observation must be matched by a step
    No,
    /// the first observation: the start states themselves may match
    Tag,
    /// the current states may match without a step (a new stuttering state is recorded)
    Stutter,
}

struct Advance {
    next: Vec<u32>,
    over_limit: bool,
}

fn state_hash(s: &StateRef, n: usize) -> R<u64> {
    let mut h = Hasher::new();
    s.with(|vals| -> R<()> {
        for v in &vals[..n] {
            h.value(v)?;
        }
        Ok(())
    })?;
    Ok(h.finish())
}

fn short(s: &str, max: usize) -> String {
    if s.chars().count() <= max {
        return s.to_string();
    }
    let cut: String = s.chars().take(max.saturating_sub(4)).collect();
    format!("{} ...", cut)
}

impl<'a> Engine<'a> {
    fn nvars(&self) -> usize {
        self.model.vars.len()
    }
    fn obs_match(&self, oi: usize, s: &StateRef) -> bool {
        self.obs[oi].state.iter().all(|(i, j)| matches(j, &s.get(*i)))
    }
    /// The actions an observation allows (None: any).
    fn action_mask(&self, oi: usize) -> Option<Vec<bool>> {
        let o = &self.obs[oi];
        let name = o.action.as_ref()?;
        Some(self.model.actions.iter().map(|a| &a.name == name && o.params.as_ref().map_or(true, |p| params_match(p, a))).collect())
    }
    /// The name of a CONSTRAINT / ACTION_CONSTRAINT that excludes the state (or the step into it).
    fn constraint_violated(&self, s: Option<&StateRef>, t: &StateRef) -> R<Option<String>> {
        if !self.opts.constraints {
            return Ok(None);
        }
        for c in &self.model.constraints {
            if !self.ck.eval_pred(c, t, None)? {
                return Ok(Some(c.name.clone()));
            }
        }
        if let Some(s) = s {
            for c in &self.model.action_constraints {
                if !self.ck.eval_pred(c, s, Some(t))? {
                    return Ok(Some(c.name.clone()));
                }
            }
        }
        Ok(None)
    }

    /// The states matching observation `oi` that are reachable from `frontier`: by no step (`zero`), or by
    /// up to `steps` unobserved steps followed by one step of the observed action.
    fn advance(&mut self, frontier: &[u32], oi: usize, zero: Zero, steps: Option<u32>) -> R<Advance> {
        let n = self.nvars();
        let mask = self.action_mask(oi);
        let mut next: Vec<u32> = vec![];
        let mut matched: HashSet<u64> = HashSet::new();
        let mut visited: HashSet<u64> = HashSet::new();
        let mut created = 0usize;
        for &f in frontier {
            let s = self.nodes[f as usize].state.clone();
            let h = state_hash(&s, n)?;
            visited.insert(h);
            match zero {
                Zero::No => {}
                Zero::Tag => {
                    if self.obs_match(oi, &s) && matched.insert(h) {
                        self.nodes[f as usize].obs = oi as u32;
                        next.push(f);
                    }
                }
                Zero::Stutter => {
                    if self.obs_match(oi, &s) && matched.insert(h) {
                        next.push(self.nodes.len() as u32);
                        self.nodes.push(Node { state: s, parent: f, action: ACT_STUTTER, obs: oi as u32 });
                    }
                }
            }
        }
        let hidden = match steps {
            Some(h) => h,
            None => return Ok(Advance { next, over_limit: false }),
        };
        let mut level: Vec<u32> = frontier.to_vec();
        let mut succs: Vec<StateRef> = vec![];
        let mut acts: Vec<u32> = vec![];
        for depth in 0..=hidden {
            let mut new_level: Vec<u32> = vec![];
            for &f in &level {
                let s = self.nodes[f as usize].state.clone();
                succs.clear();
                acts.clear();
                self.ck.successors(&s, &mut succs, &mut acts)?;
                for (t, &ai) in succs.iter().zip(acts.iter()) {
                    let h = state_hash(t, n)?;
                    let want_match = mask.as_ref().map_or(true, |m| m[ai as usize]) && !matched.contains(&h) && self.obs_match(oi, t);
                    let want_hidden = depth < hidden && !visited.contains(&h);
                    if !want_match && !want_hidden {
                        continue;
                    }
                    if let Some(c) = self.constraint_violated(Some(&s), t)? {
                        if want_match {
                            self.cut += 1;
                            self.cut_name = Some(c);
                        }
                        continue;
                    }
                    if want_match {
                        matched.insert(h);
                        next.push(self.nodes.len() as u32);
                        self.nodes.push(Node { state: t.clone(), parent: f, action: ai as i32, obs: oi as u32 });
                        created += 1;
                    }
                    if want_hidden {
                        visited.insert(h);
                        new_level.push(self.nodes.len() as u32);
                        self.nodes.push(Node { state: t.clone(), parent: f, action: ai as i32, obs: NONE });
                        created += 1;
                    }
                    if created > self.opts.limit {
                        return Ok(Advance { next, over_limit: true });
                    }
                }
            }
            if new_level.is_empty() {
                break;
            }
            level = new_level;
        }
        Ok(Advance { next, over_limit: false })
    }

    fn behavior_to(&self, node: u32) -> Vec<BehaviorStep> {
        let mut out = vec![];
        let mut i = node;
        while i != NONE {
            let nd = &self.nodes[i as usize];
            out.push(BehaviorStep {
                state: nd.state.clone(),
                action: if nd.action >= 0 { Some(nd.action as usize) } else { None },
                stutter: nd.action == ACT_STUTTER,
                line: if nd.obs == NONE { None } else { Some(self.obs[nd.obs as usize].line) },
            });
            i = nd.parent;
        }
        out.reverse();
        out
    }

    fn label(&self, ai: usize) -> String {
        let a = &self.model.actions[ai];
        format!("{}{}", a.name, a.params)
    }

    fn project(&self, oi: usize, s: &StateRef) -> Vec<(String, Json)> {
        self.obs[oi].state.iter().map(|(i, _)| (self.model.vars[*i].name.to_string(), to_json(&s.get(*i)))).collect()
    }

    /// Explains why observation `oi` matches no step from `frontier`.
    fn diagnose(&mut self, frontier: &[u32], oi: usize, rep: &mut Report) -> R<()> {
        let o = &self.obs[oi];
        let first_state = oi == 0 && o.action.is_none();
        let mask = self.action_mask(oi);
        // every step the spec allows here: (action, state after it)
        let mut cands: Vec<(Option<usize>, StateRef)> = vec![];
        let mut seen: HashSet<(i64, u64)> = HashSet::new();
        let n = self.nvars();
        if first_state {
            for &f in frontier {
                cands.push((None, self.nodes[f as usize].state.clone()));
            }
        } else {
            let (mut succs, mut acts) = (vec![], vec![]);
            for &f in frontier {
                let s = self.nodes[f as usize].state.clone();
                succs.clear();
                acts.clear();
                self.ck.successors(&s, &mut succs, &mut acts)?;
                for (t, &ai) in succs.iter().zip(acts.iter()) {
                    if seen.insert((ai as i64, state_hash(t, n)?)) && self.constraint_violated(Some(&s), t)?.is_none() {
                        cands.push((Some(ai as usize), t.clone()));
                    }
                }
            }
            let mut shown: Vec<String> = vec![];
            for &f in frontier {
                let p = self.project(oi, &self.nodes[f as usize].state);
                let key = Json::Obj(p.clone()).text();
                if !p.is_empty() && !shown.contains(&key) {
                    shown.push(key);
                    if rep.before.len() < 3 {
                        rep.before.push(p);
                    }
                }
            }
        }
        let diffs = |t: &StateRef| -> Vec<Differs> {
            o.state
                .iter()
                .filter(|(i, j)| !matches(j, &t.get(*i)))
                .map(|(i, j)| Differs { var: self.model.vars[*i].name.to_string(), observed: j.clone(), expected: to_json(&t.get(*i)) })
                .collect()
        };
        let act_ok = |a: Option<usize>| -> bool {
            match (&mask, a) {
                (Some(m), Some(ai)) => m[ai],
                _ => true,
            }
        };
        let named = |a: Option<usize>| -> bool {
            match (&o.action, a) {
                (Some(nm), Some(ai)) => &self.model.actions[ai].name == nm,
                _ => true,
            }
        };
        let act = o.action.clone().unwrap_or_default();
        let any_ok = cands.iter().any(|(a, _)| act_ok(*a));
        let where_ = if frontier.len() == 1 { "the state the trace has reached" } else { "any state the trace may have reached" };
        rep.message = if first_state {
            if cands.is_empty() {
                "The spec has no initial state.".to_string()
            } else {
                "No initial state of the spec has the observed values.".to_string()
            }
        } else if cands.is_empty() {
            format!("The spec allows no further step from {}.", where_)
        } else if o.action.is_some() && !any_ok {
            if cands.iter().any(|(a, _)| named(*a)) {
                let mut with: Vec<String> = cands.iter().filter(|(a, _)| named(*a)).map(|(a, _)| self.model.actions[a.unwrap()].params.clone()).collect();
                with.sort();
                with.dedup();
                format!("{} cannot happen here with these parameters; the spec allows it with {}.", act, short(&with.join(", "), 120))
            } else {
                format!("{} cannot happen here: the spec does not allow it in {}.", act, where_)
            }
        } else if o.action.is_some() {
            format!("{} can happen here, but it does not produce the observed values.", act)
        } else {
            "No step the spec allows here produces the observed values.".to_string()
        };
        // the closest steps: of the observed action if it is possible at all, else of any action
        let pool: Vec<&(Option<usize>, StateRef)> = cands.iter().filter(|(a, _)| !any_ok || act_ok(*a)).collect();
        let mut scored: Vec<(usize, &(Option<usize>, StateRef), Vec<Differs>)> = pool
            .into_iter()
            .map(|c| {
                let d = diffs(&c.1);
                (d.len(), c, d)
            })
            .collect();
        scored.sort_by_key(|x| x.0);
        let best = scored.first().map(|x| x.0);
        let mut near_keys: Vec<String> = vec![];
        for (k, c, d) in scored {
            if Some(k) != best || rep.nearest.len() >= 3 {
                break;
            }
            let label = c.0.map(|ai| self.label(ai));
            let key = format!("{:?}{}", label, d.iter().map(|x| format!("{}={}", x.var, x.expected.text())).collect::<String>());
            if near_keys.contains(&key) {
                continue;
            }
            near_keys.push(key);
            rep.nearest.push(Nearest { action: label, differs: d });
        }
        if !first_state {
            let mut keys: Vec<String> = vec![];
            for (a, t) in &cands {
                let label = self.label(a.unwrap());
                let produces = self.project(oi, t);
                let key = format!("{}{}", label, Json::Obj(produces.clone()).text());
                if keys.contains(&key) {
                    continue;
                }
                keys.push(key);
                if rep.enabled.len() >= 8 {
                    rep.enabled_more += 1;
                } else {
                    rep.enabled.push(Enabled { action: label, produces, matches_state: self.obs_match(oi, t) });
                }
            }
        }
        // hints: would another option have matched?
        let plain = o.action.is_none();
        if !first_state && plain && !self.opts.stutter && frontier.iter().any(|&f| self.obs_match(oi, &self.nodes[f as usize].state)) {
            rep.hints.push("The observation matches the state before it, unchanged. If this line records a snapshot rather than a step, rerun with -stutter.".into());
        }
        if self.cut > 0 {
            rep.hints.push(format!(
                "{} matching state{} outside the model's bound {} (a CONSTRAINT in the configuration). Rerun with -noconstraints to follow the trace beyond it.",
                self.cut,
                if self.cut == 1 { " is" } else { "s are" },
                self.cut_name.clone().unwrap_or_default()
            ));
        }
        let keep = self.nodes.len();
        let (cut, cut_name) = (self.cut, self.cut_name.clone());
        let saved_limit = self.opts.limit;
        self.opts.limit = saved_limit.min(20_000);
        for extra in 1..=3u32 {
            let h = self.opts.hidden + extra;
            let steps = if first_state { Some(h - 1) } else { Some(h) };
            let found = matches!(self.advance(frontier, oi, Zero::No, steps), Ok(a) if !a.next.is_empty());
            self.nodes.truncate(keep);
            if found {
                rep.hints.push(format!(
                    "The observation can be matched if {} step{} went unlogged before it. If the log does not record every step, rerun with -hidden {}.",
                    h,
                    if h == 1 { "" } else { "s" },
                    h
                ));
                break;
            }
        }
        self.opts.limit = saved_limit;
        self.cut = cut;
        self.cut_name = cut_name;
        Ok(())
    }

    fn describe(&self, e: &Fail) -> String {
        self.ck.describe_err(e, true)
    }
}

/// Checks a trace against a model.
pub fn check_trace(model: &Model, trace: &str, opts: &ConformOptions) -> Report {
    let (obs, ignored) = match read_observations(model, trace) {
        Ok(x) => x,
        Err(e) => {
            let mut r = Report::new("trace-error", e.message);
            r.line = e.line;
            return r;
        }
    };
    if obs.is_empty() {
        let mut r = Report::new(
            "trace-error",
            if ignored > 0 {
                format!("the trace has no observations: none of its {} entries has an \"action\" or a \"state\" key", ignored)
            } else {
                "the trace is empty".to_string()
            },
        );
        r.ignored = ignored;
        return r;
    }
    let ck = Checker::new(model, CheckOptions { check_deadlock: false, record_graph: false });
    let mut eng = Engine { model, ck, opts: opts.clone(), obs, nodes: vec![], cut: 0, cut_name: None };
    let total = eng.obs.len();
    let mut rep = match run(&mut eng) {
        Ok(r) => r,
        Err(e) => Report::new("error", eng.describe(&e)),
    };
    rep.observations = total;
    rep.ignored = ignored;
    rep
}

fn run(eng: &mut Engine) -> R<Report> {
    let model = eng.model;
    if let Some(r) = eng.ck.check_assumptions() {
        return Ok(Report::new(if r.status == "assumption" { "assumption" } else { "error" }, r.message.unwrap_or_default()));
    }
    let n = eng.nvars();
    // the initial states
    let mut frontier: Vec<u32> = vec![];
    let mut seen: HashSet<u64> = HashSet::new();
    for s in eng.ck.enumerate_init()? {
        if seen.insert(state_hash(&s, n)?) && eng.constraint_violated(None, &s)?.is_none() {
            frontier.push(eng.nodes.len() as u32);
            eng.nodes.push(Node { state: s, parent: NONE, action: ACT_INIT, obs: NONE });
            if frontier.len() > eng.opts.limit {
                let mut r = Report::new("limit", format!("The spec has more than {} initial states.", eng.opts.limit));
                r.hints.push("Raise the limit with -limit N.".into());
                return Ok(r);
            }
        }
    }
    let mut last: Option<(usize, usize, usize)> = None;
    let mut inv_noted: HashMap<String, ()> = HashMap::new();
    let mut notes: Vec<String> = vec![];
    for oi in 0..eng.obs.len() {
        let (index, line) = (eng.obs[oi].index, eng.obs[oi].line);
        let plain = eng.obs[oi].action.is_none();
        let (zero, steps) = if oi == 0 && plain {
            (Zero::Tag, eng.opts.hidden.checked_sub(1))
        } else {
            (if eng.opts.stutter && plain { Zero::Stutter } else { Zero::No }, Some(eng.opts.hidden))
        };
        eng.cut = 0;
        let adv = eng.advance(&frontier, oi, zero, steps)?;
        if adv.over_limit {
            let mut r = Report::new(
                "limit",
                format!("More than {} spec states are consistent with the trace at line {}; the check was stopped without a verdict.", eng.opts.limit, line),
            );
            r.failed = Some((index, line, eng.obs[oi].json(model)));
            r.last_matched = last;
            r.matched = oi;
            r.hints.push(
                "Narrow the candidates: log more variables, name the action in each observation, or use a smaller -hidden. Or raise the limit with -limit N.".into(),
            );
            return Ok(r);
        }
        if adv.next.is_empty() {
            let mut r = Report::new("mismatch", String::new());
            r.failed = Some((index, line, eng.obs[oi].json(model)));
            r.last_matched = last;
            r.matched = oi;
            r.candidates = frontier.len();
            r.line = Some(line);
            eng.diagnose(&frontier, oi, &mut r)?;
            r.notes = notes;
            if eng.opts.behavior && last.is_some() {
                r.behavior = Some(eng.behavior_to(frontier[0]));
            }
            return Ok(r);
        }
        // invariants of the configuration on the matched states
        if !model.invariants.is_empty() {
            let mut violated: Vec<(u32, &str)> = vec![];
            for &id in &adv.next {
                let s = eng.nodes[id as usize].state.clone();
                for inv in &model.invariants {
                    match eng.ck.eval_pred(inv, &s, None) {
                        Ok(true) => {}
                        Ok(false) => {
                            violated.push((id, &inv.name));
                            break;
                        }
                        Err(e) => return Ok(Report::new("error", format!("Evaluating invariant {} failed.\n{}", inv.name, eng.describe(&e)))),
                    }
                }
            }
            if violated.len() == adv.next.len() {
                let (id, name) = violated[0];
                let mut r = Report::new("invariant", format!("Invariant {} is violated by the recorded behaviour at line {}.", name, line));
                r.name = Some(name.to_string());
                r.line = Some(line);
                r.matched = oi + 1;
                r.candidates = adv.next.len();
                r.last_matched = Some((index, line, adv.next.len()));
                r.behavior = Some(eng.behavior_to(id));
                r.notes = notes;
                return Ok(r);
            }
            for (_, name) in &violated {
                if inv_noted.insert(name.to_string(), ()).is_none() {
                    let k = violated.iter().filter(|v| v.1 == *name).count();
                    notes.push(format!(
                        "Invariant {} is violated in {} of the {} spec states consistent with the trace at line {}. The trace does not say which state the system was in; model-check the spec.",
                        name,
                        k,
                        adv.next.len(),
                        line
                    ));
                }
            }
        }
        last = Some((index, line, adv.next.len()));
        frontier = adv.next;
    }
    let mut r = Report::new("conforms", String::new());
    r.matched = eng.obs.len();
    r.candidates = frontier.len();
    r.last_matched = last;
    r.notes = notes;
    if eng.opts.behavior {
        r.behavior = Some(eng.behavior_to(frontier[0]));
    }
    Ok(r)
}

// ---------------------------------------------------------------------------------------------
// Output
// ---------------------------------------------------------------------------------------------

fn js(s: &str) -> Json {
    Json::Str(s.to_string())
}
fn ju(n: usize) -> Json {
    Json::Int(n as i64)
}

/// The `-json` result (also what the WebAssembly API returns).
pub fn report_json(model: &Model, rep: &Report) -> String {
    let mut o: Vec<(String, Json)> = vec![("status".into(), js(rep.status))];
    let mut put = |k: &str, v: Json| o.push((k.to_string(), v));
    if let Some(n) = &rep.name {
        put("name", js(n));
    }
    if !rep.message.is_empty() {
        put("message", js(&rep.message));
    }
    if let Some(l) = rep.line {
        put("line", ju(l));
    }
    put("observations", ju(rep.observations));
    put("ignored", ju(rep.ignored));
    put("matched", ju(rep.matched));
    put("candidates", ju(rep.candidates));
    if let Some((index, line, obs)) = &rep.failed {
        put("failed", Json::Obj(vec![("index".into(), ju(*index)), ("line".into(), ju(*line)), ("observation".into(), obs.clone())]));
    }
    if rep.status != "conforms" {
        put(
            "lastMatched",
            match rep.last_matched {
                Some((index, line, c)) => Json::Obj(vec![("index".into(), ju(index)), ("line".into(), ju(line)), ("candidates".into(), ju(c))]),
                None => Json::Null,
            },
        );
    }
    if rep.status == "mismatch" {
        put("before", Json::Arr(rep.before.iter().map(|b| Json::Obj(b.clone())).collect()));
        put(
            "nearest",
            Json::Arr(
                rep.nearest
                    .iter()
                    .map(|n| {
                        Json::Obj(vec![
                            ("action".into(), n.action.as_deref().map(js).unwrap_or(Json::Null)),
                            (
                                "differs".into(),
                                Json::Arr(
                                    n.differs
                                        .iter()
                                        .map(|d| Json::Obj(vec![("var".into(), js(&d.var)), ("observed".into(), d.observed.clone()), ("expected".into(), d.expected.clone())]))
                                        .collect(),
                                ),
                            ),
                        ])
                    })
                    .collect(),
            ),
        );
        put(
            "enabled",
            Json::Arr(
                rep.enabled
                    .iter()
                    .map(|e| Json::Obj(vec![("action".into(), js(&e.action)), ("produces".into(), Json::Obj(e.produces.clone())), ("matchesState".into(), Json::Bool(e.matches_state))]))
                    .collect(),
            ),
        );
        if rep.enabled_more > 0 {
            put("enabledMore", ju(rep.enabled_more));
        }
    }
    if !rep.hints.is_empty() {
        put("hints", Json::Arr(rep.hints.iter().map(|h| js(h)).collect()));
    }
    if !rep.notes.is_empty() {
        put("notes", Json::Arr(rep.notes.iter().map(|h| js(h)).collect()));
    }
    if let Some(b) = &rep.behavior {
        put("vars", Json::Arr(model.vars.iter().map(|v| js(&v.name.to_string())).collect()));
        put(
            "behavior",
            Json::Arr(
                b.iter()
                    .map(|s| {
                        Json::Obj(vec![
                            ("line".into(), s.line.map(ju).unwrap_or(Json::Null)),
                            (
                                "action".into(),
                                match s.action {
                                    Some(a) => js(&model.actions[a].name),
                                    None if s.stutter => js("(stuttering)"),
                                    None => Json::Null,
                                },
                            ),
                            ("state".into(), Json::Obj(model.vars.iter().enumerate().map(|(i, v)| (v.name.to_string(), js(&fmt(&s.state.get(i))))).collect())),
                        ])
                    })
                    .collect(),
            ),
        );
    }
    Json::Obj(o).text()
}

fn behavior_text(model: &Model, b: &[BehaviorStep]) -> String {
    let mut out = String::new();
    for (i, s) in b.iter().enumerate() {
        let label = if s.stutter { "Stuttering".to_string() } else { action_label(s.action.map(|a| &model.actions[a])) };
        out += &format!("State {}: {}\n{}\n", i + 1, label, state_text(model, &s.state));
    }
    // which trace line each state stands for, when that is not simply "state N is line N"
    let lines: Vec<String> = b.iter().enumerate().map(|(i, s)| format!("{}: {}", i + 1, s.line.map(|l| format!("line {}", l)).unwrap_or_else(|| "not in the trace".into()))).collect();
    if b.iter().enumerate().any(|(i, s)| s.line != Some(i + 1)) {
        out += &format!("(State: trace line)  {}\n", lines.join(", "));
    }
    out
}

fn pairs_text(p: &[(String, Json)]) -> String {
    if p.is_empty() {
        return String::new();
    }
    p.iter().map(|(k, v)| format!("{} = {}", k, short(&v.text(), 100))).collect::<Vec<_>>().join(", ")
}

fn plural(n: usize, what: &str) -> String {
    format!("{} {}{}", n, what, if n == 1 { "" } else { "s" })
}

/// The report for people.
pub fn report_text(model: &Model, rep: &Report) -> String {
    let mut o = String::new();
    let spec = &model.root_name;
    match rep.status {
        "conforms" => {
            o += &format!("Trace conforms: {} matched; the recorded run is a behaviour of {}.\n", plural(rep.observations, "observation"), spec);
            if rep.candidates > 1 {
                o += &format!("{} spec states are consistent with the whole trace.\n", rep.candidates);
            }
        }
        "mismatch" => {
            let (index, line, obs) = rep.failed.as_ref().unwrap();
            o += &format!("Error: Trace does not conform to {}: line {} (observation {} of {}) cannot be matched.\n\n", spec, line, index, rep.observations);
            o += &format!("  line {}: {}\n", line, short(&obs.text(), 300));
            match rep.last_matched {
                Some((_, l, c)) => o += &format!("  last matched: line {} ({} consistent with the trace up to there)\n", l, plural(c, "spec state")),
                None => o += "  last matched: none\n",
            }
            for b in &rep.before {
                o += &format!("  before this step: {}\n", pairs_text(b));
            }
            if rep.before.len() == 3 && rep.candidates > 3 {
                o += "  (and other possibilities)\n";
            }
            o += &format!("\n{}\n", rep.message);
            if !rep.nearest.is_empty() {
                o += if rep.last_matched.is_none() && rep.nearest.iter().all(|n| n.action.is_none()) { "Closest initial state:\n" } else { "Closest step the spec allows:\n" };
                for n in &rep.nearest {
                    let what = n.action.clone().unwrap_or_else(|| "initial state".into());
                    if n.differs.is_empty() {
                        o += &format!("  {}: gives the observed values, but it is a different action\n", what);
                    }
                    for (i, d) in n.differs.iter().enumerate() {
                        o += &format!(
                            "  {}{} is {} in the spec, {} in the trace\n",
                            if i == 0 { format!("{}: ", what) } else { " ".repeat(what.len() + 2) },
                            d.var,
                            short(&d.expected.text(), 120),
                            short(&d.observed.text(), 120)
                        );
                    }
                }
            }
            if !rep.enabled.is_empty() {
                let any_vars = rep.enabled.iter().any(|e| !e.produces.is_empty());
                o += if any_vars { "Steps the spec allows here, and the observed variables after each:\n" } else { "Steps the spec allows here:\n" };
                let w = rep.enabled.iter().map(|e| e.action.chars().count()).max().unwrap_or(0).min(40);
                for e in &rep.enabled {
                    o += format!("  {:w$}  {}", e.action, pairs_text(&e.produces), w = w).trim_end();
                    o.push('\n');
                }
                if rep.enabled_more > 0 {
                    o += &format!("  ... and {} more\n", rep.enabled_more);
                }
            }
        }
        "invariant" => {
            o += &format!("Error: {}\n", rep.message);
            o += "The trace is a behaviour of the spec, so the spec itself allows this state and model checking finds it too: fix the model (or the invariant) first.\n";
        }
        "limit" => {
            o += &format!("Error: {}\n", rep.message);
            if let Some((_, l, c)) = rep.last_matched {
                o += &format!("  last matched: line {} ({} consistent with the trace up to there)\n", l, plural(c, "spec state"));
            }
        }
        "trace-error" => match rep.line {
            Some(l) => o += &format!("Error: trace line {}: {}\n", l, rep.message),
            None => o += &format!("Error: {}\n", rep.message),
        },
        _ => o += &format!("Error: {}\n", rep.message),
    }
    if rep.ignored > 0 && rep.status != "trace-error" {
        o += &format!("({} without an \"action\" or \"state\" key ignored.)\n", plural(rep.ignored, "trace entry").replace("entrys", "entries"));
    }
    for n in &rep.notes {
        o += &format!("Note: {}\n", n);
    }
    for h in &rep.hints {
        o += &format!("Hint: {}\n", h);
    }
    if let Some(b) = &rep.behavior {
        o += match rep.status {
            "conforms" => "\nOne behaviour of the spec that matches the trace:\n",
            "invariant" => "\nThe behaviour up to this point is:\n",
            _ => "\nOne behaviour of the spec that matches the trace up to the last matched line:\n",
        };
        o += &behavior_text(model, b);
    }
    o
}

// ---------------------------------------------------------------------------------------------
// Command line
// ---------------------------------------------------------------------------------------------

pub const USAGE: &str = concat!(
    "everystate conform - check that a recorded run of the real system is a behaviour of the spec\n\n",
    "Usage: everystate conform [options] -trace TRACE SPEC[.tla]\n\n",
    "  -trace FILE      the recorded run: JSON Lines (one observation per line) or one JSON array\n",
    "  -config FILE     configuration file (default: SPEC.cfg), read as for model checking\n",
    "  -hidden N        up to N unlogged steps may happen before each observation (default 0)\n",
    "  -stutter         an observation without an \"action\" may also be a snapshot of an unchanged state\n",
    "  -behavior        print one full-state behaviour of the spec that matches the trace\n",
    "  -limit N         stop when more than N spec states are consistent with the trace (default 100000)\n",
    "  -noconstraints   ignore CONSTRAINT and ACTION_CONSTRAINT bounds of the configuration\n",
    "  -json            print a single JSON result object\n\n",
    "An observation is a JSON object; every key is optional and other keys are ignored:\n",
    "  {\"action\": \"Handle\", \"params\": [1], \"state\": {\"charges\": 1, \"queue\": [\"a\", \"b\"]}}\n",
    "  action   name of the spec action that happened (omit it: any action)\n",
    "  params   the action's arguments, as an array or as an object by parameter name\n",
    "  state    values of some or all spec variables after the step; variables left out are unconstrained\n",
    "The first observation describes the initial state; if it names an action, the initial state is\n",
    "taken as unlogged. JSON is matched against the spec's value: an array is a sequence or a set, an\n",
    "object a record or a function, a string a string or a model value. {\"k\": 1, \"...\": 0} matches a\n",
    "record or function with at least the key k.\n\n",
    "Exit status: 0 the trace conforms, 20 it does not, 21 the trace is unreadable or malformed,\n",
    "22 too many candidate states (no verdict), 12 the recorded behaviour violates an invariant of the\n",
    "configuration, 10 assumption, 150 parse error, 151 config error, 255 evaluation error.\n"
);

/// `everystate conform ...` (the arguments after `conform`).
pub fn run_cli(argv: &[String], host: HostRef, library_paths: &[String]) -> i32 {
    let mut opts = ConformOptions::default();
    let (mut spec, mut config, mut trace): (Option<String>, Option<String>, Option<String>) = (None, None, None);
    let mut json = false;
    let mut i = 0;
    let usage_error = |m: &str| -> i32 {
        host.print(&format!("Error: {}\n\n{}", m, USAGE));
        1
    };
    while i < argv.len() {
        let a = argv[i].as_str();
        let mut number = |what: &str| -> Result<u64, String> {
            i += 1;
            argv.get(i).and_then(|v| v.parse::<u64>().ok()).ok_or_else(|| format!("{} needs a number", what))
        };
        match a {
            "-config" => {
                i += 1;
                config = argv.get(i).cloned();
            }
            "-trace" => {
                i += 1;
                trace = argv.get(i).cloned();
            }
            "-hidden" => match number("-hidden") {
                Ok(n) => opts.hidden = n.min(1_000_000) as u32,
                Err(m) => return usage_error(&m),
            },
            "-limit" => match number("-limit") {
                Ok(n) => opts.limit = n as usize,
                Err(m) => return usage_error(&m),
            },
            "-stutter" => opts.stutter = true,
            "-behavior" | "-behaviour" => opts.behavior = true,
            "-noconstraints" => opts.constraints = false,
            "-json" => json = true,
            "-h" | "-help" | "--help" => {
                host.print(USAGE);
                return 0;
            }
            _ if a.starts_with('-') => return usage_error(&format!("unknown option {}", a)),
            _ => {
                if spec.is_none() {
                    spec = Some(a.to_string());
                } else if trace.is_none() {
                    trace = Some(a.to_string());
                } else {
                    return usage_error(&format!("unexpected argument {}", a));
                }
            }
        }
        i += 1;
    }
    let spec = match spec {
        Some(s) => s,
        None => return usage_error("Missing input TLA+ module."),
    };
    let trace = match trace {
        Some(t) => t,
        None => return usage_error("Missing trace file (-trace FILE)."),
    };
    let spec_path = if spec.ends_with(".tla") { spec.clone() } else { format!("{}.tla", spec) };
    let dir = dirname(&path_resolve(&host.cwd(), &spec_path));
    let root_name = basename(&spec_path, ".tla").to_string();
    let mut cfg_path = config.clone().unwrap_or_else(|| format!("{}.cfg", root_name));
    if !cfg_path.ends_with(".cfg") && !host.exists(&cfg_path) && !host.exists(&path_join(&dir, &cfg_path)) {
        cfg_path.push_str(".cfg");
    }
    if !host.exists(&cfg_path) || config.is_none() {
        let in_dir = path_join(&dir, &cfg_path);
        if host.exists(&in_dir) {
            cfg_path = in_dir;
        }
    }
    let mut libs = vec![dir];
    libs.extend(library_paths.iter().cloned());
    let resolve = file_resolver(host.clone(), libs, Rc::new(RefCell::new(vec![])));
    let setup: R<Model> = (|| {
        if !host.exists(&cfg_path) {
            return err("config", format!("TLC encountered the following error reading the configuration file {}:\nFile not found.", cfg_path));
        }
        let text = String::from_utf8_lossy(&host.read_file(&cfg_path).unwrap_or_default()).into_owned();
        let cfg = crate::cfg::parse_config(&text)?;
        build_model(&root_name, resolve, &cfg, host.clone())
    })();
    let model = match setup {
        Ok(m) => m,
        Err(e) => {
            let (o, code) = setup_error_json(&e);
            if json {
                host.print(&format!("{}\n", o));
            } else {
                let msg = match &*e {
                    Fail::Tla(t) => t.msg.clone(),
                    Fail::Check { message, .. } => message.clone(),
                    Fail::Found => "internal error during setup".into(),
                };
                host.print(&format!("{}\nError: {}\n", msg, if code == 151 { "The configuration could not be read." } else { "Parsing or semantic analysis failed." }));
            }
            return code;
        }
    };
    let rep = match host.read_file(&trace) {
        Ok(bytes) => check_trace(&model, &String::from_utf8_lossy(&bytes), &opts),
        Err(e) => Report::new("trace-error", format!("cannot read the trace file {}", e)),
    };
    if json {
        host.print(&format!("{}\n", report_json(&model, &rep)));
    } else {
        host.print(&report_text(&model, &rep));
    }
    rep.exit_code()
}
