//! Native overrides for the remaining operators of the bundled community modules (port of the rest
//! of community.ts; the hot operators live in stdlib.rs). Host access (files, environment, processes)
//! goes through `ev.host` only.
use crate::eval::Evaluator;
use crate::intern::*;
use crate::modules::NativeFn;
use crate::stdlib::js_names;
use crate::value::*;
use std::cmp::Ordering;
use std::rc::Rc;

pub type Ov = (&'static str, &'static str, u32, bool, NativeFn);

const ORD: [&str; 5] = ["first", "second", "third", "fourth", "fifth"];
fn fail<T>(msg: String) -> R<T> {
    eval_err(msg)
}
fn arg_err<T>(i: usize, op: &str, what: &str, v: &Value) -> R<T> {
    fail(format!("The {} argument of {} should be a {}, but instead it is:\n{}", ORD[i], op, what, fmt(v)))
}
fn one_arg_err<T>(op: &str, what: &str, v: &Value) -> R<T> {
    fail(format!("The argument of {} should be a {}, but instead it is:\n{}", op, what, fmt(v)))
}
fn not_in_domain<T>(i: usize, op: &str, s: &Value, v: i64) -> R<T> {
    fail(format!("The {} argument of {} must be in the domain of its first argument:\n{}\n, but instead it is\n{}", ORD[i], op, fmt(s), v))
}
fn int(v: &Value, op: &str, i: usize) -> R<i64> {
    match v {
        Value::Int(x) => Ok(*x),
        _ => fail(format!("The {} argument of {} should be an integer, but instead it is:\n{}", ORD[i], op, fmt(v))),
    }
}
fn seq<'a>(v: &'a Value, op: &str, i: usize) -> R<&'a Rc<TupleV>> {
    match v {
        Value::Tuple(t) => Ok(t),
        _ => fail(format!("The {} argument of {} should be a sequence, but instead it is:\n{}", ORD[i], op, fmt(v))),
    }
}
fn string(v: &Value, op: &str, i: usize) -> R<Rc<str>> {
    match v {
        Value::Str(s) => Ok(str_of(*s)),
        _ => arg_err(i, op, "string", v),
    }
}
fn mk_str(s: &str) -> Value {
    Value::Str(str_id(s))
}
fn tuple_of(v: Vec<Value>) -> Value {
    if v.is_empty() { empty_tuple() } else { Value::Tuple(TupleV::rc(v)) }
}
fn expect_bool(v: Value, i: usize, op: &str, what: &str, test: &Value) -> R<bool> {
    match v {
        Value::Bool(b) => Ok(b),
        _ => arg_err(i, op, what, test),
    }
}
fn unlazy(ev: &Evaluator, v: &Value) -> R<Value> {
    match v {
        Value::LazyFcn(f) => f.force(ev),
        v => Ok(v.clone()),
    }
}
fn key(v: &Value) -> String {
    fmt(v) // canonical values print identically iff they are equal
}

fn read_text(ev: &Evaluator, path: &str) -> R<String> {
    let h = ev.host.borrow().clone();
    if !h.exists(path) {
        return fail(format!("{} (No such file or directory)", path));
    }
    match h.read_file(path) {
        Ok(b) => Ok(String::from_utf8_lossy(&b).into_owned()),
        Err(e) => fail(e),
    }
}
fn host_write(r: Result<(), String>) -> R<()> {
    match r {
        Ok(()) => Ok(()),
        Err(e) => fail(e),
    }
}
fn split_lines(text: &str) -> Vec<String> {
    let mut lines: Vec<String> = text.replace("\r\n", "\n").split(['\n', '\r']).map(|s| s.to_string()).collect();
    if lines.last().map_or(false, |l| l.is_empty()) {
        lines.pop();
    }
    lines
}

// ---- sequences ----
fn sub_seq_index(s: &[Value], t: &[Value], from: usize) -> R<Option<usize>> {
    let mut i = from;
    while i + s.len() <= t.len() {
        let mut ok = true;
        for j in 0..s.len() {
            if !val_eq(&t[i + j], &s[j])? {
                ok = false;
                break;
            }
        }
        if ok {
            return Ok(Some(i));
        }
        i += 1;
    }
    Ok(None)
}
fn select_in(ev: &Evaluator, a: &[Value], op: &str, last: bool, sub: bool) -> R<Value> {
    let s = match &a[0] {
        Value::Tuple(t) => t,
        v => return arg_err(0, op, "sequence", v),
    };
    let test = &a[if sub { 3 } else { 1 }];
    let (mut from, mut to) = (1i64, s.len() as i64);
    if sub {
        from = match &a[1] {
            Value::Int(x) => *x,
            v => return arg_err(1, op, "natural", v),
        };
        to = match &a[2] {
            Value::Int(x) => *x,
            v => return arg_err(2, op, "natural", v),
        };
        if from > to {
            return Ok(Value::Int(0));
        }
        if from < 1 || from > s.len() as i64 {
            return not_in_domain(1, op, &a[0], from);
        }
        if to < 1 || to > s.len() as i64 {
            return not_in_domain(2, op, &a[0], to);
        }
    }
    let what = if last { "boolean-valued function" } else { "boolean-valued operator" };
    let pos = if sub { 3 } else { 2 }; // TLC reports "third" for the two-argument variants
    let hit = |i: i64| -> R<bool> { expect_bool(ev.apply_op(test, std::slice::from_ref(&s[(i - 1) as usize]))?, pos, op, what, test) };
    if last {
        let mut i = to;
        while i >= from {
            if hit(i)? {
                return Ok(Value::Int(i));
            }
            i -= 1;
        }
    } else {
        for i in from..=to {
            if hit(i)? {
                return Ok(Value::Int(i));
            }
        }
    }
    Ok(Value::Int(0))
}

// ---- graphs (Graphs and UndirectedGraphs share AbstractGraphs.java) ----
type Endpoints = fn(&Value) -> R<Option<(Value, Value)>>;
fn tuple_edge(e: &Value) -> R<Option<(Value, Value)>> {
    Ok(match e {
        Value::Tuple(t) if t.len() == 2 => Some((t[0].clone(), t[1].clone())),
        _ => None,
    })
}
fn pair_edge(e: &Value) -> R<Option<(Value, Value)>> {
    Ok(match e {
        Value::Set(s) if s.enumerable() => {
            let x = s.elems()?;
            if x.is_empty() || x.len() > 2 { None } else { Some((x[0].clone(), if x.len() == 2 { x[1].clone() } else { x[0].clone() })) }
        }
        _ => None,
    })
}
struct Graph {
    nodes: Rc<SetV>,
    edges: Vec<Value>,
}
fn to_graph(op: &str, pos: usize, kind: &str, v: &Value) -> R<Graph> {
    let r = match v {
        Value::Record(r) => r,
        _ => return arg_err(pos, op, &format!("{} record with a node and an edge field", kind), v),
    };
    let node = match r.get(str_id("node")) {
        Some(Value::Set(s)) => s.clone(),
        _ => return arg_err(pos, op, &format!("{} record whose node field is a set", kind), v),
    };
    let edge = match r.get(str_id("edge")) {
        Some(Value::Set(s)) => s.clone(),
        _ => return arg_err(pos, op, &format!("{} record whose edge field is a set", kind), v),
    };
    node.elems()?;
    Ok(Graph { nodes: node, edges: edge.elems()?.to_vec() })
}
#[derive(PartialEq, Clone, Copy)]
enum Mode {
    Forward,
    Transpose,
    Symmetric,
}
type Adj = Vec<(String, Vec<Value>)>;
fn adj_get<'a>(adj: &'a Adj, k: &str) -> &'a [Value] {
    adj.iter().find(|x| x.0 == k).map(|x| &x.1[..]).unwrap_or(&[])
}
fn adjacency(g: &Graph, parse: Endpoints, mode: Mode) -> R<Adj> {
    let mut adj: Adj = vec![];
    let mut add = |from: &Value, to: &Value| {
        let k = key(from);
        match adj.iter_mut().find(|x| x.0 == k) {
            Some(l) => l.1.push(to.clone()),
            None => adj.push((k, vec![to.clone()])),
        }
    };
    for e in &g.edges {
        let (mut from, mut to) = match parse(e)? {
            Some(p) => p,
            None => continue,
        };
        if !g.nodes.contains(&from)? || !g.nodes.contains(&to)? {
            continue;
        }
        if mode == Mode::Transpose {
            std::mem::swap(&mut from, &mut to);
        }
        add(&from, &to);
        if mode == Mode::Symmetric && !val_eq(&from, &to)? {
            add(&to, &from);
        }
    }
    Ok(adj)
}
fn reachable(source: &Value, adj: &Adj) -> Vec<String> {
    let mut visited = vec![key(source)];
    let mut frontier = vec![source.clone()];
    let mut i = 0;
    while i < frontier.len() {
        let succs = adj_get(adj, &key(&frontier[i])).to_vec();
        for succ in succs {
            let k = key(&succ);
            if !visited.contains(&k) {
                visited.push(k);
                frontier.push(succ);
            }
        }
        i += 1;
    }
    visited
}
fn simple_path(kind: &str, parse: Endpoints, mode: Mode, graph: &Value) -> R<Value> {
    let g = to_graph("SimplePath", 0, kind, graph)?;
    let adj = adjacency(&g, parse, mode)?;
    let mut paths: Vec<Value> = vec![];
    let mut path: Vec<Value> = vec![];
    let mut visited: Vec<String> = vec![];
    fn extend(cur: &Value, adj: &Adj, paths: &mut Vec<Value>, path: &mut Vec<Value>, visited: &mut Vec<String>) {
        paths.push(Value::Tuple(TupleV::rc(path.clone())));
        for succ in adj_get(adj, &key(cur)).to_vec() {
            let k = key(&succ);
            if visited.contains(&k) {
                continue;
            }
            visited.push(k.clone());
            path.push(succ.clone());
            extend(&succ, adj, paths, path, visited);
            path.pop();
            visited.retain(|x| *x != k);
        }
    }
    for start in g.nodes.elems()? {
        path.push(start.clone());
        visited.push(key(start));
        extend(start, &adj, &mut paths, &mut path, &mut visited);
        visited.pop();
        path.pop();
    }
    mk_set(paths)
}
fn are_connected_in(kind: &str, parse: Endpoints, mode: Mode, m: &Value, n: &Value, graph: &Value) -> R<Value> {
    let g = to_graph("AreConnectedIn", 2, kind, graph)?;
    if !g.nodes.contains(m)? || !g.nodes.contains(n)? {
        return Ok(Value::Bool(false));
    }
    if val_eq(m, n)? {
        return Ok(Value::Bool(true));
    }
    Ok(Value::Bool(reachable(m, &adjacency(&g, parse, mode)?).contains(&key(n))))
}

// ---- JSON (Json.java, which uses Gson) ----
fn json_str(s: &str, o: &mut String) {
    o.push('"');
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            '\t' => o.push_str("\\t"),
            '\x08' => o.push_str("\\b"),
            '\n' => o.push_str("\\n"),
            '\r' => o.push_str("\\r"),
            '\x0c' => o.push_str("\\f"),
            c if (c as u32) < 0x20 || c as u32 == 0x2028 || c as u32 == 0x2029 => o.push_str(&format!("\\u{:04x}", c as u32)),
            c => o.push(c),
        }
    }
    o.push('"');
}
fn json_unsupported<T>(v: &Value) -> R<T> {
    fail(format!("Cannot convert value: unsupported value type ({})", fmt(v)))
}
fn json_arr(ev: &Evaluator, xs: &[Value], o: &mut String) -> R<()> {
    o.push('[');
    for (i, x) in xs.iter().enumerate() {
        if i > 0 {
            o.push(',');
        }
        json_node(ev, x, o)?;
    }
    o.push(']');
    Ok(())
}
fn json_obj(ev: &Evaluator, keys: &[Value], vals: &[Value], o: &mut String) -> R<()> {
    // Gson's JsonObject: a repeated key keeps its position, the last value wins
    let mut m: Vec<(String, String)> = vec![];
    for i in 0..keys.len() {
        let k = match &keys[i] {
            Value::Str(s) => str_of(*s).to_string(),
            v => fmt(v),
        };
        let mut v = String::new();
        json_node(ev, &vals[i], &mut v)?;
        match m.iter_mut().find(|x| x.0 == k) {
            Some(e) => e.1 = v,
            None => m.push((k, v)),
        }
    }
    o.push('{');
    for (i, (k, v)) in m.iter().enumerate() {
        if i > 0 {
            o.push(',');
        }
        json_str(k, o);
        o.push(':');
        o.push_str(v);
    }
    o.push('}');
    Ok(())
}
fn json_node(ev: &Evaluator, v: &Value, o: &mut String) -> R<()> {
    match v {
        Value::Str(s) => json_str(&str_of(*s), o),
        Value::Int(i) => o.push_str(&i.to_string()),
        Value::Bool(b) => o.push_str(if *b { "true" } else { "false" }),
        Value::Tuple(t) => json_arr(ev, t, o)?,
        Value::Record(r) => {
            let keys: Vec<Value> = r.names.iter().map(|n| Value::Str(*n)).collect();
            json_obj(ev, &keys, &r.vals, o)?
        }
        Value::Fcn(f) => json_obj(ev, &f.dom, &f.vals, o)?,
        Value::Model(m) => json_str(&str_of(*m), o),
        Value::LazyFcn(lf) => match lf.force(ev)? {
            Value::LazyFcn(_) => return json_unsupported(v),
            f => json_node(ev, &f, o)?,
        },
        Value::Set(s) if s.enumerable() => json_arr(ev, s.elems()?, o)?,
        _ => return json_unsupported(v),
    }
    Ok(())
}
fn to_json(ev: &Evaluator, v: &Value) -> R<String> {
    let mut o = String::new();
    json_node(ev, v, &mut o)?;
    Ok(o)
}

// java.lang.String.format for the conversions that make sense with string arguments.
pub(crate) fn java_format(template: &str, params: &[String]) -> R<String> {
    // %(\d+\$)?([-#+ 0,(<]*)(\d+)?(\.\d+)?([a-zA-Z%])
    let t: Vec<char> = template.chars().collect();
    let mut out = String::new();
    let mut next = 0usize;
    let mut i = 0;
    while i < t.len() {
        if t[i] != '%' {
            out.push(t[i]);
            i += 1;
            continue;
        }
        let start = i;
        let mut j = i + 1;
        let ds = j;
        while j < t.len() && t[j].is_ascii_digit() {
            j += 1;
        }
        let mut idx: Option<usize> = None;
        if j > ds && j < t.len() && t[j] == '$' {
            idx = t[ds..j].iter().collect::<String>().parse().ok();
            j += 1;
        } else {
            j = ds;
        }
        let fs = j;
        while j < t.len() && "-#+ 0,(<".contains(t[j]) {
            j += 1;
        }
        let flags: String = t[fs..j].iter().collect();
        let ws = j;
        while j < t.len() && t[j].is_ascii_digit() {
            j += 1;
        }
        let width: Option<usize> = if j > ws { t[ws..j].iter().collect::<String>().parse().ok() } else { None };
        let mut prec: Option<usize> = None;
        if j + 1 < t.len() && t[j] == '.' && t[j + 1].is_ascii_digit() {
            let ps = j + 1;
            j = ps;
            while j < t.len() && t[j].is_ascii_digit() {
                j += 1;
            }
            prec = t[ps..j].iter().collect::<String>().parse().ok();
        }
        if j >= t.len() || !(t[j].is_ascii_alphabetic() || t[j] == '%') {
            // not a format specifier
            out.push('%');
            i = start + 1;
            continue;
        }
        let conv = t[j];
        let all: String = t[start..=j].iter().collect();
        i = j + 1;
        if conv == 'n' {
            out.push('\n');
            continue;
        }
        if conv == '%' {
            out.push('%');
            continue;
        }
        if conv != 's' && conv != 'S' {
            return fail(format!("Unsupported format conversion {} (only %s, %n and %% are supported).", all));
        }
        let k: i64 = match idx {
            Some(x) => x as i64 - 1,
            None => {
                if flags.contains('<') {
                    next as i64 - 1
                } else {
                    next += 1;
                    next as i64 - 1
                }
            }
        };
        if k < 0 || k as usize >= params.len() {
            return fail(format!("Format specifier '{}' has no matching argument.", all));
        }
        let mut v: String = params[k as usize].clone();
        if let Some(p) = prec {
            v = v.chars().take(p).collect();
        }
        if conv == 'S' {
            v = v.to_uppercase();
        }
        if let Some(w) = width {
            let n = v.chars().count();
            if n < w {
                let pad = " ".repeat(w - n);
                v = if flags.contains('-') { v + &pad } else { pad + &v };
            }
        }
        out.push_str(&v);
    }
    Ok(out)
}

// ---- TLC's binary value format (tlc2.value.ValueOutputStream / ValueInputStream), uncompressed ----
const K_BOOL: u8 = 0;
const K_INT: u8 = 1;
const K_STRING: u8 = 3;
const K_RECORD: u8 = 4;
const K_SETENUM: u8 = 5;
const K_TUPLE: u8 = 7;
const K_FCNRCD: u8 = 9;
const K_MODEL: u8 = 21;
const K_INTERVAL: u8 = 23;
const K_DUMMY: u8 = 26;
fn encode_value(ev: &Evaluator, v: &Value) -> R<Vec<u8>> {
    fn i32w(out: &mut Vec<u8>, x: i64) {
        out.extend_from_slice(&(x as i32).to_be_bytes());
    }
    fn nat(out: &mut Vec<u8>, x: usize) {
        if x > 0x7fff {
            i32w(out, -(x as i64));
        } else {
            out.extend_from_slice(&(x as u16).to_be_bytes());
        }
    }
    fn ustr(out: &mut Vec<u8>, s: &str) {
        out.push(K_STRING);
        i32w(out, 0);
        i32w(out, -1);
        let units: Vec<u16> = s.encode_utf16().collect();
        i32w(out, units.len() as i64);
        for u in units {
            out.push((u & 255) as u8);
        }
    }
    fn w(ev: &Evaluator, out: &mut Vec<u8>, x: &Value) -> R<()> {
        match x {
            Value::Bool(b) => {
                out.push(K_BOOL);
                out.push(*b as u8);
            }
            Value::Int(i) => {
                out.push(K_INT);
                i32w(out, *i);
            }
            Value::Str(s) => ustr(out, &str_of(*s)),
            Value::Tuple(t) => {
                out.push(K_TUPLE);
                nat(out, t.len());
                for e in t.iter() {
                    w(ev, out, e)?;
                }
            }
            Value::Record(r) => {
                // written as "not normalized" (negative length): TLC's field order depends on its own string table
                out.push(K_RECORD);
                i32w(out, -(r.names.len() as i64));
                for i in 0..r.names.len() {
                    ustr(out, &str_of(r.names[i]));
                    w(ev, out, &r.vals[i])?;
                }
            }
            Value::Fcn(f) => {
                out.push(K_FCNRCD);
                nat(out, f.dom.len());
                out.push(2);
                for i in 0..f.dom.len() {
                    w(ev, out, &f.dom[i])?;
                    w(ev, out, &f.vals[i])?;
                }
            }
            Value::Set(s) => match &s.k {
                SetK::Interval(lo, hi) => {
                    out.push(K_INTERVAL);
                    i32w(out, *lo);
                    i32w(out, *hi);
                }
                _ if s.enumerable() => {
                    let e = s.elems()?;
                    out.push(K_SETENUM);
                    i32w(out, -(e.len() as i64));
                    for x in e {
                        w(ev, out, x)?;
                    }
                }
                _ => return fail(format!("IOSerialize cannot serialize the value:\n{}", fmt(x))),
            },
            Value::LazyFcn(lf) => match lf.force(ev)? {
                Value::LazyFcn(_) => return fail(format!("IOSerialize cannot serialize the value:\n{}", fmt(x))),
                f => w(ev, out, &f)?,
            },
            _ => return fail(format!("IOSerialize cannot serialize the value:\n{}", fmt(x))),
        }
        Ok(())
    }
    let mut out = vec![];
    w(ev, &mut out, v)?;
    Ok(out)
}
struct Dec<'a> {
    b: &'a [u8],
    p: usize,
    handles: Vec<Option<Value>>,
}
impl Dec<'_> {
    fn need(&self, n: usize) -> R<()> {
        if self.p + n > self.b.len() {
            return fail("IODeserialize: unexpected end of file.".into());
        }
        Ok(())
    }
    fn u8(&mut self) -> R<u8> {
        self.need(1)?;
        self.p += 1;
        Ok(self.b[self.p - 1])
    }
    fn i16(&mut self) -> R<i32> {
        self.need(2)?;
        let x = i16::from_be_bytes([self.b[self.p], self.b[self.p + 1]]);
        self.p += 2;
        Ok(x as i32)
    }
    fn i32(&mut self) -> R<i32> {
        self.need(4)?;
        let x = i32::from_be_bytes([self.b[self.p], self.b[self.p + 1], self.b[self.p + 2], self.b[self.p + 3]]);
        self.p += 4;
        Ok(x)
    }
    fn nat(&mut self) -> R<i64> {
        let r = self.i16()?;
        if r >= 0 {
            return Ok(r as i64);
        }
        let lo = self.i16()? & 0xffff;
        Ok(-(((r << 16) | lo) as i64))
    }
    fn ustr(&mut self) -> R<Value> {
        self.i32()?;
        self.i32()?;
        let n = self.i32()?.max(0) as usize;
        self.need(n)?;
        let s: String = self.b[self.p..self.p + n].iter().map(|c| *c as char).collect();
        self.p += n;
        Ok(mk_str(&s))
    }
    fn handle(&self, idx: i64) -> R<Value> {
        match self.handles.get(idx.max(0) as usize) {
            Some(Some(v)) if idx >= 0 => Ok(v.clone()),
            _ => fail("IODeserialize: dangling back reference.".into()),
        }
    }
    fn r(&mut self) -> R<Value> {
        let kind = self.u8()?;
        match kind {
            K_BOOL => Ok(Value::Bool(self.u8()? != 0)),
            K_INT => Ok(Value::Int(self.i32()? as i64)),
            K_STRING => {
                let s = self.ustr()?;
                self.handles.push(Some(s.clone()));
                Ok(s)
            }
            K_INTERVAL => {
                let (lo, hi) = (self.i32()? as i64, self.i32()? as i64);
                Ok(Value::Set(Rc::new(SetV::new(SetK::Interval(lo, hi)))))
            }
            K_DUMMY => {
                let idx = self.nat()?;
                self.handle(idx)
            }
            K_MODEL => fail("IODeserialize: model values cannot be deserialized.".into()),
            K_TUPLE => {
                self.handles.push(None);
                let h = self.handles.len() - 1;
                let n = self.nat()?;
                let mut e = vec![];
                for _ in 0..n {
                    e.push(self.r()?);
                }
                let v = tuple_of(e);
                self.handles[h] = Some(v.clone());
                Ok(v)
            }
            K_SETENUM => {
                self.handles.push(None);
                let h = self.handles.len() - 1;
                let n = self.i32()?.unsigned_abs();
                let mut e = vec![];
                for _ in 0..n {
                    e.push(self.r()?);
                }
                let v = mk_set(e)?;
                self.handles[h] = Some(v.clone());
                Ok(v)
            }
            K_RECORD => {
                self.handles.push(None);
                let h = self.handles.len() - 1;
                let n = self.i32()?.unsigned_abs();
                let mut pairs = vec![];
                for _ in 0..n {
                    let name = if self.u8()? == K_DUMMY {
                        let idx = self.nat()?;
                        self.handle(idx)?
                    } else {
                        let s = self.ustr()?;
                        self.handles.push(Some(s.clone()));
                        s
                    };
                    let v = self.r()?;
                    pairs.push((name, v));
                }
                let v = make_fcn_from_pairs(pairs)?;
                self.handles[h] = Some(v.clone());
                Ok(v)
            }
            K_FCNRCD => {
                self.handles.push(None);
                let h = self.handles.len() - 1;
                let n = self.nat()?;
                let info = self.u8()?;
                let mut pairs = vec![];
                if info == 0 {
                    let lo = self.i32()? as i64;
                    self.i32()?;
                    for i in 0..n {
                        let v = self.r()?;
                        pairs.push((Value::Int(lo + i), v));
                    }
                } else {
                    for _ in 0..n {
                        let d = self.r()?;
                        let v = self.r()?;
                        pairs.push((d, v));
                    }
                }
                let v = make_fcn_from_pairs(pairs)?;
                self.handles[h] = Some(v.clone());
                Ok(v)
            }
            _ => fail(format!("ValueInputStream: Can not unpickle a value of kind {}", kind)),
        }
    }
}

// ---- statistics: chi-square goodness of fit (Apache Commons Math ChiSquareTest) ----
fn log_gamma(x: f64) -> f64 {
    let c = [76.18009172947146, -86.50532032941677, 24.01409824083091, -1.231739572450155, 0.1208650973866179e-2, -0.5395239384953e-5];
    let mut y = x;
    let mut tmp = x + 5.5;
    tmp -= (x + 0.5) * tmp.ln();
    let mut ser = 1.000000000190015;
    for cj in c {
        y += 1.0;
        ser += cj / y;
    }
    -tmp + (2.5066282746310005 * ser / x).ln()
}
fn regularized_gamma_p(a: f64, x: f64) -> f64 {
    if x <= 0.0 {
        return 0.0;
    }
    if x < a + 1.0 {
        let mut sum = 1.0 / a;
        let mut del = sum;
        let mut ap = a;
        for _ in 0..10000 {
            ap += 1.0;
            del *= x / ap;
            sum += del;
            if del.abs() < sum.abs() * 1e-15 {
                break;
            }
        }
        return sum * (-x + a * x.ln() - log_gamma(a)).exp();
    }
    let tiny = 1e-300;
    let mut bb = x + 1.0 - a;
    let mut c = 1.0 / tiny;
    let mut d = 1.0 / bb;
    let mut h = d;
    for i in 1..10000 {
        let an = -(i as f64) * (i as f64 - a);
        bb += 2.0;
        d = an * d + bb;
        if d.abs() < tiny {
            d = tiny;
        }
        c = bb + an / c;
        if c.abs() < tiny {
            c = tiny;
        }
        d = 1.0 / d;
        let del = d * c;
        h *= del;
        if (del - 1.0).abs() < 1e-15 {
            break;
        }
    }
    1.0 - (-x + a * x.ln() - log_gamma(a)).exp() * h
}

fn exec_result(exit: i64, stdout: &str, stderr: &str) -> Value {
    make_record(&js_names(&["exitValue", "stdout", "stderr"]), vec![Value::Int(exit), mk_str(stdout), mk_str(stderr)])
}
fn run_process(ev: &Evaluator, _op: &str, command: &[String], env: Option<&[(String, String)]>) -> R<Value> {
    let h = ev.host.borrow().clone();
    match h.exec(command, env) {
        Ok((code, out, err)) => Ok(exec_result(code as i64, &out, &err)),
        Err(e) => fail(e),
    }
}
fn cmd_strings(v: &Value, op: &str) -> R<Vec<String>> {
    let t = match v {
        Value::Tuple(t) => t,
        _ => return one_arg_err(op, "sequence", v),
    };
    let mut out = vec![];
    for x in t.iter() {
        match x {
            Value::Str(s) => out.push(str_of(*s).to_string()),
            _ => return one_arg_err("IOExec", "sequence", x),
        }
    }
    Ok(out)
}
fn env_record(v: &Value, op: &str) -> R<Vec<(String, String)>> {
    let r = match v {
        Value::Record(r) => r,
        _ => return one_arg_err(op, "record", v),
    };
    Ok(r.names
        .iter()
        .zip(r.vals.iter())
        .map(|(n, x)| {
            (
                str_of(*n).to_string(),
                match x {
                    Value::Str(s) => str_of(*s).to_string(),
                    o => fmt(o),
                },
            )
        })
        .collect())
}

pub fn overrides() -> Vec<Ov> {
    let mut v: Vec<Ov> = vec![];
    // FoldBag(op, base, bag): op(accumulator, element), once per copy, elements in normalized domain order.
    v.push(("BagsExt", "FoldBag", 0b1, false, |ev, a| {
        let bag = unlazy(ev, &a[2])?;
        if !is_fcn(&bag) {
            return arg_err(2, "FoldBag", "bag", &bag);
        }
        let (dom, vals) = (domain_elems(&bag)?, fcn_values(&bag)?);
        let mut acc = a[1].clone();
        for i in 0..dom.len() {
            let n = match &vals[i] {
                Value::Int(n) if *n > 0 => *n,
                x => return fail(format!("Applying FoldBag to the following value,\nwhich is not an element of Nat:\n{} (in: {}:>{})", fmt(x), fmt(&dom[i]), fmt(x))),
            };
            for _ in 0..n {
                acc = ev.apply_op(&a[0], &[acc, dom[i].clone()])?;
            }
        }
        Ok(acc)
    }));
    v.push(("SequencesExt", "LongestCommonPrefix", 0, false, |_, a| {
        let s = match &a[0] {
            Value::Set(s) => s,
            x => return one_arg_err("LongestCommonPrefix", "non-empty set", x),
        };
        let e = s.elems()?;
        if e.is_empty() {
            return one_arg_err("LongestCommonPrefix", "non-empty set", &a[0]);
        }
        if let Value::Str(first) = &e[0] {
            let mut prefix: Vec<char> = str_of(*first).chars().collect();
            for o in e {
                let os: Vec<char> = match o {
                    Value::Str(x) => str_of(*x).chars().collect(),
                    _ => return one_arg_err("LongestCommonPrefix", "sequence", &a[0]),
                };
                let mut n = 0;
                while n < prefix.len() && n < os.len() && prefix[n] == os[n] {
                    n += 1;
                }
                prefix.truncate(n);
            }
            return Ok(mk_str(&prefix.into_iter().collect::<String>()));
        }
        let first = match &e[0] {
            Value::Tuple(t) => t,
            _ => return one_arg_err("LongestCommonPrefix", "sequence", &a[0]),
        };
        let mut upper = first.len();
        for o in e {
            let t = match o {
                Value::Tuple(t) => t,
                _ => return one_arg_err("LongestCommonPrefix", "sequence", &a[0]),
            };
            let mut n = 0;
            while n < upper && n < t.len() && val_eq(&first[n], &t[n])? {
                n += 1;
            }
            upper = n;
        }
        Ok(tuple_of(first[..upper].to_vec()))
    }));
    v.push(("SequencesExt", "SelectInSeq", 0b10, false, |ev, a| select_in(ev, a, "SelectInSeq", false, false)));
    v.push(("SequencesExt", "SelectInSubSeq", 0b1000, false, |ev, a| select_in(ev, a, "SelectInSubSeq", false, true)));
    v.push(("SequencesExt", "SelectLastInSeq", 0b10, false, |ev, a| select_in(ev, a, "SelectLastInSeq", true, false)));
    v.push(("SequencesExt", "SelectLastInSubSeq", 0b1000, false, |ev, a| select_in(ev, a, "SelectLastInSubSeq", true, true)));
    v.push(("SequencesExt", "RemoveFirstMatch", 0b10, false, |ev, a| {
        let s = match &a[0] {
            Value::Tuple(t) => t,
            x => return arg_err(0, "RemoveFirstMatch", "sequence", x),
        };
        for i in 0..s.len() {
            if expect_bool(ev.apply_op(&a[1], std::slice::from_ref(&s[i]))?, 1, "RemoveFirstMatch", "boolean-valued function", &a[1])? {
                let mut out = s.to_vec();
                out.remove(i);
                return Ok(tuple_of(out));
            }
        }
        Ok(a[0].clone())
    }));
    v.push(("SequencesExt", "Suffixes", 0, false, |_, a| {
        let s = match &a[0] {
            Value::Tuple(t) => t,
            x => return one_arg_err("Suffixes", "sequence", x),
        };
        let mut out = vec![empty_tuple()];
        for i in (0..s.len()).rev() {
            out.push(Value::Tuple(TupleV::rc(s[i..].to_vec())));
        }
        mk_set(out)
    }));
    v.push(("SequencesExt", "AllSubSeqs", 0, false, |_, a| {
        let s = match &a[0] {
            Value::Tuple(t) => t,
            x => return one_arg_err("AllSubSeqs", "sequence", x),
        };
        if s.len() > 26 {
            return fail(format!("Attempted to enumerate AllSubSeqs of a sequence with {} elements; this is too large.", s.len()));
        }
        let mut out = vec![];
        for m in 0..(1u32 << s.len()) {
            out.push(tuple_of(s.iter().enumerate().filter(|(j, _)| m & (1 << j) != 0).map(|(_, x)| x.clone()).collect()));
        }
        mk_set(out)
    }));
    // ReplaceFirstSubSeq(r, s, t): replace the first occurrence of the subsequence s in t by r.
    v.push(("SequencesExt", "ReplaceFirstSubSeq", 0, false, |_, a| {
        if let (Value::Str(r), Value::Str(s), Value::Str(t)) = (&a[0], &a[1], &a[2]) {
            let (r, s, t) = (str_of(*r), str_of(*s), str_of(*t));
            if s.is_empty() {
                return Ok(mk_str(&format!("{}{}", r, t)));
            }
            return Ok(match t.find(&*s) {
                None => a[2].clone(),
                Some(i) => mk_str(&format!("{}{}{}", &t[..i], r, &t[i + s.len()..])),
            });
        }
        let (rs, ss, ts) = (seq(&a[0], "ReplaceFirstSubSeq", 0)?, seq(&a[1], "ReplaceFirstSubSeq", 1)?, seq(&a[2], "ReplaceFirstSubSeq", 2)?);
        match sub_seq_index(ss, ts, 0)? {
            None => Ok(a[2].clone()),
            Some(i) => {
                let mut out = ts[..i].to_vec();
                out.extend_from_slice(rs);
                out.extend_from_slice(&ts[i + ss.len()..]);
                Ok(tuple_of(out))
            }
        }
    }));
    // ReplaceAllSubSeqs(r, s, t): replace all (non-overlapping, leftmost first) occurrences of s in t by r.
    v.push(("SequencesExt", "ReplaceAllSubSeqs", 0, false, |_, a| {
        if let (Value::Str(r), Value::Str(s), Value::Str(t)) = (&a[0], &a[1], &a[2]) {
            let (r, s, t) = (str_of(*r), str_of(*s), str_of(*t));
            if s.is_empty() {
                let parts: Vec<String> = t.chars().map(|c| c.to_string()).collect();
                return Ok(mk_str(&format!("{}{}", r, parts.join(&r))));
            }
            return Ok(mk_str(&t.replace(&*s, &r)));
        }
        let (rs, ss, ts) = (seq(&a[0], "ReplaceAllSubSeqs", 0)?, seq(&a[1], "ReplaceAllSubSeqs", 1)?, seq(&a[2], "ReplaceAllSubSeqs", 2)?);
        if val_eq(&a[1], &a[2])? {
            return Ok(a[0].clone());
        }
        if val_eq(&a[0], &a[1])? {
            return Ok(a[2].clone());
        }
        let mut out: Vec<Value> = vec![];
        if ss.is_empty() {
            for x in ts.iter() {
                out.extend_from_slice(rs);
                out.push(x.clone());
            }
            return Ok(tuple_of(out));
        }
        let (mut i, mut hit) = (0, false);
        while i < ts.len() {
            if sub_seq_index(ss, ts, i)? == Some(i) {
                out.extend_from_slice(rs);
                i += ss.len();
                hit = true;
            } else {
                out.push(ts[i].clone());
                i += 1;
            }
        }
        Ok(if hit { tuple_of(out) } else { a[2].clone() })
    }));
    v.push(("Combinatorics", "choose", 0, false, |_, a| {
        let n = match &a[0] {
            Value::Int(n) if *n >= 0 => *n,
            x => return arg_err(0, "choose", "natural number", x),
        };
        let k = match &a[1] {
            Value::Int(k) if *k >= 0 => *k,
            x => return arg_err(1, "choose", "natural number", x),
        };
        if k == 0 || k == n {
            return Ok(Value::Int(1));
        }
        if k == 1 || k == n - 1 {
            return Ok(Value::Int(n));
        }
        if n == 0 || k > n {
            return Ok(Value::Int(0));
        }
        let mut r: u128 = 1;
        let mut j = n as u128;
        for i in 1..=(k.min(n - k) as u128) {
            r = r.saturating_mul(j) / i;
            j -= 1;
        }
        if r > 2147483647 {
            return fail(format!("Overflow when computing {}choose{}", n, k));
        }
        Ok(Value::Int(r as i64))
    }));
    // Flips only the bits below the highest set bit (the TLA+ definition has no word size to work with).
    v.push(("Bitwise", "Not", 0, false, |_, a| {
        let x = int(&a[0], "Not", 0)? as i32;
        let sh = (x.leading_zeros() as i32 - 1) & 31; // JS shift counts are taken modulo 32
        Ok(Value::Int((!x & (2147483647i32 >> sh)) as i64))
    }));
    v.push(("Bitwise", "shiftR", 0, false, |_, a| {
        let x = int(&a[0], "shiftR", 0)? as i32 as u32;
        let n = (int(&a[1], "shiftR", 1)? as u32) & 31;
        Ok(Value::Int((x >> n) as i32 as i64))
    }));
    v.push(("DyadicRationals", "Reduce", 0, false, |_, a| {
        let p = match &a[0] {
            Value::Record(r) => r,
            x => return one_arg_err("Half", "record", x),
        };
        let get = |n: &str| -> R<i64> {
            match p.get(str_id(n)) {
                Some(v) => int(v, "Reduce", 0),
                None => fail("The first argument of Reduce should be an integer, but instead it is:\n<undefined>".into()),
            }
        };
        let (num, den) = (get("num")?, get("den")?);
        let (mut x, mut y) = (num.abs(), den.abs());
        while y != 0 {
            let t = x % y;
            x = y;
            y = t;
        }
        if x == 1 {
            return Ok(a[0].clone());
        }
        if x == 0 {
            return fail("The second argument of \\div is 0.".into());
        }
        Ok(make_record(&js_names(&["den", "num"]), vec![Value::Int(den / x), Value::Int(num / x)]))
    }));
    // TRUE iff the chi-square goodness-of-fit test does NOT reject, at significance alpha, that `actual` follows `expected`.
    v.push(("Statistics", "ChiSquare", 0, false, |_, a| {
        if !is_fcn(&a[0]) {
            return arg_err(0, "ChiSquare", "function", &a[0]);
        }
        if !is_fcn(&a[1]) {
            return arg_err(1, "ChiSquare", "function", &a[1]);
        }
        let alpha_s = match &a[2] {
            Value::Str(s) => str_of(*s),
            x => return arg_err(2, "ChiSquare", "StringValue representing a double in (0, .5]", x),
        };
        let mut exp = vec![];
        for x in fcn_values(&a[0])? {
            exp.push(int(x, "ChiSquare", 0)? as f64);
        }
        let mut act = vec![];
        for x in fcn_values(&a[1])? {
            act.push(int(x, "ChiSquare", 1)? as f64);
        }
        let alpha: f64 = alpha_s.trim().parse().unwrap_or(f64::NAN);
        if !(alpha > 0.0 && alpha <= 0.5) {
            return fail(format!("out of bounds significance level ({}), must be between 0 and 0.5", alpha_s));
        }
        if exp.len() < 2 {
            return fail(format!("{} is smaller than the minimum (2)", exp.len()));
        }
        if exp.len() != act.len() {
            return fail(format!("{} != {}", exp.len(), act.len()));
        }
        for e in &exp {
            if *e <= 0.0 {
                return fail(format!("element is not strictly positive: {}", e));
            }
        }
        for o in &act {
            if *o < 0.0 {
                return fail(format!("element is negative: {}", o));
            }
        }
        let (sum_e, sum_o): (f64, f64) = (exp.iter().sum(), act.iter().sum());
        let rescale = (sum_e - sum_o).abs() > 10e-6;
        let ratio = if rescale { sum_o / sum_e } else { 1.0 };
        let mut chi = 0.0;
        for i in 0..exp.len() {
            let e = if rescale { ratio * exp[i] } else { exp[i] };
            let dev = act[i] - e;
            chi += dev * dev / e;
        }
        let p = 1.0 - regularized_gamma_p((exp.len() as f64 - 1.0) / 2.0, chi / 2.0);
        Ok(Value::Bool(!(p < alpha)))
    }));
    v.push(("Graphs", "SimplePath", 0, false, |_, a| simple_path("graph", tuple_edge, Mode::Forward, &a[0])));
    v.push(("Graphs", "AreConnectedIn", 0, false, |_, a| are_connected_in("graph", tuple_edge, Mode::Forward, &a[0], &a[1], &a[2])));
    v.push(("Graphs", "IsStronglyConnected", 0, false, |_, a| {
        let g = to_graph("IsStronglyConnected", 0, "graph", &a[0])?;
        let nodes = g.nodes.elems()?;
        if nodes.is_empty() {
            return Ok(Value::Bool(true));
        }
        Ok(Value::Bool(
            reachable(&nodes[0], &adjacency(&g, tuple_edge, Mode::Forward)?).len() == nodes.len() && reachable(&nodes[0], &adjacency(&g, tuple_edge, Mode::Transpose)?).len() == nodes.len(),
        ))
    }));
    v.push(("UndirectedGraphs", "SimplePath", 0, false, |_, a| simple_path("undirected graph", pair_edge, Mode::Symmetric, &a[0])));
    v.push(("UndirectedGraphs", "AreConnectedIn", 0, false, |_, a| are_connected_in("undirected graph", pair_edge, Mode::Symmetric, &a[0], &a[1], &a[2])));
    v.push(("UndirectedGraphs", "ConnectedComponents", 0, false, |_, a| {
        let g = to_graph("ConnectedComponents", 0, "undirected graph", &a[0])?;
        let nodes = g.nodes.elems()?;
        let keys: Vec<String> = nodes.iter().map(key).collect();
        let mut parent: Vec<usize> = (0..nodes.len()).collect();
        fn find(parent: &mut [usize], mut k: usize) -> usize {
            let mut root = k;
            while parent[root] != root {
                root = parent[root];
            }
            while k != root {
                let next = parent[k];
                parent[k] = root;
                k = next;
            }
            root
        }
        for e in &g.edges {
            let (p0, p1) = match pair_edge(e)? {
                Some(p) => p,
                None => continue,
            };
            if !g.nodes.contains(&p0)? || !g.nodes.contains(&p1)? {
                continue;
            }
            let (i0, i1) = (keys.iter().position(|k| *k == key(&p0)), keys.iter().position(|k| *k == key(&p1)));
            if let (Some(i0), Some(i1)) = (i0, i1) {
                let (x, y) = (find(&mut parent, i0), find(&mut parent, i1));
                if x != y {
                    parent[y] = x;
                }
            }
        }
        let mut comps: Vec<(usize, Vec<Value>)> = vec![];
        for (i, n) in nodes.iter().enumerate() {
            let rep = find(&mut parent, i);
            match comps.iter_mut().find(|c| c.0 == rep) {
                Some(c) => c.1.push(n.clone()),
                None => comps.push((rep, vec![n.clone()])),
            }
        }
        mk_set(comps.into_iter().map(|c| SetV::of(c.1)).collect())
    }));
    v.push(("Json", "ToJson", 0, false, |ev, a| Ok(mk_str(&to_json(ev, &a[0])?))));
    v.push(("Json", "ToJsonArray", 0, false, |ev, a| {
        let v = unlazy(ev, &a[0])?;
        match &v {
            Value::Tuple(_) | Value::Record(_) | Value::Fcn(_) => Ok(mk_str(&to_json(ev, &v)?)),
            Value::Set(s) if s.enumerable() => Ok(mk_str(&to_json(ev, &v)?)),
            _ => json_unsupported(&v),
        }
    }));
    v.push(("Json", "ToJsonObject", 0, false, |ev, a| {
        let v = unlazy(ev, &a[0])?;
        match &v {
            // TLC prints a tuple *literal* as {"0":..,"1":..} here but a function with domain 1..n as an array; the two
            // are the same value, so the array form is used for every non-empty sequence.
            Value::Tuple(t) => {
                if t.is_empty() {
                    Ok(mk_str("{}"))
                } else {
                    Ok(mk_str(&to_json(ev, &v)?))
                }
            }
            Value::Record(_) | Value::Fcn(_) => Ok(mk_str(&to_json(ev, &v)?)),
            _ => json_unsupported(&v),
        }
    }));
    v.push(("Json", "JsonSerialize", 0, false, |ev, a| {
        let path = string(&a[0], "JsonSerialize", 0)?;
        if !matches!(a[1], Value::Tuple(_) | Value::Record(_)) {
            return arg_err(1, "JsonSerialize", "sequence or record", &a[1]);
        }
        let text = to_json(ev, &a[1])?;
        host_write(ev.host.borrow().write_file(&path, text.as_bytes()))?;
        Ok(Value::Bool(true))
    }));
    v.push(("Json", "ndJsonSerialize", 0, false, |ev, a| {
        let path = string(&a[0], "ndJsonSerialize", 0)?;
        let t = match &a[1] {
            Value::Tuple(t) => t,
            x => return arg_err(1, "ndJsonSerialize", "sequence", x),
        };
        let mut text = String::new();
        for x in t.iter() {
            text += &to_json(ev, x)?;
            text.push('\n');
        }
        host_write(ev.host.borrow().write_file(&path, text.as_bytes()))?;
        Ok(Value::Bool(true))
    }));
    // Appends the record's values (and, if `headers`, first its field names) joined by `delim`.
    v.push(("CSV", "CSVWriteRecord", 0, false, |ev, a| {
        let rec = match &a[0] {
            Value::Record(r) => r,
            x => return one_arg_err("CSVWriteRecord", "record", x),
        };
        let delim = string(&a[1], "CSVWriteRecord", 1)?;
        let path = string(&a[3], "CSVWriteRecord", 3)?;
        let headers = match &a[2] {
            Value::Bool(b) => *b,
            x => return arg_err(2, "CSVWriteRecord", "boolean", x),
        };
        let mut text = String::new();
        if headers {
            text += &rec.names.iter().map(|n| str_of(*n).to_string()).collect::<Vec<_>>().join(&delim);
            text.push('\n');
        }
        text += &rec.vals.iter().map(fmt).collect::<Vec<_>>().join(&delim);
        text.push('\n');
        host_write(ev.host.borrow().append_file(&path, text.as_bytes()))?;
        Ok(Value::Bool(true))
    }));
    // Appends String.format(template, values printed as TLA+ values) as one line.
    v.push(("CSV", "CSVWrite", 0, false, |ev, a| {
        let template = string(&a[0], "CSVWrite", 0)?;
        let path = string(&a[2], "CSVWrite", 2)?;
        let t = match &a[1] {
            Value::Tuple(t) => t,
            x => return one_arg_err("CSVWrite", "sequence", x),
        };
        let text = java_format(&template, &t.iter().map(fmt).collect::<Vec<_>>())? + "\n";
        host_write(ev.host.borrow().append_file(&path, text.as_bytes()))?;
        Ok(Value::Bool(true))
    }));
    v.push(("CSV", "CSVRead", 0, false, |ev, a| {
        let cols = match &a[0] {
            Value::Tuple(t) => t,
            x => return one_arg_err("CSVRead", "sequence", x),
        };
        let mut names: Vec<Value> = vec![];
        for (i, n) in cols.iter().enumerate() {
            match n {
                Value::Str(_) => names.push(n.clone()),
                _ => return fail(format!("Column name {} of CSVRead should be a string, but instead it is:\n{}", i + 1, fmt(n))),
            }
        }
        let delim = string(&a[1], "CSVRead", 1)?;
        let path = string(&a[2], "CSVRead", 2)?;
        if !ev.host.borrow().exists(&path) {
            return Ok(empty_tuple());
        }
        let mut rows = vec![];
        for line in split_lines(&read_text(ev, &path)?) {
            // Java's String.split: the delimiter is a regex (literal delimiters are what specs use); trailing
            // empty strings are removed
            let mut cells: Vec<&str> = line.split(&*delim).collect();
            while cells.len() > 1 && cells.last().map_or(false, |c| c.is_empty()) {
                cells.pop();
            }
            for c in &cells {
                str_id(c);
            }
            // surplus fields are ignored; a short line yields a record without the trailing columns
            let pairs: Vec<(Value, Value)> = names.iter().take(cells.len()).cloned().zip(cells.iter().map(|c| mk_str(c))).collect();
            rows.push(make_fcn_from_pairs(pairs)?);
        }
        Ok(tuple_of(rows))
    }));
    v.push(("CSV", "CSVRecords", 0, false, |ev, a| {
        let path = string(&a[0], "CSVRecords", 0)?;
        if !ev.host.borrow().exists(&path) {
            return Ok(Value::Int(0));
        }
        Ok(Value::Int(split_lines(&read_text(ev, &path)?).len() as i64))
    }));
    // TLC's binary value format (uncompressed only).
    v.push(("IOUtils", "IOSerialize", 0, false, |ev, a| {
        let path = string(&a[1], "IOSerialize", 1)?;
        if !matches!(a[2], Value::Bool(false)) {
            return fail("IOSerialize: compressed (gzip) output is not supported; pass FALSE as the third argument.".into());
        }
        let bytes = encode_value(ev, &a[0])?;
        host_write(ev.host.borrow().write_file(&path, &bytes))?;
        Ok(Value::Bool(true))
    }));
    v.push(("IOUtils", "IODeserialize", 0, false, |ev, a| {
        let path = string(&a[0], "IODeserialize", 0)?;
        if !matches!(a[1], Value::Bool(false)) {
            return fail("IODeserialize: compressed (gzip) input is not supported; pass FALSE as the second argument.".into());
        }
        let h = ev.host.borrow().clone();
        if !h.exists(&path) {
            return fail(format!("{} (No such file or directory)", path));
        }
        let bytes = match h.read_file(&path) {
            Ok(b) => b,
            Err(e) => return fail(e),
        };
        Dec { b: &bytes, p: 0, handles: vec![] }.r()
    }));
    // Serialize(value, dest, options) / Deserialize(src, options): only the plain-text format is implemented (as in TLC).
    v.push(("IOUtils", "Serialize", 0, false, |ev, a| {
        let opts = match &a[2] {
            Value::Record(r) if matches!(r.get(str_id("format")), Some(Value::Str(s)) if &*str_of(*s) == "TXT") => r,
            _ => return fail("Serialize: only [format |-> \"TXT\", charset |-> ..., openOptions |-> ...] is supported.".into()),
        };
        let (oo, cs) = (opts.get(str_id("openOptions")), opts.get(str_id("charset")));
        let bad_params = || Ok(exec_result(1, "", "Serialize error invalid parameters: payload and file must be strings, charset a string and openOptions a sequence of strings"));
        let (payload, file) = match (&a[0], &a[1]) {
            (Value::Str(p), Value::Str(f)) => (str_of(*p), str_of(*f)),
            _ => return bad_params(),
        };
        let o: Vec<String> = match (oo, cs) {
            (Some(Value::Tuple(t)), Some(Value::Str(_))) if t.iter().all(|x| matches!(x, Value::Str(_))) => t.iter().map(|x| if let Value::Str(s) = x { str_of(*s).to_string() } else { String::new() }).collect(),
            _ => return bad_params(),
        };
        let h = ev.host.borrow().clone();
        let run = || -> Result<(), String> {
            const KNOWN: [&str; 10] = ["READ", "WRITE", "APPEND", "TRUNCATE_EXISTING", "CREATE", "CREATE_NEW", "DELETE_ON_CLOSE", "SPARSE", "SYNC", "DSYNC"];
            if let Some(bad) = o.iter().find(|x| !KNOWN.contains(&x.as_str())) {
                return Err(format!("java.lang.IllegalArgumentException: No enum constant java.nio.file.StandardOpenOption.{}", bad));
            }
            let exists = h.exists(&file);
            let has = |x: &str| o.iter().any(|y| y == x);
            if has("CREATE_NEW") && exists {
                return Err(format!("java.nio.file.FileAlreadyExistsException: {}", file));
            }
            if !o.is_empty() && !has("CREATE") && !has("CREATE_NEW") && !exists {
                return Err(format!("java.nio.file.NoSuchFileException: {}", file));
            }
            if has("APPEND") { h.append_file(&file, payload.as_bytes()) } else { h.write_file(&file, payload.as_bytes()) }
        };
        Ok(match run() {
            Ok(()) => exec_result(0, "Finish writing to the file with success!", ""),
            Err(e) => exec_result(1, "", &format!("Serialize error writing to the file: {}", e)),
        })
    }));
    v.push(("IOUtils", "Deserialize", 0, false, |ev, a| {
        let opts = match &a[1] {
            Value::Record(r) if matches!(r.get(str_id("format")), Some(Value::Str(s)) if &*str_of(*s) == "TXT") => r,
            _ => return fail("Deserialize: only [format |-> \"TXT\", charset |-> ...] is supported.".into()),
        };
        let file = match (&a[0], opts.get(str_id("charset"))) {
            (Value::Str(f), Some(Value::Str(_))) => str_of(*f),
            _ => return Ok(exec_result(1, "", "Deserialize error invalid parameters: file and charset must be strings")),
        };
        let h = ev.host.borrow().clone();
        if !h.exists(&file) {
            return Ok(exec_result(1, "", &format!("Deserialize error reading from the file: java.nio.file.NoSuchFileException: {}", file)));
        }
        Ok(match h.read_file(&file) {
            Ok(b) => exec_result(0, &String::from_utf8_lossy(&b), ""),
            Err(e) => exec_result(1, "", &format!("Deserialize error reading from the file: {}", e)),
        })
    }));
    v.push(("IOUtils", "IOExec", 0, false, |ev, a| run_process(ev, "IOExec", &cmd_strings(&a[0], "IOExec")?, None)));
    v.push(("IOUtils", "IOEnvExec", 0, false, |ev, a| {
        let env = env_record(&a[0], "IOEnvExec")?;
        run_process(ev, "IOEnvExec", &cmd_strings(&a[1], "IOEnvExec")?, Some(&env))
    }));
    v.push(("IOUtils", "IOExecTemplate", 0, false, |ev, a| {
        let (cmd, params) = (cmd_strings(&a[0], "IOExecTemplate")?, cmd_strings(&a[1], "IOExecTemplate")?);
        let mut c = vec![];
        for x in &cmd {
            c.push(java_format(x, &params)?);
        }
        run_process(ev, "IOExecTemplate", &c, None)
    }));
    v.push(("IOUtils", "IOEnvExecTemplate", 0, false, |ev, a| {
        let env = env_record(&a[0], "IOEnvExecTemplate")?;
        let (cmd, params) = (cmd_strings(&a[1], "IOEnvExecTemplate")?, cmd_strings(&a[2], "IOEnvExecTemplate")?);
        let mut c = vec![];
        for x in &cmd {
            c.push(java_format(x, &params)?);
        }
        run_process(ev, "IOEnvExecTemplate", &c, Some(&env))
    }));
    let _ = Ordering::Equal;
    v
}
