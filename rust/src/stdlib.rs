//! Native implementations of the TLA+ standard modules (port of stdlib.ts) and of the hot operators
//! of the bundled community modules (subset of community.ts).
use crate::ast::Param;
use crate::eval::{Evaluator, RegKey};
use crate::intern::*;
use crate::modules::*;
use crate::value::*;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::rc::Rc;

const ORD: [&str; 5] = ["first", "second", "third", "fourth", "fifth"];
fn fail<T>(msg: String) -> R<T> {
    eval_err(msg)
}
fn int(v: &Value, op: &str, i: usize) -> R<i64> {
    match v {
        Value::Int(x) => Ok(*x),
        _ => fail(format!("The {} argument of {} should be an integer, but instead it is:\n{}", ORD[i], op, fmt(v))),
    }
}
fn seq<'a>(v: &'a Value, op: &str, i: usize) -> R<&'a Rc<Vec<Value>>> {
    match v {
        Value::Tuple(t) => Ok(t),
        _ => fail(format!("The {} argument of {} should be a sequence, but instead it is:\n{}", ORD[i], op, fmt(v))),
    }
}
fn set<'a>(v: &'a Value, op: &str, i: usize) -> R<&'a Rc<SetV>> {
    match v {
        Value::Set(s) => Ok(s),
        _ => fail(format!("The {} argument of {} should be a set, but instead it is:\n{}", ORD[i], op, fmt(v))),
    }
}
fn check_int(n: i64, what: impl FnOnce() -> String) -> R<Value> {
    if n > 2147483647 || n < -2147483648 {
        return fail(format!("Overflow when computing {}", what()));
    }
    Ok(Value::Int(n))
}
fn arg_err<T>(i: usize, op: &str, what: &str, v: &Value) -> R<T> {
    fail(format!("The {} argument of {} should be a {}, but instead it is:\n{}", ORD[i], op, what, fmt(v)))
}
fn one_arg_err<T>(op: &str, what: &str, v: &Value) -> R<T> {
    fail(format!("The argument of {} should be a {}, but instead it is:\n{}", op, what, fmt(v)))
}
fn tuple_of(v: Vec<Value>) -> Value {
    if v.is_empty() { empty_tuple() } else { Value::Tuple(Rc::new(v)) }
}
fn string(id: StrId) -> Rc<str> {
    str_of(id)
}
fn mk_str(s: &str) -> Value {
    Value::Str(str_id(s))
}
fn unlazy(ev: &Evaluator, v: &Value) -> R<Value> {
    match v {
        Value::LazyFcn(f) => f.force(ev),
        v => Ok(v.clone()),
    }
}

struct MB {
    info: ModuleInfo,
    name: Name,
}
impl MB {
    fn new(nm: &str, exts: &[&Rc<ModuleInfo>]) -> MB {
        let name = name(nm);
        let mut info = ModuleInfo { name: Some(name), ..Default::default() };
        for e in exts {
            for (k, v) in &e.exports.items {
                info.syms.set(*k, *v);
                info.exports.set(*k, *v);
            }
        }
        MB { info, name }
    }
    fn add(&mut self, n: &str, arity: usize, bi: Builtin) {
        let params: Vec<Param> = (0..arity).map(|i| Param { name: name(&format!("p{}", i)), arity: if bi.ops & (1 << i) != 0 { 1 } else { 0 } }).collect();
        let def = Def::new(name(n), params, None, self.name, false, [0; 4]);
        def.builtin.set(Some(leak(bi)));
        let def = leak(def);
        self.info.syms.set(def.name, Sym::Def(def));
        self.info.exports.set(def.name, Sym::Def(def));
        self.info.own_defs.push(def);
    }
    fn op(&mut self, n: &str, arity: usize, f: NativeFn) {
        self.add(n, arity, Builtin { f: BFn::Native(f), ops: 0, lazy: false });
    }
    fn op_ops(&mut self, n: &str, arity: usize, ops: u32, f: NativeFn) {
        self.add(n, arity, Builtin { f: BFn::Native(f), ops, lazy: false });
    }
    fn op_lazy(&mut self, n: &str, arity: usize, f: NativeFn) {
        self.add(n, arity, Builtin { f: BFn::Native(f), ops: 0, lazy: true });
    }
    fn val(&mut self, n: &str, v: Value) {
        self.add(n, 0, Builtin { f: BFn::Const(v), ops: 0, lazy: false });
    }
    fn done(self) -> Rc<ModuleInfo> {
        Rc::new(self.info)
    }
}

fn inf(k: Inf) -> Value {
    Value::Set(Rc::new(SetV::new(SetK::Inf(k))))
}

pub fn global_defs() -> OrdMap {
    let mut g = MB::new("<builtin>", &[]);
    g.val("BOOLEAN", SetV::of(vec![Value::Bool(false), Value::Bool(true)]));
    g.val("STRING", inf(Inf::String));
    g.info.syms
}

fn print(s: &str) {
    println!("{}", s);
}

fn bag_pairs<'a>(b: &'a Value, op: &str) -> R<(std::borrow::Cow<'a, [Value]>, &'a [Value])> {
    if !is_fcn(b) {
        return fail(format!("Attempted to apply {} to the non-bag value:\n{}", op, fmt(b)));
    }
    Ok((domain_elems(b)?, fcn_values(b)?))
}
fn bag_n(v: &Value) -> i64 {
    match v {
        Value::Int(i) => *i,
        _ => 0,
    }
}
fn mk_bag(m: Vec<(Value, i64)>) -> R<Value> {
    make_fcn_from_pairs(m.into_iter().filter(|p| p.1 > 0).map(|(d, n)| (d, Value::Int(n))).collect())
}

fn reg_key(v: &Value, op: &str) -> R<RegKey> {
    Ok(RegKey::Int(int(v, op, 0)?))
}

pub fn build_stdlib() -> HashMap<Name, Rc<ModuleInfo>> {
    let mut m = MB::new("Naturals", &[]);
    m.op("+", 2, |_, a| {
        if let (Value::Int(x), Value::Int(y)) = (&a[0], &a[1]) {
            let r = x + y;
            if r <= 2147483647 && r >= -2147483648 {
                return Ok(Value::Int(r));
            }
        }
        check_int(int(&a[0], "+", 0)? + int(&a[1], "+", 1)?, || format!("{} + {}", fmt(&a[0]), fmt(&a[1])))
    });
    m.op("-", 2, |_, a| {
        if let (Value::Int(x), Value::Int(y)) = (&a[0], &a[1]) {
            let r = x - y;
            if r <= 2147483647 && r >= -2147483648 {
                return Ok(Value::Int(r));
            }
        }
        check_int(int(&a[0], "-", 0)? - int(&a[1], "-", 1)?, || format!("{} - {}", fmt(&a[0]), fmt(&a[1])))
    });
    m.op("*", 2, |_, a| check_int(int(&a[0], "*", 0)?.saturating_mul(int(&a[1], "*", 1)?), || format!("{} * {}", fmt(&a[0]), fmt(&a[1]))));
    m.op("^", 2, |_, a| {
        let (b, e) = (int(&a[0], "^", 0)?, int(&a[1], "^", 1)?);
        if e < 0 {
            return fail(format!("The second argument of ^ should be a natural number, but instead it is:\n{}", e));
        }
        let r = b.checked_pow(e.min(u32::MAX as i64) as u32).unwrap_or(i64::MAX);
        check_int(r, || format!("{} ^ {}", b, e))
    });
    m.op("<", 2, |_, a| Ok(Value::Bool(int(&a[0], "<", 0)? < int(&a[1], "<", 1)?)));
    m.op(">", 2, |_, a| Ok(Value::Bool(int(&a[0], ">", 0)? > int(&a[1], ">", 1)?)));
    m.op("<=", 2, |_, a| Ok(Value::Bool(int(&a[0], "<=", 0)? <= int(&a[1], "<=", 1)?)));
    m.op(">=", 2, |_, a| Ok(Value::Bool(int(&a[0], ">=", 0)? >= int(&a[1], ">=", 1)?)));
    m.op("..", 2, |_, a| Ok(Value::Set(Rc::new(SetV::new(SetK::Interval(int(&a[0], "..", 0)?, int(&a[1], "..", 1)?))))));
    m.op("\\div", 2, |_, a| {
        let (x, y) = (int(&a[0], "\\div", 0)?, int(&a[1], "\\div", 1)?);
        if y == 0 {
            return fail("The second argument of \\div is 0.".into());
        }
        let q = x / y;
        Ok(Value::Int(if x % y != 0 && ((x < 0) != (y < 0)) { q - 1 } else { q }))
    });
    m.op("%", 2, |_, a| {
        let (x, y) = (int(&a[0], "%", 0)?, int(&a[1], "%", 1)?);
        if y <= 0 {
            return fail(format!("The second argument of % should be a positive number, but instead it is:\n{}", y));
        }
        let r = x % y;
        Ok(Value::Int(if r < 0 { r + y } else { r }))
    });
    m.val("Nat", inf(Inf::Nat));
    let naturals = m.done();

    let mut m = MB::new("Integers", &[&naturals]);
    m.val("Int", inf(Inf::Int));
    m.op("-.", 1, |_, a| check_int(-int(&a[0], "-.", 0)?, || format!("-{}", fmt(&a[0]))));
    let integers = m.done();

    let mut m = MB::new("Reals", &[&integers]);
    m.val("Real", inf(Inf::Real));
    m.op("/", 2, |_, a| {
        let (x, y) = (int(&a[0], "/", 0)?, int(&a[1], "/", 1)?);
        if y == 0 {
            return fail("The second argument of / is 0.".into());
        }
        if x % y != 0 {
            return fail("TLC cannot handle real numbers that are not integers.".into());
        }
        Ok(Value::Int(x / y))
    });
    m.op("Infinity", 0, |_, _| fail("TLC cannot evaluate Infinity.".into()));
    let reals = m.done();

    let mut m = MB::new("Sequences", &[]);
    m.op("Seq", 1, |_, a| Ok(Value::Set(Rc::new(SetV::new(SetK::Seq(set(&a[0], "Seq", 0)?.clone()))))));
    m.op("Len", 1, |_, a| match &a[0] {
        Value::Str(s) => Ok(Value::Int(string(*s).encode_utf16().count() as i64)),
        v => Ok(Value::Int(seq(v, "Len", 0)?.len() as i64)),
    });
    m.op("\\o", 2, |_, a| {
        if let (Value::Str(x), Value::Str(y)) = (&a[0], &a[1]) {
            return Ok(mk_str(&format!("{}{}", string(*x), string(*y))));
        }
        let (x, y) = (seq(&a[0], "\\o", 0)?, seq(&a[1], "\\o", 1)?);
        if x.is_empty() {
            return Ok(a[1].clone());
        }
        if y.is_empty() {
            return Ok(a[0].clone());
        }
        let mut v = Vec::with_capacity(x.len() + y.len());
        v.extend_from_slice(x);
        v.extend_from_slice(y);
        Ok(Value::Tuple(Rc::new(v)))
    });
    m.op("Append", 2, |_, a| {
        let s = seq(&a[0], "Append", 0)?;
        let mut v = Vec::with_capacity(s.len() + 1);
        v.extend_from_slice(s);
        v.push(a[1].clone());
        Ok(Value::Tuple(Rc::new(v)))
    });
    m.op("Head", 1, |_, a| {
        let s = seq(&a[0], "Head", 0)?;
        if s.is_empty() {
            return fail("Attempted to apply Head to the empty sequence.".into());
        }
        Ok(s[0].clone())
    });
    m.op("Tail", 1, |_, a| {
        let s = seq(&a[0], "Tail", 0)?;
        if s.is_empty() {
            return fail("Attempted to apply Tail to the empty sequence.".into());
        }
        Ok(Value::Tuple(Rc::new(s[1..].to_vec())))
    });
    m.op("SubSeq", 3, |_, a| {
        if let Value::Str(s) = &a[0] {
            let (m, n) = (int(&a[1], "SubSeq", 1)?, int(&a[2], "SubSeq", 2)?);
            let st = string(*s);
            let chars: Vec<char> = st.chars().collect();
            let lo = (m - 1).clamp(0, chars.len() as i64) as usize;
            let hi = n.clamp(0, chars.len() as i64) as usize;
            let out: String = if lo < hi { chars[lo..hi].iter().collect() } else { String::new() };
            return Ok(mk_str(&out));
        }
        let (s, m, n) = (seq(&a[0], "SubSeq", 0)?, int(&a[1], "SubSeq", 1)?, int(&a[2], "SubSeq", 2)?);
        if m > n {
            return Ok(empty_tuple());
        }
        if m < 1 || n > s.len() as i64 {
            return fail(format!(
                "The {} argument of SubSeq must be in the domain of its first argument:\n{}\n, but instead it is\n{}",
                if m < 1 { "second" } else { "third" },
                fmt(&a[0]),
                if m < 1 { m } else { n }
            ));
        }
        Ok(Value::Tuple(Rc::new(s[(m - 1) as usize..n as usize].to_vec())))
    });
    m.op_ops("SelectSeq", 2, 0b10, |ev, a| {
        let s = seq(&a[0], "SelectSeq", 0)?;
        let mut out = Vec::new();
        for x in s.iter() {
            match ev.apply_op(&a[1], std::slice::from_ref(x))? {
                Value::Bool(true) => out.push(x.clone()),
                Value::Bool(false) => {}
                r => return fail(format!("The second argument of SelectSeq must return a boolean, but it returned:\n{}", fmt(&r))),
            }
        }
        Ok(Value::Tuple(Rc::new(out)))
    });
    let sequences = m.done();

    let mut m = MB::new("FiniteSets", &[]);
    m.op("IsFiniteSet", 1, |_, a| Ok(Value::Bool(set(&a[0], "IsFiniteSet", 0)?.enumerable())));
    m.op("Cardinality", 1, |_, a| {
        let s = set(&a[0], "Cardinality", 0)?;
        if !s.enumerable() {
            return fail(format!("Attempted to compute the cardinality of the infinite set {}", fmt_set(s)));
        }
        Ok(Value::Int(s.size()?))
    });
    let finite_sets = m.done();

    let mut m = MB::new("TLC", &[]);
    m.op("Print", 2, |_, a| {
        print(&format!("{}  {}", fmt(&a[0]), fmt(&a[1])));
        Ok(a[1].clone())
    });
    m.op("PrintT", 1, |_, a| {
        print(&fmt(&a[0]));
        Ok(Value::Bool(true))
    });
    m.op("Assert", 2, |_, a| match &a[0] {
        Value::Bool(true) => Ok(Value::Bool(true)),
        Value::Bool(false) => err("assert", format!("The first argument of Assert evaluated to FALSE; the second argument was:\n{}", fmt(&a[1]))),
        v => fail(format!("The first argument of Assert should be a boolean, but instead it is:\n{}", fmt(v))),
    });
    m.op("JavaTime", 0, |_, _| {
        let s = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0);
        Ok(Value::Int((s & 0x7fffffff) as i64))
    });
    m.op("TLCGet", 1, |ev, a| {
        ev.st_touch.set(ev.st_touch.get() + 1); // never a constant: definitions using it must not be cached
        if let Value::Str(k) = &a[0] {
            let key = string(*k);
            if key.starts_with("s:") {
                return match ev.registers.borrow().get(&RegKey::Str(*k)) {
                    Some(v) => Ok(v.clone()),
                    None => fail(format!("TLCGet({}) was undefined.", key)),
                };
            }
            if &*key == "all" || &*key == "all:named" {
                let mut pairs = vec![];
                for (k, v) in ev.registers.borrow().iter() {
                    match k {
                        RegKey::Str(s) if &*key == "all:named" => pairs.push((Value::Str(*s), Value::Tuple(Rc::new(vec![v.clone()])))),
                        RegKey::Int(i) if &*key == "all" => pairs.push((Value::Int(*i), Value::Tuple(Rc::new(vec![v.clone()])))),
                        _ => {}
                    }
                }
                return make_fcn_from_pairs(pairs);
            }
            return match tlc_get(ev, &key) {
                Some(v) => Ok(v),
                None => fail(format!("TLCGet({}) is not supported.", fmt(&a[0]))),
            };
        }
        match ev.registers.borrow().get(&reg_key(&a[0], "TLCGet")?) {
            Some(v) => Ok(v.clone()),
            None => fail(format!("TLCGet({}) was undefined.", fmt(&a[0]))),
        }
    });
    m.op("TLCSet", 2, |ev, a| {
        if let Value::Str(k) = &a[0] {
            let key = string(*k);
            if key.starts_with("s:") {
                ev.registers.borrow_mut().insert(RegKey::Str(*k), a[1].clone());
            } else if &*key == "exit" && matches!(a[1], Value::Bool(true)) && ev.stats.active.get() {
                ev.stats.stop_requested.set(true);
            }
            return Ok(Value::Bool(true));
        }
        ev.registers.borrow_mut().insert(reg_key(&a[0], "TLCSet")?, a[1].clone());
        Ok(Value::Bool(true))
    });
    m.op(":>", 2, |_, a| Ok(make_fcn(std::slice::from_ref(&a[0]), vec![a[1].clone()])));
    m.op("@@", 2, |_, a| {
        if !is_fcn(&a[0]) {
            return fail(format!("The first argument of @@ should be a function, but instead it is:\n{}", fmt(&a[0])));
        }
        if !is_fcn(&a[1]) {
            return fail(format!("The second argument of @@ should be a function, but instead it is:\n{}", fmt(&a[1])));
        }
        let (d0, v0, d1, v1) = (domain_elems(&a[0])?, fcn_values(&a[0])?, domain_elems(&a[1])?, fcn_values(&a[1])?);
        if d1.is_empty() {
            return Ok(a[0].clone());
        }
        if d0.is_empty() {
            return Ok(a[1].clone());
        }
        // first function wins: list its pairs first; make_fcn_from_pairs keeps the first of equal keys (stable sort)
        let mut pairs: Vec<(Value, Value)> = Vec::with_capacity(d0.len() + d1.len());
        for i in 0..d0.len() {
            pairs.push((d0[i].clone(), v0[i].clone()));
        }
        for i in 0..d1.len() {
            pairs.push((d1[i].clone(), v1[i].clone()));
        }
        make_fcn_from_pairs(pairs)
    });
    m.op("Permutations", 1, |_, a| {
        let s = set(&a[0], "Permutations", 0)?.elems()?;
        let mut out = vec![];
        let mut used = vec![false; s.len()];
        let mut cur: Vec<Value> = vec![];
        fn rec(s: &[Value], used: &mut Vec<bool>, cur: &mut Vec<Value>, out: &mut Vec<Value>) {
            if cur.len() == s.len() {
                out.push(make_fcn(s, cur.clone()));
                return;
            }
            for i in 0..s.len() {
                if used[i] {
                    continue;
                }
                used[i] = true;
                cur.push(s[i].clone());
                rec(s, used, cur, out);
                cur.pop();
                used[i] = false;
            }
        }
        rec(s, &mut used, &mut cur, &mut out);
        mk_set(out)
    });
    m.op_ops("SortSeq", 2, 0b10, |ev, a| {
        let mut s = seq(&a[0], "SortSeq", 0)?.to_vec();
        try_sort_by(&mut s, |x, y| {
            if matches!(ev.apply_op(&a[1], &[x.clone(), y.clone()])?, Value::Bool(true)) {
                return Ok(Ordering::Less);
            }
            if matches!(ev.apply_op(&a[1], &[y.clone(), x.clone()])?, Value::Bool(true)) {
                return Ok(Ordering::Greater);
            }
            Ok(Ordering::Equal)
        })?;
        Ok(Value::Tuple(Rc::new(s)))
    });
    m.op("RandomElement", 1, |ev, a| {
        let s = set(&a[0], "RandomElement", 0)?.elems()?;
        if s.is_empty() {
            return fail("Attempted to apply RandomElement to the empty set.".into());
        }
        Ok(s[((ev.random() * s.len() as f64) as usize).min(s.len() - 1)].clone())
    });
    m.val("Any", Value::Set(Rc::new(SetV::new(SetK::Any))));
    m.op("ToString", 1, |_, a| Ok(mk_str(&fmt(&a[0]))));
    m.op("TLCEval", 1, |_, a| Ok(a[0].clone()));
    let tlc = m.done();

    let mut m = MB::new("TLCExt", &[]);
    m.op("AssertEq", 2, |_, a| {
        let eq = val_eq(&a[0], &a[1])?;
        if !eq {
            print(&format!("\nAssertion failed:\n{}\n!=\n{}\n", fmt(&a[0]), fmt(&a[1])));
        }
        Ok(Value::Bool(eq))
    });
    m.op_lazy("AssertError", 2, |ev, a| {
        let expected = ev.unthunk(&a[0])?;
        match ev.unthunk(&a[1]) {
            Ok(_) => Ok(Value::Bool(false)),
            Err(e) => match &*e {
                Fail::Tla(t) if t.kind == "eval" || t.kind == "assert" => {
                    if let Value::Str(s) = &expected {
                        if *string(*s) == t.msg {
                            return Ok(Value::Bool(true));
                        }
                    }
                    print(&format!("\nAssertion failed:\n{}\n!=\n{}\n", fmt(&expected), fmt(&mk_str(&t.msg))));
                    Ok(Value::Bool(false))
                }
                _ => Err(e),
            },
        }
    });
    m.op("TLCModelValue", 1, |_, a| match &a[0] {
        Value::Str(s) => Ok(Value::Model(*s)),
        v => Ok(Value::Model(str_id(&fmt(v)))),
    });
    m.op("TLCDefer", 1, |_, _| Ok(Value::Bool(true)));
    m.op("PickSuccessor", 1, |_, _| Ok(Value::Bool(true)));
    m.op("TLCNoOp", 1, |_, a| Ok(a[0].clone()));
    m.op("TLCCache", 2, |_, a| Ok(a[0].clone()));
    m.op("TLCGetOrDefault", 2, |ev, a| Ok(ev.registers.borrow().get(&reg_key(&a[0], "TLCGetOrDefault")?).cloned().unwrap_or_else(|| a[1].clone())));
    m.op_ops("TLCGetAndSet", 4, 0b10, |ev, a| {
        let key = reg_key(&a[0], "TLCGetAndSet")?;
        let old = ev.registers.borrow().get(&key).cloned().unwrap_or_else(|| a[3].clone());
        let nv = ev.apply_op(&a[1], &[old.clone(), a[2].clone()])?;
        ev.registers.borrow_mut().insert(key, nv);
        Ok(old)
    });
    m.op("TLCFP", 1, |_, _| Ok(Value::Int(0)));
    m.op("Trace", 0, |ev, _| {
        ev.st_touch.set(ev.st_touch.get() + 1);
        fail("Trace is not available in this context.".into())
    });
    m.op("CounterExample", 0, |ev, _| {
        ev.st_touch.set(ev.st_touch.get() + 1);
        fail("CounterExample is not available in this context.".into())
    });
    m.op("ToTrace", 1, |_, _| fail("ToTrace is not supported.".into()));
    let tlcext = m.done();

    // ---- Bags ----
    let mut m = MB::new("Bags", &[]);
    m.op("IsABag", 1, |_, a| Ok(Value::Bool(is_fcn(&a[0]) && fcn_values(&a[0])?.iter().all(|x| matches!(x, Value::Int(i) if *i > 0)))));
    m.op("BagToSet", 1, |_, a| Ok(SetV::of(domain_elems(&a[0])?.into_owned())));
    m.op("SetToBag", 1, |_, a| {
        let e = set(&a[0], "SetToBag", 0)?.elems()?;
        Ok(make_fcn(e, e.iter().map(|_| Value::Int(1)).collect()))
    });
    m.op("BagIn", 2, |_, a| Ok(Value::Bool(bsearch(&bag_pairs(&a[1], "BagIn")?.0, &a[0])?.is_some())));
    m.val("EmptyBag", empty_tuple());
    m.op("\\oplus", 2, |_, a| {
        let ((d0, v0), (d1, v1)) = (bag_pairs(&a[0], "(+)")?, bag_pairs(&a[1], "(+)")?);
        let mut out: Vec<(Value, i64)> = d0.iter().zip(v0.iter()).map(|(d, v)| (d.clone(), bag_n(v))).collect();
        for i in 0..d1.len() {
            match bsearch(&d0, &d1[i])? {
                Some(k) => out[k].1 += bag_n(&v1[i]),
                None => out.push((d1[i].clone(), bag_n(&v1[i]))),
            }
        }
        mk_bag(out)
    });
    m.op("\\ominus", 2, |_, a| {
        let ((d0, v0), (d1, v1)) = (bag_pairs(&a[0], "(-)")?, bag_pairs(&a[1], "(-)")?);
        let mut out = vec![];
        for i in 0..d0.len() {
            let n = match bsearch(&d1, &d0[i])? {
                Some(k) => bag_n(&v0[i]) - bag_n(&v1[k]),
                None => bag_n(&v0[i]),
            };
            out.push((d0[i].clone(), n));
        }
        mk_bag(out)
    });
    m.op("BagUnion", 1, |_, a| {
        let mut out: Vec<(Value, i64)> = vec![];
        for b in set(&a[0], "BagUnion", 0)?.elems()? {
            let (d, v) = bag_pairs(b, "BagUnion")?;
            'next: for i in 0..d.len() {
                for p in out.iter_mut() {
                    if val_eq(&p.0, &d[i])? {
                        p.1 += bag_n(&v[i]);
                        continue 'next;
                    }
                }
                out.push((d[i].clone(), bag_n(&v[i])));
            }
        }
        mk_bag(out)
    });
    m.op("\\sqsubseteq", 2, |_, a| {
        let ((d0, v0), (d1, v1)) = (bag_pairs(&a[0], "\\sqsubseteq")?, bag_pairs(&a[1], "\\sqsubseteq")?);
        for i in 0..d0.len() {
            match bsearch(&d1, &d0[i])? {
                Some(k) if bag_n(&v0[i]) <= bag_n(&v1[k]) => {}
                _ => return Ok(Value::Bool(false)),
            }
        }
        Ok(Value::Bool(true))
    });
    m.op("SubBag", 1, |_, a| {
        let (d, v) = bag_pairs(&a[0], "SubBag")?;
        let mut out: Vec<Value> = vec![];
        let mut cur: Vec<(Value, i64)> = vec![];
        fn rec(d: &[Value], v: &[Value], i: usize, cur: &mut Vec<(Value, i64)>, out: &mut Vec<Value>) -> R<()> {
            if i == d.len() {
                out.push(mk_bag(cur.clone())?);
                return Ok(());
            }
            for c in 0..=bag_n(&v[i]) {
                cur.push((d[i].clone(), c));
                rec(d, v, i + 1, cur, out)?;
                cur.pop();
            }
            Ok(())
        }
        rec(&d, v, 0, &mut cur, &mut out)?;
        mk_set(out)
    });
    m.op_ops("BagOfAll", 2, 0b01, |ev, a| {
        let (d, v) = bag_pairs(&a[1], "BagOfAll")?;
        let mut out: Vec<(Value, i64)> = vec![];
        'next: for i in 0..d.len() {
            let x = ev.apply_op(&a[0], std::slice::from_ref(&d[i]))?;
            for p in out.iter_mut() {
                if val_eq(&p.0, &x)? {
                    p.1 += bag_n(&v[i]);
                    continue 'next;
                }
            }
            out.push((x, bag_n(&v[i])));
        }
        mk_bag(out)
    });
    m.op("BagCardinality", 1, |_, a| Ok(Value::Int(bag_pairs(&a[0], "BagCardinality")?.1.iter().map(bag_n).sum())));
    m.op("CopiesIn", 2, |_, a| {
        let (d, v) = bag_pairs(&a[1], "CopiesIn")?;
        Ok(match bsearch(&d, &a[0])? {
            Some(k) => v[k].clone(),
            None => Value::Int(0),
        })
    });
    let bags = m.done();

    let mut m = MB::new("Randomization", &[]);
    m.op("RandomSubset", 2, |ev, a| {
        let k = int(&a[0], "RandomSubset", 0)?;
        let mut s = set(&a[1], "RandomSubset", 1)?.elems()?.to_vec();
        if k < 0 || k as usize > s.len() {
            return fail(format!("The first argument of RandomSubset should be between 0 and the cardinality of the set, but it is {}", k));
        }
        for i in (1..s.len()).rev() {
            let j = ((ev.random() * (i + 1) as f64) as usize).min(i);
            s.swap(i, j);
        }
        s.truncate(k as usize);
        mk_set(s)
    });
    m.op("RandomSetOfSubsets", 3, |ev, a| {
        let (k, n) = (int(&a[0], "RandomSetOfSubsets", 0)?, int(&a[1], "RandomSetOfSubsets", 1)?);
        let s = set(&a[2], "RandomSetOfSubsets", 2)?.elems()?;
        let mut out = vec![];
        for _ in 0..k {
            let p = if s.is_empty() { 0.0 } else { n as f64 / s.len() as f64 };
            out.push(SetV::of(s.iter().filter(|_| ev.random() < p).cloned().collect()));
        }
        mk_set(out)
    });
    m.op("RandomSubsetSet", 3, |ev, a| {
        let k = int(&a[0], "RandomSubsetSet", 0)?;
        let s = set(&a[2], "RandomSubsetSet", 2)?.elems()?;
        let mut out = vec![];
        for _ in 0..k {
            out.push(SetV::of(s.iter().filter(|_| ev.random() < 0.5).cloned().collect()));
        }
        mk_set(out)
    });
    m.op("TestRandomSetOfSubsets", 3, |_, _| Ok(Value::Bool(true)));
    let randomization = m.done();

    let mut out = HashMap::new();
    for x in [naturals, integers, reals, sequences, finite_sets, tlc, tlcext, bags, randomization] {
        out.insert(x.name.unwrap(), x);
    }
    out
}

fn tlc_get(ev: &Evaluator, k: &str) -> Option<Value> {
    let st = &ev.stats;
    if !st.active.get() {
        return None;
    }
    let ids = |names: &[&str]| -> Vec<StrId> { names.iter().map(|n| str_id(n)).collect() };
    Some(match k {
        "level" => Value::Int(st.level.get() + if ev.prime_depth.get() > 0 { 1 } else { 0 }),
        "distinct" => Value::Int(st.distinct.get()),
        "generated" => Value::Int(st.generated.get()),
        "queue" => Value::Int(st.queue.get()),
        "diameter" => Value::Int(st.diameter.get()),
        "duration" => Value::Int(0),
        "config" => make_record(
            &ids(&["mode", "depth", "deadlock", "worker", "traces", "seed", "fingerprint"]),
            vec![mk_str("bfs"), Value::Int(-1), Value::Bool(st.check_deadlock.get()), Value::Int(1), Value::Int(0), Value::Int(0), Value::Int(0)],
        ),
        "stats" => make_record(
            &ids(&["distinct", "generated", "queue", "diameter", "duration"]),
            vec![Value::Int(st.distinct.get()), Value::Int(st.generated.get()), Value::Int(st.queue.get()), Value::Int(st.diameter.get()), Value::Int(0)],
        ),
        _ => {
            if k.starts_with("-D") {
                mk_str(if k.ends_with(".cdot") { "true" } else { "false" })
            } else {
                return None;
            }
        }
    })
}

// ---- native overrides for bundled community modules ----
const NO_CHOICE: &str = "Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P.";

fn fold_function(ev: &Evaluator, op: &Value, base: &Value, fun: &Value) -> R<Value> {
    if !is_fcn(fun) {
        return arg_err(2, "FoldFunction", "function", fun);
    }
    let mut acc = base.clone();
    for x in fcn_values(fun)? {
        acc = ev.apply_op(op, &[x.clone(), acc])?; // values are stored in domain order
    }
    Ok(acc)
}
fn expect_bool(v: Value, i: usize, op: &str, what: &str, test: &Value) -> R<bool> {
    match v {
        Value::Bool(b) => Ok(b),
        _ => arg_err(i, op, what, test),
    }
}

fn read_text(path: &str) -> R<String> {
    if !std::path::Path::new(path).exists() {
        return fail(format!("{} (No such file or directory)", path));
    }
    match std::fs::read(path) {
        Ok(b) => Ok(String::from_utf8_lossy(&b).into_owned()),
        Err(e) => fail(format!("{} ({})", path, e)),
    }
}

/// JSON -> TLA+ values, like the community module's Java override (arrays are sequences, objects records).
struct JsonReader {
    s: Vec<char>,
    i: usize,
}
impl JsonReader {
    fn new(s: &str) -> JsonReader {
        JsonReader { s: s.chars().collect(), i: 0 }
    }
    fn err<T>(&self, msg: &str) -> R<T> {
        fail(format!("Malformed JSON: {} at offset {}", msg, self.i))
    }
    fn at(&self) -> Option<char> {
        self.s.get(self.i).copied()
    }
    fn ws(&mut self) {
        while matches!(self.at(), Some(' ' | '\t' | '\n' | '\r' | '\u{feff}')) {
            self.i += 1;
        }
    }
    fn document(&mut self) -> R<Value> {
        let v = self.value()?;
        self.ws();
        if self.i < self.s.len() {
            return self.err("unexpected trailing characters");
        }
        Ok(v)
    }
    fn value(&mut self) -> R<Value> {
        self.ws();
        let c = match self.at() {
            Some(c) => c,
            None => return self.err("unexpected end of input"),
        };
        if c == '[' {
            self.i += 1;
            let mut out = vec![];
            self.ws();
            if self.at() == Some(']') {
                self.i += 1;
                return Ok(empty_tuple());
            }
            loop {
                out.push(self.value()?);
                self.ws();
                let d = self.at();
                self.i += 1;
                if d == Some(']') {
                    return Ok(Value::Tuple(Rc::new(out)));
                }
                if d != Some(',') {
                    return self.err("expected ',' or ']'");
                }
            }
        }
        if c == '{' {
            self.i += 1;
            let mut names: Vec<StrId> = vec![];
            let mut vals: Vec<Value> = vec![];
            self.ws();
            if self.at() == Some('}') {
                self.i += 1;
                return Ok(empty_tuple());
            }
            loop {
                self.ws();
                if self.at() != Some('"') {
                    return self.err("expected a member name");
                }
                let nm = self.string()?;
                self.ws();
                let d = self.at();
                self.i += 1;
                if d != Some(':') {
                    return self.err("expected ':'");
                }
                let id = str_id(&nm);
                let v = self.value()?;
                match names.iter().position(|x| *x == id) {
                    Some(k) => vals[k] = v,
                    None => {
                        names.push(id);
                        vals.push(v);
                    }
                }
                self.ws();
                let d = self.at();
                self.i += 1;
                if d == Some('}') {
                    return Ok(make_record(&names, vals));
                }
                if d != Some(',') {
                    return self.err("expected ',' or '}'");
                }
            }
        }
        if c == '"' {
            let v = self.string()?;
            return Ok(mk_str(&v));
        }
        let rest: String = self.s[self.i..].iter().take(40).collect();
        for kw in ["true", "false", "null"] {
            if rest.starts_with(kw) && !rest[kw.len()..].chars().next().map_or(false, |x| x.is_ascii_alphanumeric() || x == '_') {
                self.i += kw.len();
                if kw == "null" {
                    return fail("Cannot convert value: unsupported JSON value null".into());
                }
                return Ok(Value::Bool(kw == "true"));
            }
        }
        // -?(0|[1-9]\d*)(\.\d+)?([eE][+-]?\d+)?
        let start = self.i;
        let mut j = self.i;
        let get = |j: usize| -> char { self.s.get(j).copied().unwrap_or('\0') };
        if get(j) == '-' {
            j += 1;
        }
        if get(j) == '0' {
            j += 1;
        } else if get(j).is_ascii_digit() {
            while get(j).is_ascii_digit() {
                j += 1;
            }
        } else {
            return self.err(&format!("unexpected character '{}'", c));
        }
        let mut is_int = true;
        if get(j) == '.' && get(j + 1).is_ascii_digit() {
            is_int = false;
            j += 1;
            while get(j).is_ascii_digit() {
                j += 1;
            }
        }
        if get(j) == 'e' || get(j) == 'E' {
            let mut k = j + 1;
            if get(k) == '+' || get(k) == '-' {
                k += 1;
            }
            if get(k).is_ascii_digit() {
                while get(k).is_ascii_digit() {
                    k += 1;
                }
                is_int = false;
                j = k;
            }
        }
        let text: String = self.s[start..j].iter().collect();
        self.i = j;
        // Gson's getAsInt(): integers wrap to 32 bits, fractions are truncated.
        if is_int {
            let n: i128 = text.parse().unwrap_or(0);
            return Ok(Value::Int(n as i32 as i64));
        }
        let x: f64 = text.parse::<f64>().unwrap_or(0.0).trunc();
        Ok(Value::Int(if x.is_finite() { (x as i128) as i32 as i64 } else { 0 }))
    }
    fn string(&mut self) -> R<String> {
        let mut o = String::new();
        self.i += 1;
        loop {
            let c = match self.at() {
                Some(c) => c,
                None => return self.err("unterminated string"),
            };
            self.i += 1;
            if c == '"' {
                return Ok(o);
            }
            if c != '\\' {
                o.push(c);
                continue;
            }
            let e = self.at();
            self.i += 1;
            match e {
                Some('n') => o.push('\n'),
                Some('t') => o.push('\t'),
                Some('r') => o.push('\r'),
                Some('b') => o.push('\x08'),
                Some('f') => o.push('\x0c'),
                Some('u') => {
                    let h: String = self.s[self.i.min(self.s.len())..(self.i + 4).min(self.s.len())].iter().collect();
                    match u32::from_str_radix(&h, 16) {
                        Ok(cp) if h.len() == 4 => o.push(char::from_u32(cp).unwrap_or('\u{fffd}')),
                        _ => return self.err("bad \\u escape"),
                    }
                    self.i += 4;
                }
                Some(x @ ('"' | '\\' | '/' | '\'')) => o.push(x),
                _ => return self.err("bad escape sequence"),
            }
        }
    }
}

type Ov = (&'static str, &'static str, u32, bool, NativeFn);

fn overrides() -> Vec<Ov> {
    let mut v: Vec<Ov> = vec![];
    // FoldSet(op, base, set): op(element, accumulator), elements in normalized order.
    v.push(("FiniteSetsExt", "FoldSet", 0b1, false, |ev, a| {
        let mut acc = a[1].clone();
        for x in set(&a[2], "FoldSet", 2)?.elems()? {
            acc = ev.apply_op(&a[0], &[x.clone(), acc])?;
        }
        Ok(acc)
    }));
    v.push(("FiniteSetsExt", "Quantify", 0b10, false, |ev, a| {
        let s = match &a[0] {
            Value::Set(s) => s,
            x => return arg_err(0, "Quantify", "set", x),
        };
        let mut n = 0;
        for x in s.elems()? {
            if expect_bool(ev.apply_op(&a[1], std::slice::from_ref(x))?, 1, "Quantify", "boolean-valued operator", &a[1])? {
                n += 1;
            }
        }
        Ok(Value::Int(n))
    }));
    v.push(("FiniteSetsExt", "SumSet", 0, false, |_, a| {
        let mut x: i64 = 0;
        for y in set(&a[0], "SumSet", 0)?.elems()? {
            let yi = int(y, "+", 0)?;
            let r = x + yi;
            if r > 2147483647 || r < -2147483648 {
                return fail(format!("Overflow when computing {} + {}", yi, x));
            }
            x = r;
        }
        Ok(Value::Int(x))
    }));
    v.push(("FiniteSetsExt", "ProductSet", 0, false, |_, a| {
        let mut x: i64 = 1;
        for y in set(&a[0], "ProductSet", 0)?.elems()? {
            let yi = int(y, "*", 0)?;
            let r = x.saturating_mul(yi);
            if r > 2147483647 || r < -2147483648 {
                return fail(format!("Overflow when computing {} * {}", yi, x));
            }
            x = r;
        }
        Ok(Value::Int(x))
    }));
    v.push(("FiniteSetsExt", "Max", 0, false, |_, a| {
        let e = set(&a[0], "Max", 0)?.elems()?;
        if e.is_empty() {
            return fail(NO_CHOICE.into());
        }
        let mut x = int(&e[0], ">=", 0)?;
        for y in e {
            x = x.max(int(y, ">=", 0)?);
        }
        Ok(Value::Int(x))
    }));
    v.push(("FiniteSetsExt", "Min", 0, false, |_, a| {
        let e = set(&a[0], "Min", 0)?.elems()?;
        if e.is_empty() {
            return fail(NO_CHOICE.into());
        }
        let mut x = int(&e[0], "=<", 0)?;
        for y in e {
            x = x.min(int(y, "=<", 0)?);
        }
        Ok(Value::Int(x))
    }));
    v.push(("FiniteSetsExt", "kSubset", 0, false, |_, a| {
        let k = match &a[0] {
            Value::Int(k) => *k,
            x => return arg_err(0, "kSubset", "natural number", x),
        };
        let base = match &a[1] {
            Value::Set(s) => s,
            x => return arg_err(1, "kSubset", "set", x),
        };
        if k < 0 {
            return Ok(Value::Set(empty_set()));
        }
        if k == 0 {
            return Ok(SetV::of(vec![Value::Set(empty_set())]));
        }
        if !base.enumerable() {
            return Ok(Value::Set(Rc::new(SetV::new(SetK::KSubset(k, base.clone())))));
        }
        let b = base.elems()?;
        if k as usize > b.len() {
            return Ok(Value::Set(empty_set()));
        }
        let mut out = vec![];
        let mut idx: Vec<usize> = vec![];
        fn rec(b: &[Value], start: usize, left: usize, idx: &mut Vec<usize>, out: &mut Vec<Value>) {
            if left == 0 {
                out.push(SetV::of(idx.iter().map(|&i| b[i].clone()).collect()));
                return;
            }
            let mut i = start;
            while i + left <= b.len() {
                idx.push(i);
                rec(b, i + 1, left - 1, idx, out);
                idx.pop();
                i += 1;
            }
        }
        rec(b, 0, k as usize, &mut idx, &mut out);
        Ok(SetV::of(out)) // same-size subsets enumerated lexicographically are in normalized order
    }));
    v.push(("Functions", "Range", 0, false, |ev, a| mk_set(fcn_values(&unlazy(ev, &a[0])?)?.to_vec())));
    v.push(("Functions", "IsInjective", 0, true, |ev, a| {
        let vals: Vec<Value>;
        let mut done = None;
        if let Value::Thunk(t) = &a[0] {
            if let crate::ast::E::RecSet(fields) = &t.e.e {
                let mut vs = vec![];
                for (_, e) in fields {
                    vs.push(ev.eval(e, &t.ctx)?);
                }
                done = Some(vs);
            }
        }
        match done {
            Some(vs) => vals = vs,
            None => {
                let f = unlazy(ev, &ev.unthunk(&a[0])?)?;
                match &f {
                    Value::Set(s) => match &s.k {
                        SetK::RecSet(_, sets) => vals = sets.iter().map(|x| Value::Set(x.clone())).collect(),
                        _ => return one_arg_err("IsInjective", "function", &f),
                    },
                    _ if is_fcn(&f) => vals = fcn_values(&f)?.to_vec(),
                    _ => return one_arg_err("IsInjective", "function", &f),
                }
            }
        }
        for i in 0..vals.len() {
            for j in i + 1..vals.len() {
                if val_eq(&vals[i], &vals[j])? {
                    return Ok(Value::Bool(false));
                }
            }
        }
        Ok(Value::Bool(true))
    }));
    v.push(("Functions", "AntiFunction", 0, false, |ev, a| {
        let f = unlazy(ev, &a[0])?;
        if !is_fcn(&f) {
            return one_arg_err("AntiFunction", "functions", &f);
        }
        let (dom, vals) = (domain_elems(&f)?, fcn_values(&f)?);
        make_fcn_from_pairs(vals.iter().cloned().zip(dom.iter().cloned()).collect())
    }));
    v.push(("Functions", "FoldFunction", 0b1, false, |ev, a| fold_function(ev, &a[0], &a[1], &unlazy(ev, &a[2])?)));
    v.push(("Functions", "FoldFunctionOnSet", 0b1, false, |ev, a| {
        if !is_fcn(&a[2]) && !matches!(a[2], Value::LazyFcn(_)) {
            return arg_err(2, "FoldFunctionOnSet", "function", &a[2]);
        }
        let s = match &a[3] {
            Value::Set(s) => s,
            x => return arg_err(3, "FoldFunctionOnSet", "set", x),
        };
        let mut acc = a[1].clone();
        for d in s.elems()? {
            acc = ev.apply_op(&a[0], &[ev.apply_fcn(&a[2], d, None)?, acc])?;
        }
        Ok(acc)
    }));
    // MapThenFoldSet(op, base, f, choose, S): the element chosen first is combined last.
    v.push(("Folds", "MapThenFoldSet", 0b1101, false, |ev, a| {
        let s = match &a[4] {
            Value::Set(s) => s,
            x => return fail(format!("Attempted to check if the non-enumerable value\n{}\nis element of\nSUBSET {}", fmt(x), fmt(x))),
        };
        let mut rest: Vec<Value> = s.elems()?.to_vec();
        let mut picked: Vec<Value> = vec![];
        while !rest.is_empty() {
            let x = ev.apply_op(&a[3], &[SetV::of(rest.clone())])?;
            match bsearch(&rest, &x)? {
                Some(i) => picked.push(rest.remove(i)),
                None => return fail(format!("The choose operator of MapThenFoldSet returned\n{}\nwhich is not an element of the set it was applied to.", fmt(&x))),
            }
        }
        let mut acc = a[1].clone();
        for p in picked.iter().rev() {
            acc = ev.apply_op(&a[0], &[ev.apply_op(&a[2], std::slice::from_ref(p))?, acc])?;
        }
        Ok(acc)
    }));
    v.push(("SequencesExt", "FoldSeq", 0b1, false, |ev, a| fold_function(ev, &a[0], &a[1], &a[2])));
    v.push(("SequencesExt", "FoldLeft", 0b1, false, |ev, a| {
        let s = match &a[2] {
            Value::Tuple(t) => t,
            x => return arg_err(2, "FoldLeft", "sequence", x),
        };
        let mut acc = a[1].clone();
        for x in s.iter() {
            acc = ev.apply_op(&a[0], &[acc, x.clone()])?;
        }
        Ok(acc)
    }));
    v.push(("SequencesExt", "FoldRight", 0b1, false, |ev, a| {
        let s = match &a[1] {
            Value::Tuple(t) => t,
            x => return arg_err(1, "FoldRight", "sequence", x),
        };
        let mut acc = a[2].clone();
        for x in s.iter().rev() {
            acc = ev.apply_op(&a[0], &[x.clone(), acc])?;
        }
        Ok(acc)
    }));
    v.push(("SequencesExt", "FoldLeftDomain", 0b1, false, |ev, a| {
        let s = match &a[2] {
            Value::Tuple(t) => t,
            x => return arg_err(2, "FoldLeftDomain", "sequence", x),
        };
        let mut acc = a[1].clone();
        for i in 1..=s.len() as i64 {
            acc = ev.apply_op(&a[0], &[acc, Value::Int(i)])?;
        }
        Ok(acc)
    }));
    v.push(("SequencesExt", "FoldRightDomain", 0b1, false, |ev, a| {
        let s = match &a[1] {
            Value::Tuple(t) => t,
            x => return arg_err(1, "FoldRightDomain", "sequence", x),
        };
        let mut acc = a[2].clone();
        for i in (1..=s.len() as i64).rev() {
            acc = ev.apply_op(&a[0], &[Value::Int(i), acc])?;
        }
        Ok(acc)
    }));
    v.push(("SequencesExt", "ToSet", 0, false, |ev, a| mk_set(fcn_values(&unlazy(ev, &a[0])?)?.to_vec())));
    v.push(("SequencesExt", "Reverse", 0, false, |_, a| Ok(tuple_of(seq(&a[0], "Reverse", 0)?.iter().rev().cloned().collect()))));
    v.push(("SequencesExt", "Cons", 0, false, |_, a| {
        let s = seq(&a[1], "Cons", 1)?;
        let mut out = Vec::with_capacity(s.len() + 1);
        out.push(a[0].clone());
        out.extend_from_slice(s);
        Ok(Value::Tuple(Rc::new(out)))
    }));
    v.push(("SequencesExt", "Front", 0, false, |_, a| {
        if let Value::Str(s) = &a[0] {
            let st = string(*s);
            let mut c: Vec<char> = st.chars().collect();
            c.pop();
            return Ok(mk_str(&c.into_iter().collect::<String>()));
        }
        let s = seq(&a[0], "Front", 0)?;
        Ok(tuple_of(if s.is_empty() { vec![] } else { s[..s.len() - 1].to_vec() }))
    }));
    v.push(("SequencesExt", "Last", 0, false, |ev, a| {
        let s = seq(&a[0], "Last", 0)?;
        match s.last() {
            Some(x) => Ok(x.clone()),
            None => ev.apply_fcn(&a[0], &Value::Int(0), None),
        }
    }));
    v.push(("SequencesExt", "IsSuffix", 0, false, |_, a| {
        let (s, t) = (seq(&a[0], "IsSuffix", 0)?, seq(&a[1], "IsSuffix", 1)?);
        if s.len() > t.len() {
            return Ok(Value::Bool(false));
        }
        let o = t.len() - s.len();
        for i in 0..s.len() {
            if !val_eq(&s[i], &t[o + i])? {
                return Ok(Value::Bool(false));
            }
        }
        Ok(Value::Bool(true))
    }));
    v.push(("SequencesExt", "Contains", 0, false, |_, a| {
        let s = match &a[0] {
            Value::Tuple(t) => t,
            x => return one_arg_err("Contains", "sequence", x),
        };
        for x in s.iter() {
            if val_eq(x, &a[1])? {
                return Ok(Value::Bool(true));
            }
        }
        Ok(Value::Bool(false))
    }));
    v.push(("SequencesExt", "IsPrefix", 0, false, |_, a| {
        if let (Value::Str(x), Value::Str(y)) = (&a[0], &a[1]) {
            return Ok(Value::Bool(string(*y).starts_with(&*string(*x))));
        }
        let (s, t) = (seq(&a[0], "IsPrefix", 0)?, seq(&a[1], "IsPrefix", 1)?);
        if s.len() > t.len() {
            return Ok(Value::Bool(false));
        }
        for i in 0..s.len() {
            if !val_eq(&s[i], &t[i])? {
                return Ok(Value::Bool(false));
            }
        }
        Ok(Value::Bool(true))
    }));
    v.push(("SequencesExt", "SetToSeq", 0, false, |_, a| Ok(tuple_of(set(&a[0], "SetToSeq", 0)?.elems()?.to_vec()))));
    v.push(("SequencesExt", "SetToSeqs", 0, false, |_, a| {
        let s = match &a[0] {
            Value::Set(s) if s.enumerable() => s.elems()?,
            x => return fail(format!("Applying SetToSeqs to the following value,\nwhich is not a finite set:\n{}", fmt(x))),
        };
        let mut out = vec![];
        let mut used = vec![false; s.len()];
        let mut cur: Vec<Value> = vec![];
        fn rec(s: &[Value], used: &mut Vec<bool>, cur: &mut Vec<Value>, out: &mut Vec<Value>) {
            if cur.len() == s.len() {
                out.push(tuple_of(cur.clone()));
                return;
            }
            for i in 0..s.len() {
                if used[i] {
                    continue;
                }
                used[i] = true;
                cur.push(s[i].clone());
                rec(s, used, cur, out);
                cur.pop();
                used[i] = false;
            }
        }
        rec(s, &mut used, &mut cur, &mut out);
        mk_set(out)
    }));
    v.push(("SequencesExt", "RemoveFirst", 0, false, |_, a| {
        let s = match &a[0] {
            Value::Tuple(t) => t,
            x => return arg_err(0, "RemoveFirst", "sequence", x),
        };
        for i in 0..s.len() {
            if val_eq(&s[i], &a[1])? {
                let mut out = s.to_vec();
                out.remove(i);
                return Ok(tuple_of(out));
            }
        }
        Ok(a[0].clone())
    }));
    v.push(("IOUtils", "IOEnv", 0, false, |_, _| {
        let vars: Vec<(String, String)> = std::env::vars_os().filter_map(|(k, v)| Some((k.into_string().ok()?, v.into_string().ok()?))).collect();
        if vars.is_empty() {
            return Ok(empty_tuple());
        }
        let names: Vec<StrId> = vars.iter().map(|(k, _)| str_id(k)).collect();
        Ok(make_record(&names, vars.iter().map(|(_, v)| mk_str(v)).collect()))
    }));
    v.push(("IOUtils", "atoi", 0, false, |_, a| {
        if let Value::Str(s) = &a[0] {
            let st = string(*s);
            let digits = st.strip_prefix(['+', '-']).unwrap_or(&st);
            if !digits.is_empty() && digits.bytes().all(|c| c.is_ascii_digit()) {
                if let Ok(n) = st.trim_start_matches('+').parse::<i64>() {
                    if (-2147483648..=2147483647).contains(&n) {
                        return Ok(Value::Int(n));
                    }
                }
            }
        }
        one_arg_err("atoi", "string", &a[0])
    }));
    v.push(("Json", "JsonDeserialize", 0, false, |_, a| {
        let path = match &a[0] {
            Value::Str(s) => string(*s),
            x => return arg_err(0, "JsonDeserialize", "string", x),
        };
        JsonReader::new(&read_text(&path)?).document()
    }));
    v.push(("Json", "ndJsonDeserialize", 0, false, |_, a| {
        let path = match &a[0] {
            Value::Str(s) => string(*s),
            x => return arg_err(0, "ndJsonDeserialize", "string", x),
        };
        let text = read_text(&path)?;
        let mut out = vec![];
        for line in text.split(['\n', '\r']) {
            let t = line.trim();
            if !t.is_empty() {
                out.push(JsonReader::new(t).document()?);
            }
        }
        Ok(tuple_of(out))
    }));
    // CausalOrder(log, clock(_), node(_), domain(_)): a topological sort of the log by its vector clocks.
    v.push(("VectorClocks", "CausalOrder", 0b1110, false, |ev, a| {
        let log = match &a[0] {
            Value::Tuple(t) => t,
            x => return arg_err(0, "CausalOrder", "sequence", x),
        };
        struct GN {
            value: Value,
            clock: Value,
            time: Value,
            hosts: Vec<Value>,
            parents: Vec<(usize, usize)>,
            children: Vec<(usize, usize)>,
        }
        let mut keys: Vec<String> = vec![];
        let mut lists: Vec<Vec<GN>> = vec![];
        for value in log.iter() {
            let node_id = ev.apply_op(&a[2], std::slice::from_ref(value))?;
            let clock = ev.apply_op(&a[1], std::slice::from_ref(value))?;
            let time = ev.apply_fcn(&clock, &node_id, None)?;
            let hosts = match ev.apply_op(&a[3], std::slice::from_ref(&clock))? {
                Value::Set(s) => s.elems()?.to_vec(),
                x => return arg_err(3, "CausalOrder", "set", &x),
            };
            let k = fmt(&node_id);
            let idx = match keys.iter().position(|x| *x == k) {
                Some(i) => i,
                None => {
                    keys.push(k);
                    lists.push(vec![]);
                    keys.len() - 1
                }
            };
            lists[idx].push(GN { value: value.clone(), clock, time, hosts, parents: vec![], children: vec![] });
        }
        // A node's own clock component totally orders its events.
        for list in lists.iter_mut() {
            try_sort_by(list, |x, y| compare(&x.time, &y.time))?;
        }
        // Merge the per-node logs into a DAG: an event depends on the latest event of every other node it has seen.
        for h in 0..lists.len() {
            let mut global: Vec<Value> = vec![Value::Int(0); keys.len()];
            for gi in 0..lists[h].len() {
                global[h] = lists[h][gi].time.clone();
                let hosts = lists[h][gi].hosts.clone();
                let clock = lists[h][gi].clock.clone();
                for other in &hosts {
                    let ok = fmt(other);
                    let time = ev.apply_fcn(&clock, other, None)?;
                    let oi = match keys.iter().position(|x| *x == ok) {
                        Some(i) => i,
                        None => {
                            if compare(&Value::Int(0), &time)? == Ordering::Less {
                                return fail(format!("CausalOrder: the log has no events of node {}, but a vector clock refers to its event {}.", fmt(other), fmt(&time)));
                            }
                            continue;
                        }
                    };
                    if compare(&global[oi], &time)? == Ordering::Less {
                        global[oi] = time.clone();
                        let pos = int(&time, "CausalOrder", 0)? - 1;
                        if pos < 0 || pos as usize >= lists[oi].len() {
                            return fail(format!("CausalOrder: the log lacks event {} of node {} (vector clocks must be continuous).", fmt(&time), fmt(other)));
                        }
                        let parent = (oi, pos as usize);
                        if !lists[h][gi].parents.contains(&parent) {
                            lists[h][gi].parents.push(parent);
                        }
                        if !lists[oi][pos as usize].children.contains(&(h, gi)) {
                            lists[oi][pos as usize].children.push((h, gi));
                        }
                    }
                }
            }
        }
        // Repeatedly pop the heads that have no pending predecessor.
        let mut sorted: Vec<Value> = vec![];
        let mut heads = vec![0usize; lists.len()];
        let mut round = 0;
        while round < log.len() && sorted.len() < log.len() {
            for h in 0..lists.len() {
                let i = heads[h];
                if i >= lists[h].len() || !lists[h][i].parents.is_empty() {
                    continue;
                }
                heads[h] = i + 1;
                let children = lists[h][i].children.clone();
                for (ch, ci) in children {
                    lists[ch][ci].parents.retain(|p| *p != (h, i));
                }
                sorted.push(lists[h][i].value.clone());
            }
            round += 1;
        }
        Ok(tuple_of(sorted))
    }));
    v.push(("Bitwise", "And", 0, false, |_, a| Ok(Value::Int(int(&a[0], "And", 0)? & int(&a[1], "And", 1)?))));
    v.push(("Bitwise", "Or", 0, false, |_, a| Ok(Value::Int(int(&a[0], "Or", 0)? | int(&a[1], "Or", 1)?))));
    v.push(("Bitwise", "Xor", 0, false, |_, a| Ok(Value::Int(int(&a[0], "Xor", 0)? ^ int(&a[1], "Xor", 1)?))));
    v
}

/// Replaces the TLA+ definitions of loaded community modules by their native implementations.
pub fn apply_overrides(loader: &Loader) {
    for (mname, op, ops, lazy, f) in overrides() {
        if let Some(m) = loader.modules.get(&name(mname)) {
            if let Some(Sym::Def(d)) = m.syms.get(name(op)) {
                d.builtin.set(Some(leak(Builtin { f: BFn::Native(f), ops, lazy })));
            }
        }
    }
}
