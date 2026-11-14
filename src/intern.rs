//! Two interners: `Name` for identifiers / operator names (arbitrary order), and `StrId` for TLA+
//! strings and model values, whose ids reproduce TLC's "order of first interning" (see TLC_NOTES 1.1).
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Name(pub u32);
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct StrId(pub u32);

#[derive(Default)]
struct Interner {
    map: HashMap<Rc<str>, u32>,
    items: Vec<Rc<str>>,
}
impl Interner {
    fn get(&mut self, s: &str) -> u32 {
        if let Some(&i) = self.map.get(s) {
            return i;
        }
        let i = self.items.len() as u32;
        let r: Rc<str> = Rc::from(s);
        self.items.push(r.clone());
        self.map.insert(r, i);
        i
    }
}

thread_local! {
    static NAMES: RefCell<Interner> = RefCell::new(Interner::default());
    static STRS: RefCell<Interner> = RefCell::new(Interner::default());
}

pub fn name(s: &str) -> Name {
    NAMES.with(|n| Name(n.borrow_mut().get(s)))
}
pub fn name_str(n: Name) -> Rc<str> {
    NAMES.with(|t| t.borrow().items[n.0 as usize].clone())
}
/// Interns a TLA+ string; the id is its position in first-seen order.
pub fn str_id(s: &str) -> StrId {
    STRS.with(|n| StrId(n.borrow_mut().get(s)))
}
pub fn str_of(id: StrId) -> Rc<str> {
    STRS.with(|t| t.borrow().items[id.0 as usize].clone())
}

impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&name_str(*self))
    }
}

thread_local! {
    static MV_TYPES: RefCell<Vec<u8>> = const { RefCell::new(Vec::new()) };
}
/// Type letter of a typed model value ("a_1" has type 'a'); None for untyped ones. Cached per string id.
static ANY_TYPED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
#[inline]
pub fn any_typed() -> bool {
    ANY_TYPED.load(std::sync::atomic::Ordering::Relaxed)
}
/// Creates (the id of) a model value; remembers whether any typed model value exists, so that the type
/// checks in comparisons cost nothing in the common untyped case.
pub fn model_value(name: &str) -> StrId {
    let b = name.as_bytes();
    if b.len() > 2 && b[1] == b'_' {
        ANY_TYPED.store(true, std::sync::atomic::Ordering::Relaxed);
    }
    str_id(name)
}
pub fn model_type(id: StrId) -> Option<u8> {
    if !any_typed() {
        return None;
    }
    MV_TYPES.with(|c| {
        let mut c = c.borrow_mut();
        let i = id.0 as usize;
        if i >= c.len() {
            c.resize(i + 1, 255);
        }
        if c[i] == 255 {
            let s = str_of(id);
            let b = s.as_bytes();
            c[i] = if b.len() > 2 && b[1] == b'_' { b[0] } else { 0 };
        }
        if c[i] == 0 { None } else { Some(c[i]) }
    })
}

pub type Loc = [u32; 4];

#[derive(Debug, Clone)]
pub struct TlaError {
    pub msg: String,
    pub loc: Option<Loc>,
    pub module: Option<String>,
    pub kind: &'static str,
}

#[derive(Debug)]
pub enum Fail {
    /// Control flow: the first satisfying assignment was found (ENABLED, \cdot as a predicate).
    Found,
    Tla(TlaError),
    /// The checker aborts with a final status (incomplete successor, illegal initial state).
    Check { status: &'static str, message: String },
}
pub type R<T> = Result<T, Box<Fail>>;

pub fn err<T>(kind: &'static str, msg: String) -> R<T> {
    Err(Box::new(Fail::Tla(TlaError { msg, loc: None, module: None, kind })))
}
pub fn eval_err<T>(msg: String) -> R<T> {
    err("eval", msg)
}
