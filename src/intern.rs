//! Two interners: `Name` for identifiers / operator names (arbitrary order), and `StrId` for TLA+
//! strings and model values, whose ids reproduce TLC's "order of first interning" (see TLC_NOTES 1.1).
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::{Arc, Mutex};

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

/// The process-wide string table: ids are positions in first-seen order and are the same in every
/// thread, so that value order and fingerprints agree between parallel workers. Only the main thread
/// adds strings; every thread keeps a cache in front of the table, so the lock is taken once per string
/// and thread.
#[derive(Default)]
struct GlobalStrs {
    map: HashMap<Arc<str>, u32>,
    items: Vec<Arc<str>>,
}
static GLOBAL_STRS: Mutex<Option<GlobalStrs>> = Mutex::new(None);

/// Ids from here on are private to one worker thread: a string that worker made and the table does not have.
const PROVISIONAL: u32 = 0x4000_0000;

#[derive(Default)]
struct StrCache {
    map: HashMap<Rc<str>, u32>,
    items: Vec<Option<Rc<str>>>,
    provisional: Vec<Rc<str>>,
}
impl StrCache {
    #[cold]
    fn slow_id(&mut self, s: &str) -> u32 {
        let r: Rc<str> = Rc::from(s);
        let i = {
            let mut g = GLOBAL_STRS.lock().unwrap_or_else(|e| e.into_inner());
            let g = g.get_or_insert_with(GlobalStrs::default);
            match g.map.get(s) {
                Some(&i) => i,
                None if is_worker() => {
                    // A worker must not decide the position of a new string in the global order: the
                    // state being evaluated goes back to the sequential search, which interns the string
                    // in its turn. Until then the worker computes with a private id.
                    worker_impure("a string first created during the search");
                    let i = PROVISIONAL + self.provisional.len() as u32;
                    self.provisional.push(r.clone());
                    self.map.insert(r, i);
                    return i;
                }
                None => {
                    let i = g.items.len() as u32;
                    let a: Arc<str> = Arc::from(s);
                    g.items.push(a.clone());
                    g.map.insert(a, i);
                    i
                }
            }
        };
        self.put(i, r.clone());
        self.map.insert(r, i);
        i
    }
    fn put(&mut self, i: u32, r: Rc<str>) {
        let i = i as usize;
        if i >= self.items.len() {
            self.items.resize(i + 1, None);
        }
        self.items[i] = Some(r);
    }
    #[cold]
    fn slow_str(&mut self, i: u32) -> Rc<str> {
        if i >= PROVISIONAL {
            return self.provisional[(i - PROVISIONAL) as usize].clone();
        }
        let r: Rc<str> = {
            let g = GLOBAL_STRS.lock().unwrap_or_else(|e| e.into_inner());
            Rc::from(&*g.as_ref().expect("string table").items[i as usize])
        };
        self.put(i, r.clone());
        self.map.insert(r.clone(), i);
        r
    }
}

thread_local! {
    static NAMES: RefCell<Interner> = RefCell::new(Interner::default());
    static STRS: RefCell<StrCache> = RefCell::new(StrCache::default());
    /// Set on the threads of parallel workers (see `worker_impure`).
    static WORKER: Cell<bool> = const { Cell::new(false) };
    static IMPURE: Cell<Option<&'static str>> = const { Cell::new(None) };
}

/// Marks the current thread as a parallel worker.
pub fn set_worker(on: bool) {
    WORKER.with(|w| w.set(on));
}
#[inline]
pub fn is_worker() -> bool {
    WORKER.with(|w| w.get())
}
/// Called where evaluation has an effect, or reads something, that depends on the order in which the
/// states are explored (printing, TLCSet / TLCGet registers, random choices, I/O, a new string). On a
/// worker thread it records the reason and returns true: the caller must not perform the effect, and the
/// state being expanded is handed back to the sequential search. Always false on the main thread.
#[inline]
pub fn worker_impure(what: &'static str) -> bool {
    if !is_worker() {
        return false;
    }
    IMPURE.with(|c| {
        if c.get().is_none() {
            c.set(Some(what));
        }
    });
    true
}
/// The first reason recorded by `worker_impure` on this thread since the last call.
pub fn take_impure() -> Option<&'static str> {
    IMPURE.with(|c| c.take())
}
/// What a builtin returns on a worker thread instead of performing an order-dependent effect.
#[cold]
pub fn impure_err<T>() -> R<T> {
    eval_err("this operator is evaluated by the sequential search only".to_string())
}

pub fn name(s: &str) -> Name {
    NAMES.with(|n| Name(n.borrow_mut().get(s)))
}
pub fn name_str(n: Name) -> Rc<str> {
    NAMES.with(|t| t.borrow().items[n.0 as usize].clone())
}
/// Interns a TLA+ string; the id is its position in first-seen order.
pub fn str_id(s: &str) -> StrId {
    STRS.with(|n| {
        let mut n = n.borrow_mut();
        if let Some(&i) = n.map.get(s) {
            return StrId(i);
        }
        StrId(n.slow_id(s))
    })
}
/// 64-bit hash of the bytes of a string (FNV-1a, then a multiply-xorshift finalizer); never 0.
fn content_hash(s: &str) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in s.as_bytes() {
        h = (h ^ *b as u64).wrapping_mul(0x0000_0100_0000_01B3);
    }
    h ^= h >> 32;
    h = h.wrapping_mul(0xD6E8_FEB8_6659_FD93);
    h ^= h >> 32;
    h | (h == 0) as u64
}
thread_local! {
    /// Content hash of each string this thread has fingerprinted, by id (0: not computed yet), and the
    /// table's (pointer, length) for `str_hash` to read without a borrow.
    static STR_HASH_TABLE: RefCell<Vec<u64>> = const { RefCell::new(Vec::new()) };
    static STR_HASHES: Cell<(*const u64, usize)> = const { Cell::new((std::ptr::null(), 0)) };
}
/// Hash of the text of a string / model value. Fingerprints are built from it, so they depend on what a
/// state contains and not on string ids: the same in every thread and for every order of interning.
#[inline]
pub fn str_hash(id: StrId) -> u64 {
    let (p, len) = STR_HASHES.with(|c| c.get());
    if (id.0 as usize) < len {
        // SAFETY: the table belongs to this thread, and the pointer and length are refreshed whenever it
        // is resized (`str_hash_slow`); the index was just checked.
        let h = unsafe { *p.add(id.0 as usize) };
        if h != 0 {
            return h;
        }
    }
    str_hash_slow(id)
}
#[cold]
fn str_hash_slow(id: StrId) -> u64 {
    let h = content_hash(&str_of(id));
    if id.0 < PROVISIONAL {
        STR_HASH_TABLE.with(|t| {
            let mut t = t.borrow_mut();
            let i = id.0 as usize;
            if i >= t.len() {
                t.resize((i + 1).next_power_of_two(), 0);
            }
            t[i] = h;
            STR_HASHES.with(|c| c.set((t.as_ptr(), t.len())));
        });
    }
    h
}
pub fn str_of(id: StrId) -> Rc<str> {
    STRS.with(|t| {
        let mut t = t.borrow_mut();
        if let Some(Some(r)) = t.items.get(id.0 as usize) {
            return r.clone();
        }
        t.slow_str(id.0)
    })
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
    if !any_typed() || id.0 >= PROVISIONAL {
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
