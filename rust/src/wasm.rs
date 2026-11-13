//! WebAssembly entry points (wasm32-unknown-unknown, no JS toolchain). The JS wrapper in `wasm/`
//! instantiates the module once per check, hands over the module sources and the config, and reads
//! back one JSON result. Imports: `env.es_print(ptr, len)` and `env.es_now() -> f64`.
use crate::checker::{CheckOptions, NoEvents};
use crate::cli::{result_json, setup_error_json};
use crate::host::Host;
use crate::intern::*;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

#[link(wasm_import_module = "env")]
extern "C" {
    fn es_print(ptr: *const u8, len: usize);
    fn es_now() -> f64;
}

struct WasmHost;
impl Host for WasmHost {
    fn read_file(&self, path: &str) -> Result<Vec<u8>, String> {
        Err(format!("{} (file access is not available in WebAssembly)", path))
    }
    fn write_file(&self, path: &str, _: &[u8]) -> Result<(), String> {
        Err(format!("{} (file access is not available in WebAssembly)", path))
    }
    fn append_file(&self, path: &str, _: &[u8]) -> Result<(), String> {
        Err(format!("{} (file access is not available in WebAssembly)", path))
    }
    fn exists(&self, _: &str) -> bool {
        false
    }
    fn env(&self) -> Vec<(String, String)> {
        vec![]
    }
    fn exec(&self, _: &[String], _: Option<&[(String, String)]>) -> Result<(i32, String, String), String> {
        Err("process execution is not available in WebAssembly".into())
    }
    fn print(&self, s: &str) {
        // Print/PrintT lines arrive with a trailing newline; the callback receives the bare line
        let line = s.strip_suffix('\n').unwrap_or(s);
        unsafe { es_print(line.as_ptr(), line.len()) }
    }
    fn now_ms(&self) -> f64 {
        unsafe { es_now() }
    }
}

thread_local! {
    static MODULES: RefCell<HashMap<String, String>> = RefCell::new(HashMap::new());
    static RESULT: RefCell<Vec<u8>> = const { RefCell::new(Vec::new()) };
}

#[no_mangle]
pub extern "C" fn es_alloc(len: usize) -> *mut u8 {
    let mut v: Vec<u8> = Vec::with_capacity(len.max(1));
    let p = v.as_mut_ptr();
    std::mem::forget(v);
    p
}

unsafe fn take_str(ptr: *mut u8, len: usize) -> String {
    let v = Vec::from_raw_parts(ptr, len, len.max(1));
    String::from_utf8_lossy(&v).into_owned()
}

/// Registers the source of a module. Both buffers must come from `es_alloc` and are consumed.
#[no_mangle]
pub unsafe extern "C" fn es_add_module(name: *mut u8, name_len: usize, src: *mut u8, src_len: usize) {
    let (n, s) = (take_str(name, name_len), take_str(src, src_len));
    MODULES.with(|m| m.borrow_mut().insert(n, s));
}

/// Model-checks `root` with the given config text. `deadlock`: 1 = check (unless the config disables it),
/// 0 = do not check. `depth_limit`: bytes of the linear-memory stack evaluation may use (0 = default).
/// Returns a pointer to the JSON result; its length is `es_result_len()`.
#[no_mangle]
pub unsafe extern "C" fn es_check(root: *mut u8, root_len: usize, cfg: *mut u8, cfg_len: usize, deadlock: i32) -> *const u8 {
    let (root, cfg_text) = (take_str(root, root_len), take_str(cfg, cfg_len));
    // The shadow stack is 64 MiB (see .cargo/config.toml); stop cleanly before it is exhausted.
    crate::eval::set_stack_limit(56 << 20);
    let json = run(&root, &cfg_text, deadlock != 0);
    RESULT.with(|r| {
        *r.borrow_mut() = json.into_bytes();
        r.borrow().as_ptr()
    })
}

#[no_mangle]
pub extern "C" fn es_result_len() -> usize {
    RESULT.with(|r| r.borrow().len())
}

fn run(root: &str, cfg_text: &str, deadlock: bool) -> String {
    let setup: R<crate::model::Model> = (|| {
        let cfg = crate::cfg::parse_config(cfg_text)?;
        let resolve: crate::modules::SourceResolver = Box::new(|name: &str| {
            MODULES.with(|m| m.borrow().get(name).cloned()).or_else(|| crate::bundled::BUNDLED.iter().find(|(n, _)| *n == name).map(|(_, s)| s.to_string()))
        });
        crate::model::build_model(root, resolve, &cfg, Rc::new(WasmHost))
    })();
    let model = match setup {
        Ok(m) => m,
        Err(e) => return setup_error_json(&e).0,
    };
    let (res, _checker) = crate::liveness::model_check(&model, CheckOptions { check_deadlock: deadlock && model.check_deadlock, record_graph: false }, &mut NoEvents);
    result_json(&model, &res, true)
}
