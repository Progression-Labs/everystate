//! Everything the checker needs from its environment. The core never touches the file system, the
//! clock or processes directly, so the same code runs natively and as WebAssembly.
use std::rc::Rc;

pub trait Host {
    fn read_file(&self, path: &str) -> Result<Vec<u8>, String>;
    fn write_file(&self, path: &str, data: &[u8]) -> Result<(), String>;
    fn append_file(&self, path: &str, data: &[u8]) -> Result<(), String>;
    fn exists(&self, path: &str) -> bool;
    fn env(&self) -> Vec<(String, String)>;
    /// Runs a command; returns (exit value, stdout, stderr).
    fn exec(&self, command: &[String], env: Option<&[(String, String)]>) -> Result<(i32, String, String), String>;
    /// Writes text to standard output (no newline is added).
    fn print(&self, s: &str);
    /// Milliseconds since the Unix epoch.
    fn now_ms(&self) -> f64;
}

/// A host without any capabilities (in-memory checking).
pub struct NullHost;
impl Host for NullHost {
    fn read_file(&self, path: &str) -> Result<Vec<u8>, String> {
        Err(format!("{} (file access is not available in this environment)", path))
    }
    fn write_file(&self, path: &str, _: &[u8]) -> Result<(), String> {
        Err(format!("{} (file access is not available in this environment)", path))
    }
    fn append_file(&self, path: &str, _: &[u8]) -> Result<(), String> {
        Err(format!("{} (file access is not available in this environment)", path))
    }
    fn exists(&self, _: &str) -> bool {
        false
    }
    fn env(&self) -> Vec<(String, String)> {
        vec![]
    }
    fn exec(&self, _: &[String], _: Option<&[(String, String)]>) -> Result<(i32, String, String), String> {
        Err("process execution is not available in this environment".into())
    }
    fn print(&self, _: &str) {}
    fn now_ms(&self) -> f64 {
        0.0
    }
}

pub type HostRef = Rc<dyn Host>;

/// "yyyy-MM-dd HH:mm:ss" (UTC) for a time in milliseconds since the epoch.
pub fn timestamp(ms: f64) -> String {
    let secs = (ms / 1000.0).floor() as i64;
    let days = secs.div_euclid(86400);
    let rem = secs.rem_euclid(86400);
    // civil-from-days (Howard Hinnant)
    let z = days + 719468;
    let era = z.div_euclid(146097);
    let doe = z.rem_euclid(146097);
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = if m <= 2 { y + 1 } else { y };
    format!("{:04}-{:02}-{:02} {:02}:{:02}:{:02}", y, m, d, rem / 3600, (rem % 3600) / 60, rem % 60)
}

#[cfg(not(target_arch = "wasm32"))]
pub struct NativeHost;
#[cfg(not(target_arch = "wasm32"))]
impl Host for NativeHost {
    fn read_file(&self, path: &str) -> Result<Vec<u8>, String> {
        std::fs::read(path).map_err(|e| format!("{} ({})", path, e))
    }
    fn write_file(&self, path: &str, data: &[u8]) -> Result<(), String> {
        if let Some(p) = std::path::Path::new(path).parent() {
            if !p.as_os_str().is_empty() {
                let _ = std::fs::create_dir_all(p);
            }
        }
        std::fs::write(path, data).map_err(|e| format!("{} ({})", path, e))
    }
    fn append_file(&self, path: &str, data: &[u8]) -> Result<(), String> {
        use std::io::Write;
        if let Some(p) = std::path::Path::new(path).parent() {
            if !p.as_os_str().is_empty() {
                let _ = std::fs::create_dir_all(p);
            }
        }
        std::fs::OpenOptions::new().create(true).append(true).open(path).and_then(|mut f| f.write_all(data)).map_err(|e| format!("{} ({})", path, e))
    }
    fn exists(&self, path: &str) -> bool {
        std::path::Path::new(path).exists()
    }
    fn env(&self) -> Vec<(String, String)> {
        std::env::vars_os().filter_map(|(k, v)| Some((k.into_string().ok()?, v.into_string().ok()?))).collect()
    }
    fn exec(&self, command: &[String], env: Option<&[(String, String)]>) -> Result<(i32, String, String), String> {
        if command.is_empty() {
            return Err("empty command".into());
        }
        let mut c = std::process::Command::new(&command[0]);
        c.args(&command[1..]);
        if let Some(e) = env {
            for (k, v) in e {
                c.env(k, v);
            }
        }
        match c.output() {
            Ok(o) => Ok((o.status.code().unwrap_or(1), String::from_utf8_lossy(&o.stdout).into_owned(), String::from_utf8_lossy(&o.stderr).into_owned())),
            Err(e) => Err(e.to_string()),
        }
    }
    fn print(&self, s: &str) {
        use std::io::Write;
        let out = std::io::stdout();
        let mut l = out.lock();
        let _ = l.write_all(s.as_bytes());
    }
    fn now_ms(&self) -> f64 {
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs_f64() * 1000.0).unwrap_or(0.0)
    }
}
