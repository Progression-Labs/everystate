//! Command-line driver (port of main.ts). Accepts TLC's flags and prints TLC-compatible output,
//! including `-tool` framing, `-dump`, the XMLExporter emulation and the `java` command-line shim.
use crate::cfg::parse_config;
use crate::checker::*;
use crate::eval::StateRef;
use crate::host::{timestamp, HostRef};
use crate::intern::*;
use crate::liveness::model_check;
use crate::model::*;
use crate::modules::{def_level, Loader, SourceResolver, Sym};
use crate::pprint::ppr;
use crate::stdlib::{build_stdlib, global_defs};
use crate::value::fmt;
use std::cell::RefCell;
use std::rc::Rc;

pub const VERSION: &str = env!("CARGO_PKG_VERSION");

// ---- path helpers (pure string operations: no file-system access) ----
/// On Windows, backslashes are separators too; everything is handled with forward slashes, which
/// Windows file APIs accept.
fn norm(p: &str) -> String {
    if cfg!(windows) { p.replace('\\', "/") } else { p.to_string() }
}
/// A Windows drive prefix such as `C:` at the start of a path.
fn drive(p: &str) -> Option<&str> {
    let b = p.as_bytes();
    if cfg!(windows) && b.len() >= 2 && b[1] == b':' && b[0].is_ascii_alphabetic() { Some(&p[..2]) } else { None }
}
pub fn path_join(a: &str, b: &str) -> String {
    let (a, b) = (norm(a), norm(b));
    if b.starts_with('/') || drive(&b).is_some() || a.is_empty() {
        return b;
    }
    if a.ends_with('/') { format!("{}{}", a, b) } else { format!("{}/{}", a, b) }
}
pub fn path_resolve(cwd: &str, p: &str) -> String {
    let full = path_join(cwd, p);
    let (prefix, rest) = match drive(&full) {
        Some(d) => (d.to_string(), &full[2..]),
        None => (String::new(), &full[..]),
    };
    let mut parts: Vec<&str> = vec![];
    for seg in rest.split('/') {
        match seg {
            "" | "." => {}
            ".." => {
                parts.pop();
            }
            s => parts.push(s),
        }
    }
    format!("{}/{}", prefix, parts.join("/"))
}
fn last_sep(p: &str) -> Option<usize> {
    if cfg!(windows) { p.rfind(|c| c == '/' || c == '\\') } else { p.rfind('/') }
}
pub fn dirname(p: &str) -> String {
    match last_sep(p) {
        Some(0) => "/".to_string(),
        Some(i) => p[..i].to_string(),
        None => ".".to_string(),
    }
}
pub fn basename<'a>(p: &'a str, ext: &str) -> &'a str {
    let b = match last_sep(p) {
        Some(i) => &p[i + 1..],
        None => p,
    };
    if !ext.is_empty() && b.ends_with(ext) && b.len() > ext.len() { &b[..b.len() - ext.len()] } else { b }
}

fn commas(n: f64) -> String {
    let s = format!("{}", n.round() as i64);
    let (neg, digits) = match s.strip_prefix('-') {
        Some(d) => (true, d.to_string()),
        None => (false, s),
    };
    let mut out = String::new();
    for (i, c) in digits.chars().enumerate() {
        if i > 0 && (digits.len() - i) % 3 == 0 {
            out.push(',');
        }
        out.push(c);
    }
    if neg { format!("-{}", out) } else { out }
}

pub fn state_text(model: &Model, s: &StateRef) -> String {
    let vars = &model.vars;
    if vars.len() == 1 {
        return format!("{} = {}\n", vars[0].name, ppr(&fmt(&s.get(0))));
    }
    let mut out = String::new();
    for (i, v) in vars.iter().enumerate() {
        out += &format!("/\\ {} = {}\n", v.name, ppr(&fmt(&s.get(i))));
    }
    out
}
pub fn action_label(a: Option<&Action>) -> String {
    match a {
        None => "<Initial predicate>".to_string(),
        Some(a) => format!("<{}{} line {}, col {} to line {}, col {} of module {}>", a.name, a.params, a.loc[0], a.loc[1], a.loc[2], a.loc[3], a.module),
    }
}

struct Reporter {
    tool: bool,
    host: HostRef,
}
impl Reporter {
    // cls: 0 none, 1 error, 2 bug, 3 warning, 4 state
    fn msg(&self, code: u32, cls: u32, text: &str) {
        if self.tool {
            self.host.print(&format!("@!@!@STARTMSG {}:{} @!@!@\n{}\n@!@!@ENDMSG {} @!@!@\n", code, cls, text, code));
        } else {
            let prefix = match cls {
                1 => "Error: ",
                3 => "Warning: ",
                4 => "State ",
                _ => "",
            };
            self.host.print(&format!("{}{}\n", prefix, text));
        }
    }
    fn plain(&self, text: &str) {
        self.host.print(&format!("{}\n", text));
    }
    fn now(&self) -> String {
        timestamp(self.host.now_ms())
    }
}

fn exit_code(status: &str) -> i32 {
    match status {
        "ok" => 0,
        "assumption" => 10,
        "deadlock" => 11,
        "invariant" | "invariant-init" => 12,
        "action-property" | "implied-init" | "liveness" => 13,
        "incomplete" => 75,
        _ => 255,
    }
}

fn arity1(a: &str) -> bool {
    matches!(
        a,
        "-workers" | "-fp" | "-lncheck" | "-metadir" | "-seed" | "-depth" | "-fpmem" | "-coverage" | "-checkpoint" | "-maxSetSize" | "-fpbits" | "-userFile" | "-recover" | "-aril"
            | "-dfid" | "-suppressMessages" | "-messagesAsErrors" | "-inv" | "-invlevel" | "-postCondition" | "-teSpecOutDir"
    )
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
            '\x08' => o.push_str("\\b"),
            '\x0c' => o.push_str("\\f"),
            c if (c as u32) < 0x20 => o.push_str(&format!("\\u{:04x}", c as u32)),
            c => o.push(c),
        }
    }
    o.push('"');
}

/// The `-json` result line (also what the WebAssembly API returns).
pub fn result_json(model: &Model, res: &CheckResult, extended: bool) -> String {
    let mut o = String::with_capacity(256);
    o.push_str("{\"status\":");
    json_str(res.status, &mut o);
    if let Some(n) = &res.name {
        o.push_str(",\"name\":");
        json_str(n, &mut o);
    }
    if let Some(m) = &res.message {
        o.push_str(",\"message\":");
        json_str(m, &mut o);
    }
    o.push_str(&format!(",\"generated\":{},\"distinct\":{},\"queue\":{},\"depth\":{}", res.generated, res.distinct, res.queue, res.depth));
    if let Some(l) = res.loop_to {
        o.push_str(&format!(",\"loopTo\":{}", l));
    }
    if extended {
        if res.status == "liveness" {
            o.push_str(",\"loopAction\":");
            match res.loop_action {
                Some(a) => json_str(&model.actions[a].name, &mut o),
                None => o.push_str("null"),
            }
        }
        if let Some(c) = res.code {
            o.push_str(&format!(",\"code\":{}", c));
        }
        o.push_str(",\"vars\":[");
        for (j, v) in model.vars.iter().enumerate() {
            if j > 0 {
                o.push(',');
            }
            json_str(&v.name.to_string(), &mut o);
        }
        o.push(']');
    }
    if let Some(tr) = &res.trace {
        o.push_str(",\"trace\":[");
        for (i, t) in tr.iter().enumerate() {
            if i > 0 {
                o.push(',');
            }
            o.push_str("{\"action\":");
            match t.action {
                Some(a) => json_str(&model.actions[a].name, &mut o),
                None => o.push_str("null"),
            }
            o.push_str(",\"state\":{");
            for (j, v) in model.vars.iter().enumerate() {
                if j > 0 {
                    o.push(',');
                }
                json_str(&v.name.to_string(), &mut o);
                o.push(':');
                json_str(&fmt(&t.state.get(j)), &mut o);
            }
            o.push_str("}}");
        }
        o.push(']');
    }
    o.push('}');
    o
}

pub fn setup_error_json(e: &Fail) -> (String, i32) {
    let (kind, msg) = match e {
        Fail::Tla(t) => (t.kind, t.msg.clone()),
        Fail::Check { message, .. } => ("error", message.clone()),
        Fail::Found => ("error", "internal error".to_string()),
    };
    let mut o = String::from("{\"status\":\"setup-error\",\"kind\":");
    json_str(kind, &mut o);
    o.push_str(",\"message\":");
    json_str(&msg, &mut o);
    o.push('}');
    (o, if kind == "config" { 151 } else { 150 })
}

struct CliEvents<'r> {
    rep: &'r Reporter,
    json: bool,
    first: bool,
}
impl Events for CliEvents<'_> {
    fn init_done(&mut self, init_generated: u64, init_distinct: u64) {
        if self.json {
            return;
        }
        self.first = false;
        let rep = self.rep;
        rep.msg(2189, 0, "Computing initial states...");
        if init_generated == init_distinct {
            rep.msg(2190, 0, &format!("Finished computing initial states: {} distinct state{} generated at {}.", init_distinct, if init_distinct == 1 { "" } else { "s" }, rep.now()));
        } else {
            rep.msg(
                2191,
                0,
                &format!("Finished computing initial states: {} state{} generated, with {} of them distinct at {}.", init_generated, if init_generated == 1 { "" } else { "s" }, init_distinct, rep.now()),
            );
        }
    }
    fn progress(&mut self, depth: u32, generated: u64, distinct: u64, queue: u64) {
        if self.json {
            return;
        }
        let rep = self.rep;
        rep.msg(
            2200,
            0,
            &format!("Progress({}) at {}: {} states generated, {} distinct states found, {} states left on queue.", depth, rep.now(), commas(generated as f64), commas(distinct as f64), commas(queue as f64)),
        );
    }
    fn liveness(&mut self, phase: &str, branches: usize, depth: u32, generated: u64, distinct: u64) {
        if self.json {
            return;
        }
        let rep = self.rep;
        match phase {
            "branches" => rep.msg(2212, 0, &format!("Implied-temporal checking--satisfiability problem has {} branches.", branches)),
            "start" => {
                if !rep.tool {
                    rep.msg(
                        2200,
                        0,
                        &format!("Progress({}) at {}: {} states generated, {} distinct states found, 0 states left on queue.", depth, rep.now(), commas(generated as f64), commas(distinct as f64)),
                    );
                }
                rep.msg(
                    2192,
                    0,
                    &format!(
                        "Checking {}temporal properties for the complete state space with {} total distinct states at ({})",
                        if branches > 1 { format!("{} branches of ", branches) } else { String::new() },
                        distinct as usize * branches,
                        rep.now()
                    ),
                );
            }
            _ => rep.msg(2267, 0, &format!("Finished checking temporal properties in 00s at {}", rep.now())),
        }
    }
}

const USAGE: &str = concat!("everystate ", env!("CARGO_PKG_VERSION"), " - a TLA+ model checker (TLC-compatible command line)\n\nUsage: everystate [options] SPEC[.tla]\n\n  -config FILE        configuration file (default: SPEC.cfg)\n  -deadlock           do not check for deadlock\n  -tool               machine-readable output (TLC's -tool message framing)\n  -dump [dot[,actionlabels]] FILE   write the reachable state graph\n  -json               print a single JSON result object instead of TLC-style output\n  -workers N, -fp N, -lncheck S, -metadir DIR, -seed N, ...   accepted for compatibility\n\nExit status: 0 success, 10 assumption, 11 deadlock, 12 safety, 13 liveness, 150 parse error, 151 config error.\n");

struct Dump {
    file: String,
    dot: bool,
    opts: String,
}

/// Module sources: the spec's directory, then the library paths, then the bundled modules.
pub fn file_resolver(host: HostRef, dirs: Vec<String>, parsed: Rc<RefCell<Vec<String>>>) -> SourceResolver {
    Box::new(move |name: &str| {
        for d in &dirs {
            let p = path_join(d, &format!("{}.tla", name));
            if host.exists(&p) {
                if let Ok(bytes) = host.read_file(&p) {
                    parsed.borrow_mut().push(p);
                    return Some(String::from_utf8_lossy(&bytes).into_owned());
                }
            }
        }
        crate::bundled::BUNDLED.iter().find(|(n, _)| *n == name).map(|(_, s)| s.to_string())
    })
}

pub fn run_cli(argv: &[String], host: HostRef, library_paths: &[String]) -> i32 {
    if argv.first().map(|a| a == "pcal").unwrap_or(false) {
        // `everystate pcal [options] File`: the PlusCal translator
        return crate::pcal::trans::run(&argv[1..], host);
    }
    let mut spec: Option<String> = None;
    let mut config: Option<String> = None;
    let (mut deadlock, mut tool, mut json) = (true, false, false);
    let mut dump: Option<Dump> = None;
    let mut i = 0;
    while i < argv.len() {
        let a = argv[i].as_str();
        match a {
            "-config" => {
                i += 1;
                config = argv.get(i).cloned();
            }
            "-deadlock" => deadlock = false,
            "-cdot" | "-Dtlc2.tool.impl.Tool.cdot=true" => crate::eval::CDOT.store(true, std::sync::atomic::Ordering::Relaxed),
            "-tool" => tool = true,
            "-json" => json = true,
            "-dump" => {
                i += 1;
                let x = argv.get(i).cloned().unwrap_or_default();
                if x == "dot" || x.starts_with("dot,") {
                    i += 1;
                    dump = Some(Dump { file: argv.get(i).cloned().unwrap_or_default(), dot: true, opts: x.to_lowercase() });
                } else {
                    dump = Some(Dump { file: x, dot: false, opts: String::new() });
                }
            }
            "-dumpTrace" | "-loadTrace" => i += 2,
            "-simulate" | "-generate" => {
                host.print("Error: simulation mode is not supported by everystate yet.\n");
                return 1;
            }
            "-h" | "-help" | "--help" => {
                host.print(USAGE);
                host.print(crate::pcal::USAGE);
                return 0;
            }
            "-version" | "--version" => {
                host.print(&format!("everystate {}\n", VERSION));
                return 0;
            }
            _ if arity1(a) => i += 1,
            _ if a.starts_with('-') => {}
            _ => {
                if let Some(s) = &spec {
                    host.print(&format!("Error: more than one input files: {} and {}\n", s, a));
                    return 1;
                }
                spec = Some(a.to_string());
            }
        }
        i += 1;
    }
    let spec = match spec {
        Some(s) => s,
        None => {
            host.print(&format!("Error: Missing input TLA+ module.\n{}", USAGE));
            return 1;
        }
    };
    let spec_path = if spec.ends_with(".tla") { spec.clone() } else { format!("{}.tla", spec) };
    let cwd = host.cwd();
    let dir = dirname(&path_resolve(&cwd, &spec_path));
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
    let rep = Reporter { tool, host: host.clone() };
    let t0 = host.now_ms();
    let parsed: Rc<RefCell<Vec<String>>> = Rc::new(RefCell::new(vec![]));
    let mut libs = vec![dir.clone()];
    libs.extend(library_paths.iter().cloned());
    let resolve = file_resolver(host.clone(), libs, parsed.clone());
    let pad = |n: i64| format!("{:02}", n);
    let finish = |code: i32| -> i32 {
        let ms = (host.now_ms() - t0).max(0.0) as i64;
        let s = ms / 1000;
        let dur = if tool {
            format!("{}ms", ms)
        } else if s < 60 {
            format!("{}s", pad(s))
        } else if s < 3600 {
            format!("{}min {}s", pad(s / 60), pad(s % 60))
        } else {
            format!("{}h {}min", pad(s / 3600), pad((s % 3600) / 60))
        };
        if !json {
            rep.msg(2186, 0, &format!("Finished in {} at ({})", dur, rep.now()));
        }
        code
    };
    if !json {
        rep.msg(2262, 0, &format!("TLC2 Version 2.19 of 08 August 2024 (everystate {})", VERSION));
        rep.msg(
            2187,
            0,
            &format!("Running breadth-first search Model-Checking with fp 0 and seed 0 with 1 worker on 1 cores with 0MB heap and 0MB offheap memory (everystate {}, Rust, HashFPSet, MemStateQueue).", VERSION),
        );
    }
    let setup: R<Model> = (|| {
        if !host.exists(&cfg_path) {
            return err("config", format!("TLC encountered the following error reading the configuration file {}:\nFile not found.", cfg_path));
        }
        let text = String::from_utf8_lossy(&host.read_file(&cfg_path).unwrap_or_default()).into_owned();
        let cfg = parse_config(&text)?;
        if !json && tool {
            rep.msg(2220, 0, "Starting SANY...");
        }
        let m = build_model(&root_name, resolve, &cfg, host.clone());
        if !json {
            // like SANY, say so when a PlusCal algorithm or its translation changed since it was translated
            let pcal = crate::pcal::trans::check_translations(&host, &parsed.borrow(), &root_name);
            for (i, p) in parsed.borrow().iter().enumerate() {
                rep.plain(&format!("Parsing file {}", p));
                host.print(&pcal.after_file[i]);
            }
            // (SANY gets as far as the warnings only if every module could be read and parsed)
            if !matches!(&m, Err(e) if matches!(&**e, Fail::Tla(t) if t.kind == "parse" || t.msg.starts_with("Cannot find source file"))) {
                host.print(&pcal.warnings);
            }
        }
        let m = m?;
        if !json {
            for name in &m.loader.load_order {
                rep.plain(&format!("Semantic processing of module {}", name));
            }
            if tool {
                rep.msg(2219, 0, "SANY finished.");
            }
        }
        Ok(m)
    })();
    let model = match setup {
        Ok(m) => m,
        Err(e) => {
            if json {
                let (o, code) = setup_error_json(&e);
                host.print(&format!("{}\n", o));
                return code;
            }
            return match &*e {
                Fail::Tla(t) if t.kind == "config" => {
                    rep.msg(1000, 1, &t.msg);
                    finish(151)
                }
                Fail::Tla(t) => {
                    rep.plain(&t.msg);
                    rep.msg(3002, 1, "Parsing or semantic analysis failed.");
                    finish(150)
                }
                _ => {
                    rep.msg(1000, 1, "internal error during setup");
                    finish(255)
                }
            };
        }
    };
    if !json {
        rep.msg(2185, 0, &format!("Starting... ({})", rep.now()));
    }
    let mut events = CliEvents { rep: &rep, json, first: true };
    let (res, checker) = model_check(&model, CheckOptions { check_deadlock: deadlock && model.check_deadlock, record_graph: dump.is_some() }, &mut events);
    let first = events.first;
    if let Some(d) = &dump {
        if let Err(e) = write_dump(&model, &checker, d, &host) {
            rep.msg(1000, 1, &format!("Failed to write the state dump: {}", e));
        }
    }
    if json {
        host.print(&format!("{}\n", result_json(&model, &res, false)));
        return exit_code(res.status);
    }
    if first {
        rep.msg(2189, 0, "Computing initial states...");
    }
    report(&rep, &model, &res, t0);
    finish(if res.call_stack.is_some() {
        75
    } else if res.code == Some(2111) {
        76
    } else {
        exit_code(res.status)
    })
}

/// ALIAS: the text TLC prints for a trace state when the configuration names an alias
/// (Tool.evalAlias and RecordValue.PrintTLCState).  `Ok(None)`: print the plain state.
/// `Err`: formatting threw, with the Java exception class and message.
fn alias_text(model: &Model, cur: &StateRef, nxt: &StateRef) -> Result<Option<String>, (String, String)> {
    let p = match &model.alias {
        Some(p) => p,
        None => return Ok(None),
    };
    let ev = crate::eval::ev();
    ev.set_state(cur, Some(nxt));
    ev.init_mode.set(false);
    ev.prime_depth.set(0);
    ev.call_depth.set(0);
    ev.n_assigned.set(0);
    let mut fields: Vec<(String, crate::value::Value)> = vec![];
    match ev.eval(p.e, &p.ctx) {
        Ok(crate::value::Value::Record(r)) => {
            // TLC prints the fields in the order of the record constructor, not sorted
            let mut order: Vec<StrId> = vec![];
            if let Some(Sym::Def(d)) = model.root.syms.get(name(&p.name)) {
                if let Some(b) = d.body.get() {
                    if let crate::ast::E::Rec(fs, _) = &b.e {
                        order = fs.iter().map(|f| f.0).collect();
                    }
                }
            }
            for id in order.iter().chain(r.names.iter()) {
                let k = str_of(*id).to_string();
                if fields.iter().any(|f| f.0 == k) {
                    continue;
                }
                if let Some(v) = r.get(*id) {
                    fields.push((k, v.clone()));
                }
            }
        }
        Ok(_) => return Ok(None),
        Err(e) => match *e {
            crate::intern::Fail::Tla(t) => {
                for (i, v) in model.vars.iter().enumerate() {
                    fields.push((v.name.to_string(), cur.get(i)));
                }
                fields.push(("_ALIASEvalError".into(), crate::value::Value::Str(str_id(&t.msg))));
            }
            _ => return Ok(None),
        },
    }
    let fi = fields.iter().position(|f| f.0 == "_format");
    let format = match fi {
        Some(i) => match &fields[i].1 {
            crate::value::Value::Str(s) => str_of(*s).to_string(),
            _ => return Err(("java.lang.ClassCastException".into(), "the _format field of an ALIAS must be a string".into())),
        },
        None => (if fields.len() == 1 { "%s = %s\n" } else { "/\\ %s = %s\n" }).to_string(),
    };
    let mut out = String::new();
    for (i, (k, v)) in fields.iter().enumerate() {
        if Some(i) == fi {
            continue;
        }
        match crate::community::java_format(&format, &[k.clone(), ppr(&fmt(v))]) {
            Ok(t) => out += &t,
            Err(_) => {
                // a conversion other than %s applied to a string argument
                let c: Vec<char> = format.chars().collect();
                let mut j = 0;
                while j < c.len() {
                    if c[j] == '%' {
                        j += 1;
                        while j < c.len() && !c[j].is_ascii_alphabetic() && c[j] != '%' {
                            j += 1;
                        }
                        if j < c.len() && !"sSn%".contains(c[j]) {
                            return Err(("java.util.IllegalFormatConversionException".into(), format!("{} != java.lang.String", c[j])));
                        }
                    }
                    j += 1;
                }
                return Err(("java.util.MissingFormatArgumentException".into(), format!("Format specifier in '{}'", format)));
            }
        }
    }
    Ok(Some(out))
}

fn print_trace(rep: &Reporter, model: &Model, res: &CheckResult) {
    if let Some(tr) = &res.trace {
        for (i, t) in tr.iter().enumerate() {
            let label = action_label(if i == 0 { None } else { t.action.map(|a| &model.actions[a]) });
            // the successor used for primed variables in an ALIAS: the next trace state, the state the
            // lasso returns to, or the state itself
            let nxt = match tr.get(i + 1) {
                Some(n) => &n.state,
                None => match res.loop_to {
                    Some(l) if l >= 0 && (l as usize) < tr.len() => &tr[l as usize].state,
                    _ => &t.state,
                },
            };
            let text = match alias_text(model, &t.state, nxt) {
                Ok(Some(x)) => x,
                Ok(None) => state_text(model, &t.state),
                Err((class, m)) => {
                    rep.msg(
                        1000,
                        1,
                        &format!("TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a {}\n: {}", class, m),
                    );
                    return;
                }
            };
            rep.msg(2217, 4, &format!("{}: {}\n{}", i + 1, label, text));
        }
    }
}

fn exp1(p: f64) -> String {
    // Number.prototype.toExponential(1), with Java's exponent format
    if p == 0.0 {
        return "0.0".into();
    }
    let s = format!("{:.1e}", p);
    s.replace('e', "E")
}

fn report(rep: &Reporter, model: &Model, res: &CheckResult, t0: f64) {
    let progress_line = || {
        let mins = ((rep.host.now_ms() - t0) / 60000.0).max(1e-6);
        rep.msg(
            2200,
            0,
            &format!(
                "Progress({}) at {}: {} states generated ({} s/min), {} distinct states found ({} ds/min), {} states left on queue.",
                res.depth,
                rep.now(),
                commas(res.generated as f64),
                commas(res.generated as f64 / mins),
                commas(res.distinct as f64),
                commas(res.distinct as f64 / mins),
                commas(res.queue as f64)
            ),
        );
    };
    let summary = || {
        if rep.tool {
            progress_line();
        }
        rep.msg(2199, 0, &format!("{} states generated, {} distinct states found, {} states left on queue.", res.generated, res.distinct, res.queue));
        rep.msg(2194, 0, &format!("The depth of the complete state graph search is {}.", res.depth));
        if let Some(o) = &res.outdegree {
            if res.status == "ok" || rep.tool {
                rep.msg(
                    2268,
                    0,
                    &format!("The average outdegree of the complete state graph is {} (minimum is {}, the maximum {} and the 95th percentile is {}).", o.avg, o.min, o.max, o.p95),
                );
            }
        }
    };
    let first_state = || res.trace.as_ref().map(|t| state_text(model, &t[0].state)).unwrap_or_default();
    let name = res.name.as_deref().unwrap_or("undefined");
    match res.status {
        "ok" => {
            let p = res.distinct as f64 * ((res.generated as f64 - res.distinct as f64) / 18446744073709551616.0);
            rep.msg(
                2193,
                0,
                &format!(
                    "Model checking completed. No error has been found.\n  Estimates of the probability that TLC did not check all reachable states\n  because two distinct states had the same fingerprint:\n  calculated (optimistic):  val = {}",
                    exp1(p)
                ),
            );
            summary();
            return;
        }
        "assumption" => {
            rep.msg(2104, 1, res.message.as_deref().unwrap_or(""));
            return;
        }
        "invariant-init" => {
            rep.msg(2107, 1, &format!("Invariant {} is violated by the initial state:\n{}", name, first_state()));
            return;
        }
        "implied-init" => {
            rep.msg(2108, 1, &format!("Property {} is violated by the initial state:\n{}", name, first_state()));
            return;
        }
        "invariant" => rep.msg(2110, 1, &format!("Invariant {} is violated.", name)),
        "action-property" => rep.msg(2112, 1, &format!("Action property {} is violated.", name)),
        "deadlock" => rep.msg(2114, 1, "Deadlock reached."),
        "liveness" => {
            rep.msg(2116, 1, "Temporal properties were violated.\n");
            rep.msg(2264, 1, "The following behavior constitutes a counter-example:\n");
            print_trace(rep, model, res);
            let n = res.trace.as_ref().map_or(0, |t| t.len());
            let la = action_label(res.loop_action.map(|a| &model.actions[a]));
            match res.loop_to {
                Some(l) if l >= 0 => {
                    if rep.tool {
                        rep.msg(2122, 4, &format!("{}: Back to state: {}\n", l + 1, la));
                    } else {
                        rep.host.print(&format!("Back to state {}: {}\n\n", l + 1, la));
                    }
                }
                _ => rep.msg(2218, 4, &format!("{}: Stuttering", n + 1)),
            }
            rep.msg(2267, 0, &format!("Finished checking temporal properties in 00s at {}", rep.now()));
            if rep.tool {
                progress_line();
            }
            rep.msg(2199, 0, &format!("{} states generated, {} distinct states found, {} states left on queue.", res.generated, res.distinct, res.queue));
            return;
        }
        "incomplete" => rep.msg(2109, 1, &format!("{}\n", res.message.as_deref().unwrap_or(""))),
        _ => {
            let m = res.message.as_deref().unwrap_or("unknown error");
            if let Some(code) = res.code {
                rep.msg(code, 1, m);
            } else {
                if let Some(tr) = &res.trace {
                    if tr.len() == 1 && tr[0].id == -1 && tr[0].action.is_none() {
                        rep.msg(2102, 1, &format!("{}\nWhile working on the initial state:\n{}", m, state_text(model, &tr[0].state)));
                        if res.print_summary {
                            summary();
                        }
                        return;
                    }
                }
                rep.msg(
                    1000,
                    1,
                    &format!("TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: {}", m),
                );
            }
        }
    }
    if res.trace.as_ref().map_or(false, |t| !t.is_empty()) {
        rep.msg(2121, 1, "The behavior up to this point is:");
        print_trace(rep, model, res);
    }
    if let Some(cs) = &res.call_stack {
        rep.msg(2103, 1, &format!("The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n{}", cs));
    }
    if res.print_summary {
        summary();
    }
}

fn write_dump(model: &Model, checker: &Checker, dump: &Dump, host: &HostRef) -> Result<(), String> {
    let states = &checker.states;
    if !dump.dot {
        let mut out = String::new();
        for (i, s) in states.iter().enumerate() {
            out += &format!("State {}:\n{}\n", i + 1, state_text(model, s));
        }
        let file = if dump.file.ends_with(".dump") { dump.file.clone() } else { format!("{}.dump", dump.file) };
        return host.write_file(&file, out.as_bytes());
    }
    let labels = dump.opts.contains("actionlabels");
    let esc = |s: &str| -> String { s.replace('\\', "\\\\").replace('"', "\\\"").trim().replace('\n', "\\n") };
    let mut ids: Vec<String> = Vec::with_capacity(states.len());
    for s in states {
        ids.push((crate::tshash::fingerprint(checker, s).map_err(|_| "cannot fingerprint a state".to_string())?).to_string());
    }
    let mut lines: Vec<String> = vec!["strict digraph DiskGraph {".into(), "nodesep=0.35;".into(), "subgraph cluster_graph {".into(), "color=\"white\";".into()];
    // ranks: level -> state ids in insertion order
    let mut ranks: Vec<(u32, Vec<usize>)> = vec![];
    let mut rank = |i: usize, ranks: &mut Vec<(u32, Vec<usize>)>| {
        let l = checker.level[i];
        match ranks.iter_mut().find(|r| r.0 == l) {
            Some(r) => {
                if !r.1.contains(&i) {
                    r.1.push(i);
                }
            }
            None => ranks.push((l, vec![i])),
        }
    };
    let mut written = vec![false; states.len()];
    for &i in &checker.inits {
        let i = i as usize;
        lines.push(format!("{} [label=\"{}\",style = filled]", ids[i], esc(&state_text(model, &states[i]))));
        written[i] = true;
        rank(i, &mut ranks);
    }
    for s in 0..states.len() {
        let empty: Vec<u32> = vec![];
        let (su, sa) = (checker.succ.get(s).unwrap_or(&empty), checker.succ_act.get(s).unwrap_or(&empty));
        for j in 0..su.len() {
            let t = su[j] as usize;
            let a = &model.actions[sa[j] as usize];
            lines.push(format!("{} -> {} [label=\"{}\",color=\"black\",fontcolor=\"black\"];", ids[s], ids[t], if labels { esc(&a.name) } else { String::new() }));
            rank(s, &mut ranks);
            if !written[t] {
                written[t] = true;
                lines.push(format!("{} [label=\"{}\"];", ids[t], esc(&state_text(model, &states[t]))));
            }
        }
    }
    ranks.sort_by_key(|r| r.0);
    for (_, set) in &ranks {
        lines.push(format!("{{rank = same; {}}}", set.iter().map(|i| format!("{};", ids[*i])).collect::<String>()));
    }
    lines.push("}".into());
    lines.push("}".into());
    let file = if dump.file.ends_with(".dot") { dump.file.clone() } else { format!("{}.dot", dump.file) };
    host.write_file(&file, (lines.join("\n") + "\n").as_bytes())
}

/// Emulates `java ... tla2sany.xml.XMLExporter [-o] [-I dir] SPEC`: a minimal XML description of the
/// root module (variables, definitions and their levels), enough for tools that only need the symbol table.
pub fn run_xml_exporter(argv: &[String], host: HostRef, library_paths: &[String], quiet: bool) -> i32 {
    let mut spec: Option<String> = None;
    let mut libs: Vec<String> = vec![];
    let mut i = 0;
    while i < argv.len() {
        if argv[i] == "-I" {
            i += 1;
            if let Some(d) = argv.get(i) {
                libs.push(d.clone());
            }
        } else if !argv[i].starts_with('-') {
            spec = Some(argv[i].clone());
        }
        i += 1;
    }
    let out = |s: &str| {
        if !quiet {
            host.print(s);
        }
    };
    let spec = match spec {
        Some(s) => s,
        None => {
            out("Usage: XMLExporter [-o] [-I dir] SPEC\n");
            return 1;
        }
    };
    let spec_path = if spec.ends_with(".tla") { spec.clone() } else { format!("{}.tla", spec) };
    let dir = dirname(&path_resolve(&host.cwd(), &spec_path));
    let root_name = basename(&spec_path, ".tla").to_string();
    let mut dirs = vec![dir];
    dirs.extend(libs);
    dirs.extend(library_paths.iter().cloned());
    let resolve = file_resolver(host.clone(), dirs, Rc::new(RefCell::new(vec![])));
    let mut loader = Loader::new(resolve, build_stdlib());
    loader.globals = global_defs();
    match loader.load(name(&root_name), None) {
        Ok(root) => {
            let esc = |t: &str| t.replace('&', "&amp;").replace('<', "&lt;").replace('>', "&gt;");
            let mut uid = 1;
            let mut entries = String::new();
            let mut refs = String::new();
            for v in &root.vars {
                uid += 1;
                refs += &format!("<OpDeclNodeRef><UID>{}</UID></OpDeclNodeRef>", uid);
                entries += &format!("<entry><UID>{}</UID><OpDeclNode><uniquename>{}</uniquename><level>1</level><arity>0</arity><kind>3</kind></OpDeclNode></entry>", uid, esc(&v.name.to_string()));
            }
            for c in &root.consts {
                uid += 1;
                refs += &format!("<OpDeclNodeRef><UID>{}</UID></OpDeclNodeRef>", uid);
                entries += &format!("<entry><UID>{}</UID><OpDeclNode><uniquename>{}</uniquename><level>0</level><arity>{}</arity><kind>2</kind></OpDeclNode></entry>", uid, esc(&c.name.to_string()), c.arity);
            }
            for (nm, sym) in &root.syms.items {
                if let Sym::Def(d) = sym {
                    if d.builtin.get().is_some() {
                        continue;
                    }
                    uid += 1;
                    refs += &format!("<UserDefinedOpKindRef><UID>{}</UID></UserDefinedOpKindRef>", uid);
                    entries += &format!(
                        "<entry><UID>{}</UID><UserDefinedOpKind><uniquename>{}</uniquename><level>{}</level><arity>{}</arity></UserDefinedOpKind></entry>",
                        uid,
                        esc(&nm.to_string()),
                        def_level(d),
                        d.params.len()
                    );
                }
            }
            out(&format!(
                "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<modules><RootModule>{}</RootModule><context><entry><UID>1</UID><ModuleNode><uniquename>{}</uniquename>{}</ModuleNode></entry>{}</context></modules>\n",
                esc(&root_name),
                esc(&root_name),
                refs,
                entries
            ));
            0
        }
        Err(e) => {
            let msg = match &*e {
                Fail::Tla(t) => t.msg.clone(),
                _ => "error".to_string(),
            };
            out(&format!("{}\n*** Errors: 1\n", msg));
            1
        }
    }
}

/// Emulates the `java` command line of the TLA+ tools, so that scripts which shell out to
/// `java -cp tla2tools.jar tlc2.TLC ...` can run on everystate unchanged.
pub fn run_java_shim(argv: &[String], host: HostRef) -> i32 {
    let mut libs: Vec<String> = vec![];
    let mut i = 0;
    while i < argv.len() {
        let a = &argv[i];
        if let Some(l) = a.strip_prefix("-DTLA-Library=") {
            libs.extend(l.split([':', ';']).filter(|x| !x.is_empty()).map(|x| x.to_string()));
        } else if a == "-Dtlc2.tool.impl.Tool.cdot=true" {
            crate::eval::CDOT.store(true, std::sync::atomic::Ordering::Relaxed);
        } else if a == "-cp" || a == "-classpath" || a == "-jar" {
            i += 1;
        } else if !a.starts_with('-') {
            break;
        }
        i += 1;
    }
    let main = argv.get(i).map(|s| s.as_str());
    let rest: &[String] = if i + 1 <= argv.len() { &argv[(i + 1).min(argv.len())..] } else { &[] };
    match main {
        Some("tlc2.TLC") => run_cli(rest, host, &libs),
        Some("tla2sany.xml.XMLExporter") => run_xml_exporter(rest, host, &libs, false),
        Some("tla2sany.SANY") => run_xml_exporter(rest, host, &libs, true),
        Some("pcal.trans") => crate::pcal::trans::run(rest, host),
        _ => {
            host.print(&format!("everystate java shim: unsupported main class {}\n", main.unwrap_or("(none)")));
            1
        }
    }
}
