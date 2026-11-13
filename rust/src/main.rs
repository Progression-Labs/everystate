//! verify-rs: a Rust port of the safety-checking core of verify.js (a TLC-compatible TLA+ model checker).
mod ast;
mod bundled;
mod cfg;
mod checker;
mod eval;
mod intern;
mod lexer;
mod model;
mod modules;
mod parser;
mod stdlib;
mod value;

use intern::*;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;
use std::path::{Path, PathBuf};

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

fn exit_code(status: &str) -> i32 {
    match status {
        "ok" => 0,
        "assumption" => 10,
        "deadlock" => 11,
        "invariant" | "invariant-init" => 12,
        "action-property" | "implied-init" => 13,
        "incomplete" => 75,
        _ => 255,
    }
}

const USAGE: &str = "verify-rs - a TLA+ model checker (Rust port of the verify.js safety checker)\n\nUsage: verify-rs [-json] [-config FILE] [-deadlock] SPEC[.tla]\n\n  -config FILE   configuration file (default: SPEC.cfg)\n  -deadlock      do not check for deadlock\n  -json          print a single JSON result object\n";

fn run(argv: Vec<String>) -> i32 {
    let mut spec: Option<String> = None;
    let mut config: Option<String> = None;
    let mut deadlock = true;
    let mut json = false;
    let mut i = 0;
    while i < argv.len() {
        let a = &argv[i];
        match a.as_str() {
            "-config" => {
                i += 1;
                config = argv.get(i).cloned();
            }
            "-deadlock" => deadlock = false,
            "-json" => json = true,
            "-h" | "-help" | "--help" => {
                print!("{}", USAGE);
                return 0;
            }
            "-workers" | "-fp" | "-metadir" | "-seed" | "-depth" | "-fpmem" | "-coverage" | "-lncheck" => i += 1,
            _ if a.starts_with('-') => {}
            _ => {
                if let Some(s) = &spec {
                    println!("Error: more than one input files: {} and {}", s, a);
                    return 1;
                }
                spec = Some(a.clone());
            }
        }
        i += 1;
    }
    let spec = match spec {
        Some(s) => s,
        None => {
            print!("Error: Missing input TLA+ module.\n{}", USAGE);
            return 1;
        }
    };
    let spec_path = if spec.ends_with(".tla") { spec.clone() } else { format!("{}.tla", spec) };
    let abs = std::fs::canonicalize(&spec_path).unwrap_or_else(|_| std::env::current_dir().unwrap_or_default().join(&spec_path));
    let dir: PathBuf = abs.parent().map(|p| p.to_path_buf()).unwrap_or_default();
    let root_name = Path::new(&spec_path).file_name().and_then(|f| f.to_str()).unwrap_or("").trim_end_matches(".tla").to_string();
    let mut cfg_path = config.clone().unwrap_or_else(|| format!("{}.cfg", root_name));
    if !cfg_path.ends_with(".cfg") && !Path::new(&cfg_path).exists() && !dir.join(&cfg_path).exists() {
        cfg_path.push_str(".cfg");
    }
    if !Path::new(&cfg_path).exists() || config.is_none() {
        let in_dir = dir.join(&cfg_path);
        if in_dir.exists() {
            cfg_path = in_dir.to_string_lossy().to_string();
        }
    }
    let t0 = std::time::Instant::now();
    let dir2 = dir.clone();
    let resolve: modules::SourceResolver = Box::new(move |name: &str| {
        let p = dir2.join(format!("{}.tla", name));
        if p.exists() {
            if let Ok(bytes) = std::fs::read(&p) {
                return Some(String::from_utf8_lossy(&bytes).into_owned());
            }
        }
        bundled::BUNDLED.iter().find(|(n, _)| *n == name).map(|(_, s)| s.to_string())
    });
    let setup = (|| -> R<model::Model> {
        if !Path::new(&cfg_path).exists() {
            return err("config", format!("TLC encountered the following error reading the configuration file {}:\nFile not found.", cfg_path));
        }
        let text = String::from_utf8_lossy(&std::fs::read(&cfg_path).unwrap_or_default()).into_owned();
        let cfg = cfg::parse_config(&text)?;
        model::build_model(&root_name, resolve, &cfg)
    })();
    let model = match setup {
        Ok(m) => m,
        Err(e) => {
            let (kind, msg) = match *e {
                Fail::Tla(t) => (t.kind, t.msg),
                Fail::Check { message, .. } => ("error", message),
                Fail::Found => ("error", "internal error".to_string()),
            };
            if json {
                let mut o = String::from("{\"status\":\"setup-error\",\"kind\":");
                json_str(kind, &mut o);
                o.push_str(",\"message\":");
                json_str(&msg, &mut o);
                o.push('}');
                println!("{}", o);
            } else {
                println!("Error: {}", msg);
            }
            return if kind == "config" { 151 } else { 150 };
        }
    };
    if !model.live_props.is_empty() {
        let names: Vec<String> = model.live_props.iter().map(|p| p.name.clone()).collect();
        if json {
            let mut o = String::from("{\"status\":\"unsupported-liveness\",\"name\":");
            json_str(&names.join(", "), &mut o);
            o.push_str(",\"message\":\"liveness checking is not supported by verify-rs\"}");
            println!("{}", o);
        } else {
            println!("Error: liveness checking is not supported by verify-rs (temporal properties: {}).", names.join(", "));
        }
        return 2;
    }
    let res = checker::model_check(&model, deadlock && model.check_deadlock);
    if json {
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
                    json_str(&value::fmt(&t.state.get(j)), &mut o);
                }
                o.push_str("}}");
            }
            o.push(']');
        }
        o.push('}');
        println!("{}", o);
        return exit_code(res.status);
    }
    // human-readable summary
    match res.status {
        "ok" => println!("Model checking completed. No error has been found."),
        "invariant" => println!("Error: Invariant {} is violated.", res.name.as_deref().unwrap_or("?")),
        "invariant-init" => println!("Error: Invariant {} is violated by the initial state.", res.name.as_deref().unwrap_or("?")),
        "implied-init" => println!("Error: Property {} is violated by the initial state.", res.name.as_deref().unwrap_or("?")),
        "action-property" => println!("Error: Action property {} is violated.", res.name.as_deref().unwrap_or("?")),
        "deadlock" => println!("Error: Deadlock reached."),
        _ => println!("Error: {}", res.message.as_deref().unwrap_or(res.status)),
    }
    if let Some(tr) = &res.trace {
        if !tr.is_empty() {
            println!("Error: The behavior up to this point is:");
        }
        for (i, t) in tr.iter().enumerate() {
            let label = match t.action {
                Some(a) if i > 0 => {
                    let a = &model.actions[a];
                    format!("<{}{} line {}, col {} to line {}, col {} of module {}>", a.name, a.params, a.loc[0], a.loc[1], a.loc[2], a.loc[3], a.module)
                }
                _ => "<Initial predicate>".to_string(),
            };
            println!("State {}: {}", i + 1, label);
            for (j, v) in model.vars.iter().enumerate() {
                if model.vars.len() == 1 {
                    println!("{} = {}", v.name, value::fmt(&t.state.get(j)));
                } else {
                    println!("/\\ {} = {}", v.name, value::fmt(&t.state.get(j)));
                }
            }
            println!();
        }
    }
    println!("{} states generated, {} distinct states found, {} states left on queue.", res.generated, res.distinct, res.queue);
    println!("The depth of the complete state graph search is {}.", res.depth);
    println!("Finished in {:.3}s.", t0.elapsed().as_secs_f64());
    exit_code(res.status)
}

fn main() {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    // Evaluating deeply recursive TLA+ definitions needs far more stack than the main thread has.
    const STACK: usize = 1 << 30;
    let child = std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            eval::set_stack_limit(STACK - (64 << 20));
            let code = run(argv);
            use std::io::Write;
            let _ = std::io::stdout().flush();
            // skip destructors: the state store is torn down by the OS
            std::process::exit(code);
        })
        .expect("failed to start the worker thread");
    let _ = child.join();
}
