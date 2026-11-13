//! everystate command-line binary. `everystate ...` is the model checker; `everystate-java ...` (the
//! same binary under that name, or `everystate java ...`) stands in for `java -cp tla2tools.jar tlc2.TLC ...`.
use everystate::host::NativeHost;
use std::rc::Rc;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() {
    let mut argv: Vec<String> = std::env::args().collect();
    let exe = argv.remove(0);
    let exe_name = exe.rsplit('/').next().unwrap_or("").to_string();
    let java = exe_name.starts_with("everystate-java") || exe_name == "java" || argv.first().map(|a| a == "java").unwrap_or(false) && { argv.remove(0); true };
    if argv.first().map(|a| a == "--ppr").unwrap_or(false) {
        // test hook: pretty-print the value on stdin at the given width (default 80), as TLC's Values.ppr does
        use std::io::{Read, Write};
        let width: i64 = argv.get(1).and_then(|w| w.parse().ok()).unwrap_or(80);
        let mut input = String::new();
        let _ = std::io::stdin().read_to_string(&mut input);
        let _ = std::io::stdout().write_all(everystate::pprint::ppr_width(&input, width).as_bytes());
        return;
    }
    // Evaluating deeply recursive TLA+ definitions needs far more stack than the main thread has.
    const STACK: usize = 1 << 30;
    let child = std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            everystate::eval::set_stack_limit(STACK - (64 << 20));
            let host = Rc::new(NativeHost);
            let code = if java { everystate::cli::run_java_shim(&argv, host) } else { everystate::cli::run_cli(&argv, host, &[]) };
            use std::io::Write;
            let _ = std::io::stdout().flush();
            // skip destructors: the state store is torn down by the OS
            std::process::exit(code);
        })
        .expect("failed to start the worker thread");
    let _ = child.join();
}
