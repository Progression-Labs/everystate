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
