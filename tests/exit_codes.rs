//! Exit statuses the binary shares with TLC, run on the specs in `repro/`.
use std::process::Command;

fn status(spec: &str) -> (i32, String) {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/repro");
    let out = Command::new(env!("CARGO_BIN_EXE_everystate"))
        .arg(format!("{dir}/{spec}.tla"))
        .output()
        .expect("running everystate");
    (out.status.code().unwrap_or(-1), String::from_utf8_lossy(&out.stdout).into_owned())
}

/// TLC 2.19 exits 10 when an assumption fails to evaluate, as when it holds a false `Assert`:
/// the same status as a false assumption, not a generic error.
#[test]
fn an_assumption_that_fails_to_evaluate_exits_10() {
    for spec in ["AssumeAssert", "AssumeError"] {
        let (code, out) = status(spec);
        assert!(out.contains("Evaluating assumption"), "{spec}: {out}");
        assert_eq!(code, 10, "{spec}: {out}");
    }
}
