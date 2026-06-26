//! Single-file probe for the online EUF + LIA combination route.
//!
//! Usage:
//! ```text
//! cargo run -p axeyum-bench --example uflia_online_probe -- <file.smt2> [timeout_ms]
//! ```

use std::path::PathBuf;
use std::time::{Duration, Instant};

use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, check_qf_uflia_online};

fn verdict(result: &CheckResult) -> &'static str {
    match result {
        CheckResult::Sat(_) => "sat",
        CheckResult::Unsat => "unsat",
        CheckResult::Unknown(_) => "unknown",
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let file = args.get(1).map_or_else(
        || {
            eprintln!("usage: uflia_online_probe <file.smt2> [timeout_ms]");
            std::process::exit(2);
        },
        PathBuf::from,
    );
    let timeout_ms = args
        .get(2)
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(10_000);

    let text = std::fs::read_to_string(&file).expect("read SMT-LIB file");
    let mut script = parse_script(&text).expect("parse SMT-LIB file");
    let assertions = script.assertions.clone();
    let config = SolverConfig::default().with_timeout(Duration::from_millis(timeout_ms));

    println!("file: {}", file.display());
    println!("timeout_ms: {timeout_ms}");
    println!("assertions: {}", assertions.len());

    let start = Instant::now();
    match check_qf_uflia_online(&mut script.arena, &assertions, &config) {
        Ok(result) => {
            println!(
                "uflia-online: {} {:.3}ms",
                verdict(&result),
                start.elapsed().as_secs_f64() * 1000.0
            );
            if let CheckResult::Unknown(reason) = result {
                println!("  unknown_kind: {:?}", reason.kind);
                println!("  detail: {}", reason.detail);
            }
        }
        Err(error) => {
            println!(
                "uflia-online: error {error} {:.3}ms",
                start.elapsed().as_secs_f64() * 1000.0
            );
        }
    }
}
