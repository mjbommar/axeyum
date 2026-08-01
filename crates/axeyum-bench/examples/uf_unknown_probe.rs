//! Diagnostic probe: solve one SMT-LIB file and print the full verdict,
//! including the `UnknownReason` kind/detail that `smtcomp_cli` hides.
//!
//! ```sh
//! cargo run -q -p axeyum-bench --example uf_unknown_probe -- file.smt2 [timeout_ms]
//! ```

use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    let Some(path) = args.get(1) else {
        eprintln!("usage: uf_unknown_probe <file.smt2> [timeout_ms]");
        std::process::exit(2);
    };
    let timeout_ms = args.get(2).and_then(|s| s.parse::<u64>().ok());

    let input = std::fs::read_to_string(path).expect("read SMT-LIB file");
    let mut config = SolverConfig::new();
    if let Some(ms) = timeout_ms {
        config = config.with_timeout(Duration::from_millis(ms));
    }

    match solve_smtlib(&input, &config) {
        Ok(outcome) => match outcome.result {
            CheckResult::Sat(_) => println!("sat"),
            CheckResult::Unsat => println!("unsat"),
            CheckResult::Unknown(reason) => {
                println!("unknown kind={:?}", reason.kind);
                println!("detail: {}", reason.detail);
            }
        },
        Err(error) => println!("error: {error}"),
    }
}
