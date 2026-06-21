//! WebAssembly binding: run the Axeyum SMT-LIB solver in the browser.
//!
//! This is the engine behind the [playground](../../docs/playground/README.md).
//! It exposes a tiny, JSON-returning surface over [`axeyum_solver::solve_smtlib`]
//! so a static page can solve a query *client-side* — no server, no install. The
//! returned `sat` has already been replay-verified by the solver, exactly as in
//! native use: the trust boundary is preserved across the WASM boundary.

use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};
use wasm_bindgen::prelude::*;

/// The crate version, for the playground footer / cache-busting.
#[wasm_bindgen]
#[must_use]
pub fn version() -> String {
    env!("CARGO_PKG_VERSION").to_owned()
}

/// Solves an SMT-LIB script and returns a small JSON object as a string:
/// `{"status": "sat"|"unsat"|"unknown"|"error", "logic": ?, "expected": ?,
/// "detail": "..."}`. `status` is the decision for the conjunction of the
/// script's assertions; `expected` echoes any `(set-info :status ...)` for
/// cross-checking but is never consulted when solving.
#[wasm_bindgen]
#[must_use]
pub fn solve_smtlib_json(input: &str, timeout_ms: u32) -> String {
    let config = SolverConfig::new().with_timeout(Duration::from_millis(u64::from(timeout_ms)));
    match solve_smtlib(input, &config) {
        Ok(outcome) => {
            let (status, detail) = match &outcome.result {
                CheckResult::Sat(_) => ("sat", String::new()),
                CheckResult::Unsat => ("unsat", String::new()),
                CheckResult::Unknown(reason) => ("unknown", format!("{reason:?}")),
            };
            format!(
                "{{\"status\":\"{status}\",\"logic\":{},\"expected\":{},\"detail\":{}}}",
                json_opt(outcome.logic.as_deref()),
                json_opt(outcome.expected_status.as_deref()),
                json_str(&detail),
            )
        }
        Err(error) => format!(
            "{{\"status\":\"error\",\"logic\":null,\"expected\":null,\"detail\":{}}}",
            json_str(&format!("{error:?}")),
        ),
    }
}

fn json_opt(value: Option<&str>) -> String {
    value.map_or_else(|| "null".to_owned(), json_str)
}

/// Minimal JSON string escaping (quotes, backslash, control chars).
fn json_str(value: &str) -> String {
    let mut out = String::with_capacity(value.len() + 2);
    out.push('"');
    for c in value.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}
