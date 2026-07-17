//! WebAssembly binding: run the Axeyum SMT-LIB solver in the browser.
//!
//! This is the engine behind the [playground](../../docs/playground/README.md).
//! It exposes a tiny, JSON-returning surface over the dependency-minimal QF_BV
//! backend so a static page can solve a query *client-side* — no server, no
//! install. The returned `sat` has already been replay-verified by the solver,
//! exactly as in native use: the trust boundary is preserved across the WASM
//! boundary.

use std::time::Duration;

use axeyum_smtlib::{ScriptCommand, parse_script};
use axeyum_solver::{CheckResult, SatBvBackend, SolverBackend, SolverConfig};
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
    match solve_qfbv_smtlib(input, &config) {
        Ok((result, logic, expected)) => {
            let (status, detail) = match &result {
                CheckResult::Sat(_) => ("sat", String::new()),
                CheckResult::Unsat => ("unsat", String::new()),
                CheckResult::Unknown(reason) => ("unknown", format!("{reason:?}")),
            };
            format!(
                "{{\"status\":\"{status}\",\"logic\":{},\"expected\":{},\"detail\":{}}}",
                json_opt(logic.as_deref()),
                json_opt(expected.as_deref()),
                json_str(&detail),
            )
        }
        Err(error) => format!(
            "{{\"status\":\"error\",\"logic\":null,\"expected\":null,\"detail\":{}}}",
            json_str(&format!("{error:?}")),
        ),
    }
}

fn solve_qfbv_smtlib(
    input: &str,
    config: &SolverConfig,
) -> Result<(CheckResult, Option<String>, Option<String>), String> {
    let script = parse_script(input).map_err(|error| error.to_string())?;
    if script
        .logic
        .as_deref()
        .is_some_and(|logic| logic != "QF_BV")
    {
        return Err("the minimal WebAssembly binding accepts only QF_BV logic".to_owned());
    }
    if script.check_sats > 1 {
        return Err(
            "the single-result WebAssembly binding accepts at most one check-sat".to_owned(),
        );
    }

    let mut assertions = Vec::new();
    let mut scopes = Vec::new();
    let mut queried_assertions = None;
    for command in &script.commands {
        match command {
            ScriptCommand::Assert(term) => assertions.push(*term),
            ScriptCommand::Push(count) => {
                for _ in 0..*count {
                    scopes.push(assertions.len());
                }
            }
            ScriptCommand::Pop(count) => {
                for _ in 0..*count {
                    if let Some(depth) = scopes.pop() {
                        assertions.truncate(depth);
                    }
                }
            }
            ScriptCommand::CheckSat => queried_assertions = Some(assertions.clone()),
            ScriptCommand::CheckSatAssuming(assumptions) => {
                let mut active = assertions.clone();
                active.extend(assumptions);
                queried_assertions = Some(active);
            }
            ScriptCommand::ResetAssertions => {
                assertions.clear();
                scopes.clear();
            }
            ScriptCommand::GetAssertions => {}
        }
    }

    let active = queried_assertions.unwrap_or(assertions);
    let mut backend = SatBvBackend::new();
    let result = backend
        .check(&script.arena, &active, config)
        .map_err(|error| error.to_string())?;
    Ok((result, script.logic, script.status))
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn minimal_binding_solves_qfbv_sat_and_unsat() {
        let sat = solve_smtlib_json(
            "(set-logic QF_BV) (set-info :status sat) \
             (declare-const x (_ BitVec 8)) (assert (= x #x2a)) (check-sat)",
            1_000,
        );
        assert!(sat.contains("\"status\":\"sat\""), "{sat}");
        assert!(sat.contains("\"logic\":\"QF_BV\""), "{sat}");
        assert!(sat.contains("\"expected\":\"sat\""), "{sat}");

        let unsat = solve_smtlib_json(
            "(set-logic QF_BV) (set-info :status unsat) \
             (declare-const x (_ BitVec 8)) \
             (assert (= x #x2a)) (assert (= x #x2b)) (check-sat)",
            1_000,
        );
        assert!(unsat.contains("\"status\":\"unsat\""), "{unsat}");
    }

    #[test]
    fn minimal_binding_rejects_non_qfbv_logic() {
        let result = solve_smtlib_json(
            "(set-logic QF_LIA) (declare-const x Int) (assert (> x 0)) (check-sat)",
            1_000,
        );
        assert!(result.contains("\"status\":\"error\""), "{result}");
        assert!(result.contains("QF_BV"), "{result}");
    }
}
