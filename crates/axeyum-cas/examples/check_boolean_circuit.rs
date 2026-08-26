//! Check a portable finite Boolean-circuit JSON artifact.

use std::fs;
use std::path::PathBuf;

use axeyum_cas::boolean_circuit::{
    BooleanCircuitArtifact, BooleanCircuitCheck, BooleanCircuitLimits, check_boolean_circuit,
};

fn fail(message: &str, code: i32) -> ! {
    eprintln!("BOOLEAN_CIRCUIT_CHECK|failed|{message}");
    std::process::exit(code);
}

fn main() {
    let mut arguments = std::env::args_os();
    let _program = arguments.next();
    let Some(raw_path) = arguments.next() else {
        fail("usage: check_boolean_circuit <artifact.json>", 2);
    };
    if arguments.next().is_some() {
        fail("usage: check_boolean_circuit <artifact.json>", 2);
    }
    let path = PathBuf::from(raw_path);
    let bytes = fs::read(path).unwrap_or_else(|error| fail(&format!("read: {error}"), 2));
    let artifact: BooleanCircuitArtifact =
        serde_json::from_slice(&bytes).unwrap_or_else(|error| fail(&format!("parse: {error}"), 2));
    match check_boolean_circuit(&artifact, BooleanCircuitLimits::default()) {
        Ok(BooleanCircuitCheck::Verified {
            rows_checked,
            gate_counts,
        }) => println!(
            "BOOLEAN_CIRCUIT_CHECK|verified|rows={rows_checked}|gates={}|counts={gate_counts:?}",
            artifact.gates.len()
        ),
        Ok(BooleanCircuitCheck::Failed {
            input,
            expected,
            observed,
        }) => fail(
            &format!("input={input}|expected={expected}|observed={observed}"),
            1,
        ),
        Err(error) => fail(&format!("malformed-or-declined={error:?}"), 2),
    }
}
