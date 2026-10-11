//! Replay an exported trace against a separately supplied equality statement.
use axeyum_cas::rewrite_trace::{PolynomialExpr, TraceLimits, replay_json};
use serde::Deserialize;
use std::{fs::File, io::Read, process::ExitCode};

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Statement {
    input: PolynomialExpr,
    result: PolynomialExpr,
}

fn bounded_file(path: &str, limit: usize) -> Result<Vec<u8>, String> {
    let mut bytes = Vec::new();
    File::open(path)
        .map_err(|e| e.to_string())?
        .take(u64::try_from(limit).map_err(|e| e.to_string())? + 1)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if bytes.len() > limit {
        return Err("file exceeds checker byte policy".to_owned());
    }
    Ok(bytes)
}
fn check() -> Result<(), String> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 {
        return Err("usage: cas_trace_check TRACE.json STATEMENT.json".to_owned());
    }
    let limits = TraceLimits::default();
    let statement: Statement = serde_json::from_slice(&bounded_file(&args[2], limits.bytes)?)
        .map_err(|e| e.to_string())?;
    let trace = replay_json(
        &bounded_file(&args[1], limits.bytes)?,
        &statement.input,
        &statement.result,
        limits,
    )
    .map_err(|e| format!("{e:?}"))?;
    println!("CHECKED|steps={}", trace.steps.len());
    Ok(())
}
fn main() -> ExitCode {
    match check() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("REJECTED|{error}");
            ExitCode::FAILURE
        }
    }
}
