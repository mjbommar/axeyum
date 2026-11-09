//! Decide rules-as-code obligations and print the checked evidence for each.
//!
//! Usage: `cargo run -q -p axeyum-solver --features full --example rules_check -- FILE.smt2...`
//!
//! For every file this prints the verdict, the evidence kind, whether the
//! evidence independently re-checked against the parsed assertions, and, for a
//! `sat` result, the model restricted to declared constants that differ from
//! their zero value (false / 0), which is how a rule finding's witness reads.

use std::process::ExitCode;

use axeyum_ir::Value;
use axeyum_smtlib::parse_script;
use axeyum_solver::{Evidence, SolverConfig, produce_evidence};

fn main() -> ExitCode {
    let paths: Vec<String> = std::env::args().skip(1).collect();
    if paths.is_empty() {
        eprintln!("usage: rules_check FILE.smt2...");
        return ExitCode::from(2);
    }
    let mut failed = false;
    for path in paths {
        let text = match std::fs::read_to_string(&path) {
            Ok(text) => text,
            Err(error) => {
                eprintln!("{path}: {error}");
                failed = true;
                continue;
            }
        };
        let mut script = match parse_script(&text) {
            Ok(script) => script,
            Err(error) => {
                eprintln!("{path}: parse error: {error}");
                failed = true;
                continue;
            }
        };
        let assertions = script.assertions.clone();
        let report =
            match produce_evidence(&mut script.arena, &assertions, &SolverConfig::default()) {
                Ok(report) => report,
                Err(error) => {
                    eprintln!("{path}: solver error: {error}");
                    failed = true;
                    continue;
                }
            };
        let checked = report
            .evidence
            .check(&script.arena, &assertions)
            .unwrap_or(false);
        let verdict = match &report.evidence {
            Evidence::Sat(_) => "sat",
            Evidence::Unknown(_) => "unknown",
            _ => "unsat",
        };
        let name = std::path::Path::new(&path)
            .file_name()
            .map_or(path.clone(), |name| name.to_string_lossy().into_owned());
        println!(
            "{name}: {verdict}  evidence={}  certified={}  rechecked={checked}",
            report.evidence.kind_label(),
            report.evidence.is_certified(),
        );
        if let Evidence::Sat(model) = &report.evidence {
            let mut rows: Vec<(String, String)> = model
                .iter()
                .filter_map(|(symbol, value)| {
                    let (name, _) = script.arena.symbol(symbol);
                    if name.starts_with('!') || name.contains("__") {
                        return None;
                    }
                    let shown = match &value {
                        Value::Bool(false) => return None,
                        Value::Bool(true) => "true".to_owned(),
                        other => {
                            let text = other.to_string();
                            if text == "0" {
                                return None;
                            }
                            text
                        }
                    };
                    Some((name.to_owned(), shown))
                })
                .collect();
            rows.sort();
            for (name, value) in rows {
                println!("    {name} = {value}");
            }
        }
        if !checked {
            failed = true;
        }
    }
    if failed {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}
