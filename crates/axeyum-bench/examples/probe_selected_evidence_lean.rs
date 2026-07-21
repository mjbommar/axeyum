//! Probe whether already-selected quantified-BV evidence reconstructs directly.
//!
//! The ordinary dominance audit calls the query-only Lean facade, which
//! re-runs certificate search. This bounded diagnostic instead consumes the
//! certificate already carried by `Evidence`, separating missing Lean support
//! from re-derivation/dispatch drift.

use std::env;
use std::fs;
use std::time::Duration;

use axeyum_smtlib::parse_script;
use axeyum_solver::{
    Evidence, SolverConfig, produce_evidence,
    reconstruct_bv_alternation_counterexample_to_lean_module,
    reconstruct_bv_closed_universal_counterexample_to_lean_module,
    reconstruct_bv_conjunctive_universal_instance_to_lean_module,
    reconstruct_bv_paired_existential_transfer_to_lean_module,
};
use serde_json::json;

fn reconstruct_selected(
    script: &axeyum_smtlib::Script,
    evidence: &Evidence,
) -> Result<(&'static str, String), String> {
    let assertions = &script.assertions;
    match evidence {
        Evidence::UnsatClosedUniversalCounterexample(certificate) => {
            reconstruct_bv_closed_universal_counterexample_to_lean_module(
                &script.arena,
                assertions,
                certificate,
            )
            .map(|module| ("closed-universal-counterexample", module))
            .map_err(|error| error.to_string())
        }
        Evidence::UnsatBvAlternationCounterexample(certificate) => {
            reconstruct_bv_alternation_counterexample_to_lean_module(
                &script.arena,
                assertions,
                certificate,
            )
            .map(|module| ("bv-alternation-counterexample", module))
            .map_err(|error| error.to_string())
        }
        Evidence::UnsatBvConjunctiveUniversalInstance(certificate) => {
            reconstruct_bv_conjunctive_universal_instance_to_lean_module(
                &script.arena,
                assertions,
                certificate,
            )
            .map(|module| ("bv-conjunctive-universal-instance", module))
            .map_err(|error| error.to_string())
        }
        Evidence::UnsatBvPairedExistentialTransfer(certificate) => {
            reconstruct_bv_paired_existential_transfer_to_lean_module(
                &script.arena,
                assertions,
                certificate,
            )
            .map(|module| ("bv-paired-existential-transfer", module))
            .map_err(|error| error.to_string())
        }
        _ => Err(format!(
            "selected evidence kind `{}` is outside this quantified-BV probe",
            evidence.kind_label()
        )),
    }
}

fn main() -> Result<(), String> {
    let paths: Vec<String> = env::args().skip(1).collect();
    if paths.is_empty() {
        return Err("usage: probe_selected_evidence_lean <file.smt2>...".to_owned());
    }
    let config = SolverConfig::default()
        .with_timeout(Duration::from_secs(10))
        .with_resource_limit(100_000);
    for path in paths {
        let text = fs::read_to_string(&path).map_err(|error| format!("{path}: {error}"))?;
        let mut script = parse_script(&text).map_err(|error| format!("{path}: {error}"))?;
        let assertions = script.assertions.clone();
        let report = produce_evidence(&mut script.arena, &assertions, &config)
            .map_err(|error| format!("{path}: {error}"))?;
        let selected_kind = report.evidence.kind_label();
        match reconstruct_selected(&script, &report.evidence) {
            Ok((route, module)) => println!(
                "{}",
                json!({
                    "file": path,
                    "selected_evidence": selected_kind,
                    "selected_reconstruction": route,
                    "lean_module_bytes": module.len(),
                    "lean_theorem_present": module.contains("theorem axeyum_refutation"),
                    "result": "reconstructed",
                })
            ),
            Err(error) => println!(
                "{}",
                json!({
                    "file": path,
                    "selected_evidence": selected_kind,
                    "result": "declined",
                    "error": error,
                })
            ),
        }
    }
    Ok(())
}
