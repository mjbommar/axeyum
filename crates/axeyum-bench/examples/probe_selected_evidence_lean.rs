//! Probe whether already-selected evidence reconstructs directly.
//!
//! The ordinary dominance audit calls the query-only Lean facade, which
//! re-runs certificate search. This bounded diagnostic instead consumes the
//! certificate already carried by `Evidence`, separating missing Lean support
//! from re-derivation/dispatch drift. It covers the measured quantified-BV
//! certificate families and generic Alethe proofs through existing EUF/UFBV/BV
//! consumers; it does not change production dispatch.

use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::time::Duration;

use axeyum_cnf::AletheCommand;
use axeyum_smtlib::parse_script;
use axeyum_solver::{
    Evidence, ReconstructCtx, SolverConfig, produce_evidence,
    reconstruct_bv_alternation_counterexample_to_lean_module,
    reconstruct_bv_closed_universal_counterexample_to_lean_module,
    reconstruct_bv_conjunctive_universal_instance_to_lean_module,
    reconstruct_bv_paired_existential_transfer_to_lean_module, reconstruct_qf_bv_proof,
    reconstruct_qf_uf_proof, reconstruct_qf_ufbv_proof,
};
use serde_json::json;

fn selected_alethe_shape(evidence: &Evidence) -> (Option<usize>, BTreeMap<String, usize>) {
    let (Evidence::UnsatAletheProof(proof) | Evidence::UnsatArithAletheProof(proof)) = evidence
    else {
        return (None, BTreeMap::new());
    };
    let mut rules = BTreeMap::new();
    for command in proof {
        if let AletheCommand::Step { rule, .. } = command {
            *rules.entry(rule.clone()).or_default() += 1;
        }
    }
    (Some(proof.len()), rules)
}

fn reconstruct_selected_alethe(proof: &[AletheCommand]) -> Result<(&'static str, String), String> {
    let mut declines = Vec::new();
    macro_rules! attempt {
        ($route:literal, $reconstruct:path) => {{
            let mut ctx = ReconstructCtx::new();
            match $reconstruct(&mut ctx, proof) {
                Ok(term) => {
                    let inferred = ctx.kernel_mut().infer(term).map_err(|error| {
                        format!(
                            "selected Alethe route `{}` failed kernel inference: {error:?}",
                            $route
                        )
                    })?;
                    let false_ = {
                        let name = ctx.prelude().false_;
                        ctx.kernel_mut().const_(name, vec![])
                    };
                    if !ctx.kernel_mut().def_eq(inferred, false_) {
                        return Err(format!(
                            "selected Alethe route `{}` did not infer to False",
                            $route
                        ));
                    }
                    let module = ctx
                        .kernel()
                        .render_lean_module("axeyum_refutation", false_, term);
                    return Ok(($route, module));
                }
                Err(error) => declines.push(format!("{}: {error}", $route)),
            }
        }};
    }

    attempt!("selected-alethe-euf", reconstruct_qf_uf_proof);
    attempt!("selected-alethe-ufbv", reconstruct_qf_ufbv_proof);
    attempt!("selected-alethe-bv", reconstruct_qf_bv_proof);
    Err(declines.join("; "))
}

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
        Evidence::UnsatAletheProof(proof) | Evidence::UnsatArithAletheProof(proof) => {
            reconstruct_selected_alethe(proof)
        }
        _ => Err(format!(
            "selected evidence kind `{}` is outside this selected-evidence probe",
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
        let (selected_proof_commands, selected_proof_rules) =
            selected_alethe_shape(&report.evidence);
        match reconstruct_selected(&script, &report.evidence) {
            Ok((route, module)) => println!(
                "{}",
                json!({
                    "file": path,
                    "selected_evidence": selected_kind,
                    "selected_proof_commands": selected_proof_commands,
                    "selected_proof_rules": selected_proof_rules,
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
                    "selected_proof_commands": selected_proof_commands,
                    "selected_proof_rules": selected_proof_rules,
                    "result": "declined",
                    "error": error,
                })
            ),
        }
    }
    Ok(())
}
