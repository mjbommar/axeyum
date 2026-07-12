//! ADR-0102: genuine Lean reconstruction of ADR-0100 counterexamples.

use axeyum_ir::Value;
use axeyum_smtlib::parse_script;
use axeyum_solver::{
    Evidence, ProofFragment, SolverConfig, produce_evidence, prove_unsat_to_lean_module,
    reconstruct_closed_universal_counterexample_to_lean_module,
};

fn assert_real_lean_accepts(tag: &str, source: &str) {
    let Some(path) = std::env::var_os("PATH") else {
        return;
    };
    let Some(lean) = std::env::split_paths(&path)
        .map(|directory| directory.join("lean"))
        .find(|candidate| candidate.is_file())
    else {
        eprintln!("[skip] {tag}: lean binary not found");
        return;
    };
    let directory = std::env::temp_dir().join(format!("axeyum_{tag}_{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("create Lean cross-check directory");
    let file = directory.join(format!("{tag}.lean"));
    std::fs::write(&file, source).expect("write Lean cross-check module");
    let output = std::process::Command::new(lean)
        .arg(&file)
        .output()
        .expect("run Lean cross-check");
    assert!(
        output.status.success(),
        "Lean rejected {tag}:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(!String::from_utf8_lossy(&output.stdout).contains("sorryAx"));
}

const ARI176E1: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../corpus/public-curated/quantified/LIA/cvc5-regress-clean/",
    "cli__regress0__quantifiers__ARI176e1.smt2"
));

const ISSUE5279: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../corpus/public-curated/quantified/LIA/cvc5-regress-clean/",
    "cli__regress1__quantifiers__issue5279-nqe.smt2"
));

fn checked_certificate(
    text: &str,
) -> (
    axeyum_smtlib::Script,
    axeyum_solver::ClosedUniversalCounterexampleCertificate,
) {
    let mut script = parse_script(text).expect("target parses");
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &SolverConfig::default())
        .expect("target has evidence");
    let Evidence::UnsatClosedUniversalCounterexample(certificate) = report.evidence else {
        panic!(
            "expected ADR-0100 evidence, got {}",
            report.evidence.kind_label()
        );
    };
    assert!(
        Evidence::UnsatClosedUniversalCounterexample(certificate.clone())
            .check(&script.arena, &assertions)
            .expect("certificate check runs")
    );
    (script, certificate)
}

#[test]
fn ari176e1_reconstructs_by_forall_elimination_and_ring_normalization() {
    let (mut script, certificate) = checked_certificate(ARI176E1);
    let assertions = script.assertions.clone();
    let source = reconstruct_closed_universal_counterexample_to_lean_module(
        &script.arena,
        &assertions,
        &certificate,
    )
    .expect("checked counterexample reconstructs");
    assert!(source.contains("theorem axeyum_refutation : False"));
    assert_real_lean_accepts("quant_closed_cex_ari176e1", &source);

    let (fragment, routed_source) =
        prove_unsat_to_lean_module(&mut script.arena, &assertions).expect("router reconstructs");
    assert_eq!(fragment, ProofFragment::ClosedUniversalCounterexample);
    assert!(routed_source.contains("theorem axeyum_refutation : False"));
}

#[test]
fn issue5279_reconstructs_bool_ite_at_false_witness() {
    let (mut script, certificate) = checked_certificate(ISSUE5279);
    let assertions = script.assertions.clone();
    let source = reconstruct_closed_universal_counterexample_to_lean_module(
        &script.arena,
        &assertions,
        &certificate,
    )
    .expect("Bool-controlled counterexample reconstructs");
    assert!(source.contains("Bool.rec"));
    assert_real_lean_accepts("quant_closed_cex_issue5279", &source);

    let (fragment, _) =
        prove_unsat_to_lean_module(&mut script.arena, &assertions).expect("router reconstructs");
    assert_eq!(fragment, ProofFragment::ClosedUniversalCounterexample);
}

#[test]
fn tampered_counterexample_is_rejected_before_reconstruction() {
    let (script, mut certificate) = checked_certificate(ARI176E1);
    let assertions = script.assertions.clone();
    certificate.bindings[0].1 = Value::Int(0);
    assert!(
        reconstruct_closed_universal_counterexample_to_lean_module(
            &script.arena,
            &assertions,
            &certificate,
        )
        .is_err()
    );
}
