//! What withholds `Float-no-simp3-main`'s certificate is the BUDGET, not the route.
//!
//! Measured 2026-08-21. The `QF_BVFP` dominance row for
//! `solver__fp__Float-no-simp3-main.smt2` regressed from
//! `bv-defined-enum-unsat` (certified, checked, Lean-reconstructed) to a bare
//! `unsat` carrying nothing to re-check. Two independent causes stack:
//!
//! 1. `bv_defined_enum_refutation` declines every FP-arithmetic row while the
//!    `Fpa2Bv` reduction is uncertified — deliberate since `887b52e64`
//!    (2026-07-22) and pinned by `bv_defined_enum`'s own
//!    `declines_qf_fp_misc_without_certified_fpa2bv`. That is a soundness
//!    retreat, not a defect, and this suite does not second-guess it.
//! 2. What it falls back to is a bare `unsat` ONLY because `produce_evidence`
//!    skips `reduction_unsat_certificate` outright whenever `config.timeout`
//!    is set. A prior triage note recorded this instance's evidence as
//!    "exceeds 120 s"; measured here it is ~30 ms.
//!
//! So this pins the pair as a FALSIFIABLE claim: the reduction certificate
//! exists and is cheap, and a budget is the only thing withholding it. It fires
//! if the budget guard is loosened (the budgeted arm starts certifying) and it
//! fires if the certificate stops being producible at all (the unbudgeted arm
//! stops). Either is a change somebody must look at.
//!
//! The certificate does NOT restore dominance: it carries `Ackermann` and
//! `BitBlast` trust holes, so the row stays a non-candidate either way.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_smtlib::parse_script;
use axeyum_solver::{Evidence, SolverConfig, TrustId, produce_evidence};

const FLOAT_NO_SIMP3: &str = include_str!(
    "../../../corpus/public-curated/non-incremental/QF_BVFP/bitwuzla-regress-clean/solver__fp__Float-no-simp3-main.smt2"
);

#[test]
fn budgeted_evidence_is_a_bare_unsat() {
    let mut script = parse_script(FLOAT_NO_SIMP3).expect("Float-no-simp3-main parses");
    let assertions = script.assertions.clone();
    let config = SolverConfig::default().with_timeout(Duration::from_secs(10));
    let report =
        produce_evidence(&mut script.arena, &assertions, &config).expect("evidence is produced");
    assert!(
        matches!(report.evidence, Evidence::Unsat(None)),
        "a budgeted caller gets the timely bare `unsat`, got {:?}",
        report.evidence
    );
    assert!(
        !report.evidence.is_certified(),
        "a bare `unsat` carries nothing to check and must not read as certified"
    );
}

#[test]
fn unbudgeted_evidence_carries_the_reduction_certificate() {
    let mut script = parse_script(FLOAT_NO_SIMP3).expect("Float-no-simp3-main parses");
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &SolverConfig::default())
        .expect("evidence is produced");
    assert!(
        matches!(report.evidence, Evidence::Unsat(Some(_))),
        "the reduction certificate is producible for this row, got {:?}",
        report.evidence
    );
    assert!(
        report
            .evidence
            .check(&script.arena, &assertions)
            .expect("the certificate re-checks"),
        "the reduction certificate must re-derive the refutation"
    );
    let steps: Vec<TrustId> = report.trusted_steps.iter().map(|step| step.id).collect();
    assert!(
        steps.contains(&TrustId::Ackermann) && steps.contains(&TrustId::BitBlast),
        "the certificate is honest about the reductions it went through, got {steps:?}"
    );
    assert!(
        report.trusted_steps.iter().any(|step| !step.certified),
        "an uncertified reduction step keeps this row out of dominance"
    );
}
