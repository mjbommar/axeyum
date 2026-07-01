//! Rules-as-code example regressions.
//!
//! These tests keep human-cited rule packs tied to Axeyum's checked-evidence
//! path. The rule formalization and search are not trusted; accepted evidence
//! must independently re-check against the parsed SMT-LIB obligation.

use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CheckResult, Evidence, SolverConfig, check_auto, produce_evidence, prove_qf_uf_unsat_alethe,
};

const BENEFIT_ELIGIBILITY_CONSISTENCY: &str = include_str!(
    "../../../docs/rules-as-code/examples/benefit-eligibility-v0/smt2/consistency-bool-qf-lia-conflict.smt2"
);
const BENEFIT_ELIGIBILITY_COVERAGE: &str = include_str!(
    "../../../docs/rules-as-code/examples/benefit-eligibility-v0/smt2/coverage-bool-qf-lia-conflict.smt2"
);
const BENEFIT_ELIGIBILITY_MONOTONICITY: &str = include_str!(
    "../../../docs/rules-as-code/examples/benefit-eligibility-v0/smt2/monotonicity-bool-qf-lia-conflict.smt2"
);
const BENEFIT_ELIGIBILITY_IMPLEMENTATION_EQUIVALENCE: &str = include_str!(
    "../../../docs/rules-as-code/examples/benefit-eligibility-v0/smt2/implementation-equivalence-bool-qf-lia-conflict.smt2"
);
const AUTHORIZATION_POLICY_TENANT_ISOLATION: &str = include_str!(
    "../../../docs/rules-as-code/examples/authorization-policy-v0/smt2/tenant-isolation-bool-qf-lia-conflict.smt2"
);
const AUTHORIZATION_POLICY_EXPLICIT_DENY_PRECEDENCE: &str = include_str!(
    "../../../docs/rules-as-code/examples/authorization-policy-v0/smt2/explicit-deny-precedence-bool-qf-lia-conflict.smt2"
);
const AUTHORIZATION_POLICY_ADMIN_TENANT_GUARD: &str = include_str!(
    "../../../docs/rules-as-code/examples/authorization-policy-v0/smt2/admin-tenant-guard-bool-qf-lia-conflict.smt2"
);
const AUTHORIZATION_POLICY_IMPLEMENTATION_EQUIVALENCE: &str = include_str!(
    "../../../docs/rules-as-code/examples/authorization-policy-v0/smt2/implementation-equivalence-bool-qf-lia-conflict.smt2"
);
const TAX_BENEFIT_ARITHMETIC_NON_NEGATIVE: &str = include_str!(
    "../../../docs/rules-as-code/examples/tax-benefit-arithmetic-v0/smt2/non-negative-benefit-bool-qf-lia-conflict.smt2"
);
const TAX_BENEFIT_ARITHMETIC_CAP_RESPECTED: &str = include_str!(
    "../../../docs/rules-as-code/examples/tax-benefit-arithmetic-v0/smt2/cap-respected-bool-qf-lia-conflict.smt2"
);
const TAX_BENEFIT_ARITHMETIC_PHASEOUT_MONOTONICITY: &str = include_str!(
    "../../../docs/rules-as-code/examples/tax-benefit-arithmetic-v0/smt2/phaseout-monotonicity-bool-qf-lia-conflict.smt2"
);
const TAX_BENEFIT_ARITHMETIC_IMPLEMENTATION_EQUIVALENCE: &str = include_str!(
    "../../../docs/rules-as-code/examples/tax-benefit-arithmetic-v0/smt2/implementation-equivalence-bool-qf-lia-conflict.smt2"
);
const PROCUREMENT_SCORING_DEBARMENT_EXCLUSION: &str = include_str!(
    "../../../docs/rules-as-code/examples/procurement-scoring-v0/smt2/debarment-exclusion-bool-qf-lia-conflict.smt2"
);
const PROCUREMENT_SCORING_LATE_SUBMISSION_EXCLUSION: &str = include_str!(
    "../../../docs/rules-as-code/examples/procurement-scoring-v0/smt2/late-submission-exclusion-bool-qf-lia-conflict.smt2"
);
const PROCUREMENT_SCORING_BID_CAP_RESPECTED: &str = include_str!(
    "../../../docs/rules-as-code/examples/procurement-scoring-v0/smt2/bid-cap-respected-bool-qf-lia-conflict.smt2"
);
const PROCUREMENT_SCORING_SCORE_MONOTONICITY: &str = include_str!(
    "../../../docs/rules-as-code/examples/procurement-scoring-v0/smt2/score-monotonicity-bool-qf-lia-conflict.smt2"
);
const PROCUREMENT_SCORING_IMPLEMENTATION_EQUIVALENCE: &str = include_str!(
    "../../../docs/rules-as-code/examples/procurement-scoring-v0/smt2/implementation-equivalence-bool-qf-lia-conflict.smt2"
);
const GRANT_ALLOCATION_TOTAL_BUDGET: &str = include_str!(
    "../../../docs/rules-as-code/examples/grant-allocation-v0/smt2/total-budget-respected-farkas-conflict.smt2"
);
const GRANT_ALLOCATION_SHELTER_MINIMUM: &str = include_str!(
    "../../../docs/rules-as-code/examples/grant-allocation-v0/smt2/shelter-minimum-respected-farkas-conflict.smt2"
);
const GRANT_ALLOCATION_CLINIC_MINIMUM: &str = include_str!(
    "../../../docs/rules-as-code/examples/grant-allocation-v0/smt2/clinic-minimum-respected-farkas-conflict.smt2"
);
const GRANT_ALLOCATION_ADMIN_CAP: &str = include_str!(
    "../../../docs/rules-as-code/examples/grant-allocation-v0/smt2/admin-cap-respected-farkas-conflict.smt2"
);
const GRANT_ALLOCATION_IMPLEMENTATION_EQUIVALENCE: &str = include_str!(
    "../../../docs/rules-as-code/examples/grant-allocation-v0/smt2/implementation-equivalence-farkas-conflict.smt2"
);
const CATEGORY_EQUIVALENCE_SAME_PRIORITY: &str = include_str!(
    "../../../docs/rules-as-code/examples/category-equivalence-v0/smt2/equivalent-categories-same-priority-qf-uf-conflict.smt2"
);
const CATEGORY_EQUIVALENCE_IMPLEMENTATION_EQUIVALENCE: &str = include_str!(
    "../../../docs/rules-as-code/examples/category-equivalence-v0/smt2/implementation-equivalence-qf-uf-conflict.smt2"
);

#[test]
fn benefit_eligibility_consistency_emits_checked_evidence() {
    assert_rule_unsat_evidence(
        "benefit-eligibility-v0 consistency",
        BENEFIT_ELIGIBILITY_CONSISTENCY,
    );
}

#[test]
fn benefit_eligibility_coverage_emits_checked_evidence() {
    assert_rule_unsat_evidence(
        "benefit-eligibility-v0 coverage",
        BENEFIT_ELIGIBILITY_COVERAGE,
    );
}

#[test]
fn benefit_eligibility_monotonicity_emits_checked_evidence() {
    assert_rule_unsat_evidence(
        "benefit-eligibility-v0 monotonicity",
        BENEFIT_ELIGIBILITY_MONOTONICITY,
    );
}

#[test]
fn benefit_eligibility_implementation_equivalence_emits_checked_evidence() {
    assert_rule_unsat_evidence(
        "benefit-eligibility-v0 implementation equivalence",
        BENEFIT_ELIGIBILITY_IMPLEMENTATION_EQUIVALENCE,
    );
}

#[test]
fn authorization_policy_tenant_isolation_emits_checked_evidence() {
    assert_rule_unsat_evidence(
        "authorization-policy-v0 tenant isolation",
        AUTHORIZATION_POLICY_TENANT_ISOLATION,
    );
}

#[test]
fn authorization_policy_explicit_deny_precedence_emits_checked_evidence() {
    assert_rule_unsat_evidence(
        "authorization-policy-v0 explicit deny precedence",
        AUTHORIZATION_POLICY_EXPLICIT_DENY_PRECEDENCE,
    );
}

#[test]
fn authorization_policy_admin_tenant_guard_emits_checked_evidence() {
    assert_rule_unsat_evidence(
        "authorization-policy-v0 admin tenant guard",
        AUTHORIZATION_POLICY_ADMIN_TENANT_GUARD,
    );
}

#[test]
fn authorization_policy_implementation_equivalence_emits_checked_evidence() {
    assert_rule_unsat_evidence(
        "authorization-policy-v0 implementation equivalence",
        AUTHORIZATION_POLICY_IMPLEMENTATION_EQUIVALENCE,
    );
}

#[test]
fn tax_benefit_arithmetic_non_negative_benefit_emits_checked_evidence() {
    assert_rule_unsat_evidence(
        "tax-benefit-arithmetic-v0 non-negative benefit",
        TAX_BENEFIT_ARITHMETIC_NON_NEGATIVE,
    );
}

#[test]
fn tax_benefit_arithmetic_cap_respected_emits_checked_evidence() {
    assert_rule_unsat_evidence(
        "tax-benefit-arithmetic-v0 cap respected",
        TAX_BENEFIT_ARITHMETIC_CAP_RESPECTED,
    );
}

#[test]
fn tax_benefit_arithmetic_phaseout_monotonicity_emits_checked_evidence() {
    assert_rule_unsat_evidence(
        "tax-benefit-arithmetic-v0 phaseout monotonicity",
        TAX_BENEFIT_ARITHMETIC_PHASEOUT_MONOTONICITY,
    );
}

#[test]
fn tax_benefit_arithmetic_implementation_equivalence_emits_checked_evidence() {
    assert_rule_unsat_evidence(
        "tax-benefit-arithmetic-v0 implementation equivalence",
        TAX_BENEFIT_ARITHMETIC_IMPLEMENTATION_EQUIVALENCE,
    );
}

#[test]
fn procurement_scoring_debarment_exclusion_emits_checked_evidence() {
    assert_rule_unsat_evidence(
        "procurement-scoring-v0 debarment exclusion",
        PROCUREMENT_SCORING_DEBARMENT_EXCLUSION,
    );
}

#[test]
fn procurement_scoring_late_submission_exclusion_emits_checked_evidence() {
    assert_rule_unsat_evidence(
        "procurement-scoring-v0 late submission exclusion",
        PROCUREMENT_SCORING_LATE_SUBMISSION_EXCLUSION,
    );
}

#[test]
fn procurement_scoring_bid_cap_respected_emits_checked_evidence() {
    assert_rule_unsat_evidence(
        "procurement-scoring-v0 bid cap respected",
        PROCUREMENT_SCORING_BID_CAP_RESPECTED,
    );
}

#[test]
fn procurement_scoring_score_monotonicity_emits_checked_evidence() {
    assert_rule_unsat_evidence(
        "procurement-scoring-v0 score monotonicity",
        PROCUREMENT_SCORING_SCORE_MONOTONICITY,
    );
}

#[test]
fn procurement_scoring_implementation_equivalence_emits_checked_evidence() {
    assert_rule_unsat_evidence(
        "procurement-scoring-v0 implementation equivalence",
        PROCUREMENT_SCORING_IMPLEMENTATION_EQUIVALENCE,
    );
}

#[test]
fn grant_allocation_total_budget_respected_emits_checked_evidence() {
    assert_rule_unsat_evidence(
        "grant-allocation-v0 total budget respected",
        GRANT_ALLOCATION_TOTAL_BUDGET,
    );
}

#[test]
fn grant_allocation_shelter_minimum_respected_emits_checked_evidence() {
    assert_rule_unsat_evidence(
        "grant-allocation-v0 shelter minimum respected",
        GRANT_ALLOCATION_SHELTER_MINIMUM,
    );
}

#[test]
fn grant_allocation_clinic_minimum_respected_emits_checked_evidence() {
    assert_rule_unsat_evidence(
        "grant-allocation-v0 clinic minimum respected",
        GRANT_ALLOCATION_CLINIC_MINIMUM,
    );
}

#[test]
fn grant_allocation_admin_cap_respected_emits_checked_evidence() {
    assert_rule_unsat_evidence(
        "grant-allocation-v0 admin cap respected",
        GRANT_ALLOCATION_ADMIN_CAP,
    );
}

#[test]
fn grant_allocation_implementation_equivalence_emits_checked_evidence() {
    assert_rule_unsat_evidence(
        "grant-allocation-v0 implementation equivalence",
        GRANT_ALLOCATION_IMPLEMENTATION_EQUIVALENCE,
    );
}

#[test]
fn category_equivalence_same_priority_emits_checked_alethe() {
    assert_rule_qf_uf_alethe(
        "category-equivalence-v0 equivalent categories same priority",
        CATEGORY_EQUIVALENCE_SAME_PRIORITY,
    );
}

#[test]
fn category_equivalence_implementation_equivalence_emits_checked_alethe() {
    assert_rule_qf_uf_alethe(
        "category-equivalence-v0 implementation equivalence",
        CATEGORY_EQUIVALENCE_IMPLEMENTATION_EQUIVALENCE,
    );
}

fn assert_rule_unsat_evidence(label: &str, smt2: &str) {
    let mut script = parse_script(smt2)
        .unwrap_or_else(|error| panic!("{label}: rule SMT-LIB artifact parses: {error}"));
    let assertions = script.assertions.clone();

    assert_eq!(
        check_auto(&mut script.arena, &assertions, &SolverConfig::default()).unwrap(),
        CheckResult::Unsat,
        "{label}: rule obligation must be unsat"
    );

    let report = produce_evidence(&mut script.arena, &assertions, &SolverConfig::default())
        .unwrap_or_else(|error| panic!("{label}: evidence production failed: {error}"));
    assert!(
        report.evidence.is_certified(),
        "{label}: expected certified evidence, got {:?}",
        report.evidence
    );
    assert!(
        report.evidence.check(&script.arena, &assertions).unwrap(),
        "{label}: evidence must independently re-check"
    );
}

fn assert_rule_qf_uf_alethe(label: &str, smt2: &str) {
    let mut script = parse_script(smt2)
        .unwrap_or_else(|error| panic!("{label}: rule SMT-LIB artifact parses: {error}"));
    let assertions = script.assertions.clone();

    assert_eq!(
        check_auto(&mut script.arena, &assertions, &SolverConfig::default()).unwrap(),
        CheckResult::Unsat,
        "{label}: rule obligation must be unsat"
    );

    let proof = prove_qf_uf_unsat_alethe(&script.arena, &assertions)
        .unwrap_or_else(|| panic!("{label}: rule obligation emits a pure EUF Alethe proof"));
    let evidence = Evidence::UnsatAletheProof(proof);
    assert!(evidence.is_certified());
    assert!(
        evidence.check(&script.arena, &assertions).unwrap(),
        "{label}: Alethe certificate must independently re-check"
    );
}
