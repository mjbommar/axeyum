//! Rules-as-code example regressions.
//!
//! These tests keep human-cited rule packs tied to Axeyum's checked-evidence
//! path. The rule formalization and search are not trusted; accepted evidence
//! must independently re-check against the parsed SMT-LIB obligation.

use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, check_auto, produce_evidence};

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
