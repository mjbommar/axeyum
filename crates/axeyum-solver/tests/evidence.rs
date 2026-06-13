//! Self-checking evidence envelopes: produce a result with its justification
//! and re-validate it independently (ADR-0005 follow-through).

use std::time::Duration;

use axeyum_ir::{Sort, TermArena};
use axeyum_solver::{
    Evidence, SolverConfig, produce_lra_dpll_evidence, produce_lra_evidence, produce_qf_bv_evidence,
};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(30))
}

#[test]
fn sat_evidence_carries_a_replayable_model() {
    // x + 1 == 5 over BV8 is satisfiable.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let five = arena.bv_const(8, 5).unwrap();
    let sum = arena.bv_add(x, one).unwrap();
    let eq = arena.eq(sum, five).unwrap();

    let report = produce_qf_bv_evidence(&arena, &[eq], &config()).unwrap();
    assert!(matches!(report.evidence, Evidence::Sat(_)));
    assert!(report.evidence.is_certified());
    // Provenance is recorded for reproducibility.
    assert_eq!(report.provenance.semantics_version, "1");
    assert_eq!(report.provenance.assertion_count, 1);
    // The evidence re-validates against the original query, independently.
    assert!(report.evidence.check(&arena, &[eq]).unwrap());
}

#[test]
fn unsat_evidence_carries_a_recheckable_drat_certificate() {
    // x & 1 == 1 AND x & 1 == 0 is unsatisfiable.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 4).unwrap();
    let one = arena.bv_const(4, 1).unwrap();
    let zero = arena.bv_const(4, 0).unwrap();
    let masked = arena.bv_and(x, one).unwrap();
    let is_one = arena.eq(masked, one).unwrap();
    let is_zero = arena.eq(masked, zero).unwrap();
    let assertions = [is_one, is_zero];

    let report = produce_qf_bv_evidence(&arena, &assertions, &config()).unwrap();
    let Evidence::Unsat(Some(_)) = &report.evidence else {
        panic!("expected a DRAT-certified unsat, got {:?}", report.evidence);
    };
    assert!(report.evidence.is_certified());
    assert!(report.provenance.backend.contains("rustsat-batsat"));
    // Re-running the trusted DRAT checker on the stored certificate confirms it.
    assert!(report.evidence.check(&arena, &assertions).unwrap());
}

#[test]
fn tampered_sat_evidence_fails_its_own_check() {
    // A model that does not satisfy the query must fail `check` (the replay
    // guard catches a bogus "sat" certificate).
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let five = arena.bv_const(8, 5).unwrap();
    let sum = arena.bv_add(x, one).unwrap();
    let eq = arena.eq(sum, five).unwrap();

    // Build a wrong model (x = 0, so x + 1 = 1 != 5) and wrap it as evidence.
    let mut model = axeyum_solver::Model::new();
    model.set(
        arena.find_symbol("x").unwrap(),
        axeyum_ir::Value::Bv { width: 8, value: 0 },
    );
    let bogus = Evidence::Sat(model);
    assert!(
        !bogus.check(&arena, &[eq]).unwrap(),
        "wrong model must not check"
    );
}

#[test]
fn lra_unsat_evidence_carries_a_recheckable_farkas_certificate() {
    // x < 0 && x > 0 is unsatisfiable over the reals.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.real_ratio(0, 1);
    let lt = arena.real_lt(x, zero).unwrap();
    let gt = arena.real_gt(x, zero).unwrap();
    let assertions = [lt, gt];

    let report = produce_lra_evidence(&arena, &assertions).unwrap();
    let Evidence::UnsatFarkas(_) = &report.evidence else {
        panic!(
            "expected a Farkas-certified unsat, got {:?}",
            report.evidence
        );
    };
    assert!(report.evidence.is_certified());
    assert_eq!(report.provenance.backend, "lra-fourier-motzkin-farkas");
    assert_eq!(report.provenance.assertion_count, 2);
    // Re-running the independent Farkas verifier confirms the refutation.
    assert!(report.evidence.check(&arena, &assertions).unwrap());
}

#[test]
fn lra_sat_evidence_replays() {
    // 3*x == 1 pins x = 1/3; the model replays through the evaluator.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let three = arena.real_ratio(3, 1);
    let one = arena.real_ratio(1, 1);
    let three_x = arena.real_mul(three, x).unwrap();
    let eq = arena.eq(three_x, one).unwrap();

    let report = produce_lra_evidence(&arena, &[eq]).unwrap();
    assert!(matches!(report.evidence, Evidence::Sat(_)));
    assert!(report.evidence.check(&arena, &[eq]).unwrap());
}

#[test]
fn tampered_farkas_evidence_fails_its_own_check() {
    // A Farkas certificate with a zeroed multiplier no longer cancels the
    // variable, so the independent verifier rejects it.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.real_ratio(0, 1);
    let lt = arena.real_lt(x, zero).unwrap();
    let gt = arena.real_gt(x, zero).unwrap();
    let assertions = [lt, gt];

    let report = produce_lra_evidence(&arena, &assertions).unwrap();
    let Evidence::UnsatFarkas(cert) = report.evidence else {
        panic!("expected a Farkas certificate");
    };
    let mut tampered = cert;
    tampered.multipliers[0] = axeyum_ir::Rational::zero();
    let bogus = Evidence::UnsatFarkas(tampered);
    assert!(
        !bogus.check(&arena, &assertions).unwrap(),
        "a tampered Farkas certificate must not check"
    );
}

#[test]
fn lra_dpll_unsat_evidence_carries_a_recheckable_refutation() {
    // (x < 0 ∨ x > 0) ∧ x >= 0 ∧ x <= 0 : Boolean-structured pure-real unsat.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.real_ratio(0, 1);
    let lt = arena.real_lt(x, zero).unwrap();
    let gt = arena.real_gt(x, zero).unwrap();
    let split = arena.or(lt, gt).unwrap();
    let ge = arena.real_ge(x, zero).unwrap();
    let le = arena.real_le(x, zero).unwrap();
    let assertions = [split, ge, le];

    let report = produce_lra_dpll_evidence(&mut arena, &assertions, &config()).unwrap();
    let Evidence::UnsatLraDpll(_) = &report.evidence else {
        panic!("expected a lazy-SMT refutation, got {:?}", report.evidence);
    };
    assert!(report.evidence.is_certified());
    assert_eq!(report.provenance.backend, "lra-dpll-farkas-enumeration");
    // The single Evidence::check re-runs the independent refutation verifier.
    assert!(report.evidence.check(&arena, &assertions).unwrap());
}

#[test]
fn lra_dpll_sat_evidence_replays() {
    // (x < 0 ∨ x > 0) ∧ x >= 1 : satisfiable via the x > 0 branch.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.real_ratio(0, 1);
    let one = arena.real_ratio(1, 1);
    let lt = arena.real_lt(x, zero).unwrap();
    let gt = arena.real_gt(x, zero).unwrap();
    let split = arena.or(lt, gt).unwrap();
    let ge1 = arena.real_ge(x, one).unwrap();
    let assertions = [split, ge1];

    let report = produce_lra_dpll_evidence(&mut arena, &assertions, &config()).unwrap();
    assert!(matches!(report.evidence, Evidence::Sat(_)));
    assert!(report.evidence.check(&arena, &assertions).unwrap());
}

#[test]
fn tampered_lra_dpll_evidence_fails_its_own_check() {
    // Strip the lemmas from the refutation: the bare skeleton is satisfiable, so
    // the independent verifier rejects the doctored evidence.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.real_ratio(0, 1);
    let lt = arena.real_lt(x, zero).unwrap();
    let gt = arena.real_gt(x, zero).unwrap();
    let split = arena.or(lt, gt).unwrap();
    let ge = arena.real_ge(x, zero).unwrap();
    let le = arena.real_le(x, zero).unwrap();
    let assertions = [split, ge, le];

    let report = produce_lra_dpll_evidence(&mut arena, &assertions, &config()).unwrap();
    let Evidence::UnsatLraDpll(mut refutation) = report.evidence else {
        panic!("expected a refutation");
    };
    refutation.lemmas.clear();
    let bogus = Evidence::UnsatLraDpll(refutation);
    assert!(
        !bogus.check(&arena, &assertions).unwrap(),
        "a lemma-stripped refutation must not check"
    );
}
