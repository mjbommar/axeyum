//! Self-checking evidence envelopes: produce a result with its justification
//! and re-validate it independently (ADR-0005 follow-through).

use std::time::Duration;

use axeyum_ir::{Sort, TermArena};
use axeyum_solver::{
    Evidence, EvidenceReport, SolverConfig, TrustId, produce_evidence, produce_lra_dpll_evidence,
    produce_lra_evidence, produce_qf_bv_evidence,
};

/// The trust-step ids a report depends on (P3.0).
fn step_ids(report: &EvidenceReport) -> Vec<TrustId> {
    report.trusted_steps.iter().map(|s| s.id).collect()
}

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
    // Per-layer provenance is snapshotted so a replay failure localizes (#8).
    let layers = report.provenance.layers;
    assert_eq!(layers, axeyum_solver::LayerVersions::CURRENT);
    assert_eq!(layers.sat_adapter, "rustsat-batsat");
    assert!(!layers.bitblaster.is_empty() && !layers.cnf.is_empty());
    // The evidence re-validates against the original query, independently.
    assert!(report.evidence.check(&arena, &[eq]).unwrap());
}

#[test]
fn unsat_evidence_carries_a_recheckable_drat_certificate() {
    // x & 1 == 1 AND x & 1 == 0 is unsatisfiable. Use a 24-bit variable so the
    // combined domain exceeds the term-level enumeration budget and the DRAT
    // clausal route is exercised.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 24).unwrap();
    let one = arena.bv_const(24, 1).unwrap();
    let zero = arena.bv_const(24, 0).unwrap();
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

#[test]
fn unified_front_door_routes_qf_bv_to_a_checkable_unsat() {
    // Pure QF_BV unsat → produce_evidence routes to the QF_BV pipeline. A 24-bit
    // variable exceeds the term-level enumeration budget, so this is the DRAT
    // clausal route.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 24).unwrap();
    let one = arena.bv_const(24, 1).unwrap();
    let zero = arena.bv_const(24, 0).unwrap();
    let masked = arena.bv_and(x, one).unwrap();
    let is_one = arena.eq(masked, one).unwrap();
    let is_zero = arena.eq(masked, zero).unwrap();
    let assertions = [is_one, is_zero];

    let report = axeyum_solver::produce_evidence(&mut arena, &assertions, &config()).unwrap();
    assert!(matches!(report.evidence, Evidence::Unsat(Some(_))));
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&arena, &assertions).unwrap());
}

#[test]
fn small_qf_bv_unsat_is_term_level_certified_and_rechecks() {
    // A small (4-bit) unsatisfiable QF_BV query gets the strongest evidence: a
    // reduction-free term-level certificate (only the evaluator is trusted), and
    // it re-validates via Evidence::check by re-enumerating.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 4).unwrap();
    let one = arena.bv_const(4, 1).unwrap();
    let zero = arena.bv_const(4, 0).unwrap();
    let masked = arena.bv_and(x, one).unwrap();
    let is_one = arena.eq(masked, one).unwrap();
    let is_zero = arena.eq(masked, zero).unwrap();
    let assertions = [is_one, is_zero];

    let report = produce_qf_bv_evidence(&arena, &assertions, &config()).unwrap();
    let Evidence::UnsatTermLevel { cases, .. } = &report.evidence else {
        panic!(
            "expected a term-level certificate, got {:?}",
            report.evidence
        );
    };
    assert_eq!(*cases, 16, "a 4-bit variable has 2^4 = 16 assignments");
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&arena, &assertions).unwrap());

    // The term-level certificate re-checks against the actual query: a different
    // (satisfiable) query must not pass this evidence's check.
    let sat_query = [arena.eq(masked, one).unwrap()];
    assert!(!report.evidence.check(&arena, &sat_query).unwrap());
}

#[test]
fn unified_front_door_routes_pure_real_to_a_refutation() {
    // Boolean-structured pure-real unsat → the lazy-SMT refutation route.
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_ratio(0, 1);
    let lt = arena.real_lt(x, zero).unwrap();
    let gt = arena.real_gt(x, zero).unwrap();
    let split = arena.or(lt, gt).unwrap();
    let ge = arena.real_ge(x, zero).unwrap();
    let le = arena.real_le(x, zero).unwrap();
    let assertions = [split, ge, le];

    let report = axeyum_solver::produce_evidence(&mut arena, &assertions, &config()).unwrap();
    assert!(matches!(report.evidence, Evidence::UnsatLraDpll(_)));
    assert!(report.evidence.check(&arena, &assertions).unwrap());
}

#[test]
fn unified_front_door_falls_back_for_integer_queries() {
    // A bounded-integer query is outside the certified routes; produce_evidence
    // falls back to the unified engine and the sat model is replay-certified.
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let one = arena.int_const(1);
    let five = arena.int_const(5);
    let sum = arena.int_add(x, one).unwrap();
    let eq = arena.eq(sum, five).unwrap();

    let report = axeyum_solver::produce_evidence(&mut arena, &[eq], &config()).unwrap();
    assert!(matches!(report.evidence, Evidence::Sat(_)));
    assert_eq!(report.provenance.backend, "auto-solve");
    assert!(report.evidence.check(&arena, &[eq]).unwrap());
}

#[test]
fn produce_evidence_certifies_qf_abv_unsat() {
    // The unified evidence path now attaches a re-checkable DRAT certificate for
    // a BV-reducible (array) unsat, instead of a bare Unsat(None). Read-over-
    // write: i==j => select(store(mem,i,v),j) == v, so the inequality is unsat.
    let mut arena = TermArena::new();
    let mem = arena
        .declare(
            "mem",
            Sort::Array {
                index: 4,
                element: 4,
            },
        )
        .unwrap();
    let mem_v = arena.var(mem);
    let is = arena.declare("i", Sort::BitVec(4)).unwrap();
    let js = arena.declare("j", Sort::BitVec(4)).unwrap();
    let vs = arena.declare("v", Sort::BitVec(4)).unwrap();
    let (i, j, v) = (arena.var(is), arena.var(js), arena.var(vs));
    let stored = arena.store(mem_v, i, v).unwrap();
    let loaded = arena.select(stored, j).unwrap();
    let i_eq_j = arena.eq(i, j).unwrap();
    let load_ne_v = {
        let eq = arena.eq(loaded, v).unwrap();
        arena.not(eq).unwrap()
    };

    let report = produce_evidence(&mut arena, &[i_eq_j, load_ne_v], &config()).unwrap();
    assert!(
        matches!(report.evidence, Evidence::Unsat(Some(_))),
        "QF_ABV unsat must now carry a certificate, got {:?}",
        report.evidence
    );
    // The attached certificate re-validates independently.
    assert!(report.evidence.check(&arena, &[i_eq_j, load_ne_v]).unwrap());
}

// ----- P3.0 trust-ledger: per-result trust steps ----------------------------

#[test]
fn qf_bv_drat_unsat_reports_bitblast_tseitin_sat_steps() {
    // The DRAT route (24-bit, too large to enumerate) depends on bit-blast +
    // Tseitin + the SAT refutation — and on no theory reduction.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 24).unwrap();
    let one = arena.bv_const(24, 1).unwrap();
    let zero = arena.bv_const(24, 0).unwrap();
    let masked = arena.bv_and(x, one).unwrap();
    let is_one = arena.eq(masked, one).unwrap();
    let is_zero = arena.eq(masked, zero).unwrap();
    let assertions = [is_one, is_zero];

    let report = produce_qf_bv_evidence(&arena, &assertions, &config()).unwrap();
    let ids = step_ids(&report);
    assert!(ids.contains(&TrustId::BitBlast), "got {ids:?}");
    assert!(ids.contains(&TrustId::Tseitin), "got {ids:?}");
    assert!(ids.contains(&TrustId::SatRefutation), "got {ids:?}");
    assert!(
        !ids.contains(&TrustId::ArrayElim),
        "no array reduction here"
    );
    // Tseitin + SAT refutation are certified this run; bit-blast is recorded but
    // not miter-certified on the plain DRAT route.
    let tseitin = report
        .trusted_steps
        .iter()
        .find(|s| s.id == TrustId::Tseitin)
        .unwrap();
    assert!(tseitin.certified);
    let bitblast = report
        .trusted_steps
        .iter()
        .find(|s| s.id == TrustId::BitBlast)
        .unwrap();
    assert!(!bitblast.certified);
}

#[test]
fn small_qf_bv_unsat_reports_only_term_level_step() {
    // The term-level route (4-bit) trusts only the evaluator — exactly one step.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 4).unwrap();
    let one = arena.bv_const(4, 1).unwrap();
    let zero = arena.bv_const(4, 0).unwrap();
    let masked = arena.bv_and(x, one).unwrap();
    let is_one = arena.eq(masked, one).unwrap();
    let is_zero = arena.eq(masked, zero).unwrap();
    let assertions = [is_one, is_zero];

    let report = produce_qf_bv_evidence(&arena, &assertions, &config()).unwrap();
    assert_eq!(step_ids(&report), vec![TrustId::TermLevelEnum]);
    assert!(report.trusted_steps.iter().all(|s| s.certified));
}

#[test]
fn qf_abv_unsat_reports_array_elim_trust_hole() {
    // The array reduction is a recorded trust hole; bit-blast is also recorded.
    let mut arena = TermArena::new();
    let mem = arena
        .declare(
            "mem",
            Sort::Array {
                index: 4,
                element: 4,
            },
        )
        .unwrap();
    let mem_v = arena.var(mem);
    let is = arena.declare("i", Sort::BitVec(4)).unwrap();
    let js = arena.declare("j", Sort::BitVec(4)).unwrap();
    let vs = arena.declare("v", Sort::BitVec(4)).unwrap();
    let (i, j, v) = (arena.var(is), arena.var(js), arena.var(vs));
    let stored = arena.store(mem_v, i, v).unwrap();
    let loaded = arena.select(stored, j).unwrap();
    let i_eq_j = arena.eq(i, j).unwrap();
    let load_ne_v = {
        let eq = arena.eq(loaded, v).unwrap();
        arena.not(eq).unwrap()
    };

    let report = produce_evidence(&mut arena, &[i_eq_j, load_ne_v], &config()).unwrap();
    let ids = step_ids(&report);
    assert!(ids.contains(&TrustId::ArrayElim), "got {ids:?}");
    assert!(ids.contains(&TrustId::BitBlast), "got {ids:?}");
    let array_step = report
        .trusted_steps
        .iter()
        .find(|s| s.id == TrustId::ArrayElim)
        .unwrap();
    assert!(!array_step.certified, "array-elim is a trust hole");
}

#[test]
fn qf_lra_unsat_reports_no_bitblast() {
    // The Farkas route carries no bit-blast / Tseitin trust — only the certified
    // Farkas refutation.
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_ratio(0, 1);
    let one = arena.real_ratio(1, 1);
    let ge_one = arena.real_ge(x, one).unwrap();
    let le_zero = arena.real_le(x, zero).unwrap();
    let assertions = [ge_one, le_zero];

    let report = produce_lra_evidence(&arena, &assertions).unwrap();
    let ids = step_ids(&report);
    assert!(!ids.contains(&TrustId::BitBlast), "got {ids:?}");
    assert!(!ids.contains(&TrustId::Tseitin), "got {ids:?}");
    assert!(ids.contains(&TrustId::Farkas), "got {ids:?}");
    assert!(report.trusted_steps.iter().all(|s| s.certified));
}
