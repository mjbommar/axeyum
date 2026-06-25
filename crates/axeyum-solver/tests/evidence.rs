//! Self-checking evidence envelopes: produce a result with its justification
//! and re-validate it independently (ADR-0005 follow-through).

use std::time::Duration;

use axeyum_ir::{ArraySortKey, Sort, TermArena};
use axeyum_smtlib::parse_script;
use axeyum_solver::{
    ArrayAxiomKind, Evidence, EvidenceReport, SolverConfig, TrustId, produce_evidence,
    produce_lra_dpll_evidence, produce_lra_evidence, produce_qf_bv_evidence,
};

/// The trust-step ids a report depends on (P3.0).
fn step_ids(report: &EvidenceReport) -> Vec<TrustId> {
    report.trusted_steps.iter().map(|s| s.id).collect()
}

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(30))
}

fn unbounded_config() -> SolverConfig {
    SolverConfig::new()
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
fn large_in_fragment_qf_bv_unsat_carries_an_alethe_proof() {
    // (bvult a b) ∧ (bvult b c) ∧ (bvult c a) over three 8-bit vars: a strict
    // ordering 3-cycle, unsatisfiable, every assertion in the Alethe driver's
    // predicate fragment. 24 total bits bypasses term-level enumeration, so the
    // new Alethe-proof route (not plain DRAT) is taken.
    let mut arena = TermArena::new();
    let a = arena.bv_var("a", 8).unwrap();
    let b = arena.bv_var("b", 8).unwrap();
    let c = arena.bv_var("c", 8).unwrap();
    let ab = arena.bv_ult(a, b).unwrap();
    let bc = arena.bv_ult(b, c).unwrap();
    let ca = arena.bv_ult(c, a).unwrap();
    let assertions = [ab, bc, ca];

    let report = produce_qf_bv_evidence(&arena, &assertions, &config()).unwrap();
    let Evidence::UnsatAletheProof(_) = &report.evidence else {
        panic!(
            "expected an Alethe-proof-certified unsat, got {:?}",
            report.evidence
        );
    };
    assert!(report.evidence.is_certified());
    // The single Evidence::check re-runs check_alethe on the stored proof.
    assert!(report.evidence.check(&arena, &assertions).unwrap());

    // The Alethe proof certifies the bit-blast itself (unlike the DRAT route).
    let ids = step_ids(&report);
    assert!(ids.contains(&TrustId::BitBlast), "got {ids:?}");
    let bitblast = report
        .trusted_steps
        .iter()
        .find(|s| s.id == TrustId::BitBlast)
        .unwrap();
    assert!(
        bitblast.certified,
        "the Alethe proof re-derives the bit-blast, so it is certified"
    );
    let tseitin = report
        .trusted_steps
        .iter()
        .find(|s| s.id == TrustId::Tseitin)
        .unwrap();
    assert!(tseitin.certified);
    let sat = report
        .trusted_steps
        .iter()
        .find(|s| s.id == TrustId::SatRefutation)
        .unwrap();
    assert!(sat.certified);
}

#[test]
fn qf_ufbv_unsat_carries_a_zero_trust_alethe_certificate() {
    // f(a) = #b00 ∧ a = b ∧ ¬(f(b) = #b00): unsat by Ackermann congruence over `f`.
    // produce_evidence must now certify it with a check_alethe-validated Alethe proof
    // that DERIVES the functional-consistency reduction by eq_congruent — so the
    // evidence carries NO trusted reduction step, rather than the old trusted DRAT
    // certificate that recorded TrustId::Ackermann as a trust hole.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(2)], Sort::BitVec(2))
        .unwrap();
    let a = arena.bv_var("a", 2).unwrap();
    let b = arena.bv_var("b", 2).unwrap();
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let c00 = arena.bv_const(2, 0).unwrap();
    let e1 = arena.eq(fa, c00).unwrap();
    let e2 = arena.eq(a, b).unwrap();
    let e3 = {
        let e = arena.eq(fb, c00).unwrap();
        arena.not(e).unwrap()
    };
    let assertions = [e1, e2, e3];

    let report = produce_evidence(&mut arena, &assertions, &config()).unwrap();
    let Evidence::UnsatAletheProof(_) = &report.evidence else {
        panic!(
            "expected a zero-trust Alethe-certified unsat, got {:?}",
            report.evidence
        );
    };
    assert!(report.evidence.is_certified());
    // The single Evidence::check re-runs check_alethe on the stored proof.
    assert!(report.evidence.check(&arena, &assertions).unwrap());
    // No trusted reduction step: the Ackermann congruence is PROVEN, not trusted.
    assert!(
        report.trusted_steps.is_empty(),
        "expected zero trust holes (Ackermann proven via eq_congruent), got {:?}",
        step_ids(&report)
    );
}

#[test]
fn qf_ufbv_finite_domain_pigeonhole_unsat_carries_certificate() {
    let mut script = parse_script(
        r"
        (set-logic QF_UFBV)
        (declare-sort A 0)
        (declare-fun f ((_ BitVec 1)) A)
        (declare-fun g (A) (_ BitVec 1))
        (declare-fun x () A)
        (declare-fun y () A)
        (declare-fun z () A)
        (assert (and
          (not (= (f (g x)) (f (g y))))
          (not (= (f (g x)) (f (g z))))
          (not (= (f (g y)) (f (g z))))))
        (check-sat)
    ",
    )
    .unwrap();

    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
    let Evidence::UnsatFiniteDomainPigeonhole(cert) = &report.evidence else {
        panic!(
            "expected finite-domain pigeonhole evidence, got {:?}",
            report.evidence
        );
    };
    assert_eq!(cert.domain_size, 2);
    assert_eq!(cert.applications.len(), 3);
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(
        report.trusted_steps.is_empty(),
        "the pigeonhole certificate is checked directly from the original query"
    );
}

#[test]
#[allow(clippy::many_single_char_names)]
fn qf_abv_read_consistency_unsat_carries_a_zero_trust_alethe_certificate() {
    // select(a, i) = #b0…0 ∧ i = j ∧ ¬(select(a, j) = #b0…0): unsat by read
    // consistency over the array `a`. produce_evidence must now certify it with a
    // check_alethe-validated Alethe proof that DERIVES the read-consistency reduction
    // by eq_congruent over the unary select function — so the evidence carries NO
    // trusted reduction step, not the old DRAT cert recording TrustId::ArrayElim.
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let j = arena.bv_var("j", 4).unwrap();
    let c = arena.bv_const(8, 0).unwrap();
    let sa = arena.select(a, i).unwrap();
    let sb = arena.select(a, j).unwrap();
    let e1 = arena.eq(sa, c).unwrap();
    let e2 = arena.eq(i, j).unwrap();
    let e3 = {
        let e = arena.eq(sb, c).unwrap();
        arena.not(e).unwrap()
    };
    let assertions = [e1, e2, e3];

    let report = produce_evidence(&mut arena, &assertions, &config()).unwrap();
    let Evidence::UnsatAletheProof(_) = &report.evidence else {
        panic!(
            "expected a zero-trust Alethe-certified array unsat, got {:?}",
            report.evidence
        );
    };
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&arena, &assertions).unwrap());
    assert!(
        report.trusted_steps.is_empty(),
        "expected zero trust holes (read consistency proven via eq_congruent), got {:?}",
        step_ids(&report)
    );
}

#[test]
fn qf_dt_read_over_construct_unsat_carries_a_zero_trust_alethe_certificate() {
    // select_0(mk(a, b)) = #b00 ∧ ¬(a = #b00): unsat by read-over-construct
    // (select_0(mk(a, b)) → a). Now that evidence_route sends datatype queries
    // through `solve`, produce_evidence reaches the zero-trust cert helper, which
    // emits a check_alethe-validated Alethe proof that folds the projection by
    // eq_transitive (the projection discharged by ι-reduction) — so the evidence
    // carries NO trusted datatype reduction step, not the old DRAT/DatatypeElim cert.
    let mut arena = TermArena::new();
    let pair = arena.declare_datatype("Pair");
    let mk = arena.add_constructor(
        pair,
        "mk",
        &[("a".into(), Sort::BitVec(2)), ("b".into(), Sort::BitVec(2))],
    );
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let p = arena.construct(mk, &[a, b]).unwrap();
    let sel = arena.dt_select(mk, 0, p).unwrap();
    let c00 = arena.bv_const(2, 0).unwrap();
    let e1 = arena.eq(sel, c00).unwrap();
    let e2 = {
        let e = arena.eq(a, c00).unwrap();
        arena.not(e).unwrap()
    };
    let assertions = [e1, e2];

    let report = produce_evidence(&mut arena, &assertions, &config()).unwrap();
    let Evidence::UnsatAletheProof(_) = &report.evidence else {
        panic!(
            "expected a zero-trust Alethe-certified datatype unsat, got {:?}",
            report.evidence
        );
    };
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&arena, &assertions).unwrap());
    assert!(
        report.trusted_steps.is_empty(),
        "expected zero trust holes (datatype fold proven), got {:?}",
        step_ids(&report)
    );
}

#[test]
fn large_out_of_fragment_qf_bv_unsat_falls_back_to_drat() {
    // (= (bvshl x one) zero) ∧ (= x mask) style: a `bvshl` subterm is outside
    // the Alethe driver's fragment, so the >20-bit unsat falls back to the plain
    // DRAT route, where bit-blast is recorded but not certified. We use a
    // shift-by-zero conflict: x << 0 == x, asserted both == x and != x.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 24).unwrap();
    let zero = arena.bv_const(24, 0).unwrap();
    let shifted = arena.bv_shl(x, zero).unwrap(); // x << 0 == x, but bvshl is a Carcara hole
    let one = arena.bv_const(24, 1).unwrap();
    let masked = arena.bv_and(x, one).unwrap();
    let shifted_low = arena.bv_and(shifted, one).unwrap();
    let is_one = arena.eq(masked, one).unwrap();
    let is_zero = arena.eq(shifted_low, zero).unwrap();
    let assertions = [is_one, is_zero];

    let report = produce_qf_bv_evidence(&arena, &assertions, &config()).unwrap();
    let Evidence::Unsat(Some(_)) = &report.evidence else {
        panic!("expected a DRAT fallback unsat, got {:?}", report.evidence);
    };
    assert!(report.evidence.check(&arena, &assertions).unwrap());
    // On the DRAT route the bit-blast is trusted, not certified.
    let bitblast = report
        .trusted_steps
        .iter()
        .find(|s| s.id == TrustId::BitBlast)
        .unwrap();
    assert!(!bitblast.certified, "DRAT route does not certify bit-blast");
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
fn pure_real_front_door_falls_back_when_lra_certificate_declines() {
    let mut script = parse_script(
        r"
        (set-logic QF_LRA)
        (declare-fun x () Real)
        (declare-fun P () Bool)
        (assert
         (let ((y (ite P 1.0 x)))
           (and (not (= y 1))
                (> y 0)
                (<= y 1))))
        (check-sat)
    ",
    )
    .unwrap();

    let report = produce_evidence(&mut script.arena, &script.assertions, &config()).unwrap();
    assert!(
        matches!(report.evidence, Evidence::Sat(_)),
        "expected a replayed SAT model after LRA cert decline, got {:?}",
        report.evidence
    );
    assert!(
        report
            .evidence
            .check(&script.arena, &script.assertions)
            .unwrap()
    );
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
                index: ArraySortKey::BitVec(4),
                element: ArraySortKey::BitVec(4),
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

    let report = produce_evidence(&mut arena, &[i_eq_j, load_ne_v], &unbounded_config()).unwrap();
    assert!(
        matches!(report.evidence, Evidence::Unsat(Some(_))),
        "QF_ABV unsat must now carry a certificate, got {:?}",
        report.evidence
    );
    // The attached certificate re-validates independently.
    assert!(report.evidence.check(&arena, &[i_eq_j, load_ne_v]).unwrap());
}

#[test]
fn timed_produce_evidence_can_skip_optional_array_reduction_export() {
    // With an explicit wall-clock evidence budget, the unified front door remains
    // timely after solve has already decided `unsat`: if no stronger certificate
    // applies, it may skip the optional reduced-CNF DRAT export and return a bare
    // checked unsat instead of overrunning the audit budget.
    let mut arena = TermArena::new();
    let mem = arena
        .declare(
            "mem",
            Sort::Array {
                index: ArraySortKey::BitVec(4),
                element: ArraySortKey::BitVec(4),
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
    assert!(matches!(report.evidence, Evidence::Unsat(None)));
    assert!(!report.evidence.is_certified());
    assert!(report.evidence.check(&arena, &[i_eq_j, load_ne_v]).unwrap());
}

#[test]
fn produce_evidence_certifies_finite_array_extensionality_unsat() {
    // Explicit finite extensionality over all four BV2 indices:
    // every concrete read of `a` and `b` is equal, yet `a != b`.
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 2, 2).unwrap();
    let b = arena.array_var("b", 2, 2).unwrap();
    let mut assertions = Vec::new();
    for value in 0..4 {
        let idx = arena.bv_const(2, value).unwrap();
        let lhs = arena.select(a, idx).unwrap();
        let rhs = arena.select(b, idx).unwrap();
        assertions.push(arena.eq(lhs, rhs).unwrap());
    }
    let diseq = {
        let eq = arena.eq(a, b).unwrap();
        arena.not(eq).unwrap()
    };
    assertions.push(diseq);

    let report = produce_evidence(&mut arena, &assertions, &config()).unwrap();
    let Evidence::UnsatFiniteArrayExtensionality(cert) = &report.evidence else {
        panic!(
            "finite-array extensionality unsat must carry direct evidence, got {:?}",
            report.evidence
        );
    };
    assert_eq!(cert.index_width, 2);
    assert_eq!(cert.read_equalities.len(), 4);
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&arena, &assertions).unwrap());
    assert!(
        report.trusted_steps.is_empty(),
        "finite-array evidence carries no reduction trust holes"
    );
}

#[test]
fn produce_evidence_certifies_small_array_axiom_unsats() {
    let cases = [
        (
            "mccarthy",
            ArrayAxiomKind::ReadOverWrite,
            r"
            (set-logic QF_AUFBV)
            (declare-fun i () (_ BitVec 32))
            (declare-fun j () (_ BitVec 32))
            (declare-fun v () (_ BitVec 8))
            (declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
            (assert (not (= (select (store a i v) j) (ite (= i j) v (select a j)))))
            (check-sat)
        ",
        ),
        (
            "select_ite",
            ArrayAxiomKind::SelectIte,
            r"
            (set-logic QF_AUFBV)
            (declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
            (declare-fun b () (Array (_ BitVec 32) (_ BitVec 8)))
            (declare-fun i () (_ BitVec 32))
            (declare-fun c () Bool)
            (assert (not (= (ite c (select a i) (select b i)) (select (ite c a b) i))))
            (check-sat)
        ",
        ),
        (
            "store_ite_select",
            ArrayAxiomKind::StoreIteSelect,
            r"
            (set-logic QF_AUFBV)
            (declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
            (declare-fun b () (Array (_ BitVec 32) (_ BitVec 8)))
            (declare-fun i () (_ BitVec 32))
            (declare-fun j () (_ BitVec 32))
            (declare-fun v () (_ BitVec 8))
            (declare-fun c () Bool)
            (assert (not (= (select (ite c (store a i v) (store b i v)) j)
                            (select (store (ite c a b) i v) j))))
            (check-sat)
        ",
        ),
        (
            "abv_btor_write1",
            ArrayAxiomKind::ReadOverWrite,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write1.btor.smt2"
            ),
        ),
        (
            "abv_btor_write13",
            ArrayAxiomKind::ReadOverWrite,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write13.btor.smt2"
            ),
        ),
        (
            "abv_btor_write2",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write2.btor.smt2"
            ),
        ),
        (
            "abv_btor_write4",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write4.btor.smt2"
            ),
        ),
        (
            "abv_btor_write7",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write7.btor.smt2"
            ),
        ),
        (
            "abv_btor_write8",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write8.btor.smt2"
            ),
        ),
        (
            "abv_btor_write9",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write9.btor.smt2"
            ),
        ),
        (
            "abv_btor_write10",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write10.btor.smt2"
            ),
        ),
        (
            "abv_btor_rwpropindexplusconst1",
            ArrayAxiomKind::ReadOverWrite,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rwpropindexplusconst1.btor.smt2"
            ),
        ),
        (
            "abv_btor_rwpropindexplusconst3",
            ArrayAxiomKind::ReadOverWrite,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rwpropindexplusconst3.btor.smt2"
            ),
        ),
        (
            "abv_btor_write22",
            ArrayAxiomKind::StoreShadowing,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write22.btor.smt2"
            ),
        ),
        (
            "abv_btor_write23",
            ArrayAxiomKind::StoreShadowing,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write23.btor.smt2"
            ),
        ),
        (
            "abv_btor_write24",
            ArrayAxiomKind::StoreShadowing,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write24.btor.smt2"
            ),
        ),
        (
            "abv_btor_rw30",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw30.btor.smt2"
            ),
        ),
        (
            "abv_btor_rw31",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw31.btor.smt2"
            ),
        ),
        (
            "abv_btor_rw32",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw32.btor.smt2"
            ),
        ),
        (
            "abv_btor_rw33",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw33.btor.smt2"
            ),
        ),
        (
            "abv_btor_write14",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write14.btor.smt2"
            ),
        ),
        (
            "abv_btor_arraycondconst",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycondconst.btor.smt2"
            ),
        ),
        (
            "abv_btor_arraycondconstaig",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycondconstaig.btor.smt2"
            ),
        ),
        (
            "abv_btor_ext5",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext5.btor.smt2"
            ),
        ),
        (
            "abv_btor_ext21",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext21.btor.smt2"
            ),
        ),
        (
            "abv_btor_ext23",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext23.btor.smt2"
            ),
        ),
        (
            "abv_btor_ext16",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext16.btor.smt2"
            ),
        ),
        (
            "abv_btor_ext26",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext26.btor.smt2"
            ),
        ),
        (
            "abv_btor_ext19",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext19.btor.smt2"
            ),
        ),
        (
            "abv_btor_ext24",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext24.btor.smt2"
            ),
        ),
        (
            "abv_btor_ext25",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext25.btor.smt2"
            ),
        ),
        (
            "abv_btor_3vl1",
            ArrayAxiomKind::ReadOverWrite,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__3vl1.btor.smt2"
            ),
        ),
        (
            "abv_btor_extarraywrite1",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__extarraywrite1.btor.smt2"
            ),
        ),
        (
            "abv_btor_ext22",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext22.btor.smt2"
            ),
        ),
        (
            "abv_btor_ext27",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext27.btor.smt2"
            ),
        ),
        (
            "abv_btor_ext28",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext28.btor.smt2"
            ),
        ),
        (
            "abv_btor_read1",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read1.btor.smt2"
            ),
        ),
        (
            "abv_btor_read4",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read4.btor.smt2"
            ),
        ),
        (
            "abv_btor_read10",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read10.btor.smt2"
            ),
        ),
        (
            "abv_btor_read22",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read22.btor.smt2"
            ),
        ),
    ];

    for (name, kind, smt2) in cases {
        let mut script = parse_script(smt2).unwrap_or_else(|err| panic!("{name} parses: {err}"));
        let assertions = script.assertions.clone();
        let report = produce_evidence(&mut script.arena, &assertions, &config())
            .unwrap_or_else(|err| panic!("{name} decides: {err}"));
        let Evidence::UnsatArrayAxiom(cert) = &report.evidence else {
            panic!(
                "{name}: expected array-axiom evidence, got {:?}",
                report.evidence
            );
        };
        assert_eq!(cert.kind, kind, "{name}");
        assert!(report.evidence.is_certified(), "{name}");
        assert!(
            report.evidence.check(&script.arena, &assertions).unwrap(),
            "{name}"
        );
        assert!(report.trusted_steps.is_empty(), "{name}");
    }
}

#[test]
fn produce_evidence_certifies_array_bv_abstraction_unsat() {
    let text = include_str!(
        "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/rewrite__array__rw213.smt2"
    );
    let mut script = parse_script(text).expect("rw213 parses");
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config())
        .expect("rw213 produces evidence");
    let Evidence::UnsatBvAbstraction(cert) = &report.evidence else {
        panic!(
            "expected BV-abstraction evidence for rw213, got {:?}",
            report.evidence
        );
    };
    assert_eq!(cert.abstracted_terms.len(), 2);
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(
        report.trusted_steps.is_empty(),
        "BV-abstraction evidence carries no outer reduction trust holes"
    );
}

#[test]
fn produce_evidence_certifies_aligned_write_chain_commutation_unsat() {
    let text = include_str!(
        "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__wchains002ue.smt2"
    );
    let mut script = parse_script(text).expect("wchains002ue parses");
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config())
        .expect("wchains002ue produces evidence");
    let Evidence::UnsatAlignedWriteChainCommutation(cert) = &report.evidence else {
        panic!(
            "expected aligned-write-chain evidence for wchains002ue, got {:?}",
            report.evidence
        );
    };
    assert_eq!(cert.lanes, 4);
    assert_eq!(cert.element_width, 8);
    assert_eq!(cert.index_width, 32);
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(
        report.trusted_steps.is_empty(),
        "aligned-write-chain evidence carries no outer reduction trust holes"
    );
}

#[test]
fn produce_evidence_certifies_two_byte_memcpy_unsat() {
    let text = include_str!(
        "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__memcpy02.smt2"
    );
    let mut script = parse_script(text).expect("memcpy02 parses");
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config())
        .expect("memcpy02 produces evidence");
    let Evidence::UnsatTwoByteMemcpy(cert) = &report.evidence else {
        panic!(
            "expected two-byte memcpy evidence for memcpy02, got {:?}",
            report.evidence
        );
    };
    assert_eq!(cert.index_width, 32);
    assert_eq!(cert.element_width, 8);
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(
        report.trusted_steps.is_empty(),
        "two-byte memcpy evidence carries no outer reduction trust holes"
    );
}

#[test]
fn produce_evidence_certifies_two_element_bubble_sort_unsat() {
    let text = include_str!(
        "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__bubsort002un.smt2"
    );
    let mut script = parse_script(text).expect("bubsort002un parses");
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config())
        .expect("bubsort002un produces evidence");
    let Evidence::UnsatTwoElementBubbleSort(cert) = &report.evidence else {
        panic!(
            "expected two-element bubble-sort evidence for bubsort002un, got {:?}",
            report.evidence
        );
    };
    assert_eq!(cert.index_width, 32);
    assert_eq!(cert.element_width, 8);
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(
        report.trusted_steps.is_empty(),
        "two-element bubble-sort evidence carries no outer reduction trust holes"
    );
}

#[test]
fn produce_evidence_certifies_two_element_selection_sort_unsat() {
    let text = include_str!(
        "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__selsort002un.smt2"
    );
    let mut script = parse_script(text).expect("selsort002un parses");
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config())
        .expect("selsort002un produces evidence");
    let Evidence::UnsatTwoElementSelectionSort(cert) = &report.evidence else {
        panic!(
            "expected two-element selection-sort evidence for selsort002un, got {:?}",
            report.evidence
        );
    };
    assert_eq!(cert.index_width, 32);
    assert_eq!(cert.element_width, 8);
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(
        report.trusted_steps.is_empty(),
        "two-element selection-sort evidence carries no outer reduction trust holes"
    );
}

#[test]
fn produce_evidence_certifies_two_cell_xor_swap_unsat() {
    let text = include_str!(
        "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__dubreva002ue.smt2"
    );
    let mut script = parse_script(text).expect("dubreva002ue parses");
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config())
        .expect("dubreva002ue produces evidence");
    let Evidence::UnsatTwoCellXorSwap(cert) = &report.evidence else {
        panic!(
            "expected two-cell XOR-swap evidence for dubreva002ue, got {:?}",
            report.evidence
        );
    };
    assert_eq!(cert.index_width, 32);
    assert_eq!(cert.element_width, 8);
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(
        report.trusted_steps.is_empty(),
        "two-cell XOR-swap evidence carries no outer reduction trust holes"
    );
}

#[test]
fn produce_evidence_certifies_two_byte_xor_swap_roundtrip_unsat() {
    let text = include_str!(
        "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__swapmem002ue.smt2"
    );
    let mut script = parse_script(text).expect("swapmem002ue parses");
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config())
        .expect("swapmem002ue produces evidence");
    let Evidence::UnsatTwoByteXorSwapRoundtrip(cert) = &report.evidence else {
        panic!(
            "expected two-byte XOR-swap round-trip evidence for swapmem002ue, got {:?}",
            report.evidence
        );
    };
    assert_eq!(cert.index_width, 32);
    assert_eq!(cert.element_width, 8);
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(
        report.trusted_steps.is_empty(),
        "two-byte XOR-swap round-trip evidence carries no outer reduction trust holes"
    );
}

#[test]
fn produce_evidence_certifies_binary_search16_unsat() {
    let text = include_str!(
        "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__binarysearch32s016.smt2"
    );
    let mut script = parse_script(text).expect("binarysearch32s016 parses");
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config())
        .expect("binarysearch32s016 produces evidence");
    let Evidence::UnsatBinarySearch16(cert) = &report.evidence else {
        panic!(
            "expected binary-search16 evidence for binarysearch32s016, got {:?}",
            report.evidence
        );
    };
    assert_eq!(cert.index_width, 4);
    assert_eq!(cert.element_width, 32);
    assert_eq!(cert.probes.len(), 5);
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(
        report.trusted_steps.is_empty(),
        "binary-search16 evidence carries no outer reduction trust holes"
    );
}

#[test]
fn produce_evidence_certifies_fifo_bc04_unsat() {
    let text = include_str!(
        "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__fifo32bc04k05.smt2"
    );
    let mut script = parse_script(text).expect("fifo32bc04k05 parses");
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config())
        .expect("fifo32bc04k05 produces evidence");
    let Evidence::UnsatFifoBc04(cert) = &report.evidence else {
        panic!(
            "expected FIFO BC04 evidence for fifo32bc04k05, got {:?}",
            report.evidence
        );
    };
    assert_eq!(cert.bound, 5);
    assert_eq!(cert.index_width, 4);
    assert_eq!(cert.element_width, 32);
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(
        report.trusted_steps.is_empty(),
        "FIFO BC04 evidence carries no outer reduction trust holes"
    );
}

#[test]
fn produce_evidence_replays_fifo_ia04_sat() {
    let text = include_str!(
        "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__fifo32ia04k05.smt2"
    );
    let mut script = parse_script(text).expect("fifo32ia04k05 parses");
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config())
        .expect("fifo32ia04k05 produces evidence");
    let Evidence::Sat(model) = &report.evidence else {
        panic!(
            "expected SAT model for fifo32ia04k05, got {:?}",
            report.evidence
        );
    };
    assert!(!model.is_empty());
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
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
                index: ArraySortKey::BitVec(4),
                element: ArraySortKey::BitVec(4),
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

    let report = produce_evidence(&mut arena, &[i_eq_j, load_ne_v], &unbounded_config()).unwrap();
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

#[test]
fn produce_evidence_array_row_same_carries_alethe_proof() {
    // Structural read-over-write-same: select(store(a, i, v), i) != v is unsat by
    // the ROW-same axiom. produce_evidence now attaches the check_alethe-validated
    // array Alethe proof directly (no array-elimination or bit-blast reduction), so
    // it carries NO reduction trust holes.
    let mut arena = TermArena::new();
    let a = arena
        .declare(
            "a",
            Sort::Array {
                index: ArraySortKey::BitVec(4),
                element: ArraySortKey::BitVec(8),
            },
        )
        .unwrap();
    let a_v = arena.var(a);
    let i_sym = arena.declare("i", Sort::BitVec(4)).unwrap();
    let i = arena.var(i_sym);
    let v_sym = arena.declare("v", Sort::BitVec(8)).unwrap();
    let v = arena.var(v_sym);
    let stored = arena.store(a_v, i, v).unwrap();
    let sel = arena.select(stored, i).unwrap();
    let diseq = {
        let eq = arena.eq(sel, v).unwrap();
        arena.not(eq).unwrap()
    };

    let report = produce_evidence(&mut arena, &[diseq], &config()).unwrap();
    assert!(
        matches!(report.evidence, Evidence::UnsatAletheProof(_)),
        "structural ROW-same unsat must carry the array Alethe proof, got {:?}",
        report.evidence
    );
    assert!(
        report.evidence.check(&arena, &[diseq]).unwrap(),
        "proof re-checks"
    );
    assert!(
        report.trusted_steps.is_empty(),
        "the direct array Alethe proof has no reduction trust holes, got {:?}",
        report.trusted_steps
    );
}
