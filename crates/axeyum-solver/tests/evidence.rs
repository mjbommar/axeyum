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
    // f(a) = #x00 ∧ a = b ∧ ¬(f(b) = #x00): unsat by Ackermann congruence over `f`.
    // Use 8-bit variables so the newer tiny local BV+UF enumerator declines and
    // this test continues to exercise the zero-trust Alethe route directly.
    // produce_evidence must now certify it with a check_alethe-validated Alethe proof
    // that DERIVES the functional-consistency reduction by eq_congruent — so the
    // evidence carries NO trusted reduction step, rather than the old trusted DRAT
    // certificate that recorded TrustId::Ackermann as a trust hole.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
        .unwrap();
    let a = arena.bv_var("a", 8).unwrap();
    let b = arena.bv_var("b", 8).unwrap();
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let c00 = arena.bv_const(8, 0).unwrap();
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
fn qf_uf_declared_sort_equality_unsat_carries_zero_trust_alethe_certificate() {
    let mut script = parse_script(
        r"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun x () U)
        (declare-fun y () U)
        (assert (distinct x y))
        (assert (let ((x y) (y x)) (= x y)))
        (check-sat)
    ",
    )
    .unwrap();

    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
    let Evidence::UnsatAletheProof(_) = &report.evidence else {
        panic!(
            "expected a pure EUF Alethe certificate, got {:?}",
            report.evidence
        );
    };
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(
        report.trusted_steps.is_empty(),
        "carrier-sort equality conflicts should be proved, not trusted"
    );
}

#[test]
fn qf_uf_parser_as_sat_evidence_replays_declared_sort_model() {
    let mut script = parse_script(
        r"
        (set-logic QF_UF)
        (declare-sort I 0)
        (declare-fun e0 () I)
        (assert (= (as e0 I) (as e0 I)))
        (check-sat)
    ",
    )
    .unwrap();

    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
    assert!(
        matches!(report.evidence, Evidence::Sat(_)),
        "expected replayable SAT evidence for parser/as row, got {:?}",
        report.evidence
    );
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(report.trusted_steps.is_empty());
}

#[test]
fn qf_uf_declared_sort_ite_sat_evidence_replays_model() {
    let mut script = parse_script(
        r"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun x () U)
        (declare-fun y () U)
        (declare-fun a () Bool)
        (assert (not (= x (ite a (ite a x y) (ite (not a) y x)))))
        (check-sat)
    ",
    )
    .unwrap();

    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
    assert!(
        matches!(report.evidence, Evidence::Sat(_)),
        "expected replayable SAT evidence for declared-sort ITE row, got {:?}",
        report.evidence
    );
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(report.trusted_steps.is_empty());
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
fn qf_ufbv_fun1_bool_uf_exhaustive_unsat_carries_certificate() {
    let mut script = parse_script(include_str!(
        "../../../corpus/public-curated/non-incremental/QF_UFBV/bitwuzla-regress-clean/solver__fun__fun1.smt2"
    ))
    .expect("bitwuzla fun1 row parses");

    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
    let Evidence::UnsatBoolUfExhaustive(cert) = &report.evidence else {
        panic!(
            "expected finite Boolean-UF exhaustive evidence, got {:?}",
            report.evidence
        );
    };
    assert_eq!(cert.bool_symbols.len(), 2);
    assert_eq!(cert.functions.len(), 1);
    assert_eq!(cert.cases, 16);
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(
        report.trusted_steps.is_empty(),
        "the Boolean-UF certificate is checked directly from the original query"
    );
}

#[test]
fn qf_uf_set_cardinality_rows_use_checked_cardinality_evidence() {
    for (tag, input) in [
        (
            "sets-card",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress0__sets__card.smt2"
            ),
        ),
        (
            "sets-card-6",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress1__sets__card-6.smt2"
            ),
        ),
    ] {
        let mut script = parse_script(input).expect("QF_UF set-cardinality row parses");
        let assertions = script.assertions.clone();
        let report = produce_evidence(&mut script.arena, &assertions, &config())
            .unwrap_or_else(|error| panic!("{tag}: produce evidence failed: {error}"));
        let Evidence::UnsatSetCardinality(cert) = &report.evidence else {
            panic!(
                "{tag}: expected set-cardinality evidence, got {:?}",
                report.evidence
            );
        };
        assert_eq!(cert.lower_bound, 5, "{tag}");
        assert_eq!(cert.upper_bound, 4, "{tag}");
        assert!(report.evidence.is_certified(), "{tag}");
        assert!(
            report.evidence.check(&script.arena, &assertions).unwrap(),
            "{tag}"
        );
        assert!(
            report.trusted_steps.is_empty(),
            "{tag}: cardinality certificate should be checked directly"
        );
    }
}

#[test]
fn qf_uf_boolean_euf_rows_use_checked_exhaustive_evidence() {
    for (tag, input, expected_atoms) in [
        (
            "simple-uf",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress0__simple-uf.smt2"
            ),
            2,
        ),
        (
            "cnf-and-neg",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress0__uf__cnf-and-neg.smt2"
            ),
            4,
        ),
        (
            "cnf-ite",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress0__uf__cnf-ite.smt2"
            ),
            8,
        ),
    ] {
        let mut script = parse_script(input).expect("QF_UF Boolean-EUF row parses");
        let assertions = script.assertions.clone();
        let report = produce_evidence(&mut script.arena, &assertions, &config())
            .unwrap_or_else(|error| panic!("{tag}: produce evidence failed: {error}"));
        let Evidence::UnsatBoolEufExhaustive(cert) = &report.evidence else {
            panic!(
                "{tag}: expected Boolean-EUF exhaustive evidence, got {:?}",
                report.evidence
            );
        };
        assert_eq!(cert.atoms.len(), expected_atoms, "{tag}");
        assert!(report.evidence.is_certified(), "{tag}");
        assert!(
            report.evidence.check(&script.arena, &assertions).unwrap(),
            "{tag}"
        );
        assert!(
            report.trusted_steps.is_empty(),
            "{tag}: Boolean-EUF certificate should be checked directly"
        );
    }
}

#[test]
fn qf_uf_overbound_rows_use_checked_online_euf_evidence() {
    for (tag, input) in [
        (
            "cnf_abc",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-overbound/cli__regress0__uf__cnf_abc.smt2"
            ),
        ),
        (
            "proof00",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-overbound/cli__regress1__proof00.smt2"
            ),
        ),
        (
            "macro_res_exp",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-overbound/cli__regress1__proofs__macro-res-exp-crowding-lit-inside-unit.smt2"
            ),
        ),
    ] {
        let mut script = parse_script(input).expect("QF_UF overbound row parses");
        let assertions = script.assertions.clone();
        let report = produce_evidence(&mut script.arena, &assertions, &config())
            .unwrap_or_else(|error| panic!("{tag}: produce evidence failed: {error}"));
        let Evidence::UnsatBoolEufOnline(cert) = &report.evidence else {
            panic!(
                "{tag}: expected online Boolean-EUF evidence, got {:?}",
                report.evidence
            );
        };
        assert!(
            cert.atoms > 16,
            "{tag}: expected large Boolean-EUF skeleton"
        );
        assert!(report.evidence.is_certified(), "{tag}");
        assert!(
            report.evidence.check(&script.arena, &assertions).unwrap(),
            "{tag}"
        );
        assert!(
            report.trusted_steps.is_empty(),
            "{tag}: online Boolean-EUF certificate should be checked directly"
        );
    }
}

#[test]
fn qf_uf_bug303_uses_checked_uf_arith_congruence_evidence() {
    let mut script = parse_script(include_str!(
        "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress0__bug303.smt2"
    ))
    .expect("bug303 parses");
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config())
        .expect("bug303 evidence is produced");
    let Evidence::UnsatUfArithCongruence(cert) = &report.evidence else {
        panic!(
            "expected UF arithmetic congruence evidence for bug303, got {:?}",
            report.evidence
        );
    };
    assert_eq!(cert.arithmetic_assertions, 3);
    assert_eq!(cert.congruence_consequents, 1);
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(
        report.trusted_steps.is_empty(),
        "UF arithmetic congruence certificate should be checked directly"
    );
}

#[test]
fn qf_dt_cvc5_slice_uses_checked_datatype_structural_evidence() {
    for (tag, input, min_branches) in [
        (
            "pf-v2l60078",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_DT/cvc5-regress-clean/cli__regress0__datatypes__pf-v2l60078.smt2"
            ),
            1,
        ),
        (
            "dt-cons-eq-clash",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_DT/cvc5-regress-clean/cli__regress0__proofs__dt-cons-eq-clash-qfdt.smt2"
            ),
            1,
        ),
        (
            "acyclicity-sr-ground096",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_DT/cvc5-regress-clean/cli__regress1__datatypes__acyclicity-sr-ground096.smt2"
            ),
            2,
        ),
    ] {
        let mut script = parse_script(input).unwrap_or_else(|e| panic!("{tag}: parses: {e}"));
        let assertions = script.assertions.clone();
        let report = produce_evidence(&mut script.arena, &assertions, &config())
            .unwrap_or_else(|e| panic!("{tag}: should produce evidence: {e}"));
        let Evidence::UnsatDatatypeStructural(cert) = &report.evidence else {
            panic!(
                "{tag}: expected datatype structural evidence, got {:?}",
                report.evidence
            );
        };
        assert!(
            cert.branches >= min_branches,
            "{tag}: expected at least {min_branches} structural branch(es), got {}",
            cert.branches
        );
        assert!(report.evidence.is_certified(), "{tag}");
        assert!(
            report.evidence.check(&script.arena, &assertions).unwrap(),
            "{tag}"
        );
        assert!(
            report.trusted_steps.is_empty(),
            "{tag}: the datatype structural certificate is checked directly from the original query"
        );
    }
}

#[test]
fn qf_nra_sos_certificate_wrapper_carries_lean_module() {
    let mut script = parse_script(include_str!(
        "../../../corpus/public-curated/synthetic/QF_NRA/graduated/nra-sos-unsat-k01.smt2"
    ))
    .expect("synthetic NRA SOS row parses");

    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
    let Evidence::UnsatSos {
        certificate,
        lean_module,
    } = &report.evidence
    else {
        panic!("expected SOS evidence, got {:?}", report.evidence);
    };
    assert!(certificate.verify());
    assert!(lean_module.as_ref().is_some_and(|m| !m.contains("sorryAx")));
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(
        report.trusted_steps.iter().all(|step| step.certified),
        "SOS certificate should not introduce uncertified trust holes: {:?}",
        step_ids(&report)
    );
}

#[test]
fn qf_nra_even_power_rows_use_checked_evidence() {
    for (input, terms, max_exp) in [
        (
            include_str!(
                "../../../corpus/public-curated/synthetic/QF_NRA/graduated/nra-neg-square-d02.smt2"
            ),
            1,
            4,
        ),
        (
            include_str!(
                "../../../corpus/public-curated/synthetic/QF_NRA/graduated/nra-sos-strict-unsat-d02.smt2"
            ),
            2,
            4,
        ),
    ] {
        let mut script = parse_script(input).expect("synthetic NRA even-power row parses");
        let assertions = script.assertions.clone();
        let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
        let Evidence::UnsatNraEvenPower(cert) = &report.evidence else {
            panic!(
                "expected NRA even-power evidence, got {:?}",
                report.evidence
            );
        };
        assert_eq!(cert.even_power_terms, terms);
        assert_eq!(cert.max_even_exponent, max_exp);
        assert!(report.evidence.is_certified());
        assert!(report.evidence.check(&script.arena, &assertions).unwrap());
        assert!(
            report.trusted_steps.is_empty(),
            "the even-power certificate is checked directly from the original query"
        );
    }
}

#[test]
fn qf_nia_bounded_unsat_rows_use_bounded_int_blast_evidence() {
    for input in [
        include_str!(
            "../../../corpus/public-curated/synthetic/QF_NIA/graduated/nia-no-square-mod-b01.smt2"
        ),
        include_str!(
            "../../../corpus/public-curated/synthetic/QF_NIA/graduated/nia-no-square-mod-b08.smt2"
        ),
        include_str!(
            "../../../corpus/public-curated/synthetic/QF_NIA/graduated/nia-sum-sq-2-n01.smt2"
        ),
        include_str!(
            "../../../corpus/public-curated/synthetic/QF_NIA/graduated/nia-sum-sq-2-n08.smt2"
        ),
    ] {
        let mut script = parse_script(input).expect("synthetic QF_NIA row parses");
        let assertions = script.assertions.clone();
        let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
        let Evidence::UnsatBoundedIntBlast(cert) = &report.evidence else {
            panic!(
                "expected bounded-int-blast evidence, got {:?}",
                report.evidence
            );
        };
        assert!(!cert.per_var_bounds().is_empty());
        assert!(cert.recheck(&script.arena, &assertions).unwrap());
        assert!(report.evidence.is_certified());
        assert!(report.evidence.check(&script.arena, &assertions).unwrap());
        assert!(
            report.trusted_steps.iter().all(|step| step.certified),
            "bounded-int-blast evidence should not carry uncertified trust holes: {:?}",
            step_ids(&report)
        );
    }
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
fn pure_real_identity_contradiction_uses_term_identity_evidence() {
    let mut script = parse_script(include_str!(
        "../../../corpus/public-curated/non-incremental/QF_LRA/cvc5-regress-clean/cli__regress0__ite_arith.smt2"
    ))
    .expect("ite_arith parses");

    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
    assert!(
        matches!(report.evidence, Evidence::UnsatTermIdentity(_)),
        "expected term-identity evidence, got {:?}",
        report.evidence
    );
    assert!(report.evidence.is_certified());
    assert!(report.trusted_steps.is_empty());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
}

#[test]
fn qf_lia_audit_misses_use_arith_dpll_evidence() {
    for input in [
        include_str!(
            "../../../corpus/public-curated/non-incremental/QF_LIA/cvc5-regress-clean-bounded/cli__regress0__dump-unsat-core-full.smt2"
        ),
        include_str!(
            "../../../corpus/public-curated/non-incremental/QF_LIA/cvc5-regress-clean-bounded/cli__regress0__named-expr-use.smt2"
        ),
    ] {
        let mut script = parse_script(input).expect("QF_LIA audit row parses");
        let assertions = script.assertions.clone();
        let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
        assert!(
            matches!(report.evidence, Evidence::UnsatArithDpll(_)),
            "expected arith-DPLL evidence, got {:?}",
            report.evidence
        );
        assert!(report.evidence.is_certified());
        assert!(report.trusted_steps.is_empty());
        assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    }
}

#[test]
fn qf_lia_boolean_stress_row_uses_bool_simplification_evidence() {
    let mut script = parse_script(include_str!(
        "../../../corpus/public-curated/non-incremental/QF_LIA/cvc5-regress-clean-bounded/cli__regress0__proofs__RF-11-aci-norm-ndet.smt2"
    ))
    .expect("RF row parses");
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
    assert!(
        matches!(report.evidence, Evidence::UnsatBoolSimplification(_)),
        "expected bool-simplification evidence, got {:?}",
        report.evidence
    );
    assert!(report.evidence.is_certified());
    assert!(report.trusted_steps.is_empty());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
}

#[test]
fn qf_uf_issue3970_uses_checked_term_identity_evidence() {
    let mut script = parse_script(include_str!(
        "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress1__issue3970-nl-ext-purify.smt2"
    ))
    .expect("issue3970 row parses");
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
    assert!(
        matches!(report.evidence, Evidence::UnsatTermIdentity(_)),
        "expected term-identity evidence, got {:?}",
        report.evidence
    );
    assert!(report.evidence.is_certified());
    assert!(report.trusted_steps.is_empty());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
}

#[test]
fn congruence_free_uflia_uses_opaque_arith_alethe_evidence() {
    // f(0) <= 0 ∧ f(0) >= 1 is unsat after treating the repeated UF application
    // as one opaque integer term; no Ackermann/congruence lemmas are needed.
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let f0 = arena.apply(f, &[zero]).unwrap();
    let le = arena.int_le(f0, zero).unwrap();
    let ge = arena.int_ge(f0, one).unwrap();
    let assertions = [le, ge];

    let report = produce_evidence(&mut arena, &assertions, &config()).unwrap();
    let Evidence::UnsatArithAletheProof(_) = &report.evidence else {
        panic!(
            "expected opaque UFLIA arith-Alethe evidence, got {:?}",
            report.evidence
        );
    };
    assert!(report.evidence.is_certified());
    assert!(report.trusted_steps.is_empty());
    assert!(report.evidence.check(&arena, &assertions).unwrap());
}

#[test]
fn qf_uflia_use_name_rows_use_opaque_arith_dpll_evidence() {
    for input in [
        include_str!("../../../corpus/public-curated/named/cvc5__use-name-in-same-command.smt2"),
        include_str!(
            "../../../corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-bounded/cli__regress0__parser__use-name-in-same-command.smt2"
        ),
    ] {
        let mut script = parse_script(input).expect("QF_UFLIA use-name row parses");
        let assertions = script.assertions.clone();
        let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
        assert!(
            matches!(report.evidence, Evidence::UnsatArithDpll(_)),
            "expected opaque UFLIA arith-DPLL evidence, got {:?}",
            report.evidence
        );
        assert!(report.evidence.is_certified());
        assert!(report.trusted_steps.is_empty());
        assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    }
}

#[test]
fn satisfiable_uflia_opaque_arith_abstraction_still_replays_sat_model() {
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let f0 = arena.apply(f, &[zero]).unwrap();
    let eq = arena.eq(f0, one).unwrap();

    let report = produce_evidence(&mut arena, &[eq], &config()).unwrap();
    assert!(
        matches!(report.evidence, Evidence::Sat(_)),
        "expected replay-checkable UFLIA sat evidence, got {:?}",
        report.evidence
    );
    assert!(report.evidence.is_certified());
    assert!(report.trusted_steps.is_empty());
    assert!(report.evidence.check(&arena, &[eq]).unwrap());
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
fn quantified_bv_audit_unsats_use_finite_domain_enum_evidence() {
    for (tag, input) in [
        (
            "abstract_unsatcore1",
            include_str!(
                "../../../corpus/public-curated/quantified/BV/bitwuzla-regress-clean/solver__abstract__unsatcore1.smt2"
            ),
        ),
        (
            "quant_issue97",
            include_str!(
                "../../../corpus/public-curated/quantified/BV/bitwuzla-regress-clean/solver__quant__issue97.smt2"
            ),
        ),
        (
            "quant_regrnormquant",
            include_str!(
                "../../../corpus/public-curated/quantified/BV/bitwuzla-regress-clean/solver__quant__regrnormquant.smt2"
            ),
        ),
    ] {
        let mut script = parse_script(input).expect("quantified BV audit row parses");
        let assertions = script.assertions.clone();
        let report = produce_evidence(&mut script.arena, &assertions, &config())
            .unwrap_or_else(|error| panic!("{tag}: evidence production failed: {error}"));
        let Evidence::UnsatFiniteDomainEnum {
            cases,
            max_total_bits,
        } = &report.evidence
        else {
            panic!(
                "{tag}: expected finite-domain enum evidence, got {:?}",
                report.evidence
            );
        };
        assert!(*cases > 0, "{tag}: certificate should count finite cases");
        assert_eq!(*max_total_bits, 20);
        assert!(
            report.evidence.is_certified(),
            "{tag}: evidence should be certified"
        );
        assert!(
            report.evidence.check(&script.arena, &assertions).unwrap(),
            "{tag}: evidence should re-check"
        );
        let step = report
            .trusted_steps
            .iter()
            .find(|s| s.id == TrustId::TermLevelEnum)
            .unwrap_or_else(|| panic!("{tag}: missing TermLevelEnum trust step"));
        assert!(
            step.certified,
            "{tag}: finite-domain enumeration should be certified"
        );
    }
}

#[test]
fn cvc5_quantified_bv_inversion_rows_use_checked_nonconstant_evidence() {
    for (tag, input) in [
        (
            "invert_bvadd",
            include_str!(
                "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress0__quantifiers__qbv-test-invert-bvadd-neq.smt2"
            ),
        ),
        (
            "invert_bvashr",
            include_str!(
                "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress0__quantifiers__qbv-test-invert-bvashr-0-neq.smt2"
            ),
        ),
        (
            "invert_concat_0",
            include_str!(
                "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress0__quantifiers__qbv-test-invert-concat-0-neq.smt2"
            ),
        ),
        (
            "invert_concat_1",
            include_str!(
                "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress0__quantifiers__qbv-test-invert-concat-1-neq.smt2"
            ),
        ),
        (
            "invert_bvudiv_0",
            include_str!(
                "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__qbv-test-invert-bvudiv-0-neq.smt2"
            ),
        ),
        (
            "invert_bvudiv_1",
            include_str!(
                "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__qbv-test-invert-bvudiv-1-neq.smt2"
            ),
        ),
    ] {
        let mut script = parse_script(input).expect("cvc5 quantified BV inversion row parses");
        let assertions = script.assertions.clone();
        let report = produce_evidence(&mut script.arena, &assertions, &config())
            .unwrap_or_else(|error| panic!("{tag}: evidence production failed: {error}"));
        let Evidence::UnsatBvForallNonconstant(cert) = &report.evidence else {
            panic!(
                "{tag}: expected BV forall non-constant evidence, got {:?}",
                report.evidence
            );
        };
        assert_eq!(cert.variable_width, 8, "{tag}");
        assert!(
            report.evidence.is_certified(),
            "{tag}: evidence should be certified"
        );
        assert!(
            report.evidence.check(&script.arena, &assertions).unwrap(),
            "{tag}: evidence should re-check"
        );
        assert!(
            report.trusted_steps.is_empty(),
            "{tag}: direct structural certificate should carry no trust holes"
        );
    }
}

#[test]
fn qf_ufff_rows_use_checked_bv_uf_local_evidence() {
    for (tag, input) in [
        (
            "qf_ufff_with_uf",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_UFFF/cvc5-regress-clean/cli__regress0__ff__with_uf.smt2"
            ),
        ),
        (
            "qf_ufff_with_uf2",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_UFFF/cvc5-regress-clean/cli__regress0__ff__with_uf2.smt2"
            ),
        ),
        (
            "qf_ufff_with_uf3",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_UFFF/cvc5-regress-clean/cli__regress0__ff__with_uf3.smt2"
            ),
        ),
        (
            "qf_ufff_with_uf5",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_UFFF/cvc5-regress-clean/cli__regress0__ff__with_uf5.smt2"
            ),
        ),
        (
            "qf_ufff_with_uf7",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_UFFF/cvc5-regress-clean/cli__regress0__ff__with_uf7.smt2"
            ),
        ),
        (
            "qf_ufff_with_uf8",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_UFFF/cvc5-regress-clean/cli__regress0__ff__with_uf8.smt2"
            ),
        ),
    ] {
        let mut script = parse_script(input).expect("QF_UFFF row parses");
        let assertions = script.assertions.clone();
        let report = produce_evidence(&mut script.arena, &assertions, &config())
            .unwrap_or_else(|error| panic!("{tag}: evidence production failed: {error}"));
        let Evidence::UnsatBvUfLocal(cert) = &report.evidence else {
            panic!(
                "{tag}: expected local BV+UF evidence, got {:?}",
                report.evidence
            );
        };
        assert!(
            !cert.derived_equalities.is_empty(),
            "{tag}: certificate should carry derived BV equality facts"
        );
        assert!(
            report.evidence.is_certified(),
            "{tag}: evidence should be certified"
        );
        assert!(
            report.evidence.check(&script.arena, &assertions).unwrap(),
            "{tag}: evidence should re-check"
        );
        assert!(
            report.trusted_steps.is_empty(),
            "{tag}: direct structural certificate should carry no trust holes"
        );
    }
}

#[test]
fn qf_ff_gap_rows_use_checked_bv_defined_enum_evidence() {
    for (tag, input) in [
        (
            "qf_ff_xor_sound",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_FF/cvc5-regress-clean/cli__regress0__ff__ff_xor_sound.smt2"
            ),
        ),
        (
            "qf_ff_issue10937",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_FF/cvc5-regress-clean/cli__regress0__ff__issue10937.smt2"
            ),
        ),
    ] {
        let mut script = parse_script(input).expect("QF_FF row parses");
        let assertions = script.assertions.clone();
        let report = produce_evidence(&mut script.arena, &assertions, &config())
            .unwrap_or_else(|error| panic!("{tag}: evidence production failed: {error}"));
        let Evidence::UnsatBvDefinedEnum(cert) = &report.evidence else {
            panic!(
                "{tag}: expected definition-aware BV enum evidence, got {:?}",
                report.evidence
            );
        };
        assert!(cert.cases > 0, "{tag}: certificate should count cases");
        assert!(
            report.evidence.is_certified(),
            "{tag}: evidence should be certified"
        );
        assert!(
            report.evidence.check(&script.arena, &assertions).unwrap(),
            "{tag}: evidence should re-check"
        );
        assert!(
            report.trusted_steps.is_empty(),
            "{tag}: direct structural certificate should carry no trust holes"
        );
    }
}

#[test]
fn qf_fp_bitwuzla_rows_use_checked_bv_defined_enum_evidence() {
    for (tag, input) in [
        (
            "qf_fp_inf",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_FP/bitwuzla-regress-clean/solver__fp__fp_inf.smt2"
            ),
        ),
        (
            "qf_fp_zero",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_FP/bitwuzla-regress-clean/solver__fp__fp_zero.smt2"
            ),
        ),
        (
            "qf_fp_misc",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_FP/bitwuzla-regress-clean/solver__fp__fp_misc.smt2"
            ),
        ),
    ] {
        let mut script = parse_script(input).expect("QF_FP row parses");
        let assertions = script.assertions.clone();
        let report = produce_evidence(&mut script.arena, &assertions, &config())
            .unwrap_or_else(|error| panic!("{tag}: evidence production failed: {error}"));
        let Evidence::UnsatBvDefinedEnum(cert) = &report.evidence else {
            panic!(
                "{tag}: expected definition-aware scalar enum evidence, got {:?}",
                report.evidence
            );
        };
        assert!(
            (1..=10).contains(&cert.cases),
            "{tag}: FP certificate should stay in the small replay slice, got {} cases",
            cert.cases
        );
        assert!(
            report.evidence.is_certified(),
            "{tag}: evidence should be certified"
        );
        assert!(
            report.evidence.check(&script.arena, &assertions).unwrap(),
            "{tag}: evidence should re-check"
        );
        assert!(
            report.trusted_steps.is_empty(),
            "{tag}: direct structural certificate should carry no trust holes"
        );
    }
}

#[test]
fn qf_bvfp_bitwuzla_rows_use_checked_bv_defined_enum_evidence() {
    for (tag, input, max_cases) in [
        (
            "qf_bvfp_float_no_simp3",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_BVFP/bitwuzla-regress-clean/solver__fp__Float-no-simp3-main.smt2"
            ),
            2,
        ),
        (
            "qf_bvfp_fp_fromsbv",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_BVFP/bitwuzla-regress-clean/solver__fp__fp_fromsbv.smt2"
            ),
            10,
        ),
    ] {
        let mut script = parse_script(input).expect("QF_BVFP row parses");
        let assertions = script.assertions.clone();
        let report = produce_evidence(&mut script.arena, &assertions, &config())
            .unwrap_or_else(|error| panic!("{tag}: evidence production failed: {error}"));
        let Evidence::UnsatBvDefinedEnum(cert) = &report.evidence else {
            panic!(
                "{tag}: expected definition-aware scalar enum evidence, got {:?}",
                report.evidence
            );
        };
        assert!(
            (1..=max_cases).contains(&cert.cases),
            "{tag}: QF_BVFP certificate should stay in the small replay slice, got {} cases",
            cert.cases
        );
        assert!(
            report.evidence.is_certified(),
            "{tag}: evidence should be certified"
        );
        assert!(
            report.evidence.check(&script.arena, &assertions).unwrap(),
            "{tag}: evidence should re-check"
        );
        assert!(
            report.trusted_steps.is_empty(),
            "{tag}: direct structural certificate should carry no trust holes"
        );
    }
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
            "abv_btor_rw34",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw34.btor.smt2"
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
            "abv_btor_arraycond3",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond3.btor.smt2"
            ),
        ),
        (
            "abv_btor_arraycond5",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond5.btor.smt2"
            ),
        ),
        (
            "abv_btor_arraycond6",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond6.btor.smt2"
            ),
        ),
        (
            "abv_btor_arraycond7",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond7.btor.smt2"
            ),
        ),
        (
            "abv_btor_arraycond8",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond8.btor.smt2"
            ),
        ),
        (
            "abv_btor_arraycond9",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond9.btor.smt2"
            ),
        ),
        (
            "abv_btor_arraycond11",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond11.btor.smt2"
            ),
        ),
        (
            "abv_btor_arraycond12",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond12.btor.smt2"
            ),
        ),
        (
            "abv_btor_arraycond13",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond13.btor.smt2"
            ),
        ),
        (
            "abv_btor_arraycond14",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond14.btor.smt2"
            ),
        ),
        (
            "abv_btor_arraycond18",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond18.btor.smt2"
            ),
        ),
        (
            "abv_btor_ext11",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext11.btor.smt2"
            ),
        ),
        (
            "abv_cvc5_issue9519",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__bv__issue9519.smt2"
            ),
        ),
        (
            "abv_cvc5_proj_issue321",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__bv__proj-issue321.smt2"
            ),
        ),
        (
            "abv_cvc5_bug637_delta",
            ArrayAxiomKind::StoreShadowing,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__arrays__bug637.delta.smt2"
            ),
        ),
        (
            "abv_cvc5_issue9041",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__arrays__issue9041.smt2"
            ),
        ),
        (
            "abv_cvc5_bvproof2",
            ArrayAxiomKind::StoreShadowing,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__bv__bvproof2.smt2"
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
            "abv_btor_ext13",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext13.btor.smt2"
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
            "abv_btor_read9",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read9.btor.smt2"
            ),
        ),
        (
            "abv_btor_write16",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write16.btor.smt2"
            ),
        ),
        (
            "abv_btor_write17",
            ArrayAxiomKind::ReadCongruence,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write17.btor.smt2"
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
