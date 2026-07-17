//! The **finite-modeled theories** opened this session — `QF_FF` (finite fields),
//! `QF_S` (strings), `QF_SET` (finite sets), and `QF_SEQ` (sequences) — all desugar to
//! `QF_BV` in [`axeyum_smtlib::parse_script`]. This test confirms that their `unsat`
//! instances therefore inherit the bit-vector path's **machine-checkable UNSAT
//! certificate**, extending axeyum's *Certifying* moat (the Lean-parity half of the
//! goal: "every unsat carries a checkable certificate") to these new divisions.
//!
//! For each theory a small `unsat` instance is parsed to its desugared-BV
//! [`axeyum_ir::TermArena`] and run through the proof-producing bit-vector path:
//!
//!  1. [`axeyum_solver::export_qf_bv_unsat_proof`] emits a DRAT refutation of the
//!     bit-blasted CNF, and [`axeyum_solver::UnsatProof::recheck`] **independently
//!     re-runs [`axeyum_cnf::check_drat`]** (RUP/RAT) over that DRAT against the
//!     emitted DIMACS — a wrong or holey proof fails the re-check.
//!  2. [`axeyum_solver::certify_qf_bv_unsat_end_to_end`] additionally composes a
//!     bit-blast-**faithfulness** miter (term ↔ CNF, checked against an independent
//!     reference bit-blaster) with the CNF-`unsat` DRAT, and
//!     [`axeyum_solver::EndToEndUnsatOutcome::recheck`] re-validates **both** DRAT
//!     sub-proofs. This is the stronger term-level certificate.
//!
//! Every assertion below is checked to produce a non-trivial CNF (real clauses) whose
//! refutation `check_drat` independently accepts — so the certificate is *re-validated*,
//! not merely shaped.
//!
//! ## What the Alethe/Carcara route does (and does not) cover here
//!
//! The complementary [`axeyum_solver::prove_qf_bv_unsat_alethe`] (Carcara-reconstructible
//! Alethe) route returns `None` for all four desugared formulas: the desugarings emit
//! `bvmul`/`bvurem` (finite-field arithmetic), `concat`/`extract` (strings/sequences),
//! and `bvand`/`bvor` over wide set words that fall **outside** the core bit-blast
//! fragment Carcara can reconstruct (mul/div/shifts are Carcara holes). So for these
//! divisions the **DRAT + `check_drat`** route — not Alethe/Carcara — is the certifying
//! path today; [`alethe_route_is_out_of_fragment_for_now`] documents that boundary so a
//! future Alethe-coverage increment has a regression anchor.
#![cfg(feature = "full")]

use axeyum_solver::{
    EndToEndUnsatOutcome, UnsatProofOutcome, certify_qf_bv_unsat_end_to_end,
    export_qf_bv_unsat_proof, prove_qf_bv_unsat_alethe,
};

/// Parses `src` to its desugared-BV arena+assertions, emits a DRAT refutation via
/// [`export_qf_bv_unsat_proof`], and asserts that [`axeyum_cnf::check_drat`] (run inside
/// [`axeyum_solver::UnsatProof::recheck`]) **independently accepts** it over a non-trivial
/// CNF. Then re-confirms the stronger end-to-end (faithfulness miter + DRAT) certificate
/// also re-validates. Returns the independently-rechecked clause count for the report.
fn assert_unsat_carries_rechecked_drat(theory: &str, src: &str) -> usize {
    let script = axeyum_smtlib::parse_script(src)
        .unwrap_or_else(|e| panic!("{theory}: parse to desugared BV failed: {e:?}"));
    assert!(
        !script.assertions.is_empty(),
        "{theory}: instance has no assertions"
    );

    // (1) DRAT proof of the bit-blasted CNF, independently re-checked by `check_drat`.
    let proof = match export_qf_bv_unsat_proof(&script.arena, &script.assertions) {
        Ok(UnsatProofOutcome::Proved(proof)) => proof,
        other => panic!(
            "{theory}: expected a DRAT UNSAT proof from the desugared-BV path, got {other:?}"
        ),
    };
    let clauses = proof
        .dimacs
        .lines()
        .filter(|l| !l.starts_with('p') && !l.starts_with('c') && !l.trim().is_empty())
        .count();
    assert!(
        clauses > 0,
        "{theory}: certificate is over a non-trivial (non-empty) CNF"
    );
    assert_eq!(
        proof.recheck(),
        Ok(true),
        "{theory}: independent check_drat (RUP/RAT) must accept the DRAT refutation"
    );

    // (2) Stronger end-to-end certificate: bit-blast-faithfulness miter ∘ CNF-unsat DRAT,
    //     with BOTH sub-proofs re-validated by `recheck`.
    match certify_qf_bv_unsat_end_to_end(&script.arena, &script.assertions) {
        Ok(outcome @ EndToEndUnsatOutcome::Certified { .. }) => {
            assert_eq!(
                outcome.recheck(),
                Ok(true),
                "{theory}: end-to-end (faithfulness + DRAT) certificate must re-validate"
            );
        }
        other => panic!("{theory}: expected an end-to-end Certified outcome, got {other:?}"),
    }

    clauses
}

/// `QF_FF` — `x*x = x` over `GF(17)` with `x ≠ 0` and `x ≠ 1` is `unsat` (the only
/// idempotents of a field are 0 and 1). The desugaring models `(_ FiniteField 17)` as a
/// `BitVec` with a `bvult x 17` well-formedness guard and `ff.mul` as `bvmul`-mod-17, so
/// the refutation is a real bit-blasted CNF, independently re-checked by `check_drat`.
#[test]
fn qf_ff_unsat_carries_rechecked_drat_proof() {
    let clauses = assert_unsat_carries_rechecked_drat(
        "QF_FF",
        "(set-logic QF_FF)\n\
         (declare-fun x () (_ FiniteField 17))\n\
         (assert (= (ff.mul x x) x))\n\
         (assert (not (= x #f1m17)))\n\
         (assert (not (= x #f0m17)))\n\
         (check-sat)",
    );
    assert!(clauses > 1, "QF_FF refutation exercises bit-blasted ff.mul");
}

/// `QF_S` — a string variable cannot equal two distinct string literals. The desugaring
/// fixes `s` to a bit-packed `"ab"` and `"cd"`; the two literal constraints conflict at
/// the bit level, and `check_drat` independently accepts the refutation.
#[test]
fn qf_s_unsat_carries_rechecked_drat_proof() {
    assert_unsat_carries_rechecked_drat(
        "QF_S",
        "(set-logic QF_S)\n\
         (declare-const s String)\n\
         (assert (= s \"ab\"))\n\
         (assert (= s \"cd\"))\n\
         (check-sat)",
    );
}

/// `QF_SET` — finite sets over a finite element domain are modeled as bit-sets:
/// `1 ∈ (S ∩ T)` forces `1 ∈ S`, contradicting `1 ∉ S`. The desugaring lowers
/// `set.inter`/`set.member` to `bvand`/bit-test over the modeled universe word; the
/// refutation is `check_drat`-accepted.
#[test]
fn qf_set_unsat_carries_rechecked_drat_proof() {
    assert_unsat_carries_rechecked_drat(
        "QF_SET",
        "(set-logic QF_UF)\n\
         (declare-fun S () (Set (_ BitVec 4)))\n\
         (declare-fun T () (Set (_ BitVec 4)))\n\
         (assert (set.member #x1 (set.inter S T)))\n\
         (assert (not (set.member #x1 S)))\n\
         (check-sat)",
    );
}

/// `QF_SEQ` — `(seq.unit #x0001)` and `(seq.unit #x0002)` are length-1 sequences whose
/// single elements `#x0001 ≠ #x0002`, so they cannot be equal (`seq.unit` is injective).
/// The desugaring packs the unit sequences into fixed-width BV words; the element-bit
/// disequality refutes at the bit level and `check_drat` accepts it.
#[test]
fn qf_seq_unsat_carries_rechecked_drat_proof() {
    assert_unsat_carries_rechecked_drat(
        "QF_SEQ",
        "(set-logic QF_SEQ)\n\
         (declare-fun x () (Seq (_ BitVec 16)))\n\
         (assert (= (seq.unit #x0001) (seq.unit #x0002)))\n\
         (check-sat)",
    );
}

/// Documents the *current* Alethe/Carcara boundary: the Carcara-reconstructible Alethe
/// emitter [`prove_qf_bv_unsat_alethe`] returns `None` for all four desugared formulas,
/// because their desugarings use `bvmul`/`bvurem`/`concat`/`extract`/wide `bvand`/`bvor`
/// that lie outside the bit-blast fragment Carcara reconstructs. The DRAT route (the four
/// tests above) is the certifying path for these theories today; if a future increment
/// extends Alethe coverage so any of these starts returning `Some(_)`, this regression
/// flips and the comment above should be revisited.
#[test]
fn alethe_route_is_out_of_fragment_for_now() {
    let cases: [(&str, &str); 4] = [
        (
            "QF_FF",
            "(set-logic QF_FF)\n(declare-fun x () (_ FiniteField 17))\n\
             (assert (= (ff.mul x x) x))\n(assert (not (= x #f1m17)))\n\
             (assert (not (= x #f0m17)))\n(check-sat)",
        ),
        (
            "QF_S",
            "(set-logic QF_S)\n(declare-const s String)\n\
             (assert (= s \"ab\"))\n(assert (= s \"cd\"))\n(check-sat)",
        ),
        (
            "QF_SET",
            "(set-logic QF_UF)\n(declare-fun S () (Set (_ BitVec 4)))\n\
             (declare-fun T () (Set (_ BitVec 4)))\n\
             (assert (set.member #x1 (set.inter S T)))\n\
             (assert (not (set.member #x1 S)))\n(check-sat)",
        ),
        (
            "QF_SEQ",
            "(set-logic QF_SEQ)\n(declare-fun x () (Seq (_ BitVec 16)))\n\
             (assert (= (seq.unit #x0001) (seq.unit #x0002)))\n(check-sat)",
        ),
    ];
    for (theory, src) in cases {
        let script = axeyum_smtlib::parse_script(src).expect("parse");
        assert!(
            prove_qf_bv_unsat_alethe(&script.arena, &script.assertions).is_none(),
            "{theory}: Alethe/Carcara route is not yet wired for this desugaring \
             (out-of-fragment operator); DRAT is the certifying path. If this now \
             returns Some(_), Alethe coverage was extended — update the moat note."
        );
    }
}
