//! Golden test for the **support matrix**: the committed support-matrix document
//! must equal what the in-code source of truth renders, so the four-axis status
//! report cannot drift out of sync with the code.
//!
//! Beyond the drift guard, this file *probes* the load-bearing solver/proof cells
//! through the public SMT-LIB front door (`solve_smtlib`) so the claimed statuses
//! are exercised against the real engine — in particular the first-class
//! "unsat decided; sat→unknown" status and the proof-supports cells.
#![cfg(feature = "full")]

use axeyum_solver::support_matrix::{
    ProofStatus, SUPPORT_MATRIX, SolverStatus, support_matrix_markdown,
};
use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

const DOC: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../docs/research/08-planning/support-matrix.md"
);

#[test]
fn support_matrix_doc_is_in_sync() {
    let generated = support_matrix_markdown();
    if std::env::var_os("UPDATE_SUPPORT_MATRIX").is_some() {
        std::fs::write(DOC, &generated).expect("write support-matrix.md");
        return;
    }
    let committed = std::fs::read_to_string(DOC).expect(
        "docs/research/08-planning/support-matrix.md missing — regenerate with \
         `UPDATE_SUPPORT_MATRIX=1 cargo test -p axeyum-solver --test support_matrix`",
    );
    assert_eq!(
        committed, generated,
        "support-matrix.md is stale vs the source of truth — regenerate with \
         `UPDATE_SUPPORT_MATRIX=1 cargo test -p axeyum-solver --test support_matrix`",
    );
}

#[test]
fn matrix_rows_are_well_formed() {
    assert!(!SUPPORT_MATRIX.is_empty(), "matrix must not be empty");
    let mut seen = std::collections::BTreeSet::new();
    for r in SUPPORT_MATRIX {
        assert!(!r.fragment.is_empty(), "fragment must be set");
        assert!(
            !r.note.is_empty(),
            "note (code grounding) must be set for {}",
            r.fragment
        );
        assert!(
            seen.insert(r.fragment),
            "duplicate fragment row: {}",
            r.fragment
        );
    }
}

/// Helper: decide a self-contained SMT-LIB script and return its `CheckResult`.
fn decide(script: &str) -> CheckResult {
    solve_smtlib(script, &SolverConfig::default())
        .unwrap_or_else(|e| panic!("solve_smtlib failed for probe:\n{script}\n-> {e}"))
        .result
}

fn is_sat(r: &CheckResult) -> bool {
    matches!(r, CheckResult::Sat(_))
}
fn is_unsat(r: &CheckResult) -> bool {
    matches!(r, CheckResult::Unsat)
}

// ---------------------------------------------------------------------------
// Probes for `solver-decides` cells. Each asserts the matrix's claimed status
// is backed by real engine behavior on a representative core query.
// ---------------------------------------------------------------------------

#[test]
fn probe_qf_bv_decides() {
    // unsat: x = 1 ∧ x = 2 over BitVec 8
    let unsat = decide(
        "(declare-const x (_ BitVec 8))\
         (assert (= x #x01))(assert (= x #x02))(check-sat)",
    );
    assert!(is_unsat(&unsat), "QF_BV unsat probe: {unsat:?}");
    // sat
    let sat = decide("(declare-const x (_ BitVec 8))(assert (= x #x01))(check-sat)");
    assert!(is_sat(&sat), "QF_BV sat probe: {sat:?}");
}

#[test]
fn probe_qf_uf_decides() {
    // f(a)=1 ∧ f(b)=2 ∧ a=b  is unsat by congruence (BV-sorted, fully decided).
    let unsat = decide(
        "(declare-fun f ((_ BitVec 8)) (_ BitVec 8))\
         (declare-const a (_ BitVec 8))(declare-const b (_ BitVec 8))\
         (assert (= (f a) #x01))(assert (= (f b) #x02))(assert (= a b))(check-sat)",
    );
    assert!(is_unsat(&unsat), "QF_UF congruence unsat probe: {unsat:?}");
}

#[test]
fn probe_qf_lra_decides() {
    let unsat = decide(
        "(declare-const x Real)\
         (assert (< x 0.0))(assert (> x 1.0))(check-sat)",
    );
    assert!(is_unsat(&unsat), "QF_LRA unsat probe: {unsat:?}");
    let sat = decide("(declare-const x Real)(assert (> x 0.0))(check-sat)");
    assert!(is_sat(&sat), "QF_LRA sat probe: {sat:?}");
}

#[test]
fn probe_qf_lia_decides() {
    let unsat = decide(
        "(declare-const x Int)\
         (assert (< x 0))(assert (> x 0))(assert (= x 0))(check-sat)",
    );
    assert!(is_unsat(&unsat), "QF_LIA unsat probe: {unsat:?}");
}

#[test]
fn probe_qf_nia_single_var_polynomial_decides() {
    // x*x = 2 has no integer solution: the single-variable polynomial decider
    // returns a definite unsat (the bit-blast/relaxation paths would say unknown).
    let unsat = decide("(declare-const x Int)(assert (= (* x x) 2))(check-sat)");
    assert!(
        is_unsat(&unsat),
        "QF_NIA single-var polynomial unsat probe (x*x=2): {unsat:?}"
    );
}

#[test]
fn probe_uflia_decides_unsat_and_replay_checked_sat() {
    // UNSAT side is decided: f:Int->Int, f(a)=1 ∧ f(b)=2 ∧ a=b is unsat by
    // congruence + LIA.
    let unsat = decide(
        "(declare-fun f (Int) Int)\
         (declare-const a Int)(declare-const b Int)\
         (assert (= (f a) 1))(assert (= (f b) 2))(assert (= a b))(check-sat)",
    );
    assert!(
        is_unsat(&unsat),
        "UFLIA arithmetic-sorted UF unsat probe: {unsat:?}"
    );

    // SAT side is now DECIDED with a replay-checked model: the eager-Ackermann
    // arithmetic model is projected back to a full-Value-keyed function
    // interpretation and replayed against the original assertions (drop the
    // `a=b` so the two `f` points are genuinely satisfiable).
    let sat_query = decide(
        "(declare-fun f (Int) Int)\
         (declare-const a Int)(declare-const b Int)\
         (assert (= (f a) 1))(assert (= (f b) 2))(check-sat)",
    );
    assert!(
        is_sat(&sat_query),
        "UFLIA satisfiable query must now be a replay-checked sat (never a wrong \
         sat/unsat): {sat_query:?}"
    );

    // And the matrix row must record that UFLIA now decides.
    let row = SUPPORT_MATRIX
        .iter()
        .find(|r| r.fragment.starts_with("QF_UFLIA"))
        .expect("QF_UFLIA row present");
    assert_eq!(
        row.solver,
        SolverStatus::Decides,
        "the UFLIA row must record that satisfiable queries now decide (replay-checked sat)"
    );
}

/// A satisfiable `QF_UFLRA` query through the SMT-LIB front door is likewise a
/// replay-checked `sat` (the real-keyed function interpretation projects).
#[test]
fn probe_uflra_satisfiable_is_replay_checked_sat() {
    let sat_query = decide(
        "(declare-fun g (Real) Real)\
         (declare-const p Real)\
         (assert (= (g p) 1.0))(assert (= p 2.0))(check-sat)",
    );
    assert!(
        is_sat(&sat_query),
        "UFLRA satisfiable query must be a replay-checked sat: {sat_query:?}"
    );
}

// ---------------------------------------------------------------------------
// Probes for `proof-supports` cells.
// ---------------------------------------------------------------------------

#[test]
fn probe_qf_bv_unsat_proof_is_checked() {
    use axeyum_ir::TermArena;
    use axeyum_solver::{UnsatProofOutcome, export_qf_bv_unsat_proof};

    // x = 1 ∧ x = 2 over BitVec 8 → a DRAT proof that re-checks from text alone.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let two = arena.bv_const(8, 2).unwrap();
    let a1 = arena.eq(x, one).unwrap();
    let a2 = arena.eq(x, two).unwrap();

    let outcome = export_qf_bv_unsat_proof(&arena, &[a1, a2]).expect("export QF_BV proof");
    match outcome {
        UnsatProofOutcome::Proved(proof) => {
            assert_eq!(
                proof.recheck().ok(),
                Some(true),
                "QF_BV unsat DRAT proof must re-check from text alone (proof-supports=checked)"
            );
        }
        other => panic!("expected a checkable QF_BV unsat proof, got {other:?}"),
    }

    // The matrix row must claim `checked`.
    let row = SUPPORT_MATRIX
        .iter()
        .find(|r| r.fragment.starts_with("QF_BV"))
        .expect("QF_BV row present");
    assert_eq!(row.proof, ProofStatus::Checked);
}

#[test]
fn probe_qf_lra_unsat_has_farkas_certificate() {
    use axeyum_ir::TermArena;
    use axeyum_solver::{check_with_lra, lra_farkas_certificate};

    // x < 0 ∧ x > 0 is unsat in QF_LRA; an exact-rational Farkas certificate must
    // verify from scratch (proof-supports=checked).
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_ratio(0, 1);
    let lt0 = arena.real_lt(x, zero).unwrap();
    let gt0 = arena.real_gt(x, zero).unwrap();

    let res = check_with_lra(&arena, &[lt0, gt0]).expect("LRA decide");
    assert!(matches!(res, CheckResult::Unsat), "QF_LRA unsat: {res:?}");

    let cert = lra_farkas_certificate(&arena, &[lt0, gt0])
        .expect("LRA farkas")
        .expect("an unsat query yields a Farkas certificate");
    assert!(
        cert.verify(),
        "QF_LRA Farkas certificate must verify from scratch (proof-supports=checked)"
    );

    let row = SUPPORT_MATRIX
        .iter()
        .find(|r| r.fragment.starts_with("QF_LRA"))
        .expect("QF_LRA row present");
    assert_eq!(row.proof, ProofStatus::Checked);
}

// ---------------------------------------------------------------------------
// Probes for `parser-accepts` first-class statuses.
// ---------------------------------------------------------------------------

#[test]
fn probe_accepted_but_ignored_and_rejected_commands() {
    // Output commands are accepted by the single-result facade: a script using
    // them still parses and decides, even when richer command output is served
    // through explicit helper APIs.
    let ok = solve_smtlib(
        "(set-option :produce-models true)\
         (get-option :produce-models)\
         (echo \"hi\")\
         (declare-const x (_ BitVec 4))(assert (= x #x1))(check-sat)\
         (get-model)(exit)",
        &SolverConfig::default(),
    );
    assert!(
        ok.is_ok(),
        "accepted-but-ignored output commands must not break parsing/solving: {ok:?}"
    );

    // Full `reset` is deliberately rejected (distinct from accepted-but-ignored).
    let rejected = solve_smtlib(
        "(declare-const x (_ BitVec 4))(reset)(check-sat)",
        &SolverConfig::default(),
    );
    assert!(
        rejected.is_err(),
        "full `reset` must be rejected by the parser, got Ok: {rejected:?}"
    );
}
