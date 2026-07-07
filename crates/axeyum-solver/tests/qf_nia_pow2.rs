//! Soundness + capability tests for the `int.pow2` wiring (P2.5 slice 6, task #41).
//!
//! `int.pow2` follows cvc5's total semantics VERBATIM (authoritative source:
//! `references/cvc5/src/theory/evaluator.cpp`): `pow2(x) = 2^x` for `x ≥ 0` and
//! the DEFINED value `pow2(x) = 0` for `x < 0` (cvc5's `ARITH_NL_POW2_NEG_REFINE`
//! lemma `x < 0 ⇒ pow2(x) = 0`, and its `pow2-native-0` regression, both pin the
//! negative case to `0` — it is NOT underspecified). The NIA linearizer abstracts
//! each `pow2(x)` to a fresh integer with theory-valid axioms; every `sat` is
//! additionally replay-checked against the ORIGINAL `pow2` term under the ground
//! evaluator, so a mis-abstraction can never produce a wrong `sat`.

use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

fn decide(text: &str) -> CheckResult {
    let cfg = SolverConfig {
        timeout: Some(Duration::from_secs(10)),
        ..SolverConfig::default()
    };
    solve_smtlib(text, &cfg)
        .unwrap_or_else(|e| panic!("solve_smtlib error on:\n{text}\nerror: {e}"))
        .result
}

fn assert_sat(text: &str) {
    match decide(text) {
        CheckResult::Sat(_) => {}
        other => panic!("expected sat, got {other:?} on:\n{text}"),
    }
}

fn assert_unsat(text: &str) {
    match decide(text) {
        CheckResult::Unsat => {}
        other => panic!("expected unsat, got {other:?} on:\n{text}"),
    }
}

fn assert_not_unsat(text: &str) {
    if matches!(decide(text), CheckResult::Unsat) {
        panic!("WRONG-UNSAT (soundness bug) on:\n{text}");
    }
}

// ---------------------------------------------------------------------------
// The seven committed cvc5 `pow2-native` corpus rows (the frontier this slice
// targets). Each is decided by the pow2 axioms / value table / box evaluation.
// ---------------------------------------------------------------------------

#[test]
fn pow2_native_1_positive_is_sat() {
    assert_sat(
        "(set-logic QF_NIA)\n(declare-fun x () Int)\n\
         (assert (and (<= 0 x) (< x 16)))\n(assert (> (int.pow2 x) 0))\n(check-sat)\n",
    );
}

#[test]
fn pow2_native_2_below_x_is_unsat() {
    // 0 ≤ x < 16 ∧ pow2(x) < x — unsat (2^x ≥ x + 1 > x for x ≥ 0).
    assert_unsat(
        "(set-logic QF_NIA)\n(declare-fun x () Int)\n\
         (assert (and (<= 0 x) (< x 16)))\n(assert (< (int.pow2 x) x))\n(check-sat)\n",
    );
}

#[test]
fn pow2_native_3_monotonicity_is_unsat() {
    // 0 ≤ x, 0 ≤ y, x < y ∧ pow2(x) > pow2(y) — unsat (strict monotonicity).
    assert_unsat(
        "(set-logic QF_NIA)\n(declare-fun x () Int)\n(declare-fun y () Int)\n\
         (assert (<= 0 x))\n(assert (<= 0 y))\n(assert (< x y))\n\
         (assert (> (int.pow2 x) (int.pow2 y)))\n(check-sat)\n",
    );
}

#[test]
fn pow2_native_4_positivity_is_unsat() {
    // 0 ≤ x ∧ 0 > pow2(x) — unsat (pow2(x) ≥ 1 for x ≥ 0).
    assert_unsat(
        "(set-logic QF_NIA)\n(declare-fun x () Int)\n\
         (assert (<= 0 x))\n(assert (> 0 (int.pow2 x)))\n(check-sat)\n",
    );
}

#[test]
fn pow2_native_5_evenness_is_unsat() {
    // x > 0 ∧ pow2(x) odd — unsat (2^x even for x ≥ 1).
    assert_unsat(
        "(set-logic QF_NIA)\n(declare-fun x () Int)\n\
         (assert (> x 0))\n(assert (< 0 (mod (int.pow2 x) 2)))\n(check-sat)\n",
    );
}

#[test]
fn pow2_native_6_div_by_pow2_is_unsat() {
    // 0 ≤ x ∧ div(x, pow2(x)) ≠ 0 — unsat (0 ≤ x < pow2(x) ⇒ div = 0).
    assert_unsat(
        "(set-logic QF_NIA)\n(declare-fun x () Int)\n\
         (assert (<= 0 x))\n(assert (distinct 0 (div x (int.pow2 x))))\n(check-sat)\n",
    );
}

#[test]
fn pow2_native_7_bounded_super_quadratic_is_unsat() {
    // 7 ≤ x ≤ 9 ∧ 2x² > pow2(x) — unsat (128,256,512 dominate 98,128,162).
    assert_unsat(
        "(set-logic QF_NIA)\n(declare-fun x () Int)\n\
         (assert (<= 7 x))\n(assert (>= 9 x))\n\
         (assert (> (* 2 (* x x)) (int.pow2 x)))\n(check-sat)\n",
    );
}

// ---------------------------------------------------------------------------
// SOUNDNESS BARS — the negative-exponent axis (the P0-class trap).
// ---------------------------------------------------------------------------

#[test]
fn pow2_negative_exponent_is_zero_unsat() {
    // cvc5's `pow2-native-0`: x < 0 ∧ pow2(x) ≠ 0 — UNSAT (negative case is
    // DEFINED to be 0). Our neg axiom `x < 0 ⇒ p = 0` decides it.
    assert_unsat(
        "(set-logic QF_NIA)\n(declare-fun x () Int)\n\
         (assert (< x 0))\n(assert (distinct (int.pow2 x) 0))\n(check-sat)\n",
    );
}

#[test]
fn pow2_negative_exponent_equals_zero_is_sat() {
    // x < 0 ∧ pow2(x) = 0 — SAT (the defined negative value). Must replay.
    assert_sat(
        "(set-logic QF_NIA)\n(declare-fun x () Int)\n\
         (assert (< x 0))\n(assert (= (int.pow2 x) 0))\n(check-sat)\n",
    );
}

#[test]
fn pow2_monotone_neg_soundness_is_sat() {
    // cvc5's `pow2-monotone-neg-soundness`: x < y ∧ y² = 4 ∧ pow2(y) ≤ pow2(x).
    // SAT via y = -2, x < -2: pow2(y) = pow2(x) = 0, 0 ≤ 0. A monotonicity axiom
    // NOT guarded by x ≥ 0 would WRONGLY refute this — the P0 soundness test.
    assert_not_unsat(
        "(set-logic QF_NIA)\n(declare-fun x () Int)\n(declare-fun y () Int)\n\
         (assert (< x y))\n(assert (= (* y y) 4))\n\
         (assert (<= (int.pow2 y) (int.pow2 x)))\n(check-sat)\n",
    );
}

#[test]
fn pow2_zero_is_one() {
    // pow2(0) = 1 (the boundary of the two branches). x = 0 ∧ pow2(x) = 1 sat.
    assert_sat(
        "(set-logic QF_NIA)\n(declare-fun x () Int)\n\
         (assert (= x 0))\n(assert (= (int.pow2 x) 1))\n(check-sat)\n",
    );
    // x = 0 ∧ pow2(x) ≠ 1 — unsat.
    assert_unsat(
        "(set-logic QF_NIA)\n(declare-fun x () Int)\n\
         (assert (= x 0))\n(assert (distinct (int.pow2 x) 1))\n(check-sat)\n",
    );
}

#[test]
fn pow2_exact_value_at_constant() {
    // pow2(10) = 1024, and ≠ 1024 is unsat — the exact value replay/eval.
    assert_sat(
        "(set-logic QF_NIA)\n(declare-fun x () Int)\n\
         (assert (= x 10))\n(assert (= (int.pow2 x) 1024))\n(check-sat)\n",
    );
    assert_unsat(
        "(set-logic QF_NIA)\n(declare-fun x () Int)\n\
         (assert (= x 10))\n(assert (distinct (int.pow2 x) 1024))\n(check-sat)\n",
    );
}

#[test]
fn pow2_unbounded_positive_witness_is_not_refuted() {
    // pow2(x) = 8 ∧ x ≥ 0 — SAT (x = 3). Must find/replay a real witness, never
    // wrongly refute an unbounded-but-satisfiable pow2 query.
    assert_not_unsat(
        "(set-logic QF_NIA)\n(declare-fun x () Int)\n\
         (assert (<= 0 x))\n(assert (= (int.pow2 x) 8))\n(check-sat)\n",
    );
}
