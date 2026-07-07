//! `QF_NIA` `((_ iand k) a b)` bounded bit-blast (P2.5 slice 5).
//!
//! `iand` is desugared at parse time into `bv2nat(bvand(int2bv k a, int2bv k b))`
//! (an exact, denotation-preserving reduction; no new IR op). This slice teaches
//! the **finite-box** proof (`prove_int_box` / `decide_bounded_int_blast`) to
//! cover the resulting `bv2nat` bridge — its value is structurally in `[0, 2^k)` —
//! and to derive per-variable bounds from linear inequalities (`x + y ≤ 32 ∧ y ≥ 0
//! ⇒ x ≤ 32`). With the whole query proven to live in a finite, exactly-encodable
//! integer box, a bit-vector `Unsat` is a genuine integer `Unsat` (no wraparound),
//! and a `Sat` witness replays through the ground `iand` evaluator.
//!
//! Every verdict here is checkable: `Sat` by replay against the ORIGINAL script,
//! `Unsat` by the exact bounded box (re-checkable per ADR bounded-int-blast
//! certificate). The slice is strictly additive — it turns former `unknown`s into
//! decisions and never flips a decided verdict.

use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

fn cfg() -> SolverConfig {
    SolverConfig {
        timeout: Some(Duration::from_secs(10)),
        ..SolverConfig::default()
    }
}

fn verdict(script: &str) -> CheckResult {
    solve_smtlib(script, &cfg())
        .unwrap_or_else(|e| panic!("solve_smtlib errored: {e:?}"))
        .result
}

// ---------------------------------------------------------------------------
// The two census targets (`iand-native-2`, `iand-native-granularities`).
// ---------------------------------------------------------------------------

#[test]
fn iand_native_2_unsat() {
    // `((_ iand 4) x y) > 0 ∧ x·y = 0 ∧ x + y = 15`, with `0 ≤ x,y < 16`.
    // `x·y = 0` forces one of them to 0, so `iand(x,y) = 0`, contradicting `> 0`.
    let s = r"(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (and (<= 0 x) (< x 16)))
(assert (and (<= 0 y) (< y 16)))
(assert (> ((_ iand 4) x y) 0))
(assert (= (* x y) 0))
(assert (= (+ x y) 15))
(check-sat)";
    assert_eq!(verdict(s), CheckResult::Unsat);
}

#[test]
fn iand_native_granularities_unsat() {
    // `x,y ≥ 0`, `x + y ≤ 32`, `(iand5(x,y) ≥ 32 ∨ iand6(x,y) ≥ 32)`.
    // `iand5 < 32` always; `iand6 ≥ 32` needs bit 5 in both ⇒ `x,y ≥ 32` ⇒
    // `x + y ≥ 64 > 32`. Needs the linear upper bound `x ≤ 32` (from `x+y≤32`).
    let s = r"(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (>= x 0))
(assert (>= y 0))
(assert (<= (+ x y) 32))
(assert (or (>= ((_ iand 5) x y) 32) (>= ((_ iand 6) x y) 32)))
(check-sat)";
    assert_eq!(verdict(s), CheckResult::Unsat);
}

#[test]
fn iand_native_1_sat() {
    // `((_ iand 4) x y) > 0`, `0 ≤ x,y < 16` — satisfiable (e.g. x=y=1 ⇒ iand=1).
    let s = r"(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (and (<= 0 x) (< x 16)))
(assert (and (<= 0 y) (< y 16)))
(assert (> ((_ iand 4) x y) 0))
(check-sat)";
    assert!(
        matches!(verdict(s), CheckResult::Sat(_)),
        "iand-native-1 must be sat (model replay-checked in the entry point)"
    );
}

// ---------------------------------------------------------------------------
// `iand` semantics: `(_ iand k) a b` == the k-bit bitwise-AND of a,b.
// ---------------------------------------------------------------------------

/// Reference: the SMT-LIB `((_ iand k) a b)` value — bitwise-AND of the low `k`
/// bits (`int2bv`/`bvand`/`bv2nat`), always non-negative and `< 2^k`.
fn iand_ref(k: u32, a: i128, b: i128) -> i128 {
    let mask = (1i128 << k) - 1;
    (a & mask) & (b & mask)
}

#[test]
fn iand_semantics_matches_reference_via_var_pin() {
    // Pin x,y to concrete values with a bounded box and assert the iand result
    // equals / differs from the reference. Uses variables so the finite-box path
    // is exercised (a purely-constant query would fold trivially).
    for (k, a, b) in [(4u32, 6i128, 3i128), (4, 15, 15), (5, 21, 10), (6, 63, 32)] {
        let want = iand_ref(k, a, b);
        // Correct value ⇒ sat.
        let sat = format!(
            "(set-logic QF_NIA)\n\
             (declare-fun x () Int)\n(declare-fun y () Int)\n\
             (assert (= x {a}))\n(assert (= y {b}))\n\
             (assert (= ((_ iand {k}) x y) {want}))\n(check-sat)"
        );
        assert!(
            matches!(verdict(&sat), CheckResult::Sat(_)),
            "iand {k} {a} {b} = {want} must be sat"
        );
        // Wrong value (want+1) ⇒ unsat.
        let unsat = format!(
            "(set-logic QF_NIA)\n\
             (declare-fun x () Int)\n(declare-fun y () Int)\n\
             (assert (= x {a}))\n(assert (= y {b}))\n\
             (assert (= ((_ iand {k}) x y) {}))\n(check-sat)",
            want + 1
        );
        assert_eq!(
            verdict(&unsat),
            CheckResult::Unsat,
            "iand {k} {a} {b} != {} must be unsat",
            want + 1
        );
    }
}

// ---------------------------------------------------------------------------
// Property: over a small box, the ONLY satisfying (x,y) for a pinned iand
// output are exactly those the reference agrees with (both directions).
// ---------------------------------------------------------------------------

#[test]
fn iand_property_result_upper_bound_unsat() {
    // `iand(x,y) < 2^k` is a tautology, so `iand(x,y) >= 2^k` is unsat for any
    // bounded x,y — this exercises the structural `[0, 2^k)` interval directly.
    for k in [1u32, 3, 4, 6] {
        let hi = 1i128 << k;
        let s = format!(
            "(set-logic QF_NIA)\n\
             (declare-fun x () Int)\n(declare-fun y () Int)\n\
             (assert (and (<= 0 x) (< x 256)))\n\
             (assert (and (<= 0 y) (< y 256)))\n\
             (assert (>= ((_ iand {k}) x y) {hi}))\n(check-sat)"
        );
        assert_eq!(
            verdict(&s),
            CheckResult::Unsat,
            "iand {k} result >= 2^{k} must be unsat"
        );
    }
}

#[test]
fn iand_property_specific_witness_sat_and_replays() {
    // `iand(x,y) = k-bit-all-ones` forces every low bit of both to 1 ⇒ x,y ≡
    // (2^k − 1) mod 2^k; with `0 ≤ x,y < 2^k` the unique model is x = y = 2^k−1.
    for k in [2u32, 4, 5] {
        let all_ones = (1i128 << k) - 1;
        let s = format!(
            "(set-logic QF_NIA)\n\
             (declare-fun x () Int)\n(declare-fun y () Int)\n\
             (assert (and (<= 0 x) (< x {two_k})))\n\
             (assert (and (<= 0 y) (< y {two_k})))\n\
             (assert (= ((_ iand {k}) x y) {all_ones}))\n(check-sat)",
            two_k = 1i128 << k
        );
        assert!(
            matches!(verdict(&s), CheckResult::Sat(_)),
            "iand {k} = all-ones must be sat"
        );
    }
}
