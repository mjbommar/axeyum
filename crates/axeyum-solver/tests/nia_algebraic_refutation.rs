//! Integer-aware, UNSAT-only polynomial-identity refutation (`QF_NIA`).
//!
//! Covers the [`integer_algebraic_refutation`](axeyum_solver) route wired into
//! `check_auto` as an `Unknown`-fallback: a `QF_NIA` conjunction whose asserted
//! disequality `p ≠ 0` reduces, under the asserted equalities (including the
//! integer tight-bound `g ≥ 0 ∧ −g ≥ 0 ⊢ g = 0`), to the zero polynomial — hence
//! `0 ≠ 0`, UNSAT. The route is genuinely integer-specific: `nl-eq-infer`'s real
//! relaxation is SAT (`i−n = 3/2`), so the multivariate CAD cannot see it.
//!
//! The soundness contract is the usual one: the route emits **only** UNSAT and
//! never a model, so it can never produce a wrong `sat`; and every UNSAT it
//! emits must match the benchmark `:status`. The wrong-sat-negative cases below
//! pin that a genuinely SATISFIABLE integer query is NOT falsely refuted.

use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

fn verdict(text: &str) -> CheckResult {
    // Bound the solve so a genuinely-hard sat case (the wrong-sat-negatives run
    // the full NIA path) degrades to `Unknown` rather than hanging — the
    // refutation route only ever DECLINES on sat, so `Unknown` still satisfies
    // the `assert_ne Unsat` contract. The unsat cases are decided instantly by
    // the pure-arithmetic identity route, well within the budget.
    let config = SolverConfig::default().with_timeout(Duration::from_secs(5));
    solve_smtlib(text, &config).expect("solve").result
}

/// The keystone: `cli__regress1__nl__nl-eq-infer` (`QF_NIA`, unsat). E2 ∧ E3 pin
/// `i − n = 1`; substituting `n = i−1` and `s = (i²−i)/2` (from E1) into D
/// (`n² + n − 2s ≠ 0`) collapses D to `0` ⇒ UNSAT.
#[test]
fn nl_eq_infer_is_unsat() {
    let text = r"
(set-logic QF_NIA)
(declare-fun i () Int)
(declare-fun n () Int)
(declare-fun s () Int)
(assert (and
  (= i (+ (* (- 2) s) (* i i)))
  (>= (+ i (* (- 1) n)) 1)
  (not (>= (+ i (* (- 1) n)) 2))
))
(assert (not (= n (+ (* 2 s) (* (- 1) (* n n))))))
(check-sat)
";
    assert_eq!(verdict(text), CheckResult::Unsat);
}

/// A minimal tight-bound identity: `x − y = 1` (via `≥ 1 ∧ ¬(≥ 2)`) and the
/// disequality `x − y ≠ 1` are jointly unsat over ℤ.
#[test]
fn tight_bound_pins_difference() {
    let text = r"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (and (>= (- x y) 1) (not (>= (- x y) 2))))
(assert (not (= (- x y) 1)))
(check-sat)
";
    assert_eq!(verdict(text), CheckResult::Unsat);
}

// ---------------------------------------------------------------------------
// Wrong-sat-negatives: a genuinely satisfiable integer query must NOT be
// refuted. `solve_smtlib` may return `Sat` OR `Unknown` (the route only ever
// DECLINES on sat) — the one forbidden outcome is `Unsat`.
// ---------------------------------------------------------------------------

/// The real-relaxation witness of `nl-eq-infer` uses `i − n = 3/2`; over ℤ the
/// WEAKER query WITHOUT the upper tight-bound (`¬(i−n ≥ 2)` dropped) is
/// satisfiable — the refutation must not fire without both bounds.
#[test]
fn without_upper_bound_not_refuted() {
    let text = r"
(set-logic QF_NIA)
(declare-fun i () Int)
(declare-fun n () Int)
(declare-fun s () Int)
(assert (and
  (= i (+ (* (- 2) s) (* i i)))
  (>= (+ i (* (- 1) n)) 1)
))
(assert (not (= n (+ (* 2 s) (* (- 1) (* n n))))))
(check-sat)
";
    assert_ne!(verdict(text), CheckResult::Unsat);
}

/// A loose bound `x − y ∈ [1, 3)` does NOT pin the difference, so the
/// disequality `x − y ≠ 1` is satisfiable (`x − y = 2`). Must not be refuted.
#[test]
fn loose_bound_not_refuted() {
    let text = r"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (and (>= (- x y) 1) (not (>= (- x y) 3))))
(assert (not (= (- x y) 1)))
(check-sat)
";
    assert_ne!(verdict(text), CheckResult::Unsat);
}

/// A plain satisfiable polynomial disequality with no pinning equalities.
#[test]
fn free_disequality_not_refuted() {
    let text = r"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (not (= (* x x) (* y y))))
(check-sat)
";
    assert_ne!(verdict(text), CheckResult::Unsat);
}
