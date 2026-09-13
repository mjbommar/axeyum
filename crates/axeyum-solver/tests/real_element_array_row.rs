//! The `(Array _ Real)` element sort through the lazy ROW/extensionality CEGAR
//! (ADR-1960).
//!
//! Until `57bd22d37` a flat read-over-write over a Real-element array came back
//! `unknown` while the identical query over `Int` or `(_ BitVec 64)` came back
//! `unsat`. Three sequential gates produced that, and only the third was known:
//!
//! 1. `auto.rs`, the pure-real branch — `check_with_nra` refuses a `select`
//!    subterm and the `Err(Unsupported)` arm **returned** that refusal as the
//!    query's verdict, so the array ladder below was unreachable.
//! 2. `dispatch_uf_routes` — `uf-arithmetic`'s `Unknown` was returned early
//!    whenever `has_real`, for the same reason and with the same effect.
//! 3. `scalar_alia_auflia_arrays_supported` — `!features.has_real`, which
//!    [ADR-1955] measured and which nothing had ever argued for.
//!
//! This suite is the soundness half of lifting them. It is deliberately NOT a
//! capability ratchet: every test here either pins a verdict **both** reference
//! solvers agree with, or is an adversarial fixture over a **satisfiable**
//! query whose wrong answer would be `unsat`.
//!
//! The rule this file exists to enforce: **a query that used to decline and now
//! returns a wrong verdict is far worse than one that declines.** So the
//! `Sat` cases replay the returned model against the ORIGINAL assertions inside
//! the test, rather than trusting the route's own replay — a checker that
//! cannot fail is worse than no checker, and the route's replay is the thing
//! under test.
//!
//! [ADR-1955]: ../../../docs/research/09-decisions/adr-1955-the-nested-array-sort-is-the-first-of-three-gates-and-the-only-one-the-ir-owns.md

#![cfg(feature = "full")]

use axeyum_ir::{Value, eval};
use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, check_auto};

/// Runs a quantifier-free script through the ordinary front door and, for a
/// `Sat`, **replays the model against the original assertions here**.
///
/// A `Sat` whose model does not satisfy every original assertion fails the test
/// rather than being reported, because that is the failure mode this whole
/// change is fenced against: the route's own replay is part of the subject.
fn decide(text: &str) -> CheckResult {
    let mut script = parse_script(text).expect("script parses");
    let assertions = script.checked_flat_view().to_vec();
    let result = check_auto(&mut script.arena, &assertions, &SolverConfig::default())
        .expect("check_auto reports a verdict rather than an error");
    if let CheckResult::Sat(model) = &result {
        let assignment = model.to_assignment();
        for (n, &assertion) in assertions.iter().enumerate() {
            let value = eval(&script.arena, assertion, &assignment);
            assert!(
                matches!(value, Ok(Value::Bool(true))),
                "WRONG SAT: assertion {n} evaluates to {value:?} under the returned model, \
                 not `true`. The Real-element array route returned a model that does not \
                 satisfy the original query."
            );
        }
    }
    result
}

// ---------------------------------------------------------------------------
// The unsat side. Each of these is a read-over-write obligation the SMT-LIB
// array theory forces, and z3 4.13.3 and cvc5 1.3.4 both answer `unsat`
// (re-run 2026-09-13, `z3 -T:24` / `cvc5 --tlimit 24000`).
// ---------------------------------------------------------------------------

/// The obligation the whole lane turns on: read-over-write at a **distinct**
/// symbolic index, `(Array Int Real)`.
///
/// The distinct index is load-bearing. With the same symbol on both sides the
/// query folds and is decided either way, so it cannot tell the array theory
/// from constant propagation.
#[test]
fn flat_real_row_at_distinct_indices_is_unsat() {
    assert_eq!(
        decide(
            "(set-logic AUFLIRA)
             (declare-fun m () (Array Int Real))
             (declare-fun i () Int) (declare-fun j () Int) (declare-fun v () Real)
             (assert (not (= (select (store m i v) j) (ite (= i j) v (select m j)))))
             (check-sat)"
        ),
        CheckResult::Unsat,
        "the read-over-write axiom is a tautology for EVERY element sort; this is \
         the query ADR-1955 measured as `unknown` and ADR-1960 lifted"
    );
}

/// Select congruence over a Real element sort: equal indices, equal reads.
#[test]
fn real_select_congruence_is_unsat() {
    assert_eq!(
        decide(
            "(set-logic AUFLIRA)
             (declare-fun m () (Array Int Real))
             (declare-fun i () Int) (declare-fun j () Int)
             (assert (= i j))
             (assert (not (= (select m i) (select m j))))
             (check-sat)"
        ),
        CheckResult::Unsat,
        "congruence must hold through a Real-element read"
    );
}

/// Store-then-read at the written index, with the value constrained to a
/// **non-integer** rational so an Int-shaped abstraction of the element could
/// not produce this refutation by accident.
#[test]
fn real_store_readback_at_a_rational_is_unsat() {
    assert_eq!(
        decide(
            "(set-logic AUFLIRA)
             (declare-fun m () (Array Int Real))
             (declare-fun i () Int) (declare-fun v () Real)
             (assert (= v (/ 1.0 3.0)))
             (assert (not (= (select (store m i v) i) v)))
             (check-sat)"
        ),
        CheckResult::Unsat,
        "store-then-read at the same index returns the written value"
    );
}

// ---------------------------------------------------------------------------
// The soundness-negative side: SATISFIABLE queries whose plausible wrong answer
// is `unsat`. These are the tests that die if the element sort is mishandled.
// `Unknown` is accepted (a decline is not a defect); `Unsat` is the failure.
// ---------------------------------------------------------------------------

/// **The element sort discriminator.** `0 < m[i] < 1` is satisfiable over
/// `Real` and UNSATISFIABLE over `Int`.
///
/// This is the single most important test in the file: the route abstracts each
/// `select` to a fresh symbol *at the element sort*, and if anything on the new
/// path were to treat that symbol as an integer — a fallback to the bounded
/// integer blast, an `ArraySortKey` collapsed to `Int`, a scalar backend that
/// silently integralizes — the answer would be a wrong `unsat`. z3 and cvc5
/// both answer `sat`.
#[test]
fn a_strictly_fractional_read_is_satisfiable_over_reals() {
    let result = decide(
        "(set-logic AUFLIRA)
         (declare-fun m () (Array Int Real))
         (declare-fun i () Int)
         (assert (> (select m i) 0.0))
         (assert (< (select m i) 1.0))
         (check-sat)",
    );
    assert!(
        !matches!(result, CheckResult::Unsat),
        "WRONG UNSAT: `0 < m[i] < 1` is satisfiable over Real (m[i] = 1/2) and \
         unsatisfiable only over Int. An `unsat` here means the Real element sort \
         was integralized somewhere on the array route. Got {result:?}"
    );
}

/// A store at `i` read at `j` with **no** disequality asserted: satisfiable,
/// because `i = j` is allowed and then the read is `v`.
///
/// A route that dropped the `ite` from read-over-write — keeping only the
/// "different index, unchanged" leg — would answer `unsat`.
#[test]
fn an_unconstrained_index_pair_does_not_force_the_read_to_agree() {
    let result = decide(
        "(set-logic AUFLIRA)
         (declare-fun m () (Array Int Real))
         (declare-fun i () Int) (declare-fun j () Int) (declare-fun v () Real)
         (assert (not (= (select (store m i v) j) (select m j))))
         (check-sat)",
    );
    assert!(
        !matches!(result, CheckResult::Unsat),
        "WRONG UNSAT: with `i` and `j` unconstrained the write is visible at `j` \
         whenever `i = j`, so this is satisfiable. An `unsat` means the \
         read-over-write case split was lost. Got {result:?}"
    );
}

/// Two reads of the same array at indices asserted **distinct** may take
/// different Real values. A route that Ackermannized without the index guard
/// would force them equal and answer `unsat`.
#[test]
fn distinct_indices_may_read_different_reals() {
    let result = decide(
        "(set-logic AUFLIRA)
         (declare-fun m () (Array Int Real))
         (declare-fun i () Int) (declare-fun j () Int)
         (assert (not (= i j)))
         (assert (not (= (select m i) (select m j))))
         (check-sat)",
    );
    assert!(
        !matches!(result, CheckResult::Unsat),
        "WRONG UNSAT: distinct indices impose nothing on the two reads. Got {result:?}"
    );
}

/// The mixed `QF_ALIRA` shape: a Real element and an Int index constrained
/// together. Satisfiable, and the witness needs a genuine rational.
#[test]
fn a_mixed_int_index_real_element_query_is_satisfiable() {
    let result = decide(
        "(set-logic AUFLIRA)
         (declare-fun m () (Array Int Real))
         (declare-fun i () Int)
         (assert (> i 2))
         (assert (< i 4))
         (assert (= (select m i) (/ 7.0 2.0)))
         (check-sat)",
    );
    assert!(
        !matches!(result, CheckResult::Unsat),
        "WRONG UNSAT: `i = 3` with `m[3] = 7/2` satisfies this. Got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// The no-Real controls. These must be unaffected by ADR-1960 in either
// direction: a test suite for a relaxation that never runs the un-relaxed case
// cannot tell a lifted gate from a broken one.
// ---------------------------------------------------------------------------

/// The same read-over-write obligation with an `Int` element — decided before
/// ADR-1960 and after it, by the same route.
#[test]
fn flat_int_row_at_distinct_indices_is_still_unsat() {
    assert_eq!(
        decide(
            "(set-logic QF_ALIA)
             (declare-fun m () (Array Int Int))
             (declare-fun i () Int) (declare-fun j () Int) (declare-fun v () Int)
             (assert (not (= (select (store m i v) j) (ite (= i j) v (select m j)))))
             (check-sat)"
        ),
        CheckResult::Unsat,
        "the Int element route is the control; a failure here is a regression, not \
         a frontier move"
    );
}

/// The Int-element mirror of `a_strictly_fractional_read_is_satisfiable_over_reals`:
/// over `Int` the same constraint IS unsatisfiable. Without this row the Real
/// test above would pass for a route that answers `sat` for everything.
#[test]
fn a_strictly_fractional_read_is_unsatisfiable_over_ints() {
    assert_eq!(
        decide(
            "(set-logic QF_ALIA)
             (declare-fun m () (Array Int Int))
             (declare-fun i () Int)
             (assert (> (select m i) 0))
             (assert (< (select m i) 1))
             (check-sat)"
        ),
        CheckResult::Unsat,
        "`0 < m[i] < 1` has no INTEGER solution; if this is not `unsat`, the pair \
         with the Real row above proves nothing about the element sort"
    );
}
