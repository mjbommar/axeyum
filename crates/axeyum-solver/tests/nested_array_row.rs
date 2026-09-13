//! The soundness fence around admitting a nested array sort (ADR-1965).
//!
//! `crates/axeyum-ir/src/sort.rs` refused `(Array I (Array J E))` at parse until
//! ADR-1965 interned the component behind `ArraySortKey::Array(ArraySortId)`.
//! Four SMT-LIB divisions — AUFLIRA, ABV, ALIA, AUFNIRA — had **27,150 of
//! 29,564 files** behind that one refusal, so this is the widest single
//! population any change in this repository has ever admitted at once.
//!
//! **A file that now parses and then gets a WRONG verdict is far worse than one
//! that refused at ingest.** This suite is the fence against that, and it is
//! deliberately NOT a capability ratchet: what it pins is what we must never
//! answer, not how much we decide.
//!
//! ## Why the assertions read `!= Unsat` / `!= Sat` rather than a verdict
//!
//! Admitting the sort does not add an array *decision procedure* for it. Every
//! array route reaches its components through `Sort::array_sorts`, which
//! returns `None` for a nested sort, so each one declines by construction. What
//! survives is congruence through the nested `select` — which is exactly the
//! reach ADR-1965 measured, and exactly nothing more.
//!
//! So most of these queries come back `Unknown`, and `Unknown` is the correct
//! answer to pin for a route that does not exist. Pinning a verdict instead
//! would make this file a frontier ratchet that goes red on progress. What each
//! test forbids is the ONE answer that would be wrong:
//!
//! * a satisfiable query must never come back `Unsat`;
//! * an unsatisfiable query must never come back `Sat`;
//! * every `Sat` is replayed against the ORIGINAL assertions **inside the
//!   test**, because the route's own replay is part of the subject.
//!
//! ## Why this cannot read as "a solver that answers `unknown` to everything"
//!
//! Three things, and they have to hold together:
//!
//! 1. `nested_select_congruence_is_unsat` and its BV twin are POSITIVE
//!    controls — they must return `Unsat`. A solver stuck on `Unknown` fails
//!    them.
//! 2. The `Real`/`Int` fractional pair is the same query one token apart, and
//!    the two halves forbid OPPOSITE answers: the `Real` half is satisfiable
//!    (`0 < m[i][j] < 1`) and must not be `Unsat`; the `Int` half is
//!    unsatisfiable and must not be `Sat`. A solver that answers `unsat` to
//!    everything fails the first; one that answers `sat` to everything fails
//!    the second.
//! 3. `flat_row_still_decides_beside_a_nested_declaration` fixes the other
//!    direction of regression: a flat array in the SAME script as a nested
//!    declaration must still be decided, so admitting the sort cannot be paid
//!    for by quietly declining everything near it.
//!
//! Verdicts below marked "z3 and cvc5 agree" were re-run 2026-09-13 with
//! `z3 -T:15` and `cvc5 --tlimit=15000`.

#![cfg(feature = "full")]

use axeyum_ir::{Sort, Value, eval};
use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, check_auto};

/// Runs a script through the ordinary front door and, for a `Sat`, **replays
/// the model against the original assertions here**.
///
/// A `Sat` whose model does not satisfy every original assertion fails the test
/// rather than being reported: the route's own replay is part of what admitting
/// a nested sort puts at risk, so it cannot be the thing that clears it.
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
                 not `true`. A nested-array query returned a model that does not satisfy \
                 the original assertions."
            );
        }
    }
    result
}

/// Asserts that a **satisfiable** query does not come back `Unsat`.
fn refute_is_forbidden(what: &str, text: &str) {
    let result = decide(text);
    assert!(
        !matches!(result, CheckResult::Unsat),
        "WRONG UNSAT on {what}: this query is SATISFIABLE (z3 and cvc5 both \
         answer `sat`). Returning `unsat` means something on the nested-array \
         path derived a contradiction that the array theory does not license. \
         `Unknown` is the correct answer while no nested array route exists; a \
         verdict here has to be the right one."
    );
}

/// Asserts that an **unsatisfiable** query does not come back `Sat`.
fn model_is_forbidden(what: &str, text: &str) {
    let result = decide(text);
    assert!(
        !matches!(result, CheckResult::Sat(_)),
        "WRONG SAT on {what}: this query is UNSATISFIABLE (z3 and cvc5 both \
         answer `unsat`). A `sat` means a model was built for a nested array \
         that the array theory forbids."
    );
}

// ---------------------------------------------------------------------------
// Positive controls: what admitting the sort actually bought.
// ---------------------------------------------------------------------------

/// Congruence through a nested `select`: `i = j` forces `m[i][k] = m[j][k]`.
///
/// This is the whole capability the parse lift delivers, and ADR-1965's reach
/// measurement rests on it: 86.5% of the AUFLIRA/AUFNIRA winnable set has a
/// refutation that needs this and no other array property. z3 and cvc5 agree
/// (`unsat`).
#[test]
fn nested_select_congruence_is_unsat() {
    assert_eq!(
        decide(
            "(set-logic ALL)
             (declare-fun m () (Array Int (Array Int Real)))
             (declare-fun i () Int) (declare-fun j () Int) (declare-fun k () Int)
             (assert (= i j))
             (assert (not (= (select (select m i) k) (select (select m j) k))))
             (check-sat)"
        ),
        CheckResult::Unsat,
        "congruence through a nested select is the capability ADR-1965 admits \
         the sort FOR; if this regresses the reach measurement is void"
    );
}

/// The same at ABV's width, so a fix reaching only the `Int`-indexed shape does
/// not look complete. z3 and cvc5 agree (`unsat`).
#[test]
fn nested_select_congruence_is_unsat_bv64() {
    assert_eq!(
        decide(
            "(set-logic ALL)
             (declare-fun m () (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))))
             (declare-fun i () (_ BitVec 64))
             (declare-fun j () (_ BitVec 64))
             (declare-fun k () (_ BitVec 64))
             (assert (= i j))
             (assert (not (= (select (select m i) k) (select (select m j) k))))
             (check-sat)"
        ),
        CheckResult::Unsat,
        "ABV's nested shape is `(Array (_ BitVec 64) (Array (_ BitVec 64) _))`"
    );
}

/// A flat array in the same script as a nested declaration must still decide.
///
/// This is the regression direction the rest of the file cannot see: admitting
/// the nested sort must not be paid for by the flat routes declining whenever a
/// nested sort is anywhere in the arena. z3 and cvc5 agree (`unsat`).
#[test]
fn flat_row_still_decides_beside_a_nested_declaration() {
    assert_eq!(
        decide(
            "(set-logic ALL)
             (declare-fun nested () (Array Int (Array Int Int)))
             (declare-fun m () (Array Int Int))
             (declare-fun i () Int) (declare-fun j () Int) (declare-fun v () Int)
             (assert (not (= (select (store m i v) j) (ite (= i j) v (select m j)))))
             (check-sat)"
        ),
        CheckResult::Unsat,
        "the flat read-over-write route must survive a nested declaration \
         sitting beside it in the same arena"
    );
}

// ---------------------------------------------------------------------------
// The adversarial half: satisfiable queries whose wrong answer is `unsat`.
// ---------------------------------------------------------------------------

/// `0 < m[i][j] < 1` over a `Real` leaf, two nesting levels down.
///
/// Satisfiable over `Real` and **unsatisfiable over `Int`** — its twin is the
/// next test, in this file, so the pair cannot read as a solver that answers
/// one thing to everything. This is the test that dies if anything on the newly
/// reachable path integralizes a leaf sort it reached through an interned
/// component: `ArraySortKey::to_sort()` returns `None` for a nested component,
/// and a caller that papered over that `None` with a default would land here.
/// z3 and cvc5 agree (`sat`).
#[test]
fn a_strictly_fractional_nested_read_is_satisfiable_over_reals() {
    refute_is_forbidden(
        "a strictly fractional nested read over Real",
        "(set-logic ALL)
         (declare-fun m () (Array Int (Array Int Real)))
         (declare-fun i () Int) (declare-fun j () Int)
         (assert (< 0.0 (select (select m i) j)))
         (assert (< (select (select m i) j) 1.0))
         (check-sat)",
    );
}

/// The `Int` twin of the test above: the same query with `Real` swapped for
/// `Int`, which makes it unsatisfiable. z3 and cvc5 agree (`unsat`).
#[test]
fn a_strictly_fractional_nested_read_is_unsatisfiable_over_ints() {
    model_is_forbidden(
        "a strictly fractional nested read over Int",
        "(set-logic ALL)
         (declare-fun m () (Array Int (Array Int Int)))
         (declare-fun i () Int) (declare-fun j () Int)
         (assert (< 0 (select (select m i) j)))
         (assert (< (select (select m i) j) 1))
         (check-sat)",
    );
}

/// Two outer rows read at the same inner index may hold different values.
///
/// Nothing constrains `i` and `j` to be equal, so a model exists. An `unsat`
/// here would mean the outer level collapsed — every outer index reaching the
/// same row — which is what a flattening that loses the outer index looks like
/// from outside. z3 and cvc5 agree (`sat`).
#[test]
fn distinct_outer_rows_may_read_different_values() {
    refute_is_forbidden(
        "two outer rows at one inner index",
        "(set-logic ALL)
         (declare-fun m () (Array Int (Array Int Real)))
         (declare-fun i () Int) (declare-fun j () Int) (declare-fun k () Int)
         (assert (= (select (select m i) k) 1.0))
         (assert (= (select (select m j) k) 2.0))
         (check-sat)",
    );
}

/// `m[i][j]` and `m[j][i]` are different reads.
///
/// A flattening that keys the nested read on the *unordered* index pair — or
/// one that interns the two `select` applications as one term because their
/// argument multiset matches — makes this unsat. It is satisfiable: the two
/// reads are independent for `i != j`. z3 and cvc5 agree (`sat`).
#[test]
fn a_transposed_nested_read_is_independent() {
    refute_is_forbidden(
        "m[i][j] against m[j][i]",
        "(set-logic ALL)
         (declare-fun m () (Array Int (Array Int Real)))
         (declare-fun i () Int) (declare-fun j () Int)
         (assert (not (= i j)))
         (assert (= (select (select m i) j) 1.0))
         (assert (= (select (select m j) i) 2.0))
         (check-sat)",
    );
}

/// An outer `store` does not have to change a row it did not write.
///
/// `m[i := r]` read at a *different* index `j` is `m[j]`, which is
/// unconstrained, so the query is satisfiable. An `unsat` would mean the outer
/// `store` was treated as overwriting every row. z3 and cvc5 agree (`sat`).
#[test]
fn an_outer_store_leaves_other_rows_free() {
    refute_is_forbidden(
        "an outer store read at a different index",
        "(set-logic ALL)
         (declare-fun m () (Array Int (Array Int Int)))
         (declare-fun r () (Array Int Int))
         (declare-fun i () Int) (declare-fun j () Int) (declare-fun k () Int)
         (assert (not (= i j)))
         (assert (= (select (select (store m i r) j) k) 7))
         (assert (= (select r k) 9))
         (check-sat)",
    );
}

/// The outer read-over-write axiom itself, which is unsatisfiable.
///
/// The companion of the test above, so the outer `store` is fenced in both
/// directions: it may not overwrite a row it did not write, and it may not fail
/// to write the row it did. z3 and cvc5 agree (`unsat`).
#[test]
fn outer_read_over_write_may_not_be_satisfied() {
    model_is_forbidden(
        "outer read-over-write",
        "(set-logic ALL)
         (declare-fun m () (Array Int (Array Int Int)))
         (declare-fun r () (Array Int Int))
         (declare-fun i () Int) (declare-fun j () Int)
         (assert (not (= (select (store m i r) j) (ite (= i j) r (select m j)))))
         (check-sat)",
    );
}

/// A nested read whose inner base came out of an outer `select`, and whose
/// inner array is written. Unsatisfiable (read-over-write at the inner level).
/// z3 and cvc5 agree (`unsat`).
#[test]
fn inner_read_over_write_under_an_outer_select_may_not_be_satisfied() {
    model_is_forbidden(
        "inner read-over-write below an outer select",
        "(set-logic ALL)
         (declare-fun m () (Array Int (Array Int Int)))
         (declare-fun i () Int) (declare-fun j () Int)
         (declare-fun v () Int) (declare-fun p () Int)
         (assert (not (= (select (store (select m p) i v) j)
                         (ite (= i j) v (select (select m p) j)))))
         (check-sat)",
    );
}

// ---------------------------------------------------------------------------
// The IR contract the routes' conservatism rests on.
// ---------------------------------------------------------------------------

/// Every route that predates nesting refuses a nested sort **because the
/// arena-free helpers return `None`**, not because anyone audited it. This test
/// is that claim, stated where it can fail.
///
/// If `Sort::array_sorts` ever returns `Some` for a nested sort, dozens of
/// routes silently start reasoning about a component they cannot expand, and
/// every `!= Unsat` assertion above becomes the only thing standing between
/// that and a wrong verdict.
#[test]
fn the_arena_free_helpers_refuse_a_nested_sort() {
    let script = parse_script(
        "(set-logic ALL)
         (declare-fun m () (Array Int (Array Int Real)))
         (declare-fun flat () (Array Int Real))
         (check-sat)",
    )
    .expect("script parses");
    let nested = script.arena.find_symbol("m").expect("m is declared");
    let flat = script.arena.find_symbol("flat").expect("flat is declared");
    let (_, nested_sort) = script.arena.symbol(nested);
    let (_, flat_sort) = script.arena.symbol(flat);

    assert!(
        nested_sort.array_sorts().is_none(),
        "`Sort::array_sorts` expanded a NESTED array without the arena. That \
         `None` is what makes every pre-nesting array route refuse by \
         construction (ADR-1965); without it they accept a component they \
         cannot reason about."
    );
    assert!(
        nested_sort.array_widths().is_none(),
        "`Sort::array_widths` must refuse a nested sort for the same reason"
    );
    // The control: the SAME helper on a FLAT array must still answer, or the
    // assertion above would pass for a helper that refuses everything.
    assert_eq!(
        flat_sort.array_sorts(),
        Some((Sort::Int, Sort::Real)),
        "the flat control must still expand; otherwise the nested assertions \
         above are vacuous"
    );
    // And the arena-aware expansion is what a nesting-aware route would use.
    assert_eq!(
        script.arena.array_component_sorts(nested_sort),
        Some((
            Sort::Int,
            Sort::Array {
                index: axeyum_ir::ArraySortKey::Int,
                element: axeyum_ir::ArraySortKey::Real,
            }
        )),
        "`TermArena::array_component_sorts` is the nesting-aware expansion"
    );
}

/// Interning is by value: the same nested sort written twice is one id, and two
/// different nested sorts are two.
///
/// This is what lets `ArraySortKey` keep `Eq + Hash` over structural identity,
/// which `TermNode` hash-consing requires — `Op::ConstArray { index }` and
/// `Op::SeqEmpty(_)` carry an `ArraySortKey` inside the interning key. If equal
/// sorts got distinct ids, two structurally identical terms would be two terms.
#[test]
fn equal_nested_sorts_intern_to_one_id() {
    let script = parse_script(
        "(set-logic ALL)
         (declare-fun a () (Array Int (Array Int Real)))
         (declare-fun b () (Array Int (Array Int Real)))
         (declare-fun c () (Array Int (Array Int Int)))
         (check-sat)",
    )
    .expect("script parses");
    let sort_of = |name: &str| {
        let symbol = script.arena.find_symbol(name).expect("declared");
        script.arena.symbol(symbol).1
    };
    assert_eq!(
        sort_of("a"),
        sort_of("b"),
        "two declarations of the same nested sort must be the SAME `Sort`; \
         otherwise `TermNode` hash-consing splits structurally identical terms"
    );
    assert_ne!(
        sort_of("c"),
        sort_of("a"),
        "a Real leaf and an Int leaf must NOT intern to one id -- the control \
         that keeps the assertion above from passing on a degenerate interner \
         that returns a single id for everything"
    );
}
