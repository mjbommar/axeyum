//! The gate map behind the nested array sort (ADR-1955).
//!
//! `crates/axeyum-ir/src/sort.rs` refuses a nested array sort at parse, and
//! four SMT-LIB divisions — AUFLIRA, ABV, ALIA, AUFNIRA — have **27,150 of
//! 29,564 files** behind that one refusal (counted over the whole population,
//! `bench-results/nested-array-ir-20260913/parse-census/`).
//!
//! That count is a BLOCKED count. Parse is the first gate of all, so it hides
//! every gate behind it by construction (ADR-1927), and a blocked count is an
//! upper bound on a reachable count (ADR-1945). ADR-1955 measured the gates
//! behind it. **This file pins that measurement so nobody has to re-derive
//! it**, and so that the day one of these gates moves, a test says so instead
//! of the frontier drifting silently.
//!
//! Each test names ONE gate. Two kinds of assertion live here and they read in
//! opposite directions:
//!
//! * `..._decides` — a capability we HAVE. A failure is a regression.
//! * `..._is_undecided` / `..._refused_at_parse` — a capability we do NOT have,
//!   and the reason a larger population is not reachable. **A failure here is
//!   good news**: the frontier moved, and ADR-1955's arithmetic is stale. The
//!   panic message says which number to redo.
//!
//! The point of the pairs is that the two sides differ in exactly one thing.
//! `flat_int_element_array_row_decides` and
//! `flat_real_element_array_row_is_undecided` are the same query with `Int`
//! swapped for `Real`; that difference alone is why AUFLIRA's 18,644 nested
//! files are not reachable by removing the parse refusal.

#![cfg(feature = "full")]

use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, check_auto};

/// Runs a quantifier-free script through the ordinary front door.
fn decide(text: &str) -> CheckResult {
    let mut script = parse_script(text).expect("script parses");
    let assertions = script.checked_flat_view().to_vec();
    check_auto(&mut script.arena, &assertions, &SolverConfig::default())
        .expect("check_auto reports a verdict rather than an error")
}

/// The read-over-write obligation at a *symbolic* index — the smallest query
/// that needs the array theory rather than constant folding. The asserted
/// formula is the negation of a tautology, so **every one of these queries is
/// unsat**; that is what lets the undecided case below distinguish "we declined"
/// from "we answered wrongly".
fn row_script(logic: &str, index: &str, element: &str) -> String {
    format!(
        "(set-logic {logic})
         (declare-fun m () (Array {index} {element}))
         (declare-fun i () {index})
         (declare-fun j () {index})
         (declare-fun v () {element})
         (assert (not (= (select (store m i v) j)
                         (ite (= i j) v (select m j)))))
         (check-sat)"
    )
}

// ---------------------------------------------------------------------------
// Gate 2a: the element sort of a FLAT array. This is the gate behind the parse
// refusal, and it is where the two halves of the blocked population separate.
// ---------------------------------------------------------------------------

/// `(Array Int Int)` — ALIA's leaf shape. The scalar Int lazy-ROW route takes
/// it, so nesting really is ALIA's first binding gate.
#[test]
fn flat_int_element_array_row_decides() {
    assert_eq!(
        decide(&row_script("QF_ALIA", "Int", "Int")),
        CheckResult::Unsat,
        "the Int-element array route is what makes ALIA's 3,028 nested files a \
         candidate population at all; if this regresses, ADR-1955's upper \
         bound of 7,530 is no longer supported"
    );
}

/// `(Array (_ BitVec 64) (_ BitVec 64))` — ABV's leaf shape, at the width its
/// benchmarks actually use (the 2023 UltimateAutomizer memory model).
#[test]
fn flat_bv64_element_array_row_decides() {
    assert_eq!(
        decide(&row_script("QF_ABV", "(_ BitVec 64)", "(_ BitVec 64)")),
        CheckResult::Unsat,
        "the BV-element array route is what makes ABV's 4,502 nested files a \
         candidate population"
    );
}

/// `(Array Int Real)` — AUFLIRA's and AUFNIRA's leaf shape, and the whole
/// reason their **19,620** nested files are not reachable by lifting the parse
/// refusal. This query has NO nested array in it: it is refused one gate
/// further down, at `scalar_alia_auflia_arrays_supported`'s `!has_real`.
#[test]
fn flat_real_element_array_row_is_undecided() {
    // The query is unsat by construction, so `Unknown` and `Sat` are NOT the
    // same finding: asserting only "not unsat" would pass on a wrong `sat`,
    // which is the failure this repository cares about most. Pin `Unknown`.
    match decide(&row_script("AUFLIRA", "Int", "Real")) {
        CheckResult::Unknown(_) => {}
        CheckResult::Unsat => panic!(
            "GOOD NEWS, STALE ARITHMETIC: a Real-element array obligation now \
             decides. ADR-1955 rules 19,620 AUFLIRA/AUFNIRA files out of the \
             nested-array-sort population BECAUSE this was undecided. \
             Re-measure that split and update the ADR, then delete this test."
        ),
        CheckResult::Sat(_) => panic!(
            "WRONG VERDICT: this query is the negation of the read-over-write \
             tautology and is unsat for every element sort. A `sat` here is a \
             soundness defect in the Real-element array path, not a frontier \
             move."
        ),
    }
}

// ---------------------------------------------------------------------------
// Gate 1: the parse refusal itself.
// ---------------------------------------------------------------------------

/// The refusal this lane was dispatched at. Both the ALIA leaf shape and the
/// ABV one, because a fix that reached only one of them would otherwise look
/// complete.
#[test]
fn nested_array_sort_is_refused_at_parse() {
    for sort in [
        "(Array Int (Array Int Int))",
        "(Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))",
    ] {
        let text = format!("(set-logic ALL) (declare-fun m () {sort}) (check-sat)");
        let err = parse_script(&text).err().unwrap_or_else(|| {
            panic!(
                "GOOD NEWS: {sort} now parses. ADR-1955's design (an \
                 interned array-sort id behind `ArraySortKey`) has landed, or \
                 something else admits it. Re-measure the reachable count and \
                 update the ADR."
            )
        });
        let message = format!("{err:?}");
        assert!(
            message.contains("nested array element sort is unsupported"),
            "{sort} is refused, but by a different gate than ADR-1955 measured: {message}"
        );
    }
}

// ---------------------------------------------------------------------------
// Gate 3: what an outer array would curry ONTO. ADR-1955 sized the no-IR-change
// alternative — represent `(Array I1 (Array I2 E))` as a function
// `I1 -> (Array I2 E)` — and these are the reason that alternative has a live
// target at all. They are also why it is NOT the recommendation: it reaches
// 0% of AUFLIRA, whose files quantify over outer arrays and pass them as
// function arguments.
// ---------------------------------------------------------------------------

/// An array-valued uninterpreted function result, Int leaf: congruence through
/// the function, then a read.
#[test]
fn array_valued_uf_result_decides_int() {
    assert_eq!(
        decide(
            "(set-logic ALL)
             (declare-fun row (Int) (Array Int Int))
             (declare-fun i () Int) (declare-fun j () Int) (declare-fun k () Int)
             (assert (= i k))
             (assert (not (= (select (row i) j) (select (row k) j))))
             (check-sat)"
        ),
        CheckResult::Unsat,
        "array-valued UF results are the curry target ADR-1955 sized; if this \
         regresses, that alternative loses its route"
    );
}

/// The same at ABV's width.
#[test]
fn array_valued_uf_result_decides_bv64() {
    assert_eq!(
        decide(
            "(set-logic ALL)
             (declare-fun row ((_ BitVec 64)) (Array (_ BitVec 64) (_ BitVec 64)))
             (declare-fun i () (_ BitVec 64))
             (declare-fun j () (_ BitVec 64))
             (declare-fun k () (_ BitVec 64))
             (assert (= i k))
             (assert (not (= (select (row i) j) (select (row k) j))))
             (check-sat)"
        ),
        CheckResult::Unsat,
        "array-valued UF results at ABV's 64-bit width"
    );
}

/// A `store` into a UF-returned array — the position an outer-level `store`
/// curries into, and the one that makes 2,649 ALIA and 1,107 ABV occurrences
/// expressible rather than just the reads.
#[test]
fn store_into_array_valued_uf_result_decides() {
    assert_eq!(
        decide(
            "(set-logic ALL)
             (declare-fun row (Int) (Array Int Int))
             (declare-fun i () Int) (declare-fun j () Int) (declare-fun v () Int)
             (assert (not (= (select (store (row i) j v) j) v)))
             (check-sat)"
        ),
        CheckResult::Unsat,
        "without this, currying could express only the outer reads"
    );
}
