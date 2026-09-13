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
//! **ADR-1965 moved gate 1.** `(Array I (Array J E))` now parses: the component
//! is an arena-interned [`axeyum_ir::ArraySortId`] behind
//! `ArraySortKey::Array`. What that reached, and what it did not, is measured in
//! that ADR; the tests below are re-pointed at the gate that is now FIRST for a
//! nested query, which is the array THEORY, not the sort.
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
//! swapped for `Real`.
//!
//! ADR-1955 read that pair as ruling AUFLIRA's 18,644 nested files out of the
//! nested-array population. ADR-1960 refuted the arithmetic (the two counts
//! were one population counted twice) and ADR-1965 refuted the conclusion by
//! measurement: **a nested AUFLIRA query does not need the array theory at
//! all.** Its refutation runs on congruence through the nested `select`, which
//! is why `nested_select_congruence_decides` below is `..._decides` while every
//! nested query that needs read-over-write or extensionality is still
//! `..._is_undecided`.

#![cfg(feature = "full")]

use axeyum_ir::Sort;
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
/// benchmarks actually use (the 2023 `UltimateAutomizer` memory model).
#[test]
fn flat_bv64_element_array_row_decides() {
    assert_eq!(
        decide(&row_script("QF_ABV", "(_ BitVec 64)", "(_ BitVec 64)")),
        CheckResult::Unsat,
        "the BV-element array route is what makes ABV's 4,502 nested files a \
         candidate population"
    );
}

/// `(Array Int Real)` — AUFLIRA's and AUFNIRA's leaf shape.
///
/// **This row moved on 2026-09-13 and the panic that predicted it fired.** It
/// was `flat_real_element_array_row_is_undecided`, pinning `Unknown` with a
/// "GOOD NEWS, STALE ARITHMETIC" message naming the number to re-measure.
/// [ADR-1960](../../../docs/research/09-decisions/adr-1960-the-real-element-array-gate-was-three-gates-and-none-of-the-19620-were-behind-it.md)
/// is that re-measurement: the gate was three sequential gates, only the third
/// of which ADR-1955 had found, and the 19,620 figure was a BLOCKED count whose
/// reachable part — measured over all 29,564 files with the census in
/// `bench-results/array-real-gate-20260913/` — is **zero**, because every one of
/// those files is still behind the parse refusal this file's Gate 1 pins.
///
/// The row is kept rather than deleted because the pair is what carries the
/// meaning: `flat_int_element_array_row_decides` and this test are the same
/// query with `Int` swapped for `Real`, and they now agree. If they ever stop
/// agreeing again, that is the same finding in the other direction.
/// `crates/axeyum-solver/tests/real_element_array_row.rs` carries the soundness
/// fixtures for the route this now takes.
#[test]
fn flat_real_element_array_row_decides() {
    match decide(&row_script("AUFLIRA", "Int", "Real")) {
        CheckResult::Unsat => {}
        CheckResult::Unknown(reason) => panic!(
            "REGRESSION: the Real-element read-over-write obligation has stopped \
             deciding. ADR-1960 lifted three gates to reach it (the pure-real \
             `nra` early return, `uf-arithmetic`'s `has_real` early return, and \
             `scalar_alia_auflia_arrays_supported`'s `!has_real`); one of them is \
             back, or the route behind them has narrowed: {reason:?}"
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
// Gate 1: the parse refusal itself. LIFTED by ADR-1965.
// ---------------------------------------------------------------------------

/// The refusal this file's first version was dispatched at, now the other way
/// round. Both the ALIA leaf shape and the ABV one, because a fix reaching only
/// one of them would otherwise look complete; and the AUFLIRA shape, which is
/// 91% of ADR-1957's 20,399-file ceiling and was not in the original pair.
///
/// This test flipped from `nested_array_sort_is_refused_at_parse`. It is kept
/// rather than deleted because the *sort round-tripping* is the property that
/// makes the parse admissible at all: an interned component that cannot be
/// expanded back is how a nested query would get a wrong sort rather than a
/// refusal.
#[test]
fn nested_array_sort_parses_and_round_trips() {
    for sort in [
        "(Array Int (Array Int Int))",
        "(Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))",
        "(Array Int (Array Int Real))",
    ] {
        let text = format!("(set-logic ALL) (declare-fun m () {sort}) (check-sat)");
        let script = parse_script(&text).unwrap_or_else(|e| {
            panic!(
                "REGRESSION: {sort} no longer parses ({e:?}). ADR-1965 admits a \
                 nested array component as an arena-interned `ArraySortId`; \
                 without it AUFLIRA/ALIA/ABV/AUFNIRA go back to 0 at ingest."
            )
        });
        let symbol = script
            .arena
            .find_symbol("m")
            .expect("the declared symbol is in the arena");
        let (_, declared) = script.arena.symbol(symbol);
        let Sort::Array { element, .. } = declared else {
            panic!("{sort} did not parse to an array sort: {declared}");
        };
        // The component is interned, so the arena-free helper MUST refuse it —
        // that `None` is what keeps every pre-nesting route conservative by
        // construction rather than by audit (ADR-1965).
        assert!(
            element.to_sort().is_none(),
            "{sort}: the nested element expanded WITHOUT the arena. Every route \
             that predates nesting refuses because `ArraySortKey::to_sort` and \
             `Sort::array_sorts` return `None`; if this expands, those routes \
             silently accept a sort they cannot reason about."
        );
        assert!(
            script.arena.sort_has_nested_array(declared),
            "{sort} parsed but is not reported as nested; `Features::note_sort` \
             reads this and would mis-route the query"
        );
        // And the arena-aware expansion round-trips to the written form.
        let expanded = script.arena.array_key_sort(element);
        assert!(
            matches!(expanded, Sort::Array { .. }),
            "{sort}: the interned component expanded to {expanded}, not an array"
        );
    }
}

/// The gate that is FIRST for a nested query now that the sort parses:
/// congruence through a nested `select`. `i = j` forces `m[i][k] = m[j][k]`,
/// with no read-over-write and no extensionality anywhere.
///
/// This is the capability ADR-1965 measured as the whole of the AUFLIRA and
/// AUFNIRA reach: 86.5% of the winnable set of those divisions has a refutation
/// that needs exactly this and nothing else
/// (`bench-results/nested-array-build-20260913/`).
#[test]
fn nested_select_congruence_decides() {
    for element in ["Int", "Real"] {
        let text = format!(
            "(set-logic ALL)
             (declare-fun m () (Array Int (Array Int {element})))
             (declare-fun i () Int) (declare-fun j () Int) (declare-fun k () Int)
             (assert (= i j))
             (assert (not (= (select (select m i) k) (select (select m j) k))))
             (check-sat)"
        );
        assert_eq!(
            decide(&text),
            CheckResult::Unsat,
            "congruence through a nested select over {element} is the ONLY array \
             property AUFLIRA's nested files need; ADR-1965's reach measurement \
             rests on it"
        );
    }
}

// ---------------------------------------------------------------------------
// Gate 2b: the array THEORY at a nested level. This is the gate that is binding
// for ALIA and ABV now that the sort parses, and it is why ADR-1965's reach
// measurement says nothing about their 511 + 423: 33 of 36 ALIA and 12 of 17
// ABV winnable files WRITE to the outer array, so read-over-write at the outer
// level is load-bearing for them.
// ---------------------------------------------------------------------------

/// Read-over-write at the OUTER level of a nested array. This is unsat by
/// construction (it is the negation of the array axiom), so `Unknown` and `Sat`
/// are different findings and `Unknown` is what gets pinned.
#[test]
fn outer_read_over_write_on_a_nested_array_is_undecided() {
    let text = "(set-logic ALL)
         (declare-fun m () (Array Int (Array Int Int)))
         (declare-fun r () (Array Int Int))
         (declare-fun i () Int) (declare-fun j () Int)
         (assert (not (= (select (store m i r) j) (ite (= i j) r (select m j)))))
         (check-sat)";
    match decide(text) {
        CheckResult::Unknown(_) => {}
        CheckResult::Unsat => panic!(
            "GOOD NEWS, STALE ARITHMETIC: outer read-over-write on a nested \
             array now decides. ADR-1965 rules ALIA's 511 and ABV's 423 out of \
             the measured reach BECAUSE this was undecided (their winnable \
             files write the outer array). Re-measure \
             `bench-results/nested-array-build-20260913/` with the surrogate's \
             `outer-level store` refusal lifted, and update ADR-1965."
        ),
        CheckResult::Sat(_) => panic!(
            "WRONG VERDICT: this query is the negation of the read-over-write \
             tautology and is unsat for every element sort, nested included. A \
             `sat` here is a soundness defect on the nested-array path."
        ),
    }
}

/// The INNER level's read-over-write, reached through an outer `select`. The
/// inner array is a perfectly ordinary `(Array Int Int)` — the only thing
/// nested about this query is that its base came out of an outer read.
#[test]
fn inner_read_over_write_under_an_outer_select_is_undecided() {
    let text = "(set-logic ALL)
         (declare-fun m () (Array Int (Array Int Int)))
         (declare-fun i () Int) (declare-fun j () Int)
         (declare-fun v () Int) (declare-fun p () Int)
         (assert (not (= (select (store (select m p) i v) j)
                         (ite (= i j) v (select (select m p) j)))))
         (check-sat)";
    match decide(text) {
        CheckResult::Unknown(_) => {}
        CheckResult::Unsat => panic!(
            "GOOD NEWS, STALE ARITHMETIC: read-over-write on an INNER array \
             whose base is an outer select now decides. This is the shape \
             ADR-1955 attributed to `RowCtx::resolve_select` having no arm for \
             an array-valued base that is itself a `Select`; re-measure and \
             update ADR-1965."
        ),
        CheckResult::Sat(_) => panic!(
            "WRONG VERDICT: unsat by construction (read-over-write), so a `sat` \
             is a soundness defect, not a frontier move."
        ),
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
