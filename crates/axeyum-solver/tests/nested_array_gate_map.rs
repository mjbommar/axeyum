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
//!
//! **ADR-1971 sized the gate this file named as next, and it is worth zero.**
//! `outer_read_over_write_on_a_nested_array_is_undecided` was ADR-1965's
//! nominated frontier, holding ALIA's 511 files and ABV's 423. A surrogate that
//! curries the outer array and performs read-over-write syntactically hands the
//! solver that capability with the nested sort removed entirely, and axeyum
//! still answers `unknown` on 18 of 18 accepted ALIA files. The reason is not
//! the array theory: **39 of the 53 winnable ALIA + ABV files are SATISFIABLE**,
//! and read-over-write is a refutation mechanism, so the gate's ceiling is 220
//! files rather than 934 before reach is measured at all. The two rows those
//! numbers came from are at the bottom of this file, and they are the in-repo
//! form of the sizing's own non-vacuity controls
//! (`bench-results/nested-array-outer-row-20260913/controls/`).

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
///
/// **[ADR-1971](../../../docs/research/09-decisions/adr-1971-outer-read-over-write-is-worth-zero-alia-and-abv-are-held-by-satisfiability.md)
/// measured what moving this is worth, and the answer is zero.** A surrogate
/// that curries the outer array and performs this axiom syntactically — so the
/// solver gets the capability for free, with the nested sort removed entirely —
/// still leaves axeyum at `unknown` on 18 of 18 accepted ALIA files and 8 of 9
/// accepted ABV files. Sharper: 5 ALIA files are refutable AND inside the
/// fragment AND had read-over-write performed for them, and axeyum decided 0 of
/// 5. And the ceiling is 220 rather than 934 before reach is even measured,
/// because **39 of the 53 winnable ALIA+ABV files are satisfiable** and this is
/// a refutation mechanism.
///
/// So the test stays, and stays `..._is_undecided`, but its GOOD NEWS message
/// no longer points at ADR-1965's 511 + 423: moving this row is a capability
/// gain with no measured benchmark gain behind it.
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
            "GOOD NEWS: outer read-over-write on a nested array now decides. \
             Re-run `bench-results/nested-array-outer-row-20260913/sweep.sh` on \
             the ALIA and ABV winnable lists and update ADR-1971 with the \
             number. Expect a SMALL one: ADR-1971 handed this capability to the \
             solver for free through a currying surrogate and measured 0 of 5 \
             refutable-and-accepted ALIA files, with the whole gate's ceiling at \
             220 because 39 of 53 winnable ALIA+ABV files are SATISFIABLE and \
             read-over-write cannot produce a `sat`."
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
            "GOOD NEWS: read-over-write on an INNER array whose base is an outer \
             select now decides. This is the shape ADR-1955 attributed to \
             `RowCtx::resolve_select` having no arm for an array-valued base \
             that is itself a `Select`; re-measure with \
             `bench-results/nested-array-outer-row-20260913/` and update \
             ADR-1971, whose reach table is what a new number replaces."
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

// ---------------------------------------------------------------------------
// ADR-1971: what the outer-read-over-write sizing actually found. These two
// rows are the in-repo form of the surrogate's `controls/c1` and `controls/c2`,
// and together they say WHERE the capability stops: not at read-over-write
// itself, which we have, but at reaching it through the nested sort — and then
// at one rewrite that `eliminate_arrays` owns and these queries do not enter.
// ---------------------------------------------------------------------------

/// The **curried** form of `outer_read_over_write_on_a_nested_array_is_undecided`:
/// the same obligation with the outer array replaced by a function
/// `row : Int -> (Array Int Int)` and the outer `store` expanded by hand into
/// the `ite` the read-over-write axiom produces.
///
/// This is `controls/c1-outer-row-refutation.smt2` of
/// `bench-results/nested-array-outer-row-20260913/`, and it is what makes
/// ADR-1971's zeroes readable rather than vacuous: the sizing instrument
/// refuses AUFLIRA 187/187 and AUFNIRA 139/139, so without a fixture the
/// solver DOES decide, "reach 0 on ALIA" would be indistinguishable from an
/// instrument that cannot reach anything.
///
/// A failure here is a regression that silently invalidates ADR-1971's reach
/// table, because the table is read as "the solver had the capability and the
/// files still did not decide".
#[test]
fn outer_read_over_write_decides_once_the_outer_array_is_curried() {
    assert_eq!(
        decide(
            "(set-logic ALL)
             (declare-fun row (Int) (Array Int Int))
             (declare-fun r () (Array Int Int))
             (declare-fun i () Int) (declare-fun j () Int) (declare-fun o () Int)
             (assert (= i j))
             (assert (not (= (select (ite (= i j) r (row j)) o) (select r o))))
             (check-sat)"
        ),
        CheckResult::Unsat,
        "ADR-1971's reach measurement reads its zeroes as a statement about the \
         ALIA and ABV populations. That reading requires the solver to decide \
         the curried read-over-write obligation the surrogate hands it; if this \
         regresses, the zeroes become a statement about the solver instead and \
         the ADR's table must be re-derived."
    );
}

/// The DISJOINT-index half of the same obligation, curried the same way — and
/// we answer `unknown` on it.
///
/// This is `controls/c2-outer-row-disjoint-index.smt2`, and the reason it is
/// pinned separately from the row above is that the pair localizes the gap to
/// one rewrite. The query is unsat because `i != j` makes the `ite` take its
/// else branch, leaving both sides identical. Writing the same query with
/// `select` pushed through the array-sorted `ite` by hand — that is,
/// `(ite (= i j) (select r o) (select (row j) o))` — gives `Unsat`. So what is
/// missing is select-over-`ite` on an array-sorted `ite` whose branch is a
/// UF-returned row, a rewrite `crates/axeyum-rewrite/src/arrays.rs` already
/// has and this query does not reach.
///
/// ADR-1971 sized closing it, by running the whole sweep with the `select`
/// pushed through for every file: **+0 on ALIA and +0 on ABV**. So this row is
/// pinned as a capability gap with a measured price of zero benchmark files,
/// not as a task.
#[test]
fn select_through_an_array_ite_on_a_uf_returned_row_is_undecided() {
    let text = "(set-logic ALL)
         (declare-fun row (Int) (Array Int Int))
         (declare-fun r () (Array Int Int))
         (declare-fun i () Int) (declare-fun j () Int) (declare-fun o () Int)
         (assert (not (= i j)))
         (assert (not (= (select (ite (= i j) r (row j)) o) (select (row j) o))))
         (check-sat)";
    match decide(text) {
        CheckResult::Unknown(_) => {}
        CheckResult::Unsat => panic!(
            "GOOD NEWS: `select` now distributes through an array-sorted `ite` \
             whose branch is a UF-returned row. ADR-1971 measured that closing \
             this is worth +0 on ALIA and +0 on ABV (the `--distribute` arm of \
             `bench-results/nested-array-outer-row-20260913/`), so this is a \
             capability gain rather than a frontier move — but re-run that arm \
             before quoting the old number, and flip this row to \
             `..._decides`."
        ),
        CheckResult::Sat(_) => panic!(
            "WRONG VERDICT: `i != j` forces the `ite` to its else branch, so \
             both sides of the disequality are the same term and this query is \
             unsat. A `sat` is a soundness defect on the array-`ite` path, not \
             a frontier move."
        ),
    }
}
