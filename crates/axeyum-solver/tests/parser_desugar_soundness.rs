//! ADR-2010: the VERDICT half of the parser's unconditional s-expression
//! desugars (`desugar_sets`, `desugar_const_arrays`).
//!
//! # Why these verdicts are asserted HERE and not left to the model replay
//!
//! The shipped front door's replay is `check_model(&solved.script.arena,
//! &solved.assertions, model)` — a model of the assertions the PARSER produced,
//! checked against those same assertions. For these two rewrites that check is
//! not weak, it is **structurally incapable** of firing:
//!
//!  * `desugar_sets` rewrites `(Set E)` to `BitVec` **on the s-expression tree,
//!    before any term is built**. The source set terms never become IR terms at
//!    all, so there is nothing for a replay to evaluate them against. Replaying
//!    "against the originally parsed assertions" would not help either — the
//!    original parse IS the encoding.
//!  * `desugar_const_arrays` is a STRENGTHENING rewrite, and the replay only
//!    ever inspects `sat`. A rewrite that manufactures wrong `unsat` is
//!    invisible to any model replay, however that replay is implemented.
//!
//! Both shipped wrong verdicts through the default front door — no lever, no
//! feature gate — until 2026-09-14. So the verdicts below are the gate.
//!
//! # Every test here is paired with a non-vacuity control
//!
//! ADR-1976 measured that a satisfiable query is a vacuous control: an
//! underconstrained `sat` stays `sat` under a broken rewrite, so two reference
//! solvers will happily agree with a deliberately broken encoding. Each pair
//! below is therefore aimed at the direction where the defect has somewhere to
//! go, and each `unsat` expectation sits beside a query differing in ONE small
//! term that must still be `sat` — so a solver that answered `unsat` to
//! everything (or `unknown` to everything) could not pass the pair.

use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SmtLibResponse, SolverConfig, check_auto, solve_smtlib_session};

/// Parse and decide the flat assertion view.
fn verdict(src: &str) -> CheckResult {
    let mut script =
        parse_script(src).unwrap_or_else(|e| panic!("parse failed: {e:?}\n--- source ---\n{src}"));
    let assertions = script.assertions.clone();
    check_auto(&mut script.arena, &assertions, &SolverConfig::default())
        .unwrap_or_else(|e| panic!("solve failed: {e:?}\n--- source ---\n{src}"))
}

fn name(r: &CheckResult) -> &'static str {
    match r {
        CheckResult::Sat(_) => "sat",
        CheckResult::Unsat => "unsat",
        CheckResult::Unknown(_) => "unknown",
    }
}

#[track_caller]
fn assert_unsat(label: &str, src: &str) {
    let got = verdict(src);
    assert!(
        matches!(got, CheckResult::Unsat),
        "{label}: expected unsat, got {}\n--- source ---\n{src}",
        name(&got)
    );
}

#[track_caller]
fn assert_sat(label: &str, src: &str) {
    let got = verdict(src);
    assert!(
        matches!(got, CheckResult::Sat(_)),
        "{label}: expected sat, got {}\n--- source ---\n{src}",
        name(&got)
    );
}

// ---------------------------------------------------------------------------
// `desugar_sets`: a literal's bit position is its VALUE, never its spelling.
// ---------------------------------------------------------------------------
//
// Each `*_spellings_are_one_element` test is the shape that shipped `sat` when
// `set_element_key` returned the literal's raw text. Each is followed by the
// control that makes it non-vacuous: the SAME script with two genuinely
// different values, which must stay `sat`. Without that control a
// `set_element_key` that mapped every literal to one bit would pass the whole
// group.

/// `#b0101` and `#x5` are one 4-bit value, so `s` cannot both contain and not
/// contain it. Keying on spelling answered `sat` here (cvc5: `unsat`).
#[test]
fn bv_binary_and_hex_spellings_are_one_element() {
    assert_unsat(
        "#b0101 vs #x5",
        "(set-logic ALL)\n(declare-fun s () (Set (_ BitVec 4)))\n\
         (assert (set.member #b0101 s))\n(assert (not (set.member #x5 s)))\n(check-sat)\n",
    );
}

/// `(_ bv5 4)` is the third spelling of that same value.
#[test]
fn bv_indexed_and_hex_spellings_are_one_element() {
    assert_unsat(
        "(_ bv5 4) vs #x5",
        "(set-logic ALL)\n(declare-fun s () (Set (_ BitVec 4)))\n\
         (assert (set.member (_ bv5 4) s))\n(assert (not (set.member #x5 s)))\n(check-sat)\n",
    );
}

/// The non-vacuity control for both tests above: two DIFFERENT 4-bit values
/// must still get different bits, so this stays `sat`. A `set_element_key` that
/// collapsed everything to one bit would turn this `unsat`.
#[test]
fn distinct_bv_values_still_get_distinct_bits() {
    assert_sat(
        "#b0101 vs #x6 (genuinely different)",
        "(set-logic ALL)\n(declare-fun s () (Set (_ BitVec 4)))\n\
         (assert (set.member #b0101 s))\n(assert (not (set.member #x6 s)))\n(check-sat)\n",
    );
}

/// `1.5` and `1.50` are one Real. Trailing fractional zeros are not part of the
/// value.
#[test]
fn decimal_trailing_zero_spellings_are_one_element() {
    assert_unsat(
        "1.5 vs 1.50",
        "(set-logic ALL)\n(declare-fun s () (Set Real))\n\
         (assert (set.member 1.5 s))\n(assert (not (set.member 1.50 s)))\n(check-sat)\n",
    );
}

/// Leading integer zeros are likewise not part of the value.
#[test]
fn numeral_leading_zero_spellings_are_one_element() {
    assert_unsat(
        "7 vs 07",
        "(set-logic ALL)\n(declare-fun s () (Set Int))\n\
         (assert (set.member 7 s))\n(assert (not (set.member 07 s)))\n(check-sat)\n",
    );
}

/// `2` and `2.0`. Under SMT-LIB's `Reals_Ints` embedding these are one element
/// of a `(Set Real)`; see `set_element_key`'s note for why collapsing them is
/// safe under the stricter reading too.
#[test]
fn integer_and_decimal_spellings_are_one_element() {
    assert_unsat(
        "2 vs 2.0",
        "(set-logic ALL)\n(declare-fun s () (Set Real))\n\
         (assert (set.member 2 s))\n(assert (not (set.member 2.0 s)))\n(check-sat)\n",
    );
}

/// The non-vacuity control for the three numeric tests above: `1.5` and `2.5`
/// are different Reals and must keep different bits.
#[test]
fn distinct_numeric_values_still_get_distinct_bits() {
    assert_sat(
        "1.5 vs 2.5 (genuinely different)",
        "(set-logic ALL)\n(declare-fun s () (Set Real))\n\
         (assert (set.member 1.5 s))\n(assert (not (set.member 2.5 s)))\n(check-sat)\n",
    );
}

/// The same defect through `set.singleton`/`=` rather than `set.member`: two
/// spellings of one element build the SAME singleton, so asserting they differ
/// is `unsat`.
#[test]
fn singletons_of_one_value_spelled_two_ways_are_equal() {
    assert_unsat(
        "singleton #b0101 != singleton #x5",
        "(set-logic ALL)\n\
         (assert (not (= (set.singleton #b0101) (set.singleton #x5))))\n(check-sat)\n",
    );
}

/// Non-vacuity for the singleton route: singletons of genuinely different
/// values really are different sets.
#[test]
fn singletons_of_distinct_values_differ() {
    assert_sat(
        "singleton #b0101 != singleton #x6",
        "(set-logic ALL)\n\
         (assert (not (= (set.singleton #b0101) (set.singleton #x6))))\n(check-sat)\n",
    );
}

// ---------------------------------------------------------------------------
// `desugar_sets`: the universe is wide enough to witness the distinctions the
// formula demands.
// ---------------------------------------------------------------------------
//
// The width was `d + SET_MARGIN_BITS` with `SET_MARGIN_BITS` a CONSTANT 2, so a
// set variable had exactly `2^(d+2)` possible values and an `N`-way `distinct`
// over free sets was refuted by pigeonhole for `N > 2^(d+2)`. The three tests
// below are the witness and the two controls that pin the THRESHOLD rather than
// just the symptom — which is what shows the mechanism is the width and not
// something else in the set encoding.

/// Five free set variables with no named element. Five distinct subsets of an
/// infinite sort plainly exist, so this is `sat`; at width `0 + 2` it was
/// refuted by pigeonhole. cvc5 answers `sat`.
#[test]
fn five_free_sets_can_be_pairwise_distinct() {
    assert_sat(
        "5 free sets, d=0",
        "(set-logic ALL)\n(declare-sort E 0)\n\
         (declare-fun s1 () (Set E))\n(declare-fun s2 () (Set E))\n\
         (declare-fun s3 () (Set E))\n(declare-fun s4 () (Set E))\n\
         (declare-fun s5 () (Set E))\n\
         (assert (distinct s1 s2 s3 s4 s5))\n(check-sat)\n",
    );
}

/// Threshold control below the old cliff: FOUR free sets fit in `2^(0+2) = 4`
/// values, so this was `sat` even before the fix. It pins that the five-set
/// test above is about the WIDTH — a change that broke set distinctness
/// generally would take this one down too.
#[test]
fn four_free_sets_can_be_pairwise_distinct() {
    assert_sat(
        "4 free sets, d=0 (was sat before the fix too)",
        "(set-logic ALL)\n(declare-sort E 0)\n\
         (declare-fun s1 () (Set E))\n(declare-fun s2 () (Set E))\n\
         (declare-fun s3 () (Set E))\n(declare-fun s4 () (Set E))\n\
         (assert (distinct s1 s2 s3 s4))\n(check-sat)\n",
    );
}

/// Threshold control above the old cliff, built by raising `d`: the SAME five
/// sets, plus one named literal element, which took the old width to `1 + 2`
/// and `2^3 = 8 >= 5`. So this was `sat` before the fix and must stay `sat`
/// after it.
///
/// The construction matters and is stated here because it is easy to get a
/// different query by accident: the extra element must be a NAMED LITERAL in a
/// `set.member`, since `d` counts distinct literal element terms. Declaring an
/// element-sorted *variable* and asserting membership of it does not raise `d`
/// — `scan_set_ops` declines a non-literal element — and that script answers
/// `unknown`, not `sat`.
#[test]
fn five_free_sets_with_a_named_element_stay_sat() {
    assert_sat(
        "5 free sets + one named literal element, d=1",
        "(set-logic ALL)\n\
         (declare-fun s1 () (Set Int))\n(declare-fun s2 () (Set Int))\n\
         (declare-fun s3 () (Set Int))\n(declare-fun s4 () (Set Int))\n\
         (declare-fun s5 () (Set Int))\n\
         (assert (distinct s1 s2 s3 s4 s5))\n(assert (set.member 1 s1))\n(check-sat)\n",
    );
}

/// A width past `MAX_SET_WIDTH` must DECLINE, never clamp.
///
/// This is the test that makes the fix safe rather than merely different: a
/// `min(demand, MAX_SET_WIDTH)` in place of the decline would silently
/// reintroduce the pigeonhole bug at a higher threshold and would look like a
/// fix. Under a clamp this script parses and answers a verdict; the assertion
/// is that it does not parse at all.
///
/// 200 pairwise-distinct free sets demand `200*199/2` witness slots, far past
/// the 128-bit cap, so the demand cannot be met.
#[test]
fn set_width_over_the_cap_declines() {
    let mut src = String::from("(set-logic ALL)\n(declare-sort E 0)\n");
    for i in 0..200 {
        src.push_str(&format!("(declare-fun s{i} () (Set E))\n"));
    }
    src.push_str("(assert (distinct");
    for i in 0..200 {
        src.push_str(&format!(" s{i}"));
    }
    src.push_str("))\n(check-sat)\n");

    let err = parse_script(&src)
        .err()
        .expect("a set universe past MAX_SET_WIDTH must be refused, not clamped to the cap");
    let text = err.to_string();
    assert!(
        text.contains("cap"),
        "expected a capacity decline naming the cap, got: {text}"
    );
}

// ---------------------------------------------------------------------------
// `desugar_const_arrays`: a definition is eliminated only where it is in force.
// ---------------------------------------------------------------------------
//
// These go through `solve_smtlib_session`, NOT the flat `check_auto` view
// above, and the distinction is load-bearing: `Script::assertions` is the flat
// view and *ignores* `push`/`pop` and `reset-assertions` by construction
// (`parse.rs:103-105`). A flat-view test of a popped definition would see the
// definition either way and could not tell a fixed parser from a broken one.

/// The `(check-sat)` verdicts of a script, in command order.
fn session_verdicts(src: &str) -> Vec<CheckResult> {
    solve_smtlib_session(src, &SolverConfig::default())
        .unwrap_or_else(|e| panic!("session failed: {e:?}\n--- source ---\n{src}"))
        .into_iter()
        .filter_map(|r| match r {
            SmtLibResponse::CheckSat(result) => Some(result),
            _ => None,
        })
        .collect()
}

#[track_caller]
fn assert_session(label: &str, src: &str, expected: &[&str]) {
    let got = session_verdicts(src);
    let names: Vec<&str> = got.iter().map(name).collect();
    assert_eq!(
        names.as_slice(),
        expected,
        "{label}: verdict sequence\n--- source ---\n{src}"
    );
}

/// A const-array definition inside a scope that is POPPED before the
/// `check-sat` does not constrain the symbol. Inlining it anyway shipped
/// `unsat` for a satisfiable script.
#[test]
fn const_array_definition_in_a_popped_scope_is_not_inlined() {
    assert_session(
        "definition popped before check-sat",
        "(set-logic QF_ALIA)\n(declare-const a (Array Int Int))\n\
         (push 1)\n(assert (= a ((as const (Array Int Int)) 0)))\n(pop 1)\n\
         (assert (not (= (select a 5) 0)))\n(check-sat)\n",
        &["sat"],
    );
}

/// Non-vacuity #1 for the test above: with no definition at all the query is
/// satisfiable for the same reason, so this pins that `sat` is reachable at
/// all through this route.
#[test]
fn const_array_query_without_any_definition_is_sat() {
    assert_session(
        "no definition at all",
        "(set-logic QF_ALIA)\n(declare-const a (Array Int Int))\n\
         (assert (not (= (select a 5) 0)))\n(check-sat)\n",
        &["sat"],
    );
}

/// Non-vacuity #2, and the one that matters: with the definition genuinely in
/// force the answer IS `unsat`. Together with the popped-scope test this
/// brackets the defect — a "fix" that simply disabled the rewrite everywhere
/// would still pass the popped test, and would still pass this one only if the
/// residual `(= a const)` assert is solved correctly, which is the point.
#[test]
fn const_array_definition_at_top_level_is_still_unsat() {
    assert_session(
        "definition at top level",
        "(set-logic QF_ALIA)\n(declare-const a (Array Int Int))\n\
         (assert (= a ((as const (Array Int Int)) 0)))\n\
         (assert (not (= (select a 5) 0)))\n(check-sat)\n",
        &["unsat"],
    );
}

/// A definition that appears AFTER a `check-sat` must not be inlined backwards
/// into the query that preceded it. No `push`/`pop` is involved — this is
/// ordinary SMT-LIB with two queries, and the first verdict was wrong.
#[test]
fn const_array_definition_is_not_inlined_backwards_past_a_check_sat() {
    assert_session(
        "definition after the first check-sat",
        "(set-logic QF_ALIA)\n(declare-const a (Array Int Int))\n\
         (assert (= (select a 5) 1))\n(check-sat)\n\
         (assert (= a ((as const (Array Int Int)) 0)))\n(check-sat)\n",
        &["sat", "unsat"],
    );
}

/// `reset-assertions` retracts even a depth-0 definition, so a definition
/// before one must not reach the assertions after it.
#[test]
fn const_array_definition_before_a_reset_is_not_inlined() {
    assert_session(
        "definition retracted by reset-assertions",
        "(set-logic QF_ALIA)\n(declare-const a (Array Int Int))\n\
         (assert (= a ((as const (Array Int Int)) 0)))\n(reset-assertions)\n\
         (assert (not (= (select a 5) 0)))\n(check-sat)\n",
        &["sat"],
    );
}
