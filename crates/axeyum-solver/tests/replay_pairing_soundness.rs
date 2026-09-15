#![cfg(feature = "full")]
// Guarded because every route this suite exercises is `full`-only, so without
// the feature the crate does not compile `--all-targets` on DEFAULT features --
// which `cargo check --workspace` hides through Cargo's feature unification.
//
// The guard has a cost worth naming: a `#![cfg]`-ed suite compiles to ZERO
// tests and exits 0 without the feature, which is how one gate here stayed
// inert for 15 days. Its count under `--features full` is pinned in the commit
// that added this file, and `hooks/pre-push` runs it WITH the feature.
//! ADR-2070: `SmtLibSolved.assertions` and `.model` must be an actual **pair**.
//!
//! # The invariant
//!
//! `SmtLibSolved`'s own documentation says `model` is `Some` exactly when the
//! flat path decided `Sat` over `assertions`, so
//! `check_model(&solved.script.arena, &solved.assertions, model)` is meaningful.
//! Until 2026-09-14 that was false: the string second chances
//! (`fd:word-route`, `fd:membership`, `fd:length-lia`, ...) decide against the
//! SOURCE expressions and bind the parser's `!weq!<name>` sequence mirrors,
//! while `assertions` stayed the PACKED flat vector over the declared names at
//! `(_ BitVec string_total(m))`. Different `SymbolId`s, different names,
//! different sorts — so the replay could not evaluate at all.
//!
//! Measured over the 217 string-division files: **5 of 109 `sat` results**, all
//! failing as `no value bound for symbol #0`. The verdicts were all correct;
//! the damage was a FALSE ALARM, and it was confirmed end to end rather than
//! traced — `axeyum-py`'s `Outcome.replay()`, run on those five rows, answered
//! `False` on four (its docs call that "a soundness signal") and `True` on the
//! fifth over an all-empty substituted model, which is a vacuous pass and
//! worse.
//!
//! # Why every test here is paired with a control
//!
//! ADR-1976 measured that a satisfiable query is a VACUOUS control: an
//! underconstrained `sat` stays `sat` under a deliberately broken rewrite. So
//! "this row now replays `Ok(true)`" is not on its own evidence of anything —
//! a repair that simply stopped checking would also produce it. Each pair below
//! therefore differs in ONE small term and lands on OPPOSITE sides of the
//! packed encoding's cap, so a build that withheld everything and a build that
//! paired everything each fail exactly one half.
//!
//! # The one test that keeps the checker honest
//!
//! `the_replay_can_still_answer_false` is the load-bearing one.
//! `pair_replay_state` deliberately does NOT consult `check_model` before
//! shipping a pair — it guards on completeness of the binding instead — because
//! verifying satisfaction there would make every downstream replay a tautology.
//! That test proves the replay retains its power to reject.

use axeyum_ir::{Sort, Value};
use axeyum_solver::{
    CheckResult, SolverConfig, check_model,
    smtlib::{SmtLibSolved, solve_smtlib_with_model},
};

/// Decide a script through the shipped front door, carrying replay state.
#[track_caller]
fn solve(src: &str) -> SmtLibSolved {
    solve_smtlib_with_model(src, &SolverConfig::default())
        .unwrap_or_else(|e| panic!("front door failed: {e:?}\n--- source ---\n{src}"))
}

#[track_caller]
fn assert_sat(label: &str, solved: &SmtLibSolved) {
    assert!(
        matches!(solved.outcome.result, CheckResult::Sat(_)),
        "{label}: expected sat, got {:?}",
        solved.outcome.result
    );
}

/// The row ships a replayable pair AND the replay holds.
#[track_caller]
fn assert_pairs(label: &str, solved: &SmtLibSolved) {
    assert!(
        !solved.assertions.is_empty(),
        "{label}: shipped an EMPTY assertion vector, so there is nothing to replay"
    );
    let model = solved
        .model
        .as_ref()
        .unwrap_or_else(|| panic!("{label}: shipped no model, so there is nothing to replay"));
    match check_model(&solved.script.arena, &solved.assertions, model) {
        Ok(true) => {}
        Ok(false) => panic!("{label}: the replay REFUTED the model shipped beside the assertions"),
        Err(error) => panic!("{label}: the replay could not evaluate at all: {error}"),
    }
}

/// The row withholds replay state — both halves, because either one alone is a
/// claim this type refuses to make (a model with no assertions replays `true`
/// vacuously; assertions with no model are inert).
#[track_caller]
fn assert_withholds(label: &str, solved: &SmtLibSolved) {
    assert!(
        solved.assertions.is_empty() && solved.model.is_none(),
        "{label}: expected NO replay state, got assertions={} model={}",
        solved.assertions.len(),
        solved.model.is_some()
    );
}

// ---------------------------------------------------------------------------
// The cap boundary. These two differ in ONE numeral and must land on opposite
// sides, which is what makes neither of them vacuous.
// ---------------------------------------------------------------------------
//
// `STRING_MAX_LEN` is 12 bytes for a declared `String`. A witness at or under
// it is representable in the packed layout, so the lift exists and the replay
// is real evidence. A witness past it is representable by NOTHING: running the
// packed vector alone through `check_auto` returns `unsat`, so there is no model
// to lift to and pairing anything with it would replay `false` on a correct
// `sat`.

/// The exact shape ADR-2010 handed off as `r1_QF_SLIA_re-inter-stack-ovf`,
/// reduced to the one assertion that matters. The witness must be ≥ 15 bytes
/// and the packed cap is 12, so this row MUST withhold.
#[test]
fn a_witness_past_the_packed_cap_withholds_rather_than_shipping_an_unreplayable_pair() {
    let solved = solve(
        "(set-logic QF_SLIA)\n\
         (declare-fun var0 () String)\n\
         (assert (str.in_re var0 (re.+ (re.union (str.to_re \"0\") (str.to_re \"1\")))))\n\
         (assert (<= 15 (str.len var0)))\n\
         (check-sat)",
    );
    assert_sat("past-the-cap", &solved);
    assert_withholds("past-the-cap", &solved);
}

/// **The control for the test above, differing in one numeral.** Ten bytes fits
/// the packed cap of twelve, so this row must NOT withhold — it must ship a
/// pair whose replay holds. Without this half, a build that withheld every
/// string `sat` would pass the test above and have removed the evidence
/// entirely, which is exactly the repair this ADR rejected.
#[test]
fn a_witness_within_the_packed_cap_ships_a_pair_whose_replay_holds() {
    let solved = solve(
        "(set-logic QF_SLIA)\n\
         (declare-fun var0 () String)\n\
         (assert (str.in_re var0 (re.+ (re.union (str.to_re \"0\") (str.to_re \"1\")))))\n\
         (assert (<= 10 (str.len var0)))\n\
         (check-sat)",
    );
    assert_sat("within-the-cap", &solved);
    assert_pairs("within-the-cap", &solved);
}

// ---------------------------------------------------------------------------
// The routes. Each of the four string second chances that can replace the
// verdict with a source-level model gets a row, because the defect is per-route
// and a repair wired into three of four would look identical on any aggregate.
// ---------------------------------------------------------------------------

/// `fd:word-route`. Four of the five measured corpus rows were decided here.
#[test]
fn the_word_route_ships_a_replayable_pair() {
    let solved = solve(
        "(set-logic QF_SLIA)\n\
         (declare-fun x () String)\n\
         (declare-fun y () String)\n\
         (assert (= (str.++ x y) \"abc\"))\n\
         (assert (= (str.len x) 1))\n\
         (check-sat)",
    );
    assert_sat("word-route", &solved);
    assert_pairs("word-route", &solved);
}

/// `fd:length-lia` — **ADR-2010's own headline witness**, and the route the
/// 217-file corpus never reaches. A repair validated only against the corpus
/// would leave this one unfixed and every aggregate would still read clean.
#[test]
fn the_length_lia_route_ships_a_replayable_pair() {
    let solved = solve(
        "(set-logic QF_SLIA)\n\
         (declare-fun x () String)\n\
         (assert (= (str.len x) 10))\n\
         (check-sat)",
    );
    assert_sat("length-lia", &solved);
    assert_pairs("length-lia", &solved);
}

/// **The control for the row above**, differing in one numeral and crossing the
/// cap. `str.len x = 20` is ADR-2010's literal example; twenty is past twelve,
/// so this must withhold while `= 10` pairs. The pair pins that the boundary
/// is the packed CAP and not "string routes withhold" in general.
#[test]
fn the_length_lia_route_withholds_past_the_cap() {
    let solved = solve(
        "(set-logic QF_SLIA)\n\
         (declare-fun x () String)\n\
         (assert (= (str.len x) 20))\n\
         (check-sat)",
    );
    assert_sat("length-lia-past-cap", &solved);
    assert_withholds("length-lia-past-cap", &solved);
}

/// `fd:membership`. The fifth measured corpus row was decided here.
#[test]
fn the_membership_route_ships_a_replayable_pair() {
    let solved = solve(
        "(set-logic QF_SLIA)\n\
         (declare-fun var0 () String)\n\
         (assert (str.in_re var0 (re.++ (str.to_re \"ab\") (re.* (str.to_re \"c\")))))\n\
         (assert (<= 4 (str.len var0)))\n\
         (check-sat)",
    );
    assert_sat("membership", &solved);
    assert_pairs("membership", &solved);
}

// ---------------------------------------------------------------------------
// The guard that keeps the repair from being a narrowed check.
// ---------------------------------------------------------------------------

/// **Load-bearing.** The repair would be worthless — worse than the bug — if it
/// made `check_model` unable to reject. `pair_replay_state` guards on
/// COMPLETENESS of the binding, never on satisfaction, precisely so that the
/// downstream replay keeps its teeth.
///
/// This takes a row that now pairs, replaces the lifted string binding with a
/// DIFFERENT well-formed packing, and requires the replay to answer `Ok(false)`
/// — not `Ok(true)`, and not `Err`. A build in which the front door verified
/// satisfaction before shipping would still pass this (the tampering happens
/// after), but a build whose replay had been narrowed to something that cannot
/// fail would not.
#[test]
fn the_replay_can_still_answer_false() {
    let solved = solve(
        "(set-logic QF_SLIA)\n\
         (declare-fun x () String)\n\
         (assert (= (str.len x) 10))\n\
         (check-sat)",
    );
    assert_pairs("tamper-base", &solved);
    let mut tampered = solved.model.clone().expect("the row pairs");
    // Rebind every declared string to the packing of the EMPTY string (length
    // field zero, no content). The query demands length 10, so this model is a
    // genuine non-model and the replay must say so.
    let mut retargeted = 0;
    for &(symbol, _) in &solved.script.declared_strings {
        let (_, sort) = solved.script.arena.symbol(symbol);
        if let Sort::BitVec(width) = sort {
            tampered.set(symbol, Value::Bv { width, value: 0 });
            retargeted += 1;
        }
    }
    // Without this the test could pass by tampering with nothing at all — the
    // vacuity failure mode ADR-1976 names.
    assert!(
        retargeted > 0,
        "the tamper retargeted NO symbol, so this test proves nothing"
    );
    assert_eq!(
        check_model(&solved.script.arena, &solved.assertions, &tampered).expect("replay evaluates"),
        false,
        "the replay accepted a model binding every string to the empty string for a query \
         demanding length 10 — it has been narrowed to something that cannot fail"
    );
}

/// The non-string control for the whole suite. A plain `QF_BV` `sat` never went
/// through a source route and must be untouched by the repair: it pairs, as it
/// always did. If this ever withholds, `pair_replay_state`'s completeness guard
/// has started firing on rows it was never meant to see.
#[test]
fn a_plain_bv_sat_is_untouched_by_the_pairing_repair() {
    let solved = solve(
        "(set-logic QF_BV)\n\
         (declare-fun x () (_ BitVec 8))\n\
         (assert (= x #x2a))\n\
         (check-sat)",
    );
    assert_sat("qf-bv-control", &solved);
    assert_pairs("qf-bv-control", &solved);
}

/// An `unsat` must keep its assertion vector. The repair touches only the `Sat`
/// arm, and a completeness guard that also fired on `unsat` would silently
/// empty a vector other callers read (the unsat-core and certificate routes).
#[test]
fn an_unsat_keeps_its_assertion_vector() {
    let solved = solve(
        "(set-logic QF_SLIA)\n\
         (declare-fun x () String)\n\
         (assert (= x \"ab\"))\n\
         (assert (= (str.len x) 3))\n\
         (check-sat)",
    );
    assert!(
        matches!(solved.outcome.result, CheckResult::Unsat),
        "expected unsat, got {:?}",
        solved.outcome.result
    );
    assert!(
        !solved.assertions.is_empty(),
        "the repair emptied an `unsat`'s assertion vector"
    );
    assert!(solved.model.is_none(), "an `unsat` must carry no model");
}
