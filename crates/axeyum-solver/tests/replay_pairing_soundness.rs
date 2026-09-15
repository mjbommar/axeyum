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
//! Until 2026-09-14 that was false: the string second chances decide against the
//! SOURCE expressions and bind the parser's `!weq!<name>` sequence mirrors,
//! while `assertions` stayed the PACKED flat vector over the declared names at
//! `(_ BitVec string_total(m))`. Different `SymbolId`s, different names,
//! different sorts — so the replay could not evaluate at all. Measured over the
//! 217 string-division files: **5 of 109 `sat` results**.
//!
//! # EVERY test here asserts WHICH ROUTE DECIDED IT, and that is not decoration
//!
//! The first version of this suite named the routes in its test names and
//! reached **none of them**. `(= (str.len x) 10)` and a short `str.in_re` are
//! both decided by the FLAT path (`bv2nat-blast`), because the bounded encoding
//! can represent a ten-character witness perfectly well — the second chances
//! only ever run after the flat path declines. So three tests called
//! "the ... route ships a replayable pair" were passing without the lift ever
//! executing, and the mutation table is what exposed it: deleting the entire
//! `lift_source_strings_onto_packed` call **survived all nine tests**.
//!
//! Every test therefore pins its deciding stage through
//! [`RouteAttributionGuard`]. A fixture that drifts onto another route now fails
//! loudly instead of quietly testing nothing.
//!
//! # What the routes can and cannot do, measured
//!
//! `fd:length-lia` and `fd:membership` exist precisely to decide rows whose
//! witness EXCEEDS the packed cap — which is the same condition that makes the
//! flat path decline and hand over to them. In this corpus and in these
//! fixtures they are therefore reached only by rows that can never be lifted,
//! and they can only withhold. The lift is exercised through `fd:word-route`,
//! whose witnesses can be short. Both halves are pinned below.
//!
//! # The load-bearing test
//!
//! `the_replay_can_still_answer_false`. `pair_replay_state` deliberately does
//! NOT consult `check_model` before shipping a pair — it guards on completeness
//! of the binding instead — because verifying satisfaction there would make
//! every downstream replay a tautology. That test proves the replay retains its
//! power to reject.

use std::fmt::Write as _;

use axeyum_ir::{Sort, Value};
use axeyum_smtlib::{decode_packed_string, parse_script};
use axeyum_solver::{
    CheckResult, RouteAttributionGuard, RouteOutcome, SmtLibResponse, SolverConfig, Verdict,
    check_auto, check_model, front_door_stage, last_route_attribution,
    smtlib::{SmtLibSolved, solve_smtlib_with_model},
    solve_smtlib_session,
};

/// The `r1_QF_SLIA_type002` shape, one of the four corpus rows the defect was
/// measured on. `i >= 420` forces `x` to be at least three digits, and the
/// witness (`x = "500"`, `y = "5"`, `z = "0"`) sits well inside the packed cap,
/// so this row is LIFTABLE.
const WORD_ROUTE_SHORT: &str = "(set-logic QF_SLIA)\n\
     (declare-fun x () String)\n\
     (declare-fun y () String)\n\
     (declare-fun z () String)\n\
     (declare-fun i () Int)\n\
     (assert (>= i 420))\n\
     (assert (= x (str.from_int i)))\n\
     (assert (= x (str.++ y \"0\" z)))\n\
     (assert (not (= y \"\")))\n\
     (assert (not (= z \"\")))\n\
     (check-sat)";

/// **The non-vacuity control for `WORD_ROUTE_SHORT`, differing in one numeral.**
/// `4_200_000_000_000` is thirteen digits and the packed cap is twelve, so the
/// same shape on the same route is UNLIFTABLE and must withhold. Without this
/// half, a build that paired everything unconditionally would pass; without the
/// other half, a build that withheld everything would.
const WORD_ROUTE_LONG: &str = "(set-logic QF_SLIA)\n\
     (declare-fun x () String)\n\
     (declare-fun y () String)\n\
     (declare-fun z () String)\n\
     (declare-fun i () Int)\n\
     (assert (>= i 4200000000000))\n\
     (assert (= x (str.from_int i)))\n\
     (assert (= x (str.++ y \"0\" z)))\n\
     (assert (not (= y \"\")))\n\
     (assert (not (= z \"\")))\n\
     (check-sat)";

/// Decide a script through the shipped front door, carrying replay state, and
/// report the front-door stage that decided it.
#[track_caller]
fn solve(src: &str) -> (SmtLibSolved, String) {
    let solved = {
        let _guard = RouteAttributionGuard::enable();
        solve_smtlib_with_model(src, &SolverConfig::default())
            .unwrap_or_else(|e| panic!("front door failed: {e:?}\n--- source ---\n{src}"))
    };
    let trace = last_route_attribution();
    let route = trace
        .attempts()
        .iter()
        .rev()
        .find(|a| matches!(a.outcome, RouteOutcome::Decided(Verdict::Sat)))
        .map_or_else(|| "UNATTRIBUTED".to_owned(), |a| a.route.to_owned());
    (solved, route)
}

/// The row is `sat` AND it was decided by the stage this test claims.
///
/// The second half is what keeps the test from measuring nothing: a fixture
/// that drifts onto the flat path still answers `sat`, and without this it
/// would keep passing while the code it names never runs.
#[track_caller]
fn assert_sat_via(label: &str, expected: &str, (solved, route): &(SmtLibSolved, String)) {
    assert!(
        matches!(solved.outcome.result, CheckResult::Sat(_)),
        "{label}: expected sat, got {:?}",
        solved.outcome.result
    );
    assert_eq!(
        route, expected,
        "{label}: this fixture no longer reaches `{expected}` — it was decided by `{route}`, so \
         the test is measuring a different code path than its name claims"
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
// The word route, both sides of the packed cap. This is the pair that
// exercises the LIFT; everything else in this file exercises the withhold.
// ---------------------------------------------------------------------------

/// The repair itself: a source-route witness is packed onto the declared
/// symbol, so the replay runs and holds. Before ADR-2070 this row answered
/// `sat` with `check_model` -> `Err("no value bound for symbol #0")`.
#[test]
fn the_word_route_lifts_a_short_witness_into_a_replayable_pair() {
    let row = solve(WORD_ROUTE_SHORT);
    assert_sat_via("word-short", front_door_stage::WORD_ROUTE, &row);
    assert_pairs("word-short", &row.0);
}

/// **The control, one numeral apart.** Same route, same shape, a witness of
/// thirteen digits against a twelve-byte cap: unliftable, so it must withhold
/// rather than ship a pair that cannot be evaluated.
#[test]
fn the_word_route_withholds_when_the_witness_is_past_the_packed_cap() {
    let row = solve(WORD_ROUTE_LONG);
    assert_sat_via("word-long", front_door_stage::WORD_ROUTE, &row);
    assert_withholds("word-long", &row.0);
}

/// The lift must bind the DECLARED symbol, not merely leave a `Seq` lying
/// around under `!weq!x`. Reads the value back at the packed sort and requires
/// it to decode to a non-empty string — the empty packing is what
/// `complete_with_defaults` produced downstream before the repair, and it is
/// exactly the wrong model `axeyum-py` was reporting to users.
#[test]
fn the_lift_binds_the_declared_symbol_and_not_only_the_word_mirror() {
    let (solved, _) = solve(WORD_ROUTE_SHORT);
    let model = solved.model.as_ref().expect("the short witness pairs");
    let mut checked = 0;
    for &(symbol, _) in &solved.script.declared_strings {
        let (name, sort) = solved.script.arena.symbol(symbol);
        let Sort::BitVec(width) = sort else { continue };
        let value = model
            .get(symbol)
            .unwrap_or_else(|| panic!("declared string `{name}` is unbound after the lift"));
        assert!(
            matches!(value, Value::Bv { width: w, .. } if w == width),
            "declared string `{name}` is bound at the wrong sort: {value:?}"
        );
        checked += 1;
    }
    // Without this the test would pass over an empty `declared_strings`, which
    // is the vacuity this suite already fell into once.
    assert!(
        checked >= 3,
        "expected the three declared strings of this fixture, examined {checked}"
    );
    // `x = str.from_int i` with `i >= 420`, so at least one string is non-empty.
    // An all-empty model is what the defect produced, and it would satisfy every
    // structural assertion above.
    let non_empty = solved.script.declared_strings.iter().any(
        |&(symbol, _)| matches!(model.get(symbol), Some(Value::Bv { value, .. }) if value != 0),
    );
    assert!(
        non_empty,
        "every declared string packed to the EMPTY string — that is the defaulted model the \
         defect produced, not the witness the route found"
    );
}

// ---------------------------------------------------------------------------
// The two routes that can only ever withhold, and their flat-path controls.
// ---------------------------------------------------------------------------
//
// Each pair differs in ONE numeral and crosses `STRING_MAX_LEN = 12`. Below the
// cap the FLAT path decides and the pair is real; above it the flat path
// declines, the second chance answers, and there is nothing to lift to. That is
// why these two routes withhold rather than pair: not a limitation of the lift,
// but the reason the routes exist.

/// `fd:length-lia`, ADR-2010's own headline witness. Twenty characters against
/// a twelve-byte cap: `check_auto` on the packed vector alone is `unsat`, so no
/// lift exists and pairing anything with it would replay `false` on a correct
/// `sat`.
#[test]
fn the_length_lia_route_withholds_past_the_packed_cap() {
    let row = solve(
        "(set-logic QF_SLIA)\n\
         (declare-fun x () String)\n\
         (assert (= (str.len x) 20))\n\
         (check-sat)",
    );
    assert_sat_via("length-lia", front_door_stage::LENGTH_LIA, &row);
    assert_withholds("length-lia", &row.0);
}

/// **The control for the row above**, differing in one numeral. Twelve is the
/// cap, so the FLAT path decides this and the pair is genuine. It pins that the
/// boundary is the cap and not "string rows withhold" in general — and that the
/// repair did not start emptying vectors the flat path filled correctly.
#[test]
fn a_length_constraint_within_the_cap_is_decided_flat_and_pairs() {
    let row = solve(
        "(set-logic QF_SLIA)\n\
         (declare-fun x () String)\n\
         (assert (= (str.len x) 12))\n\
         (check-sat)",
    );
    assert_sat_via("length-flat", "bv2nat-blast", &row);
    assert_pairs("length-flat", &row.0);
}

/// `fd:membership`, the shape of the fifth measured corpus row
/// (`r1_QF_SLIA_re-inter-stack-ovf`): `(<= 15 (str.len var0))` past a cap of 12.
#[test]
fn the_membership_route_withholds_past_the_packed_cap() {
    let row = solve(
        "(set-logic QF_SLIA)\n\
         (declare-fun var0 () String)\n\
         (assert (str.in_re var0 (re.+ (re.union (str.to_re \"0\") (str.to_re \"1\")))))\n\
         (assert (<= 15 (str.len var0)))\n\
         (check-sat)",
    );
    assert_sat_via("membership", front_door_stage::MEMBERSHIP, &row);
    assert_withholds("membership", &row.0);
}

/// **The control for the row above**, `15` -> `11`. Inside the cap the flat
/// path decides the same regex and the pair is genuine.
#[test]
fn a_membership_within_the_cap_is_decided_flat_and_pairs() {
    let row = solve(
        "(set-logic QF_SLIA)\n\
         (declare-fun var0 () String)\n\
         (assert (str.in_re var0 (re.+ (re.union (str.to_re \"0\") (str.to_re \"1\")))))\n\
         (assert (<= 11 (str.len var0)))\n\
         (check-sat)",
    );
    assert_sat_via("membership-flat", "bv2nat-blast", &row);
    assert_pairs("membership-flat", &row.0);
}

/// **Why the withholding rows are permanent, pinned rather than asserted.**
///
/// It would be easy to read "these rows withhold" as a limitation of the lift —
/// something a later lane could push further. It is not. For a row whose
/// witness exceeds the packed cap, the PACKED ASSERTION VECTOR ITSELF IS
/// `unsat`: there is no model in that space, so no lift can exist and pairing
/// ANY model with those assertions would replay `false` on a correct `sat`.
///
/// This runs `check_auto` over the parser's own assertion vector for the
/// past-the-cap membership row and requires `unsat`. Its control is the same
/// regex one numeral below the cap, which must be `sat` — without that half a
/// build whose parser produced a trivially unsatisfiable vector for EVERY
/// string query would pass, and the conclusion drawn here would be wrong.
#[test]
fn past_the_cap_the_packed_vector_has_no_model_at_all() {
    let past = "(set-logic QF_SLIA)\n\
         (declare-fun var0 () String)\n\
         (assert (str.in_re var0 (re.+ (re.union (str.to_re \"0\") (str.to_re \"1\")))))\n\
         (assert (<= 15 (str.len var0)))\n\
         (check-sat)";
    let within = past.replace("<= 15", "<= 11");

    let mut script = parse_script(past).expect("parse the past-the-cap row");
    let assertions = script.assertions.clone();
    let verdict = check_auto(&mut script.arena, &assertions, &SolverConfig::default())
        .expect("the packed vector decides");
    assert!(
        matches!(verdict, CheckResult::Unsat),
        "the packed vector for a 15-byte demand against a 12-byte cap should have NO model; got \
         {verdict:?}. If this is no longer `unsat`, the withholding above is not permanent and \
         the lift should be reconsidered."
    );

    let mut control = parse_script(&within).expect("parse the within-the-cap control");
    let control_assertions = control.assertions.clone();
    let control_verdict = check_auto(
        &mut control.arena,
        &control_assertions,
        &SolverConfig::default(),
    )
    .expect("the control decides");
    assert!(
        matches!(control_verdict, CheckResult::Sat(_)),
        "the SAME regex one numeral below the cap must be `sat` — otherwise the `unsat` above \
         says nothing about the cap; got {control_verdict:?}"
    );
}

// ---------------------------------------------------------------------------
// The guard that keeps the repair from being a narrowed check.
// ---------------------------------------------------------------------------

/// **Load-bearing.** The repair would be worthless — worse than the bug — if it
/// made `check_model` unable to reject. `pair_replay_state` guards on
/// COMPLETENESS of the binding, never on satisfaction, precisely so the
/// downstream replay keeps its teeth.
///
/// This takes the lifted word-route row, replaces every lifted string binding
/// with the packing of the EMPTY string, and requires the replay to answer
/// `Ok(false)` — not `Ok(true)`, and not `Err`. The empty model is not a
/// strawman: it is exactly what `complete_with_defaults` substituted downstream
/// before the repair, and what `axeyum-py` was reporting to users.
#[test]
fn the_replay_can_still_answer_false() {
    let (solved, _) = solve(WORD_ROUTE_SHORT);
    assert_pairs("tamper-base", &solved);
    let mut tampered = solved.model.clone().expect("the row pairs");
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
    assert!(
        !check_model(&solved.script.arena, &solved.assertions, &tampered)
            .expect("the replay evaluates"),
        "the replay accepted a model binding every string to the empty string for a query that \
         forces a three-digit one — it has been narrowed to something that cannot fail"
    );
}

/// The non-string control for the whole suite. A plain `QF_BV` `sat` never went
/// through a source route and must be untouched: it pairs, as it always did. If
/// this ever withholds, the completeness guard has started firing on rows it
/// was never meant to see.
#[test]
fn a_plain_bv_sat_is_untouched_by_the_pairing_repair() {
    let row = solve(
        "(set-logic QF_BV)\n\
         (declare-fun x () (_ BitVec 8))\n\
         (assert (= x #x2a))\n\
         (check-sat)",
    );
    assert!(matches!(row.0.outcome.result, CheckResult::Sat(_)));
    assert_pairs("qf-bv-control", &row.0);
}

/// An `unsat` must keep its assertion vector. The repair touches only the `Sat`
/// arm, and a completeness guard that also fired on `unsat` would silently
/// empty a vector other callers read (the unsat-core and certificate routes).
#[test]
fn an_unsat_keeps_its_assertion_vector() {
    let (solved, _) = solve(
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

// ---------------------------------------------------------------------------
// The assertion this suite did not have: does the model SATISFY THE QUERY?
// ---------------------------------------------------------------------------
//
// Eleven tests covered the pairing, the cap boundary and the withholding, and
// every one of them asked whether a REPLAY returned `Ok`. None asked whether the
// values a user is handed actually satisfy the assertions the user wrote. The
// coordinator found the gap by running `axeyum_cli` with `(get-model)` on a row
// this lane claimed to have fixed and getting `x=""  y=""  z=""  i=500` back —
// a model that violates `(not (= y ""))` outright.
//
// The rule one level up from this suite's own: a test that names a ROUTE must
// assert the route, and a test that names a MODEL must assert the model
// satisfies the query — not that some checker returned `Ok`.
//
// How "satisfies the source" is decided here without a second evaluator: pin
// EVERY model symbol to its reported value with an added equality and re-decide
// the ORIGINAL script. With every free symbol pinned the query is ground, so the
// verdict is evaluation. `sat` means the model satisfies the source assertions;
// `unsat` means it does not. Each use is paired with the all-empty model as the
// control, which MUST come back `unsat` — otherwise the check cannot
// discriminate and proves nothing.

/// The reported model for `src`, as `(name, smtlib-literal)` pairs, taken from
/// the front door's own `sat` and decoded through the PUBLIC decoder.
fn reported_model(solved: &SmtLibSolved) -> Vec<(String, String)> {
    let CheckResult::Sat(result_model) = &solved.outcome.result else {
        panic!("not sat");
    };
    let arena = &solved.script.arena;
    let mut out = Vec::new();
    for &symbol in &solved.script.model_symbols {
        let (name, sort) = arena.symbol(symbol);
        let is_string = solved
            .script
            .declared_strings
            .iter()
            .any(|&(s, _)| s == symbol);
        // Read the model the front door ships beside its verdict, exactly as a
        // consumer would, falling back the way the rendering path falls back.
        let value = solved
            .model
            .as_ref()
            .and_then(|m| m.get(symbol))
            .or_else(|| result_model.get(symbol))
            .or_else(|| axeyum_ir::well_founded_default(arena, sort));
        let Some(value) = value else { continue };
        let literal = match (&value, is_string) {
            (Value::Bv { width, value: bits }, true) => {
                let bytes = decode_packed_string(*width, *bits)
                    .unwrap_or_else(|| panic!("`{name}` is not a well-formed packing"));
                format!("\"{}\"", String::from_utf8_lossy(&bytes))
            }
            (Value::Int(i), _) => format!("{i}"),
            (other, _) => panic!("`{name}` has an unrenderable value {other:?}"),
        };
        out.push((name.to_owned(), literal));
    }
    out
}

/// `src` with every model symbol pinned to the given literal, so the query is
/// ground and its verdict is evaluation of the ORIGINAL assertions.
fn pin(src: &str, bindings: &[(String, String)]) -> String {
    let mut out = String::new();
    for line in src.lines() {
        if line.trim_start().starts_with("(check-sat)") {
            for (name, literal) in bindings {
                let _ = writeln!(out, "(assert (= {name} {literal}))");
            }
        }
        out.push_str(line);
        out.push('\n');
    }
    out
}

/// Decides a pinned script through the front door.
#[track_caller]
fn verdict_of(src: &str) -> CheckResult {
    solve_smtlib_with_model(src, &SolverConfig::default())
        .unwrap_or_else(|e| panic!("front door failed: {e:?}\n{src}"))
        .outcome
        .result
}

/// **The test the coordinator found missing.** The model the front door reports
/// for a lifted word-route row must satisfy the ORIGINAL source assertions, not
/// merely make some replay return `Ok`.
#[test]
fn the_reported_model_satisfies_the_original_source_assertions() {
    let (solved, route) = solve(WORD_ROUTE_SHORT);
    assert_sat_via(
        "source-check",
        front_door_stage::WORD_ROUTE,
        &(solved, route),
    );
    let (solved, _) = solve(WORD_ROUTE_SHORT);
    let bindings = reported_model(&solved);
    assert!(
        bindings.len() >= 4,
        "expected the fixture's four model symbols, got {bindings:?}"
    );
    let pinned = pin(WORD_ROUTE_SHORT, &bindings);
    assert!(
        matches!(verdict_of(&pinned), CheckResult::Sat(_)),
        "the model the front door reports does NOT satisfy the source assertions.\n\
         reported: {bindings:?}\n--- pinned ---\n{pinned}"
    );

    // **The control.** The all-empty model — exactly what the defect produced,
    // and what `axeyum_cli` printed for this shape — must come back `unsat`.
    // Without this half the check above would pass on a build where pinning
    // silently did nothing, and prove nothing at all.
    let empty: Vec<(String, String)> = bindings
        .iter()
        .map(|(name, literal)| {
            let replacement = if literal.starts_with('"') {
                "\"\"".to_owned()
            } else {
                literal.clone()
            };
            (name.clone(), replacement)
        })
        .collect();
    assert_ne!(
        empty, bindings,
        "the control is identical to the subject, so it discriminates nothing"
    );
    assert!(
        matches!(
            verdict_of(&pin(WORD_ROUTE_SHORT, &empty)),
            CheckResult::Unsat
        ),
        "pinning every string to \"\" must be `unsat` for this query — if it is not, this \
         check cannot tell a good model from a bad one"
    );
}

/// The same question asked of the `(get-model)` RENDERING path, which is a
/// different function from the replay path and was still defaulting the packed
/// symbol after this lane's first landing.
///
/// `answer_get_model` reads `model.get(declared)` and falls back to
/// `well_founded_default`, so a source route that bound only `!weq!x` printed
/// `x = ""`. That is a wrong model, not a missing one, and nothing checked it.
#[test]
fn the_rendered_get_model_satisfies_the_original_source_assertions() {
    let with_get_model = format!("{WORD_ROUTE_SHORT}\n(get-model)");
    let responses = solve_smtlib_session(&with_get_model, &SolverConfig::default())
        .expect("the session decides");
    let rendered = responses
        .iter()
        .find_map(|r| match r {
            SmtLibResponse::Model(text) => Some(text.clone()),
            _ => None,
        })
        .expect("the session answered `(get-model)`");

    // Re-parse the rendered `define-fun` lines back into pinning assertions, so
    // what is checked is the TEXT a consumer is handed, not an internal value.
    let mut bindings = Vec::new();
    for line in rendered.lines() {
        let line = line.trim();
        let Some(rest) = line.strip_prefix("(define-fun ") else {
            continue;
        };
        let Some((name, rest)) = rest.split_once(" () ") else {
            continue;
        };
        let rest = rest.trim_end_matches(')');
        let Some((_sort, literal)) = rest.split_once(' ') else {
            continue;
        };
        bindings.push((name.to_owned(), literal.trim().to_owned()));
    }
    assert!(
        bindings.len() >= 4,
        "parsed {} bindings out of the rendered model, expected the fixture's four:\n{rendered}",
        bindings.len()
    );

    let pinned = pin(WORD_ROUTE_SHORT, &bindings);
    assert!(
        matches!(verdict_of(&pinned), CheckResult::Sat(_)),
        "`(get-model)` printed values that do NOT satisfy the source assertions — a WRONG \
         model, not a missing one.\n--- rendered ---\n{rendered}\n--- pinned ---\n{pinned}"
    );
}
