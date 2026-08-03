//! The **string-bound ladder**: the text front door's last second chance.
//!
//! The packed ADR-0029 encoding models each declared `String` as a fixed 12-byte
//! window. A query that is genuinely `sat`, but whose every witness needs a longer
//! string, therefore encodes as a *bounded* `unsat` and used to surface as
//! `unknown` ("no model within the bounded integer width …"). `solve_smtlib` now
//! re-parses at successively wider windows (24 / 32 / 48) and returns the first
//! `Sat`.
//!
//! Why this file is mostly negative tests: the ladder's whole safety claim is that
//! it is **strictly additive** — it fires only on that one `unknown`, accepts only
//! `Sat`, and shares the front door's single wall-clock deadline. A wider-window
//! `unsat` is still a bound artifact and must never be reported as a query
//! `unsat`, so the tests below pin "does not change a decided verdict" at least as
//! hard as they pin "decides more".
//!
//! Provenance of the rungs: they were chosen by measuring the `QF_SLIA` parity
//! residual (`bench-results/parity-lists/QF_SLIA.txt`), where rung 24 first
//! decides two `20180523-Reynolds/pyex` files, rung 32 adds a `kaluza` file, and
//! rung 48 adds a `20230327-stringfuzz-lu` file — all four `sat`, all four
//! agreeing with cvc5.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_solver::{Value, solve_smtlib_get_model, solve_smtlib_get_value};

use axeyum_ir::Sort;
use axeyum_smtlib::{parse_script, parse_script_with_string_bound};
use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(20))
}

fn verdict(src: &str) -> CheckResult {
    solve_smtlib(src, &config())
        .expect("front door decides the script")
        .result
}

/// A witness must hold a 20-byte literal, so no string inside the default 12-byte
/// window satisfies it — the shape the ladder exists for.
const NEEDS_A_LONG_WITNESS: &str = "\
(set-logic QF_S)
(declare-const x String)
(assert (str.contains x \"abcdefghijklmnopqrst\"))
(check-sat)
";

/// The packed sort width of the single declared `String` symbol.
fn declared_string_width(src: &str, floor: Option<u32>) -> u32 {
    let script = match floor {
        None => parse_script(src),
        Some(floor) => parse_script_with_string_bound(src, floor),
    }
    .expect("script parses");
    let (_, _, sort) = script
        .arena
        .symbols()
        .find(|&(_, name, _)| name == "x")
        .expect("the declared String symbol `x` is in the arena");
    match sort {
        Sort::BitVec(width) => width,
        other => panic!("a packed String symbol is a BitVec, got {other:?}"),
    }
}

/// The mechanism: a wider floor really does widen the declared symbol's packed
/// window. Without this, a `sat` below could be coming from some unrelated route
/// and the ladder could be dead code that still passes the capability test.
#[test]
fn a_wider_floor_widens_the_declared_string_window() {
    let default = declared_string_width(NEEDS_A_LONG_WITNESS, None);
    let explicit_default = declared_string_width(NEEDS_A_LONG_WITNESS, Some(12));
    let wide = declared_string_width(NEEDS_A_LONG_WITNESS, Some(48));
    assert_eq!(
        default, explicit_default,
        "the default floor must reproduce `parse_script` exactly"
    );
    assert!(
        wide > default,
        "floor 48 must widen the packed window (default {default} bits, wide {wide} bits)"
    );
}

/// A floor below the default only ever widens — it is clamped, never narrowing the
/// window (which would be the one direction that could LOSE a witness).
#[test]
fn a_floor_below_the_default_is_clamped_not_applied() {
    let default = declared_string_width(NEEDS_A_LONG_WITNESS, None);
    for floor in [0, 1, 4, 11] {
        assert_eq!(
            declared_string_width(NEEDS_A_LONG_WITNESS, Some(floor)),
            default,
            "floor {floor} must clamp up to the default, never narrow the window"
        );
    }
}

/// The capability: the front door decides the long-witness query.
#[test]
fn the_ladder_decides_a_witness_past_the_default_window() {
    assert!(
        matches!(verdict(NEEDS_A_LONG_WITNESS), CheckResult::Sat(_)),
        "a 20-byte witness is reachable at rung 24"
    );
}

/// SOUNDNESS. A genuine `unsat` must stay `unsat` — the ladder never runs on a
/// decided verdict at all.
#[test]
fn a_genuine_unsat_is_untouched() {
    for src in [
        "(set-logic QF_S)\n(declare-const x String)\n(assert (= x \"a\"))\n\
         (assert (= x \"b\"))\n(check-sat)\n",
        // Both literals are past the default window, so the wider rungs would
        // happily encode them — and must still not manufacture a model.
        "(set-logic QF_S)\n(declare-const x String)\n\
         (assert (= x \"abcdefghijklmnopqrst\"))\n\
         (assert (= x \"abcdefghijklmnopqrsu\"))\n(check-sat)\n",
        // Unsatisfiable only for a length reason that no window can relieve.
        "(set-logic QF_S)\n(declare-const x String)\n\
         (assert (str.prefixof \"abcdefghijklmnopqrst\" x))\n\
         (assert (= (str.len x) 3))\n(check-sat)\n",
    ] {
        assert_eq!(
            verdict(src),
            CheckResult::Unsat,
            "the ladder must not disturb a genuine unsat:\n{src}"
        );
    }
}

/// SOUNDNESS. A wider window's `unsat` is a bound artifact, not a query `unsat`.
/// This query IS satisfiable (`x` is 60 bytes), past every rung — the ladder must
/// therefore leave it `unknown`, never report `unsat`.
#[test]
fn a_witness_past_every_rung_stays_unknown_never_unsat() {
    let src = "(set-logic QF_S)\n(declare-const x String)\n\
               (assert (= (str.len x) 60))\n\
               (assert (str.prefixof \"abcdefghijklmnopqrst\" x))\n\
               (assert (str.suffixof \"tsrqponmlkjihgfedcba\" x))\n(check-sat)\n";
    match verdict(src) {
        CheckResult::Unsat => {
            panic!("WRONG-UNSAT: a satisfiable 60-byte query was refuted by a bounded window")
        }
        CheckResult::Sat(_) | CheckResult::Unknown(_) => {}
    }
}

/// An already-`sat` query is returned by the default rung and never re-solved.
#[test]
fn an_already_sat_query_is_untouched() {
    let src = "(set-logic QF_S)\n(declare-const x String)\n\
               (assert (= x \"abc\"))\n(check-sat)\n";
    assert!(matches!(verdict(src), CheckResult::Sat(_)));
}

/// A non-string query cannot reach the ladder at all (no declared `String`), and
/// must be bit-for-bit unaffected.
#[test]
fn a_string_free_query_is_unaffected() {
    let src = "(set-logic QF_BV)\n(declare-const a (_ BitVec 8))\n\
               (assert (= (bvadd a #x01) #x00))\n(check-sat)\n";
    assert!(matches!(verdict(src), CheckResult::Sat(_)));
}

/// Determinism is a public API promise: the same text decides the same way every
/// time, ladder or not.
#[test]
fn the_ladder_is_deterministic() {
    let first = verdict(NEEDS_A_LONG_WITNESS);
    for _ in 0..3 {
        assert_eq!(
            std::mem::discriminant(&first),
            std::mem::discriminant(&verdict(NEEDS_A_LONG_WITNESS)),
            "repeated runs must agree"
        );
    }
}

/// The ladder shares the front door's single deadline; a tiny budget must not let
/// it run three extra full-budget solves.
#[test]
fn the_ladder_honours_the_front_door_budget() {
    let config = SolverConfig::new().with_timeout(Duration::from_millis(200));
    let start = std::time::Instant::now();
    let _ = solve_smtlib(NEEDS_A_LONG_WITNESS, &config);
    assert!(
        start.elapsed() < Duration::from_secs(10),
        "a 200 ms budget must not become four full solves (took {:?})",
        start.elapsed()
    );
}

/// The full-grammar guard the repo learned the hard way: a widened window must
/// handle `\\u{…}` / `\\uXXXX` escapes and code points above `0xFF` the same way
/// the default window does — either decide, or decline; never a wrong verdict.
#[test]
fn escapes_and_wide_code_points_never_produce_a_wrong_verdict() {
    // `\u{41}` is `A`; the query is satisfiable by `x = "AAAAAAAAAAAAAAAA"`.
    let sat_src = "(set-logic QF_S)\n(declare-const x String)\n\
                   (assert (str.contains x \"\\u{41}\\u{41}\\u{41}\\u{41}\\u{41}\\u{41}\\u{41}\
                   \\u{41}\\u{41}\\u{41}\\u{41}\\u{41}\\u{41}\\u{41}\\u{41}\\u{41}\"))\n\
                   (check-sat)\n";
    assert_ne!(
        verdict(sat_src),
        CheckResult::Unsat,
        "WRONG-UNSAT on an escaped-literal query that `x = \"A\"*16` satisfies"
    );
    // A code point above 0xFF (`\u{1F600}`) is outside the byte-packed window; the
    // encoder may decline it, but must never refute a satisfiable query.
    let wide_src = "(set-logic QF_S)\n(declare-const x String)\n\
                    (assert (= x \"\\u{1F600}\"))\n(check-sat)\n";
    assert_ne!(
        verdict(wide_src),
        CheckResult::Unsat,
        "WRONG-UNSAT: `x = \"\\u{{1F600}}\"` is trivially satisfiable"
    );
}

/// `(get-value)` on a declared `String` renders a string, and a genuine
/// bit-vector of the SAME width is left alone.
///
/// Measured defect 2026-08-02: `(get-value (x))` on `(declare-fun x () String)`
/// returned `Bv { width: 100, value: 271378 }` instead of `"AB"` — ADR-0029
/// packs a String into a bit-vector and nothing decoded it on the way out. A
/// consumer cannot read that, and SMT-COMP's Model Validation track would
/// reject it.
///
/// The negative half is the load-bearing one: decoding on WIDTH would render a
/// real `(_ BitVec 100)` as a bogus string, turning a representation bug into a
/// wrong model — strictly worse than an unreadable one.
#[test]
fn get_value_renders_a_declared_string_and_spares_a_same_width_bitvector() {
    let cfg = SolverConfig::new().with_timeout(Duration::from_secs(30));

    let values = solve_smtlib_get_value(
        "(set-logic QF_SLIA)\n(declare-fun x () String)\n(assert (= x \"AB\"))\n(check-sat)\n(get-value (x))\n",
        &cfg,
    )
    .expect("string get-value solves")
    .expect("a model exists");
    match &values[..] {
        [Value::Seq(elems)] => {
            let bytes: Vec<u128> = elems
                .iter()
                .map(|e| match e {
                    Value::Bv { value, .. } => *value,
                    other => panic!("a string element must be a code point, got {other:?}"),
                })
                .collect();
            assert_eq!(bytes, vec![65, 66], "\"AB\" must render as its code points");
        }
        other => panic!("a declared String must render as a Seq, got {other:?}"),
    }

    let values = solve_smtlib_get_value(
        "(set-logic QF_BV)\n(declare-fun b () (_ BitVec 100))\n(assert (= b (_ bv271378 100)))\n(check-sat)\n(get-value (b))\n",
        &cfg,
    )
    .expect("bitvector get-value solves")
    .expect("a model exists");
    match &values[..] {
        [Value::Bv { width, value }] => {
            assert_eq!(
                (*width, *value),
                (100, 271_378),
                "a genuine BV is untouched"
            );
        }
        other => panic!("a same-width bit-vector must NOT be decoded, got {other:?}"),
    }
}

/// `(get-model)` renders a declared `String` as a string too, not just
/// `(get-value)`.
///
/// The two are separate export paths, and fixing one first did NOT fix the
/// other — a distinction that cost a wrong assumption when this defect was
/// being tracked. Same rule on both: rewrite only what `declared_strings`
/// lists, so a genuine bit-vector of the same width is untouched.
#[test]
fn get_model_renders_a_declared_string() {
    let cfg = SolverConfig::new().with_timeout(Duration::from_secs(30));
    let model = solve_smtlib_get_model(
        "(set-logic QF_SLIA)\n(declare-fun x () String)\n(assert (= x \"AB\"))\n(check-sat)\n(get-model)\n",
        &cfg,
    )
    .expect("string get-model solves")
    .expect("a model exists");
    let (_, value) = model
        .constants
        .iter()
        .find(|(name, _)| name == "x")
        .expect("x appears in the model");
    match value {
        Value::Seq(elements) => {
            let bytes: Vec<u128> = elements
                .iter()
                .map(|e| match e {
                    Value::Bv { value, .. } => *value,
                    other => panic!("a string element must be a code point, got {other:?}"),
                })
                .collect();
            assert_eq!(bytes, vec![65, 66], "\"AB\" must render as its code points");
        }
        other => panic!("a declared String must render as a Seq in get-model, got {other:?}"),
    }
}
