//! Word-first parse fallback (T-B.4d) at the full front door (`solve_smtlib`).
//!
//! The bounded ADR-0029 string encoder rejects a whole class of scripts *at
//! parse*: a string literal over the length cap (`STRING_MAX_LEN = 8`), a
//! `str.++` whose bounded result width exceeds the cap (`STRING_BOUND_CAP = 16`),
//! or another bounded-encoder capacity limit. These caps are an artifact of the
//! *bounded* encoding — a pure word-equation problem is decidable unbounded no
//! matter how long its literals or how wide its concats. The word-first fallback
//! retries such a declined parse with a word-level-only build (unbounded
//! `Seq(BitVec(18))` IR) and lets the sat-only, replay-checked word route decide
//! it.
//!
//! These are the exact shapes measured as `unsupported`-at-parse in the public
//! `cvc5-regress-clean` `QF_S`/`QF_SLIA` corpora (e.g. `issue6520`, `issue6681`),
//! reproduced here as minimal inline scripts (no NAS corpus path referenced).
//!
//! Two invariants are pinned:
//!
//! - **Coverage.** Scripts the bounded parse rejects, but which *are* pure word
//!   equations, now decide `sat` through the fallback — never a bounded parse
//!   error, never a wrong `unsat` (the word route has no `unsat` capability).
//! - **Honesty on decline.** A rejected script that is *not* a pure word-equation
//!   problem (e.g. it mixes in `str.indexof`) reproduces the **original** bounded
//!   parse error, so a previously-`unsupported` script never silently becomes a
//!   bare `unknown`/`sat`.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_solver::{
    CheckResult, SolverConfig, SolverError, solve_smtlib, solve_smtlib_incremental,
};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(10))
}

/// `issue6520` verbatim — a single pure word equation `(= (str.++ "AB" b c)
/// (str.++ c "B" a))`, declared `sat`. Its bounded result width (`2 + 8 + 8 = 18`)
/// exceeds `STRING_BOUND_CAP = 16`, so the bounded parse rejects it; the fallback's
/// word route decides it. `b`/`c` recur on both sides (a quadratic system), so the
/// search *may* burn its Skolem cap to `unknown` — acceptable — but it must never
/// return a wrong `unsat` or a bounded parse error.
#[test]
fn issue6520_decides_via_fallback() {
    let text = "(set-logic QF_SLIA)\
                (declare-fun a () String)(declare-fun b () String)(declare-fun c () String)\
                (assert (= (str.++ \"AB\" b c) (str.++ c \"B\" a)))\
                (set-info :status sat)(check-sat)";
    let outcome = solve_smtlib(text, &config()).expect("fallback decides, never a parse error");
    assert!(
        matches!(outcome.result, CheckResult::Sat(_)),
        "issue6520 is sat; the word-first fallback should decide it, got {:?}",
        outcome.result
    );
    // The declared `:status` is still surfaced for cross-checking.
    assert_eq!(outcome.expected_status.as_deref(), Some("sat"));
    assert_eq!(outcome.logic.as_deref(), Some("QF_SLIA"));
}

/// `issue6681` verbatim — a wide word equation whose bounded result width blows the
/// cap. Declared `sat`; the fallback decides it.
#[test]
fn issue6681_decides_via_fallback() {
    let text = "(set-logic QF_SLIA)\
                (declare-fun a () String)(declare-fun b () String)\
                (declare-fun c () String)(declare-fun d () String)\
                (assert (= (str.++ \"A\" a \"CBA\" b \"BA\" d) (str.++ b \"BA\" d a \"CBA\" c)))\
                (set-info :status sat)(check-sat)";
    let outcome = solve_smtlib(text, &config()).expect("fallback decides, never a parse error");
    assert!(
        matches!(outcome.result, CheckResult::Sat(_)),
        "issue6681 is sat; got {:?}",
        outcome.result
    );
}

/// An **over-long literal** (12 bytes > `STRING_MAX_LEN = 8`): the bounded parse
/// rejects the literal wholesale, and only the word-first fallback can decide the
/// (linear, hence easy) equation. The witness is fully concrete, so it is `sat`.
#[test]
fn over_long_literal_linear_decides() {
    let text = "(set-logic QF_S)\
                (declare-const x String)(declare-const y String)\
                (assert (= x (str.++ \"abcdefghijkl\" y)))(assert (= y \"mnop\"))(check-sat)";
    let outcome = solve_smtlib(text, &config()).expect("fallback decides the over-long literal");
    assert!(
        matches!(outcome.result, CheckResult::Sat(_)),
        "x = \"abcdefghijklmnop\" is sat; got {:?}",
        outcome.result
    );
}

/// A **wide variable concat** whose bounded result width (`8 + 8 + 8 = 24`) exceeds
/// `STRING_BOUND_CAP = 16` even with only 8-byte literals. The bounded parse
/// rejects it at the width cap; the fallback decides the linear system `sat`.
#[test]
fn wide_variable_concat_decides() {
    let text = "(set-logic QF_S)\
                (declare-const a String)(declare-const b String)(declare-const c String)\
                (assert (= c (str.++ \"AAAAAAAA\" a b)))(assert (= a \"xx\"))(assert (= b \"yy\"))\
                (check-sat)";
    let outcome = solve_smtlib(text, &config()).expect("fallback decides the wide concat");
    assert!(
        matches!(outcome.result, CheckResult::Sat(_)),
        "the wide concat is sat; got {:?}",
        outcome.result
    );
}

/// A rejected script that is **not** a pure word-equation problem — it mixes in
/// `str.indexof`, which none of the unbounded fallback routes represents — must
/// reproduce the **original** bounded parse error, not fabricate an
/// `unknown`/`sat`. This keeps
/// bench/consumer classification identical to the pre-fallback world for anything
/// the word route cannot legitimately upgrade.
#[test]
fn non_word_fragment_reproduces_original_error() {
    let text = "(set-info :status sat)(set-logic QF_SLIA)\
                (declare-const i0 Int)(declare-const s1 String)(declare-const s2 String)\
                (assert (= (str.++ s1 \"ijruldtzyp\") s2))\
                (assert (= (str.indexof s2 \"z\" 0) i0))(check-sat)";
    match solve_smtlib(text, &config()) {
        Err(SolverError::Parse(msg)) => {
            // The *bounded* encoder's original decline — surfaced unchanged.
            assert!(
                msg.contains("bounded length") || msg.contains("ADR-0029"),
                "expected the original bounded parse error, got: {msg}"
            );
        }
        other => panic!(
            "a non-word-fragment rejected script must reproduce the original parse \
             error, got {other:?}"
        ),
    }
}

/// The fallback also fronts the incremental entry point: a word-only script is
/// non-incremental by construction, so it yields exactly one decided result.
#[test]
fn incremental_entry_decides_word_only() {
    let text = "(set-logic QF_S)\
                (declare-const x String)(declare-const y String)\
                (assert (= x (str.++ \"abcdefghijkl\" y)))(assert (= y \"mnop\"))(check-sat)";
    let results = solve_smtlib_incremental(text, &config()).expect("incremental fallback decides");
    assert_eq!(results.len(), 1, "one implicit check-sat");
    assert!(
        matches!(results[0], CheckResult::Sat(_)),
        "got {:?}",
        results[0]
    );
}

/// A bounded-representable script is untouched by the fallback: it parses and
/// decides through the ordinary bounded path exactly as before.
#[test]
fn bounded_representable_is_untouched() {
    let text = "(set-logic QF_S)(declare-const x String)\
                (assert (= x (str.++ \"ab\" \"cd\")))(check-sat)";
    let outcome = solve_smtlib(text, &config()).expect("bounded path decides");
    assert!(matches!(outcome.result, CheckResult::Sat(_)));
}
