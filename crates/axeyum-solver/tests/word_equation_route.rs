//! Bridge regression for the word-equation second-chance route (ADR-0053,
//! T-B.4b).
//!
//! The word-level arrangement search behind the bounded gate can only ever
//! **add** `sat` where the ADR-0029 bounded pre-check + ADR-0052 gate returned
//! `unknown`; it has no `unsat` capability by construction, and every `sat` it
//! returns has replayed against the original equalities/disequalities through the
//! ground evaluator inside `axeyum-strings`. This test pins both halves of that
//! contract at the **full front door** (`solve_smtlib`):
//!
//! - **The bridge never emits a wrong verdict on an UNSAT instance.** A family of
//!   adversarially unsatisfiable word-equation scripts is decided; every one must
//!   come back `unsat` or `unknown` — **never `sat`**.
//! - **The bridge adds a re-checked `unsat` (ADR-0053, T-B.7).** The word route
//!   now decides `unsat`, but *only* through an independently re-checked
//!   derivation. Scripts whose refutation is a checkable **constant clash** past
//!   the bounded encoder's `max_len` — which the bounded gate downgrades to
//!   `unknown` — are now decided `unsat` by the word route's refuter. Shapes that
//!   are not an aligned constant clash (loops, parity/length arguments) are never
//!   certified by the word route; at the full front door they are still decided
//!   `unsat` by the bounded ADR-0052 length abstraction (never reaching the word
//!   route), and the word route's own decline on those shapes is pinned directly
//!   in `axeyum-strings` (the `check_derivation` / `refute_property` suites).
//! - **The bridge adds `sat` for genuinely-satisfiable instances the bounded path
//!   cannot decide.** Scripts whose only witness exceeds the bounded encoder's
//!   `max_len` (a variable forced past 8 bytes by literal concatenation) return
//!   `unknown` from the bounded gate today; the word route now decides them `sat`.

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

fn verdict(text: &str) -> CheckResult {
    solve_smtlib(text, &SolverConfig::default())
        .unwrap_or_else(|e| panic!("front door errored on:\n{text}\nerror: {e}"))
        .result
}

/// Every genuinely-unsatisfiable word-equation script, regardless of which route
/// decides it. Split by *how* they are (soundly) decided at the front door.
const UNSAT_SCRIPTS: &[&str] = &[
    // x = "a" ++ x  — a length loop (|x| = 1 + |x|), unsatisfiable.
    "(set-logic QF_S)(declare-const x String)\
     (assert (= x (str.++ \"a\" x)))(check-sat)",
    // x = x ++ "a"  — the append loop.
    "(set-logic QF_S)(declare-const x String)\
     (assert (= x (str.++ x \"a\")))(check-sat)",
    // Mutual loop x = y++\"a\", y = x++\"b\".
    "(set-logic QF_S)(declare-const x String)(declare-const y String)\
     (assert (= x (str.++ y \"a\")))(assert (= y (str.++ x \"b\")))(check-sat)",
    // Distinct constants equated.
    "(set-logic QF_S)(assert (= \"a\" \"b\"))(check-sat)",
    // Suffix clash: x++\"a\" = x++\"b\".
    "(set-logic QF_S)(declare-const x String)\
     (assert (= (str.++ x \"a\") (str.++ x \"b\")))(check-sat)",
    // Prefix clash: x = \"ab\"++y and x = \"cd\"++y.
    "(set-logic QF_S)(declare-const x String)(declare-const y String)\
     (assert (= x (str.++ \"ab\" y)))(assert (= x (str.++ \"cd\" y)))(check-sat)",
    // x=x++x with x nonempty (a parity/length contradiction).
    "(set-logic QF_S)(declare-const x String)\
     (assert (= x (str.++ x x)))(assert (not (= x \"\")))(check-sat)",
];

/// The soundness pin: no unsatisfiable script may ever be decided `sat`, on any
/// route. A wrong `sat` is the one failure the word route could introduce.
#[test]
fn no_unsat_script_is_ever_sat() {
    for &text in UNSAT_SCRIPTS.iter().chain(PAST_BOUND_CONST_CLASH_UNSAT) {
        if let CheckResult::Sat(model) = verdict(text) {
            panic!(
                "WRONG SAT: decided an UNSAT script satisfiable — a soundness bug.\n\
                 script:\n{text}\nmodel: {model:?}"
            );
        }
    }
}

/// Past-the-bound **constant clashes** whose refutation is an aligned constant
/// clash the T-B.7 checker can re-derive. The bounded encoder cannot decide them
/// (the witness is forced past `max_len 8`), so before T-B.7 they were downgraded
/// to `unknown`; now the word route's independently re-checked refutation decides
/// them `unsat`.
const PAST_BOUND_CONST_CLASH_UNSAT: &[&str] = &[
    // x = "abcdefgh"++z and x = "abcdefgi"++z with z nonempty: |x| >= 9 (> max_len
    // 8) downgrades the bounded gate; the two 8-char constant blocks differ at
    // position 7, an aligned constant clash the checker certifies.
    "(set-logic QF_S)(declare-const x String)(declare-const z String)\
     (assert (= x (str.++ \"abcdefgh\" z)))(assert (= x (str.++ \"abcdefgi\" z)))\
     (assert (not (= z \"\")))(check-sat)",
    // A variable prefix pinned long, plus a spurious diseq var: x=y++"a", x=y++"b"
    // ⇒ y++"a" ≈ y++"b", a suffix constant clash after the shared y.
    "(set-logic QF_S)(declare-const x String)(declare-const y String)(declare-const z String)\
     (assert (= x (str.++ y \"a\")))(assert (= x (str.++ y \"b\")))\
     (assert (= y \"abcdefgh\"))(assert (not (= z \"\")))(assert (= x (str.++ y z)))(check-sat)",
];

/// The T-B.7 capability, end to end: a past-the-bound constant clash the bounded
/// path downgrades is now decided `unsat` by the word route's re-checked
/// refutation. (With the refuter disabled these return `unknown`; see the module
/// history — this is the one behavior T-B.7 adds at the front door.)
#[test]
fn past_bound_constant_clash_refutes_to_unsat() {
    for &text in PAST_BOUND_CONST_CLASH_UNSAT {
        assert!(
            matches!(verdict(text), CheckResult::Unsat),
            "the past-the-bound constant clash must now decide unsat via the \
             re-checked word-equation refutation:\n{text}\ngot: {:?}",
            verdict(text)
        );
    }
}

/// The bounded ADR-0052 length abstraction soundly decides the loop / parity
/// shapes `unsat` *before* the word route runs (a length argument the word route
/// deliberately does not certify — that decline is pinned in `axeyum-strings`).
/// Here we only require the front-door verdict is a sound one: `unsat` or
/// `unknown`, never `sat`.
#[test]
fn loop_and_parity_shapes_are_sound() {
    for &text in UNSAT_SCRIPTS {
        assert!(
            matches!(verdict(text), CheckResult::Unsat | CheckResult::Unknown(_)),
            "an unsat loop/parity/clash shape must be unsat or unknown, never sat:\n{text}"
        );
    }
}

/// The word route decides genuinely-satisfiable instances the bounded encoder
/// cannot: the witness exceeds the `max_len 8` encoding bound, so the bounded
/// gate returns `unknown` today, and the word route upgrades to `sat`.
#[test]
fn bridge_adds_sat_beyond_the_bound() {
    let sat_scripts = [
        // x = "abcdefgh" ++ z, z = "xyz"  ⇒  x = "abcdefghxyz" (11 > 8 bytes).
        "(set-logic QF_S)(declare-const x String)(declare-const z String)\
         (assert (= x (str.++ \"abcdefgh\" z)))(assert (= z \"xyz\"))(check-sat)",
        // x = y ++ y, y = "abcde"  ⇒  x = "abcdeabcde" (10 > 8 bytes).
        "(set-logic QF_S)(declare-const x String)(declare-const y String)\
         (assert (= x (str.++ y y)))(assert (= y \"abcde\"))(check-sat)",
        // x = "abcdefgh" ++ z with z nonempty  ⇒  |x| >= 9 > 8.
        "(set-logic QF_S)(declare-const x String)(declare-const z String)\
         (assert (= x (str.++ \"abcdefgh\" z)))(assert (not (= z \"\")))(check-sat)",
        // x = y ++ z, y and z both maximal 8-byte literals ⇒ |x| = 16 > 8.
        "(set-logic QF_S)(declare-const x String)(declare-const y String)(declare-const z String)\
         (assert (= x (str.++ y z)))(assert (= y \"aaaaaaaa\"))(assert (= z \"bbbbbbbb\"))(check-sat)",
    ];

    for text in sat_scripts {
        match verdict(text) {
            CheckResult::Sat(_) => {}
            other => panic!(
                "expected the word route to decide this SAT (witness > max_len 8):\n\
                 {text}\ngot: {other:?}"
            ),
        }
    }
}

/// A pure word-equation script the bounded path already decides `sat` within the
/// bound is unaffected — the word route only fires on `unknown`, so the fast
/// bounded verdict stands.
#[test]
fn bounded_sat_within_bound_is_untouched() {
    let text = "(set-logic QF_S)(declare-const x String)\
                (assert (= x (str.++ \"ab\" \"cd\")))(check-sat)";
    assert!(matches!(verdict(text), CheckResult::Sat(_)));
}

/// A script outside the pure word-equation fragment (`str.len` here) must not
/// build a word-problem side channel, so the bridge is inert and the bounded
/// verdict is returned unchanged.
#[test]
fn non_word_fragment_is_not_routed() {
    // `str.len` is not representable as a word equation; the side channel stays
    // `None`, so whatever the bounded path returns is returned verbatim.
    let text = "(set-logic QF_SLIA)(declare-const x String)\
                (assert (= (str.len x) 3))(assert (= x \"abc\"))(check-sat)";
    // The bounded path decides this small instance; the important property is
    // simply that it is not a wrong verdict (sat, with x = "abc").
    assert!(matches!(
        verdict(text),
        CheckResult::Sat(_) | CheckResult::Unknown(_)
    ));
}

// --- positive-polarity extended-function reductions (T-B.4c) -----------------
//
// `(str.prefixof p x)`, `(str.suffixof s x)`, and `(str.contains x c)` in a
// positive (top-level-conjunction) position reduce to fresh-variable word
// equations that are equisatisfiable with the atom:
//
//     prefixof(p, x) ⟺ ∃k.     x = p ++ k
//     suffixof(s, x) ⟺ ∃k.     x = k ++ s
//     contains(x, c) ⟺ ∃k1,k2. x = k1 ++ c ++ k2
//
// Each is *sat-implying*, so a replay-checked `Sat` of the reduced problem is a
// genuine `Sat` of the original.
//
// NOTE on witness length: the bounded front-end hard-errors on a *single* string
// literal longer than `max_len 8`, on a `str.++` whose result exceeds the parse
// cap 16, and it constant-folds `str.++` of two literals into one literal (which
// then trips the >8 check). So — exactly as the existing `beyond_bound` sat tests
// do — the past-the-bound operands below are built as `"8-char-lit" ++ var` with
// the `var` pinned to a second 8-char literal, giving a 16-char term (2× max_len
// 8) that never folds and stays within the cap. A 16-char witness is past
// `max_len 8`, so the bounded gate cannot decide it and downgrades to `unknown`;
// the unbounded word search then decides it `sat`.

/// A positive `str.contains` whose needle is forced to 16 chars — so any witness
/// runs past `max_len 8` — decides `sat` via the word route.
#[test]
fn word_route_positive_contains_beyond_bound() {
    // c = "abcdefgh" ++ w, w = "ijklmnop"  ⇒  c = "abcdefghijklmnop" (16). x must
    // be ≥ 16 to contain c, past max_len 8 ⇒ bounded `unknown`. The reduction
    // x = k1 ++ c ++ k2 is satisfied by x = c (k1 = k2 = "").
    let text = "(set-logic QF_S)(declare-const x String)(declare-const c String)(declare-const w String)\
                (assert (= c (str.++ \"abcdefgh\" w)))(assert (= w \"ijklmnop\"))\
                (assert (str.contains x c))(check-sat)";
    assert!(
        matches!(verdict(text), CheckResult::Sat(_)),
        "positive str.contains with a 16-char needle should decide sat via the word route"
    );
}

/// A positive `str.prefixof` whose prefix is forced to 16 chars decides `sat`
/// via the word route.
#[test]
fn word_route_positive_prefixof_beyond_bound() {
    // p = "abcdefgh" ++ w, w = "ijklmnop"  ⇒  p = 16 chars. prefixof(p, x) forces
    // |x| ≥ 16 (bounded `unknown`); the reduction x = p ++ k is satisfied by x = p.
    let text = "(set-logic QF_S)(declare-const x String)(declare-const p String)(declare-const w String)\
                (assert (= p (str.++ \"abcdefgh\" w)))(assert (= w \"ijklmnop\"))\
                (assert (str.prefixof p x))(check-sat)";
    assert!(
        matches!(verdict(text), CheckResult::Sat(_)),
        "positive str.prefixof with a 16-char prefix should decide sat via the word route"
    );
}

/// A positive `str.suffixof` whose suffix is forced to 16 chars decides `sat`
/// via the word route.
#[test]
fn word_route_positive_suffixof_beyond_bound() {
    // s = "abcdefgh" ++ w, w = "ijklmnop"  ⇒  s = 16 chars. suffixof(s, x) forces
    // |x| ≥ 16 (bounded `unknown`); the reduction x = k ++ s is satisfied by x = s.
    let text = "(set-logic QF_S)(declare-const x String)(declare-const s String)(declare-const w String)\
                (assert (= s (str.++ \"abcdefgh\" w)))(assert (= w \"ijklmnop\"))\
                (assert (str.suffixof s x))(check-sat)";
    assert!(
        matches!(verdict(text), CheckResult::Sat(_)),
        "positive str.suffixof with a 16-char suffix should decide sat via the word route"
    );
}

/// A mixed script — word equations plus a positive `str.contains` — decides
/// `sat` via the word route. The concatenation forces x to 16 chars (past the
/// bound) and the contains needle is consistent with it.
#[test]
fn word_route_mixed_equations_and_contains() {
    // x = y ++ "abcdefgh", y = "12345678"  ⇒  x = "12345678abcdefgh" (16 chars,
    // 2× max_len 8), and x contains the literal "abcdefgh" — satisfiable, but
    // past the bounded encoder.
    let text = "(set-logic QF_S)\
                (declare-const x String)(declare-const y String)\
                (assert (= x (str.++ y \"abcdefgh\")))(assert (= y \"12345678\"))\
                (assert (str.contains x \"abcdefgh\"))(check-sat)";
    assert!(
        matches!(verdict(text), CheckResult::Sat(_)),
        "mixed equations + positive str.contains should decide sat via the word route"
    );
}

/// **Polarity guard.** A *negative* `str.contains` (`(not (str.contains …))`) is
/// not a sat-implying reduction, so the dual build must decline wholesale — the
/// side channel stays `None` and the word route can never emit `sat` for it.
///
/// This instance is adversarially UNSAT: `x` is forced to a 16-char constant that
/// *does* contain the needle, so `(not (str.contains x needle))` is false and the
/// script is unsatisfiable. Because `x` runs past the bounded encoder's
/// `max_len 8`, the bounded gate downgrades to `unknown` — so a *broken* polarity
/// guard (reducing the contains positively, ignoring the `not`) would let the
/// word route find `x = k1 ++ needle ++ k2` and fabricate a WRONG `sat`. A correct
/// guard declines the whole side channel, leaving the verdict `unsat`/`unknown` —
/// never `sat`.
#[test]
fn word_route_negative_contains_declines() {
    let text = "(set-logic QF_S)(declare-const x String)(declare-const w String)\
                (assert (= x (str.++ \"abcdefgh\" w)))(assert (= w \"ijklmnop\"))\
                (assert (not (str.contains x \"abcdefgh\")))(check-sat)";
    match verdict(text) {
        CheckResult::Sat(model) => panic!(
            "WRONG SAT: negative str.contains must not be decided `sat` by the \
             word route (the reduction is only sound in positive position).\n\
             model: {model:?}"
        ),
        CheckResult::Unsat | CheckResult::Unknown(_) => {}
    }
}

/// **Polarity guard.** A `str.contains` under `or` is a disjunctive (non
/// positive-conjunction) position; the dual build recognizes no `or`, so the
/// whole side channel collapses to `None` and the word route is inert.
///
/// Adversarially UNSAT: `x` is a 16-char constant containing neither disjunct's
/// needle/prefix, so the `or` is false and the script is unsatisfiable. `x` is
/// past the bound, so the bounded gate downgrades to `unknown`; a broken guard
/// that reduced either disjunct positively would fabricate a WRONG `sat`. A
/// correct build declines (the top-level `or` is unrepresentable), so the verdict
/// is `unsat`/`unknown` — never `sat`.
#[test]
fn word_route_contains_under_or_declines() {
    let text = "(set-logic QF_S)(declare-const x String)(declare-const w String)\
                (assert (= x (str.++ \"abcdefgh\" w)))(assert (= w \"ijklmnop\"))\
                (assert (or (str.contains x \"zzz\") (str.prefixof \"qqq\" x)))(check-sat)";
    match verdict(text) {
        CheckResult::Sat(model) => panic!(
            "WRONG SAT: a str.contains/prefixof under `or` must not be decided \
             `sat` by the word route.\nmodel: {model:?}"
        ),
        CheckResult::Unsat | CheckResult::Unknown(_) => {}
    }
}
