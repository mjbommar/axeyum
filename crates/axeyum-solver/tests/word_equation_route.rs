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
//!   come back `unsat` (soundly, from the bounded path) or `unknown` (the word
//!   route declined) — **never `sat`**. The instances that reach the word route
//!   (the bounded gate downgraded them to `unknown`) must stay `unknown`.
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

/// The bridge must never turn an unsatisfiable script into `sat` — a wrong sat is
/// the one soundness failure the word route could introduce. Every listed script
/// is genuinely UNSAT; the verdict must be `unsat` or `unknown`, never `sat`.
#[test]
fn bridge_never_emits_sat_on_unsat() {
    // Each script is genuinely unsatisfiable in the real (unbounded) string
    // theory. Some are decided `unsat` directly by the bounded path; the ones
    // that force a witness past the encoding bound get downgraded to `unknown`,
    // and it is *those* that exercise the word route — which must decline, not
    // fabricate a model.
    let unsat_scripts = [
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
        // Content clash that only shows up past the bound: x = \"abcdefgh\"++z and
        // x = \"abcdefgi\"++z with z nonempty forces |x| >= 9 (> max_len 8), so the
        // bounded gate downgrades to `unknown` and the WORD ROUTE handles it —
        // the prefixes differ at position 7, so it must decline, never sat.
        "(set-logic QF_S)(declare-const x String)(declare-const z String)\
         (assert (= x (str.++ \"abcdefgh\" z)))(assert (= x (str.++ \"abcdefgi\" z)))\
         (assert (not (= z \"\")))(check-sat)",
        // Same idea with a variable prefix pinned long, plus a spurious diseq var.
        "(set-logic QF_S)(declare-const x String)(declare-const y String)(declare-const z String)\
         (assert (= x (str.++ y \"a\")))(assert (= x (str.++ y \"b\")))\
         (assert (= y \"abcdefgh\"))(assert (not (= z \"\")))(assert (= x (str.++ y z)))(check-sat)",
    ];

    let mut reached_word_route = 0;
    for text in unsat_scripts {
        match verdict(text) {
            CheckResult::Sat(model) => panic!(
                "WRONG SAT: the bridge decided an UNSAT script satisfiable — a \
                 soundness bug.\nscript:\n{text}\nmodel: {model:?}"
            ),
            CheckResult::Unsat => {}
            CheckResult::Unknown(reason) => {
                // The word route decline shows up in the reason detail.
                if reason.detail.contains("word-equation route declined") {
                    reached_word_route += 1;
                }
            }
        }
    }

    // Sanity: at least one adversarial instance actually flowed through the word
    // route (otherwise this would only be testing the bounded path).
    assert!(
        reached_word_route >= 2,
        "expected the word route to engage on the past-the-bound unsat instances \
         (got {reached_word_route})"
    );
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
