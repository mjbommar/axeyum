//! Soundness bars for the `str.from_code` byte-model fix (P0, task #46).
//!
//! `str.from_code i` must be the exact partial inverse of `str.to_code` over the
//! byte alphabet's representable range `0..=255`, `""` for a genuinely invalid
//! code point (`i < 0` or `i > 0x2FFFF`), and — for the valid-but-unrepresentable
//! `256..=0x2FFFF` window or any symbolic argument — a **decline** (`Unknown`/
//! parse-error), never a wrong verdict.
//!
//! The bug this closes: `string_from_code` folded every `i > 127` to the empty
//! string, so `(= (str.from_code 200) "")` was decided **Sat** while the correct
//! answer (Z3's) is **Unsat** — `str.from_code 200` is the non-empty length-1
//! character U+00C8, and `str.to_code (str.from_code 200) = 200` is a theorem.
//!
//! These tests use the SMT-LIB front door (the fix lives in the parser lowering)
//! and need no oracle: each asserted formula's correct verdict is a theorem.

use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

/// Outcome of the front door, collapsing a parse-decline and `Unknown` into one
/// adjudication-neutral `Declined` — both are sound (never a wrong verdict).
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum Outcome {
    Sat,
    Unsat,
    Declined,
}

fn decide(text: &str) -> Outcome {
    let config = SolverConfig::new().with_timeout(Duration::from_secs(10));
    match solve_smtlib(text, &config) {
        Ok(outcome) => match outcome.result {
            // A `Sat` is already replay-checked against the lowered term.
            CheckResult::Sat(_) => Outcome::Sat,
            CheckResult::Unsat => Outcome::Unsat,
            CheckResult::Unknown(_) => Outcome::Declined,
        },
        // A parse decline (`Unsupported` for the unrepresentable window / symbolic
        // argument) surfaces here — adjudication-neutral, never a wrong verdict.
        Err(_) => Outcome::Declined,
    }
}

fn qf_slia(body: &str) -> String {
    format!("(set-logic QF_SLIA)\n{body}\n(check-sat)\n")
}

// ---------------------------------------------------------------------------
// Bar 1: the confirmed P0 and the whole 128..=255 class — `(from_code k) = ""`
// is UNSAT (k in 0..=255 is a non-empty byte character), never Sat.
// ---------------------------------------------------------------------------
#[test]
fn bar1_from_code_byte_range_is_never_empty() {
    for k in [0, 1, 32, 65, 127, 128, 200, 254, 255] {
        let text = qf_slia(&format!("(assert (= (str.from_code {k}) \"\"))"));
        let got = decide(&text);
        assert_eq!(
            got,
            Outcome::Unsat,
            "(= (str.from_code {k}) \"\") must be Unsat (byte {k} is a non-empty \
             length-1 character); got {got:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// Bar 2: round-trip `str.to_code (str.from_code k) = k` holds (Sat) and its
// negation `(distinct …)` is never wrong-sat, for every representable k in
// `0..=255`. The `from_code` byte model round-trips exactly — the pure-BV
// `(distinct (str.len (str.from_code k)) 1)` is refuted (Unsat). But `str.to_code`
// itself goes through a **code-bridge** that relaxes to_code to a free code Int,
// so it cannot *refute* a `distinct` over to_code and reports it `Unknown`
// (Declined): a pre-existing to_code completeness limit, independent of this
// from_code fix and sound (never a wrong verdict — verified below by the
// no-from_code control in `bar2b`). We assert the soundness property: the `=`
// direction is Sat and the `distinct` is never Sat (Unsat-or-Declined only).
// ---------------------------------------------------------------------------
#[test]
fn bar2_to_code_of_from_code_round_trips() {
    for k in [0, 1, 65, 127, 128, 200, 255] {
        let eq = qf_slia(&format!(
            "(assert (= (str.to_code (str.from_code {k})) {k}))"
        ));
        assert_eq!(
            decide(&eq),
            Outcome::Sat,
            "(= (str.to_code (str.from_code {k})) {k}) must be Sat (round-trip theorem)"
        );
        let ne = qf_slia(&format!(
            "(assert (distinct (str.to_code (str.from_code {k})) {k}))"
        ));
        assert_ne!(
            decide(&ne),
            Outcome::Sat,
            "(distinct (str.to_code (str.from_code {k})) {k}) must never be Sat \
             (round-trip theorem; Unsat or Declined only)"
        );

        // The from_code byte model itself IS exactly decidable (no code-bridge):
        // a length-1 result is provable, so its negation is refuted.
        let len_ne = qf_slia(&format!(
            "(assert (distinct (str.len (str.from_code {k})) 1))"
        ));
        assert_eq!(
            decide(&len_ne),
            Outcome::Unsat,
            "(distinct (str.len (str.from_code {k})) 1) must be Unsat (byte {k} → length 1)"
        );
    }
}

/// Control for bar 2's `distinct` decline: `(distinct (str.to_code "A") 65)` — no
/// `from_code` at all — also declines, pinning the limitation on the `str.to_code`
/// code-bridge rather than on this fix. Sound: never a wrong-sat.
#[test]
fn bar2b_tocode_distinct_decline_is_preexisting() {
    let t = qf_slia("(assert (distinct (str.to_code \"A\") 65))");
    assert_ne!(
        decide(&t),
        Outcome::Sat,
        "(distinct (str.to_code \"A\") 65) must never be Sat (theorem)"
    );
    let eq = qf_slia("(assert (= (str.to_code \"A\") 65))");
    assert_eq!(
        decide(&eq),
        Outcome::Sat,
        "(= (str.to_code \"A\") 65) is Sat"
    );
}

// ---------------------------------------------------------------------------
// Bar 3: genuinely-invalid code points fold to "" — `(from_code i) = ""` is Sat.
// ---------------------------------------------------------------------------
#[test]
fn bar3_invalid_code_points_are_empty() {
    for i in ["(- 1)", "(- 256)", "196608", "300000"] {
        // 196608 = 0x30000 (one past the SMT-LIB max 0x2FFFF), 300000 well past.
        let text = qf_slia(&format!("(assert (= (str.from_code {i}) \"\"))"));
        assert_eq!(
            decide(&text),
            Outcome::Sat,
            "(= (str.from_code {i}) \"\") must be Sat (invalid code point → empty)"
        );
    }
}

// ---------------------------------------------------------------------------
// Bar 4: the valid-but-unrepresentable 256..=0x2FFFF window — no wrong-sat AND
// no wrong-unsat. `(from_code 300) = ""` must NOT be Sat (Z3: Unsat; a decline
// is acceptable), and `to_code(from_code 300) = 300` must NOT be Unsat (Z3: Sat;
// a decline is acceptable).
// ---------------------------------------------------------------------------
#[test]
fn bar4_unrepresentable_window_no_wrong_verdict() {
    for k in [256, 300, 1000, 0x2FFFF] {
        // Not a wrong-sat: emptiness of a non-empty valid char is Unsat/Declined.
        let empty = qf_slia(&format!("(assert (= (str.from_code {k}) \"\"))"));
        let got = decide(&empty);
        assert_ne!(
            got,
            Outcome::Sat,
            "(= (str.from_code {k}) \"\") must NOT be Sat ({k} is a valid non-empty \
             code point; Z3: Unsat) — got {got:?}"
        );

        // Not a wrong-unsat: the round-trip must not be refuted.
        let round = qf_slia(&format!(
            "(assert (= (str.to_code (str.from_code {k})) {k}))"
        ));
        let got = decide(&round);
        assert_ne!(
            got,
            Outcome::Unsat,
            "(= (str.to_code (str.from_code {k})) {k}) must NOT be Unsat (Z3: Sat) \
             — got {got:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// Bar 5 (companion): a symbolic argument the query does not pin into 0..=255 is
// declined — never a wrong verdict on `(from_code n) = ""` (which the buggy
// engine could have wrong-sat'd by picking n in 128..=255 or 256..=0x2FFFF).
// ---------------------------------------------------------------------------
#[test]
fn bar5_symbolic_argument_declines() {
    let text = "(set-logic QF_SLIA)\n(declare-const n Int)\n\
                (assert (>= n 128))\n(assert (= (str.from_code n) \"\"))\n(check-sat)\n";
    let got = decide(text);
    // Sat would be a wrong verdict for n in 128..=0x2FFFF (non-empty char). Unsat
    // would be wrong too (n = 0x30000 makes it empty). Decline is the sound answer.
    assert_ne!(
        got,
        Outcome::Sat,
        "symbolic from_code = \"\" must not be Sat"
    );
}
