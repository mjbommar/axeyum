//! `#[axeyum::verify]` over `match`-on-int (desugared to an `if`/`else` chain).
//! Each `#[verify]` fn expands to a generated `#[test]`: the safe one asserts
//! VERIFIED; the `expect_bug` one asserts a counterexample is found AND that the
//! witness, run through the *original* function, actually panics (DISAGREE = 0).

// These are synthetic fixtures whose shape is dictated by what we exercise in the
// proc-macro (a `match` with one literal arm + `_`); the idiomatic-Rust lints do
// not apply.
#![allow(unused_assignments, clippy::single_match)]

use axeyum_verify::{Verdict, verify};

/// Safe: every arm sets `r` to a value ≥ 10, so the assert always holds.
#[verify]
fn classify(x: u8) -> u8 {
    let mut r: u8 = 30;
    match x {
        0 => {
            r = 10;
        }
        1 => {
            r = 20;
        }
        _ => {}
    }
    assert!(r >= 10);
    r
}

#[test]
fn classify_verifies() {
    match classify__axeyum_verdict() {
        Verdict::Verified { certified, .. } => assert!(certified, "classify proof must re-check"),
        other => panic!("classify (match) must verify, got {other:?}"),
    }
}

/// Bug: the `1` arm sets `r = 200`, so `assert!(r != 200)` fails when `x == 1`.
/// The generated `expect_bug` test finds the counterexample and confirms the
/// original fn panics on it.
#[verify(expect_bug)]
fn bad_match(x: u8) -> u8 {
    let mut r: u8 = 0;
    match x {
        1 => {
            r = 200;
        }
        _ => {}
    }
    assert!(r != 200);
    r
}

#[test]
fn bad_match_finds_counterexample() {
    match bad_match__axeyum_verdict() {
        Verdict::Counterexample { .. } => {}
        other => panic!("bad_match (match) must find a counterexample, got {other:?}"),
    }
}
