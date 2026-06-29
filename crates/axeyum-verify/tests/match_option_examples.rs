//! `#[axeyum::verify]` over `match a.checked_*(b) { Some(v) => .., None => .. }`
//! — Option-flow with a value binding. Desugars to `if !Overflows(op,a,b) { let
//! v = wrapping_op(a,b); <some> } else { <none> }`. The masked-safe fn VERIFIES;
//! the overflow fn takes the `None` arm and its assert is reachably violated.

#![allow(clippy::many_single_char_names, unused_assignments)] // terse fixtures

use axeyum_verify::{Verdict, verify};

/// Safe: `a <= 15`, so `a.checked_add(1)` is always `Some(a + 1)` — the `None`
/// arm is unreachable and `r == a + 1` holds.
#[verify]
fn match_some_in_range(x: u8) -> u8 {
    let a: u8 = x & 0x0f;
    let mut r: u8 = 0;
    match a.checked_add(1) {
        Some(v) => {
            r = v;
        }
        None => {
            r = 0;
        }
    }
    assert!(r == a + 1);
    r
}

#[test]
fn match_some_in_range_verifies() {
    match match_some_in_range__axeyum_verdict() {
        Verdict::Verified { certified, .. } => {
            assert!(certified, "match_some_in_range proof must re-check");
        }
        other => panic!("match_some_in_range must verify, got {other:?}"),
    }
}

/// Bug: when `a + b` overflows the `None` arm sets `r = 0`, so `assert!(r != 0)`
/// is reachably violated (e.g. a=200, b=100).
#[verify(expect_bug)]
fn match_none_on_overflow(a: u8, b: u8) -> u8 {
    let mut r: u8 = 1;
    match a.checked_add(b) {
        Some(v) => {
            r = v;
        }
        None => {
            r = 0;
        }
    }
    assert!(r != 0);
    r
}

#[test]
fn match_none_on_overflow_finds_counterexample() {
    match match_none_on_overflow__axeyum_verdict() {
        Verdict::Counterexample { .. } => {}
        other => panic!("match_none_on_overflow must find a counterexample, got {other:?}"),
    }
}
