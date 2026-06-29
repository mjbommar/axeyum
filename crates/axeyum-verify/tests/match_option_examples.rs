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

// ---- first-class (let-bound) Option flow ---------------------------------------

/// Safe: `s` is a *let-bound* Option; `a <= 15` so `s` is always `Some(a+1)` and
/// `s.unwrap_or(0)` yields `a + 1`.
#[verify]
fn let_bound_unwrap_or(x: u8) -> u8 {
    let a: u8 = x & 0x0f;
    let s = a.checked_add(1);
    let r: u8 = s.unwrap_or(0);
    assert!(r == a + 1);
    r
}

#[test]
fn let_bound_unwrap_or_verifies() {
    match let_bound_unwrap_or__axeyum_verdict() {
        Verdict::Verified { certified, .. } => {
            assert!(certified, "let_bound_unwrap_or proof must re-check");
        }
        other => panic!("let_bound_unwrap_or must verify, got {other:?}"),
    }
}

/// Safe: `s.is_some()` is always true for `a <= 15` (no overflow).
#[verify]
fn let_bound_is_some(x: u8) -> u8 {
    let a: u8 = x & 0x0f;
    let s = a.checked_add(1);
    let ok: bool = s.is_some();
    assert!(ok);
    a
}

#[test]
fn let_bound_is_some_verifies() {
    match let_bound_is_some__axeyum_verdict() {
        Verdict::Verified { .. } => {}
        other => panic!("let_bound_is_some must verify, got {other:?}"),
    }
}

/// Bug: `match` on a *let-bound* Option takes the `None` arm on overflow,
/// setting `r = 0` and violating `r != 0`.
#[verify(expect_bug)]
fn let_bound_match_none(a: u8, b: u8) -> u8 {
    let s = a.checked_add(b);
    let mut r: u8 = 1;
    match s {
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
fn let_bound_match_none_finds_counterexample() {
    match let_bound_match_none__axeyum_verdict() {
        Verdict::Counterexample { .. } => {}
        other => panic!("let_bound_match_none must find a counterexample, got {other:?}"),
    }
}
