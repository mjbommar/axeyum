//! `#[axeyum::verify]` over `wrapping_*` arithmetic — deliberate modular ops that
//! must NOT be flagged as overflow panics. The safe fn VERIFIES (a plain `+`
//! there would be an overflow bug); the buggy fn's false claim about the wrapped
//! result yields a counterexample whose witness panics in the original fn
//! (DISAGREE = 0).

use axeyum_verify::{Verdict, verify};

/// Safe: `wrapping_add` never panics, and the masked result is always ≤ 0x0f.
/// (The same body with a plain `+` would be an overflow bug for large `x`.)
#[verify]
fn wrap_then_mask(x: u8) -> u8 {
    let s: u8 = x.wrapping_add(200);
    let r: u8 = s & 0x0f;
    assert!(r <= 15);
    r
}

#[test]
fn wrap_then_mask_verifies() {
    match wrap_then_mask__axeyum_verdict() {
        Verdict::Verified { certified, .. } => {
            assert!(certified, "wrap_then_mask proof must re-check");
        }
        other => panic!("wrap_then_mask must verify, got {other:?}"),
    }
}

/// Bug: `wrapping_add` wraps mod 256, so `x.wrapping_add(1) > x` is false at
/// `x == 255` (wraps to 0). The assert is reachably violated.
#[verify(expect_bug)]
fn wrap_is_not_monotone(x: u8) -> u8 {
    let s: u8 = x.wrapping_add(1);
    assert!(s > x);
    s
}

#[test]
fn wrap_is_not_monotone_finds_counterexample() {
    match wrap_is_not_monotone__axeyum_verdict() {
        Verdict::Counterexample { .. } => {}
        other => panic!("wrap_is_not_monotone must find a counterexample, got {other:?}"),
    }
}
