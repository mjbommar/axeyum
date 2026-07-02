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

/// Safe: `saturating_add` of a non-negative amount never decreases an unsigned
/// value, so `s >= x` always holds (and it never panics).
#[verify]
fn saturating_does_not_decrease(x: u8) -> u8 {
    let s: u8 = x.saturating_add(10);
    assert!(s >= x);
    s
}

#[test]
fn saturating_does_not_decrease_verifies() {
    match saturating_does_not_decrease__axeyum_verdict() {
        Verdict::Verified { certified, .. } => {
            assert!(
                certified,
                "saturating_does_not_decrease proof must re-check"
            );
        }
        other => panic!("saturating_does_not_decrease must verify, got {other:?}"),
    }
}

/// Bug: at `x == 255`, `saturating_add(1)` clamps back to 255, so `s > x` is
/// reachably false.
#[verify(expect_bug)]
fn saturating_is_not_strictly_increasing(x: u8) -> u8 {
    let s: u8 = x.saturating_add(1);
    assert!(s > x);
    s
}

#[test]
fn saturating_is_not_strictly_increasing_finds_counterexample() {
    match saturating_is_not_strictly_increasing__axeyum_verdict() {
        Verdict::Counterexample { .. } => {}
        other => panic!("saturating_is_not_strictly_increasing must find a cex, got {other:?}"),
    }
}

/// Safe: `x.min(10)` is always ≤ 10 (a clamp); the assert always holds.
#[verify]
fn min_clamps(x: u8) -> u8 {
    let r: u8 = x.min(10);
    assert!(r <= 10);
    r
}

#[test]
fn min_clamps_verifies() {
    match min_clamps__axeyum_verdict() {
        Verdict::Verified { certified, .. } => assert!(certified, "min_clamps proof must re-check"),
        other => panic!("min_clamps must verify, got {other:?}"),
    }
}

/// Bug: `x.max(10)` is ≥ 10, never < 10, so `r < 10` is unsatisfiable as a true
/// branch — but asserting it is reachably false for every `x` (e.g. x=0 ⇒ r=10).
#[verify(expect_bug)]
fn max_is_never_below_floor(x: u8) -> u8 {
    let r: u8 = x.max(10);
    assert!(r < 10);
    r
}

#[test]
fn max_is_never_below_floor_finds_counterexample() {
    match max_is_never_below_floor__axeyum_verdict() {
        Verdict::Counterexample { .. } => {}
        other => panic!("max_is_never_below_floor must find a cex, got {other:?}"),
    }
}
