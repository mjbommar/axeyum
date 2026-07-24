//! `#[axeyum::verify]` over `rotate_left`/`rotate_right` by a constant amount.
//! Rotation is a bijection, so a left-then-right round-trip is the identity — a
//! clean provable property; a single rotation is generally *not* the identity.

// The verifier's bounded fixture contract intentionally exercises `assert!`.
#![allow(clippy::manual_assert_eq)]

use axeyum_verify::{Verdict, verify};

/// Safe: `rotate_left(8)` then `rotate_right(8)` is the identity on u16.
#[verify]
fn rotate_roundtrip(x: u16) -> u16 {
    let r: u16 = x.rotate_left(8).rotate_right(8);
    assert!(r == x);
    r
}

#[test]
fn rotate_roundtrip_verifies() {
    match rotate_roundtrip__axeyum_verdict() {
        Verdict::Verified { certified, .. } => {
            assert!(certified, "rotate_roundtrip proof must re-check");
        }
        other => panic!("rotate_roundtrip must verify, got {other:?}"),
    }
}

/// Bug: `rotate_left(4)` is not the identity (e.g. x=1 → 16 != 1), so asserting
/// `r == x` is reachably violated.
#[verify(expect_bug)]
fn rotate_is_not_identity(x: u16) -> u16 {
    let r: u16 = x.rotate_left(4);
    assert!(r == x);
    r
}

#[test]
fn rotate_is_not_identity_finds_counterexample() {
    match rotate_is_not_identity__axeyum_verdict() {
        Verdict::Counterexample { .. } => {}
        other => panic!("rotate_is_not_identity must find a counterexample, got {other:?}"),
    }
}
