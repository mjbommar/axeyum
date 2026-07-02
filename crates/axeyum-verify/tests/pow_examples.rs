//! `#[axeyum::verify]` over `recv.pow(N)` with a constant exponent — folded to
//! N-1 nested checked `Mul`s, so the overflow panic matches Rust's `pow` exactly.

use axeyum_verify::{Verdict, verify};

/// Safe: `a <= 15`, so `a.pow(2) = a*a <= 225` never overflows u8.
#[verify]
fn pow_in_range(x: u8) -> u8 {
    let a: u8 = x & 0x0f;
    let r: u8 = a.pow(2);
    assert!(r <= 225);
    r
}

#[test]
fn pow_in_range_verifies() {
    match pow_in_range__axeyum_verdict() {
        Verdict::Verified { certified, .. } => {
            assert!(certified, "pow_in_range proof must re-check");
        }
        other => panic!("pow_in_range must verify, got {other:?}"),
    }
}

/// Bug: unbounded `x.pow(2)` overflows u8 for x >= 16 (e.g. 16*16 = 256).
#[verify(expect_bug)]
fn pow_overflows(x: u8) -> u8 {
    x.pow(2)
}

#[test]
fn pow_overflows_finds_counterexample() {
    match pow_overflows__axeyum_verdict() {
        Verdict::Counterexample { .. } => {}
        other => panic!("pow_overflows must find a counterexample, got {other:?}"),
    }
}
