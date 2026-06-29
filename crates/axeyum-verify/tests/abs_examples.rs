//! `#[axeyum::verify]` over `.abs()` — which has a real panic class: `iN::MIN`
//! has no non-negative representation, so `iN::MIN.abs()` overflows (panics in
//! debug). The guarded fn VERIFIES; the unguarded fn's bug is found and the
//! witness (`x == iN::MIN`) panics in the original (DISAGREE = 0).

use axeyum_verify::{Verdict, verify};

/// Safe: `abs` is only taken when `x > 0`, where it cannot hit `iN::MIN`, so no
/// overflow is reachable and `r >= 0` always holds.
#[verify]
fn abs_guarded(x: i8) -> i8 {
    let mut r: i8 = 0;
    if x > 0 {
        r = x.abs();
    }
    assert!(r >= 0);
    r
}

#[test]
fn abs_guarded_verifies() {
    match abs_guarded__axeyum_verdict() {
        Verdict::Verified { certified, .. } => {
            assert!(certified, "abs_guarded proof must re-check");
        }
        other => panic!("abs_guarded must verify, got {other:?}"),
    }
}

/// Bug: unguarded `x.abs()` overflows at `x == i8::MIN` (-128 has no +128 in i8).
#[verify(expect_bug)]
fn abs_min_overflows(x: i8) -> i8 {
    let r: i8 = x.abs();
    assert!(r >= 0);
    r
}

#[test]
fn abs_min_overflows_finds_counterexample() {
    match abs_min_overflows__axeyum_verdict() {
        Verdict::Counterexample { .. } => {}
        other => panic!("abs_min_overflows must find a counterexample, got {other:?}"),
    }
}
