//! `#[axeyum::verify]` over `recv.checked_{add,sub,mul}(arg).unwrap()` — the
//! common "panic on overflow, explicitly" idiom. It is exactly the checked op:
//! the unwrap-on-`None` panic IS the overflow panic. The guarded fn VERIFIES;
//! the unguarded fn's overflow is found and reproduces in the original
//! (DISAGREE = 0).

#![allow(clippy::many_single_char_names)] // terse fixtures: x/y/a/b/c

use axeyum_verify::{Verdict, verify};

/// Safe: masked so `a <= 15` and `b <= 15`, so `a + b <= 30` never overflows u8.
#[verify]
fn checked_add_in_range(x: u8, y: u8) -> u8 {
    let a: u8 = x & 0x0f;
    let b: u8 = y & 0x0f;
    let c: u8 = a.checked_add(b).unwrap();
    assert!(c <= 30);
    c
}

#[test]
fn checked_add_in_range_verifies() {
    match checked_add_in_range__axeyum_verdict() {
        Verdict::Verified { certified, .. } => {
            assert!(certified, "checked_add_in_range proof must re-check");
        }
        other => panic!("checked_add_in_range must verify, got {other:?}"),
    }
}

/// Bug: unbounded `a.checked_add(b).unwrap()` overflows (e.g. 200 + 100 > 255).
#[verify(expect_bug)]
fn checked_add_overflows(a: u8, b: u8) -> u8 {
    a.checked_add(b).unwrap()
}

#[test]
fn checked_add_overflows_finds_counterexample() {
    match checked_add_overflows__axeyum_verdict() {
        Verdict::Counterexample { .. } => {}
        other => panic!("checked_add_overflows must find a counterexample, got {other:?}"),
    }
}
