//! `#[axeyum::verify]` over `recv.checked_{add,sub,mul}(arg).unwrap_or(default)`
//! — the Option-with-fallback idiom. It never panics: on no overflow it is the
//! real result, otherwise the default. Modeled as `ite(!overflows, wrapping_op,
//! default)` (the boolean `Overflows` node + the non-panicking wrapping op).

#![allow(clippy::many_single_char_names)] // terse fixtures

use axeyum_verify::{Verdict, verify};

/// Safe: with `a <= 15`, `a + 1` never overflows, so `unwrap_or` returns `a + 1`
/// and the assert holds — and the whole expression is panic-free.
#[verify]
fn unwrap_or_takes_value_in_range(x: u8) -> u8 {
    let a: u8 = x & 0x0f;
    let c: u8 = a.checked_add(1).unwrap_or(0);
    assert!(c == a + 1);
    c
}

#[test]
fn unwrap_or_takes_value_in_range_verifies() {
    match unwrap_or_takes_value_in_range__axeyum_verdict() {
        Verdict::Verified { certified, .. } => {
            assert!(
                certified,
                "unwrap_or_takes_value_in_range proof must re-check"
            );
        }
        other => panic!("unwrap_or_takes_value_in_range must verify, got {other:?}"),
    }
}

/// Bug: when `a + 100` overflows (a >= 156), `unwrap_or(7)` yields the default 7,
/// so `assert!(c != 7)` is reachably violated.
#[verify(expect_bug)]
fn unwrap_or_falls_back_to_default(a: u8) -> u8 {
    let c: u8 = a.checked_add(100).unwrap_or(7);
    assert!(c != 7);
    c
}

#[test]
fn unwrap_or_falls_back_to_default_finds_counterexample() {
    match unwrap_or_falls_back_to_default__axeyum_verdict() {
        Verdict::Counterexample { .. } => {}
        other => panic!("unwrap_or_falls_back_to_default must find a cex, got {other:?}"),
    }
}
