//! End-to-end worked examples driven by the real `#[axeyum::verify]` macro.
//!
//! Each `#[verify]` fn expands to (1) the original fn, (2) a hidden
//! `<fn>__axeyum_verdict()` helper, and (3) a `#[test] axeyum_verify_<fn>`.
//!
//! - A **safe** fn's generated test asserts it VERIFIES (and re-checks the cert).
//! - A **bug** fn carries `#[verify(expect_bug)]`: its generated test asserts a
//!   counterexample is FOUND and — the soundness floor — that the witness, run
//!   through the *original* function, actually panics (DISAGREE = 0). So every
//!   test in this file passes, while still exercising the full pipeline.
//!
//! We additionally inspect the verdict helpers directly for the headline
//! examples (a) / (b) / (c).

#![allow(clippy::similar_names)]

use axeyum_verify::{Verdict, Witness, opt, verify};

// ---- (b) SAFE: masked clamp is verified (generated test asserts VERIFIED) ------

/// `r = x & 0x0f` is always ≤ 15, so the assert never fails.
#[verify]
fn clamp(x: u8) -> u8 {
    let r: u8 = x & 0x0f;
    assert!(r <= 15);
    r
}

#[test]
fn clamp_verdict_is_certified() {
    match clamp__axeyum_verdict() {
        Verdict::Verified { certified } => assert!(certified, "clamp proof must re-check"),
        other => panic!("clamp must verify, got {other:?}"),
    }
}

// ---- SAFE guarded division -----------------------------------------------------

/// Division guarded by a non-zero check: no ÷0, and u8/u8 never overflows.
#[verify]
#[allow(clippy::manual_checked_ops)]
fn safe_div(a: u8, b: u8) -> u8 {
    let mut q: u8 = 0;
    if b > 0 {
        q = a / b;
    }
    q
}

// ---- (a) BUG: u8 addition overflows --------------------------------------------

/// `a + b` overflows `u8` for large inputs.
#[verify(expect_bug)]
fn add(a: u8, b: u8) -> u8 {
    a + b
}

#[test]
fn add_overflow_witness_reproduces() {
    let Verdict::Counterexample { class, inputs } = add__axeyum_verdict() else {
        panic!("u8 add must overflow");
    };
    assert_eq!(class, "add overflow");
    let a = u8::try_from(int_bits(&inputs, "a")).unwrap();
    let b = u8::try_from(int_bits(&inputs, "b")).unwrap();
    assert!(
        axeyum_verify::reproduce::panics_on(|| {
            let _ = add(a, b);
        }),
        "witness add({a},{b}) must overflow-panic in the original fn"
    );
}

// ---- (c) BUG: assert! inside a #[unwind(K)] loop -------------------------------

/// For some `x`, one of the four iterations makes `x + i == 200`, tripping the
/// assert. The function-level `#[axeyum::unwind(4)]` is the honest unwind bound.
#[verify(expect_bug)]
#[axeyum_verify::unwind(4)]
fn loopy(x: u16) -> u16 {
    for i in 0..4u16 {
        let s: u16 = x + i;
        assert!(s != 200);
    }
    0
}

#[test]
fn loop_assert_witness_reproduces() {
    let Verdict::Counterexample { class, inputs } = loopy__axeyum_verdict() else {
        panic!("the unwound loop assert must be violable");
    };
    assert_eq!(class, "assert! violated");
    let x = u16::try_from(int_bits(&inputs, "x")).unwrap();
    assert!(axeyum_verify::reproduce::panics_on(|| {
        let _ = loopy(x);
    }));
}

// ---- BUG: unwrap on a modeled Option -------------------------------------------

/// `opt(present, x).unwrap()` panics when `present == false`.
#[verify(expect_bug)]
fn maybe(present: bool, x: u8) -> u8 {
    opt(present, x).unwrap()
}

#[test]
fn unwrap_none_witness_reproduces() {
    let Verdict::Counterexample { class, inputs } = maybe__axeyum_verdict() else {
        panic!("unwrap can hit None");
    };
    assert_eq!(class, "unwrap on None");
    let present = inputs.iter().find_map(|w| match w {
        Witness::Bool { name, value } if name == "present" => Some(*value),
        _ => None,
    });
    assert_eq!(present, Some(false));
    assert!(axeyum_verify::reproduce::panics_on(|| {
        let _ = maybe(false, 0);
    }));
}

// ---- helper --------------------------------------------------------------------

fn int_bits(inputs: &[Witness], name: &str) -> u128 {
    inputs
        .iter()
        .find_map(|w| match w {
            Witness::Int { name: n, bits, .. } if n == name => Some(*bits),
            _ => None,
        })
        .unwrap_or_else(|| panic!("no int witness `{name}` in {inputs:?}"))
}
