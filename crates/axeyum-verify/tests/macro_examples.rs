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

// ---- (d) BUG: array index out of bounds (Phase 2 macro array support) ----------

/// `a[i]` panics when `i >= 4`. The runtime models index-OOB; Phase 2 wires the
/// macro to parse the `[u8; 4]` param and the `a[i]` indexing.
#[verify(expect_bug)]
fn get(a: [u8; 4], i: usize) -> u8 {
    a[i]
}

#[test]
fn array_oob_witness_reproduces() {
    let Verdict::Counterexample { class, inputs } = get__axeyum_verdict() else {
        panic!("a[i] must be able to go out of bounds");
    };
    assert_eq!(class, "index out of bounds");
    // The witness `i` must be >= 4 (the array length).
    let i = inputs
        .iter()
        .find_map(|w| match w {
            Witness::Int { name, bits, .. } if name == "i" => Some(*bits),
            _ => None,
        })
        .expect("an `i` witness");
    assert!(i >= 4, "OOB witness i={i} must be >= len 4");
    let arr = [0u8; 4];
    let iw = usize::try_from(i).unwrap();
    assert!(
        axeyum_verify::reproduce::panics_on(move || {
            let _ = get(arr, iw);
        }),
        "witness get(_, {iw}) must index-panic in the original fn"
    );
}

// ---- SAFE: guarded array access is verified ------------------------------------

/// Indexing is guarded by `i < 4`, so it never goes out of bounds; the `&[u8; 4]`
/// reference form is also exercised here.
#[verify]
#[allow(clippy::trivially_copy_pass_by_ref)] // the `&[T; N]` form is intentionally exercised
fn safe_get(a: &[u8; 4], i: usize) -> u8 {
    let mut r: u8 = 0;
    if i < 4 {
        r = a[i];
    }
    r
}

#[test]
fn guarded_array_access_is_verified() {
    match safe_get__axeyum_verdict() {
        Verdict::Verified { .. } => {}
        other => panic!("guarded array access must verify, got {other:?}"),
    }
}

// ---- usize/isize width mapping (Phase 2 #2) ------------------------------------

/// A `usize` add can overflow at the modeled 64-bit width.
#[verify(expect_bug)]
fn usize_add(a: usize, b: usize) -> usize {
    a + b
}

#[test]
fn usize_add_overflows() {
    let Verdict::Counterexample { class, inputs } = usize_add__axeyum_verdict() else {
        panic!("usize add can overflow at 64-bit");
    };
    assert_eq!(class, "add overflow");
    // The witnesses are 64-bit ints (the documented usize model width).
    let (w, _, _) = inputs
        .iter()
        .find_map(|wit| match wit {
            Witness::Int {
                name,
                width,
                signed,
                bits,
            } if name == "a" => Some((*width, *signed, *bits)),
            _ => None,
        })
        .expect("an `a` witness");
    assert_eq!(w, 64, "usize is modeled at 64 bits");
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
