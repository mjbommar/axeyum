//! Width guard (soundness). The generic FP circuits use `u128` sign masks
//! (`1u128 << (width - 1)`), so a format wider than 128 bits is unrepresentable: the
//! raw shift would panic (debug) or silently produce a wrong mask (release) → a
//! corrupt circuit → a possibly-wrong verdict, and a wrong `certified: true` on the
//! `Fpa2Bv` trust sub-case. Every FP builder calls `FloatFormat::check` first, which
//! now rejects `width() > 128` with a graceful [`axeyum_ir::IrError::InvalidWidth`].
//! `width() == 128` (F128, sign bit at index 127) is representable and must still work.

use axeyum_fp::{FloatFormat, abs, eq, is_negative, neg};
use axeyum_ir::{Sort, TermArena};

/// `(_ FloatingPoint 5 130)` — total width 135 > 128. A legal SMT-LIB FP sort (the
/// parser caps neither `eb` nor `sb`), so it can reach the FP builders.
fn over_128_fmt() -> FloatFormat {
    FloatFormat {
        exp_bits: 5,
        sig_bits: 130,
    }
}

#[test]
fn fp_ops_on_over_128_bit_format_error_not_panic() {
    let fmt = over_128_fmt();
    assert!(fmt.width() > 128, "sanity: width {} > 128", fmt.width());
    let mut arena = TermArena::new();
    let sx = arena
        .declare("x", Sort::BitVec(fmt.width()))
        .expect("declare a wide BV symbol");
    let x = arena.var(sx);
    // Each builder must return Err (InvalidWidth) — never panic, never a corrupt
    // circuit. (Runs in debug, where the old `sign_mask` shift panicked.)
    assert!(
        neg(&mut arena, fmt, x).is_err(),
        "fp.neg on a >128-bit format must error, not panic"
    );
    assert!(
        abs(&mut arena, fmt, x).is_err(),
        "fp.abs on a >128-bit format must error"
    );
    assert!(
        is_negative(&mut arena, fmt, x).is_err(),
        "fp.isNegative on a >128-bit format must error"
    );
    assert!(
        eq(&mut arena, fmt, x, x).is_err(),
        "fp.eq on a >128-bit format must error"
    );
}

#[test]
fn f128_width_exactly_128_still_builds() {
    let fmt = FloatFormat::F128;
    assert_eq!(fmt.width(), 128, "F128 is exactly 128 bits");
    let mut arena = TermArena::new();
    let sx = arena
        .declare("x", Sort::BitVec(128))
        .expect("declare a 128-bit BV symbol");
    let x = arena.var(sx);
    assert!(
        neg(&mut arena, fmt, x).is_ok(),
        "F128 (width 128) is representable in u128 — neg must still build"
    );
    assert!(
        abs(&mut arena, fmt, x).is_ok(),
        "F128 (width 128) abs must still build"
    );
}
