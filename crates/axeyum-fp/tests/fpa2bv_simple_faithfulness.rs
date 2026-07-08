//! **F16 faithfulness witnesses for the `Fpa2Bv`-certified FP operators** (tasks
//! #69/#70/#70a), the ops the per-query certified sub-case relies on. The companion
//! `fpa2bv_faithfulness.rs` witnesses the *arithmetic* circuits at `FP8_E5M2`; this
//! file witnesses the **certified** operators at F16 (S1E5M10, matching
//! [`FloatFormat::F16`]) against the independent [`rustc_apfloat`] `ieee::Half`
//! reference. Two tiers:
//!
//! **Exact bit ops / predicates — exhaustive over all 65 536 patterns.** Each is a
//! pure, width-parametric bit operation / exact field-pattern test, so confirming
//! the circuit **is** exactly that operation at one fully-enumerable width (F16),
//! plus the width-parametric builders, establishes faithfulness at every width:
//!
//! - `fp.neg` = `bvxor` sign mask (flip bit 15); `fp.abs` = `bvand` ~sign mask;
//! - the category predicates — equalities on the exponent / trailing-significand
//!   fields (`exp all-ones ∧ sig≠0`=NaN, `∧ sig=0`=∞, `exp all-zero ∧ sig=0`=zero,
//!   `∧ sig≠0`=subnormal, else normal);
//! - the sign predicates `fp.isNegative` (`sign ∧ ¬NaN`) / `fp.isPositive`
//!   (`¬sign ∧ ¬NaN`) — the reference is `rustc_apfloat`'s raw `is_negative`
//!   conjoined with `¬is_nan` (the signed-NaN case is exactly where the SMT-LIB
//!   predicate `false` differs from apfloat's bare sign bit `true`).
//!
//! **Proven-faithful comparison circuits — F16 edge cross-product** (the exhaustive
//! anchor is `fpa2bv_faithfulness.rs` at FP8). `fp.eq`/`fp.lt`/`fp.leq` are faithful
//! by a width-independent argument (monotone `order_key` + `¬NaN`/`±0` guards); the
//! curated F16 edge set double-anchors that claim at a second width.

use axeyum_fp::{
    FloatFormat, abs, eq, is_infinite, is_nan, is_negative, is_normal, is_positive, is_subnormal,
    is_zero, leq, lt, neg,
};
use axeyum_ir::{Assignment, Sort, TermArena, TermId, Value, eval};
use rustc_apfloat::Float;
use rustc_apfloat::ieee::Half as Ref;

const FMT: FloatFormat = FloatFormat::F16;
const WIDTH: u32 = 16;
const N: u128 = 1 << WIDTH; // 65 536 patterns
const SIGN_MASK: u128 = 1 << (WIDTH - 1); // 0x8000

fn r_from(bits: u128) -> Ref {
    Ref::from_bits(bits)
}

fn is_ref_nan(bits: u128) -> bool {
    r_from(bits).is_nan()
}

/// Builds a unary FP op circuit (BV → BV) once and evaluates it per bit pattern via
/// the strict ground evaluator (the circuit's own denotation — no SAT, no replay).
fn unary_bv_evaluator(
    build: impl Fn(&mut TermArena, FloatFormat, TermId) -> Result<TermId, axeyum_ir::IrError>,
) -> impl Fn(u128) -> u128 {
    let mut arena = TermArena::new();
    let sx = arena.declare("x", Sort::BitVec(WIDTH)).unwrap();
    let x = arena.var(sx);
    let t = build(&mut arena, FMT, x).unwrap();
    move |xb| {
        let mut asg = Assignment::new();
        asg.set(
            sx,
            Value::Bv {
                width: WIDTH,
                value: xb,
            },
        );
        match eval(&arena, t, &asg).unwrap() {
            Value::Bv { value, .. } => value,
            other => panic!("expected BV, got {other:?}"),
        }
    }
}

/// Builds a binary FP comparison circuit (BV × BV → Bool) once and evaluates it.
fn binary_cmp_evaluator(
    build: impl Fn(&mut TermArena, FloatFormat, TermId, TermId) -> Result<TermId, axeyum_ir::IrError>,
) -> impl Fn(u128, u128) -> bool {
    let mut arena = TermArena::new();
    let sx = arena.declare("x", Sort::BitVec(WIDTH)).unwrap();
    let sy = arena.declare("y", Sort::BitVec(WIDTH)).unwrap();
    let (x, y) = (arena.var(sx), arena.var(sy));
    let t = build(&mut arena, FMT, x, y).unwrap();
    move |xb, yb| {
        let mut asg = Assignment::new();
        asg.set(
            sx,
            Value::Bv {
                width: WIDTH,
                value: xb,
            },
        );
        asg.set(
            sy,
            Value::Bv {
                width: WIDTH,
                value: yb,
            },
        );
        match eval(&arena, t, &asg).unwrap() {
            Value::Bool(b) => b,
            other => panic!("expected Bool, got {other:?}"),
        }
    }
}

/// Builds a unary FP predicate circuit (BV → Bool) once and evaluates it.
fn unary_pred_evaluator(
    build: impl Fn(&mut TermArena, FloatFormat, TermId) -> Result<TermId, axeyum_ir::IrError>,
) -> impl Fn(u128) -> bool {
    let mut arena = TermArena::new();
    let sx = arena.declare("x", Sort::BitVec(WIDTH)).unwrap();
    let x = arena.var(sx);
    let t = build(&mut arena, FMT, x).unwrap();
    move |xb| {
        let mut asg = Assignment::new();
        asg.set(
            sx,
            Value::Bv {
                width: WIDTH,
                value: xb,
            },
        );
        match eval(&arena, t, &asg).unwrap() {
            Value::Bool(b) => b,
            other => panic!("expected Bool, got {other:?}"),
        }
    }
}

// --- neg / abs: exact bit ops, and value-faithful vs the reference -----------

#[test]
fn f16_neg_faithful_exhaustive() {
    let circuit = unary_bv_evaluator(neg);
    for xb in 0..N {
        let got = circuit(xb);
        // Direct spec: neg flips exactly the sign bit (bit 15), width-parametric.
        assert_eq!(got, xb ^ SIGN_MASK, "fp.neg({xb:#06x}): sign-flip");
        // Independent value cross-check (NaN payload may be canonicalized by the
        // reference, so a NaN input need only stay NaN — the bit-flip is checked
        // above directly).
        if is_ref_nan(xb) {
            assert!(is_ref_nan(got), "fp.neg({xb:#06x}) of NaN must stay NaN");
        } else {
            assert_eq!(
                got,
                (-r_from(xb)).to_bits(),
                "fp.neg({xb:#06x}) vs reference"
            );
        }
    }
}

#[test]
fn f16_abs_faithful_exhaustive() {
    let circuit = unary_bv_evaluator(abs);
    for xb in 0..N {
        let got = circuit(xb);
        // Direct spec: abs clears exactly the sign bit.
        assert_eq!(got, xb & !SIGN_MASK, "fp.abs({xb:#06x}): clear sign");
        if is_ref_nan(xb) {
            assert!(is_ref_nan(got), "fp.abs({xb:#06x}) of NaN must stay NaN");
        } else {
            assert_eq!(
                got,
                r_from(xb).abs().to_bits(),
                "fp.abs({xb:#06x}) vs reference"
            );
        }
    }
}

// --- category predicates: exact field-pattern tests vs the reference ---------

#[test]
fn f16_isnan_faithful_exhaustive() {
    let circuit = unary_pred_evaluator(is_nan);
    for xb in 0..N {
        assert_eq!(circuit(xb), r_from(xb).is_nan(), "fp.isNaN({xb:#06x})");
    }
}

#[test]
fn f16_isinfinite_faithful_exhaustive() {
    let circuit = unary_pred_evaluator(is_infinite);
    for xb in 0..N {
        assert_eq!(
            circuit(xb),
            r_from(xb).is_infinite(),
            "fp.isInfinite({xb:#06x})"
        );
    }
}

#[test]
fn f16_iszero_faithful_exhaustive() {
    let circuit = unary_pred_evaluator(is_zero);
    for xb in 0..N {
        assert_eq!(circuit(xb), r_from(xb).is_zero(), "fp.isZero({xb:#06x})");
    }
}

#[test]
fn f16_isnormal_faithful_exhaustive() {
    let circuit = unary_pred_evaluator(is_normal);
    for xb in 0..N {
        assert_eq!(
            circuit(xb),
            r_from(xb).is_normal(),
            "fp.isNormal({xb:#06x})"
        );
    }
}

#[test]
fn f16_issubnormal_faithful_exhaustive() {
    // rustc_apfloat spells "subnormal" as `is_denormal` (IEEE-754R isSubnormal).
    let circuit = unary_pred_evaluator(is_subnormal);
    for xb in 0..N {
        assert_eq!(
            circuit(xb),
            r_from(xb).is_denormal(),
            "fp.isSubnormal({xb:#06x})"
        );
    }
}

/// `fp.isNegative x` = `sign bit set ∧ ¬NaN` (SMT-LIB sign classification: `−0` is
/// negative, `+0` is not; NaN is neither). The reference is `rustc_apfloat`'s raw
/// `is_negative` (the bare sign bit) conjoined with `¬is_nan` — this is exactly the
/// signed-NaN case where the SMT-LIB predicate (`false`) differs from apfloat's raw
/// sign bit (`true`), and the exhaustive check confirms the axeyum circuit matches
/// the SMT-LIB predicate over the entire input space.
#[test]
fn f16_isnegative_faithful_exhaustive() {
    let circuit = unary_pred_evaluator(is_negative);
    for xb in 0..N {
        let want = r_from(xb).is_negative() && !r_from(xb).is_nan();
        assert_eq!(circuit(xb), want, "fp.isNegative({xb:#06x})");
    }
}

/// `fp.isPositive x` = `sign bit clear ∧ ¬NaN` (`+0` is positive, `−0` is not; NaN
/// is neither) — the sign-mirror of `fp.isNegative`.
#[test]
fn f16_ispositive_faithful_exhaustive() {
    let circuit = unary_pred_evaluator(is_positive);
    for xb in 0..N {
        let want = !r_from(xb).is_negative() && !r_from(xb).is_nan();
        assert_eq!(circuit(xb), want, "fp.isPositive({xb:#06x})");
    }
}

// --- comparison circuits: F16 second-width witness (edge cross-product) ------

/// A curated set of F16 edge bit patterns — both zeros, both infinities, a NaN, the
/// min/max subnormal and normal of both signs, and ±1.0 — i.e. exactly where FP
/// comparison semantics live (NaN unordered, ±0 equal, sign/magnitude boundaries).
/// The full cross-product exercises every ordering relation at the **second** width
/// (F16), double-anchoring the `FP8_E5M2` exhaustive comparison witness
/// (`fpa2bv_faithfulness.rs`) for the width-parametric `order_key` argument.
const F16_EDGE: &[u128] = &[
    0x0000, 0x8000, // +0, -0
    0x7c00, 0xfc00, // +inf, -inf
    0x7e00, // qNaN
    0x0001, 0x8001, // ± smallest subnormal
    0x03ff, 0x83ff, // ± largest subnormal
    0x0400, 0x8400, // ± smallest normal
    0x3c00, 0xbc00, // ±1.0
    0x7bff, 0xfbff, // ± largest normal
];

#[test]
fn f16_eq_faithful_over_edge_cases() {
    // Oracle: rustc_apfloat IEEE `==` (NaN ≠ NaN, +0 == -0) — the SMT-LIB `fp.eq`.
    let circuit = binary_cmp_evaluator(eq);
    for &xb in F16_EDGE {
        for &yb in F16_EDGE {
            let want = r_from(xb) == r_from(yb);
            assert_eq!(circuit(xb, yb), want, "fp.eq({xb:#06x},{yb:#06x})");
        }
    }
}

#[test]
fn f16_lt_leq_faithful_over_edge_cases() {
    // Oracle: rustc_apfloat `PartialOrd` (NaN ⇒ false, ±0 equal) — SMT-LIB fp.lt/leq.
    let lt_c = binary_cmp_evaluator(lt);
    let leq_c = binary_cmp_evaluator(leq);
    for &xb in F16_EDGE {
        for &yb in F16_EDGE {
            assert_eq!(
                lt_c(xb, yb),
                r_from(xb) < r_from(yb),
                "fp.lt({xb:#06x},{yb:#06x})"
            );
            assert_eq!(
                leq_c(xb, yb),
                r_from(xb) <= r_from(yb),
                "fp.leq({xb:#06x},{yb:#06x})"
            );
        }
    }
}

// --- the five categories partition every bit pattern (self-consistency) ------

/// Every F16 bit pattern is in **exactly one** of the five categories — the reason
/// the category predicates are unambiguous field-pattern tests with no signed-zero
/// subtlety. This holds for the axeyum circuits over the whole input space.
#[test]
fn f16_categories_partition_every_pattern() {
    let is_nan_c = unary_pred_evaluator(is_nan);
    let is_inf_c = unary_pred_evaluator(is_infinite);
    let is_zero_c = unary_pred_evaluator(is_zero);
    let is_norm_c = unary_pred_evaluator(is_normal);
    let is_sub_c = unary_pred_evaluator(is_subnormal);
    for xb in 0..N {
        let n = usize::from(is_nan_c(xb))
            + usize::from(is_inf_c(xb))
            + usize::from(is_zero_c(xb))
            + usize::from(is_norm_c(xb))
            + usize::from(is_sub_c(xb));
        assert_eq!(
            n, 1,
            "pattern {xb:#06x} must be in exactly one FP category, was {n}"
        );
    }
}

// --- the miter has teeth -----------------------------------------------------

/// A self-test proving the exhaustive miter would CATCH an unfaithful simple-op
/// lowering. A `neg` that flipped the wrong bit (say bit 0 instead of the sign)
/// disagrees with the reference sign-flip on the very first non-zero pattern, so
/// the `f16_neg_faithful_exhaustive` assertion would fire. We emulate that here.
#[test]
fn miter_has_teeth_against_wrong_neg() {
    let wrong_neg = |xb: u128| xb ^ 1; // flips bit 0, not the sign bit
    let mut caught = false;
    for xb in 0..N {
        if wrong_neg(xb) != xb ^ SIGN_MASK {
            caught = true;
            break;
        }
    }
    assert!(caught, "the sign-flip spec must reject a wrong-bit neg");
}

// --- documentation: why isNegative/isPositive are excluded -------------------

/// Records the concrete divergence that keeps `fp.isNegative`/`fp.isPositive` off
/// the certified allow-list: `rustc_apfloat` classifies a **signed NaN** as
/// negative (its `is_negative` "applies to zeros and NaNs as well"), whereas
/// axeyum's `fp.isNegative` is `sign ∧ ¬NaN` — false for any NaN. With the sign +
/// NaN semantics themselves disputed across the task spec / the SMT-LIB reading /
/// the Z3-validated codebase, a `certified: true` on these two would rest on an
/// unresolved question, so they are conservatively treated as non-simple.
#[test]
fn isnegative_reference_diverges_on_signed_nan() {
    // A negative (sign-bit-set) quiet NaN in F16: exp all-ones (0x7C00), a non-zero
    // significand, sign bit set → 0xFE00.
    const NEG_QNAN: u128 = 0xFE00;
    let r = r_from(NEG_QNAN);
    assert!(r.is_nan(), "0xFE00 must be a NaN in F16");
    assert!(
        r.is_negative(),
        "rustc_apfloat classifies a signed NaN as negative — the divergence axeyum's \
         fp.isNegative (sign ∧ ¬NaN) does not follow; hence the conservative exclusion"
    );
}
