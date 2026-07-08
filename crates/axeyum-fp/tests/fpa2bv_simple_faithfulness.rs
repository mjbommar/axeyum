//! Exhaustive **F16 faithfulness witness for the structurally-exact FP operators**
//! (task #69), the ops the per-query `Fpa2Bv` certified sub-case relies on.
//!
//! The companion `fpa2bv_faithfulness.rs` witnesses the *arithmetic* circuits at
//! `FP8_E5M2` (8 bits). This file witnesses the **simple** operators — `fp.neg`,
//! `fp.abs`, and the five mutually-exclusive category predicates `fp.isNaN`,
//! `fp.isInfinite`, `fp.isZero`, `fp.isNormal`, `fp.isSubnormal` — over **every**
//! F16 bit pattern (all 65 536), against the independent [`rustc_apfloat`]
//! `ieee::Half` reference (S1E5M10, matching [`FloatFormat::F16`] bit-for-bit).
//!
//! These are the operators `axeyum_smtlib::FpUsage::fpa2bv_simple_op_certified`
//! puts on the allow-list. The by-construction argument is that each is a pure,
//! width-parametric bit operation / exact field-pattern test:
//!
//! - `fp.neg` = `bvxor` with the sign mask (flip bit 15); `fp.abs` = `bvand` with
//!   the sign mask's complement (clear bit 15) — independent of the format width;
//! - the category predicates are equalities on the extracted exponent / trailing
//!   significand fields (`exp all-ones ∧ sig≠0` = NaN, `exp all-ones ∧ sig=0` = ∞,
//!   `exp all-zero ∧ sig=0` = zero, `exp all-zero ∧ sig≠0` = subnormal, `exp
//!   neither` = normal).
//!
//! Confirming the circuit **is** exactly that operation at F16 (16 bits, fully
//! enumerable), together with the width-parametric structure of the builders,
//! establishes faithfulness at every format width. F16 is chosen (over F32) so the
//! witness is genuinely *exhaustive*, not sampled.
//!
//! `fp.isNegative`/`fp.isPositive` are **not** on the certified allow-list — their
//! signed-zero/NaN semantics are disputed (note that `rustc_apfloat`'s
//! `is_negative` classifies a signed NaN as negative, whereas axeyum's
//! `fp.isNegative` excludes NaN). A focused documentation check below records that
//! divergence so the exclusion is on the record, not accidental.

use axeyum_fp::{FloatFormat, abs, is_infinite, is_nan, is_normal, is_subnormal, is_zero, neg};
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
