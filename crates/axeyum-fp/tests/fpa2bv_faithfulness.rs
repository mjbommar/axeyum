//! Exhaustive small-format **`Fpa2Bv` faithfulness witness** (Track 3, the Lean
//! half): for a small IEEE-style floating-point format the FP → BV circuit can be
//! checked for **all** inputs against an *independent* reference, turning the
//! `Fpa2Bv` trust hole from a re-derivation-only artifact into a genuine
//! faithfulness proof.
//!
//! Why this is stronger than the re-derivation certs. Re-blasting an FP circuit
//! and re-checking the CNF (the `Fpa2Bv` analogue of the int-blast /
//! Ackermann / array-elim certificates) only proves the lowering is
//! **deterministic** — it re-derives *the same circuit*. It cannot catch an
//! *unfaithful* circuit: a lowering that is wrong but stably wrong re-derives to
//! the same wrong answer and passes. The `fp.min`/`fp.max` ±0 wrong-`unsat` fixed
//! in commit `af6c8bf` was exactly such a bug — a faithfulness defect, not a
//! determinism defect. Only an **independent oracle**, applied to **every**
//! input, catches it.
//!
//! For a small format every input bit pattern is enumerable. `FP8_E5M2` is 8 bits
//! (256 patterns; 65 536 binary pairs), so the miter is genuinely *exhaustive*:
//! the witnessed operators are faithful to the reference for the **entire** input
//! space, with no sampling.
//!
//! ## Independent reference
//!
//! [`rustc_apfloat`] — the LLVM software-float library, developed independently of
//! Axeyum's FP code (so the check is not circular). It ships
//! [`rustc_apfloat::ieee::Float8E5M2`], a native S1E5M2 IEEE-754-conventions
//! 8-bit type matching Axeyum's [`axeyum_fp::FloatFormat::FP8_E5M2`] bit-for-bit
//! (sign·5·2 layout, ∞/NaN like IEEE). Its correctly-rounded `add_r`/`sub_r`/
//! `mul_r`, ordering (`PartialOrd`), and classification (`is_nan`/`is_zero`/
//! `is_negative`) are the oracle.
//!
//! ## Excluded (no clean independent reference / not a circuit this slice)
//!
//! - **`FP8_E4M3` / `FP4_E2M1`**: deviate from IEEE (no ∞; different NaN). Axeyum
//!   itself routes their *arithmetic* to `unsupported` (`arithmetic_format_supported`
//!   is gated on `is_ieee()`), so there is no circuit to witness here — and
//!   `rustc_apfloat`'s `Float8E4M3FN` (`NanOnly` behavior) would have to be matched
//!   against an Axeyum circuit that does not exist. Future work, once Axeyum grows
//!   a validated E4M3 arithmetic circuit and its own special-value convention.
//! - **Large formats** (`F32`/`F64`/`F128`): not exhaustively enumerable; they are
//!   covered by the existing sampled differential tests against native arithmetic
//!   and `rustc_apfloat`'s `Quad`.
//!
//! ## Documented allowed non-determinism (so the miter is neither too strict nor
//! unsound)
//!
//! - **`fp.min`/`fp.max` over opposite-sign zeros** (`min(+0,−0)` etc.) is
//!   *unspecified* in SMT-LIB — the result may be `+0` **or** `−0`. Axeyum encodes
//!   this with a fresh per-application sign bit (commit `af6c8bf`). The miter
//!   therefore accepts **either** zero sign for that one case (it asserts only that
//!   the result is *a* zero), evaluating the circuit under both settings of the
//!   fresh bit to confirm both are reachable.
//! - **NaN bit patterns**: `fp.eq`/`fp.lt` treat all NaNs as unordered; arithmetic
//!   producing a NaN is compared NaN-to-NaN (any NaN matches), since SMT-LIB does
//!   not pin the NaN payload.
//! - **`fp.min`/`fp.max` NaN propagation**: SMT-LIB returns the *other operand
//!   verbatim* (`min(NaN,y)=y`), so that case is compared to the other input's
//!   exact bits, not to a reference round-trip (which would canonicalize the NaN).

use axeyum_fp::{FloatFormat, RoundingMode, abs, add, eq, leq, lt, max, min, mul, neg, sub};
use axeyum_ir::{Assignment, Sort, TermArena, TermId, Value, eval};
use rustc_apfloat::Float;
use rustc_apfloat::ieee::Float8E5M2 as Ref;

const FMT: FloatFormat = FloatFormat::FP8_E5M2;
const WIDTH: u32 = 8; // FP8_E5M2 total width
const N: u128 = 1 << WIDTH; // 256 patterns

const RNE: rustc_apfloat::Round = rustc_apfloat::Round::NearestTiesToEven;

// --- reference helpers (rustc_apfloat) ---------------------------------------

fn r_from(bits: u128) -> Ref {
    Ref::from_bits(bits)
}

fn is_ref_nan(bits: u128) -> bool {
    r_from(bits).is_nan()
}

fn is_ref_zero(bits: u128) -> bool {
    r_from(bits).is_zero()
}

fn is_ref_neg(bits: u128) -> bool {
    r_from(bits).is_negative()
}

// --- circuit evaluation ------------------------------------------------------

/// Builds a binary FP op circuit over two symbolic 8-bit operands and returns a
/// closure that evaluates it on a concrete `(x, y)` bit pair via the *strict*
/// ground evaluator (no SAT, no replay — the circuit's own denotation).
fn binary_evaluator(
    build: impl Fn(
        &mut TermArena,
        FloatFormat,
        TermId,
        TermId,
        RoundingMode,
    ) -> Result<TermId, axeyum_ir::IrError>,
) -> impl Fn(u128, u128) -> u128 {
    let mut arena = TermArena::new();
    let sx = arena.declare("x", Sort::BitVec(WIDTH)).unwrap();
    let sy = arena.declare("y", Sort::BitVec(WIDTH)).unwrap();
    let (x, y) = (arena.var(sx), arena.var(sy));
    let t = build(&mut arena, FMT, x, y, RoundingMode::NearestEven).unwrap();
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
            Value::Bv { value, .. } => value,
            other => panic!("expected BV, got {other:?}"),
        }
    }
}

/// Builds a binary FP *predicate* circuit (returns a Bool) and evaluates it.
fn predicate_evaluator(
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

/// Builds a unary FP op circuit over one symbolic operand and evaluates it.
fn unary_evaluator(
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

/// Asserts two result bit patterns agree, treating *any* NaN as equal to *any*
/// NaN (SMT-LIB does not pin the NaN payload).
fn assert_bits_agree(got: u128, want: u128, ctx: &str) {
    if is_ref_nan(want) {
        assert!(is_ref_nan(got), "{ctx}: want NaN, got {got:#04x}");
    } else {
        assert_eq!(got, want, "{ctx}: bit-pattern mismatch");
    }
}

// --- exhaustive arithmetic miters --------------------------------------------

/// Exhaustively checks a correctly-rounded binary arithmetic op (all 65 536 input
/// pairs) against the `rustc_apfloat` reference at RNE.
fn exhaustive_arith(
    build: impl Fn(
        &mut TermArena,
        FloatFormat,
        TermId,
        TermId,
        RoundingMode,
    ) -> Result<TermId, axeyum_ir::IrError>,
    oracle: impl Fn(Ref, Ref) -> Ref,
    name: &str,
) {
    let circuit = binary_evaluator(build);
    for xb in 0..N {
        for yb in 0..N {
            let got = circuit(xb, yb);
            let want = oracle(r_from(xb), r_from(yb)).to_bits();
            assert_bits_agree(got, want, &format!("{name}({xb:#04x},{yb:#04x})"));
        }
    }
}

#[test]
fn fp8_e5m2_add_faithful_exhaustive() {
    exhaustive_arith(add, |a, b| a.add_r(b, RNE).value, "fp.add");
}

#[test]
fn fp8_e5m2_sub_faithful_exhaustive() {
    exhaustive_arith(sub, |a, b| a.sub_r(b, RNE).value, "fp.sub");
}

#[test]
fn fp8_e5m2_mul_faithful_exhaustive() {
    exhaustive_arith(mul, |a, b| a.mul_r(b, RNE).value, "fp.mul");
}

// --- exhaustive unary miters (neg / abs) -------------------------------------

#[test]
fn fp8_e5m2_neg_faithful_exhaustive() {
    // `fp.neg` is a pure sign-bit flip in SMT-LIB. We confirm Axeyum's circuit
    // flips exactly the sign bit AND that the resulting *value* matches the
    // independent reference's negation for every NON-NaN input. For NaN inputs the
    // reference may canonicalize the payload, so we only require the result to stay
    // NaN (the SMT-LIB-relevant invariant) — the bit-flip itself is checked
    // directly against the input.
    let circuit = unary_evaluator(neg);
    for xb in 0..N {
        let got = circuit(xb);
        // Direct spec: neg flips bit 7 (the sign).
        assert_eq!(got, xb ^ (1 << (WIDTH - 1)), "fp.neg({xb:#04x}): sign-flip");
        if is_ref_nan(xb) {
            assert!(is_ref_nan(got), "fp.neg({xb:#04x}) of NaN must stay NaN");
        } else {
            let want = (-r_from(xb)).to_bits();
            assert_eq!(got, want, "fp.neg({xb:#04x}) value vs reference");
        }
    }
}

#[test]
fn fp8_e5m2_abs_faithful_exhaustive() {
    // `fp.abs` clears the sign bit. Same independent-reference cross-check as neg.
    let circuit = unary_evaluator(abs);
    for xb in 0..N {
        let got = circuit(xb);
        assert_eq!(
            got,
            xb & !(1 << (WIDTH - 1)),
            "fp.abs({xb:#04x}): clear sign"
        );
        if is_ref_nan(xb) {
            assert!(is_ref_nan(got), "fp.abs({xb:#04x}) of NaN must stay NaN");
        } else {
            let want = r_from(xb).abs().to_bits();
            assert_eq!(got, want, "fp.abs({xb:#04x}) value vs reference");
        }
    }
}

// --- exhaustive comparison miters (eq / lt / leq) ----------------------------

#[test]
fn fp8_e5m2_eq_faithful_exhaustive() {
    // SMT-LIB fp.eq: false if either is NaN; else equal-by-value (+0 == -0).
    let circuit = predicate_evaluator(eq);
    for xb in 0..N {
        for yb in 0..N {
            let got = circuit(xb, yb);
            let want = if is_ref_nan(xb) || is_ref_nan(yb) {
                false
            } else {
                r_from(xb) == r_from(yb)
            };
            assert_eq!(got, want, "fp.eq({xb:#04x},{yb:#04x})");
        }
    }
}

#[test]
fn fp8_e5m2_lt_faithful_exhaustive() {
    // SMT-LIB fp.lt: ordered less-than; NaN unordered; ±0 equal.
    let circuit = predicate_evaluator(lt);
    for xb in 0..N {
        for yb in 0..N {
            let got = circuit(xb, yb);
            let want = r_from(xb) < r_from(yb); // PartialOrd: NaN ⇒ false, ±0 equal
            assert_eq!(got, want, "fp.lt({xb:#04x},{yb:#04x})");
        }
    }
}

#[test]
fn fp8_e5m2_leq_faithful_exhaustive() {
    // SMT-LIB fp.leq: lt ∨ eq; NaN unordered ⇒ false.
    let circuit = predicate_evaluator(leq);
    for xb in 0..N {
        for yb in 0..N {
            let got = circuit(xb, yb);
            let want = r_from(xb) <= r_from(yb);
            assert_eq!(got, want, "fp.leq({xb:#04x},{yb:#04x})");
        }
    }
}

// --- exhaustive min / max miters (the ±0 case the af6c8bf bug lived in) -------

/// The SMT-LIB selection rule for `fp.min`/`fp.max`, computed from the
/// *independent* reference's classification and ordering — NOT from Axeyum's own
/// FP code. Returns the chosen operand's **input bits** (min/max are exact, no
/// rounding: the result is one input verbatim), or `None` for the genuinely
/// unspecified opposite-sign-zero case.
fn smtlib_minmax_ref(xb: u128, yb: u128, want_min: bool) -> Option<u128> {
    let (rx, ry) = (r_from(xb), r_from(yb));
    // NaN propagation: the OTHER operand, verbatim.
    if rx.is_nan() {
        return Some(yb);
    }
    if ry.is_nan() {
        return Some(xb);
    }
    // Opposite-sign zeros: unspecified.
    if rx.is_zero() && ry.is_zero() && rx.is_negative() != ry.is_negative() {
        return None;
    }
    // Same-sign zeros compare equal under PartialOrd; pick consistently (either is
    // the same value, and for same-sign zeros the bits are identical anyway).
    let x_le_y = rx <= ry;
    let pick_x = if want_min { x_le_y } else { !x_le_y };
    Some(if pick_x { xb } else { yb })
}

/// Builds an `fp.min`/`fp.max` circuit over two **constant** operands and returns
/// the result bits — used for the deterministic (non-opposite-sign-zero) cases.
///
/// When BOTH operands are constant zeros of the *same* sign, Axeyum still
/// allocates the per-application fresh sign bit (the override is gated only on
/// *static non-zeroness*, not on the runtime opposite-sign test), but it sits in a
/// dead `ite` branch — the `opposite_sign_zero` predicate is runtime-false, so the
/// result is the deterministic same-sign zero regardless of the fresh bit. We bind
/// that fresh symbol (if present) to `0` so the strict evaluator never hits an
/// unbound symbol; the bound value is immaterial to the (dead-branch) result.
fn minmax_const_bits(build_min: bool, xb: u128, yb: u128) -> u128 {
    let mut arena = TermArena::new();
    let xc = arena.bv_const(WIDTH, xb).unwrap();
    let yc = arena.bv_const(WIDTH, yb).unwrap();
    let t = if build_min {
        min(&mut arena, FMT, xc, yc).unwrap()
    } else {
        max(&mut arena, FMT, xc, yc).unwrap()
    };
    let op = if build_min { "min" } else { "max" };
    let mut asg = Assignment::new();
    if let Some(sym) = arena.find_internal_symbol(&format!(
        "axeyum_fp.{op}.signzero.{}.{}",
        xc.index(),
        yc.index()
    )) {
        asg.set(sym, Value::Bv { width: 1, value: 0 });
    }
    match eval(&arena, t, &asg).unwrap() {
        Value::Bv { value, .. } => value,
        other => panic!("expected BV, got {other:?}"),
    }
}

/// For the opposite-sign-zero case: build the constant `min`/`max`, find the fresh
/// per-application sign bit Axeyum allocated, and confirm the circuit yields **a
/// zero** under BOTH settings of that bit (both signs reachable — the documented
/// SMT-LIB unspecified behavior). Asserts the magnitude is always zero so the
/// nondeterminism is confined to the sign, never to a wrong value.
fn assert_opposite_zero_minmax(build_min: bool, xb: u128, yb: u128) {
    let mut arena = TermArena::new();
    let xc = arena.bv_const(WIDTH, xb).unwrap();
    let yc = arena.bv_const(WIDTH, yb).unwrap();
    let t = if build_min {
        min(&mut arena, FMT, xc, yc).unwrap()
    } else {
        max(&mut arena, FMT, xc, yc).unwrap()
    };
    let op = if build_min { "min" } else { "max" };
    let sym_name = format!("axeyum_fp.{op}.signzero.{}.{}", xc.index(), yc.index());
    let sym = arena
        .find_internal_symbol(&sym_name)
        .unwrap_or_else(|| panic!("opposite-sign-zero fp.{op} must allocate {sym_name}"));
    let mut saw_pos = false;
    let mut saw_neg = false;
    for bit in [0u128, 1u128] {
        let mut asg = Assignment::new();
        asg.set(
            sym,
            Value::Bv {
                width: 1,
                value: bit,
            },
        );
        let got = match eval(&arena, t, &asg).unwrap() {
            Value::Bv { value, .. } => value,
            other => panic!("expected BV, got {other:?}"),
        };
        // Result must be a zero (magnitude 0) of one of the two signs.
        assert!(
            is_ref_zero(got),
            "fp.{op}({xb:#04x},{yb:#04x}) opposite-sign-zero result must be a zero, got {got:#04x}"
        );
        if is_ref_neg(got) {
            saw_neg = true;
        } else {
            saw_pos = true;
        }
    }
    // Both signs are reachable: the encoding is genuinely free (not pinned).
    assert!(
        saw_pos && saw_neg,
        "fp.{op}({xb:#04x},{yb:#04x}) opposite-sign-zero sign must be free (both ±0 reachable)"
    );
}

fn exhaustive_minmax(want_min: bool, name: &str) {
    for xb in 0..N {
        for yb in 0..N {
            match smtlib_minmax_ref(xb, yb, want_min) {
                None => assert_opposite_zero_minmax(want_min, xb, yb),
                Some(want) => {
                    let got = minmax_const_bits(want_min, xb, yb);
                    // min/max are exact (one input verbatim) — bit-exact, but the
                    // NaN-propagation branch already returns the other input's bits
                    // so this is exact there too. Use NaN-tolerant compare for
                    // safety in the (here impossible) NaN-result case.
                    assert_bits_agree(got, want, &format!("{name}({xb:#04x},{yb:#04x})"));
                }
            }
        }
    }
}

#[test]
fn fp8_e5m2_min_faithful_exhaustive() {
    exhaustive_minmax(true, "fp.min");
}

#[test]
fn fp8_e5m2_max_faithful_exhaustive() {
    exhaustive_minmax(false, "fp.max");
}

// --- the miter has teeth -----------------------------------------------------

/// A self-test proving the exhaustive miter would CATCH an `af6c8bf`-style
/// unfaithful lowering. We model a *wrong* `fp.min` that, on `min(+0, −0)`,
/// deterministically returns `+0` (pinning the sign instead of leaving it free) —
/// the class of bug `af6c8bf` was. The reference says this pair is *unspecified*
/// (`smtlib_minmax_ref` returns `None`), so a faithful circuit must leave the sign
/// free; a circuit that pins it to a single value is unfaithful. The teeth check:
/// our opposite-sign-zero assertion REQUIRES both signs reachable, so a pinned
/// circuit fails it. We assert here that a pinned result is rejected.
#[test]
fn miter_has_teeth_against_pinned_signzero() {
    // +0 and -0 in E5M2: 0x00 and 0x80.
    const POS_ZERO: u128 = 0x00;
    const NEG_ZERO: u128 = 0x80;
    // The reference correctly flags this as the unspecified case.
    assert_eq!(
        smtlib_minmax_ref(POS_ZERO, NEG_ZERO, true),
        None,
        "min(+0,-0) must be the unspecified opposite-sign-zero case"
    );
    // A would-be unfaithful circuit pins the result to a single sign. Emulate the
    // miter's reachability requirement against such a pinned producer: it offers
    // only +0 regardless of the (would-be) free bit, so only one sign is ever
    // seen — the `saw_pos && saw_neg` invariant the real miter enforces fails.
    let pinned = |_free_bit: u128| POS_ZERO; // always +0 — the af6c8bf-class bug
    let mut saw_pos = false;
    let mut saw_neg = false;
    for bit in [0u128, 1u128] {
        let got = pinned(bit);
        assert!(is_ref_zero(got));
        if is_ref_neg(got) {
            saw_neg = true;
        } else {
            saw_pos = true;
        }
    }
    assert!(
        !(saw_pos && saw_neg),
        "a pinned-sign circuit must NOT satisfy the both-signs-reachable invariant"
    );
    // Conversely, the REAL Axeyum circuit DOES satisfy it (checked exhaustively in
    // `fp8_e5m2_min_faithful_exhaustive`); this asserts the teeth directly.
    assert_opposite_zero_minmax(true, POS_ZERO, NEG_ZERO);
}
