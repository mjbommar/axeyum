//! Floating-point (IEEE 754) predicates, classification, sign ops, equality,
//! and ordering as **bit-vector formula builders** — the non-arithmetic core of
//! the SMT `FloatingPoint` theory.
//!
//! A floating-point value of format `(eb, sb)` (exponent bits `eb`, significand
//! bits `sb` *including* the hidden bit) is exactly an `eb + sb`-bit IEEE 754
//! bit pattern, so — like the finite enum/record helpers (ADR-0008) — this
//! needs **no new IR sort**: an FP "variable" is a `BitVec(eb + sb)` and every
//! operation here builds a bit-vector/Boolean formula over it. Solving and model
//! replay therefore reuse the existing sound, replayed bit-vector path unchanged.
//!
//! Layout (MSB→LSB): sign (1 bit), biased exponent (`eb` bits), trailing
//! significand (`sb - 1` bits). Semantics follow SMT-LIB / IEEE 754:
//! `fp.eq` is *not* bit equality (`NaN ≠ NaN`, `+0 = -0`), `fp.lt`/`fp.leq` order
//! by value (NaN unordered, `±0` equal), and `fp.isNegative`/`isPositive` exclude
//! NaN and zeros.
//!
//! What is here: classification (`isNaN`/`isInfinite`/`isZero`/`isNormal`/
//! `isSubnormal`/`isNegative`/`isPositive`), `abs`/`neg`, `eq`, the four
//! comparisons, `min`/`max`; arithmetic as *constant folds* over F32/F64
//! (`add`/`sub`/`mul`/`div`/`sqrt`/`fma`/`rem`/`roundToIntegral`) and as
//! *validated symbolic* bit-blasters (`add`/`mul`/`div`/`sqrt`/`roundToIntegral`,
//! checked against native arithmetic); and int/real conversions. `fp.rem` is the
//! exact IEEE remainder (no rounding). **Not** yet here: symbolic `fp.rem`, and
//! symbolic conversions between FP and the `Real` sort.
//!
//! # Errors
//!
//! Every builder shares one error contract: it returns [`IrError::SortMismatch`]
//! if an operand is not a `BitVec` of the format's width, or the underlying
//! [`IrError`] from an IR builder (which cannot occur for well-formed input).
#![allow(clippy::missing_errors_doc)] // uniform contract documented above

use axeyum_ir::{IrError, MAX_BV_WIDTH, Rational, Sort, TermArena, TermId, TermNode};

/// An IEEE 754 binary format: `exp_bits` exponent bits and `sig_bits`
/// significand bits (the latter *including* the hidden bit). The bit width of a
/// value is `exp_bits + sig_bits`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FloatFormat {
    /// Exponent width in bits.
    pub exp_bits: u32,
    /// Significand width in bits, including the hidden leading bit.
    pub sig_bits: u32,
}

impl FloatFormat {
    /// IEEE 754 binary16 (half precision).
    pub const F16: Self = Self {
        exp_bits: 5,
        sig_bits: 11,
    };
    /// IEEE 754 binary32 (single precision).
    pub const F32: Self = Self {
        exp_bits: 8,
        sig_bits: 24,
    };
    /// IEEE 754 binary64 (double precision).
    pub const F64: Self = Self {
        exp_bits: 11,
        sig_bits: 53,
    };
    /// bfloat16 (BF16): the top 16 bits of an f32 — 8 exponent bits, 8
    /// significand bits. Ubiquitous in ML/GPU compute; IEEE-style (∞/NaN), so
    /// the generic arithmetic here is correct for it.
    pub const BF16: Self = Self {
        exp_bits: 8,
        sig_bits: 8,
    };
    /// NVIDIA TensorFloat-32 (TF32): 8 exponent bits, 11 significand bits (f32
    /// range, f16-ish precision). IEEE-style.
    pub const TF32: Self = Self {
        exp_bits: 8,
        sig_bits: 11,
    };
    /// OCP FP8 E5M2: 5 exponent bits, 3 significand bits. IEEE-style (has ∞/NaN),
    /// so the generic arithmetic is correct. (Its sibling E4M3 deviates from
    /// IEEE — no ∞, a single NaN encoding, extended max — and would need a
    /// per-format special-value convention; not provided here.)
    pub const FP8_E5M2: Self = Self {
        exp_bits: 5,
        sig_bits: 3,
    };
    /// OCP FP8 E4M3: 4 exponent bits, 4 significand bits. **Deviates from IEEE**
    /// (no infinities; a single NaN encoding `S.1111.111`; the all-ones exponent
    /// is reused for finite values, extending the max to ±448). Use the
    /// `e4m3_is_*` classification predicates — the generic IEEE classification and
    /// arithmetic are **not** correct for it (its overflow/saturation semantics
    /// need the OCP spec and a validation oracle; arithmetic is not yet provided).
    pub const FP8_E4M3: Self = Self {
        exp_bits: 4,
        sig_bits: 4,
    };
    /// OCP MX **element** format FP4 E2M1: 2 exponent bits, 2 significand bits
    /// (4 bits total). All-finite: **no infinities, no NaN** — every bit pattern
    /// is one of `±{0, 0.5, 1, 1.5, 2, 3, 4, 6}`. (This is only the *element*; a
    /// full MXFP4 value is a *block* of 32 such elements times a shared E8M0
    /// scale — a structured/array semantics, not a scalar sort.) Use the `e2m1_*`
    /// helpers; the generic IEEE classification/arithmetic is not correct for it.
    pub const FP4_E2M1: Self = Self {
        exp_bits: 2,
        sig_bits: 2,
    };

    /// Total bit width of a value in this format.
    #[must_use]
    pub const fn width(self) -> u32 {
        self.exp_bits + self.sig_bits
    }

    /// Whether this format follows IEEE 754 conventions (an all-ones exponent
    /// encodes ∞/NaN). The OCP FP8 `E4M3` and FP4 `E2M1` formats do not and need
    /// their dedicated helpers; the generic IEEE arithmetic is not valid for them.
    #[must_use]
    pub fn is_ieee(self) -> bool {
        self != Self::FP8_E4M3 && self != Self::FP4_E2M1
    }

    /// Decodes a constant bit pattern of this (IEEE) format to its exact `f64`
    /// value. Exact for every supported IEEE format (`sig_bits ≤ 53`). Only valid
    /// for IEEE formats — see [`Self::is_ieee`].
    #[allow(
        clippy::cast_possible_truncation,
        clippy::cast_possible_wrap,
        clippy::cast_precision_loss
    )] // frac < 2^52 is exact in f64; exponents are small and in i32 range
    fn decode_ieee_f64(self, bits: u128) -> f64 {
        let frac_bits = self.sig_bits - 1;
        let s = if (bits >> (self.width() - 1)) & 1 == 1 { -1.0 } else { 1.0 };
        let exp_mask = (1u128 << self.exp_bits) - 1;
        let exp = (bits >> frac_bits) & exp_mask;
        let frac = bits & ((1u128 << frac_bits) - 1);
        let exp_bias = (1i64 << (self.exp_bits - 1)) - 1;
        if exp == exp_mask {
            return if frac != 0 { f64::NAN } else { s * f64::INFINITY };
        }
        if exp == 0 {
            // subnormal (or zero): frac · 2^(1 − bias − frac_bits)
            return s * (frac as f64) * (2.0f64).powi((1 - exp_bias - i64::from(frac_bits)) as i32);
        }
        // normal: (frac + 2^frac_bits) · 2^(exp − bias − frac_bits)
        let mant = (frac as f64) + (2.0f64).powi(frac_bits as i32);
        s * mant * (2.0f64).powi((exp as i64 - exp_bias - i64::from(frac_bits)) as i32)
    }

    fn check(self, arena: &TermArena, x: TermId) -> Result<(), IrError> {
        let expected = Sort::BitVec(self.width());
        let found = arena.sort_of(x);
        if found == expected {
            Ok(())
        } else {
            Err(IrError::SortMismatch {
                expected: "BitVec matching the float format width",
                found,
            })
        }
    }

    fn sign(self, arena: &mut TermArena, x: TermId) -> Result<TermId, IrError> {
        let top = self.width() - 1;
        arena.extract(top, top, x)
    }

    fn exponent(self, arena: &mut TermArena, x: TermId) -> Result<TermId, IrError> {
        arena.extract(self.width() - 2, self.sig_bits - 1, x)
    }

    fn trailing_sig(self, arena: &mut TermArena, x: TermId) -> Result<TermId, IrError> {
        arena.extract(self.sig_bits - 2, 0, x)
    }
}

// --- OCP FP8 E4M3 classification (non-IEEE conventions) -----------------------
//
// E4M3 (1 sign, 4 exp, 3 significand) has NO infinities, exactly one NaN
// (`S.1111.111`), and reuses the all-ones exponent for finite values (max ±448).
// So its classification differs from the IEEE [`is_nan`]/[`is_infinite`]/… and is
// provided separately. Arithmetic on E4M3 is not yet supported (the
// overflow/saturation behavior needs the OCP spec and a validation oracle).

fn e4m3_fields(arena: &mut TermArena, x: TermId) -> Result<(TermId, TermId), IrError> {
    // (exponent[4], trailing significand[3]) of an 8-bit E4M3 value.
    let exp = arena.extract(6, 3, x)?;
    let mant = arena.extract(2, 0, x)?;
    Ok((exp, mant))
}

/// `x` is the (unique) E4M3 NaN: exponent all ones **and** significand all ones.
pub fn e4m3_is_nan(arena: &mut TermArena, x: TermId) -> Result<TermId, IrError> {
    let (exp, mant) = e4m3_fields(arena, x)?;
    let ones4 = arena.bv_const(4, 0xF)?;
    let ones3 = arena.bv_const(3, 0x7)?;
    let e = arena.eq(exp, ones4)?;
    let m = arena.eq(mant, ones3)?;
    arena.and(e, m)
}

/// `x` is an E4M3 zero (`±0`).
pub fn e4m3_is_zero(arena: &mut TermArena, x: TermId) -> Result<TermId, IrError> {
    let (exp, mant) = e4m3_fields(arena, x)?;
    let zero_exp = arena.bv_const(4, 0)?;
    let zero_sig = arena.bv_const(3, 0)?;
    let e = arena.eq(exp, zero_exp)?;
    let m = arena.eq(mant, zero_sig)?;
    arena.and(e, m)
}

/// `x` is an E4M3 subnormal: zero exponent, non-zero significand.
pub fn e4m3_is_subnormal(arena: &mut TermArena, x: TermId) -> Result<TermId, IrError> {
    let (exp, mant) = e4m3_fields(arena, x)?;
    let zero_exp = arena.bv_const(4, 0)?;
    let zero_sig = arena.bv_const(3, 0)?;
    let e = arena.eq(exp, zero_exp)?;
    let m = arena.eq(mant, zero_sig)?;
    let mnz = arena.not(m)?;
    arena.and(e, mnz)
}

/// `x` is an E4M3 normal number: non-zero exponent and not the NaN encoding
/// (the all-ones exponent is a *normal* range in E4M3, except `S.1111.111`).
pub fn e4m3_is_normal(arena: &mut TermArena, x: TermId) -> Result<TermId, IrError> {
    let (exp, _mant) = e4m3_fields(arena, x)?;
    let zero_exp = arena.bv_const(4, 0)?;
    let exp_is_zero = arena.eq(exp, zero_exp)?;
    let exp_nonzero = arena.not(exp_is_zero)?;
    let nan = e4m3_is_nan(arena, x)?;
    let not_nan = arena.not(nan)?;
    arena.and(exp_nonzero, not_nan)
}

// --- OCP MX element FP4 E2M1 (all-finite, no ∞/NaN) ---------------------------
//
// E2M1 (1 sign, 2 exp, 1 significand) has no infinities and no NaN; every code
// is a finite value in ±{0, 0.5, 1, 1.5, 2, 3, 4, 6}. So `e2m1_is_nan` and
// `e2m1_is_infinite` are always false; classification reduces to zero vs
// subnormal vs normal, and the value decodes exactly to a rational.

/// `x` is an E2M1 zero (`±0`): exponent and significand both zero.
pub fn e2m1_is_zero(arena: &mut TermArena, x: TermId) -> Result<TermId, IrError> {
    let body = arena.extract(2, 0, x)?; // exp(2) ++ sig(1) = low 3 bits
    let zero3 = arena.bv_const(3, 0)?;
    arena.eq(body, zero3)
}

/// `x` is an E2M1 subnormal: zero exponent, non-zero significand (`±0.5`).
pub fn e2m1_is_subnormal(arena: &mut TermArena, x: TermId) -> Result<TermId, IrError> {
    let exp = arena.extract(2, 1, x)?;
    let sig = arena.extract(0, 0, x)?;
    let z2 = arena.bv_const(2, 0)?;
    let o1 = arena.bv_const(1, 1)?;
    let exp_z = arena.eq(exp, z2)?;
    let sig_set = arena.eq(sig, o1)?;
    arena.and(exp_z, sig_set)
}

/// `x` is an E2M1 normal number: non-zero exponent (the all-ones exponent is a
/// normal value, `±4`/`±6`, in E2M1 — there is no infinity).
pub fn e2m1_is_normal(arena: &mut TermArena, x: TermId) -> Result<TermId, IrError> {
    let exp = arena.extract(2, 1, x)?;
    let z2 = arena.bv_const(2, 0)?;
    let exp_z = arena.eq(exp, z2)?;
    arena.not(exp_z)
}

/// Exactly decodes a **constant** E2M1 value to a `Real` (ADR-0015). E2M1 is
/// all-finite with a tiny exact value set, so this always succeeds for a
/// constant; returns `Ok(None)` for a non-constant operand. Bridges MX FP4
/// elements into linear real arithmetic (a block value is the element times its
/// shared power-of-two scale).
pub fn e2m1_to_real(arena: &mut TermArena, x: TermId) -> Result<Option<TermId>, IrError> {
    let Some(bits) = const_bits(arena, x) else {
        return Ok(None);
    };
    let sign = (bits >> 3) & 1 == 1;
    let exp = (bits >> 1) & 0b11;
    let mant = bits & 1;
    // magnitude as a rational num/den
    let (num, den): (i128, i128) = if exp == 0 {
        (i128::try_from(mant).unwrap_or(0), 2) // 0 or 1/2
    } else {
        // (2 + mant) * 2^(exp - 2)
        let base = 2 + i128::try_from(mant).unwrap_or(0);
        match exp {
            1 => (base, 2),       // *0.5
            2 => (base, 1),       // *1
            _ => (base * 2, 1),   // exp==3 -> *2
        }
    };
    let num = if sign { -num } else { num };
    Ok(Some(arena.real_const(Rational::new(num, den))))
}

/// `x` is NaN: exponent all ones and a non-zero trailing significand.
pub fn is_nan(arena: &mut TermArena, fmt: FloatFormat, x: TermId) -> Result<TermId, IrError> {
    fmt.check(arena, x)?;
    let all_ones = exp_all_ones(arena, fmt, x)?;
    let sig_nz = sig_nonzero(arena, fmt, x)?;
    arena.and(all_ones, sig_nz)
}

/// `x` is +∞ or −∞: exponent all ones and a zero trailing significand.
pub fn is_infinite(arena: &mut TermArena, fmt: FloatFormat, x: TermId) -> Result<TermId, IrError> {
    fmt.check(arena, x)?;
    let all_ones = exp_all_ones(arena, fmt, x)?;
    let sig_z = sig_zero(arena, fmt, x)?;
    arena.and(all_ones, sig_z)
}

/// `x` is +0 or −0: exponent all zero and a zero trailing significand.
pub fn is_zero(arena: &mut TermArena, fmt: FloatFormat, x: TermId) -> Result<TermId, IrError> {
    fmt.check(arena, x)?;
    let exp_z = exp_all_zero(arena, fmt, x)?;
    let sig_z = sig_zero(arena, fmt, x)?;
    arena.and(exp_z, sig_z)
}

/// `x` is subnormal: exponent all zero and a non-zero trailing significand.
pub fn is_subnormal(arena: &mut TermArena, fmt: FloatFormat, x: TermId) -> Result<TermId, IrError> {
    fmt.check(arena, x)?;
    let exp_z = exp_all_zero(arena, fmt, x)?;
    let sig_nz = sig_nonzero(arena, fmt, x)?;
    arena.and(exp_z, sig_nz)
}

/// `x` is a normal number: exponent neither all zero nor all ones.
pub fn is_normal(arena: &mut TermArena, fmt: FloatFormat, x: TermId) -> Result<TermId, IrError> {
    fmt.check(arena, x)?;
    let exp_z = exp_all_zero(arena, fmt, x)?;
    let exp_o = exp_all_ones(arena, fmt, x)?;
    let not_z = arena.not(exp_z)?;
    let not_o = arena.not(exp_o)?;
    arena.and(not_z, not_o)
}

/// `x` is negative: sign bit set, and `x` is neither NaN nor a zero.
pub fn is_negative(arena: &mut TermArena, fmt: FloatFormat, x: TermId) -> Result<TermId, IrError> {
    fmt.check(arena, x)?;
    let signed = sign_set(arena, fmt, x)?;
    let nan = is_nan(arena, fmt, x)?;
    let zero = is_zero(arena, fmt, x)?;
    not_nan_not_zero_and(arena, signed, nan, zero)
}

/// `x` is positive: sign bit clear, and `x` is neither NaN nor a zero.
pub fn is_positive(arena: &mut TermArena, fmt: FloatFormat, x: TermId) -> Result<TermId, IrError> {
    fmt.check(arena, x)?;
    let signed = sign_set(arena, fmt, x)?;
    let unsigned = arena.not(signed)?;
    let nan = is_nan(arena, fmt, x)?;
    let zero = is_zero(arena, fmt, x)?;
    not_nan_not_zero_and(arena, unsigned, nan, zero)
}

/// Absolute value: clears the sign bit.
pub fn abs(arena: &mut TermArena, fmt: FloatFormat, x: TermId) -> Result<TermId, IrError> {
    fmt.check(arena, x)?;
    let mask = arena.bv_const(fmt.width(), sign_mask(fmt) ^ all_ones_mask(fmt))?;
    arena.bv_and(x, mask)
}

/// Negation: flips the sign bit.
pub fn neg(arena: &mut TermArena, fmt: FloatFormat, x: TermId) -> Result<TermId, IrError> {
    fmt.check(arena, x)?;
    let mask = arena.bv_const(fmt.width(), sign_mask(fmt))?;
    arena.bv_xor(x, mask)
}

/// Symbolic `fp.sub` — `a − b`, via the exact IEEE identity
/// `fp.sub(a, b) = fp.add(a, fp.neg(b))` (which holds for every case, including
/// NaN/∞ and signed zeros: `a − (+0) = a + (−0)`, `a − (−0) = a + (+0)`). Same
/// format support as [`add`] (F16/F32/F64).
///
/// # Errors
///
/// Returns [`IrError`] from [`neg`] or [`add`] (mis-sized operand, width, etc.).
pub fn sub(
    arena: &mut TermArena,
    fmt: FloatFormat,
    a: TermId,
    b: TermId,
    mode: RoundingMode,
) -> Result<TermId, IrError> {
    let neg_b = neg(arena, fmt, b)?;
    add(arena, fmt, a, neg_b, mode)
}

/// IEEE equality `fp.eq`: neither operand is NaN, and they are the same value
/// (bit-identical, or both zero so `+0 = -0`).
pub fn eq(
    arena: &mut TermArena,
    fmt: FloatFormat,
    x: TermId,
    y: TermId,
) -> Result<TermId, IrError> {
    fmt.check(arena, x)?;
    fmt.check(arena, y)?;
    let nx = is_nan(arena, fmt, x)?;
    let ny = is_nan(arena, fmt, y)?;
    let no_nan = {
        let a = arena.not(nx)?;
        let b = arena.not(ny)?;
        arena.and(a, b)?
    };
    let bit_eq = arena.eq(x, y)?;
    let both_zero = {
        let zx = is_zero(arena, fmt, x)?;
        let zy = is_zero(arena, fmt, y)?;
        arena.and(zx, zy)?
    };
    let same = arena.or(bit_eq, both_zero)?;
    arena.and(no_nan, same)
}

/// `fp.lt`: ordered less-than (NaN unordered, `±0` equal).
pub fn lt(arena: &mut TermArena, fmt: FloatFormat, x: TermId, y: TermId) -> Result<TermId, IrError> {
    fmt.check(arena, x)?;
    fmt.check(arena, y)?;
    let nx = is_nan(arena, fmt, x)?;
    let ny = is_nan(arena, fmt, y)?;
    let no_nan = {
        let a = arena.not(nx)?;
        let b = arena.not(ny)?;
        arena.and(a, b)?
    };
    let both_zero = {
        let zx = is_zero(arena, fmt, x)?;
        let zy = is_zero(arena, fmt, y)?;
        arena.and(zx, zy)?
    };
    let not_both_zero = arena.not(both_zero)?;
    let kx = order_key(arena, fmt, x)?;
    let ky = order_key(arena, fmt, y)?;
    let key_lt = arena.bv_ult(kx, ky)?;
    let a = arena.and(no_nan, not_both_zero)?;
    arena.and(a, key_lt)
}

/// `fp.leq`: `lt(x, y) ∨ eq(x, y)`.
pub fn leq(
    arena: &mut TermArena,
    fmt: FloatFormat,
    x: TermId,
    y: TermId,
) -> Result<TermId, IrError> {
    let l = lt(arena, fmt, x, y)?;
    let e = eq(arena, fmt, x, y)?;
    arena.or(l, e)
}

/// `fp.gt`: `lt(y, x)`.
pub fn gt(arena: &mut TermArena, fmt: FloatFormat, x: TermId, y: TermId) -> Result<TermId, IrError> {
    lt(arena, fmt, y, x)
}

/// `fp.geq`: `leq(y, x)`.
pub fn geq(
    arena: &mut TermArena,
    fmt: FloatFormat,
    x: TermId,
    y: TermId,
) -> Result<TermId, IrError> {
    leq(arena, fmt, y, x)
}

/// `fp.min(x, y)`: the smaller operand. NaN propagates the other operand
/// (`min(NaN, y) = y`, `min(x, NaN) = x`); the result is always one of the input
/// bit patterns unchanged, so this is exact (no rounding).
///
/// For zeros of opposite sign — where SMT-LIB leaves the result unspecified —
/// this makes the deterministic, allowed choice `−0` (the smaller ordering key).
pub fn min(
    arena: &mut TermArena,
    fmt: FloatFormat,
    x: TermId,
    y: TermId,
) -> Result<TermId, IrError> {
    select_by_order(arena, fmt, x, y, true)
}

/// `fp.max(x, y)`: the larger operand. NaN propagates the other operand; the
/// result is one of the inputs unchanged (exact, no rounding). Opposite-sign
/// zeros pick `+0` (the larger ordering key), a deterministic allowed choice.
pub fn max(
    arena: &mut TermArena,
    fmt: FloatFormat,
    x: TermId,
    y: TermId,
) -> Result<TermId, IrError> {
    select_by_order(arena, fmt, x, y, false)
}

// --- symbolic round-and-pack (bit-blaster core, front half) -------------------

/// A signed constant of width `w` (two's complement of `val`).
#[allow(clippy::cast_sign_loss)]
fn sconst(arena: &mut TermArena, w: u32, val: i64) -> Result<TermId, IrError> {
    let mask = if w >= 128 { u128::MAX } else { (1u128 << w) - 1 };
    let bits = (i128::from(val) as u128) & mask;
    arena.bv_const(w, bits)
}

/// Front half of symbolic round-and-pack: from a (nonzero) significand `m_w` and
/// the exponent `e` of its least-significant bit (both `W`-bit, `e` signed),
/// compute `lsb_exp` (the exponent of the rounded result's LSB) and `drop` (how
/// many low bits of `m_w` to discard — negative means shift left), mirroring the
/// validated [`round_to_format`] reference. All arithmetic is `W`-bit signed.
///
/// Returns `(lsb_exp, drop)`. A bit-blaster building block (unstable surface).
pub fn pack_params(
    arena: &mut TermArena,
    m_w: TermId,
    e: TermId,
    sb: u32,
    bias: i64,
) -> Result<(TermId, TermId), IrError> {
    let Sort::BitVec(w) = arena.sort_of(m_w) else {
        return Err(IrError::SortMismatch {
            expected: "BitVec",
            found: arena.sort_of(m_w),
        });
    };
    // lead_idx = index of m_w's top set bit = (W-1) - clz(m_w).
    let clz = count_leading_zeros(arena, m_w)?;
    let w_minus_1 = sconst(arena, w, i64::from(w) - 1)?;
    let lead_idx = arena.bv_sub(w_minus_1, clz)?;
    // k = e + lead_idx; res_exp = max(k, emin); lsb_exp = res_exp - (sb-1).
    let k = arena.bv_add(e, lead_idx)?;
    let emin = sconst(arena, w, 1 - bias)?;
    let k_ge_emin = arena.bv_sge(k, emin)?;
    let res_exp = arena.ite(k_ge_emin, k, emin)?;
    let sbm1 = sconst(arena, w, i64::from(sb) - 1)?;
    let lsb_exp = arena.bv_sub(res_exp, sbm1)?;
    let drop = arena.bv_sub(lsb_exp, e)?;
    Ok((lsb_exp, drop))
}

/// Symbolic round-and-pack: rounds the value `(-1)^sign · m · 2^e` to format
/// `(eb, sb)` (round-nearest-ties-to-even) and returns the IEEE bit pattern
/// (`eb + sb` bits). `m` and `e` are `W`-bit (`e` signed); `m` carries the
/// significand (any leading-bit position — subnormal inputs need no special
/// pre-normalization). Handles normal/subnormal/overflow and the zero result.
///
/// This is the bit-vector transcription of [`round_to_format`] (validated there
/// in concrete arithmetic and, end to end, in tests) — the shared core both
/// `fp.add` and `fp.mul` round through. A pure BV formula; solves and replays
/// on the existing path. The caller handles NaN/∞ operands and supplies a `W`
/// wide enough that the rounding `drop` stays `< W` (see [`round_variable`]).
///
/// # Errors
///
/// Returns [`IrError`] from the builders (well-formed input cannot fail).
#[allow(clippy::similar_names, clippy::many_single_char_names, clippy::too_many_arguments)]
pub fn pack_value(
    arena: &mut TermArena,
    eb: u32,
    sb: u32,
    sign: TermId,
    m: TermId,
    e: TermId,
    mode: RoundingMode,
) -> Result<TermId, IrError> {
    let Sort::BitVec(w) = arena.sort_of(m) else {
        return Err(IrError::SortMismatch {
            expected: "BitVec",
            found: arena.sort_of(m),
        });
    };
    let total = eb + sb;
    let bias = (1i64 << (eb - 1)) - 1;
    let zero_w = arena.bv_const(w, 0)?;

    let (lsb_exp, drop) = pack_params(arena, m, e, sb, bias)?;

    // q = the rounded/scaled significand: shift left if drop<0, round right if
    // 0<=drop<W. When drop>=W the whole value is below the grid: nearest/
    // toward-zero give 0, but a directed mode rounds a nonzero value up to the
    // smallest representable magnitude (1) when the sign matches its direction.
    let one_w = arena.bv_const(w, 1)?;
    let neg_drop = arena.bv_sub(zero_w, drop)?;
    let left = arena.bv_shl(m, neg_drop)?;
    let rounded = round_variable(arena, m, drop, mode, sign)?;
    let drop_lt0 = arena.bv_slt(drop, zero_w)?;
    let w_const = sconst(arena, w, i64::from(w))?;
    let drop_ge_w = arena.bv_sge(drop, w_const)?;
    let tiny_q = {
        let m_nonzero = {
            let z = arena.eq(m, zero_w)?;
            arena.not(z)?
        };
        let up = match mode {
            RoundingMode::TowardPositive => {
                let pos = arena.not(sign)?;
                arena.and(m_nonzero, pos)?
            }
            RoundingMode::TowardNegative => arena.and(m_nonzero, sign)?,
            _ => arena.bool_const(false),
        };
        arena.ite(up, one_w, zero_w)?
    };
    let right = arena.ite(drop_ge_w, tiny_q, rounded)?;
    let q = arena.ite(drop_lt0, left, right)?;

    // Result exponent of q's leading bit.
    let clz_q = count_leading_zeros(arena, q)?;
    let w_minus_1 = sconst(arena, w, i64::from(w) - 1)?;
    let top = arena.bv_sub(w_minus_1, clz_q)?;
    let bias_c = sconst(arena, w, bias)?;
    let biased = {
        let t = arena.bv_add(lsb_exp, top)?;
        arena.bv_add(t, bias_c)?
    };

    // Classify the result exponent.
    let exp_max = sconst(arena, w, (1i64 << eb) - 1)?;
    let overflow = arena.bv_sge(biased, exp_max)?;
    let subnormal = arena.bv_sle(biased, zero_w)?;
    let m_zero = arena.eq(m, zero_w)?;
    let q_zero = arena.eq(q, zero_w)?;
    let is_zero_result = arena.or(m_zero, q_zero)?;

    // Assemble the result fields (total-bit).
    let sign_bit = {
        let on = arena.bv_const(total, 1u128 << (total - 1))?;
        let off = arena.bv_const(total, 0)?;
        arena.ite(sign, on, off)?
    };
    let exp_ones = arena.bv_const(total, ((1u128 << eb) - 1) << (sb - 1))?;
    let inf_bits = arena.bv_or(sign_bit, exp_ones)?;

    // Subnormal: exponent field 0, trailing = low (sb-1) bits of q.
    let subnormal_bits = {
        let q_low = arena.extract(sb - 2, 0, q)?;
        let q_low_t = arena.zero_ext(total - (sb - 1), q_low)?;
        arena.bv_or(sign_bit, q_low_t)?
    };
    // Normal: trailing = (q - 2^top) low (sb-1) bits; exponent field = biased.
    let normal_bits = {
        let one_w = arena.bv_const(w, 1)?;
        let pow_top = arena.bv_shl(one_w, top)?;
        let qmt = arena.bv_sub(q, pow_top)?;
        let trail = arena.extract(sb - 2, 0, qmt)?;
        let trail_t = arena.zero_ext(total - (sb - 1), trail)?;
        let biased_field = arena.extract(eb - 1, 0, biased)?;
        let biased_t = arena.zero_ext(total - eb, biased_field)?;
        let shift = arena.bv_const(total, u128::from(sb - 1))?;
        let exp_placed = arena.bv_shl(biased_t, shift)?;
        let with_exp = arena.bv_or(sign_bit, exp_placed)?;
        arena.bv_or(with_exp, trail_t)?
    };

    // Mux: zero, then overflow→∞, then subnormal, else normal.
    let normal_or_sub = arena.ite(subnormal, subnormal_bits, normal_bits)?;
    let finite = arena.ite(overflow, inf_bits, normal_or_sub)?;
    arena.ite(is_zero_result, sign_bit, finite)
}

/// Symbolic `fp.mul` (round-nearest-ties-to-even): the IEEE 754 multiplication
/// bit-blaster. Unpacks both operands (handling subnormals), multiplies the
/// significands and adds the exponents, rounds and packs the result via
/// [`pack_value`], then muxes the special cases (NaN, `0·∞ = NaN`, `∞`, zero).
/// A pure bit-vector formula, so it solves and replays on the existing path.
///
/// This is a validated — not formally proven — bit-blaster: its building blocks
/// and `pack_value` are checked against native arithmetic, and `mul` itself is
/// differentially validated against native `f32` multiplication in tests
/// (specials, subnormals, and products that overflow/underflow).
///
/// **Format support.** The intermediate is `2·sig_bits + 3` bits, so this works
/// for any format with `2·sig_bits + 3 ≤ 128` ([`MAX_BV_WIDTH`]) — **F16, F32,
/// and F64** (109 bits). Wider formats return [`IrError::InvalidWidth`].
///
/// # Errors
///
/// Returns [`IrError::InvalidWidth`] if the format's intermediate width exceeds
/// [`MAX_BV_WIDTH`], [`IrError::SortMismatch`] if an operand is not a `BitVec` of
/// the format width, or [`IrError`] from the builders.
#[allow(clippy::similar_names, clippy::many_single_char_names)]
pub fn mul(arena: &mut TermArena, fmt: FloatFormat, a: TermId, b: TermId, mode: RoundingMode) -> Result<TermId, IrError> {
    fmt.check(arena, a)?;
    fmt.check(arena, b)?;
    let (eb, sb) = (fmt.exp_bits, fmt.sig_bits);
    let total = fmt.width();
    // The significand product is exactly 2·sb bits and `mul` never needs a
    // normalizing left shift (a product of significands has its leading bit at
    // index ≥ sb−1 whenever the result is normal), so `pack_value` only ever
    // rounds *down* — 2·sb + 3 bits suffice, which fits F16/F32/F64 in 128 bits.
    let w = 2 * sb + 3;
    if w > MAX_BV_WIDTH {
        return Err(IrError::InvalidWidth(w));
    }

    let one1 = arena.bv_const(1, 1)?;
    let (sa, sig_a, e_a) = unpack_operand(arena, fmt, w, a)?;
    let (sb_bit, sig_b, e_b) = unpack_operand(arena, fmt, w, b)?;

    let product = arena.bv_mul(sig_a, sig_b)?;
    let e_prod = arena.bv_add(e_a, e_b)?;
    let sign_xor_bit = arena.bv_xor(sa, sb_bit)?;
    let sign_xor = arena.eq(sign_xor_bit, one1)?;
    let finite = pack_value(arena, eb, sb, sign_xor, product, e_prod, mode)?;

    // Special-case flags.
    let na = is_nan(arena, fmt, a)?;
    let nb = is_nan(arena, fmt, b)?;
    let ia = is_infinite(arena, fmt, a)?;
    let ib = is_infinite(arena, fmt, b)?;
    let za = is_zero(arena, fmt, a)?;
    let zb = is_zero(arena, fmt, b)?;
    let inf_zero = {
        let l = arena.and(ia, zb)?;
        let r = arena.and(za, ib)?;
        arena.or(l, r)?
    };
    let nan_flag = {
        let t = arena.or(na, nb)?;
        arena.or(t, inf_zero)?
    };
    let inf_flag = arena.or(ia, ib)?;
    let zero_flag = arena.or(za, zb)?;

    // Result field constants.
    let sign_total = {
        let on = arena.bv_const(total, 1u128 << (total - 1))?;
        let off = arena.bv_const(total, 0)?;
        arena.ite(sign_xor, on, off)?
    };
    let exp_ones = arena.bv_const(total, ((1u128 << eb) - 1) << (sb - 1))?;
    let qnan = {
        let q = arena.bv_const(total, 1u128 << (sb - 2))?;
        arena.bv_or(exp_ones, q)?
    };
    let inf_total = arena.bv_or(sign_total, exp_ones)?;

    // Mux: NaN, then ∞, then zero, else the rounded finite product.
    let if_zero = arena.ite(zero_flag, sign_total, finite)?;
    let if_inf = arena.ite(inf_flag, inf_total, if_zero)?;
    arena.ite(nan_flag, qnan, if_inf)
}

/// Unpacks an FP operand into `(sign_bit, significand_w, lsb_exponent_w)`, all
/// in working width `w`: the significand (with the hidden bit, subnormal-aware)
/// zero-extended to `w`, and the signed exponent of its least-significant bit.
/// Shared by `add` and `mul`.
fn unpack_operand(
    arena: &mut TermArena,
    fmt: FloatFormat,
    w: u32,
    x: TermId,
) -> Result<(TermId, TermId, TermId), IrError> {
    let (eb, sb, total) = (fmt.exp_bits, fmt.sig_bits, fmt.width());
    let bias = (1i64 << (eb - 1)) - 1;
    let sx = arena.extract(total - 1, total - 1, x)?;
    let exp_x = arena.extract(total - 2, sb - 1, x)?;
    let trail_x = arena.extract(sb - 2, 0, x)?;
    let exp_zero = arena.bv_const(eb, 0)?;
    let is_sub = arena.eq(exp_x, exp_zero)?;
    let one1 = arena.bv_const(1, 1)?;
    let zero1 = arena.bv_const(1, 0)?;
    let hidden = arena.ite(is_sub, zero1, one1)?;
    let sig = arena.concat(hidden, trail_x)?;
    let sig_w = arena.zero_ext(w - sb, sig)?;
    let exp_w = arena.zero_ext(w - eb, exp_x)?;
    let one_w = arena.bv_const(w, 1)?;
    let eff = arena.ite(is_sub, one_w, exp_w)?;
    let bias_sbm1 = sconst(arena, w, bias + i64::from(sb) - 1)?;
    let e = arena.bv_sub(eff, bias_sbm1)?;
    Ok((sx, sig_w, e))
}

/// Symbolic `fp.sqrt` (round-nearest-ties-to-even): the IEEE 754 square-root
/// bit-blaster. Makes the exponent even, takes the integer square root of the
/// (scaled) significand via [`isqrt`] (remainder → sticky bit), halves the
/// exponent, rounds via [`pack_value`], and muxes the special cases
/// (`sqrt(NaN)` and `sqrt(x<0)` → NaN, `sqrt(±0) = ±0`, `sqrt(+∞) = +∞`). Pure
/// bit-vector formula; solves and replays on the existing path.
///
/// Works for **F16/F32/F64** (the working width stays ≤ 128). Validated against
/// native `f32`/`f64` `sqrt`.
///
/// # Errors
///
/// Returns [`IrError::InvalidWidth`] if the format is too wide,
/// [`IrError::SortMismatch`] for a mis-sized operand, or [`IrError`] from builders.
#[allow(clippy::similar_names, clippy::many_single_char_names)]
pub fn sqrt(arena: &mut TermArena, fmt: FloatFormat, x: TermId, mode: RoundingMode) -> Result<TermId, IrError> {
    fmt.check(arena, x)?;
    let (eb, sb) = (fmt.exp_bits, fmt.sig_bits);
    let total = fmt.width();
    let shift = (sb + 1).div_ceil(2) + 3; // result fractional bits
    let mut w = (sb + 1) + 2 * shift;
    if w % 2 != 0 {
        w += 1; // isqrt needs an even width
    }
    if w > MAX_BV_WIDTH {
        return Err(IrError::InvalidWidth(w));
    }

    let (_sx, sig_w, e) = unpack_operand(arena, fmt, w, x)?;
    let one_w = arena.bv_const(w, 1)?;
    let zero_w = arena.bv_const(w, 0)?;

    // Normalize a (sub)normal significand to a full sb-bit significand (leading
    // bit at sb−1), adjusting the exponent — so the integer sqrt always gets full
    // precision regardless of how many leading zeros a subnormal input had.
    let (sig_n, e_n) = {
        let lz = count_leading_zeros(arena, sig_w)?;
        let wsb = arena.bv_const(w, u128::from(w - sb))?;
        let norm = arena.bv_sub(lz, wsb)?;
        let sig_n = arena.bv_shl(sig_w, norm)?;
        let e_n = arena.bv_sub(e, norm)?;
        (sig_n, e_n)
    };

    // Make the exponent even: if odd, double the significand and decrement E.
    let e_lsb = arena.extract(0, 0, e_n)?;
    let one1 = arena.bv_const(1, 1)?;
    let e_odd = arena.eq(e_lsb, one1)?;
    let sig2 = {
        let doubled = arena.bv_shl(sig_n, one_w)?;
        arena.ite(e_odd, doubled, sig_n)?
    };
    let e2 = {
        let dec = arena.bv_sub(e_n, one_w)?;
        arena.ite(e_odd, dec, e_n)?
    };

    // N = sig2 << (2·shift); isqrt(N) ≈ sqrt(sig2) · 2^shift.
    let two_shift = arena.bv_const(w, u128::from(2 * shift))?;
    let n = arena.bv_shl(sig2, two_shift)?;
    let (root, rem) = isqrt(arena, n)?;
    let sticky = {
        let z = arena.eq(rem, zero_w)?;
        arena.not(z)?
    };
    let sticky_bit = arena.ite(sticky, one_w, zero_w)?;
    let m = arena.bv_or(root, sticky_bit)?;

    // result exponent of m's LSB = E2/2 − shift.
    let e_half = arena.bv_ashr(e2, one_w)?; // E2 even → exact /2
    let shift_c = sconst(arena, w, i64::from(shift))?;
    let e_res = arena.bv_sub(e_half, shift_c)?;

    let plus = arena.bool_const(false);
    let finite = pack_value(arena, eb, sb, plus, m, e_res, mode)?;

    // Special cases.
    let nan_x = is_nan(arena, fmt, x)?;
    let neg_x = is_negative(arena, fmt, x)?; // negative finite or −∞ (excludes −0, NaN)
    let zero_x = is_zero(arena, fmt, x)?;
    let inf_x = is_infinite(arena, fmt, x)?;
    let nan_flag = arena.or(nan_x, neg_x)?; // sqrt(NaN) and sqrt(negative) → NaN

    let exp_ones = arena.bv_const(total, ((1u128 << eb) - 1) << (sb - 1))?;
    let qnan = {
        let q = arena.bv_const(total, 1u128 << (sb - 2))?;
        arena.bv_or(exp_ones, q)?
    };
    // sqrt(+∞) = +∞ (the negative-∞ case is already NaN via `neg_x`).
    let pos_inf = exp_ones;

    let if_inf = arena.ite(inf_x, pos_inf, finite)?;
    let if_zero = arena.ite(zero_x, x, if_inf)?; // ±0 preserved
    arena.ite(nan_flag, qnan, if_zero)
}

/// Symbolic floating-point **format conversion** `(_ to_fp)` from one float
/// format to another (e.g. `f32 → f64` widening or `f64 → f32` narrowing) under
/// `mode`. Unpacks `x` in `src` and repacks the same value into `dst` via
/// [`pack_value`] (widening is exact; narrowing rounds), with NaN/∞/±0 mapped to
/// the destination format. Pure bit-vector formula; solves and replays on the
/// existing path. Validated against native `f32`/`f64` casts.
///
/// # Errors
///
/// Returns [`IrError::InvalidWidth`] if the working width exceeds
/// [`MAX_BV_WIDTH`], [`IrError::SortMismatch`] for a mis-sized operand, or
/// [`IrError`] from the builders.
#[allow(clippy::similar_names, clippy::many_single_char_names)]
pub fn to_fp(
    arena: &mut TermArena,
    src: FloatFormat,
    dst: FloatFormat,
    mode: RoundingMode,
    x: TermId,
) -> Result<TermId, IrError> {
    src.check(arena, x)?;
    let w = src.sig_bits.max(dst.sig_bits) + 4;
    if w > MAX_BV_WIDTH {
        return Err(IrError::InvalidWidth(w));
    }
    let (deb, dsb) = (dst.exp_bits, dst.sig_bits);
    let dtotal = dst.width();

    let one1 = arena.bv_const(1, 1)?;
    let (sx, sig_w, e) = unpack_operand(arena, src, w, x)?;
    let sign = arena.eq(sx, one1)?;
    let finite = pack_value(arena, deb, dsb, sign, sig_w, e, mode)?;

    // Specials map to the destination format.
    let nan = is_nan(arena, src, x)?;
    let inf = is_infinite(arena, src, x)?;
    let zero = is_zero(arena, src, x)?;
    let sign_total = {
        let on = arena.bv_const(dtotal, 1u128 << (dtotal - 1))?;
        let off = arena.bv_const(dtotal, 0)?;
        arena.ite(sign, on, off)?
    };
    let exp_ones = arena.bv_const(dtotal, ((1u128 << deb) - 1) << (dsb - 1))?;
    let qnan = {
        let q = arena.bv_const(dtotal, 1u128 << (dsb - 2))?;
        arena.bv_or(exp_ones, q)?
    };
    let inf_total = arena.bv_or(sign_total, exp_ones)?;

    let if_zero = arena.ite(zero, sign_total, finite)?;
    let if_inf = arena.ite(inf, inf_total, if_zero)?;
    arena.ite(nan, qnan, if_inf)
}

/// Symbolic `fp.div` (round-nearest-ties-to-even): the IEEE 754 division
/// bit-blaster. Computes the quotient of the significands to `sb + 3` fractional
/// bits via `bv_udiv` (with the `bv_urem` remainder folded into a sticky bit),
/// subtracts exponents, rounds via [`pack_value`], and muxes the special cases
/// (NaN for `0/0` and `∞/∞`, `∞` for `x/0` and `∞/finite`, `0` for `finite/∞`).
/// A pure bit-vector formula; solves and replays on the existing path.
///
/// Works for **F16/F32/F64** (the `2·sb + 5`-bit intermediate fits 128 bits).
/// Validated, not proven: differentially validated against native `f32`/`f64`
/// division.
///
/// # Errors
///
/// Returns [`IrError::InvalidWidth`] if the format is too wide,
/// [`IrError::SortMismatch`] for a mis-sized operand, or [`IrError`] from builders.
#[allow(clippy::similar_names, clippy::many_single_char_names)]
pub fn div(arena: &mut TermArena, fmt: FloatFormat, a: TermId, b: TermId, mode: RoundingMode) -> Result<TermId, IrError> {
    fmt.check(arena, a)?;
    fmt.check(arena, b)?;
    let (eb, sb) = (fmt.exp_bits, fmt.sig_bits);
    let total = fmt.width();
    let w = 2 * sb + 5;
    if w > MAX_BV_WIDTH {
        return Err(IrError::InvalidWidth(w));
    }
    let frac = sb + 3; // quotient fractional bits

    let one1 = arena.bv_const(1, 1)?;
    let (sa, sig_a, e_a) = unpack_operand(arena, fmt, w, a)?;
    let (sbit, sig_b, e_b) = unpack_operand(arena, fmt, w, b)?;

    // quotient = (sig_a << frac) / sig_b, with the remainder as a sticky bit.
    let frac_c = arena.bv_const(w, u128::from(frac))?;
    let numer = arena.bv_shl(sig_a, frac_c)?;
    let quot = arena.bv_udiv(numer, sig_b)?;
    let rem = arena.bv_urem(numer, sig_b)?;
    let one_w = arena.bv_const(w, 1)?;
    let zero_w = arena.bv_const(w, 0)?;
    let sticky = {
        let is_zero = arena.eq(rem, zero_w)?;
        arena.not(is_zero)?
    };
    let sticky_bit = arena.ite(sticky, one_w, zero_w)?;
    let quot_s = arena.bv_or(quot, sticky_bit)?;

    // exponent of the quotient's LSB = E_a − E_b − frac.
    let e_q = {
        let d = arena.bv_sub(e_a, e_b)?;
        let fc = sconst(arena, w, i64::from(frac))?;
        arena.bv_sub(d, fc)?
    };
    let sign_xor_bit = arena.bv_xor(sa, sbit)?;
    let sign_xor = arena.eq(sign_xor_bit, one1)?;
    let finite = pack_value(arena, eb, sb, sign_xor, quot_s, e_q, mode)?;

    // Special cases.
    let na = is_nan(arena, fmt, a)?;
    let nb = is_nan(arena, fmt, b)?;
    let ia = is_infinite(arena, fmt, a)?;
    let ib = is_infinite(arena, fmt, b)?;
    let za = is_zero(arena, fmt, a)?;
    let zb = is_zero(arena, fmt, b)?;
    let nan_flag = {
        let zz = arena.and(za, zb)?; // 0/0
        let ii = arena.and(ia, ib)?; // ∞/∞
        let t = arena.or(na, nb)?;
        let t = arena.or(t, zz)?;
        arena.or(t, ii)?
    };
    // After NaN excluded: ∞ if a is ∞, or b is 0; 0 if b is ∞, or a is 0.
    let inf_flag = arena.or(ia, zb)?;
    let zero_flag = arena.or(ib, za)?;

    let sign_total = {
        let on = arena.bv_const(total, 1u128 << (total - 1))?;
        let off = arena.bv_const(total, 0)?;
        arena.ite(sign_xor, on, off)?
    };
    let exp_ones = arena.bv_const(total, ((1u128 << eb) - 1) << (sb - 1))?;
    let qnan = {
        let q = arena.bv_const(total, 1u128 << (sb - 2))?;
        arena.bv_or(exp_ones, q)?
    };
    let inf_total = arena.bv_or(sign_total, exp_ones)?;

    let if_zero = arena.ite(zero_flag, sign_total, finite)?;
    let if_inf = arena.ite(inf_flag, inf_total, if_zero)?;
    arena.ite(nan_flag, qnan, if_inf)
}

/// Symbolic `fp.add` (round-nearest-ties-to-even): the IEEE 754 addition
/// bit-blaster via **bounded alignment with a sticky bit**. The larger-exponent
/// operand is placed with `sb + 2` guard bits below it; the smaller is shifted
/// right by the exponent difference, with the bits shifted past the window OR'd
/// into the bottom (sticky). Magnitudes are added (same sign) or subtracted
/// (opposite sign, with a magnitude compare for the equal-exponent case), then
/// rounded by [`pack_value`], and NaN / `∞ + −∞` / `∞` / signed-zero cases are
/// muxed. A pure bit-vector formula; solves and replays on the existing path.
///
/// Borrow-clean: the sticky is nonzero only when `exp_diff > sb + 2`, where the
/// result has no catastrophic cancellation (its leading bit is the larger
/// operand's, ±1), so the sticky always lands strictly below the round position
/// and never corrupts a guard/round bit. The `2·sb + 5`-bit intermediate fits
/// **F16/F32/F64** in 128 bits ([`MAX_BV_WIDTH`]).
///
/// This is a validated — not formally proven — bit-blaster: differentially
/// validated against native `f32` and `f64` addition in tests.
///
/// # Errors
///
/// Returns [`IrError::InvalidWidth`] if the format's intermediate width exceeds
/// [`MAX_BV_WIDTH`], [`IrError::SortMismatch`] for a mis-sized operand, or
/// [`IrError`] from the builders.
#[allow(clippy::similar_names, clippy::many_single_char_names)]
pub fn add(arena: &mut TermArena, fmt: FloatFormat, a: TermId, b: TermId, mode: RoundingMode) -> Result<TermId, IrError> {
    fmt.check(arena, a)?;
    fmt.check(arena, b)?;
    let (eb, sb) = (fmt.exp_bits, fmt.sig_bits);
    let total = fmt.width();
    let w = 2 * sb + 5;
    if w > MAX_BV_WIDTH {
        return Err(IrError::InvalidWidth(w));
    }
    let guard = sb + 2;

    let one1 = arena.bv_const(1, 1)?;
    let (sa, sig_a, e_a) = unpack_operand(arena, fmt, w, a)?;
    let (sbit, sig_b, e_b) = unpack_operand(arena, fmt, w, b)?;

    // Pick the larger-exponent operand ("big"); the other ("small") is aligned
    // down to big's scale (E_big − guard) with a sticky bit.
    let a_ge = arena.bv_sge(e_a, e_b)?;
    let e_big = arena.ite(a_ge, e_a, e_b)?;
    let sig_big = arena.ite(a_ge, sig_a, sig_b)?;
    let sig_small = arena.ite(a_ge, sig_b, sig_a)?;
    let sign_big = arena.ite(a_ge, sa, sbit)?;
    let sign_small = arena.ite(a_ge, sbit, sa)?;
    let e_small = arena.ite(a_ge, e_b, e_a)?;
    let exp_diff = arena.bv_sub(e_big, e_small)?;

    let guard_c = arena.bv_const(w, u128::from(guard))?;
    let big_ext = arena.bv_shl(sig_big, guard_c)?;
    let small_placed = arena.bv_shl(sig_small, guard_c)?;
    let small_ext = arena.bv_lshr(small_placed, exp_diff)?;
    // sticky = any bit of small_placed shifted out by `exp_diff` is set.
    let one_w = arena.bv_const(w, 1)?;
    let zero_w = arena.bv_const(w, 0)?;
    let sticky = {
        let pow = arena.bv_shl(one_w, exp_diff)?;
        let mask = arena.bv_sub(pow, one_w)?;
        let lost = arena.bv_and(small_placed, mask)?;
        let is_zero = arena.eq(lost, zero_w)?;
        arena.not(is_zero)?
    };
    let sticky_bit = arena.ite(sticky, one_w, zero_w)?;
    let small_ext_s = arena.bv_or(small_ext, sticky_bit)?;

    let same_sign = arena.eq(sign_big, sign_small)?;
    let add_mag = arena.bv_add(big_ext, small_ext_s)?;
    let ge = arena.bv_uge(big_ext, small_ext_s)?;
    let sub_ab = arena.bv_sub(big_ext, small_ext_s)?;
    let sub_ba = arena.bv_sub(small_ext_s, big_ext)?;
    let sub_mag = arena.ite(ge, sub_ab, sub_ba)?;
    let sub_sign = arena.ite(ge, sign_big, sign_small)?;
    let result_mag = arena.ite(same_sign, add_mag, sub_mag)?;
    let result_sign_bit = arena.ite(same_sign, sign_big, sub_sign)?;
    let result_sign = arena.eq(result_sign_bit, one1)?;
    let e_c = arena.bv_sub(e_big, guard_c)?;
    let finite = pack_value(arena, eb, sb, result_sign, result_mag, e_c, mode)?;

    // Special-case flags.
    let na = is_nan(arena, fmt, a)?;
    let nb = is_nan(arena, fmt, b)?;
    let ia = is_infinite(arena, fmt, a)?;
    let ib = is_infinite(arena, fmt, b)?;
    let za = is_zero(arena, fmt, a)?;
    let zb = is_zero(arena, fmt, b)?;
    let signs_differ = {
        let s = arena.eq(sa, sbit)?;
        arena.not(s)?
    };
    let inf_minus_inf = {
        let both = arena.and(ia, ib)?;
        arena.and(both, signs_differ)?
    };
    let nan_flag = {
        let t = arena.or(na, nb)?;
        arena.or(t, inf_minus_inf)?
    };
    let inf_flag = arena.or(ia, ib)?;
    let inf_sign = arena.ite(ia, sa, sbit)?; // sign of the (an) infinity
    let both_zero = arena.and(za, zb)?;
    let mag_zero = arena.eq(result_mag, zero_w)?;

    // Field constants.
    let pos_zero = arena.bv_const(total, 0)?;
    let neg_zero = arena.bv_const(total, 1u128 << (total - 1))?;
    let exp_ones = arena.bv_const(total, ((1u128 << eb) - 1) << (sb - 1))?;
    let qnan = {
        let q = arena.bv_const(total, 1u128 << (sb - 2))?;
        arena.bv_or(exp_ones, q)?
    };
    let inf_total = {
        let inf_is_neg = arena.eq(inf_sign, one1)?;
        let neg_inf = arena.bv_or(neg_zero, exp_ones)?;
        arena.ite(inf_is_neg, neg_inf, exp_ones)?
    };
    // Both zero: −0 only if both are −0; else +0. (RNE: x + −x = +0 too.)
    let both_neg_zero = {
        let na_ = arena.eq(sa, one1)?;
        let nb_ = arena.eq(sbit, one1)?;
        arena.and(na_, nb_)?
    };
    let bothzero_total = arena.ite(both_neg_zero, neg_zero, pos_zero)?;

    // Mux: NaN, ∞, both-zero, exact-cancellation→+0, else rounded finite.
    let r0 = arena.ite(mag_zero, pos_zero, finite)?;
    let r1 = arena.ite(both_zero, bothzero_total, r0)?;
    let r2 = arena.ite(inf_flag, inf_total, r1)?;
    arena.ite(nan_flag, qnan, r2)
}

/// Symbolic `fp.fma` — fused multiply-add `a·b + c` with a **single**
/// round-nearest-style rounding (no intermediate rounding of the product). The
/// exact product (`2·sb`-bit significand at `e_a + e_b`) is aligned with `c` and
/// summed exactly, then [`pack_value`] rounds once. The intermediate width is
/// `3·sb + 5`, so **F16 and F32** fit the 128-bit cap (F64 needs 164 bits →
/// `InvalidWidth`).
///
/// Special cases per IEEE: NaN if any operand is NaN, if `a·b` is `0·∞`, or if
/// `a·b` and `c` are infinities of opposite sign; otherwise the infinity of an
/// infinite product or addend. Validated against native `f32::mul_add` (the
/// correctly-rounded fma) over a wide sweep.
///
/// # Errors
///
/// Returns [`IrError::InvalidWidth`] if `3·sb + 5 > 128`, [`IrError::SortMismatch`]
/// for a mis-sized operand, or [`IrError`] from the builders.
#[allow(clippy::similar_names, clippy::many_single_char_names, clippy::too_many_lines)]
pub fn fma(
    arena: &mut TermArena,
    fmt: FloatFormat,
    a: TermId,
    b: TermId,
    c: TermId,
    mode: RoundingMode,
) -> Result<TermId, IrError> {
    fmt.check(arena, a)?;
    fmt.check(arena, b)?;
    fmt.check(arena, c)?;
    let (eb, sb) = (fmt.exp_bits, fmt.sig_bits);
    let total = fmt.width();
    let w = 3 * sb + 5;
    if w > MAX_BV_WIDTH {
        return Err(IrError::InvalidWidth(w));
    }
    let guard = sb + 2;
    let one1 = arena.bv_const(1, 1)?;
    let (sa, sig_a, e_a) = unpack_operand(arena, fmt, w, a)?;
    let (sbb, sig_b, e_b) = unpack_operand(arena, fmt, w, b)?;
    let (sc, sig_c, e_c) = unpack_operand(arena, fmt, w, c)?;

    // Exact product (no rounding): significand `sig_a·sig_b` at `e_a + e_b`.
    let sig_p = arena.bv_mul(sig_a, sig_b)?;
    let e_p = arena.bv_add(e_a, e_b)?;
    let sp_bit = arena.bv_xor(sa, sbb)?;

    // Align the product and `c` (bigger exponent is "big"); same scheme as `add`.
    let p_ge = arena.bv_sge(e_p, e_c)?;
    let e_big = arena.ite(p_ge, e_p, e_c)?;
    let sig_big = arena.ite(p_ge, sig_p, sig_c)?;
    let sig_small = arena.ite(p_ge, sig_c, sig_p)?;
    let sign_big = arena.ite(p_ge, sp_bit, sc)?;
    let sign_small = arena.ite(p_ge, sc, sp_bit)?;
    let e_small = arena.ite(p_ge, e_c, e_p)?;
    let exp_diff = arena.bv_sub(e_big, e_small)?;

    let guard_c = arena.bv_const(w, u128::from(guard))?;
    let big_ext = arena.bv_shl(sig_big, guard_c)?;
    let small_placed = arena.bv_shl(sig_small, guard_c)?;
    let small_ext = arena.bv_lshr(small_placed, exp_diff)?;
    let one_w = arena.bv_const(w, 1)?;
    let zero_w = arena.bv_const(w, 0)?;
    let sticky = {
        let pow = arena.bv_shl(one_w, exp_diff)?;
        let mask = arena.bv_sub(pow, one_w)?;
        let lost = arena.bv_and(small_placed, mask)?;
        let is_zero = arena.eq(lost, zero_w)?;
        arena.not(is_zero)?
    };
    let sticky_bit = arena.ite(sticky, one_w, zero_w)?;
    let small_ext_s = arena.bv_or(small_ext, sticky_bit)?;

    let same_sign = arena.eq(sign_big, sign_small)?;
    let add_mag = arena.bv_add(big_ext, small_ext_s)?;
    let ge = arena.bv_uge(big_ext, small_ext_s)?;
    let sub_ab = arena.bv_sub(big_ext, small_ext_s)?;
    let sub_ba = arena.bv_sub(small_ext_s, big_ext)?;
    let sub_mag = arena.ite(ge, sub_ab, sub_ba)?;
    let sub_sign = arena.ite(ge, sign_big, sign_small)?;
    let result_mag = arena.ite(same_sign, add_mag, sub_mag)?;
    let result_sign_bit = arena.ite(same_sign, sign_big, sub_sign)?;
    let result_sign = arena.eq(result_sign_bit, one1)?;
    let e_result = arena.bv_sub(e_big, guard_c)?;
    let finite = pack_value(arena, eb, sb, result_sign, result_mag, e_result, mode)?;

    // Special-case flags.
    let na = is_nan(arena, fmt, a)?;
    let nb = is_nan(arena, fmt, b)?;
    let nc = is_nan(arena, fmt, c)?;
    let ia = is_infinite(arena, fmt, a)?;
    let ib = is_infinite(arena, fmt, b)?;
    let ic = is_infinite(arena, fmt, c)?;
    let za = is_zero(arena, fmt, a)?;
    let zb = is_zero(arena, fmt, b)?;
    let zc = is_zero(arena, fmt, c)?;

    // product NaN = 0·∞; product ∞ otherwise when a or b is ∞.
    let prod_nan = {
        let l = arena.and(ia, zb)?;
        let r = arena.and(ib, za)?;
        arena.or(l, r)?
    };
    let prod_inf = {
        let l = {
            let nzb = arena.not(zb)?;
            arena.and(ia, nzb)?
        };
        let r = {
            let nza = arena.not(za)?;
            arena.and(ib, nza)?
        };
        arena.or(l, r)?
    };
    // ∞ − ∞ between the product and c.
    let prod_c_inf_clash = {
        let both = arena.and(prod_inf, ic)?;
        let signs_differ = {
            let s = arena.eq(sp_bit, sc)?;
            arena.not(s)?
        };
        arena.and(both, signs_differ)?
    };
    let nan_flag = {
        let a1 = arena.or(na, nb)?;
        let a2 = arena.or(a1, nc)?;
        let a3 = arena.or(a2, prod_nan)?;
        arena.or(a3, prod_c_inf_clash)?
    };
    let inf_flag = arena.or(prod_inf, ic)?;
    // Sign of the infinite result: the product's if it is ∞, else c's.
    let inf_sign_bit = arena.ite(prod_inf, sp_bit, sc)?;

    // Field constants.
    let pos_zero = arena.bv_const(total, 0)?;
    let neg_zero = arena.bv_const(total, 1u128 << (total - 1))?;
    let exp_ones = arena.bv_const(total, ((1u128 << eb) - 1) << (sb - 1))?;
    let qnan = {
        let q = arena.bv_const(total, 1u128 << (sb - 2))?;
        arena.bv_or(exp_ones, q)?
    };
    let inf_total = {
        let inf_is_neg = arena.eq(inf_sign_bit, one1)?;
        let neg_inf = arena.bv_or(neg_zero, exp_ones)?;
        arena.ite(inf_is_neg, neg_inf, exp_ones)?
    };
    let mag_zero = arena.eq(result_mag, zero_w)?;

    // Zero-sign rule (RNE): the sum of two zeros is −0 only if *both* the product
    // and `c` are −0; any other zero result (incl. exact cancellation) is +0.
    let prod_zero = arena.or(za, zb)?; // a·b is zero iff a or b is zero
    let both_zero = arena.and(prod_zero, zc)?;
    let prod_neg_zero = {
        let neg = arena.eq(sp_bit, one1)?;
        arena.and(prod_zero, neg)?
    };
    let c_neg_zero = {
        let neg = arena.eq(sc, one1)?;
        arena.and(zc, neg)?
    };
    let both_neg_zero = arena.and(prod_neg_zero, c_neg_zero)?;
    let bothzero_total = arena.ite(both_neg_zero, neg_zero, pos_zero)?;

    // Mux: NaN, ∞, both-zero, exact-cancellation → +0, else rounded finite.
    let r0 = arena.ite(mag_zero, pos_zero, finite)?;
    let r1 = arena.ite(both_zero, bothzero_total, r0)?;
    let r2 = arena.ite(inf_flag, inf_total, r1)?;
    arena.ite(nan_flag, qnan, r2)
}

// --- constant folding (round-nearest-even arithmetic) -------------------------
//
// Rounded FP arithmetic (`add`/`sub`/`mul`/`div`/`sqrt`) is, for *constant*
// F32/F64 operands, computed by delegating to the platform's native IEEE 754
// arithmetic — which is round-nearest-even and correct — so these folds are
// sound by construction and need no hand-written rounding. They also serve as
// the differential oracle for a future *symbolic* FP bit-blaster (validate the
// blaster against native arithmetic before trusting it for solving).
//
// Each returns `Ok(Some(result))` when both operands are bit-vector constants in
// F32/F64, and `Ok(None)` otherwise (symbolic operands, other formats, or other
// rounding modes are not folded here — that is the next, separately-validated
// unit).

/// Constant-folds `fp.add` (round-nearest-even) over F32/F64 constants.
pub fn add_rne(
    arena: &mut TermArena,
    fmt: FloatFormat,
    x: TermId,
    y: TermId,
) -> Result<Option<TermId>, IrError> {
    fold_bin(arena, fmt, x, y, |a, b| a + b, |a, b| a + b)
}

/// Constant-folds `fp.sub` (round-nearest-even) over F32/F64 constants.
pub fn sub_rne(
    arena: &mut TermArena,
    fmt: FloatFormat,
    x: TermId,
    y: TermId,
) -> Result<Option<TermId>, IrError> {
    fold_bin(arena, fmt, x, y, |a, b| a - b, |a, b| a - b)
}

/// Constant-folds `fp.mul` (round-nearest-even) over F32/F64 constants.
pub fn mul_rne(
    arena: &mut TermArena,
    fmt: FloatFormat,
    x: TermId,
    y: TermId,
) -> Result<Option<TermId>, IrError> {
    fold_bin(arena, fmt, x, y, |a, b| a * b, |a, b| a * b)
}

/// Constant-folds `fp.div` (round-nearest-even) over F32/F64 constants.
pub fn div_rne(
    arena: &mut TermArena,
    fmt: FloatFormat,
    x: TermId,
    y: TermId,
) -> Result<Option<TermId>, IrError> {
    fold_bin(arena, fmt, x, y, |a, b| a / b, |a, b| a / b)
}

/// Constant-folds `fp.sqrt` (round-nearest-even) over an F32/F64 constant.
pub fn sqrt_rne(
    arena: &mut TermArena,
    fmt: FloatFormat,
    x: TermId,
) -> Result<Option<TermId>, IrError> {
    let Some(xv) = const_bits(arena, x) else {
        return Ok(None);
    };
    let bits = if fmt == FloatFormat::F32 {
        u128::from(f32::from_bits(low32(xv)).sqrt().to_bits())
    } else if fmt == FloatFormat::F64 {
        u128::from(f64::from_bits(low64(xv)).sqrt().to_bits())
    } else {
        return Ok(None);
    };
    Ok(Some(arena.bv_const(fmt.width(), bits)?))
}

/// Constant-folds `fp.fma` (fused multiply-add, `x*y + z` with a *single*
/// round-nearest-even rounding) over F32/F64 constants, via native `mul_add`.
pub fn fma_rne(
    arena: &mut TermArena,
    fmt: FloatFormat,
    x: TermId,
    y: TermId,
    z: TermId,
) -> Result<Option<TermId>, IrError> {
    let (Some(xv), Some(yv), Some(zv)) =
        (const_bits(arena, x), const_bits(arena, y), const_bits(arena, z))
    else {
        return Ok(None);
    };
    let bits = if fmt == FloatFormat::F32 {
        let r = f32::from_bits(low32(xv)).mul_add(f32::from_bits(low32(yv)), f32::from_bits(low32(zv)));
        u128::from(r.to_bits())
    } else if fmt == FloatFormat::F64 {
        let r = f64::from_bits(low64(xv)).mul_add(f64::from_bits(low64(yv)), f64::from_bits(low64(zv)));
        u128::from(r.to_bits())
    } else {
        return Ok(None);
    };
    Ok(Some(arena.bv_const(fmt.width(), bits)?))
}

/// The IEEE 754 / SMT-LIB `fp.rem(x, y)` remainder: `x − y·n` where `n` is the
/// integer quotient `x/y` rounded to nearest, ties to even. The result is
/// *exact* (always representable, no rounding mode), with `|r| ≤ |y|/2`.
///
/// Special cases follow IEEE: `NaN` if `x` is infinite, `y` is zero, or either
/// is `NaN`; `x` itself if `y` is infinite (and `x` finite); `±0` (sign of `x`)
/// if `x` is zero. Computed via `fmod` (exact) then a nearest-adjust that
/// resolves the half-integer tie by the parity of the truncated quotient.
#[allow(clippy::float_cmp)] // exact half-integer tie detection is intentional
fn ieee_remainder(x: f64, y: f64) -> f64 {
    if x.is_nan() || y.is_nan() || x.is_infinite() || y == 0.0 {
        return f64::NAN;
    }
    if y.is_infinite() {
        return x; // x is finite
    }
    if x == 0.0 {
        return x; // preserve the sign of zero
    }
    let ay = y.abs();
    let mut r = x % ay; // fmod: exact, |r| < ay, sign of x
    let half = ay * 0.5; // exact (×0.5)
    let ar = r.abs();
    if ar > half {
        r -= r.signum() * ay;
    } else if ar == half {
        // Tie: x/y is a half-integer; n is the even neighbour of the truncated
        // quotient nA. nA is even iff |x mod 2·ay| < ay (so x sits in the lower
        // half of a 2·ay-wide band). When 2·ay overflows to ∞, |x| < 2·ay forces
        // nA ∈ {0} at a tie, i.e. even — and x % ∞ = x gives |x| = ay/2 < ay,
        // which the same test reports as even. So no overflow guard is needed.
        let r2 = x % (2.0 * ay);
        if r2.abs() >= ay {
            r -= r.signum() * ay; // nA odd → step to the even neighbour
        }
    }
    r
}

/// Constant-folds `fp.rem` (IEEE remainder, exact — no rounding mode) over
/// constants of any IEEE format (`F16`/`F32`/`F64`/`BF16`/`TF32`/`FP8_E5M2`).
/// The remainder of two format values is itself exactly representable in the
/// format, so re-encoding is exact. Returns `Ok(None)` for symbolic operands or
/// the non-IEEE formats (`FP8_E4M3`/`FP4_E2M1`).
///
/// # Errors
///
/// Returns [`IrError`] from the constant builder.
pub fn rem(
    arena: &mut TermArena,
    fmt: FloatFormat,
    x: TermId,
    y: TermId,
) -> Result<Option<TermId>, IrError> {
    let (Some(xv), Some(yv)) = (const_bits(arena, x), const_bits(arena, y)) else {
        return Ok(None);
    };
    let bits = if fmt == FloatFormat::F32 {
        // f32 → f64 is exact; the exact remainder of two f32 values is itself an
        // f32 value, so narrowing back is exact too.
        let r = ieee_remainder(f64::from(f32::from_bits(low32(xv))), f64::from(f32::from_bits(low32(yv))));
        #[allow(clippy::cast_possible_truncation)] // r is exactly an f32 value
        u128::from((r as f32).to_bits())
    } else if fmt == FloatFormat::F64 {
        let r = ieee_remainder(f64::from_bits(low64(xv)), f64::from_bits(low64(yv)));
        u128::from(r.to_bits())
    } else if fmt.is_ieee() {
        // Other IEEE formats (incl. the GPU/ML precisions): decode exactly to
        // f64, take the remainder, and round back (exact, since the result is a
        // format value). round_to_format handles NaN/∞/±0 with the correct sign.
        let r = ieee_remainder(fmt.decode_ieee_f64(xv), fmt.decode_ieee_f64(yv));
        round_to_format(fmt.exp_bits, fmt.sig_bits, r, RoundingMode::NearestEven)
    } else {
        return Ok(None);
    };
    Ok(Some(arena.bv_const(fmt.width(), bits)?))
}

/// Symbolic `fp.rem` (IEEE remainder, exact) bit-blaster for **small-exponent**
/// IEEE formats (`F16`, `FP8_E5M2`). Both magnitudes are scaled to a common
/// minimum exponent so they become integers, the truncated remainder and
/// quotient come from the sound `bvurem`/`bvudiv`, and a nearest-adjust (compare
/// `2·r₀` to `|y|`, ties resolved by the parity of the quotient) selects the
/// final magnitude and sign; the exact result is packed via [`pack_value`].
///
/// The scaled integers need `sig_bits + (2^exp_bits − 3) + 2` bits, which only
/// fits the 128-bit cap for `exp_bits ≤ 5`. Wide-exponent formats
/// (`F32`/`F64`/`BF16`/`TF32`) return [`IrError::InvalidWidth`] — their symbolic
/// remainder needs an iterative encoding (future work); the constant fold
/// [`rem`] still covers them when both operands are known.
///
/// Validated against the trusted constant fold [`rem`] over F16.
///
/// # Errors
///
/// Returns [`IrError::Unsupported`] for a non-IEEE format,
/// [`IrError::InvalidWidth`] for a wide-exponent format, [`IrError::SortMismatch`]
/// for a mis-sized operand, or [`IrError`] from builders.
#[allow(clippy::similar_names, clippy::many_single_char_names, clippy::too_many_lines)]
pub fn rem_sym(arena: &mut TermArena, fmt: FloatFormat, x: TermId, y: TermId) -> Result<TermId, IrError> {
    fmt.check(arena, x)?;
    fmt.check(arena, y)?;
    if !fmt.is_ieee() {
        return Err(IrError::Unsupported("fp.rem symbolic: non-IEEE format"));
    }
    let (eb, sb) = (fmt.exp_bits, fmt.sig_bits);
    let total = fmt.width();
    let e_span = (1u32 << eb) - 3; // max LSB-exponent minus min LSB-exponent
    let w = sb + e_span + 2;
    if w > MAX_BV_WIDTH {
        // The scaled-integer encoding overflows 128 bits (wide exponent). Fall
        // back to the iterative shift-subtract reduction, which uses a small
        // (`sb`-wide) register but `e_span` data-independent steps. Capped at
        // `e_span ≤ 256` (exp_bits ≤ 8: F32/BF16/TF32) to keep the formula
        // bounded; F64 (e_span 2045) is out of range.
        if e_span <= 256 {
            return rem_iterative(arena, fmt, x, y);
        }
        return Err(IrError::InvalidWidth(w));
    }
    let bias = (1i64 << (eb - 1)) - 1;
    let e_min = 1 - bias - i64::from(sb - 1);

    let one1 = arena.bv_const(1, 1)?;
    let (sx, mx, ex) = unpack_operand(arena, fmt, w, x)?;
    let (_sy, my, ey) = unpack_operand(arena, fmt, w, y)?;

    // Scale both magnitudes to integers at the common scale 2^e_min.
    let emin_c = sconst(arena, w, e_min)?;
    let shx = arena.bv_sub(ex, emin_c)?;
    let shy = arena.bv_sub(ey, emin_c)?;
    let xi = arena.bv_shl(mx, shx)?;
    let yi = arena.bv_shl(my, shy)?;

    // Truncated remainder r0 and quotient parity (bvurem/bvudiv are sound;
    // division by zero is masked out by the y-zero → NaN special case below).
    let r0 = arena.bv_urem(xi, yi)?;
    let q0 = arena.bv_udiv(xi, yi)?;
    let q0_lsb = arena.extract(0, 0, q0)?;
    let q0_odd = arena.eq(q0_lsb, one1)?;

    // Nearest-adjust: compare 2·r0 to |y|; on a tie, adjust iff the quotient is odd.
    let shift1 = arena.bv_const(w, 1)?;
    let two_r0 = arena.bv_shl(r0, shift1)?;
    let gt = arena.bv_ugt(two_r0, yi)?;
    let eq_half = arena.eq(two_r0, yi)?;
    let tie_adj = arena.and(eq_half, q0_odd)?;
    let adjust = arena.or(gt, tie_adj)?;

    // magnitude = adjust ? |y| - r0 : r0 ; sign = sign(x) flipped on adjust.
    let yi_minus_r0 = arena.bv_sub(yi, r0)?;
    let mag = arena.ite(adjust, yi_minus_r0, r0)?;
    let sx_bool = arena.eq(sx, one1)?;
    let nsx = arena.not(sx_bool)?;
    let sign = arena.ite(adjust, nsx, sx_bool)?;

    // Pack the exact remainder magnitude·2^e_min (rounding is identity).
    let finite = pack_value(arena, eb, sb, sign, mag, emin_c, RoundingMode::NearestEven)?;

    // Special cases: NaN if x is NaN/∞ or y is NaN/0; x itself if y is ∞.
    let nx = is_nan(arena, fmt, x)?;
    let ny = is_nan(arena, fmt, y)?;
    let ix = is_infinite(arena, fmt, x)?;
    let iy = is_infinite(arena, fmt, y)?;
    let zy = is_zero(arena, fmt, y)?;
    let nan_flag = {
        let a1 = arena.or(nx, ny)?;
        let a2 = arena.or(a1, ix)?;
        arena.or(a2, zy)?
    };
    let exp_ones = arena.bv_const(total, ((1u128 << eb) - 1) << (sb - 1))?;
    let qnan = {
        let q = arena.bv_const(total, 1u128 << (sb - 2))?;
        arena.bv_or(exp_ones, q)?
    };
    // y infinite (x finite) → x unchanged; else the packed finite remainder.
    let if_yinf = arena.ite(iy, x, finite)?;
    arena.ite(nan_flag, qnan, if_yinf)
}

/// Iterative (shift-subtract) symbolic `fp.rem` for wide-exponent formats
/// (`exp_bits = 8`: F32/BF16/TF32), where the scaled-integer encoding of
/// [`rem_sym`] would exceed 128 bits. The truncated remainder of `|x|` by `|y|`
/// is computed with a small (`sb`-wide) register over `e_span`
/// data-independent reduction steps (so `Mx·2^d mod My` for `Ex ≥ Ey`, else
/// `|x|`), the quotient's parity is tracked for the tie rule, and a nearest
/// adjust selects the final magnitude/sign before [`pack_value`] packs the exact
/// result. Validated against the trusted constant fold [`rem`] over F32.
#[allow(clippy::similar_names, clippy::many_single_char_names, clippy::too_many_lines)]
fn rem_iterative(arena: &mut TermArena, fmt: FloatFormat, x: TermId, y: TermId) -> Result<TermId, IrError> {
    let (eb, sb) = (fmt.exp_bits, fmt.sig_bits);
    let total = fmt.width();
    let e_span = (1u32 << eb) - 3;
    let w = sb + 4;
    let one1 = arena.bv_const(1, 1)?;
    let one_w = arena.bv_const(w, 1)?;
    let (sx, mx, ex) = unpack_operand(arena, fmt, w, x)?;
    let (_sy, my, ey) = unpack_operand(arena, fmt, w, y)?;

    let d = arena.bv_sub(ex, ey)?; // signed; ≥ 0 in the `Ex ≥ Ey` case
    let ex_ge_ey = arena.bv_sge(ex, ey)?;

    // Reduction for `Ex ≥ Ey`: rem = (Mx·2^d) mod My, tracking the quotient LSB.
    // Phase 1 — `rem = Mx mod My` by MSB-first long division over Mx's `sb` bits
    // (a full reduction, correct even when `My` is small, i.e. `y` subnormal).
    let mut rem = arena.bv_const(w, 0)?;
    let mut q_lsb = arena.bool_const(false);
    for k in 0..sb {
        let bit_idx = sb - 1 - k;
        let bit = arena.extract(bit_idx, bit_idx, mx)?;
        let bit_w = arena.zero_ext(w - 1, bit)?;
        let shifted = {
            let r2 = arena.bv_shl(rem, one_w)?;
            arena.bv_add(r2, bit_w)?
        };
        let sub = arena.bv_uge(shifted, my)?;
        let subbed = arena.bv_sub(shifted, my)?;
        rem = arena.ite(sub, subbed, shifted)?;
        q_lsb = sub; // the final iteration leaves the LSB of `Mx div My`
    }
    // Phase 2 — fold in the `d` trailing zero bits: rem = (rem·2^d) mod My.
    for i in 1..=e_span {
        let i_c = sconst(arena, w, i64::from(i))?;
        let active = arena.bv_sle(i_c, d)?; // i ≤ d
        let rem2 = arena.bv_shl(rem, one_w)?;
        let sub = arena.bv_uge(rem2, my)?;
        let rem2_minus = arena.bv_sub(rem2, my)?;
        let rem_next = arena.ite(sub, rem2_minus, rem2)?;
        rem = arena.ite(active, rem_next, rem)?;
        q_lsb = arena.ite(active, sub, q_lsb)?;
    }

    // Nearest-adjust comparison of 2·R0 vs |y|.
    //   Ex ≥ Ey: R0 = rem·2^Ey, |y| = My·2^Ey  ⇒  compare 2·rem vs My.
    //   Ex < Ey: |x| < |y|; an adjust is possible only when Ey = Ex+1 (d = −1),
    //            where 2|x| = Mx·2^Ey ⇒ compare Mx vs My (else strictly less).
    let rem2_final = arena.bv_shl(rem, one_w)?;
    let cmp_a_gt = arena.bv_ugt(rem2_final, my)?;
    let cmp_a_eq = arena.eq(rem2_final, my)?;
    let neg1 = sconst(arena, w, -1)?;
    let d_is_neg1 = arena.eq(d, neg1)?;
    let cmp_b_gt = {
        let g = arena.bv_ugt(mx, my)?;
        arena.and(d_is_neg1, g)?
    };
    let cmp_b_eq = {
        let e = arena.eq(mx, my)?;
        arena.and(d_is_neg1, e)?
    };
    let cmp_gt = arena.ite(ex_ge_ey, cmp_a_gt, cmp_b_gt)?;
    let cmp_eq = arena.ite(ex_ge_ey, cmp_a_eq, cmp_b_eq)?;
    let q0_odd = arena.and(ex_ge_ey, q_lsb)?; // Ex<Ey ⇒ q0 = 0 (even)
    let adjust = {
        let tie = arena.and(cmp_eq, q0_odd)?;
        arena.or(cmp_gt, tie)?
    };

    // Result magnitude/exponent/sign per case.
    let my_minus_rem = arena.bv_sub(my, rem)?;
    let mag_a = arena.ite(adjust, my_minus_rem, rem)?; // scale Ey
    let two_my = arena.bv_shl(my, one_w)?;
    let two_my_minus_mx = arena.bv_sub(two_my, mx)?;
    let mag_b = arena.ite(adjust, two_my_minus_mx, mx)?; // scale Ex
    let mag = arena.ite(ex_ge_ey, mag_a, mag_b)?;
    let mag_exp = arena.ite(ex_ge_ey, ey, ex)?;
    let sx_bool = arena.eq(sx, one1)?;
    let nsx = arena.not(sx_bool)?;
    let sign = arena.ite(adjust, nsx, sx_bool)?;

    let finite = pack_value(arena, eb, sb, sign, mag, mag_exp, RoundingMode::NearestEven)?;

    // Specials: NaN if x NaN/∞ or y NaN/0; x itself if y is ∞.
    let nx = is_nan(arena, fmt, x)?;
    let ny = is_nan(arena, fmt, y)?;
    let ix = is_infinite(arena, fmt, x)?;
    let iy = is_infinite(arena, fmt, y)?;
    let zy = is_zero(arena, fmt, y)?;
    let nan_flag = {
        let a1 = arena.or(nx, ny)?;
        let a2 = arena.or(a1, ix)?;
        arena.or(a2, zy)?
    };
    let exp_ones = arena.bv_const(total, ((1u128 << eb) - 1) << (sb - 1))?;
    let qnan = {
        let q = arena.bv_const(total, 1u128 << (sb - 2))?;
        arena.bv_or(exp_ones, q)?
    };
    let if_yinf = arena.ite(iy, x, finite)?;
    arena.ite(nan_flag, qnan, if_yinf)
}

/// A floating-point rounding mode (SMT-LIB `RoundingMode`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RoundingMode {
    /// Round to nearest, ties to even (`RNE`, the default).
    NearestEven,
    /// Round to nearest, ties away from zero (`RNA`).
    NearestAway,
    /// Round toward zero (`RTZ`).
    TowardZero,
    /// Round toward +∞ (`RTP`).
    TowardPositive,
    /// Round toward −∞ (`RTN`).
    TowardNegative,
}

/// Constant-folds `fp.roundToIntegral` over an F32/F64 constant, per rounding
/// mode, via the native rounding methods (correct by delegation).
pub fn round_to_integral(
    arena: &mut TermArena,
    fmt: FloatFormat,
    mode: RoundingMode,
    x: TermId,
) -> Result<Option<TermId>, IrError> {
    let Some(xv) = const_bits(arena, x) else {
        return Ok(None);
    };
    let bits = if fmt == FloatFormat::F32 {
        let v = f32::from_bits(low32(xv));
        let r = match mode {
            RoundingMode::NearestEven => v.round_ties_even(),
            RoundingMode::NearestAway => v.round(),
            RoundingMode::TowardZero => v.trunc(),
            RoundingMode::TowardPositive => v.ceil(),
            RoundingMode::TowardNegative => v.floor(),
        };
        u128::from(r.to_bits())
    } else if fmt == FloatFormat::F64 {
        let v = f64::from_bits(low64(xv));
        let r = match mode {
            RoundingMode::NearestEven => v.round_ties_even(),
            RoundingMode::NearestAway => v.round(),
            RoundingMode::TowardZero => v.trunc(),
            RoundingMode::TowardPositive => v.ceil(),
            RoundingMode::TowardNegative => v.floor(),
        };
        u128::from(r.to_bits())
    } else if fmt.is_ieee() {
        // Other IEEE formats: decode exactly, round to an integer value (itself a
        // format value), and re-encode exactly via round_to_format (which also
        // handles NaN/∞/±0 with the right sign).
        let v = fmt.decode_ieee_f64(xv);
        let r = round_f64(v, mode);
        round_to_format(fmt.exp_bits, fmt.sig_bits, r, RoundingMode::NearestEven)
    } else {
        return Ok(None);
    };
    Ok(Some(arena.bv_const(fmt.width(), bits)?))
}

/// Symbolic `fp.roundToIntegral`: rounds `x` to an integer-valued float under
/// `mode`. A value with a nonnegative LSB exponent is already integral (returned
/// unchanged); otherwise the fractional bits are rounded off via [`round_variable`]
/// and the integer is repacked via [`pack_value`]. NaN/∞/±0 pass through. Pure
/// bit-vector formula; F16/F32/F64. Validated against native `f32` rounding.
///
/// # Errors
///
/// Returns [`IrError::SortMismatch`] for a mis-sized operand or [`IrError`] from
/// builders.
#[allow(clippy::similar_names, clippy::many_single_char_names)]
pub fn round_to_integral_sym(
    arena: &mut TermArena,
    fmt: FloatFormat,
    mode: RoundingMode,
    x: TermId,
) -> Result<TermId, IrError> {
    fmt.check(arena, x)?;
    let (eb, sb) = (fmt.exp_bits, fmt.sig_bits);
    let total = fmt.width();
    let w = sb + 4;
    if w > MAX_BV_WIDTH {
        return Err(IrError::InvalidWidth(w));
    }
    let one1 = arena.bv_const(1, 1)?;
    let (sx, sig_w, e) = unpack_operand(arena, fmt, w, x)?;
    let sign = arena.eq(sx, one1)?;
    let zero_w = arena.bv_const(w, 0)?;
    let one_w = arena.bv_const(w, 1)?;

    // E ≥ 0 ⇒ already integral; E < 0 ⇒ round off `-E` fractional bits.
    let e_ge0 = arena.bv_sge(e, zero_w)?;
    let neg_e = arena.bv_sub(zero_w, e)?;
    let rounded = round_variable(arena, sig_w, neg_e, mode, sign)?;
    // |value| < 1 (drop ≥ w): nearest/toward-zero → 0; directed → ±1.
    let w_const = arena.bv_const(w, u128::from(w))?;
    let drop_ge_w = arena.bv_uge(neg_e, w_const)?;
    let tiny = {
        let m_nonzero = {
            let z = arena.eq(sig_w, zero_w)?;
            arena.not(z)?
        };
        let up = match mode {
            RoundingMode::TowardPositive => {
                let pos = arena.not(sign)?;
                arena.and(m_nonzero, pos)?
            }
            RoundingMode::TowardNegative => arena.and(m_nonzero, sign)?,
            _ => arena.bool_const(false),
        };
        arena.ite(up, one_w, zero_w)?
    };
    let mag = arena.ite(drop_ge_w, tiny, rounded)?;
    let repacked = pack_value(arena, eb, sb, sign, mag, zero_w, mode)?;
    let finite = arena.ite(e_ge0, x, repacked)?;

    // Specials: NaN → NaN; ∞ and ±0 pass through unchanged.
    let nan = is_nan(arena, fmt, x)?;
    let inf = is_infinite(arena, fmt, x)?;
    let zero = is_zero(arena, fmt, x)?;
    let exp_ones = arena.bv_const(total, ((1u128 << eb) - 1) << (sb - 1))?;
    let qnan = {
        let q = arena.bv_const(total, 1u128 << (sb - 2))?;
        arena.bv_or(exp_ones, q)?
    };
    let if_zero = arena.ite(zero, x, finite)?;
    let if_inf = arena.ite(inf, x, if_zero)?;
    arena.ite(nan, qnan, if_inf)
}

/// Constant-folds `(_ to_fp eb sb)` from an **unsigned** bit-vector constant
/// (`(_ to_fp_unsigned ...)`): the unsigned value, rounded to nearest-even into
/// F32/F64 by native conversion. Always defined.
#[allow(clippy::cast_precision_loss)] // intentional integer→float rounding
pub fn ubv_to_fp(
    arena: &mut TermArena,
    fmt: FloatFormat,
    bv: TermId,
) -> Result<Option<TermId>, IrError> {
    let Some(v) = const_bits(arena, bv) else {
        return Ok(None);
    };
    let bits = if fmt == FloatFormat::F32 {
        u128::from((v as f32).to_bits())
    } else if fmt == FloatFormat::F64 {
        u128::from((v as f64).to_bits())
    } else {
        return Ok(None);
    };
    Ok(Some(arena.bv_const(fmt.width(), bits)?))
}

/// Constant-folds `(_ to_fp eb sb)` from a **signed** (two's-complement)
/// bit-vector constant: the signed value, rounded to nearest-even into F32/F64.
/// Always defined.
#[allow(clippy::cast_precision_loss)] // intentional integer→float rounding
pub fn sbv_to_fp(
    arena: &mut TermArena,
    fmt: FloatFormat,
    bv: TermId,
) -> Result<Option<TermId>, IrError> {
    let Some(v) = const_bits(arena, bv) else {
        return Ok(None);
    };
    let Sort::BitVec(w) = arena.sort_of(bv) else {
        return Ok(None);
    };
    let signed = to_signed(v, w);
    let bits = if fmt == FloatFormat::F32 {
        u128::from((signed as f32).to_bits())
    } else if fmt == FloatFormat::F64 {
        u128::from((signed as f64).to_bits())
    } else {
        return Ok(None);
    };
    Ok(Some(arena.bv_const(fmt.width(), bits)?))
}

/// Symbolic **round-nearest-ties-to-even** of a significand bit-vector: rounds
/// the `n`-bit `sig` to keep its top `keep` bits, dropping the low `drop = n -
/// keep` bits via guard/round/sticky, and returns a `BitVec(keep + 1)` (one
/// extra bit so a round-up carry out of the top is visible to the caller, which
/// adjusts the exponent). This is the rounding sub-circuit of the symbolic FP
/// bit-blaster — the bit-vector transcription of the algorithm validated in
/// [`round_to_format`]; a pure BV formula, so it solves and replays normally.
///
/// # Errors
///
/// Returns [`IrError::SortMismatch`] if `sig` is not a bit-vector, or
/// [`IrError`] from the builders.
pub fn round_significand(
    arena: &mut TermArena,
    sig: TermId,
    keep: u32,
) -> Result<TermId, IrError> {
    let Sort::BitVec(n) = arena.sort_of(sig) else {
        return Err(IrError::SortMismatch {
            expected: "BitVec",
            found: arena.sort_of(sig),
        });
    };
    if keep >= n {
        // No bits dropped: zero-extend to keep+1 (room for the absent carry).
        return arena.zero_ext(keep + 1 - n, sig);
    }
    let drop = n - keep;
    // kept = top `keep` bits, zero-extended to keep+1 for the carry slot.
    let kept = arena.extract(n - 1, drop, sig)?;
    let kept_ext = arena.zero_ext(1, kept)?; // width keep+1
    // guard bit = bit at position drop-1.
    let guard = arena.extract(drop - 1, drop - 1, sig)?;
    let one1 = arena.bv_const(1, 1)?;
    let guard_set = arena.eq(guard, one1)?;
    // sticky = any bit below the guard is set (none if drop == 1).
    let sticky = if drop >= 2 {
        let low = arena.extract(drop - 2, 0, sig)?;
        let zero_low = arena.bv_const(drop - 1, 0)?;
        let is_zero = arena.eq(low, zero_low)?;
        arena.not(is_zero)?
    } else {
        arena.bool_const(false)
    };
    // lsb of the kept significand = bit at position `drop`.
    let lsb = arena.extract(drop, drop, sig)?;
    let lsb_set = arena.eq(lsb, one1)?;
    // round_up = guard AND (sticky OR lsb).
    let sticky_or_lsb = arena.or(sticky, lsb_set)?;
    let round_up = arena.and(guard_set, sticky_or_lsb)?;
    // result = kept_ext + (round_up ? 1 : 0).
    let one_w = arena.bv_const(keep + 1, 1)?;
    let zero_w = arena.bv_const(keep + 1, 0)?;
    let inc = arena.ite(round_up, one_w, zero_w)?;
    arena.bv_add(kept_ext, inc)
}

/// Symbolic **integer square root**: returns `(root, remainder)` for the `W`-bit
/// operand `n` (`W` even), where `root = floor(sqrt(n))` and
/// `remainder = n − root²` (so `remainder != 0` ⟺ `n` is not a perfect square —
/// the sticky bit `fp.sqrt` needs). Built by the classic digit-by-digit
/// (two-bits-at-a-time) algorithm as a pure bit-vector formula.
///
/// # Errors
///
/// Returns [`IrError::SortMismatch`] if `n` is not a bit-vector, or
/// [`IrError::InvalidWidth`] if its width is odd, or [`IrError`] from builders.
#[allow(clippy::similar_names)] // rem4/res4/res2 are the classic algorithm's terms
pub fn isqrt(arena: &mut TermArena, n: TermId) -> Result<(TermId, TermId), IrError> {
    let Sort::BitVec(w) = arena.sort_of(n) else {
        return Err(IrError::SortMismatch {
            expected: "BitVec",
            found: arena.sort_of(n),
        });
    };
    if w % 2 != 0 {
        return Err(IrError::InvalidWidth(w));
    }
    let mut res = arena.bv_const(w, 0)?;
    let mut rem = arena.bv_const(w, 0)?;
    let one_c = arena.bv_const(w, 1)?;
    let two_c = arena.bv_const(w, 2)?;
    let three_c = arena.bv_const(w, 3)?;
    for i in (0..w / 2).rev() {
        // Bring down the next 2 bits of n (group i).
        let shift = arena.bv_const(w, u128::from(2 * i))?;
        let shifted = arena.bv_lshr(n, shift)?;
        let two_bits = arena.bv_and(shifted, three_c)?;
        // rem = rem*4 + group; trial = res*4 + 1.
        let rem4 = arena.bv_shl(rem, two_c)?;
        rem = arena.bv_or(rem4, two_bits)?;
        let res4 = arena.bv_shl(res, two_c)?;
        let trial = arena.bv_or(res4, one_c)?;
        let ge = arena.bv_uge(rem, trial)?;
        let rem_sub = arena.bv_sub(rem, trial)?;
        rem = arena.ite(ge, rem_sub, rem)?;
        // res = res*2 (+1 if we subtracted).
        let res2 = arena.bv_shl(res, one_c)?;
        let res2_1 = arena.bv_or(res2, one_c)?;
        res = arena.ite(ge, res2_1, res2)?;
    }
    Ok((res, rem))
}

/// Symbolic rounding of a nonnegative magnitude `m` by a *variable* drop amount
/// under a given [`RoundingMode`]: returns `round(m / 2^drop)` (`n`-bit), the
/// form the FP bit-blaster needs when the number of bits to drop depends on a
/// symbolic exponent. `negative` is the sign of the value `m` represents (a
/// `Bool` term; consulted only for the directed modes `TowardPositive`/
/// `TowardNegative`). `drop == 0` returns `m` unchanged.
///
/// Round-up rule by mode: nearest-even — over half, or exactly half with odd
/// LSB; nearest-away — at least half; toward-zero — never; toward-±∞ — any
/// nonzero remainder when the sign matches the rounding direction.
///
/// **Precondition:** `drop < n` (the FP bit-blaster guarantees this; for
/// `drop >= n`, `2^drop` overflows the width and the result is unspecified).
///
/// # Errors
///
/// Returns [`IrError::SortMismatch`] if `m` is not a bit-vector, or [`IrError`]
/// from the builders.
pub fn round_variable(
    arena: &mut TermArena,
    m: TermId,
    drop: TermId,
    mode: RoundingMode,
    negative: TermId,
) -> Result<TermId, IrError> {
    let Sort::BitVec(n) = arena.sort_of(m) else {
        return Err(IrError::SortMismatch {
            expected: "BitVec",
            found: arena.sort_of(m),
        });
    };
    let one = arena.bv_const(n, 1)?;
    let zero = arena.bv_const(n, 0)?;
    let pow = arena.bv_shl(one, drop)?; // 2^drop
    let half = arena.bv_lshr(pow, one)?; // 2^(drop-1)
    let mask = arena.bv_sub(pow, one)?; // 2^drop - 1
    let dropped = arena.bv_and(m, mask)?; // bits being discarded
    let shifted = arena.bv_lshr(m, drop)?; // kept quotient
    let lsb = arena.bv_and(shifted, one)?;
    let lsb_set = arena.eq(lsb, one)?;
    let gt_half = arena.bv_ugt(dropped, half)?;
    let eq_half = arena.eq(dropped, half)?;
    let any = {
        let is_zero = arena.eq(dropped, zero)?;
        arena.not(is_zero)?
    };
    let above = match mode {
        RoundingMode::NearestEven => {
            let tie = arena.and(eq_half, lsb_set)?;
            arena.or(gt_half, tie)?
        }
        RoundingMode::NearestAway => arena.or(gt_half, eq_half)?,
        RoundingMode::TowardZero => arena.bool_const(false),
        RoundingMode::TowardPositive => {
            let pos = arena.not(negative)?;
            arena.and(any, pos)?
        }
        RoundingMode::TowardNegative => arena.and(any, negative)?,
    };
    // No rounding when drop == 0 (then dropped == 0, which would otherwise look
    // like a tie for the nearest modes).
    let drop_nonzero = {
        let is_zero = arena.eq(drop, zero)?;
        arena.not(is_zero)?
    };
    let round_up = arena.and(drop_nonzero, above)?;
    let inc = arena.ite(round_up, one, zero)?;
    arena.bv_add(shifted, inc)
}

/// Symbolic **count-leading-zeros** over a bit-vector: returns a `BitVec(w)`
/// term giving the number of leading zero bits of the `w`-bit operand `x`
/// (`w` when `x` is zero). This is the variable-shift amount the FP normalizer
/// needs for the future symbolic bit-blaster; it is a pure bit-vector formula,
/// so it solves and replays on the existing path.
///
/// # Errors
///
/// Returns [`IrError::SortMismatch`] if `x` is not a bit-vector.
pub fn count_leading_zeros(arena: &mut TermArena, x: TermId) -> Result<TermId, IrError> {
    let Sort::BitVec(w) = arena.sort_of(x) else {
        return Err(IrError::SortMismatch {
            expected: "BitVec",
            found: arena.sort_of(x),
        });
    };
    let mut count = arena.bv_const(w, 0)?;
    let one_w = arena.bv_const(w, 1)?;
    let one_bit = arena.bv_const(1, 1)?;
    let mut found = arena.bool_const(false);
    // Scan from the most-significant bit down; count zeros until the first set
    // bit (`found`), after which the count stops growing.
    for i in (0..w).rev() {
        let bit = arena.extract(i, i, x)?;
        let bit_set = arena.eq(bit, one_bit)?;
        found = arena.or(found, bit_set)?;
        let incremented = arena.bv_add(count, one_w)?;
        count = arena.ite(found, count, incremented)?;
    }
    Ok(count)
}

/// Rounds an exact `f64` value to the nearest value of format `(eb, sb)` under
/// round-nearest-ties-to-even, returning the IEEE bit pattern. This is the
/// rounding keystone for arbitrary-format FP work (and the algorithm a symbolic
/// bit-blaster must encode in bit-vectors).
///
/// Correctness is checked against native `f32` in tests: for any `f64` `v`,
/// `round_to_format(8, 24, v)` equals `(v as f32).to_bits()` — native `as f32`
/// *is* round-nearest-even f64→f32. The integer significand `m·2^e` decoded from
/// `v` is exact, so the rounding is exact.
#[must_use]
#[allow(
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::many_single_char_names
)] // dense numeric routine; bit positions are intentional
pub fn round_to_format(eb: u32, sb: u32, v: f64, mode: RoundingMode) -> u128 {
    let total = eb + sb;
    let exp_field_max = (1u128 << eb) - 1;
    let sign = if v.is_sign_negative() {
        1u128 << (total - 1)
    } else {
        0
    };
    if v.is_nan() {
        return sign | (exp_field_max << (sb - 1)) | (1u128 << (sb - 2)); // canonical qNaN
    }
    if v.is_infinite() {
        return sign | (exp_field_max << (sb - 1));
    }
    let a = v.abs();
    if a == 0.0 {
        return sign;
    }
    let bias = (1i64 << (eb - 1)) - 1;
    let emin = 1 - bias; // minimum normal unbiased exponent

    // Decode a = m · 2^e exactly (m has ≤ 53 significant bits).
    let abits = a.to_bits();
    let ae = ((abits >> 52) & 0x7FF) as i64;
    let frac = abits & ((1u64 << 52) - 1);
    let (m, e): (u64, i64) = if ae == 0 {
        (frac, -1074) // subnormal f64
    } else {
        ((1u64 << 52) | frac, ae - 1075) // normal f64
    };

    // Unbiased exponent of the leading bit, clamped up to emin for the subnormal
    // grid; the kept significand's least-significant bit has exponent `lsb_exp`.
    let k = e + (63 - i64::from(m.leading_zeros()));
    let res_exp = k.max(emin);
    let lsb_exp = res_exp - (i64::from(sb) - 1);

    // Round m·2^e to a multiple of 2^lsb_exp under `mode`.
    let negative = v.is_sign_negative();
    let drop = lsb_exp - e;
    let q: u128 = if drop <= 0 {
        u128::from(m) << ((-drop) as u32)
    } else {
        let s = drop as u32;
        let (kept, round_bit, sticky) = if s >= 64 {
            (0u128, false, m != 0) // entire significand below the grid
        } else {
            let kept = u128::from(m >> s);
            let round_bit = (m >> (s - 1)) & 1 == 1;
            let sticky = (m & ((1u64 << (s - 1)) - 1)) != 0;
            (kept, round_bit, sticky)
        };
        let up = match mode {
            RoundingMode::NearestEven => round_bit && (sticky || kept & 1 == 1),
            RoundingMode::NearestAway => round_bit,
            RoundingMode::TowardZero => false,
            RoundingMode::TowardPositive => (round_bit || sticky) && !negative,
            RoundingMode::TowardNegative => (round_bit || sticky) && negative,
        };
        if up { kept + 1 } else { kept }
    };
    if q == 0 {
        return sign; // rounded to ±0
    }

    let top = 127 - i64::from(q.leading_zeros());
    let biased = lsb_exp + top + bias;
    if biased >= exp_field_max as i64 {
        return sign | (exp_field_max << (sb - 1)); // overflow → ±∞
    }
    if biased <= 0 {
        // Subnormal: exponent field 0, trailing significand = q.
        return sign | (q & ((1u128 << (sb - 1)) - 1));
    }
    // Normal: strip the leading bit to get the stored trailing significand.
    let trailing = (q - (1u128 << top)) & ((1u128 << (sb - 1)) - 1);
    sign | ((biased as u128) << (sb - 1)) | trailing
}

/// Constant-folds `fp.to_real` (FP → mathematical Real, ADR-0015) for a finite
/// F32/F64 constant. FP→Real is **exact** (no rounding), so when the exact value
/// fits the `i128`-based [`Rational`] this folds to a `Real` constant; `NaN`/`∞`
/// (not real numbers) and values whose exact rational exceeds `i128` return
/// `Ok(None)`. Bridges FP into the linear-real-arithmetic theory.
pub fn to_real(
    arena: &mut TermArena,
    fmt: FloatFormat,
    x: TermId,
) -> Result<Option<TermId>, IrError> {
    let Some(bits) = const_bits(arena, x) else {
        return Ok(None);
    };
    let (eb, sb, total) = (fmt.exp_bits, fmt.sig_bits, fmt.width());
    let sign = (bits >> (total - 1)) & 1 == 1;
    let exp_field = (bits >> (sb - 1)) & ((1u128 << eb) - 1);
    let trailing = bits & ((1u128 << (sb - 1)) - 1);
    if exp_field == (1u128 << eb) - 1 {
        return Ok(None); // ∞ or NaN — not a real number
    }
    let exp_bias = (1i64 << (eb - 1)) - 1;
    let sb_i = i64::from(sb);
    let (mag, exp): (u128, i64) = if exp_field == 0 {
        if trailing == 0 {
            return Ok(Some(arena.real_const(Rational::integer(0))));
        }
        (trailing, 1 - exp_bias - (sb_i - 1)) // subnormal
    } else {
        let Ok(field) = i64::try_from(exp_field) else {
            return Ok(None);
        };
        ((1u128 << (sb - 1)) | trailing, field - exp_bias - (sb_i - 1)) // normal
    };
    let Ok(m) = i128::try_from(mag) else {
        return Ok(None);
    };
    let Some((num, den)) = scale_to_fraction(m, exp) else {
        return Ok(None); // exact value does not fit i128
    };
    let num = if sign { -num } else { num };
    Ok(Some(arena.real_const(Rational::new(num, den))))
}

/// `m * 2^exp` as an `i128` fraction `(num, den)`, or `None` if it overflows.
fn scale_to_fraction(m: i128, exp: i64) -> Option<(i128, i128)> {
    if exp >= 0 {
        let shift = u32::try_from(exp).ok()?;
        let used = 128 - m.leading_zeros();
        if used + shift > 127 {
            return None; // m << exp overflows i128
        }
        Some((m << shift, 1))
    } else {
        let shift = u32::try_from(-exp).ok()?;
        if shift > 126 {
            return None; // 2^shift overflows i128
        }
        Some((m, 1i128 << shift))
    }
}

/// Constant-folds `fp.to_ubv` (FP → unsigned `width`-bit BV) per rounding mode,
/// for an F32/F64 constant. Folds only when the result is **well-defined**: the
/// operand is finite and the rounded integer is in `[0, 2^width)`; otherwise
/// returns `Ok(None)` (SMT leaves NaN/∞/out-of-range unspecified, so refusing to
/// fold is sound).
#[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)] // range-checked
pub fn to_ubv(
    arena: &mut TermArena,
    fmt: FloatFormat,
    mode: RoundingMode,
    x: TermId,
    width: u32,
) -> Result<Option<TermId>, IrError> {
    let Some(v) = decode_to_f64(arena, fmt, x) else {
        return Ok(None);
    };
    if !v.is_finite() {
        return Ok(None);
    }
    let r = round_f64(v, mode);
    if r < 0.0 || width == 0 || r >= exp2(width) {
        return Ok(None);
    }
    let int = r as u128;
    Ok(Some(arena.bv_const(width, int)?))
}

/// Constant-folds `fp.to_sbv` (FP → signed two's-complement `width`-bit BV) per
/// rounding mode, for an F32/F64 constant. Folds only when well-defined: finite
/// and the rounded integer is in `[-2^(width-1), 2^(width-1))`; otherwise `None`.
#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)] // range-checked
pub fn to_sbv(
    arena: &mut TermArena,
    fmt: FloatFormat,
    mode: RoundingMode,
    x: TermId,
    width: u32,
) -> Result<Option<TermId>, IrError> {
    let Some(v) = decode_to_f64(arena, fmt, x) else {
        return Ok(None);
    };
    if !v.is_finite() || width == 0 {
        return Ok(None);
    }
    let r = round_f64(v, mode);
    let limit = exp2(width - 1);
    if r < -limit || r >= limit {
        return Ok(None);
    }
    let int = r as i128;
    let mask = if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    };
    let bits = (int as u128) & mask;
    Ok(Some(arena.bv_const(width, bits)?))
}

fn decode_to_f64(arena: &TermArena, fmt: FloatFormat, x: TermId) -> Option<f64> {
    let v = const_bits(arena, x)?;
    if fmt == FloatFormat::F32 {
        Some(f64::from(f32::from_bits(low32(v))))
    } else if fmt == FloatFormat::F64 {
        Some(f64::from_bits(low64(v)))
    } else if fmt.is_ieee() {
        // Every other IEEE format (`sig_bits ≤ 53`) decodes exactly to f64.
        Some(fmt.decode_ieee_f64(v))
    } else {
        None
    }
}

fn round_f64(v: f64, mode: RoundingMode) -> f64 {
    match mode {
        RoundingMode::NearestEven => v.round_ties_even(),
        RoundingMode::NearestAway => v.round(),
        RoundingMode::TowardZero => v.trunc(),
        RoundingMode::TowardPositive => v.ceil(),
        RoundingMode::TowardNegative => v.floor(),
    }
}

// power of two is exact in f64 for the BV widths we handle; `width` ≤ 2^31.
#[allow(clippy::cast_precision_loss, clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
fn exp2(width: u32) -> f64 {
    (2.0f64).powi(width as i32)
}

/// Interprets a `w`-bit value as two's-complement signed.
#[allow(clippy::cast_possible_wrap)] // value < 2^w ≤ 2^127 fits i128 before adjust
fn to_signed(v: u128, w: u32) -> i128 {
    if w < 128 && (v >> (w - 1)) & 1 == 1 {
        (v as i128) - (1i128 << w)
    } else {
        v as i128
    }
}

fn fold_bin(
    arena: &mut TermArena,
    fmt: FloatFormat,
    x: TermId,
    y: TermId,
    op32: impl Fn(f32, f32) -> f32,
    op64: impl Fn(f64, f64) -> f64,
) -> Result<Option<TermId>, IrError> {
    let (Some(xv), Some(yv)) = (const_bits(arena, x), const_bits(arena, y)) else {
        return Ok(None);
    };
    let bits = if fmt == FloatFormat::F32 {
        let r = op32(f32::from_bits(low32(xv)), f32::from_bits(low32(yv)));
        u128::from(r.to_bits())
    } else if fmt == FloatFormat::F64 {
        let r = op64(f64::from_bits(low64(xv)), f64::from_bits(low64(yv)));
        u128::from(r.to_bits())
    } else {
        return Ok(None);
    };
    Ok(Some(arena.bv_const(fmt.width(), bits)?))
}

fn const_bits(arena: &TermArena, t: TermId) -> Option<u128> {
    match arena.node(t) {
        TermNode::BvConst { value, .. } => Some(*value),
        _ => None,
    }
}

fn low32(v: u128) -> u32 {
    u32::try_from(v & 0xFFFF_FFFF).unwrap_or(0)
}

fn low64(v: u128) -> u64 {
    u64::try_from(v & 0xFFFF_FFFF_FFFF_FFFF).unwrap_or(0)
}

// --- internal helpers ---------------------------------------------------------

fn all_ones_mask(fmt: FloatFormat) -> u128 {
    let w = fmt.width();
    if w >= 128 { u128::MAX } else { (1u128 << w) - 1 }
}

fn sign_mask(fmt: FloatFormat) -> u128 {
    1u128 << (fmt.width() - 1)
}

fn sign_set(arena: &mut TermArena, fmt: FloatFormat, x: TermId) -> Result<TermId, IrError> {
    let s = fmt.sign(arena, x)?;
    let one = arena.bv_const(1, 1)?;
    arena.eq(s, one)
}

fn exp_all_ones(arena: &mut TermArena, fmt: FloatFormat, x: TermId) -> Result<TermId, IrError> {
    let e = fmt.exponent(arena, x)?;
    let ones = arena.bv_const(fmt.exp_bits, (1u128 << fmt.exp_bits) - 1)?;
    arena.eq(e, ones)
}

fn exp_all_zero(arena: &mut TermArena, fmt: FloatFormat, x: TermId) -> Result<TermId, IrError> {
    let e = fmt.exponent(arena, x)?;
    let zero = arena.bv_const(fmt.exp_bits, 0)?;
    arena.eq(e, zero)
}

fn sig_zero(arena: &mut TermArena, fmt: FloatFormat, x: TermId) -> Result<TermId, IrError> {
    let s = fmt.trailing_sig(arena, x)?;
    let zero = arena.bv_const(fmt.sig_bits - 1, 0)?;
    arena.eq(s, zero)
}

fn sig_nonzero(arena: &mut TermArena, fmt: FloatFormat, x: TermId) -> Result<TermId, IrError> {
    let z = sig_zero(arena, fmt, x)?;
    arena.not(z)
}

/// `cond ∧ ¬nan ∧ ¬zero` — the shared tail of `isNegative`/`isPositive`.
fn not_nan_not_zero_and(
    arena: &mut TermArena,
    cond: TermId,
    nan: TermId,
    zero: TermId,
) -> Result<TermId, IrError> {
    let not_nan = arena.not(nan)?;
    let not_zero = arena.not(zero)?;
    let a = arena.and(cond, not_nan)?;
    arena.and(a, not_zero)
}

/// Shared core of [`min`]/[`max`]: pick `x` or `y` by ordering key, propagating
/// the non-NaN operand when one is NaN. `want_smaller` selects min vs max.
fn select_by_order(
    arena: &mut TermArena,
    fmt: FloatFormat,
    x: TermId,
    y: TermId,
    want_smaller: bool,
) -> Result<TermId, IrError> {
    fmt.check(arena, x)?;
    fmt.check(arena, y)?;
    let kx = order_key(arena, fmt, x)?;
    let ky = order_key(arena, fmt, y)?;
    let x_le_y = arena.bv_ule(kx, ky)?;
    // min: x when x ≤ y; max: y when x ≤ y.
    let (lo, hi) = if want_smaller { (x, y) } else { (y, x) };
    let by_order = arena.ite(x_le_y, lo, hi)?;
    // NaN propagation: if x is NaN return y, if y is NaN return x.
    let nx = is_nan(arena, fmt, x)?;
    let ny = is_nan(arena, fmt, y)?;
    let if_x_nan = arena.ite(nx, y, by_order)?;
    arena.ite(ny, x, if_x_nan)
}

/// The monotone unsigned ordering key: flip all bits if the sign is set,
/// otherwise set the sign bit. Unsigned `<` on keys is the float order for
/// non-NaN values (with `±0` handled by the zero special-case in [`lt`]).
fn order_key(arena: &mut TermArena, fmt: FloatFormat, x: TermId) -> Result<TermId, IrError> {
    let signed = sign_set(arena, fmt, x)?;
    let flipped = arena.bv_not(x)?;
    let smask = arena.bv_const(fmt.width(), sign_mask(fmt))?;
    let pos_key = arena.bv_or(x, smask)?;
    arena.ite(signed, flipped, pos_key)
}

#[cfg(test)]
#[allow(
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::cast_precision_loss
)]
mod tests {
    use super::*;
    use axeyum_ir::{Assignment, Value, eval};

    fn to_signed(v: u128, w: u32) -> i128 {
        if w < 128 && (v >> (w - 1)) & 1 == 1 {
            (v as i128) - (1i128 << w)
        } else {
            v as i128
        }
    }

    /// `pack_params` must match a direct reference for the rounding `lsb_exp`/
    /// `drop` over a pseudo-random battery of significands and exponents.
    #[test]
    fn pack_params_matches_reference() {
        fn ref_params(m: u128, e: i64, sb: u32, bias: i64) -> (i64, i64) {
            let lead_idx = (128 - i64::from(m.leading_zeros())) - 1; // bit_length - 1
            let k = e + lead_idx;
            let res_exp = k.max(1 - bias);
            let lsb_exp = res_exp - (i64::from(sb) - 1);
            (lsb_exp, lsb_exp - e)
        }

        let w = 80u32;
        let sb = 24u32;
        let bias = 127i64;
        let mut state = 0xabcd_1234_5678_9999u64;
        for _ in 0..3000 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let m = (u128::from(state) % ((1u128 << 53) - 1)) + 1;
            let e = i64::try_from((state >> 8) % 401).unwrap() - 200;

            let mut a = TermArena::new();
            let m_w = a.bv_const(w, m).unwrap();
            let e_t = sconst(&mut a, w, e).unwrap();
            let (lsb_t, drop_t) = pack_params(&mut a, m_w, e_t, sb, bias).unwrap();
            let (want_lsb, want_drop) = ref_params(m, e, sb, bias);

            let read = |a: &TermArena, t| match eval(a, t, &Assignment::new()) {
                Ok(Value::Bv { value, .. }) => to_signed(value, w),
                other => panic!("expected Bv, got {other:?}"),
            };
            assert_eq!(read(&a, lsb_t), i128::from(want_lsb), "lsb_exp m={m} e={e}");
            assert_eq!(read(&a, drop_t), i128::from(want_drop), "drop m={m} e={e}");
        }
    }

    /// `pack_value` must equal the validated `round_to_format` reference for the
    /// value (-1)^sign · m · 2^e, over a pseudo-random battery (m ≤ 2^53, so the
    /// f64 reference value is exact), exercising normal/subnormal/overflow.
    #[test]
    #[allow(clippy::cast_precision_loss)] // m ≤ 2^53 is exact in f64
    fn pack_value_matches_round_to_format() {
        let w = 80u32;
        let (eb, sb) = (8u32, 24u32);
        let mut state = 0x0bad_c0de_0f1e_2d3cu64;
        for _ in 0..4000 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let m = (u128::from(state) % ((1u128 << 53) - 1)) + 1;
            // exponent spread across overflow / normal / subnormal / underflow
            let e = i64::try_from((state >> 7) % 380).unwrap() - 200;
            let sign = (state >> 3) & 1 == 1;

            let value = (if sign { -1.0f64 } else { 1.0 }) * (m as f64) * 2.0f64.powi(e as i32);
            let want = round_to_format(eb, sb, value, RoundingMode::NearestEven);

            let mut a = TermArena::new();
            let m_w = a.bv_const(w, m).unwrap();
            let e_t = sconst(&mut a, w, e).unwrap();
            let sign_t = a.bool_const(sign);
            let packed =
                pack_value(&mut a, eb, sb, sign_t, m_w, e_t, RoundingMode::NearestEven).unwrap();
            let got = match eval(&a, packed, &Assignment::new()) {
                Ok(Value::Bv { value, .. }) => value,
                other => panic!("expected Bv, got {other:?}"),
            };
            assert_eq!(
                got, want,
                "pack_value(sign={sign}, m={m:#x}, e={e}) = {got:#x}, want {want:#x} (value={value})"
            );
        }
    }

    /// Symbolic `fp.mul` must match native `f32` multiplication over structured
    /// values (specials/subnormals/normals) and a pseudo-random sweep. NaN
    /// results are compared as "is a NaN" (bit pattern unspecified by SMT).
    #[test]
    fn mul_matches_native_f32() {
        let mut a = TermArena::new();
        let check = |a: &mut TermArena, ab: u32, bb: u32| {
            let at = a.bv_const(32, u128::from(ab)).unwrap();
            let bt = a.bv_const(32, u128::from(bb)).unwrap();
            let r = mul(a, FloatFormat::F32, at, bt, RoundingMode::NearestEven).unwrap();
            let got = match eval(a, r, &Assignment::new()) {
                Ok(Value::Bv { value, .. }) => value,
                other => panic!("expected Bv, got {other:?}"),
            };
            let prod = f32::from_bits(ab) * f32::from_bits(bb);
            if prod.is_nan() {
                let exp = (got >> 23) & 0xFF;
                let mant = got & 0x7F_FFFF;
                assert!(
                    exp == 0xFF && mant != 0,
                    "mul({ab:#x}, {bb:#x}) should be NaN, got {got:#x}"
                );
            } else {
                assert_eq!(
                    got,
                    u128::from(prod.to_bits()),
                    "mul({ab:#x}, {bb:#x}) = {got:#x}, native = {:#x}",
                    prod.to_bits()
                );
            }
        };

        let structured: [u32; 16] = [
            0x0000_0000, // +0
            0x8000_0000, // -0
            0x3F80_0000, // 1.0
            0xBF80_0000, // -1.0
            0x4000_0000, // 2.0
            0x3F00_0000, // 0.5
            0x4040_0000, // 3.0
            0x7F80_0000, // +inf
            0xFF80_0000, // -inf
            0x7FC0_0000, // NaN
            0x0080_0000, // smallest normal
            0x0000_0001, // smallest subnormal
            0x007F_FFFF, // largest subnormal
            0x7F7F_FFFF, // f32::MAX
            0x4B00_0000, // 2^23
            0x4B80_0000, // 2^24
        ];
        for &x in &structured {
            for &y in &structured {
                check(&mut a, x, y);
            }
        }

        let mut state: u64 = 0x5151_a7e0_0d15_ea5e;
        for _ in 0..4000 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let x = (state & 0xFFFF_FFFF) as u32;
            let y = (state >> 32) as u32;
            check(&mut a, x, y);
        }
    }

    fn f16_to_f64(bits: u16) -> f64 {
        let sign = if (bits >> 15) & 1 == 1 { -1.0 } else { 1.0 };
        let exp = (bits >> 10) & 0x1F;
        let mant = bits & 0x3FF;
        if exp == 0x1F {
            return if mant != 0 { f64::NAN } else { sign * f64::INFINITY };
        }
        if exp == 0 {
            return sign * f64::from(mant) * 2f64.powi(-24); // subnormal
        }
        sign * f64::from(1024 + mant) * 2f64.powi(i32::from(exp) - 25)
    }

    /// Symbolic `fp.add` for F16 must equal the validated `round_to_format`
    /// reference applied to the exact f64 sum of the operands. Structured
    /// (specials/subnormals/normals) + pseudo-random sweep.
    #[test]
    fn add_f16_matches_reference() {
        let mut a = TermArena::new();
        let check = |a: &mut TermArena, ab: u16, bb: u16| {
            let at = a.bv_const(16, u128::from(ab)).unwrap();
            let bt = a.bv_const(16, u128::from(bb)).unwrap();
            let r = add(a, FloatFormat::F16, at, bt, RoundingMode::NearestEven).unwrap();
            let got = match eval(a, r, &Assignment::new()) {
                Ok(Value::Bv { value, .. }) => value,
                other => panic!("expected Bv, got {other:?}"),
            };
            let sum = f16_to_f64(ab) + f16_to_f64(bb); // exact for f16 operands
            if sum.is_nan() {
                let exp = (got >> 10) & 0x1F;
                let mant = got & 0x3FF;
                assert!(exp == 0x1F && mant != 0, "add({ab:#x},{bb:#x}) want NaN, got {got:#x}");
            } else {
                let want = round_to_format(5, 11, sum, RoundingMode::NearestEven);
                assert_eq!(got, want, "add({ab:#x},{bb:#x}) = {got:#x}, want {want:#x}");
            }
        };

        let structured: [u16; 14] = [
            0x0000, 0x8000, // ±0
            0x3C00, 0xBC00, // ±1.0
            0x4000, 0x3800, // 2.0, 0.5
            0x7C00, 0xFC00, // ±inf
            0x7E00, // NaN
            0x0400, // smallest normal
            0x0001, 0x03FF, // subnormals
            0x7BFF, // f16 max
            0x4900, // 10.0
        ];
        for &x in &structured {
            for &y in &structured {
                check(&mut a, x, y);
            }
        }

        let mut state: u64 = 0x9e37_79b9_7f4a_7c15;
        for _ in 0..4000 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let x = (state & 0xFFFF) as u16;
            let y = ((state >> 16) & 0xFFFF) as u16;
            check(&mut a, x, y);
        }
    }

    #[test]
    fn sqrt_matches_native_f32_and_f64() {
        let mut a = TermArena::new();
        let check32 = |a: &mut TermArena, xb: u32| {
            let xt = a.bv_const(32, u128::from(xb)).unwrap();
            let r = sqrt(a, FloatFormat::F32, xt, RoundingMode::NearestEven).unwrap();
            let got = match eval(a, r, &Assignment::new()) {
                Ok(Value::Bv { value, .. }) => value,
                other => panic!("expected Bv, got {other:?}"),
            };
            let s = f32::from_bits(xb).sqrt();
            if s.is_nan() {
                let exp = (got >> 23) & 0xFF;
                let mant = got & 0x7F_FFFF;
                assert!(exp == 0xFF && mant != 0, "sqrt({xb:#x}) want NaN, got {got:#x}");
            } else {
                assert_eq!(got, u128::from(s.to_bits()), "sqrt({xb:#x})");
            }
        };
        let s32: [u32; 12] = [
            0x0000_0000, 0x8000_0000, 0x3F80_0000, 0x4080_0000, 0x4000_0000, 0xBF80_0000,
            0x7F80_0000, 0xFF80_0000, 0x7FC0_0000, 0x0080_0000, 0x0000_0001, 0x7F7F_FFFF,
        ];
        for &x in &s32 {
            check32(&mut a, x);
        }
        let mut state: u64 = 0x5217_b1f7_2c8e_0001;
        for _ in 0..1500 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            check32(&mut a, (state >> 16) as u32);
        }

        let check64 = |a: &mut TermArena, xb: u64| {
            let xt = a.bv_const(64, u128::from(xb)).unwrap();
            let r = sqrt(a, FloatFormat::F64, xt, RoundingMode::NearestEven).unwrap();
            let got = match eval(a, r, &Assignment::new()) {
                Ok(Value::Bv { value, .. }) => value,
                other => panic!("expected Bv, got {other:?}"),
            };
            let s = f64::from_bits(xb).sqrt();
            if s.is_nan() {
                assert!((got >> 52) & 0x7FF == 0x7FF && got & 0xF_FFFF_FFFF_FFFF != 0);
            } else {
                assert_eq!(got, u128::from(s.to_bits()), "sqrt64({xb:#x})");
            }
        };
        let mut s = 0x3243_f6a8_885a_308du64;
        for _ in 0..1000 {
            s = s.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1_442_695_040_888_963_407);
            check64(&mut a, s);
        }
    }

    #[test]
    fn round_to_integral_sym_matches_native_f32() {
        let modes = [
            (RoundingMode::NearestEven, 0u8),
            (RoundingMode::NearestAway, 1),
            (RoundingMode::TowardZero, 2),
            (RoundingMode::TowardPositive, 3),
            (RoundingMode::TowardNegative, 4),
        ];
        let mut a = TermArena::new();
        let mut state: u64 = 0x1234_5678_9abc_def0;
        for &(mode, kind) in &modes {
            for _ in 0..600 {
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                let xb = (state >> 16) as u32;
                let xt = a.bv_const(32, u128::from(xb)).unwrap();
                let r = round_to_integral_sym(&mut a, FloatFormat::F32, mode, xt).unwrap();
                let got = match eval(&a, r, &Assignment::new()) {
                    Ok(Value::Bv { value, .. }) => value,
                    other => panic!("expected Bv, got {other:?}"),
                };
                let v = f32::from_bits(xb);
                let want = match kind {
                    0 => v.round_ties_even(),
                    1 => v.round(),
                    2 => v.trunc(),
                    3 => v.ceil(),
                    _ => v.floor(),
                };
                if want.is_nan() {
                    assert!((got >> 23) & 0xFF == 0xFF && got & 0x7F_FFFF != 0);
                } else {
                    assert_eq!(got, u128::from(want.to_bits()), "rint({xb:#x},{mode:?})");
                }
            }
        }
    }

    #[test]
    fn e2m1_decode_and_classification() {
        use axeyum_ir::Rational;
        // The full E2M1 magnitude table by (exp, mant): the 8 magnitudes.
        // codes 0..8 = sign 0; the spec value set is {0,.5,1,1.5,2,3,4,6}.
        let table: [(i128, i128); 8] = [
            (0, 1),   // 000: 0
            (1, 2),   // 001: 0.5
            (1, 1),   // 010: 1
            (3, 2),   // 011: 1.5
            (2, 1),   // 100: 2
            (3, 1),   // 101: 3
            (4, 1),   // 110: 4
            (6, 1),   // 111: 6
        ];
        let mut a = TermArena::new();
        for code in 0u128..8 {
            for sign in [0u128, 1] {
                let bits = (sign << 3) | code;
                let x = a.bv_const(4, bits).unwrap();
                let r = e2m1_to_real(&mut a, x).unwrap().expect("constant decodes");
                let (num, den) = table[code as usize];
                let want = if sign == 1 {
                    Rational::new(-num, den)
                } else {
                    Rational::new(num, den)
                };
                match eval(&a, r, &Assignment::new()) {
                    Ok(Value::Real(got)) => assert_eq!(got, want, "E2M1 {bits:#x}"),
                    other => panic!("expected Real, got {other:?}"),
                }
            }
        }
        // Classification: 0x0 zero; 0x1 subnormal (±0.5); 0b110 (=4) normal.
        let is_true = |arena: &TermArena, term: axeyum_ir::TermId| {
            matches!(eval(arena, term, &Assignment::new()), Ok(Value::Bool(true)))
        };
        let zero = a.bv_const(4, 0).unwrap();
        let t_zero = e2m1_is_zero(&mut a, zero).unwrap();
        assert!(is_true(&a, t_zero), "0 is zero");
        let half = a.bv_const(4, 1).unwrap();
        let t_sub = e2m1_is_subnormal(&mut a, half).unwrap();
        assert!(is_true(&a, t_sub), "0.5 is subnormal");
        let four = a.bv_const(4, 0b110).unwrap();
        let t_norm = e2m1_is_normal(&mut a, four).unwrap();
        assert!(is_true(&a, t_norm), "4 is normal");
    }

    #[test]
    fn e4m3_classification() {
        // OCP FP8 E4M3 deviates from IEEE: 0x7E (0.1111.110) is the *max normal*
        // (448), not infinity; only 0x7F/0xFF (S.1111.111) is NaN; there are no
        // infinities.
        let mut a = TermArena::new();
        let bit = |a: &TermArena, t: axeyum_ir::TermId| matches!(
            eval(a, t, &Assignment::new()), Ok(Value::Bool(true))
        );
        let mk = |a: &mut TermArena, v: u128| a.bv_const(8, v).unwrap();

        for nan in [0x7Fu128, 0xFF] {
            let x = mk(&mut a, nan);
            let t = e4m3_is_nan(&mut a, x).unwrap();
            assert!(bit(&a, t), "{nan:#x} is E4M3 NaN");
        }
        // 0x7E is max-normal (would be inf in IEEE) — NOT NaN, IS normal.
        let max = mk(&mut a, 0x7E);
        let t = e4m3_is_nan(&mut a, max).unwrap();
        assert!(!bit(&a, t), "0x7E is not NaN in E4M3");
        let t = e4m3_is_normal(&mut a, max).unwrap();
        assert!(bit(&a, t), "0x7E (448) is a normal in E4M3");

        for z in [0x00u128, 0x80] {
            let x = mk(&mut a, z);
            let t = e4m3_is_zero(&mut a, x).unwrap();
            assert!(bit(&a, t), "{z:#x} is zero");
        }
        let sub = mk(&mut a, 0x01);
        let t = e4m3_is_subnormal(&mut a, sub).unwrap();
        assert!(bit(&a, t), "0x01 is subnormal");
        let normal = mk(&mut a, 0x08); // 0.0001.000 smallest normal
        let t = e4m3_is_normal(&mut a, normal).unwrap();
        assert!(bit(&a, t), "0x08 is normal");
    }

    #[test]
    fn bf16_arithmetic_is_correct() {
        // bfloat16 is the top 16 bits of an f32, so we can decode it exactly to
        // f64 and use round_to_format (the algorithm validated against native f32)
        // as the correctly-rounded reference for the generic add/mul on BF16.
        // Demonstrates that GPU/ML precisions work via the format-generic ops.
        fn bf16_to_f64(bits: u16) -> f64 {
            f64::from(f32::from_bits(u32::from(bits) << 16))
        }
        let bf = FloatFormat::BF16;
        let mut a = TermArena::new();
        let mut state: u64 = 0xb16b_00b5_1234_5678;
        for _ in 0..3000 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let xb = (state & 0xFFFF) as u16;
            let yb = ((state >> 16) & 0xFFFF) as u16;
            let xt = a.bv_const(16, u128::from(xb)).unwrap();
            let yt = a.bv_const(16, u128::from(yb)).unwrap();
            for (term, exact) in [
                (mul(&mut a, bf, xt, yt, RoundingMode::NearestEven).unwrap(),
                 bf16_to_f64(xb) * bf16_to_f64(yb)),
                (add(&mut a, bf, xt, yt, RoundingMode::NearestEven).unwrap(),
                 bf16_to_f64(xb) + bf16_to_f64(yb)),
            ] {
                let got = match eval(&a, term, &Assignment::new()) {
                    Ok(Value::Bv { value, .. }) => value,
                    other => panic!("expected Bv, got {other:?}"),
                };
                if exact.is_nan() {
                    assert!((got >> 7) & 0xFF == 0xFF && got & 0x7F != 0, "bf16 want NaN");
                } else {
                    let want = round_to_format(8, 8, exact, RoundingMode::NearestEven);
                    assert_eq!(got, want, "bf16 op({xb:#x},{yb:#x}) = {got:#x}, want {want:#x}");
                }
            }
        }
    }

    #[test]
    fn to_fp_matches_native_casts() {
        let mut a = TermArena::new();
        // f32 -> f64 is exact (widening); mode-independent.
        let mut state: u64 = 0xc0ff_ee00_1234_5678;
        for _ in 0..1500 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let xb = (state >> 16) as u32;
            let xt = a.bv_const(32, u128::from(xb)).unwrap();
            let r = to_fp(&mut a, FloatFormat::F32, FloatFormat::F64, RoundingMode::NearestEven, xt)
                .unwrap();
            let got = match eval(&a, r, &Assignment::new()) {
                Ok(Value::Bv { value, .. }) => value,
                other => panic!("expected Bv, got {other:?}"),
            };
            let wide = f64::from(f32::from_bits(xb));
            if wide.is_nan() {
                assert!((got >> 52) & 0x7FF == 0x7FF && got & 0xF_FFFF_FFFF_FFFF != 0);
            } else {
                assert_eq!(got, u128::from(wide.to_bits()), "f32->f64({xb:#x})");
            }
        }
        // f64 -> f32 narrows (rounds); RNE checked against native `as f32`,
        // all modes against round_to_format on the exact f64 value.
        let modes = [
            RoundingMode::NearestEven,
            RoundingMode::NearestAway,
            RoundingMode::TowardZero,
            RoundingMode::TowardPositive,
            RoundingMode::TowardNegative,
        ];
        let mut s = 0x3243_f6a8_885a_308du64;
        for &mode in &modes {
            for _ in 0..600 {
                s = s
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                let xt = a.bv_const(64, u128::from(s)).unwrap();
                let r =
                    to_fp(&mut a, FloatFormat::F64, FloatFormat::F32, mode, xt).unwrap();
                let got = match eval(&a, r, &Assignment::new()) {
                    Ok(Value::Bv { value, .. }) => value,
                    other => panic!("expected Bv, got {other:?}"),
                };
                let v = f64::from_bits(s);
                if v.is_nan() {
                    assert!((got >> 23) & 0xFF == 0xFF && got & 0x7F_FFFF != 0);
                } else {
                    let want = round_to_format(8, 24, v, mode);
                    assert_eq!(got, want, "f64->f32({s:#x},{mode:?})");
                }
            }
        }
    }

    #[test]
    fn mul_all_rounding_modes_f32() {
        // For F32 the exact product fits f64 (≤48-bit significand), so
        // round_to_format(exact, mode) is the correctly-rounded reference for
        // every mode — validating the rounding-mode plumbing end to end.
        let modes = [
            RoundingMode::NearestEven,
            RoundingMode::NearestAway,
            RoundingMode::TowardZero,
            RoundingMode::TowardPositive,
            RoundingMode::TowardNegative,
        ];
        let mut a = TermArena::new();
        let mut state: u64 = 0x9e37_79b9_7f4a_7c15;
        for &mode in &modes {
            for _ in 0..800 {
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                let ab = (state & 0xFFFF_FFFF) as u32;
                let bb = (state >> 32) as u32;
                let at = a.bv_const(32, u128::from(ab)).unwrap();
                let bt = a.bv_const(32, u128::from(bb)).unwrap();
                let r = mul(&mut a, FloatFormat::F32, at, bt, mode).unwrap();
                let got = match eval(&a, r, &Assignment::new()) {
                    Ok(Value::Bv { value, .. }) => value,
                    other => panic!("expected Bv, got {other:?}"),
                };
                let exact = f64::from(f32::from_bits(ab)) * f64::from(f32::from_bits(bb));
                if exact.is_nan() {
                    assert!((got >> 23) & 0xFF == 0xFF && got & 0x7F_FFFF != 0);
                } else {
                    let want = round_to_format(8, 24, exact, mode);
                    assert_eq!(got, want, "mul({ab:#x},{bb:#x},{mode:?}) = {got:#x}, want {want:#x}");
                }
            }
        }
    }

    #[test]
    fn div_matches_native_f32_and_f64() {
        let mut a = TermArena::new();
        let check32 = |a: &mut TermArena, ab: u32, bb: u32| {
            let at = a.bv_const(32, u128::from(ab)).unwrap();
            let bt = a.bv_const(32, u128::from(bb)).unwrap();
            let r = div(a, FloatFormat::F32, at, bt, RoundingMode::NearestEven).unwrap();
            let got = match eval(a, r, &Assignment::new()) {
                Ok(Value::Bv { value, .. }) => value,
                other => panic!("expected Bv, got {other:?}"),
            };
            let q = f32::from_bits(ab) / f32::from_bits(bb);
            if q.is_nan() {
                let exp = (got >> 23) & 0xFF;
                let mant = got & 0x7F_FFFF;
                assert!(exp == 0xFF && mant != 0, "div({ab:#x},{bb:#x}) want NaN, got {got:#x}");
            } else {
                assert_eq!(got, u128::from(q.to_bits()), "div({ab:#x},{bb:#x})");
            }
        };
        let s32: [u32; 12] = [
            0x0000_0000, 0x8000_0000, 0x3F80_0000, 0xBF80_0000, 0x4000_0000, 0x3F00_0000,
            0x7F80_0000, 0xFF80_0000, 0x7FC0_0000, 0x0080_0000, 0x0000_0001, 0x7F7F_FFFF,
        ];
        for &x in &s32 {
            for &y in &s32 {
                check32(&mut a, x, y);
            }
        }
        let mut state: u64 = 0xd1ce_d1ce_d1ce_d1ce;
        for _ in 0..3000 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let x = (state & 0xFFFF_FFFF) as u32;
            let y = (state >> 32) as u32;
            check32(&mut a, x, y);
        }

        // F64 spot checks.
        let check64 = |a: &mut TermArena, ab: u64, bb: u64| {
            let at = a.bv_const(64, u128::from(ab)).unwrap();
            let bt = a.bv_const(64, u128::from(bb)).unwrap();
            let r = div(a, FloatFormat::F64, at, bt, RoundingMode::NearestEven).unwrap();
            let got = match eval(a, r, &Assignment::new()) {
                Ok(Value::Bv { value, .. }) => value,
                other => panic!("expected Bv, got {other:?}"),
            };
            let q = f64::from_bits(ab) / f64::from_bits(bb);
            if q.is_nan() {
                assert!((got >> 52) & 0x7FF == 0x7FF && got & 0xF_FFFF_FFFF_FFFF != 0);
            } else {
                assert_eq!(got, u128::from(q.to_bits()), "div64({ab:#x},{bb:#x})");
            }
        };
        let mut s = 0x2718_2818_2845_9045u64;
        for _ in 0..2000 {
            s = s.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1_442_695_040_888_963_407);
            let x = s;
            s = s.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1_442_695_040_888_963_407);
            check64(&mut a, x, s);
        }
    }

    #[test]
    fn add_matches_native_f32() {
        let mut a = TermArena::new();
        let check = |a: &mut TermArena, ab: u32, bb: u32| {
            let at = a.bv_const(32, u128::from(ab)).unwrap();
            let bt = a.bv_const(32, u128::from(bb)).unwrap();
            let r = add(a, FloatFormat::F32, at, bt, RoundingMode::NearestEven).unwrap();
            let got = match eval(a, r, &Assignment::new()) {
                Ok(Value::Bv { value, .. }) => value,
                other => panic!("expected Bv, got {other:?}"),
            };
            let sum = f32::from_bits(ab) + f32::from_bits(bb);
            if sum.is_nan() {
                let exp = (got >> 23) & 0xFF;
                let mant = got & 0x7F_FFFF;
                assert!(exp == 0xFF && mant != 0, "add({ab:#x},{bb:#x}) want NaN, got {got:#x}");
            } else {
                assert_eq!(got, u128::from(sum.to_bits()), "add({ab:#x},{bb:#x})");
            }
        };
        let structured: [u32; 14] = [
            0x0000_0000, 0x8000_0000, 0x3F80_0000, 0xBF80_0000, 0x4000_0000, 0x3F00_0000,
            0x7F80_0000, 0xFF80_0000, 0x7FC0_0000, 0x0080_0000, 0x0000_0001, 0x007F_FFFF,
            0x7F7F_FFFF, 0x4B80_0000,
        ];
        for &x in &structured {
            for &y in &structured {
                check(&mut a, x, y);
            }
        }
        let mut state: u64 = 0xb529_7a4d_1234_5678;
        for _ in 0..4000 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let x = (state & 0xFFFF_FFFF) as u32;
            let y = (state >> 32) as u32;
            check(&mut a, x, y);
        }
    }

    #[test]
    fn add_matches_native_f64() {
        let mut a = TermArena::new();
        let check = |a: &mut TermArena, ab: u64, bb: u64| {
            let at = a.bv_const(64, u128::from(ab)).unwrap();
            let bt = a.bv_const(64, u128::from(bb)).unwrap();
            let r = add(a, FloatFormat::F64, at, bt, RoundingMode::NearestEven).unwrap();
            let got = match eval(a, r, &Assignment::new()) {
                Ok(Value::Bv { value, .. }) => value,
                other => panic!("expected Bv, got {other:?}"),
            };
            let sum = f64::from_bits(ab) + f64::from_bits(bb);
            if sum.is_nan() {
                let exp = (got >> 52) & 0x7FF;
                let mant = got & 0xF_FFFF_FFFF_FFFF;
                assert!(exp == 0x7FF && mant != 0, "add64({ab:#x},{bb:#x}) want NaN");
            } else {
                assert_eq!(got, u128::from(sum.to_bits()), "add64({ab:#x},{bb:#x})");
            }
        };
        let structured: [u64; 10] = [
            0x0000_0000_0000_0000, 0x8000_0000_0000_0000, 0x3FF0_0000_0000_0000,
            0xBFF0_0000_0000_0000, 0x4000_0000_0000_0000, 0x7FF0_0000_0000_0000,
            0x7FF8_0000_0000_0000, 0x0010_0000_0000_0000, 0x0000_0000_0000_0001,
            0x7FEF_FFFF_FFFF_FFFF,
        ];
        for &x in &structured {
            for &y in &structured {
                check(&mut a, x, y);
            }
        }
        let mut state: u64 = 0x1357_9bdf_2468_ace0;
        for _ in 0..3000 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let x = state;
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            check(&mut a, x, state);
        }
    }

    #[test]
    fn mul_matches_native_f64() {
        let mut a = TermArena::new();
        let check = |a: &mut TermArena, ab: u64, bb: u64| {
            let at = a.bv_const(64, u128::from(ab)).unwrap();
            let bt = a.bv_const(64, u128::from(bb)).unwrap();
            let r = mul(a, FloatFormat::F64, at, bt, RoundingMode::NearestEven).unwrap();
            let got = match eval(a, r, &Assignment::new()) {
                Ok(Value::Bv { value, .. }) => value,
                other => panic!("expected Bv, got {other:?}"),
            };
            let prod = f64::from_bits(ab) * f64::from_bits(bb);
            if prod.is_nan() {
                let exp = (got >> 52) & 0x7FF;
                let mant = got & 0xF_FFFF_FFFF_FFFF;
                assert!(exp == 0x7FF && mant != 0, "mul64({ab:#x},{bb:#x}) want NaN, got {got:#x}");
            } else {
                assert_eq!(got, u128::from(prod.to_bits()), "mul64({ab:#x},{bb:#x})");
            }
        };

        let structured: [u64; 12] = [
            0x0000_0000_0000_0000, // +0
            0x8000_0000_0000_0000, // -0
            0x3FF0_0000_0000_0000, // 1.0
            0xBFF0_0000_0000_0000, // -1.0
            0x4000_0000_0000_0000, // 2.0
            0x3FE0_0000_0000_0000, // 0.5
            0x7FF0_0000_0000_0000, // +inf
            0x7FF8_0000_0000_0000, // NaN
            0x0010_0000_0000_0000, // smallest normal
            0x0000_0000_0000_0001, // smallest subnormal
            0x7FEF_FFFF_FFFF_FFFF, // f64::MAX
            0x4340_0000_0000_0000, // 2^53
        ];
        for &x in &structured {
            for &y in &structured {
                check(&mut a, x, y);
            }
        }
        let mut state: u64 = 0x243f_6a88_85a3_08d3;
        for _ in 0..3000 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let x = state;
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            check(&mut a, x, state);
        }
    }

    // Independent IEEE-remainder oracle by brute force over the integer quotient
    // (exact for a bounded quotient: the products and difference are exactly
    // representable). Picks the nearest n; ties to even n.
    #[allow(clippy::float_cmp)] // exact equality of the candidate magnitudes is intentional
    fn rem_oracle(xd: f64, yd: f64) -> f64 {
        let base = (xd / yd).floor();
        let mut best_r = f64::INFINITY;
        let mut i = -2i64;
        while i <= 2 {
            #[allow(clippy::cast_precision_loss)]
            let n = base + i as f64;
            let r = xd - yd * n;
            #[allow(clippy::cast_possible_truncation)]
            let n_even = (n as i64).rem_euclid(2) == 0;
            if r.abs() < best_r.abs() || (r.abs() == best_r.abs() && n_even) {
                best_r = r;
            }
            i += 1;
        }
        // IEEE: a zero remainder takes the sign of x (f64 subtraction loses it).
        if best_r == 0.0 {
            return 0.0_f64.copysign(xd);
        }
        best_r
    }

    #[test]
    fn rem_specials_and_ties() {
        let mut a = TermArena::new();
        // (x, y, expected) over both F32 and F64 for clean, format-independent values.
        let cases: [(f64, f64, f64); 7] = [
            (7.0, 2.0, -1.0), // 3.5 ties to even (4) -> 7-8
            (5.0, 2.0, 1.0),  // 2.5 ties to even (2) -> 5-4
            (3.0, 2.0, -1.0), // 1.5 ties to even (2) -> 3-4
            (1.0, 2.0, 1.0),  // 0.5 ties to even (0) -> 1-0
            (-7.0, 2.0, 1.0), // -3.5 ties to even (-4) -> -7+8
            (6.0, 3.0, 0.0),  // exact
            (5.5, 2.0, -0.5), // 2.75 -> 3 -> 5.5-6
        ];
        for (x, y, want) in cases {
            // F64
            let xt = a.bv_const(64, u128::from(f64::to_bits(x))).unwrap();
            let yt = a.bv_const(64, u128::from(f64::to_bits(y))).unwrap();
            let r = rem(&mut a, FloatFormat::F64, xt, yt).unwrap().unwrap();
            let got = match eval(&a, r, &Assignment::new()) {
                Ok(Value::Bv { value, .. }) => value,
                other => panic!("{other:?}"),
            };
            assert_eq!(got, u128::from(want.to_bits()), "rem64({x},{y}) want {want}");
            // F32
            #[allow(clippy::cast_possible_truncation)]
            let (xf, yf, wf) = (x as f32, y as f32, want as f32);
            let xt = a.bv_const(32, u128::from(xf.to_bits())).unwrap();
            let yt = a.bv_const(32, u128::from(yf.to_bits())).unwrap();
            let r = rem(&mut a, FloatFormat::F32, xt, yt).unwrap().unwrap();
            let got = match eval(&a, r, &Assignment::new()) {
                Ok(Value::Bv { value, .. }) => value,
                other => panic!("{other:?}"),
            };
            assert_eq!(got, u128::from(wf.to_bits()), "rem32({xf},{yf}) want {wf}");
        }

        // specials (F64): NaN when x infinite / y zero; x when y infinite; ±0 from ±0.
        let nan = |a: &mut TermArena, x: f64, y: f64| -> u128 {
            let xt = a.bv_const(64, u128::from(f64::to_bits(x))).unwrap();
            let yt = a.bv_const(64, u128::from(f64::to_bits(y))).unwrap();
            let r = rem(a, FloatFormat::F64, xt, yt).unwrap().unwrap();
            match eval(a, r, &Assignment::new()) {
                Ok(Value::Bv { value, .. }) => value,
                other => panic!("{other:?}"),
            }
        };
        assert!(f64::from_bits(nan(&mut a, f64::INFINITY, 2.0) as u64).is_nan(), "rem(inf,2)=NaN");
        assert!(f64::from_bits(nan(&mut a, 3.0, 0.0) as u64).is_nan(), "rem(3,0)=NaN");
        assert_eq!(nan(&mut a, 3.0, f64::INFINITY), u128::from(3.0f64.to_bits()), "rem(3,inf)=3");
        assert_eq!(nan(&mut a, 0.0, 3.0), u128::from(0.0f64.to_bits()), "rem(+0,3)=+0");
        assert_eq!(nan(&mut a, -0.0, 3.0), u128::from((-0.0f64).to_bits()), "rem(-0,3)=-0");
    }

    #[test]
    fn rem_matches_brute_force_f32() {
        let mut a = TermArena::new();
        let check = |a: &mut TermArena, xb: u32, yb: u32| {
            let xf = f32::from_bits(xb);
            let yf = f32::from_bits(yb);
            if !xf.is_finite() || !yf.is_finite() || yf == 0.0 {
                return;
            }
            let (xd, yd) = (f64::from(xf), f64::from(yf));
            // restrict to the bounded-quotient region where the oracle is exact
            if (xd / yd).abs() >= 60.0 {
                return;
            }
            let xt = a.bv_const(32, u128::from(xb)).unwrap();
            let yt = a.bv_const(32, u128::from(yb)).unwrap();
            let r = rem(a, FloatFormat::F32, xt, yt).unwrap().unwrap();
            let got = match eval(a, r, &Assignment::new()) {
                Ok(Value::Bv { value, .. }) => value,
                other => panic!("{other:?}"),
            };
            #[allow(clippy::cast_possible_truncation)]
            let want = (rem_oracle(xd, yd) as f32).to_bits();
            assert_eq!(got, u128::from(want), "rem({xf},{yf}) got {got:#x} want {want:#x}");
        };

        let structured: [u32; 12] = [
            0x3f80_0000, // 1.0
            0x4000_0000, // 2.0
            0x4040_0000, // 3.0
            0x40a0_0000, // 5.0
            0x40e0_0000, // 7.0
            0x40c0_0000, // 6.0
            0x3f00_0000, // 0.5
            0x40b0_0000, // 5.5
            0xc0e0_0000, // -7.0
            0x3fc0_0000, // 1.5
            0x4120_0000, // 10.0
            0x4248_0000, // 50.0
        ];
        for &x in &structured {
            for &y in &structured {
                check(&mut a, x, y);
            }
        }

        let mut state: u64 = 0x1234_5678_9abc_def0;
        for _ in 0..6000 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let x = (state & 0xFFFF_FFFF) as u32;
            let y = (state >> 32) as u32;
            check(&mut a, x, y);
        }
    }

    #[test]
    fn rem_bf16_matches_brute_force() {
        // bf16 ⊂ f32 (low 16 mantissa bits zero), so the remainder — itself a
        // bf16 value — is encoded independently as (r as f32).to_bits() >> 16.
        let mut a = TermArena::new();
        let bf16_to_f64 = |b: u16| f64::from(f32::from_bits(u32::from(b) << 16));
        let check = |a: &mut TermArena, xb: u16, yb: u16| {
            let (xd, yd) = (bf16_to_f64(xb), bf16_to_f64(yb));
            if !xd.is_finite() || !yd.is_finite() || yd == 0.0 || (xd / yd).abs() >= 60.0 {
                return;
            }
            let xt = a.bv_const(16, u128::from(xb)).unwrap();
            let yt = a.bv_const(16, u128::from(yb)).unwrap();
            let r = rem(a, FloatFormat::BF16, xt, yt).unwrap().unwrap();
            let got = match eval(a, r, &Assignment::new()) {
                Ok(Value::Bv { value, .. }) => value,
                other => panic!("{other:?}"),
            };
            #[allow(clippy::cast_possible_truncation)]
            let want = u128::from((rem_oracle(xd, yd) as f32).to_bits() >> 16);
            assert_eq!(got, want, "rem_bf16({xb:#x},{yb:#x}) got {got:#x} want {want:#x}");
        };
        let mut state: u64 = 0xfeed_face_dead_beef;
        for _ in 0..8000 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            check(&mut a, (state & 0xFFFF) as u16, ((state >> 16) & 0xFFFF) as u16);
        }
    }

    #[test]
    fn rem_f16_concrete_and_e4m3_none() {
        let mut a = TermArena::new();
        // F16 bit patterns: 1.0=0x3C00, -1.0=0xBC00, 2.0=0x4000, 3.0=0x4200,
        // 5.0=0x4500, 6.0=0x4600, 7.0=0x4700, 0.0=0x0000.
        let cases: [(u16, u16, u16); 3] = [
            (0x4700, 0x4000, 0xBC00), // rem(7,2) = -1
            (0x4500, 0x4000, 0x3C00), // rem(5,2) = 1
            (0x4600, 0x4200, 0x0000), // rem(6,3) = 0
        ];
        for (xb, yb, want) in cases {
            let xt = a.bv_const(16, u128::from(xb)).unwrap();
            let yt = a.bv_const(16, u128::from(yb)).unwrap();
            let r = rem(&mut a, FloatFormat::F16, xt, yt).unwrap().unwrap();
            let got = match eval(&a, r, &Assignment::new()) {
                Ok(Value::Bv { value, .. }) => value,
                other => panic!("{other:?}"),
            };
            assert_eq!(got, u128::from(want), "rem_f16({xb:#x},{yb:#x})");
        }
        // The non-IEEE OCP formats are not folded (no remainder semantics).
        let xt = a.bv_const(8, 0x40).unwrap();
        let yt = a.bv_const(8, 0x38).unwrap();
        assert!(rem(&mut a, FloatFormat::FP8_E4M3, xt, yt).unwrap().is_none(), "E4M3 not folded");
    }

    #[test]
    fn rem_sym_matches_fold_f16() {
        // The symbolic bit-blaster (built over constants, then evaluated) must
        // agree with the trusted constant fold across the F16 space.
        let mut a = TermArena::new();
        let is_nan_bits = |b: u128| (b >> 10) & 0x1F == 0x1F && (b & 0x3FF) != 0;
        let check = |a: &mut TermArena, xb: u16, yb: u16| {
            let xt = a.bv_const(16, u128::from(xb)).unwrap();
            let yt = a.bv_const(16, u128::from(yb)).unwrap();
            let want = match rem(a, FloatFormat::F16, xt, yt).unwrap() {
                Some(t) => match eval(a, t, &Assignment::new()) {
                    Ok(Value::Bv { value, .. }) => value,
                    other => panic!("{other:?}"),
                },
                None => panic!("fold should cover F16"),
            };
            let sym = rem_sym(a, FloatFormat::F16, xt, yt).unwrap();
            let got = match eval(a, sym, &Assignment::new()) {
                Ok(Value::Bv { value, .. }) => value,
                other => panic!("{other:?}"),
            };
            if is_nan_bits(want) {
                assert!(is_nan_bits(got), "rem_sym({xb:#x},{yb:#x}) want NaN, got {got:#x}");
            } else {
                assert_eq!(got, want, "rem_sym({xb:#x},{yb:#x}) got {got:#x} want {want:#x}");
            }
        };

        // structured: ±0, ±1, ±2, 0.5, 1.5, smallest normal/subnormals, max, ∞, NaN.
        let structured: [u16; 16] = [
            0x0000, 0x8000, 0x3C00, 0xBC00, 0x4000, 0xC000, 0x3800, 0x3E00, 0x0400,
            0x0001, 0x03FF, 0x7BFF, 0x7C00, 0xFC00, 0x7E00, 0x4900,
        ];
        for &x in &structured {
            for &y in &structured {
                check(&mut a, x, y);
            }
        }

        let mut state: u64 = 0x0bad_c0de_1234_9999;
        for _ in 0..20000 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            check(&mut a, (state & 0xFFFF) as u16, ((state >> 16) & 0xFFFF) as u16);
        }
    }

    #[test]
    fn fma_matches_native_f32() {
        // Symbolic fma (built over constants, evaluated) must equal native
        // f32::mul_add — the correctly-rounded fused multiply-add.
        let mut a = TermArena::new();
        let check = |a: &mut TermArena, xb: u32, yb: u32, zb: u32| {
            let xt = a.bv_const(32, u128::from(xb)).unwrap();
            let yt = a.bv_const(32, u128::from(yb)).unwrap();
            let zt = a.bv_const(32, u128::from(zb)).unwrap();
            let r = fma(a, FloatFormat::F32, xt, yt, zt, RoundingMode::NearestEven).unwrap();
            let got = match eval(a, r, &Assignment::new()) {
                Ok(Value::Bv { value, .. }) => value,
                other => panic!("{other:?}"),
            };
            let want = f32::from_bits(xb).mul_add(f32::from_bits(yb), f32::from_bits(zb));
            if want.is_nan() {
                let exp = (got >> 23) & 0xFF;
                let mant = got & 0x7F_FFFF;
                assert!(exp == 0xFF && mant != 0, "fma({xb:#x},{yb:#x},{zb:#x}) want NaN, got {got:#x}");
            } else {
                assert_eq!(got, u128::from(want.to_bits()), "fma({xb:#x},{yb:#x},{zb:#x})");
            }
        };
        let structured: [u32; 12] = [
            0x0000_0000, 0x8000_0000, 0x3f80_0000, 0xbf80_0000, 0x4000_0000, 0x3f00_0000,
            0x7f80_0000, 0xff80_0000, 0x7fc0_0000, 0x0080_0000, 0x0000_0001, 0x4248_0000,
        ];
        for &x in &structured {
            for &y in &structured {
                for &z in &structured {
                    check(&mut a, x, y, z);
                }
            }
        }
        let mut state: u64 = 0xfa11_3a5e_0bad_1dea;
        for _ in 0..6000 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let x = (state & 0xFFFF_FFFF) as u32;
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let y = (state & 0xFFFF_FFFF) as u32;
            let z = (state >> 32) as u32;
            check(&mut a, x, y, z);
        }
    }

    #[test]
    fn sub_matches_native_f32() {
        // Symbolic fp.sub must equal native f32 subtraction (= a + (-b)).
        let mut a = TermArena::new();
        let check = |a: &mut TermArena, xb: u32, yb: u32| {
            let xt = a.bv_const(32, u128::from(xb)).unwrap();
            let yt = a.bv_const(32, u128::from(yb)).unwrap();
            let r = sub(a, FloatFormat::F32, xt, yt, RoundingMode::NearestEven).unwrap();
            let got = match eval(a, r, &Assignment::new()) {
                Ok(Value::Bv { value, .. }) => value,
                other => panic!("{other:?}"),
            };
            let want = f32::from_bits(xb) - f32::from_bits(yb);
            if want.is_nan() {
                let exp = (got >> 23) & 0xFF;
                let mant = got & 0x7F_FFFF;
                assert!(exp == 0xFF && mant != 0, "sub({xb:#x},{yb:#x}) want NaN, got {got:#x}");
            } else {
                assert_eq!(got, u128::from(want.to_bits()), "sub({xb:#x},{yb:#x})");
            }
        };
        let structured: [u32; 10] = [
            0x0000_0000, 0x8000_0000, 0x3f80_0000, 0xbf80_0000, 0x4000_0000, 0x7f80_0000,
            0xff80_0000, 0x7fc0_0000, 0x0080_0000, 0x0000_0001,
        ];
        for &x in &structured {
            for &y in &structured {
                check(&mut a, x, y);
            }
        }
        let mut state: u64 = 0x5b50_0bad_cafe_1234;
        for _ in 0..4000 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            check(&mut a, (state & 0xFFFF_FFFF) as u32, (state >> 32) as u32);
        }
    }

    #[test]
    fn fma_f16_exact_cases() {
        // Exact (no rounding) f16 cases: a*b + c with small integer values.
        // 2.0=0x4000, 3.0=0x4200, 1.0=0x3C00, 0.5=0x3800, 7.0=0x4700,
        // 3.5=0x4300, 1.5=0x3E00.
        let mut a = TermArena::new();
        let check = |a: &mut TermArena, xb: u16, yb: u16, zb: u16, want: u16| {
            let xt = a.bv_const(16, u128::from(xb)).unwrap();
            let yt = a.bv_const(16, u128::from(yb)).unwrap();
            let zt = a.bv_const(16, u128::from(zb)).unwrap();
            let r = fma(a, FloatFormat::F16, xt, yt, zt, RoundingMode::NearestEven).unwrap();
            let got = match eval(a, r, &Assignment::new()) {
                Ok(Value::Bv { value, .. }) => value,
                other => panic!("{other:?}"),
            };
            assert_eq!(got, u128::from(want), "fma_f16({xb:#x},{yb:#x},{zb:#x})");
        };
        check(&mut a, 0x4000, 0x4200, 0x3C00, 0x4700); // 2*3 + 1 = 7
        check(&mut a, 0x3E00, 0x4000, 0x3800, 0x4300); // 1.5*2 + 0.5 = 3.5
        check(&mut a, 0x4000, 0x4000, 0x0000, 0x4400); // 2*2 + 0 = 4 (0x4400)
        check(&mut a, 0x3C00, 0x3C00, 0xBC00, 0x0000); // 1*1 + (-1) = 0
    }

    #[test]
    fn rem_sym_rejects_f64() {
        // F64 (e_span 2045) is out of range for both the scaled and iterative paths.
        let mut a = TermArena::new();
        let xt = a.bv_const(64, 0).unwrap();
        let yt = a.bv_const(64, 0).unwrap();
        assert!(rem_sym(&mut a, FloatFormat::F64, xt, yt).is_err(), "F64 rejected");
    }

    #[test]
    fn conversions_fold_for_f16() {
        // to_ubv / to_sbv / round_to_integral now fold for F16 (any IEEE format),
        // not just F32/F64. F16: 3.5=0x4300, 2.5=0x4100, -3.5=0xC300.
        let mut a = TermArena::new();
        let bits16 = |a: &mut TermArena, b: u16| a.bv_const(16, u128::from(b)).unwrap();
        let eval_bv = |a: &TermArena, t| match eval(a, t, &Assignment::new()) {
            Ok(Value::Bv { value, .. }) => value,
            other => panic!("{other:?}"),
        };
        // to_ubv(3.5, RTZ, 8) = 3
        let x = bits16(&mut a, 0x4300);
        let r = to_ubv(&mut a, FloatFormat::F16, RoundingMode::TowardZero, x, 8).unwrap().unwrap();
        assert_eq!(eval_bv(&a, r), 3);
        // to_ubv(2.5, NearestEven, 8) = 2 (ties to even)
        let x = bits16(&mut a, 0x4100);
        let r = to_ubv(&mut a, FloatFormat::F16, RoundingMode::NearestEven, x, 8).unwrap().unwrap();
        assert_eq!(eval_bv(&a, r), 2);
        // to_sbv(-3.5, RTZ, 8) = -3 = 0xFD
        let x = bits16(&mut a, 0xC300);
        let r = to_sbv(&mut a, FloatFormat::F16, RoundingMode::TowardZero, x, 8).unwrap().unwrap();
        assert_eq!(eval_bv(&a, r), 0xFD);
        // round_to_integral(3.5, RTZ) = 3.0 = 0x4200
        let x = bits16(&mut a, 0x4300);
        let r = round_to_integral(&mut a, FloatFormat::F16, RoundingMode::TowardZero, x).unwrap().unwrap();
        assert_eq!(eval_bv(&a, r), 0x4200);
        // round_to_integral(2.5, NearestEven) = 2.0 = 0x4000
        let x = bits16(&mut a, 0x4100);
        let r = round_to_integral(&mut a, FloatFormat::F16, RoundingMode::NearestEven, x).unwrap().unwrap();
        assert_eq!(eval_bv(&a, r), 0x4000);
        // BF16 too: to_ubv(2.0, RTZ, 8); 2.0 in bf16 = 0x4000.
        let x = a.bv_const(16, 0x4000).unwrap();
        let r = to_ubv(&mut a, FloatFormat::BF16, RoundingMode::TowardZero, x, 8).unwrap().unwrap();
        assert_eq!(eval_bv(&a, r), 2);
    }

    #[test]
    fn rem_sym_iterative_matches_fold_f32() {
        // The iterative wide-exponent path (F32) must agree with the trusted
        // constant fold across structured edges and a random sweep.
        let mut a = TermArena::new();
        let is_nan_bits = |b: u128| (b >> 23) & 0xFF == 0xFF && (b & 0x7F_FFFF) != 0;
        let check = |a: &mut TermArena, xb: u32, yb: u32| {
            let xt = a.bv_const(32, u128::from(xb)).unwrap();
            let yt = a.bv_const(32, u128::from(yb)).unwrap();
            let want = match rem(a, FloatFormat::F32, xt, yt).unwrap() {
                Some(t) => match eval(a, t, &Assignment::new()) {
                    Ok(Value::Bv { value, .. }) => value,
                    other => panic!("{other:?}"),
                },
                None => panic!("fold should cover F32"),
            };
            let sym = rem_sym(a, FloatFormat::F32, xt, yt).unwrap();
            let got = match eval(a, sym, &Assignment::new()) {
                Ok(Value::Bv { value, .. }) => value,
                other => panic!("{other:?}"),
            };
            if is_nan_bits(want) {
                assert!(is_nan_bits(got), "rem_f32({xb:#x},{yb:#x}) want NaN, got {got:#x}");
            } else {
                assert_eq!(got, want, "rem_f32({xb:#x},{yb:#x}) got {got:#x} want {want:#x}");
            }
        };
        let structured: [u32; 14] = [
            0x0000_0000, 0x8000_0000, 0x3f80_0000, 0xbf80_0000, 0x4000_0000, 0x3f00_0000,
            0x4070_0000, 0x40e0_0000, 0x7f80_0000, 0xff80_0000, 0x7fc0_0000, 0x0080_0000,
            0x0000_0001, 0x4248_0000,
        ];
        for &x in &structured {
            for &y in &structured {
                check(&mut a, x, y);
            }
        }
        let mut state: u64 = 0x3c0f_fee5_1234_abcd;
        for _ in 0..3000 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            check(&mut a, (state & 0xFFFF_FFFF) as u32, (state >> 32) as u32);
        }
    }
}
