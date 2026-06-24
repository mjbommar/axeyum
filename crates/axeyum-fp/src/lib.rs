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

use axeyum_ir::{IrError, Rational, Sort, TermArena, TermId, TermNode};

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
    /// IEEE 754 binary128 (quadruple precision): 15 exponent bits, 113
    /// significand bits. Its arithmetic intermediates exceed `u128`, so it runs
    /// through the wide bit-vector path and is validated against `rustc_apfloat`'s
    /// `ieee::Quad` (ADR-0028), there being no native `f128` on stable Rust.
    pub const F128: Self = Self {
        exp_bits: 15,
        sig_bits: 113,
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
        let s = if (bits >> (self.width() - 1)) & 1 == 1 {
            -1.0
        } else {
            1.0
        };
        let exp_mask = (1u128 << self.exp_bits) - 1;
        let exp = (bits >> frac_bits) & exp_mask;
        let frac = bits & ((1u128 << frac_bits) - 1);
        let exp_bias = (1i64 << (self.exp_bits - 1)) - 1;
        if exp == exp_mask {
            return if frac != 0 {
                f64::NAN
            } else {
                s * f64::INFINITY
            };
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
        // An operand may be a plain `BitVec` (the builders' internal
        // representation) or a `Float` of this format (ADR-0026); both carry the
        // `width()` bits this format operates on.
        let found = arena.sort_of(x);
        let ok = match found {
            Sort::BitVec(w) => w == self.width(),
            Sort::Float { exp, sig } => exp == self.exp_bits && sig == self.sig_bits,
            _ => false,
        };
        if ok {
            Ok(())
        } else {
            Err(IrError::SortMismatch {
                expected: "BitVec or Float matching the float format width",
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
            1 => (base, 2),     // *0.5
            2 => (base, 1),     // *1
            _ => (base * 2, 1), // exp==3 -> *2
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
pub fn lt(
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
pub fn gt(
    arena: &mut TermArena,
    fmt: FloatFormat,
    x: TermId,
    y: TermId,
) -> Result<TermId, IrError> {
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
/// For zeros of **opposite sign** — where SMT-LIB leaves the result unspecified
/// (it may be `+0` OR `−0`, and the choice may differ between argument orders) —
/// the result's sign is a **fresh free Boolean, one per application** (see
/// `select_by_order`): a faithful nondeterministic-but-consistent encoding,
/// never a wrong `unsat`.
pub fn min(
    arena: &mut TermArena,
    fmt: FloatFormat,
    x: TermId,
    y: TermId,
) -> Result<TermId, IrError> {
    select_by_order(arena, fmt, x, y, true)
}

/// `fp.max(x, y)`: the larger operand. NaN propagates the other operand; the
/// result is one of the inputs unchanged (exact, no rounding).
///
/// On **opposite-sign zeros** SMT-LIB leaves the sign unspecified (it may be
/// `+0` OR `−0`, order-dependent), so the result's sign is a **fresh free
/// Boolean, one per application** (see `select_by_order`) — consistent for the
/// same syntactic term, free to differ across distinct ones, never a wrong
/// `unsat`.
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
    if w <= 128 {
        let mask = if w == 128 {
            u128::MAX
        } else {
            (1u128 << w) - 1
        };
        let bits = (i128::from(val) as u128) & mask;
        return arena.bv_const(w, bits);
    }
    // Width exceeds the `u128` payload: `bv_const`'s wide path zero-fills the
    // high limbs, which is wrong for negative values (their high bits must be
    // ones). Any `i64` fits in 128 two's-complement bits, so build the constant
    // at 128 bits — where the cast carries the correct sign — then sign-extend
    // to `w`, replicating the sign bit into the high limbs.
    let base = arena.bv_const(128, i128::from(val) as u128)?;
    arena.sign_ext(w - 128, base)
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
#[allow(
    clippy::similar_names,
    clippy::many_single_char_names,
    clippy::too_many_arguments
)]
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
/// **Format support.** The intermediate is `2·sig_bits + 3` bits. **F16/F32/F64**
/// (≤ 109 bits) use the `u128` path; **F128** (229 bits) runs through the wide
/// bit-vector path, validated against `rustc_apfloat`'s quad (ADR-0028). Other
/// wide formats return [`IrError::InvalidWidth`].
///
/// # Errors
///
/// Returns [`IrError::InvalidWidth`] for a wide non-F128 format,
/// [`IrError::SortMismatch`] if an operand is not a `BitVec` of
/// the format width, or [`IrError`] from the builders.
#[allow(clippy::similar_names, clippy::many_single_char_names)]
pub fn mul(
    arena: &mut TermArena,
    fmt: FloatFormat,
    a: TermId,
    b: TermId,
    mode: RoundingMode,
) -> Result<TermId, IrError> {
    if !arithmetic_format_supported(fmt) {
        return Err(IrError::Unsupported("fp.mul: unvalidated format"));
    }
    fmt.check(arena, a)?;
    fmt.check(arena, b)?;
    let (eb, sb) = (fmt.exp_bits, fmt.sig_bits);
    let total = fmt.width();
    // The significand product is exactly 2·sb bits and `mul` never needs a
    // normalizing left shift (a product of significands has its leading bit at
    // index ≥ sb−1 whenever the result is normal), so `pack_value` only ever
    // rounds *down* — 2·sb + 3 bits suffice, which fits F16/F32/F64 in 128 bits.
    // F128 (229 bits) runs through the wide path, validated against `Quad`
    // (ADR-0028); other wide formats stay `unsupported` (sound) pending a sweep.
    // `pack_value`'s exponent arithmetic also runs at this width, so it must hold
    // the biased exponent (`max ~ 2^eb`): grow to `eb + 4` for formats whose
    // exponent is large relative to the significand (a no-op when `eb < 2·sb`).
    let w = (2 * sb + 3).max(eb + 4);
    if w > 128 && fmt != FloatFormat::F128 {
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

/// Whether the symbolic arithmetic circuits (`add`/`sub`/`mul`/`div`/`sqrt`/
/// `fma`) are **differentially validated** for this format, and may therefore be
/// built. Validation is the soundness contract for FP here (ADR-0023/0028): there
/// is no first-class FP op, so the evaluator runs the very circuit the solver
/// does and model replay cannot catch a wrong circuit — only an oracle can. An
/// *unvalidated* format must therefore be refused (`unsupported`), never silently
/// computed. Validated today: the small IEEE formats (`eb ≤ 10`, `sb ≤ 11` —
/// F16/BF16/TF32/FP8 and the tiny quantifier formats) against native `f64` and
/// the exact big-integer fma oracle, plus **F32**/**F64** (native) and **F128**
/// (`rustc_apfloat` and the sqrt correct-rounding oracle).
fn arithmetic_format_supported(fmt: FloatFormat) -> bool {
    fmt.is_ieee()
        && ((fmt.exp_bits <= 10 && fmt.sig_bits <= 11)
            || fmt == FloatFormat::F32
            || fmt == FloatFormat::F64
            || fmt == FloatFormat::F128)
}

/// Normalizes a (possibly subnormal) significand so its leading one sits at bit
/// `sb-1` (a full `sb`-bit significand), decreasing the LSB exponent to match —
/// the `value = sig·2^e` product is preserved. A zero significand (the operand
/// is ±0) is left zero; callers mux ±0 out via the zero special case. This makes
/// algorithms whose precision depends on a fully-populated significand (integer
/// division in [`div`], the integer square root in [`sqrt`]) correct for
/// subnormal operands, not just normal ones.
fn normalize_significand(
    arena: &mut TermArena,
    w: u32,
    sb: u32,
    sig: TermId,
    e: TermId,
) -> Result<(TermId, TermId), IrError> {
    let lz = count_leading_zeros(arena, sig)?;
    let wsb = arena.bv_const(w, u128::from(w - sb))?; // leading zeros of a normal sig
    let norm = arena.bv_sub(lz, wsb)?; // extra leading zeros to shift away
    let sig_n = arena.bv_shl(sig, norm)?;
    let e_n = arena.bv_sub(e, norm)?;
    Ok((sig_n, e_n))
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
/// Works for **F16/F32/F64** (working width ≤ 128, validated against native
/// `f32`/`f64` `sqrt`) and **F128** (234 bits, via the wide path). F128 has no
/// native or `rustc_apfloat` sqrt oracle, so it is validated against an exact
/// correct-rounding checker (the rounding-interval property over `WideUint`
/// integers) that is itself validated against native `f64::sqrt` — ADR-0028.
///
/// # Errors
///
/// Returns [`IrError::InvalidWidth`] for a wide non-F128 format,
/// [`IrError::SortMismatch`] for a mis-sized operand, or [`IrError`] from builders.
#[allow(clippy::similar_names, clippy::many_single_char_names)]
pub fn sqrt(
    arena: &mut TermArena,
    fmt: FloatFormat,
    x: TermId,
    mode: RoundingMode,
) -> Result<TermId, IrError> {
    if !arithmetic_format_supported(fmt) {
        return Err(IrError::Unsupported("fp.sqrt: unvalidated format"));
    }
    fmt.check(arena, x)?;
    let (eb, sb) = (fmt.exp_bits, fmt.sig_bits);
    let total = fmt.width();
    let shift = (sb + 1).div_ceil(2) + 3; // result fractional bits
    // `eb + 4` headroom so `pack_value`'s exponent arithmetic doesn't overflow
    // for formats whose exponent is large relative to the significand.
    let mut w = ((sb + 1) + 2 * shift).max(eb + 4);
    if w % 2 != 0 {
        w += 1; // isqrt needs an even width
    }
    // F16/F32/F64 keep `w ≤ 128`; F128 (234 bits) runs through the wide path,
    // validated against an exact correct-rounding oracle (ADR-0028 —
    // `rustc_apfloat` has no sqrt, so the oracle checks the rounding-interval
    // property and is itself validated against native `f64::sqrt`). Other wide
    // formats stay `unsupported` (sound).
    if w > 128 && fmt != FloatFormat::F128 {
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
/// 128 bits, [`IrError::SortMismatch`] for a mis-sized operand, or
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
    if w > 128 {
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

/// `((_ to_fp eb sb) RM bv)` reading `x` as an **unsigned** integer: round its
/// value to the nearest `dst`-format float under `mode`. The integer `n` is the
/// value `n · 2⁰`, so its magnitude is the significand and the exponent is 0;
/// [`pack_value`] does the rounding. Exact `0` maps to `+0`. (z3's `to_fp` over a
/// bit-vector source; the unsigned reading is `to_fp_unsigned`.)
///
/// # Errors
///
/// [`IrError::SortMismatch`] if `x` is not a bit-vector, [`IrError::InvalidWidth`]
/// if the working width exceeds 128, or builder errors.
pub fn from_ubv(
    arena: &mut TermArena,
    dst: FloatFormat,
    mode: RoundingMode,
    x: TermId,
) -> Result<TermId, IrError> {
    let Sort::BitVec(wi) = arena.sort_of(x) else {
        return Err(IrError::SortMismatch {
            expected: "BitVec",
            found: arena.sort_of(x),
        });
    };
    from_int_bits(arena, dst, mode, x, wi, false)
}

/// `((_ to_fp eb sb) RM bv)` reading `x` as a **signed (two's-complement)**
/// integer. Like [`from_ubv`] but the sign comes from the top bit and the
/// magnitude is `|x|` (the two's-complement negation read unsigned, which is
/// correct even for `INT_MIN`).
///
/// # Errors
///
/// As [`from_ubv`].
pub fn from_sbv(
    arena: &mut TermArena,
    dst: FloatFormat,
    mode: RoundingMode,
    x: TermId,
) -> Result<TermId, IrError> {
    let Sort::BitVec(wi) = arena.sort_of(x) else {
        return Err(IrError::SortMismatch {
            expected: "BitVec",
            found: arena.sort_of(x),
        });
    };
    from_int_bits(arena, dst, mode, x, wi, true)
}

/// Shared integer→float core: round the `wi`-bit integer `x` (signed or unsigned)
/// to the `dst` format under `mode`.
fn from_int_bits(
    arena: &mut TermArena,
    dst: FloatFormat,
    mode: RoundingMode,
    x: TermId,
    wi: u32,
    signed: bool,
) -> Result<TermId, IrError> {
    let w = wi.max(dst.sig_bits) + 4;
    if w > 128 {
        return Err(IrError::InvalidWidth(w));
    }
    let total = dst.width();
    // Sign + `wi`-bit magnitude. For a signed source the magnitude is the
    // two's-complement negation read as unsigned (|x|, correct for `INT_MIN` too).
    let (sign, mag_wi) = if signed {
        let msb = arena.extract(wi - 1, wi - 1, x)?;
        let one1 = arena.bv_const(1, 1)?;
        let sign = arena.eq(msb, one1)?;
        let neg = arena.bv_neg(x)?;
        let mag = arena.ite(sign, neg, x)?;
        (sign, mag)
    } else {
        (arena.bool_const(false), x)
    };
    // Significand m = magnitude (value · 2⁰), exponent e = 0; pack_value rounds.
    let m = arena.zero_ext(w - wi, mag_wi)?;
    let e = arena.bv_const(w, 0)?;
    let packed = pack_value(arena, dst.exp_bits, dst.sig_bits, sign, m, e, mode)?;
    // Exact zero → +0 (all-zero bits): bypass the nonzero-significand pack path.
    let zero_wi = arena.bv_const(wi, 0)?;
    let is_zero = arena.eq(x, zero_wi)?;
    let pos_zero = arena.bv_const(total, 0)?;
    arena.ite(is_zero, pos_zero, packed)
}

/// `((_ to_fp eb sb) RM r)` for a **rational constant** `r` (z3's `to_fp` from a
/// `Real`). When `r` is **dyadic** — its reduced denominator is a power of two —
/// the value is exactly `|num|·2^(−k)` with `den == 2^k`, so the integer magnitude
/// is the significand and `−k` the exponent; [`pack_value`] does the rounding
/// (including subnormal/overflow) under `mode`, reusing the validated packer. `0`
/// maps to `+0`.
///
/// Returns `Ok(None)` for a **non-dyadic** `r` (e.g. `1/3`, `1/10`): correctly
/// rounding a general rational needs wider-than-`i128` arithmetic and is a planned
/// follow-up (the f64 bridge would double-round for sub-`f64` formats, so it is not
/// used). `Ok(None)` is also returned if the working width would exceed 128 bits.
/// `None` is a *decline*, never a wrong answer — every `Some` value is exact-then-
/// `pack_value`-rounded.
///
/// # Errors
///
/// Builder [`IrError`]s (well-formed input does not fail).
pub fn from_real(
    arena: &mut TermArena,
    dst: FloatFormat,
    mode: RoundingMode,
    r: Rational,
) -> Result<Option<TermId>, IrError> {
    let (eb, sb) = (dst.exp_bits, dst.sig_bits);
    let num = r.numerator();
    let den = r.denominator();
    let bits = round_rational_to_format(eb, sb, num, den, mode).or_else(|| {
        // Non-dyadic (or out of the exact-f64 window): round the exact rational by
        // pure-integer arithmetic under `mode` — no double-rounding.
        if num != 0 && den > 0 {
            round_rational_rne(
                eb,
                sb,
                mode,
                num < 0,
                num.unsigned_abs(),
                den.unsigned_abs(),
            )
        } else {
            None
        }
    });
    match bits {
        Some(bits) => Ok(Some(arena.bv_const(dst.width(), bits)?)),
        None => Ok(None),
    }
}

/// Symbolic `fp.div` (round-nearest-ties-to-even): the IEEE 754 division
/// bit-blaster. Computes the quotient of the significands to `sb + 3` fractional
/// bits via `bv_udiv` (with the `bv_urem` remainder folded into a sticky bit),
/// subtracts exponents, rounds via [`pack_value`], and muxes the special cases
/// (NaN for `0/0` and `∞/∞`, `∞` for `x/0` and `∞/finite`, `0` for `finite/∞`).
/// A pure bit-vector formula; solves and replays on the existing path.
///
/// Works for **F16/F32/F64** (the `2·sb + 5`-bit intermediate fits 128 bits) and
/// **F128** (231 bits, via the wide path). Validated, not proven: differentially
/// validated against native `f32`/`f64` division and `rustc_apfloat`'s quad
/// (ADR-0028).
///
/// # Errors
///
/// Returns [`IrError::InvalidWidth`] for a wide non-F128 format,
/// [`IrError::SortMismatch`] for a mis-sized operand, or [`IrError`] from builders.
#[allow(clippy::similar_names, clippy::many_single_char_names)]
pub fn div(
    arena: &mut TermArena,
    fmt: FloatFormat,
    a: TermId,
    b: TermId,
    mode: RoundingMode,
) -> Result<TermId, IrError> {
    if !arithmetic_format_supported(fmt) {
        return Err(IrError::Unsupported("fp.div: unvalidated format"));
    }
    fmt.check(arena, a)?;
    fmt.check(arena, b)?;
    let (eb, sb) = (fmt.exp_bits, fmt.sig_bits);
    let total = fmt.width();
    // `eb + 4` headroom so `pack_value`'s exponent arithmetic doesn't overflow
    // for formats whose exponent is large relative to the significand (a no-op
    // when `eb < 2·sb`, i.e. all standard formats).
    let w = (2 * sb + 5).max(eb + 4);
    // F16/F32/F64 fit `u128`; F128 (231 bits) runs through the wide path,
    // validated against `Quad` (ADR-0028). Other wide formats stay `unsupported`.
    if w > 128 && fmt != FloatFormat::F128 {
        return Err(IrError::InvalidWidth(w));
    }
    let frac = sb + 3; // quotient fractional bits

    let one1 = arena.bv_const(1, 1)?;
    let (sa, sig_a0, e_a0) = unpack_operand(arena, fmt, w, a)?;
    let (sbit, sig_b0, e_b0) = unpack_operand(arena, fmt, w, b)?;
    // Normalize subnormal operands to a full `sb`-bit significand so the integer
    // division below always yields the same precision (otherwise a subnormal
    // dividend under-produces quotient bits and the sticky/round bit is wrong).
    let (sig_a, e_a) = normalize_significand(arena, w, sb, sig_a0, e_a0)?;
    let (sig_b, e_b) = normalize_significand(arena, w, sb, sig_b0, e_b0)?;

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
/// **F16/F32/F64** in 128 bits; **F128** (231 bits) runs through the wide path.
///
/// This is a validated — not formally proven — bit-blaster: differentially
/// validated against native `f32`/`f64` addition and `rustc_apfloat`'s quad
/// (ADR-0028) in tests.
///
/// # Errors
///
/// Returns [`IrError::InvalidWidth`] for a wide non-F128 format,
/// [`IrError::SortMismatch`] for a mis-sized operand, or
/// [`IrError`] from the builders.
#[allow(clippy::similar_names, clippy::many_single_char_names)]
pub fn add(
    arena: &mut TermArena,
    fmt: FloatFormat,
    a: TermId,
    b: TermId,
    mode: RoundingMode,
) -> Result<TermId, IrError> {
    if !arithmetic_format_supported(fmt) {
        return Err(IrError::Unsupported("fp.add: unvalidated format"));
    }
    fmt.check(arena, a)?;
    fmt.check(arena, b)?;
    let (eb, sb) = (fmt.exp_bits, fmt.sig_bits);
    let total = fmt.width();
    // `eb + 4` headroom so `pack_value`'s exponent arithmetic doesn't overflow
    // for formats whose exponent is large relative to the significand (a no-op
    // when `eb < 2·sb`, i.e. all standard formats).
    let w = (2 * sb + 5).max(eb + 4);
    // F16/F32/F64 fit `u128`; F128 (231 bits) runs through the wide path,
    // validated against `Quad` (ADR-0028). Other wide formats stay `unsupported`.
    if w > 128 && fmt != FloatFormat::F128 {
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
/// `3·sb + 5`; **F16/F32** fit the 128-bit `u128` path, while **F64** (164 bits)
/// and **F128** (344 bits) run through the wide bit-vector path. Other wide
/// formats return `InvalidWidth` — they have no oracle to validate the circuit.
///
/// Special cases per IEEE: NaN if any operand is NaN, if `a·b` is `0·∞`, or if
/// `a·b` and `c` are infinities of opposite sign; otherwise the infinity of an
/// infinite product or addend. Validated against native `f32::mul_add`/
/// `f64::mul_add` and `rustc_apfloat`'s quad fma (ADR-0028) over a wide sweep.
///
/// # Errors
///
/// Returns [`IrError::InvalidWidth`] for formats wider than F64 other than F128,
/// [`IrError::SortMismatch`] for a mis-sized operand, or [`IrError`] from the
/// builders.
#[allow(
    clippy::similar_names,
    clippy::many_single_char_names,
    clippy::too_many_lines
)]
pub fn fma(
    arena: &mut TermArena,
    fmt: FloatFormat,
    a: TermId,
    b: TermId,
    c: TermId,
    mode: RoundingMode,
) -> Result<TermId, IrError> {
    if !arithmetic_format_supported(fmt) {
        return Err(IrError::Unsupported("fp.fma: unvalidated format"));
    }
    fmt.check(arena, a)?;
    fmt.check(arena, b)?;
    fmt.check(arena, c)?;
    let (eb, sb) = (fmt.exp_bits, fmt.sig_bits);
    let total = fmt.width();
    // Constant operands under round-nearest-even fold via native `mul_add` (a
    // single, correctly-rounded fused op — the ADR-0023 "fold constants via native
    // arithmetic" basis). This decides constant F64 `fp.fma`.
    if mode == RoundingMode::NearestEven
        && let Some(folded) = fma_rne(arena, fmt, a, b, c)?
    {
        return Ok(folded);
    }
    // `eb + 4` headroom so `pack_value`'s exponent arithmetic doesn't overflow
    // for formats whose exponent is large relative to the significand.
    let w = (3 * sb + 5).max(eb + 4);
    // The symbolic FMA circuit runs through the wide bit-vector path for
    // intermediates that exceed `u128` (F64 needs 164 bits, F128 needs 344).
    // There is no first-class FP op, so the evaluator evaluates this very
    // circuit — a wrong circuit is NOT caught by model replay; the only assurance
    // is differential validation against an independent oracle (ADR-0028). The
    // wide path is therefore enabled only for formats with a validated sweep:
    // F64 against native `f64::mul_add` (`symbolic_f64_fma_matches_native`) and
    // F128 against `rustc_apfloat`'s `ieee::Quad` (`symbolic_f128_fma_matches_apfloat`).
    // Other wide formats stay `unsupported` (sound) pending their own sweep.
    if w > 128 && fmt != FloatFormat::F64 && fmt != FloatFormat::F128 {
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
    let (Some(xv), Some(yv), Some(zv)) = (
        const_bits(arena, x),
        const_bits(arena, y),
        const_bits(arena, z),
    ) else {
        return Ok(None);
    };
    let bits = if fmt == FloatFormat::F32 {
        let r =
            f32::from_bits(low32(xv)).mul_add(f32::from_bits(low32(yv)), f32::from_bits(low32(zv)));
        u128::from(r.to_bits())
    } else if fmt == FloatFormat::F64 {
        let r =
            f64::from_bits(low64(xv)).mul_add(f64::from_bits(low64(yv)), f64::from_bits(low64(zv)));
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
    // Compare 2·|r| to |y| (not |r| to |y|/2): `ay*0.5` underflows to 0 for the
    // smallest subnormals, which would spuriously trigger the tie branch at r=0.
    // `2·|r|` is exact for the magnitudes here (and overflow to ∞ only happens
    // when |r| > |y|/2, where an adjust is correct anyway).
    let two_ar = 2.0 * r.abs();
    if two_ar > ay {
        r -= r.signum() * ay;
    } else if two_ar == ay {
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
        let r = ieee_remainder(
            f64::from(f32::from_bits(low32(xv))),
            f64::from(f32::from_bits(low32(yv))),
        );
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
#[allow(
    clippy::similar_names,
    clippy::many_single_char_names,
    clippy::too_many_lines
)]
pub fn rem_sym(
    arena: &mut TermArena,
    fmt: FloatFormat,
    x: TermId,
    y: TermId,
) -> Result<TermId, IrError> {
    fmt.check(arena, x)?;
    fmt.check(arena, y)?;
    if !fmt.is_ieee() {
        return Err(IrError::Unsupported("fp.rem symbolic: non-IEEE format"));
    }
    // Only the differentially-validated formats are accepted (ADR-0023): a wrong
    // FP circuit is not caught by model replay. The symbolic remainder is
    // validated against the trusted fold for F16/F32/F64. Wider-exponent formats
    // also reach the iterative reduction, but F128's `e_span` (32765) makes that
    // circuit impractical and it is unvalidated — refuse rather than risk a wrong
    // (or unbuildable) result.
    if !matches!(fmt, FloatFormat::F16 | FloatFormat::F32 | FloatFormat::F64) {
        return Err(IrError::Unsupported(
            "fp.rem symbolic: format not differentially validated (only F16/F32/F64)",
        ));
    }
    let (eb, sb) = (fmt.exp_bits, fmt.sig_bits);
    let total = fmt.width();
    let e_span = (1u32 << eb) - 3; // max LSB-exponent minus min LSB-exponent
    let w = sb + e_span + 2;
    if w > 128 {
        // The scaled-integer encoding overflows 128 bits (wide exponent). Fall
        // back to the iterative shift-subtract reduction, which uses a small
        // `sb+4`-bit register (the only 128-bit constraint) over `e_span`
        // data-independent steps. Of the validated formats this covers F32
        // (e_span 253) and F64 (e_span 2045); F16 uses the scaled path above.
        if sb + 4 <= 128 {
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
/// (F32/BF16/TF32 and F64), where the scaled-integer encoding of [`rem_sym`]
/// would exceed 128 bits. Only the small `sb+4`-bit register is 128-bit bound;
/// the `e_span` reduction steps make a larger but bounded formula (F64: 2045). The truncated remainder of `|x|` by `|y|`
/// is computed with a small (`sb`-wide) register over `e_span`
/// data-independent reduction steps (so `Mx·2^d mod My` for `Ex ≥ Ey`, else
/// `|x|`), the quotient's parity is tracked for the tie rule, and a nearest
/// adjust selects the final magnitude/sign before [`pack_value`] packs the exact
/// result. Validated against the trusted constant fold [`rem`] over F32.
#[allow(
    clippy::similar_names,
    clippy::many_single_char_names,
    clippy::too_many_lines
)]
fn rem_iterative(
    arena: &mut TermArena,
    fmt: FloatFormat,
    x: TermId,
    y: TermId,
) -> Result<TermId, IrError> {
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
    if w > 128 {
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

/// The working width for an `m`-bit integer → `(eb, sb)` float conversion: wide
/// enough to hold the magnitude, the left-shift of a small value into the
/// significand, and the rounding `drop` (`< W`). `None` if it would exceed
/// 128 bits.
fn int_to_fp_width(m: u32, sb: u32) -> Option<u32> {
    let w = m + sb + 4;
    (w <= 128).then_some(w)
}

/// `(_ to_fp eb sb)` from an **unsigned** bit-vector (`(_ to_fp_unsigned ...)`):
/// the unsigned value rounded to `(eb, sb)` under `mode`. Constant operands under
/// round-nearest-even fold via native conversion (exact); otherwise a symbolic
/// circuit rounds the value through the validated [`pack_value`] core (the integer
/// `v` is the magnitude `v · 2^0`). Returns `None` only when the working width
/// would exceed 128 bits.
pub fn ubv_to_fp(
    arena: &mut TermArena,
    fmt: FloatFormat,
    bv: TermId,
    mode: RoundingMode,
) -> Result<Option<TermId>, IrError> {
    let Sort::BitVec(m) = arena.sort_of(bv) else {
        return Err(IrError::SortMismatch {
            expected: "BitVec",
            found: arena.sort_of(bv),
        });
    };
    // Constant + RNE: native conversion is exact and folds to a clean constant.
    #[allow(clippy::cast_precision_loss)] // intentional integer→float rounding
    if mode == RoundingMode::NearestEven
        && let Some(v) = const_bits(arena, bv)
    {
        if fmt == FloatFormat::F32 {
            return Ok(Some(arena.bv_const(32, u128::from((v as f32).to_bits()))?));
        } else if fmt == FloatFormat::F64 {
            return Ok(Some(arena.bv_const(64, u128::from((v as f64).to_bits()))?));
        }
    }
    let Some(w) = int_to_fp_width(m, fmt.sig_bits) else {
        return Ok(None);
    };
    let mag = arena.zero_ext(w - m, bv)?;
    let sign = arena.bool_const(false);
    let e = arena.bv_const(w, 0)?;
    Ok(Some(pack_value(
        arena,
        fmt.exp_bits,
        fmt.sig_bits,
        sign,
        mag,
        e,
        mode,
    )?))
}

/// `(_ to_fp eb sb)` from a **signed** (two's-complement) bit-vector: the signed
/// value rounded to `(eb, sb)` under `mode`. Constant operands under
/// round-nearest-even fold via native conversion; otherwise a symbolic circuit
/// splits the sign and magnitude (the magnitude is `−v` for a negative `v`, which
/// is correct including the most-negative value) and rounds through the validated
/// [`pack_value`] core. Returns `None` only when the working width would exceed
/// 128 bits.
pub fn sbv_to_fp(
    arena: &mut TermArena,
    fmt: FloatFormat,
    bv: TermId,
    mode: RoundingMode,
) -> Result<Option<TermId>, IrError> {
    let Sort::BitVec(m) = arena.sort_of(bv) else {
        return Err(IrError::SortMismatch {
            expected: "BitVec",
            found: arena.sort_of(bv),
        });
    };
    #[allow(clippy::cast_precision_loss)] // intentional integer→float rounding
    if mode == RoundingMode::NearestEven
        && let Some(v) = const_bits(arena, bv)
    {
        let signed = to_signed(v, m);
        if fmt == FloatFormat::F32 {
            return Ok(Some(
                arena.bv_const(32, u128::from((signed as f32).to_bits()))?,
            ));
        } else if fmt == FloatFormat::F64 {
            return Ok(Some(
                arena.bv_const(64, u128::from((signed as f64).to_bits()))?,
            ));
        }
    }
    let Some(w) = int_to_fp_width(m, fmt.sig_bits) else {
        return Ok(None);
    };
    // sign = top bit; magnitude = |v| (two's-complement negate when negative,
    // which maps the most-negative value to its correct unsigned magnitude).
    let one1 = arena.bv_const(1, 1)?;
    let sign_bv = arena.extract(m - 1, m - 1, bv)?;
    let sign = arena.eq(sign_bv, one1)?;
    let neg = arena.bv_neg(bv)?;
    let abs = arena.ite(sign, neg, bv)?;
    let mag = arena.zero_ext(w - m, abs)?;
    let e = arena.bv_const(w, 0)?;
    Ok(Some(pack_value(
        arena,
        fmt.exp_bits,
        fmt.sig_bits,
        sign,
        mag,
        e,
        mode,
    )?))
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
pub fn round_significand(arena: &mut TermArena, sig: TermId, keep: u32) -> Result<TermId, IrError> {
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

/// Rounds an exact rational `num/den` (`den > 0`) to IEEE format `(eb, sb)` under
/// `mode`, returning the bit pattern — but **only** when `num/den` is a *dyadic*
/// number exactly representable as an `f64` (denominator a power of two,
/// `|num| < 2^53`, `den ≤ 2^62`). In that case the `f64` division is exact, so the
/// single rounding to the target format (the validated [`round_to_format`]) is the
/// only rounding and the result is correct. For any other rational (non-dyadic
/// like `1/3`, or out of the exact range) it returns `None`, so a `(_ to_fp …)`
/// from such a real literal is reported *unsupported* rather than double-rounded
/// (which could yield a wrong value). This keeps real→FP conversion sound.
#[must_use]
#[allow(
    clippy::cast_precision_loss,
    clippy::cast_sign_loss,
    clippy::cast_possible_truncation
)]
pub fn round_rational_to_format(
    eb: u32,
    sb: u32,
    num: i128,
    den: i128,
    mode: RoundingMode,
) -> Option<u128> {
    if den <= 0 {
        return None;
    }
    if num == 0 {
        return Some(round_to_format(eb, sb, 0.0, mode)); // +0
    }
    let uden = den as u128; // den > 0 checked
    if !uden.is_power_of_two() {
        return None; // denominator not a power of two → non-dyadic
    }
    if num.unsigned_abs() >= (1u128 << 53) {
        return None; // numerator needs > 53 significant bits
    }
    if uden > (1u128 << 62) {
        return None; // scale too small to stay exact in f64
    }
    // Both operands are exact f64s and the quotient has ≤ 53 significant bits with
    // a power-of-two scale in range, so this division is exact.
    let v = (num as f64) / (den as f64);
    Some(round_to_format(eb, sb, v, mode))
}

/// `a << s` as a `u128`, or `None` if it would overflow 128 bits.
fn shl_u128_checked(a: u128, s: u32) -> Option<u128> {
    if a == 0 {
        return Some(0);
    }
    if s >= 128 || a.leading_zeros() < s {
        return None;
    }
    Some(a << s)
}

/// Whether `a/den ≥ 2^e` for `a, den > 0` and any `e`, computed without overflow.
fn ratio_ge_pow2(a: u128, den: u128, e: i64) -> bool {
    if e >= 0 {
        // a ≥ den·2^e; an overflowing `den·2^e` exceeds `a`, so the answer is no.
        match shl_u128_checked(den, u32::try_from(e).unwrap_or(u32::MAX)) {
            Some(t) => a >= t,
            None => false,
        }
    } else {
        // a·2^(-e) ≥ den; an overflowing `a·2^(-e)` exceeds `den`, so the answer is yes.
        match shl_u128_checked(a, u32::try_from(-e).unwrap_or(u32::MAX)) {
            Some(t) => t >= den,
            None => true,
        }
    }
}

/// `floor(log2(a/den))` for `a, den > 0`.
fn floor_log2_ratio(a: u128, den: u128) -> i64 {
    let la = 128 - i64::from(a.leading_zeros());
    let ld = 128 - i64::from(den.leading_zeros());
    let mut e = la - ld; // within ±1 of the true value
    while ratio_ge_pow2(a, den, e + 1) {
        e += 1;
    }
    while !ratio_ge_pow2(a, den, e) {
        e -= 1;
    }
    e
}

/// Whether to round the truncated quotient `q` up, given the remainder `rem` of
/// `numer/denom` (`rem < denom`), the rounding `mode`, and the value's sign `neg`.
fn round_up_decision(q: u128, rem: u128, denom: u128, mode: RoundingMode, neg: bool) -> bool {
    if rem == 0 {
        return false;
    }
    match mode {
        // Compare 2·rem with denom via rem vs denom−rem (no overflow).
        RoundingMode::NearestEven => match rem.cmp(&(denom - rem)) {
            core::cmp::Ordering::Greater => true,
            core::cmp::Ordering::Less => false,
            core::cmp::Ordering::Equal => (q & 1) == 1, // tie → to even
        },
        RoundingMode::NearestAway => rem >= denom - rem, // 2·rem ≥ denom
        RoundingMode::TowardZero => false,
        RoundingMode::TowardPositive => !neg, // up == away-from-zero for a positive value
        RoundingMode::TowardNegative => neg,
    }
}

/// The bits an overflowing magnitude rounds to under `mode`: `±∞` for the nearest
/// modes, the max finite magnitude for truncation, and direction-dependent for the
/// directed modes.
fn overflow_bits(eb: u32, sb: u32, neg: bool, mode: RoundingMode, sign_bit: u128) -> u128 {
    let inf = sign_bit | (((1u128 << eb) - 1) << (sb - 1));
    let max_finite = sign_bit | (((1u128 << eb) - 2) << (sb - 1)) | ((1u128 << (sb - 1)) - 1);
    match mode {
        RoundingMode::NearestEven | RoundingMode::NearestAway => inf,
        RoundingMode::TowardZero => max_finite,
        RoundingMode::TowardPositive => {
            if neg {
                max_finite
            } else {
                inf
            }
        }
        RoundingMode::TowardNegative => {
            if neg {
                inf
            } else {
                max_finite
            }
        }
    }
}

/// Exact rounding of `a/den` (sign `neg`; `a, den > 0`) to an `(eb, sb)` IEEE float
/// under `mode`, by pure-integer arithmetic — correct for non-dyadic rationals,
/// with no f64 double-rounding. `sb` counts the implicit bit. Returns `None` if an
/// intermediate would exceed `u128` (the caller then declines).
fn round_rational_rne(
    eb: u32,
    sb: u32,
    mode: RoundingMode,
    neg: bool,
    a: u128,
    den: u128,
) -> Option<u128> {
    if a == 0 {
        return None; // num == 0 is handled by the caller (→ +0)
    }
    let total = eb + sb;
    let bias = (1i64 << (eb - 1)) - 1;
    let emax = bias; // largest normal unbiased exponent
    let emin = 1 - bias; // smallest normal unbiased exponent
    let sign_bit: u128 = if neg { 1u128 << (total - 1) } else { 0 };
    let implicit = 1u128 << (sb - 1);

    // Significand `round(a/den · 2^(sb-1-exp))` as an integer, or None on overflow.
    let round_at = |exp: i64| -> Option<u128> {
        let shift = i64::from(sb) - 1 - exp;
        let (numer, denom) = if shift >= 0 {
            (shl_u128_checked(a, u32::try_from(shift).ok()?)?, den)
        } else {
            (a, shl_u128_checked(den, u32::try_from(-shift).ok()?)?)
        };
        let q = numer / denom;
        let rem = numer % denom;
        Some(q + u128::from(round_up_decision(q, rem, denom, mode, neg)))
    };

    let e = floor_log2_ratio(a, den);

    if e < emin {
        // Subnormal: significand aligned at the fixed exponent `emin`.
        let m = round_at(emin)?;
        if m == 0 {
            return Some(sign_bit); // rounds to ±0
        }
        if m >= implicit {
            // Rounded up into the smallest normal (exponent field 1).
            return Some(sign_bit | implicit | (m - implicit));
        }
        return Some(sign_bit | m); // exponent field 0, trailing = m
    }

    let mut m = round_at(e)?;
    let mut e_adj = e;
    if m == (1u128 << sb) {
        // Significand carried past the top bit; renormalize up one exponent.
        m = implicit;
        e_adj += 1;
    }
    if e_adj > emax {
        return Some(overflow_bits(eb, sb, neg, mode, sign_bit));
    }
    #[allow(clippy::cast_sign_loss)]
    let expfield = (e_adj + bias) as u128; // in [1, 2^eb − 2]
    Some(sign_bit | (expfield << (sb - 1)) | (m - implicit))
}

/// Constant-folds `fp.to_real` (FP → mathematical Real, ADR-0015) for a finite
/// constant in **any IEEE-style format** (F16, BF16, TF32, F32, F64, FP8 E5M2, …):
/// the decode below is generic in `(exp_bits, sig_bits)`. FP→Real is **exact** (no
/// rounding), so when the exact value fits the `i128`-based [`Rational`] this folds
/// to a `Real` constant; `NaN`/`∞` (not real numbers) and values whose exact
/// rational exceeds `i128` return `Ok(None)`. Bridges FP into the linear-real-
/// arithmetic theory. (Non-IEEE formats like E4M3/E2M1 reuse the all-ones exponent
/// for finite values, so the `∞`/NaN short-circuit here is not valid for them.)
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
        (
            (1u128 << (sb - 1)) | trailing,
            field - exp_bias - (sb_i - 1),
        ) // normal
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

/// Computes the rounded integer **magnitude** of `x` (an FP value), as a `W`-bit
/// bit-vector, together with `(sign, e)`: `|x|` rounded to an integer under
/// `mode`. `e` is the unpacked LSB exponent (signed, `W`-bit) and `sign` the
/// sign bit (`Bool`); the value is `(-1)^sign · magnitude`. Shared by
/// [`to_ubv_sym`]/[`to_sbv_sym`]. `e ≥ 0` ⇒ the integer is `sig · 2^e`
/// (left shift); `e < 0` ⇒ the fractional bits are rounded off via the validated
/// [`round_variable`]. Magnitudes with `e ≥ width` overflow the requested integer
/// width and are caught by the callers' range check (here the shift just yields a
/// don't-care).
#[allow(
    clippy::similar_names,
    clippy::many_single_char_names,
    clippy::type_complexity
)]
fn fp_rounded_magnitude(
    arena: &mut TermArena,
    fmt: FloatFormat,
    w: u32,
    x: TermId,
    mode: RoundingMode,
) -> Result<(TermId, TermId, TermId), IrError> {
    let one1 = arena.bv_const(1, 1)?;
    let (sx, sig_w, e) = unpack_operand(arena, fmt, w, x)?;
    let sign = arena.eq(sx, one1)?;
    let zero_w = arena.bv_const(w, 0)?;
    let one_w = arena.bv_const(w, 1)?;
    let w_const = arena.bv_const(w, u128::from(w))?;

    // e >= 0: integer = sig << e (don't-care, becomes 0, when e >= w).
    let e_ge0 = arena.bv_sge(e, zero_w)?;
    let e_lt_w = arena.bv_ult(e, w_const)?;
    let shifted = arena.bv_shl(sig_w, e)?;
    let int_mag = arena.ite(e_lt_w, shifted, zero_w)?;

    // e < 0: round off `-e` fractional bits. |value| < 1 (drop >= w) gives 0
    // (nearest/toward-zero) or 1 (directed mode matching the sign).
    let neg_e = arena.bv_sub(zero_w, e)?;
    let rounded = round_variable(arena, sig_w, neg_e, mode, sign)?;
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
    let frac_mag = arena.ite(drop_ge_w, tiny, rounded)?;

    let mag = arena.ite(e_ge0, int_mag, frac_mag)?;
    Ok((mag, sign, e))
}

/// Symbolic `fp.to_ubv` (FP → unsigned `width`-bit BV) under `mode`. The rounded
/// magnitude is **pinned** only when the value is *definitely* in `[0, 2^width)`
/// (finite, nonnegative, no shift overflow); NaN/∞/negative/out-of-range route to
/// `fresh` — an unconstrained `BitVec(width)` the caller supplies — matching
/// SMT-LIB's leaving those cases unspecified. Over-routing to `fresh` is always
/// sound (it can never force a wrong `unsat`); only the pinned value must be
/// correct, and it reuses the validated rounding primitives. `fresh` is returned
/// whole if the working width would exceed 128 bits.
#[allow(clippy::similar_names, clippy::many_single_char_names)]
pub fn to_ubv_sym(
    arena: &mut TermArena,
    fmt: FloatFormat,
    mode: RoundingMode,
    x: TermId,
    width: u32,
    fresh: TermId,
) -> Result<TermId, IrError> {
    let w = width + fmt.sig_bits + 4;
    if width == 0 || w > 128 {
        return Ok(fresh);
    }
    let (mag, sign, e) = fp_rounded_magnitude(arena, fmt, w, x, mode)?;
    let zero_w = arena.bv_const(w, 0)?;
    let finite = {
        let nan = is_nan(arena, fmt, x)?;
        let inf = is_infinite(arena, fmt, x)?;
        let bad = arena.or(nan, inf)?;
        arena.not(bad)?
    };
    // Nonnegative: not (sign && mag != 0)  (−0 is allowed, value 0).
    let mag_zero = arena.eq(mag, zero_w)?;
    let nonneg = {
        let neg_nonzero = {
            let nz = arena.not(mag_zero)?;
            arena.and(sign, nz)?
        };
        arena.not(neg_nonzero)?
    };
    // e < width (necessary: value ≥ 2^e), and value < 2^width (high bits zero).
    let width_c = sconst(arena, w, i64::from(width))?;
    let e_small = arena.bv_slt(e, width_c)?;
    let high = arena.extract(w - 1, width, mag)?;
    let high_zero = {
        let hz = arena.bv_const(w - width, 0)?;
        arena.eq(high, hz)?
    };
    let in_range = {
        let a = arena.and(finite, nonneg)?;
        let b = arena.and(e_small, high_zero)?;
        arena.and(a, b)?
    };
    let low = arena.extract(width - 1, 0, mag)?;
    arena.ite(in_range, low, fresh)
}

/// Symbolic `fp.to_sbv` (FP → signed two's-complement `width`-bit BV) under
/// `mode`. As [`to_ubv_sym`], pins the value only when *definitely* in range:
/// finite and `|magnitude| < 2^(width−1)` (the most-negative `−2^(width−1)` is
/// conservatively routed to `fresh` too — sound, just incomplete for that one
/// value). NaN/∞/out-of-range route to the unconstrained `fresh`.
#[allow(clippy::similar_names, clippy::many_single_char_names)]
pub fn to_sbv_sym(
    arena: &mut TermArena,
    fmt: FloatFormat,
    mode: RoundingMode,
    x: TermId,
    width: u32,
    fresh: TermId,
) -> Result<TermId, IrError> {
    let w = width + fmt.sig_bits + 4;
    if width == 0 || w > 128 {
        return Ok(fresh);
    }
    let (mag, sign, e) = fp_rounded_magnitude(arena, fmt, w, x, mode)?;
    let finite = {
        let nan = is_nan(arena, fmt, x)?;
        let inf = is_infinite(arena, fmt, x)?;
        let bad = arena.or(nan, inf)?;
        arena.not(bad)?
    };
    // e < width (shift validity / coarse bound) and |mag| < 2^(width−1), plus the
    // exact most-negative value −2^(width−1) (mag == 2^(width−1) with sign set),
    // whose two's-complement is itself.
    let width_c = sconst(arena, w, i64::from(width))?;
    let e_small = arena.bv_slt(e, width_c)?;
    let high = arena.extract(w - 1, width - 1, mag)?;
    let mag_fits = {
        let hz = arena.bv_const(w - (width - 1), 0)?;
        arena.eq(high, hz)?
    };
    let is_min_neg = {
        let min_mag = arena.bv_const(w, 1u128 << (width - 1))?;
        let eq_min = arena.eq(mag, min_mag)?;
        arena.and(sign, eq_min)?
    };
    let fits = arena.or(mag_fits, is_min_neg)?;
    let in_range = {
        let a = arena.and(finite, e_small)?;
        arena.and(a, fits)?
    };
    // Two's-complement: negate the low `width` bits when the sign is set.
    let low = arena.extract(width - 1, 0, mag)?;
    let neg = arena.bv_neg(low)?;
    let signed = arena.ite(sign, neg, low)?;
    arena.ite(in_range, signed, fresh)
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
#[allow(
    clippy::cast_precision_loss,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap
)]
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
    if w >= 128 {
        u128::MAX
    } else {
        (1u128 << w) - 1
    }
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
///
/// SMT-LIB leaves the result of `fp.min`/`fp.max` on **opposite-sign zeros**
/// (`+0` vs `−0`, equal magnitude) **unspecified** — the result may be `+0` OR
/// `−0`, and the choice may even differ between argument orders. A *deterministic*
/// pick is therefore unsound for `unsat` (it could force two genuinely-free
/// results equal and exclude a real model). So on the opposite-sign-zero case the
/// result here is a zero whose sign is a **fresh free Boolean**, one per
/// application: structural hashing makes the same syntactic `fp.min`/`fp.max`
/// term reuse its fresh bit (self-consistent — a real function), while distinct
/// applications (e.g. `fp.max(a,b)` vs `fp.max(b,a)`) get independent bits and so
/// **may** differ. Every other input keeps the exact [`order_key`] selection
/// unchanged, so only the genuinely-unspecified case becomes free.
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
    // Opposite-sign-zero override: SMT-LIB-unspecified, so a free zero whose sign
    // is a fresh per-application bit. `both_zero ∧ sign(x) ≠ sign(y)`.
    let opp = opposite_sign_zero(arena, fmt, x, y)?;
    let free_zero = free_sign_zero(arena, fmt, x, y, want_smaller)?;
    let by_order = arena.ite(opp, free_zero, by_order)?;
    // NaN propagation: if x is NaN return y, if y is NaN return x.
    let nx = is_nan(arena, fmt, x)?;
    let ny = is_nan(arena, fmt, y)?;
    let if_x_nan = arena.ite(nx, y, by_order)?;
    arena.ite(ny, x, if_x_nan)
}

/// `is_zero(x) ∧ is_zero(y) ∧ sign(x) ≠ sign(y)` — the genuinely-unspecified
/// case for `fp.min`/`fp.max` (both operands zero, opposite signs).
fn opposite_sign_zero(
    arena: &mut TermArena,
    fmt: FloatFormat,
    x: TermId,
    y: TermId,
) -> Result<TermId, IrError> {
    let zx = is_zero(arena, fmt, x)?;
    let zy = is_zero(arena, fmt, y)?;
    let sx = sign_set(arena, fmt, x)?;
    let sy = sign_set(arena, fmt, y)?;
    let diff_sign = arena.eq(sx, sy)?;
    let diff_sign = arena.not(diff_sign)?;
    let both_zero = arena.and(zx, zy)?;
    arena.and(both_zero, diff_sign)
}

/// A zero of the format's width whose sign is a **fresh free Boolean**, one per
/// `fp.min`/`fp.max` application. The fresh symbol's name is a deterministic
/// function of the operand term ids and the min/max flavor, so the same
/// syntactic application reuses one bit (consistent — a real function) while
/// distinct applications get independent bits (so they may differ, exactly as
/// SMT-LIB permits). Magnitude is `0`; only the sign bit varies.
fn free_sign_zero(
    arena: &mut TermArena,
    fmt: FloatFormat,
    x: TermId,
    y: TermId,
    want_smaller: bool,
) -> Result<TermId, IrError> {
    let flavor = if want_smaller { "min" } else { "max" };
    let name = format!("axeyum_fp.{flavor}.signzero.{}.{}", x.index(), y.index());
    let sign = arena.bv_var(&name, 1)?;
    // result = sign-bit ++ (width-1) zero bits = ±0 with the chosen sign.
    let lower = arena.bv_const(fmt.width() - 1, 0)?;
    arena.concat(sign, lower)
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

    #[test]
    fn rational_to_format_dyadic_matches_native_f32_and_f64() {
        // Dyadic rationals round to exactly the native cast (the only rounding is
        // the validated round_to_format on the exact f64).
        for &(num, den) in &[
            (1i128, 1i128),
            (-1, 1),
            (1, 2),
            (-3, 2),
            (1, 4),
            (5, 8),
            (-7, 16),
            (3, 1),
            (255, 256),
            (123_456, 1024),
        ] {
            let v = num as f64 / den as f64;
            assert_eq!(
                round_rational_to_format(8, 24, num, den, RoundingMode::NearestEven),
                Some(u128::from((v as f32).to_bits())),
                "F32 {num}/{den}",
            );
            assert_eq!(
                round_rational_to_format(11, 53, num, den, RoundingMode::NearestEven),
                Some(u128::from(v.to_bits())),
                "F64 {num}/{den}",
            );
        }
        // Zero folds to +0.
        assert_eq!(
            round_rational_to_format(8, 24, 0, 1, RoundingMode::NearestEven),
            Some(0)
        );
        // `round_rational_to_format` stays dyadic-only and sound: non-dyadic and
        // out-of-(f64-)window rationals report `None` (never double-rounded). The
        // exact integer RNE path lives separately (see `from_real`).
        assert_eq!(
            round_rational_to_format(8, 24, 1, 3, RoundingMode::NearestEven),
            None,
            "1/3 is non-dyadic",
        );
        assert_eq!(
            round_rational_to_format(8, 24, 1, 10, RoundingMode::NearestEven),
            None,
            "1/10 is non-dyadic",
        );
        assert_eq!(
            round_rational_to_format(8, 24, 1i128 << 53, 1, RoundingMode::NearestEven),
            None,
            "numerator needs > 53 bits",
        );
        assert_eq!(
            round_rational_to_format(8, 24, 1, 1i128 << 63, RoundingMode::NearestEven),
            None,
            "denominator scale too small",
        );
    }

    /// `from_real` builds an `F32` constant whose evaluated bits equal the native
    /// cast — for both dyadic and round-nearest-even non-dyadic rationals.
    #[test]
    fn from_real_builds_f32_constants_matching_native() {
        use rustc_apfloat::Float;
        use rustc_apfloat::ieee::Single;
        let read = |a: &TermArena, t| match eval(a, t, &Assignment::new()) {
            Ok(Value::Bv { value, .. }) => value,
            other => panic!("expected a bit-vector value, got {other:?}"),
        };
        for &(num, den) in &[
            (1i128, 1i128),
            (-1, 1),
            (1, 2),
            (-5, 2),
            (1, 4),
            (3, 1),
            (255, 256),
            ((1i128 << 24) + 1, 1i128 << 24), // 25-bit numerator → rounds
            (1, 3),                           // non-dyadic, rounded (RNE)
            (1, 10),
            (-2, 7),
            (22, 7),
        ] {
            let mut a = TermArena::new();
            let bits = from_real(
                &mut a,
                FloatFormat::F32,
                RoundingMode::NearestEven,
                Rational::new(num, den),
            )
            .unwrap()
            .expect("dyadic rational is representable");
            let v = num as f64 / den as f64;
            assert_eq!(
                read(&a, bits),
                u128::from((v as f32).to_bits()),
                "from_real F32 {num}/{den}",
            );
        }
        // All five rounding modes over a non-dyadic value match `rustc_apfloat`'s
        // correctly-rounded division (the independent IEEE reference).
        let ap_round = |mode: RoundingMode| match mode {
            RoundingMode::NearestEven => rustc_apfloat::Round::NearestTiesToEven,
            RoundingMode::NearestAway => rustc_apfloat::Round::NearestTiesToAway,
            RoundingMode::TowardZero => rustc_apfloat::Round::TowardZero,
            RoundingMode::TowardPositive => rustc_apfloat::Round::TowardPositive,
            RoundingMode::TowardNegative => rustc_apfloat::Round::TowardNegative,
        };
        for &(num, den) in &[(1i128, 3i128), (-1, 3), (1, 10), (22, 7), (-22, 7), (2, 7)] {
            for mode in [
                RoundingMode::NearestEven,
                RoundingMode::NearestAway,
                RoundingMode::TowardZero,
                RoundingMode::TowardPositive,
                RoundingMode::TowardNegative,
            ] {
                let p = Single::from_i128(num).value;
                let q = Single::from_i128(den).value;
                let oracle = p.div_r(q, ap_round(mode)).value.to_bits();
                let mut a = TermArena::new();
                let bits = from_real(&mut a, FloatFormat::F32, mode, Rational::new(num, den))
                    .unwrap()
                    .expect("representable in F32");
                assert_eq!(
                    read(&a, bits),
                    oracle,
                    "from_real {num}/{den} mode {mode:?}"
                );
            }
        }
    }

    /// The pure-integer RNE rational rounder agrees with the validated f64 path on
    /// dyadic rationals (normal / rounding / tie / F16-subnormal), and rounds
    /// non-dyadic values to the native cast.
    #[test]
    fn round_rational_rne_matches_validated_path() {
        let dyadic: &[(u32, u32, i128, i128)] = &[
            (8, 24, 3, 2),
            (8, 24, -5, 4),
            (8, 24, (1 << 24) + 1, 1 << 24),
            (8, 24, (1 << 25) + 1, 1 << 25),
            (8, 24, (1 << 24) + 3, 1 << 24),
            (5, 11, 1, 1),
            (5, 11, 1, 1024),
            (5, 11, 1, 32768), // F16 subnormal (2^-15)
            (5, 11, 3, 32768), // F16 subnormal, rounds
            (5, 11, (1 << 11) + 1, 1 << 11),
            (11, 53, 7, 8),
            (11, 53, -1, 1024),
        ];
        for &(eb, sb, num, den) in dyadic {
            let oracle = round_rational_to_format(eb, sb, num, den, RoundingMode::NearestEven);
            let got = round_rational_rne(
                eb,
                sb,
                RoundingMode::NearestEven,
                num < 0,
                num.unsigned_abs(),
                den as u128,
            );
            assert_eq!(got, oracle, "dyadic {num}/{den} fmt({eb},{sb})");
        }
        // Non-dyadic RNE (via the integer path directly) vs the (non-midpoint, hence
        // correct) f64 bridge.
        for &(num, den) in &[(1i128, 3i128), (1, 10), (2, 7), (-1, 3), (22, 7)] {
            let v = num as f64 / den as f64;
            assert_eq!(
                round_rational_rne(
                    8,
                    24,
                    RoundingMode::NearestEven,
                    num < 0,
                    num.unsigned_abs(),
                    den as u128
                ),
                Some(u128::from((v as f32).to_bits())),
                "non-dyadic F32 {num}/{den}",
            );
            assert_eq!(
                round_rational_rne(
                    11,
                    53,
                    RoundingMode::NearestEven,
                    num < 0,
                    num.unsigned_abs(),
                    den as u128
                ),
                Some(u128::from(v.to_bits())),
                "non-dyadic F64 {num}/{den}",
            );
        }
    }

    /// `to_real` decodes finite constants of the small (ML) IEEE-style formats
    /// exactly — not just F32/F64 — and rejects ∞/NaN.
    #[test]
    fn to_real_decodes_small_ieee_formats() {
        let real = |a: &TermArena, t| match a.node(t) {
            TermNode::RealConst(r) => *r,
            other => panic!("expected RealConst, got {other:?}"),
        };
        // F16: 1.5=0x3E00, 0.5=0x3800, smallest subnormal=0x0001 (2^-24), +0=0x0000.
        for &(bits, n, d) in &[
            (0x3E00u128, 3i128, 2i128),
            (0x3800, 1, 2),
            (0x0001, 1, 1 << 24),
            (0x0000, 0, 1),
        ] {
            let mut a = TermArena::new();
            let x = a.bv_const(16, bits).unwrap();
            let r = to_real(&mut a, FloatFormat::F16, x)
                .unwrap()
                .expect("finite F16 → real");
            assert_eq!(real(&a, r), Rational::new(n, d), "F16 {bits:#06x}");
        }
        // FP8 E5M2 (8-bit): 1.0=0x3C, 1.5=0x3E, smallest subnormal=0x01 (2^-16).
        for &(bits, n, d) in &[(0x3Cu128, 1i128, 1i128), (0x3E, 3, 2), (0x01, 1, 1 << 16)] {
            let mut a = TermArena::new();
            let x = a.bv_const(8, bits).unwrap();
            let r = to_real(&mut a, FloatFormat::FP8_E5M2, x)
                .unwrap()
                .expect("finite E5M2 → real");
            assert_eq!(real(&a, r), Rational::new(n, d), "E5M2 {bits:#04x}");
        }
        // ∞ / NaN are not real numbers (F16 +∞=0x7C00, NaN=0x7E00).
        for bits in [0x7C00u128, 0x7E00] {
            let mut a = TermArena::new();
            let x = a.bv_const(16, bits).unwrap();
            assert_eq!(
                to_real(&mut a, FloatFormat::F16, x).unwrap(),
                None,
                "F16 {bits:#06x} is not real",
            );
        }
    }

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
            return if mant != 0 {
                f64::NAN
            } else {
                sign * f64::INFINITY
            };
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
                assert!(
                    exp == 0x1F && mant != 0,
                    "add({ab:#x},{bb:#x}) want NaN, got {got:#x}"
                );
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
                assert!(
                    exp == 0xFF && mant != 0,
                    "sqrt({xb:#x}) want NaN, got {got:#x}"
                );
            } else {
                assert_eq!(got, u128::from(s.to_bits()), "sqrt({xb:#x})");
            }
        };
        let s32: [u32; 12] = [
            0x0000_0000,
            0x8000_0000,
            0x3F80_0000,
            0x4080_0000,
            0x4000_0000,
            0xBF80_0000,
            0x7F80_0000,
            0xFF80_0000,
            0x7FC0_0000,
            0x0080_0000,
            0x0000_0001,
            0x7F7F_FFFF,
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
            s = s
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
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
    fn round_to_integral_sym_matches_native_f64() {
        // F64 is a primary real-world format; `fp.roundToIntegral` is exact
        // integer rounding, so native f64 rounding is an exact oracle. Validate
        // all five modes (the F32 test above leaves F64 uncovered).
        let modes = [
            (RoundingMode::NearestEven, 0u8),
            (RoundingMode::NearestAway, 1),
            (RoundingMode::TowardZero, 2),
            (RoundingMode::TowardPositive, 3),
            (RoundingMode::TowardNegative, 4),
        ];
        let mut a = TermArena::new();
        let is_nan_bits = |b: u128| (b >> 52) & 0x7FF == 0x7FF && (b & 0xF_FFFF_FFFF_FFFF) != 0;
        let structured: [u64; 12] = [
            0x0000_0000_0000_0000, // +0
            0x8000_0000_0000_0000, // -0
            0x3FE0_0000_0000_0000, // 0.5
            0xBFE0_0000_0000_0000, // -0.5
            0x3FF8_0000_0000_0000, // 1.5
            0x4004_0000_0000_0000, // 2.5
            0x7FF0_0000_0000_0000, // +inf
            0xFFF0_0000_0000_0000, // -inf
            0x7FF8_0000_0000_0000, // NaN
            0x0008_0000_0000_0000, // subnormal
            0x4049_21FB_5444_2D18, // ~pi-ish
            0xC059_0000_0000_0000, // -100.0
        ];
        let mut state: u64 = 0x9e37_79b9_7f4a_7c15;
        for &(mode, kind) in &modes {
            let mut inputs = structured.to_vec();
            for _ in 0..400 {
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                inputs.push(state);
            }
            for xb in inputs {
                let xt = a.bv_const(64, u128::from(xb)).unwrap();
                let r = round_to_integral_sym(&mut a, FloatFormat::F64, mode, xt).unwrap();
                let got = match eval(&a, r, &Assignment::new()) {
                    Ok(Value::Bv { value, .. }) => value,
                    other => panic!("expected Bv, got {other:?}"),
                };
                let v = f64::from_bits(xb);
                let want = match kind {
                    0 => v.round_ties_even(),
                    1 => v.round(),
                    2 => v.trunc(),
                    3 => v.ceil(),
                    _ => v.floor(),
                };
                if want.is_nan() {
                    assert!(
                        is_nan_bits(got),
                        "rint64({xb:#x},{mode:?}) want NaN got {got:#x}"
                    );
                } else {
                    assert_eq!(got, u128::from(want.to_bits()), "rint64({xb:#x},{mode:?})");
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
            (0, 1), // 000: 0
            (1, 2), // 001: 0.5
            (1, 1), // 010: 1
            (3, 2), // 011: 1.5
            (2, 1), // 100: 2
            (3, 1), // 101: 3
            (4, 1), // 110: 4
            (6, 1), // 111: 6
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
        let bit = |a: &TermArena, t: axeyum_ir::TermId| {
            matches!(eval(a, t, &Assignment::new()), Ok(Value::Bool(true)))
        };
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
                (
                    mul(&mut a, bf, xt, yt, RoundingMode::NearestEven).unwrap(),
                    bf16_to_f64(xb) * bf16_to_f64(yb),
                ),
                (
                    add(&mut a, bf, xt, yt, RoundingMode::NearestEven).unwrap(),
                    bf16_to_f64(xb) + bf16_to_f64(yb),
                ),
            ] {
                let got = match eval(&a, term, &Assignment::new()) {
                    Ok(Value::Bv { value, .. }) => value,
                    other => panic!("expected Bv, got {other:?}"),
                };
                if exact.is_nan() {
                    assert!(
                        (got >> 7) & 0xFF == 0xFF && got & 0x7F != 0,
                        "bf16 want NaN"
                    );
                } else {
                    let want = round_to_format(8, 8, exact, RoundingMode::NearestEven);
                    assert_eq!(
                        got, want,
                        "bf16 op({xb:#x},{yb:#x}) = {got:#x}, want {want:#x}"
                    );
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
            let r = to_fp(
                &mut a,
                FloatFormat::F32,
                FloatFormat::F64,
                RoundingMode::NearestEven,
                xt,
            )
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
                let r = to_fp(&mut a, FloatFormat::F64, FloatFormat::F32, mode, xt).unwrap();
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
    #[allow(clippy::many_single_char_names)]
    fn to_fp_small_format_pairs_match_round_to_format() {
        // Validate FP→FP conversion over many small (src, dst) format pairs (the
        // native-cast test above only covers F32↔F64). A small/standard `src`
        // value is exact in f64 (sb ≤ 53, eb ≤ 11), so converting via
        // `round_to_format(dst, src_value)` is a single, correctly-rounded step —
        // an exact oracle. Covers F16/BF16/TF32/F32/F64 widening and narrowing.
        let modes = [
            RoundingMode::NearestEven,
            RoundingMode::TowardZero,
            RoundingMode::TowardPositive,
            RoundingMode::TowardNegative,
        ];
        let fmts = [
            FloatFormat::F16,
            FloatFormat::BF16,
            FloatFormat::TF32,
            FloatFormat {
                exp_bits: 6,
                sig_bits: 8,
            },
            FloatFormat::F32,
            FloatFormat::F64,
        ];
        let mut a = TermArena::new();
        let mut state: u64 = 0x51a5_3c3c_9696_5151;
        let next = |s: &mut u64| {
            *s = s
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            *s
        };
        let is_nan_bits = |b: u128, eb: u32, sb: u32| {
            (b >> (sb - 1)) & ((1u128 << eb) - 1) == (1u128 << eb) - 1
                && b & ((1u128 << (sb - 1)) - 1) != 0
        };
        let mut uid = 0u32;
        for &src in &fmts {
            for &dst in &fmts {
                let smask = (1u128 << src.width()) - 1;
                for &mode in &modes {
                    uid += 1;
                    let xt = a
                        .declare(&format!("x{uid}"), Sort::BitVec(src.width()))
                        .unwrap();
                    let xv = a.var(xt);
                    let t = to_fp(&mut a, src, dst, mode, xv).unwrap();
                    for _ in 0..40 {
                        let xb = u128::from(next(&mut state)) & smask;
                        // Source value, exact in f64 (decode is exact for eb ≤ 11
                        // here; for F64 use native from_bits to dodge powi range).
                        let v = if src == FloatFormat::F64 {
                            f64::from_bits(xb as u64)
                        } else {
                            src.decode_ieee_f64(xb)
                        };
                        let mut asg = Assignment::new();
                        asg.set(
                            xt,
                            Value::Bv {
                                width: src.width(),
                                value: xb,
                            },
                        );
                        let got = match eval(&a, t, &asg) {
                            Ok(Value::Bv { value, .. }) => value,
                            other => panic!("{other:?}"),
                        };
                        if v.is_nan() {
                            assert!(
                                is_nan_bits(got, dst.exp_bits, dst.sig_bits),
                                "to_fp {src:?}->{dst:?} {xb:#x} want NaN got {got:#x}"
                            );
                        } else {
                            let want = round_to_format(dst.exp_bits, dst.sig_bits, v, mode);
                            assert_eq!(got, want, "to_fp {src:?}->{dst:?} ({xb:#x},{mode:?})");
                        }
                    }
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
                    assert_eq!(
                        got, want,
                        "mul({ab:#x},{bb:#x},{mode:?}) = {got:#x}, want {want:#x}"
                    );
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
                assert!(
                    exp == 0xFF && mant != 0,
                    "div({ab:#x},{bb:#x}) want NaN, got {got:#x}"
                );
            } else {
                assert_eq!(got, u128::from(q.to_bits()), "div({ab:#x},{bb:#x})");
            }
        };
        let s32: [u32; 12] = [
            0x0000_0000,
            0x8000_0000,
            0x3F80_0000,
            0xBF80_0000,
            0x4000_0000,
            0x3F00_0000,
            0x7F80_0000,
            0xFF80_0000,
            0x7FC0_0000,
            0x0080_0000,
            0x0000_0001,
            0x7F7F_FFFF,
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
            s = s
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let x = s;
            s = s
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            check64(&mut a, x, s);
        }
    }

    /// Regression: `div` must normalize **subnormal** operands before the integer
    /// division, or it under-produces quotient bits and loses the sticky bit
    /// (round-down where round-to-nearest should round up). A subnormal dividend
    /// is the trigger; validated against native `f32` division (correctly rounded).
    #[test]
    fn div_subnormal_operands_f32_matches_native() {
        let mut a = TermArena::new();
        let check = |a: &mut TermArena, ab: u32, bb: u32| {
            let at = a.bv_const(32, u128::from(ab)).unwrap();
            let bt = a.bv_const(32, u128::from(bb)).unwrap();
            let r = div(a, FloatFormat::F32, at, bt, RoundingMode::NearestEven).unwrap();
            let got = match eval(a, r, &Assignment::new()) {
                Ok(Value::Bv { value, .. }) => value,
                other => panic!("{other:?}"),
            };
            let q = f32::from_bits(ab) / f32::from_bits(bb);
            if q.is_nan() {
                assert!(
                    (got >> 23) & 0xFF == 0xFF && got & 0x7F_FFFF != 0,
                    "div({ab:#x},{bb:#x}) want NaN got {got:#x}"
                );
            } else {
                assert_eq!(got, u128::from(q.to_bits()), "div({ab:#x},{bb:#x})");
            }
        };
        let mut s = 0x9e37_79b9_7f4a_7c15u64;
        let mut next = || {
            s = s
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            s
        };
        for _ in 0..5000 {
            // Subnormal dividend (exp field 0, nonzero fraction, random sign).
            let sub = ((next() & 0x8000_0000) | (next() & 0x7F_FFFF) | 1) as u32;
            let other = next() as u32;
            check(&mut a, sub, other); // subnormal / arbitrary
            check(&mut a, other, sub); // arbitrary / subnormal
            // Subnormal / subnormal.
            let sub2 = ((next() & 0x8000_0000) | (next() & 0x7F_FFFF) | 1) as u32;
            check(&mut a, sub, sub2);
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
                assert!(
                    exp == 0xFF && mant != 0,
                    "add({ab:#x},{bb:#x}) want NaN, got {got:#x}"
                );
            } else {
                assert_eq!(got, u128::from(sum.to_bits()), "add({ab:#x},{bb:#x})");
            }
        };
        let structured: [u32; 14] = [
            0x0000_0000,
            0x8000_0000,
            0x3F80_0000,
            0xBF80_0000,
            0x4000_0000,
            0x3F00_0000,
            0x7F80_0000,
            0xFF80_0000,
            0x7FC0_0000,
            0x0080_0000,
            0x0000_0001,
            0x007F_FFFF,
            0x7F7F_FFFF,
            0x4B80_0000,
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
            0x0000_0000_0000_0000,
            0x8000_0000_0000_0000,
            0x3FF0_0000_0000_0000,
            0xBFF0_0000_0000_0000,
            0x4000_0000_0000_0000,
            0x7FF0_0000_0000_0000,
            0x7FF8_0000_0000_0000,
            0x0010_0000_0000_0000,
            0x0000_0000_0000_0001,
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
                assert!(
                    exp == 0x7FF && mant != 0,
                    "mul64({ab:#x},{bb:#x}) want NaN, got {got:#x}"
                );
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
            assert_eq!(
                got,
                u128::from(want.to_bits()),
                "rem64({x},{y}) want {want}"
            );
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
        assert!(
            f64::from_bits(nan(&mut a, f64::INFINITY, 2.0) as u64).is_nan(),
            "rem(inf,2)=NaN"
        );
        assert!(
            f64::from_bits(nan(&mut a, 3.0, 0.0) as u64).is_nan(),
            "rem(3,0)=NaN"
        );
        assert_eq!(
            nan(&mut a, 3.0, f64::INFINITY),
            u128::from(3.0f64.to_bits()),
            "rem(3,inf)=3"
        );
        assert_eq!(
            nan(&mut a, 0.0, 3.0),
            u128::from(0.0f64.to_bits()),
            "rem(+0,3)=+0"
        );
        assert_eq!(
            nan(&mut a, -0.0, 3.0),
            u128::from((-0.0f64).to_bits()),
            "rem(-0,3)=-0"
        );
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
            assert_eq!(
                got,
                u128::from(want),
                "rem({xf},{yf}) got {got:#x} want {want:#x}"
            );
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
            assert_eq!(
                got, want,
                "rem_bf16({xb:#x},{yb:#x}) got {got:#x} want {want:#x}"
            );
        };
        let mut state: u64 = 0xfeed_face_dead_beef;
        for _ in 0..8000 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            check(
                &mut a,
                (state & 0xFFFF) as u16,
                ((state >> 16) & 0xFFFF) as u16,
            );
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
        assert!(
            rem(&mut a, FloatFormat::FP8_E4M3, xt, yt)
                .unwrap()
                .is_none(),
            "E4M3 not folded"
        );
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
                assert!(
                    is_nan_bits(got),
                    "rem_sym({xb:#x},{yb:#x}) want NaN, got {got:#x}"
                );
            } else {
                assert_eq!(
                    got, want,
                    "rem_sym({xb:#x},{yb:#x}) got {got:#x} want {want:#x}"
                );
            }
        };

        // structured: ±0, ±1, ±2, 0.5, 1.5, smallest normal/subnormals, max, ∞, NaN.
        let structured: [u16; 16] = [
            0x0000, 0x8000, 0x3C00, 0xBC00, 0x4000, 0xC000, 0x3800, 0x3E00, 0x0400, 0x0001, 0x03FF,
            0x7BFF, 0x7C00, 0xFC00, 0x7E00, 0x4900,
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
            check(
                &mut a,
                (state & 0xFFFF) as u16,
                ((state >> 16) & 0xFFFF) as u16,
            );
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
                assert!(
                    exp == 0xFF && mant != 0,
                    "fma({xb:#x},{yb:#x},{zb:#x}) want NaN, got {got:#x}"
                );
            } else {
                assert_eq!(
                    got,
                    u128::from(want.to_bits()),
                    "fma({xb:#x},{yb:#x},{zb:#x})"
                );
            }
        };
        let structured: [u32; 12] = [
            0x0000_0000,
            0x8000_0000,
            0x3f80_0000,
            0xbf80_0000,
            0x4000_0000,
            0x3f00_0000,
            0x7f80_0000,
            0xff80_0000,
            0x7fc0_0000,
            0x0080_0000,
            0x0000_0001,
            0x4248_0000,
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
                assert!(
                    exp == 0xFF && mant != 0,
                    "sub({xb:#x},{yb:#x}) want NaN, got {got:#x}"
                );
            } else {
                assert_eq!(got, u128::from(want.to_bits()), "sub({xb:#x},{yb:#x})");
            }
        };
        let structured: [u32; 10] = [
            0x0000_0000,
            0x8000_0000,
            0x3f80_0000,
            0xbf80_0000,
            0x4000_0000,
            0x7f80_0000,
            0xff80_0000,
            0x7fc0_0000,
            0x0080_0000,
            0x0000_0001,
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
    fn rem_sym_refuses_unvalidated_formats() {
        // Only F16/F32/F64 are differentially validated for symbolic fp.rem.
        // Others (incl. F128, whose iterative circuit is impractical at e_span
        // 32765) must be refused, not silently built.
        let mut a = TermArena::new();
        for fmt in [
            FloatFormat::F128,
            FloatFormat::BF16,
            FloatFormat::TF32,
            FloatFormat {
                exp_bits: 6,
                sig_bits: 8,
            },
        ] {
            let w = fmt.width();
            let x = a.bv_const(w, 0).unwrap();
            let y = a.bv_const(w, 0).unwrap();
            assert!(
                matches!(rem_sym(&mut a, fmt, x, y), Err(IrError::Unsupported(_))),
                "rem_sym should refuse {fmt:?}"
            );
        }
        // Validated formats still build.
        for fmt in [FloatFormat::F16, FloatFormat::F32, FloatFormat::F64] {
            let w = fmt.width();
            let x = a.bv_const(w, 0).unwrap();
            let y = a.bv_const(w, 0).unwrap();
            assert!(
                rem_sym(&mut a, fmt, x, y).is_ok(),
                "rem_sym should build {fmt:?}"
            );
        }
    }

    #[test]
    fn rem_sym_iterative_matches_fold_f64() {
        // F64 uses the iterative path (e_span 2045); validate against the trusted
        // fold on a modest sample (the formula is large, so eval is slow).
        let mut a = TermArena::new();
        let is_nan_bits = |b: u128| (b >> 52) & 0x7FF == 0x7FF && (b & 0xF_FFFF_FFFF_FFFF) != 0;
        let check = |a: &mut TermArena, xb: u64, yb: u64| {
            let xt = a.bv_const(64, u128::from(xb)).unwrap();
            let yt = a.bv_const(64, u128::from(yb)).unwrap();
            let want = match rem(a, FloatFormat::F64, xt, yt).unwrap() {
                Some(t) => match eval(a, t, &Assignment::new()) {
                    Ok(Value::Bv { value, .. }) => value,
                    other => panic!("{other:?}"),
                },
                None => panic!("fold covers F64"),
            };
            let sym = rem_sym(a, FloatFormat::F64, xt, yt).unwrap();
            let got = match eval(a, sym, &Assignment::new()) {
                Ok(Value::Bv { value, .. }) => value,
                other => panic!("{other:?}"),
            };
            if is_nan_bits(want) {
                assert!(
                    is_nan_bits(got),
                    "rem_f64({xb:#x},{yb:#x}) want NaN, got {got:#x}"
                );
            } else {
                assert_eq!(
                    got, want,
                    "rem_f64({xb:#x},{yb:#x}) got {got:#x} want {want:#x}"
                );
            }
        };
        let structured: [u64; 10] = [
            0x0000_0000_0000_0000,
            0x8000_0000_0000_0000,
            0x3ff0_0000_0000_0000, // ±0, 1.0
            0xbff0_0000_0000_0000,
            0x4000_0000_0000_0000,
            0x3fe0_0000_0000_0000, // -1, 2, 0.5
            0x4008_0000_0000_0000,
            0x0000_0000_0000_0001,
            0x7ff0_0000_0000_0000, // 3, subn, +inf
            0x7ff8_0000_0000_0000, // NaN
        ];
        for &xb in &structured {
            for &yb in &structured {
                check(&mut a, xb, yb);
            }
        }
        let mut state: u64 = 0xd00d_feed_face_b00c;
        for _ in 0..40 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let xb = state;
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            check(&mut a, xb, state);
        }
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
        let r = to_ubv(&mut a, FloatFormat::F16, RoundingMode::TowardZero, x, 8)
            .unwrap()
            .unwrap();
        assert_eq!(eval_bv(&a, r), 3);
        // to_ubv(2.5, NearestEven, 8) = 2 (ties to even)
        let x = bits16(&mut a, 0x4100);
        let r = to_ubv(&mut a, FloatFormat::F16, RoundingMode::NearestEven, x, 8)
            .unwrap()
            .unwrap();
        assert_eq!(eval_bv(&a, r), 2);
        // to_sbv(-3.5, RTZ, 8) = -3 = 0xFD
        let x = bits16(&mut a, 0xC300);
        let r = to_sbv(&mut a, FloatFormat::F16, RoundingMode::TowardZero, x, 8)
            .unwrap()
            .unwrap();
        assert_eq!(eval_bv(&a, r), 0xFD);
        // round_to_integral(3.5, RTZ) = 3.0 = 0x4200
        let x = bits16(&mut a, 0x4300);
        let r = round_to_integral(&mut a, FloatFormat::F16, RoundingMode::TowardZero, x)
            .unwrap()
            .unwrap();
        assert_eq!(eval_bv(&a, r), 0x4200);
        // round_to_integral(2.5, NearestEven) = 2.0 = 0x4000
        let x = bits16(&mut a, 0x4100);
        let r = round_to_integral(&mut a, FloatFormat::F16, RoundingMode::NearestEven, x)
            .unwrap()
            .unwrap();
        assert_eq!(eval_bv(&a, r), 0x4000);
        // BF16 too: to_ubv(2.0, RTZ, 8); 2.0 in bf16 = 0x4000.
        let x = a.bv_const(16, 0x4000).unwrap();
        let r = to_ubv(&mut a, FloatFormat::BF16, RoundingMode::TowardZero, x, 8)
            .unwrap()
            .unwrap();
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
                assert!(
                    is_nan_bits(got),
                    "rem_f32({xb:#x},{yb:#x}) want NaN, got {got:#x}"
                );
            } else {
                assert_eq!(
                    got, want,
                    "rem_f32({xb:#x},{yb:#x}) got {got:#x} want {want:#x}"
                );
            }
        };
        let structured: [u32; 14] = [
            0x0000_0000,
            0x8000_0000,
            0x3f80_0000,
            0xbf80_0000,
            0x4000_0000,
            0x3f00_0000,
            0x4070_0000,
            0x40e0_0000,
            0x7f80_0000,
            0xff80_0000,
            0x7fc0_0000,
            0x0080_0000,
            0x0000_0001,
            0x4248_0000,
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

#[cfg(test)]
mod fma_f64_const_tests {
    use super::*;
    use axeyum_ir::{Assignment, Value, eval};

    #[test]
    fn constant_f64_fma_folds_via_native_mul_add() {
        // F64 fp.fma's symbolic circuit needs 164 bits (> 128=128), but
        // constant operands under RNE fold via native mul_add (ADR-0026 note).
        let mut arena = TermArena::new();
        let mk =
            |arena: &mut TermArena, v: f64| arena.bv_const(64, u128::from(v.to_bits())).unwrap();
        for &(x, y, z) in &[
            (2.0f64, 3.0, 1.0),
            (0.1, 0.2, 0.3),
            (1e300, 1e300, f64::NEG_INFINITY), // product overflows to +inf; +(-inf) = NaN
            (-2.0, 4.0, 0.5),
            (f64::MAX, 2.0, 0.0),
        ] {
            let a = mk(&mut arena, x);
            let b = mk(&mut arena, y);
            let c = mk(&mut arena, z);
            let t = fma(
                &mut arena,
                FloatFormat::F64,
                a,
                b,
                c,
                RoundingMode::NearestEven,
            )
            .unwrap();
            // Result is a Float64-width bit-vector equal to native mul_add.
            let want = x.mul_add(y, z).to_bits();
            assert_eq!(
                eval(&arena, t, &Assignment::new()).unwrap(),
                Value::Bv {
                    width: 64,
                    value: u128::from(want)
                },
                "fma({x}, {y}, {z})"
            );
        }
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn symbolic_f64_fma_matches_native() {
        // Symbolic F64 operands force the 164-bit wide circuit (no constant
        // fold). It must equal native `f64::mul_add` — the correctly-rounded
        // fused multiply-add — over a wide sweep. This validates the wide
        // bit-vector path for `pack_value`'s signed exponent arithmetic.
        let mut arena = TermArena::new();
        let sx = arena.declare("fx", Sort::BitVec(64)).unwrap();
        let sy = arena.declare("fy", Sort::BitVec(64)).unwrap();
        let sz = arena.declare("fz", Sort::BitVec(64)).unwrap();
        let (x, y, z) = (arena.var(sx), arena.var(sy), arena.var(sz));
        let t = fma(
            &mut arena,
            FloatFormat::F64,
            x,
            y,
            z,
            RoundingMode::NearestEven,
        )
        .unwrap();
        let check = |arena: &TermArena, xb: u64, yb: u64, zb: u64| {
            let mut asg = Assignment::new();
            asg.set(
                sx,
                Value::Bv {
                    width: 64,
                    value: u128::from(xb),
                },
            );
            asg.set(
                sy,
                Value::Bv {
                    width: 64,
                    value: u128::from(yb),
                },
            );
            asg.set(
                sz,
                Value::Bv {
                    width: 64,
                    value: u128::from(zb),
                },
            );
            let got = match eval(arena, t, &asg).unwrap() {
                Value::Bv { value, .. } => value,
                other => panic!("{other:?}"),
            };
            let want = f64::from_bits(xb).mul_add(f64::from_bits(yb), f64::from_bits(zb));
            if want.is_nan() {
                let exp = (got >> 52) & 0x7FF;
                let mant = got & 0xF_FFFF_FFFF_FFFF;
                assert!(
                    exp == 0x7FF && mant != 0,
                    "fma({xb:#x},{yb:#x},{zb:#x}) want NaN, got {got:#x}"
                );
            } else {
                assert_eq!(
                    got,
                    u128::from(want.to_bits()),
                    "fma({xb:#x},{yb:#x},{zb:#x})"
                );
            }
        };
        // Structured: zeros, signed ones, 2.0, 0.5, infinities, NaN, subnormal,
        // smallest, a non-trivial fraction, and a large finite value.
        let structured: [u64; 12] = [
            0x0000_0000_0000_0000, // +0
            0x8000_0000_0000_0000, // -0
            0x3FF0_0000_0000_0000, // 1.0
            0xBFF0_0000_0000_0000, // -1.0
            0x4000_0000_0000_0000, // 2.0
            0x3FE0_0000_0000_0000, // 0.5
            0x7FF0_0000_0000_0000, // +inf
            0xFFF0_0000_0000_0000, // -inf
            0x7FF8_0000_0000_0000, // NaN
            0x0008_0000_0000_0000, // subnormal
            0x0000_0000_0000_0001, // smallest subnormal
            0x4049_21FB_5444_2D18, // ~pi*... a generic finite value
        ];
        for &xb in &structured {
            for &yb in &structured {
                for &zb in &structured {
                    check(&arena, xb, yb, zb);
                }
            }
        }
        let mut state: u64 = 0xf00d_face_dead_b33f;
        let next = |state: &mut u64| {
            *state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            *state
        };
        for _ in 0..3000 {
            check(&arena, next(&mut state), next(&mut state), next(&mut state));
        }
    }
}

#[cfg(test)]
#[allow(clippy::many_single_char_names)]
mod fma_f128_apfloat_tests {
    use super::*;
    use axeyum_ir::{Assignment, Value, eval};
    use rustc_apfloat::{Float, Round, ieee::Quad};

    // F128 field layout: sign at bit 127, 15-bit exponent at bits 112..=126,
    // 112-bit trailing significand at bits 0..=111.
    const EXP_SHIFT: u32 = 112;
    const MANT_MASK: u128 = (1u128 << 112) - 1;
    const EXP_ONES: u128 = 0x7FFF;

    fn f128(sign: bool, exp: u32, mant: u128) -> u128 {
        (u128::from(sign) << 127) | (u128::from(exp) << EXP_SHIFT) | (mant & MANT_MASK)
    }

    fn is_f128_nan(bits: u128) -> bool {
        ((bits >> EXP_SHIFT) & EXP_ONES) == EXP_ONES && (bits & MANT_MASK) != 0
    }

    /// A battery of F128 corner bit-patterns: signed zeros, ±1, 2.0, 0.5,
    /// ±inf, NaN, the smallest subnormal, and a generic finite value.
    fn structured() -> [u128; 11] {
        [
            f128(false, 0, 0),                          // +0
            f128(true, 0, 0),                           // -0
            f128(false, 0x3FFF, 0),                     // 1.0
            f128(true, 0x3FFF, 0),                      // -1.0
            f128(false, 0x4000, 0),                     // 2.0
            f128(false, 0x3FFE, 0),                     // 0.5
            f128(false, 0x7FFF, 0),                     // +inf
            f128(true, 0x7FFF, 0),                      // -inf
            f128(false, 0x7FFF, 1),                     // NaN
            f128(false, 0, 1),                          // smallest subnormal
            f128(false, 0x4000, 0x1234_5678_9abc_def0), // a generic finite value
        ]
    }

    /// Splits a 64-bit LCG state into a 128-bit pattern (full bit coverage,
    /// including NaNs and infinities).
    fn rng128(state: &mut u64) -> u128 {
        let mut next = || {
            *state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            *state
        };
        (u128::from(next()) << 64) | u128::from(next())
    }

    /// Validates an F128 binary op circuit against `rustc_apfloat`'s `Quad`
    /// (RNE) over the structured battery plus 2000 random pairs.
    fn validate_binop(
        build: impl Fn(
            &mut TermArena,
            FloatFormat,
            TermId,
            TermId,
            RoundingMode,
        ) -> Result<TermId, IrError>,
        oracle: impl Fn(Quad, Quad) -> Quad,
        name: &str,
    ) {
        let mut arena = TermArena::new();
        let sx = arena.declare("a", Sort::BitVec(128)).unwrap();
        let sy = arena.declare("b", Sort::BitVec(128)).unwrap();
        let (x, y) = (arena.var(sx), arena.var(sy));
        let t = build(
            &mut arena,
            FloatFormat::F128,
            x,
            y,
            RoundingMode::NearestEven,
        )
        .unwrap();
        let check = |arena: &TermArena, xb: u128, yb: u128| {
            let mut asg = Assignment::new();
            asg.set(
                sx,
                Value::Bv {
                    width: 128,
                    value: xb,
                },
            );
            asg.set(
                sy,
                Value::Bv {
                    width: 128,
                    value: yb,
                },
            );
            let got = match eval(arena, t, &asg).unwrap() {
                Value::Bv { value, .. } => value,
                other => panic!("{other:?}"),
            };
            let want = oracle(Quad::from_bits(xb), Quad::from_bits(yb)).to_bits();
            if Quad::from_bits(want).is_nan() {
                assert!(
                    is_f128_nan(got),
                    "{name}({xb:#x},{yb:#x}) want NaN, got {got:#x}"
                );
            } else {
                assert_eq!(got, want, "{name}({xb:#x},{yb:#x})");
            }
        };
        let s = structured();
        for &xb in &s {
            for &yb in &s {
                check(&arena, xb, yb);
            }
        }
        let mut state: u64 = 0x9e37_79b9_7f4a_7c15;
        for _ in 0..2000 {
            check(&arena, rng128(&mut state), rng128(&mut state));
        }
    }

    #[test]
    fn symbolic_f128_add_matches_apfloat() {
        validate_binop(
            add,
            |a, b| a.add_r(b, Round::NearestTiesToEven).value,
            "add",
        );
    }

    #[test]
    fn symbolic_f128_mul_matches_apfloat() {
        validate_binop(
            mul,
            |a, b| a.mul_r(b, Round::NearestTiesToEven).value,
            "mul",
        );
    }

    #[test]
    fn symbolic_f128_div_matches_apfloat() {
        validate_binop(
            div,
            |a, b| a.div_r(b, Round::NearestTiesToEven).value,
            "div",
        );
    }

    #[test]
    fn symbolic_f128_fma_matches_apfloat() {
        // Symbolic F128 operands force the 344-bit wide circuit (no constant
        // fold). It must equal `rustc_apfloat`'s correctly-rounded quad fma
        // (ADR-0028) — there is no native `f128` on stable Rust. This validates
        // the wide path at the widest standard format.
        let mut arena = TermArena::new();
        let sx = arena.declare("qx", Sort::BitVec(128)).unwrap();
        let sy = arena.declare("qy", Sort::BitVec(128)).unwrap();
        let sz = arena.declare("qz", Sort::BitVec(128)).unwrap();
        let (x, y, z) = (arena.var(sx), arena.var(sy), arena.var(sz));
        let t = fma(
            &mut arena,
            FloatFormat::F128,
            x,
            y,
            z,
            RoundingMode::NearestEven,
        )
        .unwrap();
        let check = |arena: &TermArena, xb: u128, yb: u128, zb: u128| {
            let mut asg = Assignment::new();
            asg.set(
                sx,
                Value::Bv {
                    width: 128,
                    value: xb,
                },
            );
            asg.set(
                sy,
                Value::Bv {
                    width: 128,
                    value: yb,
                },
            );
            asg.set(
                sz,
                Value::Bv {
                    width: 128,
                    value: zb,
                },
            );
            let got = match eval(arena, t, &asg).unwrap() {
                Value::Bv { value, .. } => value,
                other => panic!("{other:?}"),
            };
            let want = Quad::from_bits(xb)
                .mul_add_r(
                    Quad::from_bits(yb),
                    Quad::from_bits(zb),
                    Round::NearestTiesToEven,
                )
                .value
                .to_bits();
            if Quad::from_bits(want).is_nan() {
                assert!(
                    is_f128_nan(got),
                    "fma({xb:#x},{yb:#x},{zb:#x}) want NaN, got {got:#x}"
                );
            } else {
                assert_eq!(got, want, "fma({xb:#x},{yb:#x},{zb:#x})");
            }
        };
        let s = structured();
        for &xb in &s {
            for &yb in &s {
                for &zb in &s {
                    check(&arena, xb, yb, zb);
                }
            }
        }
        // Randomized 128-bit patterns (full bit-pattern coverage incl. NaNs/inf).
        let mut state: u64 = 0xc0ff_ee00_d15e_a5e5;
        for _ in 0..2000 {
            check(
                &arena,
                rng128(&mut state),
                rng128(&mut state),
                rng128(&mut state),
            );
        }
    }
}

/// An independent, exact correct-rounding oracle for `fp.sqrt`, used to validate
/// the (wide) F128 `sqrt` circuit — `rustc_apfloat` implements no square root,
/// so there is no off-the-shelf oracle (ADR-0028). Instead of recomputing the
/// root, this checks the *defining property* of round-nearest-ties-to-even: the
/// candidate result `r` is correct iff the true `√x` lies in `r`'s rounding
/// interval `[(pred+r)/2, (r+succ)/2]`, with exact ties resolved to the even
/// significand. The check squares the dyadic interval endpoints and compares to
/// `x` with exact big integers (`WideUint`), never forming an irrational root.
///
/// Crucially, the oracle is itself **validated against native `f64::sqrt`**
/// (which is IEEE correctly-rounded) over a wide sweep — it must accept the
/// native result and reject both neighbours — before it is trusted for F128.
#[cfg(test)]
#[allow(
    clippy::cast_possible_truncation,
    clippy::many_single_char_names,
    clippy::similar_names
)]
mod sqrt_correct_rounding_oracle {
    use super::*;
    use axeyum_ir::{Assignment, Value, WideUint, eval};
    use core::cmp::Ordering;

    const W: u32 = 1024; // wide enough for F128 squared significands + alignment

    fn field(bits: u128, eb: u32, sb: u32) -> (bool, u128, u128) {
        let sign = (bits >> (eb + sb - 1)) & 1 == 1;
        let exp = (bits >> (sb - 1)) & ((1u128 << eb) - 1);
        let frac = bits & ((1u128 << (sb - 1)) - 1);
        (sign, exp, frac)
    }

    fn is_nan(bits: u128, eb: u32, sb: u32) -> bool {
        let (_, exp, frac) = field(bits, eb, sb);
        exp == (1u128 << eb) - 1 && frac != 0
    }
    fn is_inf(bits: u128, eb: u32, sb: u32) -> bool {
        let (_, exp, frac) = field(bits, eb, sb);
        exp == (1u128 << eb) - 1 && frac == 0
    }
    fn is_zero(bits: u128, eb: u32, sb: u32) -> bool {
        let (_, exp, frac) = field(bits, eb, sb);
        exp == 0 && frac == 0
    }

    /// Decodes a *positive finite* pattern to an exact dyadic `(mant, exp)`
    /// meaning `mant · 2^exp`. `+0` decodes to `(0, 0)`.
    fn decode(bits: u128, eb: u32, sb: u32) -> (u128, i64) {
        let (_, exp, frac) = field(bits, eb, sb);
        let bias = (1i64 << (eb - 1)) - 1;
        if exp == 0 {
            if frac == 0 {
                return (0, 0); // +0
            }
            (frac, 1 - bias - i64::from(sb - 1))
        } else {
            let m = frac | (1u128 << (sb - 1));
            let e = i64::try_from(exp).unwrap() - bias - i64::from(sb - 1);
            (m, e)
        }
    }

    /// `a + b` for exact dyadics (one may be zero).
    fn add(a: (u128, i64), b: (u128, i64)) -> (u128, i64) {
        if a.0 == 0 {
            return b;
        }
        if b.0 == 0 {
            return a;
        }
        let e0 = a.1.min(b.1);
        let m = (a.0 << (a.1 - e0)) + (b.0 << (b.1 - e0));
        (m, e0)
    }

    /// Squares an exact dyadic, returning `(value², exp)` as a wide integer.
    fn square(v: (u128, i64)) -> (WideUint, i64) {
        let m = WideUint::from_u128(v.0, W);
        (m.mul(&m), 2 * v.1)
    }

    /// Compares `a.0 · 2^a.1` against `b.0 · 2^b.1` (both non-negative). Panics if
    /// the exponent gap would overflow the working width — a signal that the
    /// candidate is wildly off, which never happens for a near-correct root.
    fn cmp(a: &(WideUint, i64), b: &(WideUint, i64)) -> Ordering {
        let m = a.1.min(b.1);
        let da = u32::try_from(a.1 - m).unwrap();
        let db = u32::try_from(b.1 - m).unwrap();
        assert!(
            da < W - 256 && db < W - 256,
            "exponent gap too large: {da}/{db}"
        );
        let l = a.0.shl(da);
        let r = b.0.shl(db);
        if l.ult(&r) {
            Ordering::Less
        } else if r.ult(&l) {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }

    /// True iff `rbits` is the round-nearest-ties-to-even `sqrt` of `xbits` in
    /// format `(eb, sb)`.
    fn correctly_rounded_sqrt(eb: u32, sb: u32, xbits: u128, rbits: u128) -> bool {
        let (xsign, _, _) = field(xbits, eb, sb);
        // Special cases (mirror IEEE / the circuit): sqrt(NaN) and sqrt(x<0) are
        // NaN; sqrt(±0) = ±0; sqrt(+inf) = +inf.
        if is_nan(xbits, eb, sb) {
            return is_nan(rbits, eb, sb);
        }
        let x_is_neg_zero = is_zero(xbits, eb, sb) && xsign;
        if xsign && !x_is_neg_zero {
            return is_nan(rbits, eb, sb); // negative finite or -inf
        }
        if is_zero(xbits, eb, sb) {
            return rbits == xbits; // ±0 preserved (sign included)
        }
        if is_inf(xbits, eb, sb) {
            return is_inf(rbits, eb, sb) && !field(rbits, eb, sb).0; // +inf
        }
        // Positive finite x: the result must be positive, finite and non-zero.
        let (rsign, _, _) = field(rbits, eb, sb);
        if rsign || is_nan(rbits, eb, sb) || is_inf(rbits, eb, sb) || is_zero(rbits, eb, sb) {
            return false;
        }
        let vx = {
            let (mx, ex) = decode(xbits, eb, sb);
            (WideUint::from_u128(mx, W), ex)
        };
        let vr = decode(rbits, eb, sb);
        let vp = decode(rbits - 1, eb, sb); // predecessor (or +0 at the bottom)
        let r_even = (vr.0 & 1) == 0;

        // Lower endpoint: (pred + r)/2, squared, vs x.
        let lower_sq = {
            let (m, e) = add(vp, vr);
            square((m, e - 1)) // /2
        };
        let lower_ok = match cmp(&lower_sq, &vx) {
            Ordering::Less => true,     // pred-midpoint strictly below x ⇒ inside
            Ordering::Equal => r_even,  // exact tie pred|r ⇒ rounds to even
            Ordering::Greater => false, // √x below the interval ⇒ r too big
        };

        // Upper endpoint: (r + succ)/2, squared, vs x. A succ of +inf imposes no
        // upper bound (never happens for a real sqrt result, handled for safety).
        let succ = rbits + 1;
        let upper_ok = if is_inf(succ, eb, sb) {
            true
        } else {
            let upper_sq = {
                let (m, e) = add(vr, decode(succ, eb, sb));
                square((m, e - 1))
            };
            match cmp(&upper_sq, &vx) {
                Ordering::Greater => true, // succ-midpoint strictly above x ⇒ inside
                Ordering::Equal => r_even, // exact tie r|succ ⇒ rounds to even
                Ordering::Less => false,   // √x above the interval ⇒ r too small
            }
        };
        lower_ok && upper_ok
    }

    fn rng(state: &mut u64) -> u64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        *state
    }

    /// The oracle itself must agree with native `f64::sqrt` (IEEE correctly
    /// rounded): accept the native result, reject both finite neighbours.
    #[test]
    fn oracle_matches_native_f64_sqrt() {
        let check = |xb: u64| {
            let xf = f64::from_bits(xb);
            let r = xf.sqrt().to_bits();
            assert!(
                correctly_rounded_sqrt(11, 53, u128::from(xb), u128::from(r)),
                "oracle rejected native sqrt({xb:#x}) = {r:#x}"
            );
            // Neighbours must be rejected (only meaningful for positive finite x,
            // where r is a positive finite non-zero float with finite neighbours).
            if xf.is_sign_positive() && xf.is_finite() && xf != 0.0 {
                for nb in [r.wrapping_sub(1), r.wrapping_add(1)] {
                    if !is_nan(u128::from(nb), 11, 53) && !is_inf(u128::from(nb), 11, 53) {
                        assert!(
                            !correctly_rounded_sqrt(11, 53, u128::from(xb), u128::from(nb)),
                            "oracle accepted wrong neighbour {nb:#x} for sqrt({xb:#x})"
                        );
                    }
                }
            }
        };
        let structured: [u64; 12] = [
            0x0000_0000_0000_0000, // +0
            0x8000_0000_0000_0000, // -0
            0x3FF0_0000_0000_0000, // 1.0
            0x4000_0000_0000_0000, // 2.0
            0x4010_0000_0000_0000, // 4.0
            0x7FF0_0000_0000_0000, // +inf
            0xFFF0_0000_0000_0000, // -inf
            0x7FF8_0000_0000_0000, // NaN
            0xBFF0_0000_0000_0000, // -1.0 (negative ⇒ NaN)
            0x0008_0000_0000_0000, // subnormal
            0x0000_0000_0000_0001, // smallest subnormal
            0x4048_F5C2_8F5C_28F6, // ~49.92
        ];
        for &x in &structured {
            check(x);
        }
        let mut state = 0x1234_5678_9abc_def0u64;
        for _ in 0..20000 {
            check(rng(&mut state));
        }
    }

    // F128 field layout helpers (sign at 127, 15-bit exp at 112..=126).
    fn q128(sign: bool, exp: u32, mant: u128) -> u128 {
        (u128::from(sign) << 127) | (u128::from(exp) << 112) | (mant & ((1u128 << 112) - 1))
    }

    /// The wide F128 `sqrt` circuit must produce the correctly-rounded result for
    /// every input, judged by the (native-validated) oracle above.
    #[test]
    fn symbolic_f128_sqrt_matches_oracle() {
        let mut arena = TermArena::new();
        let s = arena.declare("qx", Sort::BitVec(128)).unwrap();
        let x = arena.var(s);
        let t = sqrt(&mut arena, FloatFormat::F128, x, RoundingMode::NearestEven).unwrap();
        let check = |arena: &TermArena, xb: u128| {
            let mut asg = Assignment::new();
            asg.set(
                s,
                Value::Bv {
                    width: 128,
                    value: xb,
                },
            );
            let got = match eval(arena, t, &asg).unwrap() {
                Value::Bv { value, .. } => value,
                other => panic!("{other:?}"),
            };
            assert!(
                correctly_rounded_sqrt(15, 113, xb, got),
                "F128 sqrt({xb:#034x}) = {got:#034x} is not correctly rounded"
            );
        };
        let structured: [u128; 12] = [
            q128(false, 0, 0),                               // +0
            q128(true, 0, 0),                                // -0
            q128(false, 0x3FFF, 0),                          // 1.0
            q128(false, 0x4000, 0),                          // 2.0
            q128(false, 0x4001, 0),                          // 4.0
            q128(false, 0x7FFF, 0),                          // +inf
            q128(true, 0x7FFF, 0),                           // -inf
            q128(false, 0x7FFF, 1),                          // NaN
            q128(true, 0x3FFF, 0),                           // -1.0 (negative ⇒ NaN)
            q128(false, 0, 1),                               // smallest subnormal
            q128(false, 1, 0),                               // smallest normal
            q128(false, 0x4000, 0x1234_5678_9abc_def0_1234), // a generic value
        ];
        for &xb in &structured {
            check(&arena, xb);
        }
        let mut state = 0xdead_beef_0bad_f00du64;
        for _ in 0..1500 {
            let xb = (u128::from(rng(&mut state)) << 64) | u128::from(rng(&mut state));
            check(&arena, xb);
        }
    }
}

/// Differential validation of the symbolic FP `add`/`mul`/`div`/`sqrt` circuits
/// **over small IEEE formats** — every `(eb, sb)` with `eb ≤ 11` and `sb ≤ 11`
/// (which covers F16, BF16, TF32, FP8 E5M2, and the tiny formats used by
/// quantifier expansion). These formats are exactly representable in `f64`, and
/// for a *single* operation round-nearest double rounding through `f64`'s 53-bit
/// significand is innocuous at this precision (`53 ≥ 2·sb + 2`), so
/// `round_to_format(native f64 op)` is a correct oracle. (`fma` is excluded — see
/// the note in the test — because its fused result can exceed 53 bits, making the
/// f64 oracle unsound.) This validates formats that reach the circuit from the
/// parser but were previously untested (a wrong FP circuit is not caught by model
/// replay — there is no first-class FP op), and it caught a real `div` sticky-bit
/// bug for subnormal operands and an exponent-width overflow for large-`eb`
/// formats, both fixed.
#[cfg(test)]
#[allow(clippy::cast_possible_truncation, clippy::many_single_char_names)]
mod small_format_arithmetic_validation {
    use super::*;
    use axeyum_ir::{Assignment, Value, eval};

    fn is_nan_bits(bits: u128, eb: u32, sb: u32) -> bool {
        let exp = (bits >> (sb - 1)) & ((1u128 << eb) - 1);
        let frac = bits & ((1u128 << (sb - 1)) - 1);
        exp == (1u128 << eb) - 1 && frac != 0
    }

    /// Expected format bits for an exact-or-native-rounded `f64` result `rf`.
    fn expected(eb: u32, sb: u32, rf: f64) -> Option<u128> {
        if rf.is_nan() {
            return None; // NaN: compare by class, not bits
        }
        Some(round_to_format(eb, sb, rf, RoundingMode::NearestEven))
    }

    fn eval_bits(arena: &TermArena, t: TermId, s: axeyum_ir::SymbolId, v: u128) -> u128 {
        let mut asg = Assignment::new();
        asg.set(
            s,
            Value::Bv {
                width: 32,
                value: v,
            },
        );
        match eval(arena, t, &asg).unwrap() {
            Value::Bv { value, .. } => value,
            other => panic!("{other:?}"),
        }
    }

    #[test]
    fn unvalidated_formats_are_refused_not_silently_wrong() {
        // Formats outside the validated set must return `Unsupported`, never a
        // silently-unvalidated (possibly wrong) circuit — enabled ⟹ validated.
        let mut a = TermArena::new();
        let unvalidated = [
            FloatFormat {
                exp_bits: 8,
                sig_bits: 20,
            }, // sb > 11, not standard
            FloatFormat {
                exp_bits: 11,
                sig_bits: 5,
            }, // eb > 10, not standard
            FloatFormat {
                exp_bits: 15,
                sig_bits: 64,
            }, // wide, not F128
            FloatFormat::FP8_E4M3, // non-IEEE
        ];
        for fmt in unvalidated {
            let w = fmt.width();
            let x = a.bv_const(w, 0).unwrap();
            let y = a.bv_const(w, 0).unwrap();
            assert!(
                matches!(
                    add(&mut a, fmt, x, y, RoundingMode::NearestEven),
                    Err(IrError::Unsupported(_))
                ),
                "add {fmt:?}"
            );
            assert!(
                matches!(
                    mul(&mut a, fmt, x, y, RoundingMode::NearestEven),
                    Err(IrError::Unsupported(_))
                ),
                "mul {fmt:?}"
            );
            assert!(
                matches!(
                    div(&mut a, fmt, x, y, RoundingMode::NearestEven),
                    Err(IrError::Unsupported(_))
                ),
                "div {fmt:?}"
            );
            assert!(
                matches!(
                    sqrt(&mut a, fmt, x, RoundingMode::NearestEven),
                    Err(IrError::Unsupported(_))
                ),
                "sqrt {fmt:?}"
            );
            assert!(
                matches!(
                    fma(&mut a, fmt, x, y, x, RoundingMode::NearestEven),
                    Err(IrError::Unsupported(_))
                ),
                "fma {fmt:?}"
            );
        }
        // Validated formats still build.
        for fmt in [
            FloatFormat::F16,
            FloatFormat::BF16,
            FloatFormat::F32,
            FloatFormat::F64,
            FloatFormat::F128,
        ] {
            let w = fmt.width();
            let x = a.bv_const(w, 0).unwrap();
            let y = a.bv_const(w, 0).unwrap();
            assert!(
                add(&mut a, fmt, x, y, RoundingMode::NearestEven).is_ok(),
                "add {fmt:?} should build"
            );
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // exhaustive per-format sweep, kept as one test
    fn small_ieee_formats_match_f64_oracle() {
        let mut state = 0x5151_a5a5_3c3c_9696u64;
        let rng = |state: &mut u64| {
            *state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            *state
        };
        // `eb ≤ 10` keeps every format value within f64's normal range, so the
        // `f64` oracle (and `decode_ieee_f64`, which scales by `2^e`) stays exact
        // — at `eb = 11` the format's subnormal exponents reach `2^-1024`, where
        // `2.0.powi(-1024)` overflows to `1/inf = 0`. All real small formats
        // (F16/BF16/TF32/FP8, `eb ≤ 8`) fall well within this range.
        for eb in 2u32..=10 {
            for sb in 2u32..=11 {
                let fmt = FloatFormat {
                    exp_bits: eb,
                    sig_bits: sb,
                };
                if !fmt.is_ieee() {
                    continue; // (4,4)=FP8_E4M3 and (2,2)=FP4_E2M1 are non-IEEE
                }
                let total = eb + sb;
                let bias = (1i64 << (eb - 1)) - 1;
                // Per-format structured corners: ±0, ±1, ±2, +inf, -inf, NaN,
                // smallest subnormal, largest finite.
                let one = (u128::try_from(bias).unwrap()) << (sb - 1);
                let inf = ((1u128 << eb) - 1) << (sb - 1);
                let max_fin = inf - 1;
                let corners: [u128; 10] = [
                    0,
                    1u128 << (total - 1),         // -0
                    one,                          // 1.0
                    one | (1u128 << (total - 1)), // -1.0
                    one + (1u128 << (sb - 1)),    // 2.0
                    inf,                          // +inf
                    inf | (1u128 << (total - 1)), // -inf
                    inf | 1,                      // NaN
                    1,                            // smallest subnormal
                    max_fin,                      // largest finite
                ];
                let mask = (1u128 << total) - 1;
                let mut inputs: Vec<u128> = corners.to_vec();
                for _ in 0..120 {
                    inputs.push(u128::from(rng(&mut state)) & mask);
                }

                // Build each op once over a symbolic operand pair, eval per input.
                let mut a = TermArena::new();
                let sx = a.declare("x", Sort::BitVec(total)).unwrap();
                let sy = a.declare("y", Sort::BitVec(total)).unwrap();
                let (x, y) = (a.var(sx), a.var(sy));
                let rne = RoundingMode::NearestEven;
                let t_add = add(&mut a, fmt, x, y, rne).unwrap();
                let t_mul = mul(&mut a, fmt, x, y, rne).unwrap();
                let t_div = div(&mut a, fmt, x, y, rne).unwrap();
                let t_sqrt = sqrt(&mut a, fmt, x, rne).unwrap();
                // NB: `fma` is deliberately NOT validated here. f64 `mul_add` is
                // not a valid oracle for fused multiply-add at these formats: the
                // exact `a·b + c` can span more than 53 bits (when the product
                // and addend exponents differ widely), so the f64 fma discards
                // information that decides the final rounding — a double-rounding
                // error in the oracle, not the circuit. Small-format fma needs an
                // exact big-integer oracle (future work); fma is validated for
                // F16(exact)/F32/F64 (native) and F128 (`rustc_apfloat`).

                let set2 = |a: &TermArena, t: TermId, xb: u128, yb: u128| {
                    let mut asg = Assignment::new();
                    asg.set(
                        sx,
                        Value::Bv {
                            width: total,
                            value: xb,
                        },
                    );
                    asg.set(
                        sy,
                        Value::Bv {
                            width: total,
                            value: yb,
                        },
                    );
                    match eval(a, t, &asg).unwrap() {
                        Value::Bv { value, .. } => value,
                        other => panic!("{other:?}"),
                    }
                };

                for i in 0..inputs.len() {
                    let xb = inputs[i];
                    let xf = fmt.decode_ieee_f64(xb);
                    // sqrt (unary)
                    {
                        let got = eval_bits(&a, t_sqrt, sx, xb);
                        let rf = xf.sqrt();
                        match expected(eb, sb, rf) {
                            Some(w) => assert_eq!(got, w, "sqrt {eb},{sb} x={xb:#x}"),
                            None => assert!(
                                is_nan_bits(got, eb, sb),
                                "sqrt {eb},{sb} x={xb:#x} want NaN got {got:#x}"
                            ),
                        }
                    }
                    // binary ops paired with another input
                    let yb = inputs[(i * 7 + 3) % inputs.len()];
                    let yf = fmt.decode_ieee_f64(yb);
                    for (t, rf, name) in [
                        (t_add, xf + yf, "add"),
                        (t_mul, xf * yf, "mul"),
                        (t_div, xf / yf, "div"),
                    ] {
                        let got = set2(&a, t, xb, yb);
                        match expected(eb, sb, rf) {
                            Some(w) => assert_eq!(got, w, "{name} {eb},{sb} x={xb:#x} y={yb:#x}"),
                            None => assert!(
                                is_nan_bits(got, eb, sb),
                                "{name} {eb},{sb} x={xb:#x} y={yb:#x} want NaN got {got:#x}"
                            ),
                        }
                    }
                }
            }
        }
    }
}

/// An exact big-integer oracle for `fp.fma`, and validation of the symbolic fma
/// circuit over small formats against it. `f64`'s `mul_add` is **not** a valid
/// oracle for small-format fma — the exact `a·b + c` can span far more than 53
/// bits when the product and addend exponents differ widely, so `f64` discards
/// information that decides the final rounding. This oracle instead forms the
/// exact sum with `WideUint` integers and rounds once, round-nearest-ties-to-even.
/// It is itself validated against native `f32::mul_add` (correctly rounded,
/// exercising the wide fused intermediate) before being trusted on small formats.
#[cfg(test)]
#[allow(
    clippy::cast_possible_truncation,
    clippy::many_single_char_names,
    clippy::similar_names
)]
mod fma_exact_oracle {
    use super::*;
    use axeyum_ir::{Assignment, Value, WideUint, eval};

    const FW: u32 = 4096; // exact-arithmetic width; covers eb ≤ 11 exponent spread

    #[allow(dead_code)] // Inf/Nan are classified but resolved via the f64 result
    enum Cls {
        Nan,
        Inf(bool),
        /// `(-1)^neg · mant · 2^e`; `mant == 0` is signed zero.
        Fin(bool, u128, i64),
    }

    fn classify(bits: u128, eb: u32, sb: u32) -> Cls {
        let total = eb + sb;
        let neg = (bits >> (total - 1)) & 1 == 1;
        let exp = (bits >> (sb - 1)) & ((1u128 << eb) - 1);
        let frac = bits & ((1u128 << (sb - 1)) - 1);
        let bias = (1i64 << (eb - 1)) - 1;
        if exp == (1u128 << eb) - 1 {
            return if frac == 0 { Cls::Inf(neg) } else { Cls::Nan };
        }
        if exp == 0 {
            return Cls::Fin(neg, frac, 1 - bias - i64::from(sb - 1));
        }
        Cls::Fin(
            neg,
            frac | (1u128 << (sb - 1)),
            i64::try_from(exp).unwrap() - bias - i64::from(sb - 1),
        )
    }

    fn inf_bits(eb: u32, sb: u32, neg: bool) -> u128 {
        let total = eb + sb;
        (u128::from(neg) << (total - 1)) | (((1u128 << eb) - 1) << (sb - 1))
    }
    fn zero_bits(eb: u32, sb: u32, neg: bool) -> u128 {
        u128::from(neg) << (eb + sb - 1)
    }

    /// Rounds `(-1)^neg · mag · 2^emin` (with `mag > 0`) to format `(eb, sb)`
    /// under round-nearest-ties-to-even, returning the IEEE bit pattern.
    fn round_mag(eb: u32, sb: u32, neg: bool, mag: &WideUint, emin: i64) -> u128 {
        let total = eb + sb;
        let bias = (1i64 << (eb - 1)) - 1;
        let bl = i64::from(mag.width() - mag.count_leading_zeros()); // significant bits ≥ 1
        let e_lead = emin + (bl - 1); // unbiased exponent of the leading bit
        let normal_lsb = e_lead - i64::from(sb - 1);
        let sub_lsb = 1 - bias - i64::from(sb - 1);
        let target_lsb = normal_lsb.max(sub_lsb);
        let shift = emin - target_lsb;
        // The significand fits in `sb+1` bits; take the low 128 of the wide value
        // (`to_u128` rejects a >128-bit *width*, even when the value is small).
        let q: u128 = if shift >= 0 {
            mag.shl(u32::try_from(shift).unwrap())
                .extract(127, 0)
                .to_u128()
        } else {
            let drop = u32::try_from(-shift).unwrap();
            let kept = mag.lshr(drop).extract(127, 0).to_u128();
            let round_bit = mag.bit(drop - 1);
            let sticky = (0..drop - 1).any(|i| mag.bit(i));
            let mut qv = kept;
            if round_bit && (sticky || (qv & 1 == 1)) {
                qv += 1;
            }
            qv
        };
        if q == 0 {
            return zero_bits(eb, sb, neg); // rounded away to ±0
        }
        let value_exp = target_lsb + i64::from(q.ilog2());
        let biased = value_exp + bias;
        if biased >= (1i64 << eb) - 1 {
            return inf_bits(eb, sb, neg); // overflow
        }
        if biased >= 1 {
            let frac = q & ((1u128 << (sb - 1)) - 1);
            (u128::from(neg) << (total - 1)) | (u128::try_from(biased).unwrap() << (sb - 1)) | frac
        } else {
            // subnormal: exponent field 0, `q` is the trailing significand.
            (u128::from(neg) << (total - 1)) | q
        }
    }

    /// Exact correctly-rounded (RNE) `fma(a, b, c)` in format `(eb, sb)`.
    /// Returns `None` to mean "a NaN" (compared by class, not bits).
    fn exact_fma(fmt: FloatFormat, ab: u128, bb: u128, cb: u128) -> Option<u128> {
        let (eb, sb) = (fmt.exp_bits, fmt.sig_bits);
        // Special cases (NaN/Inf) are precision-independent, so derive them from
        // f64 — exact for these small formats (eb ≤ 11 keeps values in range).
        let rf = fmt
            .decode_ieee_f64(ab)
            .mul_add(fmt.decode_ieee_f64(bb), fmt.decode_ieee_f64(cb));
        if rf.is_nan() {
            return None;
        }
        if rf.is_infinite() {
            return Some(inf_bits(eb, sb, rf.is_sign_negative()));
        }
        // All operands finite. Form the exact a·b + c with big integers.
        let Cls::Fin(an, am, ae) = classify(ab, eb, sb) else {
            unreachable!("finite (rf finite)")
        };
        let Cls::Fin(bn, bm, be) = classify(bb, eb, sb) else {
            unreachable!()
        };
        let Cls::Fin(cn, cm, ce) = classify(cb, eb, sb) else {
            unreachable!()
        };
        let pneg = an ^ bn;
        let pmant = am * bm; // ≤ 2^(2·sb), fits u128 for sb ≤ 64
        let pe = ae + be;
        let emin = pe.min(ce);
        let p = WideUint::from_u128(pmant, FW).shl(u32::try_from(pe - emin).unwrap());
        let c = WideUint::from_u128(cm, FW).shl(u32::try_from(ce - emin).unwrap());
        let (mag, rneg) = if pneg == cn {
            (p.add(&c), pneg)
        } else if p.uge(&c) {
            (p.sub(&c), pneg)
        } else {
            (c.sub(&p), cn)
        };
        if mag.is_zero() {
            // Exact zero: RNE gives +0 (sign of the f64 result is authoritative).
            return Some(zero_bits(eb, sb, rf.is_sign_negative()));
        }
        Some(round_mag(eb, sb, rneg, &mag, emin))
    }

    fn is_nan_bits(bits: u128, eb: u32, sb: u32) -> bool {
        let exp = (bits >> (sb - 1)) & ((1u128 << eb) - 1);
        let frac = bits & ((1u128 << (sb - 1)) - 1);
        exp == (1u128 << eb) - 1 && frac != 0
    }

    fn rng(state: &mut u64) -> u64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        *state
    }

    /// The oracle must agree with native `f32::mul_add` (IEEE correctly rounded),
    /// which exercises the wide fused intermediate the oracle's big-integer path
    /// is for. This validates the oracle before it judges small-format circuits.
    #[test]
    fn oracle_matches_native_f32_fma() {
        let f = FloatFormat::F32;
        let check = |xb: u32, yb: u32, zb: u32| {
            let got = exact_fma(f, u128::from(xb), u128::from(yb), u128::from(zb));
            let want = f32::from_bits(xb).mul_add(f32::from_bits(yb), f32::from_bits(zb));
            match got {
                None => assert!(
                    want.is_nan(),
                    "oracle NaN but native {want} for {xb:#x},{yb:#x},{zb:#x}"
                ),
                Some(bits) => {
                    assert!(
                        !want.is_nan(),
                        "oracle {bits:#x} but native NaN for {xb:#x},{yb:#x},{zb:#x}"
                    );
                    assert_eq!(
                        bits,
                        u128::from(want.to_bits()),
                        "fma {xb:#x},{yb:#x},{zb:#x}"
                    );
                }
            }
        };
        let structured: [u32; 10] = [
            0x0000_0000,
            0x8000_0000,
            0x3f80_0000,
            0xbf80_0000,
            0x4000_0000,
            0x7f80_0000,
            0xff80_0000,
            0x7fc0_0000,
            0x0080_0000,
            0x0000_0001,
        ];
        for &x in &structured {
            for &y in &structured {
                for &z in &structured {
                    check(x, y, z);
                }
            }
        }
        let mut s = 0xabcd_1234_5678_9f0fu64;
        for _ in 0..8000 {
            check(rng(&mut s) as u32, rng(&mut s) as u32, rng(&mut s) as u32);
        }
    }

    /// With the oracle trusted, the symbolic fma circuit must be correctly rounded
    /// over all small IEEE formats (`eb ≤ 10`, `sb ≤ 11`) — closing the last
    /// small-format arithmetic validation gap.
    #[test]
    fn small_format_fma_matches_exact_oracle() {
        let mut state = 0x0fee_1dad_c0de_2025u64;
        for eb in 2u32..=10 {
            for sb in 2u32..=11 {
                let fmt = FloatFormat {
                    exp_bits: eb,
                    sig_bits: sb,
                };
                if !fmt.is_ieee() {
                    continue; // (4,4)=FP8_E4M3 and (2,2)=FP4_E2M1 are non-IEEE
                }
                let total = eb + sb;
                let mask = (1u128 << total) - 1;
                let mut a = TermArena::new();
                let sx = a.declare("x", Sort::BitVec(total)).unwrap();
                let sy = a.declare("y", Sort::BitVec(total)).unwrap();
                let sz = a.declare("z", Sort::BitVec(total)).unwrap();
                let (x, y, z) = (a.var(sx), a.var(sy), a.var(sz));
                let t = fma(&mut a, fmt, x, y, z, RoundingMode::NearestEven).unwrap();
                for _ in 0..150 {
                    let xb = u128::from(rng(&mut state)) & mask;
                    let yb = u128::from(rng(&mut state)) & mask;
                    let zb = u128::from(rng(&mut state)) & mask;
                    let mut asg = Assignment::new();
                    asg.set(
                        sx,
                        Value::Bv {
                            width: total,
                            value: xb,
                        },
                    );
                    asg.set(
                        sy,
                        Value::Bv {
                            width: total,
                            value: yb,
                        },
                    );
                    asg.set(
                        sz,
                        Value::Bv {
                            width: total,
                            value: zb,
                        },
                    );
                    let got = match eval(&a, t, &asg).unwrap() {
                        Value::Bv { value, .. } => value,
                        other => panic!("{other:?}"),
                    };
                    match exact_fma(fmt, xb, yb, zb) {
                        None => assert!(
                            is_nan_bits(got, eb, sb),
                            "fma {eb},{sb} {xb:#x},{yb:#x},{zb:#x} want NaN got {got:#x}"
                        ),
                        Some(w) => assert_eq!(got, w, "fma {eb},{sb} {xb:#x},{yb:#x},{zb:#x}"),
                    }
                }
            }
        }
    }
}

#[cfg(test)]
#[allow(clippy::cast_precision_loss, clippy::cast_possible_truncation)]
mod int_to_fp_symbolic_tests {
    use super::*;
    use axeyum_ir::{Assignment, Value, eval};

    fn eval_bits(arena: &TermArena, t: TermId, sym: axeyum_ir::SymbolId, v: u128) -> u128 {
        let mut asg = Assignment::new();
        asg.set(
            sym,
            Value::Bv {
                width: 32,
                value: v,
            },
        );
        match eval(arena, t, &asg).unwrap() {
            Value::Bv { value, .. } => value,
            other => panic!("{other:?}"),
        }
    }

    #[test]
    fn symbolic_ubv_to_fp_matches_native_and_round_to_format() {
        // A symbolic 32-bit operand forces the pack_value circuit (not the
        // constant fold). Validate against native (RNE) and round_to_format (all
        // modes); 32-bit values are exact in f64, so f64 is the exact reference.
        let mut arena = TermArena::new();
        let s = arena.declare("x", Sort::BitVec(32)).unwrap();
        let x = arena.var(s);
        let modes = [
            RoundingMode::NearestEven,
            RoundingMode::NearestAway,
            RoundingMode::TowardZero,
            RoundingMode::TowardPositive,
            RoundingMode::TowardNegative,
        ];
        let vals: [u128; 12] = [
            0,
            1,
            2,
            3,
            5,
            255,
            1 << 23,
            (1 << 24) + 1,
            (1 << 24) + 3,
            0x7FFF_FFFF,
            0xFFFF_FFFF,
            0xFFFF_FF81,
        ];
        for mode in modes {
            let t = ubv_to_fp(&mut arena, FloatFormat::F32, x, mode)
                .unwrap()
                .unwrap();
            for &v in &vals {
                let got = eval_bits(&arena, t, s, v);
                let want = round_to_format(8, 24, v as f64, mode);
                assert_eq!(
                    got, want,
                    "ubv {v} mode {mode:?}: got {got:#x} want {want:#x}"
                );
                if mode == RoundingMode::NearestEven {
                    assert_eq!(got, u128::from((v as f32).to_bits()), "ubv {v} vs native");
                }
            }
        }
    }

    #[test]
    fn symbolic_sbv_to_fp_matches_native_and_round_to_format() {
        let mut arena = TermArena::new();
        let s = arena.declare("y", Sort::BitVec(32)).unwrap();
        let y = arena.var(s);
        let to_signed = |v: u128| -> i64 {
            if v >> 31 & 1 == 1 {
                (v as i64) - (1i64 << 32)
            } else {
                v as i64
            }
        };
        let modes = [
            RoundingMode::NearestEven,
            RoundingMode::TowardZero,
            RoundingMode::TowardPositive,
            RoundingMode::TowardNegative,
        ];
        let vals: [u128; 10] = [
            0,
            1,
            0xFFFF_FFFF,
            0xFFFF_FFFE,
            0x8000_0000,
            0x7FFF_FFFF,
            5,
            0xFFFF_FF81,
            (1 << 24) + 1,
            0x8000_0001,
        ];
        for mode in modes {
            let t = sbv_to_fp(&mut arena, FloatFormat::F32, y, mode)
                .unwrap()
                .unwrap();
            for &v in &vals {
                let sv = to_signed(v);
                let got = eval_bits(&arena, t, s, v);
                let want = round_to_format(8, 24, sv as f64, mode);
                assert_eq!(
                    got, want,
                    "sbv {sv} mode {mode:?}: got {got:#x} want {want:#x}"
                );
                if mode == RoundingMode::NearestEven {
                    assert_eq!(got, u128::from((sv as f32).to_bits()), "sbv {sv} vs native");
                }
            }
        }
    }
}

#[cfg(test)]
#[allow(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::float_cmp
)]
mod fp_to_int_symbolic_tests {
    use super::*;
    use axeyum_ir::{Assignment, Value, eval};

    // The symbolic FP->int circuit must match the validated constant fold on
    // in-range inputs, and route out-of-range / NaN / inf to the fresh value.
    fn check(signed: bool) {
        let modes = [
            RoundingMode::NearestEven,
            RoundingMode::TowardZero,
            RoundingMode::TowardPositive,
            RoundingMode::TowardNegative,
        ];
        let vals: [f32; 14] = [
            0.0,
            -0.0,
            2.7,
            -2.7,
            5.0,
            -5.0,
            0.5,
            -0.5,
            1.5,
            127.0,
            -128.0,
            130.0,
            f32::NAN,
            f32::INFINITY,
        ];
        for &width in &[8u32, 16, 32] {
            for mode in modes {
                let mut a = TermArena::new();
                let xs = a.declare("x", Sort::BitVec(32)).unwrap();
                let x = a.var(xs);
                let fs = a.declare("fresh", Sort::BitVec(width)).unwrap();
                let fresh = a.var(fs);
                let t = if signed {
                    to_sbv_sym(&mut a, FloatFormat::F32, mode, x, width, fresh).unwrap()
                } else {
                    to_ubv_sym(&mut a, FloatFormat::F32, mode, x, width, fresh).unwrap()
                };
                for &v in &vals {
                    let bits = u128::from(v.to_bits());
                    // Reference: the validated constant fold (None = unspecified).
                    let cx = a.bv_const(32, bits).unwrap();
                    let want = if signed {
                        to_sbv(&mut a, FloatFormat::F32, mode, cx, width).unwrap()
                    } else {
                        to_ubv(&mut a, FloatFormat::F32, mode, cx, width).unwrap()
                    };
                    let fresh_val = 0xA5u128 & ((1u128 << width) - 1);
                    let mut asg = Assignment::new();
                    asg.set(
                        xs,
                        Value::Bv {
                            width: 32,
                            value: bits,
                        },
                    );
                    asg.set(
                        fs,
                        Value::Bv {
                            width,
                            value: fresh_val,
                        },
                    );
                    let got = match eval(&a, t, &asg).unwrap() {
                        Value::Bv { value, .. } => value,
                        other => panic!("{other:?}"),
                    };
                    match want {
                        Some(rt) => {
                            // In range: pinned to the rounded value (fold reference).
                            let w_ref = match eval(&a, rt, &Assignment::new()).unwrap() {
                                Value::Bv { value, .. } => value,
                                other => panic!("{other:?}"),
                            };
                            assert_eq!(
                                got,
                                w_ref,
                                "{} v={v} width={width} mode={mode:?}: got {got:#x} want {w_ref:#x}",
                                if signed { "sbv" } else { "ubv" }
                            );
                        }
                        None => {
                            // Unspecified: must route to the fresh (unconstrained) value.
                            assert_eq!(
                                got,
                                fresh_val,
                                "{} v={v} width={width} mode={mode:?}: out-of-range must be fresh",
                                if signed { "sbv" } else { "ubv" }
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn symbolic_to_ubv_matches_fold_in_range_and_fresh_out_of_range() {
        check(false);
    }

    #[test]
    fn symbolic_to_sbv_matches_fold_in_range_and_fresh_out_of_range() {
        check(true);
    }

    /// `from_sbv`/`from_ubv` (integer→float, round-nearest-even) match Rust's own
    /// `as f32`/`as f64` integer-to-float casts — the IEEE-754 ground truth — over
    /// edge values and a pseudo-random sweep. Confirms the SMT-LIB
    /// `(_ to_fp eb sb) RM bv` conversion (both signed and unsigned readings).
    #[test]
    #[allow(clippy::cast_precision_loss, clippy::similar_names)] // the rounding cast IS the oracle
    fn int_to_float_matches_native_casts() {
        let mut a = TermArena::new();
        let rne = RoundingMode::NearestEven;
        let bits = |a: &mut TermArena, t| match eval(a, t, &Assignment::new()) {
            Ok(Value::Bv { value, .. }) => value,
            other => panic!("expected Bv, got {other:?}"),
        };

        // Signed 32→F32 against `i32 as f32`.
        let chk_s32 = |a: &mut TermArena, v: i32| {
            #[allow(clippy::cast_sign_loss)]
            let xt = a.bv_const(32, u128::from(v as u32)).unwrap();
            let r = from_sbv(a, FloatFormat::F32, rne, xt).unwrap();
            assert_eq!(
                bits(a, r),
                u128::from((v as f32).to_bits()),
                "i32 {v} as f32"
            );
        };
        for v in [
            0i32,
            1,
            -1,
            2,
            -2,
            5,
            -5,
            16_777_217,
            -16_777_217,
            i32::MIN,
            i32::MAX,
            123_456_789,
        ] {
            chk_s32(&mut a, v);
        }
        // Unsigned 32→F32 against `u32 as f32`.
        let chk_u32 = |a: &mut TermArena, v: u32| {
            let xt = a.bv_const(32, u128::from(v)).unwrap();
            let r = from_ubv(a, FloatFormat::F32, rne, xt).unwrap();
            assert_eq!(
                bits(a, r),
                u128::from((v as f32).to_bits()),
                "u32 {v} as f32"
            );
        };
        for v in [0u32, 1, 2, 16_777_217, u32::MAX, 0x8000_0000, 3_000_000_001] {
            chk_u32(&mut a, v);
        }
        // Signed 64→F64 against `i64 as f64`.
        let chk_s64 = |a: &mut TermArena, v: i64| {
            #[allow(clippy::cast_sign_loss)]
            let xt = a.bv_const(64, u128::from(v as u64)).unwrap();
            let r = from_sbv(a, FloatFormat::F64, rne, xt).unwrap();
            assert_eq!(
                bits(a, r),
                u128::from((v as f64).to_bits()),
                "i64 {v} as f64"
            );
        };
        for v in [
            0i64,
            1,
            -1,
            i64::MIN,
            i64::MAX,
            9_007_199_254_740_993,
            -9_007_199_254_740_993,
        ] {
            chk_s64(&mut a, v);
        }

        // Pseudo-random sweep (signed 32→F32 and unsigned 64→F64).
        let mut state = 0x1234_5678_9abc_def0u64;
        for _ in 0..3000 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            #[allow(clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
            let s = state as u32 as i32;
            chk_s32(&mut a, s);
            let u = state; // full u64
            let xt = a.bv_const(64, u128::from(u)).unwrap();
            let r = from_ubv(&mut a, FloatFormat::F64, rne, xt).unwrap();
            assert_eq!(
                bits(&mut a, r),
                u128::from((u as f64).to_bits()),
                "u64 {u} as f64"
            );
        }
    }

    /// Integer→float under **all five rounding modes** matches `rustc_apfloat`'s
    /// correctly-rounded `from_i128_r` (Rust's `as` casts only cover round-nearest).
    /// Uses values whose magnitude exceeds 24 bits so the mode actually matters.
    #[test]
    fn int_to_float_directed_modes_match_apfloat() {
        use rustc_apfloat::Float;
        use rustc_apfloat::ieee::Single;
        let bits = |a: &mut TermArena, t| match eval(a, t, &Assignment::new()) {
            Ok(Value::Bv { value, .. }) => value,
            other => panic!("expected Bv, got {other:?}"),
        };
        let ap_round = |mode: RoundingMode| match mode {
            RoundingMode::NearestEven => rustc_apfloat::Round::NearestTiesToEven,
            RoundingMode::NearestAway => rustc_apfloat::Round::NearestTiesToAway,
            RoundingMode::TowardZero => rustc_apfloat::Round::TowardZero,
            RoundingMode::TowardPositive => rustc_apfloat::Round::TowardPositive,
            RoundingMode::TowardNegative => rustc_apfloat::Round::TowardNegative,
        };
        let modes = [
            RoundingMode::NearestEven,
            RoundingMode::NearestAway,
            RoundingMode::TowardZero,
            RoundingMode::TowardPositive,
            RoundingMode::TowardNegative,
        ];
        for &v in &[
            16_777_217i32, // 2^24 + 1, needs rounding to F32
            16_777_219,
            -16_777_217,
            33_554_435,
            2_147_483_647,  // i32::MAX
            -2_147_483_648, // i32::MIN
            123_456_789,
            -123_456_789,
        ] {
            for mode in modes {
                let mut a = TermArena::new();
                #[allow(clippy::cast_sign_loss)]
                let xt = a.bv_const(32, u128::from(v as u32)).unwrap();
                let r = from_sbv(&mut a, FloatFormat::F32, mode, xt).unwrap();
                let got = bits(&mut a, r);
                let oracle = Single::from_i128_r(i128::from(v), ap_round(mode))
                    .value
                    .to_bits();
                assert_eq!(got, oracle, "i32 {v} → F32 mode {mode:?}");
            }
        }
    }

    // --- fp.min / fp.max opposite-sign-zero nondeterminism (issue208) ---------

    /// On opposite-sign zeros `fp.min`/`fp.max` is SMT-LIB-*unspecified*: the
    /// result may be `+0` OR `−0`, and the choice may differ between argument
    /// orders. The fix encodes a *fresh per-application* sign bit so:
    ///   * `fp.max(+0,−0)` and `fp.max(−0,+0)` CAN differ (the sat model that
    ///     `(distinct …)` needs — what was a wrong-`unsat` before),
    ///   * the SAME syntactic term is self-consistent (a real function),
    ///   * a non-opposite-sign case stays the deterministic ordered pick.
    #[test]
    fn min_max_opposite_sign_zero_is_free_per_application() {
        const POS0: u128 = 0;
        const NEG0: u128 = 1u128 << 63; // F64 sign bit

        let bit = |a: &TermArena, t, asg: &Assignment| match eval(a, t, asg) {
            Ok(Value::Bv { value, .. }) => value,
            other => panic!("expected a bit-vector value, got {other:?}"),
        };

        let mut a = TermArena::new();
        let xp = a.bv_const(64, POS0).unwrap(); // +0
        let yn = a.bv_const(64, NEG0).unwrap(); // −0

        // Two distinct applications of fp.max with swapped argument order.
        let m_xy = max(&mut a, FloatFormat::F64, xp, yn).unwrap();
        let m_yx = max(&mut a, FloatFormat::F64, yn, xp).unwrap();
        // The SAME syntactic application reuses its fresh bit (structural hash).
        let m_xy2 = max(&mut a, FloatFormat::F64, xp, yn).unwrap();
        assert_eq!(m_xy, m_xy2, "same fp.max application must reuse its term");

        // The fresh sign bits are deterministically named per application
        // (`<flavor>.signzero.<x>.<y>`); look them up by that exact name.
        let s_xy = a
            .find_symbol(&format!(
                "axeyum_fp.max.signzero.{}.{}",
                xp.index(),
                yn.index()
            ))
            .expect("fp.max(+0,−0) declared its fresh sign bit");
        let s_yx = a
            .find_symbol(&format!(
                "axeyum_fp.max.signzero.{}.{}",
                yn.index(),
                xp.index()
            ))
            .expect("fp.max(−0,+0) declared its fresh sign bit");
        assert_ne!(s_xy, s_yx, "swapped-order applications get distinct bits");

        // Witness that the two applications CAN differ: set m_xy → +0, m_yx → −0.
        // This is precisely the model the issue208 `(distinct …)` needs; a
        // deterministic encoding would have made them equal (wrong unsat).
        let mut differ = Assignment::new();
        differ.set(s_xy, Value::Bv { width: 1, value: 0 }); // +0
        differ.set(s_yx, Value::Bv { width: 1, value: 1 }); // −0
        assert_eq!(bit(&a, m_xy, &differ), POS0);
        assert_eq!(bit(&a, m_yx, &differ), NEG0);
        assert_ne!(
            bit(&a, m_xy, &differ),
            bit(&a, m_yx, &differ),
            "opposite-sign-zero fp.max results must be free to differ",
        );

        // They CAN also coincide (the choice is genuinely free both ways).
        let mut same = Assignment::new();
        same.set(s_xy, Value::Bv { width: 1, value: 1 });
        same.set(s_yx, Value::Bv { width: 1, value: 1 });
        assert_eq!(bit(&a, m_xy, &same), bit(&a, m_yx, &same));

        // The result is always a valid ±0 bit pattern (no spurious magnitude).
        for v in [0u128, 1] {
            let mut asg = Assignment::new();
            asg.set(s_xy, Value::Bv { width: 1, value: v });
            let r = bit(&a, m_xy, &asg);
            assert!(r == POS0 || r == NEG0, "result must be ±0, got {r:#x}");
        }
    }

    /// `fp.min` over opposite-sign zeros is symmetric to `fp.max`, and a NON-zero
    /// `fp.min`/`fp.max` stays the deterministic ordered pick (the override only
    /// fires on the genuinely-unspecified both-zero-opposite-sign case).
    #[test]
    fn min_nonzero_stays_deterministic_and_zero_case_is_free() {
        const POS0: u128 = 0;
        const NEG0: u128 = 1u128 << 63;
        // Two finite F64 values: 1.0 = 0x3FF0…, 2.0 = 0x4000…
        const ONE: u128 = 0x3FF0_0000_0000_0000;
        const TWO: u128 = 0x4000_0000_0000_0000;

        let bit = |a: &TermArena, t, asg: &Assignment| match eval(a, t, asg) {
            Ok(Value::Bv { value, .. }) => value,
            other => panic!("expected a bit-vector value, got {other:?}"),
        };

        let mut a = TermArena::new();
        let one = a.bv_const(64, ONE).unwrap();
        let two = a.bv_const(64, TWO).unwrap();
        let mn = min(&mut a, FloatFormat::F64, one, two).unwrap();
        let mx = max(&mut a, FloatFormat::F64, one, two).unwrap();
        // The opposite-sign-zero guard is structurally present but evaluates
        // false here (1.0/2.0 are not zero), so the ordered pick is fully
        // determined regardless of the (unconstrained) fresh sign bits — bind
        // them arbitrarily to evaluate, and try BOTH values to prove the pick
        // does not depend on them.
        let signzero_ids: Vec<axeyum_ir::SymbolId> = a
            .symbols()
            .filter(|(_, name, _)| name.contains(".signzero."))
            .map(|(sid, _, _)| sid)
            .collect();
        for v in [0u128, 1] {
            let mut asg = Assignment::new();
            for &sid in &signzero_ids {
                asg.set(sid, Value::Bv { width: 1, value: v });
            }
            assert_eq!(bit(&a, mn, &asg), ONE, "min(1,2) = 1, deterministic");
            assert_eq!(bit(&a, mx, &asg), TWO, "max(1,2) = 2, deterministic");
        }

        // fp.min on opposite-sign zeros is free (mirror of the fp.max test).
        let xp = a.bv_const(64, POS0).unwrap();
        let yn = a.bv_const(64, NEG0).unwrap();
        let mn_xy = min(&mut a, FloatFormat::F64, xp, yn).unwrap();
        let mn_yx = min(&mut a, FloatFormat::F64, yn, xp).unwrap();
        let s_xy = a
            .find_symbol(&format!(
                "axeyum_fp.min.signzero.{}.{}",
                xp.index(),
                yn.index()
            ))
            .expect("fp.min(+0,−0) declared its fresh sign bit");
        let s_yx = a
            .find_symbol(&format!(
                "axeyum_fp.min.signzero.{}.{}",
                yn.index(),
                xp.index()
            ))
            .expect("fp.min(−0,+0) declared its fresh sign bit");
        let mut differ = Assignment::new();
        differ.set(s_xy, Value::Bv { width: 1, value: 0 });
        differ.set(s_yx, Value::Bv { width: 1, value: 1 });
        assert_ne!(
            bit(&a, mn_xy, &differ),
            bit(&a, mn_yx, &differ),
            "opposite-sign-zero fp.min results must be free to differ",
        );
    }
}
