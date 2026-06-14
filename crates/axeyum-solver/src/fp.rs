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
//! `isSubnormal`/`isNegative`/`isPositive`), `abs`/`neg`, `eq`, and the four
//! comparisons. **Not** here: arithmetic (`add`/`mul`/`div`/`sqrt`/`fma`/
//! `roundToIntegral`) and real/int conversions, which require correct rounding —
//! the harder next layer, deferred deliberately rather than done unsoundly.
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

    /// Total bit width of a value in this format.
    #[must_use]
    pub const fn width(self) -> u32 {
        self.exp_bits + self.sig_bits
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
}
