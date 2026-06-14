//! Arbitrary-width unsigned bit-vector arithmetic (the foundation for lifting the
//! `u128`/`MAX_BV_WIDTH = 128` ceiling).
//!
//! `Value::Bv` and `TermNode::BvConst` currently store a `u128`, capping
//! bit-vectors at 128 bits — which blocks, e.g., the F64 `fp.fma` symbolic
//! circuit (a `3·sig + 5 = 164`-bit intermediate). [`WideUint`] is the
//! limb-based unsigned integer those will eventually carry for wider widths; it
//! implements the bit-vector operator semantics (wrapping mod `2^width`) over
//! little-endian `u64` limbs.
//!
//! Every operation is validated against the native `u128` reference for all
//! widths `≤ 128` (see the tests), so wiring it in keeps the existing semantics
//! exactly. It is not yet referenced by the evaluator; that integration (a
//! `Value::WideBv` / `TermNode::WideBvConst` variant threaded through `eval`,
//! `bits`, and the arena) is the next step and is gated on this validated core.
#![allow(dead_code)] // foundation for >128-bit bit-vectors; wired in a follow-up.
// Limb arithmetic deliberately takes the low 64/32 bits of wider intermediates.
#![allow(clippy::cast_possible_truncation)]

/// An unsigned bit-vector value of a fixed `width`, stored little-endian as
/// `u64` limbs and always masked to `width` (bits above `width` are zero).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct WideUint {
    width: u32,
    /// Little-endian limbs; `limbs.len() == ceil(width / 64)` (≥ 1).
    limbs: Vec<u64>,
}

/// Number of 64-bit limbs needed for `width` bits (at least one).
fn limb_count(width: u32) -> usize {
    (width.max(1) as usize).div_ceil(64)
}

impl WideUint {
    /// The all-zero value of `width` bits.
    #[must_use]
    pub fn zero(width: u32) -> Self {
        Self {
            width,
            limbs: vec![0; limb_count(width)],
        }
    }

    /// The width in bits.
    #[must_use]
    pub fn width(&self) -> u32 {
        self.width
    }

    /// A `width`-bit value from a `u128` (reduced mod `2^width`).
    #[must_use]
    pub fn from_u128(value: u128, width: u32) -> Self {
        let mut v = Self::zero(width);
        let masked = value & low_mask_u128(width);
        if !v.limbs.is_empty() {
            v.limbs[0] = masked as u64;
        }
        if v.limbs.len() > 1 {
            v.limbs[1] = (masked >> 64) as u64;
        }
        v.mask();
        v
    }

    /// The value as a `u128`, valid when `width ≤ 128`.
    ///
    /// # Panics
    ///
    /// Panics if `width > 128` (the value does not fit a `u128`).
    #[must_use]
    pub fn to_u128(&self) -> u128 {
        assert!(self.width <= 128, "to_u128 on a {}-bit value", self.width);
        let lo = u128::from(self.limbs.first().copied().unwrap_or(0));
        let hi = u128::from(self.limbs.get(1).copied().unwrap_or(0));
        (hi << 64) | lo
    }

    /// Clears any bits at or above `width` in the top limb.
    fn mask(&mut self) {
        let bits_in_top = self.width % 64;
        if bits_in_top != 0
            && let Some(top) = self.limbs.last_mut()
        {
            *top &= (1u64 << bits_in_top) - 1;
        }
        // (When width % 64 == 0 the top limb is fully used; nothing to clear.)
    }

    /// Bit `i` (`0` = least significant), or `false` if `i ≥ width`.
    #[must_use]
    pub fn bit(&self, i: u32) -> bool {
        if i >= self.width {
            return false;
        }
        (self.limbs[(i / 64) as usize] >> (i % 64)) & 1 == 1
    }

    /// `self + other` mod `2^width` (both must have the same width).
    #[must_use]
    pub fn add(&self, other: &Self) -> Self {
        debug_assert_eq!(self.width, other.width);
        let mut out = Self::zero(self.width);
        let mut carry = 0u128;
        for i in 0..out.limbs.len() {
            let sum = u128::from(self.limbs[i]) + u128::from(other.limbs[i]) + carry;
            out.limbs[i] = sum as u64;
            carry = sum >> 64;
        }
        out.mask();
        out
    }

    /// `self - other` mod `2^width` (two's-complement wrap).
    #[must_use]
    pub fn sub(&self, other: &Self) -> Self {
        self.add(&other.neg())
    }

    /// `-self` mod `2^width` (two's-complement negation).
    #[must_use]
    pub fn neg(&self) -> Self {
        let one = Self::from_u128(1, self.width);
        self.not().add(&one)
    }

    /// `self * other` mod `2^width`.
    #[must_use]
    pub fn mul(&self, other: &Self) -> Self {
        debug_assert_eq!(self.width, other.width);
        let n = self.limbs.len();
        let mut acc = vec![0u64; n];
        for i in 0..n {
            let mut carry = 0u128;
            for j in 0..(n - i) {
                let cur = u128::from(acc[i + j])
                    + u128::from(self.limbs[i]) * u128::from(other.limbs[j])
                    + carry;
                acc[i + j] = cur as u64;
                carry = cur >> 64;
            }
            // Higher carry falls off the top (mod 2^width).
        }
        let mut out = Self {
            width: self.width,
            limbs: acc,
        };
        out.mask();
        out
    }

    /// Bitwise NOT (masked to `width`).
    #[must_use]
    pub fn not(&self) -> Self {
        let mut out = Self {
            width: self.width,
            limbs: self.limbs.iter().map(|l| !l).collect(),
        };
        out.mask();
        out
    }

    /// Bitwise AND (same width).
    #[must_use]
    pub fn and(&self, other: &Self) -> Self {
        self.zip_with(other, |a, b| a & b)
    }

    /// Bitwise OR (same width).
    #[must_use]
    pub fn or(&self, other: &Self) -> Self {
        self.zip_with(other, |a, b| a | b)
    }

    /// Bitwise XOR (same width).
    #[must_use]
    pub fn xor(&self, other: &Self) -> Self {
        self.zip_with(other, |a, b| a ^ b)
    }

    fn zip_with(&self, other: &Self, f: impl Fn(u64, u64) -> u64) -> Self {
        debug_assert_eq!(self.width, other.width);
        let mut out = Self {
            width: self.width,
            limbs: self
                .limbs
                .iter()
                .zip(&other.limbs)
                .map(|(&a, &b)| f(a, b))
                .collect(),
        };
        out.mask();
        out
    }

    /// Logical left shift by `amount` bits (mod `2^width`).
    #[must_use]
    pub fn shl(&self, amount: u32) -> Self {
        let mut out = Self::zero(self.width);
        if amount >= self.width {
            return out;
        }
        let limb_shift = (amount / 64) as usize;
        let bit_shift = amount % 64;
        for i in (0..out.limbs.len()).rev() {
            if i < limb_shift {
                continue;
            }
            let src = i - limb_shift;
            let mut v = self.limbs[src] << bit_shift;
            if bit_shift != 0 && src >= 1 {
                v |= self.limbs[src - 1] >> (64 - bit_shift);
            }
            out.limbs[i] = v;
        }
        out.mask();
        out
    }

    /// Logical right shift by `amount` bits (zero-fill).
    #[must_use]
    pub fn lshr(&self, amount: u32) -> Self {
        let mut out = Self::zero(self.width);
        if amount >= self.width {
            return out;
        }
        let limb_shift = (amount / 64) as usize;
        let bit_shift = amount % 64;
        let n = out.limbs.len();
        for i in 0..n {
            let src = i + limb_shift;
            if src >= n {
                break;
            }
            let mut v = self.limbs[src] >> bit_shift;
            if bit_shift != 0 && src + 1 < n {
                v |= self.limbs[src + 1] << (64 - bit_shift);
            }
            out.limbs[i] = v;
        }
        out.mask();
        out
    }

    /// Unsigned `self < other` (same width).
    #[must_use]
    pub fn ult(&self, other: &Self) -> bool {
        debug_assert_eq!(self.width, other.width);
        for i in (0..self.limbs.len()).rev() {
            if self.limbs[i] != other.limbs[i] {
                return self.limbs[i] < other.limbs[i];
            }
        }
        false
    }

    /// Unsigned `self ≤ other`.
    #[must_use]
    pub fn ule(&self, other: &Self) -> bool {
        !other.ult(self)
    }

    /// `true` if every bit is zero.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.limbs.iter().all(|&l| l == 0)
    }

    /// Unsigned `self ≥ other`.
    #[must_use]
    pub fn uge(&self, other: &Self) -> bool {
        !self.ult(other)
    }

    /// The top (sign) bit.
    #[must_use]
    pub fn is_negative(&self) -> bool {
        self.bit(self.width - 1)
    }

    /// Sets bit `i` to one (no-op if `i ≥ width`).
    fn set_bit(&mut self, i: u32) {
        if i < self.width {
            self.limbs[(i / 64) as usize] |= 1u64 << (i % 64);
        }
    }

    /// The all-ones value of `width` bits.
    #[must_use]
    pub fn ones(width: u32) -> Self {
        Self::zero(width).not()
    }

    /// `(quotient, remainder)` of unsigned division with SMT-LIB totality:
    /// dividing by zero yields all-ones / the dividend. Restoring long division.
    #[must_use]
    pub fn udivrem(&self, divisor: &Self) -> (Self, Self) {
        debug_assert_eq!(self.width, divisor.width);
        if divisor.is_zero() {
            return (Self::ones(self.width), self.clone());
        }
        let mut q = Self::zero(self.width);
        let mut r = Self::zero(self.width);
        for i in (0..self.width).rev() {
            r = r.shl(1);
            if self.bit(i) {
                r.set_bit(0);
            }
            if r.uge(divisor) {
                r = r.sub(divisor);
                q.set_bit(i);
            }
        }
        (q, r)
    }

    /// Unsigned quotient (`bvudiv`, `÷0 = all-ones`).
    #[must_use]
    pub fn udiv(&self, d: &Self) -> Self {
        self.udivrem(d).0
    }

    /// Unsigned remainder (`bvurem`, `rem 0 = self`).
    #[must_use]
    pub fn urem(&self, d: &Self) -> Self {
        self.udivrem(d).1
    }

    /// Signed quotient (`bvsdiv`): magnitudes divided, sign by XOR; `÷0` per
    /// SMT-LIB totality (`1` if `self ≥ 0`, `-1` if `self < 0`).
    #[must_use]
    pub fn sdiv(&self, d: &Self) -> Self {
        if d.is_zero() {
            return if self.is_negative() {
                Self::from_u128(1, self.width)
            } else {
                Self::ones(self.width)
            };
        }
        let (an, a) = abs(self);
        let (bn, b) = abs(d);
        let q = a.udiv(&b);
        if an ^ bn { q.neg() } else { q }
    }

    /// Signed remainder (`bvsrem`): sign follows the dividend; `rem 0 = self`.
    #[must_use]
    pub fn srem(&self, d: &Self) -> Self {
        if d.is_zero() {
            return self.clone();
        }
        let (an, a) = abs(self);
        let (_, b) = abs(d);
        let r = a.urem(&b);
        if an { r.neg() } else { r }
    }

    /// Signed modulo (`bvsmod`): sign follows the divisor; `mod 0 = self`.
    #[must_use]
    pub fn smod(&self, d: &Self) -> Self {
        if d.is_zero() {
            return self.clone();
        }
        let (an, a) = abs(self);
        let (bn, b) = abs(d);
        let u = a.urem(&b);
        if u.is_zero() {
            return u;
        }
        // Combine signs per SMT-LIB bvsmod.
        match (an, bn) {
            (false, false) => u,
            (true, false) => b.sub(&u),
            (false, true) => b.sub(&u).neg(),
            (true, true) => u.neg(),
        }
    }

    /// Arithmetic right shift by `amount` (sign-replicating).
    #[must_use]
    pub fn ashr(&self, amount: u32) -> Self {
        let logical = self.lshr(amount);
        if !self.is_negative() || amount == 0 {
            return logical;
        }
        // OR in the sign-fill: the top `min(amount,width)` bits become one.
        let fill = amount.min(self.width);
        let top_ones = Self::ones(self.width).shl(self.width - fill);
        logical.or(&top_ones)
    }

    /// Signed `self < other`.
    #[must_use]
    pub fn slt(&self, other: &Self) -> bool {
        match (self.is_negative(), other.is_negative()) {
            (true, false) => true,
            (false, true) => false,
            _ => self.ult(other), // same sign: unsigned order agrees
        }
    }

    /// Signed `self ≤ other`.
    #[must_use]
    pub fn sle(&self, other: &Self) -> bool {
        !other.slt(self)
    }

    /// Bits `[lo, hi]` (inclusive) as a `hi − lo + 1`-bit value.
    #[must_use]
    pub fn extract(&self, hi: u32, lo: u32) -> Self {
        debug_assert!(hi >= lo && hi < self.width);
        let out_w = hi - lo + 1;
        let shifted = self.lshr(lo);
        let mut out = Self::zero(out_w);
        for i in 0..out.limbs.len() {
            out.limbs[i] = shifted.limbs.get(i).copied().unwrap_or(0);
        }
        out.mask();
        out
    }

    /// Concatenation `self ++ low` (self is the high part).
    #[must_use]
    pub fn concat(&self, low: &Self) -> Self {
        let out_w = self.width + low.width;
        // Place `self` above `low`: (zext self to out_w) << low.width | (zext low).
        let hi = self.zero_ext(out_w - self.width).shl(low.width);
        let lo = low.zero_ext(out_w - low.width);
        hi.or(&lo)
    }

    /// Zero-extend by `by` bits.
    #[must_use]
    pub fn zero_ext(&self, by: u32) -> Self {
        let mut out = Self::zero(self.width + by);
        for i in 0..self.limbs.len() {
            out.limbs[i] = self.limbs[i];
        }
        out.mask();
        out
    }

    /// Sign-extend by `by` bits.
    #[must_use]
    pub fn sign_ext(&self, by: u32) -> Self {
        let z = self.zero_ext(by);
        if !self.is_negative() || by == 0 {
            return z;
        }
        // Set the new high `by` bits.
        let fill = Self::ones(z.width).shl(self.width);
        z.or(&fill)
    }

    /// The bits LSB-first (index `i` is bit `i`), length `width` — the order the
    /// IR's `bits` layer and the bit-blaster use (ADR-0006).
    #[must_use]
    pub fn to_lsb_bits(&self) -> Vec<bool> {
        (0..self.width).map(|i| self.bit(i)).collect()
    }

    /// Builds a `bits.len()`-bit value from LSB-first bits (index `i` is bit `i`).
    #[must_use]
    pub fn from_lsb_bits(bits: &[bool]) -> Self {
        let width = u32::try_from(bits.len()).expect("bit count fits u32");
        let mut v = Self::zero(width);
        for (i, &b) in bits.iter().enumerate() {
            if b {
                v.set_bit(u32::try_from(i).expect("bit index fits u32"));
            }
        }
        v
    }

    /// Number of leading zero bits (from the MSB); `width` if all-zero.
    #[must_use]
    pub fn count_leading_zeros(&self) -> u32 {
        for i in (0..self.width).rev() {
            if self.bit(i) {
                return self.width - 1 - i;
            }
        }
        self.width
    }
}

/// `(is_negative, |value|)` as an unsigned magnitude of the same width.
fn abs(v: &WideUint) -> (bool, WideUint) {
    if v.is_negative() {
        (true, v.neg())
    } else {
        (false, v.clone())
    }
}

/// Mask of the low `width` bits within a `u128` (all ones if `width ≥ 128`).
fn low_mask_u128(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

#[cfg(test)]
#[allow(
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names
)]
mod tests {
    use super::*;

    // A small linear-congruential generator (no external deps, deterministic).
    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u128 {
            self.0 = self.0.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            let hi = u128::from(self.0);
            self.0 = self.0.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (hi << 64) | u128::from(self.0)
        }
    }

    fn mask128(v: u128, w: u32) -> u128 {
        v & low_mask_u128(w)
    }

    #[test]
    fn ops_match_u128_reference_over_widths() {
        let mut rng = Lcg(0x1234_5678_9abc_def0);
        for width in [1u32, 2, 7, 8, 31, 32, 63, 64, 65, 100, 127, 128] {
            for _ in 0..200 {
                let a = mask128(rng.next(), width);
                let b = mask128(rng.next(), width);
                let wa = WideUint::from_u128(a, width);
                let wb = WideUint::from_u128(b, width);
                assert_eq!(wa.to_u128(), a, "round-trip a width {width}");
                assert_eq!(wb.to_u128(), b, "round-trip b width {width}");
                assert_eq!(wa.add(&wb).to_u128(), a.wrapping_add(b) & low_mask_u128(width), "add {width}");
                assert_eq!(wa.sub(&wb).to_u128(), a.wrapping_sub(b) & low_mask_u128(width), "sub {width}");
                assert_eq!(wa.mul(&wb).to_u128(), a.wrapping_mul(b) & low_mask_u128(width), "mul {width}");
                assert_eq!(wa.neg().to_u128(), a.wrapping_neg() & low_mask_u128(width), "neg {width}");
                assert_eq!(wa.not().to_u128(), !a & low_mask_u128(width), "not {width}");
                assert_eq!(wa.and(&wb).to_u128(), a & b, "and {width}");
                assert_eq!(wa.or(&wb).to_u128(), a | b, "or {width}");
                assert_eq!(wa.xor(&wb).to_u128(), a ^ b, "xor {width}");
                assert_eq!(wa.ult(&wb), a < b, "ult {width}");
                assert_eq!(wa.ule(&wb), a <= b, "ule {width}");
                for sh in [0u32, 1, 7, 63, 64, 65, width.saturating_sub(1), width] {
                    let want_shl = if sh >= width { 0 } else { a.wrapping_shl(sh) & low_mask_u128(width) };
                    let want_lshr = if sh >= width { 0 } else { (a & low_mask_u128(width)) >> sh };
                    assert_eq!(wa.shl(sh).to_u128(), want_shl, "shl {width} by {sh}");
                    assert_eq!(wa.lshr(sh).to_u128(), want_lshr, "lshr {width} by {sh}");
                }
            }
        }
    }

    // SMT-LIB-total reference helpers over the masked low `width` bits of a u128.
    // `wrapping_sub` keeps `w = 127` correct (where `1i128 << w` is the sign bit).
    fn to_signed(v: u128, w: u32) -> i128 {
        if w < 128 && (v >> (w - 1)) & 1 == 1 {
            (v as i128).wrapping_sub(1i128 << w)
        } else {
            v as i128
        }
    }

    #[test]
    #[allow(clippy::cast_sign_loss, clippy::cast_possible_wrap)]
    fn extended_ops_match_u128_reference() {
        let mut rng = Lcg(0x0f1e_2d3c_4b5a_6978);
        for width in [1u32, 2, 8, 13, 32, 63, 64, 65, 100, 127, 128] {
            let m = |v: u128| v & low_mask_u128(width);
            for _ in 0..300 {
                let a = m(rng.next());
                let b = m(rng.next());
                let wa = WideUint::from_u128(a, width);
                let wb = WideUint::from_u128(b, width);

                // Unsigned div/rem with SMT-LIB totality.
                let (eq, er) = match (a.checked_div(b), a.checked_rem(b)) {
                    (Some(q), Some(r)) => (q, r),
                    _ => (low_mask_u128(width), a),
                };
                assert_eq!(wa.udiv(&wb).to_u128(), eq, "udiv {a}/{b} w{width}");
                assert_eq!(wa.urem(&wb).to_u128(), er, "urem {a}%{b} w{width}");

                // Signed div/rem/mod.
                let sa = to_signed(a, width);
                let sb = to_signed(b, width);
                let sdiv_ref = if sb == 0 {
                    if sa < 0 { 1 } else { -1i128 }
                } else {
                    sa.wrapping_div(sb)
                };
                let srem_ref = if sb == 0 { sa } else { sa.wrapping_rem(sb) };
                assert_eq!(wa.sdiv(&wb).to_u128(), m(sdiv_ref as u128), "sdiv w{width}");
                assert_eq!(wa.srem(&wb).to_u128(), m(srem_ref as u128), "srem w{width}");
                let smod_ref = if sb == 0 {
                    sa
                } else {
                    let r = sa.rem_euclid(sb.abs());
                    if sb < 0 && r != 0 { r - sb.abs() } else { r }
                };
                assert_eq!(wa.smod(&wb).to_u128(), m(smod_ref as u128), "smod {sa} {sb} w{width}");

                // Signed compares.
                assert_eq!(wa.slt(&wb), sa < sb, "slt w{width}");
                assert_eq!(wa.sle(&wb), sa <= sb, "sle w{width}");
                assert_eq!(wa.uge(&wb), a >= b, "uge w{width}");
                assert_eq!(wa.count_leading_zeros(), a.leading_zeros() - (128 - width), "clz {a} w{width}");

                // Arithmetic shift.
                for sh in [0u32, 1, 7, width / 2, width.saturating_sub(1), width] {
                    let want = if sh >= width {
                        if sa < 0 { low_mask_u128(width) } else { 0 }
                    } else {
                        m((sa >> sh) as u128)
                    };
                    assert_eq!(wa.ashr(sh).to_u128(), want, "ashr {sa} by {sh} w{width}");
                }
            }
        }
    }

    #[test]
    fn structural_ops_match_u128_reference() {
        let mut rng = Lcg(0xa1b2_c3d4_e5f6_0718);
        for width in [4u32, 8, 16, 32, 60, 64, 96] {
            for _ in 0..200 {
                let a = rng.next() & low_mask_u128(width);
                let wa = WideUint::from_u128(a, width);
                // extract
                let lo = rng.next() as u32 % width;
                let hi = lo + rng.next() as u32 % (width - lo);
                let ew = hi - lo + 1;
                let want = (a >> lo) & low_mask_u128(ew);
                assert_eq!(wa.extract(hi, lo).to_u128(), want, "extract[{hi}:{lo}] w{width}");
                // zero/sign extend (keep total within 128 for the reference)
                if width <= 64 {
                    let by = rng.next() as u32 % (128 - width);
                    assert_eq!(wa.zero_ext(by).to_u128(), a, "zext w{width} by{by}");
                    let sref = (to_signed(a, width) as u128) & low_mask_u128(width + by);
                    assert_eq!(wa.sign_ext(by).to_u128(), sref, "sext w{width} by{by}");
                    // concat with a second value
                    let bw = 1 + rng.next() as u32 % (128 - width).max(1);
                    if width + bw <= 128 {
                        let b = rng.next() & low_mask_u128(bw);
                        let wb = WideUint::from_u128(b, bw);
                        assert_eq!(wa.concat(&wb).to_u128(), (a << bw) | b, "concat w{width}++{bw}");
                    }
                }
            }
        }
    }

    #[test]
    fn lsb_bits_round_trip_and_match_u128() {
        let mut rng = Lcg(0x5151_2626_3737_4848);
        for width in [1u32, 8, 64, 65, 100, 128, 129, 200, 256] {
            for _ in 0..50 {
                let lo = rng.next();
                let hi = rng.next();
                // Build a wide value from two limbs' worth of random bits.
                let mut bits: Vec<bool> = (0..width)
                    .map(|i| {
                        let src = if i < 128 { lo } else { hi };
                        (src >> (i % 128)) & 1 == 1
                    })
                    .collect();
                let w = WideUint::from_lsb_bits(&bits);
                assert_eq!(w.width(), width);
                assert_eq!(w.to_lsb_bits(), bits, "round-trip width {width}");
                // Bit accessor agrees with the LSB-first vector.
                for i in 0..width {
                    assert_eq!(w.bit(i), bits[i as usize], "bit {i} width {width}");
                }
                // For width <= 128, the value matches the u128 assembled from bits.
                if width <= 128 {
                    let mut want = 0u128;
                    for (i, &b) in bits.iter().enumerate() {
                        if b {
                            want |= 1u128 << i;
                        }
                    }
                    assert_eq!(w.to_u128(), want, "to_u128 from bits width {width}");
                }
                bits.clear();
            }
        }
    }

    #[test]
    fn wide_beyond_u128_algebraic_identities() {
        // No u128 reference exists above 128 bits, so check algebraic laws.
        let mut rng = Lcg(0xdead_beef_cafe_babe);
        for width in [129u32, 164, 200, 256] {
            let one = WideUint::from_u128(1, width);
            let zero = WideUint::zero(width);
            for _ in 0..50 {
                let a = WideUint::from_u128(rng.next(), width).shl(rng.next() as u32 % width);
                let b = WideUint::from_u128(rng.next(), width);
                assert_eq!(a.add(&zero), a, "a+0");
                assert_eq!(a.mul(&one), a, "a*1");
                assert_eq!(a.add(&b), b.add(&a), "add comm");
                assert_eq!(a.mul(&b), b.mul(&a), "mul comm");
                assert_eq!(a.sub(&a), zero, "a-a");
                assert_eq!(a.add(&a.neg()), zero, "a+(-a)");
                assert_eq!(a.xor(&a), zero, "a^a");
                assert_eq!(a.not().not(), a, "double not");
                // x << k >> k clears the top k bits: equals x & (2^(width-k)-1).
                let k = 1 + rng.next() as u32 % (width - 1);
                assert_eq!(a.shl(k).lshr(k), a.lshr(0).and(&one.shl(width - k).sub(&one)), "shl/lshr {width} {k}");
            }
        }
    }
}
