//! Denotation-preserving lowering of **derived** bit-vector operators to the
//! `QF_BV` bitblast **core** — the 17 operators the Alethe emitter, Carcara, and Lean
//! reconstruction all support
//! (see `docs/research/05-algorithms/qfbv-proof-operator-coverage.md`).
//!
//! Reducing `bvsub`/`bvnand`/`bvnor`, the six non-core comparisons, the structural
//! `zero_extend`/`rotate_left`/`rotate_right`, the shifts (`bvshl`/`bvlshr`/`bvashr`,
//! constant *and* variable amount), and the full division family
//! (`bvudiv`/`bvurem`, `bvsdiv`/`bvsrem`/`bvsmod`) to core lets the proof track cover
//! them: lower first, then emit a proof over core ops only. This is the **entire**
//! `QF_BV` operator set beyond the 17-op bitblast core. Every rule is a standard
//! SMT-LIB identity, checked denotation-preserving by the ground evaluator below.
//!
//! Coverage caveat: the *lowering* of every operator here is denotation-preserving
//! and exhaustively tested. Most reconstruct end-to-end, but the unrolled long
//! `divide` produces a large term whose proof reconstruction is intractable beyond
//! tiny widths (the multiplier-style term blowup) and currently also trips
//! `cnf_intro` over Boolean-constant operands — see
//! `docs/research/05-algorithms/qfbv-proof-operator-coverage.md`.

use axeyum_ir::{IrError, Op, TermArena, TermId, TermNode};

/// Recursively rewrite every derived bit-vector operator in `term` to the bitblast
/// core, bottom-up. Sort- and denotation-preserving. Non-derived nodes are rebuilt
/// with lowered children; interning collapses unchanged subtrees back to the input,
/// so a formula already in the core fragment returns its own `term`.
///
/// Lowered operators (all standard SMT-LIB identities):
/// - `bvsub a b → bvadd a (bvneg b)`
/// - `bvnand a b → bvnot (bvand a b)`, `bvnor a b → bvnot (bvor a b)`
/// - `bvugt a b → bvult b a`, `bvule a b → ¬(bvult b a)`, `bvuge a b → ¬(bvult a b)`
/// - `bvsgt a b → bvslt b a`, `bvsle a b → ¬(bvslt b a)`, `bvsge a b → ¬(bvslt a b)`
/// - `zero_extend k x → concat (0:k) x`
/// - `rotate_left`/`rotate_right` → `concat` of two `extract`s
/// - `bvshl`/`bvlshr`/`bvashr`: constant amount → `concat`/`extract`/`sign_extend`;
///   variable amount → a barrel-shifter (mux) network
/// - `bvudiv`/`bvurem` → one unrolled long-division pass (shift-subtract)
/// - `bvsdiv`/`bvsrem`/`bvsmod` → unsigned division of the magnitudes + sign logic
///
/// # Errors
///
/// Propagates any [`IrError`] from the rebuilt sub-terms (e.g. a sort mismatch),
/// which cannot occur for a well-formed input term.
///
/// # Panics
///
/// Panics on a malformed shift whose shifted operand lacks a bit-vector sort (it
/// cannot occur for a well-formed `bvshl`/`bvlshr`/`bvashr` term).
pub fn lower_derived_bv(arena: &mut TermArena, term: TermId) -> Result<TermId, IrError> {
    // Copy `op` and children out without cloning the node, then lower bottom-up.
    let (op, args): (Op, Vec<TermId>) = match arena.node(term) {
        TermNode::App { op, args } => (*op, args.to_vec()),
        _ => return Ok(term),
    };
    let mut largs = Vec::with_capacity(args.len());
    for a in args {
        largs.push(lower_derived_bv(arena, a)?);
    }

    Ok(match op {
        Op::BvSub => {
            let nb = arena.bv_neg(largs[1])?;
            arena.bv_add(largs[0], nb)?
        }
        Op::BvNand => {
            let g = arena.bv_and(largs[0], largs[1])?;
            arena.bv_not(g)?
        }
        Op::BvNor => {
            let g = arena.bv_or(largs[0], largs[1])?;
            arena.bv_not(g)?
        }
        // a >ᵤ b ⟺ b <ᵤ a
        Op::BvUgt => arena.bv_ult(largs[1], largs[0])?,
        // a ≤ᵤ b ⟺ ¬(b <ᵤ a)
        Op::BvUle => {
            let lt = arena.bv_ult(largs[1], largs[0])?;
            arena.not(lt)?
        }
        // a ≥ᵤ b ⟺ ¬(a <ᵤ b)
        Op::BvUge => {
            let lt = arena.bv_ult(largs[0], largs[1])?;
            arena.not(lt)?
        }
        // a >ₛ b ⟺ b <ₛ a
        Op::BvSgt => arena.bv_slt(largs[1], largs[0])?,
        // a ≤ₛ b ⟺ ¬(b <ₛ a)
        Op::BvSle => {
            let lt = arena.bv_slt(largs[1], largs[0])?;
            arena.not(lt)?
        }
        // a ≥ₛ b ⟺ ¬(a <ₛ b)
        Op::BvSge => {
            let lt = arena.bv_slt(largs[0], largs[1])?;
            arena.not(lt)?
        }
        // zero_extend by k ≡ concat (0:k) x  (k zero bits in the high end).
        Op::ZeroExt { by } => {
            if by == 0 {
                largs[0]
            } else {
                let z = arena.bv_const(by, 0)?;
                arena.concat(z, largs[0])?
            }
        }
        // rotate_left by k on width w ≡ concat x[w-k-1:0] x[w-1:w-k]  (low w-k bits to
        // the high end, high k bits to the low end). k is taken mod w.
        Op::RotateLeft { by } => rotate_via_concat(arena, largs[0], by, true)?,
        // rotate_right by k ≡ concat x[k-1:0] x[w-1:k].
        Op::RotateRight { by } => rotate_via_concat(arena, largs[0], by, false)?,
        // Shifts reduce to core: a CONSTANT amount via concat/extract/sign_extend, a
        // VARIABLE amount via a barrel-shifter (mux) network.
        Op::BvShl | Op::BvLshr | Op::BvAshr => {
            let shift = match arena.node(largs[1]) {
                TermNode::BvConst { value, .. } => Some(*value),
                _ => None,
            };
            let w = arena
                .sort_of(largs[0])
                .bv_width()
                .expect("shift operand has BV sort");
            match shift {
                Some(s) => lower_const_shift(arena, op, largs[0], s, w)?,
                None => lower_var_shift(arena, op, largs[0], largs[1], w)?,
            }
        }
        // Unsigned division/remainder: one unrolled long-division pass yields both;
        // SMT-LIB's `y = 0` totality (udiv = all-ones, urem = x) falls out for free.
        Op::BvUdiv | Op::BvUrem => {
            let w = arena
                .sort_of(largs[0])
                .bv_width()
                .expect("div operand has BV sort");
            let (quotient, remainder) = divide(arena, largs[0], largs[1], w)?;
            if matches!(op, Op::BvUdiv) {
                quotient
            } else {
                remainder
            }
        }
        // Signed division/remainder/modulo: unsigned `divide` of the magnitudes plus
        // sign adjustments (SMT-LIB definitions).
        Op::BvSdiv | Op::BvSrem | Op::BvSmod => {
            let w = arena
                .sort_of(largs[0])
                .bv_width()
                .expect("signed div operand has BV sort");
            lower_signed_divrem(arena, op, largs[0], largs[1], w)?
        }
        // Not a lowered operator: rebuild with lowered children (sort preserved).
        _ => arena.rebuild_with_args(term, &largs),
    })
}

/// `rotate_left`/`rotate_right` of `x` by `by` (taken mod the operand width),
/// expressed as a `concat` of two `extract`s — both core operators. `left` selects
/// the rotate direction. A zero effective amount is the identity.
fn rotate_via_concat(
    arena: &mut TermArena,
    x: TermId,
    by: u32,
    left: bool,
) -> Result<TermId, IrError> {
    let w = arena
        .sort_of(x)
        .bv_width()
        .expect("rotate operand has BV sort");
    let k = if w == 0 { 0 } else { by % w };
    if k == 0 {
        return Ok(x);
    }
    // left:  high = x[w-k-1:0]  (low w-k bits),  low = x[w-1:w-k] (high k bits)
    // right: high = x[k-1:0]    (low k bits),    low = x[w-1:k]   (high w-k bits)
    let (hi, lo) = if left {
        (
            arena.extract(w - k - 1, 0, x)?,
            arena.extract(w - 1, w - k, x)?,
        )
    } else {
        (arena.extract(k - 1, 0, x)?, arena.extract(w - 1, k, x)?)
    };
    arena.concat(hi, lo)
}

/// A by-`shift` (unsigned) `bvshl`/`bvlshr`/`bvashr` of width-`w` `x`, expressed in
/// core operators. SMT-LIB semantics: `shift ≥ w` ⇒ `bvshl`/`bvlshr` are `0` and
/// `bvashr` is all sign bits; `shift = 0` is the identity.
///
/// # Panics
///
/// Panics if `op` is not `bvshl`/`bvlshr`/`bvashr` — the caller dispatches only
/// those. The internal `u32` conversions of the (already `< w`) amount cannot fail.
fn lower_const_shift(
    arena: &mut TermArena,
    op: Op,
    x: TermId,
    shift: u128,
    w: u32,
) -> Result<TermId, IrError> {
    let wv = u128::from(w);
    // In every `shift < wv` branch the amount is `< w`, so it fits `u32` exactly.
    let amt = || u32::try_from(shift).expect("shift < w fits u32");
    match op {
        // x << k: drop the high k bits, append k zeros at the low end.
        Op::BvShl => {
            if shift == 0 {
                Ok(x)
            } else if shift >= wv {
                arena.bv_const(w, 0)
            } else {
                let k = amt();
                let lo = arena.extract(w - 1 - k, 0, x)?; // low w-k bits → high
                let z = arena.bv_const(k, 0)?; // k zeros → low
                arena.concat(lo, z)
            }
        }
        // x >>ᵤ k: prepend k zeros at the high end, drop the low k bits.
        Op::BvLshr => {
            if shift == 0 {
                Ok(x)
            } else if shift >= wv {
                arena.bv_const(w, 0)
            } else {
                let k = amt();
                let z = arena.bv_const(k, 0)?; // k zeros → high
                let hi = arena.extract(w - 1, k, x)?; // high w-k bits → low
                arena.concat(z, hi)
            }
        }
        // x >>ₛ k: like lshr but fill the high bits with the sign — `sign_extend` of
        // the surviving high slice (whose MSB is x's sign bit).
        Op::BvAshr => {
            if shift == 0 {
                Ok(x)
            } else if shift >= wv {
                let sign = arena.extract(w - 1, w - 1, x)?; // 1-bit sign
                arena.sign_ext(w - 1, sign) // all w bits = sign
            } else {
                let k = amt();
                let part = arena.extract(w - 1, k, x)?; // w-k bits, MSB = sign
                arena.sign_ext(k, part) // extend by k → w bits
            }
        }
        _ => unreachable!("lower_const_shift only handles bvshl/bvlshr/bvashr"),
    }
}

/// Zero-extend `a` by `by` bits using **core** ops only (`concat` of a zero const) —
/// unlike `TermArena::zero_ext`, which builds a derived `ZeroExt` node that would
/// reach the emitter unlowered.
fn zext_core(arena: &mut TermArena, by: u32, a: TermId) -> Result<TermId, IrError> {
    if by == 0 {
        return Ok(a);
    }
    let z = arena.bv_const(by, 0)?;
    arena.concat(z, a)
}

/// The sign bit of width-`w` `t`, splatted to a width-`w` all-ones/all-zeros mask via
/// `sign_extend` of the 1-bit MSB slice.
fn splat_sign(arena: &mut TermArena, t: TermId, w: u32) -> Result<TermId, IrError> {
    let sign = arena.extract(w - 1, w - 1, t)?;
    arena.sign_ext(w - 1, sign)
}

/// Two's-complement absolute value `|t| = sign(t) ? -t : t` in core ops.
fn bv_abs(arena: &mut TermArena, t: TermId, w: u32) -> Result<TermId, IrError> {
    let mask = splat_sign(arena, t, w)?;
    let nt = arena.bv_neg(t)?;
    select(arena, mask, nt, t)
}

/// Bitwise mux `mask ? a : b` over width-`w` operands where `mask` is all-ones or
/// all-zeros: `(mask ∧ a) ∨ (¬mask ∧ b)`. Core ops only.
fn select(arena: &mut TermArena, mask: TermId, a: TermId, b: TermId) -> Result<TermId, IrError> {
    let nm = arena.bv_not(mask)?;
    let ta = arena.bv_and(mask, a)?;
    let tb = arena.bv_and(nm, b)?;
    arena.bv_or(ta, tb)
}

/// A by-`s` (a width-`w` term, not a constant) `bvshl`/`bvlshr`/`bvashr` of `x`,
/// expressed in core operators as a **barrel shifter**: stage `i` (for `2^i < w`)
/// conditionally applies the constant shift by `2^i`, selected by bit `i` of `s`
/// (splatted to width `w` via `sign_extend` of the 1-bit slice). Shift amounts
/// `s ≥ w` — detected as any high bit of `s` at/above `⌈log₂ w⌉` being set — force the
/// SMT-LIB result (`0` for `bvshl`/`bvlshr`, all-sign for `bvashr`).
fn lower_var_shift(
    arena: &mut TermArena,
    op: Op,
    x: TermId,
    s: TermId,
    w: u32,
) -> Result<TermId, IrError> {
    let mut cur = x;
    let mut stage = 0u32;
    while (1u32 << stage) < w {
        let cond = arena.extract(stage, stage, s)?; // bit s[stage]
        let mask = arena.sign_ext(w - 1, cond)?; // splat to width w
        let shifted = lower_const_shift(arena, op, cur, 1u128 << stage, w)?;
        cur = select(arena, mask, shifted, cur)?;
        stage += 1;
    }
    // Overflow: s ≥ w iff any bit s[w-1 : stage] is set (stage = ⌈log₂ w⌉ ≤ w-1).
    let s_high = arena.extract(w - 1, stage, s)?;
    let zero_high = arena.bv_const(w - stage, 0)?;
    let is_zero = arena.bv_comp(s_high, zero_high)?; // 1-bit: 1 iff s_high == 0
    let overflow_bit = arena.bv_not(is_zero)?; // 1-bit: s_high != 0
    let ov_mask = arena.sign_ext(w - 1, overflow_bit)?; // splat
    let fallback = if matches!(op, Op::BvAshr) {
        let sign = arena.extract(w - 1, w - 1, x)?;
        arena.sign_ext(w - 1, sign)? // all sign bits
    } else {
        arena.bv_const(w, 0)?
    };
    select(arena, ov_mask, fallback, cur)
}

/// Unsigned long division of width-`w` `x` by `y`, returning `(quotient, remainder)`
/// as core-operator terms. The classic restoring shift-subtract loop, fully unrolled
/// over `w` steps and computed in `w+1`/`w+2`-bit intermediates so the shift-in and
/// the `≥` borrow never lose information. SMT-LIB totality is automatic: for `y = 0`
/// every step subtracts (the `≥ 0` test is always true) ⇒ `quotient` is all-ones and
/// `remainder` is `x`.
#[allow(clippy::many_single_char_names)] // x/y operands, w width, t/i step/bit indices
fn divide(
    arena: &mut TermArena,
    x: TermId,
    y: TermId,
    w: u32,
) -> Result<(TermId, TermId), IrError> {
    let mut rem = arena.bv_const(w, 0)?; // width w
    let mut quo_bits: Vec<TermId> = Vec::with_capacity(w as usize); // MSB-first
    for t in 0..w {
        let i = w - 1 - t; // process x bit `i` (MSB first)
        // shifted = (rem << 1) | x[i] = concat(rem, x[i])  [w+1 bits, no loss].
        let xi = arena.extract(i, i, x)?;
        let shifted = arena.concat(rem, xi)?; // w+1 bits
        let y_ext = zext_core(arena, 1, y)?; // w+1 bits
        // cond (1-bit) = shifted ≥ y_ext, via the borrow of a w+2-bit subtraction.
        let sa = zext_core(arena, 1, shifted)?; // w+2
        let sb = zext_core(arena, 1, y_ext)?; // w+2
        let neg_sb = arena.bv_neg(sb)?;
        let d = arena.bv_add(sa, neg_sb)?; // w+2; top bit = borrow
        let borrow = arena.extract(w + 1, w + 1, d)?; // 1 bit
        let cond = arena.bv_not(borrow)?; // 1 bit: shifted ≥ y_ext
        // subtracted = shifted - y_ext (w+1 bits); keep it iff cond.
        let neg_y = arena.bv_neg(y_ext)?;
        let subtracted = arena.bv_add(shifted, neg_y)?;
        let cond_mask = arena.sign_ext(w, cond)?; // splat cond to w+1 bits
        let rem_ext_new = select(arena, cond_mask, subtracted, shifted)?;
        rem = arena.extract(w - 1, 0, rem_ext_new)?; // back to w bits
        quo_bits.push(cond);
    }
    // quotient: quo_bits[t] is bit `w-1-t`, so concat MSB-first reproduces it.
    let mut q = quo_bits[w as usize - 1];
    for t in (0..w as usize - 1).rev() {
        q = arena.concat(quo_bits[t], q)?;
    }
    Ok((q, rem))
}

/// The **signed** division family, reduced to the unsigned [`divide`] of the operand
/// magnitudes plus sign adjustments — all SMT-LIB definitions, in core ops.
/// `bvsdiv`: `|x|/|y|` negated iff the signs differ. `bvsrem`: `|x| rem |y|`, sign of
/// the dividend. `bvsmod`: modulo with the sign of the divisor (the 5-way SMT-LIB
/// rule, including the `u = 0` and sign-quadrant cases).
#[allow(clippy::many_single_char_names)] // x/y operands, w width, q/u div results
fn lower_signed_divrem(
    arena: &mut TermArena,
    op: Op,
    x: TermId,
    y: TermId,
    w: u32,
) -> Result<TermId, IrError> {
    let abs_x = bv_abs(arena, x, w)?;
    let abs_y = bv_abs(arena, y, w)?;
    let (q, u) = divide(arena, abs_x, abs_y, w)?;
    let sx = splat_sign(arena, x, w)?;
    let sy = splat_sign(arena, y, w)?;
    match op {
        // |x|/|y|, negated iff sign(x) ≠ sign(y).
        Op::BvSdiv => {
            let x_msb = arena.extract(w - 1, w - 1, x)?;
            let y_msb = arena.extract(w - 1, w - 1, y)?;
            let diff = arena.bv_xor(x_msb, y_msb)?;
            let mask = arena.sign_ext(w - 1, diff)?;
            let neg_q = arena.bv_neg(q)?;
            select(arena, mask, neg_q, q)
        }
        // |x| rem |y|, taking the sign of the dividend x.
        Op::BvSrem => {
            let neg_u = arena.bv_neg(u)?;
            select(arena, sx, neg_u, u)
        }
        // bvsmod: sign of the divisor; the SMT-LIB 5-way rule.
        Op::BvSmod => {
            let zero = arena.bv_const(w, 0)?;
            let u_zero = arena.bv_comp(u, zero)?; // 1-bit: u == 0
            let neg_u = arena.bv_neg(u)?;
            let neg_u_plus_y = arena.bv_add(neg_u, y)?;
            let u_plus_y = arena.bv_add(u, y)?;
            // inner = sign(x) ? (sign(y) ? -u : -u+y) : (sign(y) ? u+y : u)
            let inner_sx1 = select(arena, sy, neg_u, neg_u_plus_y)?;
            let inner_sx0 = select(arena, sy, u_plus_y, u)?;
            let inner = select(arena, sx, inner_sx1, inner_sx0)?;
            let uz_mask = arena.sign_ext(w - 1, u_zero)?;
            select(arena, uz_mask, u, inner) // u == 0 ⇒ result 0
        }
        _ => unreachable!("lower_signed_divrem only handles bvsdiv/bvsrem/bvsmod"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::{Assignment, Sort, Value};

    /// Exhaustively confirm a lowered binary BV op agrees with the original on every
    /// pair of `width`-bit inputs (the soundness obligation: lowering is
    /// denotation-preserving).
    fn assert_lowering_preserves(
        width: u32,
        build: impl Fn(&mut TermArena, TermId, TermId) -> TermId,
    ) {
        let mut arena = TermArena::new();
        let sa = arena.declare("a", Sort::BitVec(width)).unwrap();
        let sb = arena.declare("b", Sort::BitVec(width)).unwrap();
        let a = arena.var(sa);
        let b = arena.var(sb);
        let orig = build(&mut arena, a, b);
        let low = lower_derived_bv(&mut arena, orig).unwrap();
        let n = 1u128 << width;
        for av in 0..n {
            for bv in 0..n {
                let mut asn = Assignment::new();
                asn.set(sa, Value::Bv { width, value: av });
                asn.set(sb, Value::Bv { width, value: bv });
                let eo = axeyum_ir::eval(&arena, orig, &asn).unwrap();
                let el = axeyum_ir::eval(&arena, low, &asn).unwrap();
                assert_eq!(eo, el, "lowering changed denotation at a={av}, b={bv}");
            }
        }
    }

    #[test]
    fn sub_nand_nor_preserve_denotation() {
        assert_lowering_preserves(3, |a, x, y| a.bv_sub(x, y).unwrap());
        assert_lowering_preserves(3, |a, x, y| a.bv_nand(x, y).unwrap());
        assert_lowering_preserves(3, |a, x, y| a.bv_nor(x, y).unwrap());
    }

    #[test]
    fn comparisons_preserve_denotation() {
        assert_lowering_preserves(3, |a, x, y| a.bv_ule(x, y).unwrap());
        assert_lowering_preserves(3, |a, x, y| a.bv_uge(x, y).unwrap());
        assert_lowering_preserves(3, |a, x, y| a.bv_ugt(x, y).unwrap());
        assert_lowering_preserves(3, |a, x, y| a.bv_sle(x, y).unwrap());
        assert_lowering_preserves(3, |a, x, y| a.bv_sge(x, y).unwrap());
        assert_lowering_preserves(3, |a, x, y| a.bv_sgt(x, y).unwrap());
    }

    /// Exhaustively confirm a lowered unary BV op agrees with the original on every
    /// `width`-bit input.
    fn assert_unary_lowering_preserves(
        width: u32,
        build: impl Fn(&mut TermArena, TermId) -> TermId,
    ) {
        let mut arena = TermArena::new();
        let sa = arena.declare("a", Sort::BitVec(width)).unwrap();
        let a = arena.var(sa);
        let orig = build(&mut arena, a);
        let low = lower_derived_bv(&mut arena, orig).unwrap();
        for av in 0..(1u128 << width) {
            let mut asn = Assignment::new();
            asn.set(sa, Value::Bv { width, value: av });
            let eo = axeyum_ir::eval(&arena, orig, &asn).unwrap();
            let el = axeyum_ir::eval(&arena, low, &asn).unwrap();
            assert_eq!(eo, el, "unary lowering changed denotation at a={av}");
        }
    }

    #[test]
    fn structural_ops_preserve_denotation() {
        assert_unary_lowering_preserves(3, |a, x| a.zero_ext(2, x).unwrap());
        assert_unary_lowering_preserves(4, |a, x| a.rotate_left(1, x).unwrap());
        assert_unary_lowering_preserves(4, |a, x| a.rotate_left(3, x).unwrap());
        assert_unary_lowering_preserves(4, |a, x| a.rotate_right(1, x).unwrap());
        assert_unary_lowering_preserves(4, |a, x| a.rotate_right(3, x).unwrap());
        // by ≡ 0 mod w and by > w (wrap) are identities / well-defined.
        assert_unary_lowering_preserves(4, |a, x| a.rotate_left(4, x).unwrap());
        assert_unary_lowering_preserves(4, |a, x| a.rotate_left(5, x).unwrap());
    }

    #[test]
    fn const_shifts_preserve_denotation() {
        // Amounts spanning 0, mid, exactly w, and > w (all defined by SMT-LIB).
        for amt in [0u128, 1, 2, 3, 4, 7] {
            assert_unary_lowering_preserves(4, move |a, x| {
                let k = a.bv_const(4, amt).unwrap();
                a.bv_shl(x, k).unwrap()
            });
            assert_unary_lowering_preserves(4, move |a, x| {
                let k = a.bv_const(4, amt).unwrap();
                a.bv_lshr(x, k).unwrap()
            });
            assert_unary_lowering_preserves(4, move |a, x| {
                let k = a.bv_const(4, amt).unwrap();
                a.bv_ashr(x, k).unwrap()
            });
        }
    }

    /// Exhaustively confirm a lowered two-operand op (variable shift, div/rem) agrees
    /// with the original on every `(x, y)` pair of `width`-bit inputs — the
    /// barrel-shifter / long-division soundness obligation, including every overflow
    /// and `y = 0` corner.
    fn assert_lowered_binary_preserves(
        width: u32,
        build: impl Fn(&mut TermArena, TermId, TermId) -> TermId,
    ) {
        let mut arena = TermArena::new();
        let sx = arena.declare("x", Sort::BitVec(width)).unwrap();
        let ss = arena.declare("s", Sort::BitVec(width)).unwrap();
        let x = arena.var(sx);
        let s = arena.var(ss);
        let orig = build(&mut arena, x, s);
        let low = lower_derived_bv(&mut arena, orig).unwrap();
        // The lowering must actually have rewritten the operator.
        assert_ne!(low, orig, "two-operand op was not lowered");
        let n = 1u128 << width;
        for xv in 0..n {
            for sv in 0..n {
                let mut asn = Assignment::new();
                asn.set(sx, Value::Bv { width, value: xv });
                asn.set(ss, Value::Bv { width, value: sv });
                let eo = axeyum_ir::eval(&arena, orig, &asn).unwrap();
                let el = axeyum_ir::eval(&arena, low, &asn).unwrap();
                assert_eq!(eo, el, "barrel shift differs at x={xv}, s={sv}");
            }
        }
    }

    #[test]
    fn variable_shifts_preserve_denotation() {
        // Non-power-of-two and power-of-two widths exercise the overflow corners.
        for w in [2u32, 3, 4] {
            assert_lowered_binary_preserves(w, |a, x, s| a.bv_shl(x, s).unwrap());
            assert_lowered_binary_preserves(w, |a, x, s| a.bv_lshr(x, s).unwrap());
            assert_lowered_binary_preserves(w, |a, x, s| a.bv_ashr(x, s).unwrap());
        }
    }

    #[test]
    fn div_rem_preserve_denotation() {
        // Exhaustive over all (x, y) incl. y = 0 (SMT-LIB: udiv→all-ones, urem→x).
        for w in [2u32, 3, 4] {
            assert_lowered_binary_preserves(w, |a, x, y| a.bv_udiv(x, y).unwrap());
            assert_lowered_binary_preserves(w, |a, x, y| a.bv_urem(x, y).unwrap());
        }
    }

    #[test]
    fn signed_div_rem_mod_preserve_denotation() {
        // Exhaustive over all (x, y) incl. y = 0 and the sign quadrants / INT_MIN.
        for w in [2u32, 3, 4] {
            assert_lowered_binary_preserves(w, |a, x, y| a.bv_sdiv(x, y).unwrap());
            assert_lowered_binary_preserves(w, |a, x, y| a.bv_srem(x, y).unwrap());
            assert_lowered_binary_preserves(w, |a, x, y| a.bv_smod(x, y).unwrap());
        }
    }

    #[test]
    fn core_fragment_is_unchanged() {
        // A formula already in the core returns its own interned term (no-op).
        let mut arena = TermArena::new();
        let s = arena.declare("a", Sort::BitVec(4)).unwrap();
        let a = arena.var(s);
        let t = arena.bv_add(a, a).unwrap();
        assert_eq!(lower_derived_bv(&mut arena, t).unwrap(), t);
    }
}
