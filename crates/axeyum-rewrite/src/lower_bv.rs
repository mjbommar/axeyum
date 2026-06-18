//! Denotation-preserving lowering of **derived** bit-vector operators to the
//! `QF_BV` bitblast **core** — the 17 operators the Alethe emitter, Carcara, and Lean
//! reconstruction all support
//! (see `docs/research/05-algorithms/qfbv-proof-operator-coverage.md`).
//!
//! Reducing `bvsub`/`bvnand`/`bvnor`, the six non-core comparisons, and the
//! structural `zero_extend`/`rotate_left`/`rotate_right` to core lets the proof track
//! cover them: lower first, then emit a proof over core ops only. Every rule is a
//! standard SMT-LIB identity, and each is checked denotation-preserving by the ground
//! evaluator in the tests below.

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

    /// Exhaustively confirm a lowered variable (two-operand) shift agrees with the
    /// original on every `(x, s)` pair of `width`-bit inputs — the barrel-shifter
    /// soundness obligation, including every `s ≥ width` overflow case.
    fn assert_var_shift_preserves(
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
        // The lowering must actually have rewritten the variable shift.
        assert_ne!(low, orig, "variable shift was not lowered");
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
            assert_var_shift_preserves(w, |a, x, s| a.bv_shl(x, s).unwrap());
            assert_var_shift_preserves(w, |a, x, s| a.bv_lshr(x, s).unwrap());
            assert_var_shift_preserves(w, |a, x, s| a.bv_ashr(x, s).unwrap());
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
