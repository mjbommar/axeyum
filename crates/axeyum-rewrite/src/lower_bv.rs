//! Denotation-preserving lowering of **derived** bit-vector operators to the
//! `QF_BV` bitblast **core** — the 17 operators the Alethe emitter, Carcara, and Lean
//! reconstruction all support
//! (see `docs/research/05-algorithms/qfbv-proof-operator-coverage.md`).
//!
//! Reducing `bvsub`/`bvnand`/`bvnor` and the four unsigned/signed "other"
//! comparisons to core lets the proof track cover them: lower first, then emit a
//! proof over core ops only. Every rule is a standard SMT-LIB identity, and each is
//! checked denotation-preserving by the ground evaluator in the tests below.

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
///
/// # Errors
///
/// Propagates any [`IrError`] from the rebuilt sub-terms (e.g. a sort mismatch),
/// which cannot occur for a well-formed input term.
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
        // Not a lowered operator: rebuild with lowered children (sort preserved).
        _ => arena.rebuild_with_args(term, &largs),
    })
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
