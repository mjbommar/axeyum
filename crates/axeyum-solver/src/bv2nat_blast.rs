//! Complete BV blast of the linear-over-`bv2nat` integer fragment (P2.7 A.2).
//!
//! The `str.len`-unsat gap (ADR-0029 / the gap-analysis "Gap 10" marker): the
//! bounded string front-end lowers `str.len` to `bv2nat(len_field)`, so a string
//! query's integer atoms are **linear constraints over `bv2nat` terms and
//! constants — with no free `Int` symbols**. On that fragment every integer value
//! is provably bounded (`bv2nat(b) ∈ [0, 2^W − 1]`), so the integer atoms can be
//! rewritten to **equivalent** pure bit-vector atoms at a width large enough that
//! no sum overflows. Unlike the bounded integer-blast (ADR-0014, sat-only) this
//! is an *equivalence*, so the SAT path downstream decides **both** directions —
//! `unsat` carries the usual DRAT evidence and `sat` a replayable model over the
//! unchanged symbols.
//!
//! Atom rewrite: normalize `L ⋈ R` to `Σ cᵢ·bv2nat(bᵢ) + k ⋈ 0`, split into a
//! non-negative side pair `A ⋈ B` (positive coefficients and `max(k, 0)` on the
//! left, negated negative ones and `max(−k, 0)` on the right), and evaluate both
//! sides exactly in `W`-bit unsigned bit-vector arithmetic where
//! `W = bits(max(bound(A), bound(B)))` and `bound(·)` is the side's maximal
//! attainable value (`Σ cᵢ·(2^{wᵢ} − 1) + k`, computed in checked `u128`). Each
//! `bv2nat(bᵢ)` becomes `zero_ext(W − wᵢ, bᵢ)`, whose unsigned value *is*
//! `bv2nat(bᵢ)`; with no overflow possible at width `W` the BV comparison
//! coincides with the integer comparison, so the rewrite preserves models
//! exactly (same symbols, no fresh declarations).
//!
//! Soundness:
//!
//! - The rewrite applies **only** when every integer-sorted subterm of the query
//!   lives inside a recognized linear atom (`=`, `<`, `≤`, `>`, `≥` over linear
//!   combinations of `bv2nat` terms and `Int` constants). A free `Int` symbol, an
//!   `Int` `div`/`mod`/`abs`, a non-constant product, a quantifier, or an `Int`
//!   subterm inside any other atom declines the whole pass (`Ok(None)`), leaving
//!   the caller's behaviour unchanged.
//! - Every constant computation is checked `u128`/`i128`; any overflow or a
//!   result width past [`MAX_BLAST_WIDTH`] declines. No wrong verdict is
//!   possible: the pass either produces an equivalent query or does nothing.
//! - The caller must still replay any `sat` model against the **original**
//!   assertions (the standard "every sat is checkable" gate); equivalence makes
//!   that replay succeed, and the guard converts any defect here to a loud
//!   `unknown`, never a wrong `sat`.

use std::collections::{BTreeMap, HashMap};

use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode};
use axeyum_rewrite::replace_subterms;

use crate::backend::SolverError;

/// Largest result width the blast will build. `bv_const` takes a `u128`, so the
/// per-side bound must fit 128 bits; wider (adversarial) combinations decline
/// gracefully to the caller's prior behaviour.
const MAX_BLAST_WIDTH: u32 = 128;

/// A linear form `Σ coeffs[b]·bv2nat(b) + constant` over bit-vector terms `b`.
/// `BTreeMap` keys the (deterministic, insertion-ordered) `TermId`s so the
/// rebuilt term order is stable across runs.
struct LinForm {
    coeffs: BTreeMap<TermId, i128>,
    constant: i128,
}

impl LinForm {
    fn constant(k: i128) -> Self {
        LinForm {
            coeffs: BTreeMap::new(),
            constant: k,
        }
    }

    /// `self + sign·other`, all coefficient arithmetic checked.
    fn add_scaled(mut self, other: &LinForm, sign: i128) -> Option<Self> {
        for (&b, &c) in &other.coeffs {
            let scaled = c.checked_mul(sign)?;
            let entry = self.coeffs.entry(b).or_insert(0);
            *entry = entry.checked_add(scaled)?;
        }
        self.constant = self
            .constant
            .checked_add(other.constant.checked_mul(sign)?)?;
        Some(self)
    }

    /// `self · k`, checked.
    fn scale(mut self, k: i128) -> Option<Self> {
        for c in self.coeffs.values_mut() {
            *c = c.checked_mul(k)?;
        }
        self.constant = self.constant.checked_mul(k)?;
        Some(self)
    }
}

/// The comparison of a recognized integer atom, normalized to `lhs ⋈ rhs`.
enum Rel {
    Eq,
    Lt,
    Le,
}

/// Rewrites the assertions of a **pure BV + Int** query whose every integer atom
/// is linear over `bv2nat` terms and constants into an *equivalent* pure
/// bit-vector query (same symbols, no fresh declarations). Returns `Ok(None)`
/// when the query is outside the fragment or contains no `bv2nat` (nothing to
/// gain) — the caller proceeds unchanged.
///
/// # Errors
///
/// Returns [`SolverError::Backend`] only for arena build failures (cannot occur
/// for well-sorted input).
pub fn blast_bv2nat_linear(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<Option<Vec<TermId>>, SolverError> {
    // Pass 1: classify the Boolean skeleton, collect the integer atoms, and
    // verify no Int-sorted term escapes a recognized atom.
    let mut atoms: Vec<TermId> = Vec::new();
    for &a in assertions {
        if !collect_int_atoms(arena, a, &mut atoms) {
            return Ok(None);
        }
    }
    if atoms.is_empty() {
        return Ok(None);
    }

    // Pass 2: extract each atom's linear form; decline (all-or-nothing) on any
    // out-of-fragment shape or checked-arithmetic overflow.
    let mut extracted: Vec<(TermId, Rel, LinForm)> = Vec::new();
    let mut saw_bv2nat = false;
    for &atom in &atoms {
        let TermNode::App { op, args } = arena.node(atom) else {
            return Ok(None);
        };
        let (lhs, rhs) = (args[0], args[1]);
        let (rel, l, r) = match op {
            Op::Eq => (Rel::Eq, lhs, rhs),
            Op::IntLt => (Rel::Lt, lhs, rhs),
            Op::IntLe => (Rel::Le, lhs, rhs),
            // Swap the operands so only three relations remain.
            Op::IntGt => (Rel::Lt, rhs, lhs),
            Op::IntGe => (Rel::Le, rhs, lhs),
            _ => return Ok(None),
        };
        let Some(lf) = linear_form(arena, l) else {
            return Ok(None);
        };
        let Some(rf) = linear_form(arena, r) else {
            return Ok(None);
        };
        // difference = l − r ⋈ 0
        let Some(diff) = lf.add_scaled(&rf, -1) else {
            return Ok(None);
        };
        saw_bv2nat |= !diff.coeffs.is_empty();
        extracted.push((atom, rel, diff));
    }
    if !saw_bv2nat {
        // Constant-only integer atoms: leave them to the exact LIA paths.
        return Ok(None);
    }

    // Pass 3: build the equivalent BV atom for each integer atom.
    let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
    let mut replacements: HashMap<TermId, TermId> = HashMap::new();
    for (atom, rel, diff) in extracted {
        // Split `Σ cᵢ·nᵢ + k ⋈ 0` into non-negative sides `A ⋈ B`.
        let mut pos: Vec<(TermId, u128)> = Vec::new();
        let mut neg: Vec<(TermId, u128)> = Vec::new();
        for (&b, &c) in &diff.coeffs {
            if c > 0 {
                pos.push((b, c.unsigned_abs()));
            } else if c < 0 {
                neg.push((b, c.unsigned_abs()));
            }
        }
        let (k_pos, k_neg) = if diff.constant >= 0 {
            (diff.constant.unsigned_abs(), 0u128)
        } else {
            (0u128, diff.constant.unsigned_abs())
        };
        let Some(bound_pos) = side_bound(arena, &pos, k_pos) else {
            return Ok(None);
        };
        let Some(bound_neg) = side_bound(arena, &neg, k_neg) else {
            return Ok(None);
        };
        let width = bits_needed(bound_pos.max(bound_neg)).max(1);
        if width > MAX_BLAST_WIDTH {
            return Ok(None);
        }
        let a_side = build_side(arena, &pos, k_pos, width).map_err(err)?;
        let b_side = build_side(arena, &neg, k_neg, width).map_err(err)?;
        let bv_atom = match rel {
            Rel::Eq => arena.eq(a_side, b_side).map_err(err)?,
            Rel::Lt => arena.bv_ult(a_side, b_side).map_err(err)?,
            Rel::Le => arena.bv_ule(a_side, b_side).map_err(err)?,
        };
        replacements.insert(atom, bv_atom);
    }

    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut out = Vec::with_capacity(assertions.len());
    for &a in assertions {
        out.push(replace_subterms(arena, a, &replacements, &mut memo).map_err(err)?);
    }
    Ok(Some(out))
}

/// Walks a Boolean-sorted term: recurses through the propositional skeleton,
/// records recognized integer atoms, and rejects (returns `false`) any shape
/// that could hide an integer-sorted subterm outside a recognized atom.
fn collect_int_atoms(arena: &TermArena, term: TermId, atoms: &mut Vec<TermId>) -> bool {
    match arena.node(term) {
        TermNode::BoolConst(_) => true,
        TermNode::Symbol(_) => arena.sort_of(term) == Sort::Bool,
        TermNode::App { op, args } => match op {
            Op::BoolNot | Op::BoolAnd | Op::BoolOr | Op::BoolXor | Op::BoolImplies => {
                let args = args.clone();
                args.iter().all(|&a| collect_int_atoms(arena, a, atoms))
            }
            // A Bool-sorted `ite`/`=` recurses only when its branches are
            // Boolean; Int-sorted branches fall to the atom cases below.
            Op::Ite if arena.sort_of(args[1]) == Sort::Bool => {
                let args = args.clone();
                args.iter().all(|&a| collect_int_atoms(arena, a, atoms))
            }
            Op::Eq if arena.sort_of(args[0]) == Sort::Bool => {
                let args = args.clone();
                args.iter().all(|&a| collect_int_atoms(arena, a, atoms))
            }
            Op::Eq if arena.sort_of(args[0]) == Sort::Int => {
                atoms.push(term);
                true
            }
            Op::IntLt | Op::IntLe | Op::IntGt | Op::IntGe => {
                atoms.push(term);
                true
            }
            // Quantifiers are outside this pass entirely.
            Op::Forall(_) | Op::Exists(_) => false,
            // Any other Boolean atom (BV comparison, …) is left untouched but
            // must not contain an integer-sorted subterm the rewrite would miss.
            _ => subtree_is_int_free(arena, term),
        },
        _ => false,
    }
}

/// `true` iff no subterm (including `term` itself) is `Int`-sorted.
fn subtree_is_int_free(arena: &TermArena, term: TermId) -> bool {
    let mut stack = vec![term];
    let mut seen = std::collections::BTreeSet::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if arena.sort_of(t) == Sort::Int {
            return false;
        }
        if let TermNode::App { args, .. } = arena.node(t) {
            stack.extend(args.iter().copied());
        }
    }
    true
}

/// Extracts `term` as a linear form over `bv2nat` arguments. `None` when the
/// term is outside the linear fragment (free `Int` symbol, `div`/`mod`/`abs`,
/// non-constant product, `Int`-sorted `ite`, an `Int` inside a `bv2nat`
/// argument, …) or a coefficient computation overflows.
fn linear_form(arena: &TermArena, term: TermId) -> Option<LinForm> {
    match arena.node(term) {
        TermNode::IntConst(k) => Some(LinForm::constant(*k)),
        TermNode::App { op, args } => match op {
            Op::Bv2Nat => {
                let b = args[0];
                // The BV argument must itself be free of integer subterms
                // (an `int2bv` inside would escape the rewrite).
                if !subtree_is_int_free(arena, b) {
                    return None;
                }
                let mut coeffs = BTreeMap::new();
                coeffs.insert(b, 1i128);
                Some(LinForm {
                    coeffs,
                    constant: 0,
                })
            }
            Op::IntNeg => linear_form(arena, args[0])?.scale(-1),
            Op::IntAdd => {
                let l = linear_form(arena, args[0])?;
                let r = linear_form(arena, args[1])?;
                l.add_scaled(&r, 1)
            }
            Op::IntSub => {
                let l = linear_form(arena, args[0])?;
                let r = linear_form(arena, args[1])?;
                l.add_scaled(&r, -1)
            }
            Op::IntMul => {
                // Only constant · linear stays linear.
                let (a, b) = (args[0], args[1]);
                if let TermNode::IntConst(k) = arena.node(a) {
                    let k = *k;
                    linear_form(arena, b)?.scale(k)
                } else if let TermNode::IntConst(k) = arena.node(b) {
                    let k = *k;
                    linear_form(arena, a)?.scale(k)
                } else {
                    None
                }
            }
            _ => None,
        },
        _ => None,
    }
}

/// The maximal attainable value of a non-negative side: `Σ cᵢ·(2^{wᵢ} − 1) + k`,
/// checked `u128`. `None` on overflow or a `bv2nat` argument at/over 128 bits.
fn side_bound(arena: &TermArena, terms: &[(TermId, u128)], k: u128) -> Option<u128> {
    let mut bound = k;
    for &(b, c) in terms {
        let Sort::BitVec(w) = arena.sort_of(b) else {
            return None;
        };
        if w >= 128 {
            return None;
        }
        let max_b = (1u128 << w) - 1;
        bound = bound.checked_add(c.checked_mul(max_b)?)?;
    }
    Some(bound)
}

/// Bits needed to represent `v` (0 → 0; callers clamp to ≥ 1).
fn bits_needed(v: u128) -> u32 {
    128 - v.leading_zeros()
}

/// Builds `Σ cᵢ·zero_ext(bᵢ) + k` at `width` bits. The caller has proven the
/// side's bound fits `width`, so no addition or constant multiplication wraps.
fn build_side(
    arena: &mut TermArena,
    terms: &[(TermId, u128)],
    k: u128,
    width: u32,
) -> Result<TermId, axeyum_ir::IrError> {
    let mut acc = arena.bv_const(width, k)?;
    for &(b, c) in terms {
        let Sort::BitVec(w) = arena.sort_of(b) else {
            unreachable!("side_bound already verified the sort");
        };
        let extended = if w == width {
            b
        } else {
            arena.zero_ext(width - w, b)?
        };
        let scaled = if c == 1 {
            extended
        } else {
            let c_const = arena.bv_const(width, c)?;
            arena.bv_mul(c_const, extended)?
        };
        acc = arena.bv_add(acc, scaled)?;
    }
    Ok(acc)
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::{Sort, TermArena};

    fn setup() -> (TermArena, TermId, TermId) {
        let mut arena = TermArena::new();
        let b = arena.declare("b", Sort::BitVec(4)).expect("declare b");
        let c = arena.declare("c", Sort::BitVec(4)).expect("declare c");
        let b = arena.var(b);
        let c = arena.var(c);
        (arena, b, c)
    }

    #[test]
    fn blasts_equality_against_in_range_constant() {
        let (mut arena, b, _) = setup();
        let n = arena.bv2nat(b).expect("bv2nat");
        let three = arena.int_const(3);
        let atom = arena.eq(n, three).expect("eq");
        let out = blast_bv2nat_linear(&mut arena, &[atom])
            .expect("blast")
            .expect("in fragment");
        assert_eq!(out.len(), 1);
        // The rewritten atom is pure BV (no Int-sorted subterm anywhere).
        assert!(subtree_is_int_free(&arena, out[0]));
    }

    #[test]
    fn declines_free_int_symbol() {
        let (mut arena, b, _) = setup();
        let n = arena.bv2nat(b).expect("bv2nat");
        let x = arena.declare("x", Sort::Int).expect("declare x");
        let x = arena.var(x);
        let atom = arena.eq(n, x).expect("eq");
        assert!(
            blast_bv2nat_linear(&mut arena, &[atom])
                .expect("blast")
                .is_none()
        );
    }

    #[test]
    fn declines_nonlinear_product() {
        let (mut arena, b, c) = setup();
        let nb = arena.bv2nat(b).expect("bv2nat");
        let nc = arena.bv2nat(c).expect("bv2nat");
        let prod = arena.int_mul(nb, nc).expect("mul");
        let k = arena.int_const(3);
        let atom = arena.eq(prod, k).expect("eq");
        assert!(
            blast_bv2nat_linear(&mut arena, &[atom])
                .expect("blast")
                .is_none()
        );
    }

    #[test]
    fn declines_int_div() {
        let (mut arena, b, _) = setup();
        let n = arena.bv2nat(b).expect("bv2nat");
        let two = arena.int_const(2);
        let d = arena.int_div(n, two).expect("div");
        let k = arena.int_const(1);
        let atom = arena.eq(d, k).expect("eq");
        assert!(
            blast_bv2nat_linear(&mut arena, &[atom])
                .expect("blast")
                .is_none()
        );
    }

    #[test]
    fn declines_constant_only_atoms() {
        let mut arena = TermArena::new();
        let one = arena.int_const(1);
        let two = arena.int_const(2);
        let atom = arena.int_lt(one, two).expect("lt");
        assert!(
            blast_bv2nat_linear(&mut arena, &[atom])
                .expect("blast")
                .is_none()
        );
    }

    #[test]
    fn linear_combination_with_negative_coefficients_round_trips() {
        // 2·bv2nat(b) − 3·bv2nat(c) ≤ −1  ⟺  2·nb + 1 ≤ 3·nc
        let (mut arena, b, c) = setup();
        let nb = arena.bv2nat(b).expect("bv2nat");
        let nc = arena.bv2nat(c).expect("bv2nat");
        let two = arena.int_const(2);
        let three = arena.int_const(3);
        let l = arena.int_mul(two, nb).expect("mul");
        let r = arena.int_mul(three, nc).expect("mul");
        let diff = arena.int_sub(l, r).expect("sub");
        let neg_one = arena.int_const(-1);
        let atom = arena.int_le(diff, neg_one).expect("le");
        let out = blast_bv2nat_linear(&mut arena, &[atom])
            .expect("blast")
            .expect("in fragment");
        assert!(subtree_is_int_free(&arena, out[0]));
        // Semantic check across the full 4-bit × 4-bit space: the blasted atom
        // evaluates exactly like the integer original.
        let TermNode::Symbol(sb) = *arena.node(b) else {
            unreachable!()
        };
        let TermNode::Symbol(sc) = *arena.node(c) else {
            unreachable!()
        };
        for vb in 0u128..16 {
            for vc in 0u128..16 {
                let mut assignment = axeyum_ir::Assignment::new();
                assignment.set(
                    sb,
                    axeyum_ir::Value::Bv {
                        width: 4,
                        value: vb,
                    },
                );
                assignment.set(
                    sc,
                    axeyum_ir::Value::Bv {
                        width: 4,
                        value: vc,
                    },
                );
                #[allow(clippy::cast_possible_wrap)]
                let expected = 2 * (vb as i128) - 3 * (vc as i128) <= -1;
                let got = axeyum_ir::eval(&arena, out[0], &assignment).expect("eval");
                assert_eq!(
                    got,
                    axeyum_ir::Value::Bool(expected),
                    "vb={vb} vc={vc}: blasted atom must match integer semantics"
                );
            }
        }
    }
}
