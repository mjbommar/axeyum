//! Sums indexed by SUBSETS — the primitive under both general
//! inclusion–exclusion (roadmap W2-19) and Möbius inversion (ADR-1619's named
//! residue).
//!
//! # Why this is not `sumRange` over `2^n` codes
//!
//! ADR-1614 enumerates the subsets of `[0,n)` by a `Nat` code:
//! `Nat.Finset.decode n k` reads the bits of `k < 2^n`. That is the right shape
//! for a *search*, and it is the wrong shape for a *sum*, because the sum needs
//! the SPLIT LAW
//!
//! ```text
//! sumSubsets (succ n) F = sumSubsets n F + sumSubsets n (F ∘ insertAt n)
//! ```
//!
//! — "the subsets of `[0,n+1)` are the subsets of `[0,n)` twice: once without
//! `n` and once with it". Over the code enumeration that law splits the range
//! `[0, 2^(n+1))` at `2^n` and then has to prove
//! `testBit (2^n + k) i = testBit k i` for `i < n` and
//! `testBit (2^n + k) n = 1` — two facts about adding a power of two to a
//! bounded number that this prelude does not have, and that would cost a
//! `div`/`mod`-by-`2^i` development to get. Over the recursion below the same
//! law is `Eq.refl`.
//!
//! So a subset here is a `Nat → Bool` **predicate**, not a `Nat.Finset`, and
//! the enumeration is a fold over the width rather than over a code. The two
//! views are not reconciled in this module and that is recorded as a gap in
//! ADR-1624: `sumSubsets` and `Nat.Finset.anySubset` range over the same `2^n`
//! subsets in the same binary order (`sumSubsets_card` pins the count, and the
//! tests pin the order at `n ≤ 3`), but no theorem here relates them.
//!
//! Dropping the `Nat.Finset` carrier is also what makes the split law free
//! rather than congruence-laden: two `Nat.Finset`s with the same members are
//! not `Eq` (the carrier stores a bound), so a `Finset`-valued enumeration
//! cannot have a `refl` split law at all — `decode n k` and `decode (succ n) k`
//! are different terms for the same set.
//!
//! # What is here
//!
//! ```text
//! Nat.Subsets.empty        := fun _ => false
//! Nat.Subsets.insertAt n s := fun i => if beq i n then true else s i
//!
//! Nat.Subsets.sumSubsets n F              -- Σ over ALL subsets of [0,n)
//!   | 0      F = F empty
//!   | succ m F = sumSubsets m F + sumSubsets m (fun s => F (insertAt m s))
//!
//! Nat.Subsets.sumSel n F b                -- Σ over subsets of PARITY b
//!   | 0      F b = if b then F empty else 0          -- ∅ is even
//!   | succ m F b = sumSel m F b + sumSel m (fun s => F (insertAt m s)) (notB b)
//!
//! Nat.Subsets.sumSelPos n F b             -- the same, over NON-EMPTY subsets
//!   | 0      F b = 0
//!   | succ m F b = sumSelPos m F b + sumSel m (fun s => F (insertAt m s)) (notB b)
//! ```
//!
//! `b = true` means EVEN. The signed sum `Σ (−1)^|s| F s` has no home in `Nat`,
//! so it lands as the graded pair `(sumSel n F true, sumSel n F false)` — the
//! shape ADR-1619 used for Möbius: identities are stated as `even = odd + rest`,
//! never as a subtraction.
//!
//! # The support invariant, and why it is a hypothesis
//!
//! `sumSel n F b` only ever applies `F` to predicates that are `false` at every
//! index `≥ n` — `Nat.Subsets.Supported s n`. A summand that reads `s` above
//! `n` is therefore free to return anything, and every consumer that builds its
//! summand from a width (a product over `[0,n)`, say) needs to know the
//! enumerated sets are supported. `sumSel_congr` is that fact in usable form:
//! two summands agreeing on the SUPPORTED predicates give equal sums. It is the
//! lemma the inclusion–exclusion induction turns on, and it is stated with the
//! obligation explicit rather than hidden inside a `beq`.

#![allow(clippy::many_single_char_names, clippy::too_many_lines)]

use super::NatPrelude;
use super::graph::not_b;
use super::ops::{NatDev, NatOps, bool_true_or_false};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::{BinderInfo, ExprId};

// ---------------------------------------------------------------------------
// Small term builders.
// ---------------------------------------------------------------------------

/// `Nat → Bool` — a subset, as a decidable membership predicate.
pub(super) fn set_ty(d: &mut NatDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    d.arrow(nat, bool_ty)
}

/// `(Nat → Bool) → Nat` — a summand.
pub(super) fn summand_ty(d: &mut NatDev<'_>) -> ExprId {
    let s = set_ty(d);
    let nat = d.nat_ty();
    d.arrow(s, nat)
}

/// `Nat.Subsets.empty`.
pub(super) fn empty_set(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    d.kernel().const_(p.subsets_empty, vec![])
}

/// `Nat.Subsets.insertAt n s`.
pub(super) fn insert_at(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId, s: ExprId) -> ExprId {
    d.const_app(p.subsets_insert_at, &[n, s])
}

/// `Nat.Subsets.sumSubsets n F`.
pub(super) fn sum_subsets(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId, f: ExprId) -> ExprId {
    d.const_app(p.subsets_sum_subsets, &[n, f])
}

/// `Nat.Subsets.sumSel n F b`.
pub(super) fn sum_sel(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n: ExprId,
    f: ExprId,
    b: ExprId,
) -> ExprId {
    d.const_app(p.subsets_sum_sel, &[n, f, b])
}

/// `Nat.Subsets.sumSelPos n F b`.
pub(super) fn sum_sel_pos(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n: ExprId,
    f: ExprId,
    b: ExprId,
) -> ExprId {
    d.const_app(p.subsets_sum_sel_pos, &[n, f, b])
}

/// `Nat.Subsets.Supported s n`.
pub(super) fn supported(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.subsets_supported, &[s, n])
}

/// `fun s => F (insertAt n s)` — the "with `n`" half of the split.
pub(super) fn with_top(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, n: ExprId) -> ExprId {
    let p = *p;
    let sty = set_ty(d);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let ins = insert_at(d, &p, n, s);
    let body = d.apply(f, &[ins]);
    d.lam_fv(s_fv, sty, body)
}

/// `Bool.rec (fun _ => Bool) on_false on_true condition`. Per this prelude's
/// per-file convention, each module carries its own copy.
pub(super) fn bool_select_bool(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    condition: ExprId,
    on_true: ExprId,
    on_false: ExprId,
) -> ExprId {
    let bool_ty = d.bool_ty();
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, bool_ty, bool_ty, BinderInfo::Default);
    let one = d.level_one();
    let rec = d.kernel().const_(p.logic.bool_rec, vec![one]);
    d.apply(rec, &[motive, on_false, on_true, condition])
}

/// Non-dependent `Or.rec` into a `Prop` goal.
#[allow(clippy::too_many_arguments)]
pub(super) fn or_elim(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    left_ty: ExprId,
    right_ty: ExprId,
    goal: ExprId,
    left_case: ExprId,
    right_case: ExprId,
    or_proof: ExprId,
) -> ExprId {
    let anon = d.anon_name();
    let or_ty = d.const_app(p.logic.or, &[left_ty, right_ty]);
    let motive = d.kernel().lam(anon, or_ty, goal, BinderInfo::Default);
    let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
    d.apply(
        or_rec,
        &[left_ty, right_ty, motive, left_case, right_case, or_proof],
    )
}

/// `h1 : a1 = b1`, `h2 : a2 = b2` ⊢ `a1 + a2 = b1 + b2`.
pub(super) fn add_congr(
    d: &mut NatDev<'_>,
    a1: ExprId,
    b1: ExprId,
    h1: ExprId,
    a2: ExprId,
    b2: ExprId,
    h2: ExprId,
) -> ExprId {
    let left = d.congr(a1, b1, h1, &|d, x| d.add(x, a2));
    let right = d.congr(a2, b2, h2, &|d, x| d.add(b1, x));
    let start = d.add(a1, a2);
    let mid = d.add(b1, a2);
    let stop = d.add(b1, b2);
    d.trans(start, mid, stop, left, right)
}

// ---------------------------------------------------------------------------
// The definitions.
// ---------------------------------------------------------------------------

fn declare_definitions(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let sty = set_ty(d);
    let fty = summand_ty(d);
    let anon = d.anon_name();
    let one = d.level_one();

    // empty : Nat -> Bool := fun _ => false
    {
        let fal = d.bool_false();
        let value = d.kernel().lam(anon, nat, fal, BinderInfo::Default);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.subsets_empty,
            uparams: vec![],
            ty: sty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // insertAt : Nat -> (Nat -> Bool) -> Nat -> Bool
    //   := fun n s i => if beq i n then true else s i
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let cond = d.beq(i, n);
        let tv = d.bool_true();
        let si = d.apply(s, &[i]);
        let body = bool_select_bool(d, &p, cond, tv, si);
        let value = {
            let with_i = d.lam_fv(i_fv, nat, body);
            let with_s = d.lam_fv(s_fv, sty, with_i);
            d.lam_fv(n_fv, nat, with_s)
        };
        let ty = {
            let inner = d.arrow(sty, sty);
            d.arrow(nat, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.subsets_insert_at,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(2),
        })?;
    }

    // sumSubsets : Nat -> ((Nat -> Bool) -> Nat) -> Nat
    {
        let carrier = d.arrow(fty, nat);
        let motive = d.kernel().lam(anon, nat, carrier, BinderInfo::Default);
        let base = {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let e = empty_set(d, &p);
            let body = d.apply(f, &[e]);
            d.lam_fv(f_fv, fty, body)
        };
        let step = {
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let left = d.apply(ih, &[f]);
            let shifted = with_top(d, &p, f, m);
            let right = d.apply(ih, &[shifted]);
            let body = d.add(left, right);
            let with_f = d.lam_fv(f_fv, fty, body);
            let with_ih = d.lam_fv(ih_fv, carrier, with_f);
            d.lam_fv(m_fv, nat, with_ih)
        };
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let rec = d.kernel().const_(p.rec, vec![one]);
        let body = d.apply(rec, &[motive, base, step, n]);
        let value = d.lam_fv(n_fv, nat, body);
        let ty = d.arrow(nat, carrier);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.subsets_sum_subsets,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    // sumSel : Nat -> ((Nat -> Bool) -> Nat) -> Bool -> Nat
    {
        let inner = d.arrow(bool_ty, nat);
        let carrier = d.arrow(fty, inner);
        let motive = d.kernel().lam(anon, nat, carrier, BinderInfo::Default);
        let base = {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let e = empty_set(d, &p);
            let at_empty = d.apply(f, &[e]);
            let zero = d.zero();
            let body = d.bool_select_nat(b, at_empty, zero);
            let with_b = d.lam_fv(b_fv, bool_ty, body);
            d.lam_fv(f_fv, fty, with_b)
        };
        let step = {
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let left = d.apply(ih, &[f, b]);
            let shifted = with_top(d, &p, f, m);
            let flipped = not_b(d, &p, b);
            let right = d.apply(ih, &[shifted, flipped]);
            let body = d.add(left, right);
            let with_b = d.lam_fv(b_fv, bool_ty, body);
            let with_f = d.lam_fv(f_fv, fty, with_b);
            let with_ih = d.lam_fv(ih_fv, carrier, with_f);
            d.lam_fv(m_fv, nat, with_ih)
        };
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let rec = d.kernel().const_(p.rec, vec![one]);
        let body = d.apply(rec, &[motive, base, step, n]);
        let value = d.lam_fv(n_fv, nat, body);
        let ty = d.arrow(nat, carrier);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.subsets_sum_sel,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(5),
        })?;
    }

    // sumSelPos : Nat -> ((Nat -> Bool) -> Nat) -> Bool -> Nat
    {
        let inner = d.arrow(bool_ty, nat);
        let carrier = d.arrow(fty, inner);
        let motive = d.kernel().lam(anon, nat, carrier, BinderInfo::Default);
        let base = {
            let f_fv = d.fresh_fvar();
            let b_fv = d.fresh_fvar();
            let zero = d.zero();
            let with_b = d.lam_fv(b_fv, bool_ty, zero);
            d.lam_fv(f_fv, fty, with_b)
        };
        let step = {
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let left = d.apply(ih, &[f, b]);
            let shifted = with_top(d, &p, f, m);
            let flipped = not_b(d, &p, b);
            let right = sum_sel(d, &p, m, shifted, flipped);
            let body = d.add(left, right);
            let with_b = d.lam_fv(b_fv, bool_ty, body);
            let with_f = d.lam_fv(f_fv, fty, with_b);
            let with_ih = d.lam_fv(ih_fv, carrier, with_f);
            d.lam_fv(m_fv, nat, with_ih)
        };
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let rec = d.kernel().const_(p.rec, vec![one]);
        let body = d.apply(rec, &[motive, base, step, n]);
        let value = d.lam_fv(n_fv, nat, body);
        let ty = d.arrow(nat, carrier);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.subsets_sum_sel_pos,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(6),
        })?;
    }

    // Supported : (Nat -> Bool) -> Nat -> Prop
    //   := fun s n => forall i, Le n i -> Eq Bool (s i) false
    {
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hle = d.le(n, i);
        let si = d.apply(s, &[i]);
        let fal = d.bool_false();
        let concl = d.bool_eq(si, fal);
        let with_hle = d.arrow(hle, concl);
        let body = d.pi_fv(i_fv, nat, with_hle);
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            d.lam_fv(s_fv, sty, with_n)
        };
        let zero_level = d.kernel().level_zero();
        let prop = d.kernel().sort(zero_level);
        let ty = {
            let inner = d.arrow(nat, prop);
            d.arrow(sty, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.subsets_supported,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(2),
        })?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// The equations — every one of them `Eq.refl`.
// ---------------------------------------------------------------------------

/// The six unfolding equations, including THE SPLIT LAW.
fn declare_equations(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let fty = summand_ty(d);

    // sumSubsets_zero : forall F, sumSubsets 0 F = F empty
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let zero = d.zero();
        let lhs = sum_subsets(d, &p, zero, f);
        let e = empty_set(d, &p);
        let rhs = d.apply(f, &[e]);
        let concl = d.eq(lhs, rhs);
        let ty = d.pi_fv(f_fv, fty, concl);
        let proof = d.refl(lhs);
        let value = d.lam_fv(f_fv, fty, proof);
        d.declare_theorem(p.subsets_sum_subsets_zero, ty, value)?;
    }

    // sumSubsets_succ (THE SPLIT LAW)
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.succ(n);
        let lhs = sum_subsets(d, &p, sn, f);
        let low = sum_subsets(d, &p, n, f);
        let shifted = with_top(d, &p, f, n);
        let high = sum_subsets(d, &p, n, shifted);
        let rhs = d.add(low, high);
        let concl = d.eq(lhs, rhs);
        let ty = {
            let with_n = d.pi_fv(n_fv, nat, concl);
            d.pi_fv(f_fv, fty, with_n)
        };
        let proof = d.refl(lhs);
        let value = {
            let with_n = d.lam_fv(n_fv, nat, proof);
            d.lam_fv(f_fv, fty, with_n)
        };
        d.declare_theorem(p.subsets_sum_subsets_succ, ty, value)?;
    }

    // sumSel_zero : forall F b, sumSel 0 F b = if b then F empty else 0
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let zero = d.zero();
        let lhs = sum_sel(d, &p, zero, f, b);
        let e = empty_set(d, &p);
        let at_empty = d.apply(f, &[e]);
        let z = d.zero();
        let rhs = d.bool_select_nat(b, at_empty, z);
        let concl = d.eq(lhs, rhs);
        let ty = {
            let with_b = d.pi_fv(b_fv, bool_ty, concl);
            d.pi_fv(f_fv, fty, with_b)
        };
        let proof = d.refl(lhs);
        let value = {
            let with_b = d.lam_fv(b_fv, bool_ty, proof);
            d.lam_fv(f_fv, fty, with_b)
        };
        d.declare_theorem(p.subsets_sum_sel_zero, ty, value)?;
    }

    // sumSel_succ (THE GRADED SPLIT LAW)
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let sn = d.succ(n);
        let lhs = sum_sel(d, &p, sn, f, b);
        let low = sum_sel(d, &p, n, f, b);
        let shifted = with_top(d, &p, f, n);
        let flipped = not_b(d, &p, b);
        let high = sum_sel(d, &p, n, shifted, flipped);
        let rhs = d.add(low, high);
        let concl = d.eq(lhs, rhs);
        let ty = {
            let with_b = d.pi_fv(b_fv, bool_ty, concl);
            let with_n = d.pi_fv(n_fv, nat, with_b);
            d.pi_fv(f_fv, fty, with_n)
        };
        let proof = d.refl(lhs);
        let value = {
            let with_b = d.lam_fv(b_fv, bool_ty, proof);
            let with_n = d.lam_fv(n_fv, nat, with_b);
            d.lam_fv(f_fv, fty, with_n)
        };
        d.declare_theorem(p.subsets_sum_sel_succ, ty, value)?;
    }

    // sumSelPos_zero : forall F b, sumSelPos 0 F b = 0
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let zero = d.zero();
        let lhs = sum_sel_pos(d, &p, zero, f, b);
        let rhs = d.zero();
        let concl = d.eq(lhs, rhs);
        let ty = {
            let with_b = d.pi_fv(b_fv, bool_ty, concl);
            d.pi_fv(f_fv, fty, with_b)
        };
        let proof = d.refl(lhs);
        let value = {
            let with_b = d.lam_fv(b_fv, bool_ty, proof);
            d.lam_fv(f_fv, fty, with_b)
        };
        d.declare_theorem(p.subsets_sum_sel_pos_zero, ty, value)?;
    }

    // sumSelPos_succ
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let sn = d.succ(n);
        let lhs = sum_sel_pos(d, &p, sn, f, b);
        let low = sum_sel_pos(d, &p, n, f, b);
        let shifted = with_top(d, &p, f, n);
        let flipped = not_b(d, &p, b);
        let high = sum_sel(d, &p, n, shifted, flipped);
        let rhs = d.add(low, high);
        let concl = d.eq(lhs, rhs);
        let ty = {
            let with_b = d.pi_fv(b_fv, bool_ty, concl);
            let with_n = d.pi_fv(n_fv, nat, with_b);
            d.pi_fv(f_fv, fty, with_n)
        };
        let proof = d.refl(lhs);
        let value = {
            let with_b = d.lam_fv(b_fv, bool_ty, proof);
            let with_n = d.lam_fv(n_fv, nat, with_b);
            d.lam_fv(f_fv, fty, with_n)
        };
        d.declare_theorem(p.subsets_sum_sel_pos_succ, ty, value)?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// The support invariant.
// ---------------------------------------------------------------------------

/// `supported_empty`, `supported_succ` and `supported_insertAt`.
fn declare_support(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let sty = set_ty(d);

    // supported_empty : forall n, Supported empty n
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let e = empty_set(d, &p);
        let concl = supported(d, &p, e, n);
        let ty = d.pi_fv(n_fv, nat, concl);
        let proof = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hle_ty = d.le(n, i);
            let hle_fv = d.fresh_fvar();
            let fal = d.bool_false();
            let body = d.bool_refl(fal);
            let with_h = d.lam_fv(hle_fv, hle_ty, body);
            d.lam_fv(i_fv, nat, with_h)
        };
        let value = d.lam_fv(n_fv, nat, proof);
        d.declare_theorem(p.subsets_supported_empty, ty, value)?;
    }

    // supported_succ : forall s n, Supported s n -> Supported s (succ n)
    {
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let hyp_ty = supported(d, &p, s, n);
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);
        let sn = d.succ(n);
        let concl = supported(d, &p, s, sn);
        let proof = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hle_ty = d.le(sn, i);
            let hle_fv = d.fresh_fvar();
            let hle = d.kernel().fvar(hle_fv);
            let step = d.lemma(p.le_succ, &[n]);
            let down = d.lemma(p.le_trans, &[n, sn, i, step, hle]);
            let body = d.apply(hyp, &[i, down]);
            let with_h = d.lam_fv(hle_fv, hle_ty, body);
            d.lam_fv(i_fv, nat, with_h)
        };
        let ty = {
            let with_hyp = d.arrow(hyp_ty, concl);
            let with_n = d.pi_fv(n_fv, nat, with_hyp);
            d.pi_fv(s_fv, sty, with_n)
        };
        let value = {
            let with_hyp = d.lam_fv(hyp_fv, hyp_ty, proof);
            let with_n = d.lam_fv(n_fv, nat, with_hyp);
            d.lam_fv(s_fv, sty, with_n)
        };
        d.declare_theorem(p.subsets_supported_succ, ty, value)?;
    }

    // supported_insertAt : forall s n, Supported s n -> Supported (insertAt n s) (succ n)
    {
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let hyp_ty = supported(d, &p, s, n);
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);
        let sn = d.succ(n);
        let ins = insert_at(d, &p, n, s);
        let concl = supported(d, &p, ins, sn);
        let proof = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hle_ty = d.le(sn, i);
            let hle_fv = d.fresh_fvar();
            let hle = d.kernel().fvar(hle_fv);

            // `i ≠ n`: otherwise `succ n ≤ n`.
            let ne_proof = {
                let he_fv = d.fresh_fvar();
                let he = d.kernel().fvar(he_fv);
                let he_ty = d.eq(i, n);
                let motive = d.eq_motive(i, &|d, x| d.le(sn, x));
                let moved = d.transport(i, motive, hle, n, he);
                let absurd = d.lemma(p.not_succ_le_self, &[n, moved]);
                d.lam_fv(he_fv, he_ty, absurd)
            };
            let beq_false = d.lemma(p.beq_eq_false_of_ne, &[i, n, ne_proof]);

            // `insertAt n s i = s i`.
            let cond = d.beq(i, n);
            let tv = d.bool_true();
            let si = d.apply(s, &[i]);
            let sel = bool_select_bool(d, &p, cond, tv, si);
            let fal = d.bool_false();
            let back = d.bool_symm(cond, fal, beq_false);
            let motive = d.bool_eq_motive(fal, &|d, v| {
                let tv = d.bool_true();
                let inner = bool_select_bool(d, &p, v, tv, si);
                d.bool_eq(inner, si)
            });
            let refl_case = d.bool_refl(si);
            let unfolded = d.bool_transport(fal, motive, refl_case, cond, back);

            let step = d.lemma(p.le_succ, &[n]);
            let down = d.lemma(p.le_trans, &[n, sn, i, step, hle]);
            let s_false = d.apply(hyp, &[i, down]);
            let body = d.bool_trans(sel, si, fal, unfolded, s_false);
            let with_h = d.lam_fv(hle_fv, hle_ty, body);
            d.lam_fv(i_fv, nat, with_h)
        };
        let ty = {
            let with_hyp = d.arrow(hyp_ty, concl);
            let with_n = d.pi_fv(n_fv, nat, with_hyp);
            d.pi_fv(s_fv, sty, with_n)
        };
        let value = {
            let with_hyp = d.lam_fv(hyp_fv, hyp_ty, proof);
            let with_n = d.lam_fv(n_fv, nat, with_hyp);
            d.lam_fv(s_fv, sty, with_n)
        };
        d.declare_theorem(p.subsets_supported_insert_at, ty, value)?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// `sumSel_congr` — the lemma every width-indexed summand consumes.
// ---------------------------------------------------------------------------

/// `Nat.Subsets.sumSel_congr : ∀ n F G b,
/// (∀ s, Supported s n → F s = G s) → sumSel n F b = sumSel n G b`.
fn declare_sum_sel_congr(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let sty = set_ty(d);
    let fty = summand_ty(d);

    let agree_ty = |d: &mut NatDev<'_>, f: ExprId, g: ExprId, w: ExprId| -> ExprId {
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let sup = supported(d, &p, s, w);
        let fs = d.apply(f, &[s]);
        let gs = d.apply(g, &[s]);
        let eq = d.eq(fs, gs);
        let with_sup = d.arrow(sup, eq);
        d.pi_fv(s_fv, sty, with_sup)
    };

    let motive_at = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let agree = agree_ty(d, f, g, n);
        let lhs = sum_sel(d, &p, n, f, b);
        let rhs = sum_sel(d, &p, n, g, b);
        let concl = d.eq(lhs, rhs);
        let with_agree = d.arrow(agree, concl);
        let with_b = d.pi_fv(b_fv, bool_ty, with_agree);
        let with_g = d.pi_fv(g_fv, fty, with_b);
        d.pi_fv(f_fv, fty, with_g)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let body = d.induct(
        &|d, x| motive_at(d, x),
        &|d| {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let zero = d.zero();
            let hyp_ty = agree_ty(d, f, g, zero);
            let hyp_fv = d.fresh_fvar();
            let hyp = d.kernel().fvar(hyp_fv);
            let e = empty_set(d, &p);
            let sup = d.lemma(p.subsets_supported_empty, &[zero]);
            let at_empty = d.apply(hyp, &[e, sup]);
            let fe = d.apply(f, &[e]);
            let ge = d.apply(g, &[e]);
            let proof = d.congr(fe, ge, at_empty, &|d, x| {
                let z = d.zero();
                d.bool_select_nat(b, x, z)
            });
            let with_hyp = d.lam_fv(hyp_fv, hyp_ty, proof);
            let with_b = d.lam_fv(b_fv, bool_ty, with_hyp);
            let with_g = d.lam_fv(g_fv, fty, with_b);
            d.lam_fv(f_fv, fty, with_g)
        },
        &|d, j, ih| {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let sj = d.succ(j);
            let hyp_ty = agree_ty(d, f, g, sj);
            let hyp_fv = d.fresh_fvar();
            let hyp = d.kernel().fvar(hyp_fv);

            let low_agree = {
                let s_fv = d.fresh_fvar();
                let s = d.kernel().fvar(s_fv);
                let sup_j = supported(d, &p, s, j);
                let hs_fv = d.fresh_fvar();
                let hs = d.kernel().fvar(hs_fv);
                let lifted = d.lemma(p.subsets_supported_succ, &[s, j, hs]);
                let body = d.apply(hyp, &[s, lifted]);
                let with_hs = d.lam_fv(hs_fv, sup_j, body);
                d.lam_fv(s_fv, sty, with_hs)
            };
            let low = d.apply(ih, &[f, g, b, low_agree]);

            let f_top = with_top(d, &p, f, j);
            let g_top = with_top(d, &p, g, j);
            let high_agree = {
                let s_fv = d.fresh_fvar();
                let s = d.kernel().fvar(s_fv);
                let sup_j = supported(d, &p, s, j);
                let hs_fv = d.fresh_fvar();
                let hs = d.kernel().fvar(hs_fv);
                let lifted = d.lemma(p.subsets_supported_insert_at, &[s, j, hs]);
                let ins = insert_at(d, &p, j, s);
                let body = d.apply(hyp, &[ins, lifted]);
                let with_hs = d.lam_fv(hs_fv, sup_j, body);
                d.lam_fv(s_fv, sty, with_hs)
            };
            let flipped = not_b(d, &p, b);
            let high = d.apply(ih, &[f_top, g_top, flipped, high_agree]);

            let a1 = sum_sel(d, &p, j, f, b);
            let b1 = sum_sel(d, &p, j, g, b);
            let a2 = sum_sel(d, &p, j, f_top, flipped);
            let b2 = sum_sel(d, &p, j, g_top, flipped);
            let proof = add_congr(d, a1, b1, low, a2, b2, high);

            let with_hyp = d.lam_fv(hyp_fv, hyp_ty, proof);
            let with_b = d.lam_fv(b_fv, bool_ty, with_hyp);
            let with_g = d.lam_fv(g_fv, fty, with_b);
            d.lam_fv(f_fv, fty, with_g)
        },
        n,
    );

    let stmt = motive_at(d, n);
    let ty = d.pi_fv(n_fv, nat, stmt);
    let value = d.lam_fv(n_fv, nat, body);
    d.declare_theorem(p.subsets_sum_sel_congr, ty, value)
}

// ---------------------------------------------------------------------------
// The grading laws.
// ---------------------------------------------------------------------------

/// `Nat.Subsets.sumSel_add : ∀ n F,
/// sumSel n F true + sumSel n F false = sumSubsets n F`.
fn declare_sum_sel_add(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fty = summand_ty(d);

    let motive_at = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let tv = d.bool_true();
        let fal = d.bool_false();
        let even = sum_sel(d, &p, n, f, tv);
        let odd = sum_sel(d, &p, n, f, fal);
        let lhs = d.add(even, odd);
        let rhs = sum_subsets(d, &p, n, f);
        let concl = d.eq(lhs, rhs);
        d.pi_fv(f_fv, fty, concl)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let body = d.induct(
        &|d, x| motive_at(d, x),
        &|d| {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let e = empty_set(d, &p);
            let at_empty = d.apply(f, &[e]);
            let proof = d.lemma(p.add_zero, &[at_empty]);
            d.lam_fv(f_fv, fty, proof)
        },
        &|d, j, ih| {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let tv = d.bool_true();
            let fal = d.bool_false();
            let f_top = with_top(d, &p, f, j);

            let x = sum_sel(d, &p, j, f, tv);
            let y = sum_sel(d, &p, j, f, fal);
            let z = sum_sel(d, &p, j, f_top, tv);
            let w = sum_sel(d, &p, j, f_top, fal);

            // `(x + w) + (y + z) = (x + y) + (w + z)`.
            let regroup = d.lemma(p.add_add_add_comm, &[x, w, y, z]);
            let xy = d.add(x, y);
            let wz = d.add(w, z);
            let zw = d.add(z, w);
            let swap_inner = d.lemma(p.add_comm, &[w, z]);
            let fix = d.congr(wz, zw, swap_inner, &|d, t| d.add(xy, t));

            let start = {
                let xw = d.add(x, w);
                let yz = d.add(y, z);
                d.add(xw, yz)
            };
            let mid = d.add(xy, wz);
            let mid2 = d.add(xy, zw);
            let step1 = d.trans(start, mid, mid2, regroup, fix);

            let ih_f = d.apply(ih, &[f]);
            let ih_top = d.apply(ih, &[f_top]);
            let sub_f = sum_subsets(d, &p, j, f);
            let sub_top = sum_subsets(d, &p, j, f_top);
            let step2 = add_congr(d, xy, sub_f, ih_f, zw, sub_top, ih_top);
            let stop = d.add(sub_f, sub_top);
            let proof = d.trans(start, mid2, stop, step1, step2);
            d.lam_fv(f_fv, fty, proof)
        },
        n,
    );

    let stmt = motive_at(d, n);
    let ty = d.pi_fv(n_fv, nat, stmt);
    let value = d.lam_fv(n_fv, nat, body);
    d.declare_theorem(p.subsets_sum_sel_add, ty, value)
}

/// `fun s => F s * c`.
fn scale(d: &mut NatDev<'_>, f: ExprId, c: ExprId) -> ExprId {
    let sty = set_ty(d);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let fs = d.apply(f, &[s]);
    let body = d.mul(fs, c);
    d.lam_fv(s_fv, sty, body)
}

/// `Nat.Subsets.sumSel_mul_right : ∀ n F c b,
/// sumSel n (fun s => F s * c) b = sumSel n F b * c`.
///
/// The scaling law. Inclusion–exclusion's induction step pulls the new
/// element's indicator out of the "with `n`" half of the split, and this is
/// what lets it.
fn declare_sum_sel_mul_right(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let fty = summand_ty(d);

    let motive_at = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let scaled = scale(d, f, c);
        let lhs = sum_sel(d, &p, n, scaled, b);
        let plain = sum_sel(d, &p, n, f, b);
        let rhs = d.mul(plain, c);
        let concl = d.eq(lhs, rhs);
        let with_b = d.pi_fv(b_fv, bool_ty, concl);
        let with_c = d.pi_fv(c_fv, nat, with_b);
        d.pi_fv(f_fv, fty, with_c)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let body = d.induct(
        &|d, x| motive_at(d, x),
        &|d| {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let c_fv = d.fresh_fvar();
            let c = d.kernel().fvar(c_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let e = empty_set(d, &p);
            let fe = d.apply(f, &[e]);

            // `Eq (sel v (fe*c) 0) (sel v fe 0 * c)`, at a `Bool` value `v`.
            let goal_at = |d: &mut NatDev<'_>, v: ExprId| -> ExprId {
                let z = d.zero();
                let scaled = d.mul(fe, c);
                let lhs = d.bool_select_nat(v, scaled, z);
                let z2 = d.zero();
                let plain = d.bool_select_nat(v, fe, z2);
                let rhs = d.mul(plain, c);
                d.eq(lhs, rhs)
            };

            let tv = d.bool_true();
            let fal = d.bool_false();
            let is_true = d.bool_eq(b, tv);
            let is_false = d.bool_eq(b, fal);
            let decided = bool_true_or_false(d, &p, b);
            let goal = goal_at(d, b);

            let on_true = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let back = d.bool_symm(b, tv, h);
                let motive = d.bool_eq_motive(tv, &|d, v| goal_at(d, v));
                let refl_case = {
                    let scaled = d.mul(fe, c);
                    d.refl(scaled)
                };
                let proof = d.bool_transport(tv, motive, refl_case, b, back);
                d.lam_fv(h_fv, is_true, proof)
            };
            let on_false = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let back = d.bool_symm(b, fal, h);
                let motive = d.bool_eq_motive(fal, &|d, v| goal_at(d, v));
                let refl_case = {
                    // `0 = 0 * c`.
                    let zc = d.lemma(p.zero_mul, &[c]);
                    let z = d.zero();
                    let zero_times = d.mul(z, c);
                    d.symm(zero_times, z, zc)
                };
                let proof = d.bool_transport(fal, motive, refl_case, b, back);
                d.lam_fv(h_fv, is_false, proof)
            };
            let proof = or_elim(d, &p, is_true, is_false, goal, on_true, on_false, decided);
            let with_b = d.lam_fv(b_fv, bool_ty, proof);
            let with_c = d.lam_fv(c_fv, nat, with_b);
            d.lam_fv(f_fv, fty, with_c)
        },
        &|d, j, ih| {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let c_fv = d.fresh_fvar();
            let c = d.kernel().fvar(c_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let f_top = with_top(d, &p, f, j);
            let flipped = not_b(d, &p, b);

            let low = d.apply(ih, &[f, c, b]);
            let high = d.apply(ih, &[f_top, c, flipped]);

            let scaled = scale(d, f, c);
            let scaled_top = scale(d, f_top, c);
            let a1 = sum_sel(d, &p, j, scaled, b);
            let a2 = sum_sel(d, &p, j, scaled_top, flipped);
            let x = sum_sel(d, &p, j, f, b);
            let y = sum_sel(d, &p, j, f_top, flipped);
            let b1 = d.mul(x, c);
            let b2 = d.mul(y, c);
            let joined = add_congr(d, a1, b1, low, a2, b2, high);

            // `x*c + y*c = (x + y) * c`.
            let distrib = d.lemma(p.right_distrib, &[x, y, c]);
            let sum_xy = d.add(x, y);
            let scaled_sum = d.mul(sum_xy, c);
            let split_sum = d.add(b1, b2);
            let back = d.symm(scaled_sum, split_sum, distrib);

            let start = d.add(a1, a2);
            let proof = d.trans(start, split_sum, scaled_sum, joined, back);
            let with_b = d.lam_fv(b_fv, bool_ty, proof);
            let with_c = d.lam_fv(c_fv, nat, with_b);
            d.lam_fv(f_fv, fty, with_c)
        },
        n,
    );

    let stmt = motive_at(d, n);
    let ty = d.pi_fv(n_fv, nat, stmt);
    let value = d.lam_fv(n_fv, nat, body);
    d.declare_theorem(p.subsets_sum_sel_mul_right, ty, value)
}

/// `Nat.Subsets.sumSel_swap : ∀ n G b m,
/// sumSel n (fun s => sumRange (fun v => G s v) m) b
///   = sumRange (fun v => sumSel n (fun s => G s v) b) m`.
///
/// The subset sum commutes with a range sum. Inclusion–exclusion is this lemma
/// plus a per-element identity: the outer sum runs over subsets, the inner over
/// the ambient range, and the whole argument is "swap, then count one element
/// at a time".
fn declare_sum_sel_swap(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let sty = set_ty(d);
    let gty = {
        let inner = d.arrow(nat, nat);
        d.arrow(sty, inner)
    };

    // `fun s => sumRange (fun v => G s v) m`.
    let rows = |d: &mut NatDev<'_>, g: ExprId, m: ExprId| -> ExprId {
        let sty = set_ty(d);
        let nat = d.nat_ty();
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let gsv = d.apply(g, &[s, v]);
        let row = d.lam_fv(v_fv, nat, gsv);
        let body = d.sum_range(row, m);
        d.lam_fv(s_fv, sty, body)
    };

    // `fun s => G s v`, one column.
    let column = |d: &mut NatDev<'_>, g: ExprId, v: ExprId| -> ExprId {
        let sty = set_ty(d);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let gsv = d.apply(g, &[s, v]);
        d.lam_fv(s_fv, sty, gsv)
    };

    let motive_at = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let outer = rows(d, g, m);
        let lhs = sum_sel(d, &p, n, outer, b);
        let rhs = {
            let v_fv = d.fresh_fvar();
            let v = d.kernel().fvar(v_fv);
            let col = column(d, g, v);
            let inner = sum_sel(d, &p, n, col, b);
            let f = d.lam_fv(v_fv, nat, inner);
            d.sum_range(f, m)
        };
        let concl = d.eq(lhs, rhs);
        let with_m = d.pi_fv(m_fv, nat, concl);
        let with_b = d.pi_fv(b_fv, bool_ty, with_m);
        d.pi_fv(g_fv, gty, with_b)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let body = d.induct(
        &|d, x| motive_at(d, x),
        &|d| {
            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let e = empty_set(d, &p);

            // `fun v => G empty v`.
            let empty_row = {
                let v_fv = d.fresh_fvar();
                let v = d.kernel().fvar(v_fv);
                let gev = d.apply(g, &[e, v]);
                d.lam_fv(v_fv, nat, gev)
            };

            // `Eq (sel value (sumRange empty_row m) 0)
            //     (sumRange (fun v => sel value (G empty v) 0) m)`.
            let goal_at = |d: &mut NatDev<'_>, value: ExprId| -> ExprId {
                let z = d.zero();
                let total = d.sum_range(empty_row, m);
                let lhs = d.bool_select_nat(value, total, z);
                let rhs = {
                    let v_fv = d.fresh_fvar();
                    let v = d.kernel().fvar(v_fv);
                    let gev = d.apply(g, &[e, v]);
                    let z2 = d.zero();
                    let sel = d.bool_select_nat(value, gev, z2);
                    let f = d.lam_fv(v_fv, nat, sel);
                    d.sum_range(f, m)
                };
                d.eq(lhs, rhs)
            };

            let tv = d.bool_true();
            let fal = d.bool_false();
            let is_true = d.bool_eq(b, tv);
            let is_false = d.bool_eq(b, fal);
            let decided = bool_true_or_false(d, &p, b);
            let goal = goal_at(d, b);

            let on_true = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let back = d.bool_symm(b, tv, h);
                let motive = d.bool_eq_motive(tv, &|d, v| goal_at(d, v));
                let refl_case = {
                    let total = d.sum_range(empty_row, m);
                    d.refl(total)
                };
                let proof = d.bool_transport(tv, motive, refl_case, b, back);
                d.lam_fv(h_fv, is_true, proof)
            };
            let on_false = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let back = d.bool_symm(b, fal, h);
                let motive = d.bool_eq_motive(fal, &|d, v| goal_at(d, v));
                let refl_case = {
                    // `0 = sumRange (fun _ => 0) m`.
                    let vanish = d.lemma(p.sum_range_const_zero, &[m]);
                    let zeros = {
                        let anon = d.anon_name();
                        let nat = d.nat_ty();
                        let z = d.zero();
                        let f = d.kernel().lam(anon, nat, z, BinderInfo::Default);
                        d.sum_range(f, m)
                    };
                    let z = d.zero();
                    d.symm(zeros, z, vanish)
                };
                let proof = d.bool_transport(fal, motive, refl_case, b, back);
                d.lam_fv(h_fv, is_false, proof)
            };
            let proof = or_elim(d, &p, is_true, is_false, goal, on_true, on_false, decided);
            let with_m = d.lam_fv(m_fv, nat, proof);
            let with_b = d.lam_fv(b_fv, bool_ty, with_m);
            d.lam_fv(g_fv, gty, with_b)
        },
        &|d, j, ih| {
            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let flipped = not_b(d, &p, b);

            // `G' s v := G (insertAt j s) v`.
            let g_top = {
                let s_fv = d.fresh_fvar();
                let s = d.kernel().fvar(s_fv);
                let v_fv = d.fresh_fvar();
                let v = d.kernel().fvar(v_fv);
                let ins = insert_at(d, &p, j, s);
                let body = d.apply(g, &[ins, v]);
                let with_v = d.lam_fv(v_fv, nat, body);
                d.lam_fv(s_fv, sty, with_v)
            };

            let low = d.apply(ih, &[g, b, m]);
            let high = d.apply(ih, &[g_top, flipped, m]);

            let outer = rows(d, g, m);
            let outer_top = rows(d, g_top, m);
            let a1 = sum_sel(d, &p, j, outer, b);
            let a2 = sum_sel(d, &p, j, outer_top, flipped);

            // `fun v => sumSel j (fun s => G s v) b`.
            let col_sum = |d: &mut NatDev<'_>, gg: ExprId, bb: ExprId| -> ExprId {
                let nat = d.nat_ty();
                let v_fv = d.fresh_fvar();
                let v = d.kernel().fvar(v_fv);
                let col = column(d, gg, v);
                let inner = sum_sel(d, &p, j, col, bb);
                d.lam_fv(v_fv, nat, inner)
            };
            let left_fn = col_sum(d, g, b);
            let right_fn = col_sum(d, g_top, flipped);
            let b1 = d.sum_range(left_fn, m);
            let b2 = d.sum_range(right_fn, m);
            let joined = add_congr(d, a1, b1, low, a2, b2, high);

            // `sumRange left + sumRange right = sumRange (fun v => left v + right v)`.
            let merged = {
                let nat = d.nat_ty();
                let v_fv = d.fresh_fvar();
                let v = d.kernel().fvar(v_fv);
                let l = d.apply(left_fn, &[v]);
                let r = d.apply(right_fn, &[v]);
                let body = d.add(l, r);
                let f = d.lam_fv(v_fv, nat, body);
                d.sum_range(f, m)
            };
            let split = d.lemma(p.sum_range_add, &[left_fn, right_fn, m]);
            let split_sum = d.add(b1, b2);
            let back = d.symm(merged, split_sum, split);

            let start = d.add(a1, a2);
            let proof = d.trans(start, split_sum, merged, joined, back);
            let with_m = d.lam_fv(m_fv, nat, proof);
            let with_b = d.lam_fv(b_fv, bool_ty, with_m);
            d.lam_fv(g_fv, gty, with_b)
        },
        n,
    );

    let stmt = motive_at(d, n);
    let ty = d.pi_fv(n_fv, nat, stmt);
    let value = d.lam_fv(n_fv, nat, body);
    d.declare_theorem(p.subsets_sum_sel_swap, ty, value)
}

/// `sumSel_true_eq_empty_add_pos` and `sumSel_false_eq_pos` — the empty set is
/// the only difference between the graded sum and its non-empty restriction,
/// and it sits entirely on the EVEN side.
fn declare_pos_split(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fty = summand_ty(d);

    // sumSel_false_eq_pos : forall n F, sumSel n F false = sumSelPos n F false
    {
        let motive_at = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let fal = d.bool_false();
            let lhs = sum_sel(d, &p, n, f, fal);
            let rhs = sum_sel_pos(d, &p, n, f, fal);
            let concl = d.eq(lhs, rhs);
            d.pi_fv(f_fv, fty, concl)
        };
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = d.induct(
            &|d, x| motive_at(d, x),
            &|d| {
                let f_fv = d.fresh_fvar();
                let zero = d.zero();
                let proof = d.refl(zero);
                d.lam_fv(f_fv, fty, proof)
            },
            &|d, j, ih| {
                let f_fv = d.fresh_fvar();
                let f = d.kernel().fvar(f_fv);
                let fal = d.bool_false();
                let tv = d.bool_true();
                let f_top = with_top(d, &p, f, j);
                let tail = sum_sel(d, &p, j, f_top, tv);
                let a1 = sum_sel(d, &p, j, f, fal);
                let b1 = sum_sel_pos(d, &p, j, f, fal);
                let step = d.apply(ih, &[f]);
                let proof = d.congr(a1, b1, step, &|d, x| d.add(x, tail));
                d.lam_fv(f_fv, fty, proof)
            },
            n,
        );
        let stmt = motive_at(d, n);
        let ty = d.pi_fv(n_fv, nat, stmt);
        let value = d.lam_fv(n_fv, nat, body);
        d.declare_theorem(p.subsets_sum_sel_false_pos, ty, value)?;
    }

    // sumSel_true_eq_empty_add_pos :
    //   forall n F, sumSel n F true = F empty + sumSelPos n F true
    {
        let motive_at = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let tv = d.bool_true();
            let lhs = sum_sel(d, &p, n, f, tv);
            let e = empty_set(d, &p);
            let at_empty = d.apply(f, &[e]);
            let pos = sum_sel_pos(d, &p, n, f, tv);
            let rhs = d.add(at_empty, pos);
            let concl = d.eq(lhs, rhs);
            d.pi_fv(f_fv, fty, concl)
        };
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = d.induct(
            &|d, x| motive_at(d, x),
            &|d| {
                let f_fv = d.fresh_fvar();
                let f = d.kernel().fvar(f_fv);
                let e = empty_set(d, &p);
                let at_empty = d.apply(f, &[e]);
                let plus_zero = d.lemma(p.add_zero, &[at_empty]);
                let z = d.zero();
                let sum = d.add(at_empty, z);
                let proof = d.symm(sum, at_empty, plus_zero);
                d.lam_fv(f_fv, fty, proof)
            },
            &|d, j, ih| {
                let f_fv = d.fresh_fvar();
                let f = d.kernel().fvar(f_fv);
                let tv = d.bool_true();
                let fal = d.bool_false();
                let e = empty_set(d, &p);
                let at_empty = d.apply(f, &[e]);
                let f_top = with_top(d, &p, f, j);
                let tail = sum_sel(d, &p, j, f_top, fal);

                let a1 = sum_sel(d, &p, j, f, tv);
                let pos = sum_sel_pos(d, &p, j, f, tv);
                let b1 = d.add(at_empty, pos);
                let step = d.apply(ih, &[f]);
                let lifted = d.congr(a1, b1, step, &|d, x| d.add(x, tail));

                // `(F empty + Pos) + tail = F empty + (Pos + tail)`.
                let assoc = d.lemma(p.add_assoc, &[at_empty, pos, tail]);
                let mid = d.add(b1, tail);
                let stop = {
                    let inner = d.add(pos, tail);
                    d.add(at_empty, inner)
                };
                let start = d.add(a1, tail);
                let proof = d.trans(start, mid, stop, lifted, assoc);
                d.lam_fv(f_fv, fty, proof)
            },
            n,
        );
        let stmt = motive_at(d, n);
        let ty = d.pi_fv(n_fv, nat, stmt);
        let value = d.lam_fv(n_fv, nat, body);
        d.declare_theorem(p.subsets_sum_sel_true_split, ty, value)?;
    }

    Ok(())
}

/// `Nat.Subsets.sumSubsets_card : ∀ n, sumSubsets n (fun _ => 1) = pow 2 n`.
///
/// The fold really does visit `2^n` subsets, and `pow 2 n` is never formed
/// here, only named. What this does NOT pin is that the two halves are
/// DIFFERENT: a fold whose step read `ih F + ih F` satisfies this law too (both
/// halves are `2^(n-1)`), and so does the split law, which is `refl` in any
/// enumeration that recurses on the width. `sumSel_add` refutes that mutant —
/// it ties the graded fold to this one — and so does the evaluation test
/// `sumSubsets 2 card = 4`, which such a fold answers `0`.
fn declare_sum_subsets_card(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let ones = |d: &mut NatDev<'_>| -> ExprId {
        let sty = set_ty(d);
        let anon = d.anon_name();
        let one = d.num(1);
        d.kernel().lam(anon, sty, one, BinderInfo::Default)
    };

    let motive_at = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
        let k = ones(d);
        let lhs = sum_subsets(d, &p, n, k);
        let two = d.num(2);
        let rhs = d.pow(two, n);
        d.eq(lhs, rhs)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let body = d.induct(
        &|d, x| motive_at(d, x),
        &|d| {
            let two = d.num(2);
            let zero = d.zero();
            let at_zero = d.lemma(p.pow_zero, &[two]);
            let two_again = d.num(2);
            let powered = d.pow(two_again, zero);
            let one = d.num(1);
            d.symm(powered, one, at_zero)
        },
        &|d, j, ih| {
            let two = d.num(2);
            let x = d.pow(two, j);
            let k = ones(d);
            let k_top = with_top(d, &p, k, j);
            let low = sum_subsets(d, &p, j, k);
            let high = sum_subsets(d, &p, j, k_top);
            let joined = add_congr(d, low, x, ih, high, x, ih);

            // `x + x = (0 + x) + x = x * 2 = pow 2 (succ j)`.
            let zx = {
                let z = d.zero();
                d.add(z, x)
            };
            let za = d.lemma(p.zero_add, &[x]);
            let back = d.symm(zx, x, za);
            let widen = d.congr(x, zx, back, &|d, t| d.add(t, x));
            let doubled = d.add(x, x);
            let shifted = d.add(zx, x);
            let two_again = d.num(2);
            let scaled = d.mul(x, two_again);
            let as_mul = d.refl(shifted);
            let sj = d.succ(j);
            let two_more = d.num(2);
            let target = d.pow(two_more, sj);
            let two_pow = d.num(2);
            let pow_step = d.lemma(p.pow_succ, &[two_pow, j]);
            let unfold = d.symm(scaled, target, pow_step);

            let start = d.add(low, high);
            let s1 = d.trans(start, doubled, shifted, joined, widen);
            let s2 = d.trans(start, shifted, scaled, s1, as_mul);
            d.trans(start, scaled, target, s2, unfold)
        },
        n,
    );

    let stmt = motive_at(d, n);
    let ty = d.pi_fv(n_fv, nat, stmt);
    let value = d.lam_fv(n_fv, nat, body);
    d.declare_theorem(p.subsets_sum_subsets_card, ty, value)
}

/// `Nat.Subsets.sumSel_const : ∀ c n,
/// sumSel (succ n) (fun _ => c) true = sumSel (succ n) (fun _ => c) false`.
///
/// THE ALTERNATING SUM OVER A NON-EMPTY GROUND SET VANISHES — in `Nat`'s graded
/// form, the even and odd halves are equal. It is `add_comm` and nothing else:
/// the split law sends `even (succ n)` to `even n + odd n` and `odd (succ n)`
/// to `odd n + even n`, and a constant summand is unchanged by `insertAt`. This
/// is the identity Möbius inversion turns on (`∑_{d ∣ n} μ(d) = [n = 1]` is
/// this statement at the prime factors of a squarefree `n`), which is why the
/// split law was worth making free.
fn declare_sum_sel_const(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let sty = set_ty(d);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let anon = d.anon_name();
    let k = d.kernel().lam(anon, sty, c, BinderInfo::Default);
    let sn = d.succ(n);
    let tv = d.bool_true();
    let fal = d.bool_false();
    let lhs = sum_sel(d, &p, sn, k, tv);
    let rhs = sum_sel(d, &p, sn, k, fal);
    let concl = d.eq(lhs, rhs);

    let even = sum_sel(d, &p, n, k, tv);
    let odd = sum_sel(d, &p, n, k, fal);
    let proof = d.lemma(p.add_comm, &[even, odd]);

    let ty = {
        let with_n = d.pi_fv(n_fv, nat, concl);
        d.pi_fv(c_fv, nat, with_n)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(c_fv, nat, with_n)
    };
    d.declare_theorem(p.subsets_sum_sel_const, ty, value)
}

/// Declare the subset-sum primitive.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection, naming the step that
/// failed — one rejected declaration fails the whole shared `build_nat_prelude`
/// and the raw `TypeMismatch` names neither.
pub(super) fn declare_subset_sums_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let steps: [(
        &str,
        fn(&mut NatDev<'_>, &NatPrelude) -> Result<(), KernelError>,
    ); 10] = [
        ("definitions", declare_definitions),
        ("equations", declare_equations),
        ("support", declare_support),
        ("sumSel_congr", declare_sum_sel_congr),
        ("sumSel_add", declare_sum_sel_add),
        ("sumSel_mul_right", declare_sum_sel_mul_right),
        ("sumSel_swap", declare_sum_sel_swap),
        ("pos_split", declare_pos_split),
        ("sumSubsets_card", declare_sum_subsets_card),
        ("sumSel_const", declare_sum_sel_const),
    ];
    for (name, step) in steps {
        if let Err(e) = step(d, p) {
            let rendered = d.explain(&e);
            eprintln!("subset_sums: step `{name}` REJECTED: {rendered}");
            return Err(e);
        }
    }
    Ok(())
}
