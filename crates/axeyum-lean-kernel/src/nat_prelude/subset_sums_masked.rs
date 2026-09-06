//! Subset sums restricted to a MASK — the enumeration shape the divisor
//! transfer needs (roadmap W2-18, ADR-1671).
//!
//! # The counting mismatch this exists to fix
//!
//! `Nat.Multiset.prodSel` selects by VALUE over `[0, bound m)` (ADR-1658), and
//! `Nat.Subsets.sumSubsets k` enumerates **all** `2^k` predicates on `[0, k)`
//! (ADR-1624). For a squarefree `n` with `m := factorization n` the two counts
//! do not match: `n` has `2^(number of distinct primes)` divisors while
//! `sumSubsets (bound m)` visits `2^(bound m)` predicates, and the gap is
//! exactly the values below the bound that are NOT in `m`'s support. A
//! selection that turns one of those on names the same divisor as the selection
//! that leaves it off, because `q ^ count m q = q ^ 0 = 1` there. So a transfer
//! onto `sumSubsets` would count every divisor `2^(bound m − ω(n))` times.
//!
//! ADR-1658 left the repair as an open choice between two shapes. This module
//! is the first of them:
//!
//! ```text
//! Nat.Subsets.sumSubsetsOn P 0        F = F empty
//! Nat.Subsets.sumSubsetsOn P (succ j) F
//!   = sumSubsetsOn P j F + (if P j then sumSubsetsOn P j (F ∘ insertAt j) else 0)
//!
//! Nat.Subsets.sumSelOn P 0        F b = if b then F empty else 0
//! Nat.Subsets.sumSelOn P (succ j) F b
//!   = sumSelOn P j F b + (if P j then sumSelOn P j (F ∘ insertAt j) (notB b) else 0)
//! ```
//!
//! — the same fold over the width, except that an index outside the mask `P`
//! contributes only the "without it" half. The enumerated predicates are then
//! exactly the subsets of `{i < n : P i}`, so at `P q := 0 < count m q` the
//! fold visits each divisor once. `Nat.Subsets.sumSubsetsOn_card` is that
//! statement in checkable form: the fold's cardinality is `2 ^ countRange P n`,
//! not `2 ^ n`.
//!
//! # Why this and not position enumeration
//!
//! The other shape ADR-1658 named is to enumerate the SUPPORT into `[0, k)` —
//! a `nth`-of-support construction with its own correctness theory, which is
//! the position indexing ADR-1658 declined at the multiset. The masked fold
//! costs two definitions and four `Eq.refl` equations here; position
//! enumeration costs a monotone selector `supportNth m : Nat → Nat`, its
//! injectivity, its surjectivity onto the support, and a `prodSel`-through-the-
//! selector bridge — four theorems before any transfer statement can even be
//! written, and every one of them about an object that does not otherwise
//! exist. It is the more expensive half by a wide margin, and it buys the same
//! thing.
//!
//! The one property the masked fold gives up: the width is still `bound m`, so
//! the fold's RECURSION visits `bound m` levels even though only `ω(n)` of them
//! branch. That is a cost in reduction, never in the statement, and the
//! evaluation tests keep the numerals tiny for exactly that reason.
//!
//! # The vanishing law is the point
//!
//! `Nat.Subsets.sumSelOn_const_of_mem` — a constant summand's even and odd
//! halves are EQUAL as soon as the mask contains one index below the width — is
//! `Σ_{d ∣ n} μ(d) = 0` in this shape once the transfer exists, and it is the
//! reason the mask had to become part of the fold rather than a hypothesis on
//! the summand. Its proof is the same `add_comm` that closes
//! `Nat.Subsets.sumSel_const`, but only in the branch where the top index is IN
//! the mask; the branch where it is not needs the induction hypothesis at a
//! strictly smaller width, which is where the mask witness has to be moved down
//! past the top index. That step is `Lt i (succ j)` plus `i ≠ j` — and `i ≠ j`
//! comes from the mask itself, since `P i = true` and `P j = false` cannot both
//! hold at one index.
//!
//! # House rules observed here
//!
//! Every helper hoists each sub-expression into its own `let` before passing it
//! to a `NatOps` method (`&mut NatDev` cannot be reborrowed twice in one call),
//! as `subset_sums.rs` and `multiset_select.rs` document. Numerals in the tests
//! are tiny: this prelude's numerals are unary `succ` towers.

#![allow(clippy::too_many_lines)]

use super::NatPrelude;
use super::graph::not_b;
use super::ops::{NatDev, NatOps, bool_true_or_false};
use super::steps::absurd;
use super::subset_sums::{add_congr, empty_set, or_elim, set_ty, summand_ty, with_top};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::{BinderInfo, ExprId};
use crate::name::NameId;

/// Delta height for `Nat.Subsets.sumSubsetsOn`, mirroring
/// `Nat.Subsets.sumSubsets` (4): above `empty` (1) and `insertAt` (2).
const SUM_SUBSETS_ON_HEIGHT: u16 = 4;
/// Delta height for `Nat.Subsets.sumSelOn`, mirroring `Nat.Subsets.sumSel` (5).
const SUM_SEL_ON_HEIGHT: u16 = 5;

// ---------------------------------------------------------------------------
// Term builders.
// ---------------------------------------------------------------------------

/// `Nat.Subsets.sumSubsetsOn P n F`.
pub(super) fn sum_subsets_on(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    mask: ExprId,
    n: ExprId,
    f: ExprId,
) -> ExprId {
    d.const_app(p.subsets_sum_subsets_on, &[mask, n, f])
}

/// `Nat.Subsets.sumSelOn P n F b`.
pub(super) fn sum_sel_on(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    mask: ExprId,
    n: ExprId,
    f: ExprId,
    b: ExprId,
) -> ExprId {
    d.const_app(p.subsets_sum_sel_on, &[mask, n, f, b])
}

/// `fun _ => true` — the full mask, at which the masked folds are the
/// unrestricted ones.
fn full_mask(d: &mut NatDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let tv = d.bool_true();
    d.kernel().lam(anon, nat, tv, BinderInfo::Default)
}

/// `Bool.rec` at a `Prop` motive: case analysis on `b`, with the branch proofs
/// built by the two closures. A private copy of `multiset_select.rs`'s helper,
/// per this development's per-file-copy convention.
fn bool_cases(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    b: ExprId,
    motive: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
    at_false: &dyn Fn(&mut NatDev<'_>) -> ExprId,
    at_true: &dyn Fn(&mut NatDev<'_>) -> ExprId,
) -> ExprId {
    let bool_ty = d.bool_ty();
    let motive_lam = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let body = motive(d, x);
        d.lam_fv(x_fv, bool_ty, body)
    };
    let false_case = at_false(d);
    let true_case = at_true(d);
    let level_zero = d.kernel().level_zero();
    let rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
    d.apply(rec, &[motive_lam, false_case, true_case, b])
}

/// `∀ binders, stmt`, proved by `proof`.
fn declare_forall(
    d: &mut NatDev<'_>,
    name: NameId,
    binders: &[(u64, ExprId)],
    stmt: ExprId,
    proof: ExprId,
) -> Result<(), KernelError> {
    let mut ty = stmt;
    let mut value = proof;
    for &(fv, binder_ty) in binders.iter().rev() {
        ty = d.pi_fv(fv, binder_ty, ty);
        value = d.lam_fv(fv, binder_ty, value);
    }
    d.declare_theorem(name, ty, value)
}

// ---------------------------------------------------------------------------
// The two definitions.
// ---------------------------------------------------------------------------

fn declare_definitions(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let sty = set_ty(d);
    let fty = summand_ty(d);
    let anon = d.anon_name();
    let one = d.level_one();

    // sumSubsetsOn : (Nat -> Bool) -> Nat -> ((Nat -> Bool) -> Nat) -> Nat
    {
        let carrier = d.arrow(fty, nat);
        let mask_fv = d.fresh_fvar();
        let mask = d.kernel().fvar(mask_fv);
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
            let high = d.apply(ih, &[shifted]);
            let zero = d.zero();
            let at_m = d.apply(mask, &[m]);
            let right = d.bool_select_nat(at_m, high, zero);
            let body = d.add(left, right);
            let with_f = d.lam_fv(f_fv, fty, body);
            let with_ih = d.lam_fv(ih_fv, carrier, with_f);
            d.lam_fv(m_fv, nat, with_ih)
        };
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let rec = d.kernel().const_(p.rec, vec![one]);
        let applied = d.apply(rec, &[motive, base, step, n]);
        let value = {
            let over_n = d.lam_fv(n_fv, nat, applied);
            d.lam_fv(mask_fv, sty, over_n)
        };
        let ty = {
            let over_n = d.arrow(nat, carrier);
            d.arrow(sty, over_n)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.subsets_sum_subsets_on,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(SUM_SUBSETS_ON_HEIGHT),
        })?;
    }

    // sumSelOn : (Nat -> Bool) -> Nat -> ((Nat -> Bool) -> Nat) -> Bool -> Nat
    {
        let inner = d.arrow(bool_ty, nat);
        let carrier = d.arrow(fty, inner);
        let mask_fv = d.fresh_fvar();
        let mask = d.kernel().fvar(mask_fv);
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
            let high = d.apply(ih, &[shifted, flipped]);
            let zero = d.zero();
            let at_m = d.apply(mask, &[m]);
            let right = d.bool_select_nat(at_m, high, zero);
            let body = d.add(left, right);
            let with_b = d.lam_fv(b_fv, bool_ty, body);
            let with_f = d.lam_fv(f_fv, fty, with_b);
            let with_ih = d.lam_fv(ih_fv, carrier, with_f);
            d.lam_fv(m_fv, nat, with_ih)
        };
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let rec = d.kernel().const_(p.rec, vec![one]);
        let applied = d.apply(rec, &[motive, base, step, n]);
        let value = {
            let over_n = d.lam_fv(n_fv, nat, applied);
            d.lam_fv(mask_fv, sty, over_n)
        };
        let ty = {
            let over_n = d.arrow(nat, carrier);
            d.arrow(sty, over_n)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.subsets_sum_sel_on,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(SUM_SEL_ON_HEIGHT),
        })?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// The four unfolding equations. Every one of them `Eq.refl`.
// ---------------------------------------------------------------------------

fn declare_equations(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let sty = set_ty(d);
    let fty = summand_ty(d);

    // sumSubsetsOn_zero : forall P F, sumSubsetsOn P 0 F = F empty
    {
        let mask_fv = d.fresh_fvar();
        let mask = d.kernel().fvar(mask_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let zero = d.zero();
        let lhs = sum_subsets_on(d, &p, mask, zero, f);
        let e = empty_set(d, &p);
        let rhs = d.apply(f, &[e]);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(lhs);
        declare_forall(
            d,
            p.subsets_sum_subsets_on_zero,
            &[(mask_fv, sty), (f_fv, fty)],
            stmt,
            proof,
        )?;
    }

    // sumSubsetsOn_succ : forall P n F, sumSubsetsOn P (succ n) F =
    //   sumSubsetsOn P n F + (if P n then sumSubsetsOn P n (F . insertAt n) else 0)
    {
        let mask_fv = d.fresh_fvar();
        let mask = d.kernel().fvar(mask_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let sn = d.succ(n);
        let lhs = sum_subsets_on(d, &p, mask, sn, f);
        let low = sum_subsets_on(d, &p, mask, n, f);
        let shifted = with_top(d, &p, f, n);
        let high = sum_subsets_on(d, &p, mask, n, shifted);
        let zero = d.zero();
        let at_n = d.apply(mask, &[n]);
        let guarded = d.bool_select_nat(at_n, high, zero);
        let rhs = d.add(low, guarded);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(rhs);
        declare_forall(
            d,
            p.subsets_sum_subsets_on_succ,
            &[(mask_fv, sty), (n_fv, nat), (f_fv, fty)],
            stmt,
            proof,
        )?;
    }

    // sumSelOn_zero : forall P F b, sumSelOn P 0 F b = if b then F empty else 0
    {
        let mask_fv = d.fresh_fvar();
        let mask = d.kernel().fvar(mask_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let zero = d.zero();
        let lhs = sum_sel_on(d, &p, mask, zero, f, b);
        let e = empty_set(d, &p);
        let at_empty = d.apply(f, &[e]);
        let z2 = d.zero();
        let rhs = d.bool_select_nat(b, at_empty, z2);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(lhs);
        declare_forall(
            d,
            p.subsets_sum_sel_on_zero,
            &[(mask_fv, sty), (f_fv, fty), (b_fv, bool_ty)],
            stmt,
            proof,
        )?;
    }

    // sumSelOn_succ : forall P n F b, sumSelOn P (succ n) F b =
    //   sumSelOn P n F b + (if P n then sumSelOn P n (F . insertAt n) (notB b) else 0)
    {
        let mask_fv = d.fresh_fvar();
        let mask = d.kernel().fvar(mask_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let sn = d.succ(n);
        let lhs = sum_sel_on(d, &p, mask, sn, f, b);
        let low = sum_sel_on(d, &p, mask, n, f, b);
        let shifted = with_top(d, &p, f, n);
        let flipped = not_b(d, &p, b);
        let high = sum_sel_on(d, &p, mask, n, shifted, flipped);
        let zero = d.zero();
        let at_n = d.apply(mask, &[n]);
        let guarded = d.bool_select_nat(at_n, high, zero);
        let rhs = d.add(low, guarded);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(rhs);
        declare_forall(
            d,
            p.subsets_sum_sel_on_succ,
            &[(mask_fv, sty), (n_fv, nat), (f_fv, fty), (b_fv, bool_ty)],
            stmt,
            proof,
        )?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// The full mask recovers the unrestricted folds.
// ---------------------------------------------------------------------------

fn declare_full_mask(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let fty = summand_ty(d);

    // sumSubsetsOn_all : forall n F, sumSubsetsOn (fun _ => true) n F = sumSubsets n F
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let mask = full_mask(d);
        let lhs = sum_subsets_on(d, &p, mask, n, f);
        let rhs = d.const_app(p.subsets_sum_subsets, &[n, f]);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(rhs);
        declare_forall(
            d,
            p.subsets_sum_subsets_on_all,
            &[(n_fv, nat), (f_fv, fty)],
            stmt,
            proof,
        )?;
    }

    // sumSelOn_all : forall n F b, sumSelOn (fun _ => true) n F b = sumSel n F b
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let mask = full_mask(d);
        let lhs = sum_sel_on(d, &p, mask, n, f, b);
        let rhs = d.const_app(p.subsets_sum_sel, &[n, f, b]);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(rhs);
        declare_forall(
            d,
            p.subsets_sum_sel_on_all,
            &[(n_fv, nat), (f_fv, fty), (b_fv, bool_ty)],
            stmt,
            proof,
        )?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// The grading is a partition of the masked fold.
// ---------------------------------------------------------------------------

/// `Nat.Subsets.sumSelOn_add : ∀ P n F,
/// sumSelOn P n F true + sumSelOn P n F false = sumSubsetsOn P n F`.
///
/// The two parities together visit exactly what the ungraded masked fold
/// visits. This is what ties `sumSubsetsOn_card` — which counts the ungraded
/// fold — to the graded one the vanishing law is about, and it is the guard
/// that the graded step really does flip the parity: a step reading
/// `ih F b + ih (F ∘ insertAt j) b` satisfies the split law and fails this.
fn declare_sum_sel_on_add(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let sty = set_ty(d);
    let fty = summand_ty(d);

    let mask_fv = d.fresh_fvar();
    let mask = d.kernel().fvar(mask_fv);

    let motive_at = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let tv = d.bool_true();
        let fal = d.bool_false();
        let even = sum_sel_on(d, &p, mask, n, f, tv);
        let odd = sum_sel_on(d, &p, mask, n, f, fal);
        let lhs = d.add(even, odd);
        let rhs = sum_subsets_on(d, &p, mask, n, f);
        let concl = d.eq(lhs, rhs);
        d.pi_fv(f_fv, fty, concl)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let body = d.induct(
        &|d, x| motive_at(d, x),
        &|d| {
            // `F empty + 0 = F empty`.
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
            let g = with_top(d, &p, f, j);

            let a_t = sum_sel_on(d, &p, mask, j, f, tv);
            let a_f = sum_sel_on(d, &p, mask, j, f, fal);
            let b_t = sum_sel_on(d, &p, mask, j, g, tv);
            let b_f = sum_sel_on(d, &p, mask, j, g, fal);
            let c_f = sum_subsets_on(d, &p, mask, j, f);
            let c_g = sum_subsets_on(d, &p, mask, j, g);

            let ih_f = d.apply(ih, &[f]);
            let ih_g = d.apply(ih, &[g]);

            let at_j = d.apply(mask, &[j]);
            let proof = bool_cases(
                d,
                &p,
                at_j,
                &|d, x| {
                    let z1 = d.zero();
                    let hi_even = d.bool_select_nat(x, b_f, z1);
                    let z2 = d.zero();
                    let hi_odd = d.bool_select_nat(x, b_t, z2);
                    let even = d.add(a_t, hi_even);
                    let odd = d.add(a_f, hi_odd);
                    let lhs = d.add(even, odd);
                    let z3 = d.zero();
                    let hi_all = d.bool_select_nat(x, c_g, z3);
                    let rhs = d.add(c_f, hi_all);
                    d.eq(lhs, rhs)
                },
                // mask off: `(A_t + 0) + (A_f + 0) = C_F + 0`.
                &|d| {
                    let z1 = d.zero();
                    let padded_t = d.add(a_t, z1);
                    let z2 = d.zero();
                    let padded_f = d.add(a_f, z2);
                    let drop_t = d.lemma(p.add_zero, &[a_t]);
                    let drop_f = d.lemma(p.add_zero, &[a_f]);
                    let joined = add_congr(d, padded_t, a_t, drop_t, padded_f, a_f, drop_f);
                    let start = d.add(padded_t, padded_f);
                    let mid = d.add(a_t, a_f);
                    let z3 = d.zero();
                    let stop = d.add(c_f, z3);
                    let restore = {
                        let drop_c = d.lemma(p.add_zero, &[c_f]);
                        d.symm(stop, c_f, drop_c)
                    };
                    let (_, chained) =
                        d.chain(start, &[(mid, joined), (c_f, ih_f), (stop, restore)]);
                    chained
                },
                // mask on: `(A_t + B_f) + (A_f + B_t) = C_F + C_G`.
                &|d| {
                    let start = {
                        let even = d.add(a_t, b_f);
                        let odd = d.add(a_f, b_t);
                        d.add(even, odd)
                    };
                    let regrouped = {
                        let left = d.add(a_t, a_f);
                        let right = d.add(b_f, b_t);
                        d.add(left, right)
                    };
                    let step1 = d.lemma(p.add_add_add_comm, &[a_t, b_f, a_f, b_t]);
                    let after_left = {
                        let right = d.add(b_f, b_t);
                        d.add(c_f, right)
                    };
                    let step2 = {
                        let right = d.add(b_f, b_t);
                        let inner = d.add(a_t, a_f);
                        d.congr(inner, c_f, ih_f, &|d, y| d.add(y, right))
                    };
                    let swapped = {
                        let right = d.add(b_t, b_f);
                        d.add(c_f, right)
                    };
                    let step3 = {
                        let from = d.add(b_f, b_t);
                        let to = d.add(b_t, b_f);
                        let comm = d.lemma(p.add_comm, &[b_f, b_t]);
                        d.congr(from, to, comm, &|d, y| d.add(c_f, y))
                    };
                    let stop = d.add(c_f, c_g);
                    let step4 = {
                        let from = d.add(b_t, b_f);
                        d.congr(from, c_g, ih_g, &|d, y| d.add(c_f, y))
                    };
                    let (_, chained) = d.chain(
                        start,
                        &[
                            (regrouped, step1),
                            (after_left, step2),
                            (swapped, step3),
                            (stop, step4),
                        ],
                    );
                    chained
                },
            );
            d.lam_fv(f_fv, fty, proof)
        },
        n,
    );

    let stmt = motive_at(d, n);
    declare_forall(
        d,
        p.subsets_sum_sel_on_add,
        &[(mask_fv, sty), (n_fv, nat)],
        stmt,
        body,
    )
}

// ---------------------------------------------------------------------------
// The fold visits `2 ^ countRange P n` subsets, not `2 ^ n`.
// ---------------------------------------------------------------------------

/// `Nat.Subsets.sumSubsetsOn_card : ∀ P n,
/// sumSubsetsOn P n (fun _ => 1) = pow 2 (countRange P n)`.
///
/// THE STATEMENT THE MASK EXISTS FOR. `Nat.Subsets.sumSubsets_card` pins the
/// unrestricted fold at `2^n`; this pins the masked one at two-to-the-number-
/// of-masked-indices, which is the count a squarefree `n`'s divisors have. A
/// mutant whose step ignores the mask still satisfies the split law, the
/// grading law and the vanishing law — and answers `2^n` here.
fn declare_sum_subsets_on_card(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let sty = set_ty(d);

    let mask_fv = d.fresh_fvar();
    let mask = d.kernel().fvar(mask_fv);

    let ones = |d: &mut NatDev<'_>| -> ExprId {
        let inner_sty = set_ty(d);
        let anon = d.anon_name();
        let one = d.num(1);
        d.kernel().lam(anon, inner_sty, one, BinderInfo::Default)
    };

    let motive_at = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
        let k = ones(d);
        let lhs = sum_subsets_on(d, &p, mask, n, k);
        let two = d.num(2);
        let counted = d.const_app(p.count_range, &[mask, n]);
        let rhs = d.pow(two, counted);
        d.eq(lhs, rhs)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let body = d.induct(
        &|d, x| motive_at(d, x),
        &|d| {
            // `1 = pow 2 0`; `countRange P 0` reduces to `0`.
            let two = d.num(2);
            let at_zero = d.lemma(p.pow_zero, &[two]);
            let two_again = d.num(2);
            let zero = d.zero();
            let powered = d.pow(two_again, zero);
            let one = d.num(1);
            d.symm(powered, one, at_zero)
        },
        &|d, j, ih| {
            let k = ones(d);
            let g = with_top(d, &p, k, j);
            let low = sum_subsets_on(d, &p, mask, j, k);
            let high = sum_subsets_on(d, &p, mask, j, g);
            let counted = d.const_app(p.count_range, &[mask, j]);
            let two = d.num(2);
            let x = d.pow(two, counted);

            let at_j = d.apply(mask, &[j]);
            bool_cases(
                d,
                &p,
                at_j,
                &|d, v| {
                    let z1 = d.zero();
                    let guarded = d.bool_select_nat(v, high, z1);
                    let lhs = d.add(low, guarded);
                    let one = d.num(1);
                    let z2 = d.zero();
                    let bump = d.bool_select_nat(v, one, z2);
                    let widened = d.add(counted, bump);
                    let two_inner = d.num(2);
                    let rhs = d.pow(two_inner, widened);
                    d.eq(lhs, rhs)
                },
                // mask off: `low + 0 = pow 2 (countRange P j + 0)`.
                &|d| {
                    let zero = d.zero();
                    let padded = d.add(low, zero);
                    let drop = d.lemma(p.add_zero, &[low]);
                    let z2 = d.zero();
                    let widened = d.add(counted, z2);
                    let two_inner = d.num(2);
                    let stop = d.pow(two_inner, widened);
                    let restore = {
                        let drop_count = d.lemma(p.add_zero, &[counted]);
                        let back = d.symm(counted, widened, drop_count);
                        d.congr(counted, widened, back, &|d, y| {
                            let two_more = d.num(2);
                            d.pow(two_more, y)
                        })
                    };
                    let (_, chained) = d.chain(padded, &[(low, drop), (x, ih), (stop, restore)]);
                    chained
                },
                // mask on: `low + high = pow 2 (countRange P j + 1)`, and
                // `high` is `low` at a summand that differs only by an
                // `insertAt` the constant `1` never reads.
                &|d| {
                    let start = d.add(low, high);
                    let doubled = d.add(x, x);
                    // `low = x` and `high ≡ low`, so both halves are `ih`.
                    let joined = add_congr(d, low, x, ih, high, x, ih);
                    // `x + x = (0 + x) + x = x * 2 = pow 2 (succ (countRange P j))`,
                    // the same chain `Nat.Subsets.sumSubsets_card` runs.
                    let zx = {
                        let z = d.zero();
                        d.add(z, x)
                    };
                    let za = d.lemma(p.zero_add, &[x]);
                    let back = d.symm(zx, x, za);
                    let widen = d.congr(x, zx, back, &|d, t| d.add(t, x));
                    let shifted = d.add(zx, x);
                    let two_again = d.num(2);
                    let scaled = d.mul(x, two_again);
                    let as_mul = d.refl(shifted);
                    let bumped = d.succ(counted);
                    let two_more = d.num(2);
                    let target = d.pow(two_more, bumped);
                    let two_pow = d.num(2);
                    let pow_step = d.lemma(p.pow_succ, &[two_pow, counted]);
                    let unfold = d.symm(scaled, target, pow_step);
                    let (_, chained) = d.chain(
                        start,
                        &[
                            (doubled, joined),
                            (shifted, widen),
                            (scaled, as_mul),
                            (target, unfold),
                        ],
                    );
                    chained
                },
            )
        },
        n,
    );

    let stmt = motive_at(d, n);
    declare_forall(
        d,
        p.subsets_sum_subsets_on_card,
        &[(mask_fv, sty), (n_fv, nat)],
        stmt,
        body,
    )
}

// ---------------------------------------------------------------------------
// THE VANISHING LAW.
// ---------------------------------------------------------------------------

/// `Nat.Subsets.sumSelOn_const_of_mem : ∀ c P n i, Lt i n → P i = true →
/// sumSelOn P n (fun _ => c) true = sumSelOn P n (fun _ => c) false`.
///
/// A constant summand's even and odd halves agree as soon as ONE index below
/// the width is in the mask. `Nat.Subsets.sumSel_const` is the special case at
/// the full mask, where the witness is free because the top index always
/// qualifies; here it has to be carried, and the induction is what carries it.
///
/// The two branches are asymmetric on purpose. When the top index `j` IS
/// masked, the split law sends `even (succ j)` to `even j + odd j` and
/// `odd (succ j)` to `odd j + even j`, so `add_comm` closes it and the
/// induction hypothesis is never used. When `j` is NOT masked, both sides lose
/// their high half and the goal becomes the statement at `j` — which needs the
/// witness at a strictly smaller width, i.e. `i ≠ j`. That is exactly what the
/// mask supplies: `P i = true` and `P j = false` cannot both hold at one index.
/// So the case split must be over the EQUATION `P j = false`, not over
/// `Bool.rec` on `P j`, because a `Bool.rec` branch does not hand you the
/// equation it split on and the contradiction is unreachable without it.
fn declare_sum_sel_on_const(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let sty = set_ty(d);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let mask_fv = d.fresh_fvar();
    let mask = d.kernel().fvar(mask_fv);

    let konst = |d: &mut NatDev<'_>| -> ExprId {
        let inner_sty = set_ty(d);
        let anon = d.anon_name();
        d.kernel().lam(anon, inner_sty, c, BinderInfo::Default)
    };

    // `sumSelOn P n K true = sumSelOn P n K false`.
    let vanishes_at = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
        let k = konst(d);
        let tv = d.bool_true();
        let fal = d.bool_false();
        let even = sum_sel_on(d, &p, mask, n, k, tv);
        let odd = sum_sel_on(d, &p, mask, n, k, fal);
        d.eq(even, odd)
    };

    let motive_at = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lt_ty = d.lt(i, n);
        let at_i = d.apply(mask, &[i]);
        let tv = d.bool_true();
        let hit_ty = d.bool_eq(at_i, tv);
        let concl = vanishes_at(d, n);
        let with_hit = d.arrow(hit_ty, concl);
        let with_lt = d.arrow(lt_ty, with_hit);
        d.pi_fv(i_fv, nat, with_lt)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let body = d.induct(
        &|d, x| motive_at(d, x),
        &|d| {
            // `Lt i 0` is impossible.
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let zero = d.zero();
            let lt_ty = d.lt(i, zero);
            let hlt_fv = d.fresh_fvar();
            let hlt = d.kernel().fvar(hlt_fv);
            let at_i = d.apply(mask, &[i]);
            let tv = d.bool_true();
            let hit_ty = d.bool_eq(at_i, tv);
            let hhit_fv = d.fresh_fvar();
            let goal = {
                let z = d.zero();
                vanishes_at(d, z)
            };
            let not_lt = d.lemma(p.not_lt_zero, &[i]);
            let contradiction = d.apply(not_lt, &[hlt]);
            let absurdity = absurd(d, goal, contradiction);
            let with_hit = d.lam_fv(hhit_fv, hit_ty, absurdity);
            let with_lt = d.lam_fv(hlt_fv, lt_ty, with_hit);
            d.lam_fv(i_fv, nat, with_lt)
        },
        &|d, j, ih| {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let sj = d.succ(j);
            let lt_ty = d.lt(i, sj);
            let hlt_fv = d.fresh_fvar();
            let hlt = d.kernel().fvar(hlt_fv);
            let at_i = d.apply(mask, &[i]);
            let tv0 = d.bool_true();
            let hit_ty = d.bool_eq(at_i, tv0);
            let hhit_fv = d.fresh_fvar();
            let hhit = d.kernel().fvar(hhit_fv);

            let k = konst(d);
            let tv = d.bool_true();
            let fal = d.bool_false();
            let a_t = sum_sel_on(d, &p, mask, j, k, tv);
            let a_f = sum_sel_on(d, &p, mask, j, k, fal);
            let g = with_top(d, &p, k, j);
            let b_t = sum_sel_on(d, &p, mask, j, g, tv);
            let b_f = sum_sel_on(d, &p, mask, j, g, fal);
            let at_j = d.apply(mask, &[j]);

            // `even (succ j) = odd (succ j)`, with the mask value abstracted.
            let goal_at = |d: &mut NatDev<'_>, v: ExprId| -> ExprId {
                let z1 = d.zero();
                let hi_even = d.bool_select_nat(v, b_f, z1);
                let z2 = d.zero();
                let hi_odd = d.bool_select_nat(v, b_t, z2);
                let even = d.add(a_t, hi_even);
                let odd = d.add(a_f, hi_odd);
                d.eq(even, odd)
            };
            let goal = goal_at(d, at_j);

            // `P j = true`: `A_t + B_f = A_f + B_t` is `add_comm`, since the
            // shifted summand is the same constant.
            let on_true = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let tv_inner = d.bool_true();
                let is_true = d.bool_eq(at_j, tv_inner);
                let refl_case = d.lemma(p.add_comm, &[a_t, a_f]);
                let tv_more = d.bool_true();
                let motive = d.bool_eq_motive(tv_more, &|d, v| goal_at(d, v));
                let tv_again = d.bool_true();
                let back = d.bool_symm(at_j, tv_again, h);
                let tv_final = d.bool_true();
                let proof = d.bool_transport(tv_final, motive, refl_case, at_j, back);
                d.lam_fv(h_fv, is_true, proof)
            };

            // `P j = false`: both high halves vanish and the goal is the
            // statement at `j`, which needs the witness moved below `j`.
            let on_false = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let fal_inner = d.bool_false();
                let is_false = d.bool_eq(at_j, fal_inner);

                let inner_goal = d.eq(a_t, a_f);
                let le_i_j = d.lemma(p.le_of_lt_succ, &[i, j, hlt]);
                let split = d.lemma(p.lt_or_eq_of_le, &[i, j, le_i_j]);
                let lt_i_j = d.lt(i, j);
                let eq_i_j = d.eq(i, j);
                let below = {
                    let hb_fv = d.fresh_fvar();
                    let hb = d.kernel().fvar(hb_fv);
                    let applied = d.apply(ih, &[i, hb, hhit]);
                    d.lam_fv(hb_fv, lt_i_j, applied)
                };
                let at_top = {
                    let he_fv = d.fresh_fvar();
                    let he = d.kernel().fvar(he_fv);
                    // `P i = true` transported to `P j = true`, against
                    // `P j = false`.
                    let motive = d.eq_motive(i, &|d, x| {
                        let at_x = d.apply(mask, &[x]);
                        let t = d.bool_true();
                        d.bool_eq(at_x, t)
                    });
                    let hit_at_j = d.transport(i, motive, hhit, j, he);
                    let fal_more = d.bool_false();
                    let flipped = d.bool_symm(at_j, fal_more, h);
                    let fal_again = d.bool_false();
                    let tv_again = d.bool_true();
                    let impossible = d.bool_trans(fal_again, at_j, tv_again, flipped, hit_at_j);
                    let elimination = d.false_true_elim(inner_goal, impossible);
                    d.lam_fv(he_fv, eq_i_j, elimination)
                };
                let core = or_elim(d, &p, lt_i_j, eq_i_j, inner_goal, below, at_top, split);

                // `A_t + 0 = A_t = A_f = A_f + 0`.
                let refl_case = {
                    let z1 = d.zero();
                    let padded_t = d.add(a_t, z1);
                    let z2 = d.zero();
                    let padded_f = d.add(a_f, z2);
                    let drop_t = d.lemma(p.add_zero, &[a_t]);
                    let drop_f = d.lemma(p.add_zero, &[a_f]);
                    let restore_f = d.symm(padded_f, a_f, drop_f);
                    let (_, chained) = d.chain(
                        padded_t,
                        &[(a_t, drop_t), (a_f, core), (padded_f, restore_f)],
                    );
                    chained
                };
                let fal_more = d.bool_false();
                let motive = d.bool_eq_motive(fal_more, &|d, v| goal_at(d, v));
                let fal_again = d.bool_false();
                let back = d.bool_symm(at_j, fal_again, h);
                let fal_final = d.bool_false();
                let proof = d.bool_transport(fal_final, motive, refl_case, at_j, back);
                d.lam_fv(h_fv, is_false, proof)
            };

            let decided = bool_true_or_false(d, &p, at_j);
            let is_true = {
                let t = d.bool_true();
                d.bool_eq(at_j, t)
            };
            let is_false = {
                let f = d.bool_false();
                d.bool_eq(at_j, f)
            };
            let proof = or_elim(d, &p, is_true, is_false, goal, on_true, on_false, decided);
            let with_hit = d.lam_fv(hhit_fv, hit_ty, proof);
            let with_lt = d.lam_fv(hlt_fv, lt_ty, with_hit);
            d.lam_fv(i_fv, nat, with_lt)
        },
        n,
    );

    let stmt = motive_at(d, n);
    declare_forall(
        d,
        p.subsets_sum_sel_on_const,
        &[(c_fv, nat), (mask_fv, sty), (n_fv, nat)],
        stmt,
        body,
    )
}

/// Declare the masked subset-sum family.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection, naming the step that
/// failed — one rejected declaration fails the whole shared `build_nat_prelude`
/// and the raw `TypeMismatch` names neither.
pub(super) fn declare_subset_sums_masked_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    type Step = fn(&mut NatDev<'_>, &NatPrelude) -> Result<(), KernelError>;
    let steps: [(&str, Step); 6] = [
        ("definitions", declare_definitions),
        ("equations", declare_equations),
        ("full mask", declare_full_mask),
        ("sumSelOn_add", declare_sum_sel_on_add),
        ("sumSubsetsOn_card", declare_sum_subsets_on_card),
        ("sumSelOn_const_of_mem", declare_sum_sel_on_const),
    ];
    for (label, step) in steps {
        if let Err(e) = step(d, p) {
            let rendered = d.explain(&e);
            eprintln!("subset_sums_masked: step `{label}` was rejected:\n  {rendered}");
            return Err(e);
        }
    }
    Ok(())
}
