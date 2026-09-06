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
use super::ops::{NatDev, NatOps};
use super::subset_sums::{empty_set, set_ty, summand_ty, with_top};
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
#[allow(dead_code)]
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
    let steps: [(&str, Step); 3] = [
        ("definitions", declare_definitions),
        ("equations", declare_equations),
        ("full mask", declare_full_mask),
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
