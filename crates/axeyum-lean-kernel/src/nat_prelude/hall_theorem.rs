//! Hall's marriage theorem — the fixed-bound inclusion decision (ADR-1644).
//!
//! # What this file is for
//!
//! `hall_sufficiency.rs` (ADR-1630) landed the base cases of the sufficiency
//! induction. The inductive step has to DECIDE a statement about every proper
//! nonempty subset `t ⊆ s` — "is some `t` critical?" — and the only decision
//! procedure in this kernel is `Nat.Finset.anySubset` with its two reflection
//! lemmas [`finset_exists_subset_of_search`](super::NatPrelude::finset_exists_subset_of_search)
//! and [`finset_forall_subset_of_search`](super::NatPrelude::finset_forall_subset_of_search).
//!
//! `forallSubset_of_search` carries a congruence premise:
//!
//! ```text
//! (∀ u v, (∀ i, memB u i = memB v i) → P u = P v)
//! ```
//!
//! and it is that premise, not the mathematics, that fixes the shape of the
//! inclusion test. `Nat.Finset.subsetB s t` loops to `bound s`, so `subsetB t s`
//! — the natural spelling of `t ⊆ s` — loops to `bound t`, which CHANGES with
//! the argument. Two sets with the same members and different stored bounds
//! then get different loop lengths, and the congruence premise is unprovable
//! for the predicate that mentions it. So the test has to be spelled with the
//! loop bound taken from the FIXED set:
//!
//! ```text
//! Nat.Finset.subsetFixed s t := allBelow (fun i => if memB t i then memB s i
//!                                                  else true) (bound s)
//! ```
//!
//! and its congruence in `t` then reduces to `allBelow`'s congruence in its
//! predicate — which nothing in the tree had. That missing lemma is
//! [`declare_all_below_congr`], and it is the one the previous lane sized as
//! all that stood between here and the split.
//!
//! # The shelf
//!
//! ```text
//! Nat.Finset.allBelow_congr    : ∀ f g n, (∀ i, f i = g i) →
//!                                allBelow f n = allBelow g n
//! Nat.Finset.subsetFixed       : Nat.Finset → Nat.Finset → Bool
//! Nat.Finset.subsetFixed_of_mem: ∀ s t, (∀ i, memB t i = true → memB s i = true)
//!                                → subsetFixed s t = true
//! Nat.Finset.mem_of_subsetFixed: ∀ s t i, subsetFixed s t = true →
//!                                i < bound s → memB t i = true →
//!                                memB s i = true
//! Nat.Finset.subsetFixed_congr : ∀ s t t', (∀ i, memB t i = memB t' i) →
//!                                subsetFixed s t = subsetFixed s t'
//! ```
//!
//! # Two notes on the spelling
//!
//! **The guard is `if memB t i then memB s i else true`, not
//! `notB (memB t i) || memB s i`.** The two are definitionally the same Boolean
//! function, and the `if` form is the one `Nat.Finset.subsetB` already uses, so
//! the two reflection lemmas here are line-for-line the ones `subsetB` carries
//! and no new `orB`/`notB` law is needed.
//!
//! **`mem_of_subsetFixed` needs `i < bound s` and `subsetFixed_of_mem` does
//! not.** That asymmetry is `allBelow`'s, not this predicate's: a loop that
//! ran to `bound s` answers only indices below `bound s`, while a hypothesis
//! that holds at every index in particular holds at those. It is not a defect —
//! at an index at or above `bound s`, `memB s i` is `false` by
//! `memB_of_bound_le`, so the missing direction is genuinely false for a `t`
//! wider than `s`, and every caller here supplies the bound.

#![allow(clippy::many_single_char_names)]

use super::NatPrelude;
use super::graph::bool_congr;
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps, bool_true_or_false};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

// ---------------------------------------------------------------------------
// Term builders (a private copy, per this prelude's per-file convention).
// ---------------------------------------------------------------------------

/// The carrier constant `Nat.Finset`.
fn finset_ty(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    d.kernel().const_(p.finset, vec![])
}

/// `Nat → Bool`, the type `allBelow` loops over.
fn pred_ty(d: &mut NatDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    d.arrow(nat, bool_ty)
}

/// `Nat.Finset.memB s i`.
fn fs_mem(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, i: ExprId) -> ExprId {
    d.const_app(p.finset_mem_b, &[s, i])
}

/// `Eq Bool (Nat.Finset.memB s i) Bool.true`.
fn mem_true(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, i: ExprId) -> ExprId {
    let m = fs_mem(d, p, s, i);
    let t = d.bool_true();
    d.bool_eq(m, t)
}

/// `Nat.Finset.bound s`.
fn fs_bound(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId) -> ExprId {
    d.const_app(p.finset_bound, &[s])
}

/// `Nat.Finset.allBelow f n`.
fn all_below(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.finset_all_below, &[f, n])
}

/// `Bool.rec (fun _ => Bool) on_false on_true condition` — `if condition then
/// on_true else on_false` at `Bool`.
fn bool_select_bool(
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

/// `heq : Eq Bool cond true ⊢ Eq Bool (bool_select_bool cond a b) a`.
fn select_bool_true(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    cond: ExprId,
    a: ExprId,
    b: ExprId,
    heq: ExprId,
) -> ExprId {
    let p = *p;
    let true_val = d.bool_true();
    let back = d.bool_symm(cond, true_val, heq);
    let motive = d.bool_eq_motive(true_val, &|d, value| {
        let sel = bool_select_bool(d, &p, value, a, b);
        d.bool_eq(sel, a)
    });
    let refl_case = d.bool_refl(a);
    d.bool_transport(true_val, motive, refl_case, cond, back)
}

/// `heq : Eq Bool cond false ⊢ Eq Bool (bool_select_bool cond a b) b`.
fn select_bool_false(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    cond: ExprId,
    a: ExprId,
    b: ExprId,
    heq: ExprId,
) -> ExprId {
    let p = *p;
    let false_val = d.bool_false();
    let back = d.bool_symm(cond, false_val, heq);
    let motive = d.bool_eq_motive(false_val, &|d, value| {
        let sel = bool_select_bool(d, &p, value, a, b);
        d.bool_eq(sel, b)
    });
    let refl_case = d.bool_refl(b);
    d.bool_transport(false_val, motive, refl_case, cond, back)
}

/// `Or.rec` into a `Prop` goal.
#[allow(clippy::too_many_arguments)]
fn or_elim(
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

/// The `Bool`-valued implication `subsetFixed s t` loops over, as a function
/// `Nat → Bool`: `fun i => if memB t i then memB s i else true`.
///
/// Written once and reused by all four declarations below, so a change to the
/// guard cannot leave a lemma proving something about a different loop.
fn inclusion_guard(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, t: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let mti = fs_mem(d, &p, t, i);
    let msi = fs_mem(d, &p, s, i);
    let tr = d.bool_true();
    let body = bool_select_bool(d, &p, mti, msi, tr);
    d.lam_fv(i_fv, nat, body)
}

/// `Nat.Finset.subsetFixed s t`.
fn subset_fixed(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, t: ExprId) -> ExprId {
    d.const_app(p.finset_subset_fixed, &[s, t])
}

// ---------------------------------------------------------------------------
// `allBelow` is congruent in its predicate.
// ---------------------------------------------------------------------------

/// `Nat.Finset.allBelow_congr : ∀ f g n, (∀ i, Eq Bool (f i) (g i)) →
/// Eq Bool (allBelow f n) (allBelow g n)`.
///
/// The third law `allBelow` was missing. `allBelow_of_all_true`,
/// `allBelow_true_at` and `allBelow_false_witness` all relate the LOOP to its
/// predicate's values; none relates two loops to each other, and that is the
/// only thing a `Bool`-valued search predicate needs to satisfy
/// `forallSubset_of_search`'s congruence premise.
///
/// An ordinary induction on the bound, and — unlike the three existing laws —
/// with NO case split on the predicate's value. At the successor the goal is
///
/// ```text
/// (if f j then allBelow f j else false) = (if g j then allBelow g j else false)
/// ```
///
/// and two congruences close it: one moves the induction hypothesis through the
/// `then` branch, the other moves `f j = g j` through the scrutinee. Deciding
/// `f j` would work too and costs a `Bool.rec` plus two branches for nothing.
fn declare_all_below_congr(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let pty = pred_ty(d);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);

    // `∀ i, Eq Bool (f i) (g i)` — the pointwise hypothesis, bound OUTSIDE the
    // induction because it does not mention the loop bound.
    let pointwise_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let gi = d.apply(g, &[i]);
        let body = d.bool_eq(fi, gi);
        d.pi_fv(i_fv, nat, body)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let motive_at = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
        let lf = all_below(d, &p, f, n);
        let lg = all_below(d, &p, g, n);
        d.bool_eq(lf, lg)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let body = d.induct(
        &|d, x| motive_at(d, x),
        &|d| {
            // `allBelow f 0` and `allBelow g 0` are BOTH `Bool.true` by iota,
            // so the two sides are definitionally equal and `rfl` closes it.
            let t = d.bool_true();
            d.bool_refl(t)
        },
        &|d, j, ih| {
            let loop_f_j = all_below(d, &p, f, j);
            let loop_g_j = all_below(d, &p, g, j);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let false_ = d.bool_false();

            // `if f j then allBelow f j else false`
            //   = `if f j then allBelow g j else false`   (the loop tail)
            let step_tail = bool_congr(d, loop_f_j, loop_g_j, ih, &|d, x| {
                bool_select_bool(d, &p, fj, x, false_)
            });
            // `if f j then allBelow g j else false`
            //   = `if g j then allBelow g j else false`   (the scrutinee)
            let hfj = d.apply(h, &[j]);
            let step_head = bool_congr(d, fj, gj, hfj, &|d, y| {
                bool_select_bool(d, &p, y, loop_g_j, false_)
            });

            let lhs = bool_select_bool(d, &p, fj, loop_f_j, false_);
            let mid = bool_select_bool(d, &p, fj, loop_g_j, false_);
            let rhs = bool_select_bool(d, &p, gj, loop_g_j, false_);
            d.bool_trans(lhs, mid, rhs, step_tail, step_head)
        },
        n,
    );

    let ty = {
        let concl = motive_at(d, n);
        let with_h = d.arrow(pointwise_ty, concl);
        let with_n = d.pi_fv(n_fv, nat, with_h);
        let with_g = d.pi_fv(g_fv, pty, with_n);
        d.pi_fv(f_fv, pty, with_g)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, pointwise_ty, body);
        let with_n = d.lam_fv(n_fv, nat, with_h);
        let with_g = d.lam_fv(g_fv, pty, with_n);
        d.lam_fv(f_fv, pty, with_g)
    };
    d.declare_theorem(p.finset_all_below_congr, ty, value)
}

// ---------------------------------------------------------------------------
// `subsetFixed` and its two reflection lemmas.
// ---------------------------------------------------------------------------

/// `Nat.Finset.subsetFixed : Nat.Finset → Nat.Finset → Bool
/// := fun s t => allBelow (fun i => if memB t i then memB s i else true)
///                        (bound s)`.
///
/// "`t` is included in `s`, decided over `[0, bound s)`". The loop bound comes
/// from the FIRST argument where `Nat.Finset.subsetB`'s comes from the set on
/// the left of the inclusion; that single difference is what makes it congruent
/// in `t`, which is the whole reason it exists. See this module's header.
fn declare_subset_fixed(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let bool_ty = d.bool_ty();
    let fs = finset_ty(d, &p);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    let guard = inclusion_guard(d, &p, s, t);
    let bs = fs_bound(d, &p, s);
    let body = all_below(d, &p, guard, bs);
    let value = {
        let inner = d.lam_fv(t_fv, fs, body);
        d.lam_fv(s_fv, fs, inner)
    };
    let ty = {
        let inner = d.arrow(fs, bool_ty);
        d.arrow(fs, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.finset_subset_fixed,
        uparams: vec![],
        ty,
        value,
        // `subsetB` is `Regular(4)` over `allBelow`'s `Regular(3)`; this is the
        // same shape, so it takes the same height.
        hint: ReducibilityHint::Regular(4),
    })?;
    Ok(())
}

/// `Nat.Finset.subsetFixed_of_mem : ∀ s t,
/// (∀ i, Eq Bool (memB t i) true → Eq Bool (memB s i) true) →
/// Eq Bool (subsetFixed s t) true`.
///
/// The INTRODUCTION rule. No bound hypothesis: a pointwise implication that
/// holds everywhere in particular holds below `bound s`, which is all
/// `allBelow_of_all_true` asks for.
fn declare_subset_fixed_of_mem(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    // `∀ i, memB t i = true → memB s i = true`.
    let hyp_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let in_t = mem_true(d, &p, t, i);
        let in_s = mem_true(d, &p, s, i);
        let step = d.arrow(in_t, in_s);
        d.pi_fv(i_fv, nat, step)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let guard = inclusion_guard(d, &p, s, t);
    let bs = fs_bound(d, &p, s);

    // `∀ i, Lt i (bound s) → guard i = true`, the premise `allBelow_of_all_true`
    // consumes. The bound hypothesis is accepted and dropped.
    let all_true = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_fv = d.fresh_fvar();
        let hi_ty = d.lt(i, bs);

        let mti = fs_mem(d, &p, t, i);
        let msi = fs_mem(d, &p, s, i);
        let tr = d.bool_true();
        let sel = bool_select_bool(d, &p, mti, msi, tr);
        let goal = d.bool_eq(sel, tr);

        let decided = bool_true_or_false(d, &p, mti);
        let fa = d.bool_false();
        let left_ty = d.bool_eq(mti, tr);
        let right_ty = d.bool_eq(mti, fa);

        // `i ∈ t`: the guard collapses to `memB s i`, which `h` says is `true`.
        let left_case = {
            let hm_fv = d.fresh_fvar();
            let hm = d.kernel().fvar(hm_fv);
            let collapse = select_bool_true(d, &p, mti, msi, tr, hm);
            let in_s = d.apply(h, &[i, hm]);
            let step = d.bool_trans(sel, msi, tr, collapse, in_s);
            d.lam_fv(hm_fv, left_ty, step)
        };
        // `i ∉ t`: the guard IS `true` and nothing is asked of `s`.
        let right_case = {
            let hm_fv = d.fresh_fvar();
            let hm = d.kernel().fvar(hm_fv);
            let collapse = select_bool_false(d, &p, mti, msi, tr, hm);
            d.lam_fv(hm_fv, right_ty, collapse)
        };

        let answered = or_elim(
            d, &p, left_ty, right_ty, goal, left_case, right_case, decided,
        );
        let with_hi = d.lam_fv(hi_fv, hi_ty, answered);
        d.lam_fv(i_fv, nat, with_hi)
    };

    let proof = d.lemma(p.finset_all_below_of_all_true, &[guard, bs, all_true]);

    let ty = {
        let decided = subset_fixed(d, &p, s, t);
        let tr = d.bool_true();
        let concl = d.bool_eq(decided, tr);
        let with_h = d.arrow(hyp_ty, concl);
        let with_t = d.pi_fv(t_fv, fs, with_h);
        d.pi_fv(s_fv, fs, with_t)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, proof);
        let with_t = d.lam_fv(t_fv, fs, with_h);
        d.lam_fv(s_fv, fs, with_t)
    };
    d.declare_theorem(p.finset_subset_fixed_of_mem, ty, value)
}

/// `Nat.Finset.mem_of_subsetFixed : ∀ s t i,
/// Eq Bool (subsetFixed s t) true → Lt i (bound s) →
/// Eq Bool (memB t i) true → Eq Bool (memB s i) true`.
///
/// The ELIMINATION rule, and where the loop bound is paid for: `allBelow_true_at`
/// answers only indices below `bound s`, so `Lt i (bound s)` is a genuine
/// hypothesis rather than bookkeeping. It is not a weakness of the statement —
/// above `bound s` the conclusion is false whenever `t` is wider than `s`,
/// because `memB s i` is then `false` by `memB_of_bound_le`.
fn declare_mem_of_subset_fixed(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);

    let guard = inclusion_guard(d, &p, s, t);
    let bs = fs_bound(d, &p, s);

    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let h_ty = {
        let decided = subset_fixed(d, &p, s, t);
        let tr = d.bool_true();
        d.bool_eq(decided, tr)
    };
    let hlt_fv = d.fresh_fvar();
    let hlt = d.kernel().fvar(hlt_fv);
    let hlt_ty = d.lt(i, bs);
    let hm_fv = d.fresh_fvar();
    let hm = d.kernel().fvar(hm_fv);
    let hm_ty = mem_true(d, &p, t, i);

    // The loop's verdict at this index. `h`'s type is stated at `subsetFixed`,
    // which the kernel unfolds to the `allBelow` this lemma names.
    let answered = d.lemma(p.finset_all_below_true_at, &[guard, bs, h, i, hlt]);

    let mti = fs_mem(d, &p, t, i);
    let msi = fs_mem(d, &p, s, i);
    let tr = d.bool_true();
    let sel = bool_select_bool(d, &p, mti, msi, tr);
    let collapse = select_bool_true(d, &p, mti, msi, tr, hm);
    let back = d.bool_symm(sel, msi, collapse);
    let proof = d.bool_trans(msi, sel, tr, back, answered);

    let ty = {
        let concl = mem_true(d, &p, s, i);
        let with_hm = d.arrow(hm_ty, concl);
        let with_hlt = d.arrow(hlt_ty, with_hm);
        let with_h = d.arrow(h_ty, with_hlt);
        let with_i = d.pi_fv(i_fv, nat, with_h);
        let with_t = d.pi_fv(t_fv, fs, with_i);
        d.pi_fv(s_fv, fs, with_t)
    };
    let value = {
        let with_hm = d.lam_fv(hm_fv, hm_ty, proof);
        let with_hlt = d.lam_fv(hlt_fv, hlt_ty, with_hm);
        let with_h = d.lam_fv(h_fv, h_ty, with_hlt);
        let with_i = d.lam_fv(i_fv, nat, with_h);
        let with_t = d.lam_fv(t_fv, fs, with_i);
        d.lam_fv(s_fv, fs, with_t)
    };
    d.declare_theorem(p.finset_mem_of_subset_fixed, ty, value)
}

/// `Nat.Finset.subsetFixed_congr : ∀ s t t',
/// (∀ i, Eq Bool (memB t i) (memB t' i)) →
/// Eq Bool (subsetFixed s t) (subsetFixed s t')`.
///
/// The payoff. This is `forallSubset_of_search`'s congruence premise for every
/// search predicate built from `subsetFixed s ·`, and the reason the loop bound
/// had to come from `s`: both sides loop to the SAME `bound s`, so
/// [`declare_all_below_congr`] applies directly and the two sets' differing
/// stored bounds never enter.
fn declare_subset_fixed_congr(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    let hyp_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let mti = fs_mem(d, &p, t, i);
        let mui = fs_mem(d, &p, u, i);
        let body = d.bool_eq(mti, mui);
        d.pi_fv(i_fv, nat, body)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let guard_t = inclusion_guard(d, &p, s, t);
    let guard_u = inclusion_guard(d, &p, s, u);
    let bs = fs_bound(d, &p, s);

    // `∀ i, guard_t i = guard_u i` — one `bool_congr` through the scrutinee.
    let pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let mti = fs_mem(d, &p, t, i);
        let mui = fs_mem(d, &p, u, i);
        let msi = fs_mem(d, &p, s, i);
        let tr = d.bool_true();
        let hi = d.apply(h, &[i]);
        let body = bool_congr(d, mti, mui, hi, &|d, y| bool_select_bool(d, &p, y, msi, tr));
        d.lam_fv(i_fv, nat, body)
    };

    let proof = d.lemma(p.finset_all_below_congr, &[guard_t, guard_u, bs, pointwise]);

    let ty = {
        let lhs = subset_fixed(d, &p, s, t);
        let rhs = subset_fixed(d, &p, s, u);
        let concl = d.bool_eq(lhs, rhs);
        let with_h = d.arrow(hyp_ty, concl);
        let with_u = d.pi_fv(u_fv, fs, with_h);
        let with_t = d.pi_fv(t_fv, fs, with_u);
        d.pi_fv(s_fv, fs, with_t)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, proof);
        let with_u = d.lam_fv(u_fv, fs, with_h);
        let with_t = d.lam_fv(t_fv, fs, with_u);
        d.lam_fv(s_fv, fs, with_t)
    };
    d.declare_theorem(p.finset_subset_fixed_congr, ty, value)
}

// ---------------------------------------------------------------------------
// The critical-subset split (ADR-1644, deliverable 2).
//
// Everything below is shared vocabulary for the split lemmas.
// ---------------------------------------------------------------------------

/// `Nat → Nat.Finset`, the type of an indexed family.
fn family_ty(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let nat = d.nat_ty();
    let fs = finset_ty(d, p);
    d.arrow(nat, fs)
}

/// `Nat.Finset.card s`.
fn fs_card(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId) -> ExprId {
    d.const_app(p.finset_card, &[s])
}

/// `Nat.Finset.union s t`.
fn fs_union(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, t: ExprId) -> ExprId {
    d.const_app(p.finset_union, &[s, t])
}

/// `Nat.Hall.unionOver nb t`.
fn union_over(d: &mut NatDev<'_>, p: &NatPrelude, nb: ExprId, t: ExprId) -> ExprId {
    d.const_app(p.hall_union_over, &[nb, t])
}

/// `Nat.Hall.HallCondition s nb`.
fn hall_condition(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, nb: ExprId) -> ExprId {
    d.const_app(p.hall_condition, &[s, nb])
}

/// `Eq Bool (Nat.Finset.memB s i) Bool.false`.
fn mem_false(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, i: ExprId) -> ExprId {
    let m = fs_mem(d, p, s, i);
    let fa = d.bool_false();
    d.bool_eq(m, fa)
}

/// `False.rec` into a `Prop` goal.
fn false_elim(d: &mut NatDev<'_>, p: &NatPrelude, goal: ExprId, proof: ExprId) -> ExprId {
    let zero = d.kernel().level_zero();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, false_ty, goal, BinderInfo::Default);
    let rec = d.kernel().const_(p.logic.false_rec, vec![zero]);
    d.apply(rec, &[motive, proof])
}

/// `Exists.{1} Nat pred`.
fn exists_nat(d: &mut NatDev<'_>, p: &NatPrelude, pred: ExprId) -> ExprId {
    let one = d.level_one();
    let nat = d.nat_ty();
    let ex = d.kernel().const_(p.logic.exists_, vec![one]);
    d.apply(ex, &[nat, pred])
}

/// `Exists.rec.{1}` over `Nat` into a `Prop` goal.
fn exists_elim_nat(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pred: ExprId,
    goal: ExprId,
    minor: ExprId,
    proof: ExprId,
) -> ExprId {
    let one = d.level_one();
    let nat = d.nat_ty();
    let ex_ty = exists_nat(d, p, pred);
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, ex_ty, goal, BinderInfo::Default);
    let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
    d.apply(rec, &[nat, pred, motive, minor, proof])
}

/// `fun i => And (memB t i = true) (memB (mb i) v = true)` —
/// `Nat.Hall.memB_unionOver_elim`'s payload at the family `mb`.
fn union_witness_pred(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    mb: ExprId,
    t: ExprId,
    v: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let in_t = mem_true(d, &p, t, i);
    let member = d.apply(mb, &[i]);
    let holds = mem_true(d, &p, member, v);
    let body = d.const_app(p.logic.and, &[in_t, holds]);
    d.lam_fv(i_fv, nat, body)
}

/// `h : Eq Nat a b`, `hle : Le a c  ⊢  Le b c` — rewriting the LEFT side of an
/// order fact along a `Nat` equation.
///
/// `NatOps::le_congr` takes the pre-substitution type and is the wrong shape
/// here; this is the plain `Eq.rec` with the order relation as the motive.
fn le_rewrite_left(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    h: ExprId,
    hle: ExprId,
) -> ExprId {
    let motive = d.eq_motive(a, &|d, x| d.le(x, c));
    d.transport(a, motive, hle, b, h)
}

// ---------------------------------------------------------------------------
// Three facts the split consumes.
// ---------------------------------------------------------------------------

/// `Nat.Finset.card_union_of_disjoint : ∀ s t,
/// (∀ i, Eq Bool (memB s i) true → Eq Bool (memB t i) false) →
/// Eq Nat (card (union s t)) (add (card s) (card t))`.
///
/// **No new counting argument.** `card s` is `countRange (memB s) (bound s)`
/// and `sum s f` is `sumRangeIf (memB s) f (bound s)`; unfolding both,
/// `sum s (fun _ => 1)` and `card s` are the SAME `Nat.rec` term — the
/// accumulator is `ih + (if memB s j then 1 else 0)` on each side — so
/// `Nat.Finset.sum_union_disjoint` at the constant `1` already IS this
/// statement, and the proof is that lemma with its hypothesis translated.
///
/// The translation is the whole content. `sum_union_disjoint` spells
/// disjointness as `setInter (memB s) (memB t) i = false`, and every consumer
/// in the Hall split has it as the implication `i ∈ s → i ∉ t` — that is what
/// `Nat.Finset.memB_sdiff_elim` hands back. `setInter f g i` is
/// `if f i then g i else false`, so the two are one `Bool.rec` apart.
fn declare_card_union_of_disjoint(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    let hyp_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let in_s = mem_true(d, &p, s, i);
        let not_t = mem_false(d, &p, t, i);
        let step = d.arrow(in_s, not_t);
        d.pi_fv(i_fv, nat, step)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    // `∀ i, setInter (memB s) (memB t) i = false`, in the spelling
    // `sum_union_disjoint` asks for.
    let pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let msi = fs_mem(d, &p, s, i);
        let mti = fs_mem(d, &p, t, i);
        let fa = d.bool_false();
        let sel = bool_select_bool(d, &p, msi, mti, fa);
        let goal = d.bool_eq(sel, fa);

        let decided = bool_true_or_false(d, &p, msi);
        let tr = d.bool_true();
        let left_ty = d.bool_eq(msi, tr);
        let right_ty = d.bool_eq(msi, fa);

        // `i ∈ s`: the guard is `memB t i`, which the hypothesis says is
        // `false`.
        let left_case = {
            let hm_fv = d.fresh_fvar();
            let hm = d.kernel().fvar(hm_fv);
            let collapse = select_bool_true(d, &p, msi, mti, fa, hm);
            let vanishes = d.apply(h, &[i, hm]);
            let step = d.bool_trans(sel, mti, fa, collapse, vanishes);
            d.lam_fv(hm_fv, left_ty, step)
        };
        // `i ∉ s`: the guard IS `false` and the hypothesis is not needed.
        let right_case = {
            let hm_fv = d.fresh_fvar();
            let hm = d.kernel().fvar(hm_fv);
            let collapse = select_bool_false(d, &p, msi, mti, fa, hm);
            d.lam_fv(hm_fv, right_ty, collapse)
        };

        let answered = or_elim(
            d, &p, left_ty, right_ty, goal, left_case, right_case, decided,
        );
        d.lam_fv(i_fv, nat, answered)
    };

    // `fun _ => 1`, the weight that turns a sum into a count.
    let ones = {
        let anon = d.anon_name();
        let one = d.num(1);
        d.kernel().lam(anon, nat, one, BinderInfo::Default)
    };
    let proof = d.lemma(p.finset_sum_union_disjoint, &[s, t, ones, pointwise]);

    let ty = {
        let u = fs_union(d, &p, s, t);
        let lhs = fs_card(d, &p, u);
        let cs = fs_card(d, &p, s);
        let ct = fs_card(d, &p, t);
        let rhs = d.add(cs, ct);
        let concl = d.eq(lhs, rhs);
        let with_h = d.arrow(hyp_ty, concl);
        let with_t = d.pi_fv(t_fv, fs, with_h);
        d.pi_fv(s_fv, fs, with_t)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, proof);
        let with_t = d.lam_fv(t_fv, fs, with_h);
        d.lam_fv(s_fv, fs, with_t)
    };
    d.declare_theorem(p.finset_card_union_of_disjoint, ty, value)
}

/// `Nat.Hall.hallCondition_subset : ∀ s t nb, HallCondition s nb →
/// (∀ i, Eq Bool (memB t i) true → Eq Bool (memB s i) true) →
/// HallCondition t nb`.
///
/// Hall's condition restricts to any subset, and it is pure composition:
/// `HallCondition` quantifies over the subsets of its index set, so a subset of
/// `t` is a subset of `s` and the original condition answers it. Landed as a
/// named lemma because the inductive step needs it in BOTH branches and both
/// spellings of the inclusion (`t ⊆ s` given, `w ⊆ t` demanded) are pointwise,
/// so composing them by hand at each site is where an argument-order slip would
/// go unnoticed.
fn declare_hall_condition_subset(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);
    let fam = family_ty(d, &p);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let nb_fv = d.fresh_fvar();
    let nb = d.kernel().fvar(nb_fv);

    let hc_s = hall_condition(d, &p, s, nb);
    let hh_fv = d.fresh_fvar();
    let hh = d.kernel().fvar(hh_fv);

    let incl_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let in_t = mem_true(d, &p, t, i);
        let in_s = mem_true(d, &p, s, i);
        let step = d.arrow(in_t, in_s);
        d.pi_fv(i_fv, nat, step)
    };
    let hts_fv = d.fresh_fvar();
    let hts = d.kernel().fvar(hts_fv);

    // `fun w hw => hh w (fun i hi => hts i (hw i hi))`.
    let proof = {
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let hw_ty = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let in_w = mem_true(d, &p, w, i);
            let in_t = mem_true(d, &p, t, i);
            let step = d.arrow(in_w, in_t);
            d.pi_fv(i_fv, nat, step)
        };
        let hw_fv = d.fresh_fvar();
        let hw = d.kernel().fvar(hw_fv);

        let composed = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hi_fv = d.fresh_fvar();
            let hi_ty = mem_true(d, &p, w, i);
            let hi = d.kernel().fvar(hi_fv);
            let in_t = d.apply(hw, &[i, hi]);
            let in_s = d.apply(hts, &[i, in_t]);
            let with_hi = d.lam_fv(hi_fv, hi_ty, in_s);
            d.lam_fv(i_fv, nat, with_hi)
        };
        let answered = d.apply(hh, &[w, composed]);
        let with_hw = d.lam_fv(hw_fv, hw_ty, answered);
        d.lam_fv(w_fv, fs, with_hw)
    };

    let ty = {
        let concl = hall_condition(d, &p, t, nb);
        let with_hts = d.arrow(incl_ty, concl);
        let with_hh = d.arrow(hc_s, with_hts);
        let with_nb = d.pi_fv(nb_fv, fam, with_hh);
        let with_t = d.pi_fv(t_fv, fs, with_nb);
        d.pi_fv(s_fv, fs, with_t)
    };
    let value = {
        let with_hts = d.lam_fv(hts_fv, incl_ty, proof);
        let with_hh = d.lam_fv(hh_fv, hc_s, with_hts);
        let with_nb = d.lam_fv(nb_fv, fam, with_hh);
        let with_t = d.lam_fv(t_fv, fs, with_nb);
        d.lam_fv(s_fv, fs, with_t)
    };
    d.declare_theorem(p.hall_condition_subset, ty, value)
}

/// `Nat.Hall.memB_unionOver_union_of_vanishing : ∀ mb w t v,
/// (∀ i, Eq Bool (memB t i) true → Eq Bool (memB (mb i) v) false) →
/// Eq Bool (memB (unionOver mb (union w t)) v) (memB (unionOver mb w) v)`.
///
/// Indices whose family member is EMPTY at `v` may be dropped from a union.
///
/// This is the step the critical branch runs on, and the reason it is stated as
/// its own lemma: in that branch the deleted family is
/// `nb' i := sdiff (nb i) (unionOver nb t)`, which is empty at every `i ∈ t` —
/// everything `nb i` could contribute for such an `i` is exactly what was
/// deleted — so the union over `w ∪ t` and the union over `w` have the same
/// members even though their stored bounds differ.
/// `Nat.Finset.card_congr_of_memB` then makes the two counts equal, which is
/// what the counting chain needs.
///
/// Both directions are needed and neither is `Bool` trivia: the forward one
/// runs `memB_unionOver_elim` and splits the recovered index with
/// `memB_union_elim`, and its `i ∈ t` branch is where the vanishing hypothesis
/// is spent.
fn declare_mem_union_over_union_of_vanishing(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);
    let fam = family_ty(d, &p);

    let mb_fv = d.fresh_fvar();
    let mb = d.kernel().fvar(mb_fv);
    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);

    let hyp_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let in_t = mem_true(d, &p, t, i);
        let member = d.apply(mb, &[i]);
        let vanishes = mem_false(d, &p, member, v);
        let step = d.arrow(in_t, vanishes);
        d.pi_fv(i_fv, nat, step)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let big = fs_union(d, &p, w, t);
    let cover_big = union_over(d, &p, mb, big);
    let cover_w = union_over(d, &p, mb, w);
    let lhs = fs_mem(d, &p, cover_big, v);
    let rhs = fs_mem(d, &p, cover_w, v);
    let goal = d.bool_eq(lhs, rhs);

    let tr = d.bool_true();
    let fa = d.bool_false();

    let decided_rhs = bool_true_or_false(d, &p, rhs);
    let rhs_true_ty = d.bool_eq(rhs, tr);
    let rhs_false_ty = d.bool_eq(rhs, fa);

    // `v` is already covered by `w`: widening the index set keeps it.
    let rhs_true_case = {
        let hb_fv = d.fresh_fvar();
        let hb = d.kernel().fvar(hb_fv);
        let pred = union_witness_pred(d, &p, mb, w, v);
        let found = d.lemma(p.hall_mem_union_over_elim, &[mb, w, v, hb]);
        let minor = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let in_w = mem_true(d, &p, w, i);
            let member = d.apply(mb, &[i]);
            let holds = mem_true(d, &p, member, v);
            let hand_fv = d.fresh_fvar();
            let hand = d.kernel().fvar(hand_fv);
            let hi_w = and_left(d, in_w, holds, hand);
            let hi_mb = and_right(d, in_w, holds, hand);
            let hi_big = d.lemma(p.finset_mem_b_union_left, &[w, t, i, hi_w]);
            let ha = d.lemma(p.hall_mem_union_over, &[mb, big, i, v, hi_big, hi_mb]);
            let back = d.bool_symm(rhs, tr, hb);
            let step = d.bool_trans(lhs, tr, rhs, ha, back);
            let and_ty = d.const_app(p.logic.and, &[in_w, holds]);
            let with_hand = d.lam_fv(hand_fv, and_ty, step);
            d.lam_fv(i_fv, nat, with_hand)
        };
        let answered = exists_elim_nat(d, &p, pred, goal, minor, found);
        d.lam_fv(hb_fv, rhs_true_ty, answered)
    };

    // `v` is not covered by `w`. Then it is not covered by `w ∪ t` either:
    // anything `t` could contribute has been deleted.
    let rhs_false_case = {
        let hb_fv = d.fresh_fvar();
        let hb = d.kernel().fvar(hb_fv);

        let decided_lhs = bool_true_or_false(d, &p, lhs);
        let lhs_true_ty = d.bool_eq(lhs, tr);
        let lhs_false_ty = d.bool_eq(lhs, fa);

        let lhs_true_case = {
            let ha_fv = d.fresh_fvar();
            let ha = d.kernel().fvar(ha_fv);
            let pred = union_witness_pred(d, &p, mb, big, v);
            let found = d.lemma(p.hall_mem_union_over_elim, &[mb, big, v, ha]);
            let minor = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let in_big = mem_true(d, &p, big, i);
                let member = d.apply(mb, &[i]);
                let holds = mem_true(d, &p, member, v);
                let hand_fv = d.fresh_fvar();
                let hand = d.kernel().fvar(hand_fv);
                let hi_big = and_left(d, in_big, holds, hand);
                let hi_mb = and_right(d, in_big, holds, hand);

                let split = d.lemma(p.finset_mem_b_union_elim, &[w, t, i, hi_big]);
                let in_w = mem_true(d, &p, w, i);
                let in_t = mem_true(d, &p, t, i);

                // `i ∈ w`: then `v` IS covered by `w`, contradicting `hb`.
                let from_w = {
                    let hw_fv = d.fresh_fvar();
                    let hw = d.kernel().fvar(hw_fv);
                    let covered = d.lemma(p.hall_mem_union_over, &[mb, w, i, v, hw, hi_mb]);
                    let back = d.bool_symm(rhs, fa, hb);
                    let impossible = d.bool_trans(fa, rhs, tr, back, covered);
                    let absurd = d.false_true_elim(goal, impossible);
                    d.lam_fv(hw_fv, in_w, absurd)
                };
                // `i ∈ t`: then `mb i` is empty at `v`, contradicting `hi_mb`.
                let from_t = {
                    let ht_fv = d.fresh_fvar();
                    let ht = d.kernel().fvar(ht_fv);
                    let vanishes = d.apply(h, &[i, ht]);
                    let member2 = d.apply(mb, &[i]);
                    let mv = fs_mem(d, &p, member2, v);
                    let back = d.bool_symm(mv, fa, vanishes);
                    let impossible = d.bool_trans(fa, mv, tr, back, hi_mb);
                    let absurd = d.false_true_elim(goal, impossible);
                    d.lam_fv(ht_fv, in_t, absurd)
                };

                let answered = or_elim(d, &p, in_w, in_t, goal, from_w, from_t, split);
                let and_ty = d.const_app(p.logic.and, &[in_big, holds]);
                let with_hand = d.lam_fv(hand_fv, and_ty, answered);
                d.lam_fv(i_fv, nat, with_hand)
            };
            let answered = exists_elim_nat(d, &p, pred, goal, minor, found);
            d.lam_fv(ha_fv, lhs_true_ty, answered)
        };
        let lhs_false_case = {
            let ha_fv = d.fresh_fvar();
            let ha = d.kernel().fvar(ha_fv);
            let back = d.bool_symm(rhs, fa, hb);
            let step = d.bool_trans(lhs, fa, rhs, ha, back);
            d.lam_fv(ha_fv, lhs_false_ty, step)
        };
        let answered = or_elim(
            d,
            &p,
            lhs_true_ty,
            lhs_false_ty,
            goal,
            lhs_true_case,
            lhs_false_case,
            decided_lhs,
        );
        d.lam_fv(hb_fv, rhs_false_ty, answered)
    };

    let body = or_elim(
        d,
        &p,
        rhs_true_ty,
        rhs_false_ty,
        goal,
        rhs_true_case,
        rhs_false_case,
        decided_rhs,
    );

    let ty = {
        let with_h = d.arrow(hyp_ty, goal);
        let with_v = d.pi_fv(v_fv, nat, with_h);
        let with_t = d.pi_fv(t_fv, fs, with_v);
        let with_w = d.pi_fv(w_fv, fs, with_t);
        d.pi_fv(mb_fv, fam, with_w)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, body);
        let with_v = d.lam_fv(v_fv, nat, with_h);
        let with_t = d.lam_fv(t_fv, fs, with_v);
        let with_w = d.lam_fv(w_fv, fs, with_t);
        d.lam_fv(mb_fv, fam, with_w)
    };
    d.declare_theorem(p.hall_mem_union_over_union_of_vanishing, ty, value)
}

/// `Nat.Finset.sdiff s t`.
fn fs_sdiff(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, t: ExprId) -> ExprId {
    d.const_app(p.finset_sdiff, &[s, t])
}

/// `fun i => Nat.Finset.sdiff (nb i) u` — the family with `u` deleted from
/// every member, spelled EXACTLY as
/// `Nat.Hall.card_le_card_unionOver_sdiff_add` spells it so the two match
/// without a conversion step.
fn deleted_family(d: &mut NatDev<'_>, p: &NatPrelude, nb: ExprId, u: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let member = d.apply(nb, &[i]);
    let body = fs_sdiff(d, &p, member, u);
    d.lam_fv(i_fv, nat, body)
}

/// `h : Eq Nat a b`, `hp : motive a  ⊢  motive b`, for a `Prop`-valued motive
/// built from one `Nat` hole.
///
/// The general form of [`le_rewrite_left`]; the counting
/// chain below rewrites inside `Le x (add y z)` at both holes, which neither of
/// those two covers.
fn nat_rewrite_prop(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    hp: ExprId,
    motive_at: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let motive = d.eq_motive(a, motive_at);
    d.transport(a, motive, hp, b, h)
}

/// `Nat.Hall.hallCondition_sdiff_of_critical : ∀ s t nb, HallCondition s nb →
/// (∀ i, Eq Bool (memB t i) true → Eq Bool (memB s i) true) →
/// Le (card (unionOver nb t)) (card t) →
/// HallCondition (sdiff s t) (fun i => sdiff (nb i) (unionOver nb t))`.
///
/// **The critical branch of Hall's inductive step.** When a subset `t ⊆ s` is
/// CRITICAL — its neighbourhood is no bigger than itself, which given Hall's
/// condition means exactly as big — the rest of the index set still satisfies
/// Hall's condition once `t`'s neighbourhood is deleted from every member of
/// the family. That is what lets the induction match `t` and `s \ t`
/// separately and glue: nothing the second matching picks can collide with the
/// first, because everything the first could use has been deleted.
///
/// The counting chain, at an arbitrary `w ⊆ s \ t`, writing `u` for
/// `unionOver nb t`, `nb'` for the deleted family and `W` for `w ∪ t`:
///
/// ```text
///   card w + card t
/// = card W                                  disjoint union (w ⊆ s \ t)
/// ≤ card (unionOver nb W)                   Hall's condition at s
/// ≤ card (unionOver nb' W) + card u         the deficiency inequality
/// = card (unionOver nb' w) + card u         nb' VANISHES on t
/// ≤ card (unionOver nb' w) + card t         criticality
/// ```
///
/// and cancelling `card t` on the right leaves the goal. Every line is an
/// existing lemma except the fourth, which is
/// [`declare_mem_union_over_union_of_vanishing`] through
/// `Nat.Finset.card_congr_of_memB` — and that step is where the two unions'
/// differing stored bounds would otherwise stop the chain.
///
/// **Only one direction of criticality is a hypothesis.** `Le (card u)
/// (card t)` is the half that does not follow from Hall's condition; the other
/// half, `Le (card t) (card u)`, is Hall's condition at `t` itself and is never
/// needed here. Taking the weaker hypothesis is what lets the caller decide
/// criticality with a `Le` test rather than an equality test.
fn declare_hall_condition_sdiff_of_critical(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);
    let fam = family_ty(d, &p);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let nb_fv = d.fresh_fvar();
    let nb = d.kernel().fvar(nb_fv);

    let u = union_over(d, &p, nb, t);
    let nb_deleted = deleted_family(d, &p, nb, u);
    let rest = fs_sdiff(d, &p, s, t);

    // The three hypotheses.
    let hc_ty = hall_condition(d, &p, s, nb);
    let hc_fv = d.fresh_fvar();
    let hc = d.kernel().fvar(hc_fv);

    let incl_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let in_t = mem_true(d, &p, t, i);
        let in_s = mem_true(d, &p, s, i);
        let step = d.arrow(in_t, in_s);
        d.pi_fv(i_fv, nat, step)
    };
    let hts_fv = d.fresh_fvar();
    let hts = d.kernel().fvar(hts_fv);

    let crit_ty = {
        let cu = fs_card(d, &p, u);
        let ct = fs_card(d, &p, t);
        d.le(cu, ct)
    };
    let hcrit_fv = d.fresh_fvar();
    let hcrit = d.kernel().fvar(hcrit_fv);

    // `fun w hw => <the chain>`.
    let proof = {
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let hw_ty = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let in_w = mem_true(d, &p, w, i);
            let in_rest = mem_true(d, &p, rest, i);
            let step = d.arrow(in_w, in_rest);
            d.pi_fv(i_fv, nat, step)
        };
        let hw_fv = d.fresh_fvar();
        let hw = d.kernel().fvar(hw_fv);

        let big = fs_union(d, &p, w, t);

        // (1) `w` and `t` are disjoint: `w ⊆ s \ t`.
        let hdisj = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hi_fv = d.fresh_fvar();
            let hi_ty = mem_true(d, &p, w, i);
            let hi = d.kernel().fvar(hi_fv);
            let in_rest = d.apply(hw, &[i, hi]);
            let split = d.lemma(p.finset_mem_b_sdiff_elim, &[s, t, i, in_rest]);
            let in_s = mem_true(d, &p, s, i);
            let not_t = mem_false(d, &p, t, i);
            let step = and_right(d, in_s, not_t, split);
            let with_hi = d.lam_fv(hi_fv, hi_ty, step);
            d.lam_fv(i_fv, nat, with_hi)
        };

        // (2) `card (w ∪ t) = card w + card t`.
        let hcard_big = d.lemma(p.finset_card_union_of_disjoint, &[w, t, hdisj]);

        // (3) `w ∪ t ⊆ s`.
        let hbig_s = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hi_fv = d.fresh_fvar();
            let hi_ty = mem_true(d, &p, big, i);
            let hi = d.kernel().fvar(hi_fv);
            let goal = mem_true(d, &p, s, i);
            let split = d.lemma(p.finset_mem_b_union_elim, &[w, t, i, hi]);
            let in_w = mem_true(d, &p, w, i);
            let in_t = mem_true(d, &p, t, i);
            let from_w = {
                let hj_fv = d.fresh_fvar();
                let hj = d.kernel().fvar(hj_fv);
                let in_rest = d.apply(hw, &[i, hj]);
                let pair = d.lemma(p.finset_mem_b_sdiff_elim, &[s, t, i, in_rest]);
                let in_s = mem_true(d, &p, s, i);
                let not_t = mem_false(d, &p, t, i);
                let step = and_left(d, in_s, not_t, pair);
                d.lam_fv(hj_fv, in_w, step)
            };
            let from_t = {
                let hj_fv = d.fresh_fvar();
                let hj = d.kernel().fvar(hj_fv);
                let step = d.apply(hts, &[i, hj]);
                d.lam_fv(hj_fv, in_t, step)
            };
            let answered = or_elim(d, &p, in_w, in_t, goal, from_w, from_t, split);
            let with_hi = d.lam_fv(hi_fv, hi_ty, answered);
            d.lam_fv(i_fv, nat, with_hi)
        };

        // (4) Hall's condition at `s`, applied to `w ∪ t`.
        let hall_big = d.apply(hc, &[big, hbig_s]);

        // (5) The deficiency inequality across the deleted family.
        let deficiency = d.lemma(p.hall_card_le_card_union_over_sdiff_add, &[nb, u, big]);

        // (6) `nb'` vanishes on `t`, at every value.
        let vanish_at = |d: &mut NatDev<'_>, v: ExprId| -> ExprId {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hit_fv = d.fresh_fvar();
            let hit_ty = mem_true(d, &p, t, i);
            let hit = d.kernel().fvar(hit_fv);

            let member = d.apply(nb, &[i]);
            let deleted = fs_sdiff(d, &p, member, u);
            let goal = mem_false(d, &p, deleted, v);
            let mdv = fs_mem(d, &p, deleted, v);
            let tr = d.bool_true();
            let fa = d.bool_false();

            let decided = bool_true_or_false(d, &p, mdv);
            let is_true = d.bool_eq(mdv, tr);
            let is_false = d.bool_eq(mdv, fa);

            // If `v` survived the deletion it is outside `u` — but `i ∈ t` and
            // `v ∈ nb i` put it inside `u`.
            let true_case = {
                let hx_fv = d.fresh_fvar();
                let hx = d.kernel().fvar(hx_fv);
                let pair = d.lemma(p.finset_mem_b_sdiff_elim, &[member, u, v, hx]);
                let in_nb = mem_true(d, &p, member, v);
                let not_u = mem_false(d, &p, u, v);
                let hnb = and_left(d, in_nb, not_u, pair);
                let hnu = and_right(d, in_nb, not_u, pair);
                let covered = d.lemma(p.hall_mem_union_over, &[nb, t, i, v, hit, hnb]);
                let muv = fs_mem(d, &p, u, v);
                let back = d.bool_symm(muv, fa, hnu);
                let impossible = d.bool_trans(fa, muv, tr, back, covered);
                let absurd = d.false_true_elim(goal, impossible);
                d.lam_fv(hx_fv, is_true, absurd)
            };
            let false_case = {
                let hx_fv = d.fresh_fvar();
                let hx = d.kernel().fvar(hx_fv);
                d.lam_fv(hx_fv, is_false, hx)
            };
            let answered = or_elim(
                d, &p, is_true, is_false, goal, true_case, false_case, decided,
            );
            let with_hit = d.lam_fv(hit_fv, hit_ty, answered);
            d.lam_fv(i_fv, nat, with_hit)
        };

        // (7) The two unions over the deleted family have the same members.
        let same_members = {
            let v_fv = d.fresh_fvar();
            let v = d.kernel().fvar(v_fv);
            let hyp = vanish_at(d, v);
            let step = d.lemma(
                p.hall_mem_union_over_union_of_vanishing,
                &[nb_deleted, w, t, v, hyp],
            );
            d.lam_fv(v_fv, nat, step)
        };
        let cover_big = union_over(d, &p, nb_deleted, big);
        let cover_w = union_over(d, &p, nb_deleted, w);
        let hcard_cover = d.lemma(
            p.finset_card_congr_of_mem_b,
            &[cover_big, cover_w, same_members],
        );

        // (8) The chain.
        let cw = fs_card(d, &p, w);
        let ct = fs_card(d, &p, t);
        let cu = fs_card(d, &p, u);
        let sum_wt = d.add(cw, ct);
        let card_big = fs_card(d, &p, big);
        let c_nb_big = {
            let cover = union_over(d, &p, nb, big);
            fs_card(d, &p, cover)
        };
        let d_big = fs_card(d, &p, cover_big);
        let e_w = fs_card(d, &p, cover_w);

        // `Le (card w + card t) (card (unionOver nb (w ∪ t)))`.
        let step_a = le_rewrite_left(d, card_big, sum_wt, c_nb_big, hcard_big, hall_big);
        // ...through the deficiency inequality.
        let d_plus_u = d.add(d_big, cu);
        let step_c = d.lemma(
            p.le_trans,
            &[sum_wt, c_nb_big, d_plus_u, step_a, deficiency],
        );
        // ...with the union over `w ∪ t` collapsed to the union over `w`.
        let step_d = nat_rewrite_prop(d, d_big, e_w, hcard_cover, step_c, &|d, x| {
            let rhs = d.add(x, cu);
            d.le(sum_wt, rhs)
        });
        // ...and criticality replacing `card u` by `card t`.
        let e_plus_u = d.add(e_w, cu);
        let e_plus_t = d.add(e_w, ct);
        let widen = d.lemma(p.add_le_add_left, &[e_w, cu, ct, hcrit]);
        let step_g = d.lemma(p.le_trans, &[sum_wt, e_plus_u, e_plus_t, step_d, widen]);
        // Cancel `card t` on the right of both sides.
        let step_h = d.lemma(p.le_of_add_le_add_right, &[ct, cw, e_w, step_g]);

        let with_hw = d.lam_fv(hw_fv, hw_ty, step_h);
        d.lam_fv(w_fv, fs, with_hw)
    };

    let ty = {
        let concl = hall_condition(d, &p, rest, nb_deleted);
        let with_crit = d.arrow(crit_ty, concl);
        let with_hts = d.arrow(incl_ty, with_crit);
        let with_hc = d.arrow(hc_ty, with_hts);
        let with_nb = d.pi_fv(nb_fv, fam, with_hc);
        let with_t = d.pi_fv(t_fv, fs, with_nb);
        d.pi_fv(s_fv, fs, with_t)
    };
    let value = {
        let with_crit = d.lam_fv(hcrit_fv, crit_ty, proof);
        let with_hts = d.lam_fv(hts_fv, incl_ty, with_crit);
        let with_hc = d.lam_fv(hc_fv, hc_ty, with_hts);
        let with_nb = d.lam_fv(nb_fv, fam, with_hc);
        let with_t = d.lam_fv(t_fv, fs, with_nb);
        d.lam_fv(s_fv, fs, with_t)
    };
    d.declare_theorem(p.hall_condition_sdiff_of_critical, ty, value)
}

/// `Nat.Finset.singleton a`.
fn fs_singleton(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId) -> ExprId {
    d.const_app(p.finset_singleton, &[a])
}

/// `Nat.Hall.hallCondition_sdiff_singleton_of_strict : ∀ s v nb,
/// (∀ w, (∀ i, Eq Bool (memB w i) true → Eq Bool (memB s i) true) →
///       Lt zero (card w) → Lt (card w) (card (unionOver nb w))) →
/// HallCondition s (fun i => sdiff (nb i) (singleton v))`.
///
/// **The non-critical branch of Hall's inductive step.** When every NONEMPTY
/// subset of `s` has strict slack — which is exactly what "no proper nonempty
/// subset is critical" gives, once Hall's condition supplies the non-strict
/// half — one single value may be deleted from every member of the family and
/// Hall's condition survives. That is what lets the induction commit an
/// arbitrary index to an arbitrary one of its neighbours and recurse on the
/// rest: the commitment removes exactly one value from the pool, and the slack
/// pays for it.
///
/// At a subset `w ⊆ s`, writing `nb'` for the deleted family:
///
/// ```text
///   succ (card w) ≤ card (unionOver nb w)                strict slack
///                 ≤ card (unionOver nb' w) + card {v}    the deficiency inequality
///                 = card (unionOver nb' w) + 1           card_singleton
///                 ≡ succ (card (unionOver nb' w))        add x 1 is succ x by iota
/// ```
///
/// and `le_of_succ_le_succ` strips the successor. The last line is a
/// DEFINITIONAL step, not a lemma: `Nat.add` recurses on its right argument, so
/// `add x 1` is `succ (add x zero)` is `succ x`, and the kernel closes it with
/// no rewriting at all.
///
/// **The empty subset is not covered by the hypothesis and must not be.**
/// `Lt (card w) (card (unionOver nb w))` at `w := empty` would read
/// `0 < card (unionOver nb empty)`, which is false — the union over no indices
/// is empty. So the hypothesis is guarded by `Lt zero (card w)` and the empty
/// case is discharged separately by `Nat.zero_le`, decided with `Nat.lt_or_ge`
/// rather than assumed.
///
/// **Hall's condition at `s` is not a hypothesis.** It would be redundant: the
/// strict hypothesis is stronger wherever it applies, and where it does not
/// apply (`card w = 0`) the conclusion is free.
fn declare_hall_condition_sdiff_singleton_of_strict(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);
    let fam = family_ty(d, &p);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let nb_fv = d.fresh_fvar();
    let nb = d.kernel().fvar(nb_fv);

    let one_set = fs_singleton(d, &p, v);
    let nb_deleted = deleted_family(d, &p, nb, one_set);

    // `∀ w, w ⊆ s → 0 < card w → card w < card (unionOver nb w)`.
    let hyp_ty = {
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let incl = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let in_w = mem_true(d, &p, w, i);
            let in_s = mem_true(d, &p, s, i);
            let step = d.arrow(in_w, in_s);
            d.pi_fv(i_fv, nat, step)
        };
        let cw = fs_card(d, &p, w);
        let zero = d.zero();
        let nonempty = d.lt(zero, cw);
        let cover = union_over(d, &p, nb, w);
        let cc = fs_card(d, &p, cover);
        let slack = d.lt(cw, cc);
        let with_ne = d.arrow(nonempty, slack);
        let with_incl = d.arrow(incl, with_ne);
        d.pi_fv(w_fv, fs, with_incl)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let proof = {
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let hw_ty = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let in_w = mem_true(d, &p, w, i);
            let in_s = mem_true(d, &p, s, i);
            let step = d.arrow(in_w, in_s);
            d.pi_fv(i_fv, nat, step)
        };
        let hw_fv = d.fresh_fvar();
        let hw = d.kernel().fvar(hw_fv);

        let cw = fs_card(d, &p, w);
        let cover_del = union_over(d, &p, nb_deleted, w);
        let e_w = fs_card(d, &p, cover_del);
        let goal = d.le(cw, e_w);

        let zero = d.zero();
        let decided = d.lemma(p.lt_or_ge, &[zero, cw]);
        let pos_ty = d.lt(zero, cw);
        let empty_ty = d.le(cw, zero);

        // `w` is nonempty: spend the slack.
        let pos_case = {
            let hp_fv = d.fresh_fvar();
            let hp = d.kernel().fvar(hp_fv);
            let strict = d.apply(h, &[w, hw, hp]);

            // `card (unionOver nb w) ≤ card (unionOver nb' w) + card {v}`.
            let deficiency = d.lemma(p.hall_card_le_card_union_over_sdiff_add, &[nb, one_set, w]);
            let cover = union_over(d, &p, nb, w);
            let cc = fs_card(d, &p, cover);
            let c_one = fs_card(d, &p, one_set);
            let e_plus_one_set = d.add(e_w, c_one);
            let succ_cw = d.succ(cw);
            // `Lt a b` IS `Le (succ a) b`, so `strict` chains directly.
            let chained = d.lemma(
                p.le_trans,
                &[succ_cw, cc, e_plus_one_set, strict, deficiency],
            );
            // `card {v} = 1`, and `add x 1` IS `succ x` by iota.
            let card_one = d.lemma(p.finset_card_singleton, &[v]);
            let one = d.num(1);
            let stepped = nat_rewrite_prop(d, c_one, one, card_one, chained, &|d, x| {
                let rhs = d.add(e_w, x);
                d.le(succ_cw, rhs)
            });
            let step = d.lemma(p.le_of_succ_le_succ, &[cw, e_w, stepped]);
            d.lam_fv(hp_fv, pos_ty, step)
        };
        // `w` is empty: the conclusion is `Le 0 _` after one transitivity.
        let empty_case = {
            let he_fv = d.fresh_fvar();
            let he = d.kernel().fvar(he_fv);
            let base = d.lemma(p.zero_le, &[e_w]);
            let step = d.lemma(p.le_trans, &[cw, zero, e_w, he, base]);
            d.lam_fv(he_fv, empty_ty, step)
        };

        let answered = or_elim(d, &p, pos_ty, empty_ty, goal, pos_case, empty_case, decided);
        let with_hw = d.lam_fv(hw_fv, hw_ty, answered);
        d.lam_fv(w_fv, fs, with_hw)
    };

    let ty = {
        let concl = hall_condition(d, &p, s, nb_deleted);
        let with_h = d.arrow(hyp_ty, concl);
        let with_nb = d.pi_fv(nb_fv, fam, with_h);
        let with_v = d.pi_fv(v_fv, nat, with_nb);
        d.pi_fv(s_fv, fs, with_v)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, proof);
        let with_nb = d.lam_fv(nb_fv, fam, with_h);
        let with_v = d.lam_fv(v_fv, nat, with_nb);
        d.lam_fv(s_fv, fs, with_v)
    };
    d.declare_theorem(p.hall_condition_sdiff_singleton_of_strict, ty, value)
}

// ---------------------------------------------------------------------------
// Two normalisations the inductive step needs (ADR-1644, deliverable 3
// groundwork).
// ---------------------------------------------------------------------------

/// `Nat.Finset.restrict s n := mk (memB s) n` — the same MEMBERS with the
/// stored bound forced to `n`.
///
/// `Nat.Finset.forallSubset_of_search` concludes only for sets with
/// `Le (bound t) n`, because the enumeration runs over `[0, n)`. A caller's
/// `w ⊆ s` may have a stored bound larger than `bound s` even though every one
/// of its members is below `bound s` — `memB` truncates, so the stored bound is
/// an upper bound on the members and nothing more. This is the normalisation
/// that closes that gap, and it is a `Definition` rather than an appeal to
/// `decode`/`encode`: `Nat.Finset.memB_decode_encode` needs `Le (bound t) n` as
/// a HYPOTHESIS, which is exactly what is missing.
fn declare_restrict(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let ms = d.const_app(p.finset_mem_b, &[s]);
    let body = d.const_app(p.finset_mk, &[ms, n]);
    let value = {
        let inner = d.lam_fv(n_fv, nat, body);
        d.lam_fv(s_fv, fs, inner)
    };
    let ty = {
        let inner = d.arrow(nat, fs);
        d.arrow(fs, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.finset_restrict,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(3),
    })?;
    Ok(())
}

/// `Nat.Finset.bound_restrict : ∀ s n, Eq Nat (bound (restrict s n)) n`.
///
/// `refl`. `Nat.Finset` is a structure and `bound (mk p b)` is `b` by iota, so
/// this holds definitionally — it is stated anyway because it is the fact
/// `forallSubset_of_search`'s `Le (bound t) n` premise consumes, and a caller
/// should not have to know that `restrict` is a `mk` in order to use it.
fn declare_bound_restrict(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let r = d.const_app(p.finset_restrict, &[s, n]);
    let lhs = fs_bound(d, &p, r);
    let concl = d.eq(lhs, n);
    let proof = d.refl(n);

    let ty = {
        let with_n = d.pi_fv(n_fv, nat, concl);
        d.pi_fv(s_fv, fs, with_n)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(s_fv, fs, with_n)
    };
    d.declare_theorem(p.finset_bound_restrict, ty, value)
}

/// `Nat.Finset.memB_restrict : ∀ s n,
/// (∀ j, Eq Bool (memB s j) true → Lt j n) →
/// ∀ i, Eq Bool (memB (restrict s n) i) (memB s i)`.
///
/// Restricting changes no members, PROVIDED every member was already below the
/// new bound. Both branches are one existing lemma:
///
/// - below `n`, `memB_of_lt` reads the restricted set's membership off its
///   stored predicate, which IS `memB s` by iota, so the two sides are
///   definitionally equal and nothing is rewritten;
/// - at or above `n`, `memB_of_bound_le` makes the left side `false`, and the
///   hypothesis makes the right side `false` too — a member at `i` would give
///   `Lt i n` against `Le n i`, which `lt_of_lt_of_le` turns into `Lt i i` and
///   `lt_irrefl` refutes.
fn declare_mem_b_restrict(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let hyp_ty = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let in_s = mem_true(d, &p, s, j);
        let below = d.lt(j, n);
        let step = d.arrow(in_s, below);
        d.pi_fv(j_fv, nat, step)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let r = d.const_app(p.finset_restrict, &[s, n]);

    let body = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lhs = fs_mem(d, &p, r, i);
        let rhs = fs_mem(d, &p, s, i);
        let goal = d.bool_eq(lhs, rhs);

        let decided = d.lemma(p.lt_or_ge, &[i, n]);
        let below_ty = d.lt(i, n);
        let above_ty = d.le(n, i);

        // Below the new bound: `memB_of_lt` unfolds to the stored predicate,
        // which is `memB s` by iota.
        let below_case = {
            let hb_fv = d.fresh_fvar();
            let hb = d.kernel().fvar(hb_fv);
            let step = d.lemma(p.finset_mem_b_of_lt, &[r, i, hb]);
            d.lam_fv(hb_fv, below_ty, step)
        };
        // At or above: both sides are `false`.
        let above_case = {
            let ha_fv = d.fresh_fvar();
            let ha = d.kernel().fvar(ha_fv);
            let fa = d.bool_false();
            let vanish_l = d.lemma(p.finset_mem_b_of_bound_le, &[r, i, ha]);

            let vanish_r = {
                let inner_goal = d.bool_eq(rhs, fa);
                let tr = d.bool_true();
                let dec2 = bool_true_or_false(d, &p, rhs);
                let is_true = d.bool_eq(rhs, tr);
                let is_false = d.bool_eq(rhs, fa);
                let true_case = {
                    let hm_fv = d.fresh_fvar();
                    let hm = d.kernel().fvar(hm_fv);
                    let below = d.apply(h, &[i, hm]);
                    let self_lt = d.lemma(p.lt_of_lt_of_le, &[i, n, i, below, ha]);
                    let irrefl = d.lemma(p.lt_irrefl, &[i]);
                    let boom = d.apply(irrefl, &[self_lt]);
                    let absurd = false_elim(d, &p, inner_goal, boom);
                    d.lam_fv(hm_fv, is_true, absurd)
                };
                let false_case = {
                    let hm_fv = d.fresh_fvar();
                    let hm = d.kernel().fvar(hm_fv);
                    d.lam_fv(hm_fv, is_false, hm)
                };
                or_elim(
                    d, &p, is_true, is_false, inner_goal, true_case, false_case, dec2,
                )
            };

            let back = d.bool_symm(rhs, fa, vanish_r);
            let step = d.bool_trans(lhs, fa, rhs, vanish_l, back);
            d.lam_fv(ha_fv, above_ty, step)
        };

        let answered = or_elim(
            d, &p, below_ty, above_ty, goal, below_case, above_case, decided,
        );
        d.lam_fv(i_fv, nat, answered)
    };

    let ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lhs = fs_mem(d, &p, r, i);
        let rhs = fs_mem(d, &p, s, i);
        let concl = d.bool_eq(lhs, rhs);
        let with_i = d.pi_fv(i_fv, nat, concl);
        let with_h = d.arrow(hyp_ty, with_i);
        let with_n = d.pi_fv(n_fv, nat, with_h);
        d.pi_fv(s_fv, fs, with_n)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, body);
        let with_n = d.lam_fv(n_fv, nat, with_h);
        d.lam_fv(s_fv, fs, with_n)
    };
    d.declare_theorem(p.finset_mem_b_restrict, ty, value)
}

/// `Nat.Finset.memB_union_sdiff_self : ∀ s t,
/// (∀ i, Eq Bool (memB t i) true → Eq Bool (memB s i) true) →
/// ∀ i, Eq Bool (memB (union t (sdiff s t)) i) (memB s i)`.
///
/// Splitting a set at a subset and putting it back changes no members.
///
/// The last step of the critical branch, and the one that could not be skipped:
/// `Nat.Hall.isMatching_union` produces a matching on `union t (sdiff s t)`, and
/// `Nat.Hall.isMatching_congr` moves it to `s` given exactly this pointwise
/// identity. The two sets' stored BOUNDS differ — `union` sums them — so
/// nothing weaker than a pointwise statement will do.
///
/// The hypothesis `t ⊆ s` is genuinely needed: without it a `t` with members
/// outside `s` makes the left side larger.
fn declare_mem_b_union_sdiff_self(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    let hyp_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let in_t = mem_true(d, &p, t, i);
        let in_s = mem_true(d, &p, s, i);
        let step = d.arrow(in_t, in_s);
        d.pi_fv(i_fv, nat, step)
    };
    let hts_fv = d.fresh_fvar();
    let hts = d.kernel().fvar(hts_fv);

    let rest = fs_sdiff(d, &p, s, t);
    let rebuilt = fs_union(d, &p, t, rest);

    let body = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lhs = fs_mem(d, &p, rebuilt, i);
        let rhs = fs_mem(d, &p, s, i);
        let goal = d.bool_eq(lhs, rhs);
        let tr = d.bool_true();
        let fa = d.bool_false();

        let decided = bool_true_or_false(d, &p, rhs);
        let s_true = d.bool_eq(rhs, tr);
        let s_false = d.bool_eq(rhs, fa);

        // `i ∈ s`: it is in `t` or in `s \ t`, and either way in the union.
        let s_true_case = {
            let hs_fv = d.fresh_fvar();
            let hs = d.kernel().fvar(hs_fv);
            let mti = fs_mem(d, &p, t, i);
            let dec2 = bool_true_or_false(d, &p, mti);
            let t_true = d.bool_eq(mti, tr);
            let t_false = d.bool_eq(mti, fa);

            let from_t = {
                let ht_fv = d.fresh_fvar();
                let ht = d.kernel().fvar(ht_fv);
                let inl = d.lemma(p.finset_mem_b_union_left, &[t, rest, i, ht]);
                let back = d.bool_symm(rhs, tr, hs);
                let step = d.bool_trans(lhs, tr, rhs, inl, back);
                d.lam_fv(ht_fv, t_true, step)
            };
            let from_rest = {
                let ht_fv = d.fresh_fvar();
                let ht = d.kernel().fvar(ht_fv);
                let in_rest = d.lemma(p.finset_mem_b_sdiff_intro, &[s, t, i, hs, ht]);
                let inr = d.lemma(p.finset_mem_b_union_right, &[t, rest, i, in_rest]);
                let back = d.bool_symm(rhs, tr, hs);
                let step = d.bool_trans(lhs, tr, rhs, inr, back);
                d.lam_fv(ht_fv, t_false, step)
            };
            let answered = or_elim(d, &p, t_true, t_false, goal, from_t, from_rest, dec2);
            d.lam_fv(hs_fv, s_true, answered)
        };

        // `i ∉ s`: nothing in the union can hold it, because both halves are
        // inside `s`.
        let s_false_case = {
            let hs_fv = d.fresh_fvar();
            let hs = d.kernel().fvar(hs_fv);
            let dec2 = bool_true_or_false(d, &p, lhs);
            let u_true = d.bool_eq(lhs, tr);
            let u_false = d.bool_eq(lhs, fa);

            let u_true_case = {
                let hu_fv = d.fresh_fvar();
                let hu = d.kernel().fvar(hu_fv);
                let split = d.lemma(p.finset_mem_b_union_elim, &[t, rest, i, hu]);
                let in_t = mem_true(d, &p, t, i);
                let in_rest = mem_true(d, &p, rest, i);
                // From `t`: the inclusion hypothesis puts `i` in `s`.
                let via_t = {
                    let hj_fv = d.fresh_fvar();
                    let hj = d.kernel().fvar(hj_fv);
                    let in_s = d.apply(hts, &[i, hj]);
                    let back = d.bool_symm(rhs, fa, hs);
                    let impossible = d.bool_trans(fa, rhs, tr, back, in_s);
                    let absurd = d.false_true_elim(goal, impossible);
                    d.lam_fv(hj_fv, in_t, absurd)
                };
                // From `s \ t`: its left conjunct puts `i` in `s`.
                let via_rest = {
                    let hj_fv = d.fresh_fvar();
                    let hj = d.kernel().fvar(hj_fv);
                    let pair = d.lemma(p.finset_mem_b_sdiff_elim, &[s, t, i, hj]);
                    let left = mem_true(d, &p, s, i);
                    let right = mem_false(d, &p, t, i);
                    let in_s = and_left(d, left, right, pair);
                    let back = d.bool_symm(rhs, fa, hs);
                    let impossible = d.bool_trans(fa, rhs, tr, back, in_s);
                    let absurd = d.false_true_elim(goal, impossible);
                    d.lam_fv(hj_fv, in_rest, absurd)
                };
                let answered = or_elim(d, &p, in_t, in_rest, goal, via_t, via_rest, split);
                d.lam_fv(hu_fv, u_true, answered)
            };
            let u_false_case = {
                let hu_fv = d.fresh_fvar();
                let hu = d.kernel().fvar(hu_fv);
                let back = d.bool_symm(rhs, fa, hs);
                let step = d.bool_trans(lhs, fa, rhs, hu, back);
                d.lam_fv(hu_fv, u_false, step)
            };
            let answered = or_elim(
                d,
                &p,
                u_true,
                u_false,
                goal,
                u_true_case,
                u_false_case,
                dec2,
            );
            d.lam_fv(hs_fv, s_false, answered)
        };

        let answered = or_elim(
            d,
            &p,
            s_true,
            s_false,
            goal,
            s_true_case,
            s_false_case,
            decided,
        );
        d.lam_fv(i_fv, nat, answered)
    };

    let ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lhs = fs_mem(d, &p, rebuilt, i);
        let rhs = fs_mem(d, &p, s, i);
        let concl = d.bool_eq(lhs, rhs);
        let with_i = d.pi_fv(i_fv, nat, concl);
        let with_hts = d.arrow(hyp_ty, with_i);
        let with_t = d.pi_fv(t_fv, fs, with_hts);
        d.pi_fv(s_fv, fs, with_t)
    };
    let value = {
        let with_hts = d.lam_fv(hts_fv, hyp_ty, body);
        let with_t = d.lam_fv(t_fv, fs, with_hts);
        d.lam_fv(s_fv, fs, with_t)
    };
    d.declare_theorem(p.finset_mem_b_union_sdiff_self, ty, value)
}

// ---------------------------------------------------------------------------
// Entry point.
// ---------------------------------------------------------------------------

/// Declare the fixed-bound inclusion decision (ADR-1644).
pub(super) fn declare_hall_theorem_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_all_below_congr(d, p)?;
    declare_subset_fixed(d, p)?;
    declare_subset_fixed_of_mem(d, p)?;
    declare_mem_of_subset_fixed(d, p)?;
    declare_subset_fixed_congr(d, p)?;
    declare_card_union_of_disjoint(d, p)?;
    declare_hall_condition_subset(d, p)?;
    declare_mem_union_over_union_of_vanishing(d, p)?;
    declare_hall_condition_sdiff_of_critical(d, p)?;
    declare_hall_condition_sdiff_singleton_of_strict(d, p)?;
    declare_restrict(d, p)?;
    declare_bound_restrict(d, p)?;
    declare_mem_b_restrict(d, p)?;
    declare_mem_b_union_sdiff_self(d, p)?;
    Ok(())
}
