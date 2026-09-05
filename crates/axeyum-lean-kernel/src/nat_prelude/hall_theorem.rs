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
    Ok(())
}
