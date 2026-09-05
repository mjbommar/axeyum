//! `Nat.Hall` — the marriage problem over `Nat.Finset`, and the direction that
//! `Nat.Finset.card_le_of_injOn` already proves (ADR-1608).
//!
//! # What is here
//!
//! A *system of distinct representatives* for a family `nb : Nat → Nat.Finset`
//! indexed by a finite set `s` is an injective `f` with `f i ∈ nb i` for every
//! `i ∈ s`. Hall's marriage theorem says one exists **iff** every subfamily
//! covers at least its own size.
//!
//! ```text
//! Nat.Hall.anyBelow f n     := notB (allBelow (fun i => notB (f i)) n)
//! Nat.Hall.unionBound nb n  := sumRange (fun i => Nat.Finset.bound (nb i)) n
//! Nat.Hall.unionOver nb t   := Nat.Finset.mk
//!                                (fun v => anyBelow (fun i => memB t i && memB (nb i) v)
//!                                                   (bound t))
//!                                (unionBound nb (bound t))
//! Nat.Hall.IsMatching s nb f    := (∀ i ∈ s, f i ∈ nb i) ∧ (f injective on s)
//! Nat.Hall.HallCondition s nb   := ∀ t, (∀ i, i ∈ t → i ∈ s) →
//!                                       card t ≤ card (unionOver nb t)
//! ```
//!
//! and the **necessity** direction,
//! `Nat.Hall.hallCondition_of_isMatching`, is proved: a matching restricted to
//! any subfamily is an injection into that subfamily's union, so
//! `Nat.Finset.card_le_of_injOn` (ADR-1593) gives the count directly. That is
//! the half the combinatorics reviewer calls "the standard test of whether a
//! finite-set library is usable", and it needed no new counting machinery at
//! all — only the two carriers.
//!
//! # Three design choices
//!
//! **`unionOver` computes its own bound.** `Nat.Finset` needs a bound at `mk`,
//! and the union of a family has no bound in sight, so `unionBound` takes the
//! `Nat.sumRange` of the members' bounds — the same "sum, not max" choice
//! `Nat.Finset.union` makes (ADR-1577), and for the same reason: the lemma that
//! makes it usable, `Nat.le_sumRange_of_lt`, is stated at `sumRange` and
//! applies literally, with no case analysis on which member's bound is largest.
//!
//! **Inclusion is spelled POINTWISE, not through `Nat.Finset.subsetB`.**
//! `subsetB` is a `Bool` loop and `finset.rs` carries no reflection lemma
//! taking `subsetB s t = true` back to pointwise membership — only
//! `card_le_of_subsetB`. Every consumer of `HallCondition` has the pointwise
//! fact already (the sub-family it is testing is one it built), so the
//! pointwise form costs nothing and avoids a second bounded search. This is the
//! same call `finset.rs` made for `sum_union_disjoint`'s disjointness premise.
//!
//! **`anyBelow` is `notB ∘ allBelow ∘ notB`, and only its INTRODUCTION rule is
//! proved.** `Nat.Finset.allBelow` has three laws (build, read back, and the
//! `false` witness); `anyBelow` here needs only "a witness makes it `true`",
//! which is what the necessity direction consumes. The elimination rule — a
//! `true` `anyBelow` yields a witness — is exactly what the *sufficiency*
//! direction would need, and is not proved; see the module's closing note.
//!
//! # Where this stops, and why
//!
//! The **sufficiency** direction — Hall's condition implies a matching — is NOT
//! proved. It is not blocked by a missing lemma but by three pieces of
//! machinery this carrier does not have, and naming them is the deliverable:
//!
//! 1. **Induction on `card s`, not on a `Nat` argument.** The textbook proof
//!    splits on whether some proper non-empty `t ⊂ s` is *critical*
//!    (`card t = card (unionOver nb t)`) and recurses on two strictly smaller
//!    families. This kernel's `Nat.rec` recurses on a numeral, so the argument
//!    needs strong induction on `card s` with the family varying — a motive
//!    `∀ k, ∀ s nb, card s ≤ k → …`. There is **no** `Nat.strongInduction` in
//!    this prelude (checked, and `Nat.base_induction` is not it); the machinery
//!    that exists is `Nat.lt_well_founded : WellFounded Nat.lt` together with
//!    the generic `WellFounded.fix`, which is enough but has no `Nat`-specific
//!    wrapper, and no existing helper quantifies inside the motive over
//!    `Nat.Finset` and `Nat → Nat.Finset`.
//! 2. **Choosing the critical subfamily.** The split needs *some* critical `t`
//!    or a proof that none exists, which is a search over subsets of `s`. This
//!    kernel has no classical choice, so it must be COMPUTED — a
//!    `Nat.Finset`-valued bounded search over the `2^(bound s)` subsets,
//!    together with its own reflection lemma. Nothing of that shape exists;
//!    `Nat.Finset.allBelow_false_witness` is the one-dimensional analogue and
//!    would be the model.
//! 3. **Deleting from a family.** Both branches build a new family
//!    (`fun i => Nat.Finset.sdiff (nb i) (unionOver nb t)`) and a new index set,
//!    then have to transport Hall's condition across the change. `sdiff` and
//!    the counting laws exist; what does not is any lemma relating
//!    `unionOver` of a modified family to `unionOver` of the original.
//!
//! Item 2 is the real one. Items 1 and 3 are bookkeeping over machinery that
//! exists; item 2 is a new search-plus-reflection primitive of the same kind
//! `Nat.Finset.exists_collision` had to be built for the pigeonhole, and it is
//! the piece a lane should size first.

#![allow(clippy::many_single_char_names, clippy::too_many_lines)]

use super::NatPrelude;
use super::graph::{and_b, bool_congr, not_b};
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps, bool_true_or_false};
use super::subset_search::{not_b_false_elim, not_b_true_elim};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

// ---------------------------------------------------------------------------
// Small term builders.
// ---------------------------------------------------------------------------

/// `Prop`.
fn prop(d: &mut NatDev<'_>) -> ExprId {
    d.kernel().sort_zero()
}

/// `Nat.Finset`.
fn finset_ty(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    d.kernel().const_(p.finset, vec![])
}

/// `Nat → Nat.Finset`, the type of an indexed family.
fn family_ty(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let nat = d.nat_ty();
    let fs = finset_ty(d, p);
    d.arrow(nat, fs)
}

/// `Nat → Nat`, the type of a choice function.
fn choice_ty(d: &mut NatDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    d.arrow(nat, nat)
}

/// `Nat → Bool`.
fn pred_ty(d: &mut NatDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    d.arrow(nat, bool_ty)
}

/// `Nat.Finset.memB s i`.
fn mem_b(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, i: ExprId) -> ExprId {
    d.const_app(p.finset_mem_b, &[s, i])
}

/// `Eq Bool (Nat.Finset.memB s i) true`.
fn mem_true(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, i: ExprId) -> ExprId {
    let m = mem_b(d, p, s, i);
    let t = d.bool_true();
    d.bool_eq(m, t)
}

/// `Nat.Finset.bound s`.
fn fs_bound(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId) -> ExprId {
    d.const_app(p.finset_bound, &[s])
}

/// `Nat.Finset.card s`.
fn fs_card(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId) -> ExprId {
    d.const_app(p.finset_card, &[s])
}

/// `Nat.Hall.anyBelow f n`.
fn any_below(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.hall_any_below, &[f, n])
}

/// `Nat.Hall.unionOver nb t`.
fn union_over(d: &mut NatDev<'_>, p: &NatPrelude, nb: ExprId, t: ExprId) -> ExprId {
    d.const_app(p.hall_union_over, &[nb, t])
}

/// `fun i => memB t i && memB (nb i) v` — `unionOver`'s inner predicate at a
/// fixed value `v`.
fn cover_pred(d: &mut NatDev<'_>, p: &NatPrelude, nb: ExprId, t: ExprId, v: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let in_t = mem_b(d, p, t, i);
    let member = d.apply(nb, &[i]);
    let holds = mem_b(d, p, member, v);
    let body = and_b(d, p, in_t, holds);
    d.lam_fv(i_fv, nat, body)
}

// ---------------------------------------------------------------------------
// The definitions.
// ---------------------------------------------------------------------------

fn declare_definitions(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let prop_ty = prop(d);
    let fs = finset_ty(d, &p);
    let fam = family_ty(d, &p);
    let ch = choice_ty(d);
    let pty = pred_ty(d);

    // anyBelow f n := notB (allBelow (fun i => notB (f i)) n)
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let negated = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let at_i = d.apply(f, &[i]);
            let body = not_b(d, &p, at_i);
            d.lam_fv(i_fv, nat, body)
        };
        let looped = d.const_app(p.finset_all_below, &[negated, n]);
        let body = not_b(d, &p, looped);
        let value = {
            let inner = d.lam_fv(n_fv, nat, body);
            d.lam_fv(f_fv, pty, inner)
        };
        let ty = {
            let inner = d.arrow(nat, bool_ty);
            d.arrow(pty, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.hall_any_below,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(3),
        })?;
    }

    // unionBound nb n := sumRange (fun i => Nat.Finset.bound (nb i)) n
    {
        let nb_fv = d.fresh_fvar();
        let nb = d.kernel().fvar(nb_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sizes = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let member = d.apply(nb, &[i]);
            let body = fs_bound(d, &p, member);
            d.lam_fv(i_fv, nat, body)
        };
        let body = d.sum_range(sizes, n);
        let value = {
            let inner = d.lam_fv(n_fv, nat, body);
            d.lam_fv(nb_fv, fam, inner)
        };
        let ty = {
            let inner = d.arrow(nat, nat);
            d.arrow(fam, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.hall_union_bound,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(3),
        })?;
    }

    // unionOver nb t := mk (fun v => anyBelow (cover_pred nb t v) (bound t))
    //                      (unionBound nb (bound t))
    {
        let nb_fv = d.fresh_fvar();
        let nb = d.kernel().fvar(nb_fv);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let bt = fs_bound(d, &p, t);
        let indicator = {
            let v_fv = d.fresh_fvar();
            let v = d.kernel().fvar(v_fv);
            let inner = cover_pred(d, &p, nb, t, v);
            let body = any_below(d, &p, inner, bt);
            d.lam_fv(v_fv, nat, body)
        };
        let bound = d.const_app(p.hall_union_bound, &[nb, bt]);
        let body = d.const_app(p.finset_mk, &[indicator, bound]);
        let value = {
            let inner = d.lam_fv(t_fv, fs, body);
            d.lam_fv(nb_fv, fam, inner)
        };
        let ty = {
            let inner = d.arrow(fs, fs);
            d.arrow(fam, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.hall_union_over,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(5),
        })?;
    }

    // IsMatching s nb f := (∀ i, memB s i = true → memB (nb i) (f i) = true)
    //                    ∧ (∀ i j, memB s i = true → memB s j = true →
    //                              f i = f j → i = j)
    {
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let nb_fv = d.fresh_fvar();
        let nb = d.kernel().fvar(nb_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);

        let maps_into = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hyp = mem_true(d, &p, s, i);
            let member = d.apply(nb, &[i]);
            let fi = d.apply(f, &[i]);
            let concl = mem_true(d, &p, member, fi);
            let step = d.arrow(hyp, concl);
            d.pi_fv(i_fv, nat, step)
        };
        let injective = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let hi = mem_true(d, &p, s, i);
            let hj = mem_true(d, &p, s, j);
            let fi = d.apply(f, &[i]);
            let fj = d.apply(f, &[j]);
            let heq = d.eq(fi, fj);
            let concl = d.eq(i, j);
            let s4 = d.arrow(heq, concl);
            let s3 = d.arrow(hj, s4);
            let s2 = d.arrow(hi, s3);
            let inner = d.pi_fv(j_fv, nat, s2);
            d.pi_fv(i_fv, nat, inner)
        };
        let body = d.const_app(p.logic.and, &[maps_into, injective]);
        let value = {
            let s3 = d.lam_fv(f_fv, ch, body);
            let s2 = d.lam_fv(nb_fv, fam, s3);
            d.lam_fv(s_fv, fs, s2)
        };
        let ty = {
            let s3 = d.arrow(ch, prop_ty);
            let s2 = d.arrow(fam, s3);
            d.arrow(fs, s2)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.hall_is_matching,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(3),
        })?;
    }

    // HallCondition s nb := ∀ t, (∀ i, memB t i = true → memB s i = true) →
    //                            Le (card t) (card (unionOver nb t))
    {
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let nb_fv = d.fresh_fvar();
        let nb = d.kernel().fvar(nb_fv);
        let body = {
            let t_fv = d.fresh_fvar();
            let t = d.kernel().fvar(t_fv);
            let hyp = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let in_t = mem_true(d, &p, t, i);
                let in_s = mem_true(d, &p, s, i);
                let step = d.arrow(in_t, in_s);
                d.pi_fv(i_fv, nat, step)
            };
            let lhs = fs_card(d, &p, t);
            let cover = union_over(d, &p, nb, t);
            let rhs = fs_card(d, &p, cover);
            let concl = d.le(lhs, rhs);
            let step = d.arrow(hyp, concl);
            d.pi_fv(t_fv, fs, step)
        };
        let value = {
            let inner = d.lam_fv(nb_fv, fam, body);
            d.lam_fv(s_fv, fs, inner)
        };
        let ty = {
            let inner = d.arrow(fam, prop_ty);
            d.arrow(fs, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.hall_condition,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(6),
        })?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// `anyBelow`'s introduction rule.
// ---------------------------------------------------------------------------

/// `Nat.Hall.anyBelow_of_witness : ∀ f n i, Lt i n → f i = true →
/// anyBelow f n = true`.
///
/// `anyBelow` is `notB` of a loop, so the proof is: decide the loop. If it is
/// `true`, `allBelow_true_at` at `i` gives `notB (f i) = true`, which against
/// `f i = true` is `false = true`. If it is `false`, `notB false` is `true` and
/// one congruence closes.
fn declare_any_below_intro(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let pty = pred_ty(d);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let true_ = d.bool_true();
    let false_ = d.bool_false();

    let hlt_ty = d.lt(i, n);
    let hlt_fv = d.fresh_fvar();
    let hlt = d.kernel().fvar(hlt_fv);
    let at_i = d.apply(f, &[i]);
    let hf_ty = d.bool_eq(at_i, true_);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);

    let negated = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let at_k = d.apply(f, &[k]);
        let body = not_b(d, &p, at_k);
        d.lam_fv(k_fv, nat, body)
    };
    let looped = d.const_app(p.finset_all_below, &[negated, n]);
    let goal = {
        let lhs = any_below(d, &p, f, n);
        d.bool_eq(lhs, true_)
    };

    let is_true = d.bool_eq(looped, true_);
    let is_false = d.bool_eq(looped, false_);
    let dichotomy = bool_true_or_false(d, &p, looped);
    let on_true = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        // `allBelow_true_at` at `i` gives `notB (f i) = true`.
        let read = d.const_app(p.finset_all_below_true_at, &[negated, n, h, i, hlt]);
        // `f i = true` makes the same term `notB true`, i.e. `false`.
        let negated_at_i = not_b(d, &p, at_i);
        let collapse = bool_congr(d, at_i, true_, hf, &|d, x| not_b(d, &p, x));
        let flipped = d.bool_symm(negated_at_i, false_, collapse);
        let absurd = d.bool_trans(false_, negated_at_i, true_, flipped, read);
        let body = d.false_true_elim(goal, absurd);
        d.lam_fv(h_fv, is_true, body)
    };
    let on_false = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        // `notB (allBelow …) = notB false`, i.e. `true`.
        let body = bool_congr(d, looped, false_, h, &|d, x| not_b(d, &p, x));
        d.lam_fv(h_fv, is_false, body)
    };
    let proof = d.const_app(
        p.logic.or_elim,
        &[is_true, is_false, goal, dichotomy, on_true, on_false],
    );

    let ty = {
        let s5 = d.arrow(hf_ty, goal);
        let s4 = d.arrow(hlt_ty, s5);
        let s3 = d.pi_fv(i_fv, nat, s4);
        let s2 = d.pi_fv(n_fv, nat, s3);
        d.pi_fv(f_fv, pty, s2)
    };
    let value = {
        let s5 = d.lam_fv(hf_fv, hf_ty, proof);
        let s4 = d.lam_fv(hlt_fv, hlt_ty, s5);
        let s3 = d.lam_fv(i_fv, nat, s4);
        let s2 = d.lam_fv(n_fv, nat, s3);
        d.lam_fv(f_fv, pty, s2)
    };
    d.declare_theorem(p.hall_any_below_of_witness, ty, value)
}

// ---------------------------------------------------------------------------
// Membership in the union.
// ---------------------------------------------------------------------------

/// `Nat.Hall.memB_unionOver : ∀ nb t i v, memB t i = true →
/// memB (nb i) v = true → memB (unionOver nb t) v = true`.
///
/// Two obligations: the value is below `unionOver`'s own bound (it is below
/// `bound (nb i)`, which `Nat.le_sumRange_of_lt` puts below the sum), and the
/// indicator fires (one `anyBelow_of_witness` at the index `i`).
fn declare_mem_union_over(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);
    let fam = family_ty(d, &p);
    let true_ = d.bool_true();

    let nb_fv = d.fresh_fvar();
    let nb = d.kernel().fvar(nb_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);

    let hi_ty = mem_true(d, &p, t, i);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);
    let member = d.apply(nb, &[i]);
    let hv_ty = mem_true(d, &p, member, v);
    let hv_fv = d.fresh_fvar();
    let hv = d.kernel().fvar(hv_fv);

    let bt = fs_bound(d, &p, t);
    let cover = union_over(d, &p, nb, t);
    let goal = mem_true(d, &p, cover, v);

    // `i < bound t`, so `bound (nb i) <= unionBound nb (bound t)`.
    let hi_lt = d.const_app(p.finset_lt_bound_of_mem_b, &[t, i, hi]);
    let sizes = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let at_k = d.apply(nb, &[k]);
        let body = fs_bound(d, &p, at_k);
        d.lam_fv(k_fv, nat, body)
    };
    let size_le = d.const_app(p.le_sum_range_of_lt, &[sizes, bt, i, hi_lt]);
    // `v < bound (nb i)`, so `v < unionBound nb (bound t)`.
    let hv_lt = d.const_app(p.finset_lt_bound_of_mem_b, &[member, v, hv]);
    let succ_v = d.succ(v);
    let member_bound = fs_bound(d, &p, member);
    let union_bound = d.const_app(p.hall_union_bound, &[nb, bt]);
    let v_lt = d.const_app(
        p.le_trans,
        &[succ_v, member_bound, union_bound, hv_lt, size_le],
    );

    // The indicator fires at index `i`.
    let indicator = cover_pred(d, &p, nb, t, v);
    let in_t = mem_b(d, &p, t, i);
    let holds = mem_b(d, &p, member, v);
    let conj = d.const_app(p.graph_and_b_intro, &[in_t, holds, hi, hv]);
    let fired = d.const_app(
        p.hall_any_below_of_witness,
        &[indicator, bt, i, hi_lt, conj],
    );

    // `memB (unionOver nb t) v = <indicator at v>`, then rewrite to `true`.
    let unfolded = d.const_app(p.finset_mem_b_of_lt, &[cover, v, v_lt]);
    let indicator_at_v = any_below(d, &p, indicator, bt);
    let mem_here = mem_b(d, &p, cover, v);
    let proof = d.bool_trans(mem_here, indicator_at_v, true_, unfolded, fired);

    let ty = {
        let s6 = d.arrow(hv_ty, goal);
        let s5 = d.arrow(hi_ty, s6);
        let s4 = d.pi_fv(v_fv, nat, s5);
        let s3 = d.pi_fv(i_fv, nat, s4);
        let s2 = d.pi_fv(t_fv, fs, s3);
        d.pi_fv(nb_fv, fam, s2)
    };
    let value = {
        let s6 = d.lam_fv(hv_fv, hv_ty, proof);
        let s5 = d.lam_fv(hi_fv, hi_ty, s6);
        let s4 = d.lam_fv(v_fv, nat, s5);
        let s3 = d.lam_fv(i_fv, nat, s4);
        let s2 = d.lam_fv(t_fv, fs, s3);
        d.lam_fv(nb_fv, fam, s2)
    };
    d.declare_theorem(p.hall_mem_union_over, ty, value)
}

// ---------------------------------------------------------------------------
// Necessity: a matching forces Hall's condition.
// ---------------------------------------------------------------------------

/// `Nat.Hall.hallCondition_of_isMatching : ∀ s nb f, IsMatching s nb f →
/// HallCondition s nb`.
///
/// The whole content is one application of `Nat.Finset.card_le_of_injOn`
/// (ADR-1593): the matching restricted to a subfamily `t` is still injective on
/// `t` and still lands in `unionOver nb t`, so `card t ≤ card (unionOver nb t)`.
/// No new counting machinery — which is the point of the exercise.
fn declare_necessity(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);
    let fam = family_ty(d, &p);
    let ch = choice_ty(d);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let nb_fv = d.fresh_fvar();
    let nb = d.kernel().fvar(nb_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let hm_ty = d.const_app(p.hall_is_matching, &[s, nb, f]);
    let hm_fv = d.fresh_fvar();
    let hm = d.kernel().fvar(hm_fv);
    let concl = d.const_app(p.hall_condition, &[s, nb]);

    // Take `IsMatching` apart.
    let maps_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hyp = mem_true(d, &p, s, i);
        let member = d.apply(nb, &[i]);
        let fi = d.apply(f, &[i]);
        let target = mem_true(d, &p, member, fi);
        let step = d.arrow(hyp, target);
        d.pi_fv(i_fv, nat, step)
    };
    let inj_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let hi = mem_true(d, &p, s, i);
        let hj = mem_true(d, &p, s, j);
        let fi = d.apply(f, &[i]);
        let fj = d.apply(f, &[j]);
        let heq = d.eq(fi, fj);
        let target = d.eq(i, j);
        let s4 = d.arrow(heq, target);
        let s3 = d.arrow(hj, s4);
        let s2 = d.arrow(hi, s3);
        let inner = d.pi_fv(j_fv, nat, s2);
        d.pi_fv(i_fv, nat, inner)
    };
    let maps = and_left(d, maps_ty, inj_ty, hm);
    let inj = and_right(d, maps_ty, inj_ty, hm);

    let body = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let sub_ty = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let in_t = mem_true(d, &p, t, i);
            let in_s = mem_true(d, &p, s, i);
            let step = d.arrow(in_t, in_s);
            d.pi_fv(i_fv, nat, step)
        };
        let sub_fv = d.fresh_fvar();
        let sub = d.kernel().fvar(sub_fv);
        let cover = union_over(d, &p, nb, t);

        let inj_on_t = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let hi_ty = mem_true(d, &p, t, i);
            let hi_fv = d.fresh_fvar();
            let hi = d.kernel().fvar(hi_fv);
            let hj_ty = mem_true(d, &p, t, j);
            let hj_fv = d.fresh_fvar();
            let hj = d.kernel().fvar(hj_fv);
            let fi = d.apply(f, &[i]);
            let fj = d.apply(f, &[j]);
            let heq_ty = d.eq(fi, fj);
            let heq_fv = d.fresh_fvar();
            let heq = d.kernel().fvar(heq_fv);
            let hi_s = d.apply(sub, &[i, hi]);
            let hj_s = d.apply(sub, &[j, hj]);
            let step = d.apply(inj, &[i, j, hi_s, hj_s, heq]);
            let s4 = d.lam_fv(heq_fv, heq_ty, step);
            let s3 = d.lam_fv(hj_fv, hj_ty, s4);
            let s2 = d.lam_fv(hi_fv, hi_ty, s3);
            let inner = d.lam_fv(j_fv, nat, s2);
            d.lam_fv(i_fv, nat, inner)
        };
        let maps_into_cover = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hi_ty = mem_true(d, &p, t, i);
            let hi_fv = d.fresh_fvar();
            let hi = d.kernel().fvar(hi_fv);
            let hi_s = d.apply(sub, &[i, hi]);
            let fi = d.apply(f, &[i]);
            let in_member = d.apply(maps, &[i, hi_s]);
            let step = d.const_app(p.hall_mem_union_over, &[nb, t, i, fi, hi, in_member]);
            let inner = d.lam_fv(hi_fv, hi_ty, step);
            d.lam_fv(i_fv, nat, inner)
        };
        let counted = d.const_app(
            p.finset_card_le_of_inj_on,
            &[t, cover, f, inj_on_t, maps_into_cover],
        );
        let with_sub = d.lam_fv(sub_fv, sub_ty, counted);
        d.lam_fv(t_fv, fs, with_sub)
    };

    let ty = {
        let s4 = d.arrow(hm_ty, concl);
        let s3 = d.pi_fv(f_fv, ch, s4);
        let s2 = d.pi_fv(nb_fv, fam, s3);
        d.pi_fv(s_fv, fs, s2)
    };
    let value = {
        let s4 = d.lam_fv(hm_fv, hm_ty, body);
        let s3 = d.lam_fv(f_fv, ch, s4);
        let s2 = d.lam_fv(nb_fv, fam, s3);
        d.lam_fv(s_fv, fs, s2)
    };
    d.declare_theorem(p.hall_condition_of_is_matching, ty, value)
}

// ---------------------------------------------------------------------------
// Entry point.
// ---------------------------------------------------------------------------

/// Declare `Nat.Hall` and the necessity direction of the marriage theorem.
///
/// # Errors
///
/// Returns the kernel's rejection if any declaration fails to type-check.
// ---------------------------------------------------------------------------
// Logical plumbing (this prelude's per-file convention is a private copy).
// ---------------------------------------------------------------------------

/// Non-dependent `Or.rec` into a `Prop` goal.
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

/// `Exists.{1} Nat pred`.
fn exists_nat(d: &mut NatDev<'_>, p: &NatPrelude, pred: ExprId) -> ExprId {
    let one = d.level_one();
    let nat = d.nat_ty();
    let ex = d.kernel().const_(p.logic.exists_, vec![one]);
    d.apply(ex, &[nat, pred])
}

/// `Exists.intro.{1} Nat pred w h`.
fn exists_intro_nat(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pred: ExprId,
    w: ExprId,
    h: ExprId,
) -> ExprId {
    let one = d.level_one();
    let nat = d.nat_ty();
    let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
    d.apply(intro, &[nat, pred, w, h])
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

/// `fun i => And (Lt i n) (Eq Bool (f i) false)` — the shape
/// `Nat.Finset.allBelow_false_witness` produces.
fn below_witness_pred(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let lt = d.lt(i, n);
    let fi = d.apply(f, &[i]);
    let fal = d.bool_false();
    let is_false = d.bool_eq(fi, fal);
    let body = d.const_app(p.logic.and, &[lt, is_false]);
    d.lam_fv(i_fv, nat, body)
}

/// `fun i => And (Lt i n) (Eq Bool (f i) true)` — the shape
/// [`declare_any_below_witness`] produces, and `below_witness_pred`'s
/// opposite polarity.
fn above_witness_pred(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let lt = d.lt(i, n);
    let fi = d.apply(f, &[i]);
    let tru = d.bool_true();
    let is_true = d.bool_eq(fi, tru);
    let body = d.const_app(p.logic.and, &[lt, is_true]);
    d.lam_fv(i_fv, nat, body)
}

/// `fun i => And (memB t i = true) (memB (nb i) v = true)` — the witness shape
/// [`declare_mem_union_over_elim`] produces. The index bound is DROPPED:
/// `Nat.Finset.lt_bound_of_memB` recovers `Lt i (bound t)` from the first
/// conjunct, so carrying it would make every consumer discard it.
fn union_witness_pred(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    nb: ExprId,
    t: ExprId,
    v: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let in_t = mem_true(d, &p, t, i);
    let member = d.apply(nb, &[i]);
    let holds = mem_true(d, &p, member, v);
    let body = d.const_app(p.logic.and, &[in_t, holds]);
    d.lam_fv(i_fv, nat, body)
}

/// Two `Bool` terms that imply each other's truth are equal. This kernel has
/// no `propext` and no `Bool`-valued iff, so the bridge from a two-way
/// implication to an equation is three nested decisions: `a`, and in the
/// `false` branch `b` as well.
fn bool_eq_of_iff(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    fwd: ExprId,
    bwd: ExprId,
) -> ExprId {
    let p = *p;
    let tru = d.bool_true();
    let fal = d.bool_false();
    let goal = d.bool_eq(a, b);
    let a_true = d.bool_eq(a, tru);
    let a_false = d.bool_eq(a, fal);
    let decided = bool_true_or_false(d, &p, a);

    let on_true = {
        let ha_fv = d.fresh_fvar();
        let ha = d.kernel().fvar(ha_fv);
        let hb = d.apply(fwd, &[ha]);
        let back = d.bool_symm(b, tru, hb);
        let body = d.bool_trans(a, tru, b, ha, back);
        d.lam_fv(ha_fv, a_true, body)
    };
    let on_false = {
        let ha_fv = d.fresh_fvar();
        let ha = d.kernel().fvar(ha_fv);
        let b_true = d.bool_eq(b, tru);
        let b_false = d.bool_eq(b, fal);
        let decided_b = bool_true_or_false(d, &p, b);
        let on_b_true = {
            let hb_fv = d.fresh_fvar();
            let hb = d.kernel().fvar(hb_fv);
            let ha2 = d.apply(bwd, &[hb]);
            let back = d.bool_symm(a, fal, ha);
            let impossible = d.bool_trans(fal, a, tru, back, ha2);
            let absurd = d.false_true_elim(goal, impossible);
            d.lam_fv(hb_fv, b_true, absurd)
        };
        let on_b_false = {
            let hb_fv = d.fresh_fvar();
            let hb = d.kernel().fvar(hb_fv);
            let back = d.bool_symm(b, fal, hb);
            let body = d.bool_trans(a, fal, b, ha, back);
            d.lam_fv(hb_fv, b_false, body)
        };
        let body = or_elim(
            d, &p, b_true, b_false, goal, on_b_true, on_b_false, decided_b,
        );
        d.lam_fv(ha_fv, a_false, body)
    };
    or_elim(d, &p, a_true, a_false, goal, on_true, on_false, decided)
}

// ---------------------------------------------------------------------------
// `anyBelow`'s ELIMINATION rule — the half ADR-1608 declared missing.
// ---------------------------------------------------------------------------

/// `Nat.Hall.anyBelow_witness : ∀ f n, Eq Bool (anyBelow f n) true →
/// Exists (fun i => And (Lt i n) (Eq Bool (f i) true))`.
///
/// ADR-1608 declared only the introduction rule and named this one as what
/// sufficiency would need; ADR-1614 then observed it is a one-dimensional
/// instance of `Nat.Finset.allBelow_false_witness` and called it bookkeeping.
/// It is: `anyBelow` is `notB ∘ allBelow ∘ notB`, so a `true` verdict is a
/// `false` loop (`not_b_true_elim`), the loop's own third law computes an
/// index where its body is `false`, and the body's `notB` comes back off
/// (`not_b_false_elim`). No choice principle — the recursion inside
/// `allBelow_false_witness` IS the search.
fn declare_any_below_witness(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let pty = pred_ty(d);
    let tru = d.bool_true();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let search = any_below(d, &p, f, n);
    let hyp_ty = d.bool_eq(search, tru);

    let result_pred = above_witness_pred(d, &p, f, n);
    let goal = exists_nat(d, &p, result_pred);

    let negated = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let at_k = d.apply(f, &[k]);
        let body = not_b(d, &p, at_k);
        d.lam_fv(k_fv, nat, body)
    };
    let looped = d.const_app(p.finset_all_below, &[negated, n]);
    let loop_false = not_b_true_elim(d, &p, looped, h);
    let found = d.lemma(p.finset_all_below_false_witness, &[negated, n, loop_false]);

    let witness_pred = below_witness_pred(d, &p, negated, n);
    let minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let lt_ty = d.lt(k, n);
        let neg_at_k = d.apply(negated, &[k]);
        let fal = d.bool_false();
        let neg_false = d.bool_eq(neg_at_k, fal);
        let hw_ty = d.const_app(p.logic.and, &[lt_ty, neg_false]);
        let hw_fv = d.fresh_fvar();
        let hw = d.kernel().fvar(hw_fv);

        let lt_pf = and_left(d, lt_ty, neg_false, hw);
        let off = and_right(d, lt_ty, neg_false, hw);
        let at_k = d.apply(f, &[k]);
        // `negated k` beta-reduces to `notB (f k)`; the kernel identifies them.
        let holds = not_b_false_elim(d, &p, at_k, off);
        let tru2 = d.bool_true();
        let is_true = d.bool_eq(at_k, tru2);
        let pair = d.const_app(p.logic.and_intro, &[lt_ty, is_true, lt_pf, holds]);
        let intro = exists_intro_nat(d, &p, result_pred, k, pair);
        let with_hw = d.lam_fv(hw_fv, hw_ty, intro);
        d.lam_fv(k_fv, nat, with_hw)
    };
    let proof = exists_elim_nat(d, &p, witness_pred, goal, minor, found);

    let ty = {
        let with_h = d.arrow(hyp_ty, goal);
        let with_n = d.pi_fv(n_fv, nat, with_h);
        d.pi_fv(f_fv, pty, with_n)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, proof);
        let with_n = d.lam_fv(n_fv, nat, with_h);
        d.lam_fv(f_fv, pty, with_n)
    };
    d.declare_theorem(p.hall_any_below_witness, ty, value)
}

// ---------------------------------------------------------------------------
// Membership in the union, in the other direction.
// ---------------------------------------------------------------------------

/// `Nat.Hall.memB_unionOver_elim : ∀ nb t v,
/// Eq Bool (memB (unionOver nb t) v) true →
/// Exists (fun i => And (Eq Bool (memB t i) true) (Eq Bool (memB (nb i) v) true))`.
///
/// The converse of [`declare_mem_union_over`], and with it `unionOver` finally
/// has a two-sided characterisation: `v` is in the union exactly when SOME
/// index of `t` supplies it. Everything below in this file is that
/// characterisation used twice.
///
/// `memB` truncates, so the hypothesis already places `v` below the union's
/// own bound (`lt_bound_of_memB`) and `memB_of_lt` exposes the stored
/// indicator, which is one `anyBelow`. [`declare_any_below_witness`] computes
/// the index and `Nat.Graph.andB_left`/`andB_right` split the conjunction the
/// indicator is built from.
fn declare_mem_union_over_elim(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);
    let fam = family_ty(d, &p);
    let tru = d.bool_true();

    let nb_fv = d.fresh_fvar();
    let nb = d.kernel().fvar(nb_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let cover = union_over(d, &p, nb, t);
    let mem_here = mem_b(d, &p, cover, v);
    let hyp_ty = d.bool_eq(mem_here, tru);

    let result_pred = union_witness_pred(d, &p, nb, t, v);
    let goal = exists_nat(d, &p, result_pred);

    let bt = fs_bound(d, &p, t);
    let indicator = cover_pred(d, &p, nb, t, v);
    let ind_at = any_below(d, &p, indicator, bt);

    let hlt = d.lemma(p.finset_lt_bound_of_mem_b, &[cover, v, h]);
    let unfolded = d.lemma(p.finset_mem_b_of_lt, &[cover, v, hlt]);
    let back = d.bool_symm(mem_here, ind_at, unfolded);
    let ind_true = d.bool_trans(ind_at, mem_here, tru, back, h);
    let found = d.lemma(p.hall_any_below_witness, &[indicator, bt, ind_true]);

    let witness_pred = above_witness_pred(d, &p, indicator, bt);
    let minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let lt_ty = d.lt(k, bt);
        let ind_k = d.apply(indicator, &[k]);
        let tru2 = d.bool_true();
        let ind_k_true = d.bool_eq(ind_k, tru2);
        let hw_ty = d.const_app(p.logic.and, &[lt_ty, ind_k_true]);
        let hw_fv = d.fresh_fvar();
        let hw = d.kernel().fvar(hw_fv);

        let fired = and_right(d, lt_ty, ind_k_true, hw);
        let in_t = mem_b(d, &p, t, k);
        let member = d.apply(nb, &[k]);
        let holds = mem_b(d, &p, member, v);
        // `indicator k` beta-reduces to `andB (memB t k) (memB (nb k) v)`.
        let hi = d.lemma(p.graph_and_b_left, &[in_t, holds, fired]);
        let hv = d.lemma(p.graph_and_b_right, &[in_t, holds, fired]);

        let in_t_true = mem_true(d, &p, t, k);
        let holds_true = mem_true(d, &p, member, v);
        let pair = d.const_app(p.logic.and_intro, &[in_t_true, holds_true, hi, hv]);
        let intro = exists_intro_nat(d, &p, result_pred, k, pair);
        let with_hw = d.lam_fv(hw_fv, hw_ty, intro);
        d.lam_fv(k_fv, nat, with_hw)
    };
    let proof = exists_elim_nat(d, &p, witness_pred, goal, minor, found);

    let ty = {
        let with_h = d.arrow(hyp_ty, goal);
        let with_v = d.pi_fv(v_fv, nat, with_h);
        let with_t = d.pi_fv(t_fv, fs, with_v);
        d.pi_fv(nb_fv, fam, with_t)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, proof);
        let with_v = d.lam_fv(v_fv, nat, with_h);
        let with_t = d.lam_fv(t_fv, fs, with_v);
        d.lam_fv(nb_fv, fam, with_t)
    };
    d.declare_theorem(p.hall_mem_union_over_elim, ty, value)
}

// ---------------------------------------------------------------------------
// The union depends on the index set's MEMBERS, not on its stored bound.
// ---------------------------------------------------------------------------

/// `Nat.Hall.memB_unionOver_congr : ∀ nb t t',
/// (∀ i, Eq Bool (memB t i) (memB t' i)) →
/// ∀ v, Eq Bool (memB (unionOver nb t) v) (memB (unionOver nb t') v)`.
///
/// **The bookkeeping obstruction ADR-1614 §4 named, closed.** `unionOver nb t`
/// stores `unionBound nb (bound t)`, which reads `t`'s BOUND and not its
/// members, so two membership-equal index sets give unions that are not `Eq`
/// and whose bounds differ — and until now nothing said their MEMBERSHIPS
/// agree. They do, and the reason is that membership in the union never
/// mentions the bound: [`declare_mem_union_over_elim`] turns a member into an
/// index of `t`, the hypothesis moves that index to `t'`, and
/// [`declare_mem_union_over`] puts it back. Twice, once per direction, plus
/// the `Bool` decision that turns a two-way implication into an equation.
fn declare_mem_union_over_congr(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);
    let fam = family_ty(d, &p);
    let tru = d.bool_true();

    let nb_fv = d.fresh_fvar();
    let nb = d.kernel().fvar(nb_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let hc_fv = d.fresh_fvar();
    let hc = d.kernel().fvar(hc_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);

    let hc_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lhs = mem_b(d, &p, t, i);
        let rhs = mem_b(d, &p, u, i);
        let body = d.bool_eq(lhs, rhs);
        d.pi_fv(i_fv, nat, body)
    };

    let cover_t = union_over(d, &p, nb, t);
    let cover_u = union_over(d, &p, nb, u);
    let mem_t_side = mem_b(d, &p, cover_t, v);
    let mem_u_side = mem_b(d, &p, cover_u, v);

    // `from`'s membership implies `to`'s, transporting each witnessing index
    // across `hc` in the direction `flip` selects.
    let direction = |d: &mut NatDev<'_>, from: ExprId, to: ExprId, flip: bool| -> ExprId {
        let src = union_over(d, &p, nb, from);
        let dst = union_over(d, &p, nb, to);
        let mem_src = mem_b(d, &p, src, v);
        let mem_dst = mem_b(d, &p, dst, v);
        let hyp_ty = d.bool_eq(mem_src, tru);
        let goal = d.bool_eq(mem_dst, tru);
        let ha_fv = d.fresh_fvar();
        let ha = d.kernel().fvar(ha_fv);

        let found = d.lemma(p.hall_mem_union_over_elim, &[nb, from, v, ha]);
        let witness_pred = union_witness_pred(d, &p, nb, from, v);
        let minor = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let in_src = mem_true(d, &p, from, k);
            let member = d.apply(nb, &[k]);
            let holds = mem_true(d, &p, member, v);
            let hw_ty = d.const_app(p.logic.and, &[in_src, holds]);
            let hw_fv = d.fresh_fvar();
            let hw = d.kernel().fvar(hw_fv);

            let hi = and_left(d, in_src, holds, hw);
            let hv = and_right(d, in_src, holds, hw);

            // `hc k : memB t k = memB u k`, oriented for this direction.
            let at_k = d.apply(hc, &[k]);
            let mem_from = mem_b(d, &p, from, k);
            let mem_to = mem_b(d, &p, to, k);
            let oriented = if flip {
                d.bool_symm(mem_to, mem_from, at_k)
            } else {
                at_k
            };
            let back = d.bool_symm(mem_from, mem_to, oriented);
            let hi_to = d.bool_trans(mem_to, mem_from, tru, back, hi);

            let placed = d.lemma(p.hall_mem_union_over, &[nb, to, k, v, hi_to, hv]);
            let with_hw = d.lam_fv(hw_fv, hw_ty, placed);
            d.lam_fv(k_fv, nat, with_hw)
        };
        let body = exists_elim_nat(d, &p, witness_pred, goal, minor, found);
        d.lam_fv(ha_fv, hyp_ty, body)
    };

    let fwd = direction(d, t, u, false);
    let bwd = direction(d, u, t, true);
    let proof = bool_eq_of_iff(d, &p, mem_t_side, mem_u_side, fwd, bwd);

    let goal = d.bool_eq(mem_t_side, mem_u_side);
    let ty = {
        let with_v = d.pi_fv(v_fv, nat, goal);
        let with_hc = d.arrow(hc_ty, with_v);
        let with_u = d.pi_fv(u_fv, fs, with_hc);
        let with_t = d.pi_fv(t_fv, fs, with_u);
        d.pi_fv(nb_fv, fam, with_t)
    };
    let value = {
        let with_v = d.lam_fv(v_fv, nat, proof);
        let with_hc = d.lam_fv(hc_fv, hc_ty, with_v);
        let with_u = d.lam_fv(u_fv, fs, with_hc);
        let with_t = d.lam_fv(t_fv, fs, with_u);
        d.lam_fv(nb_fv, fam, with_t)
    };
    d.declare_theorem(p.hall_mem_union_over_congr, ty, value)
}

/// `Nat.Hall.card_unionOver_congr : ∀ nb t t',
/// (∀ i, Eq Bool (memB t i) (memB t' i)) →
/// Eq Nat (card (unionOver nb t)) (card (unionOver nb t'))`.
///
/// [`declare_mem_union_over_congr`] fed to `Nat.Finset.card_congr_of_memB`
/// (ADR-1614), which is exactly the lemma that survives a difference in the
/// two sets' stored bounds — and the two bounds here DO differ, since
/// `unionBound` sums over `bound t`. This is the form the searched property in
/// Hall's sufficiency has to discharge.
fn declare_card_union_over_congr(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);
    let fam = family_ty(d, &p);

    let nb_fv = d.fresh_fvar();
    let nb = d.kernel().fvar(nb_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let hc_fv = d.fresh_fvar();
    let hc = d.kernel().fvar(hc_fv);

    let hc_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lhs = mem_b(d, &p, t, i);
        let rhs = mem_b(d, &p, u, i);
        let body = d.bool_eq(lhs, rhs);
        d.pi_fv(i_fv, nat, body)
    };

    let cover_t = union_over(d, &p, nb, t);
    let cover_u = union_over(d, &p, nb, u);
    let pointwise = d.lemma(p.hall_mem_union_over_congr, &[nb, t, u, hc]);
    let proof = d.lemma(p.finset_card_congr_of_mem_b, &[cover_t, cover_u, pointwise]);

    let lhs = fs_card(d, &p, cover_t);
    let rhs = fs_card(d, &p, cover_u);
    let goal = d.eq(lhs, rhs);
    let ty = {
        let with_hc = d.arrow(hc_ty, goal);
        let with_u = d.pi_fv(u_fv, fs, with_hc);
        let with_t = d.pi_fv(t_fv, fs, with_u);
        d.pi_fv(nb_fv, fam, with_t)
    };
    let value = {
        let with_hc = d.lam_fv(hc_fv, hc_ty, proof);
        let with_u = d.lam_fv(u_fv, fs, with_hc);
        let with_t = d.lam_fv(t_fv, fs, with_u);
        d.lam_fv(nb_fv, fam, with_t)
    };
    d.declare_theorem(p.hall_card_union_over_congr, ty, value)
}

// ---------------------------------------------------------------------------
// The union under family modification — the piece ADR-1614 said to size.
// ---------------------------------------------------------------------------

/// `fun i => Nat.Finset.sdiff (nb i) u` — the family with `u` deleted from
/// every member, which is what BOTH branches of Hall's induction build.
fn deleted_family(d: &mut NatDev<'_>, p: &NatPrelude, nb: ExprId, u: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let member = d.apply(nb, &[i]);
    let body = d.const_app(p.finset_sdiff, &[member, u]);
    d.lam_fv(i_fv, nat, body)
}

/// `Nat.Hall.memB_unionOver_sdiff : ∀ nb u t v,
/// Eq Bool (memB (unionOver (fun i => sdiff (nb i) u) t) v)
///         (memB (sdiff (unionOver nb t) u) v)`.
///
/// **Deleting commutes with the union**: throwing `u` out of every member of
/// the family and then unioning is the same set as unioning and then throwing
/// `u` out. This is the statement ADR-1614 §4 asked the next lane to size, and
/// it is not a counting argument at all — it is `∃i. (P i ∧ ¬Q) ↔ (∃i. P i) ∧ ¬Q`,
/// which holds because the deleted set does not depend on the index.
///
/// The bounds do NOT match up incidentally: `bound (sdiff s u)` IS `bound s`,
/// so the modified family has the same `unionBound`. Nothing here relies on
/// that — the proof is pointwise — but it is why `card` follows in one step.
fn declare_mem_union_over_sdiff(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);
    let fam = family_ty(d, &p);
    let tru = d.bool_true();

    let nb_fv = d.fresh_fvar();
    let nb = d.kernel().fvar(nb_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);

    let nb_del = deleted_family(d, &p, nb, u);
    let cover_del = union_over(d, &p, nb_del, t);
    let cover = union_over(d, &p, nb, t);
    let del_cover = d.const_app(p.finset_sdiff, &[cover, u]);

    let lhs = mem_b(d, &p, cover_del, v);
    let rhs = mem_b(d, &p, del_cover, v);

    // `union of the deleted family  ⟹  deletion of the union`.
    let fwd = {
        let hyp_ty = d.bool_eq(lhs, tru);
        let goal = d.bool_eq(rhs, tru);
        let ha_fv = d.fresh_fvar();
        let ha = d.kernel().fvar(ha_fv);

        let found = d.lemma(p.hall_mem_union_over_elim, &[nb_del, t, v, ha]);
        let witness_pred = union_witness_pred(d, &p, nb_del, t, v);
        let minor = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let in_t = mem_true(d, &p, t, k);
            let del_member = d.apply(nb_del, &[k]);
            let holds = mem_true(d, &p, del_member, v);
            let hw_ty = d.const_app(p.logic.and, &[in_t, holds]);
            let hw_fv = d.fresh_fvar();
            let hw = d.kernel().fvar(hw_fv);

            let hi = and_left(d, in_t, holds, hw);
            let hv = and_right(d, in_t, holds, hw);

            let member = d.apply(nb, &[k]);
            // `nb_del k` beta-reduces to `sdiff (nb k) u`.
            let split = d.lemma(p.finset_mem_b_sdiff_elim, &[member, u, v, hv]);
            let member_true = mem_true(d, &p, member, v);
            let mem_u = mem_b(d, &p, u, v);
            let fal = d.bool_false();
            let u_false = d.bool_eq(mem_u, fal);
            let in_member = and_left(d, member_true, u_false, split);
            let off_u = and_right(d, member_true, u_false, split);

            let placed = d.lemma(p.hall_mem_union_over, &[nb, t, k, v, hi, in_member]);
            let body = d.lemma(p.finset_mem_b_sdiff_intro, &[cover, u, v, placed, off_u]);
            let with_hw = d.lam_fv(hw_fv, hw_ty, body);
            d.lam_fv(k_fv, nat, with_hw)
        };
        let body = exists_elim_nat(d, &p, witness_pred, goal, minor, found);
        d.lam_fv(ha_fv, hyp_ty, body)
    };

    // `deletion of the union  ⟹  union of the deleted family`.
    let bwd = {
        let hyp_ty = d.bool_eq(rhs, tru);
        let goal = d.bool_eq(lhs, tru);
        let hb_fv = d.fresh_fvar();
        let hb = d.kernel().fvar(hb_fv);

        let split = d.lemma(p.finset_mem_b_sdiff_elim, &[cover, u, v, hb]);
        let cover_true = mem_true(d, &p, cover, v);
        let mem_u = mem_b(d, &p, u, v);
        let fal = d.bool_false();
        let u_false = d.bool_eq(mem_u, fal);
        let in_cover = and_left(d, cover_true, u_false, split);
        let off_u = and_right(d, cover_true, u_false, split);

        let found = d.lemma(p.hall_mem_union_over_elim, &[nb, t, v, in_cover]);
        let witness_pred = union_witness_pred(d, &p, nb, t, v);
        let minor = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let in_t = mem_true(d, &p, t, k);
            let member = d.apply(nb, &[k]);
            let holds = mem_true(d, &p, member, v);
            let hw_ty = d.const_app(p.logic.and, &[in_t, holds]);
            let hw_fv = d.fresh_fvar();
            let hw = d.kernel().fvar(hw_fv);

            let hi = and_left(d, in_t, holds, hw);
            let hv = and_right(d, in_t, holds, hw);
            let deleted = d.lemma(p.finset_mem_b_sdiff_intro, &[member, u, v, hv, off_u]);
            let body = d.lemma(p.hall_mem_union_over, &[nb_del, t, k, v, hi, deleted]);
            let with_hw = d.lam_fv(hw_fv, hw_ty, body);
            d.lam_fv(k_fv, nat, with_hw)
        };
        let body = exists_elim_nat(d, &p, witness_pred, goal, minor, found);
        d.lam_fv(hb_fv, hyp_ty, body)
    };

    let proof = bool_eq_of_iff(d, &p, lhs, rhs, fwd, bwd);
    let goal = d.bool_eq(lhs, rhs);

    let ty = {
        let with_v = d.pi_fv(v_fv, nat, goal);
        let with_t = d.pi_fv(t_fv, fs, with_v);
        let with_u = d.pi_fv(u_fv, fs, with_t);
        d.pi_fv(nb_fv, fam, with_u)
    };
    let value = {
        let with_v = d.lam_fv(v_fv, nat, proof);
        let with_t = d.lam_fv(t_fv, fs, with_v);
        let with_u = d.lam_fv(u_fv, fs, with_t);
        d.lam_fv(nb_fv, fam, with_u)
    };
    d.declare_theorem(p.hall_mem_union_over_sdiff, ty, value)
}

/// `Nat.Hall.card_unionOver_sdiff : ∀ nb u t,
/// Eq Nat (card (unionOver (fun i => sdiff (nb i) u) t))
///        (card (sdiff (unionOver nb t) u))`.
fn declare_card_union_over_sdiff(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let fs = finset_ty(d, &p);
    let fam = family_ty(d, &p);

    let nb_fv = d.fresh_fvar();
    let nb = d.kernel().fvar(nb_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    let nb_del = deleted_family(d, &p, nb, u);
    let cover_del = union_over(d, &p, nb_del, t);
    let cover = union_over(d, &p, nb, t);
    let del_cover = d.const_app(p.finset_sdiff, &[cover, u]);

    let pointwise = d.lemma(p.hall_mem_union_over_sdiff, &[nb, u, t]);
    let proof = d.lemma(
        p.finset_card_congr_of_mem_b,
        &[cover_del, del_cover, pointwise],
    );

    let lhs = fs_card(d, &p, cover_del);
    let rhs = fs_card(d, &p, del_cover);
    let goal = d.eq(lhs, rhs);
    let ty = {
        let with_t = d.pi_fv(t_fv, fs, goal);
        let with_u = d.pi_fv(u_fv, fs, with_t);
        d.pi_fv(nb_fv, fam, with_u)
    };
    let value = {
        let with_t = d.lam_fv(t_fv, fs, proof);
        let with_u = d.lam_fv(u_fv, fs, with_t);
        d.lam_fv(nb_fv, fam, with_u)
    };
    d.declare_theorem(p.hall_card_union_over_sdiff, ty, value)
}

/// `Nat.Hall.card_le_card_unionOver_sdiff_add : ∀ nb u t,
/// Le (card (unionOver nb t))
///    (add (card (unionOver (fun i => sdiff (nb i) u) t)) (card u))`.
///
/// **The deficiency inequality**, and the whole reason this lane exists.
/// Hall's inductive step deletes a critical subfamily's union `u` from every
/// member and must re-establish Hall's condition for what is left; the count
/// it needs is exactly this — the union of the DELETED family loses at most
/// `card u` from the union of the original. `Nat.sub` is truncated, so the
/// statement is additive.
///
/// Two lemmas, in this order: [`declare_card_union_over_sdiff`] moves the
/// deletion outside the union, and `Nat.Finset.card_le_card_sdiff_add` counts
/// a single deletion. Neither existed before this lane; between them the
/// counting obstruction ADR-1614 §4 named is discharged.
fn declare_card_le_union_over_sdiff(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let fs = finset_ty(d, &p);
    let fam = family_ty(d, &p);

    let nb_fv = d.fresh_fvar();
    let nb = d.kernel().fvar(nb_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    let nb_del = deleted_family(d, &p, nb, u);
    let cover_del = union_over(d, &p, nb_del, t);
    let cover = union_over(d, &p, nb, t);
    let del_cover = d.const_app(p.finset_sdiff, &[cover, u]);

    let card_cover = fs_card(d, &p, cover);
    let card_del_cover = fs_card(d, &p, del_cover);
    let card_cover_del = fs_card(d, &p, cover_del);
    let card_u = fs_card(d, &p, u);

    let base = d.lemma(p.finset_card_le_card_sdiff_add, &[cover, u]);
    let swap = d.lemma(p.hall_card_union_over_sdiff, &[nb, u, t]);
    let back = d.symm(card_cover_del, card_del_cover, swap);
    let motive = d.eq_motive(card_del_cover, &|d, x| {
        let rhs = d.add(x, card_u);
        d.le(card_cover, rhs)
    });
    let proof = d.transport(card_del_cover, motive, base, card_cover_del, back);

    let ty = {
        let rhs = d.add(card_cover_del, card_u);
        let concl = d.le(card_cover, rhs);
        let with_t = d.pi_fv(t_fv, fs, concl);
        let with_u = d.pi_fv(u_fv, fs, with_t);
        d.pi_fv(nb_fv, fam, with_u)
    };
    let value = {
        let with_t = d.lam_fv(t_fv, fs, proof);
        let with_u = d.lam_fv(u_fv, fs, with_t);
        d.lam_fv(nb_fv, fam, with_u)
    };
    d.declare_theorem(p.hall_card_le_card_union_over_sdiff_add, ty, value)
}

pub(super) fn declare_hall_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_definitions(d, p)?;
    declare_any_below_intro(d, p)?;
    declare_mem_union_over(d, p)?;
    declare_necessity(d, p)?;
    declare_any_below_witness(d, p)?;
    declare_mem_union_over_elim(d, p)?;
    declare_mem_union_over_congr(d, p)?;
    declare_card_union_over_congr(d, p)?;
    declare_mem_union_over_sdiff(d, p)?;
    declare_card_union_over_sdiff(d, p)?;
    declare_card_le_union_over_sdiff(d, p)?;
    Ok(())
}
