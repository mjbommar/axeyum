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
pub(super) fn declare_hall_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_definitions(d, p)?;
    declare_any_below_intro(d, p)?;
    declare_mem_union_over(d, p)?;
    declare_necessity(d, p)?;
    Ok(())
}
