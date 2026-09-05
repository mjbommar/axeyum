//! Hall's marriage theorem, the SUFFICIENCY direction (ADR-1630).
//!
//! `hall.rs` proves necessity (`Nat.Hall.hallCondition_of_isMatching`) and
//! ADR-1614/ADR-1623 discharged the three obstructions the sufficiency
//! direction was blocked on. What was left was the bottom of the induction:
//! nothing turned a positive `card` into a member, and the empty set and the
//! singleton carried no lemmas at all. `finset_singleton.rs` (this lane) fixed
//! that; this file spends it.
//!
//! ```text
//! Nat.Hall.isMatching_congr
//!   : ∀ s s' nb f, (∀ i, memB s i = memB s' i) →
//!     IsMatching s nb f → IsMatching s' nb f
//! Nat.Hall.exists_isMatching_of_card_le_zero
//!   : ∀ s nb, card s ≤ 0 → ∃ f, IsMatching s nb f
//! Nat.Hall.exists_isMatching_singleton
//!   : ∀ a nb, HallCondition (singleton a) nb →
//!     ∃ f, IsMatching (singleton a) nb f
//! ```
//!
//! # Why the base case is not trivial
//!
//! At a one-element index set the matching is a CONSTANT function, and the
//! whole content is producing the value it is constant at. `HallCondition` is
//! a counting statement; it says `1 ≤ card (unionOver nb (singleton a))` and
//! nothing about which value is in there. Turning that count back into a value
//! is `Nat.Finset.exists_memB_of_card_pos`, and locating the value inside
//! `nb a` rather than merely inside the union is
//! `Nat.Hall.memB_unionOver_elim` followed by
//! `Nat.Finset.eq_of_memB_singleton` — the index the elimination hands back is
//! *some* member of `singleton a`, and only the singleton lemma says that is
//! `a`.
//!
//! `Le (card (singleton a)) (card U)` becomes `Lt zero (card U)` with no
//! bridging lemma: `Nat.lt x y` is `Nat.le (succ x) y` by δ and
//! `Nat.Finset.card_singleton` gives `succ zero` on the nose.

#![allow(clippy::many_single_char_names)]

use super::NatPrelude;
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

// ---------------------------------------------------------------------------
// Term builders (a private copy, per this prelude's per-file convention).
// ---------------------------------------------------------------------------

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

/// `Nat.Finset.singleton a`.
fn singleton(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId) -> ExprId {
    d.const_app(p.finset_singleton, &[a])
}

/// `Nat.Hall.unionOver nb t`.
fn union_over(d: &mut NatDev<'_>, p: &NatPrelude, nb: ExprId, t: ExprId) -> ExprId {
    d.const_app(p.hall_union_over, &[nb, t])
}

/// `IsMatching`'s FIRST conjunct at `(s, nb, f)`, written out so `and_left`
/// can be offered the component type the definition names.
fn maps_into_ty(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, nb: ExprId, f: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hyp = mem_true(d, &p, s, i);
    let member = d.apply(nb, &[i]);
    let fi = d.apply(f, &[i]);
    let concl = mem_true(d, &p, member, fi);
    let step = d.arrow(hyp, concl);
    d.pi_fv(i_fv, nat, step)
}

/// `IsMatching`'s SECOND conjunct at `(s, nb, f)`.
fn inj_on_ty(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, f: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
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

/// `Exists.{1} (Nat → Nat) pred` — the shape of every conclusion here.
/// `Nat → Nat` is `Sort 1`, the same level as `Nat` itself, so the universe
/// argument is the same `1` the `Nat` existentials use.
fn exists_choice(d: &mut NatDev<'_>, p: &NatPrelude, pred: ExprId) -> ExprId {
    let one = d.level_one();
    let ch = choice_ty(d);
    let ex = d.kernel().const_(p.logic.exists_, vec![one]);
    d.apply(ex, &[ch, pred])
}

/// `Exists.intro.{1} (Nat → Nat) pred w h`.
fn exists_intro_choice(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pred: ExprId,
    w: ExprId,
    h: ExprId,
) -> ExprId {
    let one = d.level_one();
    let ch = choice_ty(d);
    let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
    d.apply(intro, &[ch, pred, w, h])
}

/// `fun f => Nat.Hall.IsMatching s nb f` — the goal predicate.
fn matching_pred(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, nb: ExprId) -> ExprId {
    let p = *p;
    let ch = choice_ty(d);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let body = d.const_app(p.hall_is_matching, &[s, nb, f]);
    d.lam_fv(f_fv, ch, body)
}

/// `Exists (fun f => IsMatching s nb f)`.
fn exists_matching(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, nb: ExprId) -> ExprId {
    let pred = matching_pred(d, p, s, nb);
    exists_choice(d, p, pred)
}

/// `And.intro` at the two `IsMatching` conjuncts, packaged as the definition's
/// own body so `Exists.intro` can be handed a proof of
/// `IsMatching s nb f` directly.
fn is_matching_intro(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    s: ExprId,
    nb: ExprId,
    f: ExprId,
    maps: ExprId,
    inj: ExprId,
) -> ExprId {
    let p = *p;
    let maps_ty = maps_into_ty(d, &p, s, nb, f);
    let inj_ty = inj_on_ty(d, &p, s, f);
    d.const_app(p.logic.and_intro, &[maps_ty, inj_ty, maps, inj])
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

/// `fun i => And (Eq Bool (memB t i) true) (Eq Bool (memB (nb i) v) true)` —
/// `Nat.Hall.memB_unionOver_elim`'s payload. The index bound is NOT part of
/// it; see `hall.rs`'s `union_witness_pred`.
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

/// `fun k => And (Lt k (bound s)) (Eq Bool (memB s k) true)` —
/// `Nat.Finset.exists_memB_of_card_pos`'s payload.
fn member_witness_pred(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let bs = fs_bound(d, &p, s);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let lt = d.lt(k, bs);
    let mk = mem_b(d, &p, s, k);
    let tru = d.bool_true();
    let is_true = d.bool_eq(mk, tru);
    let body = d.const_app(p.logic.and, &[lt, is_true]);
    d.lam_fv(k_fv, nat, body)
}

// ---------------------------------------------------------------------------
// A matching depends only on the index set's MEMBERS.
// ---------------------------------------------------------------------------

/// `Nat.Hall.isMatching_congr : ∀ s s' nb f,
/// (∀ i, Eq Bool (memB s i) (memB s' i)) → IsMatching s nb f →
/// IsMatching s' nb f`.
///
/// The index-set twin of `Nat.Hall.memB_unionOver_congr`. Both `IsMatching`
/// conjuncts mention the index set ONLY in hypothesis position, so the whole
/// proof is composing the pointwise equation with each incoming membership
/// proof — no counting, and unlike `card_unionOver_congr` no appeal to
/// `card_congr_of_memB`, because nothing here is counted.
///
/// Needed because Hall's inductive step builds its matching on
/// `union t (sdiff s t)`, which has the same members as `s` but a different
/// stored bound; without this the result cannot be moved back to `s`.
fn declare_is_matching_congr(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);
    let fam = family_ty(d, &p);
    let ch = choice_ty(d);
    let tru = d.bool_true();

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let s2_fv = d.fresh_fvar();
    let s2 = d.kernel().fvar(s2_fv);
    let nb_fv = d.fresh_fvar();
    let nb = d.kernel().fvar(nb_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    let hcongr_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let l = mem_b(d, &p, s, i);
        let r = mem_b(d, &p, s2, i);
        let body = d.bool_eq(l, r);
        d.pi_fv(i_fv, nat, body)
    };
    let hcongr_fv = d.fresh_fvar();
    let hcongr = d.kernel().fvar(hcongr_fv);

    let hm_ty = d.const_app(p.hall_is_matching, &[s, nb, f]);
    let hm_fv = d.fresh_fvar();
    let hm = d.kernel().fvar(hm_fv);

    let maps_ty = maps_into_ty(d, &p, s, nb, f);
    let inj_ty = inj_on_ty(d, &p, s, f);
    let maps = and_left(d, maps_ty, inj_ty, hm);
    let inj = and_right(d, maps_ty, inj_ty, hm);

    // `memB s' i = true` becomes `memB s i = true` by the pointwise equation.
    let back_at = |d: &mut NatDev<'_>, i: ExprId, h: ExprId| -> ExprId {
        let l = mem_b(d, &p, s, i);
        let r = mem_b(d, &p, s2, i);
        let step = d.apply(hcongr, &[i]);
        d.bool_trans(l, r, tru, step, h)
    };

    let new_maps = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let h_ty = mem_true(d, &p, s2, i);
        let carried = back_at(d, i, h);
        let body = d.apply(maps, &[i, carried]);
        let with_h = d.lam_fv(h_fv, h_ty, body);
        d.lam_fv(i_fv, nat, with_h)
    };
    let new_inj = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let hi_ty = mem_true(d, &p, s2, i);
        let hj_fv = d.fresh_fvar();
        let hj = d.kernel().fvar(hj_fv);
        let hj_ty = mem_true(d, &p, s2, j);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let fi = d.apply(f, &[i]);
        let fj = d.apply(f, &[j]);
        let heq_ty = d.eq(fi, fj);
        let ci = back_at(d, i, hi);
        let cj = back_at(d, j, hj);
        let body = d.apply(inj, &[i, j, ci, cj, heq]);
        let s4 = d.lam_fv(heq_fv, heq_ty, body);
        let s3 = d.lam_fv(hj_fv, hj_ty, s4);
        let s2t = d.lam_fv(hi_fv, hi_ty, s3);
        let inner = d.lam_fv(j_fv, nat, s2t);
        d.lam_fv(i_fv, nat, inner)
    };

    let built = is_matching_intro(d, &p, s2, nb, f, new_maps, new_inj);
    let concl = d.const_app(p.hall_is_matching, &[s2, nb, f]);

    let ty = {
        let s6 = d.arrow(hm_ty, concl);
        let s5 = d.arrow(hcongr_ty, s6);
        let s4 = d.pi_fv(f_fv, ch, s5);
        let s3 = d.pi_fv(nb_fv, fam, s4);
        let s2p = d.pi_fv(s2_fv, fs, s3);
        d.pi_fv(s_fv, fs, s2p)
    };
    let value = {
        let s6 = d.lam_fv(hm_fv, hm_ty, built);
        let s5 = d.lam_fv(hcongr_fv, hcongr_ty, s6);
        let s4 = d.lam_fv(f_fv, ch, s5);
        let s3 = d.lam_fv(nb_fv, fam, s4);
        let s2p = d.lam_fv(s2_fv, fs, s3);
        d.lam_fv(s_fv, fs, s2p)
    };
    d.declare_theorem(p.hall_is_matching_congr, ty, value)
}

// ---------------------------------------------------------------------------
// The bottom of the induction.
// ---------------------------------------------------------------------------

/// `Nat.Hall.exists_isMatching_of_card_le_zero : ∀ s nb, Le (card s) zero →
/// Exists (fun f => IsMatching s nb f)`.
///
/// The witness is the constant `fun _ => zero` and both `IsMatching` conjuncts
/// are vacuous: `Nat.Finset.card_pos_of_memB` turns any membership hypothesis
/// into `Lt zero (card s)`, which against `Le (card s) zero` is
/// `Lt zero zero`.
///
/// Stated at `Le (card s) zero` rather than `Eq Nat (card s) zero` because
/// that is what the induction's decision produces —
/// `Nat.lt_or_ge zero (card s)` returns `Le (card s) zero` on the right — and
/// this prelude has no `Nat.le_zero` to convert it (checked: `--name-like
/// Nat.le_zero` ABSENT at 3,093 declarations).
fn declare_empty_case(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);
    let fam = family_ty(d, &p);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let nb_fv = d.fresh_fvar();
    let nb = d.kernel().fvar(nb_fv);

    let zero = d.zero();
    let card = fs_card(d, &p, s);
    let h_ty = d.le(card, zero);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let constant = {
        let i_fv = d.fresh_fvar();
        let z = d.zero();
        d.lam_fv(i_fv, nat, z)
    };

    // `memB s i = true ⊢ False`.
    let refute = |d: &mut NatDev<'_>, i: ExprId, hi: ExprId| -> ExprId {
        let pos = d.lemma(p.finset_card_pos_of_mem_b, &[s, i, hi]);
        let z = d.zero();
        let one = d.num(1);
        let c = fs_card(d, &p, s);
        // `Lt zero (card s)` IS `Le 1 (card s)`; chaining with `card s ≤ 0`
        // gives `Le 1 0`, which IS `Lt zero zero`.
        let chained = d.lemma(p.le_trans, &[one, c, z, pos, h]);
        d.lemma(p.lt_irrefl, &[z, chained])
    };

    let maps = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let hi_ty = mem_true(d, &p, s, i);
        let member = d.apply(nb, &[i]);
        let fi = d.apply(constant, &[i]);
        let goal = mem_true(d, &p, member, fi);
        let absurd = refute(d, i, hi);
        let body = false_elim(d, &p, goal, absurd);
        let with_hi = d.lam_fv(hi_fv, hi_ty, body);
        d.lam_fv(i_fv, nat, with_hi)
    };
    let inj = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let hi_ty = mem_true(d, &p, s, i);
        let hj_fv = d.fresh_fvar();
        let hj_ty = mem_true(d, &p, s, j);
        let heq_fv = d.fresh_fvar();
        let fi = d.apply(constant, &[i]);
        let fj = d.apply(constant, &[j]);
        let heq_ty = d.eq(fi, fj);
        let goal = d.eq(i, j);
        let absurd = refute(d, i, hi);
        let body = false_elim(d, &p, goal, absurd);
        let s4 = d.lam_fv(heq_fv, heq_ty, body);
        let s3 = d.lam_fv(hj_fv, hj_ty, s4);
        let s2 = d.lam_fv(hi_fv, hi_ty, s3);
        let inner = d.lam_fv(j_fv, nat, s2);
        d.lam_fv(i_fv, nat, inner)
    };

    let built = is_matching_intro(d, &p, s, nb, constant, maps, inj);
    let pred = matching_pred(d, &p, s, nb);
    let proof = exists_intro_choice(d, &p, pred, constant, built);
    let goal = exists_matching(d, &p, s, nb);

    let ty = {
        let s3 = d.arrow(h_ty, goal);
        let s2 = d.pi_fv(nb_fv, fam, s3);
        d.pi_fv(s_fv, fs, s2)
    };
    let value = {
        let s3 = d.lam_fv(h_fv, h_ty, proof);
        let s2 = d.lam_fv(nb_fv, fam, s3);
        d.lam_fv(s_fv, fs, s2)
    };
    d.declare_theorem(p.hall_exists_is_matching_of_card_le_zero, ty, value)
}

/// `Nat.Hall.exists_isMatching_singleton : ∀ a nb,
/// HallCondition (singleton a) nb →
/// Exists (fun f => IsMatching (singleton a) nb f)`.
///
/// **Hall's base case.** `HallCondition` at `t := singleton a` — the inclusion
/// premise is the identity — gives
/// `Le (card (singleton a)) (card (unionOver nb (singleton a)))`;
/// `Nat.Finset.card_singleton` rewrites the left side to `succ zero`, and
/// `Le (succ zero) x` IS `Lt zero x`. Then
/// `Nat.Finset.exists_memB_of_card_pos` produces a value `v` in the union,
/// `Nat.Hall.memB_unionOver_elim` produces an index `i` of the singleton with
/// `v ∈ nb i`, and `Nat.Finset.eq_of_memB_singleton` says `i = a`.
///
/// The matching is `fun _ => v`. Injectivity needs no hypothesis about `v` at
/// all: any two indices of a singleton are both `a`, hence equal.
fn declare_singleton_case(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fam = family_ty(d, &p);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let nb_fv = d.fresh_fvar();
    let nb = d.kernel().fvar(nb_fv);

    let sa = singleton(d, &p, a);
    let hc_ty = d.const_app(p.hall_condition, &[sa, nb]);
    let hc_fv = d.fresh_fvar();
    let hc = d.kernel().fvar(hc_fv);

    let goal = exists_matching(d, &p, sa, nb);
    let cover = union_over(d, &p, nb, sa);

    // `HallCondition` at the singleton itself; the inclusion is the identity.
    let self_sub = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let h_ty = mem_true(d, &p, sa, i);
        let with_h = d.lam_fv(h_fv, h_ty, h);
        d.lam_fv(i_fv, nat, with_h)
    };
    let counted = d.apply(hc, &[sa, self_sub]);
    // `card (singleton a) = succ zero`, so the count is a positivity fact.
    let card_one = d.lemma(p.finset_card_singleton, &[a]);
    let card_sa = fs_card(d, &p, sa);
    let card_cover = fs_card(d, &p, cover);
    let motive = d.eq_motive(card_sa, &|d, x| d.le(x, card_cover));
    let one = d.num(1);
    let positive = d.transport(card_sa, motive, counted, one, card_one);

    let found_value = d.lemma(p.finset_exists_mem_b_of_card_pos, &[cover, positive]);
    let value_pred = member_witness_pred(d, &p, cover);

    let handle_value = {
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let hv_fv = d.fresh_fvar();
        let hv = d.kernel().fvar(hv_fv);
        let bc = fs_bound(d, &p, cover);
        let lt_ty = d.lt(v, bc);
        let in_cover_ty = mem_true(d, &p, cover, v);
        let hv_ty = d.const_app(p.logic.and, &[lt_ty, in_cover_ty]);
        let in_cover = and_right(d, lt_ty, in_cover_ty, hv);

        let found_index = d.lemma(p.hall_mem_union_over_elim, &[nb, sa, v, in_cover]);
        let index_pred = union_witness_pred(d, &p, nb, sa, v);

        let handle_index = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hi_fv = d.fresh_fvar();
            let hi = d.kernel().fvar(hi_fv);
            let in_sa_ty = mem_true(d, &p, sa, i);
            let member_i = d.apply(nb, &[i]);
            let holds_ty = mem_true(d, &p, member_i, v);
            let hi_ty = d.const_app(p.logic.and, &[in_sa_ty, holds_ty]);
            let in_sa = and_left(d, in_sa_ty, holds_ty, hi);
            let holds = and_right(d, in_sa_ty, holds_ty, hi);

            // `i = a`, so the value lives in `nb a`.
            let i_is_a = d.lemma(p.finset_eq_of_mem_b_singleton, &[a, i, in_sa]);
            let at_a = {
                let motive = d.eq_motive(i, &|d, x| {
                    let member = d.apply(nb, &[x]);
                    mem_true(d, &p, member, v)
                });
                d.transport(i, motive, holds, a, i_is_a)
            };

            let constant = {
                let k_fv = d.fresh_fvar();
                d.lam_fv(k_fv, nat, v)
            };

            let maps = {
                let j_fv = d.fresh_fvar();
                let j = d.kernel().fvar(j_fv);
                let hj_fv = d.fresh_fvar();
                let hj = d.kernel().fvar(hj_fv);
                let hj_ty = mem_true(d, &p, sa, j);
                let j_is_a = d.lemma(p.finset_eq_of_mem_b_singleton, &[a, j, hj]);
                let a_is_j = d.symm(j, a, j_is_a);
                let motive = d.eq_motive(a, &|d, x| {
                    let member = d.apply(nb, &[x]);
                    mem_true(d, &p, member, v)
                });
                let moved = d.transport(a, motive, at_a, j, a_is_j);
                let with_hj = d.lam_fv(hj_fv, hj_ty, moved);
                d.lam_fv(j_fv, nat, with_hj)
            };
            let inj = {
                let j_fv = d.fresh_fvar();
                let j = d.kernel().fvar(j_fv);
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let hj_fv = d.fresh_fvar();
                let hj = d.kernel().fvar(hj_fv);
                let hj_ty = mem_true(d, &p, sa, j);
                let hk_fv = d.fresh_fvar();
                let hk = d.kernel().fvar(hk_fv);
                let hk_ty = mem_true(d, &p, sa, k);
                let heq_fv = d.fresh_fvar();
                let fj = d.apply(constant, &[j]);
                let fk = d.apply(constant, &[k]);
                let heq_ty = d.eq(fj, fk);
                let j_is_a = d.lemma(p.finset_eq_of_mem_b_singleton, &[a, j, hj]);
                let k_is_a = d.lemma(p.finset_eq_of_mem_b_singleton, &[a, k, hk]);
                let a_is_k = d.symm(k, a, k_is_a);
                let body = d.trans(j, a, k, j_is_a, a_is_k);
                let s4 = d.lam_fv(heq_fv, heq_ty, body);
                let s3 = d.lam_fv(hk_fv, hk_ty, s4);
                let s2 = d.lam_fv(hj_fv, hj_ty, s3);
                let inner = d.lam_fv(k_fv, nat, s2);
                d.lam_fv(j_fv, nat, inner)
            };

            let built = is_matching_intro(d, &p, sa, nb, constant, maps, inj);
            let pred = matching_pred(d, &p, sa, nb);
            let intro = exists_intro_choice(d, &p, pred, constant, built);
            let with_hi = d.lam_fv(hi_fv, hi_ty, intro);
            d.lam_fv(i_fv, nat, with_hi)
        };

        let body = exists_elim_nat(d, &p, index_pred, goal, handle_index, found_index);
        let with_hv = d.lam_fv(hv_fv, hv_ty, body);
        d.lam_fv(v_fv, nat, with_hv)
    };

    let proof = exists_elim_nat(d, &p, value_pred, goal, handle_value, found_value);

    let ty = {
        let s3 = d.arrow(hc_ty, goal);
        let s2 = d.pi_fv(nb_fv, fam, s3);
        d.pi_fv(a_fv, nat, s2)
    };
    let value = {
        let s3 = d.lam_fv(hc_fv, hc_ty, proof);
        let s2 = d.lam_fv(nb_fv, fam, s3);
        d.lam_fv(a_fv, nat, s2)
    };
    d.declare_theorem(p.hall_exists_is_matching_singleton, ty, value)
}

// ---------------------------------------------------------------------------
// Entry point.
// ---------------------------------------------------------------------------

/// Declare Hall's sufficiency shelf (ADR-1630).
pub(super) fn declare_hall_sufficiency_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_is_matching_congr(d, p)?;
    declare_empty_case(d, p)?;
    declare_singleton_case(d, p)?;
    Ok(())
}
