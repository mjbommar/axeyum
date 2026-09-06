//! Hall's marriage theorem — the statement (ADR-1645).
//!
//! # What this file is
//!
//! The assembly. Everything it composes was landed by earlier slices:
//! necessity (ADR-1608), the subset search and `Nat.strongInduction`
//! (ADR-1614), the counting shelf and the matching glue (ADR-1623), the two
//! base cases (ADR-1630), both branches of the critical-subset split
//! (ADR-1644), and the descent measure (`hall_descent.rs`, this ADR). What
//! remained was to decide the branch, run the induction, and compose.
//!
//! ```text
//! Nat.Hall.sufficient   : ∀ s nb, HallCondition s nb →
//!                         ∃ f, IsMatching s nb f
//! Nat.Hall.marriage_iff : ∀ s nb, HallCondition s nb ↔ ∃ f, IsMatching s nb f
//! ```
//!
//! # The decision, and the four conjuncts it tests
//!
//! `Nat.Finset.anySubset` is the only decision procedure over subsets here, and
//! it takes a `Bool`-valued predicate. `Nat.Hall.criticalB` is that predicate:
//!
//! ```text
//! criticalB s nb t := andB (andB (subsetFixed s t)  (ble 1 (card t)))
//!                          (andB (ble 1 (card (sdiff s t)))
//!                                (ble (card (unionOver nb t)) (card t)))
//! ```
//!
//! Each conjunct is there for one obligation and no other:
//!
//! | conjunct                            | what consumes it                                    |
//! |-------------------------------------|-----------------------------------------------------|
//! | `subsetFixed s t`                   | `t ⊆ s`, via `memB_of_subsetFixed_of_bound_le`      |
//! | `ble 1 (card t)`                    | `card (sdiff s t) < card s` — the SECOND descent     |
//! | `ble 1 (card (sdiff s t))`          | `card t < card s` — the FIRST descent                |
//! | `ble (card (unionOver nb t)) (card t)` | criticality, `hallCondition_sdiff_of_critical`   |
//!
//! **The two positivity conjuncts are not one condition written twice.** They
//! are the two nonemptiness facts the two recursive calls need, and they sit on
//! OPPOSITE sides of the split: without `0 < card t` the critical branch could
//! fire at `t = empty` and recurse on `sdiff s empty`, whose count is `card s`
//! and whose induction therefore does not descend; without
//! `0 < card (sdiff s t)` it could fire at `t = s` and recurse on `t` at the
//! same count. Each is exactly the hypothesis of one descent lemma.
//!
//! **Properness is spelled by the two counts, not by `t ≠ s`.** There is no
//! decidable set equality in play, and none is needed: what the induction wants
//! is a strictly smaller measure on both sides, which is what the descent
//! lemmas deliver from the two positivity facts.
//!
//! # Why the non-critical branch normalises its subset
//!
//! `forallSubset_of_search` concludes only for sets with `Le (bound w) n`, and
//! the `w` handed to `hallCondition_sdiff_singleton_of_strict`'s hypothesis is
//! an arbitrary `Finset` whose STORED bound is unconstrained — `memB`
//! truncates, so a set can carry a bound far above its largest member.
//! `Nat.Finset.restrict` (ADR-1644) is the normalisation: `restrict w (bound s)`
//! has `bound = bound s` by `refl` and the same members, because every member
//! of `w` is a member of `s` and so below `bound s` by `lt_bound_of_memB`.
//! Every fact is then pulled back to `w` through `card_congr_of_memB` and
//! `card_unionOver_congr`.
//!
//! # Why the search's non-membership is turned around rather than reflected
//!
//! The exhaustion rule yields `criticalB s nb w' = false`, and what the branch
//! needs is `card w < card (unionOver nb w)`. Going directly would need
//! `ble a b = false → Lt b a`, a reflection direction this tree does not carry
//! (it has `ble_eq_false_of_lt`, the other way). So the branch decides with
//! `Nat.lt_or_ge` instead: on the strict side it is done, and on the `≥` side it
//! BUILDS `criticalB s nb w' = true` from the four conjuncts and clashes it
//! against the search's `false`. No new reflection lemma, and the four conjuncts
//! are assembled by `Nat.Graph.andB_intro` rather than unfolded.
//!
//! # The two family-weakening lemmas
//!
//! Both branches recurse against a DELETED family — `fun i => sdiff (nb i) u`,
//! for `u` the critical neighbourhood or the committed value's singleton — and
//! then have to hand `Nat.Hall.isMatching_union` a matching into the ORIGINAL
//! family plus the collision fact that the two halves never pick the same
//! value. Both come from `Nat.Finset.memB_sdiff_elim`, which returns exactly
//! the conjunction "in `nb i`" and "not in `u`", and both are landed here as
//! named lemmas because each branch needs both and reading the wrong conjunct
//! out of the pair type-checks as the other lemma.

#![allow(clippy::many_single_char_names)]
#![allow(clippy::too_many_lines)]

use super::NatPrelude;
use super::graph::bool_congr;
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps, bool_true_or_false};
use super::subset_search::nat_to_bool_congr;
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
fn fs_mem(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, i: ExprId) -> ExprId {
    d.const_app(p.finset_mem_b, &[s, i])
}

/// `Eq Bool (Nat.Finset.memB s i) Bool.true`.
fn mem_true(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, i: ExprId) -> ExprId {
    let m = fs_mem(d, p, s, i);
    let t = d.bool_true();
    d.bool_eq(m, t)
}

/// `Eq Bool (Nat.Finset.memB s i) Bool.false`.
fn mem_false(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, i: ExprId) -> ExprId {
    let m = fs_mem(d, p, s, i);
    let f = d.bool_false();
    d.bool_eq(m, f)
}

/// `Nat.Finset.bound s`.
fn fs_bound(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId) -> ExprId {
    d.const_app(p.finset_bound, &[s])
}

/// `Nat.Finset.card s`.
fn fs_card(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId) -> ExprId {
    d.const_app(p.finset_card, &[s])
}

/// `Nat.Finset.sdiff s t`.
fn fs_sdiff(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, t: ExprId) -> ExprId {
    d.const_app(p.finset_sdiff, &[s, t])
}

/// `Nat.Finset.union s t`.
fn fs_union(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, t: ExprId) -> ExprId {
    d.const_app(p.finset_union, &[s, t])
}

/// `Nat.Finset.singleton a`.
fn fs_singleton(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId) -> ExprId {
    d.const_app(p.finset_singleton, &[a])
}

/// `Nat.Finset.restrict s n`.
fn fs_restrict(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.finset_restrict, &[s, n])
}

/// `Nat.Hall.unionOver nb t`.
fn union_over(d: &mut NatDev<'_>, p: &NatPrelude, nb: ExprId, t: ExprId) -> ExprId {
    d.const_app(p.hall_union_over, &[nb, t])
}

/// `Nat.Hall.HallCondition s nb`.
fn hall_condition(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, nb: ExprId) -> ExprId {
    d.const_app(p.hall_condition, &[s, nb])
}

/// `Nat.Hall.IsMatching s nb f`.
fn is_matching(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, nb: ExprId, f: ExprId) -> ExprId {
    d.const_app(p.hall_is_matching, &[s, nb, f])
}

/// `Nat.Graph.andB a b`.
fn and_b(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.graph_and_b, &[a, b])
}

/// `fun i => Nat.Finset.sdiff (nb i) u` — the family with `u` deleted from
/// every member. Written once, because both split lemmas name this exact term
/// in their conclusions and a differently-shaped copy would not match.
fn deleted_family(d: &mut NatDev<'_>, p: &NatPrelude, nb: ExprId, u: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let member = d.apply(nb, &[i]);
    let body = fs_sdiff(d, &p, member, u);
    d.lam_fv(i_fv, nat, body)
}

/// `IsMatching`'s FIRST conjunct at `(s, nb, f)`, so `and_left` can be offered
/// the component type the definition names.
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

/// `IsMatching`'s SECOND conjunct at `(s, f)`.
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

/// `And.intro` at the two `IsMatching` conjuncts.
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

/// `Exists.{1} carrier pred` at a `Sort 1` carrier.
fn exists_at(d: &mut NatDev<'_>, p: &NatPrelude, carrier: ExprId, pred: ExprId) -> ExprId {
    let one = d.level_one();
    let ex = d.kernel().const_(p.logic.exists_, vec![one]);
    d.apply(ex, &[carrier, pred])
}

/// `Exists.rec.{1}` at a `Sort 1` carrier, into a `Prop` goal.
#[allow(clippy::too_many_arguments)]
fn exists_elim_at(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    carrier: ExprId,
    pred: ExprId,
    goal: ExprId,
    minor: ExprId,
    proof: ExprId,
) -> ExprId {
    let one = d.level_one();
    let ex_ty = exists_at(d, p, carrier, pred);
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, ex_ty, goal, BinderInfo::Default);
    let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
    d.apply(rec, &[carrier, pred, motive, minor, proof])
}

/// `Exists.intro.{1}` at a `Sort 1` carrier.
fn exists_intro_at(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    carrier: ExprId,
    pred: ExprId,
    w: ExprId,
    h: ExprId,
) -> ExprId {
    let one = d.level_one();
    let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
    d.apply(intro, &[carrier, pred, w, h])
}

/// `fun f => Nat.Hall.IsMatching s nb f` — the goal predicate.
fn matching_pred(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, nb: ExprId) -> ExprId {
    let p = *p;
    let ch = choice_ty(d);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let body = is_matching(d, &p, s, nb, f);
    d.lam_fv(f_fv, ch, body)
}

/// `Exists (fun f => IsMatching s nb f)`.
fn exists_matching(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, nb: ExprId) -> ExprId {
    let ch = choice_ty(d);
    let pred = matching_pred(d, p, s, nb);
    exists_at(d, p, ch, pred)
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
    let is_true = mem_true(d, &p, s, k);
    let body = d.const_app(p.logic.and, &[lt, is_true]);
    d.lam_fv(k_fv, nat, body)
}

/// `fun i => And (memB t i = true) (memB (nb i) v = true)` —
/// `Nat.Hall.memB_unionOver_elim`'s payload.
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

/// `h : Eq Nat a b`, `hle : Le a c  ⊢  Le b c`.
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

/// `h : Eq Nat b c`, `hle : Le a b  ⊢  Le a c`.
fn le_rewrite_right(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    h: ExprId,
    hle: ExprId,
) -> ExprId {
    let motive = d.eq_motive(b, &|d, x| d.le(a, x));
    d.transport(b, motive, hle, c, h)
}

/// `h : Eq Nat b c`, `hlt : Lt a b  ⊢  Lt a c`.
fn lt_rewrite_right(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    h: ExprId,
    hlt: ExprId,
) -> ExprId {
    let motive = d.eq_motive(b, &|d, x| d.lt(a, x));
    d.transport(b, motive, hlt, c, h)
}

// ---------------------------------------------------------------------------
// The complement's members depend only on the subtracted set's members.
// ---------------------------------------------------------------------------

/// `Nat.Finset.memB_sdiff_congr : ∀ s u v,
/// (∀ i, Eq Bool (memB u i) (memB v i)) →
/// ∀ i, Eq Bool (memB (sdiff s u) i) (memB (sdiff s v) i)`.
///
/// The one place [`declare_critical_b_congr`] has to descend into a set
/// CONSTRUCTOR rather than pass a pointwise equation straight through: the
/// search predicate counts `sdiff s t`, and a pointwise equation on `t` has to
/// become one on `sdiff s t` before `card_congr_of_memB` can be applied.
///
/// Proved by deciding both sides with `bool_true_or_false` and moving each
/// `true` across with `memB_sdiff_elim` + `memB_sdiff_intro`, NOT by unfolding
/// `Nat.setDiff`. The unfolding route needs the exact `Bool.rec` shape
/// `setDiff` reduces to — including whether the inner negation is spelled as
/// `Nat.Graph.notB` or as a raw selector — and a lemma that depends on that is
/// one refactor away from a `TypeMismatch` naming nothing. The intro/elim pair
/// is the interface `finset.rs` deliberately provides for exactly this.
fn declare_mem_b_sdiff_congr(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);
    let tr = d.bool_true();
    let fa = d.bool_false();

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);

    let h_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let a = fs_mem(d, &p, u, i);
        let b = fs_mem(d, &p, v, i);
        let body = d.bool_eq(a, b);
        d.pi_fv(i_fv, nat, body)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let du = fs_sdiff(d, &p, s, u);
    let dv = fs_sdiff(d, &p, s, v);
    let lhs = fs_mem(d, &p, du, i);
    let rhs = fs_mem(d, &p, dv, i);
    let goal = d.bool_eq(lhs, rhs);

    // `memB (sdiff s from) i = true  ⊢  memB (sdiff s to) i = true`, with
    // `hstep : memB to i = memB from i` supplying the direction.
    let carry =
        |d: &mut NatDev<'_>, from: ExprId, to: ExprId, hstep: ExprId, hm: ExprId| -> ExprId {
            let in_s = mem_true(d, &p, s, i);
            let not_from = mem_false(d, &p, from, i);
            let pair = d.lemma(p.finset_mem_b_sdiff_elim, &[s, from, i, hm]);
            let ms = and_left(d, in_s, not_from, pair);
            let nf = and_right(d, in_s, not_from, pair);
            let m_to = fs_mem(d, &p, to, i);
            let m_from = fs_mem(d, &p, from, i);
            let nt = d.bool_trans(m_to, m_from, fa, hstep, nf);
            d.lemma(p.finset_mem_b_sdiff_intro, &[s, to, i, ms, nt])
        };

    let mu = fs_mem(d, &p, u, i);
    let mv = fs_mem(d, &p, v, i);
    let step_uv = d.apply(h, &[i]);
    let step_vu = d.bool_symm(mu, mv, step_uv);

    let decided_u = bool_true_or_false(d, &p, lhs);
    let u_true_ty = d.bool_eq(lhs, tr);
    let u_false_ty = d.bool_eq(lhs, fa);

    // `sdiff s u` holds at `i`: so does `sdiff s v`, and both sides are `true`.
    let on_u_true = {
        let hm_fv = d.fresh_fvar();
        let hm = d.kernel().fvar(hm_fv);
        let moved = carry(d, u, v, step_vu, hm);
        let back = d.bool_symm(rhs, tr, moved);
        let body = d.bool_trans(lhs, tr, rhs, hm, back);
        d.lam_fv(hm_fv, u_true_ty, body)
    };
    // It does not: decide the other side, and refute its `true`.
    let on_u_false = {
        let hm_fv = d.fresh_fvar();
        let hm = d.kernel().fvar(hm_fv);
        let decided_v = bool_true_or_false(d, &p, rhs);
        let v_true_ty = d.bool_eq(rhs, tr);
        let v_false_ty = d.bool_eq(rhs, fa);
        let on_v_true = {
            let hn_fv = d.fresh_fvar();
            let hn = d.kernel().fvar(hn_fv);
            let moved = carry(d, v, u, step_uv, hn);
            let flipped = d.bool_symm(lhs, fa, hm);
            let clash = d.bool_trans(fa, lhs, tr, flipped, moved);
            let body = d.false_true_elim(goal, clash);
            d.lam_fv(hn_fv, v_true_ty, body)
        };
        let on_v_false = {
            let hn_fv = d.fresh_fvar();
            let hn = d.kernel().fvar(hn_fv);
            let back = d.bool_symm(rhs, fa, hn);
            let body = d.bool_trans(lhs, fa, rhs, hm, back);
            d.lam_fv(hn_fv, v_false_ty, body)
        };
        let answered = or_elim(
            d, &p, v_true_ty, v_false_ty, goal, on_v_true, on_v_false, decided_v,
        );
        d.lam_fv(hm_fv, u_false_ty, answered)
    };
    let proof = or_elim(
        d, &p, u_true_ty, u_false_ty, goal, on_u_true, on_u_false, decided_u,
    );

    let ty = {
        let with_i = d.pi_fv(i_fv, nat, goal);
        let with_h = d.arrow(h_ty, with_i);
        let s4 = d.pi_fv(v_fv, fs, with_h);
        let s3 = d.pi_fv(u_fv, fs, s4);
        d.pi_fv(s_fv, fs, s3)
    };
    let value = {
        let with_i = d.lam_fv(i_fv, nat, proof);
        let with_h = d.lam_fv(h_fv, h_ty, with_i);
        let s4 = d.lam_fv(v_fv, fs, with_h);
        let s3 = d.lam_fv(u_fv, fs, s4);
        d.lam_fv(s_fv, fs, s3)
    };
    d.declare_theorem(p.finset_mem_b_sdiff_congr, ty, value)
}

// ---------------------------------------------------------------------------
// The two family-weakening lemmas.
// ---------------------------------------------------------------------------

/// `Nat.Hall.isMatching_of_family_sdiff : ∀ s nb u f,
/// IsMatching s (fun i => sdiff (nb i) u) f → IsMatching s nb f`.
///
/// A matching into the family with `u` deleted is a matching into the family.
/// Both branches of the inductive step recurse against a deleted family and
/// then have to feed `Nat.Hall.isMatching_union`, which quantifies ONE family
/// over both halves; this is the weakening that lets them.
///
/// Only the first conjunct moves: injectivity does not mention the family at
/// all, so it is passed through untouched, and the maps-into conjunct is
/// `memB_sdiff_elim`'s LEFT component.
fn declare_is_matching_of_family_sdiff(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);
    let fam = family_ty(d, &p);
    let ch = choice_ty(d);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let nb_fv = d.fresh_fvar();
    let nb = d.kernel().fvar(nb_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    let nb2 = deleted_family(d, &p, nb, u);
    let hm_ty = is_matching(d, &p, s, nb2, f);
    let hm_fv = d.fresh_fvar();
    let hm = d.kernel().fvar(hm_fv);

    let maps_ty = maps_into_ty(d, &p, s, nb2, f);
    let inj_ty = inj_on_ty(d, &p, s, f);
    let maps = and_left(d, maps_ty, inj_ty, hm);
    let inj = and_right(d, maps_ty, inj_ty, hm);

    let new_maps = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let h_ty = mem_true(d, &p, s, i);
        let member = d.apply(nb, &[i]);
        let fi = d.apply(f, &[i]);
        // `memB (sdiff (nb i) u) (f i) = true`.
        let held = d.apply(maps, &[i, h]);
        let pair = d.lemma(p.finset_mem_b_sdiff_elim, &[member, u, fi, held]);
        let left = mem_true(d, &p, member, fi);
        let right = mem_false(d, &p, u, fi);
        let body = and_left(d, left, right, pair);
        let with_h = d.lam_fv(h_fv, h_ty, body);
        d.lam_fv(i_fv, nat, with_h)
    };

    let built = is_matching_intro(d, &p, s, nb, f, new_maps, inj);
    let concl = is_matching(d, &p, s, nb, f);

    let ty = {
        let s6 = d.arrow(hm_ty, concl);
        let s5 = d.pi_fv(f_fv, ch, s6);
        let s4 = d.pi_fv(u_fv, fs, s5);
        let s3 = d.pi_fv(nb_fv, fam, s4);
        d.pi_fv(s_fv, fs, s3)
    };
    let value = {
        let s6 = d.lam_fv(hm_fv, hm_ty, built);
        let s5 = d.lam_fv(f_fv, ch, s6);
        let s4 = d.lam_fv(u_fv, fs, s5);
        let s3 = d.lam_fv(nb_fv, fam, s4);
        d.lam_fv(s_fv, fs, s3)
    };
    d.declare_theorem(p.hall_is_matching_of_family_sdiff, ty, value)
}

/// `Nat.Hall.memB_false_of_family_sdiff : ∀ s nb u f,
/// IsMatching s (fun i => sdiff (nb i) u) f →
/// ∀ i, Eq Bool (memB s i) true → Eq Bool (memB u (f i)) false`.
///
/// The other half of `memB_sdiff_elim`'s pair: a matching into the deleted
/// family never picks a value of `u`. That is the collision premise
/// `Nat.Hall.isMatching_union` asks for, in both branches — the first half's
/// values all lie in `u` (the critical neighbourhood, or the committed
/// singleton) and the second half's avoid it.
///
/// Landed separately from [`declare_is_matching_of_family_sdiff`] rather than
/// as one lemma returning the pair, because the two are consumed at different
/// arities and reading the wrong component of an `And` type-checks as the
/// other lemma's statement.
fn declare_mem_b_false_of_family_sdiff(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);
    let fam = family_ty(d, &p);
    let ch = choice_ty(d);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let nb_fv = d.fresh_fvar();
    let nb = d.kernel().fvar(nb_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    let nb2 = deleted_family(d, &p, nb, u);
    let hm_ty = is_matching(d, &p, s, nb2, f);
    let hm_fv = d.fresh_fvar();
    let hm = d.kernel().fvar(hm_fv);

    let maps_ty = maps_into_ty(d, &p, s, nb2, f);
    let inj_ty = inj_on_ty(d, &p, s, f);
    let maps = and_left(d, maps_ty, inj_ty, hm);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let h_ty = mem_true(d, &p, s, i);
    let member = d.apply(nb, &[i]);
    let fi = d.apply(f, &[i]);
    let held = d.apply(maps, &[i, h]);
    let pair = d.lemma(p.finset_mem_b_sdiff_elim, &[member, u, fi, held]);
    let left = mem_true(d, &p, member, fi);
    let right = mem_false(d, &p, u, fi);
    let proof = and_right(d, left, right, pair);

    let ty = {
        let with_h = d.arrow(h_ty, right);
        let with_i = d.pi_fv(i_fv, nat, with_h);
        let s6 = d.arrow(hm_ty, with_i);
        let s5 = d.pi_fv(f_fv, ch, s6);
        let s4 = d.pi_fv(u_fv, fs, s5);
        let s3 = d.pi_fv(nb_fv, fam, s4);
        d.pi_fv(s_fv, fs, s3)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, h_ty, proof);
        let with_i = d.lam_fv(i_fv, nat, with_h);
        let s6 = d.lam_fv(hm_fv, hm_ty, with_i);
        let s5 = d.lam_fv(f_fv, ch, s6);
        let s4 = d.lam_fv(u_fv, fs, s5);
        let s3 = d.lam_fv(nb_fv, fam, s4);
        d.lam_fv(s_fv, fs, s3)
    };
    d.declare_theorem(p.hall_mem_b_false_of_family_sdiff, ty, value)
}

// ---------------------------------------------------------------------------
// The search predicate.
// ---------------------------------------------------------------------------

/// The body of `criticalB s nb t`, written once so the definition, its
/// congruence lemma and both branches of the induction cannot drift apart.
fn critical_body(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, nb: ExprId, t: ExprId) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let card_t = fs_card(d, &p, t);
    let diff = fs_sdiff(d, &p, s, t);
    let card_diff = fs_card(d, &p, diff);
    let cover = union_over(d, &p, nb, t);
    let card_cover = fs_card(d, &p, cover);

    let included = d.const_app(p.finset_subset_fixed, &[s, t]);
    let nonempty = d.ble(one, card_t);
    let proper = d.ble(one, card_diff);
    let critical = d.ble(card_cover, card_t);

    let left = and_b(d, &p, included, nonempty);
    let right = and_b(d, &p, proper, critical);
    and_b(d, &p, left, right)
}

/// `Nat.Hall.criticalB : Nat.Finset → (Nat → Nat.Finset) → Nat.Finset → Bool`.
///
/// The inductive step's decision, in the only form `Nat.Finset.anySubset` can
/// consume. See this module's header for what each of the four conjuncts pays
/// for; the short version is that the two `ble 1 …` tests are the two
/// nonemptiness facts the two recursive calls need, on opposite sides of the
/// split, and neither implies the other.
fn declare_critical_b(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let fs = finset_ty(d, &p);
    let fam = family_ty(d, &p);
    let bool_ty = d.bool_ty();

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let nb_fv = d.fresh_fvar();
    let nb = d.kernel().fvar(nb_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    let body = critical_body(d, &p, s, nb, t);

    let ty = {
        let s3 = d.arrow(fs, bool_ty);
        let s2 = d.arrow(fam, s3);
        d.arrow(fs, s2)
    };
    let value = {
        let s3 = d.lam_fv(t_fv, fs, body);
        let s2 = d.lam_fv(nb_fv, fam, s3);
        d.lam_fv(s_fv, fs, s2)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.hall_critical_b,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(6),
    })
}

/// `Nat.Hall.criticalB_congr : ∀ s nb u v, (∀ i, Eq Bool (memB u i) (memB v i))
/// → Eq Bool (criticalB s nb u) (criticalB s nb v)`.
///
/// `Nat.Finset.forallSubset_of_search`'s premise. Every loop bound inside the
/// predicate is independent of the quantified set (ADR-1644's general rule), so
/// this is composition and nothing else:
/// [`finset_subset_fixed_congr`](super::NatPrelude::finset_subset_fixed_congr)
/// for the inclusion test, `card_congr_of_memB` for the two counts,
/// `Nat.Hall.card_unionOver_congr` for the neighbourhood's count, and
/// `memB_sdiff` twice for the complement's members — the one place the argument
/// has to descend into a set CONSTRUCTOR rather than pass a pointwise equation
/// straight through.
fn declare_critical_b_congr(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);
    let fam = family_ty(d, &p);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let nb_fv = d.fresh_fvar();
    let nb = d.kernel().fvar(nb_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);

    let h_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let a = fs_mem(d, &p, u, i);
        let b = fs_mem(d, &p, v, i);
        let body = d.bool_eq(a, b);
        d.pi_fv(i_fv, nat, body)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let diff_pointwise = d.lemma(p.finset_mem_b_sdiff_congr, &[s, u, v, h]);

    let card_u = fs_card(d, &p, u);
    let card_v = fs_card(d, &p, v);
    let h_card = d.lemma(p.finset_card_congr_of_mem_b, &[u, v, h]);

    let du = fs_sdiff(d, &p, s, u);
    let dv = fs_sdiff(d, &p, s, v);
    let card_du = fs_card(d, &p, du);
    let card_dv = fs_card(d, &p, dv);
    let h_card_diff = d.lemma(p.finset_card_congr_of_mem_b, &[du, dv, diff_pointwise]);

    let cover_u = union_over(d, &p, nb, u);
    let cover_v = union_over(d, &p, nb, v);
    let card_cu = fs_card(d, &p, cover_u);
    let card_cv = fs_card(d, &p, cover_v);
    let h_card_cover = d.lemma(p.hall_card_union_over_congr, &[nb, u, v, h]);

    let one = d.num(1);
    let inc_u = d.const_app(p.finset_subset_fixed, &[s, u]);
    let inc_v = d.const_app(p.finset_subset_fixed, &[s, v]);
    let h_inc = d.lemma(p.finset_subset_fixed_congr, &[s, u, v, h]);

    // `ble 1 (card u) = ble 1 (card v)`.
    let ne_u = d.ble(one, card_u);
    let ne_v = d.ble(one, card_v);
    let h_ne = nat_to_bool_congr(d, card_u, card_v, h_card, &|d, x| d.ble(one, x));

    // `ble 1 (card (sdiff s u)) = ble 1 (card (sdiff s v))`.
    let pr_u = d.ble(one, card_du);
    let pr_v = d.ble(one, card_dv);
    let h_pr = nat_to_bool_congr(d, card_du, card_dv, h_card_diff, &|d, x| d.ble(one, x));

    // `ble (card (unionOver nb u)) (card u) = ble (card (unionOver nb v)) (card v)`,
    // in two steps because both arguments move.
    let cr_u = d.ble(card_cu, card_u);
    let cr_mid = d.ble(card_cv, card_u);
    let cr_v = d.ble(card_cv, card_v);
    let h_cr_left = nat_to_bool_congr(d, card_cu, card_cv, h_card_cover, &|d, x| d.ble(x, card_u));
    let h_cr_right = nat_to_bool_congr(d, card_u, card_v, h_card, &|d, x| d.ble(card_cv, x));
    let h_cr = d.bool_trans(cr_u, cr_mid, cr_v, h_cr_left, h_cr_right);

    // Assemble the two `andB` levels, one argument at a time.
    let left_u = and_b(d, &p, inc_u, ne_u);
    let left_mid = and_b(d, &p, inc_v, ne_u);
    let left_v = and_b(d, &p, inc_v, ne_v);
    let l1 = bool_congr(d, inc_u, inc_v, h_inc, &|d, x| and_b(d, &p, x, ne_u));
    let l2 = bool_congr(d, ne_u, ne_v, h_ne, &|d, x| and_b(d, &p, inc_v, x));
    let h_left = d.bool_trans(left_u, left_mid, left_v, l1, l2);

    let right_u = and_b(d, &p, pr_u, cr_u);
    let right_mid = and_b(d, &p, pr_v, cr_u);
    let right_v = and_b(d, &p, pr_v, cr_v);
    let r1 = bool_congr(d, pr_u, pr_v, h_pr, &|d, x| and_b(d, &p, x, cr_u));
    let r2 = bool_congr(d, cr_u, cr_v, h_cr, &|d, x| and_b(d, &p, pr_v, x));
    let h_right = d.bool_trans(right_u, right_mid, right_v, r1, r2);

    let whole_u = and_b(d, &p, left_u, right_u);
    let whole_mid = and_b(d, &p, left_v, right_u);
    let whole_v = and_b(d, &p, left_v, right_v);
    let w1 = bool_congr(d, left_u, left_v, h_left, &|d, x| and_b(d, &p, x, right_u));
    let w2 = bool_congr(d, right_u, right_v, h_right, &|d, x| {
        and_b(d, &p, left_v, x)
    });
    let proof = d.bool_trans(whole_u, whole_mid, whole_v, w1, w2);

    let ty = {
        let lhs = d.const_app(p.hall_critical_b, &[s, nb, u]);
        let rhs = d.const_app(p.hall_critical_b, &[s, nb, v]);
        let concl = d.bool_eq(lhs, rhs);
        let s5 = d.arrow(h_ty, concl);
        let s4 = d.pi_fv(v_fv, fs, s5);
        let s3 = d.pi_fv(u_fv, fs, s4);
        let s2 = d.pi_fv(nb_fv, fam, s3);
        d.pi_fv(s_fv, fs, s2)
    };
    let value = {
        let s5 = d.lam_fv(h_fv, h_ty, proof);
        let s4 = d.lam_fv(v_fv, fs, s5);
        let s3 = d.lam_fv(u_fv, fs, s4);
        let s2 = d.lam_fv(nb_fv, fam, s3);
        d.lam_fv(s_fv, fs, s2)
    };
    d.declare_theorem(p.hall_critical_b_congr, ty, value)
}

// ---------------------------------------------------------------------------
// Hall's marriage theorem.
// ---------------------------------------------------------------------------

/// `Nat.Hall.sufficient : ∀ s nb, HallCondition s nb →
/// Exists (fun f => IsMatching s nb f)`.
///
/// Strong induction on `card s`, with the motive carrying the count as an
/// equation so both recursive calls can be made at a measure the descent
/// lemmas produce:
///
/// ```text
/// motive n := ∀ s nb, card s = n → HallCondition s nb → ∃ f, IsMatching s nb f
/// ```
///
/// The empty case is `Nat.Hall.exists_isMatching_of_card_le_zero`, decided by
/// `Nat.lt_or_ge`. Above it, `Nat.Finset.anySubset` decides whether some subset
/// is critical, and the two branches are the two halves of ADR-1644.
///
/// **`Nat.Hall.exists_isMatching_singleton` is not used.** It is stated at a
/// literal `Nat.Finset.singleton a`, and an arbitrary `s` with `card s = 1` is
/// not definitionally one; the non-critical branch subsumes that case anyway,
/// since it commits one index and recurses on a set the empty case then
/// answers. The singleton lemma remains the standalone statement it was landed
/// as (ADR-1630).
fn declare_sufficient(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);
    let fam = family_ty(d, &p);
    let ch = choice_ty(d);
    let tr = d.bool_true();
    let fa = d.bool_false();
    let zero = d.zero();
    let one = d.num(1);

    // --- the motive ---------------------------------------------------------
    let motive_at = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let nb_fv = d.fresh_fvar();
        let nb = d.kernel().fvar(nb_fv);
        let card_s = fs_card(d, &p, s);
        let hcard = d.eq(card_s, n);
        let hall = hall_condition(d, &p, s, nb);
        let goal = exists_matching(d, &p, s, nb);
        let s4 = d.arrow(hall, goal);
        let s3 = d.arrow(hcard, s4);
        let s2 = d.pi_fv(nb_fv, fam, s3);
        d.pi_fv(s_fv, fs, s2)
    };
    let motive = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = motive_at(d, n);
        d.lam_fv(n_fv, nat, body)
    };

    // --- the step -----------------------------------------------------------
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let ih_ty = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let hm_fv = d.fresh_fvar();
        let hm_ty = d.lt(m, n);
        let at_m = motive_at(d, m);
        let with_hm = d.pi_fv(hm_fv, hm_ty, at_m);
        d.pi_fv(m_fv, nat, with_hm)
    };
    let ih_fv = d.fresh_fvar();
    let ih = d.kernel().fvar(ih_fv);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let nb_fv = d.fresh_fvar();
    let nb = d.kernel().fvar(nb_fv);

    let card_s = fs_card(d, &p, s);
    let bound_s = fs_bound(d, &p, s);
    let hcard_ty = d.eq(card_s, n);
    let hcard_fv = d.fresh_fvar();
    let hcard = d.kernel().fvar(hcard_fv);
    let hall_ty = hall_condition(d, &p, s, nb);
    let hall_fv = d.fresh_fvar();
    let hall = d.kernel().fvar(hall_fv);

    let goal = exists_matching(d, &p, s, nb);
    let goal_pred = matching_pred(d, &p, s, nb);

    // `Lt (card x) (card s)  ⊢  Lt (card x) n`, the descent transported onto
    // the induction variable.
    let to_measure = |d: &mut NatDev<'_>, cx: ExprId, hlt: ExprId| -> ExprId {
        lt_rewrite_right(d, cx, card_s, n, hcard, hlt)
    };

    // --- above the bottom: decide whether some subset is critical -----------
    let predicate = d.const_app(p.hall_critical_b, &[s, nb]);
    let search = d.const_app(p.finset_any_subset, &[predicate, bound_s]);
    let search_true = d.bool_eq(search, tr);
    let search_false = d.bool_eq(search, fa);

    // `fun t => And (Eq Nat (bound t) (bound s)) (Eq Bool (criticalB s nb t) true)`
    let found_pred = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let bt = fs_bound(d, &p, t);
        let at_bound = d.eq(bt, bound_s);
        let pt = d.apply(predicate, &[t]);
        let holds = d.bool_eq(pt, tr);
        let body = d.const_app(p.logic.and, &[at_bound, holds]);
        d.lam_fv(t_fv, fs, body)
    };

    // ===== the CRITICAL branch =============================================
    let on_search_true = {
        let hsearch_fv = d.fresh_fvar();
        let hsearch = d.kernel().fvar(hsearch_fv);
        let witness = d.lemma(
            p.finset_exists_subset_of_search,
            &[predicate, bound_s, hsearch],
        );

        let minor = {
            let t_fv = d.fresh_fvar();
            let t = d.kernel().fvar(t_fv);
            let hpair_fv = d.fresh_fvar();
            let hpair = d.kernel().fvar(hpair_fv);

            let bt = fs_bound(d, &p, t);
            let at_bound = d.eq(bt, bound_s);
            let pt = d.apply(predicate, &[t]);
            let holds = d.bool_eq(pt, tr);
            let hpair_ty = d.const_app(p.logic.and, &[at_bound, holds]);

            let hbound = and_left(d, at_bound, holds, hpair);
            let hcrit = and_right(d, at_bound, holds, hpair);

            // `Le (bound t) (bound s)` from the search's exact bound.
            let hb = {
                let base = d.lemma(p.le_refl, &[bt]);
                le_rewrite_right(d, bt, bt, bound_s, hbound, base)
            };

            // The four conjuncts.
            let card_t = fs_card(d, &p, t);
            let diff = fs_sdiff(d, &p, s, t);
            let card_diff = fs_card(d, &p, diff);
            let cover = union_over(d, &p, nb, t);
            let card_cover = fs_card(d, &p, cover);

            let included = d.const_app(p.finset_subset_fixed, &[s, t]);
            let nonempty = d.ble(one, card_t);
            let proper = d.ble(one, card_diff);
            let critical = d.ble(card_cover, card_t);
            let left_half = and_b(d, &p, included, nonempty);
            let right_half = and_b(d, &p, proper, critical);

            let h_left = d.lemma(p.graph_and_b_left, &[left_half, right_half, hcrit]);
            let h_right = d.lemma(p.graph_and_b_right, &[left_half, right_half, hcrit]);
            let hsf = d.lemma(p.graph_and_b_left, &[included, nonempty, h_left]);
            let h_ne = d.lemma(p.graph_and_b_right, &[included, nonempty, h_left]);
            let h_pr = d.lemma(p.graph_and_b_left, &[proper, critical, h_right]);
            let h_cr = d.lemma(p.graph_and_b_right, &[proper, critical, h_right]);

            let pos_t = d.lemma(p.le_of_ble_eq_true, &[one, card_t, h_ne]);
            let pos_d = d.lemma(p.le_of_ble_eq_true, &[one, card_diff, h_pr]);
            let crit_le = d.lemma(p.le_of_ble_eq_true, &[card_cover, card_t, h_cr]);

            let hsub = d.lemma(p.finset_mem_b_of_subset_fixed_of_bound_le, &[s, t, hb, hsf]);
            let lt_t = d.lemma(
                p.finset_card_lt_card_of_subset_fixed,
                &[s, t, hb, hsf, pos_d],
            );
            let lt_d = d.lemma(
                p.finset_card_sdiff_lt_card_of_subset_fixed,
                &[s, t, hb, hsf, pos_t],
            );

            // Recurse on `t` against the ORIGINAL family.
            let hall_t = d.lemma(p.hall_condition_subset, &[s, t, nb, hall, hsub]);
            let measure_t = to_measure(d, card_t, lt_t);
            let refl_t = d.refl(card_t);
            let rec_t = {
                let at_m = d.apply(ih, &[card_t, measure_t]);
                d.apply(at_m, &[t, nb, refl_t, hall_t])
            };

            // Recurse on `s \ t` against the DELETED family.
            let nb2 = deleted_family(d, &p, nb, cover);
            let hall_d = d.lemma(
                p.hall_condition_sdiff_of_critical,
                &[s, t, nb, hall, hsub, crit_le],
            );
            let measure_d = to_measure(d, card_diff, lt_d);
            let refl_d = d.refl(card_diff);
            let rec_d = {
                let at_m = d.apply(ih, &[card_diff, measure_d]);
                d.apply(at_m, &[diff, nb2, refl_d, hall_d])
            };

            let pred_t = matching_pred(d, &p, t, nb);
            let pred_d = matching_pred(d, &p, diff, nb2);

            // Two `Exists.rec`s, then glue.
            let inner = {
                let f1_fv = d.fresh_fvar();
                let f1 = d.kernel().fvar(f1_fv);
                let hm1_fv = d.fresh_fvar();
                let hm1 = d.kernel().fvar(hm1_fv);
                let hm1_ty = is_matching(d, &p, t, nb, f1);

                let body = {
                    let f2_fv = d.fresh_fvar();
                    let f2 = d.kernel().fvar(f2_fv);
                    let hm2_fv = d.fresh_fvar();
                    let hm2 = d.kernel().fvar(hm2_fv);
                    let hm2_ty = is_matching(d, &p, diff, nb2, f2);

                    let hm2_plain = d.lemma(
                        p.hall_is_matching_of_family_sdiff,
                        &[diff, nb, cover, f2, hm2],
                    );
                    let avoid = d.lemma(
                        p.hall_mem_b_false_of_family_sdiff,
                        &[diff, nb, cover, f2, hm2],
                    );
                    let maps1_ty = maps_into_ty(d, &p, t, nb, f1);
                    let inj1_ty = inj_on_ty(d, &p, t, f1);
                    let maps1 = and_left(d, maps1_ty, inj1_ty, hm1);

                    // `i ∈ t`, `j ∈ s \ t`, `f1 i = f2 j  ⊢  False`.
                    let collision = {
                        let i_fv = d.fresh_fvar();
                        let i = d.kernel().fvar(i_fv);
                        let j_fv = d.fresh_fvar();
                        let j = d.kernel().fvar(j_fv);
                        let hi_fv = d.fresh_fvar();
                        let hi = d.kernel().fvar(hi_fv);
                        let hi_ty = mem_true(d, &p, t, i);
                        let hj_fv = d.fresh_fvar();
                        let hj = d.kernel().fvar(hj_fv);
                        let hj_ty = mem_true(d, &p, diff, j);
                        let heq_fv = d.fresh_fvar();
                        let heq = d.kernel().fvar(heq_fv);
                        let f1i = d.apply(f1, &[i]);
                        let f2j = d.apply(f2, &[j]);
                        let heq_ty = d.eq(f1i, f2j);

                        let hin = d.apply(maps1, &[i, hi]);
                        let covered = d.lemma(p.hall_mem_union_over, &[nb, t, i, f1i, hi, hin]);
                        // Move `f1 i ∈ unionOver nb t` onto `f2 j`.
                        let moved = {
                            let motive = d.eq_motive(f1i, &|d, x| {
                                let m = fs_mem(d, &p, cover, x);
                                d.bool_eq(m, tr)
                            });
                            d.transport(f1i, motive, covered, f2j, heq)
                        };
                        let avoided = d.apply(avoid, &[j, hj]);
                        let mf2 = fs_mem(d, &p, cover, f2j);
                        let flipped = d.bool_symm(mf2, fa, avoided);
                        let clash = d.bool_trans(fa, mf2, tr, flipped, moved);
                        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
                        let body = d.false_true_elim(false_ty, clash);

                        let s5 = d.lam_fv(heq_fv, heq_ty, body);
                        let s4 = d.lam_fv(hj_fv, hj_ty, s5);
                        let s3 = d.lam_fv(hi_fv, hi_ty, s4);
                        let s2 = d.lam_fv(j_fv, nat, s3);
                        d.lam_fv(i_fv, nat, s2)
                    };

                    let glued = d.lemma(
                        p.hall_is_matching_union,
                        &[t, diff, nb, f1, f2, hm1, hm2_plain, collision],
                    );
                    let rebuilt = fs_union(d, &p, t, diff);
                    let pointwise = d.lemma(p.finset_mem_b_union_sdiff_self, &[s, t, hsub]);
                    let glue_fn = d.const_app(p.hall_glue, &[f1, f2, t]);
                    let moved = d.lemma(
                        p.hall_is_matching_congr,
                        &[rebuilt, s, nb, glue_fn, pointwise, glued],
                    );
                    let built = exists_intro_at(d, &p, ch, goal_pred, glue_fn, moved);

                    let with_hm2 = d.lam_fv(hm2_fv, hm2_ty, built);
                    let minor2 = d.lam_fv(f2_fv, ch, with_hm2);
                    exists_elim_at(d, &p, ch, pred_d, goal, minor2, rec_d)
                };

                let with_hm1 = d.lam_fv(hm1_fv, hm1_ty, body);
                let minor1 = d.lam_fv(f1_fv, ch, with_hm1);
                exists_elim_at(d, &p, ch, pred_t, goal, minor1, rec_t)
            };

            let with_hpair = d.lam_fv(hpair_fv, hpair_ty, inner);
            d.lam_fv(t_fv, fs, with_hpair)
        };

        let body = exists_elim_at(d, &p, fs, found_pred, goal, minor, witness);
        d.lam_fv(hsearch_fv, search_true, body)
    };

    // ===== the NON-CRITICAL branch =========================================
    let on_search_false = {
        let hsearch_fv = d.fresh_fvar();
        let hsearch = d.kernel().fvar(hsearch_fv);
        let hpos_fv = d.fresh_fvar();
        let hpos = d.kernel().fvar(hpos_fv);
        let hpos_ty = d.lt(zero, card_s);

        let congr = d.lemma(p.hall_critical_b_congr, &[s, nb]);
        let exhausted = d.lemma(
            p.finset_forall_subset_of_search,
            &[predicate, bound_s, congr, hsearch],
        );

        // Pick a member of `s`.
        let member_pred = member_witness_pred(d, &p, s);
        let have_member = d.lemma(p.finset_exists_mem_b_of_card_pos, &[s, hpos]);

        let minor_x = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_fv = d.fresh_fvar();
            let hx_pair = d.kernel().fvar(hx_fv);
            let lt_ty = d.lt(x, bound_s);
            let in_ty = mem_true(d, &p, s, x);
            let hx_ty = d.const_app(p.logic.and, &[lt_ty, in_ty]);
            let hx = and_right(d, lt_ty, in_ty, hx_pair);

            let sing_x = fs_singleton(d, &p, x);

            // `∀ i, memB {x} i = true → memB s i = true`.
            let sing_sub = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let hi_fv = d.fresh_fvar();
                let hi = d.kernel().fvar(hi_fv);
                let hi_ty = mem_true(d, &p, sing_x, i);
                let is_x = d.lemma(p.finset_eq_of_mem_b_singleton, &[x, i, hi]);
                let back = d.symm(i, x, is_x);
                let motive = d.eq_motive(x, &|d, y| mem_true(d, &p, s, y));
                let body = d.transport(x, motive, hx, i, back);
                let with_hi = d.lam_fv(hi_fv, hi_ty, body);
                d.lam_fv(i_fv, nat, with_hi)
            };

            // A neighbour of `x` exists, from Hall's condition at `{x}`.
            let cover_x = union_over(d, &p, nb, sing_x);
            let card_cover_x = fs_card(d, &p, cover_x);
            let card_sing = fs_card(d, &p, sing_x);
            let bounded = d.apply(hall, &[sing_x, sing_sub]);
            let sing_is_one = d.lemma(p.finset_card_singleton, &[x]);
            let cover_pos = le_rewrite_left(d, card_sing, one, card_cover_x, sing_is_one, bounded);
            let cover_member_pred = member_witness_pred(d, &p, cover_x);
            let have_v = d.lemma(p.finset_exists_mem_b_of_card_pos, &[cover_x, cover_pos]);

            let minor_v = {
                let v_fv = d.fresh_fvar();
                let v = d.kernel().fvar(v_fv);
                let hv_fv = d.fresh_fvar();
                let hv_pair = d.kernel().fvar(hv_fv);
                let bound_cover_x = fs_bound(d, &p, cover_x);
                let vlt_ty = d.lt(v, bound_cover_x);
                let vin_ty = mem_true(d, &p, cover_x, v);
                let hv_ty = d.const_app(p.logic.and, &[vlt_ty, vin_ty]);
                let hv = and_right(d, vlt_ty, vin_ty, hv_pair);

                let uw_pred = union_witness_pred(d, &p, nb, sing_x, v);
                let have_i0 = d.lemma(p.hall_mem_union_over_elim, &[nb, sing_x, v, hv]);

                let minor_i0 = {
                    let i0_fv = d.fresh_fvar();
                    let i0 = d.kernel().fvar(i0_fv);
                    let hi0_fv = d.fresh_fvar();
                    let hi0_pair = d.kernel().fvar(hi0_fv);
                    let in_sing = mem_true(d, &p, sing_x, i0);
                    let member_i0 = d.apply(nb, &[i0]);
                    let holds = mem_true(d, &p, member_i0, v);
                    let hi0_ty = d.const_app(p.logic.and, &[in_sing, holds]);
                    let hi0_sing = and_left(d, in_sing, holds, hi0_pair);
                    let hi0_v = and_right(d, in_sing, holds, hi0_pair);

                    // `i0 = x`, so `v` is a neighbour of `x`.
                    let is_x = d.lemma(p.finset_eq_of_mem_b_singleton, &[x, i0, hi0_sing]);
                    let hxv = {
                        let motive = d.eq_motive(i0, &|d, y| {
                            let mem = d.apply(nb, &[y]);
                            mem_true(d, &p, mem, v)
                        });
                        d.transport(i0, motive, hi0_v, x, is_x)
                    };

                    let sing_v = fs_singleton(d, &p, v);
                    let nb2 = deleted_family(d, &p, nb, sing_v);
                    let rest = fs_sdiff(d, &p, s, sing_x);
                    let card_rest = fs_card(d, &p, rest);

                    // Every nonempty subset of `s \ {x}` has STRICT slack.
                    let strict = {
                        let w_fv = d.fresh_fvar();
                        let w = d.kernel().fvar(w_fv);
                        let hw_fv = d.fresh_fvar();
                        let hw = d.kernel().fvar(hw_fv);
                        let hw_ty = {
                            let i_fv = d.fresh_fvar();
                            let i = d.kernel().fvar(i_fv);
                            let a = mem_true(d, &p, w, i);
                            let b = mem_true(d, &p, rest, i);
                            let step = d.arrow(a, b);
                            d.pi_fv(i_fv, nat, step)
                        };
                        let hwp_fv = d.fresh_fvar();
                        let hwp = d.kernel().fvar(hwp_fv);
                        let card_w = fs_card(d, &p, w);
                        let hwp_ty = d.lt(zero, card_w);
                        let cover_w = union_over(d, &p, nb, w);
                        let card_cover_w = fs_card(d, &p, cover_w);
                        let strict_goal = d.lt(card_w, card_cover_w);

                        // `w ⊆ s`, through `s \ {x}`.
                        let hw_s = {
                            let i_fv = d.fresh_fvar();
                            let i = d.kernel().fvar(i_fv);
                            let hi_fv = d.fresh_fvar();
                            let hi = d.kernel().fvar(hi_fv);
                            let hi_ty = mem_true(d, &p, w, i);
                            let in_rest = d.apply(hw, &[i, hi]);
                            let pair = d.lemma(p.finset_mem_b_sdiff_elim, &[s, sing_x, i, in_rest]);
                            let l = mem_true(d, &p, s, i);
                            let r = mem_false(d, &p, sing_x, i);
                            let body = and_left(d, l, r, pair);
                            let with_hi = d.lam_fv(hi_fv, hi_ty, body);
                            d.lam_fv(i_fv, nat, with_hi)
                        };

                        // `x ∉ w`, because every member of `w` avoids `x`.
                        let hw_not_x = {
                            let mwx = fs_mem(d, &p, w, x);
                            let decided = bool_true_or_false(d, &p, mwx);
                            let goal_nx = d.bool_eq(mwx, fa);
                            let left_ty = d.bool_eq(mwx, tr);
                            let right_ty = d.bool_eq(mwx, fa);
                            let left_case = {
                                let hm_fv = d.fresh_fvar();
                                let hm = d.kernel().fvar(hm_fv);
                                let in_rest = d.apply(hw, &[x, hm]);
                                let pair =
                                    d.lemma(p.finset_mem_b_sdiff_elim, &[s, sing_x, x, in_rest]);
                                let l = mem_true(d, &p, s, x);
                                let r = mem_false(d, &p, sing_x, x);
                                let not_self = and_right(d, l, r, pair);
                                let self_in = d.lemma(p.finset_mem_b_singleton_self, &[x]);
                                let msx = fs_mem(d, &p, sing_x, x);
                                let flipped = d.bool_symm(msx, fa, not_self);
                                let clash = d.bool_trans(fa, msx, tr, flipped, self_in);
                                let body = d.false_true_elim(goal_nx, clash);
                                d.lam_fv(hm_fv, left_ty, body)
                            };
                            let right_case = {
                                let hm_fv = d.fresh_fvar();
                                let hm = d.kernel().fvar(hm_fv);
                                d.lam_fv(hm_fv, right_ty, hm)
                            };
                            or_elim(
                                d, &p, left_ty, right_ty, goal_nx, left_case, right_case, decided,
                            )
                        };

                        // Normalise `w`'s stored bound so the search can answer it.
                        let w2 = fs_restrict(d, &p, w, bound_s);
                        let below = {
                            let j_fv = d.fresh_fvar();
                            let j = d.kernel().fvar(j_fv);
                            let hj_fv = d.fresh_fvar();
                            let hj = d.kernel().fvar(hj_fv);
                            let hj_ty = mem_true(d, &p, w, j);
                            let in_s = d.apply(hw_s, &[j, hj]);
                            let body = d.lemma(p.finset_lt_bound_of_mem_b, &[s, j, in_s]);
                            let with_hj = d.lam_fv(hj_fv, hj_ty, body);
                            d.lam_fv(j_fv, nat, with_hj)
                        };
                        let same = d.lemma(p.finset_mem_b_restrict, &[w, bound_s, below]);
                        let bound_w2 = fs_bound(d, &p, w2);
                        let hbw = {
                            let eq_bound = d.lemma(p.finset_bound_restrict, &[w, bound_s]);
                            let base = d.lemma(p.le_refl, &[bound_s]);
                            let back = d.symm(bound_w2, bound_s, eq_bound);
                            le_rewrite_left(d, bound_s, bound_w2, bound_s, back, base)
                        };
                        let refuted = d.apply(exhausted, &[w2, hbw]);

                        let card_w2 = fs_card(d, &p, w2);
                        let cover_w2 = union_over(d, &p, nb, w2);
                        let card_cover_w2 = fs_card(d, &p, cover_w2);
                        let hcw = d.lemma(p.finset_card_congr_of_mem_b, &[w2, w, same]);
                        let hcu = d.lemma(p.hall_card_union_over_congr, &[nb, w2, w, same]);

                        // Decide the goal; the `≥` side rebuilds `criticalB = true`.
                        let decided = d.lemma(p.lt_or_ge, &[card_w, card_cover_w]);
                        let lt_ty = d.lt(card_w, card_cover_w);
                        let ge_ty = d.le(card_cover_w, card_w);
                        let on_lt = {
                            let h_fv = d.fresh_fvar();
                            let h = d.kernel().fvar(h_fv);
                            d.lam_fv(h_fv, lt_ty, h)
                        };
                        let on_ge = {
                            let h_fv = d.fresh_fvar();
                            let h = d.kernel().fvar(h_fv);

                            // 1. `subsetFixed s w2 = true`.
                            let c1 = {
                                let pw = {
                                    let i_fv = d.fresh_fvar();
                                    let i = d.kernel().fvar(i_fv);
                                    let hi_fv = d.fresh_fvar();
                                    let hi = d.kernel().fvar(hi_fv);
                                    let hi_ty = mem_true(d, &p, w2, i);
                                    let step = d.apply(same, &[i]);
                                    let m2 = fs_mem(d, &p, w2, i);
                                    let m1 = fs_mem(d, &p, w, i);
                                    // `same` points w2 -> w, and the membership
                                    // hypothesis is about w2, so it is the
                                    // FLIPPED equation that composes.
                                    let back = d.bool_symm(m2, m1, step);
                                    let carried = d.bool_trans(m1, m2, tr, back, hi);
                                    let body = d.apply(hw_s, &[i, carried]);
                                    let with_hi = d.lam_fv(hi_fv, hi_ty, body);
                                    d.lam_fv(i_fv, nat, with_hi)
                                };
                                d.lemma(p.finset_subset_fixed_of_mem, &[s, w2, pw])
                            };
                            // 2. `ble 1 (card w2) = true`.
                            let c2 = {
                                let back = d.symm(card_w2, card_w, hcw);
                                let lifted = le_rewrite_right(d, one, card_w, card_w2, back, hwp);
                                d.lemma(p.ble_eq_true_of_le, &[one, card_w2, lifted])
                            };
                            // 3. `ble 1 (card (sdiff s w2)) = true`, because `x`
                            //    is in `s` and not in `w2`.
                            let c3 = {
                                let step = d.apply(same, &[x]);
                                let m2 = fs_mem(d, &p, w2, x);
                                let m1 = fs_mem(d, &p, w, x);
                                let not_in = d.bool_trans(m2, m1, fa, step, hw_not_x);
                                let in_diff =
                                    d.lemma(p.finset_mem_b_sdiff_intro, &[s, w2, x, hx, not_in]);
                                let diff2 = fs_sdiff(d, &p, s, w2);
                                let card_diff2 = fs_card(d, &p, diff2);
                                let positive =
                                    d.lemma(p.finset_card_pos_of_mem_b, &[diff2, x, in_diff]);
                                d.lemma(p.ble_eq_true_of_le, &[one, card_diff2, positive])
                            };
                            // 4. `ble (card (unionOver nb w2)) (card w2) = true`.
                            let c4 = {
                                let back_u = d.symm(card_cover_w2, card_cover_w, hcu);
                                let back_w = d.symm(card_w2, card_w, hcw);
                                let step1 = le_rewrite_left(
                                    d,
                                    card_cover_w,
                                    card_cover_w2,
                                    card_w,
                                    back_u,
                                    h,
                                );
                                let step2 = le_rewrite_right(
                                    d,
                                    card_cover_w2,
                                    card_w,
                                    card_w2,
                                    back_w,
                                    step1,
                                );
                                d.lemma(p.ble_eq_true_of_le, &[card_cover_w2, card_w2, step2])
                            };

                            let included = d.const_app(p.finset_subset_fixed, &[s, w2]);
                            let nonempty = d.ble(one, card_w2);
                            let diff2 = fs_sdiff(d, &p, s, w2);
                            let card_diff2 = fs_card(d, &p, diff2);
                            let proper = d.ble(one, card_diff2);
                            let critical = d.ble(card_cover_w2, card_w2);
                            let left_half = and_b(d, &p, included, nonempty);
                            let right_half = and_b(d, &p, proper, critical);
                            let hl = d.lemma(p.graph_and_b_intro, &[included, nonempty, c1, c2]);
                            let hr = d.lemma(p.graph_and_b_intro, &[proper, critical, c3, c4]);
                            let whole =
                                d.lemma(p.graph_and_b_intro, &[left_half, right_half, hl, hr]);

                            let pw2 = d.const_app(p.hall_critical_b, &[s, nb, w2]);
                            let flipped = d.bool_symm(pw2, fa, refuted);
                            let clash = d.bool_trans(fa, pw2, tr, flipped, whole);
                            let body = d.false_true_elim(strict_goal, clash);
                            d.lam_fv(h_fv, ge_ty, body)
                        };
                        let answered =
                            or_elim(d, &p, lt_ty, ge_ty, strict_goal, on_lt, on_ge, decided);

                        let with_hwp = d.lam_fv(hwp_fv, hwp_ty, answered);
                        let with_hw = d.lam_fv(hw_fv, hw_ty, with_hwp);
                        d.lam_fv(w_fv, fs, with_hw)
                    };

                    let hall_rest = d.lemma(
                        p.hall_condition_sdiff_singleton_of_strict,
                        &[rest, v, nb, strict],
                    );

                    // `card (s \ {x}) < card s`. `bound {x}` IS `succ x`
                    // (`singleton a := mk (fun k => beq k a) (succ a)`), and
                    // `x < bound s` IS `Le (succ x) (bound s)`, so the witness's
                    // own bound fact already IS `Le (bound {x}) (bound s)`.
                    let hb2 = and_left(d, lt_ty, in_ty, hx_pair);
                    let hsf2 = d.lemma(p.finset_subset_fixed_of_mem, &[s, sing_x, sing_sub]);
                    let self_in = d.lemma(p.finset_mem_b_singleton_self, &[x]);
                    let pos_sing = d.lemma(p.finset_card_pos_of_mem_b, &[sing_x, x, self_in]);
                    let lt_rest = d.lemma(
                        p.finset_card_sdiff_lt_card_of_subset_fixed,
                        &[s, sing_x, hb2, hsf2, pos_sing],
                    );
                    let measure_rest = to_measure(d, card_rest, lt_rest);
                    let refl_rest = d.refl(card_rest);
                    let rec_rest = {
                        let at_m = d.apply(ih, &[card_rest, measure_rest]);
                        d.apply(at_m, &[rest, nb2, refl_rest, hall_rest])
                    };

                    let pred_rest = matching_pred(d, &p, rest, nb2);
                    let constant = {
                        let i_fv = d.fresh_fvar();
                        d.lam_fv(i_fv, nat, v)
                    };

                    let minor_f2 = {
                        let f2_fv = d.fresh_fvar();
                        let f2 = d.kernel().fvar(f2_fv);
                        let hm2_fv = d.fresh_fvar();
                        let hm2 = d.kernel().fvar(hm2_fv);
                        let hm2_ty = is_matching(d, &p, rest, nb2, f2);

                        let hm2_plain = d.lemma(
                            p.hall_is_matching_of_family_sdiff,
                            &[rest, nb, sing_v, f2, hm2],
                        );
                        let avoid = d.lemma(
                            p.hall_mem_b_false_of_family_sdiff,
                            &[rest, nb, sing_v, f2, hm2],
                        );

                        // The committed index, matched to `v`.
                        let hm1 = {
                            let maps = {
                                let i_fv = d.fresh_fvar();
                                let i = d.kernel().fvar(i_fv);
                                let hi_fv = d.fresh_fvar();
                                let hi = d.kernel().fvar(hi_fv);
                                let hi_ty = mem_true(d, &p, sing_x, i);
                                let is_x = d.lemma(p.finset_eq_of_mem_b_singleton, &[x, i, hi]);
                                let back = d.symm(i, x, is_x);
                                let motive = d.eq_motive(x, &|d, y| {
                                    let mem = d.apply(nb, &[y]);
                                    mem_true(d, &p, mem, v)
                                });
                                let body = d.transport(x, motive, hxv, i, back);
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
                                let hi_ty = mem_true(d, &p, sing_x, i);
                                let hj_fv = d.fresh_fvar();
                                let hj = d.kernel().fvar(hj_fv);
                                let hj_ty = mem_true(d, &p, sing_x, j);
                                let heq_fv = d.fresh_fvar();
                                let ci = d.apply(constant, &[i]);
                                let cj = d.apply(constant, &[j]);
                                let heq_ty = d.eq(ci, cj);
                                let i_is_x = d.lemma(p.finset_eq_of_mem_b_singleton, &[x, i, hi]);
                                let j_is_x = d.lemma(p.finset_eq_of_mem_b_singleton, &[x, j, hj]);
                                let back = d.symm(j, x, j_is_x);
                                let body = d.trans(i, x, j, i_is_x, back);
                                let s4 = d.lam_fv(heq_fv, heq_ty, body);
                                let s3 = d.lam_fv(hj_fv, hj_ty, s4);
                                let s2 = d.lam_fv(hi_fv, hi_ty, s3);
                                let inner = d.lam_fv(j_fv, nat, s2);
                                d.lam_fv(i_fv, nat, inner)
                            };
                            is_matching_intro(d, &p, sing_x, nb, constant, maps, inj)
                        };

                        // `i ∈ {x}`, `j ∈ s \ {x}`, `v = f2 j  ⊢  False`.
                        let collision = {
                            let i_fv = d.fresh_fvar();
                            let i = d.kernel().fvar(i_fv);
                            let j_fv = d.fresh_fvar();
                            let j = d.kernel().fvar(j_fv);
                            let hi_fv = d.fresh_fvar();
                            let hi_ty = mem_true(d, &p, sing_x, i);
                            let hj_fv = d.fresh_fvar();
                            let hj = d.kernel().fvar(hj_fv);
                            let hj_ty = mem_true(d, &p, rest, j);
                            let heq_fv = d.fresh_fvar();
                            let heq = d.kernel().fvar(heq_fv);
                            let ci = d.apply(constant, &[i]);
                            let f2j = d.apply(f2, &[j]);
                            let heq_ty = d.eq(ci, f2j);

                            let self_v = d.lemma(p.finset_mem_b_singleton_self, &[v]);
                            let moved = {
                                let motive = d.eq_motive(v, &|d, y| {
                                    let m = fs_mem(d, &p, sing_v, y);
                                    d.bool_eq(m, tr)
                                });
                                d.transport(v, motive, self_v, f2j, heq)
                            };
                            let avoided = d.apply(avoid, &[j, hj]);
                            let mf2 = fs_mem(d, &p, sing_v, f2j);
                            let flipped = d.bool_symm(mf2, fa, avoided);
                            let clash = d.bool_trans(fa, mf2, tr, flipped, moved);
                            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
                            let body = d.false_true_elim(false_ty, clash);

                            let s5 = d.lam_fv(heq_fv, heq_ty, body);
                            let s4 = d.lam_fv(hj_fv, hj_ty, s5);
                            let s3 = d.lam_fv(hi_fv, hi_ty, s4);
                            let s2 = d.lam_fv(j_fv, nat, s3);
                            d.lam_fv(i_fv, nat, s2)
                        };

                        let glued = d.lemma(
                            p.hall_is_matching_union,
                            &[sing_x, rest, nb, constant, f2, hm1, hm2_plain, collision],
                        );
                        let rebuilt = fs_union(d, &p, sing_x, rest);
                        let pointwise =
                            d.lemma(p.finset_mem_b_union_sdiff_self, &[s, sing_x, sing_sub]);
                        let glue_fn = d.const_app(p.hall_glue, &[constant, f2, sing_x]);
                        let moved = d.lemma(
                            p.hall_is_matching_congr,
                            &[rebuilt, s, nb, glue_fn, pointwise, glued],
                        );
                        let built = exists_intro_at(d, &p, ch, goal_pred, glue_fn, moved);

                        let with_hm2 = d.lam_fv(hm2_fv, hm2_ty, built);
                        d.lam_fv(f2_fv, ch, with_hm2)
                    };

                    let body = exists_elim_at(d, &p, ch, pred_rest, goal, minor_f2, rec_rest);
                    let with_hi0 = d.lam_fv(hi0_fv, hi0_ty, body);
                    d.lam_fv(i0_fv, nat, with_hi0)
                };

                let body = exists_elim_at(d, &p, nat, uw_pred, goal, minor_i0, have_i0);
                let with_hv = d.lam_fv(hv_fv, hv_ty, body);
                d.lam_fv(v_fv, nat, with_hv)
            };

            let body = exists_elim_at(d, &p, nat, cover_member_pred, goal, minor_v, have_v);
            let with_hx = d.lam_fv(hx_fv, hx_ty, body);
            d.lam_fv(x_fv, nat, with_hx)
        };

        let body = exists_elim_at(d, &p, nat, member_pred, goal, minor_x, have_member);
        let with_pos = d.lam_fv(hpos_fv, hpos_ty, body);
        d.lam_fv(hsearch_fv, search_false, with_pos)
    };

    // --- the bottom, and the branch ----------------------------------------
    let decided_empty = d.lemma(p.lt_or_ge, &[zero, card_s]);
    let pos_ty = d.lt(zero, card_s);
    let empty_ty = d.le(card_s, zero);
    let on_empty = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = d.lemma(p.hall_exists_is_matching_of_card_le_zero, &[s, nb, h]);
        d.lam_fv(h_fv, empty_ty, body)
    };
    let on_pos = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let decided_search = bool_true_or_false(d, &p, search);
        // `on_search_false` binds the search verdict FIRST and the positivity
        // second, so the `Or.rec` gets a function of the verdict alone.
        let right_case = {
            let hf_fv = d.fresh_fvar();
            let hf = d.kernel().fvar(hf_fv);
            let applied = d.apply(on_search_false, &[hf, h]);
            d.lam_fv(hf_fv, search_false, applied)
        };
        let body = or_elim(
            d,
            &p,
            search_true,
            search_false,
            goal,
            on_search_true,
            right_case,
            decided_search,
        );
        d.lam_fv(h_fv, pos_ty, body)
    };
    let step_body = or_elim(
        d,
        &p,
        pos_ty,
        empty_ty,
        goal,
        on_pos,
        on_empty,
        decided_empty,
    );

    let step = {
        let s6 = d.lam_fv(hall_fv, hall_ty, step_body);
        let s5 = d.lam_fv(hcard_fv, hcard_ty, s6);
        let s4 = d.lam_fv(nb_fv, fam, s5);
        let s3 = d.lam_fv(s_fv, fs, s4);
        let s2 = d.lam_fv(ih_fv, ih_ty, s3);
        d.lam_fv(n_fv, nat, s2)
    };
    // --- the theorem --------------------------------------------------------
    let s2_fv = d.fresh_fvar();
    let s2 = d.kernel().fvar(s2_fv);
    let nb2_fv = d.fresh_fvar();
    let nb2 = d.kernel().fvar(nb2_fv);
    let card_s2 = fs_card(d, &p, s2);
    let hall2_ty = hall_condition(d, &p, s2, nb2);
    let hall2_fv = d.fresh_fvar();
    let hall2 = d.kernel().fvar(hall2_fv);
    let concl = exists_matching(d, &p, s2, nb2);

    let zero_lvl = d.kernel().level_zero();
    let si = d.kernel().const_(p.strong_induction, vec![zero_lvl]);
    let refl_card = d.refl(card_s2);
    let applied = d.apply(si, &[motive, step, card_s2]);
    let proof = d.apply(applied, &[s2, nb2, refl_card, hall2]);

    let ty = {
        let s4 = d.arrow(hall2_ty, concl);
        let s3 = d.pi_fv(nb2_fv, fam, s4);
        d.pi_fv(s2_fv, fs, s3)
    };
    let value = {
        let s4 = d.lam_fv(hall2_fv, hall2_ty, proof);
        let s3 = d.lam_fv(nb2_fv, fam, s4);
        d.lam_fv(s2_fv, fs, s3)
    };
    d.declare_theorem(p.hall_sufficient, ty, value)
}

/// `Nat.Hall.marriage_iff : ∀ s nb,
/// Iff (HallCondition s nb) (Exists (fun f => IsMatching s nb f))`.
///
/// Hall's marriage theorem. The forward direction is
/// [`declare_sufficient`]; the backward direction is
/// `Nat.Hall.hallCondition_of_isMatching` (ADR-1608, necessity) under one
/// `Exists.rec` to name the matching.
fn declare_marriage_iff(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let fs = finset_ty(d, &p);
    let fam = family_ty(d, &p);
    let ch = choice_ty(d);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let nb_fv = d.fresh_fvar();
    let nb = d.kernel().fvar(nb_fv);

    let lhs = hall_condition(d, &p, s, nb);
    let rhs = exists_matching(d, &p, s, nb);
    let pred = matching_pred(d, &p, s, nb);

    let forward = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = d.lemma(p.hall_sufficient, &[s, nb, h]);
        d.lam_fv(h_fv, lhs, body)
    };
    let backward = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let minor = {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let hm_fv = d.fresh_fvar();
            let hm = d.kernel().fvar(hm_fv);
            let hm_ty = is_matching(d, &p, s, nb, f);
            let body = d.lemma(p.hall_condition_of_is_matching, &[s, nb, f, hm]);
            let with_hm = d.lam_fv(hm_fv, hm_ty, body);
            d.lam_fv(f_fv, ch, with_hm)
        };
        let body = exists_elim_at(d, &p, ch, pred, lhs, minor, h);
        d.lam_fv(h_fv, rhs, body)
    };

    let stmt = d.const_app(p.logic.iff, &[lhs, rhs]);
    let proof = d.const_app(p.logic.iff_intro, &[lhs, rhs, forward, backward]);

    let ty = {
        let inner = d.pi_fv(nb_fv, fam, stmt);
        d.pi_fv(s_fv, fs, inner)
    };
    let value = {
        let inner = d.lam_fv(nb_fv, fam, proof);
        d.lam_fv(s_fv, fs, inner)
    };
    d.declare_theorem(p.hall_marriage_iff, ty, value)
}

/// Declare Hall's marriage theorem, in dependency order.
pub(super) fn declare_hall_marriage_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_mem_b_sdiff_congr(d, p)?;
    declare_is_matching_of_family_sdiff(d, p)?;
    declare_mem_b_false_of_family_sdiff(d, p)?;
    declare_critical_b(d, p)?;
    declare_critical_b_congr(d, p)?;
    declare_sufficient(d, p)?;
    declare_marriage_iff(d, p)?;
    Ok(())
}
