//! `Nat.Finset.empty` and the singleton shelf (ADR-1630).
//!
//! # What was missing
//!
//! `Nat.Finset.singleton` has been DEFINED since `finset.rs` landed
//! (`singleton a := mk (fun k => beq k a) (succ a)`) and carried **zero**
//! lemmas: measured at 3,093 declarations,
//! `shape_search --const Nat.Finset.singleton` reported ABSENT while the
//! same-kind positive control `--const Nat.Finset.sdiff` reported FOUND 7.
//! `Nat.Finset.empty` did not exist at all (`--name-like Finset.empty`
//! ABSENT; the hint's `Nat.Subsets.empty` is a `Nat -> Bool`, not a carrier
//! value).
//!
//! The other half of the gap is the direction nothing could travel: a
//! POSITIVE cardinality could not be turned back into a member.
//! `Nat.countRange_eq_zero_of_all_false` goes the other way, and
//! `shape_search --const Nat.countRange --concl Exists` was ABSENT. Hall's
//! inductive step needs exactly that step — it picks an index out of a
//! non-empty index set — so it is landed here as
//! [`declare_exists_mem_b_of_card_pos`].
//!
//! # The shelf
//!
//! ```text
//! Nat.Finset.empty                := mk (fun _ => false) 0
//! Nat.Finset.memB_empty           : ∀ i, memB empty i = false
//! Nat.Finset.card_empty           : card empty = 0
//! Nat.Finset.memB_singleton       : ∀ a i, memB (singleton a) i = beq i a
//! Nat.Finset.memB_singleton_self  : ∀ a, memB (singleton a) a = true
//! Nat.Finset.eq_of_memB_singleton : ∀ a i, memB (singleton a) i = true → i = a
//! Nat.Finset.card_singleton       : ∀ a, card (singleton a) = 1
//! Nat.Finset.card_eq_zero_of_no_memB
//!                                 : ∀ s, (∀ i, memB s i = false) → card s = 0
//! Nat.Finset.exists_memB_of_card_pos
//!                                 : ∀ s, 0 < card s →
//!                                   ∃ k, k < bound s ∧ memB s k = true
//! ```
//!
//! # Two design notes
//!
//! **`memB_singleton` is the FULL equation, not the two one-way rules.**
//! The intro (`memB_singleton_self`) and elim (`eq_of_memB_singleton`) forms
//! each avoid a case split — `lt_succ_self` and `lt_bound_of_memB` supply the
//! bound side for free — but `card_singleton` needs
//! `memB (singleton a) k = false` at every `k < a`, which the one-way rules
//! cannot give. So the equation is proved once by `Nat.lt_or_ge` on
//! `(i, succ a)` and the rest is projection.
//!
//! **`exists_memB_of_card_pos` is a SEARCH, not a choice.** This kernel has no
//! classical choice, so the witness is computed: decide
//! `allBelow (fun k => notB (memB s k)) (bound s)`. A `false` loop hands the
//! index straight over through `Nat.Finset.allBelow_false_witness`; a `true`
//! loop says every index below the bound is a non-member, so
//! `Nat.countRange_eq_zero_of_all_false` collapses `card s` to `0` and the
//! positivity hypothesis is refuted by `Nat.lt_irrefl`. The bound is the
//! carrier's own `bound s`, which is the sharp one: `lt_bound_of_memB` says
//! nothing outside it can be a member anyway.

#![allow(clippy::many_single_char_names)]

use super::NatPrelude;
use super::graph::not_b;
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps, bool_true_or_false};
use super::subset_search::{not_b_false_elim, not_b_true_elim};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

// ---------------------------------------------------------------------------
// Term builders (this prelude's per-file convention is a private copy of these
// one-liners rather than a shared export).
// ---------------------------------------------------------------------------

/// The carrier constant `Nat.Finset`.
fn finset_ty(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    d.kernel().const_(p.finset, vec![])
}

/// `Nat.Finset.memB s i`.
fn fs_mem(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, i: ExprId) -> ExprId {
    d.const_app(p.finset_mem_b, &[s, i])
}

/// `Nat.Finset.memB s : Nat -> Bool`.
fn fs_mem_fn(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId) -> ExprId {
    d.const_app(p.finset_mem_b, &[s])
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

/// `Nat.Finset.empty`.
fn empty(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    d.kernel().const_(p.finset_empty, vec![])
}

/// `Nat.countRange f n`.
fn count_range(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.count_range, &[f, n])
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

/// `Exists.rec.{1}` into a `Prop` goal — `minor` takes the witness and its
/// property.
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

/// `fun k => And (Lt k n) (Eq Bool (f k) false)` —
/// `Nat.Finset.allBelow_false_witness`'s payload.
fn below_false_pred(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, n: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let lt = d.lt(k, n);
    let fk = d.apply(f, &[k]);
    let fal = d.bool_false();
    let is_false = d.bool_eq(fk, fal);
    let body = d.const_app(p.logic.and, &[lt, is_false]);
    d.lam_fv(k_fv, nat, body)
}

/// `fun k => And (Lt k (bound s)) (Eq Bool (memB s k) true)` — what
/// [`declare_exists_mem_b_of_card_pos`] produces a witness for.
fn member_witness_pred(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let bs = fs_bound(d, &p, s);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let lt = d.lt(k, bs);
    let mk = fs_mem(d, &p, s, k);
    let tru = d.bool_true();
    let is_true = d.bool_eq(mk, tru);
    let body = d.const_app(p.logic.and, &[lt, is_true]);
    d.lam_fv(k_fv, nat, body)
}

/// `Not (Eq Nat x y)` from `Lt x y`: an equation would carry the strict
/// inequality onto its own right-hand side, which `Nat.lt_irrefl` refutes.
/// The prelude has no `Nat.ne_of_lt`, and this is two lines.
fn ne_of_lt(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId, y: ExprId, hlt: ExprId) -> ExprId {
    let p = *p;
    let heq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(heq_fv);
    let heq_ty = d.eq(x, y);
    let motive = d.eq_motive(x, &|d, z| d.lt(z, y));
    let shifted = d.transport(x, motive, hlt, y, heq);
    let absurd = d.lemma(p.lt_irrefl, &[y, shifted]);
    d.lam_fv(heq_fv, heq_ty, absurd)
}

// ---------------------------------------------------------------------------
// `Nat.Finset.empty`.
// ---------------------------------------------------------------------------

/// `Nat.Finset.empty : Nat.Finset := mk (fun _ => false) 0` — the set with
/// nothing in it, and the only `Nat.Finset` whose bound is `zero`.
///
/// A CONSTANT, not a function of a bound: `memB` truncates at the bound in its
/// own definition, so `mk (fun _ => false) b` has the same members for every
/// `b` and there is nothing to parameterise over. `Nat.Finset.range 0` is
/// extensionally the same set but not definitionally this one (its stored
/// predicate is `fun _ => true`), and every consumer here wants the `false`
/// predicate so that [`declare_mem_b_empty`] is one `memB_of_bound_le`.
fn declare_empty(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);
    let never = {
        let k_fv = d.fresh_fvar();
        let f = d.bool_false();
        d.lam_fv(k_fv, nat, f)
    };
    let zero = d.zero();
    let value = d.const_app(p.finset_mk, &[never, zero]);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.finset_empty,
        uparams: vec![],
        ty: fs,
        value,
        hint: ReducibilityHint::Regular(4),
    })?;
    Ok(())
}

/// `Nat.Finset.memB_empty : ∀ i, Eq Bool (memB empty i) Bool.false` and
/// `Nat.Finset.card_empty : Eq Nat (card empty) zero`.
///
/// `bound empty` is `zero` by ι, so `Nat.zero_le` discharges
/// `memB_of_bound_le`'s hypothesis at every index — no case split, and in
/// particular no appeal to how `Nat.ble` reduces at a variable index. The
/// count then collapses through `Nat.countRange_eq_zero_of_all_false`, whose
/// hypothesis is BOUNDED (`∀ k, Lt k n → …`), so the pointwise fact is used
/// with its bound argument discarded.
fn declare_mem_b_empty(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fal = d.bool_false();

    // memB_empty
    {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let e = empty(d, &p);
        let hle = d.lemma(p.zero_le, &[i]);
        let proof = d.lemma(p.finset_mem_b_of_bound_le, &[e, i, hle]);
        let lhs = fs_mem(d, &p, e, i);
        let concl = d.bool_eq(lhs, fal);
        let ty = d.pi_fv(i_fv, nat, concl);
        let value = d.lam_fv(i_fv, nat, proof);
        d.declare_theorem(p.finset_mem_b_empty, ty, value)?;
    }

    // card_empty
    {
        let e = empty(d, &p);
        let m = fs_mem_fn(d, &p, e);
        let be = fs_bound(d, &p, e);
        let all_false = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let h_fv = d.fresh_fvar();
            let hyp_ty = d.lt(k, be);
            let at_k = d.lemma(p.finset_mem_b_empty, &[k]);
            let with_h = d.lam_fv(h_fv, hyp_ty, at_k);
            d.lam_fv(k_fv, nat, with_h)
        };
        let proof = d.lemma(p.count_range_eq_zero_of_all_false, &[m, be, all_false]);
        let zero = d.zero();
        let card = fs_card(d, &p, e);
        let ty = d.eq(card, zero);
        d.declare_theorem(p.finset_card_empty, ty, proof)?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// The singleton's membership equation.
// ---------------------------------------------------------------------------

/// `Nat.Finset.memB_singleton : ∀ a i,
/// Eq Bool (memB (singleton a) i) (Nat.beq i a)`.
///
/// `singleton a` is `mk (fun k => beq k a) (succ a)`, so BELOW the bound the
/// stored predicate is read literally (`memB_of_lt`, whose right-hand side
/// `pred (singleton a) i` is `beq i a` by ι) and ABOVE it both sides are
/// `false` — the left by `memB_of_bound_le`, the right because `succ a ≤ i`
/// makes `i = a` impossible, which is what `Nat.beq_eq_false_of_ne` consumes.
/// `Nat.lt_or_ge` at `(i, succ a)` is the split.
fn declare_mem_b_singleton(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fal = d.bool_false();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);

    let sa = singleton(d, &p, a);
    let succ_a = d.succ(a);
    let lhs = fs_mem(d, &p, sa, i);
    let rhs = d.beq(i, a);
    let goal = d.bool_eq(lhs, rhs);

    let below_ty = d.lt(i, succ_a);
    let above_ty = d.le(succ_a, i);

    let on_below = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        // `bound (singleton a)` is `succ a` by ι, so `memB_of_lt` applies with
        // the hypothesis as it stands.
        let read = d.lemma(p.finset_mem_b_of_lt, &[sa, i, h]);
        d.lam_fv(h_fv, below_ty, read)
    };
    let on_above = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let gone = d.lemma(p.finset_mem_b_of_bound_le, &[sa, i, h]);
        // `Le (succ a) i` IS `Lt a i`, so the disequality is `ne_of_lt`
        // pointed the other way round.
        let ne_rev = ne_of_lt(d, &p, a, i, h);
        // `Not (Eq Nat i a)` from `Not (Eq Nat a i)`.
        let ne = {
            let heq_fv = d.fresh_fvar();
            let heq = d.kernel().fvar(heq_fv);
            let heq_ty = d.eq(i, a);
            let flipped = d.symm(i, a, heq);
            let absurd = d.apply(ne_rev, &[flipped]);
            d.lam_fv(heq_fv, heq_ty, absurd)
        };
        let beq_false = d.lemma(p.beq_eq_false_of_ne, &[i, a, ne]);
        // `memB (singleton a) i = false = beq i a`.
        let back = d.bool_symm(rhs, fal, beq_false);
        let joined = d.bool_trans(lhs, fal, rhs, gone, back);
        d.lam_fv(h_fv, above_ty, joined)
    };

    let decided = d.lemma(p.lt_or_ge, &[i, succ_a]);
    let body = or_elim(d, &p, below_ty, above_ty, goal, on_below, on_above, decided);

    let ty = {
        let with_i = d.pi_fv(i_fv, nat, goal);
        d.pi_fv(a_fv, nat, with_i)
    };
    let value = {
        let with_i = d.lam_fv(i_fv, nat, body);
        d.lam_fv(a_fv, nat, with_i)
    };
    d.declare_theorem(p.finset_mem_b_singleton, ty, value)
}

/// `Nat.Finset.memB_singleton_self : ∀ a,
/// Eq Bool (memB (singleton a) a) Bool.true` and
/// `Nat.Finset.eq_of_memB_singleton : ∀ a i,
/// Eq Bool (memB (singleton a) i) Bool.true → Eq Nat i a`.
///
/// Both are [`declare_mem_b_singleton`] composed with a `beq` bridge:
/// `Nat.beq_refl` forward, `Nat.eq_of_beq_eq_true` backward. Together they are
/// the two rules a consumer actually cites; the equation itself is only needed
/// where a `false` value matters, which is [`declare_card_singleton`].
fn declare_singleton_rules(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let tru = d.bool_true();

    // memB_singleton_self
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let sa = singleton(d, &p, a);
        let lhs = fs_mem(d, &p, sa, a);
        let beq_aa = d.beq(a, a);
        let read = d.lemma(p.finset_mem_b_singleton, &[a, a]);
        let refl_true = d.lemma(p.beq_refl, &[a]);
        let proof = d.bool_trans(lhs, beq_aa, tru, read, refl_true);
        let concl = d.bool_eq(lhs, tru);
        let ty = d.pi_fv(a_fv, nat, concl);
        let value = d.lam_fv(a_fv, nat, proof);
        d.declare_theorem(p.finset_mem_b_singleton_self, ty, value)?;
    }

    // eq_of_memB_singleton
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let sa = singleton(d, &p, a);
        let lhs = fs_mem(d, &p, sa, i);
        let beq_ia = d.beq(i, a);
        let hyp_ty = d.bool_eq(lhs, tru);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let read = d.lemma(p.finset_mem_b_singleton, &[a, i]);
        let back = d.bool_symm(lhs, beq_ia, read);
        let beq_true = d.bool_trans(beq_ia, lhs, tru, back, h);
        let proof = d.lemma(p.eq_of_beq_eq_true, &[i, a, beq_true]);

        let concl = d.eq(i, a);
        let ty = {
            let with_h = d.arrow(hyp_ty, concl);
            let with_i = d.pi_fv(i_fv, nat, with_h);
            d.pi_fv(a_fv, nat, with_i)
        };
        let value = {
            let with_h = d.lam_fv(h_fv, hyp_ty, proof);
            let with_i = d.lam_fv(i_fv, nat, with_h);
            d.lam_fv(a_fv, nat, with_i)
        };
        d.declare_theorem(p.finset_eq_of_mem_b_singleton, ty, value)?;
    }

    Ok(())
}

/// `Nat.Finset.card_singleton : ∀ a, Eq Nat (card (singleton a)) (succ zero)`.
///
/// `card (singleton a)` is `countRange (memB (singleton a)) (succ a)` by δ,
/// and `bound (singleton a)` is `succ a` by ι, so the count peels at the top
/// index: `Nat.countRange_succ_of_true` at the witness
/// [`declare_singleton_rules`] supplies, over a body
/// `countRange (memB (singleton a)) a` that
/// `Nat.countRange_eq_zero_of_all_false` kills — every `k < a` is `≠ a`, so
/// `memB (singleton a) k` is `beq k a` is `false`.
///
/// The `1` is spelled `succ zero`, which is what `countRange_succ_of_true`
/// leaves behind; nothing is gained by routing it through another numeral.
fn declare_card_singleton(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fal = d.bool_false();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let sa = singleton(d, &p, a);
    let m = fs_mem_fn(d, &p, sa);
    let succ_a = d.succ(a);

    // Below the top index the singleton is empty.
    let all_false = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let hk_ty = d.lt(k, a);
        let ne = ne_of_lt(d, &p, k, a, hk);
        let beq_false = d.lemma(p.beq_eq_false_of_ne, &[k, a, ne]);
        let read = d.lemma(p.finset_mem_b_singleton, &[a, k]);
        let mk = fs_mem(d, &p, sa, k);
        let beq_ka = d.beq(k, a);
        let body = d.bool_trans(mk, beq_ka, fal, read, beq_false);
        let with_hk = d.lam_fv(hk_fv, hk_ty, body);
        d.lam_fv(k_fv, nat, with_hk)
    };
    let tail_zero = d.lemma(p.count_range_eq_zero_of_all_false, &[m, a, all_false]);

    let hself = d.lemma(p.finset_mem_b_singleton_self, &[a]);
    let peel = d.lemma(p.count_range_succ_of_true, &[m, a, hself]);

    // `peel : countRange m (succ a) = succ (countRange m a)`; rewrite the body.
    let top = count_range(d, &p, m, succ_a);
    let body_count = count_range(d, &p, m, a);
    let motive = d.eq_motive(body_count, &|d, x| {
        let sx = d.succ(x);
        d.eq(top, sx)
    });
    let zero = d.zero();
    let proof = d.transport(body_count, motive, peel, zero, tail_zero);

    let one = d.num(1);
    let card = fs_card(d, &p, sa);
    let concl = d.eq(card, one);
    let ty = d.pi_fv(a_fv, nat, concl);
    let value = d.lam_fv(a_fv, nat, proof);
    d.declare_theorem(p.finset_card_singleton, ty, value)
}

// ---------------------------------------------------------------------------
// Counting back and forth.
// ---------------------------------------------------------------------------

/// `Nat.Finset.card_eq_zero_of_no_memB : ∀ s,
/// (∀ i, Eq Bool (memB s i) Bool.false) → Eq Nat (card s) zero`.
///
/// The `Nat.Finset` reading of `Nat.countRange_eq_zero_of_all_false`. Stated
/// with an UNBOUNDED hypothesis (`∀ i`, not `∀ i < bound s`) because every
/// producer of it in this tree proves it at every index anyway — `memB` is
/// `false` above the bound for free.
fn declare_card_eq_zero_of_no_mem(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);
    let fal = d.bool_false();

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let hyp_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let mi = fs_mem(d, &p, s, i);
        let body = d.bool_eq(mi, fal);
        d.pi_fv(i_fv, nat, body)
    };

    let m = fs_mem_fn(d, &p, s);
    let bs = fs_bound(d, &p, s);
    let bounded = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_fv = d.fresh_fvar();
        let hk_ty = d.lt(k, bs);
        let at_k = d.apply(h, &[k]);
        let with_hk = d.lam_fv(hk_fv, hk_ty, at_k);
        d.lam_fv(k_fv, nat, with_hk)
    };
    let proof = d.lemma(p.count_range_eq_zero_of_all_false, &[m, bs, bounded]);

    let zero = d.zero();
    let card = fs_card(d, &p, s);
    let concl = d.eq(card, zero);
    let ty = {
        let with_h = d.arrow(hyp_ty, concl);
        d.pi_fv(s_fv, fs, with_h)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, proof);
        d.lam_fv(s_fv, fs, with_h)
    };
    d.declare_theorem(p.finset_card_eq_zero_of_no_mem_b, ty, value)
}

/// `Nat.Finset.card_pos_of_memB : ∀ s i, Eq Bool (memB s i) Bool.true →
/// Lt zero (card s)`.
///
/// The converse of [`declare_exists_mem_b_of_card_pos`], and much cheaper —
/// no search, because the witness is handed in. `lt_bound_of_memB` puts the
/// index inside the counting range, `Nat.countRange_succ_of_true` peels it off
/// as a `succ`, and `Nat.countRange_le_of_le` carries the resulting `≥ 1` up
/// to the set's own bound. `Lt i (bound s)` IS `Le (succ i) (bound s)`, which
/// is exactly what `countRange_le_of_le` wants, so no bridging step.
///
/// Landed with the shelf rather than with its consumer: Hall's induction needs
/// BOTH directions — this one to refute membership in the `card s = 0` branch,
/// the search to produce an index in every other branch.
fn declare_card_pos_of_mem_b(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);
    let tru = d.bool_true();

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let mi = fs_mem(d, &p, s, i);
    let hyp_ty = d.bool_eq(mi, tru);

    let m = fs_mem_fn(d, &p, s);
    let bs = fs_bound(d, &p, s);
    let zero = d.zero();
    let one = d.num(1);
    let succ_i = d.succ(i);

    let hlt = d.lemma(p.finset_lt_bound_of_mem_b, &[s, i, h]);
    let peel = d.lemma(p.count_range_succ_of_true, &[m, i, h]);
    let body_count = count_range(d, &p, m, i);
    let head_count = count_range(d, &p, m, succ_i);
    // `1 ≤ succ (countRange m i)`, then rewritten back along `peel`.
    let zero_le_body = d.lemma(p.zero_le, &[body_count]);
    let one_le_succ = d.lemma(p.le_succ_succ, &[zero, body_count, zero_le_body]);
    let succ_body = d.succ(body_count);
    let back = d.symm(head_count, succ_body, peel);
    let motive = d.eq_motive(succ_body, &|d, x| {
        let o = d.num(1);
        d.le(o, x)
    });
    let one_le_head = d.transport(succ_body, motive, one_le_succ, head_count, back);
    // `Lt i (bound s)` IS `Le (succ i) (bound s)`.
    let mono = d.lemma(p.count_range_le_of_le, &[m, succ_i, bs, hlt]);
    let tail_count = count_range(d, &p, m, bs);
    let proof = d.lemma(
        p.le_trans,
        &[one, head_count, tail_count, one_le_head, mono],
    );

    let card = fs_card(d, &p, s);
    let concl = d.lt(zero, card);
    let ty = {
        let with_h = d.arrow(hyp_ty, concl);
        let with_i = d.pi_fv(i_fv, nat, with_h);
        d.pi_fv(s_fv, fs, with_i)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, proof);
        let with_i = d.lam_fv(i_fv, nat, with_h);
        d.lam_fv(s_fv, fs, with_i)
    };
    d.declare_theorem(p.finset_card_pos_of_mem_b, ty, value)
}

/// `Nat.Finset.exists_memB_of_card_pos : ∀ s, Lt zero (card s) →
/// Exists (fun k => And (Lt k (bound s)) (Eq Bool (memB s k) Bool.true))`.
///
/// **The direction nothing in this tree could travel.** Every counting law
/// here turns members into a count; this turns a positive count back into a
/// member, and Hall's inductive step is its first consumer (it must pick an
/// index out of a non-empty index set with no choice principle available).
///
/// Constructive, and the recursion IS the search: decide the loop
/// `allBelow (fun k => notB (memB s k)) (bound s)`.
///
/// * `false` — `Nat.Finset.allBelow_false_witness` computes an index `k` below
///   the bound with `notB (memB s k) = false`, and `not_b_false_elim` reads
///   that as membership. The witness is re-introduced unchanged.
/// * `true` — `Nat.Finset.allBelow_true_at` says `notB (memB s k) = true` at
///   every `k` below the bound, so `not_b_true_elim` makes each a non-member,
///   `Nat.countRange_eq_zero_of_all_false` collapses `card s` to `zero`, and
///   the hypothesis becomes `Lt zero zero`, refuted by `Nat.lt_irrefl`.
fn declare_exists_mem_b_of_card_pos(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);
    let tru = d.bool_true();
    let fal = d.bool_false();

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let zero = d.zero();
    let card = fs_card(d, &p, s);
    let hyp_ty = d.lt(zero, card);
    let bs = fs_bound(d, &p, s);

    let target_pred = member_witness_pred(d, &p, s);
    let goal = exists_nat(d, &p, target_pred);

    // `fun k => notB (memB s k)`, the loop body.
    let absent = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let mk = fs_mem(d, &p, s, k);
        let body = not_b(d, &p, mk);
        d.lam_fv(k_fv, nat, body)
    };
    let loop_ = d.const_app(p.finset_all_below, &[absent, bs]);
    let loop_true = d.bool_eq(loop_, tru);
    let loop_false = d.bool_eq(loop_, fal);
    let decided = bool_true_or_false(d, &p, loop_);

    // The exhausted loop: nothing is a member, so the count is zero.
    let on_true = {
        let hl_fv = d.fresh_fvar();
        let hl = d.kernel().fvar(hl_fv);
        let m = fs_mem_fn(d, &p, s);
        let all_false = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let hk_fv = d.fresh_fvar();
            let hk = d.kernel().fvar(hk_fv);
            let hk_ty = d.lt(k, bs);
            let at_k = d.lemma(p.finset_all_below_true_at, &[absent, bs, hl, k, hk]);
            let mk = fs_mem(d, &p, s, k);
            let member_false = not_b_true_elim(d, &p, mk, at_k);
            let with_hk = d.lam_fv(hk_fv, hk_ty, member_false);
            d.lam_fv(k_fv, nat, with_hk)
        };
        let card_zero = d.lemma(p.count_range_eq_zero_of_all_false, &[m, bs, all_false]);
        let motive = d.eq_motive(card, &|d, x| {
            let z = d.zero();
            d.lt(z, x)
        });
        let shifted = d.transport(card, motive, h, zero, card_zero);
        let absurd = d.lemma(p.lt_irrefl, &[zero, shifted]);
        let elim = false_elim(d, &p, goal, absurd);
        d.lam_fv(hl_fv, loop_true, elim)
    };

    // The refuted loop: the search produced an index.
    let on_false = {
        let hl_fv = d.fresh_fvar();
        let hl = d.kernel().fvar(hl_fv);
        let found = d.lemma(p.finset_all_below_false_witness, &[absent, bs, hl]);
        let src_pred = below_false_pred(d, &p, absent, bs);
        let minor = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let hw_fv = d.fresh_fvar();
            let hw = d.kernel().fvar(hw_fv);
            let lt_ty = d.lt(k, bs);
            let mk = fs_mem(d, &p, s, k);
            let nk = not_b(d, &p, mk);
            let nk_false = d.bool_eq(nk, fal);
            let hw_ty = d.const_app(p.logic.and, &[lt_ty, nk_false]);
            let lt_pf = and_left(d, lt_ty, nk_false, hw);
            let neg_pf = and_right(d, lt_ty, nk_false, hw);
            let member = not_b_false_elim(d, &p, mk, neg_pf);
            let mem_ty = d.bool_eq(mk, tru);
            let pair = d.const_app(p.logic.and_intro, &[lt_ty, mem_ty, lt_pf, member]);
            let intro = exists_intro_nat(d, &p, target_pred, k, pair);
            let with_hw = d.lam_fv(hw_fv, hw_ty, intro);
            d.lam_fv(k_fv, nat, with_hw)
        };
        let body = exists_elim_nat(d, &p, src_pred, goal, minor, found);
        d.lam_fv(hl_fv, loop_false, body)
    };

    let answered = or_elim(
        d, &p, loop_true, loop_false, goal, on_true, on_false, decided,
    );

    let ty = {
        let with_h = d.arrow(hyp_ty, goal);
        d.pi_fv(s_fv, fs, with_h)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, answered);
        d.lam_fv(s_fv, fs, with_h)
    };
    d.declare_theorem(p.finset_exists_mem_b_of_card_pos, ty, value)
}

// ---------------------------------------------------------------------------
// Entry point.
// ---------------------------------------------------------------------------

/// Declare the empty-set/singleton shelf (ADR-1630).
pub(super) fn declare_finset_singleton_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_empty(d, p)?;
    declare_mem_b_empty(d, p)?;
    declare_mem_b_singleton(d, p)?;
    declare_singleton_rules(d, p)?;
    declare_card_singleton(d, p)?;
    declare_card_eq_zero_of_no_mem(d, p)?;
    declare_card_pos_of_mem_b(d, p)?;
    declare_exists_mem_b_of_card_pos(d, p)?;
    Ok(())
}
