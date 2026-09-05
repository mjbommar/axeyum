//! Hall's marriage theorem — the descent measure (ADR-1645).
//!
//! # What this file is for
//!
//! ADR-1644 closed both branches of Hall's critical-subset split and named the
//! one place where "a surprise is still possible": the arithmetic of the two
//! descent steps. `Nat.Hall.sufficient` runs
//! [`strong_induction`](super::NatPrelude::strong_induction) on `card s`, and
//! every recursive call has to hand the induction hypothesis a STRICTLY smaller
//! measure:
//!
//! ```text
//!   critical branch:      card t              < card s
//!   critical branch:      card (sdiff s t)    < card s
//!   non-critical branch:  card (sdiff s {x})  < card s
//! ```
//!
//! All three are instances of one identity and one positivity fact, and this
//! file lands them.
//!
//! # The identity, and why it is not `card_le_card_sdiff_add`
//!
//! The tree already had `Nat.Finset.card_le_card_sdiff_add`, an INEQUALITY
//! (`card s ≤ card (sdiff s t) + card t`) proved for arbitrary `s`, `t`. That
//! is not enough for a descent: `≤` in that direction bounds `card s` from
//! above, and a strict decrease needs the other direction with equality. For a
//! genuine subset the two sides are equal, and the equation is one line of
//! composition from ADR-1644's own shelf:
//!
//! ```text
//!   card s
//! = card (union t (sdiff s t))                   memB_union_sdiff_self, card_congr_of_memB
//! = card t + card (sdiff s t)                    card_union_of_disjoint
//! ```
//!
//! The first step is where the stored bounds would stop a definitional
//! argument — `union` SUMS its arguments' bounds, so the rebuilt set is not
//! `s` — and `card_congr_of_memB` is exactly the tool that does not care.
//! The second step's disjointness premise is `memB_sdiff_elim` read
//! contrapositively.
//!
//! Both descent inequalities then fall out of `Nat.add_lt_add_left` at the
//! summand that is `0`, because `Nat.add` recurses on its RIGHT argument and
//! so `add x zero` IS `x` by iota — no `add_zero` rewrite is needed on the
//! `card t` side, and one `add_comm` is needed on the other.
//!
//! # Why the statements are over `subsetFixed` and carry a bound hypothesis
//!
//! The brief for this lane asks for the measure lemmas stated over
//! `Nat.Finset.subsetFixed`, because that is what the inductive step's search
//! predicate produces — `existsSubset_of_search` returns a `t` together with
//! `subsetFixed s t = true`, never a pointwise inclusion.
//!
//! `subsetFixed s t = true` **does not imply** pointwise inclusion on its own,
//! and ADR-1644 says so with a committed counterexample:
//! `subsetFixed empty (singleton 0)` is `true`, because `bound empty` is `0`
//! and the loop answers no index at all. The missing side condition is
//! `Le (bound t) (bound s)`: above `bound s` a `t` no wider than `s` has no
//! members either, by `memB_of_bound_le`. That is
//! [`declare_mem_b_of_subset_fixed_of_bound_le`], and it is the bridge between
//! the search's output and the counting shelf's input. The caller in the
//! inductive step gets the hypothesis for free — `existsSubset_of_search`
//! returns `bound t = bound s` on the nose.
//!
//! # The shelf this file adds
//!
//! ```text
//! Nat.Finset.memB_of_subsetFixed_of_bound_le
//!     : ∀ s t, Le (bound t) (bound s) → subsetFixed s t = true →
//!       ∀ i, memB t i = true → memB s i = true
//! Nat.Finset.card_add_card_sdiff
//!     : ∀ s t, (∀ i, memB t i = true → memB s i = true) →
//!       card s = card t + card (sdiff s t)
//! Nat.Finset.card_lt_card_of_subsetFixed
//!     : ∀ s t, Le (bound t) (bound s) → subsetFixed s t = true →
//!       0 < card (sdiff s t) → card t < card s
//! Nat.Finset.card_sdiff_lt_card_of_subsetFixed
//!     : ∀ s t, Le (bound t) (bound s) → subsetFixed s t = true →
//!       0 < card t → card (sdiff s t) < card s
//! ```

use super::NatPrelude;
use super::helpers::and_right;
use super::ops::{NatDev, NatOps, bool_true_or_false};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

// ---------------------------------------------------------------------------
// Term builders (a private copy, per this prelude's per-file convention).
// ---------------------------------------------------------------------------

/// The carrier constant `Nat.Finset`.
fn finset_ty(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    d.kernel().const_(p.finset, vec![])
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

/// `Eq Bool (Nat.Finset.subsetFixed s t) Bool.true`.
fn subset_fixed_true(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, t: ExprId) -> ExprId {
    let sf = d.const_app(p.finset_subset_fixed, &[s, t]);
    let tr = d.bool_true();
    d.bool_eq(sf, tr)
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

/// `h : Eq Nat b c`, `hlt : Lt a b  ⊢  Lt a c` — rewriting the RIGHT side of a
/// strict order fact along a `Nat` equation.
///
/// `NatOps::le_congr` takes the pre-substitution type and is the wrong shape;
/// this is the plain `Eq.rec` with the order relation as the motive, the same
/// pattern `hall_theorem.rs`'s `le_rewrite_left` uses on the other side.
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
// The bridge from the search's output to the counting shelf's input.
// ---------------------------------------------------------------------------

/// `Nat.Finset.memB_of_subsetFixed_of_bound_le : ∀ s t,
/// Le (bound t) (bound s) → Eq Bool (subsetFixed s t) true →
/// ∀ i, Eq Bool (memB t i) true → Eq Bool (memB s i) true`.
///
/// `Nat.Finset.mem_of_subsetFixed` answers only BELOW `bound s`, which is
/// `allBelow`'s asymmetry and not a defect (ADR-1644): above the bound
/// `subsetFixed s t = true` is genuinely compatible with `t ⊄ s`. The extra
/// hypothesis `Le (bound t) (bound s)` closes exactly that tail — at an index
/// at or above `bound s` the index is also at or above `bound t`, so
/// `memB_of_bound_le` says `t` has no member there and the premise is refuted
/// rather than used. `Nat.lt_or_ge` splits.
fn declare_mem_b_of_subset_fixed_of_bound_le(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    let bt = fs_bound(d, &p, t);
    let bs = fs_bound(d, &p, s);
    let hb_ty = d.le(bt, bs);
    let hb_fv = d.fresh_fvar();
    let hb = d.kernel().fvar(hb_fv);

    let hsf_ty = subset_fixed_true(d, &p, s, t);
    let hsf_fv = d.fresh_fvar();
    let hsf = d.kernel().fvar(hsf_fv);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hi_ty = mem_true(d, &p, t, i);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);
    let goal = mem_true(d, &p, s, i);

    let lt_ty = d.lt(i, bs);
    let ge_ty = d.le(bs, i);
    let decided = d.lemma(p.lt_or_ge, &[i, bs]);

    // Below `bound s`: the elimination rule applies verbatim.
    let on_lt = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = d.lemma(p.finset_mem_of_subset_fixed, &[s, t, i, hsf, h, hi]);
        d.lam_fv(h_fv, lt_ty, body)
    };
    // At or above it: `t` is no wider than `s`, so `memB t i` is `false` and
    // the hypothesis `memB t i = true` is the contradiction.
    let on_ge = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let above_t = d.lemma(p.le_trans, &[bt, bs, i, hb, h]);
        let t_false = d.lemma(p.finset_mem_b_of_bound_le, &[t, i, above_t]);
        let mti = fs_mem(d, &p, t, i);
        let tr = d.bool_true();
        let fa = d.bool_false();
        let flipped = d.bool_symm(mti, fa, t_false);
        let clash = d.bool_trans(fa, mti, tr, flipped, hi);
        let body = d.false_true_elim(goal, clash);
        d.lam_fv(h_fv, ge_ty, body)
    };
    let proof = or_elim(d, &p, lt_ty, ge_ty, goal, on_lt, on_ge, decided);

    let ty = {
        let with_hi = d.arrow(hi_ty, goal);
        let with_i = d.pi_fv(i_fv, nat, with_hi);
        let with_sf = d.arrow(hsf_ty, with_i);
        let with_b = d.arrow(hb_ty, with_sf);
        let with_t = d.pi_fv(t_fv, fs, with_b);
        d.pi_fv(s_fv, fs, with_t)
    };
    let value = {
        let with_hi = d.lam_fv(hi_fv, hi_ty, proof);
        let with_i = d.lam_fv(i_fv, nat, with_hi);
        let with_sf = d.lam_fv(hsf_fv, hsf_ty, with_i);
        let with_b = d.lam_fv(hb_fv, hb_ty, with_sf);
        let with_t = d.lam_fv(t_fv, fs, with_b);
        d.lam_fv(s_fv, fs, with_t)
    };
    d.declare_theorem(p.finset_mem_b_of_subset_fixed_of_bound_le, ty, value)
}

// ---------------------------------------------------------------------------
// The identity the two descent inequalities share.
// ---------------------------------------------------------------------------

/// `Nat.Finset.card_add_card_sdiff : ∀ s t,
/// (∀ i, Eq Bool (memB t i) true → Eq Bool (memB s i) true) →
/// Eq Nat (card s) (add (card t) (card (sdiff s t)))`.
///
/// Splitting a set at a subset splits its count. Two of ADR-1644's lemmas
/// composed, with the disjointness premise read off `memB_sdiff_elim`:
///
/// ```text
///   card s
/// = card (union t (sdiff s t))    memB_union_sdiff_self + card_congr_of_memB
/// = card t + card (sdiff s t)     card_union_of_disjoint
/// ```
///
/// **Not** `card_le_card_sdiff_add`, which is the same shape as an inequality
/// in the useless direction and holds without the subset hypothesis; a descent
/// needs the equation.
///
/// The disjointness argument is a `Bool` case split rather than an unfolding of
/// `setDiff`: `bool_true_or_false` decides `memB (sdiff s t) i`, and on the
/// `true` side `memB_sdiff_elim` returns `memB t i = false`, which contradicts
/// the premise. That is shorter than pushing the hypothesis through both of
/// `setDiff`'s selectors and does not depend on which argument it scrutinises
/// first.
fn declare_card_add_card_sdiff(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    let hsub_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let in_t = mem_true(d, &p, t, i);
        let in_s = mem_true(d, &p, s, i);
        let step = d.arrow(in_t, in_s);
        d.pi_fv(i_fv, nat, step)
    };
    let hsub_fv = d.fresh_fvar();
    let hsub = d.kernel().fvar(hsub_fv);

    let diff = fs_sdiff(d, &p, s, t);

    // `∀ i, memB t i = true → memB (sdiff s t) i = false`.
    let disjoint = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_ty = mem_true(d, &p, t, i);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let goal = mem_false(d, &p, diff, i);

        let mdi = fs_mem(d, &p, diff, i);
        let decided = bool_true_or_false(d, &p, mdi);
        let tr = d.bool_true();
        let fa = d.bool_false();
        let left_ty = d.bool_eq(mdi, tr);
        let right_ty = d.bool_eq(mdi, fa);

        // `i ∈ sdiff s t` says `i ∉ t`, and `i ∈ t` is the premise.
        let left_case = {
            let hm_fv = d.fresh_fvar();
            let hm = d.kernel().fvar(hm_fv);
            let pair = d.lemma(p.finset_mem_b_sdiff_elim, &[s, t, i, hm]);
            let in_s = mem_true(d, &p, s, i);
            let not_t = mem_false(d, &p, t, i);
            let t_false = and_right(d, in_s, not_t, pair);
            let mti = fs_mem(d, &p, t, i);
            let flipped = d.bool_symm(mti, fa, t_false);
            let clash = d.bool_trans(fa, mti, tr, flipped, hi);
            let body = d.false_true_elim(goal, clash);
            d.lam_fv(hm_fv, left_ty, body)
        };
        // `i ∉ sdiff s t` IS the goal.
        let right_case = {
            let hm_fv = d.fresh_fvar();
            let hm = d.kernel().fvar(hm_fv);
            d.lam_fv(hm_fv, right_ty, hm)
        };

        let answered = or_elim(
            d, &p, left_ty, right_ty, goal, left_case, right_case, decided,
        );
        let with_hi = d.lam_fv(hi_fv, hi_ty, answered);
        d.lam_fv(i_fv, nat, with_hi)
    };

    let rebuilt = fs_union(d, &p, t, diff);
    let split = d.lemma(p.finset_card_union_of_disjoint, &[t, diff, disjoint]);
    let pointwise = d.lemma(p.finset_mem_b_union_sdiff_self, &[s, t, hsub]);
    let rebuilt_eq = d.lemma(p.finset_card_congr_of_mem_b, &[rebuilt, s, pointwise]);

    let card_s = fs_card(d, &p, s);
    let card_rebuilt = fs_card(d, &p, rebuilt);
    let card_t = fs_card(d, &p, t);
    let card_diff = fs_card(d, &p, diff);
    let sum = d.add(card_t, card_diff);

    let back = d.symm(card_rebuilt, card_s, rebuilt_eq);
    let proof = d.trans(card_s, card_rebuilt, sum, back, split);

    let ty = {
        let concl = d.eq(card_s, sum);
        let with_h = d.arrow(hsub_ty, concl);
        let with_t = d.pi_fv(t_fv, fs, with_h);
        d.pi_fv(s_fv, fs, with_t)
    };
    let value = {
        let with_h = d.lam_fv(hsub_fv, hsub_ty, proof);
        let with_t = d.lam_fv(t_fv, fs, with_h);
        d.lam_fv(s_fv, fs, with_t)
    };
    d.declare_theorem(p.finset_card_add_card_sdiff, ty, value)
}

// ---------------------------------------------------------------------------
// The two descent inequalities.
// ---------------------------------------------------------------------------

/// `Nat.Finset.card_lt_card_of_subsetFixed : ∀ s t,
/// Le (bound t) (bound s) → Eq Bool (subsetFixed s t) true →
/// Lt zero (card (sdiff s t)) → Lt (card t) (card s)`.
///
/// The measure the CRITICAL branch's first recursive call needs: a subset that
/// misses at least one member is strictly smaller.
///
/// `Nat.add_lt_add_left (card t) zero (card (sdiff s t))` applied to the
/// positivity hypothesis has type `Lt (add (card t) zero) (add (card t) …)`,
/// and `add x zero` IS `x` — `Nat.add` recurses on its RIGHT argument, so the
/// left side is already the goal's by iota and no `add_zero` rewrite appears in
/// the term. One transport along
/// [`declare_card_add_card_sdiff`] moves the right side back to `card s`.
///
/// "Misses at least one member" is spelled `0 < card (sdiff s t)` rather than
/// "∃ x, x ∈ s ∧ x ∉ t" because that is what the caller has:
/// `Nat.Finset.card_pos_of_memB` turns a witness into it in one step, and the
/// counting form is what the arithmetic consumes.
fn declare_card_lt_card_of_subset_fixed(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let fs = finset_ty(d, &p);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    let bt = fs_bound(d, &p, t);
    let bs = fs_bound(d, &p, s);
    let hb_ty = d.le(bt, bs);
    let hb_fv = d.fresh_fvar();
    let hb = d.kernel().fvar(hb_fv);

    let hsf_ty = subset_fixed_true(d, &p, s, t);
    let hsf_fv = d.fresh_fvar();
    let hsf = d.kernel().fvar(hsf_fv);

    let diff = fs_sdiff(d, &p, s, t);
    let card_diff = fs_card(d, &p, diff);
    let zero = d.zero();
    let hpos_ty = d.lt(zero, card_diff);
    let hpos_fv = d.fresh_fvar();
    let hpos = d.kernel().fvar(hpos_fv);

    let card_s = fs_card(d, &p, s);
    let card_t = fs_card(d, &p, t);
    let sum = d.add(card_t, card_diff);

    let subset = d.lemma(p.finset_mem_b_of_subset_fixed_of_bound_le, &[s, t, hb, hsf]);
    let identity = d.lemma(p.finset_card_add_card_sdiff, &[s, t, subset]);

    // `Lt (add (card t) zero) (add (card t) (card (sdiff s t)))`; the left side
    // reduces to `card t` by iota.
    let grown = d.lemma(p.add_lt_add_left, &[card_t, zero, card_diff, hpos]);
    let back = d.symm(card_s, sum, identity);
    let proof = lt_rewrite_right(d, card_t, sum, card_s, back, grown);

    let ty = {
        let concl = d.lt(card_t, card_s);
        let with_pos = d.arrow(hpos_ty, concl);
        let with_sf = d.arrow(hsf_ty, with_pos);
        let with_b = d.arrow(hb_ty, with_sf);
        let with_t = d.pi_fv(t_fv, fs, with_b);
        d.pi_fv(s_fv, fs, with_t)
    };
    let value = {
        let with_pos = d.lam_fv(hpos_fv, hpos_ty, proof);
        let with_sf = d.lam_fv(hsf_fv, hsf_ty, with_pos);
        let with_b = d.lam_fv(hb_fv, hb_ty, with_sf);
        let with_t = d.lam_fv(t_fv, fs, with_b);
        d.lam_fv(s_fv, fs, with_t)
    };
    d.declare_theorem(p.finset_card_lt_card_of_subset_fixed, ty, value)
}

/// `Nat.Finset.card_sdiff_lt_card_of_subsetFixed : ∀ s t,
/// Le (bound t) (bound s) → Eq Bool (subsetFixed s t) true →
/// Lt zero (card t) → Lt (card (sdiff s t)) (card s)`.
///
/// The measure the CRITICAL branch's second recursive call needs, and the one
/// the NON-CRITICAL branch needs at `t = singleton x`: removing a nonempty
/// subset strictly shrinks the set.
///
/// The same identity, and one `Nat.add_comm` more than
/// [`declare_card_lt_card_of_subset_fixed`], because `add_lt_add_left` grows
/// the RIGHT summand and here the surviving one is on the left.
fn declare_card_sdiff_lt_card_of_subset_fixed(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let fs = finset_ty(d, &p);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    let bt = fs_bound(d, &p, t);
    let bs = fs_bound(d, &p, s);
    let hb_ty = d.le(bt, bs);
    let hb_fv = d.fresh_fvar();
    let hb = d.kernel().fvar(hb_fv);

    let hsf_ty = subset_fixed_true(d, &p, s, t);
    let hsf_fv = d.fresh_fvar();
    let hsf = d.kernel().fvar(hsf_fv);

    let card_t = fs_card(d, &p, t);
    let zero = d.zero();
    let hpos_ty = d.lt(zero, card_t);
    let hpos_fv = d.fresh_fvar();
    let hpos = d.kernel().fvar(hpos_fv);

    let diff = fs_sdiff(d, &p, s, t);
    let card_diff = fs_card(d, &p, diff);
    let card_s = fs_card(d, &p, s);
    let sum = d.add(card_t, card_diff);
    let flipped_sum = d.add(card_diff, card_t);

    let subset = d.lemma(p.finset_mem_b_of_subset_fixed_of_bound_le, &[s, t, hb, hsf]);
    let identity = d.lemma(p.finset_card_add_card_sdiff, &[s, t, subset]);

    // `Lt (add (card d) zero) (add (card d) (card t))`, i.e. `card d < card d + card t`.
    let grown = d.lemma(p.add_lt_add_left, &[card_diff, zero, card_t, hpos]);
    // Commute to the identity's orientation, then transport onto `card s`.
    let comm = d.lemma(p.add_comm, &[card_diff, card_t]);
    let oriented = lt_rewrite_right(d, card_diff, flipped_sum, sum, comm, grown);
    let back = d.symm(card_s, sum, identity);
    let proof = lt_rewrite_right(d, card_diff, sum, card_s, back, oriented);

    let ty = {
        let concl = d.lt(card_diff, card_s);
        let with_pos = d.arrow(hpos_ty, concl);
        let with_sf = d.arrow(hsf_ty, with_pos);
        let with_b = d.arrow(hb_ty, with_sf);
        let with_t = d.pi_fv(t_fv, fs, with_b);
        d.pi_fv(s_fv, fs, with_t)
    };
    let value = {
        let with_pos = d.lam_fv(hpos_fv, hpos_ty, proof);
        let with_sf = d.lam_fv(hsf_fv, hsf_ty, with_pos);
        let with_b = d.lam_fv(hb_fv, hb_ty, with_sf);
        let with_t = d.lam_fv(t_fv, fs, with_b);
        d.lam_fv(s_fv, fs, with_t)
    };
    d.declare_theorem(p.finset_card_sdiff_lt_card_of_subset_fixed, ty, value)
}

/// Declare the descent measure, in dependency order.
pub(super) fn declare_hall_descent_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_mem_b_of_subset_fixed_of_bound_le(d, p)?;
    declare_card_add_card_sdiff(d, p)?;
    declare_card_lt_card_of_subset_fixed(d, p)?;
    declare_card_sdiff_lt_card_of_subset_fixed(d, p)?;
    Ok(())
}
