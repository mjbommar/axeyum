//! `Nat.countRange_permute` — **counting over `[0,n)` is invariant under any
//! injective self-map of `[0,n)`**, the primitive
//! `docs/plan/status/320-totient-bijection.md` named as the one genuinely
//! missing piece under `Nat.totient_mul_of_coprime` (and so under the two
//! remaining `ml430` totient mirrors).
//!
//! ## Statement, and why this statement
//!
//! ```text
//! Nat.countRange_permute :
//!   ∀ (f : Nat → Bool) (σ : Nat → Nat) (n : Nat),
//!     Nat.InjectiveOn σ n → Nat.MapsInto σ n →
//!     Eq Nat (countRange f n) (countRange (fun k => f (σ k)) n)
//! ```
//!
//! It is the exact `countRange` mirror of `Int.prodRange_permute`
//! (`int_prelude/prod.rs`), deliberately — same hypotheses, same argument
//! order, same `f`-outside/`σ`-generalized induction — so the two can be read
//! against each other.
//!
//! The CRT consumer needs precisely this and nothing more general. For
//! coprime `m`, `n` the map `g x := (x mod m) * n + (x mod n)` is an
//! injective self-map of `[0, m*n)`, and the coprimality predicate satisfies
//! `[gcd x (m*n) = 1] = [gcd (x mod m) m = 1 ∧ gcd (x mod n) n = 1]` — i.e.
//! `P x = Q (g x)` — for **every** `x`, not merely `x < m*n`. So the consumer
//! reaches `countRange Q (m*n) = countRange (Q ∘ g) (m*n)` from this theorem
//! and then `countRange (Q ∘ g) (m*n) = countRange P (m*n)` from the
//! *unconditional* `Nat.countRange_congr` that already existed. Nothing here
//! is stated over a `P`/`Q` pair or over a bounded pointwise agreement,
//! because the argument that consumes it does not need either.
//!
//! ## Route
//!
//! Induction on `n`, `f` quantified OUTSIDE the recursion and the motive
//! generalized over `σ` (generalizing over `f` instead does not close — the
//! recursive call reuses the same `f` and only `σ` moves). At `succ n`:
//!
//! - `Nat.injective_on_imp_surjective_on` (`finite.rs`'s pigeonhole) gives
//!   `i0 < succ n` with `σ i0 = n`.
//! - **`i0 = n`** — `σ` already fixes the top index. `InjectiveOn σ n` is pure
//!   bound-weakening and `MapsInto σ n` follows from `σ i ≠ n` for `i < n`, so
//!   the induction hypothesis applies to `σ` itself.
//! - **`i0 < n`** — restrict along the single-point override
//!   `τ := fun k => point_override σ i0 (σ n) k`, whose `InjectiveOn τ n` and
//!   `MapsInto τ n` are *exactly* `Nat.restrict_injective` and
//!   `Nat.restrict_maps_into` (`finite.rs`, built for
//!   `Int.prodRange_permute`'s identical step and reused here unchanged).
//!
//! ## What replaces `Int.prodRange_swap`
//!
//! `Int.prodRange_permute`'s `i0 < n` branch has to move the value sitting at
//! slot `i0` up to slot `n`, and pays for it with `Int.prodRange_swap` — built
//! on an adjacent-transposition induction that `wilson.rs` records as taking
//! three drafts. Counting needs no such thing, because `countRange`'s
//! accumulator is `Nat.add`: two predicates that agree on `[0,n)` **except
//! possibly at one index** have counts that differ exactly as their two values
//! at that index do. That is [`declare_count_range_point_change`], one
//! induction with an `add`-rearrangement in each branch, and it is what makes
//! this file far shorter than its `Int` counterpart.
//!
//! ## What is declared
//!
//! - [`declare_count_range_congr_lt`] — `Nat.countRange_congr_lt`, the
//!   BOUNDED pointwise congruence. `Nat.countRange_congr` (`totient.rs`) is
//!   unconditional and its own doc comment says to add this form when a proof
//!   needs it; this is that proof.
//! - [`declare_count_range_point_change`] — `Nat.countRange_point_change`,
//!   the one-index-differs counting law described above. Its two agreement
//!   hypotheses are split at `i0` (`k < i0` and `i0 < k < n`) rather than
//!   stated as a single `k ≠ i0`, so neither producing nor consuming them
//!   needs any `Not`-elimination.
//! - [`declare_count_range_permute`] — the headline.
//! - [`declare_count_range_product`] — `Nat.countRange_product`, the second
//!   half the CRT argument needs and the one that is **coprimality-
//!   INDEPENDENT**: counting a predicate over `[0, n*m)` that factors through
//!   the block decomposition `y = n*a + b` (`b < n`) multiplies the two
//!   factors' counts. Keeping this apart from the totient identity — which is
//!   NOT coprimality-independent — is the whole lesson of the false
//!   `count_range_row_major` claim `docs/plan/status/301-totient-
//!   multiplicative.md` recorded and `316-queue-sweep.md` refuted.
//!
//! No new `Definition` is introduced, so nothing here can be well-typed and
//! mean the wrong thing.

use super::NatPrelude;
use super::finite::{
    override_eq_at, override_eq_gt, override_eq_lt, point_override, select_nat_false,
    select_nat_true,
};
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps, bool_true_or_false};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

// ============================================================================
// Local copies of shared devices (this prelude's own per-file convention).
// ============================================================================

/// `countRange f n`.
fn count_range(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.count_range, &[f, n])
}

/// `bool_select_nat (b) 1 0` — the per-index contribution `countRange`
/// accumulates.
fn sel(d: &mut NatDev<'_>, b: ExprId) -> ExprId {
    let one = d.num(1);
    let zero = d.zero();
    d.bool_select_nat(b, one, zero)
}

/// `fun k => f (g k)`.
fn compose(d: &mut NatDev<'_>, f: ExprId, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let gk = d.apply(g, &[k]);
    let body = d.apply(f, &[gk]);
    d.lam_fv(k_fv, nat, body)
}

/// `h : Lt i m ⊢ Lt i (succ m)` (local copy of `finite.rs`'s `lift_lt`).
fn lift_lt(d: &mut NatDev<'_>, p: &NatPrelude, i: ExprId, m: ExprId, h: ExprId) -> ExprId {
    let p = *p;
    let succ_i = d.succ(i);
    let sm = d.succ(m);
    let m_le_sm = d.lemma(p.le_succ, &[m]);
    d.lemma(p.le_trans, &[succ_i, m, sm, h, m_le_sm])
}

/// `False.rec (fun _ => goal) contradiction : goal`.
fn absurd(d: &mut NatDev<'_>, p: &NatPrelude, goal: ExprId, contradiction: ExprId) -> ExprId {
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, goal, BinderInfo::Default);
    let zero = d.kernel().level_zero();
    let rec = d.kernel().const_(p.logic.false_rec, vec![zero]);
    d.apply(rec, &[motive, contradiction])
}

/// Non-dependent `Or.rec` into `goal`.
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

/// Non-dependent `Exists.rec` over `Nat` into a `Prop` goal.
fn exists_elim(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    predicate: ExprId,
    goal: ExprId,
    minor: ExprId,
    proof: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let level_one = d.level_one();
    let exists_const = d.kernel().const_(p.logic.exists_, vec![level_one]);
    let exists_ty = d.apply(exists_const, &[nat, predicate]);
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, exists_ty, goal, BinderInfo::Default);
    let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![level_one]);
    d.apply(exists_rec, &[nat, predicate, motive, minor, proof])
}

/// `h : Eq Bool a b ⊢ Eq Nat (body a) (body b)` (local copy of `totient.rs`'s
/// `bool_congr_nat`).
fn bool_congr_nat(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    body: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = body(d, a);
    let motive = d.bool_eq_motive(a, &|d, x| {
        let fx = body(d, x);
        d.eq(fa, fx)
    });
    let refl_case = d.refl(fa);
    d.bool_transport(a, motive, refl_case, b, h)
}

/// `h : Eq Nat x y ⊢ Eq Bool (body x) (body y)` — the Nat-hypothesis,
/// Bool-conclusion congruence (`prod.rs`'s `nat_eq_to_int`, retargeted).
fn nat_congr_bool(
    d: &mut NatDev<'_>,
    x: ExprId,
    y: ExprId,
    h: ExprId,
    body: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fx = body(d, x);
    let motive = d.eq_motive(x, &|d, t| {
        let ft = body(d, t);
        d.bool_eq(fx, ft)
    });
    let refl_case = d.bool_refl(fx);
    d.transport(x, motive, refl_case, y, h)
}

/// `Eq Nat (add (add x u) s) (add (add x s) u)` — the only `add`
/// rearrangement this file needs, from `add_assoc` and `add_comm`.
fn add_swap_right(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId, u: ExprId, s: ExprId) -> ExprId {
    let p = *p;
    let xu = d.add(x, u);
    let start = d.add(xu, s);
    let us = d.add(u, s);
    let mid = d.add(x, us);
    let su = d.add(s, u);
    let mid2 = d.add(x, su);
    let xs = d.add(x, s);
    let end_ = d.add(xs, u);

    let step1 = d.lemma(p.add_assoc, &[x, u, s]);
    let comm = d.lemma(p.add_comm, &[u, s]);
    let step2 = d.congr(us, su, comm, &|d, t| d.add(x, t));
    let assoc2 = d.lemma(p.add_assoc, &[x, s, u]);
    let step3 = d.symm(end_, mid2, assoc2);

    let (_e, proof) = d.chain(start, &[(mid, step1), (mid2, step2), (end_, step3)]);
    proof
}

// ============================================================================
// `Nat.countRange_congr_lt`.
// ============================================================================

/// The bounded pointwise-agreement hypothesis
/// `∀ i, Lt i bound → Eq Bool (f i) (g i)`.
fn agree_below(d: &mut NatDev<'_>, f: ExprId, g: ExprId, bound: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let fi = d.apply(f, &[i]);
    let gi = d.apply(g, &[i]);
    let eq = d.bool_eq(fi, gi);
    let hyp = d.lt(i, bound);
    let body = d.arrow(hyp, eq);
    d.pi_fv(i_fv, nat, body)
}

/// `Nat.countRange_congr_lt : ∀ f g n, (∀ i, Lt i n → Eq Bool (f i) (g i)) →
/// Eq Nat (countRange f n) (countRange g n)`.
///
/// The bounded companion to `Nat.countRange_congr` (`totient.rs`), whose own
/// doc comment says to add this form when a proof needs it. Induction on `n`
/// with the hypothesis carried INSIDE the motive (an arrow motive, so the
/// induction hypothesis is a function to apply) — `countRange_le_of_subset`
/// in `finite_set.rs` is the template.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
pub(super) fn declare_count_range_congr_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut NatDev<'_>, x: ExprId| {
        let hyp = agree_below(d, f, g, x);
        let lhs = count_range(d, &p, f, x);
        let rhs = count_range(d, &p, g, x);
        let concl = d.eq(lhs, rhs);
        d.arrow(hyp, concl)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            let hyp = agree_below(d, f, g, zero);
            let refl_case = d.refl(zero);
            let h_fv = d.fresh_fvar();
            d.lam_fv(h_fv, hyp, refl_case)
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let hyp_ty = agree_below(d, f, g, sj);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            // Restrict the hypothesis from `succ j` down to `j`.
            let restricted = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let hi_fv = d.fresh_fvar();
                let hi = d.kernel().fvar(hi_fv);
                let hi_ty = d.lt(i, j);
                let lifted = lift_lt(d, &p, i, j, hi);
                let applied = d.apply(h, &[i, lifted]);
                let with_hi = d.lam_fv(hi_fv, hi_ty, applied);
                d.lam_fv(i_fv, nat, with_hi)
            };
            let ih_result = d.apply(ih, &[restricted]);

            let f_prior = count_range(d, &p, f, j);
            let g_prior = count_range(d, &p, g, j);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let f_sel = sel(d, fj);

            let start = d.add(f_prior, f_sel);
            let mid = d.add(g_prior, f_sel);
            let step1 = d.congr(f_prior, g_prior, ih_result, &|d, t| d.add(t, f_sel));

            let g_sel = sel(d, gj);
            let end_ = d.add(g_prior, g_sel);
            let j_lt_sj = d.lemma(p.lt_succ_self, &[j]);
            let at_j = d.apply(h, &[j, j_lt_sj]);
            let step2 = bool_congr_nat(d, fj, gj, at_j, &|d, x| {
                let sv = sel(d, x);
                d.add(g_prior, sv)
            });

            let (_e, chained) = d.chain(start, &[(mid, step1), (end_, step2)]);
            d.lam_fv(h_fv, hyp_ty, chained)
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_g = d.pi_fv(g_fv, pred_ty, over_n);
        d.pi_fv(f_fv, pred_ty, over_g)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_g = d.lam_fv(g_fv, pred_ty, over_n);
        d.lam_fv(f_fv, pred_ty, over_g)
    };
    d.declare_theorem(p.count_range_congr_lt, ty, value)
}

// ============================================================================
// `Nat.countRange_point_change`.
// ============================================================================

/// `∀ k, Lt k i0 → Eq Bool (a k) (b k)`.
fn agree_strictly_below(d: &mut NatDev<'_>, a: ExprId, b: ExprId, i0: ExprId) -> ExprId {
    agree_below(d, a, b, i0)
}

/// `∀ k, Lt i0 k → Lt k bound → Eq Bool (a k) (b k)`.
fn agree_above(d: &mut NatDev<'_>, a: ExprId, b: ExprId, i0: ExprId, bound: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let ak = d.apply(a, &[k]);
    let bk = d.apply(b, &[k]);
    let eq = d.bool_eq(ak, bk);
    let upper = d.lt(k, bound);
    let inner = d.arrow(upper, eq);
    let lower = d.lt(i0, k);
    let body = d.arrow(lower, inner);
    d.pi_fv(k_fv, nat, body)
}

/// `Nat.countRange_point_change : ∀ a b i0 n, Lt i0 n →
///   (∀ k, Lt k i0 → Eq Bool (a k) (b k)) →
///   (∀ k, Lt i0 k → Lt k n → Eq Bool (a k) (b k)) →
///   Eq Nat (add (countRange a n) (sel (b i0))) (add (countRange b n) (sel (a i0)))`
///
/// Two predicates agreeing on `[0,n)` except possibly at the single index
/// `i0` have counts that differ exactly as their values at `i0` do — stated
/// ADDITIVELY, since `Nat.sub` is truncated and the subtractive form would
/// need a side condition this one does not.
///
/// Induction on `n`, with `Lt i0 n` and both agreement hypotheses carried in
/// the motive. `n = 0` is vacuous (`not_lt_zero`). At `succ j`, `lt_or_eq_of_le`
/// splits `Le i0 j`:
///
/// - `Lt i0 j` — the induction hypothesis applies at `j`, the top index `j`
///   is off `i0` so `a j = b j`, and the two sides differ by one
///   [`add_swap_right`] on each side.
/// - `Eq i0 j` — the top index IS `i0`; below it the two predicates agree
///   everywhere, so [`declare_count_range_congr_lt`] equates the two prefix
///   counts and one [`add_swap_right`] finishes.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_count_range_point_change(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let i0_fv = d.fresh_fvar();
    let i0 = d.kernel().fvar(i0_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let conclusion = |d: &mut NatDev<'_>, x: ExprId| {
        let ca = count_range(d, &p, a, x);
        let cb = count_range(d, &p, b, x);
        let ai0 = d.apply(a, &[i0]);
        let bi0 = d.apply(b, &[i0]);
        let sa = sel(d, ai0);
        let sb = sel(d, bi0);
        let lhs = d.add(ca, sb);
        let rhs = d.add(cb, sa);
        d.eq(lhs, rhs)
    };

    let motive = |d: &mut NatDev<'_>, x: ExprId| {
        let concl = conclusion(d, x);
        let above = agree_above(d, a, b, i0, x);
        let inner = d.arrow(above, concl);
        let below = agree_strictly_below(d, a, b, i0);
        let with_below = d.arrow(below, inner);
        let bound = d.lt(i0, x);
        d.arrow(bound, with_below)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            let bound_ty = d.lt(i0, zero);
            let below_ty = agree_strictly_below(d, a, b, i0);
            let above_ty = agree_above(d, a, b, i0, zero);
            let concl = conclusion(d, zero);

            let hb_fv = d.fresh_fvar();
            let hb = d.kernel().fvar(hb_fv);
            let contradiction = d.lemma(p.not_lt_zero, &[i0, hb]);
            let body = absurd(d, &p, concl, contradiction);

            let ha_fv = d.fresh_fvar();
            let with_above = d.lam_fv(ha_fv, above_ty, body);
            let hbl_fv = d.fresh_fvar();
            let with_below = d.lam_fv(hbl_fv, below_ty, with_above);
            d.lam_fv(hb_fv, bound_ty, with_below)
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let bound_ty = d.lt(i0, sj);
            let below_ty = agree_strictly_below(d, a, b, i0);
            let above_ty = agree_above(d, a, b, i0, sj);
            let goal = conclusion(d, sj);

            let hb_fv = d.fresh_fvar();
            let hb = d.kernel().fvar(hb_fv);
            let hbelow_fv = d.fresh_fvar();
            let hbelow = d.kernel().fvar(hbelow_fv);
            let habove_fv = d.fresh_fvar();
            let habove = d.kernel().fvar(habove_fv);

            // Shared abbreviations for both branches.
            let ca_j = count_range(d, &p, a, j);
            let cb_j = count_range(d, &p, b, j);
            let aj = d.apply(a, &[j]);
            let bj = d.apply(b, &[j]);
            let sa_j = sel(d, aj);
            let sb_j = sel(d, bj);
            let ai0 = d.apply(a, &[i0]);
            let bi0 = d.apply(b, &[i0]);
            let sa_i0 = sel(d, ai0);
            let sb_i0 = sel(d, bi0);

            let le_i0_j = d.lemma(p.le_of_lt_succ, &[i0, j, hb]);
            let disj = d.lemma(p.lt_or_eq_of_le, &[i0, j, le_i0_j]);
            let lt_ty = d.lt(i0, j);
            let eq_ty = d.eq(i0, j);

            // --- branch `Lt i0 j`: the induction hypothesis carries it. -----
            let on_lt = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);

                let above_j = {
                    let k_fv = d.fresh_fvar();
                    let k = d.kernel().fvar(k_fv);
                    let hlo_fv = d.fresh_fvar();
                    let hlo = d.kernel().fvar(hlo_fv);
                    let hhi_fv = d.fresh_fvar();
                    let hhi = d.kernel().fvar(hhi_fv);
                    let lifted = lift_lt(d, &p, k, j, hhi);
                    let applied = d.apply(habove, &[k, hlo, lifted]);
                    let hhi_ty = d.lt(k, j);
                    let with_hi = d.lam_fv(hhi_fv, hhi_ty, applied);
                    let hlo_ty = d.lt(i0, k);
                    let with_lo = d.lam_fv(hlo_fv, hlo_ty, with_hi);
                    d.lam_fv(k_fv, nat, with_lo)
                };
                let ih_result = d.apply(ih, &[h, hbelow, above_j]);

                let j_lt_sj = d.lemma(p.lt_succ_self, &[j]);
                let at_j = d.apply(habove, &[j, h, j_lt_sj]);

                // (Ca j + sa j) + sb i0
                //   = (Ca j + sb i0) + sa j     [add_swap_right]
                //   = (Cb j + sa i0) + sa j     [ih]
                //   = (Cb j + sa j)  + sa i0    [add_swap_right]
                //   = (Cb j + sb j)  + sa i0    [a j = b j]
                let lhs0 = {
                    let inner = d.add(ca_j, sa_j);
                    d.add(inner, sb_i0)
                };
                let s1_rhs = {
                    let inner = d.add(ca_j, sb_i0);
                    d.add(inner, sa_j)
                };
                let step1 = add_swap_right(d, &p, ca_j, sa_j, sb_i0);

                let s2_rhs = {
                    let inner = d.add(cb_j, sa_i0);
                    d.add(inner, sa_j)
                };
                let lhs_ih = d.add(ca_j, sb_i0);
                let rhs_ih = d.add(cb_j, sa_i0);
                let step2 = d.congr(lhs_ih, rhs_ih, ih_result, &|d, t| d.add(t, sa_j));

                let s3_rhs = {
                    let inner = d.add(cb_j, sa_j);
                    d.add(inner, sa_i0)
                };
                let step3 = add_swap_right(d, &p, cb_j, sa_i0, sa_j);

                let s4_rhs = {
                    let inner = d.add(cb_j, sb_j);
                    d.add(inner, sa_i0)
                };
                let step4 = bool_congr_nat(d, aj, bj, at_j, &|d, x| {
                    let sv = sel(d, x);
                    let inner = d.add(cb_j, sv);
                    d.add(inner, sa_i0)
                });

                let (_e, chained) = d.chain(
                    lhs0,
                    &[
                        (s1_rhs, step1),
                        (s2_rhs, step2),
                        (s3_rhs, step3),
                        (s4_rhs, step4),
                    ],
                );
                d.lam_fv(h_fv, lt_ty, chained)
            };

            // --- branch `Eq i0 j`: the top index IS `i0`. -------------------
            let on_eq = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);

                // `∀ k, Lt k j → a k = b k`, from `hbelow` and `i0 = j`.
                let below_j = {
                    let k_fv = d.fresh_fvar();
                    let k = d.kernel().fvar(k_fv);
                    let hk_fv = d.fresh_fvar();
                    let hk = d.kernel().fvar(hk_fv);
                    let hk_ty = d.lt(k, j);
                    let j_eq_i0 = d.symm(i0, j, h);
                    let motive_bound = d.eq_motive(j, &|d, x| d.lt(k, x));
                    let k_lt_i0 = d.transport(j, motive_bound, hk, i0, j_eq_i0);
                    let applied = d.apply(hbelow, &[k, k_lt_i0]);
                    let with_hk = d.lam_fv(hk_fv, hk_ty, applied);
                    d.lam_fv(k_fv, nat, with_hk)
                };
                let prefix_eq = d.lemma(p.count_range_congr_lt, &[a, b, j, below_j]);

                // `a i0 = a j` and `b i0 = b j`, from `i0 = j`.
                let a_at = nat_congr_bool(d, i0, j, h, &|d, x| d.apply(a, &[x]));
                let b_at = nat_congr_bool(d, i0, j, h, &|d, x| d.apply(b, &[x]));
                let b_at_rev = d.bool_symm(bi0, bj, b_at);

                // (Ca j + sa j) + sb i0
                //   = (Cb j + sa j)  + sb i0    [prefix_eq]
                //   = (Cb j + sa i0) + sb i0    [a i0 = a j, backwards]
                //   = (Cb j + sb i0) + sa i0    [add_swap_right]
                //   = (Cb j + sb j)  + sa i0    [b i0 = b j]
                let lhs0 = {
                    let inner = d.add(ca_j, sa_j);
                    d.add(inner, sb_i0)
                };
                let s1_rhs = {
                    let inner = d.add(cb_j, sa_j);
                    d.add(inner, sb_i0)
                };
                let step1 = d.congr(ca_j, cb_j, prefix_eq, &|d, t| {
                    let inner = d.add(t, sa_j);
                    d.add(inner, sb_i0)
                });

                let s2_rhs = {
                    let inner = d.add(cb_j, sa_i0);
                    d.add(inner, sb_i0)
                };
                let a_at_rev = d.bool_symm(ai0, aj, a_at);
                let step2 = bool_congr_nat(d, aj, ai0, a_at_rev, &|d, x| {
                    let sv = sel(d, x);
                    let inner = d.add(cb_j, sv);
                    d.add(inner, sb_i0)
                });

                let s3_rhs = {
                    let inner = d.add(cb_j, sb_i0);
                    d.add(inner, sa_i0)
                };
                let step3 = add_swap_right(d, &p, cb_j, sa_i0, sb_i0);

                let s4_rhs = {
                    let inner = d.add(cb_j, sb_j);
                    d.add(inner, sa_i0)
                };
                let step4 = bool_congr_nat(d, bi0, bj, b_at, &|d, x| {
                    let sv = sel(d, x);
                    let inner = d.add(cb_j, sv);
                    d.add(inner, sa_i0)
                });
                let _ = b_at_rev;

                let (_e, chained) = d.chain(
                    lhs0,
                    &[
                        (s1_rhs, step1),
                        (s2_rhs, step2),
                        (s3_rhs, step3),
                        (s4_rhs, step4),
                    ],
                );
                d.lam_fv(h_fv, eq_ty, chained)
            };

            let body = or_elim(d, &p, lt_ty, eq_ty, goal, on_lt, on_eq, disj);
            let with_above = d.lam_fv(habove_fv, above_ty, body);
            let with_below = d.lam_fv(hbelow_fv, below_ty, with_above);
            d.lam_fv(hb_fv, bound_ty, with_below)
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_i0 = d.pi_fv(i0_fv, nat, over_n);
        let over_b = d.pi_fv(b_fv, pred_ty, over_i0);
        d.pi_fv(a_fv, pred_ty, over_b)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_i0 = d.lam_fv(i0_fv, nat, over_n);
        let over_b = d.lam_fv(b_fv, pred_ty, over_i0);
        d.lam_fv(a_fv, pred_ty, over_b)
    };
    d.declare_theorem(p.count_range_point_change, ty, value)
}

// ============================================================================
// `Nat.countRange_permute`.
// ============================================================================

/// `∀ σ, InjectiveOn σ x → MapsInto σ x →
///   Eq Nat (countRange f x) (countRange (fun k => f (σ k)) x)` — the
/// induction motive, generalized over `σ` but NOT over `f`.
fn permute_motive(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, x: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let sigma_fv = d.fresh_fvar();
    let sigma = d.kernel().fvar(sigma_fv);
    let inj_ty = d.const_app(p.injective_on, &[sigma, x]);
    let maps_ty = d.const_app(p.maps_into, &[sigma, x]);
    let composed = compose(d, f, sigma);
    let lhs = count_range(d, &p, f, x);
    let rhs = count_range(d, &p, composed, x);
    let concl = d.eq(lhs, rhs);
    let with_maps = d.arrow(maps_ty, concl);
    let with_inj = d.arrow(inj_ty, with_maps);
    d.pi_fv(sigma_fv, fn_ty, with_inj)
}

/// Branch `i0 = n` of the successor step: `σ` already fixes the top index, so
/// no restriction is needed — `InjectiveOn σ n` is bound-weakening and
/// `MapsInto σ n` follows from `σ i ≠ n` for `i < n`.
#[allow(clippy::too_many_arguments)]
fn permute_branch_fixed(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    f: ExprId,
    n: ExprId,
    sigma: ExprId,
    inj_sigma: ExprId,
    maps_sigma: ExprId,
    i0: ExprId,
    heq: ExprId,
    sigma_i0_eq_n: ExprId,
    ih: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();

    let sigma_i0 = d.apply(sigma, &[i0]);
    let sigma_n = d.apply(sigma, &[n]);
    let motive_sigma = d.eq_motive(i0, &|d, x| {
        let sx = d.apply(sigma, &[x]);
        d.eq(sx, n)
    });
    let sigma_n_eq_n = d.transport(i0, motive_sigma, sigma_i0_eq_n, n, heq);
    let _ = sigma_i0;
    let n_eq_sigma_n = d.symm(sigma_n, n, sigma_n_eq_n);

    // `InjectiveOn σ n`: pure bound-weakening.
    let inj_n = {
        let i_fv = d.fresh_fvar();
        let ivar = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let jvar = d.kernel().fvar(j_fv);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let hj_fv = d.fresh_fvar();
        let hj = d.kernel().fvar(hj_fv);
        let heq2_fv = d.fresh_fvar();
        let heq2 = d.kernel().fvar(heq2_fv);
        let si = d.apply(sigma, &[ivar]);
        let sj = d.apply(sigma, &[jvar]);
        let heq2_ty = d.eq(si, sj);
        let i_lt_sn = lift_lt(d, &p, ivar, n, hi);
        let j_lt_sn = lift_lt(d, &p, jvar, n, hj);
        let result = d.apply(inj_sigma, &[ivar, jvar, i_lt_sn, j_lt_sn, heq2]);
        let with_heq2 = d.lam_fv(heq2_fv, heq2_ty, result);
        let hj_ty = d.lt(jvar, n);
        let with_hj = d.lam_fv(hj_fv, hj_ty, with_heq2);
        let hi_ty = d.lt(ivar, n);
        let with_hi = d.lam_fv(hi_fv, hi_ty, with_hj);
        let with_j = d.lam_fv(j_fv, nat, with_hi);
        d.lam_fv(i_fv, nat, with_j)
    };

    // `MapsInto σ n`.
    let maps_n = {
        let i_fv = d.fresh_fvar();
        let ivar = d.kernel().fvar(i_fv);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let hi_ty = d.lt(ivar, n);
        let i_lt_sn = lift_lt(d, &p, ivar, n, hi);
        let si = d.apply(sigma, &[ivar]);
        let si_lt_sn = d.apply(maps_sigma, &[ivar, i_lt_sn]);
        let si_le_n = d.lemma(p.le_of_lt_succ, &[si, n, si_lt_sn]);

        let lt_sin = d.lt(si, n);
        let eq_sin = d.eq(si, n);
        let disj = d.lemma(p.lt_or_eq_of_le, &[si, n, si_le_n]);

        let on_lt = {
            let hh_fv = d.fresh_fvar();
            let hh = d.kernel().fvar(hh_fv);
            d.lam_fv(hh_fv, lt_sin, hh)
        };
        let on_eq = {
            let e_fv = d.fresh_fvar();
            let e = d.kernel().fvar(e_fv);
            let si_eq_sigma_n = d.trans(si, n, sigma_n, e, n_eq_sigma_n);
            let n_lt_sn = d.lemma(p.lt_succ_self, &[n]);
            let i_eq_n = d.apply(inj_sigma, &[ivar, n, i_lt_sn, n_lt_sn, si_eq_sigma_n]);
            let motive = d.eq_motive(ivar, &|d, x| d.lt(x, n));
            let n_lt_n = d.transport(ivar, motive, hi, n, i_eq_n);
            let false_pf = d.lemma(p.lt_irrefl, &[n, n_lt_n]);
            let goal = d.lt(si, n);
            let body = absurd(d, &p, goal, false_pf);
            d.lam_fv(e_fv, eq_sin, body)
        };
        let target = d.lt(si, n);
        let si_lt_n = or_elim(d, &p, lt_sin, eq_sin, target, on_lt, on_eq, disj);
        let with_hi = d.lam_fv(hi_fv, hi_ty, si_lt_n);
        d.lam_fv(i_fv, nat, with_hi)
    };

    let ih_result = d.apply(ih, &[sigma, inj_n, maps_n]);

    let composed = compose(d, f, sigma);
    let f_prior = count_range(d, &p, f, n);
    let g_prior = count_range(d, &p, composed, n);
    let f_n = d.apply(f, &[n]);
    let f_sigma_n = d.apply(f, &[sigma_n]);
    let sel_fn = sel(d, f_n);
    let sel_fsn = sel(d, f_sigma_n);

    let start = d.add(f_prior, sel_fn);
    let mid = d.add(g_prior, sel_fn);
    let step1 = d.congr(f_prior, g_prior, ih_result, &|d, t| d.add(t, sel_fn));
    let end_ = d.add(g_prior, sel_fsn);
    let fn_eq = nat_congr_bool(d, n, sigma_n, n_eq_sigma_n, &|d, x| d.apply(f, &[x]));
    let step2 = bool_congr_nat(d, f_n, f_sigma_n, fn_eq, &|d, x| {
        let sv = sel(d, x);
        d.add(g_prior, sv)
    });
    let (_e, proof) = d.chain(start, &[(mid, step1), (end_, step2)]);
    proof
}

/// Branch `i0 < n` of the successor step: restrict along the single-point
/// override `τ := fun k => point_override σ i0 (σ n) k`
/// (`Nat.restrict_injective` / `Nat.restrict_maps_into`), then close with
/// `Nat.countRange_point_change` — `f ∘ τ` and `f ∘ σ` agree on `[0,n)`
/// everywhere except at `i0`.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn permute_branch_override(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    f: ExprId,
    n: ExprId,
    sigma: ExprId,
    inj_sigma: ExprId,
    maps_sigma: ExprId,
    i0: ExprId,
    lt_i0_n: ExprId,
    sigma_i0_eq_n: ExprId,
    ih: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let sn = d.succ(n);
    let _ = sn;

    let v = d.apply(sigma, &[n]);
    let tau = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = point_override(d, sigma, i0, v, k);
        d.lam_fv(k_fv, nat, body)
    };

    let inj_tau = d.const_app(p.restrict_injective, &[sigma, i0, n, inj_sigma, lt_i0_n]);
    let maps_tau = d.const_app(
        p.restrict_maps_into,
        &[sigma, i0, n, inj_sigma, maps_sigma, lt_i0_n, sigma_i0_eq_n],
    );
    let ih_result = d.apply(ih, &[tau, inj_tau, maps_tau]);

    let f_tau = compose(d, f, tau);
    let f_sigma = compose(d, f, sigma);

    // `f ∘ τ` and `f ∘ σ` agree strictly below `i0` and strictly above it.
    let below = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let hk_ty = d.lt(k, i0);
        let ov_eq = override_eq_lt(d, &p, sigma, i0, v, k, hk);
        let ov = point_override(d, sigma, i0, v, k);
        let sk = d.apply(sigma, &[k]);
        let body = nat_congr_bool(d, ov, sk, ov_eq, &|d, x| d.apply(f, &[x]));
        let with_hk = d.lam_fv(hk_fv, hk_ty, body);
        d.lam_fv(k_fv, nat, with_hk)
    };
    let above = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hlo_fv = d.fresh_fvar();
        let hlo = d.kernel().fvar(hlo_fv);
        let hhi_fv = d.fresh_fvar();
        let hhi_ty = d.lt(k, n);
        let ov_eq = override_eq_gt(d, &p, sigma, i0, v, k, hlo);
        let ov = point_override(d, sigma, i0, v, k);
        let sk = d.apply(sigma, &[k]);
        let body = nat_congr_bool(d, ov, sk, ov_eq, &|d, x| d.apply(f, &[x]));
        let with_hi = d.lam_fv(hhi_fv, hhi_ty, body);
        let hlo_ty = d.lt(i0, k);
        let with_lo = d.lam_fv(hlo_fv, hlo_ty, with_hi);
        d.lam_fv(k_fv, nat, with_lo)
    };

    let change = d.const_app(
        p.count_range_point_change,
        &[f_tau, f_sigma, i0, n, lt_i0_n, below, above],
    );

    // `change : C(f∘τ) n + sel (f (σ i0)) = C(f∘σ) n + sel (f (τ i0))`,
    // with `σ i0 = n` and `τ i0 = σ n`.
    let c_tau = count_range(d, &p, f_tau, n);
    let c_sigma = count_range(d, &p, f_sigma, n);
    let sigma_i0 = d.apply(sigma, &[i0]);
    let f_sigma_i0 = d.apply(f, &[sigma_i0]);
    let tau_i0 = point_override(d, sigma, i0, v, i0);
    let f_tau_i0 = d.apply(f, &[tau_i0]);
    let sel_fsi0 = sel(d, f_sigma_i0);
    let sel_fti0 = sel(d, f_tau_i0);

    let f_n = d.apply(f, &[n]);
    let f_v = d.apply(f, &[v]);
    let sel_fn = sel(d, f_n);
    let sel_fv = sel(d, f_v);

    // Rewrite both index arguments to their reduced forms.
    let change_lhs = d.add(c_tau, sel_fsi0);
    let change_rhs = d.add(c_sigma, sel_fti0);

    let f_si0_eq_fn = nat_congr_bool(d, sigma_i0, n, sigma_i0_eq_n, &|d, x| d.apply(f, &[x]));
    let rewrite_lhs = bool_congr_nat(d, f_sigma_i0, f_n, f_si0_eq_fn, &|d, x| {
        let sv = sel(d, x);
        d.add(c_tau, sv)
    });
    let tau_i0_eq_v = override_eq_at(d, &p, sigma, i0, v);
    let f_ti0_eq_fv = nat_congr_bool(d, tau_i0, v, tau_i0_eq_v, &|d, x| d.apply(f, &[x]));
    let rewrite_rhs = bool_congr_nat(d, f_tau_i0, f_v, f_ti0_eq_fv, &|d, x| {
        let sv = sel(d, x);
        d.add(c_sigma, sv)
    });

    let reduced_lhs = d.add(c_tau, sel_fn);
    let reduced_rhs = d.add(c_sigma, sel_fv);
    let lhs_rev = d.symm(change_lhs, reduced_lhs, rewrite_lhs);
    let via = d.trans(reduced_lhs, change_lhs, change_rhs, lhs_rev, change);
    let reduced = d.trans(reduced_lhs, change_rhs, reduced_rhs, via, rewrite_rhs);

    // `countRange f (succ n) ≡ C(f) n + sel (f n)`
    //   = C(f∘τ) n + sel (f n)      [ih]
    //   = C(f∘σ) n + sel (f (σ n))  [reduced]
    //   ≡ countRange (f∘σ) (succ n)
    let c_f = count_range(d, &p, f, n);
    let start = d.add(c_f, sel_fn);
    let step1 = d.congr(c_f, c_tau, ih_result, &|d, t| d.add(t, sel_fn));
    let (_e, proof) = d.chain(start, &[(reduced_lhs, step1), (reduced_rhs, reduced)]);
    proof
}

/// The successor step: the pigeonhole locates `i0 < succ n` with `σ i0 = n`,
/// and `lt_or_eq_of_le` splits into [`permute_branch_override`] (`i0 < n`) and
/// [`permute_branch_fixed`] (`i0 = n`).
fn permute_step(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, n: ExprId, ih: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let sn = d.succ(n);

    let sigma_fv = d.fresh_fvar();
    let sigma = d.kernel().fvar(sigma_fv);
    let inj_ty = d.const_app(p.injective_on, &[sigma, sn]);
    let inj_fv = d.fresh_fvar();
    let inj_sigma = d.kernel().fvar(inj_fv);
    let maps_ty = d.const_app(p.maps_into, &[sigma, sn]);
    let maps_fv = d.fresh_fvar();
    let maps_sigma = d.kernel().fvar(maps_fv);

    let composed = compose(d, f, sigma);
    let lhs = count_range(d, &p, f, sn);
    let rhs = count_range(d, &p, composed, sn);
    let target = d.eq(lhs, rhs);

    let surj = d.const_app(
        p.injective_on_imp_surjective_on,
        &[sn, sigma, inj_sigma, maps_sigma],
    );
    let n_lt_sn = d.lemma(p.lt_succ_self, &[n]);
    let ex = d.apply(surj, &[n, n_lt_sn]);

    let predicate = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let bound = d.lt(i, sn);
        let si = d.apply(sigma, &[i]);
        let eqn = d.eq(si, n);
        let body = d.const_app(p.logic.and, &[bound, eqn]);
        d.lam_fv(i_fv, nat, body)
    };

    let minor = {
        let i0_fv = d.fresh_fvar();
        let i0 = d.kernel().fvar(i0_fv);
        let hand_fv = d.fresh_fvar();
        let hand = d.kernel().fvar(hand_fv);
        let bound_ty = d.lt(i0, sn);
        let si0 = d.apply(sigma, &[i0]);
        let eqn_ty = d.eq(si0, n);
        let hand_ty = d.const_app(p.logic.and, &[bound_ty, eqn_ty]);
        let h_i0_lt_sn = and_left(d, bound_ty, eqn_ty, hand);
        let sigma_i0_eq_n = and_right(d, bound_ty, eqn_ty, hand);

        let le_i0_n = d.lemma(p.le_of_lt_succ, &[i0, n, h_i0_lt_sn]);
        let disj = d.lemma(p.lt_or_eq_of_le, &[i0, n, le_i0_n]);
        let lt_i0_n_ty = d.lt(i0, n);
        let eq_i0_n_ty = d.eq(i0, n);

        let on_lt = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = permute_branch_override(
                d,
                &p,
                f,
                n,
                sigma,
                inj_sigma,
                maps_sigma,
                i0,
                h,
                sigma_i0_eq_n,
                ih,
            );
            d.lam_fv(h_fv, lt_i0_n_ty, body)
        };
        let on_eq = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = permute_branch_fixed(
                d,
                &p,
                f,
                n,
                sigma,
                inj_sigma,
                maps_sigma,
                i0,
                h,
                sigma_i0_eq_n,
                ih,
            );
            d.lam_fv(h_fv, eq_i0_n_ty, body)
        };

        let body = or_elim(d, &p, lt_i0_n_ty, eq_i0_n_ty, target, on_lt, on_eq, disj);
        let with_hand = d.lam_fv(hand_fv, hand_ty, body);
        d.lam_fv(i0_fv, nat, with_hand)
    };

    let for_sigma = exists_elim(d, &p, predicate, target, minor, ex);
    let with_maps = d.lam_fv(maps_fv, maps_ty, for_sigma);
    let with_inj = d.lam_fv(inj_fv, inj_ty, with_maps);
    d.lam_fv(sigma_fv, fn_ty, with_inj)
}

/// `Nat.countRange_permute : ∀ f σ n, InjectiveOn σ n → MapsInto σ n →
/// Eq Nat (countRange f n) (countRange (fun k => f (σ k)) n)`.
///
/// See the module doc for the route.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
pub(super) fn declare_count_range_permute(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let stmt = permute_motive(d, &p, f, n);
    let proof = d.induct(
        &|d, x| permute_motive(d, &p, f, x),
        &|d| {
            let nat_inner = d.nat_ty();
            let fn_ty = d.arrow(nat_inner, nat_inner);
            let zero = d.zero();
            let sigma_fv = d.fresh_fvar();
            let sigma = d.kernel().fvar(sigma_fv);
            let inj_ty = d.const_app(p.injective_on, &[sigma, zero]);
            let maps_ty = d.const_app(p.maps_into, &[sigma, zero]);
            let body = d.refl(zero);
            let maps_fv = d.fresh_fvar();
            let with_maps = d.lam_fv(maps_fv, maps_ty, body);
            let inj_fv = d.fresh_fvar();
            let with_inj = d.lam_fv(inj_fv, inj_ty, with_maps);
            d.lam_fv(sigma_fv, fn_ty, with_inj)
        },
        &|d, m, ih| permute_step(d, &p, f, m, ih),
        n,
    );

    // The induction necessarily binds `n` (its target) outside `σ` (generalized
    // in the motive). Re-abstract to the natural reading order `∀ f σ n`: the
    // binders are introduced by free variable, so their ORDER is free, and
    // nothing in `σ`'s type depends on `n`.
    let _ = stmt;
    let fn_ty = d.arrow(nat, nat);
    let sigma_fv = d.fresh_fvar();
    let sigma = d.kernel().fvar(sigma_fv);
    let inj_ty = d.const_app(p.injective_on, &[sigma, n]);
    let inj_fv = d.fresh_fvar();
    let inj = d.kernel().fvar(inj_fv);
    let maps_ty = d.const_app(p.maps_into, &[sigma, n]);
    let maps_fv = d.fresh_fvar();
    let maps = d.kernel().fvar(maps_fv);
    let applied = d.apply(proof, &[sigma, inj, maps]);

    let composed = compose(d, f, sigma);
    let lhs = count_range(d, &p, f, n);
    let rhs = count_range(d, &p, composed, n);
    let concl = d.eq(lhs, rhs);

    let ty = {
        let with_maps = d.arrow(maps_ty, concl);
        let with_inj = d.arrow(inj_ty, with_maps);
        let over_n = d.pi_fv(n_fv, nat, with_inj);
        let over_sigma = d.pi_fv(sigma_fv, fn_ty, over_n);
        d.pi_fv(f_fv, pred_ty, over_sigma)
    };
    let value = {
        let with_maps = d.lam_fv(maps_fv, maps_ty, applied);
        let with_inj = d.lam_fv(inj_fv, inj_ty, with_maps);
        let over_n = d.lam_fv(n_fv, nat, with_inj);
        let over_sigma = d.lam_fv(sigma_fv, fn_ty, over_n);
        d.lam_fv(f_fv, pred_ty, over_sigma)
    };
    d.declare_theorem(p.count_range_permute, ty, value)
}

// ============================================================================
// `Nat.countRange_product` — the block/Fubini factorization.
// ============================================================================

/// `fun k => f (add offset k)` — `f` shifted so its own zero sits at `offset`,
/// exactly the shape `Nat.countRange_split`'s tail is stated at.
fn shifted(d: &mut NatDev<'_>, f: ExprId, offset: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let ok = d.add(offset, k);
    let body = d.apply(f, &[ok]);
    d.lam_fv(k_fv, nat, body)
}

/// `hf : ∀ k, Lt k n → Eq Bool (f k) false ⊢ Eq Nat (countRange f n) zero`.
///
/// A short arrow-motive induction, the same shape
/// [`declare_count_range_congr_lt`] uses. Kept private: the only caller is
/// [`declare_count_range_product`]'s `R j = false` branch, where the whole
/// block contributes nothing.
fn count_range_zero_of_false_below(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    f: ExprId,
    n: ExprId,
    hf: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let motive = |d: &mut NatDev<'_>, x: ExprId| {
        let false_ = d.bool_false();
        let hyp = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let fk = d.apply(f, &[k]);
            let eq = d.bool_eq(fk, false_);
            let bound = d.lt(k, x);
            let body = d.arrow(bound, eq);
            d.pi_fv(k_fv, nat, body)
        };
        let count = count_range(d, &p, f, x);
        let zero = d.zero();
        let concl = d.eq(count, zero);
        d.arrow(hyp, concl)
    };
    let proof = d.induct(
        &motive,
        &|d| {
            let false_ = d.bool_false();
            let hyp = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let fk = d.apply(f, &[k]);
                let eq = d.bool_eq(fk, false_);
                let zero_inner = d.zero();
                let bound = d.lt(k, zero_inner);
                let body = d.arrow(bound, eq);
                d.pi_fv(k_fv, nat, body)
            };
            let zero = d.zero();
            let refl_case = d.refl(zero);
            let h_fv = d.fresh_fvar();
            d.lam_fv(h_fv, hyp, refl_case)
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let false_ = d.bool_false();
            let hyp_ty = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let fk = d.apply(f, &[k]);
                let eq = d.bool_eq(fk, false_);
                let bound = d.lt(k, sj);
                let body = d.arrow(bound, eq);
                d.pi_fv(k_fv, nat, body)
            };
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let restricted = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let hk_fv = d.fresh_fvar();
                let hk = d.kernel().fvar(hk_fv);
                let hk_ty = d.lt(k, j);
                let lifted = lift_lt(d, &p, k, j, hk);
                let applied = d.apply(h, &[k, lifted]);
                let with_hk = d.lam_fv(hk_fv, hk_ty, applied);
                d.lam_fv(k_fv, nat, with_hk)
            };
            let ih_result = d.apply(ih, &[restricted]);

            let prior = count_range(d, &p, f, j);
            let fj = d.apply(f, &[j]);
            let sel_fj = sel(d, fj);
            let zero = d.zero();
            let start = d.add(prior, sel_fj);
            let mid = d.add(zero, sel_fj);
            let step1 = d.congr(prior, zero, ih_result, &|d, t| d.add(t, sel_fj));

            let j_lt_sj = d.lemma(p.lt_succ_self, &[j]);
            let at_j = d.apply(h, &[j, j_lt_sj]);
            let one = d.num(1);
            let sel_zero = select_nat_false(d, fj, one, zero, at_j);
            let step2 = d.congr(sel_fj, zero, sel_zero, &|d, t| {
                let zero_inner = d.zero();
                d.add(zero_inner, t)
            });

            // `add zero zero` is defeq `zero`, so the chain may end there.
            let (_e, chained) = d.chain(start, &[(mid, step1), (zero, step2)]);
            d.lam_fv(h_fv, hyp_ty, chained)
        },
        n,
    );
    d.apply(proof, &[hf])
}

/// `∀ a b, Lt b n → Eq Bool (R a) `value` → Eq Bool (P (add (mul n a) b))
/// `rhs(b)`` — the shape of both of [`declare_count_range_product`]'s
/// per-block hypotheses, differing only in which `Bool` `R a` is pinned to and
/// what `P` is then equal to.
fn block_hypothesis(
    d: &mut NatDev<'_>,
    pred: ExprId,
    r: ExprId,
    n: ExprId,
    value: ExprId,
    rhs: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let na = d.mul(n, a);
    let idx = d.add(na, b);
    let lhs = d.apply(pred, &[idx]);
    let target = rhs(d, b);
    let concl = d.bool_eq(lhs, target);

    let ra = d.apply(r, &[a]);
    let pinned = d.bool_eq(ra, value);
    let with_pin = d.arrow(pinned, concl);
    let bound = d.lt(b, n);
    let with_bound = d.arrow(bound, with_pin);
    let over_b = d.pi_fv(b_fv, nat, with_bound);
    d.pi_fv(a_fv, nat, over_b)
}

/// `Nat.countRange_product : ∀ P R S n m,
///   (∀ a b, Lt b n → Eq Bool (R a) true  → Eq Bool (P (add (mul n a) b)) (S b)) →
///   (∀ a b, Lt b n → Eq Bool (R a) false → Eq Bool (P (add (mul n a) b)) false) →
///   Eq Nat (countRange P (mul n m)) (mul (countRange S n) (countRange R m))`
///
/// Counting over `[0, n*m)` a predicate that factors through the block
/// decomposition `y = n*a + b` with `b < n` multiplies the two factors'
/// counts. **This step needs no coprimality**, and saying so precisely is the
/// point: the TOTIENT identity it will eventually serve does need it (false at
/// 26 of 26 non-coprime pairs with `1 ≤ m,n ≤ 9`), and conflating the two is
/// what produced `301`'s false `count_range_row_major` claim.
///
/// Stated over an arbitrary `P` with two hypotheses pinning `R a` to each
/// `Bool`, rather than over a fixed conjunction: this kernel has no exposed
/// `Bool`-valued `and` (`finite_set.rs`'s `bool_select_bool` is private), and
/// a caller supplying its own combination discharges both hypotheses by
/// reduction.
///
/// `Lt 0 n` is deliberately NOT required. At `n = 0` both sides are `zero` and
/// both hypotheses are vacuous, so the statement holds — and the proof never
/// divides, so nothing needs the divisor positive.
///
/// Induction on `m`. `mul n (succ j) ≡ add (mul n j) n` definitionally
/// (`Nat.mul` recurses on its right argument), so `Nat.countRange_split` peels
/// one block of width `n` with no `Nat.sub` anywhere. The block's own count is
/// `countRange S n` or `zero` according to `ops::bool_true_or_false` on
/// `R j`, via [`declare_count_range_congr_lt`] and
/// [`count_range_zero_of_false_below`]; `Nat.left_distrib` splits the
/// right-hand side to match.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_count_range_product(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);

    let pred_fv = d.fresh_fvar();
    let pred = d.kernel().fvar(pred_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let true_ = d.bool_true();
    let false_ = d.bool_false();
    let htrue_ty = block_hypothesis(d, pred, r, n, true_, &|d, b| d.apply(s, &[b]));
    let hfalse_ty = block_hypothesis(d, pred, r, n, false_, &|d, _b| d.bool_false());
    let htrue_fv = d.fresh_fvar();
    let htrue = d.kernel().fvar(htrue_fv);
    let hfalse_fv = d.fresh_fvar();
    let hfalse = d.kernel().fvar(hfalse_fv);

    let motive = |d: &mut NatDev<'_>, x: ExprId| {
        let bound = d.mul(n, x);
        let lhs = count_range(d, &p, pred, bound);
        let cs = count_range(d, &p, s, n);
        let cr = count_range(d, &p, r, x);
        let rhs = d.mul(cs, cr);
        d.eq(lhs, rhs)
    };
    let stmt = motive(d, m);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            d.refl(zero)
        },
        &|d, j, ih| {
            let cs = count_range(d, &p, s, n);
            let cr_j = count_range(d, &p, r, j);
            let block = d.mul(n, j);
            let cp_j = count_range(d, &p, pred, block);
            let shift = shifted(d, pred, block);
            let tail = count_range(d, &p, shift, n);
            let rj = d.apply(r, &[j]);
            let sel_rj = sel(d, rj);

            // `countRange P (mul n (succ j))` is defeq `countRange P (add (mul
            // n j) n)`, which `countRange_split` peels.
            let sj = d.succ(j);
            let bound_sj = d.mul(n, sj);
            let start = count_range(d, &p, pred, bound_sj);
            let after_split = d.add(cp_j, tail);
            let split = d.lemma(p.count_range_split, &[pred, block, n]);

            let scaled = d.mul(cs, cr_j);
            let after_ih = d.add(scaled, tail);
            let step_ih = d.congr(cp_j, scaled, ih, &|d, t| d.add(t, tail));

            // Both branches prove `add scaled tail = add scaled (mul cs sel_rj)`.
            let branch_goal = {
                let prod = d.mul(cs, sel_rj);
                let rhs = d.add(scaled, prod);
                d.eq(after_ih, rhs)
            };
            let true_ty = {
                let t = d.bool_true();
                d.bool_eq(rj, t)
            };
            let false_ty = {
                let fl = d.bool_false();
                d.bool_eq(rj, fl)
            };

            let on_true = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                // The block's predicate agrees with `S` below `n`.
                let agree = {
                    let k_fv = d.fresh_fvar();
                    let k = d.kernel().fvar(k_fv);
                    let hk_fv = d.fresh_fvar();
                    let hk = d.kernel().fvar(hk_fv);
                    let hk_ty = d.lt(k, n);
                    let applied = d.apply(htrue, &[j, k, hk, h]);
                    let with_hk = d.lam_fv(hk_fv, hk_ty, applied);
                    d.lam_fv(k_fv, nat, with_hk)
                };
                let tail_eq = d.lemma(p.count_range_congr_lt, &[shift, s, n, agree]);
                let mid = d.add(scaled, cs);
                let step1 = d.congr(tail, cs, tail_eq, &|d, t| d.add(scaled, t));

                // `sel (R j) = 1`, so `mul cs (sel (R j)) = cs`.
                let one = d.num(1);
                let zero = d.zero();
                let sel_one = select_nat_true(d, rj, one, zero, h);
                let one2 = d.num(1);
                let mul_sel_one = d.congr(sel_rj, one2, sel_one, &|d, t| d.mul(cs, t));
                let mul_one = d.lemma(p.mul_one, &[cs]);
                let mul_cs_one = d.mul(cs, one2);
                let prod = d.mul(cs, sel_rj);
                let prod_eq_cs = d.trans(prod, mul_cs_one, cs, mul_sel_one, mul_one);
                let cs_eq_prod = d.symm(prod, cs, prod_eq_cs);
                let end_ = d.add(scaled, prod);
                let step2 = d.congr(cs, prod, cs_eq_prod, &|d, t| d.add(scaled, t));

                let (_e, chained) = d.chain(after_ih, &[(mid, step1), (end_, step2)]);
                d.lam_fv(h_fv, true_ty, chained)
            };

            let on_false = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let agree = {
                    let k_fv = d.fresh_fvar();
                    let k = d.kernel().fvar(k_fv);
                    let hk_fv = d.fresh_fvar();
                    let hk = d.kernel().fvar(hk_fv);
                    let hk_ty = d.lt(k, n);
                    let applied = d.apply(hfalse, &[j, k, hk, h]);
                    let with_hk = d.lam_fv(hk_fv, hk_ty, applied);
                    d.lam_fv(k_fv, nat, with_hk)
                };
                let tail_eq = count_range_zero_of_false_below(d, &p, shift, n, agree);
                let zero = d.zero();
                let mid = d.add(scaled, zero);
                let step1 = d.congr(tail, zero, tail_eq, &|d, t| d.add(scaled, t));

                // `sel (R j) = 0`, so `mul cs (sel (R j)) = 0`.
                let one = d.num(1);
                let sel_zero = select_nat_false(d, rj, one, zero, h);
                let mul_sel_zero = d.congr(sel_rj, zero, sel_zero, &|d, t| d.mul(cs, t));
                let mul_zero = d.lemma(p.mul_zero, &[cs]);
                let mul_cs_zero = d.mul(cs, zero);
                let prod = d.mul(cs, sel_rj);
                let prod_eq_zero = d.trans(prod, mul_cs_zero, zero, mul_sel_zero, mul_zero);
                let zero_eq_prod = d.symm(prod, zero, prod_eq_zero);
                let end_ = d.add(scaled, prod);
                let step2 = d.congr(zero, prod, zero_eq_prod, &|d, t| d.add(scaled, t));

                let (_e, chained) = d.chain(after_ih, &[(mid, step1), (end_, step2)]);
                d.lam_fv(h_fv, false_ty, chained)
            };

            let decided = bool_true_or_false(d, &p, rj);
            let branch = or_elim(
                d,
                &p,
                true_ty,
                false_ty,
                branch_goal,
                on_true,
                on_false,
                decided,
            );

            // `mul cs (countRange R (succ j))` is defeq `mul cs (add cr_j
            // sel_rj)`, which `left_distrib` splits into the shape reached.
            let prod = d.mul(cs, sel_rj);
            let distributed = d.add(scaled, prod);
            let combined = d.add(cr_j, sel_rj);
            let regrouped = d.mul(cs, combined);
            let distrib = d.lemma(p.left_distrib, &[cs, cr_j, sel_rj]);
            let step_last = d.symm(regrouped, distributed, distrib);

            let (_e, whole) = d.chain(
                start,
                &[
                    (after_split, split),
                    (after_ih, step_ih),
                    (distributed, branch),
                    (regrouped, step_last),
                ],
            );
            whole
        },
        m,
    );

    let ty = {
        let with_hfalse = d.arrow(hfalse_ty, stmt);
        let with_htrue = d.arrow(htrue_ty, with_hfalse);
        let over_m = d.pi_fv(m_fv, nat, with_htrue);
        let over_n = d.pi_fv(n_fv, nat, over_m);
        let over_s = d.pi_fv(s_fv, pred_ty, over_n);
        let over_r = d.pi_fv(r_fv, pred_ty, over_s);
        d.pi_fv(pred_fv, pred_ty, over_r)
    };
    let value = {
        let with_hfalse = d.lam_fv(hfalse_fv, hfalse_ty, proof);
        let with_htrue = d.lam_fv(htrue_fv, htrue_ty, with_hfalse);
        let over_m = d.lam_fv(m_fv, nat, with_htrue);
        let over_n = d.lam_fv(n_fv, nat, over_m);
        let over_s = d.lam_fv(s_fv, pred_ty, over_n);
        let over_r = d.lam_fv(r_fv, pred_ty, over_s);
        d.lam_fv(pred_fv, pred_ty, over_r)
    };
    d.declare_theorem(p.count_range_product, ty, value)
}
