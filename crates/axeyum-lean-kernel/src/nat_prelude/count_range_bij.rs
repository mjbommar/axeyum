//! `Nat.countRange_bij` — **the cross-bound counting law**: two `Bool`-valued
//! predicates counted over two DIFFERENT ranges have the same count as soon as
//! a constructive bijection is exhibited between the two selected sets.
//!
//! ## Why this file exists
//!
//! `docs/plan/status/*rat-rank-nullity*.md` and ADR-1558 measured the exact
//! gap: `Rat.rank` is a `countRange` over ROWS and `Rat.rankCols` a
//! `countRange` over COLS, and **every one of the `Nat.countRange_*` laws in
//! the tree keeps the same bound on both sides** — `countRange_permute`
//! permutes within `[0,n)`, `countRange_split` / `countRange_product` relate
//! `n+m` / `n*m` to their own parts, `countRange_le_of_le` moves the bound but
//! keeps the predicate, `countRange_le_of_subset` moves the predicate but
//! keeps the bound. Nothing related `countRange p n` to `countRange q m` for
//! independent `p, n` and `q, m`. That absence was re-confirmed by
//! `examples/shape_search --const Nat.countRange --kind theorem` before this
//! file was written.
//!
//! ## Statement
//!
//! ```text
//! Nat.countRange_bij :
//!   ∀ (p q : Nat → Bool) (σ τ : Nat → Nat) (n m : Nat),
//!     (∀ i j, Lt i n → Eq Bool (p i) true → Lt j n → Eq Bool (p j) true →
//!        Eq Nat (σ i) (σ j) → Eq Nat i j) →
//!     (∀ i, Lt i n → Eq Bool (p i) true →
//!        And (Lt (σ i) m) (Eq Bool (q (σ i)) true)) →
//!     (∀ j, Lt j m → Eq Bool (q j) true →
//!        And (Lt (τ j) n) (Eq Bool (p (τ j)) true)) →
//!     (∀ i, Lt i n → Eq Bool (p i) true → Eq Nat (τ (σ i)) i) →
//!     (∀ j, Lt j m → Eq Bool (q j) true → Eq Nat (σ (τ j)) j) →
//!     Eq Nat (countRange p n) (countRange q m)
//! ```
//!
//! The hypotheses are `countRange_permute`'s `InjectiveOn` / `MapsInto` pair
//! **relativized to the selected sets** — `Nat.injectiveOn` and
//! `Nat.mapsInto` (`finite.rs`) are self-map notions on one shared bound and
//! cannot express a map from `{i < n | p i}` into `{j < m | q j}` — plus a
//! constructive surjectivity: an explicit inverse `τ` with its own `MapsInto`
//! and the two round-trip equations. **Surjectivity is never stated as an
//! `Exists`**: an existential would have to be eliminated inside the
//! induction, and the witness it produced would carry no computational
//! relationship to the one at the next index, so the induction could not
//! carry a coherent inverse from `succ n` down to `n`.
//!
//! ## Route
//!
//! Induction on `n` with `p` and `m` held OUTSIDE the recursion and the motive
//! generalized over `q`, `σ` and `τ` (the step removes one point from `q`'s
//! selected set, so `q` moves and `p` does not — generalizing over `p` instead
//! does not close).
//!
//! - **`n = 0`** — no index is selected on the left, and `τ`'s `MapsInto` sends
//!   every selected `j < m` into `[0,0)`, which `not_lt_zero` refutes. So `q`
//!   is false on all of `[0,m)` and [`declare_count_range_eq_zero_of_all_false`]
//!   collapses the right-hand side.
//! - **`succ n`, `p n = false`** — the top index contributes nothing; the same
//!   `q, σ, τ` satisfy the hypotheses at `n` (the only real step is that
//!   `τ j = n` would force `p n = true`).
//! - **`succ n`, `p n = true`** — `j0 := σ n` is selected by `q`, and the
//!   induction hypothesis is applied to `q` with `j0` REMOVED. Removal is the
//!   `Bool`-valued analogue of `finite.rs`'s `point_override`: the same
//!   cascaded-`Nat.ble` order comparison (never `Nat.beq`), substituting
//!   `Bool.false` at the single index `j0`. `Nat.countRange_point_change` then
//!   pays for the removal in exactly one step — `countRange q' m + 1 =
//!   countRange q m` — which is why this file needs no counting apparatus of
//!   its own.
//!
//! ## What is declared
//!
//! - [`declare_count_range_eq_zero_of_all_false`] — `Nat.countRange_eq_zero_of_all_false`,
//!   the base case's collapse. A three-line induction that did not exist:
//!   `Nat.countRange_const_true` had no `false` twin, and the route through
//!   `countRange_compl` would need an `add`-cancellation the direct induction
//!   does not.
//! - [`declare_count_range_bij`] — the headline.
//!
//! No new `Definition` is introduced, so nothing here can be well-typed and
//! mean the wrong thing.

use super::NatPrelude;
use super::finite::{ex_falso, ne_of_lt, ne_symm, restrict_ble_eq_false_of_lt};
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps, bool_true_or_false};
use super::steps::absurd;
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

/// `bool_select_nat b 1 0` — the per-index contribution `countRange`
/// accumulates.
fn sel(d: &mut NatDev<'_>, b: ExprId) -> ExprId {
    let one = d.num(1);
    let zero = d.zero();
    d.bool_select_nat(b, one, zero)
}

/// `h : Lt i m ⊢ Lt i (succ m)` (local copy of `finite.rs`'s `lift_lt`).
fn lift_lt(d: &mut NatDev<'_>, p: &NatPrelude, i: ExprId, m: ExprId, h: ExprId) -> ExprId {
    let p = *p;
    let succ_i = d.succ(i);
    let sm = d.succ(m);
    let m_le_sm = d.lemma(p.le_succ, &[m]);
    d.lemma(p.le_trans, &[succ_i, m, sm, h, m_le_sm])
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

/// `h : Eq Bool a b ⊢ Eq Nat (body a) (body b)`.
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

/// `h : Eq Nat x y ⊢ Eq Bool (body x) (body y)`.
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

/// `And.intro`.
fn and_intro(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    left_ty: ExprId,
    right_ty: ExprId,
    left: ExprId,
    right: ExprId,
) -> ExprId {
    d.const_app(p.logic.and_intro, &[left_ty, right_ty, left, right])
}

/// Computational `if condition then on_true else on_false` at `Bool` — the
/// `Bool`-valued twin of `NatOps::bool_select_nat`, which this file needs
/// because the point it removes lives in a `Nat → Bool` predicate.
fn bsel(d: &mut NatDev<'_>, condition: ExprId, on_true: ExprId, on_false: ExprId) -> ExprId {
    let bool_ty = d.bool_ty();
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, bool_ty, bool_ty, BinderInfo::Default);
    let one = d.level_one();
    let bool_rec = d.prelude().logic.bool_rec;
    let rec = d.kernel().const_(bool_rec, vec![one]);
    d.apply(rec, &[motive, on_false, on_true, condition])
}

/// `heq : Eq Bool cond true ⊢ Eq Bool (bsel cond a b) a`.
fn select_bool_true(d: &mut NatDev<'_>, cond: ExprId, a: ExprId, b: ExprId, heq: ExprId) -> ExprId {
    let true_val = d.bool_true();
    let symm_hb = d.bool_symm(cond, true_val, heq);
    let motive = d.bool_eq_motive(true_val, &|d, value| {
        let s = bsel(d, value, a, b);
        d.bool_eq(s, a)
    });
    let refl_case = d.bool_refl(a);
    d.bool_transport(true_val, motive, refl_case, cond, symm_hb)
}

/// `heq : Eq Bool cond false ⊢ Eq Bool (bsel cond a b) b`.
fn select_bool_false(
    d: &mut NatDev<'_>,
    cond: ExprId,
    a: ExprId,
    b: ExprId,
    heq: ExprId,
) -> ExprId {
    let false_val = d.bool_false();
    let symm_hb = d.bool_symm(cond, false_val, heq);
    let motive = d.bool_eq_motive(false_val, &|d, value| {
        let s = bsel(d, value, a, b);
        d.bool_eq(s, b)
    });
    let refl_case = d.bool_refl(b);
    d.bool_transport(false_val, motive, refl_case, cond, symm_hb)
}

// ============================================================================
// `Nat.countRange_eq_zero_of_all_false`.
// ============================================================================

/// `∀ k, Lt k bound → Eq Bool (f k) false`.
fn all_false_below(d: &mut NatDev<'_>, f: ExprId, bound: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let false_val = d.bool_false();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let fk = d.apply(f, &[k]);
    let eq = d.bool_eq(fk, false_val);
    let hyp = d.lt(k, bound);
    let body = d.arrow(hyp, eq);
    d.pi_fv(k_fv, nat, body)
}

/// `Nat.countRange_eq_zero_of_all_false : ∀ f n,
///   (∀ k, Lt k n → Eq Bool (f k) false) → Eq Nat (countRange f n) zero`.
///
/// The `false` twin of `Nat.countRange_const_true` (`totient.rs`), which had
/// none. Induction on `n` with the hypothesis carried inside the motive; the
/// step is `countRange f (succ j) ≡ countRange f j + sel (f j)`, whose two
/// summands the induction hypothesis and the assumption drive to `zero`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
pub(super) fn declare_count_range_eq_zero_of_all_false(
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

    let motive = |d: &mut NatDev<'_>, x: ExprId| {
        let hyp = all_false_below(d, f, x);
        let lhs = count_range(d, &p, f, x);
        let zero = d.zero();
        let concl = d.eq(lhs, zero);
        d.arrow(hyp, concl)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            let hyp = all_false_below(d, f, zero);
            let refl_case = d.refl(zero);
            let h_fv = d.fresh_fvar();
            d.lam_fv(h_fv, hyp, refl_case)
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let hyp_ty = all_false_below(d, f, sj);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            // Restrict the hypothesis from `succ j` down to `j`.
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
            let fj_sel = sel(d, fj);
            let zero = d.zero();
            let false_val = d.bool_false();

            let start = d.add(prior, fj_sel);
            let j_lt_sj = d.lemma(p.lt_succ_self, &[j]);
            let at_j = d.apply(h, &[j, j_lt_sj]);
            let false_sel = sel(d, false_val);
            let mid = d.add(prior, false_sel);
            let step1 = bool_congr_nat(d, fj, false_val, at_j, &|d, x| {
                let sv = sel(d, x);
                d.add(prior, sv)
            });
            // `add prior (sel false)` is `prior` by ι/δ, so `ih_result`
            // closes the chain.
            let (_e, chained) = d.chain(start, &[(mid, step1), (zero, ih_result)]);
            d.lam_fv(h_fv, hyp_ty, chained)
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(f_fv, pred_ty, over_n)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(f_fv, pred_ty, over_n)
    };
    d.declare_theorem(p.count_range_eq_zero_of_all_false, ty, value)
}

// ============================================================================
// The single-point removal `q'` and its three defining equations.
// ============================================================================

/// `dropPoint q j0 k := if k < j0 then q k else if j0 < k then q k else false`
/// — the `Bool`-valued analogue of `finite.rs`'s `point_override`, same
/// cascaded-`Nat.ble` convention (never `Nat.beq`), substituting `Bool.false`
/// at the single index `j0`.
fn drop_body(d: &mut NatDev<'_>, q: ExprId, j0: ExprId, k: ExprId) -> ExprId {
    let qk = d.apply(q, &[k]);
    let false_val = d.bool_false();
    let succ_j0 = d.succ(j0);
    let above_cond = d.ble(succ_j0, k);
    let inner = bsel(d, above_cond, qk, false_val);
    let succ_k = d.succ(k);
    let below_cond = d.ble(succ_k, j0);
    bsel(d, below_cond, qk, inner)
}

/// `fun k => dropPoint q j0 k`.
fn drop_pred(d: &mut NatDev<'_>, q: ExprId, j0: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let body = drop_body(d, q, j0, k);
    d.lam_fv(k_fv, nat, body)
}

/// `h : Lt k j0 ⊢ Eq Bool (dropPoint q j0 k) (q k)`.
fn drop_eq_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    q: ExprId,
    j0: ExprId,
    k: ExprId,
    h: ExprId,
) -> ExprId {
    let p = *p;
    let qk = d.apply(q, &[k]);
    let false_val = d.bool_false();
    let succ_j0 = d.succ(j0);
    let above_cond = d.ble(succ_j0, k);
    let inner = bsel(d, above_cond, qk, false_val);
    let succ_k = d.succ(k);
    let below_cond = d.ble(succ_k, j0);
    let below_true = d.lemma(p.ble_eq_true_of_le, &[succ_k, j0, h]);
    select_bool_true(d, below_cond, qk, inner, below_true)
}

/// `h : Lt j0 k ⊢ Eq Bool (dropPoint q j0 k) (q k)`.
fn drop_eq_gt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    q: ExprId,
    j0: ExprId,
    k: ExprId,
    h: ExprId,
) -> ExprId {
    let p = *p;
    let qk = d.apply(q, &[k]);
    let false_val = d.bool_false();
    let succ_j0 = d.succ(j0);
    let above_cond = d.ble(succ_j0, k);
    let inner = bsel(d, above_cond, qk, false_val);
    let succ_k = d.succ(k);
    let below_cond = d.ble(succ_k, j0);

    let le_k_succ_k = d.lemma(p.le_succ, &[k]);
    let lt_j0_succ_k = d.lemma(p.le_trans, &[succ_j0, k, succ_k, h, le_k_succ_k]);
    let below_false = restrict_ble_eq_false_of_lt(d, &p, succ_k, j0, lt_j0_succ_k);
    let step1 = select_bool_false(d, below_cond, qk, inner, below_false);

    let above_true = d.lemma(p.ble_eq_true_of_le, &[succ_j0, k, h]);
    let step2 = select_bool_true(d, above_cond, qk, false_val, above_true);

    let start = drop_body(d, q, j0, k);
    d.bool_trans(start, inner, qk, step1, step2)
}

/// `Eq Bool (dropPoint q j0 j0) false` — the removed point.
fn drop_eq_at(d: &mut NatDev<'_>, p: &NatPrelude, q: ExprId, j0: ExprId) -> ExprId {
    let p = *p;
    let qj0 = d.apply(q, &[j0]);
    let false_val = d.bool_false();
    let succ_j0 = d.succ(j0);
    let cond = d.ble(succ_j0, j0);
    let inner = bsel(d, cond, qj0, false_val);

    let lt_j0_succ_j0 = d.lemma(p.lt_succ_self, &[j0]);
    let cond_false = restrict_ble_eq_false_of_lt(d, &p, succ_j0, j0, lt_j0_succ_j0);
    let step1 = select_bool_false(d, cond, qj0, inner, cond_false);
    let step2 = select_bool_false(d, cond, qj0, false_val, cond_false);

    let start = drop_body(d, q, j0, j0);
    d.bool_trans(start, inner, false_val, step1, step2)
}

/// `Or (Lt k j0) (Or (Lt j0 k) (Eq Nat j0 k))`, from `lt_or_ge` composed with
/// `lt_or_eq_of_le` — this prelude has no packaged three-way trichotomy.
fn trichotomy_goal(d: &mut NatDev<'_>, p: &NatPrelude, j0: ExprId, k: ExprId) -> (ExprId, ExprId) {
    let p = *p;
    let lt_k = d.lt(k, j0);
    let lt_j0 = d.lt(j0, k);
    let eq_j0k = d.eq(j0, k);
    let right_ty = d.const_app(p.logic.or, &[lt_j0, eq_j0k]);
    let whole = d.const_app(p.logic.or, &[lt_k, right_ty]);
    (whole, right_ty)
}

/// Case-split `k` against `j0` into the three branches, each producing `goal`.
#[allow(clippy::too_many_arguments)]
fn split_against(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    j0: ExprId,
    k: ExprId,
    goal: ExprId,
    on_below: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
    on_above: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
    on_equal: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let p = *p;
    let lt_k = d.lt(k, j0);
    let lt_j0 = d.lt(j0, k);
    let eq_j0k = d.eq(j0, k);
    let (_whole, right_ty) = trichotomy_goal(d, &p, j0, k);

    // `lt_or_ge k j0 : Or (Lt k j0) (Le j0 k)`.
    let outer = d.lemma(p.lt_or_ge, &[k, j0]);
    let le_j0_k = d.le(j0, k);

    let below_case = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = on_below(d, h);
        d.lam_fv(h_fv, lt_k, body)
    };
    let ge_case = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let disj = d.lemma(p.lt_or_eq_of_le, &[j0, k, h]);
        let above_case = {
            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let body = on_above(d, g);
            d.lam_fv(g_fv, lt_j0, body)
        };
        let equal_case = {
            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let body = on_equal(d, g);
            d.lam_fv(g_fv, eq_j0k, body)
        };
        let inner = or_elim(d, &p, lt_j0, eq_j0k, goal, above_case, equal_case, disj);
        d.lam_fv(h_fv, le_j0_k, inner)
    };
    let _ = right_ty;
    or_elim(d, &p, lt_k, le_j0_k, goal, below_case, ge_case, outer)
}

/// `hne : Not (Eq Nat k j0) ⊢ Eq Bool (dropPoint q j0 k) (q k)`.
fn drop_eq_of_ne(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    q: ExprId,
    j0: ExprId,
    k: ExprId,
    hne: ExprId,
) -> ExprId {
    let p = *p;
    let start = drop_body(d, q, j0, k);
    let qk = d.apply(q, &[k]);
    let goal = d.bool_eq(start, qk);
    split_against(
        d,
        &p,
        j0,
        k,
        goal,
        &|d, h| drop_eq_lt(d, &p, q, j0, k, h),
        &|d, h| drop_eq_gt(d, &p, q, j0, k, h),
        &|d, h| {
            // `h : Eq Nat j0 k` contradicts `hne : Not (Eq Nat k j0)`.
            let flipped = d.symm(j0, k, h);
            let false_pf = d.apply(hne, &[flipped]);
            let start = drop_body(d, q, j0, k);
            let qk = d.apply(q, &[k]);
            let target = d.bool_eq(start, qk);
            absurd(d, target, false_pf)
        },
    )
}

/// `hk : Eq Bool (dropPoint q j0 k) true ⊢
///   And (Eq Bool (q k) true) (Not (Eq Nat k j0))` — reading the removal
/// backwards, which is what the induction hypothesis's `MapsInto` and
/// round-trip hypotheses both need.
fn drop_true_imp(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    q: ExprId,
    j0: ExprId,
    k: ExprId,
    hk: ExprId,
) -> ExprId {
    let p = *p;
    let true_val = d.bool_true();
    let qk = d.apply(q, &[k]);
    let left_ty = d.bool_eq(qk, true_val);
    let eq_k_j0 = d.eq(k, j0);
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let right_ty = d.arrow(eq_k_j0, false_ty);
    let goal = d.const_app(p.logic.and, &[left_ty, right_ty]);

    split_against(
        d,
        &p,
        j0,
        k,
        goal,
        &|d, h| {
            let eqd = drop_eq_lt(d, &p, q, j0, k, h);
            let start = drop_body(d, q, j0, k);
            let qk = d.apply(q, &[k]);
            let true_val = d.bool_true();
            let rev = d.bool_symm(start, qk, eqd);
            let q_true = d.bool_trans(qk, start, true_val, rev, hk);
            let hne = ne_of_lt(d, &p, k, j0, h);
            let left_ty = d.bool_eq(qk, true_val);
            let eq_k_j0 = d.eq(k, j0);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            let right_ty = d.arrow(eq_k_j0, false_ty);
            and_intro(d, &p, left_ty, right_ty, q_true, hne)
        },
        &|d, h| {
            let eqd = drop_eq_gt(d, &p, q, j0, k, h);
            let start = drop_body(d, q, j0, k);
            let qk = d.apply(q, &[k]);
            let true_val = d.bool_true();
            let rev = d.bool_symm(start, qk, eqd);
            let q_true = d.bool_trans(qk, start, true_val, rev, hk);
            let hne0 = ne_of_lt(d, &p, j0, k, h);
            let hne = ne_symm(d, j0, k, hne0);
            let left_ty = d.bool_eq(qk, true_val);
            let eq_k_j0 = d.eq(k, j0);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            let right_ty = d.arrow(eq_k_j0, false_ty);
            and_intro(d, &p, left_ty, right_ty, q_true, hne)
        },
        &|d, h| {
            // `h : Eq Nat j0 k` — at the removed point `q'` is `false`.
            let at_j0 = drop_eq_at(d, &p, q, j0);
            let drop_j0 = drop_body(d, q, j0, j0);
            let drop_k = drop_body(d, q, j0, k);
            let moved = nat_congr_bool(d, j0, k, h, &|d, x| drop_body(d, q, j0, x));
            let rev = d.bool_symm(drop_j0, drop_k, moved);
            let false_val = d.bool_false();
            let k_false = d.bool_trans(drop_k, drop_j0, false_val, rev, at_j0);
            let true_val = d.bool_true();
            let hk_rev = d.bool_symm(drop_k, true_val, hk);
            let true_eq_false = d.bool_trans(true_val, drop_k, false_val, hk_rev, k_false);
            let contra = d.const_app(p.logic.bool_true_ne_false, &[true_eq_false]);
            let qk = d.apply(q, &[k]);
            let left_ty = d.bool_eq(qk, true_val);
            let eq_k_j0 = d.eq(k, j0);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            let right_ty = d.arrow(eq_k_j0, false_ty);
            let target = d.const_app(p.logic.and, &[left_ty, right_ty]);
            ex_falso(d, &p, target, contra)
        },
    )
}

// ============================================================================
// `Nat.countRange_bij` — the hypothesis shapes.
// ============================================================================

/// `∀ i j, Lt i x → Eq Bool (pred i) true → Lt j x → Eq Bool (pred j) true →
///   Eq Nat (f i) (f j) → Eq Nat i j` — injectivity on the SELECTED set.
fn inj_sel_ty(d: &mut NatDev<'_>, pred: ExprId, f: ExprId, x: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let true_val = d.bool_true();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let fi = d.apply(f, &[i]);
    let fj = d.apply(f, &[j]);
    let concl = d.eq(i, j);
    let hyp_eq = d.eq(fi, fj);
    let step_eq = d.arrow(hyp_eq, concl);
    let pj = d.apply(pred, &[j]);
    let sel_j = d.bool_eq(pj, true_val);
    let step_selj = d.arrow(sel_j, step_eq);
    let hyp_j = d.lt(j, x);
    let step_j = d.arrow(hyp_j, step_selj);
    let pi = d.apply(pred, &[i]);
    let sel_i = d.bool_eq(pi, true_val);
    let step_seli = d.arrow(sel_i, step_j);
    let hyp_i = d.lt(i, x);
    let inner = d.arrow(hyp_i, step_seli);
    let with_j = d.pi_fv(j_fv, nat, inner);
    d.pi_fv(i_fv, nat, with_j)
}

/// `∀ i, Lt i src → Eq Bool (from i) true →
///   And (Lt (f i) dst) (Eq Bool (to (f i)) true)` — `f` maps the selected set
/// of `from` below `src` into the selected set of `to` below `dst`.
#[allow(clippy::too_many_arguments)]
fn maps_sel_ty(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    from: ExprId,
    to: ExprId,
    f: ExprId,
    src: ExprId,
    dst: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let true_val = d.bool_true();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);

    let fi = d.apply(f, &[i]);
    let bound = d.lt(fi, dst);
    let to_fi = d.apply(to, &[fi]);
    let selected = d.bool_eq(to_fi, true_val);
    let concl = d.const_app(p.logic.and, &[bound, selected]);
    let from_i = d.apply(from, &[i]);
    let sel_i = d.bool_eq(from_i, true_val);
    let step_sel = d.arrow(sel_i, concl);
    let hyp_i = d.lt(i, src);
    let inner = d.arrow(hyp_i, step_sel);
    d.pi_fv(i_fv, nat, inner)
}

/// `∀ i, Lt i src → Eq Bool (pred i) true → Eq Nat (g (f i)) i` — one
/// round-trip equation, stated only on the selected set.
fn roundtrip_ty(d: &mut NatDev<'_>, pred: ExprId, f: ExprId, g: ExprId, src: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let true_val = d.bool_true();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);

    let fi = d.apply(f, &[i]);
    let gfi = d.apply(g, &[fi]);
    let concl = d.eq(gfi, i);
    let pred_i = d.apply(pred, &[i]);
    let sel_i = d.bool_eq(pred_i, true_val);
    let step_sel = d.arrow(sel_i, concl);
    let hyp_i = d.lt(i, src);
    let inner = d.arrow(hyp_i, step_sel);
    d.pi_fv(i_fv, nat, inner)
}

/// The five hypothesis types at bound `x`, in declaration order.
#[allow(clippy::too_many_arguments)]
fn hyp_types(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pp: ExprId,
    q: ExprId,
    sigma: ExprId,
    tau: ExprId,
    x: ExprId,
    m: ExprId,
) -> [ExprId; 5] {
    let h1 = inj_sel_ty(d, pp, sigma, x);
    let h2 = maps_sel_ty(d, p, pp, q, sigma, x, m);
    let h3 = maps_sel_ty(d, p, q, pp, tau, m, x);
    let h4 = roundtrip_ty(d, pp, sigma, tau, x);
    let h5 = roundtrip_ty(d, q, tau, sigma, m);
    [h1, h2, h3, h4, h5]
}

/// The induction motive: `∀ q σ τ, H1 → H2 → H3 → H4 → H5 →
/// Eq Nat (countRange p x) (countRange q m)`, generalized over `q`, `σ` and
/// `τ` but NOT over `p` or `m`.
fn bij_motive(d: &mut NatDev<'_>, p: &NatPrelude, pp: ExprId, m: ExprId, x: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);
    let fn_ty = d.arrow(nat, nat);

    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let sigma_fv = d.fresh_fvar();
    let sigma = d.kernel().fvar(sigma_fv);
    let tau_fv = d.fresh_fvar();
    let tau = d.kernel().fvar(tau_fv);

    let hs = hyp_types(d, &p, pp, q, sigma, tau, x, m);
    let lhs = count_range(d, &p, pp, x);
    let rhs = count_range(d, &p, q, m);
    let mut body = d.eq(lhs, rhs);
    for h in hs.iter().rev() {
        body = d.arrow(*h, body);
    }
    let over_tau = d.pi_fv(tau_fv, fn_ty, body);
    let over_sigma = d.pi_fv(sigma_fv, fn_ty, over_tau);
    d.pi_fv(q_fv, pred_ty, over_sigma)
}

/// Bind `q, σ, τ` and the five hypotheses, then run `body` on them.
#[allow(clippy::too_many_lines)]
fn with_bij_context(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pp: ExprId,
    m: ExprId,
    x: ExprId,
    body: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId, ExprId, &[ExprId; 5]) -> ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);
    let fn_ty = d.arrow(nat, nat);

    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let sigma_fv = d.fresh_fvar();
    let sigma = d.kernel().fvar(sigma_fv);
    let tau_fv = d.fresh_fvar();
    let tau = d.kernel().fvar(tau_fv);

    let hs = hyp_types(d, &p, pp, q, sigma, tau, x, m);
    let mut h_fvs = [0u64; 5];
    let mut h_vars = [hs[0]; 5];
    for idx in 0..5 {
        let fv = d.fresh_fvar();
        h_fvs[idx] = fv;
        h_vars[idx] = d.kernel().fvar(fv);
    }

    let mut term = body(d, q, sigma, tau, &h_vars);
    for idx in (0..5).rev() {
        term = d.lam_fv(h_fvs[idx], hs[idx], term);
    }
    let over_tau = d.lam_fv(tau_fv, fn_ty, term);
    let over_sigma = d.lam_fv(sigma_fv, fn_ty, over_tau);
    d.lam_fv(q_fv, pred_ty, over_sigma)
}

/// The base case `n = 0`: nothing is selected on the left, and `τ`'s
/// `MapsInto` refutes every selected `j < m` (`not_lt_zero`), so `q` is false
/// on all of `[0,m)`.
fn bij_base(d: &mut NatDev<'_>, p: &NatPrelude, pp: ExprId, m: ExprId) -> ExprId {
    let p = *p;
    let zero = d.zero();
    with_bij_context(d, &p, pp, m, zero, &|d, q, _sigma, tau, hs| {
        let nat = d.nat_ty();
        let zero = d.zero();
        let true_val = d.bool_true();
        let false_val = d.bool_false();
        let h3 = hs[2];

        let all_false = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let hk_fv = d.fresh_fvar();
            let hk = d.kernel().fvar(hk_fv);
            let hk_ty = d.lt(k, m);
            let qk = d.apply(q, &[k]);
            let goal = d.bool_eq(qk, false_val);

            let is_true = d.bool_eq(qk, true_val);
            let is_false = d.bool_eq(qk, false_val);
            let disj = bool_true_or_false(d, &p, qk);
            let on_true = {
                let ht_fv = d.fresh_fvar();
                let ht = d.kernel().fvar(ht_fv);
                let applied = d.apply(h3, &[k, hk, ht]);
                let tk = d.apply(tau, &[k]);
                let bound = d.lt(tk, zero);
                let pp_tk = d.apply(pp, &[tk]);
                let selected = d.bool_eq(pp_tk, true_val);
                let lt_pf = and_left(d, bound, selected, applied);
                let false_pf = d.lemma(p.not_lt_zero, &[tk, lt_pf]);
                let body = absurd(d, goal, false_pf);
                d.lam_fv(ht_fv, is_true, body)
            };
            let on_false = {
                let hf_fv = d.fresh_fvar();
                let hf = d.kernel().fvar(hf_fv);
                d.lam_fv(hf_fv, is_false, hf)
            };
            let chosen = or_elim(d, &p, is_true, is_false, goal, on_true, on_false, disj);
            let with_hk = d.lam_fv(hk_fv, hk_ty, chosen);
            d.lam_fv(k_fv, nat, with_hk)
        };

        let czero = d.const_app(p.count_range_eq_zero_of_all_false, &[q, m, all_false]);
        let lhs = count_range(d, &p, pp, zero);
        let cq = count_range(d, &p, q, m);
        let lhs_zero = d.lemma(p.count_range_zero, &[pp]);
        let zero_eq_cq = d.symm(cq, zero, czero);
        d.trans(lhs, zero, cq, lhs_zero, zero_eq_cq)
    })
}

/// Weaken the selected-set injectivity hypothesis from `succ j` down to `j`.
fn weaken_inj(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pp: ExprId,
    sigma: ExprId,
    j: ExprId,
    h1: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let true_val = d.bool_true();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let ha_fv = d.fresh_fvar();
    let ha = d.kernel().fvar(ha_fv);
    let hpa_fv = d.fresh_fvar();
    let hpa = d.kernel().fvar(hpa_fv);
    let hb_fv = d.fresh_fvar();
    let hb = d.kernel().fvar(hb_fv);
    let hpb_fv = d.fresh_fvar();
    let hpb = d.kernel().fvar(hpb_fv);
    let he_fv = d.fresh_fvar();
    let he = d.kernel().fvar(he_fv);

    let a_lifted = lift_lt(d, &p, a, j, ha);
    let b_lifted = lift_lt(d, &p, b, j, hb);
    let result = d.apply(h1, &[a, b, a_lifted, hpa, b_lifted, hpb, he]);

    let sa = d.apply(sigma, &[a]);
    let sb = d.apply(sigma, &[b]);
    let he_ty = d.eq(sa, sb);
    let with_he = d.lam_fv(he_fv, he_ty, result);
    let pb = d.apply(pp, &[b]);
    let hpb_ty = d.bool_eq(pb, true_val);
    let with_hpb = d.lam_fv(hpb_fv, hpb_ty, with_he);
    let hb_ty = d.lt(b, j);
    let with_hb = d.lam_fv(hb_fv, hb_ty, with_hpb);
    let pa = d.apply(pp, &[a]);
    let hpa_ty = d.bool_eq(pa, true_val);
    let with_hpa = d.lam_fv(hpa_fv, hpa_ty, with_hb);
    let ha_ty = d.lt(a, j);
    let with_ha = d.lam_fv(ha_fv, ha_ty, with_hpa);
    let with_b = d.lam_fv(b_fv, nat, with_ha);
    d.lam_fv(a_fv, nat, with_b)
}

/// Weaken a round-trip hypothesis from `succ j` down to `j`.
fn weaken_roundtrip(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pp: ExprId,
    j: ExprId,
    h4: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let true_val = d.bool_true();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);
    let hp_fv = d.fresh_fvar();
    let hp = d.kernel().fvar(hp_fv);

    let lifted = lift_lt(d, &p, i, j, hi);
    let result = d.apply(h4, &[i, lifted, hp]);
    let pi = d.apply(pp, &[i]);
    let hp_ty = d.bool_eq(pi, true_val);
    let with_hp = d.lam_fv(hp_fv, hp_ty, result);
    let hi_ty = d.lt(i, j);
    let with_hi = d.lam_fv(hi_fv, hi_ty, with_hp);
    d.lam_fv(i_fv, nat, with_hi)
}

/// Weaken the forward `MapsInto` hypothesis from `succ j` down to `j` — the
/// destination side is untouched, so this is pure bound-lifting on the source.
fn weaken_maps(d: &mut NatDev<'_>, p: &NatPrelude, pp: ExprId, j: ExprId, h2: ExprId) -> ExprId {
    weaken_roundtrip(d, p, pp, j, h2)
}

/// `h_lt_succ : Lt fk (succ j)` plus a refutation of `Eq Nat fk j` gives
/// `Lt fk j`.
fn strict_of_le_and_ne(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    fk: ExprId,
    j: ExprId,
    h_lt_succ: ExprId,
    on_equal: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let p = *p;
    let le_pf = d.lemma(p.le_of_lt_succ, &[fk, j, h_lt_succ]);
    let disj = d.lemma(p.lt_or_eq_of_le, &[fk, j, le_pf]);
    let lt_ty = d.lt(fk, j);
    let eq_ty = d.eq(fk, j);
    let goal = d.lt(fk, j);
    let on_lt = {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        d.lam_fv(g_fv, lt_ty, g)
    };
    let on_eq = {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let contra = on_equal(d, g);
        let body = absurd(d, goal, contra);
        d.lam_fv(g_fv, eq_ty, body)
    };
    or_elim(d, &p, lt_ty, eq_ty, goal, on_lt, on_eq, disj)
}

/// The `p j = false` branch of the successor step: the top index contributes
/// nothing, and the SAME `q, σ, τ` satisfy the hypotheses at `j`.
#[allow(clippy::too_many_arguments)]
fn bij_branch_unselected(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pp: ExprId,
    m: ExprId,
    j: ExprId,
    ih: ExprId,
    q: ExprId,
    sigma: ExprId,
    tau: ExprId,
    hs: &[ExprId; 5],
    hpf: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let true_val = d.bool_true();
    let false_val = d.bool_false();

    let h1p = weaken_inj(d, &p, pp, sigma, j, hs[0]);
    let h2p = weaken_maps(d, &p, pp, j, hs[1]);
    let h4p = weaken_roundtrip(d, &p, pp, j, hs[3]);
    let h5p = hs[4];

    let h3p = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let hq_fv = d.fresh_fvar();
        let hq = d.kernel().fvar(hq_fv);

        let applied = d.apply(hs[2], &[k, hk, hq]);
        let tk = d.apply(tau, &[k]);
        let sj = d.succ(j);
        let bound = d.lt(tk, sj);
        let pp_tk = d.apply(pp, &[tk]);
        let selected = d.bool_eq(pp_tk, true_val);
        let lt_succ = and_left(d, bound, selected, applied);
        let pp_true = and_right(d, bound, selected, applied);

        let strict = strict_of_le_and_ne(d, &p, tk, j, lt_succ, &|d, he| {
            // `τ k = j` with `p (τ k) = true` contradicts `p j = false`.
            let moved = nat_congr_bool(d, tk, j, he, &|d, x| d.apply(pp, &[x]));
            let pp_tk = d.apply(pp, &[tk]);
            let pp_j = d.apply(pp, &[j]);
            let true_val = d.bool_true();
            let false_val = d.bool_false();
            let rev = d.bool_symm(pp_tk, pp_j, moved);
            let pp_j_true = d.bool_trans(pp_j, pp_tk, true_val, rev, pp_true);
            let false_eq_pp_j = d.bool_symm(pp_j, false_val, hpf);
            let false_eq_true = d.bool_trans(false_val, pp_j, true_val, false_eq_pp_j, pp_j_true);
            d.const_app(p.logic.bool_false_ne_true, &[false_eq_true])
        });

        let new_bound = d.lt(tk, j);
        let pair = and_intro(d, &p, new_bound, selected, strict, pp_true);
        let qk = d.apply(q, &[k]);
        let hq_ty = d.bool_eq(qk, true_val);
        let with_hq = d.lam_fv(hq_fv, hq_ty, pair);
        let hk_ty = d.lt(k, m);
        let with_hk = d.lam_fv(hk_fv, hk_ty, with_hq);
        d.lam_fv(k_fv, nat, with_hk)
    };

    let ih_result = d.apply(ih, &[q, sigma, tau, h1p, h2p, h3p, h4p, h5p]);

    let sj = d.succ(j);
    let start = count_range(d, &p, pp, sj);
    let cs = d.lemma(p.count_range_succ, &[pp, j]);
    let prior = count_range(d, &p, pp, j);
    let pp_j = d.apply(pp, &[j]);
    let sel_pj = sel(d, pp_j);
    let after_succ = d.add(prior, sel_pj);
    let sel_false = sel(d, false_val);
    let after_false = d.add(prior, sel_false);
    let step2 = bool_congr_nat(d, pp_j, false_val, hpf, &|d, x| {
        let sv = sel(d, x);
        d.add(prior, sv)
    });
    let cq = count_range(d, &p, q, m);
    let (_e, proof) = d.chain(
        start,
        &[(after_succ, cs), (after_false, step2), (cq, ih_result)],
    );
    let _ = nat;
    proof
}

/// The `p j = true` branch of the successor step: `j0 := σ j` is removed from
/// `q`'s selected set, the induction hypothesis runs at the smaller predicate,
/// and `Nat.countRange_point_change` pays for the removal in one step.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn bij_branch_selected(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pp: ExprId,
    m: ExprId,
    j: ExprId,
    ih: ExprId,
    q: ExprId,
    sigma: ExprId,
    tau: ExprId,
    hs: &[ExprId; 5],
    hpt: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let true_val = d.bool_true();
    let false_val = d.bool_false();

    let j_lt_sj = d.lemma(p.lt_succ_self, &[j]);
    let h2_at_j = d.apply(hs[1], &[j, j_lt_sj, hpt]);
    let j0 = d.apply(sigma, &[j]);
    let bound_ty = d.lt(j0, m);
    let q_j0 = d.apply(q, &[j0]);
    let sel_ty = d.bool_eq(q_j0, true_val);
    let hj0m = and_left(d, bound_ty, sel_ty, h2_at_j);
    let hqj0 = and_right(d, bound_ty, sel_ty, h2_at_j);

    let qd = drop_pred(d, q, j0);

    // --- the five hypotheses at `(qd, σ, τ, j)` -----------------------------
    let h1p = weaken_inj(d, &p, pp, sigma, j, hs[0]);
    let h4p = weaken_roundtrip(d, &p, pp, j, hs[3]);

    let h2p = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);

        let lifted = lift_lt(d, &p, i, j, hi);
        let applied = d.apply(hs[1], &[i, lifted, hp]);
        let si = d.apply(sigma, &[i]);
        let bound = d.lt(si, m);
        let q_si = d.apply(q, &[si]);
        let selected = d.bool_eq(q_si, true_val);
        let ltm = and_left(d, bound, selected, applied);
        let q_true = and_right(d, bound, selected, applied);

        // `σ i ≠ σ j`, because `i < j` and `σ` is injective on the selected set.
        let hne_ij = ne_of_lt(d, &p, i, j, hi);
        let hne_sig = {
            let e_fv = d.fresh_fvar();
            let e = d.kernel().fvar(e_fv);
            let e_ty = d.eq(si, j0);
            let i_eq_j = d.apply(hs[0], &[i, j, lifted, hp, j_lt_sj, hpt, e]);
            let contra = d.apply(hne_ij, &[i_eq_j]);
            d.lam_fv(e_fv, e_ty, contra)
        };
        let eqd = drop_eq_of_ne(d, &p, q, j0, si, hne_sig);
        let drop_si = drop_body(d, q, j0, si);
        let qd_true = d.bool_trans(drop_si, q_si, true_val, eqd, q_true);
        let qd_si = d.apply(qd, &[si]);
        let new_selected = d.bool_eq(qd_si, true_val);
        let pair = and_intro(d, &p, bound, new_selected, ltm, qd_true);

        let pi = d.apply(pp, &[i]);
        let hp_ty = d.bool_eq(pi, true_val);
        let with_hp = d.lam_fv(hp_fv, hp_ty, pair);
        let hi_ty = d.lt(i, j);
        let with_hi = d.lam_fv(hi_fv, hi_ty, with_hp);
        d.lam_fv(i_fv, nat, with_hi)
    };

    let h3p = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let hq_fv = d.fresh_fvar();
        let hq = d.kernel().fvar(hq_fv);

        let imp = drop_true_imp(d, &p, q, j0, k, hq);
        let qk = d.apply(q, &[k]);
        let left_ty = d.bool_eq(qk, true_val);
        let eq_k_j0 = d.eq(k, j0);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let ne_ty = d.arrow(eq_k_j0, false_ty);
        let hqk = and_left(d, left_ty, ne_ty, imp);
        let hne_k = and_right(d, left_ty, ne_ty, imp);

        let applied = d.apply(hs[2], &[k, hk, hqk]);
        let tk = d.apply(tau, &[k]);
        let sj = d.succ(j);
        let bound = d.lt(tk, sj);
        let pp_tk = d.apply(pp, &[tk]);
        let selected = d.bool_eq(pp_tk, true_val);
        let lt_succ = and_left(d, bound, selected, applied);
        let pp_true = and_right(d, bound, selected, applied);

        let h5k = d.apply(hs[4], &[k, hk, hqk]);
        let strict = strict_of_le_and_ne(d, &p, tk, j, lt_succ, &|d, he| {
            // `τ k = j` gives `k = σ (τ k) = σ j = j0`, refuted by `hne_k`.
            let moved = d.congr(tk, j, he, &|d, x| d.apply(sigma, &[x]));
            let s_tk = d.apply(sigma, &[tk]);
            let rev = d.symm(s_tk, k, h5k);
            let k_eq_j0 = d.trans(k, s_tk, j0, rev, moved);
            d.apply(hne_k, &[k_eq_j0])
        });

        let new_bound = d.lt(tk, j);
        let pair = and_intro(d, &p, new_bound, selected, strict, pp_true);
        let qd_k = d.apply(qd, &[k]);
        let hq_ty = d.bool_eq(qd_k, true_val);
        let with_hq = d.lam_fv(hq_fv, hq_ty, pair);
        let hk_ty = d.lt(k, m);
        let with_hk = d.lam_fv(hk_fv, hk_ty, with_hq);
        d.lam_fv(k_fv, nat, with_hk)
    };

    let h5p = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let hq_fv = d.fresh_fvar();
        let hq = d.kernel().fvar(hq_fv);

        let imp = drop_true_imp(d, &p, q, j0, k, hq);
        let qk = d.apply(q, &[k]);
        let left_ty = d.bool_eq(qk, true_val);
        let eq_k_j0 = d.eq(k, j0);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let ne_ty = d.arrow(eq_k_j0, false_ty);
        let hqk = and_left(d, left_ty, ne_ty, imp);
        let result = d.apply(hs[4], &[k, hk, hqk]);

        let qd_k = d.apply(qd, &[k]);
        let hq_ty = d.bool_eq(qd_k, true_val);
        let with_hq = d.lam_fv(hq_fv, hq_ty, result);
        let hk_ty = d.lt(k, m);
        let with_hk = d.lam_fv(hk_fv, hk_ty, with_hq);
        d.lam_fv(k_fv, nat, with_hk)
    };

    let ih_result = d.apply(ih, &[qd, sigma, tau, h1p, h2p, h3p, h4p, h5p]);

    // --- pay for the removal with `countRange_point_change` ------------------
    let below = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let hk_ty = d.lt(k, j0);
        let body = drop_eq_lt(d, &p, q, j0, k, hk);
        let with_hk = d.lam_fv(hk_fv, hk_ty, body);
        d.lam_fv(k_fv, nat, with_hk)
    };
    let above = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hlo_fv = d.fresh_fvar();
        let hlo = d.kernel().fvar(hlo_fv);
        let hhi_fv = d.fresh_fvar();
        let hhi_ty = d.lt(k, m);
        let body = drop_eq_gt(d, &p, q, j0, k, hlo);
        let with_hi = d.lam_fv(hhi_fv, hhi_ty, body);
        let hlo_ty = d.lt(j0, k);
        let with_lo = d.lam_fv(hlo_fv, hlo_ty, with_hi);
        d.lam_fv(k_fv, nat, with_lo)
    };
    let change = d.const_app(
        p.count_range_point_change,
        &[qd, q, j0, m, hj0m, below, above],
    );

    let c_qd = count_range(d, &p, qd, m);
    let c_q = count_range(d, &p, q, m);
    let qd_j0 = d.apply(qd, &[j0]);
    let sel_q_j0 = sel(d, q_j0);
    let sel_qd_j0 = sel(d, qd_j0);
    let change_lhs = d.add(c_qd, sel_q_j0);
    let change_rhs = d.add(c_q, sel_qd_j0);

    let sel_true = sel(d, true_val);
    let sel_false = sel(d, false_val);
    let reduced_lhs = d.add(c_qd, sel_true);
    let reduced_rhs = d.add(c_q, sel_false);

    let rewrite_lhs = bool_congr_nat(d, q_j0, true_val, hqj0, &|d, x| {
        let sv = sel(d, x);
        d.add(c_qd, sv)
    });
    let hqdj0 = drop_eq_at(d, &p, q, j0);
    let rewrite_rhs = bool_congr_nat(d, qd_j0, false_val, hqdj0, &|d, x| {
        let sv = sel(d, x);
        d.add(c_q, sv)
    });

    let lhs_rev = d.symm(change_lhs, reduced_lhs, rewrite_lhs);
    let via = d.trans(reduced_lhs, change_lhs, change_rhs, lhs_rev, change);
    let paid = d.trans(reduced_lhs, change_rhs, reduced_rhs, via, rewrite_rhs);

    // --- assemble ------------------------------------------------------------
    let sj = d.succ(j);
    let start = count_range(d, &p, pp, sj);
    let cs = d.lemma(p.count_range_succ, &[pp, j]);
    let prior = count_range(d, &p, pp, j);
    let pp_j = d.apply(pp, &[j]);
    let sel_pj = sel(d, pp_j);
    let after_succ = d.add(prior, sel_pj);
    let after_true = d.add(prior, sel_true);
    let step2 = bool_congr_nat(d, pp_j, true_val, hpt, &|d, x| {
        let sv = sel(d, x);
        d.add(prior, sv)
    });
    let step3 = d.congr(prior, c_qd, ih_result, &|d, t| d.add(t, sel_true));
    let (_e, proof) = d.chain(
        start,
        &[
            (after_succ, cs),
            (after_true, step2),
            (reduced_lhs, step3),
            (reduced_rhs, paid),
        ],
    );
    let _ = nat;
    proof
}

/// The successor step: `bool_true_or_false (p j)` splits into
/// [`bij_branch_unselected`] and [`bij_branch_selected`].
fn bij_step(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pp: ExprId,
    m: ExprId,
    j: ExprId,
    ih: ExprId,
) -> ExprId {
    let p = *p;
    let sj = d.succ(j);
    with_bij_context(d, &p, pp, m, sj, &|d, q, sigma, tau, hs| {
        let true_val = d.bool_true();
        let false_val = d.bool_false();
        let pp_j = d.apply(pp, &[j]);
        let is_true = d.bool_eq(pp_j, true_val);
        let is_false = d.bool_eq(pp_j, false_val);
        let disj = bool_true_or_false(d, &p, pp_j);

        let sj = d.succ(j);
        let lhs = count_range(d, &p, pp, sj);
        let rhs = count_range(d, &p, q, m);
        let goal = d.eq(lhs, rhs);

        let on_true = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = bij_branch_selected(d, &p, pp, m, j, ih, q, sigma, tau, hs, h);
            d.lam_fv(h_fv, is_true, body)
        };
        let on_false = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = bij_branch_unselected(d, &p, pp, m, j, ih, q, sigma, tau, hs, h);
            d.lam_fv(h_fv, is_false, body)
        };
        or_elim(d, &p, is_true, is_false, goal, on_true, on_false, disj)
    })
}

/// `Nat.countRange_bij` — the cross-bound counting law (see the module doc).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
pub(super) fn declare_count_range_bij(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);
    let fn_ty = d.arrow(nat, nat);

    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let sigma_fv = d.fresh_fvar();
    let sigma = d.kernel().fvar(sigma_fv);
    let tau_fv = d.fresh_fvar();
    let tau = d.kernel().fvar(tau_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let induction = d.induct(
        &|d, x| bij_motive(d, &p, pp, m, x),
        &|d| bij_base(d, &p, pp, m),
        &|d, j, ih| bij_step(d, &p, pp, m, j, ih),
        n,
    );

    let hs = hyp_types(d, &p, pp, q, sigma, tau, n, m);
    let mut h_fvs = [0u64; 5];
    let mut h_vars = [hs[0]; 5];
    for idx in 0..5 {
        let fv = d.fresh_fvar();
        h_fvs[idx] = fv;
        h_vars[idx] = d.kernel().fvar(fv);
    }
    let applied = {
        let mut args = vec![q, sigma, tau];
        args.extend_from_slice(&h_vars);
        d.apply(induction, &args)
    };

    let lhs = count_range(d, &p, pp, n);
    let rhs = count_range(d, &p, q, m);
    let concl = d.eq(lhs, rhs);

    let ty = {
        let mut body = concl;
        for h in hs.iter().rev() {
            body = d.arrow(*h, body);
        }
        let over_m = d.pi_fv(m_fv, nat, body);
        let over_n = d.pi_fv(n_fv, nat, over_m);
        let over_tau = d.pi_fv(tau_fv, fn_ty, over_n);
        let over_sigma = d.pi_fv(sigma_fv, fn_ty, over_tau);
        let over_q = d.pi_fv(q_fv, pred_ty, over_sigma);
        d.pi_fv(pp_fv, pred_ty, over_q)
    };
    let value = {
        let mut body = applied;
        for idx in (0..5).rev() {
            body = d.lam_fv(h_fvs[idx], hs[idx], body);
        }
        let over_m = d.lam_fv(m_fv, nat, body);
        let over_n = d.lam_fv(n_fv, nat, over_m);
        let over_tau = d.lam_fv(tau_fv, fn_ty, over_n);
        let over_sigma = d.lam_fv(sigma_fv, fn_ty, over_tau);
        let over_q = d.lam_fv(q_fv, pred_ty, over_sigma);
        d.lam_fv(pp_fv, pred_ty, over_q)
    };
    d.declare_theorem(p.count_range_bij, ty, value)
}

// ============================================================================
// `Nat.countRange_bij_of_inverse` — the common case, where `τ` is a two-sided
// inverse of `σ` on ALL of `Nat` rather than only on the selected sets.
// ============================================================================

/// `∀ i, Eq Nat (g (f i)) i` — an UNCONDITIONAL round trip, no bound and no
/// selection.
fn total_roundtrip_ty(d: &mut NatDev<'_>, f: ExprId, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let fi = d.apply(f, &[i]);
    let gfi = d.apply(g, &[fi]);
    let concl = d.eq(gfi, i);
    d.pi_fv(i_fv, nat, concl)
}

/// `Nat.countRange_bij_of_inverse : ∀ p q σ τ n m,
///   (∀ i, Eq Nat (τ (σ i)) i) → (∀ j, Eq Nat (σ (τ j)) j) →
///   (∀ i, Lt i n → p i = true → And (Lt (σ i) m) (q (σ i) = true)) →
///   (∀ j, Lt j m → q j = true → And (Lt (τ j) n) (p (τ j) = true)) →
///   Eq Nat (countRange p n) (countRange q m)`.
///
/// The shape a consumer usually has: `σ` and `τ` are mutually inverse
/// everywhere (`succ`/`pred` on a positive range, an index reflection, a
/// modular rotation), and the only genuinely per-instance obligations are the
/// two `MapsInto` facts. Injectivity is then FREE — `σ i = σ j` gives
/// `τ (σ i) = τ (σ j)`, i.e. `i = j` — so this form has four hypotheses rather
/// than five and none of them mentions injectivity.
///
/// Derived from [`declare_count_range_bij`], not re-proved.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
pub(super) fn declare_count_range_bij_of_inverse(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);
    let fn_ty = d.arrow(nat, nat);
    let true_val = d.bool_true();

    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let sigma_fv = d.fresh_fvar();
    let sigma = d.kernel().fvar(sigma_fv);
    let tau_fv = d.fresh_fvar();
    let tau = d.kernel().fvar(tau_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let hts_ty = total_roundtrip_ty(d, sigma, tau);
    let hst_ty = total_roundtrip_ty(d, tau, sigma);
    let h2_ty = maps_sel_ty(d, &p, pp, q, sigma, n, m);
    let h3_ty = maps_sel_ty(d, &p, q, pp, tau, m, n);

    let hts_fv = d.fresh_fvar();
    let hts = d.kernel().fvar(hts_fv);
    let hst_fv = d.fresh_fvar();
    let hst = d.kernel().fvar(hst_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);
    let h3_fv = d.fresh_fvar();
    let h3 = d.kernel().fvar(h3_fv);

    // Injectivity on the selected set, from the unconditional round trip.
    let h1 = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let hi_fv = d.fresh_fvar();
        let hpi_fv = d.fresh_fvar();
        let hj_fv = d.fresh_fvar();
        let hpj_fv = d.fresh_fvar();
        let he_fv = d.fresh_fvar();
        let he = d.kernel().fvar(he_fv);

        let si = d.apply(sigma, &[i]);
        let sj = d.apply(sigma, &[j]);
        let tsi = d.apply(tau, &[si]);
        let tsj = d.apply(tau, &[sj]);
        let at_i = d.apply(hts, &[i]);
        let at_j = d.apply(hts, &[j]);
        let i_eq_tsi = d.symm(tsi, i, at_i);
        let moved = d.congr(si, sj, he, &|d, x| d.apply(tau, &[x]));
        let (_e, body) = d.chain(i, &[(tsi, i_eq_tsi), (tsj, moved), (j, at_j)]);

        let he_ty = d.eq(si, sj);
        let with_he = d.lam_fv(he_fv, he_ty, body);
        let pj = d.apply(pp, &[j]);
        let hpj_ty = d.bool_eq(pj, true_val);
        let with_hpj = d.lam_fv(hpj_fv, hpj_ty, with_he);
        let hj_ty = d.lt(j, n);
        let with_hj = d.lam_fv(hj_fv, hj_ty, with_hpj);
        let pi = d.apply(pp, &[i]);
        let hpi_ty = d.bool_eq(pi, true_val);
        let with_hpi = d.lam_fv(hpi_fv, hpi_ty, with_hj);
        let hi_ty = d.lt(i, n);
        let with_hi = d.lam_fv(hi_fv, hi_ty, with_hpi);
        let with_j = d.lam_fv(j_fv, nat, with_hi);
        d.lam_fv(i_fv, nat, with_j)
    };

    // The two selected-set round trips, by forgetting the hypotheses.
    let forget = |d: &mut NatDev<'_>, pred: ExprId, bound: ExprId, total: ExprId| -> ExprId {
        let nat = d.nat_ty();
        let true_val = d.bool_true();
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_fv = d.fresh_fvar();
        let hp_fv = d.fresh_fvar();
        let body = d.apply(total, &[i]);
        let pi = d.apply(pred, &[i]);
        let hp_ty = d.bool_eq(pi, true_val);
        let with_hp = d.lam_fv(hp_fv, hp_ty, body);
        let hi_ty = d.lt(i, bound);
        let with_hi = d.lam_fv(hi_fv, hi_ty, with_hp);
        d.lam_fv(i_fv, nat, with_hi)
    };
    let h4 = forget(d, pp, n, hts);
    let h5 = forget(d, q, m, hst);

    let applied = d.const_app(
        p.count_range_bij,
        &[pp, q, sigma, tau, n, m, h1, h2, h3, h4, h5],
    );

    let lhs = count_range(d, &p, pp, n);
    let rhs = count_range(d, &p, q, m);
    let concl = d.eq(lhs, rhs);

    let ty = {
        let s4 = d.arrow(h3_ty, concl);
        let s3 = d.arrow(h2_ty, s4);
        let s2 = d.arrow(hst_ty, s3);
        let s1 = d.arrow(hts_ty, s2);
        let over_m = d.pi_fv(m_fv, nat, s1);
        let over_n = d.pi_fv(n_fv, nat, over_m);
        let over_tau = d.pi_fv(tau_fv, fn_ty, over_n);
        let over_sigma = d.pi_fv(sigma_fv, fn_ty, over_tau);
        let over_q = d.pi_fv(q_fv, pred_ty, over_sigma);
        d.pi_fv(pp_fv, pred_ty, over_q)
    };
    let value = {
        let s4 = d.lam_fv(h3_fv, h3_ty, applied);
        let s3 = d.lam_fv(h2_fv, h2_ty, s4);
        let s2 = d.lam_fv(hst_fv, hst_ty, s3);
        let s1 = d.lam_fv(hts_fv, hts_ty, s2);
        let over_m = d.lam_fv(m_fv, nat, s1);
        let over_n = d.lam_fv(n_fv, nat, over_m);
        let over_tau = d.lam_fv(tau_fv, fn_ty, over_n);
        let over_sigma = d.lam_fv(sigma_fv, fn_ty, over_tau);
        let over_q = d.lam_fv(q_fv, pred_ty, over_sigma);
        d.lam_fv(pp_fv, pred_ty, over_q)
    };
    d.declare_theorem(p.count_range_bij_of_inverse, ty, value)
}
