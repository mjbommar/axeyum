//! The first probability facts over `ℚ`: `Rat.IsDistribution`, and the two
//! properties that make it usable.
//!
//! A finite probability distribution needs no analysis — `ℚ` is enough — so
//! this is the natural next rung once [`super::sum`] gives `Rat.sumRange` and
//! its monotonicity (`sumRange_le`/`sumRange_nonneg`).
//!
//! `Rat.IsDistribution p n := (∀ k, k < n → 0 ≤ p k) ∧ sumRange p n = 1`, a
//! `Prop`-valued `Definition` over [`super::sum`]'s `bounded_nonneg` and the
//! carrier's own `Eq`, in the same style `Int.dvd` uses for its own
//! `∃`-valued `Definition` (`int_prelude/dvd.rs::declare_dvd_definition`).
//!
//! [`declare_prob_le_one`] needs "one term never exceeds the sum of a
//! nonnegative sequence" (`term_le_sum_range`, private — nothing else needs
//! it yet), proved by an ordinary bounded induction that case-splits the new
//! index against the boundary (`Nat.lt_or_eq_of_le`), exactly the shape
//! `sumRange_le` and `sumRange_nonneg` are themselves proved by, one level
//! up.
//!
//! [`declare_prob_complement`] states the complementary-mass fact over a
//! **prefix**, quantifying over the split point `m` and the tail length `j`
//! directly (`n := m + j`) rather than over `m ≤ n`, so the proof
//! (`sum_range_split`, private) never needs `Nat` subtraction — induction on
//! `j` alone, `m` and `p` held fixed, aligns with `Rat.add`'s own recursion
//! (`Nat.add m (succ j) ≡ succ (Nat.add m j)`) for free.

use super::RatPrelude;
use super::group::rsub;
use super::ops::{
    nat_eq_to_rat, radd, rat_eq_rewrite, rat_ty, rchain, rcongr, req, rle, rlt, rmul, rneg, rone,
    rrefl, rsum_range, rsymm, rtrans, rzero,
};
use super::sum::{bounded_nonneg, bounded_pointwise_le};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Delta height for `Rat.IsDistribution`: above `Rat.sumRange`
/// ([`super::sum::SUM_HEIGHT`]-equivalent, 34) and everything else this
/// prelude has declared so far.
const PROB_HEIGHT: u16 = 35;

/// Delta height for `Rat.expectation` and `Rat.uniform`: above
/// `Rat.IsDistribution` ([`PROB_HEIGHT`], 35). Neither calls the other, so
/// they share one height, both above everything else this prelude has
/// declared so far.
const EXPECTATION_HEIGHT: u16 = 36;

/// Delta height for `Rat.variance`: above `Rat.expectation`
/// ([`EXPECTATION_HEIGHT`], 36), which its own definition calls.
const VARIANCE_HEIGHT: u16 = 37;

/// Delta height for `Rat.indicator`: above `Rat.ble`
/// (`decide.rs::BLE_HEIGHT`, 33) and every other height declared in this
/// prelude so far, including [`VARIANCE_HEIGHT`] — `Rat.indicator` itself
/// only calls `Rat.ble`/`Rat.one`/`Rat.zero`, but this file's convention is a
/// single monotone sequence over the whole prelude, not just over each
/// definition's own callees.
const INDICATOR_HEIGHT: u16 = 38;

/// Delta height for `Rat.covariance`: above `Rat.indicator`
/// ([`INDICATOR_HEIGHT`], 38) and every other height declared in this prelude
/// so far — `Rat.covariance` itself only calls `Rat.expectation`/`Rat.sub`,
/// but this file's convention (see [`INDICATOR_HEIGHT`]) is a single monotone
/// sequence over the whole prelude, and `declare_covariance` runs last.
const COVARIANCE_HEIGHT: u16 = 39;

/// Delta height for `Rat.sumVars`: above `Rat.covariance`
/// ([`COVARIANCE_HEIGHT`], 39) and every other height declared in this
/// prelude so far — `Rat.sumVars` itself only calls `Rat.sumRange`, but this
/// file's convention (see [`INDICATOR_HEIGHT`]) is a single monotone
/// sequence over the whole prelude, and `declare_sum_vars` runs last.
const SUM_VARS_HEIGHT: u16 = 40;

/// Declare `Rat.IsDistribution`, `Rat.expectation`, `Rat.uniform`,
/// `Rat.variance`, Markov's and (in spirit) Chebyshev's inequalities, and
/// everything this file proves about them.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_probability(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_is_distribution(d, p)?;
    declare_prob_le_one(d, p)?;
    declare_prob_complement(d, p)?;
    declare_expectation(d, p)?;
    declare_expectation_add(d, p)?;
    declare_expectation_smul(d, p)?;
    declare_expectation_const(d, p)?;
    declare_uniform(d, p)?;
    declare_uniform_is_distribution(d, p)?;
    declare_expectation_nonneg(d, p)?;
    declare_expectation_le(d, p)?;
    declare_markov_inequality(d, p)?;
    declare_expectation_indicator_le_one(d, p)?;
    declare_variance(d, p)?;
    declare_variance_nonneg(d, p)?;
    declare_variance_eq(d, p)?;
    declare_variance_smul(d, p)?;
    declare_indicator(d, p)?;
    declare_indicator_nonneg(d, p)?;
    declare_indicator_le(d, p)?;
    declare_markov_constructed(d, p)?;
    declare_chebyshev_inequality(d, p)?;
    declare_covariance(d, p)?;
    declare_variance_add_eq(d, p)?;
    declare_variance_add_of_uncorrelated(d, p)?;
    declare_covariance_add_right(d, p)?;
    declare_sum_vars(d, p)?;
    declare_expectation_sum_vars(d, p)?;
    Ok(())
}

/// `Rat.IsDistribution p n`, i.e. `d.const_app(p.is_distribution, &[pf,
/// n])`.
fn is_distribution(d: &mut IntDev<'_>, p: RatPrelude, pf: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.is_distribution, &[pf, n])
}

/// `(∀ k, Lt k n → le zero (pf k)) ∧ sumRange pf n = one` — the body
/// [`declare_is_distribution`] admits `Rat.IsDistribution` as, rebuilt here so
/// callers that need to case on the components (`d.and_left`/`d.and_right`)
/// can reconstruct the exact left/right `Prop`s without re-declaring
/// anything.
fn is_distribution_parts(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    pf: ExprId,
    n: ExprId,
) -> (ExprId, ExprId) {
    let nonneg_part = bounded_nonneg(d, p, pf, n);
    let sum_part = {
        let sum = rsum_range(d, p, pf, n);
        let one_r = rone(d, p);
        super::ops::req(d, sum, one_r)
    };
    (nonneg_part, sum_part)
}

/// Admit `Rat.IsDistribution : (Nat → Rat) → Nat → Prop := fun p n => (∀ k,
/// Lt k n → le zero (p k)) ∧ sumRange p n = one`.
fn declare_is_distribution(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);
    let anon = d.anon_name();
    let prop = d.kernel().sort_zero();

    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let (nonneg_part, sum_part) = is_distribution_parts(d, p, pf, n);
    let body = d.and(nonneg_part, sum_part);
    let value = {
        let inner = d.lam_fv(n_fv, nat, body);
        d.lam_fv(pf_fv, fn_ty, inner)
    };
    let ty = {
        let inner = d.kernel().pi(anon, nat, prop, BinderInfo::Default);
        d.kernel().pi(anon, fn_ty, inner, BinderInfo::Default)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.is_distribution,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(PROB_HEIGHT),
    })
}

/// `∀ n, (∀ i, Lt i n → le zero (pf i)) → ∀ k, Lt k n → le (pf k) (sumRange
/// pf n)`, specialised at `n`, as a raw `(statement, proof)` pair — a single
/// term of a nonnegative finite sequence never exceeds the sum of all its
/// terms up to the bound.
///
/// Induction on `n`. The successor step case-splits the new index `k < succ
/// m` into `k < m` (chase the inductive hypothesis, then `f m ≤ sumRange f
/// m ≤ sumRange f (succ m)`) or `k = m` (transport `f m ≤ sumRange f (succ
/// m)` along the equality) via `Nat.lt_or_eq_of_le`/`Nat.le_of_lt_succ` —
/// there is no way around this split; it is the classical proof. Kept
/// private: only [`declare_prob_le_one`] needs it.
fn term_le_sum_range(d: &mut IntDev<'_>, p: RatPrelude, pf: ExprId, n: ExprId) -> (ExprId, ExprId) {
    let nat = d.nat_ty();

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let hyp = bounded_nonneg(d, p, pf, x);
        let sum = rsum_range(d, p, pf, x);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let k_lt = d.lt(k, x);
        let fk = d.apply(pf, &[k]);
        let concl = rle(d, p, fk, sum);
        let inner = d.arrow(k_lt, concl);
        let with_k = d.pi_fv(k_fv, nat, inner);
        d.arrow(hyp, with_k)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_n = d.zero();
            let hyp_ty = bounded_nonneg(d, p, pf, zero_n);
            let h_fv = d.fresh_fvar();
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let k_lt = d.lt(k, zero_n);
            let hi_fv = d.fresh_fvar();
            let hi = d.kernel().fvar(hi_fv);
            let sum0 = rsum_range(d, p, pf, zero_n);
            let fk = d.apply(pf, &[k]);
            let concl = rle(d, p, fk, sum0);
            let np = d.prelude();
            let impossible = d.lemma(np.not_lt_zero, &[k, hi]);
            let body = d.absurd(concl, impossible);
            let with_hi = d.lam_fv(hi_fv, k_lt, body);
            let with_k = d.lam_fv(k_fv, nat, with_hi);
            d.lam_fv(h_fv, hyp_ty, with_k)
        },
        &|d, m, ih| {
            let sm = d.succ(m);
            let hyp_ty = bounded_nonneg(d, p, pf, sm);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let np = d.prelude();
            let h_at_m = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let hi_ty = d.lt(i, m);
                let hi_fv = d.fresh_fvar();
                let hi = d.kernel().fvar(hi_fv);
                let le_succ_m = d.lemma(np.le_succ, &[m]);
                let lifted = d.lemma(np.lt_of_lt_of_le, &[i, m, sm, hi, le_succ_m]);
                let applied = d.apply(h, &[i, lifted]);
                let with_hi = d.lam_fv(hi_fv, hi_ty, applied);
                d.lam_fv(i_fv, nat, with_hi)
            };
            let ih_applied = d.apply(ih, &[h_at_m]);

            let lt_m_sm = d.lemma(np.lt_succ_self, &[m]);
            let f_m_nonneg = d.apply(h, &[m, lt_m_sm]);

            let sum_m = rsum_range(d, p, pf, m);
            let f_m = d.apply(pf, &[m]);
            let sum_sm = radd(d, sum_m, f_m);

            // sum_m ≤ sum_m + f_m, since 0 ≤ f_m.
            let sum_m_le_sum_sm = {
                let le_refl_sum_m = d.lemma(p.le_refl, &[sum_m]);
                let zero_r = rzero(d, p);
                let h_add = d.lemma(
                    p.add_le_add,
                    &[sum_m, sum_m, zero_r, f_m, le_refl_sum_m, f_m_nonneg],
                );
                let zero_r2 = rzero(d, p);
                let sum_m_plus_zero = radd(d, sum_m, zero_r2);
                let eq_add_zero = d.lemma(p.add_zero, &[sum_m]);
                let motive_le = |d: &mut IntDev<'_>, t: ExprId| -> ExprId { rle(d, p, t, sum_sm) };
                rat_eq_rewrite(d, sum_m_plus_zero, sum_m, eq_add_zero, h_add, &motive_le)
            };

            // f_m ≤ sum_m + f_m, since 0 ≤ sum_m.
            let f_m_le_sum_sm = {
                let sum_m_nonneg = d.lemma(p.sum_range_nonneg, &[pf, m, h_at_m]);
                let le_refl_f_m = d.lemma(p.le_refl, &[f_m]);
                let zero_r = rzero(d, p);
                let h_add2 = d.lemma(
                    p.add_le_add,
                    &[zero_r, sum_m, f_m, f_m, sum_m_nonneg, le_refl_f_m],
                );
                let zero_r2 = rzero(d, p);
                let zero_plus_fm = radd(d, zero_r2, f_m);
                let eq_zero_add = d.lemma(p.zero_add, &[f_m]);
                let motive_le = |d: &mut IntDev<'_>, t: ExprId| -> ExprId { rle(d, p, t, sum_sm) };
                rat_eq_rewrite(d, zero_plus_fm, f_m, eq_zero_add, h_add2, &motive_le)
            };

            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let k_lt_sm = d.lt(k, sm);
            let klt_fv = d.fresh_fvar();
            let klt = d.kernel().fvar(klt_fv);

            let k_le_m = d.lemma(np.le_of_lt_succ, &[k, m, klt]);
            let disj = d.lemma(np.lt_or_eq_of_le, &[k, m, k_le_m]);
            let lt_ty = d.lt(k, m);
            let eq_ty = d.eq(k, m);

            let fk = d.apply(pf, &[k]);
            let target = rle(d, p, fk, sum_sm);
            let body = d.or_elim(
                lt_ty,
                eq_ty,
                target,
                disj,
                &|d, hlt| {
                    let fk_le_summ = d.apply(ih_applied, &[k, hlt]);
                    d.lemma(
                        p.le_trans,
                        &[fk, sum_m, sum_sm, fk_le_summ, sum_m_le_sum_sm],
                    )
                },
                &|d, heq| {
                    let f_m2 = d.apply(pf, &[m]);
                    let rewritten = nat_eq_to_rat(d, k, m, heq, &|d, x| d.apply(pf, &[x]));
                    let flipped = rsymm(d, fk, f_m2, rewritten);
                    let motive_le =
                        |d: &mut IntDev<'_>, t: ExprId| -> ExprId { rle(d, p, t, sum_sm) };
                    rat_eq_rewrite(d, f_m2, fk, flipped, f_m_le_sum_sm, &motive_le)
                },
            );

            let with_klt = d.lam_fv(klt_fv, k_lt_sm, body);
            let with_k = d.lam_fv(k_fv, nat, with_klt);
            d.lam_fv(h_fv, hyp_ty, with_k)
        },
        n,
    );
    (stmt, proof)
}

/// `Rat.prob_le_one : ∀ p n, IsDistribution p n → ∀ k, Lt k n → le (p k)
/// one` — every individual probability is at most `1`. The first genuinely
/// probabilistic statement in this repository.
fn declare_prob_le_one(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let klt_fv = d.fresh_fvar();
    let klt = d.kernel().fvar(klt_fv);

    let dist_ty = is_distribution(d, p, pf, n);
    let klt_ty = d.lt(k, n);
    let fk = d.apply(pf, &[k]);
    let one_r = rone(d, p);
    let concl = rle(d, p, fk, one_r);

    let (nonneg_part, sum_part) = is_distribution_parts(d, p, pf, n);
    let h_nonneg = d.and_left(nonneg_part, sum_part, h);
    let h_sum = d.and_right(nonneg_part, sum_part, h);

    let (_term_stmt, term_proof) = term_le_sum_range(d, p, pf, n);
    let bounded_result = d.apply(term_proof, &[h_nonneg]);
    let fk_le_sum = d.apply(bounded_result, &[k, klt]);

    let sum_n = rsum_range(d, p, pf, n);
    let motive_le = |d: &mut IntDev<'_>, t: ExprId| -> ExprId { rle(d, p, fk, t) };
    let fk_le_one = rat_eq_rewrite(d, sum_n, one_r, h_sum, fk_le_sum, &motive_le);

    let value = {
        let with_klt = d.lam_fv(klt_fv, klt_ty, fk_le_one);
        let with_k = d.lam_fv(k_fv, nat, with_klt);
        let with_h = d.lam_fv(h_fv, dist_ty, with_k);
        let with_n = d.lam_fv(n_fv, nat, with_h);
        d.lam_fv(pf_fv, fn_ty, with_n)
    };
    let ty = {
        let inner = d.arrow(klt_ty, concl);
        let with_k = d.pi_fv(k_fv, nat, inner);
        let with_h = d.arrow(dist_ty, with_k);
        let with_n = d.pi_fv(n_fv, nat, with_h);
        d.pi_fv(pf_fv, fn_ty, with_n)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.prob_le_one,
        uparams: vec![],
        ty,
        value,
    })
}

/// `fun k => pf (m + k)` — the tail of `pf` starting at `m`.
fn shifted(d: &mut IntDev<'_>, pf: ExprId, m: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let idx = d.add(m, k);
    let body = d.apply(pf, &[idx]);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `Eq Rat (sumRange pf (m+j)) (sumRange pf m + sumRange (shifted pf m) j)`,
/// proved by induction on `j` (`m`, `pf` fixed) — no `Nat` subtraction is
/// needed since the split point `m` and the tail length `j` are the two
/// things quantified, and their sum IS the bound `sumRange` is taken over:
/// `Nat.add m (succ j) ≡ succ (Nat.add m j)` definitionally, matching
/// `sumRange`'s own `succ`-case ι-reduction at every step. Kept private: only
/// [`declare_prob_complement`] needs it.
fn sum_range_split(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    pf: ExprId,
    m: ExprId,
    j: ExprId,
) -> (ExprId, ExprId) {
    let g = shifted(d, pf, m);
    let sum_p_m = rsum_range(d, p, pf, m);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let bound = d.add(m, x);
        let lhs = rsum_range(d, p, pf, bound);
        let tail = rsum_range(d, p, g, x);
        let rhs = radd(d, sum_p_m, tail);
        super::ops::req(d, lhs, rhs)
    };
    let stmt = motive(d, j);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_r = rzero(d, p);
            let rhs = radd(d, sum_p_m, zero_r);
            let h = d.lemma(p.add_zero, &[sum_p_m]);
            // h : Eq Rat rhs sum_p_m (`add_zero`); flip to Eq Rat sum_p_m rhs.
            rsymm(d, rhs, sum_p_m, h)
        },
        &|d, k, ih| {
            let mk = d.add(m, k);
            let p_mk = d.apply(pf, &[mk]);
            let sum_g_k = rsum_range(d, p, g, k);

            let sum_pf_mk = rsum_range(d, p, pf, mk);
            let start = radd(d, sum_pf_mk, p_mk);
            let sum_p_m_g_k = radd(d, sum_p_m, sum_g_k);
            let mid = radd(d, sum_p_m_g_k, p_mk);
            let sum_pf_mk2 = rsum_range(d, p, pf, mk);
            let sum_p_m_g_k2 = radd(d, sum_p_m, sum_g_k);
            let h1 = super::ops::rcongr(d, sum_pf_mk2, sum_p_m_g_k2, ih, &|d, t| radd(d, t, p_mk));

            let sum_g_k_p_mk = radd(d, sum_g_k, p_mk);
            let end = radd(d, sum_p_m, sum_g_k_p_mk);
            let h2 = d.lemma(p.add_assoc, &[sum_p_m, sum_g_k, p_mk]);

            let (_e, chained) = super::ops::rchain(d, start, &[(mid, h1), (end, h2)]);
            chained
        },
        j,
    );
    (stmt, proof)
}

/// `Rat.prob_complement : ∀ p m j, IsDistribution p (m+j) → sumRange p m +
/// sumRange (fun k => p (m+k)) j = one` — the mass of a prefix of length `m`
/// and its complementary tail (length `j`) sum to `1`.
///
/// The general "sum over an arbitrary sub-range" needs machinery
/// ([`Nat` subtraction reasoning about an arbitrary `m ≤ n`]) this slice does
/// not build; this is the prefix form the task allows, via
/// [`sum_range_split`].
fn declare_prob_complement(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let bound = d.add(m, j);
    let dist_ty = is_distribution(d, p, pf, bound);

    let (nonneg_part, sum_part) = is_distribution_parts(d, p, pf, bound);
    let h_sum = d.and_right(nonneg_part, sum_part, h);

    let (_split_stmt, split_proof) = sum_range_split(d, p, pf, m, j);
    let g = shifted(d, pf, m);
    let sum_pf_m = rsum_range(d, p, pf, m);
    let sum_g_j = rsum_range(d, p, g, j);
    let target = radd(d, sum_pf_m, sum_g_j);
    let sum_bound = rsum_range(d, p, pf, bound);

    let split_rev = rsymm(d, sum_bound, target, split_proof);
    let one_r = rone(d, p);
    let final_proof = rtrans(d, target, sum_bound, one_r, split_rev, h_sum);
    let one_r2 = rone(d, p);
    let concl = super::ops::req(d, target, one_r2);

    let value = {
        let with_h = d.lam_fv(h_fv, dist_ty, final_proof);
        let with_j = d.lam_fv(j_fv, nat, with_h);
        let with_m = d.lam_fv(m_fv, nat, with_j);
        d.lam_fv(pf_fv, fn_ty, with_m)
    };
    let ty = {
        let inner = d.arrow(dist_ty, concl);
        let with_j = d.pi_fv(j_fv, nat, inner);
        let with_m = d.pi_fv(m_fv, nat, with_j);
        d.pi_fv(pf_fv, fn_ty, with_m)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.prob_complement,
        uparams: vec![],
        ty,
        value,
    })
}

// --- expectation and its linearity -----------------------------------------

/// `Rat.expectation X p n`, i.e. `d.const_app(p.expectation, &[x, pf, n])`.
fn expectation(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId, pf: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.expectation, &[x, pf, n])
}

/// `fun (_ : Nat) => c`.
fn const_fn(d: &mut IntDev<'_>, c: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, c)
}

/// `fun k => x k * pf k` — the summand [`declare_expectation`] admits
/// `Rat.expectation` as, rebuilt here (mirroring
/// [`super::probability::is_distribution_parts`]'s own reason: callers need
/// the exact literal shape `Rat.expectation` unfolds to, not a re-declared
/// stand-in).
fn weighted(d: &mut IntDev<'_>, x: ExprId, pf: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let xk = d.apply(x, &[k]);
    let pk = d.apply(pf, &[k]);
    let body = rmul(d, xk, pk);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `fun k => x k + y k`.
fn combined(d: &mut IntDev<'_>, x: ExprId, y: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let xk = d.apply(x, &[k]);
    let yk = d.apply(y, &[k]);
    let body = radd(d, xk, yk);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `fun k => x k * pf k + y k * pf k`.
fn split_weighted(d: &mut IntDev<'_>, x: ExprId, y: ExprId, pf: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let xk = d.apply(x, &[k]);
    let yk = d.apply(y, &[k]);
    let pk = d.apply(pf, &[k]);
    let xkpk = rmul(d, xk, pk);
    let ykpk = rmul(d, yk, pk);
    let body = radd(d, xkpk, ykpk);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `fun k => a * x k`.
fn scale_fn(d: &mut IntDev<'_>, a: ExprId, x: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let xk = d.apply(x, &[k]);
    let body = rmul(d, a, xk);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `fun k => a * (x k * pf k)`.
fn scale_weighted(d: &mut IntDev<'_>, a: ExprId, x: ExprId, pf: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let xk = d.apply(x, &[k]);
    let pk = d.apply(pf, &[k]);
    let xkpk = rmul(d, xk, pk);
    let body = rmul(d, a, xkpk);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// Admit `Rat.expectation : (Nat → Rat) → (Nat → Rat) → Nat → Rat := fun X p
/// n => sumRange (fun k => X k * p k) n`.
fn declare_expectation(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let summand = weighted(d, x, pf);
    let body = rsum_range(d, p, summand, n);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        d.lam_fv(x_fv, fn_ty, with_pf)
    };
    let ty = {
        let inner = d.arrow(nat, carrier);
        let over_pf = d.arrow(fn_ty, inner);
        d.arrow(fn_ty, over_pf)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.expectation,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(EXPECTATION_HEIGHT),
    })
}

/// `Rat.expectation_add : ∀ X Y p n,
/// expectation (fun k => X k + Y k) p n = expectation X p n + expectation Y p n`.
///
/// The additive half of linearity. [`RatPrelude::right_distrib`] distributes
/// the summand pointwise (via `sumRange_congr`), then
/// [`RatPrelude::sum_range_add`] splits the sum — no rearrangement lemma
/// needed, since the two scalar-free sums land directly on the goal's two
/// sides.
fn declare_expectation_add(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let xy = combined(d, x, y);
    let lhs = expectation(d, p, xy, pf, n);
    let ex = expectation(d, p, x, pf, n);
    let ey = expectation(d, p, y, pf, n);
    let rhs = radd(d, ex, ey);
    let stmt = req(d, lhs, rhs);

    // sumRange (fun k => (X k+Y k)*p k) n = sumRange (fun k => X k*p k + Y k*p k) n
    let combined_summand = weighted(d, xy, pf);
    let target_summand = split_weighted(d, x, y, pf);
    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let xk = d.apply(x, &[k]);
        let yk = d.apply(y, &[k]);
        let pk = d.apply(pf, &[k]);
        let body = d.lemma(p.right_distrib, &[xk, yk, pk]);
        d.lam_fv(k_fv, nat, body)
    };
    let congr_step = d.lemma(
        p.sum_range_congr,
        &[combined_summand, target_summand, n, pointwise],
    );

    // sumRange (fun k => X k*p k + Y k*p k) n = sumRange fX n + sumRange fY n
    let fx = weighted(d, x, pf);
    let fy = weighted(d, y, pf);
    let add_step = d.lemma(p.sum_range_add, &[fx, fy, n]);

    let sum_combined = rsum_range(d, p, combined_summand, n);
    let sum_target = rsum_range(d, p, target_summand, n);
    let (_e, proof) = rchain(
        d,
        sum_combined,
        &[(sum_target, congr_step), (rhs, add_step)],
    );

    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_y = d.lam_fv(y_fv, fn_ty, with_pf);
        d.lam_fv(x_fv, fn_ty, with_y)
    };
    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        let with_y = d.pi_fv(y_fv, fn_ty, with_pf);
        d.pi_fv(x_fv, fn_ty, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.expectation_add,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.expectation_smul : ∀ a X p n,
/// expectation (fun k => a * X k) p n = a * expectation X p n`.
///
/// The scalar half of linearity. [`RatPrelude::mul_assoc`] regroups the
/// summand pointwise, then [`RatPrelude::mul_sum_range`] pulls the constant
/// back out of the sum.
fn declare_expectation_smul(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let scaled_x = scale_fn(d, a, x);
    let lhs = expectation(d, p, scaled_x, pf, n);
    let ex = expectation(d, p, x, pf, n);
    let rhs = rmul(d, a, ex);
    let stmt = req(d, lhs, rhs);

    // sumRange (fun k => (a*X k)*p k) n = sumRange (fun k => a*(X k*p k)) n
    let combined_summand = weighted(d, scaled_x, pf);
    let regrouped_summand = scale_weighted(d, a, x, pf);
    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let xk = d.apply(x, &[k]);
        let pk = d.apply(pf, &[k]);
        let body = d.lemma(p.mul_assoc, &[a, xk, pk]);
        d.lam_fv(k_fv, nat, body)
    };
    let congr_step = d.lemma(
        p.sum_range_congr,
        &[combined_summand, regrouped_summand, n, pointwise],
    );

    // sumRange (fun k => a*(X k*p k)) n = a * sumRange (fun k => X k*p k) n
    let fx = weighted(d, x, pf);
    let mul_step = d.lemma(p.mul_sum_range, &[a, fx, n]);
    let sum_fx = rsum_range(d, p, fx, n);
    let a_sum_fx = rmul(d, a, sum_fx);
    let sum_regrouped = rsum_range(d, p, regrouped_summand, n);
    let mul_step_rev = rsymm(d, a_sum_fx, sum_regrouped, mul_step);

    let sum_combined = rsum_range(d, p, combined_summand, n);
    let (_e, proof) = rchain(
        d,
        sum_combined,
        &[(sum_regrouped, congr_step), (a_sum_fx, mul_step_rev)],
    );

    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_x = d.lam_fv(x_fv, fn_ty, with_pf);
        d.lam_fv(a_fv, carrier, with_x)
    };
    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        let with_x = d.pi_fv(x_fv, fn_ty, with_pf);
        d.pi_fv(a_fv, carrier, with_x)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.expectation_smul,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.expectation_const : ∀ c p n, IsDistribution p n →
/// expectation (fun _ => c) p n = c`.
///
/// The first theorem in this file that *uses* `IsDistribution`'s
/// `sumRange p n = one` component rather than only carrying it.
fn declare_expectation_const(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let const_c = const_fn(d, c);
    let lhs = expectation(d, p, const_c, pf, n);
    let dist_ty = is_distribution(d, p, pf, n);
    let stmt_body = req(d, lhs, c);
    let stmt = d.arrow(dist_ty, stmt_body);

    let (nonneg_part, sum_part) = is_distribution_parts(d, p, pf, n);
    let h_sum = d.and_right(nonneg_part, sum_part, h);

    let summand = weighted(d, const_c, pf);
    let sum_summand = rsum_range(d, p, summand, n);
    let sum_pf = rsum_range(d, p, pf, n);
    let c_sum_pf = rmul(d, c, sum_pf);

    let mul_step = d.lemma(p.mul_sum_range, &[c, pf, n]);
    let mul_step_rev = rsymm(d, c_sum_pf, sum_summand, mul_step);

    let one_r = rone(d, p);
    let c_one = rmul(d, c, one_r);
    let congr_c = rcongr(d, sum_pf, one_r, h_sum, &|d, t| rmul(d, c, t));
    let mul_one_step = d.lemma(p.mul_one, &[c]);

    let (_e, chained) = rchain(
        d,
        sum_summand,
        &[
            (c_sum_pf, mul_step_rev),
            (c_one, congr_c),
            (c, mul_one_step),
        ],
    );

    let value = {
        let with_h = d.lam_fv(h_fv, dist_ty, chained);
        let with_n = d.lam_fv(n_fv, nat, with_h);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        d.lam_fv(c_fv, carrier, with_pf)
    };
    let ty = {
        let with_h = d.arrow(dist_ty, stmt_body);
        let with_n = d.pi_fv(n_fv, nat, with_h);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        d.pi_fv(c_fv, carrier, with_pf)
    };
    let _ = stmt;
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.expectation_const,
        uparams: vec![],
        ty,
        value,
    })
}

// --- the uniform distribution ------------------------------------------------

/// `Rat.natDivSucc n 0` — `n` seen as a rational.
fn nat_as_rat(d: &mut IntDev<'_>, p: RatPrelude, n: ExprId) -> ExprId {
    let zero_nat = d.num(0);
    d.const_app(p.nat_div_succ, &[n, zero_nat])
}

/// `And.intro left right lp rp : And left right`.
fn and_intro(d: &mut IntDev<'_>, left: ExprId, right: ExprId, lp: ExprId, rp: ExprId) -> ExprId {
    let intro = d.int().logic.and_intro;
    d.const_app(intro, &[left, right, lp, rp])
}

/// `Eq Rat (Rat.natDivSucc Nat.zero Nat.zero) Rat.zero` — `Rat.self_normalize`
/// applied to `Rat.zero` itself: `num`/`den` are structure projections of
/// `Rat.zero`'s direct `Rat.mk`, so they reduce to exactly `natDivSucc`'s own
/// inputs (`0`, `1`), and `normalize`'s `1 ≤ den` argument is proof-irrelevant
/// — no gcd/cross-multiplication reasoning needed. The zero-companion of
/// `CReal.ratUnitEqOne`'s technique for `Rat.one`, reproduced here (not
/// reused: `Rat` cannot depend on `CReal`).
fn nat_div_succ_zero_eq_zero(d: &mut IntDev<'_>, p: RatPrelude) -> ExprId {
    let zero_r = rzero(d, p);
    d.lemma(p.self_normalize, &[zero_r])
}

/// `Eq Rat (Rat.natDivSucc 1 Nat.zero) Rat.one` — `CReal.ratUnitEqOne`'s own
/// technique, reproduced here for the same reason.
fn nat_div_succ_one_eq_one(d: &mut IntDev<'_>, p: RatPrelude) -> ExprId {
    let one_r = rone(d, p);
    d.lemma(p.self_normalize, &[one_r])
}

/// `Eq Rat (Rat.mul Rat.zero c) Rat.zero`, via `mul_comm` then `mul_zero` —
/// there is no standalone `zero_mul` law in this prelude.
fn rat_zero_mul(d: &mut IntDev<'_>, p: RatPrelude, c: ExprId) -> ExprId {
    let zero_r = rzero(d, p);
    let lhs = rmul(d, zero_r, c);
    let flipped = rmul(d, c, zero_r);
    let step1 = d.lemma(p.mul_comm, &[zero_r, c]);
    let step2 = d.lemma(p.mul_zero, &[c]);
    rtrans(d, lhs, flipped, zero_r, step1, step2)
}

/// `Eq Rat (sumRange (fun _ => c) j) (Rat.mul (natDivSucc j 0) c)` — `j`
/// copies of a constant `c` sum to `j` (seen as a rational) times `c`.
/// Induction on `j`, `c` fixed; [`declare_uniform_is_distribution`]
/// specialises at `j = n`, `c = inv (natDivSucc n 0)`, and closes with
/// `mul_inv_cancel`.
fn sum_range_const(d: &mut IntDev<'_>, p: RatPrelude, c: ExprId, j: ExprId) -> (ExprId, ExprId) {
    let constf = const_fn(d, c);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let lhs = rsum_range(d, p, constf, x);
        let nx = nat_as_rat(d, p, x);
        let rhs = rmul(d, nx, c);
        req(d, lhs, rhs)
    };
    let stmt = motive(d, j);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_r = rzero(d, p);
            let zero_n = d.zero();
            let nz = nat_as_rat(d, p, zero_n);
            let nz_c = rmul(d, nz, c);
            let zero_c = rmul(d, zero_r, c);

            let zero_mul_c = rat_zero_mul(d, p, c); // Eq(zero*c, zero)
            let step1 = rsymm(d, zero_c, zero_r, zero_mul_c); // Eq(zero, zero*c)

            let nz_eq_zero = nat_div_succ_zero_eq_zero(d, p); // ~ Eq(nz, zero)
            let zero_eq_nz = rsymm(d, nz, zero_r, nz_eq_zero); // ~ Eq(zero, nz)
            let step2 = rcongr(d, zero_r, nz, zero_eq_nz, &|d, t| rmul(d, t, c)); // Eq(zero*c, nz*c)

            let (_e, chained) = rchain(d, zero_r, &[(zero_c, step1), (nz_c, step2)]);
            chained
        },
        &|d, m, ih| {
            let nm = nat_as_rat(d, p, m);
            let ih_rhs = rmul(d, nm, c);
            let prior_sum = rsum_range(d, p, constf, m);
            let start = radd(d, prior_sum, c);

            let h1 = rcongr(d, prior_sum, ih_rhs, ih, &|d, t| radd(d, t, c));
            let after_ih = radd(d, ih_rhs, c);

            let one_nat = d.num(1);
            let zero_nat = d.num(0);
            let unit = d.const_app(p.nat_div_succ, &[one_nat, zero_nat]);
            let unit_c = rmul(d, unit, c);

            // c = unit*c, via unit = one [self_normalize] then mul_comm/mul_one.
            let unit_mul_c_eq_c = {
                let one_r = rone(d, p);
                let unit_eq_one = nat_div_succ_one_eq_one(d, p); // ~ Eq(unit, one)
                let step_a = rcongr(d, unit, one_r, unit_eq_one, &|d, t| rmul(d, t, c));
                let one_c = rmul(d, one_r, c);
                let c_one = rmul(d, c, one_r);
                let step_b = d.lemma(p.mul_comm, &[one_r, c]);
                let step_c = d.lemma(p.mul_one, &[c]);
                let (_e, ch) = rchain(d, unit_c, &[(one_c, step_a), (c_one, step_b), (c, step_c)]);
                ch
            };
            let c_eq_unit_c = rsymm(d, unit_c, c, unit_mul_c_eq_c);
            let h2 = rcongr(d, c, unit_c, c_eq_unit_c, &|d, t| radd(d, ih_rhs, t));
            let after_h2 = radd(d, ih_rhs, unit_c);

            // nm*c + unit*c = (nm+unit)*c
            let nm_plus_unit = radd(d, nm, unit);
            let nm_plus_unit_c = rmul(d, nm_plus_unit, c);
            let right_distrib_step = d.lemma(p.right_distrib, &[nm, unit, c]);
            let h3 = rsymm(d, nm_plus_unit_c, after_h2, right_distrib_step);

            // (nm+unit)*c = natDivSucc(succ m, 0)*c, via natDivSucc_add and
            // `Nat.add m 1` defeq `Nat.succ m`.
            let sm = d.succ(m);
            let nsm = nat_as_rat(d, p, sm);
            let add_eq = d.lemma(p.nat_div_succ_add, &[m, one_nat, zero_nat]);
            let h4 = rcongr(d, nm_plus_unit, nsm, add_eq, &|d, t| rmul(d, t, c));
            let target = rmul(d, nsm, c);

            let (_e, chained) = rchain(
                d,
                start,
                &[
                    (after_ih, h1),
                    (after_h2, h2),
                    (nm_plus_unit_c, h3),
                    (target, h4),
                ],
            );
            chained
        },
        j,
    );
    (stmt, proof)
}

/// Admit `Rat.uniform : Nat → Nat → Rat := fun n k => Rat.inv (Rat.natDivSucc
/// n 0)` — the uniform distribution on `n` outcomes, `k` unused.
fn declare_uniform(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let k_fv = d.fresh_fvar();

    let n_as_rat = nat_as_rat(d, p, n);
    let body = d.const_app(p.inv, &[n_as_rat]);
    let value = {
        let with_k = d.lam_fv(k_fv, nat, body);
        d.lam_fv(n_fv, nat, with_k)
    };
    let ty = {
        let over_k = d.arrow(nat, carrier);
        d.arrow(nat, over_k)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.uniform,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(EXPECTATION_HEIGHT),
    })
}

/// `Rat.uniform_is_distribution : ∀ n, Nat.lt Nat.zero n →
/// IsDistribution (uniform n) n`.
///
/// **The negative control [`RatPrelude::is_distribution`] needs**: without an
/// instance, every `IsDistribution` theorem is vacuously true. `0 < n`
/// rather than `n ≠ 0` because that is exactly the hypothesis
/// [`RatPrelude::nat_div_succ_pos`] wants, and `Nat.lt Nat.zero n` is
/// definitionally `Nat.le 1 n` — no conversion lemma needed, the hypothesis
/// is passed straight through.
fn declare_uniform_is_distribution(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let zero_n = d.zero();
    let pos_ty = d.lt(zero_n, n);

    let uniform_n = d.const_app(p.uniform, &[n]);
    let dist_ty = is_distribution(d, p, uniform_n, n);

    let n_as_rat = nat_as_rat(d, p, n);
    let n_pos = d.lemma(p.nat_div_succ_pos, &[n, zero_n, h]);
    let c = d.const_app(p.inv, &[n_as_rat]);

    let (nonneg_ty, sum_ty) = is_distribution_parts(d, p, uniform_n, n);

    let nonneg_proof = {
        let inv_pos = d.lemma(p.inv_pos, &[n_as_rat, n_pos]);
        let zero_r = rzero(d, p);
        let le_proof = d.lemma(p.le_of_lt, &[zero_r, c, inv_pos]);
        let k_fv = d.fresh_fvar();
        let klt_fv = d.fresh_fvar();
        let klt_ty = {
            let k = d.kernel().fvar(k_fv);
            d.lt(k, n)
        };
        let with_klt = d.lam_fv(klt_fv, klt_ty, le_proof);
        d.lam_fv(k_fv, nat, with_klt)
    };

    let sum_proof = {
        let (_stmt_sc, proof_sc) = sum_range_const(d, p, c, n);
        let constant_summand = const_fn(d, c);
        let a = rsum_range(d, p, constant_summand, n);
        let b = rmul(d, n_as_rat, c);
        let one_r = rone(d, p);
        let mul_inv = d.lemma(p.mul_inv_cancel, &[n_as_rat, n_pos]);
        rtrans(d, a, b, one_r, proof_sc, mul_inv)
    };

    let body = and_intro(d, nonneg_ty, sum_ty, nonneg_proof, sum_proof);

    let value = {
        let with_h = d.lam_fv(h_fv, pos_ty, body);
        d.lam_fv(n_fv, nat, with_h)
    };
    let ty = {
        let with_h = d.arrow(pos_ty, dist_ty);
        d.pi_fv(n_fv, nat, with_h)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.uniform_is_distribution,
        uparams: vec![],
        ty,
        value,
    })
}

// --- expectation is nonnegative and monotone --------------------------------

/// `Rat.expectation_nonneg : ∀ X p n, (∀ k, Lt k n → le zero (X k)) →
/// IsDistribution p n → le zero (expectation X p n)`.
///
/// Every bound the rest of this file proves rests on this and
/// [`declare_expectation_le`]: a nonnegative sequence weighted by a
/// nonnegative distribution sums to something nonnegative, via
/// [`RatPrelude::mul_nonneg`] pointwise and [`RatPrelude::sum_range_nonneg`].
/// Only `IsDistribution`'s nonnegativity component is used — the `sumRange p
/// n = one` half is not needed here.
fn declare_expectation_nonneg(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let hx_fv = d.fresh_fvar();
    let hx = d.kernel().fvar(hx_fv);
    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);

    let hx_ty = bounded_nonneg(d, p, x, n);
    let dist_ty = is_distribution(d, p, pf, n);
    let zero_r = rzero(d, p);
    let ex = expectation(d, p, x, pf, n);
    let concl = rle(d, p, zero_r, ex);

    let (nonneg_part, sum_part) = is_distribution_parts(d, p, pf, n);
    let hp_nonneg = d.and_left(nonneg_part, sum_part, hd);

    let summand = weighted(d, x, pf);
    let summand_nonneg_proof = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let klt_fv = d.fresh_fvar();
        let klt = d.kernel().fvar(klt_fv);
        let klt_ty = d.lt(k, n);
        let hxk = d.apply(hx, &[k, klt]);
        let hpk = d.apply(hp_nonneg, &[k, klt]);
        let xk = d.apply(x, &[k]);
        let pk = d.apply(pf, &[k]);
        let mul_nn = d.lemma(p.mul_nonneg, &[xk, pk, hxk, hpk]);
        let with_klt = d.lam_fv(klt_fv, klt_ty, mul_nn);
        d.lam_fv(k_fv, nat, with_klt)
    };
    let sum_nonneg = d.lemma(p.sum_range_nonneg, &[summand, n, summand_nonneg_proof]);

    let value = {
        let with_hd = d.lam_fv(hd_fv, dist_ty, sum_nonneg);
        let with_hx = d.lam_fv(hx_fv, hx_ty, with_hd);
        let with_n = d.lam_fv(n_fv, nat, with_hx);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        d.lam_fv(x_fv, fn_ty, with_pf)
    };
    let ty = {
        let with_hd = d.arrow(dist_ty, concl);
        let with_hx = d.arrow(hx_ty, with_hd);
        let with_n = d.pi_fv(n_fv, nat, with_hx);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        d.pi_fv(x_fv, fn_ty, with_pf)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.expectation_nonneg,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.expectation_le : ∀ X Y p n, (∀ k, Lt k n → le (X k) (Y k)) →
/// IsDistribution p n → le (expectation X p n) (expectation Y p n)` —
/// monotonicity. [`RatPrelude::mul_le_mul_of_nonneg_right`] lifts the
/// pointwise bound through the (nonnegative) weight, then
/// [`RatPrelude::sum_range_le`] lifts it through the sum.
fn declare_expectation_le(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let hxy_fv = d.fresh_fvar();
    let hxy = d.kernel().fvar(hxy_fv);
    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);

    let hxy_ty = bounded_pointwise_le(d, p, x, y, n);
    let dist_ty = is_distribution(d, p, pf, n);
    let ex = expectation(d, p, x, pf, n);
    let ey = expectation(d, p, y, pf, n);
    let concl = rle(d, p, ex, ey);

    let (nonneg_part, sum_part) = is_distribution_parts(d, p, pf, n);
    let hp_nonneg = d.and_left(nonneg_part, sum_part, hd);

    let fx = weighted(d, x, pf);
    let fy = weighted(d, y, pf);
    let pointwise_proof = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let klt_fv = d.fresh_fvar();
        let klt = d.kernel().fvar(klt_fv);
        let klt_ty = d.lt(k, n);
        let hxyk = d.apply(hxy, &[k, klt]);
        let hpk = d.apply(hp_nonneg, &[k, klt]);
        let xk = d.apply(x, &[k]);
        let yk = d.apply(y, &[k]);
        let pk = d.apply(pf, &[k]);
        let step = d.lemma(p.mul_le_mul_of_nonneg_right, &[xk, yk, pk, hpk, hxyk]);
        let with_klt = d.lam_fv(klt_fv, klt_ty, step);
        d.lam_fv(k_fv, nat, with_klt)
    };
    let sum_le = d.lemma(p.sum_range_le, &[fx, fy, n, pointwise_proof]);

    let value = {
        let with_hd = d.lam_fv(hd_fv, dist_ty, sum_le);
        let with_hxy = d.lam_fv(hxy_fv, hxy_ty, with_hd);
        let with_n = d.lam_fv(n_fv, nat, with_hxy);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_y = d.lam_fv(y_fv, fn_ty, with_pf);
        d.lam_fv(x_fv, fn_ty, with_y)
    };
    let ty = {
        let with_hd = d.arrow(dist_ty, concl);
        let with_hxy = d.arrow(hxy_ty, with_hd);
        let with_n = d.pi_fv(n_fv, nat, with_hxy);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        let with_y = d.pi_fv(y_fv, fn_ty, with_pf);
        d.pi_fv(x_fv, fn_ty, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.expectation_le,
        uparams: vec![],
        ty,
        value,
    })
}

// --- Markov's inequality -----------------------------------------------------

/// `Rat.markov_inequality : ∀ a X ind p n,
///   IsDistribution p n → (∀ k, Lt k n → le zero (X k)) → lt zero a →
///   (∀ k, Lt k n → le (a * ind k) (X k)) →
///   le (a * expectation ind p n) (expectation X p n)`.
///
/// The multiplied form of Markov's inequality — `a·E[ind] ≤ E[X]`, the same
/// statement as the classical `E[ind] ≤ E[X]/a` over an ordered field, but
/// needing no `Rat.inv`. `ind` is supplied as a HYPOTHESIS (`a·ind k ≤ X k`
/// pointwise, i.e. `ind` is `≥ 1` wherever `X` clears the threshold `a`, and
/// nonnegative always suffices) rather than constructed from `Rat.ble`:
/// building a genuine `{0,1}`-valued indicator and discharging this same
/// hypothesis from it is a short case split on `Rat.ble a (X k)`
/// (`mul_zero` when it is `false`, `mul_one`/`le_of_ble_eq_true` when it is
/// `true`) that can be layered on top as a corollary without changing this
/// statement.
///
/// [`RatPrelude::is_distribution`] is a genuine addition beyond the task's
/// sketch, and load-bearing: without `0 ≤ p k`, multiplying the pointwise
/// hypothesis by `p k` need not preserve the inequality direction, and the
/// conclusion is false the moment a weight goes negative. `0 ≤ X k` is
/// carried (matching the classical hypothesis) even though this particular
/// proof route does not need it — only `0 ≤ p k` and the pointwise bound do.
fn declare_markov_inequality(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let ind_fv = d.fresh_fvar();
    let ind = d.kernel().fvar(ind_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);
    let hx_fv = d.fresh_fvar();
    let ha_fv = d.fresh_fvar();
    let hind_fv = d.fresh_fvar();
    let hind = d.kernel().fvar(hind_fv);

    let dist_ty = is_distribution(d, p, pf, n);
    let hx_ty = bounded_nonneg(d, p, x, n);
    let zero_r = rzero(d, p);
    let ha_ty = rlt(d, p, zero_r, a);
    let scaled_ind = scale_fn(d, a, ind);
    let hind_ty = bounded_pointwise_le(d, p, scaled_ind, x, n);

    let concl = {
        let eind = expectation(d, p, ind, pf, n);
        let lhs = rmul(d, a, eind);
        let rhs = expectation(d, p, x, pf, n);
        rle(d, p, lhs, rhs)
    };

    let (nonneg_part, sum_part) = is_distribution_parts(d, p, pf, n);
    let hp_nonneg = d.and_left(nonneg_part, sum_part, hd);

    let scaled_summand = weighted(d, scaled_ind, pf);
    let x_summand = weighted(d, x, pf);
    let pointwise_proof = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let klt_fv = d.fresh_fvar();
        let klt = d.kernel().fvar(klt_fv);
        let klt_ty = d.lt(k, n);
        let hpk = d.apply(hp_nonneg, &[k, klt]);
        let hindk = d.apply(hind, &[k, klt]);
        let ind_k = d.apply(ind, &[k]);
        let a_ind_k = rmul(d, a, ind_k);
        let xk = d.apply(x, &[k]);
        let pk = d.apply(pf, &[k]);
        let step = d.lemma(p.mul_le_mul_of_nonneg_right, &[a_ind_k, xk, pk, hpk, hindk]);
        let with_klt = d.lam_fv(klt_fv, klt_ty, step);
        d.lam_fv(k_fv, nat, with_klt)
    };
    let sum_le = d.lemma(
        p.sum_range_le,
        &[scaled_summand, x_summand, n, pointwise_proof],
    );

    // sum_le : sumRange (weighted scaled_ind pf) n ≤ sumRange (weighted x pf) n
    //   ~ expectation scaled_ind pf n ≤ expectation x pf n              [defeq]
    let smul_eq = d.lemma(p.expectation_smul, &[a, ind, pf, n]);
    // smul_eq : expectation scaled_ind pf n = a * expectation ind pf n
    let scaled_expectation = expectation(d, p, scaled_ind, pf, n);
    let eind2 = expectation(d, p, ind, pf, n);
    let target_lhs = rmul(d, a, eind2);
    let x_expectation = expectation(d, p, x, pf, n);
    let final_proof = rat_eq_rewrite(
        d,
        scaled_expectation,
        target_lhs,
        smul_eq,
        sum_le,
        &|d, t| rle(d, p, t, x_expectation),
    );

    let value = {
        let with_hind = d.lam_fv(hind_fv, hind_ty, final_proof);
        let with_ha = d.lam_fv(ha_fv, ha_ty, with_hind);
        let with_hx = d.lam_fv(hx_fv, hx_ty, with_ha);
        let with_hd = d.lam_fv(hd_fv, dist_ty, with_hx);
        let with_n = d.lam_fv(n_fv, nat, with_hd);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_ind = d.lam_fv(ind_fv, fn_ty, with_pf);
        let with_x = d.lam_fv(x_fv, fn_ty, with_ind);
        d.lam_fv(a_fv, carrier, with_x)
    };
    let ty = {
        let with_hind = d.arrow(hind_ty, concl);
        let with_ha = d.arrow(ha_ty, with_hind);
        let with_hx = d.arrow(hx_ty, with_ha);
        let with_hd = d.arrow(dist_ty, with_hx);
        let with_n = d.pi_fv(n_fv, nat, with_hd);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        let with_ind = d.pi_fv(ind_fv, fn_ty, with_pf);
        let with_x = d.pi_fv(x_fv, fn_ty, with_ind);
        d.pi_fv(a_fv, carrier, with_x)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.markov_inequality,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.expectation_indicator_le_one : ∀ ind p n, IsDistribution p n →
/// (∀ k, Lt k n → Or (ind k = zero) (ind k = one)) →
/// le (expectation ind p n) one`.
///
/// Case-split the `{0,1}` hypothesis pointwise (`Or.rec`) to get `ind k ≤
/// one` in both branches — `le_refl one`, transported, when `ind k = one`;
/// `zero ≤ one` (`zero_lt_one`/`le_of_lt`), transported, when `ind k = zero`
/// — then lift through [`RatPrelude::expectation_le`] against the
/// constant-`1` function and collapse the bound with
/// [`RatPrelude::expectation_const`]. `ind` is a HYPOTHESIS here (any
/// `{0,1}`-valued sequence), the same choice [`declare_markov_inequality`]
/// makes for its own `ind` — `Rat.indicator` satisfies it by construction
/// (`ble_cases` selects exactly `zero`/`one`), but nothing here is tied to
/// that specific definition.
fn declare_expectation_indicator_le_one(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let ind_fv = d.fresh_fvar();
    let ind = d.kernel().fvar(ind_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);
    let hzo_fv = d.fresh_fvar();
    let hzo = d.kernel().fvar(hzo_fv);

    let dist_ty = is_distribution(d, p, pf, n);
    let zero_r = rzero(d, p);
    let one_r = rone(d, p);

    let hzo_ty = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let klt_ty = d.lt(k, n);
        let indk = d.apply(ind, &[k]);
        let left = req(d, indk, zero_r);
        let right = req(d, indk, one_r);
        let disj = d.or(left, right);
        let inner = d.arrow(klt_ty, disj);
        d.pi_fv(k_fv, nat, inner)
    };

    let eind = expectation(d, p, ind, pf, n);
    let concl = rle(d, p, eind, one_r);

    let pointwise_proof = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let klt_fv = d.fresh_fvar();
        let klt = d.kernel().fvar(klt_fv);
        let klt_ty = d.lt(k, n);
        let indk = d.apply(ind, &[k]);
        let hzk = d.apply(hzo, &[k, klt]);
        let left_ty = req(d, indk, zero_r);
        let right_ty = req(d, indk, one_r);
        let target = rle(d, p, indk, one_r);
        let body = d.or_elim(
            left_ty,
            right_ty,
            target,
            hzk,
            &|d, heq| {
                let zlt1 = d.lemma(p.zero_lt_one, &[]);
                let base = d.lemma(p.le_of_lt, &[zero_r, one_r, zlt1]);
                let flipped = rsymm(d, indk, zero_r, heq);
                rat_eq_rewrite(d, zero_r, indk, flipped, base, &|d, t| rle(d, p, t, one_r))
            },
            &|d, heq| {
                let base = d.lemma(p.le_refl, &[one_r]);
                let flipped = rsymm(d, indk, one_r, heq);
                rat_eq_rewrite(d, one_r, indk, flipped, base, &|d, t| rle(d, p, t, one_r))
            },
        );
        let with_klt = d.lam_fv(klt_fv, klt_ty, body);
        d.lam_fv(k_fv, nat, with_klt)
    };

    let const1 = const_fn(d, one_r);
    let expect_le = d.lemma(p.expectation_le, &[ind, const1, pf, n, pointwise_proof, hd]);
    let const_eq = d.lemma(p.expectation_const, &[one_r, pf, n, hd]);
    let e_const1 = expectation(d, p, const1, pf, n);
    let final_proof = rat_eq_rewrite(d, e_const1, one_r, const_eq, expect_le, &|d, t| {
        rle(d, p, eind, t)
    });

    let value = {
        let with_hzo = d.lam_fv(hzo_fv, hzo_ty, final_proof);
        let with_hd = d.lam_fv(hd_fv, dist_ty, with_hzo);
        let with_n = d.lam_fv(n_fv, nat, with_hd);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        d.lam_fv(ind_fv, fn_ty, with_pf)
    };
    let ty = {
        let with_hzo = d.arrow(hzo_ty, concl);
        let with_hd = d.arrow(dist_ty, with_hzo);
        let with_n = d.pi_fv(n_fv, nat, with_hd);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        d.pi_fv(ind_fv, fn_ty, with_pf)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.expectation_indicator_le_one,
        uparams: vec![],
        ty,
        value,
    })
}

// --- variance ----------------------------------------------------------------

/// `Rat.variance X p n`, i.e. `d.const_app(p.variance, &[x, pf, n])`.
fn variance(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId, pf: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.variance, &[x, pf, n])
}

/// `fun k => sub (x k) mu * sub (x k) mu` — the summand [`declare_variance`]
/// admits `Rat.variance` as, rebuilt here so [`declare_variance_nonneg`] and
/// [`declare_variance_eq`] can reconstruct the exact literal shape it
/// unfolds to (mirroring [`weighted`]/[`is_distribution_parts`]'s own
/// reason).
fn variance_summand(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId, mu: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let xk = d.apply(x, &[k]);
    let gap = rsub(d, p, xk, mu);
    let body = rmul(d, gap, gap);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// Admit `Rat.variance : (Nat → Rat) → (Nat → Rat) → Nat → Rat := fun X p n =>
/// expectation (fun k => sub (X k) (expectation X p n) * sub (X k)
/// (expectation X p n)) p n` — `Var[X] := E[(X − E[X])²]`.
fn declare_variance(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let mu = expectation(d, p, x, pf, n);
    let summand = variance_summand(d, p, x, mu);
    let body = expectation(d, p, summand, pf, n);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        d.lam_fv(x_fv, fn_ty, with_pf)
    };
    let ty = {
        let inner = d.arrow(nat, carrier);
        let over_pf = d.arrow(fn_ty, inner);
        d.arrow(fn_ty, over_pf)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.variance,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(VARIANCE_HEIGHT),
    })
}

/// `Rat.variance_nonneg : ∀ X p n, IsDistribution p n → le zero (variance X p
/// n)` — immediate from [`RatPrelude::expectation_nonneg`] and
/// [`RatPrelude::sq_nonneg`], since every summand is a square.
fn declare_variance_nonneg(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);

    let dist_ty = is_distribution(d, p, pf, n);
    let zero_r = rzero(d, p);
    let variance_xpn = variance(d, p, x, pf, n);
    let concl = rle(d, p, zero_r, variance_xpn);

    let mu = expectation(d, p, x, pf, n);
    let summand = variance_summand(d, p, x, mu);

    let nonneg_proof = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let klt_fv = d.fresh_fvar();
        let klt_ty = d.lt(k, n);
        let xk = d.apply(x, &[k]);
        let gap = rsub(d, p, xk, mu);
        let sqnn = d.lemma(p.sq_nonneg, &[gap]);
        let with_klt = d.lam_fv(klt_fv, klt_ty, sqnn);
        d.lam_fv(k_fv, nat, with_klt)
    };
    let ev_nonneg = d.lemma(p.expectation_nonneg, &[summand, pf, n, nonneg_proof, hd]);

    let value = {
        let with_hd = d.lam_fv(hd_fv, dist_ty, ev_nonneg);
        let with_n = d.lam_fv(n_fv, nat, with_hd);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        d.lam_fv(x_fv, fn_ty, with_pf)
    };
    let ty = {
        let with_hd = d.arrow(dist_ty, concl);
        let with_n = d.pi_fv(n_fv, nat, with_hd);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        d.pi_fv(x_fv, fn_ty, with_pf)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.variance_nonneg,
        uparams: vec![],
        ty,
        value,
    })
}

/// `(a-b)*(a-b) = a*a + (neg b*a + (neg b*a + b*b))`, over generic `a`, `b :
/// Rat`.
///
/// Returned as `(start, target, proof)` so [`declare_variance_eq`] can reuse
/// the two endpoints directly rather than re-deriving them from the `Eq`'s
/// own type. Two copies of `neg b * a` rather than one `neg (2*b) * a`, so no
/// literal `2` is needed: [`declare_variance_eq`] matches each copy against
/// a *separate* application of [`RatPrelude::expectation_add`]. Kept
/// private: only [`declare_variance_eq`] needs it.
fn sub_sq_expand(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    a: ExprId,
    b: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let neg_b = rneg(d, b);
    let w = rsub(d, p, a, b);
    let start = rmul(d, w, w);

    // (a + neg_b) * w = a*w + neg_b*w                        [right_distrib]
    let aw = rmul(d, a, w);
    let nbw = rmul(d, neg_b, w);
    let step1_rhs = radd(d, aw, nbw);
    let step1 = d.lemma(p.right_distrib, &[a, neg_b, w]);

    // a*w = a*a + a*neg_b                                     [left_distrib]
    let aa = rmul(d, a, a);
    let a_negb = rmul(d, a, neg_b);
    let aw_expanded = radd(d, aa, a_negb);
    let step2a = d.lemma(p.left_distrib, &[a, a, neg_b]);
    let mid1 = radd(d, aw_expanded, nbw);
    let h_mid1 = rcongr(d, aw, aw_expanded, step2a, &|d, t| radd(d, t, nbw));

    // neg_b*w = neg_b*a + neg_b*neg_b                         [left_distrib]
    let nba = rmul(d, neg_b, a);
    let nbnb = rmul(d, neg_b, neg_b);
    let nbw_expanded = radd(d, nba, nbnb);
    let step2b = d.lemma(p.left_distrib, &[neg_b, a, neg_b]);
    let mid2 = radd(d, aw_expanded, nbw_expanded);
    let h_mid2 = rcongr(d, nbw, nbw_expanded, step2b, &|d, t| {
        radd(d, aw_expanded, t)
    });

    // a*neg_b -> neg_b*a                                          [mul_comm]
    let comm1 = d.lemma(p.mul_comm, &[a, neg_b]);
    let aa_nba = radd(d, aa, nba);
    let mid3 = radd(d, aa_nba, nbw_expanded);
    let h_mid3 = rcongr(d, a_negb, nba, comm1, &|d, t| {
        let inner = radd(d, aa, t);
        radd(d, inner, nbw_expanded)
    });

    // neg_b*neg_b -> b*b                          [neg_mul, mul_neg, neg_neg]
    let bb = rmul(d, b, b);
    let neg_bb = rneg(d, bb);
    let b_negb = rmul(d, b, neg_b);
    let step_nm1 = d.lemma(p.neg_mul, &[b, neg_b]); // Eq(nbnb, -(b*neg_b))
    let neg_b_negb = rneg(d, b_negb);
    let step_nm2 = d.lemma(p.mul_neg, &[b, b]); // Eq(b*neg_b, -(b*b))
    let h_nm2 = rcongr(d, b_negb, neg_bb, step_nm2, &|d, t| rneg(d, t));
    let neg_neg_bb = rneg(d, neg_bb);
    let step_nn = d.lemma(p.neg_neg, &[bb]); // Eq(-(-(b*b)), b*b)
    let (_e, nbnb_to_bb) = rchain(
        d,
        nbnb,
        &[(neg_b_negb, step_nm1), (neg_neg_bb, h_nm2), (bb, step_nn)],
    );
    let nba_bb = radd(d, nba, bb);
    let nba_nba_bb = radd(d, nba, nba_bb);
    let target = radd(d, aa, nba_nba_bb);
    let mid4 = radd(d, aa_nba, nba_bb);
    let h_mid4 = rcongr(d, nbnb, bb, nbnb_to_bb, &|d, t| {
        let inner = radd(d, nba, t);
        radd(d, aa_nba, inner)
    });

    // (aa+nba) + (nba+bb) -> aa + (nba + (nba+bb))              [add_assoc]
    let step_assoc = d.lemma(p.add_assoc, &[aa, nba, nba_bb]);

    let (_e, proof) = rchain(
        d,
        start,
        &[
            (step1_rhs, step1),
            (mid1, h_mid1),
            (mid2, h_mid2),
            (mid3, h_mid3),
            (mid4, h_mid4),
            (target, step_assoc),
        ],
    );
    (start, target, proof)
}

/// `Rat.variance_eq : ∀ X p n, IsDistribution p n → variance X p n =
/// sub (expectation (fun k => X k * X k) p n) (mul (expectation X p n)
/// (expectation X p n))` — `Var[X] = E[X²] − E[X]²`, the identity every
/// variance computation uses.
///
/// [`RatPrelude::expectation_add`] (twice, nested) splits the three-term
/// pointwise expansion [`sub_sq_expand`] produces; [`RatPrelude::expectation_smul`]
/// collapses each `−E[X]·X` piece; [`RatPrelude::expectation_const`] — the
/// ONLY place in this file that needs `IsDistribution`'s `sumRange p n = 1`
/// component rather than just its nonnegativity — collapses the constant
/// `E[X]²` piece.
fn declare_variance_eq(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);

    let dist_ty = is_distribution(d, p, pf, n);
    let mu = expectation(d, p, x, pf, n);
    let mumu = rmul(d, mu, mu);
    let xx = weighted(d, x, x); // fun k => X k * X k
    let e_xx = expectation(d, p, xx, pf, n);
    let target_rhs = rsub(d, p, e_xx, mumu);
    let variance_xpn = variance(d, p, x, pf, n);
    let concl = req(d, variance_xpn, target_rhs);

    // --- pointwise: (X k - mu)*(X k - mu) = X k*X k + (negmu*Xk + (negmu*Xk + mu*mu))
    let neg_mu = rneg(d, mu);
    let t2_fn = scale_fn(d, neg_mu, x); // fun k => neg_mu * X k
    let t4_fn = const_fn(d, mumu); // fun _ => mu*mu
    let rest2_fn = combined(d, t2_fn, t4_fn);
    let rest1_fn = combined(d, t2_fn, rest2_fn);
    let abc_fn = combined(d, xx, rest1_fn);

    let variance_summand_fn = variance_summand(d, p, x, mu);

    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let xk = d.apply(x, &[k]);
        let (start_k, target_k, proof_k) = sub_sq_expand(d, p, xk, mu);
        let pk = d.apply(pf, &[k]);
        let lifted = rcongr(d, start_k, target_k, proof_k, &|d, t| rmul(d, t, pk));
        d.lam_fv(k_fv, nat, lifted)
    };

    let variance_weighted = weighted(d, variance_summand_fn, pf);
    let abc_weighted = weighted(d, abc_fn, pf);
    let congr_step = d.lemma(
        p.sum_range_congr,
        &[variance_weighted, abc_weighted, n, pointwise],
    );
    // congr_step : sumRange(variance_weighted,n) = sumRange(abc_weighted,n)
    //   ~ variance X p n = expectation abc_fn p n                    [defeq]

    let e_abc = expectation(d, p, abc_fn, pf, n);

    // expectation_add, nested twice:
    //   E[ABC] = E[XX] + (E[T2] + (E[T2]+E[T4]))
    let e_t2 = expectation(d, p, t2_fn, pf, n);
    let e_t4 = expectation(d, p, t4_fn, pf, n);
    let e_rest2 = expectation(d, p, rest2_fn, pf, n);
    let e_rest1 = expectation(d, p, rest1_fn, pf, n);

    let eq1 = d.lemma(p.expectation_add, &[xx, rest1_fn, pf, n]);
    // Eq(e_abc, radd(e_xx, e_rest1))
    let eq2 = d.lemma(p.expectation_add, &[t2_fn, rest2_fn, pf, n]);
    // Eq(e_rest1, radd(e_t2, e_rest2))
    let eq3 = d.lemma(p.expectation_add, &[t2_fn, t4_fn, pf, n]);
    // Eq(e_rest2, radd(e_t2, e_t4))

    let after_eq1 = radd(d, e_xx, e_rest1);
    let step_rest2 = radd(d, e_t2, e_rest2);
    let lift2 = rcongr(d, e_rest1, step_rest2, eq2, &|d, t| radd(d, e_xx, t));
    let after_lift2 = radd(d, e_xx, step_rest2);
    let step_t4 = radd(d, e_t2, e_t4);
    let lift3 = rcongr(d, e_rest2, step_t4, eq3, &|d, t| {
        let inner = radd(d, e_t2, t);
        radd(d, e_xx, inner)
    });
    let e_t2_step_t4 = radd(d, e_t2, step_t4);
    let after_lift3 = radd(d, e_xx, e_t2_step_t4);

    // E[T2] = neg_mu * mu                                     [expectation_smul]
    let smul_eq = d.lemma(p.expectation_smul, &[neg_mu, x, pf, n]);
    let negmu_mu = rmul(d, neg_mu, mu);

    // E[T4] = mu*mu                          [expectation_const, needs IsDistribution]
    let const_eq = d.lemma(p.expectation_const, &[mumu, pf, n, hd]);

    let e_t2_mumu = radd(d, e_t2, mumu);
    let e_t2_e_t2_mumu = radd(d, e_t2, e_t2_mumu);
    let after_step_a = radd(d, e_xx, e_t2_e_t2_mumu);
    let step_a = rcongr(d, e_t4, mumu, const_eq, &|d, t| {
        let inner1 = radd(d, e_t2, t);
        let inner2 = radd(d, e_t2, inner1);
        radd(d, e_xx, inner2)
    });

    let negmu_mu_mumu = radd(d, negmu_mu, mumu);
    let negmu_mu_negmu_mu_mumu = radd(d, negmu_mu, negmu_mu_mumu);
    let after_step_b = radd(d, e_xx, negmu_mu_negmu_mu_mumu);
    let step_b = rcongr(d, e_t2, negmu_mu, smul_eq, &|d, t| {
        let inner1 = radd(d, t, mumu);
        let inner2 = radd(d, t, inner1);
        radd(d, e_xx, inner2)
    });

    // negmu_mu = -(mumu)                                              [neg_mul]
    let neg_mumu = rneg(d, mumu);
    let step_negmul = d.lemma(p.neg_mul, &[mu, mu]); // Eq(negmu_mu, neg_mumu)
    let inner_collapsed = rcongr(d, negmu_mu, neg_mumu, step_negmul, &|d, t| {
        let inner = radd(d, t, mumu);
        radd(d, t, inner)
    });
    let neg_mumu_mumu = radd(d, neg_mumu, mumu);
    let neg_mumu_neg_mumu_mumu = radd(d, neg_mumu, neg_mumu_mumu);
    let after_step_c = radd(d, e_xx, neg_mumu_neg_mumu_mumu);
    let step_c = rcongr(
        d,
        negmu_mu_negmu_mu_mumu,
        neg_mumu_neg_mumu_mumu,
        inner_collapsed,
        &|d, t| radd(d, e_xx, t),
    );

    // neg_mumu + mumu = 0                                       [neg_add_cancel]
    let zero_r = rzero(d, p);
    let cancel = d.lemma(p.neg_add_cancel, &[mumu]); // Eq(radd(neg_mumu,mumu), zero)
    let inner_cancelled = rcongr(d, neg_mumu_mumu, zero_r, cancel, &|d, t| {
        radd(d, neg_mumu, t)
    });
    let neg_mumu_zero = radd(d, neg_mumu, zero_r);
    let after_step_d = radd(d, e_xx, neg_mumu_zero);
    let step_d = rcongr(
        d,
        neg_mumu_neg_mumu_mumu,
        neg_mumu_zero,
        inner_cancelled,
        &|d, t| radd(d, e_xx, t),
    );

    // neg_mumu + zero = neg_mumu                                        [add_zero]
    let add_zero_eq = d.lemma(p.add_zero, &[neg_mumu]);
    let after_step_e = radd(d, e_xx, neg_mumu);
    let step_e = rcongr(d, neg_mumu_zero, neg_mumu, add_zero_eq, &|d, t| {
        radd(d, e_xx, t)
    });

    let (_e, tail_proof) = rchain(
        d,
        e_abc,
        &[
            (after_eq1, eq1),
            (after_lift2, lift2),
            (after_lift3, lift3),
            (after_step_a, step_a),
            (after_step_b, step_b),
            (after_step_c, step_c),
            (after_step_d, step_d),
            (after_step_e, step_e),
        ],
    );
    // tail_proof : Eq(e_abc, radd(e_xx, neg_mumu))   [= E[X²] - mu*mu, unfolded]

    let final_proof = rtrans(d, variance_xpn, e_abc, after_step_e, congr_step, tail_proof);

    let value = {
        let with_hd = d.lam_fv(hd_fv, dist_ty, final_proof);
        let with_n = d.lam_fv(n_fv, nat, with_hd);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        d.lam_fv(x_fv, fn_ty, with_pf)
    };
    let ty = {
        let with_hd = d.arrow(dist_ty, concl);
        let with_n = d.pi_fv(n_fv, nat, with_hd);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        d.pi_fv(x_fv, fn_ty, with_pf)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.variance_eq,
        uparams: vec![],
        ty,
        value,
    })
}

/// `(a*w)*(a*w) = (a*a)*(w*w)`, over generic `a`, `w : Rat`.
///
/// Returned as `(start, target, proof)`, the same convention
/// [`sub_sq_expand`] uses. Five `mul_assoc`/`mul_comm` steps — private:
/// [`declare_variance_smul`] uses it for both the squared-deviation summand
/// and the squared mean.
fn scale_sq(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, w: ExprId) -> (ExprId, ExprId, ExprId) {
    let aw = rmul(d, a, w);
    let start = rmul(d, aw, aw);

    // (a*w)*(a*w) = a*(w*(a*w))                              [mul_assoc a w aw]
    let w_aw = rmul(d, w, aw);
    let mid1 = rmul(d, a, w_aw);
    let step1 = d.lemma(p.mul_assoc, &[a, w, aw]);

    // w*(a*w) = (w*a)*w, i.e. reverse of mul_assoc w a w
    let wa = rmul(d, w, a);
    let wa_w = rmul(d, wa, w);
    let h2 = d.lemma(p.mul_assoc, &[w, a, w]); // Eq(wa_w, w_aw)
    let h2rev = rsymm(d, wa_w, w_aw, h2); // Eq(w_aw, wa_w)
    let mid2 = rmul(d, a, wa_w);
    let step2 = rcongr(d, w_aw, wa_w, h2rev, &|d, t| rmul(d, a, t));

    // w*a = a*w                                                      [mul_comm]
    let aw2 = rmul(d, a, w);
    let aw2_w = rmul(d, aw2, w);
    let h3 = d.lemma(p.mul_comm, &[w, a]); // Eq(wa, aw2)
    let mid3 = rmul(d, a, aw2_w);
    let step3 = rcongr(d, wa, aw2, h3, &|d, t| {
        let inner = rmul(d, t, w);
        rmul(d, a, inner)
    });

    // (a*w)*w = a*(w*w)                                         [mul_assoc a w w]
    let ww = rmul(d, w, w);
    let a_ww = rmul(d, a, ww);
    let h4 = d.lemma(p.mul_assoc, &[a, w, w]); // Eq(aw2_w, a_ww)
    let mid4 = rmul(d, a, a_ww);
    let step4 = rcongr(d, aw2_w, a_ww, h4, &|d, t| rmul(d, a, t));

    // (a*a)*(w*w) = a*(a*(w*w)), reversed
    let aa = rmul(d, a, a);
    let target = rmul(d, aa, ww);
    let h5 = d.lemma(p.mul_assoc, &[a, a, ww]); // Eq(target, mid4)
    let h5rev = rsymm(d, target, mid4, h5); // Eq(mid4, target)

    let (_e, proof) = rchain(
        d,
        start,
        &[
            (mid1, step1),
            (mid2, step2),
            (mid3, step3),
            (mid4, step4),
            (target, h5rev),
        ],
    );
    (start, target, proof)
}

/// `sub (w*a) (w*b) = w * (sub a b)`, over generic `w`, `a`, `b : Rat`.
///
/// [`RatPrelude::sub_mul`] gives the RIGHT-multiplied form
/// (`sub (a*w) (b*w) = (sub a b)*w`); this is that identity with the scalar
/// commuted to the left on both sides. Private: only
/// [`declare_variance_smul`] needs it.
fn mul_sub_via_comm(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    w: ExprId,
    a: ExprId,
    b: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let wa = rmul(d, w, a);
    let wb = rmul(d, w, b);
    let start = rsub(d, p, wa, wb);

    let aw = rmul(d, a, w);
    let h1 = d.lemma(p.mul_comm, &[w, a]); // Eq(wa, aw)
    let mid1 = rsub(d, p, aw, wb);
    let step1 = rcongr(d, wa, aw, h1, &|d, t| rsub(d, p, t, wb));

    let bw = rmul(d, b, w);
    let h2 = d.lemma(p.mul_comm, &[w, b]); // Eq(wb, bw)
    let mid2 = rsub(d, p, aw, bw);
    let step2 = rcongr(d, wb, bw, h2, &|d, t| rsub(d, p, aw, t));

    let ab = rsub(d, p, a, b);
    let ab_w = rmul(d, ab, w);
    let step3 = d.lemma(p.sub_mul, &[a, b, w]); // Eq(mid2, ab_w)  [sub(aw,bw)=sub(a,b)*w]

    let target = rmul(d, w, ab);
    let step4 = d.lemma(p.mul_comm, &[ab, w]); // Eq(ab_w, target)

    let (_e, proof) = rchain(
        d,
        start,
        &[(mid1, step1), (mid2, step2), (ab_w, step3), (target, step4)],
    );
    (start, target, proof)
}

/// `Rat.variance_smul : ∀ a X p n, IsDistribution p n →
/// variance (fun k => a*X k) p n = (a*a) * variance X p n` — `Var[a·X] =
/// a²·Var[X]`.
///
/// Reuses [`RatPrelude::variance_eq`] on both sides: `Var[aX] = E[(aX)²] −
/// E[aX]²` and `Var[X] = E[X²] − E[X]²`. [`scale_sq`] turns the squared
/// summand `(a·X k)·(a·X k)` into `(a·a)·(X k·X k)` pointwise (lifted by
/// [`RatPrelude::sum_range_congr`] and pulled through the sum by
/// [`RatPrelude::expectation_smul`]) and separately turns the squared mean
/// `E[aX]·E[aX]` into `(a·a)·E[X]²` (via [`RatPrelude::expectation_smul`]
/// congr then [`scale_sq`] again); [`mul_sub_via_comm`] then factors the `a·a`
/// out of the resulting difference.
fn declare_variance_smul(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);

    let dist_ty = is_distribution(d, p, pf, n);
    let scaled_x = scale_fn(d, a, x);
    let variance_ax = variance(d, p, scaled_x, pf, n);
    let variance_x = variance(d, p, x, pf, n);
    let a_sq = rmul(d, a, a);
    let rhs = rmul(d, a_sq, variance_x);
    let concl = req(d, variance_ax, rhs);

    // veq_ax : variance_ax = sub(e_axax, e_ax*e_ax)
    let veq_ax = d.lemma(p.variance_eq, &[scaled_x, pf, n, hd]);
    let xx_ax = weighted(d, scaled_x, scaled_x); // fun k => (a*Xk)*(a*Xk)
    let e_axax = expectation(d, p, xx_ax, pf, n);
    let e_ax = expectation(d, p, scaled_x, pf, n);
    let e_ax_sq = rmul(d, e_ax, e_ax);
    let veq_ax_rhs = rsub(d, p, e_axax, e_ax_sq);

    // veq_x : variance_x = sub(e_xx, mu*mu)
    let veq_x = d.lemma(p.variance_eq, &[x, pf, n, hd]);
    let xx = weighted(d, x, x);
    let e_xx = expectation(d, p, xx, pf, n);
    let mu = expectation(d, p, x, pf, n);
    let mu_sq = rmul(d, mu, mu);
    let veq_x_rhs = rsub(d, p, e_xx, mu_sq);

    // Step A: e_axax = a_sq * e_xx
    let scale_ax_fn = scale_fn(d, a_sq, xx); // fun k => a_sq*(Xk*Xk)
    let pointwise_a = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let xk = d.apply(x, &[k]);
        let (start_k, target_k, proof_k) = scale_sq(d, p, a, xk);
        let pk = d.apply(pf, &[k]);
        let lifted = rcongr(d, start_k, target_k, proof_k, &|d, t| rmul(d, t, pk));
        d.lam_fv(k_fv, nat, lifted)
    };
    let xx_ax_weighted = weighted(d, xx_ax, pf);
    let scale_ax_weighted = weighted(d, scale_ax_fn, pf);
    let congr_a = d.lemma(
        p.sum_range_congr,
        &[xx_ax_weighted, scale_ax_weighted, n, pointwise_a],
    );
    // congr_a : Eq(sumRange(xx_ax_weighted,n), sumRange(scale_ax_weighted,n))
    //   ~ Eq(e_axax, expectation(scale_ax_fn,pf,n))                    [defeq]
    let smul_a = d.lemma(p.expectation_smul, &[a_sq, xx, pf, n]);
    // smul_a : Eq(expectation(scale_ax_fn,pf,n), a_sq*e_xx)
    let e_scale_ax = expectation(d, p, scale_ax_fn, pf, n);
    let a_sq_e_xx = rmul(d, a_sq, e_xx);
    let (_e, e_a_eq) = rchain(d, e_axax, &[(e_scale_ax, congr_a), (a_sq_e_xx, smul_a)]);
    // e_a_eq : Eq(e_axax, a_sq_e_xx)

    // Step B/C: e_ax_sq = a_sq * mu_sq
    let smul_b = d.lemma(p.expectation_smul, &[a, x, pf, n]);
    // smul_b : Eq(e_ax, a*mu)
    let a_mu = rmul(d, a, mu);
    let e_c1 = rcongr(d, e_ax, a_mu, smul_b, &|d, t| rmul(d, t, t));
    // e_c1 : Eq(e_ax*e_ax, (a*mu)*(a*mu))
    let a_mu_sq = rmul(d, a_mu, a_mu);
    let (_, target_c, proof_c) = scale_sq(d, p, a, mu);
    let (_e, e_c_eq) = rchain(d, e_ax_sq, &[(a_mu_sq, e_c1), (target_c, proof_c)]);
    // e_c_eq : Eq(e_ax_sq, target_c)  where target_c = a_sq*mu_sq

    // Step D: veq_ax_rhs = sub(a_sq*e_xx, a_sq*mu_sq)
    let d1 = rcongr(d, e_axax, a_sq_e_xx, e_a_eq, &|d, t| rsub(d, p, t, e_ax_sq));
    let after_d1 = rsub(d, p, a_sq_e_xx, e_ax_sq);
    let d2 = rcongr(d, e_ax_sq, target_c, e_c_eq, &|d, t| {
        rsub(d, p, a_sq_e_xx, t)
    });
    let after_d2 = rsub(d, p, a_sq_e_xx, target_c);

    // Step E: sub(a_sq*e_xx, a_sq*mu_sq) = a_sq * sub(e_xx,mu_sq)
    let (_, target_e, proof_e) = mul_sub_via_comm(d, p, a_sq, e_xx, mu_sq);

    // Step F: a_sq*veq_x_rhs = a_sq*variance_x                    [congr on veq_x]
    let veq_x_rev = rsymm(d, variance_x, veq_x_rhs, veq_x);
    let final_step = rcongr(d, veq_x_rhs, variance_x, veq_x_rev, &|d, t| {
        rmul(d, a_sq, t)
    });

    let (_e, tail_proof) = rchain(
        d,
        veq_ax_rhs,
        &[
            (after_d1, d1),
            (after_d2, d2),
            (target_e, proof_e),
            (rhs, final_step),
        ],
    );
    let final_proof = rtrans(d, variance_ax, veq_ax_rhs, rhs, veq_ax, tail_proof);

    let value = {
        let with_hd = d.lam_fv(hd_fv, dist_ty, final_proof);
        let with_n = d.lam_fv(n_fv, nat, with_hd);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_x = d.lam_fv(x_fv, fn_ty, with_pf);
        d.lam_fv(a_fv, carrier, with_x)
    };
    let ty = {
        let with_hd = d.arrow(dist_ty, concl);
        let with_n = d.pi_fv(n_fv, nat, with_hd);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        let with_x = d.pi_fv(x_fv, fn_ty, with_pf);
        d.pi_fv(a_fv, carrier, with_x)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.variance_smul,
        uparams: vec![],
        ty,
        value,
    })
}

// --- the constructed indicator (Rat.ble → {0,1}) ----------------------------
//
// `declare_markov_inequality` above takes `ind` as a HYPOTHESIS because there
// was no way to build one when it was proved: `Rat.le` is `Prop`-valued and
// cannot be branched on. `Rat.ble` (`rat_prelude/decide.rs`) changes that —
// it is a genuine `Bool`-valued decision, dispatching on the same integer
// cross-multiplication gap `Rat.max`/`Rat.min` use, so `Bool.rec` can select
// between two `Rat` values on it. This section builds that indicator and the
// two facts that make it usable, then reproves Markov (as
// [`declare_markov_constructed`]) and Chebyshev
// ([`declare_chebyshev_inequality`]) with it supplied rather than assumed —
// turning a conditional statement into an unconditional one.

/// `Bool.rec.{1}` selecting between two `Rat` values — the `Rat` counterpart
/// of `IntDev`'s own `bool_select_int` (`int_prelude/prod.rs`, private
/// there) and `NatOps::bool_select_nat`.
fn bool_select_rat(
    d: &mut IntDev<'_>,
    condition: ExprId,
    on_true: ExprId,
    on_false: ExprId,
) -> ExprId {
    let bool_ty = d.bool_ty();
    let carrier = rat_ty(d);
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, bool_ty, carrier, BinderInfo::Default);
    let one = d.level_one();
    let bool_rec = d.int().logic.bool_rec;
    let rec = d.kernel().const_(bool_rec, vec![one]);
    d.apply(rec, &[motive, on_false, on_true, condition])
}

/// `heq : Eq Bool cond true ⊢ Eq Rat (bool_select_rat cond a b) a`.
fn select_rat_true(d: &mut IntDev<'_>, cond: ExprId, a: ExprId, b: ExprId, heq: ExprId) -> ExprId {
    let true_val = d.bool_true();
    let symm_hb = d.bool_symm(cond, true_val, heq);
    let motive = d.bool_eq_motive(true_val, &|d, value| {
        let sel = bool_select_rat(d, value, a, b);
        req(d, sel, a)
    });
    let refl_case = rrefl(d, a);
    d.bool_transport(true_val, motive, refl_case, cond, symm_hb)
}

/// `heq : Eq Bool cond false ⊢ Eq Rat (bool_select_rat cond a b) b`.
fn select_rat_false(d: &mut IntDev<'_>, cond: ExprId, a: ExprId, b: ExprId, heq: ExprId) -> ExprId {
    let false_val = d.bool_false();
    let symm_hb = d.bool_symm(cond, false_val, heq);
    let motive = d.bool_eq_motive(false_val, &|d, value| {
        let sel = bool_select_rat(d, value, a, b);
        req(d, sel, b)
    });
    let refl_case = rrefl(d, b);
    d.bool_transport(false_val, motive, refl_case, cond, symm_hb)
}

/// Case-split a symbolic `cond : Bool` into `false`/`true`, proving a single
/// fixed `target : Prop` in each branch — the "generalise the selector, then
/// instantiate at `bool_refl(cond)`" trick `nat_prelude/finite.rs`'s
/// `compact_eq_of_gt` and `int_prelude/prod.rs`'s `ble_eq_false_of_lt` both
/// use, extracted here since [`declare_indicator_nonneg`] and
/// [`declare_indicator_le`] both need it. `on_false`/`on_true` receive the
/// equation (`cond = false`/`cond = true`) so they can unfold
/// `bool_select_rat` via [`select_rat_false`]/[`select_rat_true`].
fn ble_cases(
    d: &mut IntDev<'_>,
    cond: ExprId,
    target: ExprId,
    on_false: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
    on_true: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let bool_ty = d.bool_ty();
    let false_val = d.bool_false();
    let true_val = d.bool_true();

    let branch_for = |d: &mut IntDev<'_>, selector: ExprId| -> ExprId {
        let eq_cond_sel = d.bool_eq(cond, selector);
        d.arrow(eq_cond_sel, target)
    };
    let false_minor = {
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let heq_ty = d.bool_eq(cond, false_val);
        let body = on_false(d, heq);
        d.lam_fv(heq_fv, heq_ty, body)
    };
    let true_minor = {
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let heq_ty = d.bool_eq(cond, true_val);
        let body = on_true(d, heq);
        d.lam_fv(heq_fv, heq_ty, body)
    };
    let motive = {
        let sel_fv = d.fresh_fvar();
        let sel = d.kernel().fvar(sel_fv);
        let body = branch_for(d, sel);
        d.lam_fv(sel_fv, bool_ty, body)
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.int().logic.bool_rec;
    let rec = d.kernel().const_(bool_rec, vec![level_zero]);
    let selected = d.apply(rec, &[motive, false_minor, true_minor, cond]);
    let cond_refl = d.bool_refl(cond);
    d.apply(selected, &[cond_refl])
}

/// `Rat.ble a (X k)` — the condition [`declare_indicator`] dispatches on.
fn indicator_cond(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, xk: ExprId) -> ExprId {
    d.const_app(p.ble, &[a, xk])
}

/// `Rat.indicator a X k`, i.e. `d.const_app(p.indicator, &[a, x, k])`.
fn indicator(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, x: ExprId, k: ExprId) -> ExprId {
    d.const_app(p.indicator, &[a, x, k])
}

/// Admit `Rat.indicator : Rat → (Nat → Rat) → Nat → Rat := fun a X k =>
/// bool_select_rat (Rat.ble a (X k)) Rat.one Rat.zero` — `𝟙[a ≤ X k]`.
fn declare_indicator(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let xk = d.apply(x, &[k]);
    let cond = indicator_cond(d, p, a, xk);
    let one_r = rone(d, p);
    let zero_r = rzero(d, p);
    let body = bool_select_rat(d, cond, one_r, zero_r);

    let value = {
        let with_k = d.lam_fv(k_fv, nat, body);
        let with_x = d.lam_fv(x_fv, fn_ty, with_k);
        d.lam_fv(a_fv, carrier, with_x)
    };
    let ty = {
        let over_k = d.arrow(nat, carrier);
        let over_x = d.arrow(fn_ty, over_k);
        d.arrow(carrier, over_x)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.indicator,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(INDICATOR_HEIGHT),
    })
}

/// `Rat.indicator_nonneg : ∀ a X k, le zero (Rat.indicator a X k)`.
///
/// Case-split on `Rat.ble a (X k)`: `false` selects `Rat.zero` (`0 ≤ 0` by
/// `le_refl`), `true` selects `Rat.one` (`0 ≤ 1` from `zero_lt_one` +
/// `le_of_lt`).
fn declare_indicator_nonneg(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let xk = d.apply(x, &[k]);
    let cond = indicator_cond(d, p, a, xk);
    let one_r = rone(d, p);
    let zero_r = rzero(d, p);
    let ind_val = indicator(d, p, a, x, k);
    let concl = rle(d, p, zero_r, ind_val);

    let proof = ble_cases(
        d,
        cond,
        concl,
        &|d, heq| {
            let sel = bool_select_rat(d, cond, one_r, zero_r);
            let sel_eq_zero = select_rat_false(d, cond, one_r, zero_r, heq);
            let zero_eq_sel = rsymm(d, sel, zero_r, sel_eq_zero);
            let base = d.lemma(p.le_refl, &[zero_r]);
            rat_eq_rewrite(d, zero_r, sel, zero_eq_sel, base, &|d, t| {
                rle(d, p, zero_r, t)
            })
        },
        &|d, heq| {
            let sel = bool_select_rat(d, cond, one_r, zero_r);
            let sel_eq_one = select_rat_true(d, cond, one_r, zero_r, heq);
            let one_eq_sel = rsymm(d, sel, one_r, sel_eq_one);
            let zlt1 = d.lemma(p.zero_lt_one, &[]);
            let base = d.lemma(p.le_of_lt, &[zero_r, one_r, zlt1]);
            rat_eq_rewrite(d, one_r, sel, one_eq_sel, base, &|d, t| {
                rle(d, p, zero_r, t)
            })
        },
    );

    let value = {
        let with_k = d.lam_fv(k_fv, nat, proof);
        let with_x = d.lam_fv(x_fv, fn_ty, with_k);
        d.lam_fv(a_fv, carrier, with_x)
    };
    let ty = {
        let with_k = d.pi_fv(k_fv, nat, concl);
        let with_x = d.pi_fv(x_fv, fn_ty, with_k);
        d.pi_fv(a_fv, carrier, with_x)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.indicator_nonneg,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.indicator_le : ∀ a X k, le zero (X k) → le (a * Rat.indicator a X k)
/// (X k)` — exactly [`RatPrelude::markov_inequality`]'s fourth hypothesis,
/// now discharged from the constructed indicator instead of assumed.
///
/// Case-split on `Rat.ble a (X k)`: `false` selects `Rat.zero`, so `a *
/// indicator = a * 0 = 0 ≤ X k` is exactly the `0 ≤ X k` hypothesis
/// (`mul_zero`); `true` selects `Rat.one`, so `a * indicator = a * 1 = a ≤ X
/// k` is exactly `le_of_ble_eq_true` applied to the branch equation
/// (`mul_one`) — the `0 ≤ X k` hypothesis is not even needed in this branch.
fn declare_indicator_le(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hx_fv = d.fresh_fvar();
    let hx = d.kernel().fvar(hx_fv);

    let xk = d.apply(x, &[k]);
    let cond = indicator_cond(d, p, a, xk);
    let one_r = rone(d, p);
    let zero_r = rzero(d, p);
    let ind_val = indicator(d, p, a, x, k);
    let a_ind = rmul(d, a, ind_val);
    let hx_ty = rle(d, p, zero_r, xk);
    let concl = rle(d, p, a_ind, xk);

    let proof_body = ble_cases(
        d,
        cond,
        concl,
        &|d, heq| {
            let sel = bool_select_rat(d, cond, one_r, zero_r);
            let sel_eq_zero = select_rat_false(d, cond, one_r, zero_r, heq);
            let a_sel = rmul(d, a, sel);
            let a_zero = rmul(d, a, zero_r);
            let step1 = rcongr(d, sel, zero_r, sel_eq_zero, &|d, t| rmul(d, a, t));
            let mul_zero_step = d.lemma(p.mul_zero, &[a]);
            let a_sel_eq_zero = rtrans(d, a_sel, a_zero, zero_r, step1, mul_zero_step);
            let zero_eq_a_sel = rsymm(d, a_sel, zero_r, a_sel_eq_zero);
            rat_eq_rewrite(d, zero_r, a_sel, zero_eq_a_sel, hx, &|d, t| {
                rle(d, p, t, xk)
            })
        },
        &|d, heq| {
            let sel = bool_select_rat(d, cond, one_r, zero_r);
            let sel_eq_one = select_rat_true(d, cond, one_r, zero_r, heq);
            let a_sel = rmul(d, a, sel);
            let a_one = rmul(d, a, one_r);
            let step1 = rcongr(d, sel, one_r, sel_eq_one, &|d, t| rmul(d, a, t));
            let mul_one_step = d.lemma(p.mul_one, &[a]);
            let a_sel_eq_a = rtrans(d, a_sel, a_one, a, step1, mul_one_step);
            let a_eq_a_sel = rsymm(d, a_sel, a, a_sel_eq_a);
            let a_le_xk = d.lemma(p.le_of_ble_eq_true, &[a, xk, heq]);
            rat_eq_rewrite(d, a, a_sel, a_eq_a_sel, a_le_xk, &|d, t| rle(d, p, t, xk))
        },
    );

    let value = {
        let with_hx = d.lam_fv(hx_fv, hx_ty, proof_body);
        let with_k = d.lam_fv(k_fv, nat, with_hx);
        let with_x = d.lam_fv(x_fv, fn_ty, with_k);
        d.lam_fv(a_fv, carrier, with_x)
    };
    let ty = {
        let inner = d.arrow(hx_ty, concl);
        let with_k = d.pi_fv(k_fv, nat, inner);
        let with_x = d.pi_fv(x_fv, fn_ty, with_k);
        d.pi_fv(a_fv, carrier, with_x)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.indicator_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.markov_constructed : ∀ a X p n, IsDistribution p n → (∀ k, Lt k n →
/// le zero (X k)) → lt zero a → le (a * expectation (Rat.indicator a X) p n)
/// (expectation X p n)` — [`RatPrelude::markov_inequality`] with the
/// indicator SUPPLIED rather than hypothesised: [`declare_indicator_le`]
/// discharges the fourth hypothesis from exactly the `0 ≤ X k` this theorem
/// already carries, turning the conditional statement into an unconditional
/// one. **This is the headline this file exists for.**
fn declare_markov_constructed(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);
    let hx_fv = d.fresh_fvar();
    let hx = d.kernel().fvar(hx_fv);
    let ha_fv = d.fresh_fvar();
    let ha = d.kernel().fvar(ha_fv);

    let dist_ty = is_distribution(d, p, pf, n);
    let hx_ty = bounded_nonneg(d, p, x, n);
    let zero_r = rzero(d, p);
    let ha_ty = rlt(d, p, zero_r, a);

    let ind_fn = d.const_app(p.indicator, &[a, x]);

    let concl = {
        let eind = expectation(d, p, ind_fn, pf, n);
        let lhs = rmul(d, a, eind);
        let rhs = expectation(d, p, x, pf, n);
        rle(d, p, lhs, rhs)
    };

    let hind_proof = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let klt_fv = d.fresh_fvar();
        let klt = d.kernel().fvar(klt_fv);
        let klt_ty = d.lt(k, n);
        let hxk = d.apply(hx, &[k, klt]);
        let step = d.lemma(p.indicator_le, &[a, x, k, hxk]);
        let with_klt = d.lam_fv(klt_fv, klt_ty, step);
        d.lam_fv(k_fv, nat, with_klt)
    };

    let markov_result = d.lemma(
        p.markov_inequality,
        &[a, x, ind_fn, pf, n, hd, hx, ha, hind_proof],
    );

    let value = {
        let with_ha = d.lam_fv(ha_fv, ha_ty, markov_result);
        let with_hx = d.lam_fv(hx_fv, hx_ty, with_ha);
        let with_hd = d.lam_fv(hd_fv, dist_ty, with_hx);
        let with_n = d.lam_fv(n_fv, nat, with_hd);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_x = d.lam_fv(x_fv, fn_ty, with_pf);
        d.lam_fv(a_fv, carrier, with_x)
    };
    let ty = {
        let with_ha = d.arrow(ha_ty, concl);
        let with_hx = d.arrow(hx_ty, with_ha);
        let with_hd = d.arrow(dist_ty, with_hx);
        let with_n = d.pi_fv(n_fv, nat, with_hd);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        let with_x = d.pi_fv(x_fv, fn_ty, with_pf);
        d.pi_fv(a_fv, carrier, with_x)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.markov_constructed,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.chebyshev_inequality : ∀ a X p n, IsDistribution p n → lt zero a →
/// le ((a*a) * expectation (Rat.indicator (a*a) (fun k => (X k − expectation
/// X p n) * (X k − expectation X p n))) p n) (variance X p n)` —
/// [`declare_markov_constructed`] applied to the squared deviation `(X −
/// E[X])²` at threshold `a²`, in the multiplied-through form that needs no
/// `Rat.inv`. The classical statement divides through by `a²` to read `P(|X
/// − E[X]| ≥ a) ≤ Var[X]/a²`; this is the same content before that division.
///
/// The conclusion's right side is stated as `variance X p n` rather than the
/// `expectation` [`declare_markov_constructed`] actually produces: the two
/// are definitionally equal (`Rat.variance` unfolds to exactly this
/// `expectation` application, over the same `mu`), so the kernel's defeq
/// check closes the gap — no `variance_eq` rewrite needed.
fn declare_chebyshev_inequality(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);
    let ha_fv = d.fresh_fvar();
    let ha = d.kernel().fvar(ha_fv);

    let dist_ty = is_distribution(d, p, pf, n);
    let zero_r = rzero(d, p);
    let ha_ty = rlt(d, p, zero_r, a);

    let mu = expectation(d, p, x, pf, n);
    let y = variance_summand(d, p, x, mu);
    let a_sq = rmul(d, a, a);
    let ind_y = d.const_app(p.indicator, &[a_sq, y]);

    let concl = {
        let ey = expectation(d, p, ind_y, pf, n);
        let lhs = rmul(d, a_sq, ey);
        let variance_xpn = variance(d, p, x, pf, n);
        rle(d, p, lhs, variance_xpn)
    };

    let hy_nonneg = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let klt_fv = d.fresh_fvar();
        let klt_ty = d.lt(k, n);
        let xk = d.apply(x, &[k]);
        let gap = rsub(d, p, xk, mu);
        let sqnn = d.lemma(p.sq_nonneg, &[gap]);
        let with_klt = d.lam_fv(klt_fv, klt_ty, sqnn);
        d.lam_fv(k_fv, nat, with_klt)
    };
    let ha_sq = d.lemma(p.mul_pos, &[a, a, ha, ha]);

    let markov_result = d.lemma(
        p.markov_constructed,
        &[a_sq, y, pf, n, hd, hy_nonneg, ha_sq],
    );

    let value = {
        let with_ha = d.lam_fv(ha_fv, ha_ty, markov_result);
        let with_hd = d.lam_fv(hd_fv, dist_ty, with_ha);
        let with_n = d.lam_fv(n_fv, nat, with_hd);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_x = d.lam_fv(x_fv, fn_ty, with_pf);
        d.lam_fv(a_fv, carrier, with_x)
    };
    let ty = {
        let with_ha = d.arrow(ha_ty, concl);
        let with_hd = d.arrow(dist_ty, with_ha);
        let with_n = d.pi_fv(n_fv, nat, with_hd);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        let with_x = d.pi_fv(x_fv, fn_ty, with_pf);
        d.pi_fv(a_fv, carrier, with_x)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.chebyshev_inequality,
        uparams: vec![],
        ty,
        value,
    })
}

// --- covariance, and the variance of a sum ----------------------------------
//
// **There is no independence predicate anywhere in this development, and
// none is introduced here.** Independence is a statement about a JOINT
// distribution over a product space, and this development has only a single
// `p` over one index range — there is no product space, no joint law, and no
// way to state `P(X=x ∧ Y=y) = P(X=x)·P(Y=y)`. `Cov[X,Y] ~ 0`
// (uncorrelatedness, [`declare_variance_add_of_uncorrelated`]) is the honest
// hypothesis this section uses instead, and it is strictly weaker than
// independence — the same discipline `dist_sq_double_sum_bound` follows by
// not being called `triangle_inequality`.

/// `Rat.covariance X Y p n`, i.e. `d.const_app(p.covariance, &[x, y, pf, n])`.
fn covariance(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    x: ExprId,
    y: ExprId,
    pf: ExprId,
    n: ExprId,
) -> ExprId {
    d.const_app(p.covariance, &[x, y, pf, n])
}

/// Admit `Rat.covariance : (Nat → Rat) → (Nat → Rat) → (Nat → Rat) → Nat →
/// Rat := fun X Y p n => sub (expectation (fun k => X k * Y k) p n) (mul
/// (expectation X p n) (expectation Y p n))` — `Cov[X,Y] := E[X·Y] −
/// E[X]·E[Y]`.
fn declare_covariance(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let xy = weighted(d, x, y);
    let e_xy = expectation(d, p, xy, pf, n);
    let ex = expectation(d, p, x, pf, n);
    let ey = expectation(d, p, y, pf, n);
    let exey = rmul(d, ex, ey);
    let body = rsub(d, p, e_xy, exey);

    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_y = d.lam_fv(y_fv, fn_ty, with_pf);
        d.lam_fv(x_fv, fn_ty, with_y)
    };
    let ty = {
        let over_n = d.arrow(nat, carrier);
        let over_pf = d.arrow(fn_ty, over_n);
        let over_y = d.arrow(fn_ty, over_pf);
        d.arrow(fn_ty, over_y)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.covariance,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(COVARIANCE_HEIGHT),
    })
}

/// `(a+b)*(a+b) = a*a + (a*b + (a*b + b*b))`, over generic `a`, `b : Rat` —
/// the additive twin of [`sub_sq_expand`], using two copies of `a*b` rather
/// than a literal `2*(a*b)` for the same reason `sub_sq_expand` keeps two
/// copies of `neg b * a`. Returned as `(start, target, proof)`. Private:
/// [`declare_variance_add_eq`] uses it for both the squared-deviation-sum
/// summand and the squared sum-of-means.
fn add_sq_expand(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    a: ExprId,
    b: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let w = radd(d, a, b);
    let start = rmul(d, w, w);

    // (a+b)*w = a*w + b*w                                     [right_distrib]
    let aw = rmul(d, a, w);
    let bw = rmul(d, b, w);
    let mid1 = radd(d, aw, bw);
    let step1 = d.lemma(p.right_distrib, &[a, b, w]);

    // a*w = a*a + a*b                                          [left_distrib]
    let aa = rmul(d, a, a);
    let ab = rmul(d, a, b);
    let aw_expanded = radd(d, aa, ab);
    let step2a = d.lemma(p.left_distrib, &[a, a, b]);
    let mid2 = radd(d, aw_expanded, bw);
    let h_mid2 = rcongr(d, aw, aw_expanded, step2a, &|d, t| radd(d, t, bw));

    // b*w = b*a + b*b                                          [left_distrib]
    let ba = rmul(d, b, a);
    let bb = rmul(d, b, b);
    let bw_expanded = radd(d, ba, bb);
    let step2b = d.lemma(p.left_distrib, &[b, a, b]);
    let mid3 = radd(d, aw_expanded, bw_expanded);
    let h_mid3 = rcongr(d, bw, bw_expanded, step2b, &|d, t| radd(d, aw_expanded, t));

    // b*a = a*b                                                     [mul_comm]
    let ab_bb = radd(d, ab, bb);
    let mid4 = radd(d, aw_expanded, ab_bb);
    let comm1 = d.lemma(p.mul_comm, &[b, a]); // Eq(ba, ab)
    let h_mid4 = rcongr(d, ba, ab, comm1, &|d, t| {
        let inner = radd(d, t, bb);
        radd(d, aw_expanded, inner)
    });

    // (aa+ab)+(ab+bb) = aa+(ab+(ab+bb))                            [add_assoc]
    let ab_ab_bb = radd(d, ab, ab_bb);
    let target = radd(d, aa, ab_ab_bb);
    let step_assoc = d.lemma(p.add_assoc, &[aa, ab, ab_bb]);

    let (_e, proof) = rchain(
        d,
        start,
        &[
            (mid1, step1),
            (mid2, h_mid2),
            (mid3, h_mid3),
            (mid4, h_mid4),
            (target, step_assoc),
        ],
    );
    (start, target, proof)
}

/// `Rat.variance_add_eq : ∀ X Y p n, IsDistribution p n →
/// variance (fun k => X k + Y k) p n =
/// add (variance X p n) (add (covariance X Y p n) (add (covariance X Y p n)
/// (variance Y p n)))` — `Var[X+Y] = Var[X] + (Cov[X,Y] + (Cov[X,Y] +
/// Var[Y]))`, the two copies of `Cov[X,Y]` standing in for the classical
/// `2·Cov[X,Y]` (see [`add_sq_expand`]). **The headline: variance of a sum,
/// with the cross term named rather than assumed away.**
///
/// [`RatPrelude::variance_eq`] applied to `X+Y`, `X`, and `Y` separately turns
/// the goal into pure `expectation`/mean algebra; [`add_sq_expand`] expands
/// the pointwise squared deviation `(Xk+Yk)*(Xk+Yk)` and (reused) the squared
/// sum of means; [`RatPrelude::expectation_add`] (nested twice) splits the
/// resulting three-term sum of expectations; [`RatPrelude::sub_add_add`]
/// (three times) regroups the difference of two four-term sums into a sum of
/// four differences, three of which are exactly `Var[X]`, `Var[Y]` and (twice)
/// `Rat.covariance`'s own defining formula.
fn declare_variance_add_eq(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);

    let dist_ty = is_distribution(d, p, pf, n);
    let xy_sum = combined(d, x, y);
    let variance_sum = variance(d, p, xy_sum, pf, n);
    let variance_x = variance(d, p, x, pf, n);
    let variance_y = variance(d, p, y, pf, n);
    let cov_expr = covariance(d, p, x, y, pf, n);
    let cov_plus_vary = radd(d, cov_expr, variance_y);
    let inner_rhs = radd(d, cov_expr, cov_plus_vary);
    let rhs = radd(d, variance_x, inner_rhs);
    let concl = req(d, variance_sum, rhs);

    // veq_xy : variance_sum = sub(e_sumsum, mu_sum*mu_sum)
    let veq_xy = d.lemma(p.variance_eq, &[xy_sum, pf, n, hd]);
    let xy_sum_sq_fn = weighted(d, xy_sum, xy_sum);
    let e_sumsum = expectation(d, p, xy_sum_sq_fn, pf, n);
    let mu_sum = expectation(d, p, xy_sum, pf, n);
    let mu_sum_sq = rmul(d, mu_sum, mu_sum);

    // veq_x, veq_y
    let veq_x = d.lemma(p.variance_eq, &[x, pf, n, hd]);
    let xx = weighted(d, x, x);
    let e_xx = expectation(d, p, xx, pf, n);
    let mu_x = expectation(d, p, x, pf, n);
    let mu_x_sq = rmul(d, mu_x, mu_x);

    let veq_y = d.lemma(p.variance_eq, &[y, pf, n, hd]);
    let yy = weighted(d, y, y);
    let e_yy = expectation(d, p, yy, pf, n);
    let mu_y = expectation(d, p, y, pf, n);
    let mu_y_sq = rmul(d, mu_y, mu_y);

    let xy_fn = weighted(d, x, y);
    let e_xy = expectation(d, p, xy_fn, pf, n);
    let mu_x_mu_y = rmul(d, mu_x, mu_y);

    // --- pointwise: (Xk+Yk)*(Xk+Yk) = XkXk + (XkYk + (XkYk + YkYk))
    let rest2_fn = combined(d, xy_fn, yy);
    let rest1_fn = combined(d, xy_fn, rest2_fn);
    let abc_fn = combined(d, xx, rest1_fn);

    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let xk = d.apply(x, &[k]);
        let yk = d.apply(y, &[k]);
        let (start_k, target_k, proof_k) = add_sq_expand(d, p, xk, yk);
        let pk = d.apply(pf, &[k]);
        let lifted = rcongr(d, start_k, target_k, proof_k, &|d, t| rmul(d, t, pk));
        d.lam_fv(k_fv, nat, lifted)
    };
    let xy_sum_sq_weighted = weighted(d, xy_sum_sq_fn, pf);
    let abc_weighted = weighted(d, abc_fn, pf);
    let congr_step = d.lemma(
        p.sum_range_congr,
        &[xy_sum_sq_weighted, abc_weighted, n, pointwise],
    );
    // congr_step : Eq(sumRange(xy_sum_sq_weighted,n), sumRange(abc_weighted,n))
    //   ~ Eq(e_sumsum, expectation(abc_fn,pf,n))                      [defeq]

    let e_abc = expectation(d, p, abc_fn, pf, n);
    let e_rest1 = expectation(d, p, rest1_fn, pf, n);
    let e_rest2 = expectation(d, p, rest2_fn, pf, n);

    let eq1 = d.lemma(p.expectation_add, &[xx, rest1_fn, pf, n]);
    // eq1 : Eq(e_abc, e_xx+e_rest1)
    let eq2 = d.lemma(p.expectation_add, &[xy_fn, rest2_fn, pf, n]);
    // eq2 : Eq(e_rest1, e_xy+e_rest2)
    let eq3 = d.lemma(p.expectation_add, &[xy_fn, yy, pf, n]);
    // eq3 : Eq(e_rest2, e_xy+e_yy)

    let after_eq1 = radd(d, e_xx, e_rest1);
    let step_rest2 = radd(d, e_xy, e_rest2);
    let lift2 = rcongr(d, e_rest1, step_rest2, eq2, &|d, t| radd(d, e_xx, t));
    let after_lift2 = radd(d, e_xx, step_rest2);
    let e_xy_e_yy = radd(d, e_xy, e_yy);
    let lift3 = rcongr(d, e_rest2, e_xy_e_yy, eq3, &|d, t| {
        let inner = radd(d, e_xy, t);
        radd(d, e_xx, inner)
    });
    let e_xy_e_xy_e_yy = radd(d, e_xy, e_xy_e_yy);
    let after_lift3 = radd(d, e_xx, e_xy_e_xy_e_yy);

    let (_e, e_step_chain) = rchain(
        d,
        e_abc,
        &[(after_eq1, eq1), (after_lift2, lift2), (after_lift3, lift3)],
    );
    let final_estep = rtrans(d, e_sumsum, e_abc, after_lift3, congr_step, e_step_chain);
    // final_estep : Eq(e_sumsum, after_lift3)  where after_lift3 = e_xx+(e_xy+(e_xy+e_yy))

    // --- the squared mean: mu_sum*mu_sum = mu_x² + (mu_x·mu_y + (mu_x·mu_y + mu_y²))
    let eq_mu_sum = d.lemma(p.expectation_add, &[x, y, pf, n]);
    // eq_mu_sum : Eq(mu_sum, mu_x+mu_y)
    let mu_x_plus_mu_y = radd(d, mu_x, mu_y);
    let start2 = rmul(d, mu_x_plus_mu_y, mu_x_plus_mu_y);
    let congr_musq = rcongr(d, mu_sum, mu_x_plus_mu_y, eq_mu_sum, &|d, t| rmul(d, t, t));
    let (_, target2, proof2) = add_sq_expand(d, p, mu_x, mu_y);
    let (_e, musq_chain) = rchain(d, mu_sum_sq, &[(start2, congr_musq), (target2, proof2)]);
    let final_musqstep = musq_chain;
    // final_musqstep : Eq(mu_sum_sq, target2)  where target2 = mu_x_sq+(mu_x_mu_y+(mu_x_mu_y+mu_y_sq))

    // --- combine into sub(A,B), A := after_lift3, B := target2
    let a_term = after_lift3;
    let b_term = target2;
    let d1 = rcongr(d, e_sumsum, a_term, final_estep, &|d, t| {
        rsub(d, p, t, mu_sum_sq)
    });
    let after_d1 = rsub(d, p, a_term, mu_sum_sq);
    let d2 = rcongr(d, mu_sum_sq, b_term, final_musqstep, &|d, t| {
        rsub(d, p, a_term, t)
    });
    let after_d2 = rsub(d, p, a_term, b_term);

    // --- regroup sub(A,B) via sub_add_add, three times
    let q_r = radd(d, e_xy, e_yy);
    let qq_r = radd(d, e_xy, q_r);
    let q_r_means = radd(d, mu_x_mu_y, mu_y_sq);
    let qq_r_means = radd(d, mu_x_mu_y, q_r_means);
    let s1 = d.lemma(p.sub_add_add, &[e_xx, qq_r, mu_x_sq, qq_r_means]);
    // s1 : Eq(sub(A,B), sub(e_xx,mu_x_sq) + sub(qq_r,qq_r_means))
    let sx = rsub(d, p, e_xx, mu_x_sq);
    let qqr_sub = rsub(d, p, qq_r, qq_r_means);
    let after_s1 = radd(d, sx, qqr_sub);

    let s2 = d.lemma(p.sub_add_add, &[e_xy, q_r, mu_x_mu_y, q_r_means]);
    // s2 : Eq(qqr_sub, sub(e_xy,mu_x_mu_y) + sub(q_r,q_r_means))
    let sxy = rsub(d, p, e_xy, mu_x_mu_y);
    let qr_sub = rsub(d, p, q_r, q_r_means);
    let sxy_qr_sub = radd(d, sxy, qr_sub);
    let lift_s2 = rcongr(d, qqr_sub, sxy_qr_sub, s2, &|d, t| radd(d, sx, t));
    let after_s2 = radd(d, sx, sxy_qr_sub);

    let s3 = d.lemma(p.sub_add_add, &[e_xy, e_yy, mu_x_mu_y, mu_y_sq]);
    // s3 : Eq(qr_sub, sub(e_xy,mu_x_mu_y) + sub(e_yy,mu_y_sq)) = Eq(qr_sub, sxy+sy)
    let sy = rsub(d, p, e_yy, mu_y_sq);
    let sxy_sy = radd(d, sxy, sy);
    let lift_s3 = rcongr(d, qr_sub, sxy_sy, s3, &|d, t| {
        let inner = radd(d, sxy, t);
        radd(d, sx, inner)
    });
    let sxy_sxy_sy = radd(d, sxy, sxy_sy);
    let after_s3 = radd(d, sx, sxy_sxy_sy);

    // --- rewrite sx -> variance_x, sy -> variance_y (sxy is defeq to cov_expr)
    let veq_x_rev = rsymm(d, variance_x, sx, veq_x); // Eq(sx, variance_x)
    let after_d3 = radd(d, variance_x, sxy_sxy_sy);
    let d3 = rcongr(d, sx, variance_x, veq_x_rev, &|d, t| radd(d, t, sxy_sxy_sy));

    let veq_y_rev = rsymm(d, variance_y, sy, veq_y); // Eq(sy, variance_y)
    let sxy_variance_y = radd(d, sxy, variance_y);
    let sxy_sxy_variance_y = radd(d, sxy, sxy_variance_y);
    let after_d4 = radd(d, variance_x, sxy_sxy_variance_y);
    let d4 = rcongr(d, sy, variance_y, veq_y_rev, &|d, t| {
        let inner = radd(d, sxy, t);
        let mid = radd(d, sxy, inner);
        radd(d, variance_x, mid)
    });

    let (_e, tail_from_after_d2) = rchain(
        d,
        after_d2,
        &[
            (after_s1, s1),
            (after_s2, lift_s2),
            (after_s3, lift_s3),
            (after_d3, d3),
            (after_d4, d4),
        ],
    );
    let sub_e_sumsum_mu_sum_sq = rsub(d, p, e_sumsum, mu_sum_sq);
    let (_e, head_to_after_d2) =
        rchain(d, sub_e_sumsum_mu_sum_sq, &[(after_d1, d1), (after_d2, d2)]);
    let sub_chain = rtrans(
        d,
        sub_e_sumsum_mu_sum_sq,
        after_d2,
        after_d4,
        head_to_after_d2,
        tail_from_after_d2,
    );

    let final_proof = rtrans(
        d,
        variance_sum,
        sub_e_sumsum_mu_sum_sq,
        after_d4,
        veq_xy,
        sub_chain,
    );

    let value = {
        let with_hd = d.lam_fv(hd_fv, dist_ty, final_proof);
        let with_n = d.lam_fv(n_fv, nat, with_hd);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_y = d.lam_fv(y_fv, fn_ty, with_pf);
        d.lam_fv(x_fv, fn_ty, with_y)
    };
    let ty = {
        let with_hd = d.arrow(dist_ty, concl);
        let with_n = d.pi_fv(n_fv, nat, with_hd);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        let with_y = d.pi_fv(y_fv, fn_ty, with_pf);
        d.pi_fv(x_fv, fn_ty, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.variance_add_eq,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.variance_add_of_uncorrelated : ∀ X Y p n, IsDistribution p n →
/// covariance X Y p n = zero →
/// variance (fun k => X k + Y k) p n = add (variance X p n) (variance Y p n)`
/// — [`RatPrelude::variance_add_eq`] specialised to a vanishing cross term.
/// **Uncorrelatedness, not independence** — see this module's header doc and
/// [`RatPrelude::covariance`]'s.
fn declare_variance_add_of_uncorrelated(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);
    let hcov_fv = d.fresh_fvar();
    let hcov = d.kernel().fvar(hcov_fv);

    let dist_ty = is_distribution(d, p, pf, n);
    let cov_expr = covariance(d, p, x, y, pf, n);
    let zero_r = rzero(d, p);
    let hcov_ty = req(d, cov_expr, zero_r);

    let xy_sum = combined(d, x, y);
    let variance_sum = variance(d, p, xy_sum, pf, n);
    let variance_x = variance(d, p, x, pf, n);
    let variance_y = variance(d, p, y, pf, n);
    let rhs = radd(d, variance_x, variance_y);
    let concl = req(d, variance_sum, rhs);

    let headline = d.lemma(p.variance_add_eq, &[x, y, pf, n, hd]);
    // headline : Eq(variance_sum, variance_x + (cov_expr + (cov_expr + variance_y)))

    let cov_plus_vary = radd(d, cov_expr, variance_y);
    let inner0 = radd(d, cov_expr, cov_plus_vary);
    let headline_rhs = radd(d, variance_x, inner0);

    let step_a = rcongr(d, cov_expr, zero_r, hcov, &|d, t| {
        let inner = radd(d, cov_expr, variance_y);
        let mid = radd(d, t, inner);
        radd(d, variance_x, mid)
    });
    let zero_plus_covvary = radd(d, zero_r, cov_plus_vary);
    let after_a = radd(d, variance_x, zero_plus_covvary);

    let step_b = rcongr(d, cov_expr, zero_r, hcov, &|d, t| {
        let inner = radd(d, t, variance_y);
        let mid = radd(d, zero_r, inner);
        radd(d, variance_x, mid)
    });
    let zero_plus_vary = radd(d, zero_r, variance_y);
    let zero_plus_zero_plus_vary = radd(d, zero_r, zero_plus_vary);
    let after_b = radd(d, variance_x, zero_plus_zero_plus_vary);

    let z_inner = d.lemma(p.zero_add, &[variance_y]); // Eq(zero+variance_y, variance_y)
    let step_c = rcongr(d, zero_plus_vary, variance_y, z_inner, &|d, t| {
        let inner = radd(d, zero_r, t);
        radd(d, variance_x, inner)
    });
    let after_c = radd(d, variance_x, zero_plus_vary);

    let z_outer = d.lemma(p.zero_add, &[variance_y]); // Eq(zero+variance_y, variance_y)
    let step_d = rcongr(d, zero_plus_vary, variance_y, z_outer, &|d, t| {
        radd(d, variance_x, t)
    });

    let (_e, simplify_chain) = rchain(
        d,
        headline_rhs,
        &[
            (after_a, step_a),
            (after_b, step_b),
            (after_c, step_c),
            (rhs, step_d),
        ],
    );

    let final_proof = rtrans(d, variance_sum, headline_rhs, rhs, headline, simplify_chain);

    let value = {
        let with_hcov = d.lam_fv(hcov_fv, hcov_ty, final_proof);
        let with_hd = d.lam_fv(hd_fv, dist_ty, with_hcov);
        let with_n = d.lam_fv(n_fv, nat, with_hd);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_y = d.lam_fv(y_fv, fn_ty, with_pf);
        d.lam_fv(x_fv, fn_ty, with_y)
    };
    let ty = {
        let with_hcov = d.arrow(hcov_ty, concl);
        let with_hd = d.arrow(dist_ty, with_hcov);
        let with_n = d.pi_fv(n_fv, nat, with_hd);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        let with_y = d.pi_fv(y_fv, fn_ty, with_pf);
        d.pi_fv(x_fv, fn_ty, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.variance_add_of_uncorrelated,
        uparams: vec![],
        ty,
        value,
    })
}

// --- the finite weak law of large numbers scaffolding -----------------------
//
// `Rat.variance_add_of_uncorrelated` gives the two-variable case. Every
// multi-variable statement — the finite weak law included — needs linearity
// of expectation over a whole FAMILY of variables, which
// `Rat.expectation_add` alone does not give (it is the `m = 2` case, stated
// directly rather than by induction). `Rat.covariance_add_right` and
// `Rat.sumVars`/`Rat.expectation_sumVars` below are that scaffolding.

/// `Rat.covariance_add_right : ∀ X Y Z p n,
/// covariance X (fun k => Y k + Z k) p n = add (covariance X Y p n)
/// (covariance X Z p n)` — bilinearity of covariance in its second argument.
///
/// Purely algebraic, no `IsDistribution` hypothesis needed — matching
/// [`RatPrelude::expectation_add`]'s own unconditional linearity, not
/// [`declare_variance_add_eq`]'s (which needs it only for `variance_eq`'s own
/// `expectation_const` step, a step this proof never takes): `Cov[X,Y+Z] =
/// E[X(Y+Z)] − E[X]E[Y+Z] = (E[XY]+E[XZ]) − (E[X]E[Y]+E[X]E[Z]) =
/// Cov[X,Y]+Cov[X,Z]`, via [`RatPrelude::left_distrib`] twice (once on the
/// summand, once on the product of means) and [`RatPrelude::sub_add_add`]
/// once to regroup the difference of two two-term sums.
fn declare_covariance_add_right(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let yz = combined(d, y, z);
    let cov_x_yz = covariance(d, p, x, yz, pf, n);
    let cov_x_y = covariance(d, p, x, y, pf, n);
    let cov_x_z = covariance(d, p, x, z, pf, n);
    let rhs = radd(d, cov_x_y, cov_x_z);
    let concl = req(d, cov_x_yz, rhs);

    // --- Step A: expectation(weighted(x, yz), pf, n) = e_xy + e_xz
    let xy = weighted(d, x, y);
    let xz = weighted(d, x, z);
    let e_xy = expectation(d, p, xy, pf, n);
    let e_xz = expectation(d, p, xz, pf, n);

    let x_yz_summand = weighted(d, x, yz); // fun k => Xk*(Yk+Zk)
    let xy_xz_combined = combined(d, xy, xz); // fun k => Xk*Yk + Xk*Zk
    // `expectation` weights its argument by `pf` internally, so the
    // pointwise identity has to be proved at THAT level (`weighted(_,pf)`),
    // not at the raw random-variable level — otherwise `sum_range_congr`
    // proves an equation missing the `pf` factor entirely.
    let x_yz_weighted = weighted(d, x_yz_summand, pf); // fun k => (Xk*(Yk+Zk))*Pk
    let xy_xz_weighted = weighted(d, xy_xz_combined, pf); // fun k => (Xk*Yk+Xk*Zk)*Pk
    let pointwise_a = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let xk = d.apply(x, &[k]);
        let yk = d.apply(y, &[k]);
        let zk = d.apply(z, &[k]);
        let pk = d.apply(pf, &[k]);
        let yk_zk = radd(d, yk, zk);
        let xk_yz_k = rmul(d, xk, yk_zk);
        let xk_yk = rmul(d, xk, yk);
        let xk_zk = rmul(d, xk, zk);
        let xkyk_xkzk = radd(d, xk_yk, xk_zk);
        let step = d.lemma(p.left_distrib, &[xk, yk, zk]);
        // step : Eq(Xk*(Yk+Zk), Xk*Yk + Xk*Zk)
        let lifted = rcongr(d, xk_yz_k, xkyk_xkzk, step, &|d, t| rmul(d, t, pk));
        // lifted : Eq((Xk*(Yk+Zk))*Pk, (Xk*Yk+Xk*Zk)*Pk)
        d.lam_fv(k_fv, nat, lifted)
    };
    let congr_a = d.lemma(
        p.sum_range_congr,
        &[x_yz_weighted, xy_xz_weighted, n, pointwise_a],
    );
    // congr_a : Eq(sumRange(x_yz_weighted,n), sumRange(xy_xz_weighted,n))
    //   ~ Eq(expectation(x_yz_summand,pf,n), expectation(xy_xz_combined,pf,n)) [defeq]

    let eq_add_a = d.lemma(p.expectation_add, &[xy, xz, pf, n]);
    // eq_add_a : Eq(expectation(xy_xz_combined,pf,n), e_xy + e_xz)

    let sum_x_yz_weighted = rsum_range(d, p, x_yz_weighted, n);
    let sum_xy_xz_weighted = rsum_range(d, p, xy_xz_weighted, n);
    let e_xy_e_xz = radd(d, e_xy, e_xz);
    let (_e, a_chain) = rchain(
        d,
        sum_x_yz_weighted,
        &[(sum_xy_xz_weighted, congr_a), (e_xy_e_xz, eq_add_a)],
    );
    // a_chain : Eq(sum_x_yz_weighted, e_xy_e_xz)
    //   ~ Eq(e_x_yz, e_xy_e_xz)                                          [defeq,
    //   both at the boundary (sum_xy_xz_weighted ~ expectation(xy_xz_combined,pf,n),
    //   the LHS `eq_add_a` actually carries) and at the chain's own start]
    let e_x_yz = expectation(d, p, x_yz_summand, pf, n);

    // --- Step B: ex * e_yz = ex*ey + ex*ez
    let ex = expectation(d, p, x, pf, n);
    let ey = expectation(d, p, y, pf, n);
    let ez = expectation(d, p, z, pf, n);
    let e_yz = expectation(d, p, yz, pf, n);
    let ex_e_yz = rmul(d, ex, e_yz);

    let eq_add_b = d.lemma(p.expectation_add, &[y, z, pf, n]);
    // eq_add_b : Eq(e_yz, ey+ez)
    let ey_ez = radd(d, ey, ez);
    let step_b1 = rcongr(d, e_yz, ey_ez, eq_add_b, &|d, t| rmul(d, ex, t));
    // step_b1 : Eq(ex*e_yz, ex*(ey+ez))
    let ex_ey_ez = rmul(d, ex, ey_ez);

    let ex_ey = rmul(d, ex, ey);
    let ex_ez = rmul(d, ex, ez);
    let ex_ey_plus_ex_ez = radd(d, ex_ey, ex_ez);
    let step_b2 = d.lemma(p.left_distrib, &[ex, ey, ez]);
    // step_b2 : Eq(ex*(ey+ez), ex*ey + ex*ez)

    let (_e, b_chain) = rchain(
        d,
        ex_e_yz,
        &[(ex_ey_ez, step_b1), (ex_ey_plus_ex_ez, step_b2)],
    );
    // b_chain : Eq(ex_e_yz, ex_ey_plus_ex_ez)

    // --- Step C: combine sub(e_x_yz, ex_e_yz) into sxy + sxz
    let d1 = rcongr(d, e_x_yz, e_xy_e_xz, a_chain, &|d, t| {
        rsub(d, p, t, ex_e_yz)
    });
    let after_d1 = rsub(d, p, e_xy_e_xz, ex_e_yz);
    let d2 = rcongr(d, ex_e_yz, ex_ey_plus_ex_ez, b_chain, &|d, t| {
        rsub(d, p, e_xy_e_xz, t)
    });
    let after_d2 = rsub(d, p, e_xy_e_xz, ex_ey_plus_ex_ez);

    let s1 = d.lemma(p.sub_add_add, &[e_xy, e_xz, ex_ey, ex_ez]);
    // s1 : Eq(sub(e_xy+e_xz, ex_ey+ex_ez), sub(e_xy,ex_ey) + sub(e_xz,ex_ez))
    let sxy = rsub(d, p, e_xy, ex_ey);
    let sxz = rsub(d, p, e_xz, ex_ez);
    let target = radd(d, sxy, sxz);

    let sub_start = rsub(d, p, e_x_yz, ex_e_yz);
    let (_e, final_chain) = rchain(
        d,
        sub_start,
        &[(after_d1, d1), (after_d2, d2), (target, s1)],
    );
    // final_chain : Eq(sub_start, target)
    //   ~ Eq(cov_x_yz, cov_x_y + cov_x_z)                                [defeq]

    let value = {
        let with_n = d.lam_fv(n_fv, nat, final_chain);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_z = d.lam_fv(z_fv, fn_ty, with_pf);
        let with_y = d.lam_fv(y_fv, fn_ty, with_z);
        d.lam_fv(x_fv, fn_ty, with_y)
    };
    let ty = {
        let with_n = d.pi_fv(n_fv, nat, concl);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        let with_z = d.pi_fv(z_fv, fn_ty, with_pf);
        let with_y = d.pi_fv(y_fv, fn_ty, with_z);
        d.pi_fv(x_fv, fn_ty, with_y)
    };
    d.declare_theorem(p.covariance_add_right, ty, value)
}

/// `Rat.sumVars X m k`, i.e. the partial application `d.const_app(p.sum_vars,
/// &[x, m])` applied to `k` — the pointwise sum of `m` variables at outcome
/// `k`.
fn sum_vars_fn(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId, m: ExprId) -> ExprId {
    d.const_app(p.sum_vars, &[x, m])
}

/// Admit `Rat.sumVars : (Nat → Nat → Rat) → Nat → Nat → Rat := fun X m k =>
/// sumRange (fun j => X j k) m` — the pointwise sum of `m` variables `X 0, X
/// 1, …, X (m-1)`, each a `Nat → Rat` sequence over the same outcome index
/// `k`.
fn declare_sum_vars(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let nat_fn_ty = d.arrow(nat, carrier);
    let x_ty = d.arrow(nat, nat_fn_ty);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let inner_fn = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let xj = d.apply(x, &[j]);
        let xjk = d.apply(xj, &[k]);
        d.lam_fv(j_fv, nat, xjk)
    };
    let body = rsum_range(d, p, inner_fn, m);
    let value = {
        let with_k = d.lam_fv(k_fv, nat, body);
        let with_m = d.lam_fv(m_fv, nat, with_k);
        d.lam_fv(x_fv, x_ty, with_m)
    };
    let ty = {
        let over_k = d.arrow(nat, carrier);
        let over_m = d.arrow(nat, over_k);
        d.arrow(x_ty, over_m)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.sum_vars,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(SUM_VARS_HEIGHT),
    })
}

/// `Rat.expectation_sumVars : ∀ X p n m,
/// expectation (sumVars X m) p n = sumRange (fun j => expectation (X j) p n) m`
/// — linearity of expectation over a FAMILY of variables, by induction on `m`
/// from [`RatPrelude::expectation_add`].
///
/// Base case (`m = 0`): both sides are `zero`, but not by `Eq.refl` alone —
/// `sumVars X 0 k` ι-reduces to `zero` (under the `k`-binder, since
/// `sumRange`'s zero branch does not depend on the summand), so `expectation
/// (sumVars X 0) p n` is definitionally `expectation (fun _ => zero) p n =
/// sumRange (fun k => zero * p k) n` — a genuine sum of (pointwise-zero, but
/// not syntactically zero) terms, closed by `sumRange_congr` against
/// `rat_zero_mul` pointwise, [`sum_range_const`] at `c = zero`, and
/// `mul_zero`.
///
/// Successor case: `sumVars X (succ m) k` ι-reduces (again under the
/// `k`-binder) to `sumVars X m k + X m k`, so `expectation (sumVars X (succ
/// m)) p n` is definitionally `expectation (fun k => sumVars X m k + X m k)
/// p n`; [`RatPrelude::expectation_add`] splits it, the inductive hypothesis
/// rewrites the first summand, and the result is definitionally the target
/// `sumRange (fun j => expectation (X j) p n) m + expectation (X m) p n =
/// sumRange (…) (succ m)` via `sumRange_succ`.
fn declare_expectation_sum_vars(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);
    let nat_fn_ty = d.arrow(nat, carrier);
    let x_ty = d.arrow(nat, nat_fn_ty);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let exp_of_x = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let xj = d.apply(x, &[j]);
        let e_xj = expectation(d, p, xj, pf, n);
        d.lam_fv(j_fv, nat, e_xj)
    };

    let motive = |d: &mut IntDev<'_>, bound: ExprId| -> ExprId {
        let sv = sum_vars_fn(d, p, x, bound);
        let lhs = expectation(d, p, sv, pf, n);
        let rhs = rsum_range(d, p, exp_of_x, bound);
        req(d, lhs, rhs)
    };
    let stmt = motive(d, m);

    let proof = d.induct(
        &motive,
        &|d| {
            // Base: expectation(const_fn zero, pf, n) = zero, via
            // sumRange_congr (rat_zero_mul pointwise) + sum_range_const + mul_zero.
            let zero_r = rzero(d, p);
            let const_zero = const_fn(d, zero_r);
            let weighted_zero = weighted(d, const_zero, pf);
            let pointwise_zero = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let pk = d.apply(pf, &[k]);
                let step = rat_zero_mul(d, p, pk);
                d.lam_fv(k_fv, nat, step)
            };
            let congr1 = d.lemma(
                p.sum_range_congr,
                &[weighted_zero, const_zero, n, pointwise_zero],
            );
            let (_stmt_sc, proof_sc) = sum_range_const(d, p, zero_r, n);
            let n_as_rat = nat_as_rat(d, p, n);
            let n_zero = rmul(d, n_as_rat, zero_r);
            let mul_zero_step = d.lemma(p.mul_zero, &[n_as_rat]);
            let sum_weighted_zero = rsum_range(d, p, weighted_zero, n);
            let sum_const_zero = rsum_range(d, p, const_zero, n);
            let (_e, chain) = rchain(
                d,
                sum_weighted_zero,
                &[
                    (sum_const_zero, congr1),
                    (n_zero, proof_sc),
                    (zero_r, mul_zero_step),
                ],
            );
            chain
        },
        &|d, j, ih| {
            let sv_j = sum_vars_fn(d, p, x, j);
            let x_j = d.apply(x, &[j]);
            let combined_fn = combined(d, sv_j, x_j);

            let eq1 = d.lemma(p.expectation_add, &[sv_j, x_j, pf, n]);
            // eq1 : Eq(expectation(combined_fn,pf,n), expectation(sv_j,pf,n)+expectation(x_j,pf,n))
            let e_svj = expectation(d, p, sv_j, pf, n);
            let e_xj = expectation(d, p, x_j, pf, n);
            let rhs1 = radd(d, e_svj, e_xj);

            let sum_exp_j = rsum_range(d, p, exp_of_x, j);
            let lift_ih = rcongr(d, e_svj, sum_exp_j, ih, &|d, t| radd(d, t, e_xj));
            let target = radd(d, sum_exp_j, e_xj);

            let e_combined = expectation(d, p, combined_fn, pf, n);
            let (_e, chain) = rchain(d, e_combined, &[(rhs1, eq1), (target, lift_ih)]);
            chain
        },
        m,
    );

    let value = {
        let with_m = d.lam_fv(m_fv, nat, proof);
        let with_n = d.lam_fv(n_fv, nat, with_m);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        d.lam_fv(x_fv, x_ty, with_pf)
    };
    let ty = {
        let with_m = d.pi_fv(m_fv, nat, stmt);
        let with_n = d.pi_fv(n_fv, nat, with_m);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        d.pi_fv(x_fv, x_ty, with_pf)
    };
    d.declare_theorem(p.expectation_sum_vars, ty, value)
}
