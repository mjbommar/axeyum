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
    nat_eq_to_rat, nat_rewrite_prop, radd, rat_eq_rewrite, rat_ty, rchain, rcongr, req, rle, rlt,
    rmul, rneg, rone, rrefl, rsum_range, rsymm, rtrans, rzero,
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

/// Delta height for `Rat.PairwiseUncorrelated`: above `Rat.sumVars`
/// ([`SUM_VARS_HEIGHT`], 40) and every other height declared in this
/// prelude so far.
const PAIRWISE_UNCORRELATED_HEIGHT: u16 = 41;

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
    declare_variance_indicator(d, p)?;
    declare_variance_indicator_le_quarter(d, p)?;
    declare_markov_constructed(d, p)?;
    declare_chebyshev_inequality(d, p)?;
    declare_covariance(d, p)?;
    declare_variance_add_eq(d, p)?;
    declare_variance_add_of_uncorrelated(d, p)?;
    declare_covariance_comm(d, p)?;
    declare_covariance_add_right(d, p)?;
    declare_covariance_smul_left(d, p)?;
    declare_sum_vars(d, p)?;
    declare_expectation_sum_vars(d, p)?;
    declare_covariance_sum_vars_left(d, p)?;
    declare_covariance_sum_vars(d, p)?;
    declare_pairwise_uncorrelated(d, p)?;
    declare_variance_sum_vars(d, p)?;
    declare_variance_scaled_mean(d, p)?;
    declare_chebyshev_sample_mean_uncorrelated(d, p)?;
    declare_variance_sample_mean_uncorrelated(d, p)?;
    declare_weak_law_of_large_numbers(d, p)?;
    declare_bernoulli_law_of_large_numbers(d, p)?;
    declare_variance_scaled_add_nonneg(d, p)?;
    declare_covariance_sq_le_variance_mul_of_pos(d, p)?;
    declare_covariance_sq_le_variance_mul_of_zero_zero(d, p)?;
    declare_covariance_sq_le_variance_mul(d, p)?;
    Ok(())
}

/// `Rat.IsDistribution p n`, i.e. `d.const_app(p.is_distribution, &[pf,
/// n])`.
pub(super) fn is_distribution(d: &mut IntDev<'_>, p: RatPrelude, pf: ExprId, n: ExprId) -> ExprId {
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
pub(super) fn expectation(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    x: ExprId,
    pf: ExprId,
    n: ExprId,
) -> ExprId {
    d.const_app(p.expectation, &[x, pf, n])
}

/// `fun (_ : Nat) => c`.
pub(super) fn const_fn(d: &mut IntDev<'_>, c: ExprId) -> ExprId {
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
pub(super) fn nat_as_rat(d: &mut IntDev<'_>, p: RatPrelude, n: ExprId) -> ExprId {
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
pub(super) fn sum_range_const(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    c: ExprId,
    j: ExprId,
) -> (ExprId, ExprId) {
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
pub(super) fn variance(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    x: ExprId,
    pf: ExprId,
    n: ExprId,
) -> ExprId {
    d.const_app(p.variance, &[x, pf, n])
}

/// `fun k => sub (x k) mu * sub (x k) mu` — the summand [`declare_variance`]
/// admits `Rat.variance` as, rebuilt here so [`declare_variance_nonneg`] and
/// [`declare_variance_eq`] can reconstruct the exact literal shape it
/// unfolds to (mirroring [`weighted`]/[`is_distribution_parts`]'s own
/// reason).
pub(super) fn variance_summand(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId, mu: ExprId) -> ExprId {
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
/// `(a*w)*(a*w) = (a*a)*(w*w)`, by `ring::rat::prove_eq_at` (ring-tactic-2,
/// ADR-1582) rather than the hand five-step `mul_assoc`/`mul_comm` chain
/// this file used to carry — like `middle_swap`, needs the ring producer's
/// intra-monomial factor sorting (`sort_factors`) to see both sides as the
/// same four-factor monomial.
fn scale_sq(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, w: ExprId) -> (ExprId, ExprId, ExprId) {
    let aw = rmul(d, a, w);
    let start = rmul(d, aw, aw);
    let aa = rmul(d, a, a);
    let ww = rmul(d, w, w);
    let target = rmul(d, aa, ww);
    let proof = crate::ring::rat::prove_eq_at(d, &p, &[a, w], &|d, v| {
        let (a, w) = (v[0], v[1]);
        let aw = rmul(d, a, w);
        let lhs = rmul(d, aw, aw);
        let aa = rmul(d, a, a);
        let ww = rmul(d, w, w);
        let rhs = rmul(d, aa, ww);
        (lhs, rhs)
    })
    .expect("scale_sq: (a*w)*(a*w) = (a*a)*(w*w) is a ring identity");
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
pub(super) fn bool_select_rat(
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
pub(super) fn select_rat_true(
    d: &mut IntDev<'_>,
    cond: ExprId,
    a: ExprId,
    b: ExprId,
    heq: ExprId,
) -> ExprId {
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
pub(super) fn select_rat_false(
    d: &mut IntDev<'_>,
    cond: ExprId,
    a: ExprId,
    b: ExprId,
    heq: ExprId,
) -> ExprId {
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

// --- the Bernoulli variable (rat_prelude::probability, Rado lane) ----------
//
// `Rat.indicator a X k` is already `{0,1}`-valued ([`declare_indicator_nonneg`],
// [`declare_indicator_le`]); this section adds the one pointwise fact those
// two don't give — `ind*ind = ind` — and uses it to compute the Bernoulli
// variable's variance exactly (`p(1-p)`, [`declare_variance_indicator`]) and
// bound it (`≤ 1/4`, [`declare_variance_indicator_le_quarter`]), the two
// pieces `Rat.bernoulli_law_of_large_numbers` composes from
// `Rat.weak_law_of_large_numbers`.

/// `Eq Rat (mul (indicator a X k) (indicator a X k)) (indicator a X k)` —
/// `𝟙² = 𝟙`, the fact that makes the Bernoulli variable's second moment
/// collapse to its first. Case-split on `Rat.ble a (X k)` exactly like
/// [`declare_indicator_nonneg`]/[`declare_indicator_le`]: `false` selects
/// `Rat.zero` (`0*0=0`, `mul_zero`), `true` selects `Rat.one` (`1*1=1`,
/// `mul_one`).
fn indicator_sq_eq_self(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    a: ExprId,
    x: ExprId,
    k: ExprId,
) -> ExprId {
    let xk = d.apply(x, &[k]);
    let cond = indicator_cond(d, p, a, xk);
    let one_r = rone(d, p);
    let zero_r = rzero(d, p);
    let ind_val = indicator(d, p, a, x, k);
    let ind_val_sq = rmul(d, ind_val, ind_val);
    let concl = req(d, ind_val_sq, ind_val);

    ble_cases(
        d,
        cond,
        concl,
        &|d, heq| {
            let sel = bool_select_rat(d, cond, one_r, zero_r);
            let sel_eq_zero = select_rat_false(d, cond, one_r, zero_r, heq);
            let cong_step = rcongr(d, sel, zero_r, sel_eq_zero, &|d, t| rmul(d, t, t));
            let sel_sel = rmul(d, sel, sel);
            let zz = rmul(d, zero_r, zero_r);
            let mul_zero_step = d.lemma(p.mul_zero, &[zero_r]);
            let chain = rtrans(d, sel_sel, zz, zero_r, cong_step, mul_zero_step);
            let zero_eq_sel = rsymm(d, sel, zero_r, sel_eq_zero);
            rat_eq_rewrite(d, zero_r, sel, zero_eq_sel, chain, &|d, t| {
                let sel_sq = rmul(d, sel, sel);
                req(d, sel_sq, t)
            })
        },
        &|d, heq| {
            let sel = bool_select_rat(d, cond, one_r, zero_r);
            let sel_eq_one = select_rat_true(d, cond, one_r, zero_r, heq);
            let cong_step = rcongr(d, sel, one_r, sel_eq_one, &|d, t| rmul(d, t, t));
            let sel_sel = rmul(d, sel, sel);
            let oo = rmul(d, one_r, one_r);
            let mul_one_step = d.lemma(p.mul_one, &[one_r]);
            let chain = rtrans(d, sel_sel, oo, one_r, cong_step, mul_one_step);
            let one_eq_sel = rsymm(d, sel, one_r, sel_eq_one);
            rat_eq_rewrite(d, one_r, sel, one_eq_sel, chain, &|d, t| {
                let sel_sq = rmul(d, sel, sel);
                req(d, sel_sq, t)
            })
        },
    )
}

/// `Rat.variance_indicator : ∀ a X p n, IsDistribution p n →
/// variance (Rat.indicator a X) p n =
/// mul (expectation (Rat.indicator a X) p n)
///     (sub Rat.one (expectation (Rat.indicator a X) p n))` — the Bernoulli
/// variable's variance is `p·(1−p)` where `p := E[𝟙[a≤X]]`. **The
/// `IsDistribution` hypothesis is load-bearing**, exactly as in
/// [`RatPrelude::variance_eq`] this proof reuses: without `sumRange p n = 1`
/// there is no reason `E[ind·ind]` collapses to `E[ind]` weighted correctly,
/// let alone that the result is a genuine probability.
///
/// [`indicator_sq_eq_self`] gives `ind*ind = ind` pointwise, so
/// [`RatPrelude::sum_range_congr`] collapses `E[ind·ind]` to `E[ind]`
/// directly — no case split beyond the one already inside
/// `indicator_sq_eq_self`; [`RatPrelude::variance_eq`] then gives `Var[ind] =
/// E[ind] − E[ind]²`, and `mul_sub_via_comm` (built for
/// [`declare_variance_smul`], reused here unchanged) turns `sub(mu, mu·mu)`
/// into `mu·(1−mu)`.
fn declare_variance_indicator(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
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
    let ind = d.const_app(p.indicator, &[a, x]);
    let mu = expectation(d, p, ind, pf, n);
    let one_r = rone(d, p);
    let one_minus_mu = rsub(d, p, one_r, mu);
    let rhs = rmul(d, mu, one_minus_mu);
    let variance_ind = variance(d, p, ind, pf, n);
    let concl = req(d, variance_ind, rhs);

    let veq = d.lemma(p.variance_eq, &[ind, pf, n, hd]);
    let ind_ind = weighted(d, ind, ind);
    let e_indind = expectation(d, p, ind_ind, pf, n);
    let mu_sq = rmul(d, mu, mu);
    let veq_rhs = rsub(d, p, e_indind, mu_sq);

    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let pk = d.apply(pf, &[k]);
        let sq_eq_self = indicator_sq_eq_self(d, p, a, x, k); // Eq(ind_val*ind_val, ind_val)
        let ind_val = indicator(d, p, a, x, k);
        let ind_sq = rmul(d, ind_val, ind_val);
        let body = rcongr(d, ind_sq, ind_val, sq_eq_self, &|d, t| rmul(d, t, pk));
        // body : Eq((ind_val*ind_val)*pk, ind_val*pk) — the WEIGHTED pointwise
        // fact sum_range_congr actually wants, not the bare `ind*ind=ind`.
        d.lam_fv(k_fv, nat, body)
    };
    let indind_weighted = weighted(d, ind_ind, pf);
    let ind_weighted = weighted(d, ind, pf);
    let congr_step = d.lemma(
        p.sum_range_congr,
        &[indind_weighted, ind_weighted, n, pointwise],
    );
    // congr_step : Eq(sumRange(indind_weighted,n), sumRange(ind_weighted,n))
    //   ~ Eq(e_indind, mu)                                              [defeq]

    let after_congr = rcongr(d, e_indind, mu, congr_step, &|d, t| rsub(d, p, t, mu_sq));
    let mu_musq = rsub(d, p, mu, mu_sq);

    let mul_one_step = d.lemma(p.mul_one, &[mu]); // Eq(mul(mu,one_r), mu)
    let mu_one_r = rmul(d, mu, one_r);
    let mu_one_eq = rsymm(d, mu_one_r, mu, mul_one_step); // Eq(mu, mu_one_r)
    let lift = rcongr(d, mu, mu_one_r, mu_one_eq, &|d, t| rsub(d, p, t, mu_sq));

    let (mul_start, mul_target, mul_proof) = mul_sub_via_comm(d, p, mu, one_r, mu);
    // mul_start = sub(mu*one_r, mu*mu); mul_target = mu*(one_r-mu) = rhs

    let (_e1, chain1) = rchain(d, mu_musq, &[(mul_start, lift), (mul_target, mul_proof)]);

    let (_e2, final_proof) = rchain(
        d,
        variance_ind,
        &[(veq_rhs, veq), (mu_musq, after_congr), (mul_target, chain1)],
    );

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
    d.declare_theorem(p.variance_indicator, ty, value)
}

// --- the quarter bound (`p(1-p) ≤ 1/4`, in multiplied form) ----------------
//
// Stated as `4q − 4q² ≤ 1` rather than `q(1-q) ≤ 1/4`, the same choice
// [`RatPrelude::markov_inequality`]'s own doc explains: the same content over
// an ordered field, needing no `Rat.inv`. `4 := ((1+1)+1)+1` is built inline
// (not a prelude constant) so the whole discriminant argument stays local to
// this one theorem.

/// `add(add(x,x),add(x,x))` — four copies of `x`.
fn quad(d: &mut IntDev<'_>, x: ExprId) -> ExprId {
    let xx = radd(d, x, x);
    radd(d, xx, xx)
}

/// `Eq Rat (mul Rat.one x) x`.
fn one_mul_r(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId) -> ExprId {
    let one_r = rone(d, p);
    let comm = d.lemma(p.mul_comm, &[one_r, x]); // Eq(mul(one_r,x), mul(x,one_r))
    let mul_one_step = d.lemma(p.mul_one, &[x]); // Eq(mul(x,one_r), x)
    let mul_one_r_x = rmul(d, one_r, x);
    let x_one_r = rmul(d, x, one_r);
    rtrans(d, mul_one_r_x, x_one_r, x, comm, mul_one_step)
}

/// `Eq Rat (mul ((1+1)+1)+1) x) (quad x)` — `4·x = x+x+x+x`: peel `4 =
/// ((1+1)+1)+1` apart with three `right_distrib`s, then collapse the
/// resulting four `1*x`'s to `x` (one `congr` using [`one_mul_r`] four
/// times, mirroring [`declare_variance_eq`]'s trick of rewriting a repeated
/// subterm through a motive that mentions it more than once), then one
/// `add_assoc` to match [`quad`]'s bracketing.
fn four_mul_eq_quad(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId) -> ExprId {
    let one_r = rone(d, p);
    let two_r = radd(d, one_r, one_r);
    let three_r = radd(d, two_r, one_r);
    let four_r = radd(d, three_r, one_r);

    let one_x = rmul(d, one_r, x);
    let two_x = rmul(d, two_r, x);
    let three_x = rmul(d, three_r, x);
    let four_x = rmul(d, four_r, x);

    let step1 = d.lemma(p.right_distrib, &[three_r, one_r, x]);
    let after1 = radd(d, three_x, one_x);

    let eq2 = d.lemma(p.right_distrib, &[two_r, one_r, x]);
    let after2_inner = radd(d, two_x, one_x);
    let lift2 = rcongr(d, three_x, after2_inner, eq2, &|d, t| radd(d, t, one_x));
    let after2 = radd(d, after2_inner, one_x);

    let eq3 = d.lemma(p.right_distrib, &[one_r, one_r, x]);
    let after3_inner = radd(d, one_x, one_x);
    let lift3 = rcongr(d, two_x, after3_inner, eq3, &|d, t| {
        let inner = radd(d, t, one_x);
        radd(d, inner, one_x)
    });
    let after3 = {
        let inner = radd(d, after3_inner, one_x);
        radd(d, inner, one_x)
    };

    let om = one_mul_r(d, p, x);
    let step4 = rcongr(d, one_x, x, om, &|d, t| {
        let i1 = radd(d, t, t);
        let i2 = radd(d, i1, t);
        radd(d, i2, t)
    });
    let after4 = {
        let i1 = radd(d, x, x);
        let i2 = radd(d, i1, x);
        radd(d, i2, x)
    };

    let xx = radd(d, x, x);
    let assoc_step = d.lemma(p.add_assoc, &[xx, x, x]);
    let quad_x = radd(d, xx, xx);

    let (_e, chained) = rchain(
        d,
        four_x,
        &[
            (after1, step1),
            (after2, lift2),
            (after3, lift3),
            (after4, step4),
            (quad_x, assoc_step),
        ],
    );
    chained
}

/// `Eq Rat (mul (add q q) (add q q)) (quad (mul q q))` — `(q+q)·(q+q) = 4·q²`
/// expanded as four copies of `q·q`. One `right_distrib`, one `left_distrib`
/// (applied to both resulting `q·(q+q)` occurrences via a single `congr`,
/// the same repeated-subterm trick [`four_mul_eq_quad`] uses).
fn double_sq(d: &mut IntDev<'_>, p: RatPrelude, q: ExprId) -> ExprId {
    let qq_sum = radd(d, q, q);
    let start = rmul(d, qq_sum, qq_sum);

    let step1 = d.lemma(p.right_distrib, &[q, q, qq_sum]);
    let q_qqsum = rmul(d, q, qq_sum);
    let after1 = radd(d, q_qqsum, q_qqsum);

    let step2 = d.lemma(p.left_distrib, &[q, q, q]);
    let qq = rmul(d, q, q);
    let qq_qq = radd(d, qq, qq);
    let lift2 = rcongr(d, q_qqsum, qq_qq, step2, &|d, t| radd(d, t, t));
    let quad_qq = radd(d, qq_qq, qq_qq);

    let (_e, chained) = rchain(d, start, &[(after1, step1), (quad_qq, lift2)]);
    chained
}

/// `Rat.variance_indicator_le_quarter : ∀ q,
/// le (sub (mul four q) (mul four (mul q q))) one` — `4q − 4q² ≤ 1`, i.e.
/// `q(1−q) ≤ 1/4` with the division cleared, where `four := ((1+1)+1)+1`.
///
/// Elementary and constructive, via the nonneg-square identity `0 ≤
/// (2q−1)·(2q−1)`, never a case split: [`RatPrelude::sq_nonneg`] on `w :=
/// sub (add q q) one`, then [`sub_sq_expand`] (already built for
/// [`declare_variance_eq`]) expands `w·w` into `(q+q)·(q+q) + (neg(1)·(q+q) +
/// (neg(1)·(q+q) + 1·1))`. [`double_sq`]/[`four_mul_eq_quad`] turn the
/// quadratic and linear pieces into `4·q²` and `4·q`; `neg_mul`/`neg_add`
/// collapse the two `neg(1)·(q+q)` copies and the `1·1`; a final
/// `add_assoc`/`add_comm` shuffle and [`le_of_nonneg_sub`] finish it.
fn declare_variance_indicator_le_quarter(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let carrier = rat_ty(d);

    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);

    let one_r = rone(d, p);
    let two_r = radd(d, one_r, one_r);
    let three_r = radd(d, two_r, one_r);
    let four_r = radd(d, three_r, one_r);

    let qq = rmul(d, q, q);
    let four_q = rmul(d, four_r, q);
    let four_qq = rmul(d, four_r, qq);
    let x_val = rsub(d, p, four_q, four_qq);
    let concl = rle(d, p, x_val, one_r);

    // w := sub(add(q,q), one_r); sq_nonneg(w) : 0 ≤ w*w
    let a_val = radd(d, q, q);
    let w = rsub(d, p, a_val, one_r);
    let w_sq = rmul(d, w, w);
    let sqnn = d.lemma(p.sq_nonneg, &[w]);

    // sub_sq_expand(a_val, one_r) : Eq(w*w, aa + (nba + (nba + bb)))
    let (start, mid_target, expand_proof) = sub_sq_expand(d, p, a_val, one_r);
    let neg_one = rneg(d, one_r);
    let aa = rmul(d, a_val, a_val);
    let nba = rmul(d, neg_one, a_val);
    let bb = rmul(d, one_r, one_r);
    let nba_bb = radd(d, nba, bb);
    let nba_nba_bb = radd(d, nba, nba_bb);
    let target0 = radd(d, aa, nba_nba_bb);
    let _ = mid_target; // == target0, reconstructed for named access below
    let _ = start; // == w_sq

    // Step A: bb -> one_r                                          [mul_one]
    let bb_eq_one = d.lemma(p.mul_one, &[one_r]);
    let step_a = rcongr(d, bb, one_r, bb_eq_one, &|d, t| {
        let inner = radd(d, nba, t);
        let inner2 = radd(d, nba, inner);
        radd(d, aa, inner2)
    });
    let target1 = {
        let inner = radd(d, nba, one_r);
        let inner2 = radd(d, nba, inner);
        radd(d, aa, inner2)
    };

    // Step B: both `nba` -> neg(a_val)                    [neg_mul, one_mul_r]
    let neg_mul_step = d.lemma(p.neg_mul, &[one_r, a_val]); // Eq(nba, neg(mul(one_r,a_val)))
    let one_a = rmul(d, one_r, a_val);
    let neg_one_a = rneg(d, one_a);
    let om_a = one_mul_r(d, p, a_val); // Eq(one_a, a_val)
    let neg_a = rneg(d, a_val);
    let neg_congr = rcongr(d, one_a, a_val, om_a, &|d, t| rneg(d, t));
    let (_e_nba, nba_chain) = rchain(d, nba, &[(neg_one_a, neg_mul_step), (neg_a, neg_congr)]);
    // nba_chain : Eq(nba, neg_a)

    let step_b = rcongr(d, nba, neg_a, nba_chain, &|d, t| {
        let inner = radd(d, t, one_r);
        let inner2 = radd(d, t, inner);
        radd(d, aa, inner2)
    });
    let target2 = {
        let inner = radd(d, neg_a, one_r);
        let inner2 = radd(d, neg_a, inner);
        radd(d, aa, inner2)
    };

    // Step D: regroup add(X, add(X,one_r)) -> add(add(X,X),one_r)  [add_assoc]
    let assoc_lemma = d.lemma(p.add_assoc, &[neg_a, neg_a, one_r]);
    // Eq(add(add(X,X),one_r), add(X,add(X,one_r)))
    let xx_sum = radd(d, neg_a, neg_a);
    let xx_one = radd(d, xx_sum, one_r);
    let x_inner = radd(d, neg_a, one_r);
    let x_xinner = radd(d, neg_a, x_inner);
    let assoc_rev = rsymm(d, xx_one, x_xinner, assoc_lemma); // Eq(x_xinner, xx_one)
    let step_d = rcongr(d, x_xinner, xx_one, assoc_rev, &|d, t| radd(d, aa, t));
    let target3 = radd(d, aa, xx_one);

    // Step E: neg_a + neg_a -> neg(quad(q))                          [neg_add]
    let quad_q = quad(d, q);
    let neg_add_lemma = d.lemma(p.neg_add, &[a_val, a_val]);
    // Eq(neg(add(a_val,a_val)), add(neg_a,neg_a))
    let neg_quad_q = rneg(d, quad_q);
    let xx_eq_neg_quad = rsymm(d, neg_quad_q, xx_sum, neg_add_lemma);
    // xx_eq_neg_quad : Eq(xx_sum, neg_quad_q)
    let step_e = rcongr(d, xx_sum, neg_quad_q, xx_eq_neg_quad, &|d, t| {
        let inner = radd(d, t, one_r);
        radd(d, aa, inner)
    });
    let target4 = {
        let inner = radd(d, neg_quad_q, one_r);
        radd(d, aa, inner)
    };

    // Step F: aa -> mul(four_r, qq)                    [double_sq, four_mul_eq_quad]
    let double_sq_proof = double_sq(d, p, q); // Eq(aa, quad(qq))
    let quad_qq = quad(d, qq);
    let four_mul_qq = four_mul_eq_quad(d, p, qq); // Eq(four_qq, quad_qq)
    let four_mul_qq_rev = rsymm(d, four_qq, quad_qq, four_mul_qq); // Eq(quad_qq, four_qq)
    let aa_to_four = rtrans(d, aa, quad_qq, four_qq, double_sq_proof, four_mul_qq_rev);
    let step_f = rcongr(d, aa, four_qq, aa_to_four, &|d, t| {
        let inner = radd(d, neg_quad_q, one_r);
        radd(d, t, inner)
    });
    let target5 = {
        let inner = radd(d, neg_quad_q, one_r);
        radd(d, four_qq, inner)
    };

    // Step G: quad_q (inside the neg) -> mul(four_r, q)         [four_mul_eq_quad]
    let four_mul_q = four_mul_eq_quad(d, p, q); // Eq(four_q, quad_q)
    let quad_q_to_four = rsymm(d, four_q, quad_q, four_mul_q); // Eq(quad_q, four_q)
    let neg_step = rcongr(d, quad_q, four_q, quad_q_to_four, &|d, t| rneg(d, t));
    // neg_step : Eq(neg_quad_q, neg(four_q))
    let neg_four_q = rneg(d, four_q);
    let step_g = rcongr(d, neg_quad_q, neg_four_q, neg_step, &|d, t| {
        let inner = radd(d, t, one_r);
        radd(d, four_qq, inner)
    });
    let target6 = {
        let inner = radd(d, neg_four_q, one_r);
        radd(d, four_qq, inner)
    };

    // Reshuffle: A+(B+C) -> (A+B)+C -> (B+A)+C -> C+(B+A)
    let a_term = four_qq;
    let b_term = neg_four_q;
    let c_term = one_r;
    let assoc_x1 = d.lemma(p.add_assoc, &[a_term, b_term, c_term]);
    // Eq(add(add(A,B),C), add(A,add(B,C)))
    let ab = radd(d, a_term, b_term);
    let ab_c = radd(d, ab, c_term);
    let step_x1 = rsymm(d, ab_c, target6, assoc_x1); // Eq(target6, ab_c)

    let comm_ab = d.lemma(p.add_comm, &[a_term, b_term]); // Eq(add(A,B), add(B,A))
    let ba = radd(d, b_term, a_term);
    let step_x2 = rcongr(d, ab, ba, comm_ab, &|d, t| radd(d, t, c_term));
    let ba_c = radd(d, ba, c_term);

    let comm_bac = d.lemma(p.add_comm, &[ba, c_term]); // Eq(add(ba,C), add(C,ba))
    let c_ba = radd(d, c_term, ba);
    let step_x3 = comm_bac;

    // add(neg_four_q, four_qq) = neg(sub(four_q,four_qq)) = neg(x_val)
    let neg_four_qq = rneg(d, four_qq);
    let neg_add_x = d.lemma(p.neg_add, &[four_q, neg_four_qq]);
    // Eq(neg(add(four_q,neg_four_qq)), add(neg(four_q),neg(neg_four_qq)))
    let neg_neg_qq = d.lemma(p.neg_neg, &[four_qq]); // Eq(neg(neg_four_qq), four_qq)
    let neg_four_q_2 = rneg(d, four_q);
    let neg_neg_four_qq = rneg(d, neg_four_qq);
    let rhs_na = radd(d, neg_four_q_2, neg_neg_four_qq);
    let cong_nn = rcongr(d, neg_neg_four_qq, four_qq, neg_neg_qq, &|d, t| {
        radd(d, neg_four_q_2, t)
    });
    let ba_form = radd(d, neg_four_q_2, four_qq);
    let x_lit = radd(d, four_q, neg_four_qq);
    let neg_x_lit = rneg(d, x_lit);
    let (_e_na, na_chain) = rchain(d, neg_x_lit, &[(rhs_na, neg_add_x), (ba_form, cong_nn)]);
    // na_chain : Eq(neg_x_lit, ba_form)     where ba_form == ba (same shape)
    let na_chain_rev = rsymm(d, neg_x_lit, ba_form, na_chain); // Eq(ba_form, neg_x_lit)

    let step_final = rcongr(d, ba, neg_x_lit, na_chain_rev, &|d, t| radd(d, c_term, t));
    let final_target = radd(d, c_term, neg_x_lit);

    let (_ey, target6_to_final) = rchain(
        d,
        target6,
        &[
            (ab_c, step_x1),
            (ba_c, step_x2),
            (c_ba, step_x3),
            (final_target, step_final),
        ],
    );

    // Assemble: w*w = target0 = target1 = target2 = target3 = target4
    //   = target5 = target6 = final_target = add(one_r, neg(x_lit))
    let (_ez, full_chain) = rchain(
        d,
        w_sq,
        &[
            (target0, expand_proof),
            (target1, step_a),
            (target2, step_b),
            (target3, step_d),
            (target4, step_e),
            (target5, step_f),
            (target6, step_g),
            (final_target, target6_to_final),
        ],
    );

    let nonneg_final = rat_eq_rewrite(d, w_sq, final_target, full_chain, sqnn, &|d, t| {
        let zero_r = rzero(d, p);
        rle(d, p, zero_r, t)
    });
    // nonneg_final : le zero (add(one_r, neg(x_lit)))  ~  le zero (sub one_r x_val)  [defeq]

    let final_proof = le_of_nonneg_sub(d, p, one_r, x_val, nonneg_final);

    let ty = d.pi_fv(q_fv, carrier, concl);
    let value = d.lam_fv(q_fv, carrier, final_proof);
    d.declare_theorem(p.variance_indicator_le_quarter, ty, value)
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

/// `Rat.covariance_comm : ∀ X Y p n, covariance X Y p n = covariance Y X p n`
/// — `Cov[X,Y] = Cov[Y,X]`.
///
/// Purely algebraic, no `IsDistribution` hypothesis — matching
/// [`declare_covariance_add_right`]'s own unconditional form: `mul_comm` on
/// the pointwise product `X k · Y k` (lifted through `sum_range_congr`, at
/// the `weighted(_, pf)` level `expectation` actually applies) identifies
/// `E[X·Y]` with `E[Y·X]`, `mul_comm` on the means identifies `E[X]·E[Y]`
/// with `E[Y]·E[X]`, and the two differences match up directly (no
/// `sub_add_add` regrouping needed, unlike [`declare_covariance_add_right`]:
/// both sides are already a plain `sub` of one matched pair).
fn declare_covariance_comm(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
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

    let cov_xy = covariance(d, p, x, y, pf, n);
    let cov_yx = covariance(d, p, y, x, pf, n);
    let concl = req(d, cov_xy, cov_yx);

    // --- E[X*Y] = E[Y*X], via sum_range_congr on mul_comm pointwise
    let xy = weighted(d, x, y);
    let yx = weighted(d, y, x);
    let e_xy = expectation(d, p, xy, pf, n);
    let e_yx = expectation(d, p, yx, pf, n);

    let xy_weighted = weighted(d, xy, pf);
    let yx_weighted = weighted(d, yx, pf);
    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let xk = d.apply(x, &[k]);
        let yk = d.apply(y, &[k]);
        let pk = d.apply(pf, &[k]);
        let xkyk = rmul(d, xk, yk);
        let ykxk = rmul(d, yk, xk);
        let step = d.lemma(p.mul_comm, &[xk, yk]);
        let lifted = rcongr(d, xkyk, ykxk, step, &|d, t| rmul(d, t, pk));
        d.lam_fv(k_fv, nat, lifted)
    };
    let congr = d.lemma(p.sum_range_congr, &[xy_weighted, yx_weighted, n, pointwise]);
    // congr : Eq(sumRange(xy_weighted,n), sumRange(yx_weighted,n))
    //   ~ Eq(e_xy, e_yx)                                              [defeq]

    // --- E[X]*E[Y] = E[Y]*E[X], via mul_comm directly
    let ex = expectation(d, p, x, pf, n);
    let ey = expectation(d, p, y, pf, n);
    let exey = rmul(d, ex, ey);
    let eyex = rmul(d, ey, ex);
    let comm_means = d.lemma(p.mul_comm, &[ex, ey]);

    // --- combine: sub(e_xy,exey) = sub(e_yx,exey) = sub(e_yx,eyex)
    let sub_yx_exey = rsub(d, p, e_yx, exey);
    let d1 = rcongr(d, e_xy, e_yx, congr, &|d, t| rsub(d, p, t, exey));
    let sub_final = rsub(d, p, e_yx, eyex);
    let d2 = rcongr(d, exey, eyex, comm_means, &|d, t| rsub(d, p, e_yx, t));

    let sub_start = rsub(d, p, e_xy, exey);
    let (_e, final_chain) = rchain(d, sub_start, &[(sub_yx_exey, d1), (sub_final, d2)]);
    // final_chain : Eq(sub_start, sub_final)  ~ Eq(cov_xy, cov_yx)     [defeq]

    let value = {
        let with_n = d.lam_fv(n_fv, nat, final_chain);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_y = d.lam_fv(y_fv, fn_ty, with_pf);
        d.lam_fv(x_fv, fn_ty, with_y)
    };
    let ty = {
        let with_n = d.pi_fv(n_fv, nat, concl);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        let with_y = d.pi_fv(y_fv, fn_ty, with_pf);
        d.pi_fv(x_fv, fn_ty, with_y)
    };
    d.declare_theorem(p.covariance_comm, ty, value)
}

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

/// `Rat.covariance_smul_left : ∀ a X Y p n,
/// covariance (fun k => a * X k) Y p n = a * covariance X Y p n` —
/// bilinearity of covariance in its FIRST argument, the scalar half.
///
/// Purely algebraic, no `IsDistribution` hypothesis needed — matching
/// [`declare_covariance_add_right`]'s own unconditional form. `Cov[aX,Y] =
/// E[(aX)Y] − E[aX]E[Y]`: [`RatPrelude::mul_assoc`] turns the pointwise
/// summand `(a·Xk)·Yk` into `a·(Xk·Yk)` (lifted through `sum_range_congr` at
/// the `weighted(_,pf)` level, exactly [`declare_covariance_add_right`]'s
/// own Step A shape), then [`RatPrelude::expectation_smul`] pulls `a` out of
/// `E[(aX)Y]` entirely: `E[(aX)Y] = E[a·(XY)] = a·E[XY]`. Separately
/// `E[aX]·E[Y] = (a·E[X])·E[Y] = a·(E[X]·E[Y])` via `expectation_smul` then
/// `mul_assoc`. `mul_sub_via_comm` (private, above) then factors `a` out of
/// the resulting difference, the same step [`declare_variance_smul`] closes
/// with.
fn declare_covariance_smul_left(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let scaled_x = scale_fn(d, a, x);
    let cov_ax_y = covariance(d, p, scaled_x, y, pf, n);
    let cov_x_y = covariance(d, p, x, y, pf, n);
    let rhs = rmul(d, a, cov_x_y);
    let concl = req(d, cov_ax_y, rhs);

    let xy = weighted(d, x, y); // fun k => Xk*Yk
    let e_xy = expectation(d, p, xy, pf, n);
    let ex = expectation(d, p, x, pf, n);
    let ey = expectation(d, p, y, pf, n);
    let exey = rmul(d, ex, ey);
    // cov_x_y unfolds (defeq) to rsub(e_xy, exey).

    // --- Step A: e_xy' = a * e_xy, where xy' = weighted(scaled_x, y)
    let xy_prime = weighted(d, scaled_x, y); // fun k => (a*Xk)*Yk
    let scale_xy = scale_fn(d, a, xy); // fun k => a*(Xk*Yk)
    let pointwise_a = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let xk = d.apply(x, &[k]);
        let yk = d.apply(y, &[k]);
        let a_xk = rmul(d, a, xk);
        let lhs_k = rmul(d, a_xk, yk);
        let xk_yk = rmul(d, xk, yk);
        let rhs_k = rmul(d, a, xk_yk);
        let step = d.lemma(p.mul_assoc, &[a, xk, yk]); // Eq(lhs_k, rhs_k)
        let pk = d.apply(pf, &[k]);
        let lifted = rcongr(d, lhs_k, rhs_k, step, &|d, t| rmul(d, t, pk));
        d.lam_fv(k_fv, nat, lifted)
    };
    let xy_prime_weighted = weighted(d, xy_prime, pf);
    let scale_xy_weighted = weighted(d, scale_xy, pf);
    let congr_a = d.lemma(
        p.sum_range_congr,
        &[xy_prime_weighted, scale_xy_weighted, n, pointwise_a],
    );
    // congr_a : Eq(sumRange(xy_prime_weighted,n), sumRange(scale_xy_weighted,n))
    //   ~ Eq(e_xy_prime, expectation(scale_xy,pf,n))                    [defeq]
    let smul_a = d.lemma(p.expectation_smul, &[a, xy, pf, n]);
    // smul_a : Eq(expectation(scale_xy,pf,n), a*e_xy)
    let e_xy_prime = expectation(d, p, xy_prime, pf, n);
    let e_scale_xy = expectation(d, p, scale_xy, pf, n);
    let a_e_xy = rmul(d, a, e_xy);
    let (_e, e_a_eq) = rchain(d, e_xy_prime, &[(e_scale_xy, congr_a), (a_e_xy, smul_a)]);
    // e_a_eq : Eq(e_xy_prime, a_e_xy)

    // --- Step B: E[aX]*E[Y] = a*(ex*ey)
    let e_ax = expectation(d, p, scaled_x, pf, n);
    let smul_b = d.lemma(p.expectation_smul, &[a, x, pf, n]);
    // smul_b : Eq(e_ax, a*ex)
    let a_ex = rmul(d, a, ex);
    let e_c1 = rcongr(d, e_ax, a_ex, smul_b, &|d, t| rmul(d, t, ey));
    // e_c1 : Eq(e_ax*ey, a_ex*ey)
    let e_ax_ey = rmul(d, e_ax, ey);
    let a_ex_ey = rmul(d, a_ex, ey);
    let step_assoc = d.lemma(p.mul_assoc, &[a, ex, ey]); // Eq(a_ex_ey, a*(ex*ey))
    let a_exey = rmul(d, a, exey);
    let (_e, e_c_eq) = rchain(d, e_ax_ey, &[(a_ex_ey, e_c1), (a_exey, step_assoc)]);
    // e_c_eq : Eq(e_ax_ey, a_exey)

    // --- Step C: combine into sub(A,B), A := a_e_xy, B := a_exey
    let d1 = rcongr(d, e_xy_prime, a_e_xy, e_a_eq, &|d, t| {
        rsub(d, p, t, e_ax_ey)
    });
    let after_d1 = rsub(d, p, a_e_xy, e_ax_ey);
    let d2 = rcongr(d, e_ax_ey, a_exey, e_c_eq, &|d, t| rsub(d, p, a_e_xy, t));
    let after_d2 = rsub(d, p, a_e_xy, a_exey);

    // --- Step D: sub(a*e_xy, a*exey) = a * sub(e_xy,exey)
    let (_, target_e, proof_e) = mul_sub_via_comm(d, p, a, e_xy, exey);

    let sub_start = rsub(d, p, e_xy_prime, e_ax_ey); // ~ cov_ax_y            [defeq]
    let (_e, final_chain) = rchain(
        d,
        sub_start,
        &[(after_d1, d1), (after_d2, d2), (target_e, proof_e)],
    );
    // final_chain : Eq(sub_start, target_e) ~ Eq(cov_ax_y, a*cov_x_y)  [defeq]

    let value = {
        let with_n = d.lam_fv(n_fv, nat, final_chain);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_y = d.lam_fv(y_fv, fn_ty, with_pf);
        let with_x = d.lam_fv(x_fv, fn_ty, with_y);
        d.lam_fv(a_fv, carrier, with_x)
    };
    let ty = {
        let with_n = d.pi_fv(n_fv, nat, concl);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        let with_y = d.pi_fv(y_fv, fn_ty, with_pf);
        let with_x = d.pi_fv(x_fv, fn_ty, with_y);
        d.pi_fv(a_fv, carrier, with_x)
    };
    d.declare_theorem(p.covariance_smul_left, ty, value)
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

/// `Eq Rat (sumRange (weighted (const_fn zero) pf) n) zero` — the expectation
/// of the identically-zero sequence is zero, for ANY `pf` (no
/// `IsDistribution` needed): `sumRange_congr` collapses each summand `zero *
/// pf k` to `zero` pointwise via [`rat_zero_mul`], then [`sum_range_const`]
/// at `c = zero` plus [`RatPrelude::mul_zero`] collapses the resulting
/// constant sum. The exact argument [`declare_expectation_sum_vars`]'s own
/// base case uses, reproduced here (private to
/// [`declare_covariance_sum_vars_left`]) since it needs the identical fact
/// about `Rat.covariance`'s first argument rather than `Rat.expectation`'s
/// own recursion. Returns `(const_fn zero, proof)`.
fn expectation_zero_eq_zero(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    pf: ExprId,
    n: ExprId,
) -> (ExprId, ExprId) {
    let nat = d.nat_ty();
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
    (const_zero, chain)
}

/// `Rat.covariance_sumVars_left : ∀ X Y p n m,
/// covariance (sumVars X m) Y p n = sumRange (fun j => covariance (X j) Y p
/// n) m` — bilinearity of covariance over a FAMILY of variables in its FIRST
/// argument. **The prerequisite the finite weak law of large numbers has
/// been missing twice**: `Var[Σ_j X_j] = Σ_j Var[X_j]` under pairwise
/// uncorrelatedness needs `Cov[Σ_j X_j, Y]` reduced to a sum of covariances
/// first, which neither [`RatPrelude::covariance_add_right`] (the `m = 2`
/// case, and in the wrong argument) nor
/// [`RatPrelude::expectation_sum_vars`] (linearity of `expectation`, not
/// `covariance`) gives.
///
/// Induction on `m`, mirroring [`declare_expectation_sum_vars`]'s own shape.
///
/// **Base case** (`m = 0`): `sumVars X 0 k` ι-reduces to `zero` under the
/// `k`-binder exactly as [`declare_expectation_sum_vars`]'s own base case
/// documents, so `covariance (sumVars X 0) Y p n` is definitionally
/// `covariance (fun _ => zero) Y p n`, i.e. `sub (expectation (weighted
/// (const_fn zero) Y) p n) (mul (expectation (const_fn zero) p n)
/// (expectation Y p n))`. **No `IsDistribution` hypothesis is needed**:
/// `weighted (const_fn zero) Y` is definitionally `scale_fn zero Y` (`(const
/// zero) k` beta-reduces to `zero` directly inside the product, no proof
/// needed), so [`RatPrelude::expectation_smul`] at the zero scalar plus
/// [`rat_zero_mul`] collapses the first `expectation` term to `zero`
/// unconditionally; [`expectation_zero_eq_zero`] collapses the second the
/// same way [`declare_expectation_sum_vars`]'s base case does; and
/// [`RatPrelude::sub_self`] closes `sub zero zero = zero`.
///
/// **Successor step**: `sumVars X (succ j) k` ι-reduces (again under the
/// `k`-binder) to `sumVars X j k + X j k`, so the goal is definitionally
/// about `covariance (fun k => sumVars X j k + X j k) Y p n`. Bilinearity in
/// the FIRST argument is not directly available — only
/// [`RatPrelude::covariance_add_right`] (second argument) is proved — so this
/// derives it as a three-step corollary: [`RatPrelude::covariance_comm`] to
/// swap `Cov[A+B, Y]` to `Cov[Y, A+B]`, [`RatPrelude::covariance_add_right`]
/// to split it into `Cov[Y,A] + Cov[Y,B]`, then
/// [`RatPrelude::covariance_comm`] twice more to swap each term back to
/// `Cov[A,Y] + Cov[B,Y]`. The inductive hypothesis then rewrites `Cov[sumVars
/// X j, Y]` to `sumRange (fun jj => covariance (X jj) Y p n) j`, landing
/// definitionally on `sumRange (…) (succ j)` via `sumRange`'s own `succ`-case
/// ι-reduction.
fn declare_covariance_sum_vars_left(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);
    let nat_fn_ty = d.arrow(nat, carrier);
    let x_ty = d.arrow(nat, nat_fn_ty);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let cov_of_x = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let xj = d.apply(x, &[j]);
        let cxy = covariance(d, p, xj, y, pf, n);
        d.lam_fv(j_fv, nat, cxy)
    };

    let motive = |d: &mut IntDev<'_>, bound: ExprId| -> ExprId {
        let sv = sum_vars_fn(d, p, x, bound);
        let lhs = covariance(d, p, sv, y, pf, n);
        let rhs = rsum_range(d, p, cov_of_x, bound);
        req(d, lhs, rhs)
    };
    let stmt = motive(d, m);

    let proof = d.induct(
        &motive,
        &|d| {
            // --- Base: covariance (const_fn zero) y p n = zero, unconditionally.
            let zero_r = rzero(d, p);
            let (z0, piece_b_chain) = expectation_zero_eq_zero(d, p, pf, n);
            let weighted_z0 = weighted(d, z0, pf);
            let sum_wz0_raw = rsum_range(d, p, weighted_z0, n);

            // Piece A: expectation (scale_fn zero y) p n = zero.
            let scaled_y = scale_fn(d, zero_r, y);
            let smul_a = d.lemma(p.expectation_smul, &[zero_r, y, pf, n]);
            let ey = expectation(d, p, y, pf, n);
            let zero_mul_ey = rat_zero_mul(d, p, ey);
            let e_scaled_y = expectation(d, p, scaled_y, pf, n);
            let zero_r_times_ey = rmul(d, zero_r, ey);
            let (_e, piece_a_chain) = rchain(
                d,
                e_scaled_y,
                &[(zero_r_times_ey, smul_a), (zero_r, zero_mul_ey)],
            );

            // Piece B, multiplied by ey: sum_wz0_raw * ey = zero.
            let mul_b = rmul(d, sum_wz0_raw, ey);
            let mul_b_congr = rcongr(d, sum_wz0_raw, zero_r, piece_b_chain, &|d, t| {
                rmul(d, t, ey)
            });
            let zero_mul_ey2 = rat_zero_mul(d, p, ey);
            let zero_r_times_ey2 = rmul(d, zero_r, ey);
            let (_e, mul_b_chain) = rchain(
                d,
                mul_b,
                &[(zero_r_times_ey2, mul_b_congr), (zero_r, zero_mul_ey2)],
            );

            // sub(e_scaled_y, mul_b) = sub(zero,zero) = zero.
            let sub_start = rsub(d, p, e_scaled_y, mul_b);
            let after_d1 = rsub(d, p, zero_r, mul_b);
            let d1 = rcongr(d, e_scaled_y, zero_r, piece_a_chain, &|d, t| {
                rsub(d, p, t, mul_b)
            });
            let zero_sub_zero = rsub(d, p, zero_r, zero_r);
            let d2 = rcongr(d, mul_b, zero_r, mul_b_chain, &|d, t| rsub(d, p, zero_r, t));
            let sub_self_zero = d.lemma(p.sub_self, &[zero_r]);

            let (_e, base_chain) = rchain(
                d,
                sub_start,
                &[(after_d1, d1), (zero_sub_zero, d2), (zero_r, sub_self_zero)],
            );
            base_chain
        },
        &|d, j, ih| {
            let sv_j = sum_vars_fn(d, p, x, j);
            let x_j = d.apply(x, &[j]);
            let combined_fn = combined(d, sv_j, x_j);

            // --- Cov[A+B, Y] = Cov[Y, A+B] = Cov[Y,A]+Cov[Y,B] = Cov[A,Y]+Cov[B,Y]
            let cov_comb_y = covariance(d, p, combined_fn, y, pf, n);
            let cov_y_comb = covariance(d, p, y, combined_fn, pf, n);
            let c1 = d.lemma(p.covariance_comm, &[combined_fn, y, pf, n]);

            let cov_y_svj = covariance(d, p, y, sv_j, pf, n);
            let cov_y_xj = covariance(d, p, y, x_j, pf, n);
            let c2 = d.lemma(p.covariance_add_right, &[y, sv_j, x_j, pf, n]);
            let after_c2 = radd(d, cov_y_svj, cov_y_xj);

            let cov_svj_y = covariance(d, p, sv_j, y, pf, n);
            let c3 = d.lemma(p.covariance_comm, &[y, sv_j, pf, n]);
            let mid3 = radd(d, cov_svj_y, cov_y_xj);
            let lift3 = rcongr(d, cov_y_svj, cov_svj_y, c3, &|d, t| radd(d, t, cov_y_xj));

            let cov_xj_y = covariance(d, p, x_j, y, pf, n);
            let c4 = d.lemma(p.covariance_comm, &[y, x_j, pf, n]);
            let target_bilinear = radd(d, cov_svj_y, cov_xj_y);
            let lift4 = rcongr(d, cov_y_xj, cov_xj_y, c4, &|d, t| radd(d, cov_svj_y, t));

            // --- rewrite Cov[sumVars X j, Y] via the inductive hypothesis
            let sum_j = rsum_range(d, p, cov_of_x, j);
            let final_target = radd(d, sum_j, cov_xj_y);
            let lift_ih = rcongr(d, cov_svj_y, sum_j, ih, &|d, t| radd(d, t, cov_xj_y));

            let (_e, full_chain) = rchain(
                d,
                cov_comb_y,
                &[
                    (cov_y_comb, c1),
                    (after_c2, c2),
                    (mid3, lift3),
                    (target_bilinear, lift4),
                    (final_target, lift_ih),
                ],
            );
            full_chain
        },
        m,
    );

    let value = {
        let with_m = d.lam_fv(m_fv, nat, proof);
        let with_n = d.lam_fv(n_fv, nat, with_m);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_y = d.lam_fv(y_fv, fn_ty, with_pf);
        d.lam_fv(x_fv, x_ty, with_y)
    };
    let ty = {
        let with_m = d.pi_fv(m_fv, nat, stmt);
        let with_n = d.pi_fv(n_fv, nat, with_m);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        let with_y = d.pi_fv(y_fv, fn_ty, with_pf);
        d.pi_fv(x_fv, x_ty, with_y)
    };
    d.declare_theorem(p.covariance_sum_vars_left, ty, value)
}

/// `Rat.covariance_sumVars : ∀ X Y p n m m',
/// covariance (sumVars X m) (sumVars Y m') p n =
/// sumRange (fun i => sumRange (fun j => covariance (X i) (Y j) p n) m') m`
/// — bilinearity of covariance over TWO families at once: `Cov[Σᵢ Xᵢ, Σⱼ Yⱼ]
/// = Σᵢ Σⱼ Cov[Xᵢ, Yⱼ]`. [`declare_covariance_sum_vars_left`]'s own
/// statement already quantifies its `Y` over an ARBITRARY `Nat → Rat`
/// function, so this is not a new induction: instantiate that theorem once
/// at `Y := sumVars Y' m'` to reduce the first family, then for each fixed
/// `i` swap `Cov[X i, sumVars Y' m']` to `Cov[sumVars Y' m', X i]`
/// ([`RatPrelude::covariance_comm`]) and apply
/// [`declare_covariance_sum_vars_left`] AGAIN (roles reversed, at `m'`) to
/// reduce the second family, then swap each resulting term back
/// ([`RatPrelude::covariance_comm`] again, pointwise under the inner sum via
/// [`RatPrelude::sum_range_congr`]) and lift that pointwise fact through the
/// outer sum with a second [`RatPrelude::sum_range_congr`]. Both congruence
/// steps use the UNRESTRICTED form, not `sumRange_congr_lt`: `covariance_comm`
/// and `covariance_sumVars_left` hold for every index, not just a bounded
/// range, unlike `PairwiseUncorrelated`'s own zero facts.
///
/// This is exactly the natural double-sum generalisation `Rat.sumRange_swap`
/// (the Fubini swap landed in `rat_prelude::sum`) might have been expected to
/// unlock — and it does not: the derivation above already produces the
/// `Σᵢ Σⱼ` order directly (apply the `X`-reduction first, the `Y`-reduction
/// second, inside each `i`-th term), so no reordering of summation is ever
/// needed. `sumRange_swap` would only matter for a proof that needed the
/// OTHER order, `Σⱼ Σᵢ`, and nothing here does — [`RatPrelude::covariance_comm`]
/// already gets that symmetry for free at the level of `covariance` itself.
fn declare_covariance_sum_vars(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);
    let nat_fn_ty = d.arrow(nat, carrier);
    let x_ty = d.arrow(nat, nat_fn_ty);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let m2_fv = d.fresh_fvar();
    let m2 = d.kernel().fvar(m2_fv);

    let sv_x = sum_vars_fn(d, p, x, m);
    let sv_y = sum_vars_fn(d, p, y, m2);
    let lhs = covariance(d, p, sv_x, sv_y, pf, n);

    // outer_fn i := sumRange (fun j => covariance (X i) (Y j) p n) m2
    let outer_fn = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let xi = d.apply(x, &[i]);
        let inner_fn = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let yj = d.apply(y, &[j]);
            let cov = covariance(d, p, xi, yj, pf, n);
            d.lam_fv(j_fv, nat, cov)
        };
        let inner_sum = rsum_range(d, p, inner_fn, m2);
        d.lam_fv(i_fv, nat, inner_sum)
    };
    let rhs = rsum_range(d, p, outer_fn, m);
    let concl = req(d, lhs, rhs);

    // Step 1: Cov[sumVars X m, sumVars Y m2] p n
    //       = sumRange (fun i => Cov[X i, sumVars Y m2] p n) m
    let h1 = d.lemma(p.covariance_sum_vars_left, &[x, sv_y, pf, n, m]);
    let mid_fn = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let xi = d.apply(x, &[i]);
        let cov = covariance(d, p, xi, sv_y, pf, n);
        d.lam_fv(i_fv, nat, cov)
    };
    let mid = rsum_range(d, p, mid_fn, m);

    // Step 2: pointwise, for each i:
    //   Cov[X i, sumVars Y m2] p n = sumRange (fun j => Cov[X i, Y j] p n) m2
    let pointwise_i = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let xi = d.apply(x, &[i]);

        let cov_xi_svy = covariance(d, p, xi, sv_y, pf, n);
        let comm1 = d.lemma(p.covariance_comm, &[xi, sv_y, pf, n]);
        let cov_svy_xi = covariance(d, p, sv_y, xi, pf, n);

        // Cov[sumVars Y m2, X i] p n = sumRange (fun j => Cov[Y j, X i] p n) m2
        let h2 = d.lemma(p.covariance_sum_vars_left, &[y, xi, pf, n, m2]);
        let yx_fn = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let yj = d.apply(y, &[j]);
            let cov = covariance(d, p, yj, xi, pf, n);
            d.lam_fv(j_fv, nat, cov)
        };
        let sum_yx = rsum_range(d, p, yx_fn, m2);

        // swap each term back: Cov[Y j, X i] p n = Cov[X i, Y j] p n
        let xy_fn = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let yj = d.apply(y, &[j]);
            let cov = covariance(d, p, xi, yj, pf, n);
            d.lam_fv(j_fv, nat, cov)
        };
        let pointwise2 = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let yj = d.apply(y, &[j]);
            let body = d.lemma(p.covariance_comm, &[yj, xi, pf, n]);
            d.lam_fv(j_fv, nat, body)
        };
        let congr2 = d.lemma(p.sum_range_congr, &[yx_fn, xy_fn, m2, pointwise2]);
        let sum_xy = rsum_range(d, p, xy_fn, m2);

        let (_e, chain) = rchain(
            d,
            cov_xi_svy,
            &[(cov_svy_xi, comm1), (sum_yx, h2), (sum_xy, congr2)],
        );
        d.lam_fv(i_fv, nat, chain)
    };
    let congr1 = d.lemma(p.sum_range_congr, &[mid_fn, outer_fn, m, pointwise_i]);

    let (_e, final_chain) = rchain(d, lhs, &[(mid, h1), (rhs, congr1)]);

    let value = {
        let with_m2 = d.lam_fv(m2_fv, nat, final_chain);
        let with_m = d.lam_fv(m_fv, nat, with_m2);
        let with_n = d.lam_fv(n_fv, nat, with_m);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_y = d.lam_fv(y_fv, x_ty, with_pf);
        d.lam_fv(x_fv, x_ty, with_y)
    };
    let ty = {
        let with_m2 = d.pi_fv(m2_fv, nat, concl);
        let with_m = d.pi_fv(m_fv, nat, with_m2);
        let with_n = d.pi_fv(n_fv, nat, with_m);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        let with_y = d.pi_fv(y_fv, x_ty, with_pf);
        d.pi_fv(x_fv, x_ty, with_y)
    };
    d.declare_theorem(p.covariance_sum_vars, ty, value)
}

// --- pairwise uncorrelatedness and the variance of a sum of variables ------
//
// `Rat.covariance_sumVars_left` reduces `Cov[Σ_j X_j, Y]` to a sum of
// covariances; `Rat.variance_add_of_uncorrelated` gives the two-variable
// variance-of-a-sum step. Together with the bounded sum lemmas
// `Rat.sumRange_congr_lt`/`Rat.sumRange_eq_zero_of_lt` (`rat_prelude::sum`,
// needed because `PairwiseUncorrelated` only ever supplies zero facts
// bounded by the family's own range, never universally), this is everything
// `Rat.variance_sumVars` needs.

/// `Rat.PairwiseUncorrelated X m p n`, i.e. `d.const_app(p.pairwise_uncorrelated,
/// &[x, m, pf, n])`.
pub(super) fn pairwise_uncorrelated(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    x: ExprId,
    m: ExprId,
    pf: ExprId,
    n: ExprId,
) -> ExprId {
    d.const_app(p.pairwise_uncorrelated, &[x, m, pf, n])
}

/// `∀ i j, Lt i m → Lt j m → Not (Eq i j) → Eq Rat (covariance (X i) (X j) p
/// n) zero` — the body [`declare_pairwise_uncorrelated`] admits
/// `Rat.PairwiseUncorrelated` as, rebuilt here so [`declare_variance_sum_vars`]
/// can reconstruct the exact literal Pi shape it unfolds to (mirroring
/// [`is_distribution_parts`]'s own reason) and apply an `h :
/// PairwiseUncorrelated X m p n` hypothesis directly as a function — the
/// kernel's `infer_app` whnf-unfolds a `Regular` `Definition` like this one
/// to find the underlying `Pi`, so a bound `h` can be applied to concrete
/// indices/proofs without any separate destructuring step.
fn pairwise_uncorrelated_body(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    x: ExprId,
    m: ExprId,
    pf: ExprId,
    n: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let hi_ty = d.lt(i, m);
    let hj_ty = d.lt(j, m);
    let eq_ij = d.eq(i, j);
    let hne_ty = d.not(eq_ij);

    let xi = d.apply(x, &[i]);
    let xj = d.apply(x, &[j]);
    let cov_ij = covariance(d, p, xi, xj, pf, n);
    let zero_r = rzero(d, p);
    let concl = req(d, cov_ij, zero_r);

    let inner = d.arrow(hne_ty, concl);
    let with_hj = d.arrow(hj_ty, inner);
    let with_hi = d.arrow(hi_ty, with_hj);
    let with_j = d.pi_fv(j_fv, nat, with_hi);
    d.pi_fv(i_fv, nat, with_j)
}

/// Admit `Rat.PairwiseUncorrelated : (Nat → Nat → Rat) → Nat → (Nat → Rat) →
/// Nat → Prop := fun X m p n => ∀ i j, Lt i m → Lt j m → Not (Eq i j) →
/// covariance (X i) (X j) p n = zero` — **the honest, strictly weaker
/// hypothesis in place of independence** (see [`RatPrelude::covariance`]'s
/// own doc and this module's header): a JOINT distribution over a product
/// space is not expressible here, only `Cov ~ 0`, now over a whole FAMILY.
fn declare_pairwise_uncorrelated(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let nat_fn_ty = d.arrow(nat, carrier);
    let x_ty = d.arrow(nat, nat_fn_ty);
    let fn_ty = d.arrow(nat, carrier);
    let prop = d.kernel().sort_zero();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let body = pairwise_uncorrelated_body(d, p, x, m, pf, n);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_m = d.lam_fv(m_fv, nat, with_pf);
        d.lam_fv(x_fv, x_ty, with_m)
    };
    let ty = {
        let over_n = d.arrow(nat, prop);
        let over_pf = d.arrow(fn_ty, over_n);
        let over_m = d.arrow(nat, over_pf);
        d.arrow(x_ty, over_m)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.pairwise_uncorrelated,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(PAIRWISE_UNCORRELATED_HEIGHT),
    })
}

/// From `hlt : Lt a b` (over `Nat`), derive `Not (Eq a b)`: assume `heq : Eq
/// a b`, rewrite `hlt`'s type along `heq` (`Nat`-indexed [`nat_rewrite_prop`])
/// to get `Lt b b`, then close by `Nat.lt_irrefl`. `PairwiseUncorrelated`'s
/// own `Ne i j` hypothesis is exactly what [`declare_variance_sum_vars`]'s
/// successor step must manufacture from an ordinary `Lt`, since every
/// pairing it actually has on hand (`jj < j`, so `jj ≠ j`) is a strict order
/// fact, never a disequality directly.
fn ne_of_lt_nat(d: &mut IntDev<'_>, a: ExprId, b: ExprId, hlt: ExprId) -> ExprId {
    let np = d.prelude();
    let eq_ty = d.eq(a, b);
    let heq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(heq_fv);
    let lt_bb = nat_rewrite_prop(d, a, b, heq, hlt, &|d, x| d.lt(x, b));
    let false_proof = d.lemma(np.lt_irrefl, &[b, lt_bb]);
    d.lam_fv(heq_fv, eq_ty, false_proof)
}

/// `Eq Rat (variance (const_fn zero) p n) zero`, for ANY `p`, `n` (no
/// `IsDistribution` needed) — the base case
/// [`declare_variance_sum_vars`] needs, since `sumVars X Nat.zero` ι-reduces
/// to `const_fn zero` exactly as [`declare_expectation_sum_vars`]'s and
/// [`declare_covariance_sum_vars_left`]'s own base cases document. Returns
/// `(const_fn zero, proof)`.
///
/// [`expectation_zero_eq_zero`] collapses the mean `E[0]` to `zero`
/// unconditionally; substituting that into `variance`'s own definition
/// (`E[(X−E[X])²]`) leaves `E[(0−0)·(0−0)]`, itself a sum of
/// pointwise-zero (via [`RatPrelude::sub_self`] then [`rat_zero_mul`] twice)
/// terms — closed by [`RatPrelude::sum_range_eq_zero_of_lt`] rather than
/// [`sum_range_const`]/[`RatPrelude::mul_zero`], since the summand here is
/// not literally the constant-zero function (only pointwise equal to it).
fn variance_of_const_zero_eq_zero(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    pf: ExprId,
    n: ExprId,
) -> (ExprId, ExprId) {
    let nat = d.nat_ty();
    let zero_r = rzero(d, p);
    let (const_zero, mu_eq) = expectation_zero_eq_zero(d, p, pf, n);
    // mu_eq : Eq(expectation(const_zero, pf, n), zero_r)
    let mu_r = expectation(d, p, const_zero, pf, n);

    let summand_mu = variance_summand(d, p, const_zero, mu_r);
    let e_summand_mu = expectation(d, p, summand_mu, pf, n);
    // e_summand_mu ~ variance(const_zero, pf, n)                      [defeq]

    let vs_zero_zero = variance_summand(d, p, const_zero, zero_r);
    let e_vs_zero_zero = expectation(d, p, vs_zero_zero, pf, n);
    let step_a = rcongr(d, mu_r, zero_r, mu_eq, &|d, t| {
        let vs = variance_summand(d, p, const_zero, t);
        expectation(d, p, vs, pf, n)
    });
    // step_a : Eq(e_summand_mu, e_vs_zero_zero)

    let weighted_vs = weighted(d, vs_zero_zero, pf);
    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let klt_fv = d.fresh_fvar();
        let klt_ty = d.lt(k, n);

        let const_zero_k = d.apply(const_zero, &[k]);
        let gap = rsub(d, p, const_zero_k, zero_r);
        let gap_zero = d.lemma(p.sub_self, &[zero_r]);
        let vs_k = rmul(d, gap, gap);
        let zz = rmul(d, zero_r, zero_r);
        let step1 = rcongr(d, gap, zero_r, gap_zero, &|d, t| rmul(d, t, t));
        let step2 = rat_zero_mul(d, p, zero_r);
        let (_e, vs_k_zero) = rchain(d, vs_k, &[(zz, step1), (zero_r, step2)]);

        let pk = d.apply(pf, &[k]);
        let weighted_vs_k = rmul(d, vs_k, pk);
        let zero_pk = rmul(d, zero_r, pk);
        let step3 = rcongr(d, vs_k, zero_r, vs_k_zero, &|d, t| rmul(d, t, pk));
        let step4 = rat_zero_mul(d, p, pk);
        let (_e2, weighted_vs_k_zero) =
            rchain(d, weighted_vs_k, &[(zero_pk, step3), (zero_r, step4)]);

        let with_klt = d.lam_fv(klt_fv, klt_ty, weighted_vs_k_zero);
        d.lam_fv(k_fv, nat, with_klt)
    };
    let step_b = d.lemma(p.sum_range_eq_zero_of_lt, &[weighted_vs, n, pointwise]);
    // step_b : Eq(sumRange(weighted_vs, n), zero_r) ~ Eq(e_vs_zero_zero, zero_r) [defeq]

    let final_proof = rtrans(d, e_summand_mu, e_vs_zero_zero, zero_r, step_a, step_b);
    (const_zero, final_proof)
}

/// `Rat.variance_sumVars : ∀ X p n, IsDistribution p n → ∀ m,
/// PairwiseUncorrelated X m p n → variance (sumVars X m) p n = sumRange (fun
/// j => variance (X j) p n) m` — **the headline**: `Var[Σ_{j<m} X_j] =
/// Σ_{j<m} Var[X_j]` under pairwise uncorrelatedness. Two prior lanes stopped
/// one lemma short of this — `Rat.sumRange_eq_zero_of_lt`
/// (`rat_prelude::sum`) is that lemma.
///
/// Induction on `m`. **Base case**: [`variance_of_const_zero_eq_zero`],
/// using `sumVars X 0`'s ι-reduction to `const_fn zero`.
///
/// **Successor step**: weaken `h : PairwiseUncorrelated X (succ j) p n` to
/// `PairwiseUncorrelated X j p n` (lifting both index bounds via
/// `Nat.lt_of_lt_of_le`/`Nat.le_succ`, the same weakening
/// [`declare_sum_range_le`](super::sum) and every bounded induction in this
/// prelude uses) to feed the inductive hypothesis. The cross term
/// `Cov[sumVars X j, X j]` needed for
/// [`RatPrelude::variance_add_of_uncorrelated`] is derived, not assumed:
/// [`RatPrelude::covariance_sum_vars_left`] reduces it to `sumRange (fun jj
/// => Cov[X jj, X j]) j`, and every term of that sum is zero by `h` applied
/// at `(jj, j)` — `jj < j` gives `jj < succ j` (weakened) and `jj ≠ j` (via
/// [`ne_of_lt_nat`]), `j < succ j` is [`RatPrelude`]'s own `lt_succ_self` —
/// so [`RatPrelude::sum_range_eq_zero_of_lt`] collapses the sum, exactly the
/// prerequisite this repository's `sumRange_congr` (unrestricted) could
/// never supply. `sumVars X (succ j)`'s ι-reduction to `combined (sumVars X
/// j) (X j)` then lands `variance_add_of_uncorrelated`'s conclusion
/// definitionally on `sumRange (…) (succ j)`.
fn declare_variance_sum_vars(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
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
    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let dist_ty = is_distribution(d, p, pf, n);

    let var_of_x = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let xj = d.apply(x, &[j]);
        let vxj = variance(d, p, xj, pf, n);
        d.lam_fv(j_fv, nat, vxj)
    };

    let motive = |d: &mut IntDev<'_>, bound: ExprId| -> ExprId {
        let hpw = pairwise_uncorrelated(d, p, x, bound, pf, n);
        let sv = sum_vars_fn(d, p, x, bound);
        let lhs = variance(d, p, sv, pf, n);
        let rhs = rsum_range(d, p, var_of_x, bound);
        let concl = req(d, lhs, rhs);
        d.arrow(hpw, concl)
    };
    let stmt = motive(d, m);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_n = d.zero();
            let hpw_ty = pairwise_uncorrelated_body(d, p, x, zero_n, pf, n);
            let h_fv = d.fresh_fvar();
            let (_cz, vzero_proof) = variance_of_const_zero_eq_zero(d, p, pf, n);
            d.lam_fv(h_fv, hpw_ty, vzero_proof)
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let hpw_ty = pairwise_uncorrelated_body(d, p, x, sj, pf, n);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let np = d.prelude();

            // h_at_j : PairwiseUncorrelated X j p n, weakened from `h`.
            let h_at_j = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let jj_fv = d.fresh_fvar();
                let jj = d.kernel().fvar(jj_fv);
                let hi_ty = d.lt(i, j);
                let hi_fv = d.fresh_fvar();
                let hi = d.kernel().fvar(hi_fv);
                let hjj_ty = d.lt(jj, j);
                let hjj_fv = d.fresh_fvar();
                let hjj = d.kernel().fvar(hjj_fv);
                let eq_i_jj = d.eq(i, jj);
                let hne_ty = d.not(eq_i_jj);
                let hne_fv = d.fresh_fvar();
                let hne = d.kernel().fvar(hne_fv);

                let le_succ_j = d.lemma(np.le_succ, &[j]);
                let hi_lifted = d.lemma(np.lt_of_lt_of_le, &[i, j, sj, hi, le_succ_j]);
                let le_succ_j2 = d.lemma(np.le_succ, &[j]);
                let hjj_lifted = d.lemma(np.lt_of_lt_of_le, &[jj, j, sj, hjj, le_succ_j2]);
                let applied = d.apply(h, &[i, jj, hi_lifted, hjj_lifted, hne]);

                let with_hne = d.lam_fv(hne_fv, hne_ty, applied);
                let with_hjj = d.lam_fv(hjj_fv, hjj_ty, with_hne);
                let with_hi = d.lam_fv(hi_fv, hi_ty, with_hjj);
                let with_jj = d.lam_fv(jj_fv, nat, with_hi);
                d.lam_fv(i_fv, nat, with_jj)
            };
            let ih_applied = d.apply(ih, &[h_at_j]);
            // ih_applied : Eq(variance(sumVars X j,p,n), sumRange(var_of_x,j))

            let sv_j = sum_vars_fn(d, p, x, j);
            let x_j = d.apply(x, &[j]);
            let combined_fn = combined(d, sv_j, x_j);

            // hcov : Eq(covariance(sumVars X j, X j, p, n), zero)
            let cov_of_x_j = {
                let jj_fv = d.fresh_fvar();
                let jj = d.kernel().fvar(jj_fv);
                let x_jj = d.apply(x, &[jj]);
                let cov = covariance(d, p, x_jj, x_j, pf, n);
                d.lam_fv(jj_fv, nat, cov)
            };
            let zero_r = rzero(d, p);
            let cov_sv_j_lemma = d.lemma(p.covariance_sum_vars_left, &[x, x_j, pf, n, j]);
            // cov_sv_j_lemma : Eq(covariance(sv_j,x_j,p,n), sumRange(cov_of_x_j,j))

            let pointwise_cov_zero = {
                let jj_fv = d.fresh_fvar();
                let jj = d.kernel().fvar(jj_fv);
                let hjj_lt_fv = d.fresh_fvar();
                let hjj_lt_ty = d.lt(jj, j);
                let hjj_lt = d.kernel().fvar(hjj_lt_fv);

                let hjj_lt_sj = {
                    let le_succ_j3 = d.lemma(np.le_succ, &[j]);
                    d.lemma(np.lt_of_lt_of_le, &[jj, j, sj, hjj_lt, le_succ_j3])
                };
                let hj_lt_sj = d.lemma(np.lt_succ_self, &[j]);
                let hne_jj_j = ne_of_lt_nat(d, jj, j, hjj_lt);

                let cov_zero = d.apply(h, &[jj, j, hjj_lt_sj, hj_lt_sj, hne_jj_j]);
                // cov_zero : Eq(covariance(X jj, x_j, p, n), zero) ~ Eq(cov_of_x_j jj, zero) [defeq]

                let with_hjj_lt = d.lam_fv(hjj_lt_fv, hjj_lt_ty, cov_zero);
                d.lam_fv(jj_fv, nat, with_hjj_lt)
            };
            let sum_eq_zero = d.lemma(
                p.sum_range_eq_zero_of_lt,
                &[cov_of_x_j, j, pointwise_cov_zero],
            );
            // sum_eq_zero : Eq(sumRange(cov_of_x_j,j), zero)

            let cov_svj_xj = covariance(d, p, sv_j, x_j, pf, n);
            let sum_j_expr = rsum_range(d, p, cov_of_x_j, j);
            let hcov = rtrans(
                d,
                cov_svj_xj,
                sum_j_expr,
                zero_r,
                cov_sv_j_lemma,
                sum_eq_zero,
            );

            let headline = d.lemma(
                p.variance_add_of_uncorrelated,
                &[sv_j, x_j, pf, n, hd, hcov],
            );
            // headline : Eq(variance(combined_fn,p,n), add(variance(sv_j,p,n), variance(x_j,p,n)))

            let var_svj = variance(d, p, sv_j, pf, n);
            let var_xj = variance(d, p, x_j, pf, n);
            let sum_j2 = rsum_range(d, p, var_of_x, j);
            let mid = radd(d, var_svj, var_xj);
            let end = radd(d, sum_j2, var_xj);
            let lift_ih = rcongr(d, var_svj, sum_j2, ih_applied, &|d, t| radd(d, t, var_xj));

            let lhs_expr = variance(d, p, combined_fn, pf, n);
            let final_chain = rtrans(d, lhs_expr, mid, end, headline, lift_ih);

            d.lam_fv(h_fv, hpw_ty, final_chain)
        },
        m,
    );

    let value = {
        let with_m = d.lam_fv(m_fv, nat, proof);
        let with_hd = d.lam_fv(hd_fv, dist_ty, with_m);
        let with_n = d.lam_fv(n_fv, nat, with_hd);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        d.lam_fv(x_fv, x_ty, with_pf)
    };
    let ty = {
        let with_m = d.pi_fv(m_fv, nat, stmt);
        let with_hd = d.arrow(dist_ty, with_m);
        let with_n = d.pi_fv(n_fv, nat, with_hd);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        d.pi_fv(x_fv, x_ty, with_pf)
    };
    d.declare_theorem(p.variance_sum_vars, ty, value)
}

/// `Rat.variance_scaled_mean : ∀ X p n m, IsDistribution p n →
/// variance (fun k => inv (natDivSucc m 0) * X k) p n = (inv (natDivSucc m
/// 0) * inv (natDivSucc m 0)) * variance X p n` — `Var[a·X] = a²·Var[X]`
/// specialised at the sample-mean scalar `a := 1/m` (`Rat.uniform`'s own
/// weight, `inv (natDivSucc m 0)`). `X` is generic (any `Nat → Rat`
/// sequence, not tied to `Rat.sumVars`), so a caller applies this at `X :=
/// sumVars X' m` for the sample-mean-of-a-sum reading.
///
/// A direct corollary of [`RatPrelude::variance_smul`], not a new proof:
/// **unlike ℝ, `Rat.inv` is TOTAL (`inv zero = zero`) and ℚ's order is
/// decidable, so there is no witnessed-modulus obstruction** — verified
/// here, not assumed, by the fact that [`RatPrelude::variance_smul`] itself
/// carries no hypothesis on its scalar `a`. This holds for EVERY `m`,
/// including `m = 0` (where `a` collapses to `zero` and both sides collapse
/// to `zero`), with no `m ≠ 0` side condition anywhere.
fn declare_variance_scaled_mean(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);

    let dist_ty = is_distribution(d, p, pf, n);
    let m_as_rat = nat_as_rat(d, p, m);
    let a = d.const_app(p.inv, &[m_as_rat]);
    let scaled_x = scale_fn(d, a, x);
    let variance_ax = variance(d, p, scaled_x, pf, n);
    let variance_x = variance(d, p, x, pf, n);
    let a_sq = rmul(d, a, a);
    let rhs = rmul(d, a_sq, variance_x);
    let concl = req(d, variance_ax, rhs);

    let proof = d.lemma(p.variance_smul, &[a, x, pf, n, hd]);

    let value = {
        let with_hd = d.lam_fv(hd_fv, dist_ty, proof);
        let with_m = d.lam_fv(m_fv, nat, with_hd);
        let with_n = d.lam_fv(n_fv, nat, with_m);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        d.lam_fv(x_fv, fn_ty, with_pf)
    };
    let ty = {
        let with_hd = d.arrow(dist_ty, concl);
        let with_m = d.pi_fv(m_fv, nat, with_hd);
        let with_n = d.pi_fv(n_fv, nat, with_m);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        d.pi_fv(x_fv, fn_ty, with_pf)
    };
    d.declare_theorem(p.variance_scaled_mean, ty, value)
}

/// `Rat.chebyshev_sampleMean_uncorrelated : ∀ X eps p n m, IsDistribution p
/// n → PairwiseUncorrelated X m p n → lt zero eps → le ((eps times eps)
/// times expectation (Rat.indicator (eps times eps) (fun k => (Y k minus
/// expectation Y p n) times (Y k minus expectation Y p n))) p n) ((a times
/// a) times sumRange (fun j => variance (X j) p n) m)`, where `Y := fun k
/// => a times sumVars X m k` and `a := inv (natDivSucc m 0)` —
/// [`RatPrelude::chebyshev_inequality`] applied to the SAMPLE MEAN of `m`
/// pairwise-uncorrelated variables, in the same multiplied-through form
/// `chebyshev_inequality` itself uses (the only `Rat.inv` here is the SAME
/// scaling factor already needed to state a mean at all, not a division
/// introduced by this theorem).
///
/// Composes three already-proved facts, no new proof technique:
/// [`RatPrelude::chebyshev_inequality`] applied directly to `Y`;
/// [`RatPrelude::variance_scaled_mean`] rewriting `Var[Y]` to `a²·Var[Σ]`;
/// [`RatPrelude::variance_sum_vars`] rewriting `Var[Σ]` to `Σ_{j<m}
/// Var[X_j]` (needing the `PairwiseUncorrelated` hypothesis this theorem
/// carries for exactly that reason).
///
/// **Not the classical `P(|X̄ − μ| ≥ ε) ≤ Var/(mε²)`.** That form assumes
/// IDENTICALLY distributed variables, collapsing `Σ_{j<m} Var[X_j]` to
/// `m·v`; this development has no such hypothesis (only pairwise
/// uncorrelatedness — see [`RatPrelude::covariance`]'s own doc on why there
/// is no independence predicate here either), so the bound is left with the
/// SUM `Σ_{j<m} Var[X_j]` exactly as [`RatPrelude::variance_sum_vars`]
/// produces it, over whatever variance each `X_j` actually has.
fn declare_chebyshev_sample_mean_uncorrelated(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);
    let nat_fn_ty = d.arrow(nat, carrier);
    let x_ty = d.arrow(nat, nat_fn_ty);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let eps_fv = d.fresh_fvar();
    let eps = d.kernel().fvar(eps_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);
    let hpw_fv = d.fresh_fvar();
    let hpw = d.kernel().fvar(hpw_fv);
    let heps_fv = d.fresh_fvar();
    let heps = d.kernel().fvar(heps_fv);

    let dist_ty = is_distribution(d, p, pf, n);
    let hpw_ty = pairwise_uncorrelated(d, p, x, m, pf, n);
    let zero_r = rzero(d, p);
    let heps_ty = rlt(d, p, zero_r, eps);

    let sv = sum_vars_fn(d, p, x, m);
    let m_as_rat = nat_as_rat(d, p, m);
    let a = d.const_app(p.inv, &[m_as_rat]);
    let y = scale_fn(d, a, sv);

    let var_of_x = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let xj = d.apply(x, &[j]);
        let vxj = variance(d, p, xj, pf, n);
        d.lam_fv(j_fv, nat, vxj)
    };

    let a_sq = rmul(d, a, a);
    let sum_var = rsum_range(d, p, var_of_x, m);
    let rhs = rmul(d, a_sq, sum_var);

    let mu_y = expectation(d, p, y, pf, n);
    let dev_y = variance_summand(d, p, y, mu_y);
    let eps_sq = rmul(d, eps, eps);
    let ind_y = d.const_app(p.indicator, &[eps_sq, dev_y]);
    let e_ind_y = expectation(d, p, ind_y, pf, n);
    let lhs = rmul(d, eps_sq, e_ind_y);
    let concl = rle(d, p, lhs, rhs);

    let cheb = d.lemma(p.chebyshev_inequality, &[eps, y, pf, n, hd, heps]);
    // cheb : le lhs (variance(y, pf, n))

    let vsm = d.lemma(p.variance_scaled_mean, &[sv, pf, n, m, hd]);
    // vsm : Eq(variance(scale_fn(a,sv),pf,n), a_sq*variance(sv,pf,n))
    //     ~ Eq(variance(y,pf,n), a_sq*variance(sv,pf,n))               [defeq]

    let vsv = d.lemma(p.variance_sum_vars, &[x, pf, n, hd, m, hpw]);
    // vsv : Eq(variance(sv,pf,n), sum_var)

    let var_sv = variance(d, p, sv, pf, n);
    let rw = rcongr(d, var_sv, sum_var, vsv, &|d, t| rmul(d, a_sq, t));
    // rw : Eq(a_sq*var_sv, rhs)

    let a_sq_var_sv = rmul(d, a_sq, var_sv);
    let var_y = variance(d, p, y, pf, n);
    let combined_eq = rtrans(d, var_y, a_sq_var_sv, rhs, vsm, rw);
    // combined_eq : Eq(var_y, rhs)

    let final_proof = rat_eq_rewrite(d, var_y, rhs, combined_eq, cheb, &|d, t| rle(d, p, lhs, t));

    let value = {
        let with_heps = d.lam_fv(heps_fv, heps_ty, final_proof);
        let with_hpw = d.lam_fv(hpw_fv, hpw_ty, with_heps);
        let with_hd = d.lam_fv(hd_fv, dist_ty, with_hpw);
        let with_m = d.lam_fv(m_fv, nat, with_hd);
        let with_n = d.lam_fv(n_fv, nat, with_m);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_eps = d.lam_fv(eps_fv, carrier, with_pf);
        d.lam_fv(x_fv, x_ty, with_eps)
    };
    let ty = {
        let with_heps = d.arrow(heps_ty, concl);
        let with_hpw = d.arrow(hpw_ty, with_heps);
        let with_hd = d.arrow(dist_ty, with_hpw);
        let with_m = d.pi_fv(m_fv, nat, with_hd);
        let with_n = d.pi_fv(n_fv, nat, with_m);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        let with_eps = d.pi_fv(eps_fv, carrier, with_pf);
        d.pi_fv(x_fv, x_ty, with_eps)
    };
    d.declare_theorem(p.chebyshev_sample_mean_uncorrelated, ty, value)
}

/// `Rat.variance_sampleMean_uncorrelated : ∀ X p n, IsDistribution p n → ∀
/// m, PairwiseUncorrelated X m p n → variance (fun k => inv (natDivSucc m 0)
/// times sumVars X m k) p n = (inv (natDivSucc m 0) times inv (natDivSucc m
/// 0)) times sumRange (fun j => variance (X j) p n) m` — **the quantitative
/// heart of the weak law of large numbers, named on its own**: the variance
/// of the sample mean of `m` pairwise-uncorrelated variables is `(1/m)²
/// times Σ_{j<m} Var[X_j]`.
///
/// [`RatPrelude::variance_sumVars`] alone does NOT give this: it gives
/// `Var[Σ_j X_j] = Σ_j Var[X_j]` for the unscaled SUM, not the sample MEAN
/// (which divides the sum by `m`). This theorem is exactly the composition
/// [`RatPrelude::chebyshev_sample_mean_uncorrelated`] already builds
/// internally as its own `combined_eq` — [`RatPrelude::variance_scaled_mean`]
/// rewriting `Var[a·Σ] = a²·Var[Σ]` at `a := inv (natDivSucc m 0)`, then
/// [`RatPrelude::variance_sumVars`] rewriting `Var[Σ]` — now exposed as a
/// standalone, freestanding result rather than a step buried inside a larger
/// Chebyshev bound. No new proof technique; every lemma call here is a call
/// [`declare_chebyshev_sample_mean_uncorrelated`] already makes.
fn declare_variance_sample_mean_uncorrelated(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
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

    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);
    let hpw_fv = d.fresh_fvar();
    let hpw = d.kernel().fvar(hpw_fv);

    let dist_ty = is_distribution(d, p, pf, n);
    let hpw_ty = pairwise_uncorrelated(d, p, x, m, pf, n);

    let sv = sum_vars_fn(d, p, x, m);
    let m_as_rat = nat_as_rat(d, p, m);
    let a = d.const_app(p.inv, &[m_as_rat]);
    let y = scale_fn(d, a, sv);

    let var_of_x = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let xj = d.apply(x, &[j]);
        let vxj = variance(d, p, xj, pf, n);
        d.lam_fv(j_fv, nat, vxj)
    };

    let a_sq = rmul(d, a, a);
    let sum_var = rsum_range(d, p, var_of_x, m);
    let rhs = rmul(d, a_sq, sum_var);

    let var_y = variance(d, p, y, pf, n);
    let concl = req(d, var_y, rhs);

    let vsm = d.lemma(p.variance_scaled_mean, &[sv, pf, n, m, hd]);
    // vsm : Eq(variance(scale_fn(a,sv),pf,n), a_sq*variance(sv,pf,n))
    //     ~ Eq(var_y, a_sq*variance(sv,pf,n))                          [defeq]

    let vsv = d.lemma(p.variance_sum_vars, &[x, pf, n, hd, m, hpw]);
    // vsv : Eq(variance(sv,pf,n), sum_var)

    let var_sv = variance(d, p, sv, pf, n);
    let rw = rcongr(d, var_sv, sum_var, vsv, &|d, t| rmul(d, a_sq, t));
    // rw : Eq(a_sq*var_sv, rhs)

    let a_sq_var_sv = rmul(d, a_sq, var_sv);
    let combined_eq = rtrans(d, var_y, a_sq_var_sv, rhs, vsm, rw);
    // combined_eq : Eq(var_y, rhs)

    let value = {
        let with_hpw = d.lam_fv(hpw_fv, hpw_ty, combined_eq);
        let with_m = d.lam_fv(m_fv, nat, with_hpw);
        let with_hd = d.lam_fv(hd_fv, dist_ty, with_m);
        let with_n = d.lam_fv(n_fv, nat, with_hd);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        d.lam_fv(x_fv, x_ty, with_pf)
    };
    let ty = {
        let with_hpw = d.arrow(hpw_ty, concl);
        let with_m = d.pi_fv(m_fv, nat, with_hpw);
        let with_hd = d.arrow(dist_ty, with_m);
        let with_n = d.pi_fv(n_fv, nat, with_hd);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        d.pi_fv(x_fv, x_ty, with_pf)
    };
    d.declare_theorem(p.variance_sample_mean_uncorrelated, ty, value)
}

/// `Rat.weak_law_of_large_numbers` — **a renaming, not a new result**:
/// registered under the name a reader searching for "the weak law of large
/// numbers" will actually look for. The type is IDENTICAL to
/// [`RatPrelude::chebyshev_sample_mean_uncorrelated`]'s, and the proof is a
/// direct forward to that theorem — nothing new is proved here, and nothing
/// about the statement changes.
///
/// This IS the weak law of large numbers, in the standard finite-sample
/// Chebyshev-bound shape the classical proof of the law goes through: for
/// `m` pairwise-uncorrelated variables `X_0, …, X_{m-1}` over a distribution
/// `p`, `ε²·E[𝟙(ε² ≤ (M − E[M])²)] ≤ Var[M]` where `M` is the sample mean —
/// i.e. the (ε²-weighted) probability mass where the sample mean deviates
/// from its expectation by at least `ε` is bounded by `Var[M] = (1/m)² ·
/// Σ_{j<m} Var[X_j]` ([`RatPrelude::variance_sample_mean_uncorrelated`]),
/// which shrinks as `m` grows whenever the individual variances stay
/// bounded — exactly the content the classical statement asserts as a
/// limit, stated here at each finite `m` rather than as a limit statement.
///
/// **Not the classical i.i.d. form** `P(|X̄ − μ| ≥ ε) ≤ Var/(mε²)`: this
/// development assumes only pairwise uncorrelatedness (see
/// [`RatPrelude::covariance`]'s own doc on why there is no independence
/// predicate here), so the bound is left with the SUM `Σ_{j<m} Var[X_j]`
/// rather than collapsed to `m·σ²` under a common-variance hypothesis — a
/// strictly MORE general statement than the textbook one, not a weaker one.
fn declare_weak_law_of_large_numbers(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);
    let nat_fn_ty = d.arrow(nat, carrier);
    let x_ty = d.arrow(nat, nat_fn_ty);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let eps_fv = d.fresh_fvar();
    let eps = d.kernel().fvar(eps_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);
    let hpw_fv = d.fresh_fvar();
    let hpw = d.kernel().fvar(hpw_fv);
    let heps_fv = d.fresh_fvar();
    let heps = d.kernel().fvar(heps_fv);

    let dist_ty = is_distribution(d, p, pf, n);
    let hpw_ty = pairwise_uncorrelated(d, p, x, m, pf, n);
    let zero_r = rzero(d, p);
    let heps_ty = rlt(d, p, zero_r, eps);

    let sv = sum_vars_fn(d, p, x, m);
    let m_as_rat = nat_as_rat(d, p, m);
    let a = d.const_app(p.inv, &[m_as_rat]);
    let y = scale_fn(d, a, sv);

    let var_of_x = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let xj = d.apply(x, &[j]);
        let vxj = variance(d, p, xj, pf, n);
        d.lam_fv(j_fv, nat, vxj)
    };

    let a_sq = rmul(d, a, a);
    let sum_var = rsum_range(d, p, var_of_x, m);
    let rhs = rmul(d, a_sq, sum_var);

    let mu_y = expectation(d, p, y, pf, n);
    let dev_y = variance_summand(d, p, y, mu_y);
    let eps_sq = rmul(d, eps, eps);
    let ind_y = d.const_app(p.indicator, &[eps_sq, dev_y]);
    let e_ind_y = expectation(d, p, ind_y, pf, n);
    let lhs = rmul(d, eps_sq, e_ind_y);
    let concl = rle(d, p, lhs, rhs);

    let forward = d.lemma(
        p.chebyshev_sample_mean_uncorrelated,
        &[x, eps, pf, n, m, hd, hpw, heps],
    );

    let value = {
        let with_heps = d.lam_fv(heps_fv, heps_ty, forward);
        let with_hpw = d.lam_fv(hpw_fv, hpw_ty, with_heps);
        let with_hd = d.lam_fv(hd_fv, dist_ty, with_hpw);
        let with_m = d.lam_fv(m_fv, nat, with_hd);
        let with_n = d.lam_fv(n_fv, nat, with_m);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_eps = d.lam_fv(eps_fv, carrier, with_pf);
        d.lam_fv(x_fv, x_ty, with_eps)
    };
    let ty = {
        let with_heps = d.arrow(heps_ty, concl);
        let with_hpw = d.arrow(hpw_ty, with_heps);
        let with_hd = d.arrow(dist_ty, with_hpw);
        let with_m = d.pi_fv(m_fv, nat, with_hd);
        let with_n = d.pi_fv(n_fv, nat, with_m);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        let with_eps = d.pi_fv(eps_fv, carrier, with_pf);
        d.pi_fv(x_fv, x_ty, with_eps)
    };
    d.declare_theorem(p.weak_law_of_large_numbers, ty, value)
}

// --- Bernoulli's law of large numbers (rat_prelude::probability, Rado lane) -
//
// The instance: `n` pairwise-uncorrelated indicator variables sharing one
// expectation `q` (a common Bernoulli parameter). Assembled from
// `weak_law_of_large_numbers` (the general theorem, above),
// `variance_indicator` (step 1 — each variable's variance is `q(1-q)`) and
// `variance_indicator_le_quarter` (step 2 — `4q(1-q) ≤ 1`), so nothing here
// re-proves either.

/// `fun j => Rat.indicator (A j) (Y j)` — a family of Bernoulli variables,
/// one per index `j`, each thresholding its own underlying sequence `Y j`
/// against its own threshold `A j`.
fn bernoulli_family(d: &mut IntDev<'_>, p: RatPrelude, cap_a: ExprId, cap_y: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let aj = d.apply(cap_a, &[j]);
    let yj = d.apply(cap_y, &[j]);
    let body = d.const_app(p.indicator, &[aj, yj]);
    d.lam_fv(j_fv, nat, body)
}

/// `Eq Rat (mul a (sub one a)) (add a (neg (mul a a)))` — `a·(1−a) = a − a²`,
/// via `left_distrib` (`a*(one+neg_a) = a*one + a*neg_a`), `mul_one` and
/// `mul_neg`. The distributivity bridge between [`declare_variance_indicator`]'s
/// `p(1−p)` output and [`declare_variance_indicator_le_quarter`]'s `q−q²`
/// input shape — the two are related by an actual ring law, not a
/// definitional unfolding, so this cannot be skipped.
fn mul_one_minus_eq_sub_sq(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId) -> ExprId {
    let one_r = rone(d, p);
    let neg_a = rneg(d, a);
    let step1 = d.lemma(p.left_distrib, &[a, one_r, neg_a]);
    let a_one = rmul(d, a, one_r);
    let a_nega = rmul(d, a, neg_a);
    let after1 = radd(d, a_one, a_nega);

    let mul_one_step = d.lemma(p.mul_one, &[a]);
    let a_congr = rcongr(d, a_one, a, mul_one_step, &|d, t| radd(d, t, a_nega));
    let after2 = radd(d, a, a_nega);

    let aa = rmul(d, a, a);
    let neg_aa = rneg(d, aa);
    let mul_neg_step = d.lemma(p.mul_neg, &[a, a]);
    let b_congr = rcongr(d, a_nega, neg_aa, mul_neg_step, &|d, t| radd(d, a, t));
    let after3 = radd(d, a, neg_aa);

    let one_minus_a = rsub(d, p, one_r, a);
    let start = rmul(d, a, one_minus_a);
    let (_e, chained) = rchain(
        d,
        start,
        &[(after1, step1), (after2, a_congr), (after3, b_congr)],
    );
    chained
}

/// `Eq Rat (mul four (mul q (sub one q))) (sub (mul four q) (mul four (mul q
/// q)))` — `4·q(1−q) = 4q − 4q²`, the shape
/// [`declare_variance_indicator_le_quarter`]'s conclusion is already in,
/// reached from [`declare_variance_indicator`]'s `p(1−p)` output via
/// [`mul_one_minus_eq_sub_sq`] then one more `left_distrib` to pull `four`
/// through the resulting difference.
fn four_mul_one_minus_eq(d: &mut IntDev<'_>, p: RatPrelude, four_r: ExprId, q: ExprId) -> ExprId {
    let one_r = rone(d, p);
    let one_minus_q = rsub(d, p, one_r, q);
    let w = rmul(d, q, one_minus_q);
    let start = rmul(d, four_r, w);

    let w_eq = mul_one_minus_eq_sub_sq(d, p, q); // Eq(w, add(q, neg(qq)))
    let qq = rmul(d, q, q);
    let neg_qq = rneg(d, qq);
    let q_minus_qq = radd(d, q, neg_qq);
    let step1 = rcongr(d, w, q_minus_qq, w_eq, &|d, t| rmul(d, four_r, t));
    let after1 = rmul(d, four_r, q_minus_qq);

    let step2 = d.lemma(p.left_distrib, &[four_r, q, neg_qq]);
    let four_q = rmul(d, four_r, q);
    let four_negqq = rmul(d, four_r, neg_qq);
    let after2 = radd(d, four_q, four_negqq);

    let mul_neg_step = d.lemma(p.mul_neg, &[four_r, qq]);
    let four_qq = rmul(d, four_r, qq);
    let neg_four_qq = rneg(d, four_qq);
    let step3 = rcongr(d, four_negqq, neg_four_qq, mul_neg_step, &|d, t| {
        radd(d, four_q, t)
    });
    let after3 = radd(d, four_q, neg_four_qq);

    let (_e, chained) = rchain(
        d,
        start,
        &[(after1, step1), (after2, step2), (after3, step3)],
    );
    chained
}

/// `Eq Rat (mul a (mul b c)) (mul b (mul a c))` — commuting the OUTER factor
/// of a right-associated triple product past the inner one, via `mul_assoc`
/// (twice) and `mul_comm` (once): `a*(b*c) = (a*b)*c = (b*a)*c = b*(a*c)`.
fn left_commute(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
    let bc = rmul(d, b, c);
    let start = rmul(d, a, bc);

    let assoc1 = d.lemma(p.mul_assoc, &[a, b, c]); // Eq((a*b)*c, a*(b*c))
    let ab = rmul(d, a, b);
    let ab_c = rmul(d, ab, c);
    let step1 = rsymm(d, ab_c, start, assoc1); // Eq(start, ab_c)

    let comm = d.lemma(p.mul_comm, &[a, b]); // Eq(a*b, b*a)
    let ba = rmul(d, b, a);
    let step2 = rcongr(d, ab, ba, comm, &|d, t| rmul(d, t, c));
    let ba_c = rmul(d, ba, c);

    let assoc2 = d.lemma(p.mul_assoc, &[b, a, c]); // Eq((b*a)*c, b*(a*c))
    let ac = rmul(d, a, c);
    let target = rmul(d, b, ac);

    let (_e, chained) = rchain(d, start, &[(ab_c, step1), (ba_c, step2), (target, assoc2)]);
    chained
}

/// `Eq Rat zero four` companion: `le zero four`, built from `zero_lt_one`
/// (`0 ≤ 1`, via `le_of_lt`) doubled twice with `add_nonneg` — `four :=
/// ((1+1)+1)+1` is never negative, no matter how it is built.
fn four_nonneg(d: &mut IntDev<'_>, p: RatPrelude) -> (ExprId, ExprId) {
    let one_r = rone(d, p);
    let zero_r = rzero(d, p);
    let zlt1 = d.lemma(p.zero_lt_one, &[]);
    let h1 = d.lemma(p.le_of_lt, &[zero_r, one_r, zlt1]); // le zero one_r

    let two_r = radd(d, one_r, one_r);
    let h2 = d.lemma(p.add_nonneg, &[one_r, one_r, h1, h1]); // le zero two_r

    let three_r = radd(d, two_r, one_r);
    let h3 = d.lemma(p.add_nonneg, &[two_r, one_r, h2, h1]); // le zero three_r

    let four_r = radd(d, three_r, one_r);
    let h4 = d.lemma(p.add_nonneg, &[three_r, one_r, h3, h1]); // le zero four_r
    (four_r, h4)
}

/// `Rat.bernoulli_law_of_large_numbers` — the instance: `n` pairwise-
/// uncorrelated Bernoulli variables sharing one expectation `q`. Composes
/// [`RatPrelude::weak_law_of_large_numbers`] (scaled by the nonneg constant
/// `four`), [`RatPrelude::variance_indicator`] (each `Var[X_j] = q(1-q)`,
/// pointwise, then [`RatPrelude::sum_range_congr_lt`] +
/// `sum_range_const` collapse `Σ_{j<m} Var[X_j]` to `m·q(1-q)`) and
/// [`RatPrelude::variance_indicator_le_quarter`] (`4q(1-q) ≤ 1`, scaled by
/// the nonneg `m`): `four·(eps²·E[𝟙]) ≤ four·(a²·Σ Var[X_j]) =
/// a²·(four·Σ Var[X_j]) = a²·(four·(m·q(1-q))) = a²·(m·(four·q(1-q))) ≤
/// a²·(m·one) = a²·m`, where `a := inv(natDivSucc m 0)`.
fn declare_bernoulli_law_of_large_numbers(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);
    let cap_a_ty = fn_ty;
    let cap_y_ty = d.arrow(nat, fn_ty);

    let cap_a_fv = d.fresh_fvar();
    let cap_a = d.kernel().fvar(cap_a_fv);
    let cap_y_fv = d.fresh_fvar();
    let cap_y = d.kernel().fvar(cap_y_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let eps_fv = d.fresh_fvar();
    let eps = d.kernel().fvar(eps_fv);

    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);
    let hpw_fv = d.fresh_fvar();
    let hpw = d.kernel().fvar(hpw_fv);
    let hq_fv = d.fresh_fvar();
    let hq = d.kernel().fvar(hq_fv);
    let heps_fv = d.fresh_fvar();
    let heps = d.kernel().fvar(heps_fv);

    let x_bernoulli = bernoulli_family(d, p, cap_a, cap_y);

    let dist_ty = is_distribution(d, p, pf, n);
    let hpw_ty = pairwise_uncorrelated(d, p, x_bernoulli, m, pf, n);

    let one_r = rone(d, p);
    let hq_ty = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let jlt_ty = d.lt(j, m);
        let aj = d.apply(cap_a, &[j]);
        let yj = d.apply(cap_y, &[j]);
        let ind_aj_yj = d.const_app(p.indicator, &[aj, yj]);
        let mu_j = expectation(d, p, ind_aj_yj, pf, n);
        let eq_ty = req(d, mu_j, q);
        let inner = d.arrow(jlt_ty, eq_ty);
        d.pi_fv(j_fv, nat, inner)
    };

    let zero_r = rzero(d, p);
    let heps_ty = rlt(d, p, zero_r, eps);

    // --- reconstruct weak_law_of_large_numbers's own terms, at X := x_bernoulli
    let sv = sum_vars_fn(d, p, x_bernoulli, m);
    let m_as_rat = nat_as_rat(d, p, m);
    let a = d.const_app(p.inv, &[m_as_rat]);
    let y = scale_fn(d, a, sv);

    let var_of_x = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let xj = d.apply(x_bernoulli, &[j]);
        let vxj = variance(d, p, xj, pf, n);
        d.lam_fv(j_fv, nat, vxj)
    };

    let a_sq = rmul(d, a, a);
    let sum_var = rsum_range(d, p, var_of_x, m);
    let rhs0 = rmul(d, a_sq, sum_var);

    let mu_y = expectation(d, p, y, pf, n);
    let dev_y = variance_summand(d, p, y, mu_y);
    let eps_sq = rmul(d, eps, eps);
    let ind_y = d.const_app(p.indicator, &[eps_sq, dev_y]);
    let e_ind_y = expectation(d, p, ind_y, pf, n);
    let lhs = rmul(d, eps_sq, e_ind_y);
    let concl_stmt = rle(d, p, lhs, rhs0);
    let _ = concl_stmt; // documents wl_proof's own conclusion shape

    let wl_proof = d.lemma(
        p.weak_law_of_large_numbers,
        &[x_bernoulli, eps, pf, n, m, hd, hpw, heps],
    );
    // wl_proof : le lhs rhs0

    // --- Σ_{j<m} Var[X_j] = m_as_rat * (q*(1-q))
    let one_minus_q = rsub(d, p, one_r, q);
    let q1mq = rmul(d, q, one_minus_q);

    let pointwise = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let jlt_fv = d.fresh_fvar();
        let jlt = d.kernel().fvar(jlt_fv);
        let jlt_ty = d.lt(j, m);

        let aj = d.apply(cap_a, &[j]);
        let yj = d.apply(cap_y, &[j]);
        let ind_aj_yj = d.const_app(p.indicator, &[aj, yj]);
        let mu_j = expectation(d, p, ind_aj_yj, pf, n);

        let vi = d.lemma(p.variance_indicator, &[aj, yj, pf, n, hd]);
        // vi : Eq(variance(ind_aj_yj,pf,n), mu_j*(1-mu_j))

        let hqj = d.apply(hq, &[j, jlt]);
        // hqj : Eq(mu_j, q)

        let mu_j_one_minus = rsub(d, p, one_r, mu_j);
        let mu_j_rhs = rmul(d, mu_j, mu_j_one_minus);

        let rw = rcongr(d, mu_j, q, hqj, &|d, t| {
            let one_minus_t = rsub(d, p, one_r, t);
            rmul(d, t, one_minus_t)
        });
        // rw : Eq(mu_j_rhs, q1mq)

        let var_xj = variance(d, p, ind_aj_yj, pf, n);
        let (_e, chain) = rchain(d, var_xj, &[(mu_j_rhs, vi), (q1mq, rw)]);
        // chain : Eq(var_xj, q1mq)

        let with_jlt = d.lam_fv(jlt_fv, jlt_ty, chain);
        d.lam_fv(j_fv, nat, with_jlt)
    };

    let const_q1mq = const_fn(d, q1mq);
    let congr_step = d.lemma(p.sum_range_congr_lt, &[var_of_x, const_q1mq, m, pointwise]);
    // congr_step : Eq(sumRange(var_of_x,m), sumRange(const_q1mq,m)) ~ Eq(sum_var, sumRange(const_q1mq,m))  [defeq]

    let (_stmt_sc, proof_sc) = sum_range_const(d, p, q1mq, m);
    // proof_sc : Eq(sumRange(const_q1mq,m), m_as_rat*q1mq)

    let m_as_rat_q1mq = rmul(d, m_as_rat, q1mq);
    let sum_const_q1mq = rsum_range(d, p, const_q1mq, m);
    let (_e_sum, sum_eq) = rchain(
        d,
        sum_var,
        &[(sum_const_q1mq, congr_step), (m_as_rat_q1mq, proof_sc)],
    );
    // sum_eq : Eq(sum_var, m_as_rat_q1mq)

    // --- 4*q*(1-q) ≤ 1, in the shape variance_indicator produces
    let qb = d.lemma(p.variance_indicator_le_quarter, &[q]);
    // qb : le (sub(four_r*q, four_r*qq)) one_r
    let (four_r, four_ge0) = four_nonneg(d, p);
    let bridge = four_mul_one_minus_eq(d, p, four_r, q);
    // bridge : Eq(four_r*q1mq, sub(four_r*q,four_r*qq))
    let four_q1mq = rmul(d, four_r, q1mq);
    let qq = rmul(d, q, q);
    let four_q = rmul(d, four_r, q);
    let four_qq = rmul(d, four_r, qq);
    let sub_form = rsub(d, p, four_q, four_qq);
    let bridge_rev = rsymm(d, four_q1mq, sub_form, bridge); // Eq(sub_form, four_q1mq)
    let qb2 = rat_eq_rewrite(d, sub_form, four_q1mq, bridge_rev, qb, &|d, t| {
        rle(d, p, t, one_r)
    });
    // qb2 : le four_q1mq one_r

    // --- scale qb2 by nonneg m_as_rat, then rearrange to `four_r*sum_var ≤ m_as_rat`
    let zero_nat = d.num(0);
    let hm_nonneg = d.lemma(p.zero_le_nat_div_succ, &[m, zero_nat]);
    // hm_nonneg : le zero_r m_as_rat

    let scaled_qb2 = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[m_as_rat, four_q1mq, one_r, hm_nonneg, qb2],
    );
    // scaled_qb2 : le (m_as_rat*four_q1mq) (m_as_rat*one_r)

    let m_as_rat_one = rmul(d, m_as_rat, one_r);

    let commute1 = left_commute(d, p, m_as_rat, four_r, q1mq);
    // commute1 : Eq(m_as_rat*(four_r*q1mq), four_r*(m_as_rat*q1mq))
    let m_as_rat_four_q1mq = rmul(d, m_as_rat, four_q1mq);
    let four_m_as_rat_q1mq = rmul(d, four_r, m_as_rat_q1mq);
    let step_commute1 = rat_eq_rewrite(
        d,
        m_as_rat_four_q1mq,
        four_m_as_rat_q1mq,
        commute1,
        scaled_qb2,
        &|d, t| rle(d, p, t, m_as_rat_one),
    );
    // step_commute1 : le four_m_as_rat_q1mq (m_as_rat*one_r)

    let sum_eq_rev = rsymm(d, sum_var, m_as_rat_q1mq, sum_eq); // Eq(m_as_rat_q1mq, sum_var)
    let four_sum_var = rmul(d, four_r, sum_var);
    let step_rewrite_sum = rat_eq_rewrite(
        d,
        m_as_rat_q1mq,
        sum_var,
        sum_eq_rev,
        step_commute1,
        &|d, t| {
            let ft = rmul(d, four_r, t);
            rle(d, p, ft, m_as_rat_one)
        },
    );
    // step_rewrite_sum : le four_sum_var (m_as_rat*one_r)

    let m_one_step = d.lemma(p.mul_one, &[m_as_rat]); // Eq(m_as_rat*one_r, m_as_rat)
    let key_bound = rat_eq_rewrite(
        d,
        m_as_rat_one,
        m_as_rat,
        m_one_step,
        step_rewrite_sum,
        &|d, t| rle(d, p, four_sum_var, t),
    );
    // key_bound : le four_sum_var m_as_rat

    // --- scale wl_proof by nonneg four_r, then close via key_bound
    let scaled_wl = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[four_r, lhs, rhs0, four_ge0, wl_proof],
    );
    // scaled_wl : le (four_r*lhs) (four_r*rhs0)

    let commute2 = left_commute(d, p, four_r, a_sq, sum_var);
    // commute2 : Eq(four_r*(a_sq*sum_var), a_sq*(four_r*sum_var))
    let four_lhs = rmul(d, four_r, lhs);
    let four_rhs0 = rmul(d, four_r, rhs0);
    let a_sq_four_sum_var = rmul(d, a_sq, four_sum_var);
    let step_commute2 = rat_eq_rewrite(
        d,
        four_rhs0,
        a_sq_four_sum_var,
        commute2,
        scaled_wl,
        &|d, t| rle(d, p, four_lhs, t),
    );
    // step_commute2 : le four_lhs a_sq_four_sum_var

    let ha_sq_nonneg = d.lemma(p.sq_nonneg, &[a]); // le zero a_sq
    let scaled_key = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[a_sq, four_sum_var, m_as_rat, ha_sq_nonneg, key_bound],
    );
    // scaled_key : le (a_sq*four_sum_var) (a_sq*m_as_rat)

    let a_sq_m_as_rat = rmul(d, a_sq, m_as_rat);
    let final_proof = d.lemma(
        p.le_trans,
        &[
            four_lhs,
            a_sq_four_sum_var,
            a_sq_m_as_rat,
            step_commute2,
            scaled_key,
        ],
    );
    // final_proof : le four_lhs a_sq_m_as_rat

    let concl = rle(d, p, four_lhs, a_sq_m_as_rat);

    let value = {
        let with_heps = d.lam_fv(heps_fv, heps_ty, final_proof);
        let with_eps = d.lam_fv(eps_fv, carrier, with_heps);
        let with_hq = d.lam_fv(hq_fv, hq_ty, with_eps);
        let with_hpw = d.lam_fv(hpw_fv, hpw_ty, with_hq);
        let with_hd = d.lam_fv(hd_fv, dist_ty, with_hpw);
        let with_q = d.lam_fv(q_fv, carrier, with_hd);
        let with_m = d.lam_fv(m_fv, nat, with_q);
        let with_n = d.lam_fv(n_fv, nat, with_m);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_y = d.lam_fv(cap_y_fv, cap_y_ty, with_pf);
        d.lam_fv(cap_a_fv, cap_a_ty, with_y)
    };
    let ty = {
        let with_heps = d.arrow(heps_ty, concl);
        let with_eps = d.pi_fv(eps_fv, carrier, with_heps);
        let with_hq = d.arrow(hq_ty, with_eps);
        let with_hpw = d.arrow(hpw_ty, with_hq);
        let with_hd = d.arrow(dist_ty, with_hpw);
        let with_q = d.pi_fv(q_fv, carrier, with_hd);
        let with_m = d.pi_fv(m_fv, nat, with_q);
        let with_n = d.pi_fv(n_fv, nat, with_m);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        let with_y = d.pi_fv(cap_y_fv, cap_y_ty, with_pf);
        d.pi_fv(cap_a_fv, cap_a_ty, with_y)
    };
    d.declare_theorem(p.bernoulli_law_of_large_numbers, ty, value)
}

// --- the probabilistic Cauchy–Schwarz inequality ----------------------------
//
// `cov(X,Y)² ≤ var(X)·var(Y)`, by the discriminant argument: `Var[tX+Y] ≥ 0`
// for every rational `t` (never negative — a variance), expanded via
// `variance_add_eq`, `variance_smul` and `covariance_smul_left` into a
// quadratic in `t` with coefficients `variance X p n`, `covariance X Y p n`,
// `variance Y p n`. `declare_variance_scaled_add_nonneg` is that expansion,
// named once so both the main case (`variance X p n ≠ 0`, instantiate at
// `t := −cov·inv(var X)`) and the role-swapped case
// (`variance Y p n ≠ 0`, instantiate the SAME lemma at `X,Y` swapped) reuse
// it rather than re-deriving `Var[tX+Y] ≥ 0` twice.

/// `Rat.variance_scaled_add_nonneg : ∀ X Y p n, IsDistribution p n → ∀ t,
/// le zero (add (mul (mul t t) (variance X p n)) (add (mul t (covariance X Y
/// p n)) (add (mul t (covariance X Y p n)) (variance Y p n))))` —
/// `0 ≤ t²·Var[X] + (t·Cov[X,Y] + (t·Cov[X,Y] + Var[Y]))`, i.e. `Var[tX+Y] ≥
/// 0` fully expanded, for every rational `t`.
///
/// [`RatPrelude::variance_add_eq`] applied to `(fun k => t*X k)` and `Y`
/// gives `Var[tX+Y] = Var[tX] + (Cov[tX,Y] + (Cov[tX,Y] + Var[Y]))`;
/// [`RatPrelude::variance_smul`] rewrites `Var[tX]` to `(t*t)*Var[X]` and
/// [`RatPrelude::covariance_smul_left`] rewrites each `Cov[tX,Y]` to
/// `t*Cov[X,Y]` (three `sum_range_congr`-style substitutions into the same
/// nested sum, mirroring [`declare_variance_add_of_uncorrelated`]'s own
/// substitution shape); [`RatPrelude::variance_nonneg`] supplies `0 ≤
/// Var[tX+Y]` in the first place, and the whole chain transports it along
/// the equality.
fn declare_variance_scaled_add_nonneg(
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
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    let dist_ty = is_distribution(d, p, pf, n);
    let zero_r = rzero(d, p);

    let a = variance(d, p, x, pf, n);
    let b = covariance(d, p, x, y, pf, n);
    let c = variance(d, p, y, pf, n);

    let scaled_x = scale_fn(d, t, x);
    let combined_fn = combined(d, scaled_x, y);
    let variance_sum = variance(d, p, combined_fn, pf, n);
    let var_nonneg = d.lemma(p.variance_nonneg, &[combined_fn, pf, n, hd]);
    // var_nonneg : 0 ≤ variance_sum

    let headline = d.lemma(p.variance_add_eq, &[scaled_x, y, pf, n, hd]);
    // headline : Eq(variance_sum, variance_scaled_x + (cov_scaled_x_y +
    //   (cov_scaled_x_y + c)))
    let variance_scaled_x = variance(d, p, scaled_x, pf, n);
    let cov_scaled_x_y = covariance(d, p, scaled_x, y, pf, n);
    let inner0 = {
        let cov_plus_c = radd(d, cov_scaled_x_y, c);
        radd(d, cov_scaled_x_y, cov_plus_c)
    };
    let headline_rhs = radd(d, variance_scaled_x, inner0);

    let vs_eq = d.lemma(p.variance_smul, &[t, x, pf, n, hd]);
    // vs_eq : Eq(variance_scaled_x, (t*t)*a)
    let tt = rmul(d, t, t);
    let tt_a = rmul(d, tt, a);
    let cs_eq = d.lemma(p.covariance_smul_left, &[t, x, y, pf, n]);
    // cs_eq : Eq(cov_scaled_x_y, t*b)
    let t_b = rmul(d, t, b);

    let step1 = rcongr(d, variance_scaled_x, tt_a, vs_eq, &|d, w| {
        radd(d, w, inner0)
    });
    let after1 = radd(d, tt_a, inner0);

    let step2 = rcongr(d, cov_scaled_x_y, t_b, cs_eq, &|d, w| {
        let inner = radd(d, cov_scaled_x_y, c);
        let mid = radd(d, w, inner);
        radd(d, tt_a, mid)
    });
    let inner1 = {
        let cov_plus_c = radd(d, cov_scaled_x_y, c);
        radd(d, t_b, cov_plus_c)
    };
    let after2 = radd(d, tt_a, inner1);

    let step3 = rcongr(d, cov_scaled_x_y, t_b, cs_eq, &|d, w| {
        let inner = radd(d, w, c);
        let mid = radd(d, t_b, inner);
        radd(d, tt_a, mid)
    });
    let t_b_c = radd(d, t_b, c);
    let quad_inner = radd(d, t_b, t_b_c);
    let quad = radd(d, tt_a, quad_inner);

    let (_e, chain) = rchain(
        d,
        headline_rhs,
        &[(after1, step1), (after2, step2), (quad, step3)],
    );
    let full_eq = rtrans(d, variance_sum, headline_rhs, quad, headline, chain);
    // full_eq : Eq(variance_sum, quad)

    let final_proof = rat_eq_rewrite(d, variance_sum, quad, full_eq, var_nonneg, &|d, w| {
        rle(d, p, zero_r, w)
    });
    let concl = rle(d, p, zero_r, quad);

    let value = {
        let with_t = d.lam_fv(t_fv, carrier, final_proof);
        let with_hd = d.lam_fv(hd_fv, dist_ty, with_t);
        let with_n = d.lam_fv(n_fv, nat, with_hd);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_y = d.lam_fv(y_fv, fn_ty, with_pf);
        d.lam_fv(x_fv, fn_ty, with_y)
    };
    let ty = {
        let with_t = d.pi_fv(t_fv, carrier, concl);
        let with_hd = d.arrow(dist_ty, with_t);
        let with_n = d.pi_fv(n_fv, nat, with_hd);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        let with_y = d.pi_fv(y_fv, fn_ty, with_pf);
        d.pi_fv(x_fv, fn_ty, with_y)
    };
    d.declare_theorem(p.variance_scaled_add_nonneg, ty, value)
}

/// `Not (Eq Rat val zero)`, from `lt zero val` — rewrite the hypothesis along
/// an assumed `val = zero` to get `lt zero zero`, refuted by `lt_irrefl`.
/// Private: only [`declare_covariance_sq_le_variance_mul_of_pos`] needs it.
fn ne_zero_of_pos(d: &mut IntDev<'_>, p: RatPrelude, val: ExprId, h_pos: ExprId) -> ExprId {
    let zero_r = rzero(d, p);
    let eq_ty = req(d, val, zero_r);
    let heq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(heq_fv);
    let rewritten = rat_eq_rewrite(d, val, zero_r, heq, h_pos, &|d, t| rlt(d, p, zero_r, t));
    let irrefl = d.lemma(p.lt_irrefl, &[zero_r]);
    let false_proof = d.apply(irrefl, &[rewritten]);
    d.lam_fv(heq_fv, eq_ty, false_proof)
}

/// `Eq Rat (neg a * neg b) (a * b)`, over generic `a`, `b : Rat` — the same
/// `neg_mul`/`mul_neg`/`neg_neg` composition [`sub_sq_expand`] uses inline
/// for its own `neg_b*neg_b -> b*b` step, factored out here since
/// [`declare_covariance_sq_le_variance_mul_of_pos`] needs it applied at
/// `(neg (covariance X Y p n))`, not at a literal `b`. Private.
fn neg_mul_neg(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    a: ExprId,
    b: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let neg_a = rneg(d, a);
    let neg_b = rneg(d, b);
    let start = rmul(d, neg_a, neg_b);

    let a_negb = rmul(d, a, neg_b);
    let neg_a_negb = rneg(d, a_negb);
    let step1 = d.lemma(p.neg_mul, &[a, neg_b]); // Eq(start, neg_a_negb)

    let ab = rmul(d, a, b);
    let neg_ab = rneg(d, ab);
    let step2 = d.lemma(p.mul_neg, &[a, b]); // Eq(a_negb, neg_ab)
    let h2 = rcongr(d, a_negb, neg_ab, step2, &|d, t| rneg(d, t));
    let neg_neg_ab = rneg(d, neg_ab);

    let step3 = d.lemma(p.neg_neg, &[ab]); // Eq(neg_neg_ab, ab)

    let (_e, chain) = rchain(
        d,
        start,
        &[(neg_a_negb, step1), (neg_neg_ab, h2), (ab, step3)],
    );
    (start, ab, chain)
}

/// `le zero (sub r w) → le w r` — the rearrangement
/// [`declare_covariance_sq_le_variance_mul_of_pos`] needs to read `variance
/// Y p n ≥ (covariance X Y p n)² · inv(variance X p n)` off the discriminant
/// bound, once it is in `0 ≤ r − w` form. `add_le_add` shifts `w` onto both
/// sides, then `zero_add`/`add_assoc`/`neg_add_cancel`/`add_zero` collapse
/// each side — the same shape [`RatPrelude::le_of_sub_le`]'s own proof runs
/// (`rat_prelude::lattice::declare_shifts`), with the inequality direction
/// flipped since the hypothesis here has `0` on the LEFT, not the
/// difference. Private.
fn le_of_nonneg_sub(d: &mut IntDev<'_>, p: RatPrelude, r: ExprId, w: ExprId, h: ExprId) -> ExprId {
    let zero_r = rzero(d, p);
    let diff = rsub(d, p, r, w); // = radd(r, neg(w))

    let refl_w = d.lemma(p.le_refl, &[w]);
    let scaled = d.lemma(p.add_le_add, &[zero_r, diff, w, w, h, refl_w]);
    // scaled : le (zero+w) (diff+w)
    let zero_plus_w = radd(d, zero_r, w);
    let diff_plus_w = radd(d, diff, w);

    let lhs_eq = d.lemma(p.zero_add, &[w]); // Eq(zero+w, w)

    let neg_w = rneg(d, w);
    let negw_plus_w = radd(d, neg_w, w);
    let regroup = d.lemma(p.add_assoc, &[r, neg_w, w]); // Eq((r+negw)+w, r+(negw+w))
    let r_plus_negwplusw = radd(d, r, negw_plus_w);
    let cancel = d.lemma(p.neg_add_cancel, &[w]); // Eq(negw+w, zero)
    let vanish = rcongr(d, negw_plus_w, zero_r, cancel, &|d, t| radd(d, r, t));
    let r_plus_zero = radd(d, r, zero_r);
    let strip = d.lemma(p.add_zero, &[r]); // Eq(r+zero, r)
    let (_e, rhs_chain) = rchain(
        d,
        diff_plus_w,
        &[
            (r_plus_negwplusw, regroup),
            (r_plus_zero, vanish),
            (r, strip),
        ],
    );
    // rhs_chain : Eq(diff_plus_w, r)

    let step1 = rat_eq_rewrite(d, zero_plus_w, w, lhs_eq, scaled, &|d, t| {
        rle(d, p, t, diff_plus_w)
    });
    // step1 : le w diff_plus_w
    rat_eq_rewrite(d, diff_plus_w, r, rhs_chain, step1, &|d, t| rle(d, p, w, t))
}

/// `Rat.covariance_sq_le_variance_mul_of_pos : ∀ X Y p n, IsDistribution p n
/// → lt zero (variance X p n) → le (mul (covariance X Y p n) (covariance X Y
/// p n)) (mul (variance X p n) (variance Y p n))` — the probabilistic
/// Cauchy–Schwarz inequality, the case `variance X p n ≠ 0` closes without a
/// further split.
///
/// The discriminant argument, closed. Instantiate
/// [`RatPrelude::variance_scaled_add_nonneg`] at `t₀ := neg (covariance X Y
/// p n) * inv (variance X p n)`. Writing `P := variance X p n`, `Q :=
/// covariance X Y p n`, `R := variance Y p n`: `P*t₀ = neg Q`
/// ([`RatPrelude::mul_inv_cancel_of_ne_zero`], commuted/associated into
/// place), so `(t₀*t₀)*P = t₀*(neg Q) = (Q*Q)*inv(P)` and `t₀*Q = neg
/// ((Q*Q)*inv(P))` ([`neg_mul_neg`] for the `neg*neg -> pos` step both need).
/// The discriminant collapses (three `rcongr` rewrites, the SAME shape
/// [`declare_variance_scaled_add_nonneg`]'s own `step1`/`step2`/`step3`
/// use) to `0 ≤ R − (Q*Q)*inv(P)`, [`le_of_nonneg_sub`] reads off `(Q*Q)*inv(P)
/// ≤ R`, and multiplying both sides by `P` (`≥ 0` from the hypothesis) —
/// `P*((Q*Q)*inv(P)) = Q*Q` by the SAME cancellation — closes `Q*Q ≤ P*R`.
fn declare_covariance_sq_le_variance_mul_of_pos(
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
    let hp_fv = d.fresh_fvar();
    let hp = d.kernel().fvar(hp_fv);

    let dist_ty = is_distribution(d, p, pf, n);
    let zero_r = rzero(d, p);

    let pterm = variance(d, p, x, pf, n);
    let qterm = covariance(d, p, x, y, pf, n);
    let rterm = variance(d, p, y, pf, n);
    let hp_ty = rlt(d, p, zero_r, pterm);

    let qq = rmul(d, qterm, qterm);
    let pr = rmul(d, pterm, rterm);
    let concl = rle(d, p, qq, pr);

    // --- setup: t0 := neg(qterm) * inv(pterm)
    let hp_ne = ne_zero_of_pos(d, p, pterm, hp);
    let invp = d.const_app(p.inv, &[pterm]);
    let neg_q = rneg(d, qterm);
    let t0 = rmul(d, neg_q, invp);

    let quad_nonneg = d.lemma(p.variance_scaled_add_nonneg, &[x, y, pf, n, hd, t0]);
    // quad_nonneg : 0 ≤ (t0*t0)*pterm + (t0*qterm + (t0*qterm + rterm))

    // --- Fact 1: pterm * t0 = neg_q
    let pterm_t0 = {
        let invp_negq = rmul(d, invp, neg_q);
        let step_a = d.lemma(p.mul_comm, &[neg_q, invp]); // Eq(t0, invp_negq)
        let pterm_invp_negq = rmul(d, pterm, invp_negq);
        let step_a_lift = rcongr(d, t0, invp_negq, step_a, &|d, w| rmul(d, pterm, w));

        let pterm_invp = rmul(d, pterm, invp);
        let step_b = d.lemma(p.mul_assoc, &[pterm, invp, neg_q]); // Eq((pterm*invp)*negq, pterm*(invp*negq))
        let pterm_invp_times_negq = rmul(d, pterm_invp, neg_q);
        let step_b_rev = rsymm(d, pterm_invp_times_negq, pterm_invp_negq, step_b);

        let cancel = d.lemma(p.mul_inv_cancel_of_ne_zero, &[pterm, hp_ne]); // Eq(pterm_invp, one)
        let one_r = rone(d, p);
        let one_times_negq = rmul(d, one_r, neg_q);
        let step_c = rcongr(d, pterm_invp, one_r, cancel, &|d, w| rmul(d, w, neg_q));

        let negq_times_one = rmul(d, neg_q, one_r);
        let step_d = d.lemma(p.mul_comm, &[one_r, neg_q]); // Eq(one_times_negq, negq_times_one)
        let step_e = d.lemma(p.mul_one, &[neg_q]); // Eq(negq_times_one, neg_q)

        let start = rmul(d, pterm, t0);
        let (_e, chain) = rchain(
            d,
            start,
            &[
                (pterm_invp_negq, step_a_lift),
                (pterm_invp_times_negq, step_b_rev),
                (one_times_negq, step_c),
                (negq_times_one, step_d),
                (neg_q, step_e),
            ],
        );
        chain
    };
    // pterm_t0 : Eq(pterm*t0, neg_q)

    // --- Fact 2: (t0*t0)*pterm = (qterm*qterm)*invp
    let qq_invp = rmul(d, qq, invp);
    let t0t0_pterm_eq = {
        let t0_pterm = rmul(d, t0, pterm);
        let t0_t0 = rmul(d, t0, t0);
        let start = rmul(d, t0_t0, pterm);
        let step_a = d.lemma(p.mul_assoc, &[t0, t0, pterm]); // Eq(start, t0*(t0*pterm))
        let t0_times_t0pterm = rmul(d, t0, t0_pterm);

        let step_b = d.lemma(p.mul_comm, &[t0, pterm]); // Eq(t0_pterm, pterm*t0)
        let pterm_t0_expr = rmul(d, pterm, t0);
        let step_b_lift = rcongr(d, t0_pterm, pterm_t0_expr, step_b, &|d, w| rmul(d, t0, w));
        let t0_times_ptermt0 = rmul(d, t0, pterm_t0_expr);

        let step_c = rcongr(d, pterm_t0_expr, neg_q, pterm_t0, &|d, w| rmul(d, t0, w));
        let t0_times_negq = rmul(d, t0, neg_q);

        // t0 * neg_q = (neg_q*invp)*neg_q = neg_q*(invp*neg_q) = neg_q*(neg_q*invp)
        //   = (neg_q*neg_q)*invp = (qterm*qterm)*invp
        let invp_negq2 = rmul(d, invp, neg_q);
        let step_d = d.lemma(p.mul_assoc, &[neg_q, invp, neg_q]); // Eq(t0_times_negq, neg_q*(invp*neg_q))
        let negq_times_invpnegq = rmul(d, neg_q, invp_negq2);

        let negq_negq = rmul(d, neg_q, neg_q);
        let step_e = d.lemma(p.mul_comm, &[invp, neg_q]); // Eq(invp_negq2, negq_negq)... wait mul_comm(invp,neg_q): Eq(invp*neg_q, neg_q*invp)
        let negq_invp = rmul(d, neg_q, invp);
        let step_e_lift = rcongr(d, invp_negq2, negq_invp, step_e, &|d, w| rmul(d, neg_q, w));
        let negq_times_negqinvp = rmul(d, neg_q, negq_invp);

        let step_f = d.lemma(p.mul_assoc, &[neg_q, neg_q, invp]); // Eq(negq_negq*invp, neg_q*(neg_q*invp))
        let negqnegq_invp = rmul(d, negq_negq, invp);
        let step_f_rev = rsymm(d, negqnegq_invp, negq_times_negqinvp, step_f);

        let (_, _, step_g) = neg_mul_neg(d, p, qterm, qterm); // Eq(negq_negq, qq)
        let step_g_lift = rcongr(d, negq_negq, qq, step_g, &|d, w| rmul(d, w, invp));

        let (_e, chain) = rchain(
            d,
            start,
            &[
                (t0_times_t0pterm, step_a),
                (t0_times_ptermt0, step_b_lift),
                (t0_times_negq, step_c),
                (negq_times_invpnegq, step_d),
                (negq_times_negqinvp, step_e_lift),
                (negqnegq_invp, step_f_rev),
                (qq_invp, step_g_lift),
            ],
        );
        chain
    };
    // t0t0_pterm_eq : Eq((t0*t0)*pterm, qq_invp)

    // --- Fact 3: t0*qterm = neg(qq_invp)
    let neg_qq_invp = rneg(d, qq_invp);
    let t0_qterm_eq = {
        let start = rmul(d, t0, qterm);
        let invp_qterm = rmul(d, invp, qterm);
        let step_a = d.lemma(p.mul_assoc, &[neg_q, invp, qterm]); // Eq(t0*qterm, negq*(invp*qterm))
        let negq_times_invpqterm = rmul(d, neg_q, invp_qterm);

        let qterm_invp = rmul(d, qterm, invp);
        let step_b = d.lemma(p.mul_comm, &[invp, qterm]); // Eq(invp_qterm, qterm_invp)
        let step_b_lift = rcongr(d, invp_qterm, qterm_invp, step_b, &|d, w| rmul(d, neg_q, w));
        let negq_times_qterminvp = rmul(d, neg_q, qterm_invp);

        let step_c = d.lemma(p.mul_assoc, &[neg_q, qterm, invp]); // Eq(negq*(qterm*invp), (negq*qterm)*invp)... check direction
        // mul_assoc(neg_q,qterm,invp) : (negq*qterm)*invp = negq*(qterm*invp)
        let negq_qterm = rmul(d, neg_q, qterm);
        let negqqterm_invp = rmul(d, negq_qterm, invp);
        let step_c_rev = rsymm(d, negqqterm_invp, negq_times_qterminvp, step_c);

        let neg_qq = rneg(d, qq);
        let step_d = d.lemma(p.neg_mul, &[qterm, qterm]); // Eq(negq_qterm, neg_qq)
        let step_d_lift = rcongr(d, negq_qterm, neg_qq, step_d, &|d, w| rmul(d, w, invp));
        let negqq_invp = rmul(d, neg_qq, invp);

        let step_e = d.lemma(p.neg_mul, &[qq, invp]); // Eq(negqq_invp, neg(qq*invp))
        let neg_qqinvp2 = rneg(d, qq_invp);

        let (_e, chain) = rchain(
            d,
            start,
            &[
                (negq_times_invpqterm, step_a),
                (negq_times_qterminvp, step_b_lift),
                (negqqterm_invp, step_c_rev),
                (negqq_invp, step_d_lift),
                (neg_qqinvp2, step_e),
            ],
        );
        chain
    };
    // t0_qterm_eq : Eq(t0*qterm, neg_qq_invp)

    // --- collapse the discriminant to 0 ≤ rterm - qq_invp
    let t0t0_tmp = rmul(d, t0, t0);
    let t0t0_pterm = rmul(d, t0t0_tmp, pterm);
    let t0_qterm = rmul(d, t0, qterm);
    let inner0 = {
        let t0q_plus_r = radd(d, t0_qterm, rterm);
        radd(d, t0_qterm, t0q_plus_r)
    };
    let quad_start = radd(d, t0t0_pterm, inner0);

    let step1 = rcongr(d, t0t0_pterm, qq_invp, t0t0_pterm_eq, &|d, w| {
        radd(d, w, inner0)
    });
    let after1 = radd(d, qq_invp, inner0);

    let step2 = rcongr(d, t0_qterm, neg_qq_invp, t0_qterm_eq, &|d, w| {
        let t0q_plus_r = radd(d, t0_qterm, rterm);
        let mid = radd(d, w, t0q_plus_r);
        radd(d, qq_invp, mid)
    });
    let inner1 = {
        let t0q_plus_r = radd(d, t0_qterm, rterm);
        radd(d, neg_qq_invp, t0q_plus_r)
    };
    let after2 = radd(d, qq_invp, inner1);

    let step3 = rcongr(d, t0_qterm, neg_qq_invp, t0_qterm_eq, &|d, w| {
        let mid = radd(d, w, rterm);
        let outer = radd(d, neg_qq_invp, mid);
        radd(d, qq_invp, outer)
    });
    let neg_qqinvp_r = radd(d, neg_qq_invp, rterm);
    let neg_qqinvp_plus_r = radd(d, neg_qq_invp, neg_qqinvp_r);
    let after3 = radd(d, qq_invp, neg_qqinvp_plus_r);

    // after3 = qq_invp + (neg_qq_invp + (neg_qq_invp + rterm))
    //   regroup: (qq_invp + neg_qq_invp) + (neg_qq_invp + rterm)
    let regroup = d.lemma(p.add_assoc, &[qq_invp, neg_qq_invp, neg_qqinvp_r]);
    // regroup : Eq((qq_invp+neg_qq_invp)+neg_qqinvp_r, qq_invp+(neg_qq_invp+neg_qqinvp_r))
    let qqinvp_plus_neg = radd(d, qq_invp, neg_qq_invp);
    let regrouped = radd(d, qqinvp_plus_neg, neg_qqinvp_r);
    let regroup_rev = rsymm(d, regrouped, after3, regroup);

    let cancel = d.lemma(p.add_neg, &[qq_invp]); // Eq(qq_invp+neg_qq_invp, zero)
    let step4 = rcongr(d, qqinvp_plus_neg, zero_r, cancel, &|d, w| {
        radd(d, w, neg_qqinvp_r)
    });
    let zero_plus_rest = radd(d, zero_r, neg_qqinvp_r);

    let step5 = d.lemma(p.zero_add, &[neg_qqinvp_r]); // Eq(zero+neg_qqinvp_r, neg_qqinvp_r)

    let (_e, collapse_chain) = rchain(
        d,
        after3,
        &[
            (regrouped, regroup_rev),
            (zero_plus_rest, step4),
            (neg_qqinvp_r, step5),
        ],
    );
    // collapse_chain : Eq(after3, neg_qqinvp_r)  where neg_qqinvp_r = neg_qq_invp + rterm

    let (_e, full_chain) = rchain(
        d,
        quad_start,
        &[
            (after1, step1),
            (after2, step2),
            (after3, step3),
            (neg_qqinvp_r, collapse_chain),
        ],
    );
    let bound_at_neg_form = rat_eq_rewrite(
        d,
        quad_start,
        neg_qqinvp_r,
        full_chain,
        quad_nonneg,
        &|d, w| rle(d, p, zero_r, w),
    );
    // bound_at_neg_form : 0 ≤ neg_qq_invp + rterm

    // reorder to rterm - qq_invp (rsub's own literal shape, r + neg(w))
    let comm_step = d.lemma(p.add_comm, &[neg_qq_invp, rterm]); // Eq(neg_qq_invp+rterm, rterm+neg_qq_invp)
    let rterm_plus_negqqinvp = radd(d, rterm, neg_qq_invp);
    let bound_sub_form = rat_eq_rewrite(
        d,
        neg_qqinvp_r,
        rterm_plus_negqqinvp,
        comm_step,
        bound_at_neg_form,
        &|d, w| rle(d, p, zero_r, w),
    );
    // bound_sub_form : 0 ≤ rterm + neg(qq_invp)   ~ 0 ≤ rsub(rterm,qq_invp)  [defeq]

    // --- extract qq_invp ≤ rterm, then multiply by pterm
    let qq_invp_le_r = le_of_nonneg_sub(d, p, rterm, qq_invp, bound_sub_form);

    let hp_nonneg = d.lemma(p.le_of_lt, &[zero_r, pterm, hp]);
    let scaled_le = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[pterm, qq_invp, rterm, hp_nonneg, qq_invp_le_r],
    );
    // scaled_le : pterm*qq_invp ≤ pterm*rterm

    // pterm*qq_invp = qq
    let pterm_qqinvp = rmul(d, pterm, qq_invp);
    let pterm_qq_eq = {
        let start = pterm_qqinvp;
        let invp_qq = rmul(d, invp, qq);
        let step_a = d.lemma(p.mul_comm, &[qq, invp]); // Eq(qq_invp, invp_qq)
        let pterm_invpqq = rmul(d, pterm, invp_qq);
        let step_a_lift = rcongr(d, qq_invp, invp_qq, step_a, &|d, w| rmul(d, pterm, w));

        let pterm_invp = rmul(d, pterm, invp);
        let step_b = d.lemma(p.mul_assoc, &[pterm, invp, qq]); // Eq((pterm*invp)*qq, pterm*(invp*qq))
        let pterm_invp_times_qq = rmul(d, pterm_invp, qq);
        let step_b_rev = rsymm(d, pterm_invp_times_qq, pterm_invpqq, step_b);

        let cancel2 = d.lemma(p.mul_inv_cancel_of_ne_zero, &[pterm, hp_ne]); // Eq(pterm_invp, one)
        let one_r = rone(d, p);
        let one_times_qq = rmul(d, one_r, qq);
        let step_c = rcongr(d, pterm_invp, one_r, cancel2, &|d, w| rmul(d, w, qq));

        let qq_times_one = rmul(d, qq, one_r);
        let step_d = d.lemma(p.mul_comm, &[one_r, qq]); // Eq(one_times_qq, qq_times_one)
        let step_e = d.lemma(p.mul_one, &[qq]); // Eq(qq_times_one, qq)

        let (_e, chain) = rchain(
            d,
            start,
            &[
                (pterm_invpqq, step_a_lift),
                (pterm_invp_times_qq, step_b_rev),
                (one_times_qq, step_c),
                (qq_times_one, step_d),
                (qq, step_e),
            ],
        );
        chain
    };
    // pterm_qq_eq : Eq(pterm*qq_invp, qq)

    let final_proof = rat_eq_rewrite(d, pterm_qqinvp, qq, pterm_qq_eq, scaled_le, &|d, w| {
        rle(d, p, w, pr)
    });
    // final_proof : qq ≤ pr

    let value = {
        let with_hp = d.lam_fv(hp_fv, hp_ty, final_proof);
        let with_hd = d.lam_fv(hd_fv, dist_ty, with_hp);
        let with_n = d.lam_fv(n_fv, nat, with_hd);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_y = d.lam_fv(y_fv, fn_ty, with_pf);
        d.lam_fv(x_fv, fn_ty, with_y)
    };
    let ty = {
        let with_hp = d.arrow(hp_ty, concl);
        let with_hd = d.arrow(dist_ty, with_hp);
        let with_n = d.pi_fv(n_fv, nat, with_hd);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        let with_y = d.pi_fv(y_fv, fn_ty, with_pf);
        d.pi_fv(x_fv, fn_ty, with_y)
    };
    d.declare_theorem(p.covariance_sq_le_variance_mul_of_pos, ty, value)
}

/// `0 ≤ add (mul t (covariance X Y p n)) (mul t (covariance X Y p n))`,
/// given `variance X p n = zero` and `variance Y p n = zero` — the
/// discriminant [`RatPrelude::variance_scaled_add_nonneg`] supplies at `t`,
/// with the (now-zero) `variance X p n` and `variance Y p n` terms
/// eliminated. Private: only
/// [`declare_covariance_sq_le_variance_mul_of_zero_zero`] needs it, at `t :=
/// one` and `t := neg one`.
fn quad_nonneg_with_zero_variances(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    x: ExprId,
    y: ExprId,
    pf: ExprId,
    n: ExprId,
    hd: ExprId,
    ha0: ExprId,
    hc0: ExprId,
    t: ExprId,
) -> ExprId {
    let pterm = variance(d, p, x, pf, n);
    let qterm = covariance(d, p, x, y, pf, n);
    let rterm = variance(d, p, y, pf, n);
    let zero_r = rzero(d, p);

    let quad_nonneg = d.lemma(p.variance_scaled_add_nonneg, &[x, y, pf, n, hd, t]);
    // quad_nonneg : 0 ≤ (t*t)*pterm + (t*qterm + (t*qterm + rterm))

    let tt = rmul(d, t, t);
    let tt_pterm = rmul(d, tt, pterm);
    let t_q = rmul(d, t, qterm);
    let inner = radd(d, t_q, rterm);
    let full_inner = radd(d, t_q, inner);
    let quad_start = radd(d, tt_pterm, full_inner);

    // tt_pterm -> zero, via ha0 then mul_zero
    let tt_pterm_zero = {
        let step1 = rcongr(d, pterm, zero_r, ha0, &|d, w| rmul(d, tt, w));
        let tt_zero = rmul(d, tt, zero_r);
        let step2 = d.lemma(p.mul_zero, &[tt]); // Eq(tt*zero, zero)
        rtrans(d, tt_pterm, tt_zero, zero_r, step1, step2)
    };
    let substep_a = rcongr(d, tt_pterm, zero_r, tt_pterm_zero, &|d, w| {
        radd(d, w, full_inner)
    });
    let after_a = radd(d, zero_r, full_inner);

    // rterm -> zero, via hc0 (innermost position)
    let substep_b = rcongr(d, rterm, zero_r, hc0, &|d, w| {
        let inner2 = radd(d, t_q, w);
        let mid = radd(d, t_q, inner2);
        radd(d, zero_r, mid)
    });
    let inner_z = radd(d, t_q, zero_r);
    let after_b_mid = radd(d, t_q, inner_z);
    let after_b = radd(d, zero_r, after_b_mid);

    // t_q + zero -> t_q
    let add_zero_tq = d.lemma(p.add_zero, &[t_q]);
    let substep_c = rcongr(d, inner_z, t_q, add_zero_tq, &|d, w| {
        let mid = radd(d, t_q, w);
        radd(d, zero_r, mid)
    });
    let after_c_mid = radd(d, t_q, t_q);
    let after_c = radd(d, zero_r, after_c_mid);

    // zero + (t_q+t_q) -> t_q+t_q
    let tq_tq = radd(d, t_q, t_q);
    let substep_d = d.lemma(p.zero_add, &[tq_tq]);

    let (_e, chain) = rchain(
        d,
        quad_start,
        &[
            (after_a, substep_a),
            (after_b, substep_b),
            (after_c, substep_c),
            (tq_tq, substep_d),
        ],
    );
    rat_eq_rewrite(d, quad_start, tq_tq, chain, quad_nonneg, &|d, w| {
        rle(d, p, zero_r, w)
    })
}

/// `Rat.covariance_sq_le_variance_mul_of_zero_zero : ∀ X Y p n,
/// IsDistribution p n → variance X p n = zero → variance Y p n = zero → le
/// (mul (covariance X Y p n) (covariance X Y p n)) (mul (variance X p n)
/// (variance Y p n))` — the probabilistic Cauchy–Schwarz inequality, the
/// case where BOTH variances vanish. No inverse: `variance_scaled_add_nonneg`
/// at `t := one` gives `0 ≤ covariance X Y p n + covariance X Y p n`; at `t
/// := neg one`, `0 ≤ neg (covariance X Y p n + covariance X Y p n)` — so
/// `covariance X Y p n + covariance X Y p n = zero` (`le_antisymm`),
/// squaring both sides ([`add_sq_expand`], `rat_zero_mul`) gives `4 ·
/// (covariance X Y p n)² = zero` as a nested sum, and the same "one term ≤ a
/// nonneg sum" bound [`term_le_sum_range`] uses reads `(covariance X Y p
/// n)² ≤ zero` off it directly — no need to extract `covariance X Y p n =
/// zero` first.
fn declare_covariance_sq_le_variance_mul_of_zero_zero(
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
    let ha0_fv = d.fresh_fvar();
    let ha0 = d.kernel().fvar(ha0_fv);
    let hc0_fv = d.fresh_fvar();
    let hc0 = d.kernel().fvar(hc0_fv);

    let dist_ty = is_distribution(d, p, pf, n);
    let zero_r = rzero(d, p);

    let pterm = variance(d, p, x, pf, n);
    let qterm = covariance(d, p, x, y, pf, n);
    let rterm = variance(d, p, y, pf, n);
    let ha0_ty = req(d, pterm, zero_r);
    let hc0_ty = req(d, rterm, zero_r);

    let qq = rmul(d, qterm, qterm);
    let pr = rmul(d, pterm, rterm);
    let concl = rle(d, p, qq, pr);

    // --- t := one: 0 ≤ qterm+qterm
    let one_r = rone(d, p);
    let one_q_eq_qterm = {
        let step1 = d.lemma(p.mul_comm, &[one_r, qterm]); // Eq(one*qterm, qterm*one)
        let qterm_one = rmul(d, qterm, one_r);
        let step2 = d.lemma(p.mul_one, &[qterm]); // Eq(qterm*one, qterm)
        let one_qterm0 = rmul(d, one_r, qterm);
        rtrans(d, one_qterm0, qterm_one, qterm, step1, step2)
    };
    let base1 = quad_nonneg_with_zero_variances(d, p, x, y, pf, n, hd, ha0, hc0, one_r);
    // base1 : 0 ≤ (one*qterm) + (one*qterm)
    let one_q = rmul(d, one_r, qterm);
    let squared_eq1 = rcongr(d, one_q, qterm, one_q_eq_qterm, &|d, w| radd(d, w, w));
    // squared_eq1 : Eq((one_q)+(one_q), qterm+qterm)
    let one_q_one_q = radd(d, one_q, one_q);
    let qterm_qterm = radd(d, qterm, qterm);
    let hb_ge = rat_eq_rewrite(d, one_q_one_q, qterm_qterm, squared_eq1, base1, &|d, w| {
        rle(d, p, zero_r, w)
    });
    // hb_ge : 0 ≤ qterm+qterm

    // --- t := neg one: qterm+qterm ≤ 0
    let neg_one = rneg(d, one_r);
    let negone_q_eq_negqterm = {
        let step1 = d.lemma(p.neg_mul, &[one_r, qterm]); // Eq(neg(one)*qterm, neg(one*qterm))
        let one_qterm = rmul(d, one_r, qterm);
        let neg_one_qterm = rneg(d, one_qterm);
        let neg_qterm = rneg(d, qterm);
        let step2 = rcongr(d, one_qterm, qterm, one_q_eq_qterm, &|d, w| rneg(d, w));
        // step2 : Eq(neg(one*qterm), neg(qterm))
        let negone_qterm0 = rmul(d, neg_one, qterm);
        rtrans(d, negone_qterm0, neg_one_qterm, neg_qterm, step1, step2)
    };
    let base2 = quad_nonneg_with_zero_variances(d, p, x, y, pf, n, hd, ha0, hc0, neg_one);
    // base2 : 0 ≤ (neg_one*qterm) + (neg_one*qterm)
    let negone_q = rmul(d, neg_one, qterm);
    let neg_qterm = rneg(d, qterm);
    let squared_eq2 = rcongr(d, negone_q, neg_qterm, negone_q_eq_negqterm, &|d, w| {
        radd(d, w, w)
    });
    // squared_eq2 : Eq(negone_q+negone_q, neg_qterm+neg_qterm)
    let negone_q_negone_q = radd(d, negone_q, negone_q);
    let neg_qterm_neg_qterm = radd(d, neg_qterm, neg_qterm);
    let step_mid = rat_eq_rewrite(
        d,
        negone_q_negone_q,
        neg_qterm_neg_qterm,
        squared_eq2,
        base2,
        &|d, w| rle(d, p, zero_r, w),
    );
    // step_mid : 0 ≤ neg_qterm + neg_qterm

    let x_sum = radd(d, qterm, qterm); // qterm+qterm
    let neg_add_eq = d.lemma(p.neg_add, &[qterm, qterm]); // Eq(neg(qterm+qterm), neg(qterm)+neg(qterm))
    let neg_x_sum = rneg(d, x_sum);
    let neg_qterm_sum = radd(d, neg_qterm, neg_qterm);
    let neg_add_rev = rsymm(d, neg_x_sum, neg_qterm_sum, neg_add_eq);
    // neg_add_rev : Eq(neg_qterm+neg_qterm, neg(qterm+qterm))
    let step_final = rat_eq_rewrite(
        d,
        neg_qterm_sum,
        neg_x_sum,
        neg_add_rev,
        step_mid,
        &|d, w| rle(d, p, zero_r, w),
    );
    // step_final : 0 ≤ neg(qterm+qterm)

    let nn = d.lemma(p.neg_le_neg, &[zero_r, neg_x_sum, step_final]);
    // nn : neg(neg(qterm+qterm)) ≤ neg(zero)
    let neg_neg_x_sum = rneg(d, neg_x_sum);
    let neg_neg_x_sum_eq = d.lemma(p.neg_neg, &[x_sum]); // Eq(neg(neg(x_sum)), x_sum)
    let neg_zero_r = rneg(d, zero_r);
    let step_a3 = rat_eq_rewrite(d, neg_neg_x_sum, x_sum, neg_neg_x_sum_eq, nn, &|d, w| {
        rle(d, p, w, neg_zero_r)
    });
    // step_a3 : x_sum ≤ neg(zero)
    let neg_zero_eq = d.lemma(p.neg_zero, &[]); // Eq(neg(zero), zero)
    let hb_le = rat_eq_rewrite(d, neg_zero_r, zero_r, neg_zero_eq, step_a3, &|d, w| {
        rle(d, p, x_sum, w)
    });
    // hb_le : x_sum ≤ zero, i.e. qterm+qterm ≤ zero

    // --- combine into qterm+qterm = zero
    let heq_b0 = d.lemma(p.le_antisymm, &[zero_r, x_sum, hb_ge, hb_le]); // Eq(zero, x_sum)
    let hs_eq_zero = rsymm(d, zero_r, x_sum, heq_b0); // Eq(x_sum, zero)

    // --- (qterm+qterm)*(qterm+qterm) = zero
    let ss = rmul(d, x_sum, x_sum);
    let step_ss1 = rcongr(d, x_sum, zero_r, hs_eq_zero, &|d, w| rmul(d, w, x_sum));
    let zero_x_sum = rmul(d, zero_r, x_sum);
    let step_ss2 = rat_zero_mul(d, p, x_sum); // Eq(zero*x_sum, zero)
    let ss_zero = rtrans(d, ss, zero_x_sum, zero_r, step_ss1, step_ss2);
    // ss_zero : Eq(ss, zero)

    // --- expand ss via add_sq_expand, collapse to qq ≤ zero
    let (start_e, target_e, proof_e) = add_sq_expand(d, p, qterm, qterm);
    // start_e ~ ss (both (qterm+qterm)*(qterm+qterm)); target_e = qq+(qq+(qq+qq))
    let proof_e_rev = rsymm(d, start_e, target_e, proof_e); // Eq(target_e, start_e)
    let e_eq_zero = rtrans(d, target_e, start_e, zero_r, proof_e_rev, ss_zero);
    // e_eq_zero : Eq(target_e, zero)

    let qq_nonneg = d.lemma(p.sq_nonneg, &[qterm]); // 0 ≤ qq
    let qq_qq_nonneg = d.lemma(p.add_nonneg, &[qq, qq, qq_nonneg, qq_nonneg]); // 0 ≤ qq+qq
    let qq_qq = radd(d, qq, qq);
    let rest_nonneg = d.lemma(p.add_nonneg, &[qq, qq_qq, qq_nonneg, qq_qq_nonneg]); // 0 ≤ qq+(qq+qq)
    let rest = radd(d, qq, qq_qq);

    let le_refl_qq = d.lemma(p.le_refl, &[qq]);
    let h_add = d.lemma(
        p.add_le_add,
        &[qq, qq, zero_r, rest, le_refl_qq, rest_nonneg],
    );
    // h_add : qq+zero ≤ qq+rest
    let qq_plus_zero = radd(d, qq, zero_r);
    let add_zero_qq = d.lemma(p.add_zero, &[qq]); // Eq(qq+zero, qq)
    let qq_plus_rest = radd(d, qq, rest);
    let qq_le_target = rat_eq_rewrite(d, qq_plus_zero, qq, add_zero_qq, h_add, &|d, w| {
        rle(d, p, w, qq_plus_rest)
    });
    // qq_le_target : qq ≤ qq+rest  (= target_e)

    let qq_le_zero = rat_eq_rewrite(d, target_e, zero_r, e_eq_zero, qq_le_target, &|d, w| {
        rle(d, p, qq, w)
    });
    // qq_le_zero : qq ≤ zero

    // --- pr = zero, via ha0
    let pr_eq = {
        let step1 = rcongr(d, pterm, zero_r, ha0, &|d, w| rmul(d, w, rterm));
        let zero_rterm = rmul(d, zero_r, rterm);
        let step2 = rat_zero_mul(d, p, rterm);
        rtrans(d, pr, zero_rterm, zero_r, step1, step2)
    };
    // pr_eq : Eq(pr, zero)
    let pr_eq_rev = rsymm(d, pr, zero_r, pr_eq); // Eq(zero, pr)
    let final_proof = rat_eq_rewrite(d, zero_r, pr, pr_eq_rev, qq_le_zero, &|d, w| {
        rle(d, p, qq, w)
    });
    // final_proof : qq ≤ pr

    let value = {
        let with_hc0 = d.lam_fv(hc0_fv, hc0_ty, final_proof);
        let with_ha0 = d.lam_fv(ha0_fv, ha0_ty, with_hc0);
        let with_hd = d.lam_fv(hd_fv, dist_ty, with_ha0);
        let with_n = d.lam_fv(n_fv, nat, with_hd);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_y = d.lam_fv(y_fv, fn_ty, with_pf);
        d.lam_fv(x_fv, fn_ty, with_y)
    };
    let ty = {
        let with_hc0 = d.arrow(hc0_ty, concl);
        let with_ha0 = d.arrow(ha0_ty, with_hc0);
        let with_hd = d.arrow(dist_ty, with_ha0);
        let with_n = d.pi_fv(n_fv, nat, with_hd);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        let with_y = d.pi_fv(y_fv, fn_ty, with_pf);
        d.pi_fv(x_fv, fn_ty, with_y)
    };
    d.declare_theorem(p.covariance_sq_le_variance_mul_of_zero_zero, ty, value)
}

/// `Or (Eq Rat val zero) (Lt zero val)`, from `le zero val` — rule out the
/// `val < zero` branch of [`RatPrelude::lt_trichotomy`] via
/// [`RatPrelude::lt_of_le_of_lt`] and [`RatPrelude::lt_irrefl`], the same
/// contradiction [`ne_zero_of_pos`] runs in the other direction. Private:
/// only [`declare_covariance_sq_le_variance_mul`] needs it, applied to
/// `variance X p n` and (nested) `variance Y p n`.
fn nonneg_trichotomy(d: &mut IntDev<'_>, p: RatPrelude, val: ExprId, h_nonneg: ExprId) -> ExprId {
    let zero_r = rzero(d, p);
    let lt_val_zero = rlt(d, p, val, zero_r);
    let eq_val_zero = req(d, val, zero_r);
    let lt_zero_val = rlt(d, p, zero_r, val);
    let right_or = d.or(eq_val_zero, lt_zero_val);
    let trichotomy = d.lemma(p.lt_trichotomy, &[val, zero_r]);
    d.or_elim(
        lt_val_zero,
        right_or,
        right_or,
        trichotomy,
        &|d, h_neg| {
            let zero_lt_zero = d.lemma(p.lt_of_le_of_lt, &[zero_r, val, zero_r, h_nonneg, h_neg]);
            let irrefl = d.lemma(p.lt_irrefl, &[zero_r]);
            let false_proof = d.apply(irrefl, &[zero_lt_zero]);
            d.absurd(right_or, false_proof)
        },
        &|_d, h_rest| h_rest,
    )
}

/// `Rat.covariance_sq_le_variance_mul : ∀ X Y p n, IsDistribution p n → le
/// (mul (covariance X Y p n) (covariance X Y p n)) (mul (variance X p n)
/// (variance Y p n))` — the probabilistic Cauchy–Schwarz inequality,
/// unconditional. `cov(X,Y)² ≤ var(X)·var(Y)`, in SQUARED form (`ℚ` has no
/// square root, the same limit `creal_point.rs`'s own `cauchy_schwarz`
/// records — do not read this as `|cov| ≤ σ_X·σ_Y`).
///
/// [`nonneg_trichotomy`] on `variance X p n` (nonneg from
/// [`RatPrelude::variance_nonneg`]) splits into
/// [`RatPrelude::covariance_sq_le_variance_mul_of_pos`] directly, or — when
/// `variance X p n = 0` — a second [`nonneg_trichotomy`] on `variance Y p
/// n`: positive swaps `X`/`Y` through the SAME
/// `covariance_sq_le_variance_mul_of_pos` (rewriting the result back via
/// [`RatPrelude::covariance_comm`] and [`RatPrelude::mul_comm`]), zero closes
/// via [`RatPrelude::covariance_sq_le_variance_mul_of_zero_zero`]. Three
/// cases, no case left uncovered.
fn declare_covariance_sq_le_variance_mul(
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

    let dist_ty = is_distribution(d, p, pf, n);
    let zero_r = rzero(d, p);

    let pterm = variance(d, p, x, pf, n);
    let qterm = covariance(d, p, x, y, pf, n);
    let rterm = variance(d, p, y, pf, n);
    let qq = rmul(d, qterm, qterm);
    let pr = rmul(d, pterm, rterm);
    let concl = rle(d, p, qq, pr);

    let ha_nonneg = d.lemma(p.variance_nonneg, &[x, pf, n, hd]); // 0 ≤ pterm
    let hc_nonneg = d.lemma(p.variance_nonneg, &[y, pf, n, hd]); // 0 ≤ rterm

    let a_choice = nonneg_trichotomy(d, p, pterm, ha_nonneg); // Or(pterm=0, 0<pterm)
    let eq_a_zero = req(d, pterm, zero_r);
    let lt_zero_a = rlt(d, p, zero_r, pterm);

    let final_proof = d.or_elim(
        eq_a_zero,
        lt_zero_a,
        concl,
        a_choice,
        &|d, ha0| {
            let c_choice = nonneg_trichotomy(d, p, rterm, hc_nonneg); // Or(rterm=0, 0<rterm)
            let eq_c_zero = req(d, rterm, zero_r);
            let lt_zero_c = rlt(d, p, zero_r, rterm);
            d.or_elim(
                eq_c_zero,
                lt_zero_c,
                concl,
                c_choice,
                &|d, hc0| {
                    d.lemma(
                        p.covariance_sq_le_variance_mul_of_zero_zero,
                        &[x, y, pf, n, hd, ha0, hc0],
                    )
                },
                &|d, hc_pos| {
                    let cov_yx = covariance(d, p, y, x, pf, n);
                    let swapped = d.lemma(
                        p.covariance_sq_le_variance_mul_of_pos,
                        &[y, x, pf, n, hd, hc_pos],
                    );
                    // swapped : cov_yx*cov_yx ≤ rterm*pterm
                    let comm1 = d.lemma(p.covariance_comm, &[y, x, pf, n]); // Eq(cov_yx, qterm)
                    let cov_yx_sq = rmul(d, cov_yx, cov_yx);
                    let sq_eq = rcongr(d, cov_yx, qterm, comm1, &|d, w| rmul(d, w, w));
                    // sq_eq : Eq(cov_yx_sq, qq)
                    let rterm_pterm = rmul(d, rterm, pterm);
                    let step1 = rat_eq_rewrite(d, cov_yx_sq, qq, sq_eq, swapped, &|d, w| {
                        rle(d, p, w, rterm_pterm)
                    });
                    // step1 : qq ≤ rterm_pterm
                    let comm2 = d.lemma(p.mul_comm, &[rterm, pterm]); // Eq(rterm*pterm, pterm*rterm)
                    rat_eq_rewrite(d, rterm_pterm, pr, comm2, step1, &|d, w| rle(d, p, qq, w))
                    // : qq ≤ pr
                },
            )
        },
        &|d, ha_pos| {
            d.lemma(
                p.covariance_sq_le_variance_mul_of_pos,
                &[x, y, pf, n, hd, ha_pos],
            )
        },
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
    d.declare_theorem(p.covariance_sq_le_variance_mul, ty, value)
}
