//! ADR-1631, second half: the **binomial** — a sum of `m` Bernoulli
//! variables — its mean, its variance, and Chebyshev's bound for it, at `ℚ`.
//!
//! **Why this half is at `ℚ` and not over `AlgS.OrderedRing`.** The generic
//! layer's own header (`probability_s.rs`, ADR-1616) records the obstruction
//! precisely: `AlgS.OrderedRing.variance` is the CENTRED form `E[(X−μ)²]`
//! while `covariance` is the computational form `E[XY] − E[X]E[Y]`, and
//! relating them needs `E[fun k => X k * c] ≃ E[X] · c`, which pulls a
//! constant past the weight `p k` and therefore needs `mulComm` — a field
//! ADR-1592 §2 deliberately did not give the record. So the generic shelf
//! has no `variance_eq`, hence no `variance_add_of_uncorrelated`, hence no
//! variance of a sum. The `ℚ` shelf has all three
//! (`Rat.variance_eq`, `Rat.variance_add_of_uncorrelated`,
//! `Rat.variance_sumVars`), because `ℚ` is commutative.
//!
//! That is the whole reason the split is where it is, and it is a statement
//! about the RECORD, not about the mathematics: the moment
//! `AlgS.CommOrderedRing` exists, these three theorems move up verbatim.
//!
//! **What "binomial" means here, exactly.** This development has ONE weight
//! function `p` over ONE index range, so there is no product space and no
//! joint law — `Rat.PairwiseUncorrelated` is the honest, strictly weaker
//! hypothesis the whole `ℚ` concentration section already uses in place of
//! independence (see `probability.rs`'s own note). A binomial variable is
//! therefore `Rat.sumVars X m` together with:
//!
//! * `PairwiseUncorrelated X m p n` — the trials do not correlate;
//! * `∀ j < m, E[X j] = q` and `∀ j < m, Var[X j] = q(1−q)` — they are
//!   identically distributed, with the Bernoulli moments
//!   [`super::binomial_s`] proves for the constructed two-point model.
//!
//! Under exactly those hypotheses, `E[Σ] = m·q` and `Var[Σ] = m·q(1−q)`, and
//! both proofs are the two lines the shelf was built to make possible:
//! `expectation_sumVars`/`variance_sumVars` turn the sum into a `sumRange` of
//! per-trial moments, `sumRange_congr_lt` replaces each by the constant the
//! hypothesis names, and `sum_range_const` collapses `m` copies.
//!
//! The mass function `P[X = k] = choose m k · q^k (1−q)^(m−k)` is NOT here;
//! the obstruction is stated in the ADR.

use super::RatPrelude;
use super::group::rsub;
use super::ops::{rat_eq_rewrite, rat_ty, rchain, req, rle, rlt, rmul, rone, rsum_range, rzero};
use super::probability::{
    const_fn, expectation, is_distribution, nat_as_rat, pairwise_uncorrelated, sum_range_const,
    variance, variance_summand,
};
use crate::Kernel;
use crate::KernelError;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;

/// The three `Rat.*` names this module declares.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BinomialRatNames {
    pub binomial_expectation: NameId,
    pub binomial_variance: NameId,
    pub binomial_chebyshev: NameId,
    pub fourth_moment_inequality: NameId,
}

/// Intern the three names under the `Rat` root.
pub(crate) fn intern_binomial_rat(k: &mut Kernel) -> BinomialRatNames {
    let anon = k.anon();
    let rat = k.name_str(anon, "Rat");
    BinomialRatNames {
        binomial_expectation: k.name_str(rat, "binomial_expectation"),
        binomial_variance: k.name_str(rat, "binomial_variance"),
        binomial_chebyshev: k.name_str(rat, "binomial_chebyshev"),
        fourth_moment_inequality: k.name_str(rat, "fourth_moment_inequality"),
    }
}

/// `Rat.sumVars X m`, the pointwise sum of the first `m` trials.
fn sum_vars(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId, m: ExprId) -> ExprId {
    d.const_app(p.sum_vars, &[x, m])
}

/// `fun j => Rat.expectation (X j) p n`, the per-trial mean as a function of
/// the trial index — the summand `Rat.expectation_sumVars` produces.
fn mean_of_trial(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId, pf: ExprId, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let xj = d.apply(x, &[j]);
    let body = expectation(d, p, xj, pf, n);
    d.lam_fv(j_fv, nat, body)
}

/// `fun j => Rat.variance (X j) p n`, the summand `Rat.variance_sumVars`
/// produces.
fn variance_of_trial(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    x: ExprId,
    pf: ExprId,
    n: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let xj = d.apply(x, &[j]);
    let body = variance(d, p, xj, pf, n);
    d.lam_fv(j_fv, nat, body)
}

/// `∀ j, Nat.lt j m → Eq (f j) c` — "every trial below `m` has the moment
/// `c`", the identically-distributed hypothesis in the shape
/// `Rat.sumRange_congr_lt` consumes.
fn all_trials_eq(d: &mut IntDev<'_>, m: ExprId, f: ExprId, c: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let hyp = d.lt(j, m);
    let fj = d.apply(f, &[j]);
    let body = req(d, fj, c);
    let inner = d.arrow(hyp, body);
    d.pi_fv(j_fv, nat, inner)
}

/// From `h : ∀ j, j < m → Eq (f j) c`, the `sumRange` collapse
/// `Eq (sumRange f m) (Rat.mul (natDivSucc m 0) c)` — `sumRange_congr_lt`
/// against the constant function, then [`sum_range_const`].
///
/// This is the shared spine of both moment theorems: mean and variance
/// differ only in which `f` and which `c` they hand it.
fn collapse_constant_sum(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    f: ExprId,
    c: ExprId,
    m: ExprId,
    h: ExprId,
) -> ExprId {
    let constf = const_fn(d, c);
    let congr_step = d.lemma(p.sum_range_congr_lt, &[f, constf, m, h]);
    let (_stmt, sc) = sum_range_const(d, p, c, m);

    let sum_f = rsum_range(d, p, f, m);
    let sum_const = rsum_range(d, p, constf, m);
    let m_rat = nat_as_rat(d, p, m);
    let target = rmul(d, m_rat, c);
    let (_e, chained) = rchain(d, sum_f, &[(sum_const, congr_step), (target, sc)]);
    chained
}

/// `Rat.binomial_expectation : ∀ X p n m q, (∀ j, Nat.lt j m → Eq
/// (Rat.expectation (X j) p n) q) → Eq (Rat.expectation (Rat.sumVars X m) p
/// n) (Rat.mul (Rat.natDivSucc m 0) q)` — `E[Σ_{j<m} X_j] = m·q`.
///
/// **Two lines, and that is the measurement.** `Rat.expectation_sumVars`
/// (linearity over a family) turns the left side into `sumRange (fun j =>
/// E[X_j]) m`; [`collapse_constant_sum`] replaces each term by `q` and sums
/// `m` copies. No distribution hypothesis is needed at all — linearity of
/// expectation does not care whether the weights sum to one, and
/// `Rat.expectation_sumVars` carries no `IsDistribution` either.
fn declare_binomial_expectation(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    names: &BinomialRatNames,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);
    let x_ty = d.arrow(nat, fn_ty);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);

    let means = mean_of_trial(d, p, x, pf, n);
    let hq_ty = all_trials_eq(d, m, means, q);
    let hq_fv = d.fresh_fvar();
    let hq = d.kernel().fvar(hq_fv);

    let sv = sum_vars(d, p, x, m);
    let lhs = expectation(d, p, sv, pf, n);
    let sum_means = rsum_range(d, p, means, m);
    let m_rat = nat_as_rat(d, p, m);
    let rhs = rmul(d, m_rat, q);

    let linearity = d.lemma(p.expectation_sum_vars, &[x, pf, n, m]);
    let collapse = collapse_constant_sum(d, p, means, q, m, hq);
    let (_e, core) = rchain(d, lhs, &[(sum_means, linearity), (rhs, collapse)]);

    let concl = req(d, lhs, rhs);
    let ty = {
        let with_hq = d.arrow(hq_ty, concl);
        let with_q = d.pi_fv(q_fv, carrier, with_hq);
        let with_m = d.pi_fv(m_fv, nat, with_q);
        let with_n = d.pi_fv(n_fv, nat, with_m);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        d.pi_fv(x_fv, x_ty, with_pf)
    };
    let value = {
        let with_hq = d.lam_fv(hq_fv, hq_ty, core);
        let with_q = d.lam_fv(q_fv, carrier, with_hq);
        let with_m = d.lam_fv(m_fv, nat, with_q);
        let with_n = d.lam_fv(n_fv, nat, with_m);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        d.lam_fv(x_fv, x_ty, with_pf)
    };
    d.declare_theorem(names.binomial_expectation, ty, value)
}

/// `Rat.binomial_variance : ∀ X p n, IsDistribution p n → ∀ m q,
/// PairwiseUncorrelated X m p n → (∀ j, Nat.lt j m → Eq (Rat.variance (X j)
/// p n) (Rat.mul q (Rat.sub Rat.one q))) → Eq (Rat.variance (Rat.sumVars X
/// m) p n) (Rat.mul (Rat.natDivSucc m 0) (Rat.mul q (Rat.sub Rat.one q)))` —
/// `Var[Σ_{j<m} X_j] = m·q(1−q)`.
///
/// The same two lines as the mean, over `Rat.variance_sumVars` instead of
/// `Rat.expectation_sumVars`. The two extra hypotheses are exactly the ones
/// that theorem carries and no more: `IsDistribution` (the variance of a sum
/// genuinely needs the weights to be a distribution — `Rat.variance_eq`,
/// which `variance_add_of_uncorrelated` rests on, does) and
/// `PairwiseUncorrelated` (without it the cross terms do not vanish, and the
/// conclusion is false, not merely unproved).
///
/// The `q(1−q)` shape in the hypothesis is not decoration: it is the shape
/// [`super::binomial_s`]'s `bernoulli_variance` and the `ℚ` development's own
/// `Rat.variance_indicator` both produce, so this theorem composes with
/// either without a rewrite.
fn declare_binomial_variance(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    names: &BinomialRatNames,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);
    let x_ty = d.arrow(nat, fn_ty);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let hd_ty = is_distribution(d, p, pf, n);
    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);

    let hpw_ty = pairwise_uncorrelated(d, p, x, m, pf, n);
    let hpw_fv = d.fresh_fvar();
    let hpw = d.kernel().fvar(hpw_fv);

    let one_r = rone(d, p);
    let one_minus_q = rsub(d, p, one_r, q);
    let q1mq = rmul(d, q, one_minus_q);

    let variances = variance_of_trial(d, p, x, pf, n);
    let hv_ty = all_trials_eq(d, m, variances, q1mq);
    let hv_fv = d.fresh_fvar();
    let hv = d.kernel().fvar(hv_fv);

    let sv = sum_vars(d, p, x, m);
    let lhs = variance(d, p, sv, pf, n);
    let sum_variances = rsum_range(d, p, variances, m);
    let m_rat = nat_as_rat(d, p, m);
    let rhs = rmul(d, m_rat, q1mq);

    let additivity = d.lemma(p.variance_sum_vars, &[x, pf, n, hd, m, hpw]);
    let collapse = collapse_constant_sum(d, p, variances, q1mq, m, hv);
    let (_e, core) = rchain(d, lhs, &[(sum_variances, additivity), (rhs, collapse)]);

    let concl = req(d, lhs, rhs);
    let ty = {
        let with_hv = d.arrow(hv_ty, concl);
        let with_hpw = d.arrow(hpw_ty, with_hv);
        let with_q = d.pi_fv(q_fv, carrier, with_hpw);
        let with_m = d.pi_fv(m_fv, nat, with_q);
        let with_hd = d.arrow(hd_ty, with_m);
        let with_n = d.pi_fv(n_fv, nat, with_hd);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        d.pi_fv(x_fv, x_ty, with_pf)
    };
    let value = {
        let with_hv = d.lam_fv(hv_fv, hv_ty, core);
        let with_hpw = d.lam_fv(hpw_fv, hpw_ty, with_hv);
        let with_q = d.lam_fv(q_fv, carrier, with_hpw);
        let with_m = d.lam_fv(m_fv, nat, with_q);
        let with_hd = d.lam_fv(hd_fv, hd_ty, with_m);
        let with_n = d.lam_fv(n_fv, nat, with_hd);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        d.lam_fv(x_fv, x_ty, with_pf)
    };
    d.declare_theorem(names.binomial_variance, ty, value)
}

/// `Rat.binomial_chebyshev` — Chebyshev's inequality with the binomial's
/// variance substituted, so the bound is `m·q(1−q)` and no longer mentions
/// `variance` at all:
///
/// ```text
/// ∀ a X p n, IsDistribution p n → ∀ m q,
///   PairwiseUncorrelated X m p n →
///   (∀ j, j < m → variance (X j) p n = q·(1−q)) →
///   lt zero a →
///   le (a² · E[𝟙[a² ≤ (Σ − E[Σ])²]]) (natDivSucc m 0 · (q·(1−q)))
/// ```
///
/// **Free, and the ADR says why that is the point.** `Rat.chebyshev_inequality`
/// already bounds that left side by `Var[Σ]`; [`declare_binomial_variance`]
/// says what `Var[Σ]` is; the corollary is one `rat_eq_rewrite` under
/// `le _ ·`. The classical form divides through by `a²` to read
/// `P(|Σ − E[Σ]| ≥ a) ≤ m·q(1−q)/a²`; this is the same content before that
/// division, in the multiplied-through shape that needs no `Rat.inv`.
fn declare_binomial_chebyshev(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    names: &BinomialRatNames,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);
    let x_ty = d.arrow(nat, fn_ty);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let hd_ty = is_distribution(d, p, pf, n);
    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);

    let hpw_ty = pairwise_uncorrelated(d, p, x, m, pf, n);
    let hpw_fv = d.fresh_fvar();
    let hpw = d.kernel().fvar(hpw_fv);

    let one_r = rone(d, p);
    let one_minus_q = rsub(d, p, one_r, q);
    let q1mq = rmul(d, q, one_minus_q);

    let variances = variance_of_trial(d, p, x, pf, n);
    let hv_ty = all_trials_eq(d, m, variances, q1mq);
    let hv_fv = d.fresh_fvar();
    let hv = d.kernel().fvar(hv_fv);

    let zero_r = rzero(d, p);
    let ha_ty = rlt(d, p, zero_r, a);
    let ha_fv = d.fresh_fvar();
    let ha = d.kernel().fvar(ha_fv);

    // The left side, rebuilt exactly as `Rat.chebyshev_inequality` states it
    // at `X := Rat.sumVars X m`.
    let sv = sum_vars(d, p, x, m);
    let mu = expectation(d, p, sv, pf, n);
    let dev_sq = variance_summand(d, p, sv, mu);
    let a_sq = rmul(d, a, a);
    let ind = d.const_app(p.indicator, &[a_sq, dev_sq]);
    let e_ind = expectation(d, p, ind, pf, n);
    let bound_lhs = rmul(d, a_sq, e_ind);

    let cheb = d.lemma(p.chebyshev_inequality, &[a, sv, pf, n, hd, ha]);
    // cheb : le bound_lhs (variance sv pf n)

    let var_sv = variance(d, p, sv, pf, n);
    let m_rat = nat_as_rat(d, p, m);
    let rhs = rmul(d, m_rat, q1mq);
    let var_eq = d.lemma(names.binomial_variance, &[x, pf, n, hd, m, q, hpw, hv]);
    // var_eq : Eq (variance sv pf n) (m_rat * q1mq)

    let core = rat_eq_rewrite(d, var_sv, rhs, var_eq, cheb, &|d, t| {
        rle(d, p, bound_lhs, t)
    });

    let concl = rle(d, p, bound_lhs, rhs);
    let ty = {
        let with_ha = d.arrow(ha_ty, concl);
        let with_hv = d.arrow(hv_ty, with_ha);
        let with_hpw = d.arrow(hpw_ty, with_hv);
        let with_q = d.pi_fv(q_fv, carrier, with_hpw);
        let with_m = d.pi_fv(m_fv, nat, with_q);
        let with_hd = d.arrow(hd_ty, with_m);
        let with_n = d.pi_fv(n_fv, nat, with_hd);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        let with_x = d.pi_fv(x_fv, x_ty, with_pf);
        d.pi_fv(a_fv, carrier, with_x)
    };
    let value = {
        let with_ha = d.lam_fv(ha_fv, ha_ty, core);
        let with_hv = d.lam_fv(hv_fv, hv_ty, with_ha);
        let with_hpw = d.lam_fv(hpw_fv, hpw_ty, with_hv);
        let with_q = d.lam_fv(q_fv, carrier, with_hpw);
        let with_m = d.lam_fv(m_fv, nat, with_q);
        let with_hd = d.lam_fv(hd_fv, hd_ty, with_m);
        let with_n = d.lam_fv(n_fv, nat, with_hd);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_x = d.lam_fv(x_fv, x_ty, with_pf);
        d.lam_fv(a_fv, carrier, with_x)
    };
    d.declare_theorem(names.binomial_chebyshev, ty, value)
}

/// `Rat.fourth_moment_inequality : ∀ a X p n, IsDistribution p n → lt zero a
/// → le ((a·a)·(a·a) · expectation (Rat.indicator ((a·a)·(a·a)) (fun k =>
/// ((X k − μ)·(X k − μ))·((X k − μ)·(X k − μ)))) p n) (expectation (fun k =>
/// …) p n)` — **the fourth-moment tail bound**, i.e.
/// `P(|X − E X| ≥ a) ≤ E[(X − E X)⁴] / a⁴` in the multiplied-through form
/// that needs no `Rat.inv`.
///
/// **This is the tail bound this lane could reach without an exponential.**
/// The roadmap item asked for Hoeffding; the two obstructions are recorded
/// in ADR-1631 and are structural, not effort:
///
/// 1. Hoeffding needs `E[∏_j f(X_j)] = ∏_j E[f(X_j)]`, which is a statement
///    about a JOINT law over a product space. This development has one weight
///    function over one index range — `probability.rs`'s own header says so —
///    and `Rat.PairwiseUncorrelated` is the strictly weaker hypothesis it
///    uses instead. There is no product distribution to state the identity
///    over, and none can be built without a second index.
/// 2. Hoeffding's lemma needs `exp` on the carrier the moments live on.
///    `CReal.expFn` exists on ℝ, but `CReal.expFn_add` (the functional
///    equation `e^{x+y} = e^x·e^y`, without which the product step is not
///    even statable) does not — measured, not assumed.
///
/// So the tail bound that IS reachable is Markov at the fourth power, and
/// this is it: `Rat.markov_constructed` at threshold `a⁴` against the
/// summand `((X−μ)²)²`, whose nonnegativity is `Rat.sq_nonneg` applied to
/// `(X−μ)²` rather than to `X−μ`, and whose threshold positivity is
/// `Rat.mul_pos` twice. Nothing else is needed, and no hypothesis beyond the
/// ones Markov already carries.
///
/// It is stated for an ARBITRARY `X` rather than for `sumVars`, because that
/// is where its content is: the binomial specialisation is this theorem at
/// `X := Rat.sumVars X m`, exactly as [`declare_binomial_chebyshev`] is
/// `Rat.chebyshev_inequality` there.
fn declare_fourth_moment_inequality(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    names: &BinomialRatNames,
) -> Result<(), KernelError> {
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

    let hd_ty = is_distribution(d, p, pf, n);
    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);
    let zero_r = rzero(d, p);
    let ha_ty = rlt(d, p, zero_r, a);
    let ha_fv = d.fresh_fvar();
    let ha = d.kernel().fvar(ha_fv);

    let mu = expectation(d, p, x, pf, n);
    // `fun k => ((X k - mu) * (X k - mu)) * ((X k - mu) * (X k - mu))`.
    let quartic = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let xk = d.apply(x, &[k]);
        let gap = rsub(d, p, xk, mu);
        let sq = rmul(d, gap, gap);
        let body = rmul(d, sq, sq);
        d.lam_fv(k_fv, nat, body)
    };

    let a_sq = rmul(d, a, a);
    let a_4 = rmul(d, a_sq, a_sq);

    let hy = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let klt_fv = d.fresh_fvar();
        let klt_ty = d.lt(k, n);
        let xk = d.apply(x, &[k]);
        let gap = rsub(d, p, xk, mu);
        let sq = rmul(d, gap, gap);
        let nonneg = d.lemma(p.sq_nonneg, &[sq]);
        let with_klt = d.lam_fv(klt_fv, klt_ty, nonneg);
        d.lam_fv(k_fv, nat, with_klt)
    };
    let ha_sq = d.lemma(p.mul_pos, &[a, a, ha, ha]);
    let ha_4 = d.lemma(p.mul_pos, &[a_sq, a_sq, ha_sq, ha_sq]);

    let core = d.lemma(p.markov_constructed, &[a_4, quartic, pf, n, hd, hy, ha_4]);

    let concl = {
        let ind = d.const_app(p.indicator, &[a_4, quartic]);
        let e_ind = expectation(d, p, ind, pf, n);
        let lhs = rmul(d, a_4, e_ind);
        let rhs = expectation(d, p, quartic, pf, n);
        rle(d, p, lhs, rhs)
    };
    let ty = {
        let with_ha = d.arrow(ha_ty, concl);
        let with_hd = d.arrow(hd_ty, with_ha);
        let with_n = d.pi_fv(n_fv, nat, with_hd);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        let with_x = d.pi_fv(x_fv, fn_ty, with_pf);
        d.pi_fv(a_fv, carrier, with_x)
    };
    let value = {
        let with_ha = d.lam_fv(ha_fv, ha_ty, core);
        let with_hd = d.lam_fv(hd_fv, hd_ty, with_ha);
        let with_n = d.lam_fv(n_fv, nat, with_hd);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_x = d.lam_fv(x_fv, fn_ty, with_pf);
        d.lam_fv(a_fv, carrier, with_x)
    };
    d.declare_theorem(names.fourth_moment_inequality, ty, value)
}

/// Declare the four `ℚ` binomial/tail theorems.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(crate) fn declare_binomial_rat_all(
    d: &mut IntDev<'_>,
    p: &RatPrelude,
) -> Result<(), KernelError> {
    let names = p.binomial_rat;
    declare_binomial_expectation(d, *p, &names)?;
    declare_binomial_variance(d, *p, &names)?;
    declare_binomial_chebyshev(d, *p, &names)?;
    declare_fourth_moment_inequality(d, *p, &names)?;
    Ok(())
}

#[cfg(test)]
#[path = "binomial_rat_tests.rs"]
mod binomial_rat_tests;
