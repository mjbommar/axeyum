//! ADR-1653 (roadmap W3-12, second slice): **four-wise uncorrelatedness, the
//! fourth central moment of a sum, and the `1/m²` tail that follows** — the
//! first Hoeffding-class rate this carrier can state.
//!
//! ## Why this rate and not Hoeffding
//!
//! [`super::binomial_rat`]'s own header records the two obstructions to
//! Hoeffding, and neither has moved: `E[∏ f(X_j)] = ∏ E[f(X_j)]` is a
//! statement about a JOINT law over a product space, and this development has
//! one weight function over one index range; and Hoeffding's lemma needs
//! `CReal.expFn_add`, which does not exist on any carrier here.
//!
//! ADR-1631 named the next bounded rate that IS statable, and this module is
//! it: `E[(Σ Y_i)⁴] ≤ Σ M₄ + 3(Σ σ²)²` under a **four-wise** uncorrelatedness
//! hypothesis. It is statable for exactly the reason Chebyshev's bound was —
//! it constrains covariance-like quantities (mixed moments that vanish), not a
//! joint law. Fed through `Rat.fourth_moment_inequality` it gives a tail
//! decaying like `1/m²` in the sample size, where Chebyshev gives `1/m`.
//!
//! ## What `Rat.FourwiseUncorrelated` says, and what it does not
//!
//! It is stated about an ALREADY-CENTRED family `Y` (the intended instance is
//! `Y i := fun k => X i k − E[X i]`), as two conditions:
//!
//! 1. every mixed fourth moment with a **lone index** vanishes —
//!    `E[Y_a Y_b Y_c Y_l] = 0` whenever `l` differs from each of `a`, `b` and
//!    `c`. That single condition covers all three shapes the multinomial
//!    expansion produces with an unpaired index (`a b c l` all distinct,
//!    `a a b c`, and `a a a l`), which is why it is one `∀` and not three;
//! 2. the squares are uncorrelated — `E[Y_i² Y_j²] = E[Y_i²]·E[Y_j²]` for
//!    `i ≠ j`.
//!
//! Independence would imply both. Independence is not expressible here (there
//! is no product space — see `probability.rs`'s own header), so this is the
//! honest, strictly weaker hypothesis, exactly the role
//! `Rat.PairwiseUncorrelated` plays for the variance of a sum, one moment up.
//!
//! ## The shelf this needed
//!
//! The whole cost of the moment bound is **peeling a `Rat.sumVars` out of an
//! expectation**, which is why the two lemmas below come first and carry no
//! hypotheses at all:
//!
//! * `Rat.expectation_sumVars_mul` — `E[(Σ_{i<m} Y_i)·W] = Σ_{i<m} E[Y_i·W]`
//!   for an ARBITRARY `W`, in particular a `W` that itself mentions the sum;
//! * `Rat.expectation_sumVars_mul_eq_zero` — the same with every term known to
//!   vanish, which is what an unpaired index buys.
//!
//! Every higher step here is those two, a pointwise ring identity emitted by
//! [`crate::ring::rat`] (ADR-1582), and `sumRange_congr`/`sumRange_le`.

use super::RatPrelude;
use super::group::rsub;
use super::ops::{
    nat_rewrite_prop, radd, rat_eq_rewrite, rat_ty, rchain, rcongr, req, rle, rlt, rmul, rneg,
    rrefl, rsum_range, rsymm, rtrans, rzero,
};
use super::probability::{const_fn, expectation, is_distribution};
use crate::Kernel;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;

/// Delta height for `Rat.FourwiseUncorrelated`: above
/// `Rat.PairwiseUncorrelated` (`probability.rs`'s
/// `PAIRWISE_UNCORRELATED_HEIGHT`, 41) and every other height this prelude
/// declares, keeping `rat_prelude`'s single monotone sequence.
const FOURWISE_UNCORRELATED_HEIGHT: u16 = 42;

/// The `Rat.*` names this module declares.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FourthMomentNames {
    /// `Rat.expectation_sumVars_mul : ∀ Y W p n m,
    /// expectation (fun k => sumVars Y m k * W k) p n
    ///   = sumRange (fun i => expectation (fun k => Y i k * W k) p n) m`.
    pub expectation_sum_vars_mul: NameId,
    /// `Rat.expectation_sumVars_mul_eq_zero : ∀ Y W p n m,
    /// (∀ i, Lt i m → expectation (fun k => Y i k * W k) p n = zero) →
    /// expectation (fun k => sumVars Y m k * W k) p n = zero`.
    pub expectation_sum_vars_mul_eq_zero: NameId,
    /// `Rat.FourwiseUncorrelated : (Nat → Nat → Rat) → Nat → (Nat → Rat) →
    /// Nat → Prop` — see the module docs.
    pub fourwise_uncorrelated: NameId,
    /// `Rat.expectation_sq_sumVars_mul_sq : ∀ Y z p n m, (the pairing
    /// hypothesis) → expectation (fun k => (sumVars Y m k * sumVars Y m k) *
    /// (z k * z k)) p n = sumRange (fun i => expectation (fun k => (Y i k * Y
    /// i k) * (z k * z k)) p n) m` — the ONE cross term the fourth power of a
    /// sum does not kill.
    pub expectation_sq_sum_vars_mul_sq: NameId,
    /// `Rat.fourth_moment_sumVars_le` — the fourth central moment of a sum,
    /// bounded by `Σ M₄ + 3(Σ σ²)²` under four-wise uncorrelatedness.
    pub fourth_moment_sum_vars_le: NameId,
    /// `Rat.fourth_moment_tailSumVars` — the `1/m²` tail that follows, the
    /// first Hoeffding-class rate this carrier can state.
    pub fourth_moment_tail_sum_vars: NameId,
}

/// Intern the names under the `Rat` root.
pub(crate) fn intern_fourth_moment(k: &mut Kernel) -> FourthMomentNames {
    let anon = k.anon();
    let rat = k.name_str(anon, "Rat");
    FourthMomentNames {
        expectation_sum_vars_mul: k.name_str(rat, "expectation_sumVars_mul"),
        expectation_sum_vars_mul_eq_zero: k.name_str(rat, "expectation_sumVars_mul_eq_zero"),
        fourwise_uncorrelated: k.name_str(rat, "FourwiseUncorrelated"),
        expectation_sq_sum_vars_mul_sq: k.name_str(rat, "expectation_sq_sumVars_mul_sq"),
        fourth_moment_sum_vars_le: k.name_str(rat, "fourth_moment_sumVars_le"),
        fourth_moment_tail_sum_vars: k.name_str(rat, "fourth_moment_tailSumVars"),
    }
}

// --- redex-free builders ----------------------------------------------------
//
// `IntDev::apply` does NOT beta-reduce, so `d.apply(<a lambda>, &[k])` leaves a
// redex behind. The kernel is content with one (it is defeq), but
// `ring::rat`'s parser is not: a redex is an opaque ATOM to it, and the
// identity it is then asked to prove is not one. Every function-valued term
// below is therefore built from a BODY BUILDER applied to the binder, never by
// applying a previously built lambda.

/// `fun k => body k`, at `Nat → Rat`.
fn rat_fn(d: &mut IntDev<'_>, body: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let b = body(d, k);
    d.lam_fv(k_fv, nat, b)
}

/// `Rat.sumVars Y m k` — a constant application, so redex-free.
fn sv_at(d: &mut IntDev<'_>, p: RatPrelude, y: ExprId, m: ExprId, k: ExprId) -> ExprId {
    let f = d.const_app(p.sum_vars, &[y, m]);
    d.apply(f, &[k])
}

/// `Y i k`, with `Y` a free variable — redex-free.
fn var_at(d: &mut IntDev<'_>, y: ExprId, i: ExprId, k: ExprId) -> ExprId {
    d.apply(y, &[i, k])
}

/// `Rat.expectation (fun k => body k) p n`.
fn expect_of(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    body: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
    pf: ExprId,
    n: ExprId,
) -> ExprId {
    let f = rat_fn(d, body);
    expectation(d, p, f, pf, n)
}

/// `fun k => body k * p k` — the summand `Rat.expectation` unfolds to, built
/// redex-free from `body`.
fn weighted_of(
    d: &mut IntDev<'_>,
    body: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
    pf: ExprId,
) -> ExprId {
    rat_fn(d, &|d, k| {
        let b = body(d, k);
        let pk = d.apply(pf, &[k]);
        rmul(d, b, pk)
    })
}

/// `Eq Rat (Rat.mul Rat.zero c) Rat.zero` — `mul_comm` then `mul_zero`.
/// (`probability.rs` carries the same two lines privately; ℚ has `mul_zero`
/// on the right only.)
fn zero_mul(d: &mut IntDev<'_>, p: RatPrelude, c: ExprId) -> ExprId {
    let zero_r = rzero(d, p);
    let lhs = rmul(d, zero_r, c);
    let flipped = rmul(d, c, zero_r);
    let step1 = d.lemma(p.mul_comm, &[zero_r, c]);
    let step2 = d.lemma(p.mul_zero, &[c]);
    rtrans(d, lhs, flipped, zero_r, step1, step2)
}

// --- the shelf: peeling a `sumVars` out of an expectation -------------------

/// `Rat.expectation_sumVars_mul : ∀ Y W p n m,
/// expectation (fun k => sumVars Y m k * W k) p n
///   = sumRange (fun i => expectation (fun k => Y i k * W k) p n) m`
/// — **the workhorse of this module**, and the reason the fourth-moment
/// expansion is affordable at all.
///
/// It carries NO hypothesis: not `IsDistribution`, not uncorrelatedness, not
/// even a bound on `W`. `W` is an arbitrary `Nat → Rat`, and in the uses below
/// it MENTIONS the sum it is being peeled out of — which is exactly what makes
/// one lemma enough for `E[Σ³·z]`, `E[Σ²·z²]` and `E[Σ·z³]` alike.
///
/// Induction on `m`. **Base**: `sumVars Y 0 k` δι-reduces to
/// `sumRange (fun t => Y t k) 0`, which `Rat.sumRange_zero` sends to `zero`,
/// so every summand of the weighted sum is pointwise zero and
/// `Rat.sumRange_eq_zero_of_lt` closes it. **Successor**:
/// `sumVars Y (succ j) k` ι-reduces to `sumVars Y j k + Y j k`
/// (`Rat.sumRange_succ`), the summand distributes by
/// [`RatPrelude::right_distrib`], `Rat.expectation_add` splits the
/// expectation, and the inductive hypothesis lands the first half on
/// `sumRange _ j` — whose `Rat.sumRange_succ` step is the goal definitionally.
fn declare_expectation_sum_vars_mul(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    names: &FourthMomentNames,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);
    let x_ty = d.arrow(nat, fn_ty);

    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    // `fun i => expectation (fun k => Y i k * W k) p n`.
    let per_index = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let body = expect_of(
            d,
            p,
            &|d, k| {
                let yi = var_at(d, y, i, k);
                let wk = d.apply(w, &[k]);
                rmul(d, yi, wk)
            },
            pf,
            n,
        );
        d.lam_fv(i_fv, nat, body)
    };

    let motive = |d: &mut IntDev<'_>, bound: ExprId| -> ExprId {
        let lhs = expect_of(
            d,
            p,
            &|d, k| {
                let s = sv_at(d, p, y, bound, k);
                let wk = d.apply(w, &[k]);
                rmul(d, s, wk)
            },
            pf,
            n,
        );
        let rhs = rsum_range(d, p, per_index, bound);
        req(d, lhs, rhs)
    };
    let stmt = motive(d, m);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_n = d.zero();
            let zero_r = rzero(d, p);
            let summand = weighted_of(
                d,
                &|d, k| {
                    let s = sv_at(d, p, y, zero_n, k);
                    let wk = d.apply(w, &[k]);
                    rmul(d, s, wk)
                },
                pf,
            );
            let pointwise = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let klt_fv = d.fresh_fvar();
                let klt_ty = d.lt(k, n);

                // `fun t => Y t k`, the summand `Rat.sumVars Y 0 k` unfolds to.
                let inner = {
                    let t_fv = d.fresh_fvar();
                    let t = d.kernel().fvar(t_fv);
                    let ytk = var_at(d, y, t, k);
                    d.lam_fv(t_fv, nat, ytk)
                };
                let inner_sum = rsum_range(d, p, inner, zero_n);
                let hzero = d.lemma(p.sum_range_zero, &[inner]);
                let wk = d.apply(w, &[k]);
                let pk = d.apply(pf, &[k]);
                let lift = rcongr(d, inner_sum, zero_r, hzero, &|d, t| {
                    let a = rmul(d, t, wk);
                    rmul(d, a, pk)
                });
                // `(zero * W k) * p k = zero * p k = zero`.
                let zw = rmul(d, zero_r, wk);
                let mid = rmul(d, zw, pk);
                let step_a = zero_mul(d, p, wk);
                let step_b = rcongr(d, zw, zero_r, step_a, &|d, t| rmul(d, t, pk));
                let zp = rmul(d, zero_r, pk);
                let step_c = zero_mul(d, p, pk);
                let collapse = rtrans(d, mid, zp, zero_r, step_b, step_c);

                let start = {
                    let a = rmul(d, inner_sum, wk);
                    rmul(d, a, pk)
                };
                let full = rtrans(d, start, mid, zero_r, lift, collapse);
                let with_klt = d.lam_fv(klt_fv, klt_ty, full);
                d.lam_fv(k_fv, nat, with_klt)
            };
            d.lemma(p.sum_range_eq_zero_of_lt, &[summand, n, pointwise])
        },
        &|d, j, ih| {
            let sj = d.succ(j);

            let head_fn = rat_fn(d, &|d, k| {
                let s = sv_at(d, p, y, j, k);
                let wk = d.apply(w, &[k]);
                rmul(d, s, wk)
            });
            let tail_fn = rat_fn(d, &|d, k| {
                let yj = var_at(d, y, j, k);
                let wk = d.apply(w, &[k]);
                rmul(d, yj, wk)
            });

            let start = expect_of(
                d,
                p,
                &|d, k| {
                    let s = sv_at(d, p, y, sj, k);
                    let wk = d.apply(w, &[k]);
                    rmul(d, s, wk)
                },
                pf,
                n,
            );
            let split = expect_of(
                d,
                p,
                &|d, k| {
                    let s = sv_at(d, p, y, j, k);
                    let wk = d.apply(w, &[k]);
                    let a = rmul(d, s, wk);
                    let yj = var_at(d, y, j, k);
                    let b = rmul(d, yj, wk);
                    radd(d, a, b)
                },
                pf,
                n,
            );

            // step 1: peel `sumVars Y (succ j) k` and distribute pointwise.
            let step1 = {
                let wsum = weighted_of(
                    d,
                    &|d, k| {
                        let s = sv_at(d, p, y, sj, k);
                        let wk = d.apply(w, &[k]);
                        rmul(d, s, wk)
                    },
                    pf,
                );
                let wsplit = weighted_of(
                    d,
                    &|d, k| {
                        let s = sv_at(d, p, y, j, k);
                        let wk = d.apply(w, &[k]);
                        let a = rmul(d, s, wk);
                        let yj = var_at(d, y, j, k);
                        let b = rmul(d, yj, wk);
                        radd(d, a, b)
                    },
                    pf,
                );
                let pointwise = {
                    let k_fv = d.fresh_fvar();
                    let k = d.kernel().fvar(k_fv);
                    let inner = {
                        let t_fv = d.fresh_fvar();
                        let t = d.kernel().fvar(t_fv);
                        let ytk = var_at(d, y, t, k);
                        d.lam_fv(t_fv, nat, ytk)
                    };
                    let hsucc = d.lemma(p.sum_range_succ, &[inner, j]);
                    let sv_sj = sv_at(d, p, y, sj, k);
                    let sv_j = sv_at(d, p, y, j, k);
                    let yjk = var_at(d, y, j, k);
                    let joined = radd(d, sv_j, yjk);
                    let wk = d.apply(w, &[k]);
                    let pk = d.apply(pf, &[k]);
                    let lift = rcongr(d, sv_sj, joined, hsucc, &|d, t| {
                        let a = rmul(d, t, wk);
                        rmul(d, a, pk)
                    });
                    let joined_w = rmul(d, joined, wk);
                    let mid = rmul(d, joined_w, pk);
                    let a = rmul(d, sv_j, wk);
                    let b = rmul(d, yjk, wk);
                    let summed = radd(d, a, b);
                    let rd = d.lemma(p.right_distrib, &[sv_j, yjk, wk]);
                    let distribute = rcongr(d, joined_w, summed, rd, &|d, t| rmul(d, t, pk));
                    let target = rmul(d, summed, pk);
                    let from = {
                        let s = rmul(d, sv_sj, wk);
                        rmul(d, s, pk)
                    };
                    let full = rtrans(d, from, mid, target, lift, distribute);
                    d.lam_fv(k_fv, nat, full)
                };
                d.lemma(p.sum_range_congr, &[wsum, wsplit, n, pointwise])
            };

            // step 2: `Rat.expectation_add` splits it.
            let e_head = expectation(d, p, head_fn, pf, n);
            let e_tail = expectation(d, p, tail_fn, pf, n);
            let pair = radd(d, e_head, e_tail);
            let step2 = d.lemma(p.expectation_add, &[head_fn, tail_fn, pf, n]);

            // step 3: the inductive hypothesis on the first half.
            let sum_j = rsum_range(d, p, per_index, j);
            let step3 = rcongr(d, e_head, sum_j, ih, &|d, t| radd(d, t, e_tail));
            let landed = radd(d, sum_j, e_tail);

            let (_end, proof) = rchain(d, start, &[(split, step1), (pair, step2), (landed, step3)]);
            proof
        },
        m,
    );

    let value = {
        let with_m = d.lam_fv(m_fv, nat, proof);
        let with_n = d.lam_fv(n_fv, nat, with_m);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_w = d.lam_fv(w_fv, fn_ty, with_pf);
        d.lam_fv(y_fv, x_ty, with_w)
    };
    let ty = {
        let with_m = d.pi_fv(m_fv, nat, stmt);
        let with_n = d.pi_fv(n_fv, nat, with_m);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        let with_w = d.pi_fv(w_fv, fn_ty, with_pf);
        d.pi_fv(y_fv, x_ty, with_w)
    };
    d.declare_theorem(names.expectation_sum_vars_mul, ty, value)
}

/// `Rat.expectation_sumVars_mul_eq_zero : ∀ Y W p n m,
/// (∀ i, Lt i m → expectation (fun k => Y i k * W k) p n = zero) →
/// expectation (fun k => sumVars Y m k * W k) p n = zero` —
/// [`declare_expectation_sum_vars_mul`] followed by
/// `Rat.sumRange_eq_zero_of_lt`.
///
/// This is the form every ODD term of the fourth-power expansion uses: an
/// unpaired index makes each per-index expectation vanish, and the sum of
/// bounded pointwise zeros is zero. The hypothesis is BOUNDED (`Lt i m →`),
/// which is why `sumRange_eq_zero_of_lt` and not `sumRange_congr` closes it —
/// `Rat.FourwiseUncorrelated` supplies zeros only inside its own range, never
/// universally.
fn declare_expectation_sum_vars_mul_eq_zero(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    names: &FourthMomentNames,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);
    let x_ty = d.arrow(nat, fn_ty);

    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let per_index = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let body = expect_of(
            d,
            p,
            &|d, k| {
                let yi = var_at(d, y, i, k);
                let wk = d.apply(w, &[k]);
                rmul(d, yi, wk)
            },
            pf,
            n,
        );
        d.lam_fv(i_fv, nat, body)
    };

    let zero_r = rzero(d, p);
    let hyp_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ilt = d.lt(i, m);
        let ei = expect_of(
            d,
            p,
            &|d, k| {
                let yi = var_at(d, y, i, k);
                let wk = d.apply(w, &[k]);
                rmul(d, yi, wk)
            },
            pf,
            n,
        );
        let concl = req(d, ei, zero_r);
        let inner = d.arrow(ilt, concl);
        d.pi_fv(i_fv, nat, inner)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let lhs = expect_of(
        d,
        p,
        &|d, k| {
            let s = sv_at(d, p, y, m, k);
            let wk = d.apply(w, &[k]);
            rmul(d, s, wk)
        },
        pf,
        n,
    );
    let concl = req(d, lhs, zero_r);

    let peel = d.lemma(names.expectation_sum_vars_mul, &[y, w, pf, n, m]);
    let collapse = d.lemma(p.sum_range_eq_zero_of_lt, &[per_index, m, h]);
    let sum_m = rsum_range(d, p, per_index, m);
    let core = rtrans(d, lhs, sum_m, zero_r, peel, collapse);

    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, core);
        let with_m = d.lam_fv(m_fv, nat, with_h);
        let with_n = d.lam_fv(n_fv, nat, with_m);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_w = d.lam_fv(w_fv, fn_ty, with_pf);
        d.lam_fv(y_fv, x_ty, with_w)
    };
    let ty = {
        let with_h = d.arrow(hyp_ty, concl);
        let with_m = d.pi_fv(m_fv, nat, with_h);
        let with_n = d.pi_fv(n_fv, nat, with_m);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        let with_w = d.pi_fv(w_fv, fn_ty, with_pf);
        d.pi_fv(y_fv, x_ty, with_w)
    };
    d.declare_theorem(names.expectation_sum_vars_mul_eq_zero, ty, value)
}

// --- four-wise uncorrelatedness ---------------------------------------------

/// `expectation (fun k => ((Y a k * Y b k) * Y c k) * Y l k) p n` — the
/// canonical left-nested mixed fourth moment `Rat.FourwiseUncorrelated`'s
/// first condition is stated over. Every expansion term is rewritten into this
/// shape by a `ring::rat` identity before the hypothesis is applied, which is
/// why the association order can be fixed once, here.
pub(super) fn mixed_moment(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    y: ExprId,
    idx: [ExprId; 4],
    pf: ExprId,
    n: ExprId,
) -> ExprId {
    expect_of(
        d,
        p,
        &|d, k| {
            let a = var_at(d, y, idx[0], k);
            let b = var_at(d, y, idx[1], k);
            let c = var_at(d, y, idx[2], k);
            let l = var_at(d, y, idx[3], k);
            let ab = rmul(d, a, b);
            let abc = rmul(d, ab, c);
            rmul(d, abc, l)
        },
        pf,
        n,
    )
}

/// `expectation (fun k => Y i k * Y i k) p n` — a centred variable's second
/// moment, i.e. its variance once `E[Y i] = 0`.
pub(super) fn second_moment(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    y: ExprId,
    i: ExprId,
    pf: ExprId,
    n: ExprId,
) -> ExprId {
    expect_of(
        d,
        p,
        &|d, k| {
            let a = var_at(d, y, i, k);
            rmul(d, a, a)
        },
        pf,
        n,
    )
}

/// `expectation (fun k => (Y i k * Y i k) * (Y j k * Y j k)) p n`.
pub(super) fn paired_moment(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    y: ExprId,
    i: ExprId,
    j: ExprId,
    pf: ExprId,
    n: ExprId,
) -> ExprId {
    expect_of(
        d,
        p,
        &|d, k| {
            let a = var_at(d, y, i, k);
            let b = var_at(d, y, j, k);
            let aa = rmul(d, a, a);
            let bb = rmul(d, b, b);
            rmul(d, aa, bb)
        },
        pf,
        n,
    )
}

/// The body `Rat.FourwiseUncorrelated` is admitted as, rebuilt so callers can
/// reconstruct the literal `And` of two `Pi`s it δ-unfolds to and apply an
/// `h : FourwiseUncorrelated …` through `And.left`/`And.right` without a
/// separate destructuring step — the same reason
/// `probability.rs::pairwise_uncorrelated_body` exists.
pub(super) fn fourwise_body(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    y: ExprId,
    m: ExprId,
    pf: ExprId,
    n: ExprId,
) -> (ExprId, ExprId) {
    let nat = d.nat_ty();
    let zero_r = rzero(d, p);

    let lone = {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);

        let ha = d.lt(a, m);
        let hb = d.lt(b, m);
        let hc = d.lt(c, m);
        let hl = d.lt(l, m);
        let eq_al = d.eq(a, l);
        let hne_a = d.not(eq_al);
        let eq_bl = d.eq(b, l);
        let hne_b = d.not(eq_bl);
        let eq_cl = d.eq(c, l);
        let hne_c = d.not(eq_cl);

        let moment = mixed_moment(d, p, y, [a, b, c, l], pf, n);
        let concl = req(d, moment, zero_r);

        let t = d.arrow(hne_c, concl);
        let t = d.arrow(hne_b, t);
        let t = d.arrow(hne_a, t);
        let t = d.arrow(hl, t);
        let t = d.arrow(hc, t);
        let t = d.arrow(hb, t);
        let t = d.arrow(ha, t);
        let t = d.pi_fv(l_fv, nat, t);
        let t = d.pi_fv(c_fv, nat, t);
        let t = d.pi_fv(b_fv, nat, t);
        d.pi_fv(a_fv, nat, t)
    };

    let squares = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);

        let hi = d.lt(i, m);
        let hj = d.lt(j, m);
        let eq_ij = d.eq(i, j);
        let hne = d.not(eq_ij);

        let joint = paired_moment(d, p, y, i, j, pf, n);
        let ei = second_moment(d, p, y, i, pf, n);
        let ej = second_moment(d, p, y, j, pf, n);
        let prod = rmul(d, ei, ej);
        let concl = req(d, joint, prod);

        let t = d.arrow(hne, concl);
        let t = d.arrow(hj, t);
        let t = d.arrow(hi, t);
        let t = d.pi_fv(j_fv, nat, t);
        d.pi_fv(i_fv, nat, t)
    };

    (lone, squares)
}

/// Admit `Rat.FourwiseUncorrelated : (Nat → Nat → Rat) → Nat → (Nat → Rat) →
/// Nat → Prop` — see the module docs for what the two conditions are and why
/// they are the honest stand-in for independence on a carrier with no product
/// space.
fn declare_fourwise_uncorrelated(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    names: &FourthMomentNames,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);
    let x_ty = d.arrow(nat, fn_ty);
    let prop = d.kernel().sort_zero();

    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let (lone, squares) = fourwise_body(d, p, y, m, pf, n);
    let body = d.and(lone, squares);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_m = d.lam_fv(m_fv, nat, with_pf);
        d.lam_fv(y_fv, x_ty, with_m)
    };
    let ty = {
        let over_n = d.arrow(nat, prop);
        let over_pf = d.arrow(fn_ty, over_n);
        let over_m = d.arrow(nat, over_pf);
        d.arrow(x_ty, over_m)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: names.fourwise_uncorrelated,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(FOURWISE_UNCORRELATED_HEIGHT),
    })
}

/// A ring identity at `ℚ`, emitted by [`crate::ring::rat`] (ADR-1582). Every
/// use in this file is a commutative-ring rearrangement of a concrete
/// pointwise term whose two sides have identical normal forms, so a decline
/// here is a bug in the caller's shapes, not a mathematical gap.
fn rring(d: &mut IntDev<'_>, p: RatPrelude, lhs: ExprId, rhs: ExprId) -> ExprId {
    crate::ring::rat::prove_eq(d, &p, lhs, rhs)
        .expect("fourth_moment: a commutative-ring rearrangement must be a ring identity")
}

/// From `h : Eq a zero`, the collapse `Eq (a * b) zero`.
fn mul_eq_zero_left(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let zero_r = rzero(d, p);
    let ab = rmul(d, a, b);
    let zb = rmul(d, zero_r, b);
    let s1 = rcongr(d, a, zero_r, h, &|d, t| rmul(d, t, b));
    let s2 = zero_mul(d, p, b);
    rtrans(d, ab, zb, zero_r, s1, s2)
}

/// From `hlt : Nat.lt a b`, derive `Not (Eq Nat a b)` — the disequality
/// `Rat.FourwiseUncorrelated` asks for, out of the strict order fact every
/// bounded induction actually has on hand. (`probability.rs` carries the same
/// three lines privately, as `ne_of_lt_nat`.)
fn ne_of_lt(d: &mut IntDev<'_>, a: ExprId, b: ExprId, hlt: ExprId) -> ExprId {
    let np = d.prelude();
    let eq_ty = d.eq(a, b);
    let heq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(heq_fv);
    let lt_bb = nat_rewrite_prop(d, a, b, heq, hlt, &|d, x| d.lt(x, b));
    let false_proof = d.lemma(np.lt_irrefl, &[b, lt_bb]);
    d.lam_fv(heq_fv, eq_ty, false_proof)
}

/// `Nat.lt i (succ j)` from `Nat.lt i j` — the weakening every bounded
/// induction step in this prelude performs on its hypothesis.
fn lt_weaken_succ(d: &mut IntDev<'_>, i: ExprId, j: ExprId, h: ExprId) -> ExprId {
    let np = d.prelude();
    let sj = d.succ(j);
    let le_succ = d.lemma(np.le_succ, &[j]);
    d.lemma(np.lt_of_lt_of_le, &[i, j, sj, h, le_succ])
}

/// `Rat.expectation_sq_sumVars_mul_sq : ∀ Y z p n m,
/// (∀ i i', Lt i m → Lt i' m → Not (Eq i i') →
///     expectation (fun k => Y i k * (Y i' k * (z k * z k))) p n = zero) →
/// expectation (fun k => (sumVars Y m k * sumVars Y m k) * (z k * z k)) p n
///   = sumRange (fun i => expectation (fun k => (Y i k * Y i k) * (z k * z k)) p n) m`
/// — **the one cross term the fourth power of a sum does not kill.**
///
/// `E[(Σ_{i<m} Y_i)²·z²] = Σ_{i<m} E[Y_i²·z²]`: the off-diagonal pairs vanish
/// (that is the hypothesis), the diagonal survives.
///
/// The pairing hypothesis is SPELLED OUT rather than packaged as
/// `Rat.FourwiseUncorrelated`, for a reason that is not stylistic: the
/// induction runs over the bound `m` while `z` is a variable OUTSIDE that
/// range (in the caller it is `Y m` itself), so the hypothesis cannot be the
/// prelude's own predicate at the induction variable — it has to be uniform in
/// `m`, and this one is.
///
/// Induction on `m`, and it is the only place a diagonal is extracted without
/// a `sumRange` delta lemma. `Rat.sumRange_delta`'s hypothesis is
/// UNRESTRICTED (`∀ t`, not `∀ t, Lt t n →`) and four-wise uncorrelatedness
/// supplies zeros only inside its own range, so that lemma is unusable here.
/// The successor step instead splits `(Σ_{i<j+1})²·z² = (Σ_{i<j})²·z² +
/// 2(Σ_{i<j})·Y_j·z² + Y_j²·z²` by a `ring::rat` identity and kills the middle
/// with [`declare_expectation_sum_vars_mul_eq_zero`] — the diagonal never has
/// to be separated from a rectangle at all.
fn declare_expectation_sq_sum_vars_mul_sq(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    names: &FourthMomentNames,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);
    let x_ty = d.arrow(nat, fn_ty);

    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let zero_r = rzero(d, p);

    // `fun i => expectation (fun k => (Y i k * Y i k) * (z k * z k)) p n`.
    let per_index = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let body = expect_of(
            d,
            p,
            &|d, k| {
                let yi = var_at(d, y, i, k);
                let zk = d.apply(z, &[k]);
                let sq = rmul(d, yi, yi);
                let zz = rmul(d, zk, zk);
                rmul(d, sq, zz)
            },
            pf,
            n,
        );
        d.lam_fv(i_fv, nat, body)
    };

    // `∀ i i', Lt i b → Lt i' b → Not (Eq i i') → E[Y_i·(Y_i'·z²)] = zero`.
    let pairing = |d: &mut IntDev<'_>, bound: ExprId| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ip_fv = d.fresh_fvar();
        let ip = d.kernel().fvar(ip_fv);
        let hi = d.lt(i, bound);
        let hip = d.lt(ip, bound);
        let eq_ii = d.eq(i, ip);
        let hne = d.not(eq_ii);
        let moment = expect_of(
            d,
            p,
            &|d, k| {
                let yi = var_at(d, y, i, k);
                let yip = var_at(d, y, ip, k);
                let zk = d.apply(z, &[k]);
                let zz = rmul(d, zk, zk);
                let inner = rmul(d, yip, zz);
                rmul(d, yi, inner)
            },
            pf,
            n,
        );
        let concl = req(d, moment, zero_r);
        let t = d.arrow(hne, concl);
        let t = d.arrow(hip, t);
        let t = d.arrow(hi, t);
        let t = d.pi_fv(ip_fv, nat, t);
        d.pi_fv(i_fv, nat, t)
    };

    let motive = |d: &mut IntDev<'_>, bound: ExprId| -> ExprId {
        let hyp = pairing(d, bound);
        let lhs = expect_of(
            d,
            p,
            &|d, k| {
                let s = sv_at(d, p, y, bound, k);
                let zk = d.apply(z, &[k]);
                let ss = rmul(d, s, s);
                let zz = rmul(d, zk, zk);
                rmul(d, ss, zz)
            },
            pf,
            n,
        );
        let rhs = rsum_range(d, p, per_index, bound);
        let concl = req(d, lhs, rhs);
        d.arrow(hyp, concl)
    };
    let stmt = motive(d, m);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_n = d.zero();
            let hyp_ty = pairing(d, zero_n);
            let h_fv = d.fresh_fvar();

            let summand = weighted_of(
                d,
                &|d, k| {
                    let s = sv_at(d, p, y, zero_n, k);
                    let zk = d.apply(z, &[k]);
                    let ss = rmul(d, s, s);
                    let zz = rmul(d, zk, zk);
                    rmul(d, ss, zz)
                },
                pf,
            );
            let pointwise = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let klt_fv = d.fresh_fvar();
                let klt_ty = d.lt(k, n);

                let inner = {
                    let t_fv = d.fresh_fvar();
                    let t = d.kernel().fvar(t_fv);
                    let ytk = var_at(d, y, t, k);
                    d.lam_fv(t_fv, nat, ytk)
                };
                let is = rsum_range(d, p, inner, zero_n);
                let hzero = d.lemma(p.sum_range_zero, &[inner]);
                let zk = d.apply(z, &[k]);
                let zz = rmul(d, zk, zk);
                let pk = d.apply(pf, &[k]);

                let h1 = mul_eq_zero_left(d, p, is, is, hzero);
                let ss = rmul(d, is, is);
                let h2 = mul_eq_zero_left(d, p, ss, zz, h1);
                let ssz = rmul(d, ss, zz);
                let h3 = mul_eq_zero_left(d, p, ssz, pk, h2);

                let with_klt = d.lam_fv(klt_fv, klt_ty, h3);
                d.lam_fv(k_fv, nat, with_klt)
            };
            let core = d.lemma(p.sum_range_eq_zero_of_lt, &[summand, n, pointwise]);
            d.lam_fv(h_fv, hyp_ty, core)
        },
        &|d, b, ih| {
            let sb = d.succ(b);
            let hyp_ty = pairing(d, sb);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            // The hypothesis, weakened from `succ b` to `b`, for the IH.
            let h_at_b = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let ip_fv = d.fresh_fvar();
                let ip = d.kernel().fvar(ip_fv);
                let hi_ty = d.lt(i, b);
                let hi_fv = d.fresh_fvar();
                let hi = d.kernel().fvar(hi_fv);
                let hip_ty = d.lt(ip, b);
                let hip_fv = d.fresh_fvar();
                let hip = d.kernel().fvar(hip_fv);
                let eq_ii = d.eq(i, ip);
                let hne_ty = d.not(eq_ii);
                let hne_fv = d.fresh_fvar();
                let hne = d.kernel().fvar(hne_fv);

                let hi_up = lt_weaken_succ(d, i, b, hi);
                let hip_up = lt_weaken_succ(d, ip, b, hip);
                let applied = d.apply(h, &[i, ip, hi_up, hip_up, hne]);

                let t = d.lam_fv(hne_fv, hne_ty, applied);
                let t = d.lam_fv(hip_fv, hip_ty, t);
                let t = d.lam_fv(hi_fv, hi_ty, t);
                let t = d.lam_fv(ip_fv, nat, t);
                d.lam_fv(i_fv, nat, t)
            };
            let ih_applied = d.apply(ih, &[h_at_b]);

            // The three distinct pointwise pieces of `(Σ_{i<b} + Y_b)²·z²`.
            let t1 = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
                let s = sv_at(d, p, y, b, k);
                let zk = d.apply(z, &[k]);
                let ss = rmul(d, s, s);
                let zz = rmul(d, zk, zk);
                rmul(d, ss, zz)
            };
            let t2 = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
                let s = sv_at(d, p, y, b, k);
                let yb = var_at(d, y, b, k);
                let zk = d.apply(z, &[k]);
                let zz = rmul(d, zk, zk);
                let inner = rmul(d, yb, zz);
                rmul(d, s, inner)
            };
            let t4 = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
                let yb = var_at(d, y, b, k);
                let zk = d.apply(z, &[k]);
                let sq = rmul(d, yb, yb);
                let zz = rmul(d, zk, zk);
                rmul(d, sq, zz)
            };

            let start = expect_of(
                d,
                p,
                &|d, k| {
                    let s = sv_at(d, p, y, sb, k);
                    let zk = d.apply(z, &[k]);
                    let ss = rmul(d, s, s);
                    let zz = rmul(d, zk, zk);
                    rmul(d, ss, zz)
                },
                pf,
                n,
            );

            let nested_body = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
                let a = t1(d, k);
                let bb = t2(d, k);
                let cc = t2(d, k);
                let dd = t4(d, k);
                let tail = radd(d, cc, dd);
                let mid = radd(d, bb, tail);
                radd(d, a, mid)
            };
            let split = expect_of(d, p, &nested_body, pf, n);

            // step 1: peel the successor and expand the square.
            let step1 = {
                let wsum = weighted_of(
                    d,
                    &|d, k| {
                        let s = sv_at(d, p, y, sb, k);
                        let zk = d.apply(z, &[k]);
                        let ss = rmul(d, s, s);
                        let zz = rmul(d, zk, zk);
                        rmul(d, ss, zz)
                    },
                    pf,
                );
                let wsplit = weighted_of(d, &nested_body, pf);
                let pointwise = {
                    let k_fv = d.fresh_fvar();
                    let k = d.kernel().fvar(k_fv);
                    let inner = {
                        let t_fv = d.fresh_fvar();
                        let t = d.kernel().fvar(t_fv);
                        let ytk = var_at(d, y, t, k);
                        d.lam_fv(t_fv, nat, ytk)
                    };
                    let hsucc = d.lemma(p.sum_range_succ, &[inner, b]);
                    let sv_sb = sv_at(d, p, y, sb, k);
                    let sv_b = sv_at(d, p, y, b, k);
                    let ybk = var_at(d, y, b, k);
                    let joined = radd(d, sv_b, ybk);
                    let zk = d.apply(z, &[k]);
                    let zz = rmul(d, zk, zk);
                    let pk = d.apply(pf, &[k]);
                    let lift = rcongr(d, sv_sb, joined, hsucc, &|d, t| {
                        let ss = rmul(d, t, t);
                        let a = rmul(d, ss, zz);
                        rmul(d, a, pk)
                    });
                    let mid = {
                        let ss = rmul(d, joined, joined);
                        let a = rmul(d, ss, zz);
                        rmul(d, a, pk)
                    };
                    let target = {
                        let a = nested_body(d, k);
                        rmul(d, a, pk)
                    };
                    let expand = rring(d, p, mid, target);
                    let from = {
                        let ss = rmul(d, sv_sb, sv_sb);
                        let a = rmul(d, ss, zz);
                        rmul(d, a, pk)
                    };
                    let full = rtrans(d, from, mid, target, lift, expand);
                    d.lam_fv(k_fv, nat, full)
                };
                d.lemma(p.sum_range_congr, &[wsum, wsplit, n, pointwise])
            };

            // step 2: split into four expectations.
            let f1 = rat_fn(d, &t1);
            let f2 = rat_fn(d, &t2);
            let f4 = rat_fn(d, &t4);
            let e1 = expectation(d, p, f1, pf, n);
            let e2 = expectation(d, p, f2, pf, n);
            let e4 = expectation(d, p, f4, pf, n);
            let tail2 = rat_fn(d, &|d, k| {
                let cc = t2(d, k);
                let dd = t4(d, k);
                radd(d, cc, dd)
            });
            let tail1 = rat_fn(d, &|d, k| {
                let bb = t2(d, k);
                let cc = t2(d, k);
                let dd = t4(d, k);
                let tail = radd(d, cc, dd);
                radd(d, bb, tail)
            });
            let e_tail2 = expectation(d, p, tail2, pf, n);
            let e_tail1 = expectation(d, p, tail1, pf, n);
            let pair2 = radd(d, e2, e4);
            let pair1 = radd(d, e2, e_tail2);
            let pair1b = radd(d, e2, pair2);
            let pair0 = radd(d, e1, e_tail1);
            let pair0b = radd(d, e1, pair1b);
            let step2 = {
                let a2 = d.lemma(p.expectation_add, &[f2, f4, pf, n]);
                let a1 = d.lemma(p.expectation_add, &[f2, tail2, pf, n]);
                let lift1 = rcongr(d, e_tail2, pair2, a2, &|d, t| radd(d, e2, t));
                let inner_chain = rtrans(d, e_tail1, pair1, pair1b, a1, lift1);
                let a0 = d.lemma(p.expectation_add, &[f1, tail1, pf, n]);
                let lift0 = rcongr(d, e_tail1, pair1b, inner_chain, &|d, t| radd(d, e1, t));
                rtrans(d, split, pair0, pair0b, a0, lift0)
            };

            // step 3: the inductive hypothesis kills `E[T1]`.
            let sum_b = rsum_range(d, p, per_index, b);
            let step3 = rcongr(d, e1, sum_b, ih_applied, &|d, t| radd(d, t, pair1b));
            let after3 = radd(d, sum_b, pair1b);

            // step 4: both cross terms vanish.
            let cross_zero = {
                let w = rat_fn(d, &|d, k| {
                    let yb = var_at(d, y, b, k);
                    let zk = d.apply(z, &[k]);
                    let zz = rmul(d, zk, zk);
                    rmul(d, yb, zz)
                });
                let hyp = {
                    let i_fv = d.fresh_fvar();
                    let i = d.kernel().fvar(i_fv);
                    let hi_ty = d.lt(i, b);
                    let hi_fv = d.fresh_fvar();
                    let hi = d.kernel().fvar(hi_fv);
                    let hi_up = lt_weaken_succ(d, i, b, hi);
                    let np = d.prelude();
                    let hb_up = d.lemma(np.lt_succ_self, &[b]);
                    let hne = ne_of_lt(d, i, b, hi);
                    let applied = d.apply(h, &[i, b, hi_up, hb_up, hne]);
                    let t = d.lam_fv(hi_fv, hi_ty, applied);
                    d.lam_fv(i_fv, nat, t)
                };
                d.lemma(
                    names.expectation_sum_vars_mul_eq_zero,
                    &[y, w, pf, n, b, hyp],
                )
            };
            let step4a = rcongr(d, e2, zero_r, cross_zero, &|d, t| {
                let mid = radd(d, t, pair2);
                radd(d, sum_b, mid)
            });
            let after4a = {
                let mid = radd(d, zero_r, pair2);
                radd(d, sum_b, mid)
            };
            let step4b = rcongr(d, e2, zero_r, cross_zero, &|d, t| {
                let inner = radd(d, t, e4);
                let mid = radd(d, zero_r, inner);
                radd(d, sum_b, mid)
            });
            let inner_zero = radd(d, zero_r, e4);
            let after4b = {
                let mid = radd(d, zero_r, inner_zero);
                radd(d, sum_b, mid)
            };

            // step 5: the two `zero +` collapse.
            let za = d.lemma(p.zero_add, &[e4]);
            let step5a = rcongr(d, inner_zero, e4, za, &|d, t| {
                let mid = radd(d, zero_r, t);
                radd(d, sum_b, mid)
            });
            let after5a = {
                let mid = radd(d, zero_r, e4);
                radd(d, sum_b, mid)
            };
            let zb = d.lemma(p.zero_add, &[e4]);
            let step5b = rcongr(d, inner_zero, e4, zb, &|d, t| radd(d, sum_b, t));
            let after5b = radd(d, sum_b, e4);

            let (_end, chained) = rchain(
                d,
                start,
                &[
                    (split, step1),
                    (pair0b, step2),
                    (after3, step3),
                    (after4a, step4a),
                    (after4b, step4b),
                    (after5a, step5a),
                    (after5b, step5b),
                ],
            );
            d.lam_fv(h_fv, hyp_ty, chained)
        },
        m,
    );

    let value = {
        let with_m = d.lam_fv(m_fv, nat, proof);
        let with_n = d.lam_fv(n_fv, nat, with_m);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_z = d.lam_fv(z_fv, fn_ty, with_pf);
        d.lam_fv(y_fv, x_ty, with_z)
    };
    let ty = {
        let with_m = d.pi_fv(m_fv, nat, stmt);
        let with_n = d.pi_fv(n_fv, nat, with_m);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        let with_z = d.pi_fv(z_fv, fn_ty, with_pf);
        d.pi_fv(y_fv, x_ty, with_z)
    };
    d.declare_theorem(names.expectation_sq_sum_vars_mul_sq, ty, value)
}

/// From `hlt : Nat.lt a b`, derive `Not (Eq Nat b a)` — [`ne_of_lt`] with the
/// sides swapped, which is the orientation the lone-index condition wants
/// whenever the unpaired index is the SMALLER one.
fn ne_of_lt_rev(d: &mut IntDev<'_>, a: ExprId, b: ExprId, hlt: ExprId) -> ExprId {
    let np = d.prelude();
    let eq_ty = d.eq(b, a);
    let heq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(heq_fv);
    // `heq : Eq b a`, so rewriting `Lt a b` along it gives `Lt a a`.
    let lt_aa = nat_rewrite_prop(d, b, a, heq, hlt, &|d, x| d.lt(a, x));
    let false_proof = d.lemma(np.lt_irrefl, &[a, lt_aa]);
    d.lam_fv(heq_fv, eq_ty, false_proof)
}

/// From `h : Not (Eq Nat a b)`, the same disequality the other way round.
fn ne_symm(d: &mut IntDev<'_>, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let eq_ba = d.eq(b, a);
    let heq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(heq_fv);
    let back = NatOps::symm(d, b, a, heq);
    let applied = d.apply(h, &[back]);
    d.lam_fv(heq_fv, eq_ba, applied)
}

/// `E[fun k => f k] = E[fun k => g k]` from a pointwise RING identity between
/// the two bodies: `sumRange_congr` over the two weighted summands, with
/// `ring::rat` discharging each point.
///
/// This is how every mixed moment reaches the canonical left-nested shape
/// `Rat.FourwiseUncorrelated` is stated over. ℚ is commutative, so the
/// rearrangement is free mathematically; it is not free syntactically, and
/// this is the one place that cost is paid.
fn expectation_ring_congr(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    pf: ExprId,
    n: ExprId,
    fbody: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
    gbody: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let wf = weighted_of(d, fbody, pf);
    let wg = weighted_of(d, gbody, pf);
    let nat = d.nat_ty();
    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let pk = d.apply(pf, &[k]);
        let a = fbody(d, k);
        let lhs = rmul(d, a, pk);
        let b = gbody(d, k);
        let rhs = rmul(d, b, pk);
        let step = rring(d, p, lhs, rhs);
        d.lam_fv(k_fv, nat, step)
    };
    d.lemma(p.sum_range_congr, &[wf, wg, n, pointwise])
}

/// From `h : Eq a zero`, the bound `Rat.le a zero`.
fn le_zero_of_eq_zero(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, h: ExprId) -> ExprId {
    let zero_r = rzero(d, p);
    let refl = d.lemma(p.le_refl, &[zero_r]);
    let back = rsymm(d, a, zero_r, h);
    rat_eq_rewrite(d, zero_r, a, back, refl, &|d, t| rle(d, p, t, zero_r))
}

/// `body₁ k + (body₂ k + … + body_N k)`, right-nested and redex-free.
fn nested_at(
    d: &mut IntDev<'_>,
    parts: &[&dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId],
    k: ExprId,
) -> ExprId {
    let last = parts.len() - 1;
    let mut acc = (parts[last])(d, k);
    for f in parts[..last].iter().rev() {
        let t = f(d, k);
        acc = radd(d, t, acc);
    }
    acc
}

/// `E[fun k => f₁ k + (f₂ k + … + f_N k)] = E[f₁] + (E[f₂] + … + E[f_N])`,
/// `Rat.expectation_add` folded from the right. Returns
/// `(lhs, rhs, proof)`.
fn expectation_split(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    parts: &[&dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId],
    pf: ExprId,
    n: ExprId,
) -> (ExprId, ExprId, ExprId) {
    assert!(!parts.is_empty(), "expectation_split needs a summand");
    if parts.len() == 1 {
        let f = rat_fn(d, parts[0]);
        let e = expectation(d, p, f, pf, n);
        let pr = rrefl(d, e);
        return (e, e, pr);
    }
    let head = rat_fn(d, parts[0]);
    let e_head = expectation(d, p, head, pf, n);
    let tail = rat_fn(d, &|d, k| nested_at(d, &parts[1..], k));
    let e_tail = expectation(d, p, tail, pf, n);
    let (_lhs_tail, rhs_tail, pr_tail) = expectation_split(d, p, &parts[1..], pf, n);

    let step = d.lemma(p.expectation_add, &[head, tail, pf, n]);
    let pair = radd(d, e_head, e_tail);
    let lift = rcongr(d, e_tail, rhs_tail, pr_tail, &|d, t| radd(d, e_head, t));
    let rhs = radd(d, e_head, rhs_tail);

    let whole = rat_fn(d, &|d, k| nested_at(d, parts, k));
    let lhs = expectation(d, p, whole, pf, n);
    let pr = rtrans(d, lhs, pair, rhs, step, lift);
    (lhs, rhs, pr)
}

/// From `hᵢ : le aᵢ bᵢ`, the bound
/// `le (a₁ + (a₂ + … + a_N)) (b₁ + (b₂ + … + b_N))` — `Rat.add_le_add` folded
/// from the right. Returns `(lhs, rhs, proof)`.
fn add_le_fold(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    items: &[(ExprId, ExprId, ExprId)],
) -> (ExprId, ExprId, ExprId) {
    assert!(!items.is_empty(), "add_le_fold needs a summand");
    if items.len() == 1 {
        return items[0];
    }
    let (a, b, h) = items[0];
    let (ta, tb, th) = add_le_fold(d, p, &items[1..]);
    let lhs = radd(d, a, ta);
    let rhs = radd(d, b, tb);
    let pr = d.lemma(p.add_le_add, &[a, b, ta, tb, h, th]);
    (lhs, rhs, pr)
}

/// `∀ i, Lt i bound → Rat.le (expectation (fun k => (Y i k * Y i k) * (Y i k *
/// Y i k)) p n) M₄` — "every centred variable's fourth moment is at most
/// `M₄`", on the range the induction is over.
fn fourth_moment_bounded(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    y: ExprId,
    m4: ExprId,
    pf: ExprId,
    n: ExprId,
    bound: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hi = d.lt(i, bound);
    let moment = expect_of(
        d,
        p,
        &|d, k| {
            let yi = var_at(d, y, i, k);
            let sq = rmul(d, yi, yi);
            rmul(d, sq, sq)
        },
        pf,
        n,
    );
    let concl = rle(d, p, moment, m4);
    let inner = d.arrow(hi, concl);
    d.pi_fv(i_fv, nat, inner)
}

/// `∀ i, Lt i bound → Rat.le (expectation (fun k => Y i k * Y i k) p n) σ²`.
fn second_moment_bounded(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    y: ExprId,
    s2: ExprId,
    pf: ExprId,
    n: ExprId,
    bound: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hi = d.lt(i, bound);
    let moment = second_moment(d, p, y, i, pf, n);
    let concl = rle(d, p, moment, s2);
    let inner = d.arrow(hi, concl);
    d.pi_fv(i_fv, nat, inner)
}

/// `Rat.fourth_moment_sumVars_le : ∀ Y p n M₄ σ², IsDistribution p n →
/// le zero σ² → ∀ m, FourwiseUncorrelated Y m p n →
/// (∀ i < m, E[Y_i⁴] ≤ M₄) → (∀ i < m, E[Y_i²] ≤ σ²) →
/// E[(Σ_{i<m} Y_i)⁴] ≤ Σ_{i<m} M₄ + 3·(Σ_{i<m} σ²)²`
/// — **the fourth central moment of a sum**, and the whole content of this
/// module.
///
/// The bound is written with `sumRange` rather than `m·M₄` and `3(mσ²)²`
/// deliberately: `Rat.sumRange f (succ b) ≡ sumRange f b + f b` is `Eq.refl`
/// here, so the successor step of the induction gets the shape of its target
/// for free, where `Rat.natDivSucc (succ b) 0 = natDivSucc b 0 + 1` is a
/// rational-numeral fact this prelude does not have. `Rat.sum_range_const`
/// converts either side to the `m·c` form at the point of use, and the `3` is
/// spelled as three summands for the same reason `ring::rat` spells every
/// coefficient additively.
///
/// Induction on `m`. **Base**: `sumVars Y 0` is pointwise zero so the left
/// side is zero, and the right side is non-negative by `Rat.sq_nonneg` and
/// `Rat.add_nonneg` — no hypothesis used at all. **Successor**: the pointwise
/// quartic `(Σ_{i<b} + Y_b)⁴` is expanded by ONE `ring::rat` identity into
/// sixteen monomials, `Rat.expectation_add` splits the expectation into
/// sixteen, and then
///
/// * the four `Σ³·Y_b` terms vanish — three nested applications of
///   `Rat.expectation_sumVars_mul_eq_zero`, since `b` is a LONE index in
///   `E[Y_i Y_{i'} Y_{i''} Y_b]` for any `i, i', i'' < b`;
/// * the four `Σ·Y_b³` terms vanish — one application, with `i` the lone
///   index in `E[Y_b Y_b Y_b Y_i]`;
/// * the six `Σ²·Y_b²` terms are the ones that survive, and
///   `Rat.expectation_sq_sumVars_mul_sq` turns each into `Σ_{i<b} E[Y_i²Y_b²]`,
///   which the SECOND condition of `FourwiseUncorrelated` factors and
///   `Rat.sumRange_mul_right` collects into `(Σ_{i<b} E[Y_i²])·E[Y_b²] ≤
///   (Σ_{i<b} σ²)·σ²`;
/// * `E[Y_b⁴] ≤ M₄` is the hypothesis at `b`.
///
/// Adding those up gives `Σ_b M₄ + 3T² + 6Tσ² + M₄` against a target of
/// `Σ_b M₄ + M₄ + 3(T + σ²)²`, and the difference is exactly `3σ⁴ ≥ 0` — the
/// induction closes with slack, not on the nose, which is why the last step is
/// `Rat.add_le_add` against `Rat.sq_nonneg` and not an equality.
#[allow(clippy::too_many_lines)]
fn declare_fourth_moment_sum_vars_le(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    names: &FourthMomentNames,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);
    let x_ty = d.arrow(nat, fn_ty);

    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m4_fv = d.fresh_fvar();
    let m4 = d.kernel().fvar(m4_fv);
    let s2_fv = d.fresh_fvar();
    let s2 = d.kernel().fvar(s2_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let zero_r = rzero(d, p);
    let hd_ty = is_distribution(d, p, pf, n);
    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);
    let hs2_ty = rle(d, p, zero_r, s2);
    let hs2_fv = d.fresh_fvar();
    let hs2 = d.kernel().fvar(hs2_fv);

    let const_m4 = const_fn(d, m4);
    let const_s2 = const_fn(d, s2);

    // `Σ_{i<bound} M₄ + ((T·T + T·T) + T·T)`, `T := Σ_{i<bound} σ²`.
    let bound_at = |d: &mut IntDev<'_>, bnd: ExprId| -> ExprId {
        let sm = rsum_range(d, p, const_m4, bnd);
        let t = rsum_range(d, p, const_s2, bnd);
        let sq = rmul(d, t, t);
        let two = radd(d, sq, sq);
        let three = radd(d, two, sq);
        radd(d, sm, three)
    };

    let quartic_at = |d: &mut IntDev<'_>, bnd: ExprId| -> ExprId {
        expect_of(
            d,
            p,
            &|d, k| {
                let s = sv_at(d, p, y, bnd, k);
                let ss = rmul(d, s, s);
                rmul(d, ss, ss)
            },
            pf,
            n,
        )
    };

    let motive = |d: &mut IntDev<'_>, bnd: ExprId| -> ExprId {
        let hfw = d.const_app(names.fourwise_uncorrelated, &[y, bnd, pf, n]);
        let h4 = fourth_moment_bounded(d, p, y, m4, pf, n, bnd);
        let h2 = second_moment_bounded(d, p, y, s2, pf, n, bnd);
        let lhs = quartic_at(d, bnd);
        let rhs = bound_at(d, bnd);
        let concl = rle(d, p, lhs, rhs);
        let t = d.arrow(h2, concl);
        let t = d.arrow(h4, t);
        d.arrow(hfw, t)
    };
    let stmt = motive(d, m);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_n = d.zero();
            let hfw_ty = d.const_app(names.fourwise_uncorrelated, &[y, zero_n, pf, n]);
            let hfw_fv = d.fresh_fvar();
            let h4_ty = fourth_moment_bounded(d, p, y, m4, pf, n, zero_n);
            let h4_fv = d.fresh_fvar();
            let h2_ty = second_moment_bounded(d, p, y, s2, pf, n, zero_n);
            let h2_fv = d.fresh_fvar();

            // The left side is pointwise zero.
            let summand = weighted_of(
                d,
                &|d, k| {
                    let s = sv_at(d, p, y, zero_n, k);
                    let ss = rmul(d, s, s);
                    rmul(d, ss, ss)
                },
                pf,
            );
            let pointwise = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let klt_fv = d.fresh_fvar();
                let klt_ty = d.lt(k, n);
                let inner = {
                    let t_fv = d.fresh_fvar();
                    let t = d.kernel().fvar(t_fv);
                    let ytk = var_at(d, y, t, k);
                    d.lam_fv(t_fv, nat, ytk)
                };
                let is = rsum_range(d, p, inner, zero_n);
                let hzero = d.lemma(p.sum_range_zero, &[inner]);
                let pk = d.apply(pf, &[k]);
                let h1 = mul_eq_zero_left(d, p, is, is, hzero);
                let ss = rmul(d, is, is);
                let h2 = mul_eq_zero_left(d, p, ss, ss, h1);
                let ssss = rmul(d, ss, ss);
                let h3 = mul_eq_zero_left(d, p, ssss, pk, h2);
                let with_klt = d.lam_fv(klt_fv, klt_ty, h3);
                d.lam_fv(k_fv, nat, with_klt)
            };
            let hl = d.lemma(p.sum_range_eq_zero_of_lt, &[summand, n, pointwise]);
            let lhs = quartic_at(d, zero_n);

            // The right side is non-negative, with no hypothesis used.
            let rhs = bound_at(d, zero_n);
            let sm0 = rsum_range(d, p, const_m4, zero_n);
            let t0 = rsum_range(d, p, const_s2, zero_n);
            let sq0 = rmul(d, t0, t0);
            let two0 = radd(d, sq0, sq0);
            let three0 = radd(d, two0, sq0);
            let sq_nn = d.lemma(p.sq_nonneg, &[t0]);
            let two_nn = d.lemma(p.add_nonneg, &[sq0, sq0, sq_nn, sq_nn]);
            let three_nn = d.lemma(p.add_nonneg, &[two0, sq0, two_nn, sq_nn]);
            // `sumRange _ 0` ι-reduces to `zero`, so `le_refl zero` IS this.
            let sm_nn = d.lemma(p.le_refl, &[zero_r]);
            let rhs_nn = d.lemma(p.add_nonneg, &[sm0, three0, sm_nn, three_nn]);

            let back = rsymm(d, lhs, zero_r, hl);
            let core = rat_eq_rewrite(d, zero_r, lhs, back, rhs_nn, &|d, t| rle(d, p, t, rhs));

            let t = d.lam_fv(h2_fv, h2_ty, core);
            let t = d.lam_fv(h4_fv, h4_ty, t);
            d.lam_fv(hfw_fv, hfw_ty, t)
        },
        &|d, b, ih| {
            let sb = d.succ(b);
            let hfw_ty = d.const_app(names.fourwise_uncorrelated, &[y, sb, pf, n]);
            let hfw_fv = d.fresh_fvar();
            let hfw = d.kernel().fvar(hfw_fv);
            let h4_ty = fourth_moment_bounded(d, p, y, m4, pf, n, sb);
            let h4_fv = d.fresh_fvar();
            let h4 = d.kernel().fvar(h4_fv);
            let h2_ty = second_moment_bounded(d, p, y, s2, pf, n, sb);
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);

            let (lone_sb, squares_sb) = fourwise_body(d, p, y, sb, pf, n);
            let lone = d.and_left(lone_sb, squares_sb, hfw);
            let squares = d.and_right(lone_sb, squares_sb, hfw);

            // --- the inductive hypothesis, at `b` --------------------------
            let (lone_b, squares_b) = fourwise_body(d, p, y, b, pf, n);
            let lone_b_proof = {
                let mut idx_fv = Vec::new();
                let mut idx = Vec::new();
                for _ in 0..4 {
                    let fv = d.fresh_fvar();
                    idx_fv.push(fv);
                    idx.push(d.kernel().fvar(fv));
                }
                let mut lt_ty = Vec::new();
                let mut lt_fv = Vec::new();
                let mut lt_arg = Vec::new();
                for &index in &idx {
                    lt_ty.push(d.lt(index, b));
                    let fv = d.fresh_fvar();
                    lt_fv.push(fv);
                    lt_arg.push(d.kernel().fvar(fv));
                }
                let mut ne_ty = Vec::new();
                let mut ne_fv = Vec::new();
                let mut ne_arg = Vec::new();
                for slot in 0..3 {
                    let eq = d.eq(idx[slot], idx[3]);
                    ne_ty.push(d.not(eq));
                    let fv = d.fresh_fvar();
                    ne_fv.push(fv);
                    ne_arg.push(d.kernel().fvar(fv));
                }
                let mut args = idx.clone();
                for slot in 0..4 {
                    let up = lt_weaken_succ(d, idx[slot], b, lt_arg[slot]);
                    args.push(up);
                }
                args.extend(ne_arg.iter().copied());
                let mut t = d.apply(lone, &args);
                for slot in (0..3).rev() {
                    t = d.lam_fv(ne_fv[slot], ne_ty[slot], t);
                }
                for slot in (0..4).rev() {
                    t = d.lam_fv(lt_fv[slot], lt_ty[slot], t);
                }
                for slot in (0..4).rev() {
                    t = d.lam_fv(idx_fv[slot], nat, t);
                }
                t
            };
            let squares_b_proof = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let j_fv = d.fresh_fvar();
                let j = d.kernel().fvar(j_fv);
                let hi_ty = d.lt(i, b);
                let hi_fv = d.fresh_fvar();
                let hi = d.kernel().fvar(hi_fv);
                let hj_ty = d.lt(j, b);
                let hj_fv = d.fresh_fvar();
                let hj = d.kernel().fvar(hj_fv);
                let eq_ij = d.eq(i, j);
                let hne_ty = d.not(eq_ij);
                let hne_fv = d.fresh_fvar();
                let hne = d.kernel().fvar(hne_fv);
                let hi_up = lt_weaken_succ(d, i, b, hi);
                let hj_up = lt_weaken_succ(d, j, b, hj);
                let applied = d.apply(squares, &[i, j, hi_up, hj_up, hne]);
                let t = d.lam_fv(hne_fv, hne_ty, applied);
                let t = d.lam_fv(hj_fv, hj_ty, t);
                let t = d.lam_fv(hi_fv, hi_ty, t);
                let t = d.lam_fv(j_fv, nat, t);
                d.lam_fv(i_fv, nat, t)
            };
            let hfw_b = {
                let intro = d.int().logic.and_intro;
                d.const_app(intro, &[lone_b, squares_b, lone_b_proof, squares_b_proof])
            };
            let weaken_bound = |d: &mut IntDev<'_>, h: ExprId| -> ExprId {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let hi_ty = d.lt(i, b);
                let hi_fv = d.fresh_fvar();
                let hi = d.kernel().fvar(hi_fv);
                let up = lt_weaken_succ(d, i, b, hi);
                let applied = d.apply(h, &[i, up]);
                let t = d.lam_fv(hi_fv, hi_ty, applied);
                d.lam_fv(i_fv, nat, t)
            };
            let h4_b = weaken_bound(d, h4);
            let h2_b = weaken_bound(d, h2);
            let ih_applied = d.apply(ih, &[hfw_b, h4_b, h2_b]);

            // --- the sixteen monomials -------------------------------------
            let q1 = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
                let s = sv_at(d, p, y, b, k);
                let ss = rmul(d, s, s);
                rmul(d, ss, ss)
            };
            let q2 = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
                let s = sv_at(d, p, y, b, k);
                let yb = var_at(d, y, b, k);
                let a = rmul(d, s, yb);
                let c = rmul(d, s, a);
                rmul(d, s, c)
            };
            let q3 = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
                let s = sv_at(d, p, y, b, k);
                let yb = var_at(d, y, b, k);
                let ss = rmul(d, s, s);
                let yy = rmul(d, yb, yb);
                rmul(d, ss, yy)
            };
            let q4f = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
                let s = sv_at(d, p, y, b, k);
                let yb = var_at(d, y, b, k);
                let yy = rmul(d, yb, yb);
                let yyy = rmul(d, yy, yb);
                rmul(d, s, yyy)
            };
            let q5 = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
                let yb = var_at(d, y, b, k);
                let yy = rmul(d, yb, yb);
                rmul(d, yy, yy)
            };
            let parts: Vec<&dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId> = vec![
                &q1, &q2, &q2, &q2, &q2, &q3, &q3, &q3, &q3, &q3, &q3, &q4f, &q4f, &q4f, &q4f, &q5,
            ];

            // step 1: peel the successor and expand the quartic.
            let start = quartic_at(d, sb);
            let step1 = {
                let wsum = weighted_of(
                    d,
                    &|d, k| {
                        let s = sv_at(d, p, y, sb, k);
                        let ss = rmul(d, s, s);
                        rmul(d, ss, ss)
                    },
                    pf,
                );
                let wsplit = weighted_of(d, &|d, k| nested_at(d, &parts, k), pf);
                let pointwise = {
                    let k_fv = d.fresh_fvar();
                    let k = d.kernel().fvar(k_fv);
                    let inner = {
                        let t_fv = d.fresh_fvar();
                        let t = d.kernel().fvar(t_fv);
                        let ytk = var_at(d, y, t, k);
                        d.lam_fv(t_fv, nat, ytk)
                    };
                    let hsucc = d.lemma(p.sum_range_succ, &[inner, b]);
                    let sv_sb = sv_at(d, p, y, sb, k);
                    let sv_b = sv_at(d, p, y, b, k);
                    let ybk = var_at(d, y, b, k);
                    let joined = radd(d, sv_b, ybk);
                    let pk = d.apply(pf, &[k]);
                    let lift = rcongr(d, sv_sb, joined, hsucc, &|d, t| {
                        let ss = rmul(d, t, t);
                        let a = rmul(d, ss, ss);
                        rmul(d, a, pk)
                    });
                    let mid = {
                        let ss = rmul(d, joined, joined);
                        let a = rmul(d, ss, ss);
                        rmul(d, a, pk)
                    };
                    let target = {
                        let a = nested_at(d, &parts, k);
                        rmul(d, a, pk)
                    };
                    let expand = rring(d, p, mid, target);
                    let from = {
                        let ss = rmul(d, sv_sb, sv_sb);
                        let a = rmul(d, ss, ss);
                        rmul(d, a, pk)
                    };
                    let full = rtrans(d, from, mid, target, lift, expand);
                    d.lam_fv(k_fv, nat, full)
                };
                d.lemma(p.sum_range_congr, &[wsum, wsplit, n, pointwise])
            };

            // step 2: sixteen expectations.
            let (split_lhs, split_rhs, step2) = expectation_split(d, p, &parts, pf, n);

            // --- the four `Σ³·Y_b` terms vanish ----------------------------
            let hq2 = {
                let w1 = rat_fn(d, &|d, k| {
                    let s = sv_at(d, p, y, b, k);
                    let yb = var_at(d, y, b, k);
                    let a = rmul(d, s, yb);
                    rmul(d, s, a)
                });
                let hyp1 = {
                    let i_fv = d.fresh_fvar();
                    let i = d.kernel().fvar(i_fv);
                    let hi_ty = d.lt(i, b);
                    let hi_fv = d.fresh_fvar();
                    let hi = d.kernel().fvar(hi_fv);

                    let f_a = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
                        let yi = var_at(d, y, i, k);
                        let s = sv_at(d, p, y, b, k);
                        let yb = var_at(d, y, b, k);
                        let a = rmul(d, s, yb);
                        let c = rmul(d, s, a);
                        rmul(d, yi, c)
                    };
                    let f_b = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
                        let yi = var_at(d, y, i, k);
                        let s = sv_at(d, p, y, b, k);
                        let yb = var_at(d, y, b, k);
                        let a = rmul(d, s, yb);
                        let c = rmul(d, yi, a);
                        rmul(d, s, c)
                    };
                    let cong = expectation_ring_congr(d, p, pf, n, &f_a, &f_b);

                    let w2 = rat_fn(d, &|d, k| {
                        let yi = var_at(d, y, i, k);
                        let s = sv_at(d, p, y, b, k);
                        let yb = var_at(d, y, b, k);
                        let a = rmul(d, s, yb);
                        rmul(d, yi, a)
                    });
                    let hyp2 = {
                        let ip_fv = d.fresh_fvar();
                        let ip = d.kernel().fvar(ip_fv);
                        let hip_ty = d.lt(ip, b);
                        let hip_fv = d.fresh_fvar();
                        let hip = d.kernel().fvar(hip_fv);

                        let g_a = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
                            let yip = var_at(d, y, ip, k);
                            let yi = var_at(d, y, i, k);
                            let s = sv_at(d, p, y, b, k);
                            let yb = var_at(d, y, b, k);
                            let a = rmul(d, s, yb);
                            let c = rmul(d, yi, a);
                            rmul(d, yip, c)
                        };
                        let g_b = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
                            let yip = var_at(d, y, ip, k);
                            let yi = var_at(d, y, i, k);
                            let s = sv_at(d, p, y, b, k);
                            let yb = var_at(d, y, b, k);
                            let a = rmul(d, yi, yb);
                            let c = rmul(d, yip, a);
                            rmul(d, s, c)
                        };
                        let cong2 = expectation_ring_congr(d, p, pf, n, &g_a, &g_b);

                        let w3 = rat_fn(d, &|d, k| {
                            let yip = var_at(d, y, ip, k);
                            let yi = var_at(d, y, i, k);
                            let yb = var_at(d, y, b, k);
                            let a = rmul(d, yi, yb);
                            rmul(d, yip, a)
                        });
                        let hyp3 = {
                            let ipp_fv = d.fresh_fvar();
                            let ipp = d.kernel().fvar(ipp_fv);
                            let hipp_ty = d.lt(ipp, b);
                            let hipp_fv = d.fresh_fvar();
                            let hipp = d.kernel().fvar(hipp_fv);

                            let e_a = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
                                let yipp = var_at(d, y, ipp, k);
                                let yip = var_at(d, y, ip, k);
                                let yi = var_at(d, y, i, k);
                                let yb = var_at(d, y, b, k);
                                let a = rmul(d, yi, yb);
                                let c = rmul(d, yip, a);
                                rmul(d, yipp, c)
                            };
                            let e_b = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
                                let yipp = var_at(d, y, ipp, k);
                                let yip = var_at(d, y, ip, k);
                                let yi = var_at(d, y, i, k);
                                let yb = var_at(d, y, b, k);
                                let a = rmul(d, yipp, yip);
                                let c = rmul(d, a, yi);
                                rmul(d, c, yb)
                            };
                            let cong3 = expectation_ring_congr(d, p, pf, n, &e_a, &e_b);
                            let np = d.prelude();
                            let hb_self = d.lemma(np.lt_succ_self, &[b]);
                            let up_ipp = lt_weaken_succ(d, ipp, b, hipp);
                            let up_ip = lt_weaken_succ(d, ip, b, hip);
                            let up_i = lt_weaken_succ(d, i, b, hi);
                            let ne_ipp = ne_of_lt(d, ipp, b, hipp);
                            let ne_ip = ne_of_lt(d, ip, b, hip);
                            let ne_i = ne_of_lt(d, i, b, hi);
                            let applied = d.apply(
                                lone,
                                &[
                                    ipp, ip, i, b, up_ipp, up_ip, up_i, hb_self, ne_ipp, ne_ip,
                                    ne_i,
                                ],
                            );
                            let ea = expect_of(d, p, &e_a, pf, n);
                            let eb = expect_of(d, p, &e_b, pf, n);
                            let full = rtrans(d, ea, eb, zero_r, cong3, applied);
                            let t = d.lam_fv(hipp_fv, hipp_ty, full);
                            d.lam_fv(ipp_fv, nat, t)
                        };
                        let peel = d.lemma(
                            names.expectation_sum_vars_mul_eq_zero,
                            &[y, w3, pf, n, b, hyp3],
                        );
                        let ga = expect_of(d, p, &g_a, pf, n);
                        let gb = expect_of(d, p, &g_b, pf, n);
                        let full = rtrans(d, ga, gb, zero_r, cong2, peel);
                        let t = d.lam_fv(hip_fv, hip_ty, full);
                        d.lam_fv(ip_fv, nat, t)
                    };
                    let peel = d.lemma(
                        names.expectation_sum_vars_mul_eq_zero,
                        &[y, w2, pf, n, b, hyp2],
                    );
                    let fa = expect_of(d, p, &f_a, pf, n);
                    let fb = expect_of(d, p, &f_b, pf, n);
                    let full = rtrans(d, fa, fb, zero_r, cong, peel);
                    let t = d.lam_fv(hi_fv, hi_ty, full);
                    d.lam_fv(i_fv, nat, t)
                };
                d.lemma(
                    names.expectation_sum_vars_mul_eq_zero,
                    &[y, w1, pf, n, b, hyp1],
                )
            };

            // --- the four `Σ·Y_b³` terms vanish ----------------------------
            let hq4 = {
                let w = rat_fn(d, &|d, k| {
                    let yb = var_at(d, y, b, k);
                    let yy = rmul(d, yb, yb);
                    rmul(d, yy, yb)
                });
                let hyp = {
                    let i_fv = d.fresh_fvar();
                    let i = d.kernel().fvar(i_fv);
                    let hi_ty = d.lt(i, b);
                    let hi_fv = d.fresh_fvar();
                    let hi = d.kernel().fvar(hi_fv);

                    let e_a = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
                        let yi = var_at(d, y, i, k);
                        let yb = var_at(d, y, b, k);
                        let yy = rmul(d, yb, yb);
                        let yyy = rmul(d, yy, yb);
                        rmul(d, yi, yyy)
                    };
                    let e_b = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
                        let yi = var_at(d, y, i, k);
                        let yb = var_at(d, y, b, k);
                        let a = rmul(d, yb, yb);
                        let c = rmul(d, a, yb);
                        rmul(d, c, yi)
                    };
                    let cong = expectation_ring_congr(d, p, pf, n, &e_a, &e_b);
                    let np = d.prelude();
                    let hb_self = d.lemma(np.lt_succ_self, &[b]);
                    let up_i = lt_weaken_succ(d, i, b, hi);
                    let ne_b = ne_of_lt_rev(d, i, b, hi);
                    let applied = d.apply(
                        lone,
                        &[
                            b, b, b, i, hb_self, hb_self, hb_self, up_i, ne_b, ne_b, ne_b,
                        ],
                    );
                    let ea = expect_of(d, p, &e_a, pf, n);
                    let eb = expect_of(d, p, &e_b, pf, n);
                    let full = rtrans(d, ea, eb, zero_r, cong, applied);
                    let t = d.lam_fv(hi_fv, hi_ty, full);
                    d.lam_fv(i_fv, nat, t)
                };
                d.lemma(
                    names.expectation_sum_vars_mul_eq_zero,
                    &[y, w, pf, n, b, hyp],
                )
            };

            // --- the six `Σ²·Y_b²` terms survive, and are bounded ----------
            let t_b = rsum_range(d, p, const_s2, b);
            let c_bar = rmul(d, t_b, s2);
            let hq3 = {
                let zfn = d.apply(y, &[b]);
                let pairing = {
                    let i_fv = d.fresh_fvar();
                    let i = d.kernel().fvar(i_fv);
                    let ip_fv = d.fresh_fvar();
                    let ip = d.kernel().fvar(ip_fv);
                    let hi_ty = d.lt(i, b);
                    let hi_fv = d.fresh_fvar();
                    let hi = d.kernel().fvar(hi_fv);
                    let hip_ty = d.lt(ip, b);
                    let hip_fv = d.fresh_fvar();
                    let hip = d.kernel().fvar(hip_fv);
                    let eq_ii = d.eq(i, ip);
                    let hne_ty = d.not(eq_ii);
                    let hne_fv = d.fresh_fvar();
                    let hne = d.kernel().fvar(hne_fv);

                    let e_a = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
                        let yi = var_at(d, y, i, k);
                        let yip = var_at(d, y, ip, k);
                        let yb = var_at(d, y, b, k);
                        let yy = rmul(d, yb, yb);
                        let a = rmul(d, yip, yy);
                        rmul(d, yi, a)
                    };
                    let e_b = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
                        let yi = var_at(d, y, i, k);
                        let yip = var_at(d, y, ip, k);
                        let yb = var_at(d, y, b, k);
                        let a = rmul(d, yip, yb);
                        let c = rmul(d, a, yb);
                        rmul(d, c, yi)
                    };
                    let cong = expectation_ring_congr(d, p, pf, n, &e_a, &e_b);
                    let np = d.prelude();
                    let hb_self = d.lemma(np.lt_succ_self, &[b]);
                    let up_i = lt_weaken_succ(d, i, b, hi);
                    let up_ip = lt_weaken_succ(d, ip, b, hip);
                    let ne_ip_i = ne_symm(d, i, ip, hne);
                    let ne_b_i = ne_of_lt_rev(d, i, b, hi);
                    let applied = d.apply(
                        lone,
                        &[
                            ip, b, b, i, up_ip, hb_self, hb_self, up_i, ne_ip_i, ne_b_i, ne_b_i,
                        ],
                    );
                    let ea = expect_of(d, p, &e_a, pf, n);
                    let eb = expect_of(d, p, &e_b, pf, n);
                    let full = rtrans(d, ea, eb, zero_r, cong, applied);
                    let t = d.lam_fv(hne_fv, hne_ty, full);
                    let t = d.lam_fv(hip_fv, hip_ty, t);
                    let t = d.lam_fv(hi_fv, hi_ty, t);
                    let t = d.lam_fv(ip_fv, nat, t);
                    d.lam_fv(i_fv, nat, t)
                };
                let diag = d.lemma(
                    names.expectation_sq_sum_vars_mul_sq,
                    &[y, zfn, pf, n, b, pairing],
                );
                // diag : Eq E[q3] (sumRange (fun i => E[Y_i²·Y_b²]) b)

                let g_fn = {
                    let i_fv = d.fresh_fvar();
                    let i = d.kernel().fvar(i_fv);
                    let body = expect_of(
                        d,
                        p,
                        &|d, k| {
                            let yi = var_at(d, y, i, k);
                            let yb = var_at(d, y, b, k);
                            let sq = rmul(d, yi, yi);
                            let yy = rmul(d, yb, yb);
                            rmul(d, sq, yy)
                        },
                        pf,
                        n,
                    );
                    d.lam_fv(i_fv, nat, body)
                };
                let sec_fn = {
                    let i_fv = d.fresh_fvar();
                    let i = d.kernel().fvar(i_fv);
                    let body = second_moment(d, p, y, i, pf, n);
                    d.lam_fv(i_fv, nat, body)
                };
                let e2b = second_moment(d, p, y, b, pf, n);
                let prod_fn = {
                    let i_fv = d.fresh_fvar();
                    let i = d.kernel().fvar(i_fv);
                    let ei = second_moment(d, p, y, i, pf, n);
                    let body = rmul(d, ei, e2b);
                    d.lam_fv(i_fv, nat, body)
                };
                // Each diagonal term factors, by the SECOND condition.
                let factor_pointwise = {
                    let i_fv = d.fresh_fvar();
                    let i = d.kernel().fvar(i_fv);
                    let hi_ty = d.lt(i, b);
                    let hi_fv = d.fresh_fvar();
                    let hi = d.kernel().fvar(hi_fv);
                    let np = d.prelude();
                    let hb_self = d.lemma(np.lt_succ_self, &[b]);
                    let up_i = lt_weaken_succ(d, i, b, hi);
                    let ne_i_b = ne_of_lt(d, i, b, hi);
                    let applied = d.apply(squares, &[i, b, up_i, hb_self, ne_i_b]);
                    let t = d.lam_fv(hi_fv, hi_ty, applied);
                    d.lam_fv(i_fv, nat, t)
                };
                let factored = d.lemma(p.sum_range_congr_lt, &[g_fn, prod_fn, b, factor_pointwise]);
                let collected = d.lemma(p.sum_range_mul_right, &[sec_fn, e2b, b]);
                // collected : Eq (sumRange (fun i => sec i * e2b) b) (sumRange sec b * e2b)

                let sum_g = rsum_range(d, p, g_fn, b);
                let sum_prod = rsum_range(d, p, prod_fn, b);
                let sum_sec = rsum_range(d, p, sec_fn, b);
                let collected_rhs = rmul(d, sum_sec, e2b);
                let q3_expr = expect_of(d, p, &q3, pf, n);
                let (_endp, eq_chain) = rchain(
                    d,
                    q3_expr,
                    &[
                        (sum_g, diag),
                        (sum_prod, factored),
                        (collected_rhs, collected),
                    ],
                );

                // `Σ_{i<b} E[Y_i²] ≤ T` and `0 ≤ E[Y_b²] ≤ σ²`, so the product
                // is at most `T·σ²`.
                let le_pointwise = {
                    let i_fv = d.fresh_fvar();
                    let i = d.kernel().fvar(i_fv);
                    let hi_ty = d.lt(i, b);
                    let hi_fv = d.fresh_fvar();
                    let hi = d.kernel().fvar(hi_fv);
                    let up_i = lt_weaken_succ(d, i, b, hi);
                    let applied = d.apply(h2, &[i, up_i]);
                    let t = d.lam_fv(hi_fv, hi_ty, applied);
                    d.lam_fv(i_fv, nat, t)
                };
                let hsum_le = d.lemma(p.sum_range_le, &[sec_fn, const_s2, b, le_pointwise]);
                let yb_sq_fn = rat_fn(d, &|d, k| {
                    let yb = var_at(d, y, b, k);
                    rmul(d, yb, yb)
                });
                let nonneg_pointwise = {
                    let k_fv = d.fresh_fvar();
                    let k = d.kernel().fvar(k_fv);
                    let klt_fv = d.fresh_fvar();
                    let klt_ty = d.lt(k, n);
                    let ybk = var_at(d, y, b, k);
                    let nn = d.lemma(p.sq_nonneg, &[ybk]);
                    let t = d.lam_fv(klt_fv, klt_ty, nn);
                    d.lam_fv(k_fv, nat, t)
                };
                let he2b_nn = d.lemma(
                    p.expectation_nonneg,
                    &[yb_sq_fn, pf, n, nonneg_pointwise, hd],
                );
                let m1 = d.lemma(
                    p.mul_le_mul_of_nonneg_right,
                    &[sum_sec, t_b, e2b, he2b_nn, hsum_le],
                );
                let t_nn_pointwise = {
                    let i_fv = d.fresh_fvar();
                    let i = d.kernel().fvar(i_fv);
                    let hi_ty = d.lt(i, b);
                    let hi_fv = d.fresh_fvar();
                    let t = d.lam_fv(hi_fv, hi_ty, hs2);
                    d.lam_fv(i_fv, nat, t)
                };
                let ht_nn = d.lemma(p.sum_range_nonneg, &[const_s2, b, t_nn_pointwise]);
                let he2b_le = {
                    let np = d.prelude();
                    let hb_self = d.lemma(np.lt_succ_self, &[b]);
                    d.apply(h2, &[b, hb_self])
                };
                let m2 = d.lemma(p.mul_le_mul_of_nonneg_left, &[t_b, e2b, s2, ht_nn, he2b_le]);
                let mid = rmul(d, t_b, e2b);
                let chained = d.lemma(p.le_trans, &[collected_rhs, mid, c_bar, m1, m2]);
                let back = rsymm(d, q3_expr, collected_rhs, eq_chain);
                rat_eq_rewrite(d, collected_rhs, q3_expr, back, chained, &|d, t| {
                    rle(d, p, t, c_bar)
                })
            };

            // --- fold the sixteen bounds -----------------------------------
            let e1 = expect_of(d, p, &q1, pf, n);
            let e2 = expect_of(d, p, &q2, pf, n);
            let e3 = expect_of(d, p, &q3, pf, n);
            let e4 = expect_of(d, p, &q4f, pf, n);
            let e5 = expect_of(d, p, &q5, pf, n);
            let rhs_b = bound_at(d, b);
            let le2 = le_zero_of_eq_zero(d, p, e2, hq2);
            let le4 = le_zero_of_eq_zero(d, p, e4, hq4);
            let le5 = {
                let np = d.prelude();
                let hb_self = d.lemma(np.lt_succ_self, &[b]);
                d.apply(h4, &[b, hb_self])
            };
            let items: Vec<(ExprId, ExprId, ExprId)> = vec![
                (e1, rhs_b, ih_applied),
                (e2, zero_r, le2),
                (e2, zero_r, le2),
                (e2, zero_r, le2),
                (e2, zero_r, le2),
                (e3, c_bar, hq3),
                (e3, c_bar, hq3),
                (e3, c_bar, hq3),
                (e3, c_bar, hq3),
                (e3, c_bar, hq3),
                (e3, c_bar, hq3),
                (e4, zero_r, le4),
                (e4, zero_r, le4),
                (e4, zero_r, le4),
                (e4, zero_r, le4),
                (e5, m4, le5),
            ];
            let (folded_lhs, reached, folded) = add_le_fold(d, p, &items);

            // step 3: move the bound back onto `E[(Σ_{i<succ b})⁴]`.
            let (_e, eq12) = rchain(d, start, &[(split_lhs, step1), (split_rhs, step2)]);
            let _ = folded_lhs;
            let le_start = {
                let back = rsymm(d, start, split_rhs, eq12);
                rat_eq_rewrite(d, split_rhs, start, back, folded, &|d, t| {
                    rle(d, p, t, reached)
                })
            };

            // step 4: the induction closes with `3σ⁴` of slack.
            let slack = {
                let sq = rmul(d, s2, s2);
                let two = radd(d, sq, sq);
                radd(d, two, sq)
            };
            let slack_nn = {
                let sq = rmul(d, s2, s2);
                let nn = d.lemma(p.sq_nonneg, &[s2]);
                let two = radd(d, sq, sq);
                let two_nn = d.lemma(p.add_nonneg, &[sq, sq, nn, nn]);
                d.lemma(p.add_nonneg, &[two, sq, two_nn, nn])
            };
            let reached_refl = d.lemma(p.le_refl, &[reached]);
            let padded = d.lemma(
                p.add_le_add,
                &[reached, reached, zero_r, slack, reached_refl, slack_nn],
            );
            let reached_zero = radd(d, reached, zero_r);
            let reached_slack = radd(d, reached, slack);
            let az = d.lemma(p.add_zero, &[reached]);
            let le_slack = rat_eq_rewrite(d, reached_zero, reached, az, padded, &|d, t| {
                rle(d, p, t, reached_slack)
            });

            let target = {
                let sm_b = rsum_range(d, p, const_m4, b);
                let sm_new = radd(d, sm_b, m4);
                let t_new = radd(d, t_b, s2);
                let sq = rmul(d, t_new, t_new);
                let two = radd(d, sq, sq);
                let three = radd(d, two, sq);
                radd(d, sm_new, three)
            };
            let rebalance = rring(d, p, reached_slack, target);
            let le_target =
                rat_eq_rewrite(d, reached_slack, target, rebalance, le_slack, &|d, t| {
                    rle(d, p, reached, t)
                });

            let core = d.lemma(p.le_trans, &[start, reached, target, le_start, le_target]);

            let t = d.lam_fv(h2_fv, h2_ty, core);
            let t = d.lam_fv(h4_fv, h4_ty, t);
            d.lam_fv(hfw_fv, hfw_ty, t)
        },
        m,
    );

    let value = {
        let with_m = d.lam_fv(m_fv, nat, proof);
        let with_hs2 = d.lam_fv(hs2_fv, hs2_ty, with_m);
        let with_hd = d.lam_fv(hd_fv, hd_ty, with_hs2);
        let with_s2 = d.lam_fv(s2_fv, carrier, with_hd);
        let with_m4 = d.lam_fv(m4_fv, carrier, with_s2);
        let with_n = d.lam_fv(n_fv, nat, with_m4);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        d.lam_fv(y_fv, x_ty, with_pf)
    };
    let ty = {
        let with_m = d.pi_fv(m_fv, nat, stmt);
        let with_hs2 = d.arrow(hs2_ty, with_m);
        let with_hd = d.arrow(hd_ty, with_hs2);
        let with_s2 = d.pi_fv(s2_fv, carrier, with_hd);
        let with_m4 = d.pi_fv(m4_fv, carrier, with_s2);
        let with_n = d.pi_fv(n_fv, nat, with_m4);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        d.pi_fv(y_fv, x_ty, with_pf)
    };
    d.declare_theorem(names.fourth_moment_sum_vars_le, ty, value)
}

/// `Rat.fourth_moment_tail_sumVars : ∀ Y p n M₄ σ² a m, IsDistribution p n →
/// le zero σ² → lt zero a → (∀ i < m, E[Y_i] = 0) → FourwiseUncorrelated Y m
/// p n → (∀ i < m, E[Y_i⁴] ≤ M₄) → (∀ i < m, E[Y_i²] ≤ σ²) →
/// a⁴·E[𝟙[(Σ − E Σ)⁴ ≥ a⁴]] ≤ Σ_{i<m} M₄ + 3(Σ_{i<m} σ²)²`
/// — **the first Hoeffding-class rate this carrier can state.**
///
/// Read the two sides: the left is `a⁴·P[|Σ − E Σ| ≥ a]` in the
/// multiplied-through form `Rat.markov_constructed` and every tail bound on
/// this shelf uses (no `Rat.inv` is introduced anywhere), and the right is
/// `m·M₄ + 3m²σ⁴` once `Rat.sum_range_const` collapses the two constant sums.
/// So the tail at a deviation of `m·ε` for the SUM — equivalently `ε` for the
/// sample mean — is bounded by
/// `(m M₄ + 3m²σ⁴)/(m⁴ε⁴)`, which decays like **`1/m²`**. Chebyshev on the
/// same shelf (`Rat.chebyshev_sampleMean_uncorrelated`) gives `1/m`. That
/// gap is the whole point of paying for the fourth moment.
///
/// It is NOT Hoeffding: an exponential tail needs `E[∏ f(X_j)] = ∏ E[f(X_j)]`
/// over a product space and `expFn_add`, and `binomial_rat.rs`'s header
/// records both as structurally absent here. This is the best rate the
/// available hypotheses support, and it is stated under four-wise
/// uncorrelatedness rather than independence for exactly the same reason.
///
/// Three already-proved facts and no new technique:
/// `Rat.fourth_moment_inequality` applied at `X := Rat.sumVars Y m` (Markov at
/// the fourth power); `Rat.expectation_sumVars` plus
/// `Rat.sumRange_eq_zero_of_lt` turning the per-variable centring hypothesis
/// into `E[Σ] = 0`, which lets `sumRange_congr` replace the deviation `Σ − E Σ`
/// by `Σ` inside the right-hand expectation (`Rat.neg_zero` then
/// `Rat.add_zero`, since `Rat.sub a b` unfolds to `add a (neg b)`); and
/// [`declare_fourth_moment_sum_vars_le`] for the bound itself. The INDICATOR
/// keeps the deviation form untouched — nothing here rewrites under the
/// `Rat.indicator` binder, which would need function extensionality this
/// kernel does not have.
#[allow(clippy::too_many_lines)]
fn declare_fourth_moment_tail_sum_vars(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    names: &FourthMomentNames,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);
    let x_ty = d.arrow(nat, fn_ty);

    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m4_fv = d.fresh_fvar();
    let m4 = d.kernel().fvar(m4_fv);
    let s2_fv = d.fresh_fvar();
    let s2 = d.kernel().fvar(s2_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let zero_r = rzero(d, p);
    let hd_ty = is_distribution(d, p, pf, n);
    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);
    let hs2_ty = rle(d, p, zero_r, s2);
    let hs2_fv = d.fresh_fvar();
    let hs2 = d.kernel().fvar(hs2_fv);
    let ha_ty = rlt(d, p, zero_r, a);
    let ha_fv = d.fresh_fvar();
    let ha = d.kernel().fvar(ha_fv);

    // `fun j => expectation (Y j) p n`, and the centring hypothesis over it.
    let mean_fn = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let yj = d.apply(y, &[j]);
        let body = expectation(d, p, yj, pf, n);
        d.lam_fv(j_fv, nat, body)
    };
    let hc_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi = d.lt(i, m);
        let yi = d.apply(y, &[i]);
        let e = expectation(d, p, yi, pf, n);
        let concl = req(d, e, zero_r);
        let inner = d.arrow(hi, concl);
        d.pi_fv(i_fv, nat, inner)
    };
    let hc_fv = d.fresh_fvar();
    let hc = d.kernel().fvar(hc_fv);

    let hfw_ty = d.const_app(names.fourwise_uncorrelated, &[y, m, pf, n]);
    let hfw_fv = d.fresh_fvar();
    let hfw = d.kernel().fvar(hfw_fv);
    let h4_ty = fourth_moment_bounded(d, p, y, m4, pf, n, m);
    let h4_fv = d.fresh_fvar();
    let h4 = d.kernel().fvar(h4_fv);
    let h2_ty = second_moment_bounded(d, p, y, s2, pf, n, m);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    // The sum, its mean, and the tail threshold.
    let sv = d.const_app(p.sum_vars, &[y, m]);
    let mu = expectation(d, p, sv, pf, n);
    let a_sq = rmul(d, a, a);
    let a_4 = rmul(d, a_sq, a_sq);

    let dev_body = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
        let sk = sv_at(d, p, y, m, k);
        let gap = rsub(d, p, sk, mu);
        let sq = rmul(d, gap, gap);
        rmul(d, sq, sq)
    };
    let plain_body = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
        let sk = sv_at(d, p, y, m, k);
        let sq = rmul(d, sk, sk);
        rmul(d, sq, sq)
    };
    let dev_fn = rat_fn(d, &dev_body);
    let e_dev = expectation(d, p, dev_fn, pf, n);
    let e_plain = expect_of(d, p, &plain_body, pf, n);

    let ind = d.const_app(p.indicator, &[a_4, dev_fn]);
    let e_ind = expectation(d, p, ind, pf, n);
    let lhs = rmul(d, a_4, e_ind);

    let const_m4 = const_fn(d, m4);
    let const_s2 = const_fn(d, s2);
    let bound = {
        let sm = rsum_range(d, p, const_m4, m);
        let t = rsum_range(d, p, const_s2, m);
        let sq = rmul(d, t, t);
        let two = radd(d, sq, sq);
        let three = radd(d, two, sq);
        radd(d, sm, three)
    };
    let concl = rle(d, p, lhs, bound);

    // `E[Σ] = 0`, from the per-variable centring hypothesis.
    let hmu = {
        let esv = d.lemma(p.expectation_sum_vars, &[y, pf, n, m]);
        let collapse = d.lemma(p.sum_range_eq_zero_of_lt, &[mean_fn, m, hc]);
        let sum_m = rsum_range(d, p, mean_fn, m);
        rtrans(d, mu, sum_m, zero_r, esv, collapse)
    };

    // `E[(Σ − E Σ)⁴] = E[Σ⁴]`, pointwise, since the mean is zero.
    let bridge = {
        let w_dev = weighted_of(d, &dev_body, pf);
        let w_plain = weighted_of(d, &plain_body, pf);
        let pointwise = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let sk = sv_at(d, p, y, m, k);
            let pk = d.apply(pf, &[k]);

            let quart_at = |d: &mut IntDev<'_>, t: ExprId| -> ExprId {
                let sq = rmul(d, t, t);
                let q = rmul(d, sq, sq);
                rmul(d, q, pk)
            };
            let step_a = rcongr(d, mu, zero_r, hmu, &|d, t| {
                let gap = rsub(d, p, sk, t);
                quart_at(d, gap)
            });
            // `sub s zero` unfolds to `add s (neg zero)`; `neg_zero` then
            // `add_zero` retire it.
            let neg_zero_e = rneg(d, zero_r);
            let hnz = d.const_app(p.neg_zero, &[]);
            let s_plus_negzero = radd(d, sk, neg_zero_e);
            let s_plus_zero = radd(d, sk, zero_r);
            let s1 = rcongr(d, neg_zero_e, zero_r, hnz, &|d, t| radd(d, sk, t));
            let s2l = d.lemma(p.add_zero, &[sk]);
            let hsub = rtrans(d, s_plus_negzero, s_plus_zero, sk, s1, s2l);
            let gap_zero = rsub(d, p, sk, zero_r);
            let step_b = rcongr(d, gap_zero, sk, hsub, &|d, t| quart_at(d, t));

            let gap_mu = rsub(d, p, sk, mu);
            let from = quart_at(d, gap_mu);
            let mid = quart_at(d, gap_zero);
            let to = quart_at(d, sk);
            let full = rtrans(d, from, mid, to, step_a, step_b);
            d.lam_fv(k_fv, nat, full)
        };
        d.lemma(p.sum_range_congr, &[w_dev, w_plain, n, pointwise])
    };

    let fmi = d.lemma(
        p.binomial_rat.fourth_moment_inequality,
        &[a, sv, pf, n, hd, ha],
    );
    let le_plain = rat_eq_rewrite(d, e_dev, e_plain, bridge, fmi, &|d, t| rle(d, p, lhs, t));
    let moment = d.lemma(
        names.fourth_moment_sum_vars_le,
        &[y, pf, n, m4, s2, hd, hs2, m, hfw, h4, h2],
    );
    let core = d.lemma(p.le_trans, &[lhs, e_plain, bound, le_plain, moment]);

    let value = {
        let t = d.lam_fv(h2_fv, h2_ty, core);
        let t = d.lam_fv(h4_fv, h4_ty, t);
        let t = d.lam_fv(hfw_fv, hfw_ty, t);
        let t = d.lam_fv(hc_fv, hc_ty, t);
        let t = d.lam_fv(ha_fv, ha_ty, t);
        let t = d.lam_fv(hs2_fv, hs2_ty, t);
        let t = d.lam_fv(hd_fv, hd_ty, t);
        let t = d.lam_fv(m_fv, nat, t);
        let t = d.lam_fv(a_fv, carrier, t);
        let t = d.lam_fv(s2_fv, carrier, t);
        let t = d.lam_fv(m4_fv, carrier, t);
        let t = d.lam_fv(n_fv, nat, t);
        let t = d.lam_fv(pf_fv, fn_ty, t);
        d.lam_fv(y_fv, x_ty, t)
    };
    let ty = {
        let t = d.arrow(h2_ty, concl);
        let t = d.arrow(h4_ty, t);
        let t = d.arrow(hfw_ty, t);
        let t = d.arrow(hc_ty, t);
        let t = d.arrow(ha_ty, t);
        let t = d.arrow(hs2_ty, t);
        let t = d.arrow(hd_ty, t);
        let t = d.pi_fv(m_fv, nat, t);
        let t = d.pi_fv(a_fv, carrier, t);
        let t = d.pi_fv(s2_fv, carrier, t);
        let t = d.pi_fv(m4_fv, carrier, t);
        let t = d.pi_fv(n_fv, nat, t);
        let t = d.pi_fv(pf_fv, fn_ty, t);
        d.pi_fv(y_fv, x_ty, t)
    };
    d.declare_theorem(names.fourth_moment_tail_sum_vars, ty, value)
}

/// Declare everything this module owns.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(crate) fn declare_fourth_moment_all(
    d: &mut IntDev<'_>,
    p: &RatPrelude,
) -> Result<(), KernelError> {
    let names = p.fourth_moment;
    declare_expectation_sum_vars_mul(d, *p, &names)?;
    declare_expectation_sum_vars_mul_eq_zero(d, *p, &names)?;
    declare_fourwise_uncorrelated(d, *p, &names)?;
    declare_expectation_sq_sum_vars_mul_sq(d, *p, &names)?;
    declare_fourth_moment_sum_vars_le(d, *p, &names)?;
    declare_fourth_moment_tail_sum_vars(d, *p, &names)?;
    Ok(())
}

#[cfg(test)]
#[path = "fourth_moment_tests.rs"]
mod fourth_moment_tests;
