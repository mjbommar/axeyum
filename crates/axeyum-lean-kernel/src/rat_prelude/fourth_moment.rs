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
use super::ops::{radd, rat_ty, rchain, rcongr, req, rmul, rsum_range, rtrans, rzero};
use super::probability::expectation;
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
}

/// Intern the names under the `Rat` root.
pub(crate) fn intern_fourth_moment(k: &mut Kernel) -> FourthMomentNames {
    let anon = k.anon();
    let rat = k.name_str(anon, "Rat");
    FourthMomentNames {
        expectation_sum_vars_mul: k.name_str(rat, "expectation_sumVars_mul"),
        expectation_sum_vars_mul_eq_zero: k.name_str(rat, "expectation_sumVars_mul_eq_zero"),
        fourwise_uncorrelated: k.name_str(rat, "FourwiseUncorrelated"),
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
    Ok(())
}

#[cfg(test)]
#[path = "fourth_moment_tests.rs"]
mod fourth_moment_tests;
