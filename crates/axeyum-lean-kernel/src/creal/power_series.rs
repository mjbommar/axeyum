//! Power series over `CReal`, with a radius of convergence stated as an
//! explicit ratio witness rather than a supremum.
//!
//! ## What was already here, and what this file adds
//!
//! The comparison test and the ratio test are **not** new: `series.rs` already
//! declares [`CRealPrelude::sum_range_cauchy_of_dominated`] (`∀ f g, (∀ k, le
//! (abs (f k)) (g k)) → Cauchy (sumRange g) → Cauchy (sumRange f)`) and
//! `CReal.sumRange_comparisonTest`, `geometric.rs` declares
//! [`CRealPrelude::geom_cauchy_of_lt`], and `ratio_test.rs` declares
//! `CReal.sumRangeRatioTest` together with the scaled geometric bridge
//! [`super::RatioTestNames::geom_scaled_cauchy_of_lt`]. `power.rs` declares the
//! *term* [`CRealPrelude::power_series_term`] (`fun c j x => mul (c j) (pow x
//! j)`), its congruence, and a domination bound
//! [`CRealPrelude::power_series_term_abs_le`] restricted to `0 ≤ x ≤ r` with an
//! **unweighted** coefficient bound `|c j| ≤ M`.
//!
//! What did not exist is the partial-sum function itself and a radius
//! statement. This file adds both, plus the two general facts the radius proof
//! turned out to need.
//!
//! ## `abs_pow_le`, and why the signed case needs it
//!
//! [`CRealPrelude::power_series_term_abs_le`] can avoid any "`|xⁿ| = |x|ⁿ`"
//! lemma precisely because it assumes `0 ≤ x`: there `abs (pow x j)` is handled
//! by [`CRealPrelude::pow_nonneg`] and never has to travel through `abs` at
//! all. A radius of convergence is a statement about `|x| < R`, i.e. about an
//! `x` that may be negative, so that dodge is unavailable and the bound
//! `|xᵏ| ≤ bᵏ` has to be proved.
//!
//! [`declare_abs_pow_le`] proves it by `Nat.rec` on `k`, and the step is a
//! single application of [`CRealPrelude::abs_mul_le_of_bounds`]: `pow`'s own
//! ι-reduction identifies `pow x (Nat.succ j)` with `mul (pow x j) x` and `pow
//! b (Nat.succ j)` with `mul (pow b j) b`, so the goal is *definitionally* that
//! lemma's conclusion at `(c, t, B, b) := (pow x j, x, pow b j, b)`, and the
//! inductive hypothesis together with the outer `le (abs x) b` are exactly its
//! two premises. No case split on a sign ever happens — `CReal.le` is
//! undecidable and nothing here branches on it.
//!
//! The base case is the only fiddly part, and only because this kernel has no
//! `CReal.abs_one`: the goal `le (abs (pow x Nat.zero)) (pow b Nat.zero)`
//! reduces to `le (abs one) one`, which [`CRealPrelude::abs_le`] closes from
//! `le one one` ([`CRealPrelude::le_refl`]) and `le (neg one) one`. That second
//! premise is assembled here from [`CRealPrelude::zero_lt_one`] via
//! [`CRealPrelude::neg_le_neg`] and `series.rs`'s [`neg_zero_equiv`] (`neg zero
//! ~ zero`), then [`CRealPrelude::le_trans`].
//!
//! ## The radius, stated with a ratio witness and not a supremum
//!
//! `R` is carried as an ordinary parameter together with a coefficient bound
//! `∀ k, |a k| · Rᵏ ≤ M`, and "`x` is strictly inside the radius" is carried as
//! the **data** `le (abs x) (mul r R)` for a caller-supplied `r` with `0 ≤ r <
//! 1`. This is the same design decision `geometric.rs` records for `PosBound (1
//! − x) k`: over `CReal` the order is undecidable, so a ratio that a proof can
//! actually compute with cannot be manufactured from a bare `lt (abs x) R` —
//! it has to be supplied. Defining the radius as a supremum would need the
//! least-upper-bound principle over a set that is not located, which is a
//! strictly larger obligation than anything this file needs.
//!
//! With that, the domination chain is short:
//!
//! ```text
//!   |a k · xᵏ| ≤ |a k| · (r·R)ᵏ      -- abs_mul_le_of_bounds, using abs_pow_le
//!              = |a k| · (rᵏ · Rᵏ)   -- powMulDistrib
//!              = (|a k| · Rᵏ) · rᵏ   -- mul_assoc / mul_comm
//!              ≤ M · rᵏ              -- the coefficient bound, times rᵏ ≥ 0
//! ```
//!
//! and then the Cauchy theorem feeds that to
//! [`CRealPrelude::sum_range_cauchy_of_dominated`] against
//! [`super::RatioTestNames::geom_scaled_cauchy_of_lt`] at `(w, x) := (M, r)`.
//!
//! ## `expSeriesPartial` and `cosSeriesPartial` as instances
//!
//! Both are `sumRange` of a term sequence at the point `1`
//! (`CReal.expSeriesPartial := CReal.sumRange CReal.expTerm`), so the instance
//! statement is `Equiv (expSeriesPartial n) (powerSeriesPartial expTerm one
//! n)`. It is **not** `Eq.refl`: `powerSeriesPartial` multiplies each
//! coefficient by `pow one k`, and `pow one k` is only ι-equal to `one` at `k =
//! 0` — at `Nat.succ j` it is `mul (pow one j) one`, which needs
//! [`CRealPrelude::mul_one`] to collapse. Hence [`declare_one_pow`]
//! (`CReal.one_pow : ∀ k, Equiv (pow one k) one`, itself a `Nat.rec`
//! induction), and the instances are proved `Equiv`s obtained by
//! [`CRealPrelude::sum_range_congr`].

use super::convergence::exists_ty;
use super::series::neg_zero_equiv;
use super::{CRealPrelude, DERIVED_HEIGHT, clt, creal_ty, equiv};
use crate::Kernel;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;

// --- small local term builders, verbatim in shape to every other `creal/*`
// module's own copies (see e.g. `ratio_test.rs`, `geometric.rs`, `power.rs`) --

fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul, &[x, y])
}

fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

fn czero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

fn cone(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.one, vec![])
}

fn cle(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.le, &[x, y])
}

fn cabs(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.abs, &[x])
}

fn cpow(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.pow, &[x, n])
}

fn cadd(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.add, &[x, y])
}

fn pos_bound_of(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, k: ExprId) -> ExprId {
    d.const_app(p.pos_bound, &[x, k])
}

/// Chain a run of `Equiv` steps left to right, starting at `start`.
///
/// A verbatim reproduction of `series.rs`'s own private `echain`, which is a
/// bare `fn` there and so not reachable from this module; `ratio_test.rs` sets
/// the precedent for copying a sibling module's private helper rather than
/// widening its visibility.
fn echain(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    start: ExprId,
    steps: &[(ExprId, ExprId)],
) -> ExprId {
    let mut current = start;
    let mut proof = d.lemma(p.equiv_refl, &[start]);
    for &(next, step) in steps {
        proof = d.lemma(p.equiv_trans, &[start, current, next, proof, step]);
        current = next;
    }
    proof
}

// ---------------------------------------------------------------------------
// `CReal.abs_pow_le` -- `|x| ≤ b` implies `|xᵏ| ≤ bᵏ`.
// ---------------------------------------------------------------------------

/// `CReal.abs_pow_le : ∀ x b, le (abs x) b → ∀ k, le (abs (pow x k)) (pow b
/// k)`. See the module documentation for why the signed case needs this and
/// [`CRealPrelude::power_series_term_abs_le`]'s `0 ≤ x` route does not.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_abs_pow_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let hyp = {
        let ax = cabs(d, p, x);
        cle(d, p, ax, b)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let motive = |d: &mut IntDev<'_>, v: ExprId| -> ExprId {
        let px = cpow(d, p, x, v);
        let apx = cabs(d, p, px);
        let pb = cpow(d, p, b, v);
        cle(d, p, apx, pb)
    };

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let stmt_inner = motive(d, k);

    let proof_inner = d.induct(
        &motive,
        &|d| {
            // Goal reduces to `le (abs one) one`.
            let zero_c = czero(d, p);
            let one = cone(d, p);
            let neg_one = cneg(d, p, one);
            let neg_zero = cneg(d, p, zero_c);

            let lt01 = d.lemma(p.zero_lt_one, &[]);
            let le01 = d.lemma(p.le_of_lt, &[zero_c, one, lt01]);
            // h_nn : le (neg one) (neg zero)
            let h_nn = d.lemma(p.neg_le_neg, &[zero_c, one, le01]);
            let nz_eq = neg_zero_equiv(d, p); // Equiv (neg zero) zero
            let refl_n1 = d.lemma(p.equiv_refl, &[neg_one]);
            let h_n1_0 = d.lemma(
                p.le_congr,
                &[neg_one, neg_one, neg_zero, zero_c, refl_n1, nz_eq, h_nn],
            );
            // h_n1_1 : le (neg one) one
            let h_n1_1 = d.lemma(p.le_trans, &[neg_one, zero_c, one, h_n1_0, le01]);
            let refl_one = d.lemma(p.le_refl, &[one]);
            d.lemma(p.abs_le, &[one, one, refl_one, h_n1_1])
        },
        &|d, j, ih| {
            // Goal reduces to `le (abs (mul (pow x j) x)) (mul (pow b j) b)`,
            // which is `abs_mul_le_of_bounds` at `(pow x j, x, pow b j, b)`.
            let px_j = cpow(d, p, x, j);
            let pb_j = cpow(d, p, b, j);
            d.lemma(p.abs_mul_le_of_bounds, &[px_j, x, pb_j, b, ih, h])
        },
        k,
    );

    let ty = {
        let inner = d.pi_fv(k_fv, nat, stmt_inner);
        let with_h = d.arrow(hyp, inner);
        let with_b = d.pi_fv(b_fv, carrier, with_h);
        d.pi_fv(x_fv, carrier, with_b)
    };
    let value = {
        let inner = d.lam_fv(k_fv, nat, proof_inner);
        let with_h = d.lam_fv(h_fv, hyp, inner);
        let with_b = d.lam_fv(b_fv, carrier, with_h);
        d.lam_fv(x_fv, carrier, with_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.power_series.abs_pow_le,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// `CReal.one_pow` -- `1ᵏ ~ 1`.
// ---------------------------------------------------------------------------

/// `CReal.one_pow : ∀ k, Equiv (pow one k) one`. `Nat.rec` on `k`: at
/// `Nat.zero` `pow one Nat.zero` ι-reduces to `one` and the goal is
/// [`CRealPrelude::equiv_refl`]; at `Nat.succ j` it reduces to `mul (pow one j)
/// one`, which [`CRealPrelude::mul_one`] collapses to `pow one j` before the
/// inductive hypothesis finishes the job.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_one_pow(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    let motive = |d: &mut IntDev<'_>, v: ExprId| -> ExprId {
        let one = cone(d, p);
        let pv = cpow(d, p, one, v);
        equiv(d, p, pv, one)
    };

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let stmt_inner = motive(d, k);

    let proof_inner = d.induct(
        &motive,
        &|d| {
            let one = cone(d, p);
            d.lemma(p.equiv_refl, &[one])
        },
        &|d, j, ih| {
            let one = cone(d, p);
            let p1j = cpow(d, p, one, j);
            let prod = cmul(d, p, p1j, one);
            let collapse = d.lemma(p.mul_one, &[p1j]); // Equiv (mul p1j one) p1j
            d.lemma(p.equiv_trans, &[prod, p1j, one, collapse, ih])
        },
        k,
    );

    let ty = d.pi_fv(k_fv, nat, stmt_inner);
    let value = d.lam_fv(k_fv, nat, proof_inner);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.power_series.one_pow,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// `CReal.powerSeriesPartial` -- the partial sums.
// ---------------------------------------------------------------------------

/// `λ k, CReal.powerSeriesTerm a k x` — the summand of
/// [`declare_power_series_partial`], shared with every theorem below so the
/// `sumRange` applications all land on the identical closure shape.
fn term_fn(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, x: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let body = d.const_app(p.power_series_term, &[a, k, x]);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `CReal.powerSeriesPartial : (Nat → CReal) → CReal → Nat → CReal := fun a x
/// => sumRange (fun k => powerSeriesTerm a k x)` — the `n`-th partial sum
/// `Σ_{k<n} a k · xᵏ`, built on the already-landed
/// [`CRealPrelude::power_series_term`] rather than re-spelling `mul (a k) (pow
/// x k)`, so `power.rs`'s [`CRealPrelude::power_series_term_congr`] and
/// [`CRealPrelude::power_series_term_abs_le`] apply to it unchanged.
///
/// A bare `Definition`, asserting nothing; its evaluation test is in
/// `creal/creal_tests.rs`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_power_series_partial(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let coeff_ty = d.arrow(nat, carrier);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let f = term_fn(d, p, a, x);
    let body = d.const_app(p.sum_range, &[f]);

    let value = {
        let with_x = d.lam_fv(x_fv, carrier, body);
        d.lam_fv(a_fv, coeff_ty, with_x)
    };
    let ty = {
        let seq_ty = d.arrow(nat, carrier);
        let with_x = d.arrow(carrier, seq_ty);
        d.arrow(coeff_ty, with_x)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.power_series.power_series_partial,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 44),
    })
}

// ---------------------------------------------------------------------------
// `CReal.powerSeriesTermRadiusBound` -- the domination bound inside a radius.
// ---------------------------------------------------------------------------

/// `CReal.powerSeriesTermRadiusBound : ∀ a M R r x, (∀ k, le (mul (abs (a k))
/// (pow R k)) M) → le zero r → le (abs x) (mul r R) → ∀ k, le (abs
/// (powerSeriesTerm a k x)) (mul M (pow r k))`.
///
/// The four-step chain in the module documentation, in order:
/// [`CRealPrelude::abs_mul_le_of_bounds`] at `(a k, pow x k, abs (a k), pow
/// (mul r R) k)` — whose second premise is [`declare_abs_pow_le`] and whose
/// first is [`CRealPrelude::le_refl`] — then one `Equiv` chain built from
/// [`CRealPrelude::pow_mul_distrib`], [`CRealPrelude::mul_comm`] and
/// [`CRealPrelude::mul_assoc`], transported by [`CRealPrelude::le_congr`],
/// then the coefficient hypothesis multiplied by the nonnegative `pow r k`
/// ([`CRealPrelude::pow_nonneg`]).
///
/// `le zero R` is deliberately **not** a hypothesis: nothing in this
/// derivation needs it. The only nonnegativity the proof consumes is `0 ≤ rᵏ`,
/// which comes from `0 ≤ r` alone.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_power_series_term_radius_bound(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let coeff_ty = d.arrow(nat, carrier);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let r_big_fv = d.fresh_fvar();
    let r_big = d.kernel().fvar(r_big_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    // hcoef : ∀ k, le (mul (abs (a k)) (pow R k)) M
    let hcoef_ty = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let ak = d.apply(a, &[k]);
        let aak = cabs(d, p, ak);
        let pr = cpow(d, p, r_big, k);
        let lhs = cmul(d, p, aak, pr);
        let body = cle(d, p, lhs, m);
        d.pi_fv(k_fv, nat, body)
    };
    let hcoef_fv = d.fresh_fvar();
    let hcoef = d.kernel().fvar(hcoef_fv);

    // hr0 : le zero r
    let hr0_ty = {
        let zero_c = czero(d, p);
        cle(d, p, zero_c, r)
    };
    let hr0_fv = d.fresh_fvar();
    let hr0 = d.kernel().fvar(hr0_fv);

    // hx : le (abs x) (mul r R)
    let rr = cmul(d, p, r, r_big);
    let hx_ty = {
        let ax = cabs(d, p, x);
        cle(d, p, ax, rr)
    };
    let hx_fv = d.fresh_fvar();
    let hx = d.kernel().fvar(hx_fv);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let ak = d.apply(a, &[k]);
    let aak = cabs(d, p, ak); // A = |a k|
    let pow_r_k = cpow(d, p, r, k); // P = rᵏ
    let pow_bigr_k = cpow(d, p, r_big, k); // Q = Rᵏ
    let pow_rr_k = cpow(d, p, rr, k); // (r·R)ᵏ
    let pow_x_k = cpow(d, p, x, k);

    // step 1: |a k · xᵏ| ≤ |a k| · (r·R)ᵏ
    let refl_aak = d.lemma(p.le_refl, &[aak]);
    let habs_pow = d.lemma(p.power_series.abs_pow_le, &[x, rr, hx, k]);
    let step1 = d.lemma(
        p.abs_mul_le_of_bounds,
        &[ak, pow_x_k, aak, pow_rr_k, refl_aak, habs_pow],
    );
    let lhs1 = cmul(d, p, aak, pow_rr_k);

    // step 2: |a k| · (r·R)ᵏ ~ (|a k| · Rᵏ) · rᵏ
    let mid_pq = cmul(d, p, pow_r_k, pow_bigr_k); // P·Q
    let mid_qp = cmul(d, p, pow_bigr_k, pow_r_k); // Q·P
    let a_pq = cmul(d, p, aak, mid_pq);
    let a_qp = cmul(d, p, aak, mid_qp);
    let coef_prod = cmul(d, p, aak, pow_bigr_k); // A·Q = |a k|·Rᵏ
    let target_prod = cmul(d, p, coef_prod, pow_r_k); // (A·Q)·P

    let distrib = d.lemma(p.pow_mul_distrib, &[r, r_big, k]); // Equiv (P·Q) ((r·R)ᵏ)
    let distrib_symm = d.lemma(p.equiv_symm, &[mid_pq, pow_rr_k, distrib]);
    let refl_a1 = d.lemma(p.equiv_refl, &[aak]);
    let e1 = d.lemma(
        p.mul_congr,
        &[aak, aak, pow_rr_k, mid_pq, refl_a1, distrib_symm],
    );
    let comm_pq = d.lemma(p.mul_comm, &[pow_r_k, pow_bigr_k]); // Equiv (P·Q) (Q·P)
    let refl_a2 = d.lemma(p.equiv_refl, &[aak]);
    let e2 = d.lemma(p.mul_congr, &[aak, aak, mid_pq, mid_qp, refl_a2, comm_pq]);
    let assoc = d.lemma(p.mul_assoc, &[aak, pow_bigr_k, pow_r_k]); // Equiv ((A·Q)·P) (A·(Q·P))
    let e3 = d.lemma(p.equiv_symm, &[target_prod, a_qp, assoc]);
    let echain_proof = echain(d, p, lhs1, &[(a_pq, e1), (a_qp, e2), (target_prod, e3)]);

    // transport step1's right-hand side across that Equiv
    let term = d.const_app(p.power_series_term, &[a, k, x]);
    let abs_term = cabs(d, p, term);
    let refl_abs_term = d.lemma(p.equiv_refl, &[abs_term]);
    let step2 = d.lemma(
        p.le_congr,
        &[
            abs_term,
            abs_term,
            lhs1,
            target_prod,
            refl_abs_term,
            echain_proof,
            step1,
        ],
    );

    // step 3: (|a k| · Rᵏ) · rᵏ ≤ M · rᵏ
    let hpk = d.lemma(p.pow_nonneg, &[r, hr0, k]); // le zero (pow r k)
    let hck = d.apply(hcoef, &[k]); // le (A·Q) M
    let left_form = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[pow_r_k, coef_prod, m, hpk, hck],
    ); // le (P·(A·Q)) (P·M)
    let p_coef = cmul(d, p, pow_r_k, coef_prod);
    let p_m = cmul(d, p, pow_r_k, m);
    let m_p = cmul(d, p, m, pow_r_k);
    let comm_l = d.lemma(p.mul_comm, &[pow_r_k, coef_prod]); // Equiv (P·(A·Q)) ((A·Q)·P)
    let comm_r = d.lemma(p.mul_comm, &[pow_r_k, m]); // Equiv (P·M) (M·P)
    let step3 = d.lemma(
        p.le_congr,
        &[p_coef, target_prod, p_m, m_p, comm_l, comm_r, left_form],
    );

    let proof_inner = d.lemma(p.le_trans, &[abs_term, target_prod, m_p, step2, step3]);
    let stmt_inner = cle(d, p, abs_term, m_p);

    let ty = {
        let inner = d.pi_fv(k_fv, nat, stmt_inner);
        let with_hx = d.arrow(hx_ty, inner);
        let with_hr0 = d.arrow(hr0_ty, with_hx);
        let with_hcoef = d.arrow(hcoef_ty, with_hr0);
        let with_x = d.pi_fv(x_fv, carrier, with_hcoef);
        let with_r = d.pi_fv(r_fv, carrier, with_x);
        let with_bigr = d.pi_fv(r_big_fv, carrier, with_r);
        let with_m = d.pi_fv(m_fv, carrier, with_bigr);
        d.pi_fv(a_fv, coeff_ty, with_m)
    };
    let value = {
        let inner = d.lam_fv(k_fv, nat, proof_inner);
        let with_hx = d.lam_fv(hx_fv, hx_ty, inner);
        let with_hr0 = d.lam_fv(hr0_fv, hr0_ty, with_hx);
        let with_hcoef = d.lam_fv(hcoef_fv, hcoef_ty, with_hr0);
        let with_x = d.lam_fv(x_fv, carrier, with_hcoef);
        let with_r = d.lam_fv(r_fv, carrier, with_x);
        let with_bigr = d.lam_fv(r_big_fv, carrier, with_r);
        let with_m = d.lam_fv(m_fv, carrier, with_bigr);
        d.lam_fv(a_fv, coeff_ty, with_m)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.power_series.power_series_term_radius_bound,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// `CReal.powerSeriesCauchyWithinRadius` / `...ConvergesWithinRadius`.
// ---------------------------------------------------------------------------

/// The shared statement prefix of the two radius theorems: everything from
/// `∀ a M R r x` down to the `PosBound` witness, with `body` as the
/// conclusion. Kept in one place so the two declarations cannot drift into
/// different hypothesis orders.
struct RadiusFrame {
    a_fv: u64,
    m_fv: u64,
    r_big_fv: u64,
    r_fv: u64,
    x_fv: u64,
    hcoef_fv: u64,
    hcoef_ty: ExprId,
    hr0_fv: u64,
    hr0_ty: ExprId,
    hlt_fv: u64,
    hlt_ty: ExprId,
    hx_fv: u64,
    hx_ty: ExprId,
    kk_fv: u64,
    hpb_fv: u64,
    hpb_ty: ExprId,
}

impl RadiusFrame {
    fn close_ty(&self, d: &mut IntDev<'_>, p: CRealPrelude, body: ExprId) -> ExprId {
        let carrier = creal_ty(d, p);
        let nat = d.nat_ty();
        let coeff_ty = d.arrow(nat, carrier);
        let with_hpb = d.pi_fv(self.hpb_fv, self.hpb_ty, body);
        let with_kk = d.pi_fv(self.kk_fv, nat, with_hpb);
        let with_hx = d.arrow(self.hx_ty, with_kk);
        let with_hlt = d.arrow(self.hlt_ty, with_hx);
        let with_hr0 = d.arrow(self.hr0_ty, with_hlt);
        let with_hcoef = d.arrow(self.hcoef_ty, with_hr0);
        let with_x = d.pi_fv(self.x_fv, carrier, with_hcoef);
        let with_r = d.pi_fv(self.r_fv, carrier, with_x);
        let with_bigr = d.pi_fv(self.r_big_fv, carrier, with_r);
        let with_m = d.pi_fv(self.m_fv, carrier, with_bigr);
        d.pi_fv(self.a_fv, coeff_ty, with_m)
    }

    fn close_value(&self, d: &mut IntDev<'_>, p: CRealPrelude, body: ExprId) -> ExprId {
        let carrier = creal_ty(d, p);
        let nat = d.nat_ty();
        let coeff_ty = d.arrow(nat, carrier);
        let with_hpb = d.lam_fv(self.hpb_fv, self.hpb_ty, body);
        let with_kk = d.lam_fv(self.kk_fv, nat, with_hpb);
        let with_hx = d.lam_fv(self.hx_fv, self.hx_ty, with_kk);
        let with_hlt = d.lam_fv(self.hlt_fv, self.hlt_ty, with_hx);
        let with_hr0 = d.lam_fv(self.hr0_fv, self.hr0_ty, with_hlt);
        let with_hcoef = d.lam_fv(self.hcoef_fv, self.hcoef_ty, with_hr0);
        let with_x = d.lam_fv(self.x_fv, carrier, with_hcoef);
        let with_r = d.lam_fv(self.r_fv, carrier, with_x);
        let with_bigr = d.lam_fv(self.r_big_fv, carrier, with_r);
        let with_m = d.lam_fv(self.m_fv, carrier, with_bigr);
        d.lam_fv(self.a_fv, coeff_ty, with_m)
    }
}

/// Build the shared frame, and with it the `Cauchy (powerSeriesPartial a x)`
/// proof term that both radius theorems are built from.
///
/// Returns `(frame, partial, cauchy_proof)` where `partial` is
/// `powerSeriesPartial a x` as a term.
fn radius_cauchy(d: &mut IntDev<'_>, p: CRealPrelude) -> (RadiusFrame, ExprId, ExprId) {
    let nat = d.nat_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let r_big_fv = d.fresh_fvar();
    let r_big = d.kernel().fvar(r_big_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let hcoef_ty = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let ak = d.apply(a, &[k]);
        let aak = cabs(d, p, ak);
        let pr = cpow(d, p, r_big, k);
        let lhs = cmul(d, p, aak, pr);
        let body = cle(d, p, lhs, m);
        d.pi_fv(k_fv, nat, body)
    };
    let hcoef_fv = d.fresh_fvar();
    let hcoef = d.kernel().fvar(hcoef_fv);

    let hr0_ty = {
        let zero_c = czero(d, p);
        cle(d, p, zero_c, r)
    };
    let hr0_fv = d.fresh_fvar();
    let hr0 = d.kernel().fvar(hr0_fv);

    let one_c = cone(d, p);
    let hlt_ty = clt(d, p, r, one_c);
    let hlt_fv = d.fresh_fvar();
    let hlt = d.kernel().fvar(hlt_fv);

    let rr = cmul(d, p, r, r_big);
    let hx_ty = {
        let ax = cabs(d, p, x);
        cle(d, p, ax, rr)
    };
    let hx_fv = d.fresh_fvar();
    let hx = d.kernel().fvar(hx_fv);

    let neg_r = cneg(d, p, r);
    let one_minus_r = cadd(d, p, one_c, neg_r);
    let kk_fv = d.fresh_fvar();
    let kk = d.kernel().fvar(kk_fv);
    let hpb_ty = pos_bound_of(d, p, one_minus_r, kk);
    let hpb_fv = d.fresh_fvar();
    let hpb = d.kernel().fvar(hpb_fv);

    // f := λ k, powerSeriesTerm a k x ; g := λ n, mul M (pow r n)
    let f = term_fn(d, p, a, x);
    let g = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let pr = cpow(d, p, r, n);
        let body = cmul(d, p, m, pr);
        d.lam_fv(n_fv, nat, body)
    };

    // hdom : ∀ k, le (abs (f k)) (g k)
    let hdom = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = d.lemma(
            p.power_series.power_series_term_radius_bound,
            &[a, m, r_big, r, x, hcoef, hr0, hx, k],
        );
        d.lam_fv(k_fv, nat, body)
    };

    // hg : Cauchy (sumRange g)
    let hg = d.lemma(
        p.ratio_test.geom_scaled_cauchy_of_lt,
        &[r, hr0, hlt, kk, hpb, m],
    );

    let cauchy_proof = d.lemma(p.sum_range_cauchy_of_dominated, &[f, g, hdom, hg]);
    let partial = d.const_app(p.power_series.power_series_partial, &[a, x]);

    (
        RadiusFrame {
            a_fv,
            m_fv,
            r_big_fv,
            r_fv,
            x_fv,
            hcoef_fv,
            hcoef_ty,
            hr0_fv,
            hr0_ty,
            hlt_fv,
            hlt_ty,
            hx_fv,
            hx_ty,
            kk_fv,
            hpb_fv,
            hpb_ty,
        },
        partial,
        cauchy_proof,
    )
}

/// `CReal.powerSeriesCauchyWithinRadius`. See the module documentation: the
/// domination bound [`declare_power_series_term_radius_bound`] against
/// [`super::RatioTestNames::geom_scaled_cauchy_of_lt`] at `(w, x) := (M, r)`,
/// combined by [`CRealPrelude::sum_range_cauchy_of_dominated`].
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_power_series_cauchy_within_radius(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let (frame, partial, cauchy_proof) = radius_cauchy(d, p);
    let body = d.const_app(p.cauchy, &[partial]);
    let ty = frame.close_ty(d, p, body);
    let value = frame.close_value(d, p, cauchy_proof);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.power_series.power_series_cauchy_within_radius,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.powerSeriesConvergesWithinRadius` — the same hypotheses, with
/// [`CRealPrelude::converges_of_cauchy`] applied to
/// [`declare_power_series_cauchy_within_radius`]'s conclusion.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_power_series_converges_within_radius(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let (frame, partial, cauchy_proof) = radius_cauchy(d, p);
    let conv = d.lemma(p.converges_of_cauchy, &[partial, cauchy_proof]);

    let predicate = {
        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let inner = d.const_app(p.converges, &[partial, l]);
        d.lam_fv(l_fv, carrier, inner)
    };
    let body = exists_ty(d, p, carrier, predicate);

    let ty = frame.close_ty(d, p, body);
    let value = frame.close_value(d, p, conv);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.power_series.power_series_converges_within_radius,
        uparams: vec![],
        ty,
        value,
    })
}

/// The kernel names `creal/power_series.rs` declares.
///
/// One of ADR-1512's per-module registries behind the [`CRealPrelude`] facade:
/// the field, its documentation and its interning all live beside the
/// `declare_*` that uses them, so a declaration added here does not touch
/// `creal.rs`'s own name struct at all.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PowerSeriesNames {
    /// `CReal.abs_pow_le : ∀ x b, le (abs x) b → ∀ k, le (abs (pow x k)) (pow
    /// b k)` — the missing `|xᵏ| ≤ bᵏ` step for a **signed** `x`.
    /// [`CRealPrelude::power_series_term_abs_le`] does not need it because it
    /// assumes `0 ≤ x`; a radius of convergence is a statement about `|x| <
    /// R`, so it does. `Nat.rec` on `k`, with
    /// [`CRealPrelude::abs_mul_le_of_bounds`] as the entire step. See
    /// `creal/power_series.rs::declare_abs_pow_le`.
    pub abs_pow_le: NameId,
    /// `CReal.one_pow : ∀ k, Equiv (pow one k) one`. Needed because
    /// [`PowerSeriesNames::power_series_partial`] at the point `one` multiplies
    /// each coefficient by `pow one k`, which is `Eq.refl`-equal to `one` only
    /// at `k = 0`. See `creal/power_series.rs::declare_one_pow`.
    pub one_pow: NameId,
    /// `CReal.powerSeriesPartial : (Nat → CReal) → CReal → Nat → CReal := fun a
    /// x => sumRange (fun k => powerSeriesTerm a k x)` — the `n`-th partial sum
    /// `Σ_{k<n} a k · xᵏ`. A bare `Definition`, asserting nothing. See
    /// `creal/power_series.rs::declare_power_series_partial`.
    pub power_series_partial: NameId,
    /// `CReal.powerSeriesTermRadiusBound : ∀ a M R r x, (∀ k, le (mul (abs (a
    /// k)) (pow R k)) M) → le zero r → le (abs x) (mul r R) → ∀ k, le (abs
    /// (powerSeriesTerm a k x)) (mul M (pow r k))` — the domination bound
    /// inside the radius: a coefficient sequence weighted by `Rᵏ` and bounded
    /// by `M` dominates termwise by the geometric `M·rᵏ` at any point `x` with
    /// `|x| ≤ r·R`. `le zero R` is deliberately not a hypothesis; the proof
    /// consumes only `0 ≤ rᵏ`. See
    /// `creal/power_series.rs::declare_power_series_term_radius_bound`.
    pub power_series_term_radius_bound: NameId,
    /// `CReal.powerSeriesCauchyWithinRadius : ∀ a M R r x, (∀ k, le (mul (abs
    /// (a k)) (pow R k)) M) → le zero r → lt r one → le (abs x) (mul r R) → ∀
    /// k (h : PosBound (add one (neg r)) k), Cauchy (powerSeriesPartial a x)`
    /// — **the radius of convergence**, stated with an explicit ratio witness
    /// rather than a supremum (see the module documentation for why a sup is
    /// the wrong obligation here).
    /// [`PowerSeriesNames::power_series_term_radius_bound`] against
    /// [`super::RatioTestNames::geom_scaled_cauchy_of_lt`], combined by
    /// [`CRealPrelude::sum_range_cauchy_of_dominated`]. See
    /// `creal/power_series.rs::declare_power_series_cauchy_within_radius`.
    pub power_series_cauchy_within_radius: NameId,
    /// `CReal.powerSeriesConvergesWithinRadius` — the same hypotheses as
    /// [`PowerSeriesNames::power_series_cauchy_within_radius`] with conclusion
    /// `Exists (fun L => Converges (powerSeriesPartial a x) L)`, via
    /// [`CRealPrelude::converges_of_cauchy`]. See
    /// `creal/power_series.rs::declare_power_series_converges_within_radius`.
    pub power_series_converges_within_radius: NameId,
}

impl PowerSeriesNames {
    /// Interns this module's names under the `CReal` root.
    pub(super) fn intern(kernel: &mut Kernel, creal: NameId) -> Self {
        Self {
            abs_pow_le: kernel.name_str(creal, "abs_pow_le"),
            one_pow: kernel.name_str(creal, "one_pow"),
            power_series_partial: kernel.name_str(creal, "powerSeriesPartial"),
            power_series_term_radius_bound: kernel.name_str(creal, "powerSeriesTermRadiusBound"),
            power_series_cauchy_within_radius: kernel
                .name_str(creal, "powerSeriesCauchyWithinRadius"),
            power_series_converges_within_radius: kernel
                .name_str(creal, "powerSeriesConvergesWithinRadius"),
        }
    }
}
