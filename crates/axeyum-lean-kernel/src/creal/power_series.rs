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

use super::series::neg_zero_equiv;
use super::{CRealPrelude, DERIVED_HEIGHT, creal_ty, equiv};
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
}

impl PowerSeriesNames {
    /// Interns this module's names under the `CReal` root.
    pub(super) fn intern(kernel: &mut Kernel, creal: NameId) -> Self {
        Self {
            abs_pow_le: kernel.name_str(creal, "abs_pow_le"),
            one_pow: kernel.name_str(creal, "one_pow"),
            power_series_partial: kernel.name_str(creal, "powerSeriesPartial"),
        }
    }
}
