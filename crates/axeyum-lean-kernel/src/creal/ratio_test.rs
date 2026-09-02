//! Spivak Chapter 22–23's ratio test.
//!
//! Two declarations:
//!
//! - [`declare_geom_scaled_cauchy_of_lt`] (`CReal.geomScaledCauchyOfLt`) — the
//!   "scaled geometric bridge": a CONSTANT `w` times a geometric series at a
//!   general ratio `0 ≤ x < 1` stays `Cauchy`. `sumRange (fun n => mul w (pow
//!   x n))` is only `Equiv` to `mul w (sumRange (pow x ·) n)`
//!   (`CReal.mul_sumRange`, `series.rs`, already landed), not literally equal
//!   — `CReal.mul`'s own representative resamples its factors at a shifted
//!   index (`product.rs`), so the two sides are not the same rational at any
//!   index. Mirrors `exponential.rs::declare_exp_dominant_cauchy`'s own route
//!   verbatim, generalized from the fixed pair `(two, half)` to `(w, x)` and
//!   from [`CRealPrelude::geom_cauchy`] to [`CRealPrelude::geom_cauchy_of_lt`].
//!
//! - [`declare_sum_range_ratio_test`] (`CReal.sumRangeRatioTest`) — the ratio
//!   test itself: a sequence `f` whose consecutive absolute terms shrink by a
//!   factor `r < 1` has `Cauchy (sumRange f)`, even when `f` changes sign.
//!   Composes three already-landed general theorems, none of them redone
//!   here: [`CRealPrelude::ratio_decay_bound`] applied to `g := fun n => abs
//!   (f n)` gives `∀ n, le (abs (f n)) (mul (abs (f 0)) (pow r n))`;
//!   [`declare_geom_scaled_cauchy_of_lt`]'s own theorem at `w := abs (f 0)`
//!   gives `Cauchy (sumRange (fun n => mul (abs (f 0)) (pow r n)))`; and
//!   `series.rs::sumRange_cauchy_of_dominated` combines the two directly into
//!   `Cauchy (sumRange f)` — its domination hypothesis is stated on `abs (f
//!   k)`, so no separate "absolute convergence ⟹ convergence" bridge
//!   (`sumRange_cauchy_of_abs_cauchy`) is needed here: that bridge is for a
//!   hypothesis already phrased as `Cauchy (sumRange (fun k => abs (f k)))`,
//!   and the ratio hypothesis is a termwise BOUND, not a pre-existing Cauchy
//!   fact about the absolute series.
//!
//! Neither declaration mentions `bigK`/`hK` (`geomYBound`'s leaf-bound
//! witness): [`CRealPrelude::geom_cauchy_of_lt`]'s own public signature is
//! `∀ x, le zero x → lt x one → ∀ k h, Cauchy (sumRange (pow x ·))` — it
//! already eliminates `geomYBound`'s outer existential INTERNALLY (see
//! `geometric.rs::declare_geom_cauchy_of_lt`), so a caller only ever supplies
//! `(x, hx0, hlt, k, h)`.

use super::convergence::{converges_applied, exists_elim};
use super::{CRealPrelude, clt, creal_ty};
use crate::Kernel;
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;

// --- small local term builders, verbatim in shape to every other `creal/*`
// module's own copies (see e.g. `geometric.rs`, `power.rs`, `cancellation.rs`) -

fn cadd(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.add, &[x, y])
}

fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul, &[x, y])
}

fn czero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
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

fn pos_bound_of(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, k: ExprId) -> ExprId {
    d.const_app(p.pos_bound, &[x, k])
}

/// `λ i, CReal.pow x i` — verbatim copy of `geometric.rs::pow_fn`/
/// `power.rs::pow_fn`, reproduced here so this file's own `sumRange`
/// applications land on the identical closure shape (alpha-equivalent, hence
/// defeq to what [`CRealPrelude::geom_cauchy_of_lt`]'s own stored type
/// mentions once `x` is substituted in).
fn pow_fn(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let body = cpow(d, p, x, i);
    let nat = d.nat_ty();
    d.lam_fv(i_fv, nat, body)
}

// ---------------------------------------------------------------------------
// `CReal.geomScaledCauchyOfLt` -- the scaled geometric bridge.
// ---------------------------------------------------------------------------

/// `CReal.geomScaledCauchyOfLt`. See the module documentation above for the
/// derivation: verbatim in *shape* to
/// `exponential.rs::declare_exp_dominant_cauchy`, generalized from the fixed
/// pair `(two, half)` to a symbolic scale `w` and a symbolic ratio `x` (with
/// [`CRealPrelude::geom_cauchy_of_lt`]'s own `(x, hx0, hlt, k, h)` signature
/// in place of that theorem's implicit base-`1/2` construction).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_geom_scaled_cauchy_of_lt(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let one_c = d.kernel().const_(p.one, vec![]);
    let zero_c = czero(d, p);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let hx0_ty = cle(d, p, zero_c, x);
    let hx0_fv = d.fresh_fvar();
    let hx0 = d.kernel().fvar(hx0_fv);
    let hlt_ty = clt(d, p, x, one_c);
    let hlt_fv = d.fresh_fvar();
    let hlt = d.kernel().fvar(hlt_fv);

    let neg_x = cneg(d, p, x);
    let a_real = cadd(d, p, one_c, neg_x); // a_real = 1 - x
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let h_ty = pos_bound_of(d, p, a_real, k);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);

    let f = pow_fn(d, p, x);
    let sum_f = d.const_app(p.sum_range, &[f]);
    let geom_cauchy_proof = d.lemma(p.geom_cauchy_of_lt, &[x, hx0, hlt, k, h]);
    // geom_cauchy_proof : Cauchy sum_f

    let ex_conv = d.lemma(p.converges_of_cauchy, &[sum_f, geom_cauchy_proof]);
    // ex_conv : Exists CReal (fun L => Converges sum_f L)

    let f_scaled = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fn_n = d.apply(f, &[n]);
        let prod = cmul(d, p, w, fn_n);
        d.lam_fv(n_fv, nat, prod)
    };
    let sum_f_scaled = d.const_app(p.sum_range, &[f_scaled]);
    let target = d.const_app(p.cauchy, &[sum_f_scaled]);

    let predicate_l = {
        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let body = converges_applied(d, p, sum_f, l);
        d.lam_fv(l_fv, carrier, body)
    };

    let minor = {
        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let hl_ty = converges_applied(d, p, sum_f, l);
        let hl_fv = d.fresh_fvar();
        let hl = d.kernel().fvar(hl_fv);

        let const_w_fn = {
            let ignore_fv = d.fresh_fvar();
            d.lam_fv(ignore_fv, nat, w)
        };
        let h_const = d.lemma(p.converges_of_const, &[w]);

        let h_prod = d.lemma(p.converges_mul, &[const_w_fn, sum_f, w, l, h_const, hl]);

        let fg = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let cn = d.apply(const_w_fn, &[n]);
            let sn = d.apply(sum_f, &[n]);
            let prod = cmul(d, p, cn, sn);
            d.lam_fv(n_fv, nat, prod)
        };
        let mul_w_l = cmul(d, p, w, l);

        let h_cauchy_g = d.lemma(p.converges_cauchy, &[fg, mul_w_l, h_prod]);

        let heq = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let body = d.lemma(p.mul_sum_range, &[w, f, n]);
            d.lam_fv(n_fv, nat, body)
        };

        let cauchy_f_proof = d.lemma(
            p.cauchy_of_pointwise_equiv,
            &[fg, sum_f_scaled, heq, h_cauchy_g],
        );

        let with_hl = d.lam_fv(hl_fv, hl_ty, cauchy_f_proof);
        d.lam_fv(l_fv, carrier, with_hl)
    };

    let proof_body = exists_elim(d, p, carrier, predicate_l, target, ex_conv, minor);

    let ty = {
        let with_w = d.pi_fv(w_fv, carrier, target);
        let with_h = d.pi_fv(h_fv, h_ty, with_w);
        let with_k = d.pi_fv(k_fv, nat, with_h);
        let after_hlt = d.arrow(hlt_ty, with_k);
        let after_hx0 = d.arrow(hx0_ty, after_hlt);
        d.pi_fv(x_fv, carrier, after_hx0)
    };
    let value = {
        let with_w = d.lam_fv(w_fv, carrier, proof_body);
        let with_h = d.lam_fv(h_fv, h_ty, with_w);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        let with_hlt = d.lam_fv(hlt_fv, hlt_ty, with_k);
        let with_hx0 = d.lam_fv(hx0_fv, hx0_ty, with_hlt);
        d.lam_fv(x_fv, carrier, with_hx0)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.ratio_test.geom_scaled_cauchy_of_lt,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// `CReal.sumRangeRatioTest` -- the ratio test itself.
// ---------------------------------------------------------------------------

/// `CReal.sumRangeRatioTest`. See the module documentation above for the
/// derivation: [`CRealPrelude::ratio_decay_bound`] applied to `g := fun n =>
/// abs (f n)`, [`declare_geom_scaled_cauchy_of_lt`]'s own theorem at `w := abs
/// (f 0)`, and `series.rs::sumRange_cauchy_of_dominated` compose directly —
/// no rewriting is needed beyond beta (`g (succ n)`/`g n` reduce to `abs (f
/// (succ n))`/`abs (f n)`, and `g 0` reduces to `abs (f 0)`), since the
/// kernel's argument checking is up to defeq.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_sum_range_ratio_test(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let one_c = d.kernel().const_(p.one, vec![]);
    let zero_c = czero(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let hx0_ty = cle(d, p, zero_c, r);
    let hx0_fv = d.fresh_fvar();
    let hx0 = d.kernel().fvar(hx0_fv);
    let hlt_ty = clt(d, p, r, one_c);
    let hlt_fv = d.fresh_fvar();
    let hlt = d.kernel().fvar(hlt_fv);

    let neg_r = cneg(d, p, r);
    let a_real = cadd(d, p, one_c, neg_r); // a_real = 1 - r
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let h_ty = pos_bound_of(d, p, a_real, k);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    // hdec_ty := ∀ n, le (abs (f (succ n))) (mul r (abs (f n)))
    let hdec_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let succ_n = d.succ(n);
        let f_succ_n = d.apply(f, &[succ_n]);
        let abs_f_succ_n = cabs(d, p, f_succ_n);
        let f_n = d.apply(f, &[n]);
        let abs_f_n = cabs(d, p, f_n);
        let r_absf_n = cmul(d, p, r, abs_f_n);
        let body = cle(d, p, abs_f_succ_n, r_absf_n);
        d.pi_fv(n_fv, nat, body)
    };
    let hdec_fv = d.fresh_fvar();
    let hdec = d.kernel().fvar(hdec_fv);

    // g := fun n => abs (f n)
    let g = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fn_n = d.apply(f, &[n]);
        let body = cabs(d, p, fn_n);
        d.lam_fv(n_fv, nat, body)
    };

    // bound : ∀ n, le (g n) (mul (g 0) (pow r n)), i.e. (up to beta)
    // ∀ n, le (abs (f n)) (mul (abs (f 0)) (pow r n)).
    let bound = d.lemma(p.ratio_decay_bound, &[g, r, hx0, hdec]);

    // w := abs (f 0)
    let zero_nat = d.num(0);
    let f0 = d.apply(f, &[zero_nat]);
    let w = cabs(d, p, f0);

    // cauchy_scaled : Cauchy (sumRange (fun n => mul w (pow r n)))
    let cauchy_scaled = d.lemma(
        p.ratio_test.geom_scaled_cauchy_of_lt,
        &[r, hx0, hlt, k, h, w],
    );

    // g_scaled := fun n => mul w (pow r n)
    let g_scaled = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let pow_rn = cpow(d, p, r, n);
        let prod = cmul(d, p, w, pow_rn);
        d.lam_fv(n_fv, nat, prod)
    };

    let result = d.lemma(
        p.sum_range_cauchy_of_dominated,
        &[f, g_scaled, bound, cauchy_scaled],
    );

    let sum_f = d.const_app(p.sum_range, &[f]);
    let target = d.const_app(p.cauchy, &[sum_f]);

    let ty = {
        let after_hdec = d.arrow(hdec_ty, target);
        let with_h = d.pi_fv(h_fv, h_ty, after_hdec);
        let with_k = d.pi_fv(k_fv, nat, with_h);
        let after_hlt = d.arrow(hlt_ty, with_k);
        let after_hx0 = d.arrow(hx0_ty, after_hlt);
        let with_r = d.pi_fv(r_fv, carrier, after_hx0);
        d.pi_fv(f_fv, fn_ty, with_r)
    };
    let value = {
        let with_hdec = d.lam_fv(hdec_fv, hdec_ty, result);
        let with_h = d.lam_fv(h_fv, h_ty, with_hdec);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        let with_hlt = d.lam_fv(hlt_fv, hlt_ty, with_k);
        let with_hx0 = d.lam_fv(hx0_fv, hx0_ty, with_hlt);
        let with_r = d.lam_fv(r_fv, carrier, with_hx0);
        d.lam_fv(f_fv, fn_ty, with_r)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.ratio_test.sum_range_ratio_test,
        uparams: vec![],
        ty,
        value,
    })
}

/// The kernel names `creal/ratio_test.rs` declares.
///
/// One of ADR-1512's per-module registries behind the [`CRealPrelude`]
/// facade: the field, its documentation and its interning all live
/// beside the `declare_*` that uses them, so a declaration added here
/// does not touch `creal.rs` at all.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RatioTestNames {
    /// `CReal.geomScaledCauchyOfLt : ∀ x, le zero x → lt x one → ∀ k (h :
    /// PosBound (add one (neg x)) k) (w : CReal), Cauchy (sumRange (fun n =>
    /// mul w (pow x n)))` — a CONSTANT
    /// times a geometric series stays Cauchy, at a GENERAL ratio `0 ≤ x < 1`
    /// and a general scale `w`. This is `creal/ratio_test.rs`'s "scaled
    /// geometric bridge", the piece Chapter 22–23's ratio test needs and
    /// [`super::CRealPrelude::geom_cauchy_of_lt`] alone does not supply: `sumRange (fun n =>
    /// mul w (pow x n))` is only `Equiv` to `mul w (sumRange (pow x ·) n)`
    /// (`CReal.mul_sumRange`, `series.rs`, already landed), not literally
    /// equal — `CReal.mul`'s own representative resamples its factors at a
    /// shifted index (`product.rs`), so the two sides are not the same
    /// rational at any index.
    ///
    /// Mirrors `exponential.rs::declare_exp_dominant_cauchy`'s own route
    /// verbatim, generalized from the fixed pair `(two, half)` to `(w, x)`
    /// and from [`super::CRealPrelude::geom_cauchy`] to [`super::CRealPrelude::geom_cauchy_of_lt`]:
    /// [`super::CRealPrelude::geom_cauchy_of_lt`] gives `Cauchy (sumRange (pow x ·))`;
    /// [`super::CRealPrelude::converges_of_cauchy`] lifts it to `Converges (sumRange (pow x
    /// ·)) L` for some `L` (eliminated immediately into the Prop goal, never
    /// into data); [`super::CRealPrelude::converges_of_const`]/[`super::CRealPrelude::converges_mul`] give
    /// `Converges (fun n => mul w (sumRange (pow x ·) n)) (mul w L)`;
    /// [`super::CRealPrelude::converges_cauchy`] turns that into `Cauchy (fun n => mul w
    /// (sumRange (pow x ·) n))`; and [`super::CRealPrelude::cauchy_of_pointwise_equiv`]
    /// transports it across `CReal.mul_sumRange`'s `Equiv` onto the stated
    /// conclusion. See `creal/ratio_test.rs::declare_geom_scaled_cauchy_of_lt`.
    pub geom_scaled_cauchy_of_lt: NameId,
    /// `CReal.sumRangeRatioTest : ∀ f r, le zero r → lt r one → ∀ k (h :
    /// PosBound (add one (neg r)) k) (hdec : ∀ n, le (abs (f (Nat.succ n)))
    /// (mul r (abs (f n)))), Cauchy (sumRange f)` — Spivak Chapter 22–23's
    /// ratio test: a sequence whose consecutive
    /// absolute terms shrink by a factor `r < 1` has a Cauchy (hence
    /// convergent) partial-sum sequence, even when `f` changes sign.
    ///
    /// Composes three already-landed general theorems, none of them redone
    /// here: [`super::CRealPrelude::ratio_decay_bound`] applied to `g := fun n => abs (f
    /// n)` gives `∀ n, le (abs (f n)) (mul (abs (f 0)) (pow r n))`;
    /// [`super::RatioTestNames::geom_scaled_cauchy_of_lt`] at `w := abs (f 0)` gives `Cauchy
    /// (sumRange (fun n => mul (abs (f 0)) (pow r n)))`; and
    /// `series.rs::sumRange_cauchy_of_dominated` combines the two directly
    /// into `Cauchy (sumRange f)` — its domination hypothesis is stated on
    /// `abs (f k)`, so no separate "absolute convergence ⟹ convergence"
    /// bridge (`sumRange_cauchy_of_abs_cauchy`) is needed: that bridge is for
    /// a hypothesis already phrased as `Cauchy (sumRange (fun k => abs (f
    /// k)))`, and the ratio hypothesis here is a termwise BOUND, not a
    /// pre-existing Cauchy fact about the absolute series. See
    /// `creal/ratio_test.rs::declare_sum_range_ratio_test`.
    pub sum_range_ratio_test: NameId,
}

impl RatioTestNames {
    /// Interns this module's names under the `CReal` root.
    ///
    /// Split out of `creal.rs`'s `intern_names` by ADR-1512: the kernel
    /// spelling of each name sits in the file that declares it.
    pub(super) fn intern(kernel: &mut Kernel, creal: NameId) -> Self {
        Self {
            geom_scaled_cauchy_of_lt: kernel.name_str(creal, "geomScaledCauchyOfLt"),
            sum_range_ratio_test: kernel.name_str(creal, "sumRangeRatioTest"),
        }
    }
}
