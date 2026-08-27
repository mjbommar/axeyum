//! **`CReal.cosFn : CReal → CReal`** — general cosine as a genuine function,
//! on the bounded domain `[0, 1]`, via the power series `Σ (-1)^k x^{2k} /
//! (2k)!`. This is the piece `creal/trig.rs`'s own module documentation
//! named as out of scope for `CReal.cosOne` (a single constant, `cos 1`):
//! the general function needed a bound depending on `|x|`, i.e. a power
//! series argument, which `creal/uniform_convergence.rs`'s
//! `weierstrassMTest`/`powerSeriesUniformConvergesOn` now supply.
//!
//! ## Route
//!
//! `CReal.cosFnTerm k x := mul (cosTerm k) (pow x (Nat.add k k))` — the same
//! `cosTerm` `creal/trig.rs::declare_cos_term` already built for `cosOne`,
//! now multiplied by `x^{2k}` instead of implicitly evaluated at `x := 1`.
//! Domain `[0, 1]` is deliberately the CHEAPEST choice available: for `0 ≤ x
//! ≤ 1`, `pow x (Nat.add k k) ≤ one` ([`CRealPrelude::pow_le_one`]) directly,
//! so the domination bound needs **no new domination series at all** — it is
//! `cosTermAbsLeDominant` (`creal/trig.rs`) composed with one
//! `abs_mul_le_of_bounds` step, exactly the sentence the task brief predicted.
//!
//! `CReal.weierstrassMTest` is applied directly (not through
//! `powerSeriesUniformConvergesOn`, whose own coefficient family sums over
//! *every* `Nat` index against `pow x j` — cosine's term is supported only on
//! even exponents, so it needs its own `f`, not a coefficient sequence fed to
//! `powerSeriesTerm`) at `f := cosFnTerm`, `mseq := expDominant`, `a :=
//! zero`, `b := one`. The M-test's own `(k, hcauchy)` parameter pair —
//! required as a **raw**, non-existential Cauchy witness, mirroring
//! `powerSeriesUniformConvergesOn`'s own contract exactly, per this task's
//! brief — is supplied by `exp_dominant_cauchy_body_concrete`
//! (`creal/trig.rs`, marked `pub(super)` for this file), the SAME concrete
//! witness `cosOne`'s own construction already uses for
//! `Cauchy (sumRange expDominant)`. No bridge is needed: that function's
//! return type is already `sum_range_cauchy_body(sumRange expDominant, k)`,
//! which is *exactly* `weierstrassMTest`'s `hcauchy` shape at `mseq :=
//! expDominant`.
//!
//! ## `CReal.cosFn`, and how it is obtained
//!
//! `UniformConvergesOn F G a b`'s own `G : CReal → CReal` is one of that
//! `Type`'s four PARAMETERS (see `creal/uniform_convergence.rs`'s module
//! documentation), built entirely INSIDE `weierstrassMTest`'s own proof from
//! its `f`/`mseq`/`a`/`b`/`hab`/`k`/`hdom`/`hcauchy` arguments — so applying
//! `weierstrassMTest` at cosine's concrete arguments and reading off
//! `Kernel::infer` of the result gives back a CLOSED term for `G`
//! specialized to cosine, without this file re-deriving any of that
//! construction's `pt_clamped`/`case_proof`/`speedup`/`CReal.mk` machinery by
//! hand. [`declare_cos_fn`] does exactly that: build the applied term, infer
//! its type (`UniformConvergesOn F G zero one`), decompose that application
//! spine with [`crate::expr::ExprNode::App`] to extract `G`, and declare
//! `CReal.cosFn := G` as its own `Definition`. `CReal.cosFnUniformConverges`
//! is then declared with the SAME applied term as its `value`, ascribed
//! against a `ty` that names `CReal.cosFn` (rather than `G` again) — the
//! kernel accepts it by δ-unfolding the freshly declared `cosFn` back to `G`,
//! exactly the way `CReal.powerSeriesTerm_abs_le` ascribes its conclusion
//! through the named `CReal.powerSeriesTerm` while its own proof works with
//! the raw `mul`/`pow` term underneath.
//!
//! ## What is NOT built here
//!
//! - **`cosFn 1 ≡ cosOne`.** This needs turning `cosFn`'s own
//!   `UniformConvergesOn`/`close_within` evidence at `x := one` into a raw
//!   `Converges` witness comparable (via `CReal.converges_unique`) against
//!   `cosOneConverges`. That bridge — `close_within` back to the sample-level
//!   `Within` `Converges` needs — does not exist as a public lemma today:
//!   `converges_of_scaled_cauchy`'s own version of this step is buried inside
//!   that theorem's private proof, and the one PUBLIC lemma of this shape,
//!   `within_of_two_sided_le`, runs the *opposite* direction (`Within` to
//!   `close_within`, the direction [`super::uniform_convergence`]'s own
//!   `close_within_of_within` already needed). Building it is a real,
//!   separately-sized proof, not attempted in this file — see this module's
//!   own status note for the exact shape needed.
//! - **`sinFn`**, by the identical route with `sinTerm` — mechanically
//!   parallel to `cosFn` once `cosFn` itself was the open question; not
//!   attempted in the time this slice had.
//! - **Any approximate root of `cosFn`.** Nothing here changes `creal/ivt.rs`'s
//!   refutation of exact-root construction; an *approximate* π via
//!   `ivt_approx`/`ivt_bisect` would additionally need `cosFn`'s own
//!   uniform continuity (from `uniform_limit_uniformly_continuous`, which
//!   itself needs each partial sum `UniformlyContinuousOn` on `[0,1]` — a
//!   finite-sum induction over already-public `uniformly_continuous_add`/
//!   `_mul`/`_const`/`_id`, not attempted here) and a sign change witness,
//!   neither built in this slice.

use super::trig::{
    cabs, cadd, cle, cmul, cneg, cpow, czero, exp_dominant_cauchy_body_concrete, one_c,
};
use super::{CRealPrelude, DERIVED_HEIGHT, creal_ty, equiv};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::{ExprId, ExprNode};
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Height for `cosFnTerm`: one past `powerSeriesTerm`'s own
/// `DERIVED_HEIGHT + 43` (`creal/power.rs`), matching this development's
/// convention of giving a thin wrapper a height just past what it unfolds
/// to.
const COS_FN_TERM_HEIGHT: u16 = DERIVED_HEIGHT + 44;

/// Peel one `App` node off `e`, returning `(function, argument)`.
///
/// Used only to decompose the INFERRED type of a `weierstrassMTest`
/// application, whose shape (`UniformConvergesOn F G a b`, a 4-ary
/// application) this file controls completely by construction — this is not
/// parsing untrusted input, it is reading back a term this same function
/// just built. Panics if `e` is not an application, which would mean
/// `weierstrassMTest`'s own conclusion shape changed underneath this file.
fn unapp(d: &mut IntDev<'_>, e: ExprId) -> (ExprId, ExprId) {
    match d.kernel().expr_node(e).clone() {
        ExprNode::App(f, a) => (f, a),
        other => panic!("expected an application (UniformConvergesOn F G a b), found {other:?}"),
    }
}

/// `CReal.cosFnTerm : Nat → CReal → CReal := fun k x => mul (cosTerm k) (pow
/// x (Nat.add k k))`. See the module documentation for the route.
fn declare_cos_fn_term(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let cos_term_c = d.kernel().const_(p.cos_term, vec![]);
    let cos_term_k = d.apply(cos_term_c, &[k]);
    let two_k = d.add(k, k);
    let pow_x_2k = cpow(d, p, x, two_k);
    let body = cmul(d, p, cos_term_k, pow_x_2k);

    let value = {
        let with_x = d.lam_fv(x_fv, carrier, body);
        d.lam_fv(k_fv, nat, with_x)
    };
    let ty = {
        let with_x = d.arrow(carrier, carrier);
        d.arrow(nat, with_x)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.cos_fn_term,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(COS_FN_TERM_HEIGHT),
    })
}

/// `CReal.cosFnTerm_congr : ∀ k x y, Equiv x y → Equiv (cosFnTerm k x)
/// (cosFnTerm k y)` — `CReal.mulPowCongr` applied at the constant coefficient
/// function `fun _ => cosTerm k` and exponent `Nat.add k k`. No new
/// congruence argument: `mulPowCongr`'s own statement is `∀ c j x y, Equiv x
/// y → Equiv (mul (c j) (pow x j)) (mul (c j) (pow y j))`, universally
/// quantified over `j`, so instantiating `j := Nat.add k k` and `c := fun _
/// => cosTerm k` (so `c j` beta-reduces to `cosTerm k`) gives exactly this
/// statement up to β/δ.
fn declare_cos_fn_term_congr(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let heq_ty = equiv(d, p, x, y);
    let heq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(heq_fv);

    let cos_term_c = d.kernel().const_(p.cos_term, vec![]);
    let cos_term_k = d.apply(cos_term_c, &[k]);
    let dummy_fv = d.fresh_fvar();
    let const_fn = d.lam_fv(dummy_fv, nat, cos_term_k);
    let two_k = d.add(k, k);

    let proof = d.lemma(p.mul_pow_congr, &[const_fn, two_k, x, y, heq]);

    let value = {
        let with_heq = d.lam_fv(heq_fv, heq_ty, proof);
        let with_y = d.lam_fv(y_fv, carrier, with_heq);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(k_fv, nat, with_x)
    };
    let ty = {
        let cft_k_x = d.const_app(p.cos_fn_term, &[k, x]);
        let cft_k_y = d.const_app(p.cos_fn_term, &[k, y]);
        let concl = equiv(d, p, cft_k_x, cft_k_y);
        let with_heq = d.arrow(heq_ty, concl);
        let with_y = d.pi_fv(y_fv, carrier, with_heq);
        let with_x = d.pi_fv(x_fv, carrier, with_y);
        d.pi_fv(k_fv, nat, with_x)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_fn_term_congr,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Equiv (neg zero) zero`, reproduced from `creal/power.rs::neg_zero_equiv`
/// (private there) — see this development's established convention
/// (`creal/trig.rs::neg_zero_equiv_local`) of reproducing a sibling module's
/// private helper rather than widening its visibility.
fn neg_zero_equiv_here(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let zero_c = czero(d, p);
    let nz = cneg(d, p, zero_c);
    let padded = cadd(d, p, nz, zero_c);
    let h1 = d.lemma(p.add_zero, &[nz]); // Equiv padded nz
    let step1 = d.lemma(p.equiv_symm, &[padded, nz, h1]); // Equiv nz padded
    let h2 = d.lemma(p.add_comm, &[nz, zero_c]); // Equiv padded (add zero nz)
    let flipped = cadd(d, p, zero_c, nz);
    let h3 = d.lemma(p.add_neg, &[zero_c]); // Equiv flipped zero
    let step2 = d.lemma(p.equiv_trans, &[nz, padded, flipped, step1, h2]);
    d.lemma(p.equiv_trans, &[nz, flipped, zero_c, step2, h3])
}

/// `le zero one`, from `zero_lt_one` + `le_of_lt` — the same two-step route
/// `creal/power.rs::declare_pow_nonneg`'s base case already uses.
fn zero_le_one(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let zero_c = czero(d, p);
    let one_cc = one_c(d, p);
    let lt_witness = d.lemma(p.zero_lt_one, &[]);
    d.lemma(p.le_of_lt, &[zero_c, one_cc, lt_witness])
}

/// `CReal.cosFnTermAbsLe : ∀ x, le zero x → le x one → ∀ k, le (abs
/// (cosFnTerm k x)) (expDominant k)`. See the module documentation: no new
/// domination series, `pow_le_one` + `abs_mul_le_of_bounds` +
/// `cosTermAbsLeDominant` via `le_trans`.
fn declare_cos_fn_term_abs_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let zero_c = czero(d, p);
    let one_cc = one_c(d, p);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let hax_ty = cle(d, p, zero_c, x);
    let hax_fv = d.fresh_fvar();
    let hax = d.kernel().fvar(hax_fv);
    let hxb_ty = cle(d, p, x, one_cc);
    let hxb_fv = d.fresh_fvar();
    let hxb = d.kernel().fvar(hxb_fv);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let two_k = d.add(k, k);
    let pow_x_2k = cpow(d, p, x, two_k);

    // pow_x_2k <= one, zero <= pow_x_2k
    let h_le_one = d.lemma(p.pow_le_one, &[x, hax, hxb, two_k]);
    let h_nonneg = d.lemma(p.pow_nonneg, &[x, hax, two_k]);

    // neg pow_x_2k <= one, via neg pow_x_2k <= neg zero ~ zero <= one.
    let neg_pow = cneg(d, p, pow_x_2k);
    let neg_zero = cneg(d, p, zero_c);
    let step1 = d.lemma(p.neg_le_neg, &[zero_c, pow_x_2k, h_nonneg]); // le neg_pow neg_zero
    let nz_eq = neg_zero_equiv_here(d, p); // Equiv neg_zero zero_c
    let refl_neg_pow = d.lemma(p.equiv_refl, &[neg_pow]);
    let neg_pow_le_zero = d.lemma(
        p.le_congr,
        &[
            neg_pow,
            neg_pow,
            neg_zero,
            zero_c,
            refl_neg_pow,
            nz_eq,
            step1,
        ],
    );
    let zlo = zero_le_one(d, p);
    let neg_pow_le_one = d.lemma(p.le_trans, &[neg_pow, zero_c, one_cc, neg_pow_le_zero, zlo]);

    let abs_pow_le_one = d.lemma(p.abs_le, &[pow_x_2k, one_cc, h_le_one, neg_pow_le_one]);

    // abs (mul (cosTerm k) pow_x_2k) <= mul (abs (cosTerm k)) one.
    let cos_term_c = d.kernel().const_(p.cos_term, vec![]);
    let cos_term_k = d.apply(cos_term_c, &[k]);
    let abs_cos_term_k = cabs(d, p, cos_term_k);
    let le_refl_abs = d.lemma(p.le_refl, &[abs_cos_term_k]);
    let mul_bound = d.lemma(
        p.abs_mul_le_of_bounds,
        &[
            cos_term_k,
            pow_x_2k,
            abs_cos_term_k,
            one_cc,
            le_refl_abs,
            abs_pow_le_one,
        ],
    );

    // fold mul (abs (cosTerm k)) one ~ abs (cosTerm k) via mul_one, then
    // chain to expDominant k via cosTermAbsLeDominant.
    let mul_one_eq = d.lemma(p.mul_one, &[abs_cos_term_k]); // Equiv (mul abs_cos_term_k one) abs_cos_term_k
    let mul_term = cmul(d, p, cos_term_k, pow_x_2k);
    let lhs_abs = cabs(d, p, mul_term);
    let refl_lhs = d.lemma(p.equiv_refl, &[lhs_abs]);
    let abs_mul_one = cmul(d, p, abs_cos_term_k, one_cc);
    let mul_bound2 = d.lemma(
        p.le_congr,
        &[
            lhs_abs,
            lhs_abs,
            abs_mul_one,
            abs_cos_term_k,
            refl_lhs,
            mul_one_eq,
            mul_bound,
        ],
    );

    let dominant_k = {
        let ed = d.kernel().const_(p.exp_dominant, vec![]);
        d.apply(ed, &[k])
    };
    let cos_dom = d.lemma(p.cos_term_abs_le_dominant, &[k]);
    let final_proof = d.lemma(
        p.le_trans,
        &[lhs_abs, abs_cos_term_k, dominant_k, mul_bound2, cos_dom],
    );

    let value = {
        let with_k = d.lam_fv(k_fv, nat, final_proof);
        let with_hxb = d.lam_fv(hxb_fv, hxb_ty, with_k);
        let with_hax = d.lam_fv(hax_fv, hax_ty, with_hxb);
        d.lam_fv(x_fv, carrier, with_hax)
    };
    let ty = {
        let cft_k_x = d.const_app(p.cos_fn_term, &[k, x]);
        let abs_cft = cabs(d, p, cft_k_x);
        let concl = cle(d, p, abs_cft, dominant_k);
        let with_k = d.pi_fv(k_fv, nat, concl);
        let with_hxb = d.arrow(hxb_ty, with_k);
        let with_hax = d.arrow(hax_ty, with_hxb);
        d.pi_fv(x_fv, carrier, with_hax)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_fn_term_abs_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit `CReal.cosFn` and `CReal.cosFnUniformConverges`. Run after
/// `declare_cos_fn_term`/`declare_cos_fn_term_congr`/`declare_cos_fn_term_abs_le`
/// (this file), `trig::declare_trig` (`cosTerm`, `cosTermAbsLeDominant`),
/// `exponential::declare_e_family` (`expDominant`), and
/// `uniform_convergence::declare_weierstrass_m_test`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_cos_fn(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let zero_c = czero(d, p);
    let one_cc = one_c(d, p);

    let f0 = d.kernel().const_(p.cos_fn_term, vec![]);
    let mseq0 = d.kernel().const_(p.exp_dominant, vec![]);

    let hab0 = zero_le_one(d, p);

    // hcong0 : forall j p q, Equiv p q -> Equiv (f0 j p) (f0 j q), built
    // pointwise from `cosFnTerm_congr`.
    let hcong0 = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let pp_fv = d.fresh_fvar();
        let pp = d.kernel().fvar(pp_fv);
        let qq_fv = d.fresh_fvar();
        let qq = d.kernel().fvar(qq_fv);
        let heq_ty = equiv(d, p, pp, qq);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let body = d.lemma(p.cos_fn_term_congr, &[j, pp, qq, heq]);
        let with_heq = d.lam_fv(heq_fv, heq_ty, body);
        let with_qq = d.lam_fv(qq_fv, carrier, with_heq);
        let with_pp = d.lam_fv(pp_fv, carrier, with_qq);
        d.lam_fv(j_fv, nat, with_pp)
    };

    // (k_g, hcauchy0) : the SAME concrete witness `cosOne` itself uses for
    // `Cauchy (sumRange expDominant)` -- already exactly `weierstrassMTest`'s
    // own `hcauchy` shape, no bridge needed.
    let (k_g, hcauchy0) = exp_dominant_cauchy_body_concrete(d, p);

    // hdom0 : forall j pt, le zero pt -> le pt one -> le (abs (f0 j pt)) (mseq0 j).
    let hdom0 = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let pt_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(pt_fv);
        let hax_fv = d.fresh_fvar();
        let hax = d.kernel().fvar(hax_fv);
        let hxb_fv = d.fresh_fvar();
        let hxb = d.kernel().fvar(hxb_fv);
        let body = d.lemma(p.cos_fn_term_abs_le, &[pt, hax, hxb, j]);
        let hax_ty = cle(d, p, zero_c, pt);
        let hxb_ty = cle(d, p, pt, one_cc);
        let with_hxb = d.lam_fv(hxb_fv, hxb_ty, body);
        let with_hax = d.lam_fv(hax_fv, hax_ty, with_hxb);
        let with_pt = d.lam_fv(pt_fv, carrier, with_hax);
        d.lam_fv(j_fv, nat, with_pt)
    };

    let u0 = d.lemma(
        p.weierstrass_m_test,
        &[
            f0, mseq0, zero_c, one_cc, hab0, hcong0, k_g, hdom0, hcauchy0,
        ],
    );
    let ty0 = d.kernel().infer(u0)?;

    // ty0 : UniformConvergesOn F0 G0 zero one -- peel `b`, `a`, then `G0`.
    let (inner1, _b0) = unapp(d, ty0);
    let (inner2, _a0) = unapp(d, inner1);
    let (_inner3, g0) = unapp(d, inner2);

    let cos_fn_ty = d.arrow(carrier, carrier);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.cos_fn,
        uparams: vec![],
        ty: cos_fn_ty,
        value: g0,
        hint: ReducibilityHint::Regular(COS_FN_TERM_HEIGHT + 1),
    })?;

    // Big_f, restated so the ascribed `ty` reads with the same `F` this
    // theorem's own statement will show a caller.
    let big_f = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let pt_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(pt_fv);
        let f_pt = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let body = d.const_app(p.cos_fn_term, &[j, pt]);
            d.lam_fv(j_fv, nat, body)
        };
        let body = d.const_app(p.sum_range, &[f_pt, n]);
        let with_pt = d.lam_fv(pt_fv, carrier, body);
        d.lam_fv(n_fv, nat, with_pt)
    };
    let cos_fn_c = d.kernel().const_(p.cos_fn, vec![]);
    let ty = d.const_app(p.uniform_converges_on, &[big_f, cos_fn_c, zero_c, one_cc]);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_fn_uniform_converges,
        uparams: vec![],
        ty,
        value: u0,
    })
}

pub(super) fn declare_cos_fn_family(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_cos_fn_term(d, p)?;
    declare_cos_fn_term_congr(d, p)?;
    declare_cos_fn_term_abs_le(d, p)?;
    declare_cos_fn(d, p)
}
