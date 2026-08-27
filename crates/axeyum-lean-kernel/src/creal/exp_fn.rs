//! **`CReal.expFn : CReal → CReal`** — general exponential as a genuine
//! function, on the bounded domain `[0, 1]`, via the power series `Σ x^k /
//! k!`. Mirrors `creal/trig_fn.rs::declare_cos_fn` (Spivak's `cosFn`
//! construction, landed the same session), but is SIMPLER: `CReal.expTerm`'s
//! coefficients (`creal/exponential.rs`) are supported on EVERY `Nat` index,
//! unlike cosine's even-only support, so this file needs no per-file
//! `expFnTerm`/`expFnTerm_congr` pair at all — `CReal.powerSeriesTerm` /
//! `CReal.powerSeriesTerm_congr` (`creal/power.rs`, already fully generic)
//! apply directly at `c := expTerm`.
//!
//! ## Route
//!
//! `CReal.weierstrassMTest` is applied directly (not through
//! `CReal.powerSeriesUniformConvergesOn`, `creal/uniform_convergence.rs`)
//! because that theorem's own domination series is `mseq j := mul M (pow r
//! j)` for a domain endpoint `r` — a bound that only converges for `r < 1`
//! strictly, since `r = 1` collapses it to the divergent constant series `M,
//! M, M, …`. Reaching `x = 1` (needed for the `expFn 1 ≡ CReal.e` bridge,
//! see below) needs the SAME smarter, `x`-independent domination series
//! `cosFn` already uses: `CReal.expDominant` itself, which converges by its
//! own construction regardless of `x`, because `pow x k ≤ one` for `0 ≤ x ≤
//! 1` bounds the `x`-dependent factor by a CONSTANT rather than requiring
//! geometric decay in `x`.
//!
//! At `f := powerSeriesTerm expTerm`, `mseq := expDominant`, `a := zero`, `b
//! := one`: `hcong := powerSeriesTerm_congr expTerm` (a direct partial
//! application, exactly `creal/uniform_convergence.rs`'s own
//! `declare_power_series_uniform_converges` builds its `hcong`), `hdom` from
//! [`declare_exp_fn_term_abs_le`] (below — the domination bound, built by the
//! SAME `pow_le_one` + `abs_mul_le_of_bounds` + `mul_one` route
//! `cosFnTermAbsLe` uses, closing via [`CRealPrelude::exp_term_abs_le_dominant`]
//! rather than `cos_term_abs_le_dominant`), and `(k, hcauchy)` from
//! `exp_dominant_cauchy_body_concrete` (`creal/trig.rs`, `pub(super)`) — the
//! SAME concrete witness `CReal.e` and `cosOne` already use for `Cauchy
//! (sumRange expDominant)`. No bridge needed, exactly as in `cosFn`'s own
//! construction.
//!
//! `CReal.expFn` and `CReal.expFnUniformConverges` are then obtained by
//! reading off `Kernel::infer` of the applied `weierstrassMTest` term and
//! decomposing its application spine, identically to
//! [`super::trig_fn::declare_cos_fn`].
//!
//! ## What is NOT built here
//!
//! - **`expFn 1 ≡ CReal.e`.** Investigated in full. The "reverse `Within`
//!   bridge" `creal/trig_fn.rs`'s own module documentation names as missing
//!   for `cosFn 1 ≡ cosOne` is **NOT** the actual obstacle here — that
//!   documentation is stale (see `CLAUDE.md`'s "hiding place" retrospective,
//!   2026-08-27 correction): `CReal.close_within_of_within`
//!   (`creal/uniform_convergence.rs`) already bridges `Within` (the raw
//!   sample-level Cauchy shape `CReal.e_converges`/`CReal.Converges` use) to
//!   `close_within` (the CReal-level `le`/`abs` shape
//!   `UniformConvergesOn.spec` produces) — the FORWARD direction, and it is
//!   exactly the direction this bridge needs: apply it, per `n`, to
//!   `e_converges`'s `Exists`-eliminated witness to get `close_within
//!   (expSeriesPartial n) e K₁` for every `n`, transport
//!   `expFnUniformConverges`'s own `spec` at `x := one` along `powerSeriesTerm
//!   expTerm j one ≡ expTerm j` (`mul_one` + `pow one j ≡ one`) to get
//!   `close_within (expSeriesPartial n) (expFn one) K₂` for every `n`, and
//!   combine the two via the triangle inequality (`abs_add_le` twice) into a
//!   single `∀ n, le (abs (add e (neg (expFn one)))) (ofRat (natDivSucc K₃
//!   n))` for a FUSED constant `K₃` (`Rat.natDivSucc_add`, since both
//!   `close_within` facts already share the SAME sample index `n` — no
//!   arbitrary third index needed).
//!
//!   **The actual missing piece is downstream of all of that**: turning this
//!   `∀ n, le (abs v) (ofRat (natDivSucc K₃ n))` (`v` a FIXED `CReal`,
//!   independent of `n`) into `Equiv v zero` needs
//!   `CReal.equiv_zero_of_small` (`creal/archimedean_squeeze.rs`) — but that
//!   lemma, and the `CReal.le_of_forall_le_add_small` bridge underneath it,
//!   are both hard-coded to accuracy rate **exactly 1**
//!   (`∀ e, le (abs v) (ofRat (natDivSucc 1 e))`), not a free `K`. The
//!   underlying Archimedean-property lemma they bottom out in
//!   (`Rat.le_of_le_add_natDivSucc`) IS already general in its constant (the
//!   `5` in `le_of_forall_le_add_small`'s own proof is one particular
//!   instantiation, not a structural limit) — but generalizing the WRAPPER
//!   to a free `K₃` means re-deriving essentially the whole ~150-line
//!   telescoping argument in `archimedean_squeeze.rs` (regrouping five
//!   `natDivSucc` terms via `Rat.natDivSucc_add`/`nat_div_succ_halve`), since
//!   every one of ITS internal `1`s (not just the exposed hypothesis's) would
//!   need to become `K₃`-scaled, and its helper `half_shift_le` is private
//!   (this development's convention is to reproduce a sibling's private
//!   helper rather than widen its visibility, which would make this a
//!   genuinely new, separately-sized proof rather than an application of an
//!   existing one). This is a real, honestly-sized piece of new machinery —
//!   a general-`K` Archimedean squeeze — not attempted in this slice. It
//!   would benefit `Equiv`-from-bounded-difference arguments generally, not
//!   just this bridge, and is a reasonable next increment.
//! - **Unbounded `expFn`.** Same reason `cosFn` stays on `[0, 1]`: the
//!   domination series `expDominant` bounds `pow x k` by the CONSTANT `one`,
//!   valid only for `0 ≤ x ≤ 1`. Past `x = 1`, `pow x k` grows without bound
//!   in `k` (for `x > 1`) and the exact same `expDominant` comparison fails —
//!   a genuinely unbounded exponential needs either a per-interval `expFn`
//!   family glued at `1` (paying the `expFn 1 ≡ CReal.e` bridge above to line
//!   up scales) or the functional equation `exp(x+y) = exp(x)·exp(y)` proved
//!   independently, neither attempted here.
//! - **`sinFn`.** Mechanically parallel to `expFn`/`cosFn` once the pattern
//!   is fixed (in fact simpler still: `sinTerm`'s own domination bound
//!   already exists as `CReal.sin_term_abs_le_dominant`, `creal/trig.rs`);
//!   not attempted in the time this slice had.

use super::trig::{
    cabs, cadd, cle, cmul, cneg, cpow, czero, exp_dominant_cauchy_body_concrete, one_c,
};
use super::{CRealPrelude, DERIVED_HEIGHT, creal_ty};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::{ExprId, ExprNode};
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Height for `CReal.expFn`: one past `CReal.powerSeriesTerm`'s own
/// `DERIVED_HEIGHT + 43` (`creal/power.rs`) — matching `cosFnTerm`'s own
/// height, since `expFn` plays the same "thin wrapper one step past its
/// own machinery" role `cosFnTerm` did, without a separate `_term`
/// definition of its own.
const EXP_FN_HEIGHT: u16 = DERIVED_HEIGHT + 44;

/// Peel one `App` node off `e`, returning `(function, argument)`. Reproduced
/// from `creal/trig_fn.rs`'s own private `unapp` (Rust privacy: sibling
/// modules) — used only to decompose the INFERRED type of a
/// `weierstrassMTest` application, whose shape (`UniformConvergesOn F G a
/// b`, a 4-ary application) this file controls completely by construction.
/// Panics if `e` is not an application, which would mean `weierstrassMTest`'s
/// own conclusion shape changed underneath this file.
fn unapp(d: &mut IntDev<'_>, e: ExprId) -> (ExprId, ExprId) {
    match d.kernel().expr_node(e).clone() {
        ExprNode::App(f, a) => (f, a),
        other => panic!("expected an application (UniformConvergesOn F G a b), found {other:?}"),
    }
}

/// `Equiv (neg zero) zero`, reproduced from `creal/power.rs::neg_zero_equiv`
/// (private there) — this development's established convention (many
/// `creal/*` modules each keep their own tiny private copy rather than widen
/// visibility; see e.g. `creal/trig_fn.rs::neg_zero_equiv_here`).
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
/// `creal/trig_fn.rs::zero_le_one` (private there) already uses.
fn zero_le_one(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let zero_c = czero(d, p);
    let one_cc = one_c(d, p);
    let lt_witness = d.lemma(p.zero_lt_one, &[]);
    d.lemma(p.le_of_lt, &[zero_c, one_cc, lt_witness])
}

/// `CReal.expFnTermAbsLe : ∀ x, le zero x → le x one → ∀ k, le (abs
/// (powerSeriesTerm expTerm k x)) (expDominant k)`. See the module
/// documentation for the route: no new domination series, `pow_le_one` +
/// `abs_mul_le_of_bounds` + `exp_term_abs_le_dominant` via `le_trans` —
/// identical in shape to `trig_fn.rs::declare_cos_fn_term_abs_le`, but
/// against the raw exponent `k` (every index) rather than `Nat.add k k`
/// (even indices only), and closing directly against
/// `exp_term_abs_le_dominant` rather than needing a separate
/// `cos_term_abs_le_dominant` step.
fn declare_exp_fn_term_abs_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
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
    let pow_x_k = cpow(d, p, x, k);

    // pow_x_k <= one, zero <= pow_x_k
    let h_le_one = d.lemma(p.pow_le_one, &[x, hax, hxb, k]);
    let h_nonneg = d.lemma(p.pow_nonneg, &[x, hax, k]);

    // neg pow_x_k <= one, via neg pow_x_k <= neg zero ~ zero <= one.
    let neg_pow = cneg(d, p, pow_x_k);
    let neg_zero = cneg(d, p, zero_c);
    let step1 = d.lemma(p.neg_le_neg, &[zero_c, pow_x_k, h_nonneg]); // le neg_pow neg_zero
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

    let abs_pow_le_one = d.lemma(p.abs_le, &[pow_x_k, one_cc, h_le_one, neg_pow_le_one]);

    // abs (mul (expTerm k) pow_x_k) <= mul (abs (expTerm k)) one.
    let exp_term_c = d.kernel().const_(p.exp_term, vec![]);
    let exp_term_k = d.apply(exp_term_c, &[k]);
    let abs_exp_term_k = cabs(d, p, exp_term_k);
    let le_refl_abs = d.lemma(p.le_refl, &[abs_exp_term_k]);
    let mul_bound = d.lemma(
        p.abs_mul_le_of_bounds,
        &[
            exp_term_k,
            pow_x_k,
            abs_exp_term_k,
            one_cc,
            le_refl_abs,
            abs_pow_le_one,
        ],
    );

    // fold mul (abs (expTerm k)) one ~ abs (expTerm k) via mul_one, then
    // chain to expDominant k via exp_term_abs_le_dominant.
    let mul_one_eq = d.lemma(p.mul_one, &[abs_exp_term_k]); // Equiv (mul abs_exp_term_k one) abs_exp_term_k
    let mul_term = cmul(d, p, exp_term_k, pow_x_k);
    let lhs_abs = cabs(d, p, mul_term);
    let refl_lhs = d.lemma(p.equiv_refl, &[lhs_abs]);
    let abs_mul_one = cmul(d, p, abs_exp_term_k, one_cc);
    let mul_bound2 = d.lemma(
        p.le_congr,
        &[
            lhs_abs,
            lhs_abs,
            abs_mul_one,
            abs_exp_term_k,
            refl_lhs,
            mul_one_eq,
            mul_bound,
        ],
    );

    let dominant_k = {
        let ed = d.kernel().const_(p.exp_dominant, vec![]);
        d.apply(ed, &[k])
    };
    let exp_dom = d.lemma(p.exp_term_abs_le_dominant, &[k]);
    let final_proof = d.lemma(
        p.le_trans,
        &[lhs_abs, abs_exp_term_k, dominant_k, mul_bound2, exp_dom],
    );

    let value = {
        let with_k = d.lam_fv(k_fv, nat, final_proof);
        let with_hxb = d.lam_fv(hxb_fv, hxb_ty, with_k);
        let with_hax = d.lam_fv(hax_fv, hax_ty, with_hxb);
        d.lam_fv(x_fv, carrier, with_hax)
    };
    let ty = {
        let pst_k_x = d.const_app(p.power_series_term, &[exp_term_c, k, x]);
        let abs_pst = cabs(d, p, pst_k_x);
        let concl = cle(d, p, abs_pst, dominant_k);
        let with_k = d.pi_fv(k_fv, nat, concl);
        let with_hxb = d.arrow(hxb_ty, with_k);
        let with_hax = d.arrow(hax_ty, with_hxb);
        d.pi_fv(x_fv, carrier, with_hax)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.exp_fn_term_abs_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit `CReal.expFn` and `CReal.expFnUniformConverges`. Run after
/// `declare_exp_fn_term_abs_le` (this file), `exponential::declare_e_family`
/// (`expTerm`, `expDominant`, `exp_term_abs_le_dominant`),
/// `power::declare_power_series_term`/`declare_power_series_term_congr`, and
/// `uniform_convergence::declare_weierstrass_m_test`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_exp_fn(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let zero_c = czero(d, p);
    let one_cc = one_c(d, p);

    let exp_term_c = d.kernel().const_(p.exp_term, vec![]);
    // f0 : Nat -> CReal -> CReal := powerSeriesTerm expTerm -- a direct
    // partial application, no per-file wrapper needed.
    let f0 = d.const_app(p.power_series_term, &[exp_term_c]);
    let mseq0 = d.kernel().const_(p.exp_dominant, vec![]);

    let hab0 = zero_le_one(d, p);

    // hcong0 : forall j p q, Equiv p q -> Equiv (f0 j p) (f0 j q) -- the
    // SAME partial-application idiom
    // `uniform_convergence::declare_power_series_uniform_converges` already
    // uses successfully for its own `hcong`.
    let hcong0 = d.const_app(p.power_series_term_congr, &[exp_term_c]);

    // (k_g, hcauchy0) : the SAME concrete witness `CReal.e`/`cosOne` already
    // use for `Cauchy (sumRange expDominant)` -- exactly
    // `weierstrassMTest`'s own `hcauchy` shape, no bridge needed.
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
        let body = d.lemma(p.exp_fn_term_abs_le, &[pt, hax, hxb, j]);
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

    let exp_fn_ty = d.arrow(carrier, carrier);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.exp_fn,
        uparams: vec![],
        ty: exp_fn_ty,
        value: g0,
        hint: ReducibilityHint::Regular(EXP_FN_HEIGHT),
    })?;

    // Big_F, restated so the ascribed `ty` reads with the same `F` this
    // theorem's own statement will show a caller.
    let big_f = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let pt_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(pt_fv);
        let f_pt = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let body = d.const_app(p.power_series_term, &[exp_term_c, j, pt]);
            d.lam_fv(j_fv, nat, body)
        };
        let body = d.const_app(p.sum_range, &[f_pt, n]);
        let with_pt = d.lam_fv(pt_fv, carrier, body);
        d.lam_fv(n_fv, nat, with_pt)
    };
    let exp_fn_c = d.kernel().const_(p.exp_fn, vec![]);
    let ty = d.const_app(p.uniform_converges_on, &[big_f, exp_fn_c, zero_c, one_cc]);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.exp_fn_uniform_converges,
        uparams: vec![],
        ty,
        value: u0,
    })
}

pub(super) fn declare_exp_fn_family(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_exp_fn_term_abs_le(d, p)?;
    declare_exp_fn(d, p)
}
