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
//! ## `expFn 1 ≡ CReal.e` — landed
//!
//! `CReal.expFn_one_equiv_e : Equiv (expFn one) e`, below. Two corrections to
//! earlier diagnoses of this bridge, both confirmed by the kernel:
//!
//! - The "reverse `Within` bridge" `creal/trig_fn.rs`'s own module
//!   documentation once named as missing for `cosFn 1 ≡ cosOne` was never the
//!   obstacle here (2026-08-27 correction, `CLAUDE.md`'s "hiding place"
//!   retrospective): `CReal.close_within_of_within`
//!   (`creal/uniform_convergence.rs`, via its `close_within_of_within_at`
//!   builder) already bridges `Within` (the raw sample-level Cauchy shape
//!   `CReal.e_converges`/`CReal.Converges` use) to `close_within` (the
//!   CReal-level `le`/`abs` shape `UniformConvergesOn.spec` produces) — the
//!   FORWARD direction, and exactly the one this bridge needs.
//! - The blocker THIS file's own module doc previously named — that
//!   `CReal.equiv_zero_of_small` was hard-coded to accuracy rate **exactly
//!   1** and would need "re-deriving essentially the whole ~150-line
//!   telescoping argument" to generalize — is now stale: `equiv_zero_of_rate`
//!   (`creal/archimedean_squeeze.rs`) already generalizes it to a free rate
//!   `K`, with `equiv_zero_of_small` demoted to that theorem's own `K := 1`
//!   instance. No new Archimedean machinery was needed.
//!
//! The route: eliminate `e_converges`'s `Exists`-wrapped `Within` witness
//! (`Exists.rec`, `crate::int_prelude::ops::exists_elim`) into a per-`n`
//! `close_within (expSeriesPartial n) e K₁` fact via
//! `close_within_of_within_at` (leg 1); transport
//! `expFnUniformConverges`'s own `.spec` at `x := one` from
//! `powerSeriesTerm expTerm j one` to `expTerm j` (`pow_one_equiv`, a fresh
//! induction, plus `mul_one`/`mul_congr`, fed through `CReal.sumRange_congr`)
//! to get `close_within (expSeriesPartial n) (expFn one) K₂` for the SAME `n`
//! (leg 2); combine the two via the triangle inequality
//! (`combine_two_legs`: `abs_add_le` + `add_le_add`, after swapping leg 1
//! with `close_within_symm`) into a single `∀ n, le (abs (add e (neg (expFn
//! one)))) (ofRat (natDivSucc K₃ n))` for a fused `K₃` (`Rat.natDivSucc_add`,
//! since both legs already share the sample index `n` — no arbitrary third
//! index needed); close with `equiv_zero_of_rate` (at `k := K₃`) then
//! `equiv_of_sub_equiv_zero`.
//!
//! Verified against the kernel, not merely `cargo check`: both
//! `creal_prelude_builds` (the full `add_declaration` sweep) and
//! `every_creal_declaration_is_checked_and_axiom_free` (environment-derived
//! coverage) pass with this declaration in the prelude.
//!
//! **`cosFn 1 ≡ cosOne` transports, and every piece it needs already
//! exists.** Verified (not merely conjectured) before writing this: `CReal.
//! cosOneConverges : Converges cosSeriesPartial cosOne`
//! (`p.cos_one_converges`, `creal/trig.rs::declare_cos_one_converges`) is
//! already the exact analogue of `e_converges` this bridge's leg 1 needs, and
//! `cosFnUniformConverges` is the same `UniformConvergesOn` `.spec` shape
//! `expFnUniformConverges` is. Leg 2's transport needs only `pow one j ≡
//! one` again (`pow_one_equiv` below is not specific to `expTerm`) composed
//! against `cosFnTerm`'s own per-file congruence instead of
//! `powerSeriesTerm_congr` directly (`cosFn`'s domain is even-index-only —
//! see this file's own top-of-file doc — so its `f` is `cosFnTerm`, not a
//! bare `powerSeriesTerm expTerm` partial application; the transport
//! argument itself does not care). `close_within_of_within_at`,
//! `combine_two_legs`, `equiv_zero_of_rate`, `equiv_of_sub_equiv_zero` are
//! all verbatim reusable, none of them mentioning `exp` anywhere in their
//! statements. Not attempted in this slice — a same-shape sibling file, sized
//! like this one.
//!
//! ## Also not built here
//!
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

use super::convergence::{converges_predicate, div_succ_at};
use super::deriv_unique::equiv_of_sub_equiv_zero;
use super::trig::{
    cabs, cadd, cle, cmul, cneg, cpow, czero, exp_dominant_cauchy_body_concrete, one_c,
};
use super::uniform_continuity::abs_neg_le;
use super::uniform_convergence::close_within_of_within_at;
use super::{CRealPrelude, DERIVED_HEIGHT, creal_ty, embed, equiv};
use crate::Kernel;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::{ExprId, ExprNode};
use crate::int_prelude::ops::{IntDev, exists_elim};
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{radd, rat_eq_rewrite};

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
        name: p.exp_fn.exp_fn_term_abs_le,
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
        let body = d.lemma(p.exp_fn.exp_fn_term_abs_le, &[pt, hax, hxb, j]);
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
        name: p.exp_fn.exp_fn,
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
    let exp_fn_c = d.kernel().const_(p.exp_fn.exp_fn, vec![]);
    let ty = d.const_app(p.uniform_converges_on, &[big_f, exp_fn_c, zero_c, one_cc]);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.exp_fn.exp_fn_uniform_converges,
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

// ---------------------------------------------------------------------------
// `CReal.expFn_one_equiv_e : Equiv (expFn one) e`. See the module
// documentation's "What is NOT built here" section (now stale on this point
// — the bridge below lands it) for the route this implements.
// ---------------------------------------------------------------------------

/// `Equiv (pow one j) one`, for any `j` (including symbolic). Induction on
/// `j`: the base case is `equiv_refl` up to `pow`'s own `Nat.zero`
/// ι-reduction; the step case unfolds `pow one (succ j)` (ι) to `mul (pow
/// one j) one`, closed by `mul_one` chained against the IH.
fn pow_one_equiv(d: &mut IntDev<'_>, p: CRealPrelude, j: ExprId) -> ExprId {
    let one_cc = one_c(d, p);
    let motive = |d: &mut IntDev<'_>, v: ExprId| -> ExprId {
        let pow_v = cpow(d, p, one_cc, v);
        equiv(d, p, pow_v, one_cc)
    };
    d.induct(
        &motive,
        &|d| d.lemma(p.equiv_refl, &[one_cc]),
        &|d, j, ih| {
            let pow_j = cpow(d, p, one_cc, j);
            let mul_pow_j_one = cmul(d, p, pow_j, one_cc);
            let step1 = d.lemma(p.mul_one, &[pow_j]); // Equiv mul_pow_j_one pow_j
            d.lemma(p.equiv_trans, &[mul_pow_j_one, pow_j, one_cc, step1, ih])
        },
        j,
    )
}

/// `Equiv (powerSeriesTerm expTerm j one) (expTerm j)` — `mul_congr` against
/// [`pow_one_equiv`], then `mul_one`.
fn power_series_term_one_equiv(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    exp_term_c: ExprId,
    j: ExprId,
) -> ExprId {
    let one_cc = one_c(d, p);
    let exp_term_j = d.apply(exp_term_c, &[j]);
    let pow_one_j = cpow(d, p, one_cc, j);
    let pow_eq = pow_one_equiv(d, p, j);
    let refl_etj = d.lemma(p.equiv_refl, &[exp_term_j]);
    let mul_congr_step = d.lemma(
        p.mul_congr,
        &[exp_term_j, exp_term_j, pow_one_j, one_cc, refl_etj, pow_eq],
    );
    let mul_one_step = d.lemma(p.mul_one, &[exp_term_j]);
    let mul_pow = cmul(d, p, exp_term_j, pow_one_j);
    let mul_one_term = cmul(d, p, exp_term_j, one_cc);
    d.lemma(
        p.equiv_trans,
        &[
            mul_pow,
            mul_one_term,
            exp_term_j,
            mul_congr_step,
            mul_one_step,
        ],
    )
}

/// `Equiv a a` via `CReal.Equiv.refl`. Reproduced (Rust privacy) from the
/// same private `erefl` shape used across `creal/monotone.rs` and
/// `creal/deriv_unique.rs`.
fn erefl(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    d.lemma(p.equiv_refl, &[a])
}

/// `Equiv b a` from `h : Equiv a b`.
fn esymm(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    d.lemma(p.equiv_symm, &[a, b, h])
}

/// Chains a sequence of `Equiv` steps from `start` through each `(next,
/// step)` pair, via `equiv_trans`. Reproduced (Rust privacy) from the same
/// private `echain` shape used across several `creal/*` modules.
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

/// `Equiv (add (neg x) x) zero` — the commuted form of `add_neg`.
/// Reproduced (Rust privacy) from `creal/monotone.rs`'s private helper of the
/// same shape.
fn neg_add_self(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let nx = cneg(d, p, x);
    let x_nx = cadd(d, p, x, nx);
    let nx_x = cadd(d, p, nx, x);
    let comm = d.lemma(p.add_comm, &[x, nx]);
    let comm_symm = esymm(d, p, x_nx, nx_x, comm);
    let cancel = d.lemma(p.add_neg, &[x]);
    echain(d, p, nx_x, &[(x_nx, comm_symm), (zero_c, cancel)])
}

/// From `h : close_within x y q`, derive `close_within y x q`. Reproduced
/// (Rust privacy) from `creal/uniform_continuity.rs`'s private
/// `close_within_symm`.
fn close_within_symm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    q: ExprId,
    h: ExprId,
) -> ExprId {
    let ny = cneg(d, p, y);
    let nx = cneg(d, p, x);
    let diff = cadd(d, p, x, ny);
    let diff2 = cadd(d, p, y, nx);
    let abs_neg_diff_le = abs_neg_le(d, p, diff, q, h);
    let swap = d.lemma(p.neg_sub_swap, &[x, y]); // Equiv (neg diff) diff2
    let neg_diff = cneg(d, p, diff);
    let ac = d.lemma(p.abs_congr, &[neg_diff, diff2, swap]);
    let refl_q = erefl(d, p, q);
    let abs_neg_diff = cabs(d, p, neg_diff);
    let abs_diff2 = cabs(d, p, diff2);
    d.lemma(
        p.le_congr,
        &[abs_neg_diff, abs_diff2, q, q, ac, refl_q, abs_neg_diff_le],
    )
}

/// `Equiv (add zero w) w`.
fn zero_add_proof(d: &mut IntDev<'_>, p: CRealPrelude, w: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let zw = cadd(d, p, zero_c, w);
    let wz = cadd(d, p, w, zero_c);
    let comm = d.lemma(p.add_comm, &[zero_c, w]);
    let az = d.lemma(p.add_zero, &[w]);
    d.lemma(p.equiv_trans, &[zw, wz, w, comm, az])
}

/// `Equiv (add (neg u) (add u w)) w` — cancel a shared `u` added and then
/// negated on the left.
fn cancel_neg_add(d: &mut IntDev<'_>, p: CRealPrelude, u: ExprId, w: ExprId) -> ExprId {
    let nu = cneg(d, p, u);
    let nu_u = cadd(d, p, nu, u);
    let inner = cadd(d, p, u, w);
    let lhs = cadd(d, p, nu, inner);
    let nu_u_w = cadd(d, p, nu_u, w);
    let assoc = d.lemma(p.add_assoc, &[nu, u, w]); // Equiv nu_u_w lhs
    let assoc_symm = esymm(d, p, nu_u_w, lhs, assoc);
    let nas = neg_add_self(d, p, u); // Equiv nu_u zero
    let zero_c = czero(d, p);
    let refl_w = erefl(d, p, w);
    let congr1 = d.lemma(p.add_congr, &[nu_u, zero_c, w, w, nas, refl_w]);
    let zero_w = cadd(d, p, zero_c, w);
    let za = zero_add_proof(d, p, w);
    echain(
        d,
        p,
        lhs,
        &[(nu_u_w, assoc_symm), (zero_w, congr1), (w, za)],
    )
}

/// `Equiv (add (add e (neg x1)) (add x1 (neg g))) (add e (neg g))` — the
/// shared-`x1` cancellation the two `close_within` legs need to fuse into
/// one `e - g` bound.
fn diff_regroup(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    e_const: ExprId,
    x1: ExprId,
    g: ExprId,
) -> ExprId {
    let ne_x1 = cneg(d, p, x1);
    let a1 = cadd(d, p, e_const, ne_x1);
    let ng = cneg(d, p, g);
    let d2 = cadd(d, p, x1, ng);
    let lhs = cadd(d, p, a1, d2);

    let inner_sum = cadd(d, p, ne_x1, d2);
    let mid = cadd(d, p, e_const, inner_sum);
    let assoc = d.lemma(p.add_assoc, &[e_const, ne_x1, d2]); // Equiv lhs mid

    let inner_cancel = cancel_neg_add(d, p, x1, ng); // Equiv inner_sum ng
    let refl_e = erefl(d, p, e_const);
    let congr_outer = d.lemma(
        p.add_congr,
        &[e_const, e_const, inner_sum, ng, refl_e, inner_cancel],
    );
    let target = cadd(d, p, e_const, ng);
    echain(d, p, lhs, &[(mid, assoc), (target, congr_outer)])
}

/// From `proof1_symm : le (abs (add e (neg x1))) q1` and `proof2 : le (abs
/// (add x1 (neg g))) q2`, derive `le (abs (add e (neg g))) (add q1 q2)` —
/// the triangle-inequality combination of the two `close_within` legs
/// sharing the midpoint `x1`.
#[allow(clippy::too_many_arguments)]
fn combine_two_legs(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    e_const: ExprId,
    x1: ExprId,
    g: ExprId,
    q1_embed: ExprId,
    q2_embed: ExprId,
    proof1_symm: ExprId,
    proof2: ExprId,
) -> ExprId {
    let ne_x1 = cneg(d, p, x1);
    let a1 = cadd(d, p, e_const, ne_x1);
    let ng = cneg(d, p, g);
    let d2 = cadd(d, p, x1, ng);
    let lhs = cadd(d, p, a1, d2);

    let abs_a1 = cabs(d, p, a1);
    let abs_d2 = cabs(d, p, d2);
    let triangle = d.lemma(p.abs_add_le, &[a1, d2]); // le (abs lhs) (add abs_a1 abs_d2)
    let combined_bound = d.lemma(
        p.add_le_add,
        &[abs_a1, q1_embed, abs_d2, q2_embed, proof1_symm, proof2],
    );
    let bound_sum = cadd(d, p, q1_embed, q2_embed);
    let abs_ab = cadd(d, p, abs_a1, abs_d2);
    let abs_lhs = cabs(d, p, lhs);
    let chain_le = d.lemma(
        p.le_trans,
        &[abs_lhs, abs_ab, bound_sum, triangle, combined_bound],
    );

    let identity = diff_regroup(d, p, e_const, x1, g); // Equiv lhs target
    let target = cadd(d, p, e_const, ng);
    let abs_identity = d.lemma(p.abs_congr, &[lhs, target, identity]);
    let refl_bound = erefl(d, p, bound_sum);
    let abs_target = cabs(d, p, target);
    d.lemma(
        p.le_congr,
        &[
            abs_lhs,
            abs_target,
            bound_sum,
            bound_sum,
            abs_identity,
            refl_bound,
            chain_le,
        ],
    )
}

/// Admit `CReal.expFn_one_equiv_e : Equiv (expFn one) e`. See the module
/// documentation for the route: eliminate `CReal.e_converges`'s `Exists`
/// witness into a per-`n` `Within` fact, bridge it to `close_within` via
/// [`close_within_of_within_at`] (leg 1), transport
/// `CReal.expFnUniformConverges`'s own `.spec` at `x := one` from
/// `powerSeriesTerm expTerm j one` to `expTerm j` via
/// [`power_series_term_one_equiv`] + `CReal.sumRange_congr` (leg 2), combine
/// the two legs by the triangle inequality ([`combine_two_legs`]), and close
/// with `CReal.equiv_zero_of_rate` + [`equiv_of_sub_equiv_zero`].
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_exp_fn_equiv_e(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let one_cc = one_c(d, p);
    let e_const = d.kernel().const_(p.e, vec![]);
    let exp_term_c = d.kernel().const_(p.exp_term, vec![]);
    let exp_series_partial_c = d.kernel().const_(p.exp_series_partial, vec![]);

    // Peel `F`/`G`/`a`/`b` off `expFnUniformConverges`'s own INFERRED type,
    // rather than reconstructing `big_f` by hand — guarantees an exact match
    // with the declared theorem's actual ascribed type.
    let u_conv = d.kernel().const_(p.exp_fn.exp_fn_uniform_converges, vec![]);
    let ty_u = d.kernel().infer(u_conv)?;
    let (inner1, b_u) = unapp(d, ty_u);
    let (inner2, a_u) = unapp(d, inner1);
    let (inner3, g_u) = unapp(d, inner2);
    let (_, f_u) = unapp(d, inner3);
    let uconv_rate_val = d.const_app(p.uconv_rate, &[f_u, g_u, a_u, b_u, u_conv]);
    let uconv_spec_val = d.const_app(p.uconv_spec, &[f_u, g_u, a_u, b_u, u_conv]);

    let hab_lo = zero_le_one(d, p);
    let hab_hi = d.lemma(p.le_refl, &[one_cc]);

    let g_one = d.apply(g_u, &[one_cc]); // expFn one
    let target = equiv(d, p, g_one, e_const);

    let predicate = converges_predicate(d, p, exp_series_partial_c, e_const);
    let e_converges_c = d.kernel().const_(p.e_converges, vec![]);

    let minor = {
        let k1_fv = d.fresh_fvar();
        let k1 = d.kernel().fvar(k1_fv);
        let hk1_ty = d.apply(predicate, &[k1]);
        let hk1_fv = d.fresh_fvar();
        let hk1 = d.kernel().fvar(hk1_fv);

        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        // --- leg 1: e_converges's raw `Within` fact, bridged to `close_within`.
        let x1 = d.apply(exp_series_partial_c, &[n]);
        let hp = d.apply(hk1, &[n]);
        let (rate1, proof1) = close_within_of_within_at(d, p, x1, e_const, n, k1, hp);
        let q1_rat = div_succ_at(d, p, rate1, n);
        let q1_embed = embed(d, p, q1_rat);
        let proof1_symm = close_within_symm(d, p, x1, e_const, q1_embed, proof1);

        // --- leg 2: expFnUniformConverges's own `.spec` at (n, one),
        // transported from `powerSeriesTerm expTerm j one` to `expTerm j`.
        let spec_at_n = d.apply(uconv_spec_val, &[n, one_cc, hab_lo, hab_hi]);
        let rate2 = uconv_rate_val;
        let q2_rat = div_succ_at(d, p, rate2, n);
        let q2_embed = embed(d, p, q2_rat);

        let f_pt_one = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let body = d.const_app(p.power_series_term, &[exp_term_c, j, one_cc]);
            d.lam_fv(j_fv, nat, body)
        };
        let per_j = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let body = power_series_term_one_equiv(d, p, exp_term_c, j);
            d.lam_fv(j_fv, nat, body)
        };
        let hn = d.lemma(p.sum_range_congr, &[f_pt_one, exp_term_c, n, per_j]);
        // hn : Equiv (sum_range f_pt_one n) (sum_range exp_term_c n)
        //    = Equiv (big_f n one) x1, by defeq (big_f's own beta-reduction
        //      and exp_series_partial's own delta-unfold, respectively).

        let big_f_n_one = d.apply(f_u, &[n, one_cc]);
        let ng_one = cneg(d, p, g_one);
        let raw_diff = cadd(d, p, big_f_n_one, ng_one);
        let x1_diff = cadd(d, p, x1, ng_one);
        let refl_ng = erefl(d, p, ng_one);
        let hn2 = d.lemma(p.add_congr, &[big_f_n_one, x1, ng_one, ng_one, hn, refl_ng]);
        let abs_raw_diff = cabs(d, p, raw_diff);
        let abs_x1_diff = cabs(d, p, x1_diff);
        let habs = d.lemma(p.abs_congr, &[raw_diff, x1_diff, hn2]);
        let refl_q2 = erefl(d, p, q2_embed);
        let proof2 = d.lemma(
            p.le_congr,
            &[
                abs_raw_diff,
                abs_x1_diff,
                q2_embed,
                q2_embed,
                habs,
                refl_q2,
                spec_at_n,
            ],
        );

        // --- combine, fuse the two bounds, and close.
        let combined = combine_two_legs(
            d,
            p,
            e_const,
            x1,
            g_one,
            q1_embed,
            q2_embed,
            proof1_symm,
            proof2,
        );
        // combined : le (abs (add e_const (neg g_one))) (add q1_embed q2_embed)

        let radd_val = radd(d, q1_rat, q2_rat);
        let of_add_eq = d.lemma(p.of_rat_add, &[q1_rat, q2_rat]);
        let v_term = cadd(d, p, e_const, ng_one);
        let abs_v = cabs(d, p, v_term);
        let refl_abs_v = erefl(d, p, abs_v);
        let bound_sum = cadd(d, p, q1_embed, q2_embed);
        let radd_embed = embed(d, p, radd_val);
        let step_a = d.lemma(
            p.le_congr,
            &[
                abs_v, abs_v, bound_sum, radd_embed, refl_abs_v, of_add_eq, combined,
            ],
        );
        // step_a : le abs_v (ofRat radd_val)

        let k3 = NatOps::add(d, rate1, rate2);
        let eq_fuse = d.lemma(p.rat.nat_div_succ_add, &[rate1, rate2, n]);
        // eq_fuse : Eq (radd q1_rat q2_rat) (natDivSucc k3 n)
        let final_bound_rat = div_succ_at(d, p, k3, n);
        let final_le = rat_eq_rewrite(d, radd_val, final_bound_rat, eq_fuse, step_a, &|d, t| {
            let target_embed = embed(d, p, t);
            cle(d, p, abs_v, target_embed)
        });
        // final_le : le abs_v (ofRat (natDivSucc k3 n))

        let per_idx = d.lam_fv(n_fv, nat, final_le);
        let v_equiv_zero = d.lemma(p.equiv_zero_of_rate, &[k3, v_term, per_idx]);
        // v_equiv_zero : Equiv v_term zero  (v_term = add e_const (neg g_one))
        let equiv_e_g = equiv_of_sub_equiv_zero(d, p, e_const, g_one, v_equiv_zero);
        // equiv_e_g : Equiv e_const g_one
        let final_result = d.lemma(p.equiv_symm, &[e_const, g_one, equiv_e_g]);
        // final_result : Equiv g_one e_const

        let with_hk1 = d.lam_fv(hk1_fv, hk1_ty, final_result);
        d.lam_fv(k1_fv, nat, with_hk1)
    };

    let value = exists_elim(d, predicate, target, e_converges_c, minor);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.exp_fn.exp_fn_one_equiv_e,
        uparams: vec![],
        ty: target,
        value,
    })
}

/// The kernel names `creal/exp_fn.rs` declares.
///
/// One of ADR-1512's per-module registries behind the [`CRealPrelude`]
/// facade: the field, its documentation and its interning all live
/// beside the `declare_*` that uses them, so a declaration added here
/// does not touch `creal.rs` at all.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExpFnNames {
    /// `CReal.expFnTermAbsLe : ∀ x, le zero x → le x one → ∀ k, le (abs
    /// (powerSeriesTerm expTerm k x)) (expDominant k)` — the domination bound
    /// [`super::CRealPrelude::weierstrass_m_test`] needs. Unlike
    /// [`super::CRealPrelude::cos_fn_term_abs_le`], NO new per-file term/congruence pair is
    /// needed here: `expTerm`'s coefficients cover EVERY `Nat` index (cosine's
    /// support only even exponents), so [`super::CRealPrelude::power_series_term`] /
    /// [`super::CRealPrelude::power_series_term_congr`] (already generic, `creal/power.rs`)
    /// apply directly at `c := expTerm`. `0 ≤ x ≤ 1` gives `pow x k ≤ one`
    /// ([`super::CRealPrelude::pow_le_one`]), `abs_mul_le_of_bounds` folds that against
    /// `le_refl (abs (expTerm k))` to `abs (powerSeriesTerm expTerm k x) ≤ abs
    /// (expTerm k)` (up to `mul_one`), and [`super::CRealPrelude::exp_term_abs_le_dominant`]
    /// closes the rest by `le_trans`. See `creal/exp_fn.rs`.
    pub exp_fn_term_abs_le: NameId,
    /// `CReal.expFn : CReal → CReal` — general exponential on the bounded
    /// domain `[0, 1]`, the `G` [`super::CRealPrelude::weierstrass_m_test`]'s own proof
    /// builds when applied at `f := powerSeriesTerm expTerm`, `mseq :=
    /// expDominant`, `a := zero`, `b := one`, extracted from that
    /// application's INFERRED type (never hand-reconstructed) so it is the
    /// identical closed term [`super::ExpFnNames::exp_fn_uniform_converges`]'s own `G`
    /// slot names. See `creal/exp_fn.rs`.
    pub exp_fn: NameId,
    /// `CReal.expFnUniformConverges : UniformConvergesOn (fun n x => sumRange
    /// (fun k => powerSeriesTerm expTerm k x) n) expFn zero one` — the M-test
    /// applied at the exponential power series, ascribed against the NAMED
    /// `expFn` (rather than the raw extracted `G`) so a caller sees the
    /// constant, not its unfolding. `expDominantCauchy`'s own concrete
    /// witness (`exp_dominant_cauchy_body_concrete`, reused unchanged from
    /// `CReal.e`'s and `cosOne`'s own constructions) supplies the M-test's
    /// `(k, hcauchy)` pair DIRECTLY — no bridge needed. See
    /// `creal/exp_fn.rs`.
    pub exp_fn_uniform_converges: NameId,
    /// `CReal.expFn_one_equiv_e : Equiv (expFn one) e` — the bridge between
    /// the general power-series `expFn` (bounded to `[0, 1]`) and the
    /// concrete `CReal.e` construction, at the shared endpoint `x := 1`.
    /// Eliminates `CReal.e_converges`'s `Exists` witness into a per-`n`
    /// `Within` fact, bridges it to `close_within` via
    /// `CReal.close_within_of_within`'s own per-index construction (leg 1),
    /// transports `expFnUniformConverges`'s `.spec` at `x := one` from
    /// `powerSeriesTerm expTerm j one` to `expTerm j` via
    /// `CReal.sumRange_congr` (leg 2), combines both legs by the triangle
    /// inequality, and closes with `CReal.equiv_zero_of_rate`. See
    /// `creal/exp_fn.rs`.
    pub exp_fn_one_equiv_e: NameId,
}

impl ExpFnNames {
    /// Interns this module's names under the `CReal` root.
    ///
    /// Split out of `creal.rs`'s `intern_names` by ADR-1512: the kernel
    /// spelling of each name sits in the file that declares it.
    pub(super) fn intern(kernel: &mut Kernel, creal: NameId) -> Self {
        Self {
            exp_fn_term_abs_le: kernel.name_str(creal, "expFnTermAbsLe"),
            exp_fn: kernel.name_str(creal, "expFn"),
            exp_fn_uniform_converges: kernel.name_str(creal, "expFnUniformConverges"),
            exp_fn_one_equiv_e: kernel.name_str(creal, "expFn_one_equiv_e"),
        }
    }
}
