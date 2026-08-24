//! **`CReal.HasDerivativeOn`** (ADR-0512, continuing phase R11): the first
//! derivative in this kernel. Bishop's *uniform* differentiability on a
//! closed interval, built to the exact one-constructor-inductive shape
//! [`super::uniform_continuity::declare_uniform_continuity`]'s own module
//! documentation already justifies at length for `UniformlyContinuousOn` one
//! level down — `modulus : Nat -> Nat` is DATA for the identical reason
//! (`0 < x` and its `Nat` witness are the same proposition, yet the witness
//! cannot be pulled out of an `Exists` and used to build anything in `Type`),
//! so `HasDerivativeOn` is again declared in `Type`, with four leading
//! parameters `F F' a b` rather than `UniformlyContinuousOn`'s three, since
//! the derivative function `F'` is now itself part of the family.
//!
//! The four range hypotheses (`le a x`, `le x b`, `le a y`, `le y b`) are
//! reused **verbatim** from `UniformlyContinuousOn`'s own spec rather than a
//! bundled interval predicate — there is none in this file, and
//! `uniform_continuity.rs`'s own module documentation already explains why
//! not (the real-valued, index-free reading of a bound, not the
//! `Converges`/`Cauchy` canonical-sample idiom). `HasDerivativeOn`'s spec
//! bound is likewise real-valued and not `CReal.Within` (that predicate
//! bounds a *rational*, `Within r q := -q <= r /\ r <= q` for `r q : Rat`;
//! the derivative's error term and its bound are both `CReal`), so this file
//! builds its own two-argument closeness predicate the same way
//! `uniform_continuity.rs`'s private `close_within` does, generalised to an
//! arbitrary `CReal` bound rather than a literal `ofRat q` (`(1/(e+1)) * |y -
//! x|` is a product, not a rational constant).
//!
//! ## What this slice lands, and what it does not
//!
//! Landed: the carrier (`HasDerivativeOn`, its two projections `modulus` and
//! `spec`), and two witnesses that show the predicate is not vacuous:
//! `hasDerivative_const` and `hasDerivative_id`. Both have error term
//! **exactly** `Equiv`-zero regardless of the hypothesis (mirroring
//! `uniform_continuity.rs`'s own `id`/`const` witnesses), so neither needs a
//! genuine two-index rational estimate, and both use the trivial modulus
//! `fun _ => 0`.
//!
//! **Not landed: the sum rule, the scalar-multiple rule, and the product
//! rule.** All three were attempted; none is force-fit, for a concrete,
//! verified reason recorded here.
//!
//! **The sum rule (`hasDerivative_add`) is blocked on a missing rational
//! lemma, not on anything about `CReal`.** Given `HasDerivativeOn F F' a b`
//! with modulus `mF` and `HasDerivativeOn G G' a b` with modulus `mG`, a
//! witness for `F + G` needs ONE combined modulus `mSum` such that, from a
//! single hypothesis `Within (y-x) (natDivSucc 1 (mSum e))`, BOTH `F`'s and
//! `G`'s own hypotheses become available. Whatever `mSum` is (`max (mF e) (mG
//! e)`, `mF e + mG e`, or any other combination that dominates both), this
//! step needs: from `Nat.le j j'`, derive `Rat.le (natDivSucc 1 j')
//! (natDivSucc 1 j)` — **`Rat.natDivSucc` antitone in its index, for two
//! arbitrary indices.** This lemma does not exist anywhere in this
//! development. `rat_prelude.rs`'s own field documentation says so
//! explicitly, twice, independently: the comment on
//! [`RatPrelude::nat_div_succ_scale`] states outright that keeping
//! `natDivSucc` "antitone in its index... off the critical path" is the
//! reason that lemma is shaped the way it is, and
//! [`RatPrelude::nat_div_succ_le_one`] and [`RatPrelude::nat_div_succ_le_scaled`]
//! both carry a line reading "still **not** antitonicity of `natDivSucc` in
//! its index" about lemmas that look close. `uniform_continuity.rs`'s own
//! module documentation hits the identical wall for the identical reason
//! (closing `uniformly_continuous_imp_continuous_at` needs "a `Nat` `k`... with
//! `K/(n+1) <= 1/(modulus k + 1)`... a genuine `Nat`-division search", and
//! reports it as not built).
//!
//! Checked before giving up on it: [`RatPrelude::inv_le_of_pos_le`] (the
//! reciprocal is antitone on the positives) is close, but bridging it to two
//! `natDivSucc` VALUES needs `natDivSucc 1 j = inv (ofNat (j+1))` as an
//! equation, an `inv_inv` law for positive rationals, and a `Nat -> Rat`
//! embedding monotonicity fact — none of which this prelude exposes either,
//! and assembling all three from scratch is a rational-field development in
//! its own right, not a derivative-slice task, and would live in
//! `rat_prelude/` — out of scope for this lane (another lane holds it).
//! [`RatPrelude::nat_div_succ_le_scaled`] looked like a shortcut (it DOES
//! compare two different indices) but only for one SPECIFIC shape, `(c+1)*n +
//! c` against `n`, which is exactly what makes the scalar-multiple rule
//! below tractable and the sum rule not: combining two INDEPENDENT, ARBITRARY
//! moduli `mF`, `mG` has no such shared shape to exploit.
//!
//! **The scalar-multiple rule (`hasDerivative_smul`) does NOT hit this wall**
//! and is left as the concrete next step for whoever picks this up: unlike
//! the sum rule, it never needs to compare two independent moduli. Given a
//! `Nat` bound `k` with `le (abs c) (ofRat (natDivSucc (Nat.succ k) 0))`
//! (`|c| <= k+1`), reading `F`'s own spec at accuracy `e' := (k+1)*e + k`
//! (rather than a fresh, incomparable modulus) makes
//! `(k+1) * natDivSucc 1 e' = natDivSucc 1 e` an EQUALITY —
//! [`RatPrelude::nat_div_succ_mul`] folds `(k+1) * natDivSucc 1 e'` to
//! `natDivSucc (k+1) e'`, and [`RatPrelude::nat_div_succ_scale`] at `c :=
//! k, m := e` reads `natDivSucc (k+1) ((k+1)*e+k)` as exactly `natDivSucc 1
//! e`. No antitonicity anywhere in that chain, only two rational identities
//! this prelude already has. Not built here for want of time in this slice,
//! not for want of a route.
//!
//! **The product rule (`hasDerivative_mul`)** additionally needs boundedness
//! of `F`, `G`, `F'`, `G'` on the interval and continuity of `F`
//! (`UniformlyContinuousOn` is exactly the tool for the last one), and was
//! not attempted once the sum rule's blocker was found, since a difference
//! quotient for a product decomposes into a sum of two error terms exactly
//! the way the sum rule's does (`(FG)(y) - (FG)(x) - (F'G+FG')(x)(y-x) =
//! G(x)*[F(y)-F(x)-F'(x)(y-x)] + F(y)*[G(y)-G(x)-G'(x)(y-x)] + [G(x)-G(y)]*...`
//! — worked out on paper to the point of seeing the same two-independent-moduli
//! combination appear, not built).

#![allow(
    clippy::doc_markdown,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use super::{CRealPrelude, creal_ty};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Admit `CReal.HasDerivativeOn` (the carrier and its two projections) and
/// two witnesses: `hasDerivative_const` and `hasDerivative_id`. See the
/// module documentation for why the sum rule, the scalar-multiple rule and
/// the product rule are not landed here.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here
/// means the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_derivative(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_carrier(d, p)?;
    declare_projections(d, p)?;
    declare_has_derivative_const(d, p)?;
    declare_has_derivative_id(d, p)
}

// --- shared term builders ----------------------------------------------------

/// `CReal -> CReal`.
fn fn_ty(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let carrier = creal_ty(d, p);
    d.arrow(carrier, carrier)
}

/// `Nat -> Nat`.
fn nat_fn_ty(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    d.arrow(nat, nat)
}

fn cadd(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.add, &[x, y])
}

fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul, &[x, y])
}

fn cabs(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.abs, &[x])
}

fn czero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

/// `add x (neg y)` — `x - y`.
fn cdiff(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    let ny = cneg(d, p, y);
    cadd(d, p, x, ny)
}

/// `Rat.natDivSucc k j`, with a literal numerator `k`.
fn div_succ(d: &mut IntDev<'_>, p: CRealPrelude, k: u32, j: ExprId) -> ExprId {
    let numerator = d.num(k);
    d.const_app(p.rat.nat_div_succ, &[numerator, j])
}

/// `le (abs v) q` — `v` bounded by `q` in magnitude, both `CReal`. The
/// derivative's own two-argument closeness predicate, generalising
/// `uniform_continuity.rs`'s private `close_within` (which fixes the bound
/// to a literal `ofRat q`) to an arbitrary `CReal` bound — the error term's
/// bound here is a product, `(1/(e+1)) * |y-x|`, not a rational constant.
fn within_real(d: &mut IntDev<'_>, p: CRealPrelude, v: ExprId, q: ExprId) -> ExprId {
    let magnitude = cabs(d, p, v);
    d.const_app(p.le, &[magnitude, q])
}

/// `CReal.HasDerivativeOn F F' a b`.
fn hd_ty(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    fp: ExprId,
    a: ExprId,
    b: ExprId,
) -> ExprId {
    d.const_app(p.has_derivative_on, &[f, fp, a, b])
}

/// Chain `Equiv start ...` through `(next, step)` pairs — the `echain` idiom
/// used throughout this development (private to each module that needs it;
/// see `series.rs`'s own copy for why it is rebuilt here rather than
/// imported).
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

/// `Equiv (neg zero) zero` — the group identity `-0 = 0`, copied from
/// `series.rs::neg_zero_equiv` (private to its own module) rather than
/// imported.
fn neg_zero_equiv(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let zero_c = czero(d, p);
    let nz = cneg(d, p, zero_c);
    let padded = cadd(d, p, nz, zero_c);
    let flipped = cadd(d, p, zero_c, nz);
    let h1 = d.lemma(p.add_zero, &[nz]); // padded ~ nz
    let step1 = d.lemma(p.equiv_symm, &[padded, nz, h1]); // nz ~ padded
    let h2 = d.lemma(p.add_comm, &[nz, zero_c]); // padded ~ flipped
    let h3 = d.lemma(p.add_neg, &[zero_c]); // flipped ~ zero_c
    echain(d, p, nz, &[(padded, step1), (flipped, h2), (zero_c, h3)])
}

/// `(term, proof)` = `(ofRat (natDivSucc k idx), le zero term)` — the
/// rational bound `k/(idx+1)` lifted to `CReal`, and a proof it is
/// nonnegative, via `Rat.zero_le_natDivSucc` and `CReal.ofRat_le`.
fn nonneg_rat_bound(d: &mut IntDev<'_>, p: CRealPrelude, k: u32, idx: ExprId) -> (ExprId, ExprId) {
    let q = div_succ(d, p, k, idx);
    let ofr_q = d.const_app(p.of_rat, &[q]);
    let rzero_expr = crate::rat_prelude::ops::rzero(d, p.rat);
    let numerator = d.num(k);
    let rat_nonneg = d.lemma(p.rat.zero_le_nat_div_succ, &[numerator, idx]);
    let proof = d.lemma(p.of_rat_le, &[rzero_expr, q, rat_nonneg]);
    (ofr_q, proof)
}

/// `(bound, proof)` = `(mul (ofRat (natDivSucc 1 e)) (abs diff), le zero
/// bound)` — the standard target error bound `(1/(e+1)) * |y-x|` from the
/// derivative's own spec, and a proof it is nonnegative
/// ([`CRealPrelude::mul_nonneg`] applied to [`nonneg_rat_bound`] and
/// [`CRealPrelude::abs_nonneg`]).
fn error_bound(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    e: ExprId,
    diff_yx: ExprId,
) -> (ExprId, ExprId) {
    let (ofr_e, ofr_e_nonneg) = nonneg_rat_bound(d, p, 1, e);
    let abs_diff = cabs(d, p, diff_yx);
    let abs_diff_nonneg = d.lemma(p.abs_nonneg, &[diff_yx]);
    let bound = cmul(d, p, ofr_e, abs_diff);
    let bound_nonneg = d.lemma(
        p.mul_nonneg,
        &[ofr_e, abs_diff, ofr_e_nonneg, abs_diff_nonneg],
    );
    (bound, bound_nonneg)
}

/// From `v_equiv_zero : Equiv v zero` and `zero_le_bound : le zero bound`,
/// derive `le (abs v) bound` — the common closing step for a derivative
/// witness whose error term is exactly zero (up to `Equiv`):
/// [`CRealPrelude::abs_le`] applied to `le v bound` (from `v ~ zero <=
/// bound`) and `le (neg v) bound` (from `neg v ~ neg zero ~ zero <= bound`).
fn close_zero_error(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    v: ExprId,
    bound: ExprId,
    v_equiv_zero: ExprId,
    zero_le_bound: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);

    let v_le_zero = d.lemma(p.le_of_equiv, &[v, zero_c, v_equiv_zero]);
    let h_upper = d.lemma(p.le_trans, &[v, zero_c, bound, v_le_zero, zero_le_bound]);

    let nv = cneg(d, p, v);
    let neg_zero_c = cneg(d, p, zero_c);
    let nv_eq_negzero = d.lemma(p.neg_congr, &[v, zero_c, v_equiv_zero]); // nv ~ neg_zero_c
    let nz_eq = neg_zero_equiv(d, p); // neg_zero_c ~ zero_c
    let nv_equiv_zero = echain(d, p, nv, &[(neg_zero_c, nv_eq_negzero), (zero_c, nz_eq)]);
    let nv_le_zero = d.lemma(p.le_of_equiv, &[nv, zero_c, nv_equiv_zero]);
    let h_lower = d.lemma(p.le_trans, &[nv, zero_c, bound, nv_le_zero, zero_le_bound]);

    d.lemma(p.abs_le, &[v, bound, h_upper, h_lower])
}

/// `∀ (e : Nat) (x y : CReal), le a x → le x b → le a y → le y b →
///   le (abs (add y (neg x))) (ofRat (natDivSucc 1 (modulus e))) →
///   le (abs (add (add (F y) (neg (F x))) (neg (mul (F' x) (add y (neg
///   x)))))) (mul (ofRat (natDivSucc 1 e)) (abs (add y (neg x))))`.
fn deriv_spec_body(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    fp: ExprId,
    a: ExprId,
    b: ExprId,
    modulus: ExprId,
) -> ExprId {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let range_ax = d.const_app(p.le, &[a, x]);
    let range_xb = d.const_app(p.le, &[x, b]);
    let range_ay = d.const_app(p.le, &[a, y]);
    let range_yb = d.const_app(p.le, &[y, b]);

    let diff_yx = cdiff(d, p, y, x);

    let mod_e = d.apply(modulus, &[e]);
    let in_bound = div_succ(d, p, 1, mod_e);
    let ofr_in_bound = d.const_app(p.of_rat, &[in_bound]);
    let hyp = within_real(d, p, diff_yx, ofr_in_bound);

    let fx = d.apply(f, &[x]);
    let fy = d.apply(f, &[y]);
    let fpx = d.apply(fp, &[x]);
    let deriv_term = cmul(d, p, fpx, diff_yx);
    let fy_fx = cdiff(d, p, fy, fx);
    let error = cdiff(d, p, fy_fx, deriv_term);

    let out_bound_rat = div_succ(d, p, 1, e);
    let ofr_out = d.const_app(p.of_rat, &[out_bound_rat]);
    let abs_diff = cabs(d, p, diff_yx);
    let out_bound = cmul(d, p, ofr_out, abs_diff);
    let conclusion = within_real(d, p, error, out_bound);

    let body = d.arrow(hyp, conclusion);
    let with_yb = d.arrow(range_yb, body);
    let with_ay = d.arrow(range_ay, with_yb);
    let with_xb = d.arrow(range_xb, with_ay);
    let with_ax = d.arrow(range_ax, with_xb);
    let with_y = d.pi_fv(y_fv, carrier, with_ax);
    let with_x = d.pi_fv(x_fv, carrier, with_y);
    d.pi_fv(e_fv, nat, with_x)
}

// --- the carrier --------------------------------------------------------------

/// `CReal.HasDerivativeOn (F F' : CReal -> CReal) (a b : CReal) : Type :=
///   mk (modulus : Nat -> Nat) (spec : ...)`.
///
/// A one-constructor inductive with four leading parameters (`F, F', a, b`)
/// — genuinely parametric, exactly one level over
/// [`super::uniform_continuity::declare_carrier`]'s own three-parameter
/// shape. See the module documentation for why the data field is
/// unavoidable.
fn declare_carrier(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat_fn = nat_fn_ty(d);
    let one = d.level_one();
    let type0 = d.kernel().sort(one);

    // ty := Π (F F' : CReal→CReal) (a b : CReal), Type 0.
    let ty = {
        let f_fv = d.fresh_fvar();
        let fp_fv = d.fresh_fvar();
        let a_fv = d.fresh_fvar();
        let b_fv = d.fresh_fvar();
        let with_b = d.pi_fv(b_fv, carrier, type0);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_fp = d.pi_fv(fp_fv, func_ty, with_a);
        d.pi_fv(f_fv, func_ty, with_fp)
    };

    // mk_ty := Π (F F' a b) (modulus : Nat → Nat) (spec : deriv_spec_body …),
    //   HasDerivativeOn F F' a b.
    let mk_ty = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let fp_fv = d.fresh_fvar();
        let fp = d.kernel().fvar(fp_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let mod_fv = d.fresh_fvar();
        let modulus = d.kernel().fvar(mod_fv);

        let spec_ty = deriv_spec_body(d, p, f, fp, a, b, modulus);
        let result = hd_ty(d, p, f, fp, a, b);

        let with_spec = d.arrow(spec_ty, result);
        let with_mod = d.pi_fv(mod_fv, nat_fn, with_spec);
        let with_b = d.pi_fv(b_fv, carrier, with_mod);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_fp = d.pi_fv(fp_fv, func_ty, with_a);
        d.pi_fv(f_fv, func_ty, with_fp)
    };

    d.kernel()
        .add_inductive(p.has_derivative_on, &[], 4, ty, &[(p.hd_mk, mk_ty)])
}

/// The two projections: the modulus (large elimination, into `Type 0`) and
/// its spec (into `Prop`, with the motive at a witness `u` reading `u`'s own
/// modulus) — the identical shape
/// [`super::uniform_continuity::declare_projections`] uses one parameter
/// over.
fn declare_projections(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat_fn = nat_fn_ty(d);
    let one = d.level_one();
    let zero_level = d.kernel().level_zero();
    let anon = d.anon_name();

    // modulus : ∀ F F' a b, HasDerivativeOn F F' a b → Nat → Nat
    //   := fun F F' a b u => HasDerivativeOn.rec F F' a b (fun _ => Nat → Nat)
    //        (fun modulus _ => modulus) u.
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let fp_fv = d.fresh_fvar();
        let fp = d.kernel().fvar(fp_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let carrier_hd = hd_ty(d, p, f, fp, a, b);

        let motive = d
            .kernel()
            .lam(anon, carrier_hd, nat_fn, crate::BinderInfo::Default);
        let minor = {
            let mod_fv = d.fresh_fvar();
            let modulus = d.kernel().fvar(mod_fv);
            let spec_ty = deriv_spec_body(d, p, f, fp, a, b, modulus);
            let inner = d
                .kernel()
                .lam(anon, spec_ty, modulus, crate::BinderInfo::Default);
            d.lam_fv(mod_fv, nat_fn, inner)
        };

        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let rec = d.kernel().const_(p.hd_rec, vec![one]);
        let body = d.apply(rec, &[f, fp, a, b, motive, minor, u]);
        let value = {
            let with_u = d.lam_fv(u_fv, carrier_hd, body);
            let with_b = d.lam_fv(b_fv, carrier, with_u);
            let with_a = d.lam_fv(a_fv, carrier, with_b);
            let with_fp = d.lam_fv(fp_fv, func_ty, with_a);
            d.lam_fv(f_fv, func_ty, with_fp)
        };
        let ty = {
            let with_u = d.arrow(carrier_hd, nat_fn);
            let with_b = d.pi_fv(b_fv, carrier, with_u);
            let with_a = d.pi_fv(a_fv, carrier, with_b);
            let with_fp = d.pi_fv(fp_fv, func_ty, with_a);
            d.pi_fv(f_fv, func_ty, with_fp)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.hd_modulus,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(super::DERIVED_HEIGHT + 45),
        })?;
    }

    // spec : ∀ F F' a b (u : HasDerivativeOn F F' a b),
    //   deriv_spec_body F F' a b (HasDerivativeOn.modulus F F' a b u)
    //   := fun F F' a b u => HasDerivativeOn.rec F F' a b
    //        (fun w => deriv_spec_body F F' a b (HasDerivativeOn.modulus F F' a b w))
    //        (fun modulus spec => spec) u.
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let fp_fv = d.fresh_fvar();
        let fp = d.kernel().fvar(fp_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let carrier_hd = hd_ty(d, p, f, fp, a, b);

        let claim = |d: &mut IntDev<'_>, w: ExprId| {
            let mod_of_w = d.const_app(p.hd_modulus, &[f, fp, a, b, w]);
            deriv_spec_body(d, p, f, fp, a, b, mod_of_w)
        };

        let motive = {
            let w_fv = d.fresh_fvar();
            let w = d.kernel().fvar(w_fv);
            let body = claim(d, w);
            d.lam_fv(w_fv, carrier_hd, body)
        };
        let minor = {
            let mod_fv = d.fresh_fvar();
            let modulus = d.kernel().fvar(mod_fv);
            let spec_ty = deriv_spec_body(d, p, f, fp, a, b, modulus);
            let spec_fv = d.fresh_fvar();
            let spec_var = d.kernel().fvar(spec_fv);
            let inner = d.lam_fv(spec_fv, spec_ty, spec_var);
            d.lam_fv(mod_fv, nat_fn, inner)
        };

        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let rec = d.kernel().const_(p.hd_rec, vec![zero_level]);
        let body = d.apply(rec, &[f, fp, a, b, motive, minor, u]);
        let value = {
            let with_u = d.lam_fv(u_fv, carrier_hd, body);
            let with_b = d.lam_fv(b_fv, carrier, with_u);
            let with_a = d.lam_fv(a_fv, carrier, with_b);
            let with_fp = d.lam_fv(fp_fv, func_ty, with_a);
            d.lam_fv(f_fv, func_ty, with_fp)
        };
        let ty = {
            let inner = claim(d, u);
            let with_u = d.pi_fv(u_fv, carrier_hd, inner);
            let with_b = d.pi_fv(b_fv, carrier, with_u);
            let with_a = d.pi_fv(a_fv, carrier, with_b);
            let with_fp = d.pi_fv(fp_fv, func_ty, with_a);
            d.pi_fv(f_fv, func_ty, with_fp)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.hd_spec,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

// --- witness: `const` -----------------------------------------------------------

/// `Equiv (add (add c (neg c)) (neg (mul zero diff))) zero` — the error term
/// of the constant witness is `Equiv`-zero unconditionally: `mul zero diff ~
/// zero` ([`CRealPrelude::mul_comm`] then [`CRealPrelude::mul_zero`]), and
/// `add c (neg c) ~ zero` ([`CRealPrelude::add_neg`]).
fn const_error_equiv_zero(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    c: ExprId,
    diff_yx: ExprId,
) -> (ExprId, ExprId) {
    let zero_c = czero(d, p);
    let add_c_negc = cdiff(d, p, c, c);
    let mul_zero_diff = cmul(d, p, zero_c, diff_yx);
    let neg_mzd = cneg(d, p, mul_zero_diff);
    let error = cadd(d, p, add_c_negc, neg_mzd);

    // mul zero diff ~ zero, via mul_comm then mul_zero.
    let diff_zero = cmul(d, p, diff_yx, zero_c);
    let comm1 = d.lemma(p.mul_comm, &[zero_c, diff_yx]); // mul_zero_diff ~ diff_zero
    let mz = d.lemma(p.mul_zero, &[diff_yx]); // diff_zero ~ zero_c
    let mzd_equiv_zero = echain(d, p, mul_zero_diff, &[(diff_zero, comm1), (zero_c, mz)]);

    // neg(mul zero diff) ~ neg zero ~ zero.
    let neg_zero_c = cneg(d, p, zero_c);
    let step_neg = d.lemma(p.neg_congr, &[mul_zero_diff, zero_c, mzd_equiv_zero]);
    let nz_eq = neg_zero_equiv(d, p);
    let neg_mzd_equiv_zero = echain(d, p, neg_mzd, &[(neg_zero_c, step_neg), (zero_c, nz_eq)]);

    // add_c_negc ~ zero.
    let h1 = d.lemma(p.add_neg, &[c]);

    // error = add(add_c_negc, neg_mzd) ~ add(add_c_negc, zero) ~ add(zero,zero) ~ zero.
    let refl_addcnegc = d.lemma(p.equiv_refl, &[add_c_negc]);
    let s1_target = cadd(d, p, add_c_negc, zero_c);
    let s1_proof = d.lemma(
        p.add_congr,
        &[
            add_c_negc,
            add_c_negc,
            neg_mzd,
            zero_c,
            refl_addcnegc,
            neg_mzd_equiv_zero,
        ],
    );

    let s2_target = cadd(d, p, zero_c, zero_c);
    let refl_zero = d.lemma(p.equiv_refl, &[zero_c]);
    let s2_proof = d.lemma(
        p.add_congr,
        &[add_c_negc, zero_c, zero_c, zero_c, h1, refl_zero],
    );

    let s3_proof = d.lemma(p.add_zero, &[zero_c]);

    let proof = echain(
        d,
        p,
        error,
        &[
            (s1_target, s1_proof),
            (s2_target, s2_proof),
            (zero_c, s3_proof),
        ],
    );
    (error, proof)
}

/// `CReal.hasDerivative_const : ∀ c a b, HasDerivativeOn (fun _ => c) (fun _
/// => zero) a b`.
///
/// The cheapest witness: the error term is `c - c - 0*(y-x)`, `Equiv`-zero
/// regardless of the hypothesis, so any modulus works (`fun _ => 0` is
/// used) — mirroring
/// [`super::uniform_continuity::declare_uniformly_continuous_const`].
fn declare_has_derivative_const(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let const_fn = {
        let ignore_fv = d.fresh_fvar();
        d.lam_fv(ignore_fv, carrier, c)
    };
    let zero_c = czero(d, p);
    let zero_fn = {
        let ignore_fv = d.fresh_fvar();
        d.lam_fv(ignore_fv, carrier, zero_c)
    };
    let modulus = {
        let ignore_fv = d.fresh_fvar();
        let z = d.num(0);
        d.lam_fv(ignore_fv, nat, z)
    };

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let spec = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hax_fv = d.fresh_fvar();
        let hxb_fv = d.fresh_fvar();
        let hay_fv = d.fresh_fvar();
        let hyb_fv = d.fresh_fvar();
        let h_fv = d.fresh_fvar();

        let range_ax = d.const_app(p.le, &[a, x]);
        let range_xb = d.const_app(p.le, &[x, b]);
        let range_ay = d.const_app(p.le, &[a, y]);
        let range_yb = d.const_app(p.le, &[y, b]);

        let diff_yx = cdiff(d, p, y, x);

        let mod_e = d.apply(modulus, &[e]);
        let in_bound = div_succ(d, p, 1, mod_e);
        let ofr_in = d.const_app(p.of_rat, &[in_bound]);
        let hyp = within_real(d, p, diff_yx, ofr_in);

        let (error, error_equiv_zero) = const_error_equiv_zero(d, p, c, diff_yx);
        let (bound, bound_nonneg) = error_bound(d, p, e, diff_yx);
        let conclusion = close_zero_error(d, p, error, bound, error_equiv_zero, bound_nonneg);

        let h = d.kernel().fvar(h_fv);
        let _ = h;
        let with_h = d.lam_fv(h_fv, hyp, conclusion);
        let with_hyb = d.lam_fv(hyb_fv, range_yb, with_h);
        let with_hay = d.lam_fv(hay_fv, range_ay, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_hay);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(e_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.hd_mk, &[const_fn, zero_fn, a, b, modulus, spec]);
    let value = {
        let with_b = d.lam_fv(b_fv, carrier, mk_applied);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        d.lam_fv(c_fv, carrier, with_a)
    };
    let ty = {
        let applied = hd_ty(d, p, const_fn, zero_fn, a, b);
        let with_b = d.pi_fv(b_fv, carrier, applied);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        d.pi_fv(c_fv, carrier, with_a)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.has_derivative_const,
        uparams: vec![],
        ty,
        value,
    })
}

// --- witness: `id` --------------------------------------------------------------

/// `Equiv (add diff (neg (mul one diff))) zero` — the error term of the
/// identity witness is `Equiv`-zero unconditionally: `mul one diff ~ diff`
/// ([`CRealPrelude::mul_comm`] then [`CRealPrelude::mul_one`]), so `diff -
/// 1*diff ~ diff - diff ~ zero` ([`CRealPrelude::add_neg`]).
fn id_error_equiv_zero(d: &mut IntDev<'_>, p: CRealPrelude, diff_yx: ExprId) -> (ExprId, ExprId) {
    let one_c = d.kernel().const_(p.one, vec![]);
    let mul_one_diff = cmul(d, p, one_c, diff_yx);
    let neg_mod = cneg(d, p, mul_one_diff);
    let error = cadd(d, p, diff_yx, neg_mod);

    let diff_one = cmul(d, p, diff_yx, one_c);
    let comm1 = d.lemma(p.mul_comm, &[one_c, diff_yx]); // mul_one_diff ~ diff_one
    let mo = d.lemma(p.mul_one, &[diff_yx]); // diff_one ~ diff_yx
    let mod_equiv_diff = echain(d, p, mul_one_diff, &[(diff_one, comm1), (diff_yx, mo)]);

    let neg_diff = cneg(d, p, diff_yx);
    let step_neg = d.lemma(p.neg_congr, &[mul_one_diff, diff_yx, mod_equiv_diff]); // neg_mod ~ neg_diff

    let refl_diff = d.lemma(p.equiv_refl, &[diff_yx]);
    let s1_target = cadd(d, p, diff_yx, neg_diff);
    let s1_proof = d.lemma(
        p.add_congr,
        &[diff_yx, diff_yx, neg_mod, neg_diff, refl_diff, step_neg],
    );

    let zero_c = czero(d, p);
    let s2_proof = d.lemma(p.add_neg, &[diff_yx]); // s1_target ~ zero_c

    let proof = echain(d, p, error, &[(s1_target, s1_proof), (zero_c, s2_proof)]);
    (error, proof)
}

/// `CReal.hasDerivative_id : ∀ a b, HasDerivativeOn (fun r => r) (fun _ =>
/// one) a b`.
///
/// The error term is `(y-x) - 1*(y-x)`, `Equiv`-zero regardless of the
/// hypothesis, so any modulus works (`fun _ => 0` is used) — the same shape
/// as [`declare_has_derivative_const`], one law swapped (`mul_one` for
/// `mul_zero`).
fn declare_has_derivative_id(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let identity = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };
    let one_c = d.kernel().const_(p.one, vec![]);
    let one_fn = {
        let ignore_fv = d.fresh_fvar();
        d.lam_fv(ignore_fv, carrier, one_c)
    };
    let modulus = {
        let ignore_fv = d.fresh_fvar();
        let z = d.num(0);
        d.lam_fv(ignore_fv, nat, z)
    };

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let spec = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hax_fv = d.fresh_fvar();
        let hxb_fv = d.fresh_fvar();
        let hay_fv = d.fresh_fvar();
        let hyb_fv = d.fresh_fvar();
        let h_fv = d.fresh_fvar();

        let range_ax = d.const_app(p.le, &[a, x]);
        let range_xb = d.const_app(p.le, &[x, b]);
        let range_ay = d.const_app(p.le, &[a, y]);
        let range_yb = d.const_app(p.le, &[y, b]);

        let diff_yx = cdiff(d, p, y, x);

        let mod_e = d.apply(modulus, &[e]);
        let in_bound = div_succ(d, p, 1, mod_e);
        let ofr_in = d.const_app(p.of_rat, &[in_bound]);
        let hyp = within_real(d, p, diff_yx, ofr_in);

        let (error, error_equiv_zero) = id_error_equiv_zero(d, p, diff_yx);
        let (bound, bound_nonneg) = error_bound(d, p, e, diff_yx);
        let conclusion = close_zero_error(d, p, error, bound, error_equiv_zero, bound_nonneg);

        let h = d.kernel().fvar(h_fv);
        let _ = h;
        let with_h = d.lam_fv(h_fv, hyp, conclusion);
        let with_hyb = d.lam_fv(hyb_fv, range_yb, with_h);
        let with_hay = d.lam_fv(hay_fv, range_ay, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_hay);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(e_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.hd_mk, &[identity, one_fn, a, b, modulus, spec]);
    let value = {
        let with_b = d.lam_fv(b_fv, carrier, mk_applied);
        d.lam_fv(a_fv, carrier, with_b)
    };
    let ty = {
        let applied = hd_ty(d, p, identity, one_fn, a, b);
        let with_b = d.pi_fv(b_fv, carrier, applied);
        d.pi_fv(a_fv, carrier, with_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.has_derivative_id,
        uparams: vec![],
        ty,
        value,
    })
}
