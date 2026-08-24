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
//! `spec`), two witnesses that show the predicate is not vacuous
//! (`hasDerivative_const`, `hasDerivative_id`, error term **exactly**
//! `Equiv`-zero regardless of the hypothesis, mirroring
//! `uniform_continuity.rs`'s own `id`/`const` witnesses, trivial modulus `fun
//! _ => 0`), and — added in a later pass — the first **nonlinear** witness,
//! `hasDerivative_sq : HasDerivativeOn (fun r => r*r) (fun x => x+x) a b`.
//! `sq`'s error term is `Equiv`-**exactly** `(y-x)*(y-x)`, not zero, so it
//! needed a from-scratch ring-algebra toolkit
//! (`neg_unique`/`mul_neg_equiv`/`neg_add_distrib`/`diff_of_squares`/
//! `sq_le_abs_sq`, below) that did not exist anywhere in [`CRealPrelude`]:
//! `diff_of_squares` gets the exact error identity (`y*y - x*x - (x+x)(y-x) =
//! (y-x)(y-x)`), and `sq_le_abs_sq` (`t*t <= |t|*|t|`, via `(|t|-t)(|t|+t) >=
//! 0` — one nonneg-product identity, no sign case-split, since `CReal.le` is
//! undecidable) gets the bound. Modulus is the identity, matching `id`'s.
//!
//! **Landed in a later pass still: `hasDerivative_neg` and `hasDerivative_add`
//! (the sum rule).** `hasDerivative_add` WAS blocked (below) and is unblocked
//! by [`RatPrelude::nat_div_succ_antitone`]; `hasDerivative_neg` was simply
//! not attempted before and turns out to need no new blocking lemma at all.
//! **Not landed: the scalar-multiple rule and the product rule** — see below
//! for why, unchanged from the earlier pass.
//!
//! **`hasDerivative_neg` needed no new blocker at all.** `neg`'s scaling
//! factor is exactly `-1`, so `neg`'s error term at accuracy `e` is
//! **exactly** `neg` of `F`'s own error term at the SAME `e` — no rescaled
//! modulus, hence no antitonicity, hence no product-of-bounds lemma. The only
//! new fact needed is structural (`|-x| = |x|`, [`le_abs_neg_of_le_abs`]
//! below), plus the mirror-image multiplication law [`neg_mul_equiv_left`].
//!
//! **The sum rule (`hasDerivative_add`) WAS blocked on a missing rational
//! lemma, and the module documentation below is kept as it was written while
//! blocked** (the reasoning that follows is what a later pass, holding
//! [`RatPrelude::nat_div_succ_antitone`], used to unblock it — see
//! [`declare_has_derivative_add`]'s own doc comment for the closing
//! argument). Given `HasDerivativeOn F F' a b`
//! with modulus `mF` and `HasDerivativeOn G G' a b` with modulus `mG`, a
//! witness for `F + G` needs ONE combined modulus `mSum` such that, from a
//! single hypothesis `Within (y-x) (natDivSucc 1 (mSum e))`, BOTH `F`'s and
//! `G`'s own hypotheses become available. Whatever `mSum` is (`max (mF e) (mG
//! e)`, `mF e + mG e`, or any other combination that dominates both), this
//! step needs: from `Nat.le j j'`, derive `Rat.le (natDivSucc 1 j')
//! (natDivSucc 1 j)` — **`Rat.natDivSucc` antitone in its index, for two
//! arbitrary indices.** This lemma did not exist anywhere in this
//! development at the time this paragraph was written. `rat_prelude.rs`'s own
//! field documentation says so
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
//! reports it as not built — that bridge is still not built).
//!
//! Checked before giving up on it (before it was unblocked):
//! [`RatPrelude::inv_le_of_pos_le`] (the
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
//! below tractable and the sum rule not (by itself — `nat_div_succ_antitone`
//! is what actually closed it): combining two INDEPENDENT, ARBITRARY
//! moduli `mF`, `mG` has no such shared shape to exploit, and the fix used
//! `Nat.add` (`mF (2e+1) + mG (2e+1)`) plus antitonicity rather than any
//! shared-shape trick — see [`declare_has_derivative_add`].
//!
//! **The scalar-multiple rule (`hasDerivative_smul`) does NOT hit the
//! antitonicity wall, but it hits a DIFFERENT one, found while verifying the
//! route before building it.** The modulus rescaling is exactly as
//! previously scouted and IS correct: given a `Nat` bound `k` with `le (abs
//! c) (ofRat (natDivSucc (Nat.succ k) 0))` (`|c| <= k+1`), reading `F`'s own
//! spec at accuracy `e' := (k+1)*e + k` (rather than a fresh, incomparable
//! modulus) makes `(k+1) * natDivSucc 1 e' = natDivSucc 1 e` an EQUALITY —
//! [`RatPrelude::nat_div_succ_mul`] folds `(k+1) * natDivSucc 1 e'` to
//! `natDivSucc (k+1) e'`, and [`RatPrelude::nat_div_succ_scale`] at `c :=
//! k, m := e` reads `natDivSucc (k+1) ((k+1)*e+k)` as exactly `natDivSucc 1
//! e`. No antitonicity anywhere in that chain.
//!
//! What the rescaling does not supply is a bound on the resulting error term.
//! `smul`'s error is EXACTLY `c * error_F` where `error_F` is `F`'s own error
//! at `e'` — and closing the spec needs `abs (mul c error_F) <= (k+1) *
//! bound_F` from `abs c <= k+1` and `abs error_F <= bound_F`, i.e. a genuine
//! **two-variable** "product of two independently-bounded quantities is
//! bounded" lemma (`|c*t| <= A*B` from `|c|<=A`, `|t|<=B`, never deciding
//! either sign, since `CReal.le` is undecidable). This is a DIFFERENT, and
//! strictly harder, fact than `sq_le_abs_sq` below (which bounds `t*t`
//! against `|t|*|t|` for the SAME `t` via ONE nonneg-product identity,
//! `(|t|-t)(|t|+t) >= 0`). The two-variable version is still provable
//! case-split-free — `2*(A*B - c*t) = (A-c)(B+t) + (A+c)(B-t) >= 0` and
//! `2*(A*B + c*t) = (A+c)(B+t) + (A-c)(B-t) >= 0`, each a SUM of two
//! nonneg products — but that is TWO difference-of-squares-shaped expansions
//! per direction, roughly double `sq`'s algebra, and was not attempted here
//! for want of time in this slice, not for want of a route. The toolkit this
//! slice built (`diff_of_squares`, `mul_neg_equiv`, `neg_add_distrib`) is the
//! right starting point for it.
//!
//! **The product rule (`hasDerivative_mul`)** additionally needs boundedness
//! of `F`, `G`, `F'`, `G'` on the interval and continuity of `F`
//! (`UniformlyContinuousOn` is exactly the tool for the last one). It was not
//! attempted once the sum rule's antitonicity blocker was found, since a
//! difference quotient for a product decomposes into a sum of two error terms
//! exactly the way the sum rule's does (`(FG)(y) - (FG)(x) - (F'G+FG')(x)(y-x)
//! = G(x)*[F(y)-F(x)-F'(x)(y-x)] + F(y)*[G(y)-G(x)-G'(x)(y-x)] +
//! [G(x)-G(y)]*...` — worked out on paper to the point of seeing the same
//! two-independent-moduli combination appear, not built). **That combination
//! is unblocked now** ([`declare_has_derivative_add`] closes it), but the
//! product rule additionally needs the scalar-multiple rule's own two-variable
//! product-of-bounds lemma, described above — still not built — so it remains
//! open for that reason, not the modulus arithmetic.

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
use crate::rat_prelude::ops::{nat_rewrite_prop, radd, rat_eq_rewrite};

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
    declare_has_derivative_id(d, p)?;
    declare_has_derivative_sq(d, p)?;
    declare_has_derivative_neg(d, p)?;
    declare_has_derivative_add(d, p)
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

// --- ring algebra helpers (support the `sq` witness) -------------------------
//
// None of this is specific to squares. It is the "difference of squares"
// toolkit `uniform_continuity.rs`'s own module documentation flagged as
// missing for scalar multiplication (`mul a (neg y) ~ neg (mul a y)`, needed
// there and never built). `hasDerivative_sq`'s error-term identity AND its
// bound both need it, so it is built here, once, from the group/ring laws
// already in [`CRealPrelude`], and used twice.

/// `Equiv a a`.
fn erefl(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    d.lemma(p.equiv_refl, &[a])
}

/// From `h : Equiv a b`, `Equiv b a`.
fn esymm(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    d.lemma(p.equiv_symm, &[a, b, h])
}

/// `Equiv (add (neg x) x) zero` — `add_neg` with its two operands commuted.
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

/// From `h_ab_zero : Equiv (add a b) zero`, `Equiv b (neg a)` — `b` is the
/// unique additive inverse of `a`. Purely group-theoretic:
/// `b ~ 0+b ~ (-a+a)+b ~ -a+(a+b) ~ -a+0 ~ -a`.
fn neg_unique(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    h_ab_zero: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let neg_a = cneg(d, p, a);

    let add_a_nega = cadd(d, p, a, neg_a);
    let add_nega_a = cadd(d, p, neg_a, a);
    let h_add_neg = d.lemma(p.add_neg, &[a]);
    let comm0 = d.lemma(p.add_comm, &[a, neg_a]);
    let symm_h = esymm(d, p, add_a_nega, zero_c, h_add_neg);
    let zero_equiv_nega_a = d.lemma(
        p.equiv_trans,
        &[zero_c, add_a_nega, add_nega_a, symm_h, comm0],
    );

    let add_b_zero = cadd(d, p, b, zero_c);
    let add_zero_b = cadd(d, p, zero_c, b);
    let h_addzero_b = d.lemma(p.add_zero, &[b]);
    let b_equiv_addbzero = esymm(d, p, add_b_zero, b, h_addzero_b);
    let comm_b0 = d.lemma(p.add_comm, &[b, zero_c]);
    let b_equiv_addzerob = d.lemma(
        p.equiv_trans,
        &[b, add_b_zero, add_zero_b, b_equiv_addbzero, comm_b0],
    );

    let addnega_a = cadd(d, p, neg_a, a);
    let addnega_a_plus_b = cadd(d, p, addnega_a, b);
    let refl_b = erefl(d, p, b);
    let subst1 = d.lemma(
        p.add_congr,
        &[zero_c, addnega_a, b, b, zero_equiv_nega_a, refl_b],
    );

    let a_plus_b = cadd(d, p, a, b);
    let nega_plus_aplusb = cadd(d, p, neg_a, a_plus_b);
    let assoc = d.lemma(p.add_assoc, &[neg_a, a, b]);

    let nega_plus_zero = cadd(d, p, neg_a, zero_c);
    let refl_nega = erefl(d, p, neg_a);
    let subst2 = d.lemma(
        p.add_congr,
        &[neg_a, neg_a, a_plus_b, zero_c, refl_nega, h_ab_zero],
    );

    let final_step = d.lemma(p.add_zero, &[neg_a]);

    echain(
        d,
        p,
        b,
        &[
            (add_zero_b, b_equiv_addzerob),
            (addnega_a_plus_b, subst1),
            (nega_plus_aplusb, assoc),
            (nega_plus_zero, subst2),
            (neg_a, final_step),
        ],
    )
}

/// `Equiv (neg (neg x)) x` — double negation, from [`neg_unique`] applied to
/// [`neg_add_self`].
fn double_neg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let nx = cneg(d, p, x);
    let nnx = cneg(d, p, nx);
    let h = neg_add_self(d, p, x);
    let nu = neg_unique(d, p, nx, x, h);
    esymm(d, p, x, nnx, nu)
}

/// `Equiv (mul x (neg y)) (neg (mul x y))`.
fn mul_neg_equiv(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let ny = cneg(d, p, y);
    let xy = cmul(d, p, x, y);
    let x_ny = cmul(d, p, x, ny);
    let y_plus_ny = cadd(d, p, y, ny);
    let x_times_sum = cmul(d, p, x, y_plus_ny);

    let h_add_neg_y = d.lemma(p.add_neg, &[y]);
    let refl_x = erefl(d, p, x);
    let h_mulcongr = d.lemma(p.mul_congr, &[x, x, y_plus_ny, zero_c, refl_x, h_add_neg_y]);
    let x_zero = cmul(d, p, x, zero_c);
    let h_mulzero = d.lemma(p.mul_zero, &[x]);
    let sum_equiv_zero = echain(
        d,
        p,
        x_times_sum,
        &[(x_zero, h_mulcongr), (zero_c, h_mulzero)],
    );

    let h_ld = d.lemma(p.left_distrib, &[x, y, ny]);
    let sum_of_products = cadd(d, p, xy, x_ny);
    let symm_ld = esymm(d, p, x_times_sum, sum_of_products, h_ld);
    let h_sum_zero = d.lemma(
        p.equiv_trans,
        &[
            sum_of_products,
            x_times_sum,
            zero_c,
            symm_ld,
            sum_equiv_zero,
        ],
    );

    neg_unique(d, p, xy, x_ny, h_sum_zero)
}

/// `Equiv (neg (add a b)) (add (neg a) (neg b))`.
fn neg_add_distrib(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let na = cneg(d, p, a);
    let nb = cneg(d, p, b);
    let ab = cadd(d, p, a, b);
    let na_nb = cadd(d, p, na, nb);
    let b_na = cadd(d, p, b, na);
    let na_b = cadd(d, p, na, b);
    let b_nanb = cadd(d, p, b, na_nb);
    let b_na_nb = cadd(d, p, b_na, nb);
    let na_b_nb = cadd(d, p, na_b, nb);
    let b_nb = cadd(d, p, b, nb);
    let na_bnb = cadd(d, p, na, b_nb);
    let na_zero = cadd(d, p, na, zero_c);
    let ab_nanb = cadd(d, p, ab, na_nb);
    let a_bnanb = cadd(d, p, a, b_nanb);
    let a_na = cadd(d, p, a, na);
    let neg_ab = cneg(d, p, ab);

    let step2 = d.lemma(p.add_assoc, &[b, na, nb]);
    let step2_symm = esymm(d, p, b_na_nb, b_nanb, step2);

    let step3 = d.lemma(p.add_comm, &[b, na]);
    let refl_nb = erefl(d, p, nb);
    let step4 = d.lemma(p.add_congr, &[b_na, na_b, nb, nb, step3, refl_nb]);

    let step5 = d.lemma(p.add_assoc, &[na, b, nb]);

    let step6 = d.lemma(p.add_neg, &[b]);
    let refl_na = erefl(d, p, na);
    let step7 = d.lemma(p.add_congr, &[na, na, b_nb, zero_c, refl_na, step6]);

    let step8 = d.lemma(p.add_zero, &[na]);

    let middle_result = echain(
        d,
        p,
        b_nanb,
        &[
            (b_na_nb, step2_symm),
            (na_b_nb, step4),
            (na_bnb, step5),
            (na_zero, step7),
            (na, step8),
        ],
    );

    let refl_a = erefl(d, p, a);
    let step9 = d.lemma(p.add_congr, &[a, a, b_nanb, na, refl_a, middle_result]);
    let step10 = d.lemma(p.add_neg, &[a]);

    let step1 = d.lemma(p.add_assoc, &[a, b, na_nb]);

    let h = echain(
        d,
        p,
        ab_nanb,
        &[(a_bnanb, step1), (a_na, step9), (zero_c, step10)],
    );

    let nu = neg_unique(d, p, ab, na_nb, h);
    esymm(d, p, na_nb, neg_ab, nu)
}

/// `Equiv (add (add x (neg y)) (add y (neg z))) (add x (neg z))` — cancelling
/// a middle `+y −y` pair.
fn cancel_middle(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId, z: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let ny = cneg(d, p, y);
    let nz = cneg(d, p, z);
    let x_ny = cadd(d, p, x, ny);
    let y_nz = cadd(d, p, y, nz);
    let outer = cadd(d, p, x_ny, y_nz);
    let x_negz = cadd(d, p, x, nz);
    let ny_y = cadd(d, p, ny, y);
    let ny_y_nz = cadd(d, p, ny_y, nz);
    let ny_yz = cadd(d, p, ny, y_nz);
    let zero_nz = cadd(d, p, zero_c, nz);
    let nz_zero = cadd(d, p, nz, zero_c);
    let x_plus_nyyz = cadd(d, p, x, ny_yz);

    let inner_assoc = d.lemma(p.add_assoc, &[ny, y, nz]);
    let inner_assoc_symm = esymm(d, p, ny_y_nz, ny_yz, inner_assoc);

    let ny_y_zero = neg_add_self(d, p, y);
    let refl_nz = erefl(d, p, nz);
    let step_zero = d.lemma(p.add_congr, &[ny_y, zero_c, nz, nz, ny_y_zero, refl_nz]);

    let comm_znz = d.lemma(p.add_comm, &[zero_c, nz]);
    let step_trim = d.lemma(p.add_zero, &[nz]);
    let zero_nz_to_nz = echain(d, p, zero_nz, &[(nz_zero, comm_znz), (nz, step_trim)]);

    let middle_result = echain(
        d,
        p,
        ny_yz,
        &[
            (ny_y_nz, inner_assoc_symm),
            (zero_nz, step_zero),
            (nz, zero_nz_to_nz),
        ],
    );

    let refl_x = erefl(d, p, x);
    let step_final = d.lemma(p.add_congr, &[x, x, ny_yz, nz, refl_x, middle_result]);

    let outer_assoc = d.lemma(p.add_assoc, &[x, ny, y_nz]);

    echain(
        d,
        p,
        outer,
        &[(x_plus_nyyz, outer_assoc), (x_negz, step_final)],
    )
}

/// `Equiv (mul (add a (neg b)) (add a b)) (add (mul a a) (neg (mul b b)))` —
/// `(a-b)*(a+b) ~ a*a - b*b`.
fn diff_of_squares(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let nb = cneg(d, p, b);
    let big_a = cadd(d, p, a, nb);
    let big_b = cadd(d, p, a, b);
    let lhs0 = cmul(d, p, big_a, big_b);
    let mul_a_a = cmul(d, p, a, a);
    let mul_a_b = cmul(d, p, a, b);
    let mul_b_a = cmul(d, p, b, a);
    let mul_b_b = cmul(d, p, b, b);
    let neg_mul_a_b = cneg(d, p, mul_a_b);
    let neg_mul_b_b = cneg(d, p, mul_b_b);
    let mul_a_nb = cmul(d, p, a, nb);
    let mul_b_nb = cmul(d, p, b, nb);
    let mul_biga_a = cmul(d, p, big_a, a);
    let mul_biga_b = cmul(d, p, big_a, b);
    let mul_a_biga = cmul(d, p, a, big_a);
    let mul_b_biga = cmul(d, p, b, big_a);
    let target1 = cadd(d, p, mul_biga_a, mul_biga_b);
    let big_p = cadd(d, p, mul_a_a, neg_mul_a_b);
    let big_q = cadd(d, p, mul_a_b, neg_mul_b_b);
    let pq = cadd(d, p, big_p, big_q);
    let final_rhs = cadd(d, p, mul_a_a, neg_mul_b_b);

    let step1 = d.lemma(p.left_distrib, &[big_a, a, b]);

    let c1 = d.lemma(p.mul_comm, &[big_a, a]);
    let c2 = d.lemma(p.left_distrib, &[a, a, nb]);
    let add_aa_anb = cadd(d, p, mul_a_a, mul_a_nb);
    let c3 = mul_neg_equiv(d, p, a, b);
    let refl_aa = erefl(d, p, mul_a_a);
    let c3c = d.lemma(
        p.add_congr,
        &[mul_a_a, mul_a_a, mul_a_nb, neg_mul_a_b, refl_aa, c3],
    );
    let proof_p = echain(
        d,
        p,
        mul_biga_a,
        &[(mul_a_biga, c1), (add_aa_anb, c2), (big_p, c3c)],
    );

    let d1 = d.lemma(p.mul_comm, &[big_a, b]);
    let d2 = d.lemma(p.left_distrib, &[b, a, nb]);
    let add_ba_bnb = cadd(d, p, mul_b_a, mul_b_nb);
    let d3 = mul_neg_equiv(d, p, b, b);
    let refl_ba = erefl(d, p, mul_b_a);
    let d3c = d.lemma(
        p.add_congr,
        &[mul_b_a, mul_b_a, mul_b_nb, neg_mul_b_b, refl_ba, d3],
    );
    let add_ba_negbb = cadd(d, p, mul_b_a, neg_mul_b_b);
    let d4 = d.lemma(p.mul_comm, &[b, a]);
    let refl_negbb = erefl(d, p, neg_mul_b_b);
    let d4c = d.lemma(
        p.add_congr,
        &[mul_b_a, mul_a_b, neg_mul_b_b, neg_mul_b_b, d4, refl_negbb],
    );
    let proof_q = echain(
        d,
        p,
        mul_biga_b,
        &[
            (mul_b_biga, d1),
            (add_ba_bnb, d2),
            (add_ba_negbb, d3c),
            (big_q, d4c),
        ],
    );

    let pq_congr = d.lemma(
        p.add_congr,
        &[mul_biga_a, big_p, mul_biga_b, big_q, proof_p, proof_q],
    );

    let cm = cancel_middle(d, p, mul_a_a, mul_a_b, mul_b_b);

    echain(
        d,
        p,
        lhs0,
        &[(target1, step1), (pq, pq_congr), (final_rhs, cm)],
    )
}

/// From `h : le y z`, `le zero (add z (neg y))`.
fn sub_nonneg_of_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    y: ExprId,
    z: ExprId,
    h: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let ny = cneg(d, p, y);
    let gap = cadd(d, p, z, ny);
    let cancelled = cadd(d, p, y, ny);

    let reflexive = d.lemma(p.le_refl, &[ny]);
    let shifted = d.lemma(p.add_le_add, &[y, z, ny, ny, h, reflexive]);
    let cancel = d.lemma(p.add_neg, &[y]);
    let gap_refl = erefl(d, p, gap);
    d.lemma(
        p.le_congr,
        &[cancelled, zero_c, gap, gap, cancel, gap_refl, shifted],
    )
}

/// From `h : le zero (add b (neg a))`, `le a b`.
fn le_of_nonneg_sub(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    h: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let na = cneg(d, p, a);
    let gap = cadd(d, p, b, na);
    let zero_a = cadd(d, p, zero_c, a);
    let gap_a = cadd(d, p, gap, a);
    let na_a = cadd(d, p, na, a);
    let b_naa = cadd(d, p, b, na_a);
    let a_zero = cadd(d, p, a, zero_c);
    let b_zero = cadd(d, p, b, zero_c);

    let reflexive = d.lemma(p.le_refl, &[a]);
    let step1 = d.lemma(p.add_le_add, &[zero_c, gap, a, a, h, reflexive]);

    let lhs_comm = d.lemma(p.add_comm, &[zero_c, a]);
    let lhs_trim = d.lemma(p.add_zero, &[a]);
    let lhs_eq = echain(d, p, zero_a, &[(a_zero, lhs_comm), (a, lhs_trim)]);

    let rhs_assoc = d.lemma(p.add_assoc, &[b, na, a]);
    let na_a_zero = neg_add_self(d, p, a);
    let refl_b = erefl(d, p, b);
    let rhs_congr = d.lemma(p.add_congr, &[b, b, na_a, zero_c, refl_b, na_a_zero]);
    let rhs_trim = d.lemma(p.add_zero, &[b]);
    let rhs_eq = echain(
        d,
        p,
        gap_a,
        &[(b_naa, rhs_assoc), (b_zero, rhs_congr), (b, rhs_trim)],
    );

    d.lemma(p.le_congr, &[zero_a, a, gap_a, b, lhs_eq, rhs_eq, step1])
}

/// From `v_nonneg : le zero v` and `bound_nonneg : le zero bound`,
/// `le (neg v) bound`.
fn neg_le_of_nonneg(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    v: ExprId,
    bound: ExprId,
    v_nonneg: ExprId,
    bound_nonneg: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let neg_v = cneg(d, p, v);
    let neg_zero = cneg(d, p, zero_c);

    let step = d.lemma(p.neg_le_neg, &[zero_c, v, v_nonneg]);
    let nz_eq = neg_zero_equiv(d, p);
    let refl_negv = erefl(d, p, neg_v);
    let le_negv_zero = d.lemma(
        p.le_congr,
        &[neg_v, neg_v, neg_zero, zero_c, refl_negv, nz_eq, step],
    );

    d.lemma(
        p.le_trans,
        &[neg_v, zero_c, bound, le_negv_zero, bound_nonneg],
    )
}

/// `le (mul t t) (mul (abs t) (abs t))` — squaring is dominated by squaring
/// the magnitude, via `(|t|-t)*(|t|+t) >= 0` ([`diff_of_squares`] plus
/// [`CRealPrelude::mul_nonneg`]), never deciding `t`'s sign.
fn sq_le_abs_sq(d: &mut IntDev<'_>, p: CRealPrelude, t: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let abs_t = cabs(d, p, t);
    let nt = cneg(d, p, t);
    let nnt = cneg(d, p, nt);

    let h_self_le = d.lemma(p.le_abs_self, &[t]);
    let h1 = sub_nonneg_of_le(d, p, t, abs_t, h_self_le);

    let h_neg_le = d.lemma(p.neg_le_abs, &[t]);
    let h2a = sub_nonneg_of_le(d, p, nt, abs_t, h_neg_le);

    let nn = double_neg(d, p, t);
    let abs_t_nnt = cadd(d, p, abs_t, nnt);
    let abs_t_t = cadd(d, p, abs_t, t);
    let refl_abst = erefl(d, p, abs_t);
    let eqb = d.lemma(p.add_congr, &[abs_t, abs_t, nnt, t, refl_abst, nn]);

    let refl_zero = erefl(d, p, zero_c);
    let h2 = d.lemma(
        p.le_congr,
        &[zero_c, zero_c, abs_t_nnt, abs_t_t, refl_zero, eqb, h2a],
    );

    let abs_t_nt = cadd(d, p, abs_t, nt);
    let dos = diff_of_squares(d, p, abs_t, t);
    let prod = cmul(d, p, abs_t_nt, abs_t_t);
    let mn = d.lemma(p.mul_nonneg, &[abs_t_nt, abs_t_t, h1, h2]);

    let mul_abst_abst = cmul(d, p, abs_t, abs_t);
    let mul_t_t = cmul(d, p, t, t);
    let neg_mul_t_t = cneg(d, p, mul_t_t);
    let diffsq_rhs = cadd(d, p, mul_abst_abst, neg_mul_t_t);

    let h_diffsq_nonneg = d.lemma(
        p.le_congr,
        &[zero_c, zero_c, prod, diffsq_rhs, refl_zero, dos, mn],
    );

    le_of_nonneg_sub(d, p, mul_t_t, mul_abst_abst, h_diffsq_nonneg)
}

/// `Equiv (mul (neg a) b) (neg (mul a b))` — the mirror of [`mul_neg_equiv`]
/// (which negates the *second* factor), built the same way: commute, apply
/// [`mul_neg_equiv`], commute back under `neg_congr`.
fn neg_mul_equiv_left(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let na = cneg(d, p, a);
    let lhs = cmul(d, p, na, b);
    let b_na = cmul(d, p, b, na);
    let c1 = d.lemma(p.mul_comm, &[na, b]); // lhs ~ b_na

    let ba = cmul(d, p, b, a);
    let neg_ba = cneg(d, p, ba);
    let c2 = mul_neg_equiv(d, p, b, a); // b_na ~ neg_ba

    let ab = cmul(d, p, a, b);
    let neg_ab = cneg(d, p, ab);
    let c3a = d.lemma(p.mul_comm, &[b, a]); // ba ~ ab
    let c3 = d.lemma(p.neg_congr, &[ba, ab, c3a]); // neg_ba ~ neg_ab

    echain(d, p, lhs, &[(b_na, c1), (neg_ba, c2), (neg_ab, c3)])
}

/// `Equiv (mul (add a b) c) (add (mul a c) (mul b c))` — the missing
/// distributivity direction, the sum on the **left** of the product.
/// `CReal.left_distrib` only distributes a sum on the right; this is built
/// from it plus `mul_comm` on all three products, copied from
/// `creal/power.rs`'s own private `right_distrib` (rebuilt here rather than
/// imported, the same convention this file already follows for
/// `neg_zero_equiv`/`mul_neg_equiv`).
fn right_distrib(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
    let ab = cadd(d, p, a, b);
    let lhs = cmul(d, p, ab, c);
    let c_ab = cmul(d, p, c, ab);
    let h1 = d.lemma(p.mul_comm, &[ab, c]); // lhs ~ c_ab

    let ca = cmul(d, p, c, a);
    let cb = cmul(d, p, c, b);
    let dist = cadd(d, p, ca, cb);
    let h2 = d.lemma(p.left_distrib, &[c, a, b]); // c_ab ~ dist

    let ac = cmul(d, p, a, c);
    let bc = cmul(d, p, b, c);
    let target = cadd(d, p, ac, bc);
    let h3a = d.lemma(p.mul_comm, &[c, a]); // ca ~ ac
    let h3b = d.lemma(p.mul_comm, &[c, b]); // cb ~ bc
    let h3 = d.lemma(p.add_congr, &[ca, ac, cb, bc, h3a, h3b]); // dist ~ target

    echain(d, p, lhs, &[(c_ab, h1), (dist, h2), (target, h3)])
}

/// `Equiv (add (add a b) (add c dd)) (add (add a c) (add b dd))` — swap the
/// middle two of a four-term sum. Copied from `creal/series.rs`'s own
/// private `add4_comm` (same convention as `right_distrib` above). Returns
/// `(target, proof)`.
fn add4_comm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    dd: ExprId,
) -> (ExprId, ExprId) {
    let cd = cadd(d, p, c, dd);
    let bd = cadd(d, p, b, dd);
    let ab = cadd(d, p, a, b);
    let start = cadd(d, p, ab, cd);

    // start ~ a + (b + (c+d))
    let bcd = cadd(d, p, b, cd);
    let s1 = cadd(d, p, a, bcd);
    let h1 = d.lemma(p.add_assoc, &[a, b, cd]);

    // b+(c+d) ~ (b+c)+d
    let bc = cadd(d, p, b, c);
    let bc_d = cadd(d, p, bc, dd);
    let s2 = cadd(d, p, a, bc_d);
    let refl_a = d.lemma(p.equiv_refl, &[a]);
    let h_bcd = d.lemma(p.add_assoc, &[b, c, dd]); // (b+c)+d ~ b+(c+d)
    let h2_inner = d.lemma(p.equiv_symm, &[bc_d, bcd, h_bcd]); // b+(c+d) ~ (b+c)+d
    let h2 = d.lemma(p.add_congr, &[a, a, bcd, bc_d, refl_a, h2_inner]);

    // (b+c) ~ (c+b)
    let cb = cadd(d, p, c, b);
    let cb_d = cadd(d, p, cb, dd);
    let s3 = cadd(d, p, a, cb_d);
    let h_comm = d.lemma(p.add_comm, &[b, c]); // b+c ~ c+b
    let refl_dd = d.lemma(p.equiv_refl, &[dd]);
    let h_comm_d = d.lemma(p.add_congr, &[bc, cb, dd, dd, h_comm, refl_dd]); // (b+c)+d ~ (c+b)+d
    let h3 = d.lemma(p.add_congr, &[a, a, bc_d, cb_d, refl_a, h_comm_d]);

    // (c+b)+d ~ c+(b+d)
    let cbd = cadd(d, p, c, bd);
    let s4 = cadd(d, p, a, cbd);
    let h_assoc2 = d.lemma(p.add_assoc, &[c, b, dd]); // (c+b)+d ~ c+(b+d)
    let h4 = d.lemma(p.add_congr, &[a, a, cb_d, cbd, refl_a, h_assoc2]);

    // a+(c+(b+d)) ~ (a+c)+(b+d)
    let ac = cadd(d, p, a, c);
    let target = cadd(d, p, ac, bd);
    let h_assoc3 = d.lemma(p.add_assoc, &[a, c, bd]); // target ~ s4
    let h5 = d.lemma(p.equiv_symm, &[target, s4, h_assoc3]); // s4 ~ target

    let proof = echain(
        d,
        p,
        start,
        &[(s1, h1), (s2, h2), (s3, h3), (s4, h4), (target, h5)],
    );
    (target, proof)
}

/// `le (abs (add a b)) (add (abs a) (abs b))` — the two-term triangle
/// inequality, from [`CRealPrelude::abs_le`] with
/// [`CRealPrelude::add_le_add`]/[`CRealPrelude::le_abs_self`] for the lower
/// branch and [`neg_add_distrib`] plus [`CRealPrelude::neg_le_abs`] for the
/// upper (negated) branch. Copied from `creal/series.rs`'s own private
/// `abs_add_le`, using this file's own `neg_add_distrib` in place of
/// `series.rs`'s `neg_add` (the identical statement, built earlier in this
/// file for `sq_le_abs_sq`).
fn abs_add_le(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let s = cadd(d, p, a, b);
    let abs_a = cabs(d, p, a);
    let abs_b = cabs(d, p, b);
    let bound = cadd(d, p, abs_a, abs_b);

    // premise1 : le (add a b) (add (abs a) (abs b))
    let le_a = d.lemma(p.le_abs_self, &[a]);
    let le_b = d.lemma(p.le_abs_self, &[b]);
    let premise1 = d.lemma(p.add_le_add, &[a, abs_a, b, abs_b, le_a, le_b]);

    // premise2 : le (neg (add a b)) (add (abs a) (abs b))
    let na = cneg(d, p, a);
    let nb = cneg(d, p, b);
    let t = cadd(d, p, na, nb);
    let ns = cneg(d, p, s);
    let na_eq = neg_add_distrib(d, p, a, b); // ns ~ t
    let step1 = d.lemma(p.le_of_equiv, &[ns, t, na_eq]); // le ns t
    let nle_a = d.lemma(p.neg_le_abs, &[a]); // le na abs_a
    let nle_b = d.lemma(p.neg_le_abs, &[b]); // le nb abs_b
    let step2 = d.lemma(p.add_le_add, &[na, abs_a, nb, abs_b, nle_a, nle_b]); // le t bound
    let premise2 = d.lemma(p.le_trans, &[ns, t, bound, step1, step2]);

    d.lemma(p.abs_le, &[s, bound, premise1, premise2])
}

/// From `eq_vw : Equiv v w` and `h_w : le (abs w) bound`, derive `le (abs v)
/// bound` — [`CRealPrelude::abs_congr`] plus [`CRealPrelude::le_congr`],
/// the general "the bound transports along an `Equiv` on the value" step
/// every witness in this file that reduces its own error term to a simpler
/// shape needs at least once.
fn abs_le_of_equiv(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    v: ExprId,
    w: ExprId,
    bound: ExprId,
    eq_vw: ExprId,
    h_w: ExprId,
) -> ExprId {
    let abs_v = cabs(d, p, v);
    let abs_w = cabs(d, p, w);
    let abs_eq = d.lemma(p.abs_congr, &[v, w, eq_vw]); // Equiv abs_v abs_w
    let abs_eq_symm = esymm(d, p, abs_v, abs_w, abs_eq); // Equiv abs_w abs_v
    let refl_bound = erefl(d, p, bound);
    d.lemma(
        p.le_congr,
        &[abs_w, abs_v, bound, bound, abs_eq_symm, refl_bound, h_w],
    )
}

/// From `h : le (abs x) bound`, derive `le (abs (neg x)) bound` — `|−x| =
/// |x|` is a structural identity (true regardless of `x`'s sign, never
/// decided), so this is NOT an instance of [`abs_le_of_equiv`] (`neg x` is
/// not `Equiv`-equal to `x` in general): it goes through [`abs_le`] directly,
/// bounding `neg x` (via [`CRealPrelude::neg_le_abs`]) and `neg (neg x)`
/// (via [`double_neg`] transporting [`CRealPrelude::le_abs_self`]) each
/// against the same `bound` `h` already supplies for `abs x`.
fn le_abs_neg_of_le_abs(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    bound: ExprId,
    h: ExprId,
) -> ExprId {
    let abs_x = cabs(d, p, x);
    let nx = cneg(d, p, x);
    let nnx = cneg(d, p, nx);

    // le (neg x) bound
    let nle = d.lemma(p.neg_le_abs, &[x]); // le nx abs_x
    let upper = d.lemma(p.le_trans, &[nx, abs_x, bound, nle, h]);

    // le (neg (neg x)) bound, via double_neg transporting `le x bound`.
    let le_x_bound = {
        let sle = d.lemma(p.le_abs_self, &[x]); // le x abs_x
        d.lemma(p.le_trans, &[x, abs_x, bound, sle, h])
    };
    let nn = double_neg(d, p, x); // Equiv nnx x
    let nn_symm = esymm(d, p, nnx, x, nn); // Equiv x nnx
    let refl_bound = erefl(d, p, bound);
    let lower = d.lemma(
        p.le_congr,
        &[x, nnx, bound, bound, nn_symm, refl_bound, le_x_bound],
    );

    d.lemma(p.abs_le, &[nx, bound, upper, lower])
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

// --- witness: `sq` -----------------------------------------------------------

/// The error term for `F := fun r => mul r r`, `F' := fun x => add x x` is
/// **exactly** `mul diff diff` (not merely `Equiv`-zero, unlike
/// `const`/`id`): `y*y - x*x - (x+x)*(y-x) = (y-x)*(y+x) - (x+x)*(y-x) =
/// (y-x)*(y-x)`, using [`diff_of_squares`] once for `y*y - x*x` and again
/// (through [`neg_add_distrib`]) to cancel `(y+x) - (x+x)` down to `y - x`.
/// Returns `(error, diff, proof : Equiv error (mul diff diff))`.
fn sq_error_equiv_diffsq(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let nx = cneg(d, p, x);
    let diff = cadd(d, p, y, nx); // y - x
    let sumyx = cadd(d, p, y, x); // y + x
    let sumxx = cadd(d, p, x, x); // x + x
    let fy = cmul(d, p, y, y);
    let fx = cmul(d, p, x, x);
    let neg_fx = cneg(d, p, fx);
    let fy_fx = cadd(d, p, fy, neg_fx);
    let deriv_term = cmul(d, p, sumxx, diff);
    let neg_deriv_term = cneg(d, p, deriv_term);
    let error = cadd(d, p, fy_fx, neg_deriv_term);
    let sqdiff = cmul(d, p, diff, diff);

    // Step A: fy_fx ~ mul diff sumyx, via `diff_of_squares(y, x)`.
    let mul_diff_sumyx = cmul(d, p, diff, sumyx);
    let dos_yx = diff_of_squares(d, p, y, x); // Equiv mul_diff_sumyx fy_fx
    let step_a = esymm(d, p, mul_diff_sumyx, fy_fx, dos_yx); // Equiv fy_fx mul_diff_sumyx

    let step1_target = cadd(d, p, mul_diff_sumyx, neg_deriv_term);
    let refl_negderiv = erefl(d, p, neg_deriv_term);
    let step_a_congr = d.lemma(
        p.add_congr,
        &[
            fy_fx,
            mul_diff_sumyx,
            neg_deriv_term,
            neg_deriv_term,
            step_a,
            refl_negderiv,
        ],
    ); // Equiv error step1_target

    // Step B: neg deriv_term ~ neg (mul diff sumxx), via mul_comm.
    let mul_diff_sumxx = cmul(d, p, diff, sumxx);
    let mc = d.lemma(p.mul_comm, &[sumxx, diff]); // Equiv deriv_term mul_diff_sumxx
    let neg_mul_diff_sumxx = cneg(d, p, mul_diff_sumxx);
    let neg_mc = d.lemma(p.neg_congr, &[deriv_term, mul_diff_sumxx, mc]);

    let step2_target = cadd(d, p, mul_diff_sumyx, neg_mul_diff_sumxx);
    let refl_muldiffsumyx = erefl(d, p, mul_diff_sumyx);
    let step_b_congr = d.lemma(
        p.add_congr,
        &[
            mul_diff_sumyx,
            mul_diff_sumyx,
            neg_deriv_term,
            neg_mul_diff_sumxx,
            refl_muldiffsumyx,
            neg_mc,
        ],
    ); // Equiv step1_target step2_target

    // Step C: step2_target ~ mul diff (sumyx - sumxx), via left_distrib and
    // `mul_neg_equiv`.
    let neg_sumxx = cneg(d, p, sumxx);
    let mul_diff_negsumxx = cmul(d, p, diff, neg_sumxx);
    let mne = mul_neg_equiv(d, p, diff, sumxx); // Equiv mul_diff_negsumxx neg_mul_diff_sumxx

    let sum_yx_negsumxx = cadd(d, p, sumyx, neg_sumxx);
    let mul_diff_sum = cmul(d, p, diff, sum_yx_negsumxx);
    let ld = d.lemma(p.left_distrib, &[diff, sumyx, neg_sumxx]);
    let ld_target = cadd(d, p, mul_diff_sumyx, mul_diff_negsumxx);
    let refl_muldiffsumyx2 = erefl(d, p, mul_diff_sumyx);
    let ld_congr = d.lemma(
        p.add_congr,
        &[
            mul_diff_sumyx,
            mul_diff_sumyx,
            mul_diff_negsumxx,
            neg_mul_diff_sumxx,
            refl_muldiffsumyx2,
            mne,
        ],
    ); // Equiv ld_target step2_target

    let ld_combined = echain(
        d,
        p,
        mul_diff_sum,
        &[(ld_target, ld), (step2_target, ld_congr)],
    );
    let step_c = esymm(d, p, mul_diff_sum, step2_target, ld_combined); // Equiv step2_target mul_diff_sum

    // Step D: sum_yx_negsumxx ~ diff (the cancellation).
    let nx_nx = cadd(d, p, nx, nx);
    let nad = neg_add_distrib(d, p, x, x); // Equiv neg_sumxx nx_nx
    let refl_sumyx = erefl(d, p, sumyx);
    let sum_yx_nxnx = cadd(d, p, sumyx, nx_nx);
    let step_c1 = d.lemma(
        p.add_congr,
        &[sumyx, sumyx, neg_sumxx, nx_nx, refl_sumyx, nad],
    ); // Equiv sum_yx_negsumxx sum_yx_nxnx

    let x_nxnx = cadd(d, p, x, nx_nx);
    let y_x_nxnx = cadd(d, p, y, x_nxnx);
    let e1 = d.lemma(p.add_assoc, &[y, x, nx_nx]); // Equiv sum_yx_nxnx y_x_nxnx

    let x_nx = cadd(d, p, x, nx);
    let xnx_nx = cadd(d, p, x_nx, nx);
    let e2 = d.lemma(p.add_assoc, &[x, nx, nx]); // Equiv xnx_nx x_nxnx
    let e2_symm = esymm(d, p, xnx_nx, x_nxnx, e2); // Equiv x_nxnx xnx_nx

    let refl_y = erefl(d, p, y);
    let y_xnxnx = cadd(d, p, y, xnx_nx);
    let e2c = d.lemma(p.add_congr, &[y, y, x_nxnx, xnx_nx, refl_y, e2_symm]); // Equiv y_x_nxnx y_xnxnx

    let zero_c = czero(d, p);
    let e3 = d.lemma(p.add_neg, &[x]); // Equiv x_nx zero_c
    let refl_nx = erefl(d, p, nx);
    let zero_nx = cadd(d, p, zero_c, nx);
    let e3c = d.lemma(p.add_congr, &[x_nx, zero_c, nx, nx, e3, refl_nx]); // Equiv xnx_nx zero_nx

    let refl_y2 = erefl(d, p, y);
    let y_zeronx = cadd(d, p, y, zero_nx);
    let e3cc = d.lemma(p.add_congr, &[y, y, xnx_nx, zero_nx, refl_y2, e3c]); // Equiv y_xnxnx y_zeronx

    let nx_zero = cadd(d, p, nx, zero_c);
    let e4 = d.lemma(p.add_comm, &[zero_c, nx]); // Equiv zero_nx nx_zero
    let e5 = d.lemma(p.add_zero, &[nx]); // Equiv nx_zero nx
    let e45 = echain(d, p, zero_nx, &[(nx_zero, e4), (nx, e5)]); // Equiv zero_nx nx

    let refl_y3 = erefl(d, p, y);
    let e45c = d.lemma(p.add_congr, &[y, y, zero_nx, nx, refl_y3, e45]); // Equiv y_zeronx diff

    let final_regroup = echain(
        d,
        p,
        sum_yx_nxnx,
        &[
            (y_x_nxnx, e1),
            (y_xnxnx, e2c),
            (y_zeronx, e3cc),
            (diff, e45c),
        ],
    ); // Equiv sum_yx_nxnx diff

    let cancel_d = echain(
        d,
        p,
        sum_yx_negsumxx,
        &[(sum_yx_nxnx, step_c1), (diff, final_regroup)],
    ); // Equiv sum_yx_negsumxx diff

    let refl_diff = erefl(d, p, diff);
    let mul_congr_result = d.lemma(
        p.mul_congr,
        &[diff, diff, sum_yx_negsumxx, diff, refl_diff, cancel_d],
    ); // Equiv mul_diff_sum sqdiff

    let final_proof = echain(
        d,
        p,
        error,
        &[
            (step1_target, step_a_congr),
            (step2_target, step_b_congr),
            (mul_diff_sum, step_c),
            (sqdiff, mul_congr_result),
        ],
    );

    (error, diff, final_proof)
}

/// `CReal.hasDerivative_sq : ∀ a b, HasDerivativeOn (fun r => mul r r) (fun x
/// => add x x) a b`.
///
/// The first nonlinear derivative in this kernel. The error term is
/// **exactly** `(y-x)*(y-x)` ([`sq_error_equiv_diffsq`]), not merely
/// `Equiv`-zero, so the modulus is the identity (`fun n => n`, mirroring `id`)
/// and the bound closes via [`sq_le_abs_sq`] plus
/// [`CRealPrelude::mul_le_mul_of_nonneg_left`]: `|y-x|^2 <= |y-x| *
/// (1/(e+1))`.
fn declare_has_derivative_sq(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let square = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let rr = cmul(d, p, r, r);
        d.lam_fv(r_fv, carrier, rr)
    };
    let double = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let xx = cadd(d, p, x, x);
        d.lam_fv(x_fv, carrier, xx)
    };
    let modulus = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        d.lam_fv(n_fv, nat, n)
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

        let (error, diff, error_equiv_sqdiff) = sq_error_equiv_diffsq(d, p, x, y);
        let abs_diff = cabs(d, p, diff);
        let abs_diff_nonneg = d.lemma(p.abs_nonneg, &[diff]);

        let mod_e = d.apply(modulus, &[e]);
        let (q, q_nonneg) = nonneg_rat_bound(d, p, 1, mod_e);
        let hyp = within_real(d, p, diff, q);
        let h = d.kernel().fvar(h_fv);

        let bound = cmul(d, p, q, abs_diff);
        let bound_nonneg = d.lemma(p.mul_nonneg, &[q, abs_diff, q_nonneg, abs_diff_nonneg]);

        let sqdiff = cmul(d, p, diff, diff);
        let sq_bound_step = sq_le_abs_sq(d, p, diff); // le sqdiff (mul abs_diff abs_diff)
        let mul_abs_abs = cmul(d, p, abs_diff, abs_diff);
        let mul_abs_q = cmul(d, p, abs_diff, q);
        let mlm = d.lemma(
            p.mul_le_mul_of_nonneg_left,
            &[abs_diff, abs_diff, q, abs_diff_nonneg, h],
        ); // le mul_abs_abs mul_abs_q
        let step_ab = d.lemma(
            p.le_trans,
            &[sqdiff, mul_abs_abs, mul_abs_q, sq_bound_step, mlm],
        ); // le sqdiff mul_abs_q
        let comm_qa = d.lemma(p.mul_comm, &[abs_diff, q]); // Equiv mul_abs_q bound
        let refl_sqdiff = erefl(d, p, sqdiff);
        let h_upper_sqdiff = d.lemma(
            p.le_congr,
            &[
                sqdiff,
                sqdiff,
                mul_abs_q,
                bound,
                refl_sqdiff,
                comm_qa,
                step_ab,
            ],
        ); // le sqdiff bound

        let sqn = d.lemma(p.sq_nonneg, &[diff]); // le zero sqdiff
        let h_lower_sqdiff = neg_le_of_nonneg(d, p, sqdiff, bound, sqn, bound_nonneg); // le (neg sqdiff) bound

        let error_equiv_sqdiff_symm = esymm(d, p, error, sqdiff, error_equiv_sqdiff); // Equiv sqdiff error
        let refl_bound = erefl(d, p, bound);
        let h_upper_error = d.lemma(
            p.le_congr,
            &[
                sqdiff,
                error,
                bound,
                bound,
                error_equiv_sqdiff_symm,
                refl_bound,
                h_upper_sqdiff,
            ],
        ); // le error bound

        let neg_sqdiff = cneg(d, p, sqdiff);
        let neg_error = cneg(d, p, error);
        let neg_eq = d.lemma(p.neg_congr, &[sqdiff, error, error_equiv_sqdiff_symm]);
        let h_lower_error = d.lemma(
            p.le_congr,
            &[
                neg_sqdiff,
                neg_error,
                bound,
                bound,
                neg_eq,
                refl_bound,
                h_lower_sqdiff,
            ],
        ); // le (neg error) bound

        let conclusion = d.lemma(p.abs_le, &[error, bound, h_upper_error, h_lower_error]);

        let with_h = d.lam_fv(h_fv, hyp, conclusion);
        let with_hyb = d.lam_fv(hyb_fv, range_yb, with_h);
        let with_hay = d.lam_fv(hay_fv, range_ay, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_hay);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(e_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.hd_mk, &[square, double, a, b, modulus, spec]);
    let value = {
        let with_b = d.lam_fv(b_fv, carrier, mk_applied);
        d.lam_fv(a_fv, carrier, with_b)
    };
    let ty = {
        let applied = hd_ty(d, p, square, double, a, b);
        let with_b = d.pi_fv(b_fv, carrier, applied);
        d.pi_fv(a_fv, carrier, with_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.has_derivative_sq,
        uparams: vec![],
        ty,
        value,
    })
}

// --- witness: `neg` -----------------------------------------------------------

/// `CReal.hasDerivative_neg : ∀ F F' a b, HasDerivativeOn F F' a b →
/// HasDerivativeOn (fun r => neg (F r)) (fun x => neg (F' x)) a b`.
///
/// `neg`'s scaling factor is exactly `-1`, so — unlike the sum rule below —
/// it needs no rescaled modulus at all: `neg`'s error term at accuracy `e` is
/// **exactly** `neg` of `F`'s own error term at the SAME `e`
/// ([`neg_error_equiv_neg`]), so `F`'s own hypothesis at `e` is already
/// exactly what `F`'s own spec needs, and [`le_abs_neg_of_le_abs`] turns
/// `F`'s own bound into the bound `neg`'s error needs, transported along that
/// `Equiv` by [`abs_le_of_equiv`].
fn declare_has_derivative_neg(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let fp_fv = d.fresh_fvar();
    let fp = d.kernel().fvar(fp_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hf_ty = hd_ty(d, p, f, fp, a, b);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);

    let neg_f = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let fr = d.apply(f, &[r]);
        let nfr = cneg(d, p, fr);
        d.lam_fv(r_fv, carrier, nfr)
    };
    let neg_fp = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let fpx = d.apply(fp, &[x]);
        let nfpx = cneg(d, p, fpx);
        d.lam_fv(x_fv, carrier, nfpx)
    };
    // Reuse F's own modulus verbatim: `neg`'s error is exactly `neg` of F's,
    // so no rescaling is needed.
    let modulus = d.const_app(p.hd_modulus, &[f, fp, a, b, hf]);

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
        let abs_diff = cabs(d, p, diff_yx);

        let mod_e = d.apply(modulus, &[e]);
        let in_bound = div_succ(d, p, 1, mod_e);
        let ofr_in = d.const_app(p.of_rat, &[in_bound]);
        let hyp = within_real(d, p, diff_yx, ofr_in);
        let h_fv_expr = d.kernel().fvar(h_fv);

        let fx = d.apply(f, &[x]);
        let fy = d.apply(f, &[y]);
        let fpx = d.apply(fp, &[x]);
        let deriv_term_f = cmul(d, p, fpx, diff_yx);
        let fy_fx_f = cdiff(d, p, fy, fx);
        let error_f = cdiff(d, p, fy_fx_f, deriv_term_f);

        let neg_fy = cneg(d, p, fy);
        let neg_fx = cneg(d, p, fx);
        let neg_neg_fx = cneg(d, p, neg_fx);
        let neg_fpx = cneg(d, p, fpx);
        let fy_fx_neg = cadd(d, p, neg_fy, neg_neg_fx);
        let deriv_term_neg = cmul(d, p, neg_fpx, diff_yx);
        let neg_deriv_term_neg = cneg(d, p, deriv_term_neg);
        let error_neg = cadd(d, p, fy_fx_neg, neg_deriv_term_neg);

        let out_bound_rat = div_succ(d, p, 1, e);
        let ofr_out = d.const_app(p.of_rat, &[out_bound_rat]);
        let out_bound = cmul(d, p, ofr_out, abs_diff);

        // Step 1: `neg error_f ~ add(add(neg fy, neg(neg fx)), mul fpx diff)`.
        // `error_f = add(fy_fx_f, neg(deriv_term_f))` (a DIFFERENCE, not a
        // sum), so the outer split is over `(fy_fx_f, neg_deriv_term_f)`,
        // and the second component needs `double_neg` to fold the resulting
        // `neg(neg(deriv_term_f))` back to `deriv_term_f`.
        let neg_p_step = neg_add_distrib(d, p, fy, neg_fx); // neg(fy-fx) ~ (-fy)+(-(-fx))
        let neg_q_step = double_neg(d, p, deriv_term_f); // -(-(mul fpx diff)) ~ mul fpx diff
        let rhs_target = cadd(d, p, fy_fx_neg, deriv_term_f);
        let neg_error_f = cneg(d, p, error_f);
        let neg_deriv_term_f = cneg(d, p, deriv_term_f);
        let neg_fy_fx_f = cneg(d, p, fy_fx_f);
        let neg_error_f_split = neg_add_distrib(d, p, fy_fx_f, neg_deriv_term_f); // -error_f ~ (-fy_fx_f)+(-(-deriv_term_f))
        let neg_neg_deriv_term_f = cneg(d, p, neg_deriv_term_f);
        let step1_congr = d.lemma(
            p.add_congr,
            &[
                neg_fy_fx_f,
                fy_fx_neg,
                neg_neg_deriv_term_f,
                deriv_term_f,
                neg_p_step,
                neg_q_step,
            ],
        );
        let neg_error_f_split_target = cadd(d, p, neg_fy_fx_f, neg_neg_deriv_term_f);
        let neg_error_f_to_rhs = echain(
            d,
            p,
            neg_error_f,
            &[
                (neg_error_f_split_target, neg_error_f_split),
                (rhs_target, step1_congr),
            ],
        );

        // Step 2: `error_neg ~ rhs_target` (first component is syntactically
        // identical; second needs `neg(mul(neg fpx, diff)) ~ mul fpx diff`).
        let nmel = neg_mul_equiv_left(d, p, fpx, diff_yx); // mul(neg fpx, diff) ~ neg(mul fpx diff)
        let neg_congr_nmel = d.lemma(p.neg_congr, &[deriv_term_neg, neg_deriv_term_f, nmel]);
        let dn2 = double_neg(d, p, deriv_term_f); // neg(neg(mul fpx diff)) ~ mul fpx diff
        let second_component = echain(
            d,
            p,
            neg_deriv_term_neg,
            &[(neg_neg_deriv_term_f, neg_congr_nmel), (deriv_term_f, dn2)],
        );
        let refl_fst = erefl(d, p, fy_fx_neg);
        let error_neg_to_rhs = d.lemma(
            p.add_congr,
            &[
                fy_fx_neg,
                fy_fx_neg,
                neg_deriv_term_neg,
                deriv_term_f,
                refl_fst,
                second_component,
            ],
        );

        // Step 3: combine.
        let rhs_to_neg_error_f = esymm(d, p, neg_error_f, rhs_target, neg_error_f_to_rhs);
        let error_neg_equiv_neg_error_f = echain(
            d,
            p,
            error_neg,
            &[
                (rhs_target, error_neg_to_rhs),
                (neg_error_f, rhs_to_neg_error_f),
            ],
        );

        let hax = d.kernel().fvar(hax_fv);
        let hxb = d.kernel().fvar(hxb_fv);
        let hay = d.kernel().fvar(hay_fv);
        let hyb = d.kernel().fvar(hyb_fv);
        let error_f_bound = d.lemma(
            p.hd_spec,
            &[f, fp, a, b, hf, e, x, y, hax, hxb, hay, hyb, h_fv_expr],
        ); // le (abs error_f) out_bound
        let neg_error_f_bound = le_abs_neg_of_le_abs(d, p, error_f, out_bound, error_f_bound);
        let conclusion = abs_le_of_equiv(
            d,
            p,
            error_neg,
            neg_error_f,
            out_bound,
            error_neg_equiv_neg_error_f,
            neg_error_f_bound,
        );

        let with_h = d.lam_fv(h_fv, hyp, conclusion);
        let with_hyb = d.lam_fv(hyb_fv, range_yb, with_h);
        let with_hay = d.lam_fv(hay_fv, range_ay, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_hay);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(e_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.hd_mk, &[neg_f, neg_fp, a, b, modulus, spec]);
    let value = {
        let with_hf = d.lam_fv(hf_fv, hf_ty, mk_applied);
        let with_b = d.lam_fv(b_fv, carrier, with_hf);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_fp = d.lam_fv(fp_fv, func_ty, with_a);
        d.lam_fv(f_fv, func_ty, with_fp)
    };
    let ty = {
        let applied = hd_ty(d, p, neg_f, neg_fp, a, b);
        let with_hf = d.arrow(hf_ty, applied);
        let with_b = d.pi_fv(b_fv, carrier, with_hf);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_fp = d.pi_fv(fp_fv, func_ty, with_a);
        d.pi_fv(f_fv, func_ty, with_fp)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.has_derivative_neg,
        uparams: vec![],
        ty,
        value,
    })
}

// --- witness: `add` (the sum rule) --------------------------------------------

/// `CReal.hasDerivative_add : ∀ F F' G G' a b, HasDerivativeOn F F' a b →
/// HasDerivativeOn G G' a b → HasDerivativeOn (fun r => add (F r) (G r))
/// (fun x => add (F' x) (G' x)) a b`.
///
/// **The sum rule**, unblocked by [`RatPrelude::nat_div_succ_antitone`]
/// (see the module documentation). The combined modulus at accuracy `e` is
/// `mF (2e+1) + mG (2e+1)` (`Nat.add`, not `max` — `nat_prelude` has no
/// `Nat.max`, and `Nat.le_add_right`/`Nat.add_comm` give both `<=`
/// directions just as well: `mF(2e+1) <= mF(2e+1)+mG(2e+1)` directly, and
/// `mG(2e+1) <= mG(2e+1)+mF(2e+1) = mF(2e+1)+mG(2e+1)` after one
/// commutation). Antitonicity reads the hypothesis at the combined modulus
/// back down to each sub-derivative's own hypothesis at `2e+1`;
/// `F`'s/`G`'s own specs at `2e+1` each bound their error by `1/(2e+2) ·
/// |y-x|`; and `Rat.natDivSucc_add` + `Rat.natDivSucc_halve` fuse the two
/// `1/(2e+2)` bounds into the single target `1/(e+1)` (`1/(2e+2) +
/// 1/(2e+2) = 2/(2e+2) = 1/(e+1)`). The combined error term itself needs a
/// six-term commutative/associative regroup ([`add4_comm`], applied twice)
/// plus [`neg_add_distrib`]/[`right_distrib`] to see that it IS `F`'s error
/// plus `G`'s error, exactly.
fn declare_has_derivative_add(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let fp_fv = d.fresh_fvar();
    let fp = d.kernel().fvar(fp_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let gp_fv = d.fresh_fvar();
    let gp = d.kernel().fvar(gp_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hf_ty = hd_ty(d, p, f, fp, a, b);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);
    let hg_ty = hd_ty(d, p, g, gp, a, b);
    let hg_fv = d.fresh_fvar();
    let hg = d.kernel().fvar(hg_fv);

    let fsum = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let fr = d.apply(f, &[r]);
        let gr = d.apply(g, &[r]);
        let sum = cadd(d, p, fr, gr);
        d.lam_fv(r_fv, carrier, sum)
    };
    let fsum_p = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let fpx = d.apply(fp, &[x]);
        let gpx = d.apply(gp, &[x]);
        let sum = cadd(d, p, fpx, gpx);
        d.lam_fv(x_fv, carrier, sum)
    };
    let mf = d.const_app(p.hd_modulus, &[f, fp, a, b, hf]);
    let mg = d.const_app(p.hd_modulus, &[g, gp, a, b, hg]);
    // `modulus_sum e := mF (2e+1) + mG (2e+1)`.
    let modulus_sum = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let two = d.num(2);
        let two_e = d.mul(two, e);
        let e_prime = d.succ(two_e);
        let mf_e2 = d.apply(mf, &[e_prime]);
        let mg_e2 = d.apply(mg, &[e_prime]);
        let sum = d.add(mf_e2, mg_e2);
        d.lam_fv(e_fv, nat, sum)
    };

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
        let hax = d.kernel().fvar(hax_fv);
        let hxb = d.kernel().fvar(hxb_fv);
        let hay = d.kernel().fvar(hay_fv);
        let hyb = d.kernel().fvar(hyb_fv);

        let diff_yx = cdiff(d, p, y, x);
        let abs_diff = cabs(d, p, diff_yx);

        let mod_e = d.apply(modulus_sum, &[e]);
        let in_bound = div_succ(d, p, 1, mod_e);
        let ofr_in = d.const_app(p.of_rat, &[in_bound]);
        let hyp = within_real(d, p, diff_yx, ofr_in);
        let h = d.kernel().fvar(h_fv);

        // --- the index/modulus arithmetic ------------------------------------
        let two = d.num(2);
        let two_e = d.mul(two, e);
        let e_prime = d.succ(two_e);
        let mf_e2 = d.apply(mf, &[e_prime]);
        let mg_e2 = d.apply(mg, &[e_prime]);
        let modulus_sum_e = d.add(mf_e2, mg_e2);
        let mg_plus_mf = d.add(mg_e2, mf_e2);

        let nat_p = p.rat.int.nat;
        let h_le_f = d.lemma(nat_p.le_add_right, &[mf_e2, mg_e2]); // Le mf_e2 (add mf_e2 mg_e2)
        let raw_g = d.lemma(nat_p.le_add_right, &[mg_e2, mf_e2]); // Le mg_e2 (add mg_e2 mf_e2)
        let comm_eq = d.lemma(nat_p.add_comm, &[mg_e2, mf_e2]); // Eq (add mg_e2 mf_e2) (add mf_e2 mg_e2)
        let h_le_g = nat_rewrite_prop(d, mg_plus_mf, modulus_sum_e, comm_eq, raw_g, &|d, t| {
            d.le(mg_e2, t)
        });

        let r_f = div_succ(d, p, 1, mf_e2);
        let r_g = div_succ(d, p, 1, mg_e2);
        let r_sum = div_succ(d, p, 1, modulus_sum_e);
        let rat_f = d.lemma(p.rat.nat_div_succ_antitone, &[mf_e2, modulus_sum_e, h_le_f]); // Rat.le r_sum r_f
        let rat_g = d.lemma(p.rat.nat_div_succ_antitone, &[mg_e2, modulus_sum_e, h_le_g]); // Rat.le r_sum r_g

        let ofr_sum = d.const_app(p.of_rat, &[r_sum]);
        let ofr_f = d.const_app(p.of_rat, &[r_f]);
        let ofr_g = d.const_app(p.of_rat, &[r_g]);
        let creal_f = d.lemma(p.of_rat_le, &[r_sum, r_f, rat_f]); // le ofr_sum ofr_f
        let creal_g = d.lemma(p.of_rat_le, &[r_sum, r_g, rat_g]); // le ofr_sum ofr_g

        let hyp_f = d.lemma(p.le_trans, &[abs_diff, ofr_sum, ofr_f, h, creal_f]); // le abs_diff ofr_f
        let hyp_g = d.lemma(p.le_trans, &[abs_diff, ofr_sum, ofr_g, h, creal_g]); // le abs_diff ofr_g

        // --- F's and G's own error terms and bounds, at accuracy `2e+1` -----
        let fx = d.apply(f, &[x]);
        let fy = d.apply(f, &[y]);
        let fpx = d.apply(fp, &[x]);
        let gx = d.apply(g, &[x]);
        let gy = d.apply(g, &[y]);
        let gpx = d.apply(gp, &[x]);

        let mfxd = cmul(d, p, fpx, diff_yx);
        let mgxd = cmul(d, p, gpx, diff_yx);
        let fy_fx_f = cdiff(d, p, fy, fx);
        let fy_fx_g = cdiff(d, p, gy, gx);
        let error_f = cdiff(d, p, fy_fx_f, mfxd);
        let error_g = cdiff(d, p, fy_fx_g, mgxd);

        let error_f_bound = d.lemma(
            p.hd_spec,
            &[f, fp, a, b, hf, e_prime, x, y, hax, hxb, hay, hyb, hyp_f],
        ); // le (abs error_f) (mul (ofRat r_prime') abs_diff)
        let error_g_bound = d.lemma(
            p.hd_spec,
            &[g, gp, a, b, hg, e_prime, x, y, hax, hxb, hay, hyb, hyp_g],
        );

        let r_prime = div_succ(d, p, 1, e_prime);
        let q_prime = d.const_app(p.of_rat, &[r_prime]);
        let q_bound = cmul(d, p, q_prime, abs_diff);

        // --- combine the two bounds via the triangle inequality -------------
        let combined_error = cadd(d, p, error_f, error_g);
        let abs_error_f = cabs(d, p, error_f);
        let abs_error_g = cabs(d, p, error_g);
        let triangle = abs_add_le(d, p, error_f, error_g); // le (abs combined_error) (add abs_error_f abs_error_g)
        let sum_bounds = d.lemma(
            p.add_le_add,
            &[
                abs_error_f,
                q_bound,
                abs_error_g,
                q_bound,
                error_f_bound,
                error_g_bound,
            ],
        ); // le (add abs_error_f abs_error_g) (add q_bound q_bound)
        let abs_combined_error = cabs(d, p, combined_error);
        let abs_error_f_plus_g = cadd(d, p, abs_error_f, abs_error_g);
        let q_bound_plus_q_bound = cadd(d, p, q_bound, q_bound);
        let combined_le = d.lemma(
            p.le_trans,
            &[
                abs_combined_error,
                abs_error_f_plus_g,
                q_bound_plus_q_bound,
                triangle,
                sum_bounds,
            ],
        ); // le (abs combined_error) (add q_bound q_bound)

        // --- fuse `add q_bound q_bound` down to the single target bound -----
        let out_bound_rat = div_succ(d, p, 1, e);
        let ofr_out = d.const_app(p.of_rat, &[out_bound_rat]);
        let out_bound = cmul(d, p, ofr_out, abs_diff);

        let one_nat = d.num(1);
        let of_rat_add_proof = d.lemma(p.of_rat_add, &[r_prime, r_prime]); // Equiv (add q_prime q_prime) (ofRat (Rat.add r_prime r_prime))
        let eq1 = d.lemma(p.rat.nat_div_succ_add, &[one_nat, one_nat, e_prime]); // Eq (Rat.add r_prime r_prime) (natDivSucc (add 1 1) e_prime)
        let two_e_prime = div_succ(d, p, 2, e_prime);
        let radd_r_prime_r_prime = radd(d, r_prime, r_prime);
        let q_prime_plus_q_prime = cadd(d, p, q_prime, q_prime);
        let step_a = rat_eq_rewrite(
            d,
            radd_r_prime_r_prime,
            two_e_prime,
            eq1,
            of_rat_add_proof,
            &|d, t| {
                let oft = d.const_app(p.of_rat, &[t]);
                d.const_app(p.equiv, &[q_prime_plus_q_prime, oft])
            },
        ); // Equiv (add q_prime q_prime) (ofRat two_e_prime)
        let eq2 = d.lemma(p.rat.nat_div_succ_halve, &[e]); // Eq two_e_prime (natDivSucc 1 e)
        let sum_equiv_target_rat =
            rat_eq_rewrite(d, two_e_prime, out_bound_rat, eq2, step_a, &|d, t| {
                let oft = d.const_app(p.of_rat, &[t]);
                d.const_app(p.equiv, &[q_prime_plus_q_prime, oft])
            }); // Equiv (add q_prime q_prime) ofr_out

        let mul_q_prime_sum_abs_diff = cmul(d, p, q_prime_plus_q_prime, abs_diff);
        let rd = right_distrib(d, p, q_prime, q_prime, abs_diff); // Equiv (mul (add q_prime q_prime) abs_diff) (add q_bound q_bound)
        let rd_symm = esymm(d, p, mul_q_prime_sum_abs_diff, q_bound_plus_q_bound, rd); // Equiv (add q_bound q_bound) (mul (add q_prime q_prime) abs_diff)
        let refl_abs_diff = erefl(d, p, abs_diff);
        let mul_step = d.lemma(
            p.mul_congr,
            &[
                q_prime_plus_q_prime,
                ofr_out,
                abs_diff,
                abs_diff,
                sum_equiv_target_rat,
                refl_abs_diff,
            ],
        ); // Equiv (mul (add q_prime q_prime) abs_diff) out_bound
        let bound_equiv = echain(
            d,
            p,
            q_bound_plus_q_bound,
            &[(mul_q_prime_sum_abs_diff, rd_symm), (out_bound, mul_step)],
        ); // Equiv (add q_bound q_bound) out_bound

        let combined_error_bound = {
            let abs_combined = cabs(d, p, combined_error);
            let refl_abs = erefl(d, p, abs_combined);
            d.lemma(
                p.le_congr,
                &[
                    abs_combined,
                    abs_combined,
                    q_bound_plus_q_bound,
                    out_bound,
                    refl_abs,
                    bound_equiv,
                    combined_le,
                ],
            )
        }; // le (abs combined_error) out_bound

        // --- the actual error term IS F's error plus G's, exactly -----------
        let fsum_y = d.apply(fsum, &[y]);
        let fsum_x = d.apply(fsum, &[x]);
        let fsum_p_x = d.apply(fsum_p, &[x]);
        let deriv_term_sum = cmul(d, p, fsum_p_x, diff_yx);
        let fy_fx_sum = cdiff(d, p, fsum_y, fsum_x);
        let actual_error = cdiff(d, p, fy_fx_sum, deriv_term_sum);

        let neg_fx = cneg(d, p, fx);
        let neg_gx = cneg(d, p, gx);
        let neg_mfxd = cneg(d, p, mfxd);
        let neg_mgxd = cneg(d, p, mgxd);

        // Step A: `neg (add fx gx) ~ add (neg fx) (neg gx)`.
        let step_a_eq = neg_add_distrib(d, p, fx, gx);
        // Step B: `neg (mul (add fpx gpx) diff) ~ add (neg mfxd) (neg mgxd)`.
        let fpx_plus_gpx = cadd(d, p, fpx, gpx);
        let rd_fg = right_distrib(d, p, fpx, gpx, diff_yx); // Equiv (mul (add fpx gpx) diff) (add mfxd mgxd)
        let deriv_sum_raw = cmul(d, p, fpx_plus_gpx, diff_yx);
        let mfxd_plus_mgxd = cadd(d, p, mfxd, mgxd);
        let neg_congr_rdfg = d.lemma(p.neg_congr, &[deriv_sum_raw, mfxd_plus_mgxd, rd_fg]); // Equiv (neg deriv_sum_raw) (neg (add mfxd mgxd))
        let step_b_split = neg_add_distrib(d, p, mfxd, mgxd); // Equiv (neg (add mfxd mgxd)) (add (neg mfxd) (neg mgxd))
        let neg_deriv_sum_raw = cneg(d, p, deriv_sum_raw);
        let neg_mfxd_plus_mgxd = cneg(d, p, mfxd_plus_mgxd);
        let neg_mfxd_neg_mgxd = cadd(d, p, neg_mfxd, neg_mgxd);
        let step_b_eq = echain(
            d,
            p,
            neg_deriv_sum_raw,
            &[
                (neg_mfxd_plus_mgxd, neg_congr_rdfg),
                (neg_mfxd_neg_mgxd, step_b_split),
            ],
        );

        // Step C: `actual_error ~ intermediate`.
        let p1 = cadd(d, p, fy, gy);
        let fx_plus_gx = cadd(d, p, fx, gx);
        let neg_fx_plus_gx = cneg(d, p, fx_plus_gx);
        let neg_fx_neg_gx = cadd(d, p, neg_fx, neg_gx);
        let refl_p1 = erefl(d, p, p1);
        let fst_lift = d.lemma(
            p.add_congr,
            &[p1, p1, neg_fx_plus_gx, neg_fx_neg_gx, refl_p1, step_a_eq],
        ); // Equiv fy_fx_sum (add p1 (add (neg fx) (neg gx)))
        let intermediate_fst = cadd(d, p, p1, neg_fx_neg_gx);
        let intermediate = cadd(d, p, intermediate_fst, neg_mfxd_neg_mgxd);
        let step_c_eq = d.lemma(
            p.add_congr,
            &[
                fy_fx_sum,
                intermediate_fst,
                neg_deriv_sum_raw,
                neg_mfxd_neg_mgxd,
                fst_lift,
                step_b_eq,
            ],
        ); // Equiv actual_error intermediate

        // Step D: `add4_comm` on the first four terms.
        let (target1, proof1) = add4_comm(d, p, fy, gy, neg_fx, neg_gx);
        // target1 = add (add fy (neg fx)) (add gy (neg gx))
        let refl_neg_mfxd_neg_mgxd = erefl(d, p, neg_mfxd_neg_mgxd);
        let intermediate2_congr = d.lemma(
            p.add_congr,
            &[
                intermediate_fst,
                target1,
                neg_mfxd_neg_mgxd,
                neg_mfxd_neg_mgxd,
                proof1,
                refl_neg_mfxd_neg_mgxd,
            ],
        ); // Equiv intermediate (add target1 (add neg_mfxd neg_mgxd))

        // Step E: `add4_comm` again, on `target1`'s two halves against the
        // negated derivative terms — lands exactly on `add error_f error_g`.
        let a0 = cadd(d, p, fy, neg_fx);
        let b0 = cadd(d, p, gy, neg_gx);
        let (target2, proof2) = add4_comm(d, p, a0, b0, neg_mfxd, neg_mgxd);
        // target2 = add (add a0 neg_mfxd) (add b0 neg_mgxd) = add error_f error_g

        let target1_plus_neg_mfxd_neg_mgxd = cadd(d, p, target1, neg_mfxd_neg_mgxd);
        let ring_chain = echain(
            d,
            p,
            actual_error,
            &[
                (intermediate, step_c_eq),
                (target1_plus_neg_mfxd_neg_mgxd, intermediate2_congr),
                (target2, proof2),
            ],
        ); // Equiv actual_error combined_error (target2 == combined_error, definitionally)

        let conclusion = abs_le_of_equiv(
            d,
            p,
            actual_error,
            combined_error,
            out_bound,
            ring_chain,
            combined_error_bound,
        );

        let with_h = d.lam_fv(h_fv, hyp, conclusion);
        let with_hyb = d.lam_fv(hyb_fv, range_yb, with_h);
        let with_hay = d.lam_fv(hay_fv, range_ay, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_hay);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(e_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.hd_mk, &[fsum, fsum_p, a, b, modulus_sum, spec]);
    let value = {
        let with_hg = d.lam_fv(hg_fv, hg_ty, mk_applied);
        let with_hf = d.lam_fv(hf_fv, hf_ty, with_hg);
        let with_b = d.lam_fv(b_fv, carrier, with_hf);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_gp = d.lam_fv(gp_fv, func_ty, with_a);
        let with_g = d.lam_fv(g_fv, func_ty, with_gp);
        let with_fp = d.lam_fv(fp_fv, func_ty, with_g);
        d.lam_fv(f_fv, func_ty, with_fp)
    };
    let ty = {
        let applied = hd_ty(d, p, fsum, fsum_p, a, b);
        let with_hg = d.arrow(hg_ty, applied);
        let with_hf = d.arrow(hf_ty, with_hg);
        let with_b = d.pi_fv(b_fv, carrier, with_hf);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_gp = d.pi_fv(gp_fv, func_ty, with_a);
        let with_g = d.pi_fv(g_fv, func_ty, with_gp);
        let with_fp = d.pi_fv(fp_fv, func_ty, with_g);
        d.pi_fv(f_fv, func_ty, with_fp)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.has_derivative_add,
        uparams: vec![],
        ty,
        value,
    })
}
