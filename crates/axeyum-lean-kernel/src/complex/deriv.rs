//! **`Complex.HasDerivativeOn`** — complex differentiability on a disc, the
//! transcription of `creal/derivative.rs`'s real `CReal.HasDerivativeOn` one
//! carrier up.
//!
//! # The convention is the real shelf's, verbatim
//!
//! The brief for this module asked for "the ε–δ form the real shelf uses".
//! The real shelf's derivative is **not** a pointwise `HasDerivAt`: it is
//! Bishop's *uniform* differentiability on a closed interval, a
//! one-constructor inductive in `Type` whose first field is a modulus
//! `Nat → Nat` as **data** (`creal/derivative.rs`'s own module documentation
//! gives the reason at length: `0 < x` and its `Nat` witness are the same
//! proposition, yet the witness cannot be pulled out of an `Exists` and used
//! to build anything in `Type`). So this file mirrors *that*, and no
//! `Complex.HasDerivAt` is declared — a pointwise complex derivative stated
//! next to a uniform real one would make every future bridge between the two
//! shelves a conversion rather than a transcription.
//!
//! Everything is carried across position for position:
//!
//! | real (`CReal.HasDerivativeOn F F' a b`) | complex (`Complex.HasDerivativeOn F F' c r`) |
//! | --- | --- |
//! | `modulus : Nat → Nat` (data) | identical |
//! | four range hypotheses `le a x`, `le x b`, `le a y`, `le y b` | two, `InDisc c r x` and `InDisc c r y` |
//! | `le (CReal.abs (y − x)) (ofRat (1/(modulus e + 1)))` | `le (Complex.abs (y − x)) (ofRat (1/(modulus e + 1)))` |
//! | `le (CReal.abs (F y − F x − F' x · (y − x))) ((1/(e+1)) · CReal.abs (y − x))` | `le (Complex.abs (…)) ((1/(e+1)) · Complex.abs (y − x))` |
//!
//! The bound is a `CReal` on both sides, because [`ComplexPrelude::abs`] is
//! already `CReal`-valued. That is why the interval's *four* hypotheses
//! collapse to *two*: an interval is two inequalities per point, a disc is
//! one.
//!
//! # Why the disc is CLOSED
//!
//! `InDisc c r z := CReal.le (Complex.abs (z − c)) r` — `le`, not `lt`. The
//! real shelf's domain is the CLOSED interval `[a,b]`, and a uniform modulus
//! is exactly the notion that behaves on a compact domain; carrying `le`
//! across is the position-for-position mirror. A strict disc would also have
//! been sound, but it would have made `Complex.HasDerivativeOn` and
//! `CReal.HasDerivativeOn` differ in a way no lemma bridges, for no gain: a
//! statement about the open disc of radius `r` follows from the closed disc
//! of every smaller radius.
//!
//! # What the ℂ side gets for free that the ℝ side had to build
//!
//! `creal/derivative.rs` needed a from-scratch ring-algebra toolkit
//! (`neg_unique`, `diff_of_squares`, `mul_neg_equiv`, …) before its first
//! nonlinear witness would close, because every `CReal` identity there is an
//! *analytic* statement proved one at a time. Here `complex/ring.rs`'s
//! `ring_law_proof` already decides any commutative-ring identity between
//! `CExpr`s, so each witness's error-term identity is one call. The
//! *estimates* (`abs_add_le`, `abs_mul`, `mul_le_mul_of_nonneg_left`) are
//! what remains, and those are the same work on both carriers.
//!
//! Also cheaper here: the real closing step needed `close_zero_error`'s
//! two-sided `abs_le` split, because `CReal.abs` is a defined lattice
//! operation and a bound on it is two bounds. `Complex.abs` is
//! `sqrt (normSq ·)` and [`ComplexPrelude::abs_nonneg`] is already available,
//! so an `Equiv`-zero error closes through `abs_congr` + [`declare_abs_zero`]
//! + `le_of_equiv` + `le_trans` with no split at all.
//!
//! # Holomorphy is a `Sigma`, and that is forced
//!
//! `Complex.HolomorphicOn F c r` — "F has a derivative at every point of the
//! disc" — is `Σ (F' : Complex → Complex), HasDerivativeOn F F' c r`. It
//! cannot be an `Exists`, because `Exists`'s predicate must land in `Prop` and
//! `HasDerivativeOn` is in `Type 0` by the paragraph above. That is not a
//! limitation: the `Sigma` is the CONSTRUCTIVE statement, and every witness
//! below hands its derivative back through
//! [`declare_holomorphic_deriv`] (`Sigma.fst`) with the full ε–δ bound
//! recovered by [`declare_holomorphic_spec`] (`Sigma.snd`, the DEPENDENT
//! projection) — which is what a later Cauchy-integral argument needs and
//! what an `Exists` could not supply.
//!
//! # What is NOT here
//!
//! The product rule. Its error identity is one `ring_law_proof` call like
//! every other; what is missing is three ℂ-side ESTIMATES (a uniform bound on
//! `|G|`, one on `|F'|`, one on `|F|`) and a modulus of continuity for `G`.
//! `CReal.hasDerivative_mul` takes exactly those as `UniformlyContinuousOn`
//! plus two `Nat` witnesses, and neither `Complex.BoundedOn` nor
//! `Complex.UniformlyContinuousOn` exists. ADR-1642 sizes both routes and
//! recommends carrying the four bounds as hypotheses, because
//! [`ComplexPrelude::abs_mul`] is an exact `Equiv` where the real side needed
//! `abs_mul_le_of_bounds`. The derivative of `polyEval` is blocked behind
//! that and nothing else.

// Proof-term builders take the whole shape of the lemma they apply, so the
// argument counts follow the kernel's lemma signatures rather than any Rust
// convention.
#![allow(
    clippy::doc_markdown,
    clippy::large_types_passed_by_value,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use super::ring::{RExpr, render as rrender, ring_proof};
use super::{CExpr, ComplexPrelude, complex_ty, creal_ty, ring_law_proof};
use crate::CRealPrelude;
use crate::Kernel;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{nat_rewrite_prop, radd, rat_eq_rewrite};

/// The names [`declare_derivative`] declares, owned by this module rather than
/// by [`ComplexPrelude`] directly — the `poly.rs` arrangement (Part B of
/// `docs/research/11-design-review/2026-08-27-prelude-build-spike.md`), so a
/// new declaration inside this file never touches `complex.rs`'s struct,
/// `STEPS` table, or `intern_names`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DerivNames {
    /// `Complex.abs_zero : CReal.Equiv (Complex.abs Complex.zero) CReal.zero`.
    pub abs_zero: NameId,
    /// `Complex.InDisc (c : Complex) (r : CReal) (z : Complex) : Prop`.
    pub in_disc: NameId,
    /// `Complex.HasDerivativeOn (F F' : Complex → Complex) (c : Complex)
    /// (r : CReal) : Type`.
    pub has_derivative_on: NameId,
    /// The single constructor `Complex.HasDerivativeOn.mk`.
    pub hd_mk: NameId,
    /// The generated recursor `Complex.HasDerivativeOn.rec`.
    pub hd_rec: NameId,
    /// `Complex.HasDerivativeOn.modulus`.
    pub hd_modulus: NameId,
    /// `Complex.HasDerivativeOn.spec`.
    pub hd_spec: NameId,
    /// `Complex.hasDerivative_const`.
    pub has_derivative_const: NameId,
    /// `Complex.hasDerivative_id`.
    pub has_derivative_id: NameId,
    /// `Complex.hasDerivative_neg`.
    pub has_derivative_neg: NameId,
    /// `Complex.hasDerivative_add`.
    pub has_derivative_add: NameId,
    /// `Complex.HolomorphicOn F c r` -- a `Sigma` carrying the derivative.
    pub holomorphic_on: NameId,
    /// `Complex.holomorphicDeriv` -- `Sigma.fst`, the derivative a witness carries.
    pub holomorphic_deriv: NameId,
    /// `Complex.holomorphic_spec` -- `Sigma.snd`, the bound it satisfies.
    pub holomorphic_spec: NameId,
    /// `Complex.holomorphic_const`.
    pub holomorphic_const: NameId,
    /// `Complex.holomorphic_id`.
    pub holomorphic_id: NameId,
    /// `Complex.holomorphic_neg`.
    pub holomorphic_neg: NameId,
    /// `Complex.holomorphic_add`.
    pub holomorphic_add: NameId,
}

/// Interns this module's names under `complex` (e.g. `Complex.InDisc`).
/// Called once from `super::intern_names`.
pub(super) fn intern_names(kernel: &mut Kernel, complex: NameId) -> DerivNames {
    let has_derivative_on = kernel.name_str(complex, "HasDerivativeOn");
    DerivNames {
        abs_zero: kernel.name_str(complex, "abs_zero"),
        in_disc: kernel.name_str(complex, "InDisc"),
        has_derivative_on,
        hd_mk: kernel.name_str(has_derivative_on, "mk"),
        hd_rec: kernel.name_str(has_derivative_on, "rec"),
        hd_modulus: kernel.name_str(has_derivative_on, "modulus"),
        hd_spec: kernel.name_str(has_derivative_on, "spec"),
        has_derivative_const: kernel.name_str(complex, "hasDerivative_const"),
        has_derivative_id: kernel.name_str(complex, "hasDerivative_id"),
        has_derivative_neg: kernel.name_str(complex, "hasDerivative_neg"),
        has_derivative_add: kernel.name_str(complex, "hasDerivative_add"),
        holomorphic_on: kernel.name_str(complex, "HolomorphicOn"),
        holomorphic_deriv: kernel.name_str(complex, "holomorphicDeriv"),
        holomorphic_spec: kernel.name_str(complex, "holomorphic_spec"),
        holomorphic_const: kernel.name_str(complex, "holomorphic_const"),
        holomorphic_id: kernel.name_str(complex, "holomorphic_id"),
        holomorphic_neg: kernel.name_str(complex, "holomorphic_neg"),
        holomorphic_add: kernel.name_str(complex, "holomorphic_add"),
    }
}

/// Height for `Complex.InDisc`: its value embeds only
/// [`ComplexPrelude::abs`]/`add`/`neg` and `CReal.le`, every one of which is
/// declared before this module's step runs, so a margin above every height
/// `complex.rs` and `poly.rs` use is enough. `poly.rs`'s highest is
/// `super::DERIVED_HEIGHT + 15`.
const IN_DISC_HEIGHT: u16 = super::DERIVED_HEIGHT + 20;
/// Height for `Complex.HasDerivativeOn.modulus`: strictly above
/// [`IN_DISC_HEIGHT`], since the spec body it eliminates over mentions
/// `InDisc`.
const HD_MODULUS_HEIGHT: u16 = IN_DISC_HEIGHT + 1;
/// Height for `Complex.HolomorphicOn`: above [`HD_MODULUS_HEIGHT`], since its
/// value mentions `HasDerivativeOn` and everything below it.
const HOLOMORPHIC_HEIGHT: u16 = HD_MODULUS_HEIGHT + 2;
/// Height for `Complex.holomorphicDeriv`: strictly above
/// [`HOLOMORPHIC_HEIGHT`], whose unfolding its own argument type needs.
const HOLOMORPHIC_DERIV_HEIGHT: u16 = HOLOMORPHIC_HEIGHT + 1;

/// Declare `Complex.HasDerivativeOn` and everything this file proves about it.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_derivative(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    declare_abs_zero(d, p)?;
    declare_in_disc(d, p)?;
    declare_carrier(d, p)?;
    declare_projections(d, p)?;
    declare_has_derivative_const(d, p)?;
    declare_has_derivative_id(d, p)?;
    declare_has_derivative_neg(d, p)?;
    declare_has_derivative_add(d, p)?;
    declare_holomorphic_on(d, p)?;
    declare_holomorphic_deriv(d, p)?;
    declare_holomorphic_spec(d, p)?;
    declare_holomorphic_const(d, p)?;
    declare_holomorphic_id(d, p)?;
    declare_holomorphic_neg(d, p)?;
    declare_holomorphic_add(d, p)
}

// ---------------------------------------------------------------------------
// shared term builders
// ---------------------------------------------------------------------------

/// `Complex.add a b`.
pub(super) fn zadd(d: &mut IntDev<'_>, p: ComplexPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.add, &[a, b])
}

/// `Complex.neg a`.
pub(super) fn zneg(d: &mut IntDev<'_>, p: ComplexPrelude, a: ExprId) -> ExprId {
    d.const_app(p.neg, &[a])
}

/// `Complex.mul a b`.
pub(super) fn zmul(d: &mut IntDev<'_>, p: ComplexPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.mul, &[a, b])
}

/// `Complex.add a (Complex.neg b)` — `a − b`. There is no `Complex.sub` in
/// this development (see [`ComplexPrelude::sub_div`]'s field comment); this is
/// the convention `creal/derivative.rs`'s own `cdiff` follows one carrier
/// down.
pub(super) fn zsub(d: &mut IntDev<'_>, p: ComplexPrelude, a: ExprId, b: ExprId) -> ExprId {
    let nb = zneg(d, p, b);
    zadd(d, p, a, nb)
}

/// `Complex.zero`.
pub(super) fn zzero(d: &mut IntDev<'_>, p: ComplexPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

/// `Complex.abs a` — a `CReal`.
pub(super) fn zabs(d: &mut IntDev<'_>, p: ComplexPrelude, a: ExprId) -> ExprId {
    d.const_app(p.abs, &[a])
}

/// `Complex → Complex`.
pub(super) fn fn_ty(d: &mut IntDev<'_>, p: ComplexPrelude) -> ExprId {
    let carrier = complex_ty(d, p);
    d.arrow(carrier, carrier)
}

/// `Nat → Nat`.
pub(super) fn nat_fn_ty(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    d.arrow(nat, nat)
}

/// `CReal.ofRat (Rat.natDivSucc k j)` — `k/(j+1)` as a real, with a literal
/// numerator. `creal/derivative.rs`'s `div_succ` composed with its `of_rat`
/// application.
pub(super) fn of_div_succ(d: &mut IntDev<'_>, p: ComplexPrelude, k: u32, j: ExprId) -> ExprId {
    let creal = p.creal;
    let numerator = d.num(k);
    let q = d.const_app(creal.rat.nat_div_succ, &[numerator, j]);
    d.const_app(creal.of_rat, &[q])
}

/// `(term, proof)` = `(ofRat (natDivSucc k idx), CReal.le zero term)`, the
/// mirror of `creal/derivative.rs`'s own `nonneg_rat_bound`.
pub(super) fn nonneg_rat_bound(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    k: u32,
    idx: ExprId,
) -> (ExprId, ExprId) {
    let creal = p.creal;
    let numerator = d.num(k);
    let q = d.const_app(creal.rat.nat_div_succ, &[numerator, idx]);
    let ofr_q = d.const_app(creal.of_rat, &[q]);
    let rzero_expr = crate::rat_prelude::ops::rzero(d, creal.rat);
    let rat_nonneg = d.lemma(creal.rat.zero_le_nat_div_succ, &[numerator, idx]);
    let proof = d.lemma(creal.of_rat_le, &[rzero_expr, q, rat_nonneg]);
    (ofr_q, proof)
}

/// `(bound, proof)` = `((1/(e+1)) · Complex.abs diff, CReal.le zero bound)` —
/// the derivative spec's own target bound and its nonnegativity, the mirror of
/// `creal/derivative.rs`'s `error_bound` with [`ComplexPrelude::abs_nonneg`]
/// in place of `CReal.abs_nonneg`.
fn error_bound(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    e: ExprId,
    diff_yx: ExprId,
) -> (ExprId, ExprId) {
    let creal = p.creal;
    let (ofr_e, ofr_e_nonneg) = nonneg_rat_bound(d, p, 1, e);
    let abs_diff = zabs(d, p, diff_yx);
    let abs_diff_nonneg = d.lemma(p.abs_nonneg, &[diff_yx]);
    let bound = d.const_app(creal.mul, &[ofr_e, abs_diff]);
    let bound_nonneg = d.lemma(
        creal.mul_nonneg,
        &[ofr_e, abs_diff, ofr_e_nonneg, abs_diff_nonneg],
    );
    (bound, bound_nonneg)
}

/// `CReal.Equiv.trans` chained through `(next, step)` pairs — the `echain`
/// idiom (`creal/derivative.rs` has its own copy), at `CReal.Equiv`.
pub(super) fn rchain(
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

/// From `err_equiv_zero : Complex.Equiv err Complex.zero` and
/// `zero_le_bound : CReal.le CReal.zero bound`, derive
/// `CReal.le (Complex.abs err) bound`.
///
/// The ℂ analogue of `creal/derivative.rs`'s `close_zero_error`, and strictly
/// shorter: `Complex.abs` is `sqrt (normSq ·)` and therefore already
/// nonnegative, so there is no two-sided `abs_le` split —
/// [`ComplexPrelude::abs_congr`] carries the `Equiv` into the modulus,
/// [`declare_abs_zero`] evaluates it, and `le_of_equiv`/`le_trans` finish.
pub(super) fn close_zero_error(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    err: ExprId,
    bound: ExprId,
    err_equiv_zero: ExprId,
    zero_le_bound: ExprId,
) -> ExprId {
    let creal = p.creal;
    let zero_z = zzero(d, p);
    let abs_err = zabs(d, p, err);
    let abs_zero_z = zabs(d, p, zero_z);
    let rzero = d.kernel().const_(creal.zero, vec![]);

    // abs_err ~ abs zero ~ 0
    let step1 = d.lemma(p.abs_congr, &[err, zero_z, err_equiv_zero]);
    let step2 = d.kernel().const_(p.deriv.abs_zero, vec![]);
    let abs_err_zero = rchain(d, creal, abs_err, &[(abs_zero_z, step1), (rzero, step2)]);

    let le_abs_zero = d.lemma(creal.le_of_equiv, &[abs_err, rzero, abs_err_zero]);
    d.lemma(
        creal.le_trans,
        &[abs_err, rzero, bound, le_abs_zero, zero_le_bound],
    )
}

/// `Complex.InDisc c r z`.
pub(super) fn in_disc_ty(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    c: ExprId,
    r: ExprId,
    z: ExprId,
) -> ExprId {
    d.const_app(p.deriv.in_disc, &[c, r, z])
}

/// `Complex.HasDerivativeOn F F' c r`.
pub(super) fn hd_ty(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    f: ExprId,
    fp: ExprId,
    c: ExprId,
    r: ExprId,
) -> ExprId {
    d.const_app(p.deriv.has_derivative_on, &[f, fp, c, r])
}

/// `∀ (e : Nat) (x y : Complex), InDisc c r x → InDisc c r y →
///   CReal.le (abs (y − x)) (ofRat (1/(modulus e + 1))) →
///   CReal.le (abs ((F y − F x) − F' x · (y − x))) ((1/(e+1)) · abs (y − x))`.
///
/// Position for position `creal/derivative.rs`'s `deriv_spec_body`, with the
/// four interval hypotheses replaced by two disc memberships and `CReal.abs`
/// by [`ComplexPrelude::abs`].
pub(super) fn deriv_spec_body(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    f: ExprId,
    fp: ExprId,
    c: ExprId,
    r: ExprId,
    modulus: ExprId,
) -> ExprId {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();

    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let disc_x = in_disc_ty(d, p, c, r, x);
    let disc_y = in_disc_ty(d, p, c, r, y);

    let diff_yx = zsub(d, p, y, x);
    let abs_diff = zabs(d, p, diff_yx);

    let mod_e = d.apply(modulus, &[e]);
    let in_bound = of_div_succ(d, p, 1, mod_e);
    let hyp = d.const_app(creal.le, &[abs_diff, in_bound]);

    let fx = d.apply(f, &[x]);
    let fy = d.apply(f, &[y]);
    let fpx = d.apply(fp, &[x]);
    let deriv_term = zmul(d, p, fpx, diff_yx);
    let fy_fx = zsub(d, p, fy, fx);
    let error = zsub(d, p, fy_fx, deriv_term);
    let abs_error = zabs(d, p, error);

    let ofr_out = of_div_succ(d, p, 1, e);
    let out_bound = d.const_app(creal.mul, &[ofr_out, abs_diff]);
    let conclusion = d.const_app(creal.le, &[abs_error, out_bound]);

    let body = d.arrow(hyp, conclusion);
    let with_dy = d.arrow(disc_y, body);
    let with_dx = d.arrow(disc_x, with_dy);
    let with_y = d.pi_fv(y_fv, carrier, with_dx);
    let with_x = d.pi_fv(x_fv, carrier, with_y);
    d.pi_fv(e_fv, nat, with_x)
}

// ---------------------------------------------------------------------------
// declarations
// ---------------------------------------------------------------------------

/// `Complex.abs_zero : CReal.Equiv (Complex.abs Complex.zero) CReal.zero`.
///
/// `normSq zero` δι-unfolds to `0·0 + 0·0`, which [`ring_proof`] equates with
/// `CReal.zero`; `CReal.sqrt_congr` carries that under the root and
/// `CReal.sqrt_zero` finishes. Exactly the route `super::declare_abs_one`
/// takes for `abs one` — which existed, while this did not.
fn declare_abs_zero(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let rzero = d.kernel().const_(creal.zero, vec![]);

    // `normSq zero` unfolds to `add (mul zero zero) (mul zero zero)`.
    let lit = RExpr::add(
        RExpr::mul(RExpr::Zero, RExpr::Zero),
        RExpr::mul(RExpr::Zero, RExpr::Zero),
    );
    let lit_term = rrender(d, creal, &lit);
    let lit_zero = ring_proof(d, creal, &lit, &RExpr::Zero);

    let sqrt_lit = d.const_app(creal.sqrt, &[lit_term]);
    let sqrt_zero_term = d.const_app(creal.sqrt, &[rzero]);
    let step1 = d.lemma(creal.sqrt_congr, &[lit_term, rzero, lit_zero]);
    let step2 = d.kernel().const_(creal.sqrt_zero, vec![]);
    let value = rchain(
        d,
        creal,
        sqrt_lit,
        &[(sqrt_zero_term, step1), (rzero, step2)],
    );

    let ty = {
        let zero_z = zzero(d, p);
        let abs_zero_z = zabs(d, p, zero_z);
        d.const_app(creal.equiv, &[abs_zero_z, rzero])
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.deriv.abs_zero,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.InDisc (c : Complex) (r : CReal) (z : Complex) : Prop :=
///   CReal.le (Complex.abs (z − c)) r` — the CLOSED disc of centre `c` and
/// radius `r`. See the module documentation for why `le` and not `lt`.
fn declare_in_disc(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);
    let zero_level = d.kernel().level_zero();
    let prop = d.kernel().sort(zero_level);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);

    let diff = zsub(d, p, z, c);
    let abs_diff = zabs(d, p, diff);
    let body = d.const_app(creal.le, &[abs_diff, r]);

    let value = {
        let with_z = d.lam_fv(z_fv, carrier, body);
        let with_r = d.lam_fv(r_fv, real, with_z);
        d.lam_fv(c_fv, carrier, with_r)
    };
    let ty = {
        let with_z = d.arrow(carrier, prop);
        let with_r = d.pi_fv(r_fv, real, with_z);
        d.pi_fv(c_fv, carrier, with_r)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.deriv.in_disc,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(IN_DISC_HEIGHT),
    })
}

/// `Complex.HasDerivativeOn (F F' : Complex → Complex) (c : Complex)
/// (r : CReal) : Type := mk (modulus : Nat → Nat) (spec : …)`.
///
/// Four leading parameters, exactly `CReal.HasDerivativeOn`'s arity; the
/// modulus is data for the reason that file's module documentation gives.
fn declare_carrier(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat_fn = nat_fn_ty(d);
    let one = d.level_one();
    let type0 = d.kernel().sort(one);

    // ty := Π (F F' : Complex→Complex) (c : Complex) (r : CReal), Type 0.
    let ty = {
        let f_fv = d.fresh_fvar();
        let fp_fv = d.fresh_fvar();
        let c_fv = d.fresh_fvar();
        let r_fv = d.fresh_fvar();
        let with_r = d.pi_fv(r_fv, real, type0);
        let with_c = d.pi_fv(c_fv, carrier, with_r);
        let with_fp = d.pi_fv(fp_fv, func_ty, with_c);
        d.pi_fv(f_fv, func_ty, with_fp)
    };

    let mk_ty = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let fp_fv = d.fresh_fvar();
        let fp = d.kernel().fvar(fp_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let mod_fv = d.fresh_fvar();
        let modulus = d.kernel().fvar(mod_fv);

        let spec_ty = deriv_spec_body(d, p, f, fp, c, r, modulus);
        let result = hd_ty(d, p, f, fp, c, r);

        let with_spec = d.arrow(spec_ty, result);
        let with_mod = d.pi_fv(mod_fv, nat_fn, with_spec);
        let with_r = d.pi_fv(r_fv, real, with_mod);
        let with_c = d.pi_fv(c_fv, carrier, with_r);
        let with_fp = d.pi_fv(fp_fv, func_ty, with_c);
        d.pi_fv(f_fv, func_ty, with_fp)
    };

    d.kernel().add_inductive(
        p.deriv.has_derivative_on,
        &[],
        4,
        ty,
        &[(p.deriv.hd_mk, mk_ty)],
    )
}

/// The two projections: `modulus` (large elimination into `Type 0`, a
/// `Definition`) and `spec` (into `Prop`, a `Theorem`, motive at a witness `u`
/// reading `u`'s own modulus) — `creal/derivative.rs::declare_projections`'s
/// shape verbatim, one parameter list over.
fn declare_projections(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat_fn = nat_fn_ty(d);
    let one = d.level_one();
    let zero_level = d.kernel().level_zero();
    let anon = d.anon_name();

    // modulus : ∀ F F' c r, HasDerivativeOn F F' c r → Nat → Nat
    //   := fun F F' c r u => HasDerivativeOn.rec F F' c r (fun _ => Nat → Nat)
    //        (fun modulus _ => modulus) u.
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let fp_fv = d.fresh_fvar();
        let fp = d.kernel().fvar(fp_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let carrier_hd = hd_ty(d, p, f, fp, c, r);

        let motive = d
            .kernel()
            .lam(anon, carrier_hd, nat_fn, crate::BinderInfo::Default);
        let minor = {
            let mod_fv = d.fresh_fvar();
            let modulus = d.kernel().fvar(mod_fv);
            let spec_ty = deriv_spec_body(d, p, f, fp, c, r, modulus);
            let inner = d
                .kernel()
                .lam(anon, spec_ty, modulus, crate::BinderInfo::Default);
            d.lam_fv(mod_fv, nat_fn, inner)
        };

        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let rec = d.kernel().const_(p.deriv.hd_rec, vec![one]);
        let body = d.apply(rec, &[f, fp, c, r, motive, minor, u]);
        let value = {
            let with_u = d.lam_fv(u_fv, carrier_hd, body);
            let with_r = d.lam_fv(r_fv, real, with_u);
            let with_c = d.lam_fv(c_fv, carrier, with_r);
            let with_fp = d.lam_fv(fp_fv, func_ty, with_c);
            d.lam_fv(f_fv, func_ty, with_fp)
        };
        let ty = {
            let with_u = d.arrow(carrier_hd, nat_fn);
            let with_r = d.pi_fv(r_fv, real, with_u);
            let with_c = d.pi_fv(c_fv, carrier, with_r);
            let with_fp = d.pi_fv(fp_fv, func_ty, with_c);
            d.pi_fv(f_fv, func_ty, with_fp)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.deriv.hd_modulus,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(HD_MODULUS_HEIGHT),
        })?;
    }

    // spec : ∀ F F' c r (u : HasDerivativeOn F F' c r),
    //   deriv_spec_body F F' c r (HasDerivativeOn.modulus F F' c r u)
    //   := fun F F' c r u => HasDerivativeOn.rec F F' c r
    //        (fun w => deriv_spec_body F F' c r (modulus F F' c r w))
    //        (fun modulus spec => spec) u.
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let fp_fv = d.fresh_fvar();
        let fp = d.kernel().fvar(fp_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let carrier_hd = hd_ty(d, p, f, fp, c, r);

        let claim = |d: &mut IntDev<'_>, w: ExprId| {
            let mod_of_w = d.const_app(p.deriv.hd_modulus, &[f, fp, c, r, w]);
            deriv_spec_body(d, p, f, fp, c, r, mod_of_w)
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
            let spec_ty = deriv_spec_body(d, p, f, fp, c, r, modulus);
            let spec_fv = d.fresh_fvar();
            let spec_var = d.kernel().fvar(spec_fv);
            let inner = d.lam_fv(spec_fv, spec_ty, spec_var);
            d.lam_fv(mod_fv, nat_fn, inner)
        };

        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let rec = d.kernel().const_(p.deriv.hd_rec, vec![zero_level]);
        let body = d.apply(rec, &[f, fp, c, r, motive, minor, u]);
        let value = {
            let with_u = d.lam_fv(u_fv, carrier_hd, body);
            let with_r = d.lam_fv(r_fv, real, with_u);
            let with_c = d.lam_fv(c_fv, carrier, with_r);
            let with_fp = d.lam_fv(fp_fv, func_ty, with_c);
            d.lam_fv(f_fv, func_ty, with_fp)
        };
        let ty = {
            let inner = claim(d, u);
            let with_u = d.pi_fv(u_fv, carrier_hd, inner);
            let with_r = d.pi_fv(r_fv, real, with_u);
            let with_c = d.pi_fv(c_fv, carrier, with_r);
            let with_fp = d.pi_fv(fp_fv, func_ty, with_c);
            d.pi_fv(f_fv, func_ty, with_fp)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.deriv.hd_spec,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `Complex.hasDerivative_const : ∀ (k c : Complex) (r : CReal),
/// HasDerivativeOn (fun _ => k) (fun _ => zero) c r`.
///
/// The cheapest witness: the error term is `(k − k) − 0·(y − x)`,
/// `Complex.Equiv`-zero regardless of the hypothesis, so any modulus works
/// (`fun _ => 0` is used). On the real side that identity needed a hand-built
/// `const_error_equiv_zero`; here it is one `ring_law_proof` call.
fn declare_has_derivative_const(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);
    let nat = d.nat_ty();

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let const_fn = {
        let ignore_fv = d.fresh_fvar();
        d.lam_fv(ignore_fv, carrier, k)
    };
    let zero_z = zzero(d, p);
    let zero_fn = {
        let ignore_fv = d.fresh_fvar();
        d.lam_fv(ignore_fv, carrier, zero_z)
    };
    let modulus = {
        let ignore_fv = d.fresh_fvar();
        let z = d.num(0);
        d.lam_fv(ignore_fv, nat, z)
    };

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let spec = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hdx_fv = d.fresh_fvar();
        let hdy_fv = d.fresh_fvar();
        let h_fv = d.fresh_fvar();

        let disc_x = in_disc_ty(d, p, c, r, x);
        let disc_y = in_disc_ty(d, p, c, r, y);

        let diff_yx = zsub(d, p, y, x);
        let abs_diff = zabs(d, p, diff_yx);
        let mod_e = d.apply(modulus, &[e]);
        let in_bound = of_div_succ(d, p, 1, mod_e);
        let hyp = d.const_app(creal.le, &[abs_diff, in_bound]);

        // error := (k − k) − 0 · (y − x)
        let kk = zsub(d, p, k, k);
        let scaled = zmul(d, p, zero_z, diff_yx);
        let error = zsub(d, p, kk, scaled);

        let k_sym = CExpr::var(d, p, k);
        let y_sym = CExpr::var(d, p, y);
        let x_sym = CExpr::var(d, p, x);
        let diff_sym = CExpr::add(y_sym, CExpr::neg(x_sym));
        let error_sym = CExpr::add(
            CExpr::add(k_sym.clone(), CExpr::neg(k_sym)),
            CExpr::neg(CExpr::mul(CExpr::Zero, diff_sym)),
        );
        let error_equiv_zero = ring_law_proof(d, p, &error_sym, &CExpr::Zero);

        let (bound, bound_nonneg) = error_bound(d, p, e, diff_yx);
        let conclusion = close_zero_error(d, p, error, bound, error_equiv_zero, bound_nonneg);

        let with_h = d.lam_fv(h_fv, hyp, conclusion);
        let with_dy = d.lam_fv(hdy_fv, disc_y, with_h);
        let with_dx = d.lam_fv(hdx_fv, disc_x, with_dy);
        let with_y = d.lam_fv(y_fv, carrier, with_dx);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(e_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.deriv.hd_mk, &[const_fn, zero_fn, c, r, modulus, spec]);
    let value = {
        let with_r = d.lam_fv(r_fv, real, mk_applied);
        let with_c = d.lam_fv(c_fv, carrier, with_r);
        d.lam_fv(k_fv, carrier, with_c)
    };
    let ty = {
        let applied = hd_ty(d, p, const_fn, zero_fn, c, r);
        let with_r = d.pi_fv(r_fv, real, applied);
        let with_c = d.pi_fv(c_fv, carrier, with_r);
        d.pi_fv(k_fv, carrier, with_c)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.deriv.has_derivative_const,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.hasDerivative_id : ∀ (c : Complex) (r : CReal),
/// HasDerivativeOn (fun z => z) (fun _ => one) c r`.
///
/// Error term `(y − x) − 1·(y − x)`, again `Equiv`-zero unconditionally and
/// again one `ring_law_proof` call.
fn declare_has_derivative_id(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);
    let nat = d.nat_ty();

    let id_fn = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        d.lam_fv(z_fv, carrier, z)
    };
    let one_z = d.kernel().const_(p.one, vec![]);
    let one_fn = {
        let ignore_fv = d.fresh_fvar();
        d.lam_fv(ignore_fv, carrier, one_z)
    };
    let modulus = {
        let ignore_fv = d.fresh_fvar();
        let z = d.num(0);
        d.lam_fv(ignore_fv, nat, z)
    };

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let spec = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hdx_fv = d.fresh_fvar();
        let hdy_fv = d.fresh_fvar();
        let h_fv = d.fresh_fvar();

        let disc_x = in_disc_ty(d, p, c, r, x);
        let disc_y = in_disc_ty(d, p, c, r, y);

        let diff_yx = zsub(d, p, y, x);
        let abs_diff = zabs(d, p, diff_yx);
        let mod_e = d.apply(modulus, &[e]);
        let in_bound = of_div_succ(d, p, 1, mod_e);
        let hyp = d.const_app(creal.le, &[abs_diff, in_bound]);

        let scaled = zmul(d, p, one_z, diff_yx);
        let error = zsub(d, p, diff_yx, scaled);

        let y_sym = CExpr::var(d, p, y);
        let x_sym = CExpr::var(d, p, x);
        let diff_sym = CExpr::add(y_sym, CExpr::neg(x_sym));
        let error_sym = CExpr::add(
            diff_sym.clone(),
            CExpr::neg(CExpr::mul(CExpr::One, diff_sym)),
        );
        let error_equiv_zero = ring_law_proof(d, p, &error_sym, &CExpr::Zero);

        let (bound, bound_nonneg) = error_bound(d, p, e, diff_yx);
        let conclusion = close_zero_error(d, p, error, bound, error_equiv_zero, bound_nonneg);

        let with_h = d.lam_fv(h_fv, hyp, conclusion);
        let with_dy = d.lam_fv(hdy_fv, disc_y, with_h);
        let with_dx = d.lam_fv(hdx_fv, disc_x, with_dy);
        let with_y = d.lam_fv(y_fv, carrier, with_dx);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(e_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.deriv.hd_mk, &[id_fn, one_fn, c, r, modulus, spec]);
    let value = {
        let with_r = d.lam_fv(r_fv, real, mk_applied);
        d.lam_fv(c_fv, carrier, with_r)
    };
    let ty = {
        let applied = hd_ty(d, p, id_fn, one_fn, c, r);
        let with_r = d.pi_fv(r_fv, real, applied);
        d.pi_fv(c_fv, carrier, with_r)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.deriv.has_derivative_id,
        uparams: vec![],
        ty,
        value,
    })
}

/// From `h : Complex.Equiv a b` and `hb : CReal.le (Complex.abs b) bound`,
/// derive `CReal.le (Complex.abs a) bound` — the mirror of
/// `creal/derivative.rs`'s own `abs_le_of_equiv`, with
/// [`ComplexPrelude::abs_congr`] doing the transport `CReal.abs_congr` does
/// there.
pub(super) fn abs_le_of_equiv(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    a: ExprId,
    b: ExprId,
    bound: ExprId,
    h: ExprId,
    hb: ExprId,
) -> ExprId {
    let creal = p.creal;
    let abs_a = zabs(d, p, a);
    let abs_b = zabs(d, p, b);
    let eq = d.lemma(p.abs_congr, &[a, b, h]);
    let eq_sym = d.lemma(creal.equiv_symm, &[abs_a, abs_b, eq]);
    let refl_bound = d.lemma(creal.equiv_refl, &[bound]);
    d.lemma(
        creal.le_congr,
        &[abs_b, abs_a, bound, bound, eq_sym, refl_bound, hb],
    )
}

/// The symbolic error term `(F y − F x) − F' x · (y − x)` as a [`CExpr`] over
/// the five atoms, built once because every witness below states its own error
/// term against it.
pub(super) fn error_sym(fy: CExpr, fx: CExpr, fpx: CExpr, diff: CExpr) -> CExpr {
    CExpr::add(
        CExpr::add(fy, CExpr::neg(fx)),
        CExpr::neg(CExpr::mul(fpx, diff)),
    )
}

/// `Complex.hasDerivative_neg : ∀ F F' c r, HasDerivativeOn F F' c r →
/// HasDerivativeOn (fun z => neg (F z)) (fun z => neg (F' z)) c r`.
///
/// `neg`'s scaling factor is exactly `−1`, so the negated function's error at
/// accuracy `e` is **exactly** `neg` of `F`'s own error at the SAME `e` — no
/// rescaled modulus, hence no antitonicity and no index arithmetic at all
/// (`creal/derivative.rs`'s own `hasDerivative_neg` makes the same
/// observation). The modulus is `F`'s, verbatim, and the only two facts
/// needed are the ring identity (one `ring_law_proof`) and
/// [`ComplexPrelude::abs_neg`].
fn declare_has_derivative_neg(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let fp_fv = d.fresh_fvar();
    let fp = d.kernel().fvar(fp_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let hf_ty = hd_ty(d, p, f, fp, c, r);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);

    let neg_f = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let fz = d.apply(f, &[z]);
        let body = zneg(d, p, fz);
        d.lam_fv(z_fv, carrier, body)
    };
    let neg_fp = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let fpz = d.apply(fp, &[z]);
        let body = zneg(d, p, fpz);
        d.lam_fv(z_fv, carrier, body)
    };
    let modulus = d.const_app(p.deriv.hd_modulus, &[f, fp, c, r, hf]);

    let spec = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hdx_fv = d.fresh_fvar();
        let hdx = d.kernel().fvar(hdx_fv);
        let hdy_fv = d.fresh_fvar();
        let hdy = d.kernel().fvar(hdy_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let disc_x = in_disc_ty(d, p, c, r, x);
        let disc_y = in_disc_ty(d, p, c, r, y);

        let diff_yx = zsub(d, p, y, x);
        let abs_diff = zabs(d, p, diff_yx);
        let mod_e = d.apply(modulus, &[e]);
        let in_bound = of_div_succ(d, p, 1, mod_e);
        let hyp = d.const_app(creal.le, &[abs_diff, in_bound]);

        // `F`'s own error and bound, at the SAME accuracy `e` and the SAME
        // hypothesis `h` (the negated modulus IS `F`'s, so `h` fits verbatim).
        let fx = d.apply(f, &[x]);
        let fy = d.apply(f, &[y]);
        let fpx = d.apply(fp, &[x]);
        let deriv_term = zmul(d, p, fpx, diff_yx);
        let fy_fx = zsub(d, p, fy, fx);
        let error_f = zsub(d, p, fy_fx, deriv_term);
        let error_f_bound = d.lemma(p.deriv.hd_spec, &[f, fp, c, r, hf, e, x, y, hdx, hdy, h]);

        let ofr_out = of_div_succ(d, p, 1, e);
        let out_bound = d.const_app(creal.mul, &[ofr_out, abs_diff]);

        // `le (abs (neg error_f)) out_bound`, by `abs_neg`.
        let neg_error_f = zneg(d, p, error_f);
        let abs_error_f = zabs(d, p, error_f);
        let abs_neg_error_f = zabs(d, p, neg_error_f);
        let abs_neg_eq = d.lemma(p.abs_neg, &[error_f]);
        let abs_neg_sym = d.lemma(
            creal.equiv_symm,
            &[abs_neg_error_f, abs_error_f, abs_neg_eq],
        );
        let refl_out = d.lemma(creal.equiv_refl, &[out_bound]);
        let neg_bound = d.lemma(
            creal.le_congr,
            &[
                abs_error_f,
                abs_neg_error_f,
                out_bound,
                out_bound,
                abs_neg_sym,
                refl_out,
                error_f_bound,
            ],
        );

        // The actual error term IS `neg` of `F`'s, exactly.
        let neg_fy = d.apply(neg_f, &[y]);
        let neg_fx_applied = d.apply(neg_f, &[x]);
        let neg_fpx = d.apply(neg_fp, &[x]);
        let deriv_term_neg = zmul(d, p, neg_fpx, diff_yx);
        let fy_fx_neg = zsub(d, p, neg_fy, neg_fx_applied);
        let actual_error = zsub(d, p, fy_fx_neg, deriv_term_neg);

        let fy_sym = CExpr::var(d, p, fy);
        let fx_sym = CExpr::var(d, p, fx);
        let fpx_sym = CExpr::var(d, p, fpx);
        let y_sym = CExpr::var(d, p, y);
        let x_sym = CExpr::var(d, p, x);
        let diff_sym = CExpr::add(y_sym, CExpr::neg(x_sym));
        let ef_sym = error_sym(
            fy_sym.clone(),
            fx_sym.clone(),
            fpx_sym.clone(),
            diff_sym.clone(),
        );
        let actual_sym = error_sym(
            CExpr::neg(fy_sym),
            CExpr::neg(fx_sym),
            CExpr::neg(fpx_sym),
            diff_sym,
        );
        let ring = ring_law_proof(d, p, &actual_sym, &CExpr::neg(ef_sym));

        let conclusion =
            abs_le_of_equiv(d, p, actual_error, neg_error_f, out_bound, ring, neg_bound);

        let with_h = d.lam_fv(h_fv, hyp, conclusion);
        let with_dy = d.lam_fv(hdy_fv, disc_y, with_h);
        let with_dx = d.lam_fv(hdx_fv, disc_x, with_dy);
        let with_y = d.lam_fv(y_fv, carrier, with_dx);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(e_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.deriv.hd_mk, &[neg_f, neg_fp, c, r, modulus, spec]);
    let value = {
        let with_hf = d.lam_fv(hf_fv, hf_ty, mk_applied);
        let with_r = d.lam_fv(r_fv, real, with_hf);
        let with_c = d.lam_fv(c_fv, carrier, with_r);
        let with_fp = d.lam_fv(fp_fv, func_ty, with_c);
        d.lam_fv(f_fv, func_ty, with_fp)
    };
    let ty = {
        let applied = hd_ty(d, p, neg_f, neg_fp, c, r);
        let with_hf = d.arrow(hf_ty, applied);
        let with_r = d.pi_fv(r_fv, real, with_hf);
        let with_c = d.pi_fv(c_fv, carrier, with_r);
        let with_fp = d.pi_fv(fp_fv, func_ty, with_c);
        d.pi_fv(f_fv, func_ty, with_fp)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.deriv.has_derivative_neg,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.hasDerivative_add : ∀ F F' G G' c r, HasDerivativeOn F F' c r →
/// HasDerivativeOn G G' c r →
/// HasDerivativeOn (fun z => add (F z) (G z)) (fun z => add (F' z) (G' z)) c r`.
///
/// The combined modulus is `mSum e := mF (2e+1) + mG (2e+1)`, and reading both
/// hypotheses out of the single `mSum` one is exactly where the real proof
/// needed [`crate::RatPrelude::nat_div_succ_antitone`] — used here identically,
/// at the two `Nat` indices `mF (2e+1)` and `mSum e`. The two `1/(2e+2)`
/// bounds fuse to `1/(e+1)` through
/// [`crate::RatPrelude::nat_div_succ_add`] and
/// [`crate::RatPrelude::nat_div_succ_halve`], again verbatim from the real
/// proof.
///
/// What is NOT verbatim is the last step. `creal/derivative.rs` spends the
/// eighty-seven lines from its `// Step A` to the closing `echain`
/// (`creal/derivative.rs:3110-3196`) and five named helpers
/// (`neg_add_distrib`, `right_distrib` and `add4_comm`, each used twice, plus
/// `echain` and `erefl`) showing that the sum's error term IS the sum of the
/// two errors. Here that is one `ring_law_proof` call, because
/// `complex/ring.rs` decides commutative-ring identities.
fn declare_has_derivative_add(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);
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
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let hf_ty = hd_ty(d, p, f, fp, c, r);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);
    let hg_ty = hd_ty(d, p, g, gp, c, r);
    let hg_fv = d.fresh_fvar();
    let hg = d.kernel().fvar(hg_fv);

    let fsum = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let fz = d.apply(f, &[z]);
        let gz = d.apply(g, &[z]);
        let body = zadd(d, p, fz, gz);
        d.lam_fv(z_fv, carrier, body)
    };
    let fsum_p = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let fpz = d.apply(fp, &[z]);
        let gpz = d.apply(gp, &[z]);
        let body = zadd(d, p, fpz, gpz);
        d.lam_fv(z_fv, carrier, body)
    };
    let mf = d.const_app(p.deriv.hd_modulus, &[f, fp, c, r, hf]);
    let mg = d.const_app(p.deriv.hd_modulus, &[g, gp, c, r, hg]);
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
        let hdx_fv = d.fresh_fvar();
        let hdx = d.kernel().fvar(hdx_fv);
        let hdy_fv = d.fresh_fvar();
        let hdy = d.kernel().fvar(hdy_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let disc_x = in_disc_ty(d, p, c, r, x);
        let disc_y = in_disc_ty(d, p, c, r, y);

        let diff_yx = zsub(d, p, y, x);
        let abs_diff = zabs(d, p, diff_yx);
        let mod_e = d.apply(modulus_sum, &[e]);
        let in_bound = of_div_succ(d, p, 1, mod_e);
        let hyp = d.const_app(creal.le, &[abs_diff, in_bound]);

        // --- the index/modulus arithmetic ---------------------------------
        let two = d.num(2);
        let two_e = d.mul(two, e);
        let e_prime = d.succ(two_e);
        let mf_e2 = d.apply(mf, &[e_prime]);
        let mg_e2 = d.apply(mg, &[e_prime]);
        let modulus_sum_e = d.add(mf_e2, mg_e2);
        let mg_plus_mf = d.add(mg_e2, mf_e2);

        let nat_p = creal.rat.int.nat;
        let h_le_f = d.lemma(nat_p.le_add_right, &[mf_e2, mg_e2]);
        let raw_g = d.lemma(nat_p.le_add_right, &[mg_e2, mf_e2]);
        let comm_eq = d.lemma(nat_p.add_comm, &[mg_e2, mf_e2]);
        let h_le_g = nat_rewrite_prop(d, mg_plus_mf, modulus_sum_e, comm_eq, raw_g, &|d, t| {
            d.le(mg_e2, t)
        });

        let one_nat = d.num(1);
        let r_f = d.const_app(creal.rat.nat_div_succ, &[one_nat, mf_e2]);
        let r_g = d.const_app(creal.rat.nat_div_succ, &[one_nat, mg_e2]);
        let r_sum = d.const_app(creal.rat.nat_div_succ, &[one_nat, modulus_sum_e]);
        let rat_f = d.lemma(
            creal.rat.nat_div_succ_antitone,
            &[mf_e2, modulus_sum_e, h_le_f],
        );
        let rat_g = d.lemma(
            creal.rat.nat_div_succ_antitone,
            &[mg_e2, modulus_sum_e, h_le_g],
        );

        let ofr_sum = d.const_app(creal.of_rat, &[r_sum]);
        let ofr_f = d.const_app(creal.of_rat, &[r_f]);
        let ofr_g = d.const_app(creal.of_rat, &[r_g]);
        let creal_f = d.lemma(creal.of_rat_le, &[r_sum, r_f, rat_f]);
        let creal_g = d.lemma(creal.of_rat_le, &[r_sum, r_g, rat_g]);

        let hyp_f = d.lemma(creal.le_trans, &[abs_diff, ofr_sum, ofr_f, h, creal_f]);
        let hyp_g = d.lemma(creal.le_trans, &[abs_diff, ofr_sum, ofr_g, h, creal_g]);

        // --- F's and G's own error terms and bounds, at accuracy `2e+1` ----
        let fx = d.apply(f, &[x]);
        let fy = d.apply(f, &[y]);
        let fpx = d.apply(fp, &[x]);
        let gx = d.apply(g, &[x]);
        let gy = d.apply(g, &[y]);
        let gpx = d.apply(gp, &[x]);

        let mfxd = zmul(d, p, fpx, diff_yx);
        let mgxd = zmul(d, p, gpx, diff_yx);
        let fy_fx = zsub(d, p, fy, fx);
        let gy_gx = zsub(d, p, gy, gx);
        let error_f = zsub(d, p, fy_fx, mfxd);
        let error_g = zsub(d, p, gy_gx, mgxd);

        let error_f_bound = d.lemma(
            p.deriv.hd_spec,
            &[f, fp, c, r, hf, e_prime, x, y, hdx, hdy, hyp_f],
        );
        let error_g_bound = d.lemma(
            p.deriv.hd_spec,
            &[g, gp, c, r, hg, e_prime, x, y, hdx, hdy, hyp_g],
        );

        let r_prime = d.const_app(creal.rat.nat_div_succ, &[one_nat, e_prime]);
        let q_prime = d.const_app(creal.of_rat, &[r_prime]);
        let q_bound = d.const_app(creal.mul, &[q_prime, abs_diff]);

        // --- combine the two bounds via the triangle inequality ------------
        let combined_error = zadd(d, p, error_f, error_g);
        let abs_error_f = zabs(d, p, error_f);
        let abs_error_g = zabs(d, p, error_g);
        let triangle = d.lemma(p.abs_add_le, &[error_f, error_g]);
        let sum_bounds = d.lemma(
            creal.add_le_add,
            &[
                abs_error_f,
                q_bound,
                abs_error_g,
                q_bound,
                error_f_bound,
                error_g_bound,
            ],
        );
        let abs_combined_error = zabs(d, p, combined_error);
        let abs_sum = d.const_app(creal.add, &[abs_error_f, abs_error_g]);
        let q_bound_twice = d.const_app(creal.add, &[q_bound, q_bound]);
        let combined_le = d.lemma(
            creal.le_trans,
            &[
                abs_combined_error,
                abs_sum,
                q_bound_twice,
                triangle,
                sum_bounds,
            ],
        );

        // --- fuse `q_bound + q_bound` down to the single target bound ------
        let out_bound_rat = d.const_app(creal.rat.nat_div_succ, &[one_nat, e]);
        let ofr_out = d.const_app(creal.of_rat, &[out_bound_rat]);
        let out_bound = d.const_app(creal.mul, &[ofr_out, abs_diff]);

        let of_rat_add_proof = d.lemma(creal.of_rat_add, &[r_prime, r_prime]);
        let eq1 = d.lemma(creal.rat.nat_div_succ_add, &[one_nat, one_nat, e_prime]);
        let two_nat = d.num(2);
        let two_e_prime = d.const_app(creal.rat.nat_div_succ, &[two_nat, e_prime]);
        let radd_r_prime = radd(d, r_prime, r_prime);
        let q_prime_twice = d.const_app(creal.add, &[q_prime, q_prime]);
        let step_a = rat_eq_rewrite(
            d,
            radd_r_prime,
            two_e_prime,
            eq1,
            of_rat_add_proof,
            &|d, t| {
                let oft = d.const_app(creal.of_rat, &[t]);
                d.const_app(creal.equiv, &[q_prime_twice, oft])
            },
        );
        let eq2 = d.lemma(creal.rat.nat_div_succ_halve, &[e]);
        let sum_equiv_target_rat =
            rat_eq_rewrite(d, two_e_prime, out_bound_rat, eq2, step_a, &|d, t| {
                let oft = d.const_app(creal.of_rat, &[t]);
                d.const_app(creal.equiv, &[q_prime_twice, oft])
            });

        // `(q' + q') · |y − x| ~ q'·|y − x| + q'·|y − x|` — decided by the
        // `CReal` ring calculus rather than by a hand-built `right_distrib`.
        let q_sym = RExpr::Atom(q_prime);
        let dd_sym = RExpr::Atom(abs_diff);
        let lhs_sym = RExpr::mul(RExpr::add(q_sym.clone(), q_sym.clone()), dd_sym.clone());
        let rhs_sym = RExpr::add(
            RExpr::mul(q_sym.clone(), dd_sym.clone()),
            RExpr::mul(q_sym, dd_sym),
        );
        let rd = ring_proof(d, creal, &lhs_sym, &rhs_sym);
        let mul_q_twice = d.const_app(creal.mul, &[q_prime_twice, abs_diff]);
        let rd_symm = d.lemma(creal.equiv_symm, &[mul_q_twice, q_bound_twice, rd]);
        let refl_abs_diff = d.lemma(creal.equiv_refl, &[abs_diff]);
        let mul_step = d.lemma(
            creal.mul_congr,
            &[
                q_prime_twice,
                ofr_out,
                abs_diff,
                abs_diff,
                sum_equiv_target_rat,
                refl_abs_diff,
            ],
        );
        let bound_equiv = rchain(
            d,
            creal,
            q_bound_twice,
            &[(mul_q_twice, rd_symm), (out_bound, mul_step)],
        );

        let refl_abs_combined = d.lemma(creal.equiv_refl, &[abs_combined_error]);
        let combined_error_bound = d.lemma(
            creal.le_congr,
            &[
                abs_combined_error,
                abs_combined_error,
                q_bound_twice,
                out_bound,
                refl_abs_combined,
                bound_equiv,
                combined_le,
            ],
        );

        // --- the actual error term IS F's error plus G's, exactly ----------
        let fsum_y = d.apply(fsum, &[y]);
        let fsum_x = d.apply(fsum, &[x]);
        let fsum_p_x = d.apply(fsum_p, &[x]);
        let deriv_term_sum = zmul(d, p, fsum_p_x, diff_yx);
        let fy_fx_sum = zsub(d, p, fsum_y, fsum_x);
        let actual_error = zsub(d, p, fy_fx_sum, deriv_term_sum);

        let fy_sym = CExpr::var(d, p, fy);
        let fx_sym = CExpr::var(d, p, fx);
        let fpx_sym = CExpr::var(d, p, fpx);
        let gy_sym = CExpr::var(d, p, gy);
        let gx_sym = CExpr::var(d, p, gx);
        let gpx_sym = CExpr::var(d, p, gpx);
        let y_sym = CExpr::var(d, p, y);
        let x_sym = CExpr::var(d, p, x);
        let diff_sym = CExpr::add(y_sym, CExpr::neg(x_sym));
        let ef_sym = error_sym(
            fy_sym.clone(),
            fx_sym.clone(),
            fpx_sym.clone(),
            diff_sym.clone(),
        );
        let eg_sym = error_sym(
            gy_sym.clone(),
            gx_sym.clone(),
            gpx_sym.clone(),
            diff_sym.clone(),
        );
        let actual_sym = error_sym(
            CExpr::add(fy_sym, gy_sym),
            CExpr::add(fx_sym, gx_sym),
            CExpr::add(fpx_sym, gpx_sym),
            diff_sym,
        );
        let ring = ring_law_proof(d, p, &actual_sym, &CExpr::add(ef_sym, eg_sym));

        let conclusion = abs_le_of_equiv(
            d,
            p,
            actual_error,
            combined_error,
            out_bound,
            ring,
            combined_error_bound,
        );

        let with_h = d.lam_fv(h_fv, hyp, conclusion);
        let with_dy = d.lam_fv(hdy_fv, disc_y, with_h);
        let with_dx = d.lam_fv(hdx_fv, disc_x, with_dy);
        let with_y = d.lam_fv(y_fv, carrier, with_dx);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(e_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.deriv.hd_mk, &[fsum, fsum_p, c, r, modulus_sum, spec]);
    let value = {
        let with_hg = d.lam_fv(hg_fv, hg_ty, mk_applied);
        let with_hf = d.lam_fv(hf_fv, hf_ty, with_hg);
        let with_r = d.lam_fv(r_fv, real, with_hf);
        let with_c = d.lam_fv(c_fv, carrier, with_r);
        let with_gp = d.lam_fv(gp_fv, func_ty, with_c);
        let with_g = d.lam_fv(g_fv, func_ty, with_gp);
        let with_fp = d.lam_fv(fp_fv, func_ty, with_g);
        d.lam_fv(f_fv, func_ty, with_fp)
    };
    let ty = {
        let applied = hd_ty(d, p, fsum, fsum_p, c, r);
        let with_hg = d.arrow(hg_ty, applied);
        let with_hf = d.arrow(hf_ty, with_hg);
        let with_r = d.pi_fv(r_fv, real, with_hf);
        let with_c = d.pi_fv(c_fv, carrier, with_r);
        let with_gp = d.pi_fv(gp_fv, func_ty, with_c);
        let with_g = d.pi_fv(g_fv, func_ty, with_gp);
        let with_fp = d.pi_fv(fp_fv, func_ty, with_g);
        d.pi_fv(f_fv, func_ty, with_fp)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.deriv.has_derivative_add,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// holomorphy on a disc
// ---------------------------------------------------------------------------
//
// "Has a derivative at every point of the disc" is a statement with a
// WITNESS, and the witness is the derivative function. It cannot be an
// `Exists`: `Exists`'s predicate must land in `Prop`, and
// `Complex.HasDerivativeOn` is in `Type 0` for the reason this module's own
// documentation gives (the modulus is data). So `HolomorphicOn` is a `Sigma`
// — `sigma_prelude`'s universe-polymorphic dependent pair (ADR-1613),
// instantiated at `u = v = 0`, which is exactly where `Complex → Complex` and
// `HasDerivativeOn F F' c r` both sit.
//
// This is not a weaker statement than the ∃-form; it is the CONSTRUCTIVE one.
// Every theorem below hands back the derivative it used, so
// `Complex.holomorphicDeriv` is a total function on witnesses and
// `Complex.holomorphic_spec` recovers the full ε–δ bound — which is what a
// later Cauchy-integral argument needs and what an `Exists` could not supply.

/// `Complex.HolomorphicOn F c r`.
pub(super) fn holomorphic_ty(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    f: ExprId,
    c: ExprId,
    r: ExprId,
) -> ExprId {
    d.const_app(p.deriv.holomorphic_on, &[f, c, r])
}

/// `fun (F' : Complex → Complex) => Complex.HasDerivativeOn F F' c r` — the
/// `Sigma` family's second component, built once because
/// `Sigma`/`Sigma.mk`/`Sigma.fst`/`Sigma.snd` each take it explicitly.
fn hd_family(d: &mut IntDev<'_>, p: ComplexPrelude, f: ExprId, c: ExprId, r: ExprId) -> ExprId {
    let func_ty = fn_ty(d, p);
    let fp_fv = d.fresh_fvar();
    let fp = d.kernel().fvar(fp_fv);
    let body = hd_ty(d, p, f, fp, c, r);
    d.lam_fv(fp_fv, func_ty, body)
}

/// `Complex.HolomorphicOn (F : Complex → Complex) (c : Complex) (r : CReal)
///   : Type := Sigma (Complex → Complex) (fun F' => HasDerivativeOn F F' c r)`.
///
/// `Sigma.{0,0}`: `Complex → Complex` is `Type 0` and so is
/// `HasDerivativeOn F F' c r`, so the pair lands in `Type 0` as well.
fn declare_holomorphic_on(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let one = d.level_one();
    let type0 = d.kernel().sort(one);
    let zero_level = d.kernel().level_zero();
    let sigma = p.creal.rat.int.logic.sigma.sigma;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let family = hd_family(d, p, f, c, r);
    let sigma_c = d.kernel().const_(sigma, vec![zero_level, zero_level]);
    let body = d.apply(sigma_c, &[func_ty, family]);

    let value = {
        let with_r = d.lam_fv(r_fv, real, body);
        let with_c = d.lam_fv(c_fv, carrier, with_r);
        d.lam_fv(f_fv, func_ty, with_c)
    };
    let ty = {
        let with_r = d.arrow(real, type0);
        let with_c = d.arrow(carrier, with_r);
        d.arrow(func_ty, with_c)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.deriv.holomorphic_on,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(HOLOMORPHIC_HEIGHT),
    })
}

/// `Complex.holomorphicDeriv : ∀ F c r, HolomorphicOn F c r →
/// (Complex → Complex)` — `Sigma.fst`, i.e. the derivative the witness
/// carries. Total on witnesses, which an `Exists`-based holomorphy could not
/// be.
fn declare_holomorphic_deriv(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let zero_level = d.kernel().level_zero();
    let sigma_fst = p.creal.rat.int.logic.sigma.sigma_fst;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let holo = holomorphic_ty(d, p, f, c, r);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let family = hd_family(d, p, f, c, r);
    let fst = d.kernel().const_(sigma_fst, vec![zero_level, zero_level]);
    let body = d.apply(fst, &[func_ty, family, h]);

    let value = {
        let with_h = d.lam_fv(h_fv, holo, body);
        let with_r = d.lam_fv(r_fv, real, with_h);
        let with_c = d.lam_fv(c_fv, carrier, with_r);
        d.lam_fv(f_fv, func_ty, with_c)
    };
    let ty = {
        let with_h = d.arrow(holo, func_ty);
        let with_r = d.pi_fv(r_fv, real, with_h);
        let with_c = d.pi_fv(c_fv, carrier, with_r);
        d.pi_fv(f_fv, func_ty, with_c)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.deriv.holomorphic_deriv,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(HOLOMORPHIC_DERIV_HEIGHT),
    })
}

/// `Complex.holomorphic_spec : ∀ F c r (h : HolomorphicOn F c r),
/// HasDerivativeOn F (holomorphicDeriv F c r h) c r` — `Sigma.snd`, the
/// DEPENDENT projection, so the recovered bound is about the very function
/// [`declare_holomorphic_deriv`] hands back and not some other one.
fn declare_holomorphic_spec(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let zero_level = d.kernel().level_zero();
    let sigma_snd = p.creal.rat.int.logic.sigma.sigma_snd;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let holo = holomorphic_ty(d, p, f, c, r);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let family = hd_family(d, p, f, c, r);
    let snd = d.kernel().const_(sigma_snd, vec![zero_level, zero_level]);
    let body = d.apply(snd, &[func_ty, family, h]);

    let derivative = d.const_app(p.deriv.holomorphic_deriv, &[f, c, r, h]);
    let claim = hd_ty(d, p, f, derivative, c, r);

    let value = {
        let with_h = d.lam_fv(h_fv, holo, body);
        let with_r = d.lam_fv(r_fv, real, with_h);
        let with_c = d.lam_fv(c_fv, carrier, with_r);
        d.lam_fv(f_fv, func_ty, with_c)
    };
    let ty = {
        let with_h = d.pi_fv(h_fv, holo, claim);
        let with_r = d.pi_fv(r_fv, real, with_h);
        let with_c = d.pi_fv(c_fv, carrier, with_r);
        d.pi_fv(f_fv, func_ty, with_c)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.deriv.holomorphic_spec,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Sigma.mk (Complex → Complex) (fun F' => HasDerivativeOn F F' c r) fp
/// witness : HolomorphicOn F c r` — every constructor below is this, with a
/// different `(fp, witness)` pair.
pub(super) fn holomorphic_mk(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    f: ExprId,
    c: ExprId,
    r: ExprId,
    fp: ExprId,
    witness: ExprId,
) -> ExprId {
    let func_ty = fn_ty(d, p);
    let zero_level = d.kernel().level_zero();
    let sigma_mk = p.creal.rat.int.logic.sigma.sigma_mk;
    let family = hd_family(d, p, f, c, r);
    let mk = d.kernel().const_(sigma_mk, vec![zero_level, zero_level]);
    d.apply(mk, &[func_ty, family, fp, witness])
}

/// `Complex.holomorphic_const : ∀ (k c : Complex) (r : CReal),
/// HolomorphicOn (fun _ => k) c r`.
fn declare_holomorphic_const(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let const_fn = {
        let fv = d.fresh_fvar();
        d.lam_fv(fv, carrier, k)
    };
    let zero_z = zzero(d, p);
    let zero_fn = {
        let fv = d.fresh_fvar();
        d.lam_fv(fv, carrier, zero_z)
    };
    let witness = d.lemma(p.deriv.has_derivative_const, &[k, c, r]);
    let body = holomorphic_mk(d, p, const_fn, c, r, zero_fn, witness);

    let value = {
        let with_r = d.lam_fv(r_fv, real, body);
        let with_c = d.lam_fv(c_fv, carrier, with_r);
        d.lam_fv(k_fv, carrier, with_c)
    };
    let ty = {
        let claim = holomorphic_ty(d, p, const_fn, c, r);
        let with_r = d.pi_fv(r_fv, real, claim);
        let with_c = d.pi_fv(c_fv, carrier, with_r);
        d.pi_fv(k_fv, carrier, with_c)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.deriv.holomorphic_const,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.holomorphic_id : ∀ (c : Complex) (r : CReal),
/// HolomorphicOn (fun z => z) c r`.
fn declare_holomorphic_id(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let id_fn = {
        let fv = d.fresh_fvar();
        let z = d.kernel().fvar(fv);
        d.lam_fv(fv, carrier, z)
    };
    let one_z = d.kernel().const_(p.one, vec![]);
    let one_fn = {
        let fv = d.fresh_fvar();
        d.lam_fv(fv, carrier, one_z)
    };
    let witness = d.lemma(p.deriv.has_derivative_id, &[c, r]);
    let body = holomorphic_mk(d, p, id_fn, c, r, one_fn, witness);

    let value = {
        let with_r = d.lam_fv(r_fv, real, body);
        d.lam_fv(c_fv, carrier, with_r)
    };
    let ty = {
        let claim = holomorphic_ty(d, p, id_fn, c, r);
        let with_r = d.pi_fv(r_fv, real, claim);
        d.pi_fv(c_fv, carrier, with_r)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.deriv.holomorphic_id,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.holomorphic_neg : ∀ F c r, HolomorphicOn F c r →
/// HolomorphicOn (fun z => neg (F z)) c r`.
///
/// The derivative handed back is `fun z => neg (holomorphicDeriv F c r h z)`,
/// so the pair stays informative: destructuring the result recovers the
/// negated derivative, not merely the fact that one exists.
fn declare_holomorphic_neg(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);
    let func_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let holo = holomorphic_ty(d, p, f, c, r);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let fp = d.const_app(p.deriv.holomorphic_deriv, &[f, c, r, h]);
    let spec = d.const_app(p.deriv.holomorphic_spec, &[f, c, r, h]);

    let neg_f = {
        let fv = d.fresh_fvar();
        let z = d.kernel().fvar(fv);
        let fz = d.apply(f, &[z]);
        let body = zneg(d, p, fz);
        d.lam_fv(fv, carrier, body)
    };
    let neg_fp = {
        let fv = d.fresh_fvar();
        let z = d.kernel().fvar(fv);
        let fpz = d.apply(fp, &[z]);
        let body = zneg(d, p, fpz);
        d.lam_fv(fv, carrier, body)
    };
    let witness = d.lemma(p.deriv.has_derivative_neg, &[f, fp, c, r, spec]);
    let body = holomorphic_mk(d, p, neg_f, c, r, neg_fp, witness);

    let value = {
        let with_h = d.lam_fv(h_fv, holo, body);
        let with_r = d.lam_fv(r_fv, real, with_h);
        let with_c = d.lam_fv(c_fv, carrier, with_r);
        d.lam_fv(f_fv, func_ty, with_c)
    };
    let ty = {
        let claim = holomorphic_ty(d, p, neg_f, c, r);
        let with_h = d.arrow(holo, claim);
        let with_r = d.pi_fv(r_fv, real, with_h);
        let with_c = d.pi_fv(c_fv, carrier, with_r);
        d.pi_fv(f_fv, func_ty, with_c)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.deriv.holomorphic_neg,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.holomorphic_add : ∀ F G c r, HolomorphicOn F c r →
/// HolomorphicOn G c r → HolomorphicOn (fun z => add (F z) (G z)) c r`.
fn declare_holomorphic_add(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);
    let func_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let holo_f = holomorphic_ty(d, p, f, c, r);
    let holo_g = holomorphic_ty(d, p, g, c, r);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);
    let hg_fv = d.fresh_fvar();
    let hg = d.kernel().fvar(hg_fv);

    let fp = d.const_app(p.deriv.holomorphic_deriv, &[f, c, r, hf]);
    let gp = d.const_app(p.deriv.holomorphic_deriv, &[g, c, r, hg]);
    let spec_f = d.const_app(p.deriv.holomorphic_spec, &[f, c, r, hf]);
    let spec_g = d.const_app(p.deriv.holomorphic_spec, &[g, c, r, hg]);

    let sum_fn = {
        let fv = d.fresh_fvar();
        let z = d.kernel().fvar(fv);
        let fz = d.apply(f, &[z]);
        let gz = d.apply(g, &[z]);
        let body = zadd(d, p, fz, gz);
        d.lam_fv(fv, carrier, body)
    };
    let sum_fp = {
        let fv = d.fresh_fvar();
        let z = d.kernel().fvar(fv);
        let fpz = d.apply(fp, &[z]);
        let gpz = d.apply(gp, &[z]);
        let body = zadd(d, p, fpz, gpz);
        d.lam_fv(fv, carrier, body)
    };
    let witness = d.lemma(
        p.deriv.has_derivative_add,
        &[f, fp, g, gp, c, r, spec_f, spec_g],
    );
    let body = holomorphic_mk(d, p, sum_fn, c, r, sum_fp, witness);

    let value = {
        let with_hg = d.lam_fv(hg_fv, holo_g, body);
        let with_hf = d.lam_fv(hf_fv, holo_f, with_hg);
        let with_r = d.lam_fv(r_fv, real, with_hf);
        let with_c = d.lam_fv(c_fv, carrier, with_r);
        let with_g = d.lam_fv(g_fv, func_ty, with_c);
        d.lam_fv(f_fv, func_ty, with_g)
    };
    let ty = {
        let claim = holomorphic_ty(d, p, sum_fn, c, r);
        let with_hg = d.arrow(holo_g, claim);
        let with_hf = d.arrow(holo_f, with_hg);
        let with_r = d.pi_fv(r_fv, real, with_hf);
        let with_c = d.pi_fv(c_fv, carrier, with_r);
        let with_g = d.pi_fv(g_fv, func_ty, with_c);
        d.pi_fv(f_fv, func_ty, with_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.deriv.holomorphic_add,
        uparams: vec![],
        ty,
        value,
    })
}
