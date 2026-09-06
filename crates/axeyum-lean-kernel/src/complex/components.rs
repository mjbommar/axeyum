//! **The modulus against the real and imaginary parts**: `Complex.abs_ofReal`,
//! `Complex.abs_re_le`, `Complex.abs_im_le`.
//!
//! # Why these three, and why they are separate from the estimates
//!
//! Every fact in `complex/estimates.rs` bounds one complex quantity by
//! another; these three are the only ones that cross BACK to `CReal`, relating
//! `Complex.abs` to `CReal.abs` of a component. They are what a
//! Cauchy–Riemann argument needs and nothing before it did:
//!
//! - `abs_ofReal` says the embedding ℝ ↪ ℂ is an isometry, so a bound on a
//!   complex increment `|ofReal t|` IS a bound on the real increment `|t|`.
//!   Without it, a `Complex.HasDerivativeOn` hypothesis on a disc says nothing
//!   usable about a function restricted to a horizontal segment.
//! - `abs_re_le`/`abs_im_le` are the other direction: a bound on a complex
//!   error term bounds each component's error separately, which is how a
//!   `Complex.HasDerivativeOn` witness produces the two real
//!   `CReal.HasDerivativeOn` witnesses the Cauchy–Riemann equations relate.
//!
//! # The route, and the one place it is not the obvious one
//!
//! All three go through `CReal.sqrt_sq : ∀ x, le zero x → Equiv (sqrt (mul x
//! x)) x`, whose hypothesis is real: it needs its argument NONNEGATIVE. So the
//! square that gets cancelled is never `t·t` — it is `|t|·|t|`, reached by
//! `CReal.mul_self_abs` (`Equiv (mul (abs t) (abs t)) (mul t t)`, itself a
//! `Rat.le_or_lt` case split one carrier down). Trying to cancel `sqrt (t·t)`
//! to `t` directly is the shape that is FALSE for negative `t`, and it is the
//! reason `abs_ofReal`'s right-hand side is `CReal.abs t` and not `t`.
//!
//! `abs_re_le` additionally needs `re·re ≤ re·re + im·im`, which this prelude
//! has no one-sided lemma for: `CReal.le_add_of_nonneg` takes a **`Rat`**
//! addend, not a `CReal` one. It is `CReal.add_le_add` at
//! (`le_refl`, `sq_nonneg`) giving `le (add a zero) (add a b)`, then
//! `CReal.add_zero` under `le_congr`. Two steps, no new declaration.
//!
//! # What is NOT here
//!
//! The Cauchy–Riemann equations themselves. What is still missing is the
//! BRIDGE, and it is a genuine construction rather than a lemma: from
//! `Complex.HasDerivativeOn F F' c r` one has to produce
//! `CReal.HasDerivativeOn (fun t => CReal.re (F (c + ofReal t))) … a b` on the
//! interval a horizontal segment through `c` traces. That needs (1) `InDisc c
//! r (c + ofReal t)` from `CReal.abs t ≤ r` — `abs_ofReal` plus one ring step,
//! cheap; (2) the four interval hypotheses of `CReal.HasDerivativeOn` rebuilt
//! from two disc memberships, which is the collapse of ADR-1642's table run
//! BACKWARDS and is where the work is; and (3) the error bound transported by
//! `abs_re_le`, cheap. Sized in ADR-1646.

// Proof scripts are long, straight-line term constructions with short
// mathematical names, exactly as in `complex/deriv.rs`.
#![allow(
    clippy::doc_markdown,
    clippy::large_types_passed_by_value,
    clippy::many_single_char_names,
    clippy::similar_names
)]

use super::{ComplexPrelude, complex_ty, creal_ty};
use crate::Kernel;
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;

/// The names [`declare_components`] declares, owned by this module rather than
/// by [`ComplexPrelude`] directly — the `poly.rs`/`deriv.rs`/`estimates.rs`
/// arrangement.
///
/// Every field is named `abs_*` because every DECLARATION is, and a prelude
/// name struct's fields mirror the kernel names they intern — `check-kernel-
/// trusted-core.py` and `gen-py-prelude-fields.py` both read this struct as
/// the map from a Rust identifier to a kernel one. Renaming to satisfy
/// `clippy::struct_field_names` would put the two out of step, which is the
/// failure that lint cannot see.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(clippy::struct_field_names)]
pub struct ComponentNames {
    /// `Complex.abs_ofReal : ∀ t, CReal.Equiv (Complex.abs (Complex.ofReal t))
    /// (CReal.abs t)` — the embedding ℝ ↪ ℂ is an isometry.
    pub abs_of_real: NameId,
    /// `Complex.abs_re_le : ∀ z, CReal.le (CReal.abs (Complex.re z))
    /// (Complex.abs z)`.
    pub abs_re_le: NameId,
    /// `Complex.abs_im_le : ∀ z, CReal.le (CReal.abs (Complex.im z))
    /// (Complex.abs z)`.
    pub abs_im_le: NameId,
}

/// Interns this module's names under `complex`. Called once from
/// `super::intern_names`.
pub(super) fn intern_names(kernel: &mut Kernel, complex: NameId) -> ComponentNames {
    ComponentNames {
        abs_of_real: kernel.name_str(complex, "abs_ofReal"),
        abs_re_le: kernel.name_str(complex, "abs_re_le"),
        abs_im_le: kernel.name_str(complex, "abs_im_le"),
    }
}

/// Declare the three modulus-versus-component facts.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_components(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    declare_abs_of_real(d, p)?;
    declare_abs_component_le(d, p, true)?;
    declare_abs_component_le(d, p, false)
}

/// `CReal.add a b`.
fn radd_c(d: &mut IntDev<'_>, p: ComplexPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.creal.add, &[a, b])
}

/// `CReal.mul a b`.
fn rmul(d: &mut IntDev<'_>, p: ComplexPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.creal.mul, &[a, b])
}

/// `CReal.abs a`.
fn rabs(d: &mut IntDev<'_>, p: ComplexPrelude, a: ExprId) -> ExprId {
    d.const_app(p.creal.abs, &[a])
}

/// `CReal.sqrt a`.
fn rsqrt(d: &mut IntDev<'_>, p: ComplexPrelude, a: ExprId) -> ExprId {
    d.const_app(p.creal.sqrt, &[a])
}

/// `CReal.Equiv.trans` chained through `(next, step)` pairs.
fn rchain(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    start: ExprId,
    steps: &[(ExprId, ExprId)],
) -> ExprId {
    let creal = p.creal;
    let mut current = start;
    let mut proof = d.lemma(creal.equiv_refl, &[start]);
    for &(next, step) in steps {
        proof = d.lemma(creal.equiv_trans, &[start, current, next, proof, step]);
        current = next;
    }
    proof
}

/// `Equiv (sqrt (mul (abs t) (abs t))) (abs t)` — `CReal.sqrt_sq` at the
/// NONNEGATIVE argument `abs t`, which is the only argument this development
/// can cancel a square at (see the module documentation).
fn sqrt_of_square_abs(d: &mut IntDev<'_>, p: ComplexPrelude, t: ExprId) -> (ExprId, ExprId) {
    let creal = p.creal;
    let abs_t = rabs(d, p, t);
    let nonneg = d.lemma(creal.abs_nonneg, &[t]);
    let proof = d.lemma(creal.sqrt_sq, &[abs_t, nonneg]);
    (abs_t, proof)
}

/// `Complex.abs_ofReal : ∀ t, CReal.Equiv (Complex.abs (Complex.ofReal t))
/// (CReal.abs t)`.
///
/// `normSq (ofReal t)` δι-unfolds to `add (mul t t) (mul zero zero)` — `re
/// (ofReal t)` is `t` and `im (ofReal t)` is `CReal.zero`, both plain
/// structure projections over `ofReal t := mk t zero`. The route from there is
/// `super::declare_abs_one`'s, with `mul_self_abs` inserted so `sqrt_sq` has a
/// nonnegative argument to work at.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_abs_of_real(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let real = creal_ty(d, p);
    let rzero = d.kernel().const_(creal.zero, vec![]);

    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    // `normSq (ofReal t)` unfolds to `add (mul t t) (mul zero zero)`.
    let t_sq = rmul(d, p, t, t);
    let zero_sq = rmul(d, p, rzero, rzero);
    let lit = radd_c(d, p, t_sq, zero_sq);

    // lit ~ t·t ~ |t|·|t|
    let mul_zero_step = d.lemma(creal.mul_zero, &[rzero]);
    let refl_t_sq = d.lemma(creal.equiv_refl, &[t_sq]);
    let add_congr_step = d.lemma(
        creal.add_congr,
        &[t_sq, t_sq, zero_sq, rzero, refl_t_sq, mul_zero_step],
    );
    let t_sq_plus_zero = radd_c(d, p, t_sq, rzero);
    let add_zero_step = d.lemma(creal.add_zero, &[t_sq]);
    let lit_eq_t_sq = rchain(
        d,
        p,
        lit,
        &[(t_sq_plus_zero, add_congr_step), (t_sq, add_zero_step)],
    );

    let abs_t = rabs(d, p, t);
    let abs_t_sq = rmul(d, p, abs_t, abs_t);
    let mul_self_abs = d.lemma(creal.mul_self_abs, &[t]);
    // Equiv (mul (abs t) (abs t)) (mul t t)
    let mul_self_abs_symm = d.lemma(creal.equiv_symm, &[abs_t_sq, t_sq, mul_self_abs]);
    let lit_eq_abs_sq = d.lemma(
        creal.equiv_trans,
        &[lit, t_sq, abs_t_sq, lit_eq_t_sq, mul_self_abs_symm],
    );

    let sqrt_lit = rsqrt(d, p, lit);
    let sqrt_abs_sq = rsqrt(d, p, abs_t_sq);
    let under_sqrt = d.lemma(creal.sqrt_congr, &[lit, abs_t_sq, lit_eq_abs_sq]);
    let (_, cancel) = sqrt_of_square_abs(d, p, t);
    let body = rchain(
        d,
        p,
        sqrt_lit,
        &[(sqrt_abs_sq, under_sqrt), (abs_t, cancel)],
    );

    let value = d.lam_fv(t_fv, real, body);
    let ty = {
        let of_real_t = d.const_app(p.of_real, &[t]);
        let abs_of_real_t = d.const_app(p.abs, &[of_real_t]);
        let claim = d.const_app(creal.equiv, &[abs_of_real_t, abs_t]);
        d.pi_fv(t_fv, real, claim)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.components.abs_of_real,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.abs_re_le` (`real = true`) and `Complex.abs_im_le`
/// (`real = false`): `CReal.le (CReal.abs (re z)) (Complex.abs z)` and the
/// same for `im`.
///
/// One function for both because the two proofs differ only in which
/// projection is the kept summand and which is the discarded nonnegative one —
/// writing them twice is how the second copy ends up bounding the first
/// component by accident, which no type would catch.
///
/// `normSq z` δι-unfolds to `add (mul (re z) (re z)) (mul (im z) (im z))`, so
/// the `im` case has its kept summand SECOND and needs `CReal.add_comm` to put
/// it first; that one extra step is the whole difference between the branches.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_abs_component_le(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    is_re: bool,
) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let rzero = d.kernel().const_(creal.zero, vec![]);

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);

    let re_z = d.const_app(p.re, &[z]);
    let im_z = d.const_app(p.im, &[z]);
    let re_sq = rmul(d, p, re_z, re_z);
    let im_sq = rmul(d, p, im_z, im_z);
    // `normSq z` unfolds to exactly this, in this order.
    let norm_sq_lit = radd_c(d, p, re_sq, im_sq);

    let (kept, kept_sq, other_sq) = if is_re {
        (re_z, re_sq, im_sq)
    } else {
        (im_z, im_sq, re_sq)
    };

    // kept_sq ≤ kept_sq + other_sq, by `add_le_add` at (`le_refl`,
    // `sq_nonneg`) and then `add_zero` on the left. `CReal.le_add_of_nonneg`
    // does NOT serve here: its addend is a `Rat`.
    let kept_le = d.lemma(creal.le_refl, &[kept_sq]);
    let other_nonneg = d.lemma(creal.sq_nonneg, &[if is_re { im_z } else { re_z }]);
    let sum_le = d.lemma(
        creal.add_le_add,
        &[kept_sq, kept_sq, rzero, other_sq, kept_le, other_nonneg],
    );
    // le (add kept_sq zero) (add kept_sq other_sq)
    let kept_plus_zero = radd_c(d, p, kept_sq, rzero);
    let kept_plus_other = radd_c(d, p, kept_sq, other_sq);
    let add_zero_step = d.lemma(creal.add_zero, &[kept_sq]);
    let refl_kept_plus_other = d.lemma(creal.equiv_refl, &[kept_plus_other]);
    let kept_le_sum = d.lemma(
        creal.le_congr,
        &[
            kept_plus_zero,
            kept_sq,
            kept_plus_other,
            kept_plus_other,
            add_zero_step,
            refl_kept_plus_other,
            sum_le,
        ],
    );
    // le kept_sq (add kept_sq other_sq)

    // For `im` the literal normSq has the summands the other way round.
    let kept_le_normsq = if is_re {
        kept_le_sum
    } else {
        let comm = d.lemma(creal.add_comm, &[kept_sq, other_sq]);
        // Equiv (add im_sq re_sq) (add re_sq im_sq) = Equiv kept_plus_other norm_sq_lit
        let refl_kept = d.lemma(creal.equiv_refl, &[kept_sq]);
        d.lemma(
            creal.le_congr,
            &[
                kept_sq,
                kept_sq,
                kept_plus_other,
                norm_sq_lit,
                refl_kept,
                comm,
                kept_le_sum,
            ],
        )
    };
    // le kept_sq norm_sq_lit

    // |kept|·|kept| ≤ normSq z, then sqrt is monotone and cancels the square.
    let abs_kept = rabs(d, p, kept);
    let abs_kept_sq = rmul(d, p, abs_kept, abs_kept);
    let mul_self_abs = d.lemma(creal.mul_self_abs, &[kept]);
    // Equiv (mul (abs kept) (abs kept)) kept_sq
    let refl_normsq = d.lemma(creal.equiv_refl, &[norm_sq_lit]);
    let mul_self_abs_symm = d.lemma(creal.equiv_symm, &[abs_kept_sq, kept_sq, mul_self_abs]);
    let abs_sq_le_normsq = d.lemma(
        creal.le_congr,
        &[
            kept_sq,
            abs_kept_sq,
            norm_sq_lit,
            norm_sq_lit,
            mul_self_abs_symm,
            refl_normsq,
            kept_le_normsq,
        ],
    );
    // le abs_kept_sq norm_sq_lit

    let sqrt_abs_sq = rsqrt(d, p, abs_kept_sq);
    let sqrt_normsq = rsqrt(d, p, norm_sq_lit);
    let sqrt_mono = d.lemma(
        creal.sqrt_le_sqrt,
        &[abs_kept_sq, norm_sq_lit, abs_sq_le_normsq],
    );
    // le (sqrt abs_kept_sq) (sqrt norm_sq_lit)
    let (_, cancel) = sqrt_of_square_abs(d, p, kept);
    // Equiv (sqrt abs_kept_sq) (abs kept)
    let refl_sqrt_normsq = d.lemma(creal.equiv_refl, &[sqrt_normsq]);
    let body = d.lemma(
        creal.le_congr,
        &[
            sqrt_abs_sq,
            abs_kept,
            sqrt_normsq,
            sqrt_normsq,
            cancel,
            refl_sqrt_normsq,
            sqrt_mono,
        ],
    );
    // le (abs kept) (sqrt norm_sq_lit), and `Complex.abs z` δι-reduces to the
    // right-hand side.

    let value = d.lam_fv(z_fv, carrier, body);
    let ty = {
        let abs_z = d.const_app(p.abs, &[z]);
        let claim = d.const_app(creal.le, &[abs_kept, abs_z]);
        d.pi_fv(z_fv, carrier, claim)
    };
    let name = if is_re {
        p.components.abs_re_le
    } else {
        p.components.abs_im_le
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })
}
