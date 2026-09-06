//! **The ℂ estimates the product rule runs on**: `Complex.BoundedOn`,
//! `Complex.UniformlyContinuousOn`, and the two magnitude lemmas that turn a
//! product of complex numbers into a product of real bounds.
//!
//! # Why this file exists
//!
//! `complex/deriv.rs`'s own module documentation names the obstruction to the
//! product rule precisely, and it is not algebra: the error decomposition
//!
//! ```text
//! F(y)G(y) − F(x)G(x) − (F'(x)G(x) + F(x)G'(x))(y−x)
//!   = F(y)·[G(y) − G(x) − G'(x)(y−x)]
//!   + G(x)·[F(y) − F(x) − F'(x)(y−x)]
//!   + (F(y) − F(x))·G'(x)·(y−x)
//! ```
//!
//! is one `ring_law_proof` call on this carrier. What it needs and did not
//! have is a uniform bound on `|F|`, on `|G|` and on `|G'|`, plus a modulus of
//! continuity for `F` — the four hypotheses `CReal.hasDerivative_mul` takes as
//! `CReal.BoundedOn` (three times) and `CReal.UniformlyContinuousOn`. Neither
//! predicate existed on ℂ. ADR-1646 records the choice made here.
//!
//! # The two predicates are the real shelf's, position for position
//!
//! | real (`creal/derivative.rs`, `creal/uniform_continuity.rs`) | complex (this file) |
//! | --- | --- |
//! | `CReal.BoundedOn h a b k`, a transparent `Definition` | `Complex.BoundedOn F c r k`, likewise |
//! | two range hypotheses `le a z`, `le z b` | one, `Complex.InDisc c r z` |
//! | `CReal.UniformlyContinuousOn F a b`, an inductive in `Type 0` | `Complex.UniformlyContinuousOn F c r`, likewise |
//! | `modulus : Nat → Nat` as DATA | identical |
//! | `le (abs (x − y)) (ofRat (1/(modulus n + 1))) → le (abs (F x − F y)) (ofRat (1/(n+1)))` | identical, with `Complex.abs` |
//!
//! The modulus is data on both carriers for the reason
//! `creal/uniform_continuity.rs` gives at length: `0 < x` and its `Nat`
//! witness are the same proposition, yet the witness cannot be pulled out of
//! an `Exists` and used to build anything in `Type`. `Complex.HasDerivativeOn`
//! is already in `Type 0` for exactly that reason, so a `Prop`-valued
//! continuity predicate could not be consumed by any witness in
//! `complex/deriv.rs` at all.
//!
//! # What the ℂ side gets for free, and what it does not
//!
//! [`ComplexPrelude::abs_mul`] is an exact `CReal.Equiv`
//! (`|z·w| ~ |z|·|w|`), where `CReal.abs_mul_le_of_bounds` needed a
//! from-scratch two-sided estimate closed by two nonneg-product identities.
//! So [`declare_abs_mul_le_of_bounds`] here is four lines of monotonicity
//! (`CReal.mul_le_mul_of_nonneg_left` twice, once per factor, with
//! `CReal.mul_comm` to reach the second) rather than a page of
//! difference-of-squares.
//!
//! What is *not* cheaper is the index arithmetic: the accuracy budget, the
//! rescale-by-a-magnitude-bound fold and the equal-share fuse are statements
//! about `Rat.natDivSucc` and `Nat`, with no complex number anywhere in them.
//! They are therefore **not** re-derived here. `creal/derivative.rs`'s
//! `rescale_index`, `mag_bound`, `fold_index0_first`, `fold_index0_second`,
//! `mul_modulus_components`, `weaken_to_addend`, `fuse_three_equal_bounds`,
//! `fold_mag_bound_product` and `fold_mag_bound_sum` were made `pub(crate)`
//! and are called directly — the whole point being that
//! a bound on a complex quantity is a `CReal`, so the arithmetic that fuses
//! bounds never learns which carrier produced them. Duplicating them was the
//! alternative and is exactly the "helper duplication lanes rediscover every
//! time" the 2026-08-27 architecture review names.
//!
//! # `uniformlyContinuous_of_hasDerivative` and where the halving is
//!
//! A differentiable function on a disc is uniformly continuous there **given a
//! bound on its derivative** — the bound is not optional and is not derivable
//! here (`Complex.InDisc` is a closed disc, but this development has no
//! compactness argument that would produce a bound from continuity alone). The
//! estimate is
//!
//! ```text
//! |F x − F y| ≤ |(F x − F y) − F'(y)(x−y)| + |F'(y)(x−y)|
//!            ≤ 1/(n₂+1)                    + 1/(n₂+1)      =  1/(n+1)
//! ```
//!
//! with `n₂ := 2n+1`, so the two halves fuse by `Rat.natDivSucc_add` and
//! `Rat.natDivSucc_halve` exactly as `hasDerivative_add`'s do. **The halving
//! is load-bearing**: with `n₂ := n` each half is already the whole target and
//! the sum overshoots by a factor of two, which is what
//! `complex_estimates_tests::uniformly_continuous_modulus_is_halved` pins.
//!
//! The first summand is read at accuracy `rescale_index(0, n₂)` and closed
//! against `|x−y| ≤ 1` ([`crate::creal::derivative::fold_index0_second`] at
//! `k := 0`); the second at accuracy `rescale_index(k, n₂)` against
//! `|F'(y)| ≤ k+1` ([`crate::creal::derivative::fold_index0_first`]). Both are
//! the same fold `hasDerivative_smul` uses one carrier down.

// Proof scripts are long, straight-line term constructions with short
// mathematical names, exactly as in `complex/deriv.rs`.
#![allow(
    clippy::doc_markdown,
    clippy::large_types_passed_by_value,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use super::deriv::{
    fn_ty, in_disc_ty, nat_fn_ty, nonneg_rat_bound, of_div_succ, zabs, zadd, zmul, zneg, zsub,
};
use super::{CExpr, ComplexPrelude, complex_ty, creal_ty, ring_law_proof};
use crate::BinderInfo;
use crate::Kernel;
use crate::KernelError;
use crate::creal::derivative::{
    fold_index0_first, fold_index0_second, fold_mag_bound_product, fold_mag_bound_sum, mag_bound,
    rescale_index, weaken_to_addend,
};
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{radd, rat_eq_rewrite};

/// The names [`declare_estimates`] declares, owned by this module rather than
/// by [`ComplexPrelude`] directly — the `poly.rs`/`deriv.rs` arrangement, so a
/// new declaration inside this file never touches `complex.rs`'s struct,
/// `STEPS` table, or `intern_names`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EstimateNames {
    /// `Complex.abs_sub_le : ∀ z w, CReal.le (abs (z − w)) (add (abs z) (abs w))`.
    pub abs_sub_le: NameId,
    /// `Complex.abs_mul_le_of_bounds : ∀ u v B b, le (abs u) B → le (abs v) b →
    /// le (abs (mul u v)) (CReal.mul B b)`.
    pub abs_mul_le_of_bounds: NameId,
    /// `Complex.BoundedOn (F : Complex → Complex) (c : Complex) (r : CReal)
    /// (k : Nat) : Prop`.
    pub bounded_on: NameId,
    /// `Complex.bounded_on_unfold`.
    pub bounded_on_unfold: NameId,
    /// `Complex.bounded_on_add : ∀ F G c r k1 k2, BoundedOn F c r k1 →
    /// BoundedOn G c r k2 → BoundedOn (fun z => add (F z) (G z)) c r
    /// (k1 + Nat.succ k2)`.
    pub bounded_on_add: NameId,
    /// `Complex.bounded_on_mul : ∀ F G c r k1 k2, BoundedOn F c r k1 →
    /// BoundedOn G c r k2 → BoundedOn (fun z => mul (F z) (G z)) c r
    /// (k1·k2 + k1 + k2)`.
    pub bounded_on_mul: NameId,
    /// `Complex.UniformlyContinuousOn (F : Complex → Complex) (c : Complex)
    /// (r : CReal) : Type`.
    pub uniformly_continuous_on: NameId,
    /// The single constructor `Complex.UniformlyContinuousOn.mk`.
    pub uc_mk: NameId,
    /// The generated recursor `Complex.UniformlyContinuousOn.rec`.
    pub uc_rec: NameId,
    /// `Complex.UniformlyContinuousOn.modulus`.
    pub uc_modulus: NameId,
    /// `Complex.UniformlyContinuousOn.spec`.
    pub uc_spec: NameId,
    /// `Complex.uniformlyContinuous_const`.
    pub uniformly_continuous_const: NameId,
    /// `Complex.uniformlyContinuous_id`.
    pub uniformly_continuous_id: NameId,
    /// `Complex.uniformlyContinuous_of_hasDerivative`.
    pub uniformly_continuous_of_has_derivative: NameId,
}

/// Interns this module's names under `complex` (e.g. `Complex.BoundedOn`).
/// Called once from `super::intern_names`.
pub(super) fn intern_names(kernel: &mut Kernel, complex: NameId) -> EstimateNames {
    let uniformly_continuous_on = kernel.name_str(complex, "UniformlyContinuousOn");
    EstimateNames {
        abs_sub_le: kernel.name_str(complex, "abs_sub_le"),
        abs_mul_le_of_bounds: kernel.name_str(complex, "abs_mul_le_of_bounds"),
        bounded_on: kernel.name_str(complex, "BoundedOn"),
        bounded_on_unfold: kernel.name_str(complex, "bounded_on_unfold"),
        bounded_on_add: kernel.name_str(complex, "bounded_on_add"),
        bounded_on_mul: kernel.name_str(complex, "bounded_on_mul"),
        uniformly_continuous_on,
        uc_mk: kernel.name_str(uniformly_continuous_on, "mk"),
        uc_rec: kernel.name_str(uniformly_continuous_on, "rec"),
        uc_modulus: kernel.name_str(uniformly_continuous_on, "modulus"),
        uc_spec: kernel.name_str(uniformly_continuous_on, "spec"),
        uniformly_continuous_const: kernel.name_str(complex, "uniformlyContinuous_const"),
        uniformly_continuous_id: kernel.name_str(complex, "uniformlyContinuous_id"),
        uniformly_continuous_of_has_derivative: kernel
            .name_str(complex, "uniformlyContinuous_of_hasDerivative"),
    }
}

/// Height for `Complex.BoundedOn`: above every height `complex.rs`, `poly.rs`
/// and `deriv.rs` use (`deriv.rs`'s highest is `DERIVED_HEIGHT + 24`), since
/// its body embeds `Complex.InDisc`.
const BOUNDED_ON_HEIGHT: u16 = super::DERIVED_HEIGHT + 30;
/// Height for `Complex.UniformlyContinuousOn.modulus`: strictly above
/// [`BOUNDED_ON_HEIGHT`], since the spec body it eliminates over mentions
/// `InDisc` and everything below.
const UC_MODULUS_HEIGHT: u16 = BOUNDED_ON_HEIGHT + 1;

/// Declare the two ℂ estimate predicates and the magnitude lemmas that
/// consume them.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_estimates(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    declare_abs_sub_le(d, p)?;
    declare_abs_mul_le_of_bounds(d, p)?;
    declare_bounded_on(d, p)?;
    declare_bounded_on_unfold(d, p)?;
    declare_bounded_on_add(d, p)?;
    declare_bounded_on_mul(d, p)?;
    declare_uc_carrier(d, p)?;
    declare_uc_projections(d, p)?;
    declare_uniformly_continuous_const(d, p)?;
    declare_uniformly_continuous_id(d, p)?;
    declare_uniformly_continuous_of_has_derivative(d, p)
}

// ---------------------------------------------------------------------------
// shared term builders
// ---------------------------------------------------------------------------

/// `CReal.add a b`.
fn radd_c(d: &mut IntDev<'_>, p: ComplexPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.creal.add, &[a, b])
}

/// `CReal.mul a b`.
fn rmul(d: &mut IntDev<'_>, p: ComplexPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.creal.mul, &[a, b])
}

/// `CReal.le a b`.
fn rle(d: &mut IntDev<'_>, p: ComplexPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.creal.le, &[a, b])
}

/// `CReal.Equiv.refl a`.
fn rrefl(d: &mut IntDev<'_>, p: ComplexPrelude, a: ExprId) -> ExprId {
    d.lemma(p.creal.equiv_refl, &[a])
}

/// `CReal.Equiv.symm` at `(a, b)` from a proof of `CReal.Equiv a b`.
fn rsymm_at(d: &mut IntDev<'_>, p: ComplexPrelude, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    d.lemma(p.creal.equiv_symm, &[a, b, h])
}

/// `Complex.BoundedOn`'s own inline shape: `∀ z, InDisc c r z →
/// CReal.le (Complex.abs (F z)) (ofRat (natDivSucc (k+1) 0))`.
///
/// `creal/derivative.rs::bounded_on_ty`'s two interval hypotheses collapse to
/// one disc membership, the same collapse `deriv_spec_body` makes.
pub(super) fn bounded_on_ty(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    h: ExprId,
    c: ExprId,
    r: ExprId,
    k: ExprId,
) -> ExprId {
    let carrier = complex_ty(d, p);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let disc_z = in_disc_ty(d, p, c, r, z);
    let hz = d.apply(h, &[z]);
    let abs_hz = zabs(d, p, hz);
    let bound = mag_bound(d, p.creal, k);
    let concl = rle(d, p, abs_hz, bound);
    let with_disc = d.arrow(disc_z, concl);
    d.pi_fv(z_fv, carrier, with_disc)
}

/// `Complex.BoundedOn F c r k` applied.
fn bounded_on_applied(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    h: ExprId,
    c: ExprId,
    r: ExprId,
    k: ExprId,
) -> ExprId {
    d.const_app(p.estimates.bounded_on, &[h, c, r, k])
}

/// `Complex.UniformlyContinuousOn F c r`.
pub(super) fn uc_ty(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    f: ExprId,
    c: ExprId,
    r: ExprId,
) -> ExprId {
    d.const_app(p.estimates.uniformly_continuous_on, &[f, c, r])
}

/// `CReal.le (Complex.abs (x − y)) (CReal.ofRat q)` — `|x − y| ≤ q`, the
/// closeness predicate `creal/uniform_continuity.rs::close_within` states one
/// carrier down, with [`ComplexPrelude::abs`] in place of `CReal.abs`.
fn close_within(d: &mut IntDev<'_>, p: ComplexPrelude, x: ExprId, y: ExprId, q: ExprId) -> ExprId {
    let diff = zsub(d, p, x, y);
    let magnitude = zabs(d, p, diff);
    let target = d.const_app(p.creal.of_rat, &[q]);
    rle(d, p, magnitude, target)
}

/// `∀ (n : Nat) (x y : Complex), InDisc c r x → InDisc c r y →
///   close_within x y (natDivSucc 1 (modulus n)) →
///   close_within (F x) (F y) (natDivSucc 1 n)`.
///
/// Position for position `creal/uniform_continuity.rs`'s `uc_spec_body`, with
/// the four interval hypotheses replaced by two disc memberships.
fn uc_spec_body(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    f: ExprId,
    c: ExprId,
    r: ExprId,
    modulus: ExprId,
) -> ExprId {
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let disc_x = in_disc_ty(d, p, c, r, x);
    let disc_y = in_disc_ty(d, p, c, r, y);

    let mod_n = d.apply(modulus, &[n]);
    let one_nat = d.num(1);
    let in_bound = d.const_app(p.creal.rat.nat_div_succ, &[one_nat, mod_n]);
    let hyp = close_within(d, p, x, y, in_bound);

    let fx = d.apply(f, &[x]);
    let fy = d.apply(f, &[y]);
    let out_bound = d.const_app(p.creal.rat.nat_div_succ, &[one_nat, n]);
    let conclusion = close_within(d, p, fx, fy, out_bound);

    let body = d.arrow(hyp, conclusion);
    let with_dy = d.arrow(disc_y, body);
    let with_dx = d.arrow(disc_x, with_dy);
    let with_y = d.pi_fv(y_fv, carrier, with_dx);
    let with_x = d.pi_fv(x_fv, carrier, with_y);
    d.pi_fv(n_fv, nat, with_x)
}

// ---------------------------------------------------------------------------
// the two magnitude lemmas
// ---------------------------------------------------------------------------

/// `Complex.abs_sub_le : ∀ z w, CReal.le (Complex.abs (add z (neg w)))
/// (CReal.add (Complex.abs z) (Complex.abs w))` — the triangle inequality on a
/// DIFFERENCE, `|z − w| ≤ |z| + |w|`.
///
/// [`ComplexPrelude::abs_add_le`] at `(z, neg w)` plus
/// [`ComplexPrelude::abs_neg`] under `CReal.add_congr`; there is no
/// `Complex.sub` in this development, so `z − w` is `add z (neg w)` — the same
/// convention [`ComplexPrelude::abs_le_add_abs_sub`] uses.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_abs_sub_le(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);

    let neg_w = zneg(d, p, w);
    let diff = zadd(d, p, z, neg_w);
    let abs_diff = zabs(d, p, diff);
    let abs_z = zabs(d, p, z);
    let abs_w = zabs(d, p, w);
    let abs_neg_w = zabs(d, p, neg_w);

    let triangle = d.lemma(p.abs_add_le, &[z, neg_w]);
    // le abs_diff (add abs_z abs_neg_w)
    let neg_eq = d.lemma(p.abs_neg, &[w]);
    // Equiv abs_neg_w abs_w
    let refl_abs_z = rrefl(d, p, abs_z);
    let sum_eq = d.lemma(
        creal.add_congr,
        &[abs_z, abs_z, abs_neg_w, abs_w, refl_abs_z, neg_eq],
    );
    let sum_neg = radd_c(d, p, abs_z, abs_neg_w);
    let sum_pos = radd_c(d, p, abs_z, abs_w);
    let refl_abs_diff = rrefl(d, p, abs_diff);
    let body = d.lemma(
        creal.le_congr,
        &[
            abs_diff,
            abs_diff,
            sum_neg,
            sum_pos,
            refl_abs_diff,
            sum_eq,
            triangle,
        ],
    );
    let value = {
        let with_w = d.lam_fv(w_fv, carrier, body);
        d.lam_fv(z_fv, carrier, with_w)
    };

    let ty = {
        let concl = rle(d, p, abs_diff, sum_pos);
        let with_w = d.pi_fv(w_fv, carrier, concl);
        d.pi_fv(z_fv, carrier, with_w)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.estimates.abs_sub_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.abs_mul_le_of_bounds : ∀ (u v : Complex) (B b : CReal),
/// CReal.le (abs u) B → CReal.le (abs v) b →
/// CReal.le (abs (mul u v)) (CReal.mul B b)`.
///
/// The ℂ analogue of `CReal.abs_mul_le_of_bounds`, and much shorter than it:
/// there the estimate had to be closed by two nonneg-product identities
/// because `CReal.abs` is a defined lattice operation; here
/// [`ComplexPrelude::abs_mul`] is an exact `CReal.Equiv`, so the whole proof
/// is monotonicity of `CReal.mul` in each factor separately
/// (`CReal.mul_le_mul_of_nonneg_left` twice, reaching the second factor
/// through `CReal.mul_comm`) applied to `|u|·|v|`.
///
/// `0 ≤ B` and `0 ≤ b` are not hypotheses for the same reason they are not on
/// the real side: [`ComplexPrelude::abs_nonneg`] plus `CReal.le_trans` gets
/// both from the two bounds.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_abs_mul_le_of_bounds(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);
    let rzero = d.kernel().const_(creal.zero, vec![]);

    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let bb_fv = d.fresh_fvar();
    let bb = d.kernel().fvar(bb_fv);
    let sb_fv = d.fresh_fvar();
    let sb = d.kernel().fvar(sb_fv);

    let abs_u = zabs(d, p, u);
    let abs_v = zabs(d, p, v);
    let h1_ty = rle(d, p, abs_u, bb);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_ty = rle(d, p, abs_v, sb);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let abs_u_nonneg = d.lemma(p.abs_nonneg, &[u]);
    let abs_v_nonneg = d.lemma(p.abs_nonneg, &[v]);
    let sb_nonneg = d.lemma(creal.le_trans, &[rzero, abs_v, sb, abs_v_nonneg, h2]);

    // |u|·|v| ≤ |u|·b
    let step1 = d.lemma(
        creal.mul_le_mul_of_nonneg_left,
        &[abs_u, abs_v, sb, abs_u_nonneg, h2],
    );
    let mul_au_av = rmul(d, p, abs_u, abs_v);
    let mul_au_sb = rmul(d, p, abs_u, sb);

    // b·|u| ≤ b·B, then commuted into |u|·b ≤ B·b.
    let step2 = d.lemma(
        creal.mul_le_mul_of_nonneg_left,
        &[sb, abs_u, bb, sb_nonneg, h1],
    );
    let mul_sb_au = rmul(d, p, sb, abs_u);
    let mul_sb_bb = rmul(d, p, sb, bb);
    let mul_bb_sb = rmul(d, p, bb, sb);
    let comm_left = d.lemma(creal.mul_comm, &[sb, abs_u]);
    let comm_right = d.lemma(creal.mul_comm, &[sb, bb]);
    let step2c = d.lemma(
        creal.le_congr,
        &[
            mul_sb_au, mul_au_sb, mul_sb_bb, mul_bb_sb, comm_left, comm_right, step2,
        ],
    );

    let step3 = d.lemma(
        creal.le_trans,
        &[mul_au_av, mul_au_sb, mul_bb_sb, step1, step2c],
    );

    // |u·v| ~ |u|·|v| carries the bound back to the product's own modulus.
    let prod = zmul(d, p, u, v);
    let abs_prod = zabs(d, p, prod);
    let abs_mul_eq = d.lemma(p.abs_mul, &[u, v]);
    let abs_mul_sym = rsymm_at(d, p, abs_prod, mul_au_av, abs_mul_eq);
    let refl_bound = rrefl(d, p, mul_bb_sb);
    let body = d.lemma(
        creal.le_congr,
        &[
            mul_au_av,
            abs_prod,
            mul_bb_sb,
            mul_bb_sb,
            abs_mul_sym,
            refl_bound,
            step3,
        ],
    );

    let value = {
        let with_h2 = d.lam_fv(h2_fv, h2_ty, body);
        let with_h1 = d.lam_fv(h1_fv, h1_ty, with_h2);
        let with_sb = d.lam_fv(sb_fv, real, with_h1);
        let with_bb = d.lam_fv(bb_fv, real, with_sb);
        let with_v = d.lam_fv(v_fv, carrier, with_bb);
        d.lam_fv(u_fv, carrier, with_v)
    };
    let ty = {
        let concl = rle(d, p, abs_prod, mul_bb_sb);
        let with_h2 = d.arrow(h2_ty, concl);
        let with_h1 = d.arrow(h1_ty, with_h2);
        let with_sb = d.pi_fv(sb_fv, real, with_h1);
        let with_bb = d.pi_fv(bb_fv, real, with_sb);
        let with_v = d.pi_fv(v_fv, carrier, with_bb);
        d.pi_fv(u_fv, carrier, with_v)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.estimates.abs_mul_le_of_bounds,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// BoundedOn
// ---------------------------------------------------------------------------

/// `Complex.BoundedOn (F : Complex → Complex) (c : Complex) (r : CReal)
/// (k : Nat) : Prop := ∀ z, InDisc c r z → le (abs (F z)) (ofRat (natDivSucc
/// (k+1) 0))` — a transparent `Definition` naming [`bounded_on_ty`]'s own
/// inline shape verbatim, so the two are definitionally equal by exactly one
/// delta step. `CReal.BoundedOn`'s arrangement, one carrier up.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_bounded_on(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat = d.nat_ty();
    let zero_level = d.kernel().level_zero();
    let prop = d.kernel().sort(zero_level);

    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let body = bounded_on_ty(d, p, h, c, r, k);

    let value = {
        let with_k = d.lam_fv(k_fv, nat, body);
        let with_r = d.lam_fv(r_fv, real, with_k);
        let with_c = d.lam_fv(c_fv, carrier, with_r);
        d.lam_fv(h_fv, func_ty, with_c)
    };
    let ty = {
        let with_k = d.arrow(nat, prop);
        let with_r = d.arrow(real, with_k);
        let with_c = d.arrow(carrier, with_r);
        d.arrow(func_ty, with_c)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.estimates.bounded_on,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(BOUNDED_ON_HEIGHT),
    })
}

/// `Complex.bounded_on_unfold : ∀ F c r k, BoundedOn F c r k → ∀ z,
/// InDisc c r z → le (abs (F z)) (ofRat (natDivSucc (k+1) 0))`, proved by the
/// IDENTITY function.
///
/// The isolated confirmation that [`declare_bounded_on`]'s `Definition` really
/// is defeq to [`bounded_on_ty`]'s inline shape: an `Err` here means it is
/// not, which is otherwise only discoverable as a confusing `TypeMismatch`
/// deep inside a witness that consumes it.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_bounded_on_unfold(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat = d.nat_ty();

    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let hyp_ty = bounded_on_applied(d, p, h, c, r, k);
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    let value = {
        let with_hyp = d.lam_fv(hyp_fv, hyp_ty, hyp);
        let with_k = d.lam_fv(k_fv, nat, with_hyp);
        let with_r = d.lam_fv(r_fv, real, with_k);
        let with_c = d.lam_fv(c_fv, carrier, with_r);
        d.lam_fv(h_fv, func_ty, with_c)
    };
    let ty = {
        let concl = bounded_on_ty(d, p, h, c, r, k);
        let with_hyp = d.arrow(hyp_ty, concl);
        let with_k = d.pi_fv(k_fv, nat, with_hyp);
        let with_r = d.pi_fv(r_fv, real, with_k);
        let with_c = d.pi_fv(c_fv, carrier, with_r);
        d.pi_fv(h_fv, func_ty, with_c)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.estimates.bounded_on_unfold,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// UniformlyContinuousOn
// ---------------------------------------------------------------------------

/// `Complex.UniformlyContinuousOn (F : Complex → Complex) (c : Complex)
/// (r : CReal) : Type := mk (modulus : Nat → Nat) (spec : …)`.
///
/// Three leading parameters, `CReal.UniformlyContinuousOn`'s arity with the
/// interval's two endpoints replaced by a centre and a radius. The modulus is
/// data for the reason that file's module documentation gives.
fn declare_uc_carrier(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat_fn = nat_fn_ty(d);
    let one = d.level_one();
    let type0 = d.kernel().sort(one);

    // ty := Π (F : Complex→Complex) (c : Complex) (r : CReal), Type 0.
    let ty = {
        let f_fv = d.fresh_fvar();
        let c_fv = d.fresh_fvar();
        let r_fv = d.fresh_fvar();
        let with_r = d.pi_fv(r_fv, real, type0);
        let with_c = d.pi_fv(c_fv, carrier, with_r);
        d.pi_fv(f_fv, func_ty, with_c)
    };

    let mk_ty = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let mod_fv = d.fresh_fvar();
        let modulus = d.kernel().fvar(mod_fv);

        let spec_ty = uc_spec_body(d, p, f, c, r, modulus);
        let result = uc_ty(d, p, f, c, r);

        let with_spec = d.arrow(spec_ty, result);
        let with_mod = d.pi_fv(mod_fv, nat_fn, with_spec);
        let with_r = d.pi_fv(r_fv, real, with_mod);
        let with_c = d.pi_fv(c_fv, carrier, with_r);
        d.pi_fv(f_fv, func_ty, with_c)
    };

    d.kernel().add_inductive(
        p.estimates.uniformly_continuous_on,
        &[],
        3,
        ty,
        &[(p.estimates.uc_mk, mk_ty)],
    )
}

/// The two projections: `modulus` (large elimination into `Type 0`, a
/// `Definition`) and `spec` (into `Prop`, a `Theorem`, motive at a witness `u`
/// reading `u`'s own modulus) — `complex/deriv.rs::declare_projections`'s
/// shape verbatim, one parameter list over.
fn declare_uc_projections(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat_fn = nat_fn_ty(d);
    let one = d.level_one();
    let zero_level = d.kernel().level_zero();
    let anon = d.anon_name();

    // modulus : ∀ F c r, UniformlyContinuousOn F c r → Nat → Nat.
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let carrier_uc = uc_ty(d, p, f, c, r);

        let motive = d
            .kernel()
            .lam(anon, carrier_uc, nat_fn, BinderInfo::Default);
        let minor = {
            let mod_fv = d.fresh_fvar();
            let modulus = d.kernel().fvar(mod_fv);
            let spec_ty = uc_spec_body(d, p, f, c, r, modulus);
            let inner = d.kernel().lam(anon, spec_ty, modulus, BinderInfo::Default);
            d.lam_fv(mod_fv, nat_fn, inner)
        };

        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let rec = d.kernel().const_(p.estimates.uc_rec, vec![one]);
        let body = d.apply(rec, &[f, c, r, motive, minor, u]);
        let value = {
            let with_u = d.lam_fv(u_fv, carrier_uc, body);
            let with_r = d.lam_fv(r_fv, real, with_u);
            let with_c = d.lam_fv(c_fv, carrier, with_r);
            d.lam_fv(f_fv, func_ty, with_c)
        };
        let ty = {
            let with_u = d.arrow(carrier_uc, nat_fn);
            let with_r = d.pi_fv(r_fv, real, with_u);
            let with_c = d.pi_fv(c_fv, carrier, with_r);
            d.pi_fv(f_fv, func_ty, with_c)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.estimates.uc_modulus,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(UC_MODULUS_HEIGHT),
        })?;
    }

    // spec : ∀ F c r (u : UniformlyContinuousOn F c r),
    //   uc_spec_body F c r (UniformlyContinuousOn.modulus F c r u).
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let carrier_uc = uc_ty(d, p, f, c, r);

        let claim = |d: &mut IntDev<'_>, w: ExprId| {
            let mod_of_w = d.const_app(p.estimates.uc_modulus, &[f, c, r, w]);
            uc_spec_body(d, p, f, c, r, mod_of_w)
        };

        let motive = {
            let w_fv = d.fresh_fvar();
            let w = d.kernel().fvar(w_fv);
            let body = claim(d, w);
            d.lam_fv(w_fv, carrier_uc, body)
        };
        let minor = {
            let mod_fv = d.fresh_fvar();
            let modulus = d.kernel().fvar(mod_fv);
            let spec_ty = uc_spec_body(d, p, f, c, r, modulus);
            let spec_fv = d.fresh_fvar();
            let spec_var = d.kernel().fvar(spec_fv);
            let inner = d.lam_fv(spec_fv, spec_ty, spec_var);
            d.lam_fv(mod_fv, nat_fn, inner)
        };

        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let rec = d.kernel().const_(p.estimates.uc_rec, vec![zero_level]);
        let body = d.apply(rec, &[f, c, r, motive, minor, u]);
        let value = {
            let with_u = d.lam_fv(u_fv, carrier_uc, body);
            let with_r = d.lam_fv(r_fv, real, with_u);
            let with_c = d.lam_fv(c_fv, carrier, with_r);
            d.lam_fv(f_fv, func_ty, with_c)
        };
        let ty = {
            let inner = claim(d, u);
            let with_u = d.pi_fv(u_fv, carrier_uc, inner);
            let with_r = d.pi_fv(r_fv, real, with_u);
            let with_c = d.pi_fv(c_fv, carrier, with_r);
            d.pi_fv(f_fv, func_ty, with_c)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.estimates.uc_spec,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `Complex.uniformlyContinuous_const : ∀ (k c : Complex) (r : CReal),
/// UniformlyContinuousOn (fun _ => k) c r`.
///
/// The cheapest witness, and the one that shows the predicate is not vacuous:
/// `k − k` is `Complex.Equiv`-zero by the ring calculus regardless of the
/// hypothesis, so any modulus works (`fun _ => 0` is used).
fn declare_uniformly_continuous_const(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
) -> Result<(), KernelError> {
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
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hdx_fv = d.fresh_fvar();
        let hdy_fv = d.fresh_fvar();
        let h_fv = d.fresh_fvar();

        let disc_x = in_disc_ty(d, p, c, r, x);
        let disc_y = in_disc_ty(d, p, c, r, y);

        let mod_n = d.apply(modulus, &[n]);
        let one_nat = d.num(1);
        let in_bound = d.const_app(creal.rat.nat_div_succ, &[one_nat, mod_n]);
        let hyp = close_within(d, p, x, y, in_bound);

        let error = zsub(d, p, k, k);
        let k_sym = CExpr::var(d, p, k);
        let error_sym = CExpr::add(k_sym.clone(), CExpr::neg(k_sym));
        let error_equiv_zero = ring_law_proof(d, p, &error_sym, &CExpr::Zero);

        let (bound, bound_nonneg) = nonneg_rat_bound(d, p, 1, n);
        let conclusion =
            super::deriv::close_zero_error(d, p, error, bound, error_equiv_zero, bound_nonneg);

        let with_h = d.lam_fv(h_fv, hyp, conclusion);
        let with_dy = d.lam_fv(hdy_fv, disc_y, with_h);
        let with_dx = d.lam_fv(hdx_fv, disc_x, with_dy);
        let with_y = d.lam_fv(y_fv, carrier, with_dx);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(n_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.estimates.uc_mk, &[const_fn, c, r, modulus, spec]);
    let value = {
        let with_r = d.lam_fv(r_fv, real, mk_applied);
        let with_c = d.lam_fv(c_fv, carrier, with_r);
        d.lam_fv(k_fv, carrier, with_c)
    };
    let ty = {
        let applied = uc_ty(d, p, const_fn, c, r);
        let with_r = d.pi_fv(r_fv, real, applied);
        let with_c = d.pi_fv(c_fv, carrier, with_r);
        d.pi_fv(k_fv, carrier, with_c)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.estimates.uniformly_continuous_const,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.uniformlyContinuous_id : ∀ (c : Complex) (r : CReal),
/// UniformlyContinuousOn (fun z => z) c r`.
///
/// The modulus is the identity, so the conclusion IS the hypothesis after
/// beta: the spec is `fun n x y _ _ h => h`, and the kernel accepts it by
/// definitional equality alone. This is the witness the product rule's third
/// term consumes whenever one factor is `id`.
fn declare_uniformly_continuous_id(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);
    let nat = d.nat_ty();

    let id_fn = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        d.lam_fv(z_fv, carrier, z)
    };
    let modulus = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        d.lam_fv(n_fv, nat, n)
    };

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let spec = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hdx_fv = d.fresh_fvar();
        let hdy_fv = d.fresh_fvar();
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let disc_x = in_disc_ty(d, p, c, r, x);
        let disc_y = in_disc_ty(d, p, c, r, y);

        let mod_n = d.apply(modulus, &[n]);
        let one_nat = d.num(1);
        let in_bound = d.const_app(creal.rat.nat_div_succ, &[one_nat, mod_n]);
        let hyp = close_within(d, p, x, y, in_bound);

        let with_h = d.lam_fv(h_fv, hyp, h);
        let with_dy = d.lam_fv(hdy_fv, disc_y, with_h);
        let with_dx = d.lam_fv(hdx_fv, disc_x, with_dy);
        let with_y = d.lam_fv(y_fv, carrier, with_dx);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(n_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.estimates.uc_mk, &[id_fn, c, r, modulus, spec]);
    let value = {
        let with_r = d.lam_fv(r_fv, real, mk_applied);
        d.lam_fv(c_fv, carrier, with_r)
    };
    let ty = {
        let applied = uc_ty(d, p, id_fn, c, r);
        let with_r = d.pi_fv(r_fv, real, applied);
        d.pi_fv(c_fv, carrier, with_r)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.estimates.uniformly_continuous_id,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.uniformlyContinuous_of_hasDerivative : ∀ F F' c r,
/// HasDerivativeOn F F' c r → ∀ k, BoundedOn F' c r k →
/// UniformlyContinuousOn F c r`.
///
/// **Differentiable with a bounded derivative implies uniformly continuous.**
/// The bound is a genuine hypothesis, not an omission: `Complex.InDisc` is a
/// closed disc but this development carries no compactness argument that would
/// produce a magnitude bound from continuity, and the real shelf's
/// `CReal.BoundedOn` hypotheses on `hasDerivative_mul` are explicit for the
/// same reason.
///
/// The estimate splits `1/(n+1)` into two equal halves at `n₂ := 2n+1` (see
/// the module documentation), reads the derivative's own error at accuracy
/// `rescale_index(0, n₂)` against `|x−y| ≤ 1`, and the derivative term at
/// accuracy `rescale_index(k, n₂)` against `|F'(y)| ≤ k+1`. The three
/// hypotheses on `|x−y|` come out of one combined modulus by
/// [`crate::creal::derivative::weaken_to_addend`], whose third addend is the
/// literal `0` supplying `|x−y| ≤ 1`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_uniformly_continuous_of_has_derivative(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
) -> Result<(), KernelError> {
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
    let hf_ty = super::deriv::hd_ty(d, p, f, fp, c, r);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hb_ty = bounded_on_ty(d, p, fp, c, r, k);
    let hb_fv = d.fresh_fvar();
    let hb = d.kernel().fvar(hb_fv);

    let m = d.const_app(p.deriv.hd_modulus, &[f, fp, c, r, hf]);

    // The combined modulus, built by ONE function so the lambda's body and the
    // spec's recomputation are syntactically identical terms.
    let components = |d: &mut IntDev<'_>, n: ExprId| -> (ExprId, ExprId, ExprId, ExprId, ExprId) {
        let two = d.num(2);
        let two_n = d.mul(two, n);
        let n2 = d.succ(two_n);
        let zero_nat = d.num(0);
        let e_a = rescale_index(d, zero_nat, n2);
        let e_b = rescale_index(d, k, n2);
        let m_a = d.apply(m, &[e_a]);
        let head = d.add(m_a, e_b);
        let combined = d.add(head, zero_nat);
        (n2, e_a, e_b, head, combined)
    };

    let modulus_uc = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let (_, _, _, _, combined) = components(d, n);
        d.lam_fv(n_fv, nat, combined)
    };

    let spec = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
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

        let (n2, e_a, e_b, head, combined) = components(d, n);
        let zero_nat = d.num(0);
        let m_a = d.apply(m, &[e_a]);

        let mod_n = d.apply(modulus_uc, &[n]);
        let one_nat = d.num(1);
        let in_bound = d.const_app(creal.rat.nat_div_succ, &[one_nat, mod_n]);
        let hyp = close_within(d, p, x, y, in_bound);

        let diff_xy = zsub(d, p, x, y);
        let abs_diff = zabs(d, p, diff_xy);

        // Three weakened copies of the hypothesis: at `m(e_a)`, at `e_b`, and
        // at the literal `0` (which reads `|x − y| ≤ 1`).
        let (h_a, h_b, h_one) =
            weaken_to_addend(d, creal, abs_diff, combined, head, m_a, e_b, zero_nat, h);

        // --- summand A: the derivative's own error, at accuracy `e_a`. ------
        // `hd_spec` is stated with its BASE point second, so it is applied at
        // `(x₀, y₀) := (y, x)` to produce `F x − F y − F'(y)·(x − y)`.
        let error_a_bound = d.lemma(
            p.deriv.hd_spec,
            &[f, fp, c, r, hf, e_a, y, x, hdy, hdx, h_a],
        );
        // le (abs error_a) (mul (ofRat (natDivSucc 1 e_a)) abs_diff)
        let fx = d.apply(f, &[x]);
        let fy = d.apply(f, &[y]);
        let fpy = d.apply(fp, &[y]);
        let deriv_term = zmul(d, p, fpy, diff_xy);
        let fx_fy = zsub(d, p, fx, fy);
        let error_a = zsub(d, p, fx_fy, deriv_term);
        let abs_error_a = zabs(d, p, error_a);

        let q_a = of_div_succ(d, p, 1, e_a);
        let (_, q_a_nonneg) = nonneg_rat_bound(d, p, 1, e_a);
        let mul_qa_absdiff = rmul(d, p, q_a, abs_diff);
        let unit_bound = mag_bound(d, creal, zero_nat);
        // (1/(e_a+1))·|x−y| ≤ (1/(e_a+1))·1
        let widen_a = d.lemma(
            creal.mul_le_mul_of_nonneg_left,
            &[q_a, abs_diff, unit_bound, q_a_nonneg, h_one],
        );
        let mul_qa_unit = rmul(d, p, q_a, unit_bound);
        // `fold_index0_second` at `k := 0` returns exactly `(q_a, unit_bound,
        // ofRat (1/(n₂+1)))` — the same three terms built above, not copies —
        // so its `Equiv` closes the gap with one `le_of_equiv`.
        let (_, _, ofr_half_a, fold_a) = fold_index0_second(d, creal, zero_nat, n2, e_a);
        let fold_a_le = d.lemma(creal.le_of_equiv, &[mul_qa_unit, ofr_half_a, fold_a]);
        let step_a_1 = d.lemma(
            creal.le_trans,
            &[
                abs_error_a,
                mul_qa_absdiff,
                mul_qa_unit,
                error_a_bound,
                widen_a,
            ],
        );
        let term_a_bound = d.lemma(
            creal.le_trans,
            &[abs_error_a, mul_qa_unit, ofr_half_a, step_a_1, fold_a_le],
        );
        // le (abs error_a) (ofRat (natDivSucc 1 n2))

        // --- summand B: `F'(y)·(x − y)`, at accuracy `e_b`. ------------------
        let hb_y = d.apply(hb, &[y, hdy]);
        let big_b = mag_bound(d, creal, k);
        let q_b = of_div_succ(d, p, 1, e_b);
        let term_b_raw = d.lemma(
            p.estimates.abs_mul_le_of_bounds,
            &[fpy, diff_xy, big_b, q_b, hb_y, h_b],
        );
        // le (abs (mul (F' y) (x − y))) (mul big_b q_b)
        let abs_term_b = zabs(d, p, deriv_term);
        let mul_bigb_qb = rmul(d, p, big_b, q_b);
        // `fold_index0_first` at `k` returns `(mag_bound k, ofRat (1/(e_b+1)),
        // ofRat (1/(n₂+1)))` — again the same terms, so `le_congr` only has to
        // move the bound.
        let (_, _, ofr_half_b, fold_b) = fold_index0_first(d, creal, k, n2, e_b);
        let refl_abs_term_b = rrefl(d, p, abs_term_b);
        let term_b_bound = d.lemma(
            creal.le_congr,
            &[
                abs_term_b,
                abs_term_b,
                mul_bigb_qb,
                ofr_half_b,
                refl_abs_term_b,
                fold_b,
                term_b_raw,
            ],
        );
        // le (abs deriv_term) (ofRat (natDivSucc 1 n2))

        // --- triangle, then fuse the two equal halves down to `1/(n+1)`. ----
        let combined_terms = zadd(d, p, error_a, deriv_term);
        let abs_combined = zabs(d, p, combined_terms);
        let triangle = d.lemma(p.abs_add_le, &[error_a, deriv_term]);
        let abs_sum = radd_c(d, p, abs_error_a, abs_term_b);
        let half_twice = radd_c(d, p, ofr_half_a, ofr_half_b);
        let sum_bounds = d.lemma(
            creal.add_le_add,
            &[
                abs_error_a,
                ofr_half_a,
                abs_term_b,
                ofr_half_b,
                term_a_bound,
                term_b_bound,
            ],
        );
        let combined_le = d.lemma(
            creal.le_trans,
            &[abs_combined, abs_sum, half_twice, triangle, sum_bounds],
        );

        // `1/(n₂+1) + 1/(n₂+1) = 2/(n₂+1) = 1/(n+1)`, the halving.
        let r_half = d.const_app(creal.rat.nat_div_succ, &[one_nat, n2]);
        let of_rat_add_proof = d.lemma(creal.of_rat_add, &[r_half, r_half]);
        let eq_add = d.lemma(creal.rat.nat_div_succ_add, &[one_nat, one_nat, n2]);
        let two_nat = d.num(2);
        let two_over_n2 = d.const_app(creal.rat.nat_div_succ, &[two_nat, n2]);
        let radd_halves = radd(d, r_half, r_half);
        let motive = |d: &mut IntDev<'_>, t: ExprId| {
            let oft = d.const_app(creal.of_rat, &[t]);
            d.const_app(creal.equiv, &[half_twice, oft])
        };
        let step_a = rat_eq_rewrite(
            d,
            radd_halves,
            two_over_n2,
            eq_add,
            of_rat_add_proof,
            &motive,
        );
        let eq_halve = d.lemma(creal.rat.nat_div_succ_halve, &[n]);
        let out_rat = d.const_app(creal.rat.nat_div_succ, &[one_nat, n]);
        let fuse = rat_eq_rewrite(d, two_over_n2, out_rat, eq_halve, step_a, &motive);
        let ofr_out = d.const_app(creal.of_rat, &[out_rat]);

        let refl_abs_combined = rrefl(d, p, abs_combined);
        let final_bound = d.lemma(
            creal.le_congr,
            &[
                abs_combined,
                abs_combined,
                half_twice,
                ofr_out,
                refl_abs_combined,
                fuse,
                combined_le,
            ],
        );
        // le (abs (error_a + deriv_term)) (ofRat (natDivSucc 1 n))

        // The actual quantity IS that sum: `(Fx − Fy − T) + T ~ Fx − Fy`.
        let actual = zsub(d, p, fx, fy);
        let fx_sym = CExpr::var(d, p, fx);
        let fy_sym = CExpr::var(d, p, fy);
        let fpy_sym = CExpr::var(d, p, fpy);
        let x_sym = CExpr::var(d, p, x);
        let y_sym = CExpr::var(d, p, y);
        let diff_sym = CExpr::add(x_sym, CExpr::neg(y_sym));
        let t_sym = CExpr::mul(fpy_sym, diff_sym);
        let fx_fy_sym = CExpr::add(fx_sym, CExpr::neg(fy_sym));
        let sum_sym = CExpr::add(
            CExpr::add(fx_fy_sym.clone(), CExpr::neg(t_sym.clone())),
            t_sym,
        );
        let ring = ring_law_proof(d, p, &fx_fy_sym, &sum_sym);
        let conclusion =
            super::deriv::abs_le_of_equiv(d, p, actual, combined_terms, ofr_out, ring, final_bound);

        let with_h = d.lam_fv(h_fv, hyp, conclusion);
        let with_dy = d.lam_fv(hdy_fv, disc_y, with_h);
        let with_dx = d.lam_fv(hdx_fv, disc_x, with_dy);
        let with_y = d.lam_fv(y_fv, carrier, with_dx);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(n_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.estimates.uc_mk, &[f, c, r, modulus_uc, spec]);
    let value = {
        let with_hb = d.lam_fv(hb_fv, hb_ty, mk_applied);
        let with_k = d.lam_fv(k_fv, nat, with_hb);
        let with_hf = d.lam_fv(hf_fv, hf_ty, with_k);
        let with_r = d.lam_fv(r_fv, real, with_hf);
        let with_c = d.lam_fv(c_fv, carrier, with_r);
        let with_fp = d.lam_fv(fp_fv, func_ty, with_c);
        d.lam_fv(f_fv, func_ty, with_fp)
    };
    let ty = {
        let applied = uc_ty(d, p, f, c, r);
        let with_hb = d.arrow(hb_ty, applied);
        let with_k = d.pi_fv(k_fv, nat, with_hb);
        let with_hf = d.arrow(hf_ty, with_k);
        let with_r = d.pi_fv(r_fv, real, with_hf);
        let with_c = d.pi_fv(c_fv, carrier, with_r);
        let with_fp = d.pi_fv(fp_fv, func_ty, with_c);
        d.pi_fv(f_fv, func_ty, with_fp)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.estimates.uniformly_continuous_of_has_derivative,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.bounded_on_add : ∀ F G c r k1 k2, BoundedOn F c r k1 →
/// BoundedOn G c r k2 → BoundedOn (fun z => add (F z) (G z)) c r
/// (k1 + Nat.succ k2)`.
///
/// [`ComplexPrelude::abs_add_le`] at the point, then
/// [`crate::creal::derivative::fold_mag_bound_sum`] folds the two `mag_bound`s
/// into `mag_bound (k1 + succ k2)`. The index arithmetic is the real shelf's
/// and is called, not copied: it is a `Rat.natDivSucc` identity with no
/// complex number in it.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_bounded_on_add(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let k1_fv = d.fresh_fvar();
    let k1 = d.kernel().fvar(k1_fv);
    let k2_fv = d.fresh_fvar();
    let k2 = d.kernel().fvar(k2_fv);

    let hbf_ty = bounded_on_applied(d, p, f, c, r, k1);
    let hbf_fv = d.fresh_fvar();
    let hbf = d.kernel().fvar(hbf_fv);
    let hbg_ty = bounded_on_applied(d, p, g, c, r, k2);
    let hbg_fv = d.fresh_fvar();
    let hbg = d.kernel().fvar(hbg_fv);

    let sum_fn = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let fz = d.apply(f, &[z]);
        let gz = d.apply(g, &[z]);
        let body = zadd(d, p, fz, gz);
        d.lam_fv(z_fv, carrier, body)
    };

    let (big1, big2, mag_k3, k3, fold_proof) = fold_mag_bound_sum(d, creal, k1, k2);
    let sum_bounds = radd_c(d, p, big1, big2);

    let pointwise = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let hdz_fv = d.fresh_fvar();
        let hdz = d.kernel().fvar(hdz_fv);
        let disc_z = in_disc_ty(d, p, c, r, z);

        let fz = d.apply(f, &[z]);
        let gz = d.apply(g, &[z]);
        // `Complex.BoundedOn`'s defeq to its inline shape is what makes these
        // two applications typecheck; `Complex.bounded_on_unfold` is the
        // isolated confirmation of exactly that step.
        let h1 = d.apply(hbf, &[z, hdz]);
        let h2 = d.apply(hbg, &[z, hdz]);

        let abs_fz = zabs(d, p, fz);
        let abs_gz = zabs(d, p, gz);
        let sum = zadd(d, p, fz, gz);
        let abs_sum = zabs(d, p, sum);
        let triangle = d.lemma(p.abs_add_le, &[fz, gz]);
        let abs_plus_abs = radd_c(d, p, abs_fz, abs_gz);
        let both = d.lemma(creal.add_le_add, &[abs_fz, big1, abs_gz, big2, h1, h2]);
        let chained = d.lemma(
            creal.le_trans,
            &[abs_sum, abs_plus_abs, sum_bounds, triangle, both],
        );
        let refl_abs_sum = rrefl(d, p, abs_sum);
        let bounded = d.lemma(
            creal.le_congr,
            &[
                abs_sum,
                abs_sum,
                sum_bounds,
                mag_k3,
                refl_abs_sum,
                fold_proof,
                chained,
            ],
        );
        let with_disc = d.lam_fv(hdz_fv, disc_z, bounded);
        d.lam_fv(z_fv, carrier, with_disc)
    };

    let value = {
        let with_hbg = d.lam_fv(hbg_fv, hbg_ty, pointwise);
        let with_hbf = d.lam_fv(hbf_fv, hbf_ty, with_hbg);
        let with_k2 = d.lam_fv(k2_fv, nat, with_hbf);
        let with_k1 = d.lam_fv(k1_fv, nat, with_k2);
        let with_r = d.lam_fv(r_fv, real, with_k1);
        let with_c = d.lam_fv(c_fv, carrier, with_r);
        let with_g = d.lam_fv(g_fv, func_ty, with_c);
        d.lam_fv(f_fv, func_ty, with_g)
    };
    let ty = {
        let concl = bounded_on_applied(d, p, sum_fn, c, r, k3);
        let with_hbg = d.arrow(hbg_ty, concl);
        let with_hbf = d.arrow(hbf_ty, with_hbg);
        let with_k2 = d.pi_fv(k2_fv, nat, with_hbf);
        let with_k1 = d.pi_fv(k1_fv, nat, with_k2);
        let with_r = d.pi_fv(r_fv, real, with_k1);
        let with_c = d.pi_fv(c_fv, carrier, with_r);
        let with_g = d.pi_fv(g_fv, func_ty, with_c);
        d.pi_fv(f_fv, func_ty, with_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.estimates.bounded_on_add,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.bounded_on_mul : ∀ F G c r k1 k2, BoundedOn F c r k1 →
/// BoundedOn G c r k2 → BoundedOn (fun z => mul (F z) (G z)) c r
/// (k1·k2 + k1 + k2)`.
///
/// [`declare_abs_mul_le_of_bounds`] at the point, then
/// [`crate::creal::derivative::fold_mag_bound_product`] folds the two
/// `mag_bound`s. This is the lemma an induction over a polynomial's degree
/// needs at every step, and it is cheap here for exactly the reason
/// `abs_mul_le_of_bounds` is: [`ComplexPrelude::abs_mul`] is an exact `Equiv`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_bounded_on_mul(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let k1_fv = d.fresh_fvar();
    let k1 = d.kernel().fvar(k1_fv);
    let k2_fv = d.fresh_fvar();
    let k2 = d.kernel().fvar(k2_fv);

    let hbf_ty = bounded_on_applied(d, p, f, c, r, k1);
    let hbf_fv = d.fresh_fvar();
    let hbf = d.kernel().fvar(hbf_fv);
    let hbg_ty = bounded_on_applied(d, p, g, c, r, k2);
    let hbg_fv = d.fresh_fvar();
    let hbg = d.kernel().fvar(hbg_fv);

    let mul_fn = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let fz = d.apply(f, &[z]);
        let gz = d.apply(g, &[z]);
        let body = zmul(d, p, fz, gz);
        d.lam_fv(z_fv, carrier, body)
    };

    let (big1, big2, mag_k3, k3, fold_proof) = fold_mag_bound_product(d, creal, k1, k2);
    let prod_bounds = rmul(d, p, big1, big2);

    let pointwise = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let hdz_fv = d.fresh_fvar();
        let hdz = d.kernel().fvar(hdz_fv);
        let disc_z = in_disc_ty(d, p, c, r, z);

        let fz = d.apply(f, &[z]);
        let gz = d.apply(g, &[z]);
        let h1 = d.apply(hbf, &[z, hdz]);
        let h2 = d.apply(hbg, &[z, hdz]);

        let raw = d.lemma(
            p.estimates.abs_mul_le_of_bounds,
            &[fz, gz, big1, big2, h1, h2],
        );
        let prod = zmul(d, p, fz, gz);
        let abs_prod = zabs(d, p, prod);
        let refl_abs_prod = rrefl(d, p, abs_prod);
        let bounded = d.lemma(
            creal.le_congr,
            &[
                abs_prod,
                abs_prod,
                prod_bounds,
                mag_k3,
                refl_abs_prod,
                fold_proof,
                raw,
            ],
        );
        let with_disc = d.lam_fv(hdz_fv, disc_z, bounded);
        d.lam_fv(z_fv, carrier, with_disc)
    };

    let value = {
        let with_hbg = d.lam_fv(hbg_fv, hbg_ty, pointwise);
        let with_hbf = d.lam_fv(hbf_fv, hbf_ty, with_hbg);
        let with_k2 = d.lam_fv(k2_fv, nat, with_hbf);
        let with_k1 = d.lam_fv(k1_fv, nat, with_k2);
        let with_r = d.lam_fv(r_fv, real, with_k1);
        let with_c = d.lam_fv(c_fv, carrier, with_r);
        let with_g = d.lam_fv(g_fv, func_ty, with_c);
        d.lam_fv(f_fv, func_ty, with_g)
    };
    let ty = {
        let concl = bounded_on_applied(d, p, mul_fn, c, r, k3);
        let with_hbg = d.arrow(hbg_ty, concl);
        let with_hbf = d.arrow(hbf_ty, with_hbg);
        let with_k2 = d.pi_fv(k2_fv, nat, with_hbf);
        let with_k1 = d.pi_fv(k1_fv, nat, with_k2);
        let with_r = d.pi_fv(r_fv, real, with_k1);
        let with_c = d.pi_fv(c_fv, carrier, with_r);
        let with_g = d.pi_fv(g_fv, func_ty, with_c);
        d.pi_fv(f_fv, func_ty, with_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.estimates.bounded_on_mul,
        uparams: vec![],
        ty,
        value,
    })
}
