//! **The universal-property template** (roadmap W1-3, W3-13): the pattern
//! [`super::nat`] and [`super::int_categoricity`] each prove without naming.
//!
//! ## The finding this module answers
//!
//! `Nat.Peano.categorical` and `Int.Characterization.categorical` both prove
//! the *same shape* of theorem: a comparison map out of the constructed
//! object, proved structure-preserving and then a bijection. Nothing in the
//! kernel says so — a reader has to notice the parallel by reading both
//! modules side by side. This module states the shape once, as two
//! declarations, one per carrier, and proves each **from the existing
//! theorems** rather than re-deriving anything: [`declare`] applies
//! `Nat.Peano.iter_zero`/`iter_succ`/`iter_unique` and
//! `Int.Characterization.iter_zero`/`iter_succ`/`iter_pred`/`rec_unique` to
//! build its proof terms, so a statement that ever drifted from the
//! individually-proved theorems would make these declarations **fail to
//! type-check**, not silently disagree with them.
//!
//! ## The template, in four parts
//!
//! A universal-property theorem over this kernel's setoid discipline
//! (ADR-1595: no `funext`, no `Quot.sound`) has this shape:
//!
//! 1. **The category is implicit in the hypothesis list.** An object is a
//!    carrier plus operations satisfying *exactly* the axioms that make it a
//!    member of the relevant family — no more. For `ℕ` that family is
//!    "pointed unary algebras" `(N, z, s)`, with **no** axioms at all: every
//!    `(N, z, s)` is such an object, unconditionally. For `ℤ` it is
//!    "`ℤ`-structures" `(R, e, up, down)` with `up`/`down` mutually inverse —
//!    that mutual-inverse pair *is* the category's defining axiom, not an
//!    extra hypothesis pinning the object further.
//! 2. **The mediating map is a named, computed function**, not an extracted
//!    witness — `Nat.Peano.iter` and `Int.Characterization.iter`, both
//!    already declared. This is the "computed, not extracted" lesson of the
//!    2026-08-27 architecture review, applied one level up: the map a
//!    universal property asserts to exist is exactly the map the library
//!    already built for other reasons.
//! 3. **Existence is structure-preservation**, proved by the map's own
//!    computation rules (`iter_zero`, `iter_succ`, `iter_pred` — each a
//!    `refl`, because `iter` is *defined* to satisfy them).
//! 4. **Uniqueness is pointwise**, proved by induction on the *source* object
//!    (`Nat.Peano.iter_unique`, `Int.Characterization.rec_unique`), never by
//!    asserting `h = f` as function equality — there is no `funext` to make
//!    that legal, so "the mediating map is unique" is stated as `∀ n, h n =
//!    f n`, exactly as strong a claim as the setoid discipline permits and
//!    no stronger.
//!
//! [`NatUniversalProperty::initial`] and [`IntUniversalProperty::initial`]
//! package parts 3 and 4 into one theorem per carrier: *the* honest
//! statement of "this object is initial in its category, with a unique
//! mediating map out of it." That is deliberately **weaker** than
//! `Nat.Peano.categorical` / `Int.Characterization.categorical`, which
//! additionally assume the *target* satisfies the object's own defining
//! axioms (the Peano axioms, or generation+aperiodicity) and get a
//! **bijection** out of it — categoricity, not mere initiality. Initiality
//! needs no axioms on the target at all; categoricity is what pins the
//! object up to isomorphism *among its peers*. Conflating the two would
//! overstate what part 3+4 alone give you, which is why this module states
//! initiality as its own theorem rather than as a comment on `categorical`.
//!
//! ## What the next carrier does with this
//!
//! A future universal-property carrier (ADR-1610) follows the same four
//! steps: name the category's axioms in the hypothesis list, name the
//! mediating map, prove it structure-preserving, prove pointwise uniqueness
//! by induction on the source. Nothing here builds `Exists`-quantified
//! "there is a unique map" statements — the named map already stands in for
//! existence, exactly as `categorical` does, so the packaged theorem is a
//! conjunction (existence-equations `∧` uniqueness), not an existential.
//! That keeps every proof term a direct application of an already-checked
//! theorem, which is the whole reason this is "nearly free."

#![allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_lines,
    clippy::type_complexity
)]

use crate::KernelError;
use crate::expr::ExprId;
use crate::name::NameId;
use crate::nat_prelude::NatOps;

use super::IntCharacterization;
use super::Weakening;
use super::int::{izero, minus_one, plus_one};
use super::int_categoricity::IntCategoricity;
use super::nat::NatCharacterization;
use super::ops::CharDev;

/// `Nat.Peano.initial`: `Nat` is the initial pointed unary algebra.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NatUniversalProperty {
    /// The `Nat.Peano` namespace root (shared with [`NatCharacterization`]).
    pub root: NameId,
    /// The universe parameter `u`.
    pub uparam: NameId,
    /// `∀ (N : Sort u) (z : N) (s : N → N),`
    /// `  (iter N z s 0 = z ∧ ∀ n, iter N z s (n+1) = s (iter N z s n))`
    /// `  ∧ ∀ (h : Nat → N), (h 0 = z ∧ ∀ n, h (n+1) = s (h n)) → ∀ n, h n = iter N z s n`
    /// — the mediating map exists (the left conjunct, by `iter`'s own
    /// computation rules) and is unique (the right conjunct, by
    /// `iter_unique`), with **no** hypothesis on `(N, z, s)` at all: every
    /// pointed unary algebra admits a unique structure-preserving map out of
    /// `Nat`.
    pub initial: NameId,
}

/// `Int.Characterization.initial`: `Int` is the initial `ℤ`-structure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IntUniversalProperty {
    /// The `Int.Characterization` namespace root (shared with
    /// [`IntCharacterization`]/[`IntCategoricity`]).
    pub root: NameId,
    /// The universe parameter `u`.
    pub uparam: NameId,
    /// `∀ (R : Sort u) (e : R) (up down : R → R),`
    /// `  (∀ x, down (up x) = x) → (∀ x, up (down x) = x) →`
    /// `  ((iter 0 = e ∧ (∀ t, iter (t+1) = up (iter t)) ∧ (∀ t, iter (t−1) = down (iter t)))`
    /// `   ∧ ∀ (g : Int → R), (g 0 = e ∧ (∀ t, g (t+1) = up (g t)) ∧ (∀ t, g (t−1) = down (g t)))`
    /// `     → ∀ t, g t = iter t)`
    /// — the two mutual-inverse laws are the `ℤ`-structure's defining axioms
    /// (part of the category, not an extra pin on the object), and under
    /// **only** those, the mediating map exists and is unique.
    pub initial: NameId,
}

/// Declare both `initial` theorems.
///
/// # Errors
///
/// Returns the trusted gate's rejection. For
/// [`Weakening::NatInitialDropUniqueZero`] and
/// [`Weakening::IntInitialDropUniqueZero`] an `Err` is the **expected**
/// outcome: it means the dropped hypothesis was load-bearing.
pub(super) fn declare(
    dev: &mut CharDev<'_>,
    nat: NatCharacterization,
    int: IntCharacterization,
    cat: IntCategoricity,
    weaken: Weakening,
) -> Result<(NatUniversalProperty, IntUniversalProperty), KernelError> {
    let nat_up = declare_nat(dev, nat, weaken)?;
    let int_up = declare_int(dev, int, cat, weaken)?;
    Ok((nat_up, int_up))
}

fn declare_nat(
    dev: &mut CharDev<'_>,
    nat: NatCharacterization,
    weaken: Weakening,
) -> Result<NatUniversalProperty, KernelError> {
    let names = NatUniversalProperty {
        root: nat.root,
        uparam: nat.uparam,
        initial: dev.kernel().name_str(nat.root, "initial"),
    };

    let nat_ty = dev.nat_ty();
    let u_lvl = dev.level_of(names.uparam);
    let sort_u = dev.sort_at(u_lvl);
    let zero = dev.zero();

    let carrier_fv = dev.fresh_fvar();
    let carrier = dev.kernel().fvar(carrier_fv);
    let point_fv = dev.fresh_fvar();
    let point = dev.kernel().fvar(point_fv);
    let step_ty = dev.arrow(carrier, carrier);
    let step_fv = dev.fresh_fvar();
    let step = dev.kernel().fvar(step_fv);
    let map_ty = dev.arrow(nat_ty, carrier);

    let iter_const = dev.kernel().const_(nat.iter, vec![u_lvl]);
    let f_map = dev.apply(iter_const, &[carrier, point, step]);

    // `preserves(m) := (m 0 = point) ∧ (∀ n, m (n+1) = step (m n))`, with the
    // zero conjunct's TYPE (not the proof) weakenable for the negative
    // control: the packaged uniqueness clause quantifies over `h`, and
    // dropping `h 0 = z` there — while the proof still supplies the real
    // equation — must make the kernel refuse the theorem.
    let hom_zero_ty = |d: &mut CharDev<'_>, m: ExprId, weaken_zero: bool| {
        if weaken_zero {
            d.true_ty()
        } else {
            let applied = d.apply(m, &[zero]);
            d.eq_at(u_lvl, carrier, applied, point)
        }
    };
    let hom_succ_ty = |d: &mut CharDev<'_>, m: ExprId| {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let succ_n = d.succ(n);
        let left = d.apply(m, &[succ_n]);
        let inner = d.apply(m, &[n]);
        let right = d.apply(step, &[inner]);
        let body = d.eq_at(u_lvl, carrier, left, right);
        d.pi_fv(n_fv, nat_ty, body)
    };

    // ---- existence: `f_map` preserves the structure -------------------------
    let hom_zero_f_ty = hom_zero_ty(dev, f_map, false);
    let hom_succ_f_ty = hom_succ_ty(dev, f_map);
    let existence_ty = dev.and_of(hom_zero_f_ty, hom_succ_f_ty);

    let hom_zero_f_proof = {
        let head = dev.kernel().const_(nat.iter_zero, vec![u_lvl]);
        dev.apply(head, &[carrier, point, step])
    };
    let hom_succ_f_proof = {
        let head = dev.kernel().const_(nat.iter_succ, vec![u_lvl]);
        let n_fv = dev.fresh_fvar();
        let n = dev.kernel().fvar(n_fv);
        let body = dev.apply(head, &[carrier, point, step, n]);
        dev.lam_fv(n_fv, nat_ty, body)
    };
    let existence_proof = dev.and_intro(
        hom_zero_f_ty,
        hom_succ_f_ty,
        hom_zero_f_proof,
        hom_succ_f_proof,
    );

    // ---- uniqueness: any `h` with the same equations agrees pointwise -------
    let h_fv = dev.fresh_fvar();
    let h = dev.kernel().fvar(h_fv);
    let weaken_h_zero = weaken == Weakening::NatInitialDropUniqueZero;
    let hom_zero_h_ty = hom_zero_ty(dev, h, weaken_h_zero);
    let hom_succ_h_ty = hom_succ_ty(dev, h);
    let preserves_h_ty = dev.and_of(hom_zero_h_ty, hom_succ_h_ty);
    let hyp_fv = dev.fresh_fvar();
    let hyp = dev.kernel().fvar(hyp_fv);
    let n_fv = dev.fresh_fvar();
    let n = dev.kernel().fvar(n_fv);
    let equation_ty = {
        let left = dev.apply(h, &[n]);
        let right = dev.apply(f_map, &[n]);
        dev.eq_at(u_lvl, carrier, left, right)
    };
    let tail = dev.pi_fv(n_fv, nat_ty, equation_ty);
    let implication = dev.arrow(preserves_h_ty, tail);
    let uniqueness_ty = dev.pi_fv(h_fv, map_ty, implication);

    let uniqueness_proof = {
        let hz = dev.and_left(hom_zero_h_ty, hom_succ_h_ty, hyp);
        let hs = dev.and_right(hom_zero_h_ty, hom_succ_h_ty, hyp);
        let head = dev.kernel().const_(nat.iter_unique, vec![u_lvl]);
        let body = dev.apply(head, &[carrier, point, step, h, hz, hs, n]);
        let inner = dev.lam_fv(n_fv, nat_ty, body);
        let with_hyp = dev.lam_fv(hyp_fv, preserves_h_ty, inner);
        dev.lam_fv(h_fv, map_ty, with_hyp)
    };

    let conclusion = dev.and_of(existence_ty, uniqueness_ty);
    let body = dev.and_intro(
        existence_ty,
        uniqueness_ty,
        existence_proof,
        uniqueness_proof,
    );
    let binders = [
        (carrier_fv, sort_u),
        (point_fv, carrier),
        (step_fv, step_ty),
    ];
    let statement = dev.close_pi(&binders, conclusion);
    let value = dev.close_lam(&binders, body);
    dev.declare_theorem_u(names.initial, vec![names.uparam], statement, value)?;
    Ok(names)
}

fn declare_int(
    dev: &mut CharDev<'_>,
    int: IntCharacterization,
    cat: IntCategoricity,
    weaken: Weakening,
) -> Result<IntUniversalProperty, KernelError> {
    let names = IntUniversalProperty {
        root: int.root,
        uparam: int.uparam,
        initial: dev.kernel().name_str(int.root, "initial"),
    };

    let int_ty = dev.int_ty();
    let u_lvl = dev.level_of(names.uparam);
    let sort_u = dev.sort_at(u_lvl);
    let int_zero = izero(dev);

    let carrier_fv = dev.fresh_fvar();
    let carrier = dev.kernel().fvar(carrier_fv);
    let point_fv = dev.fresh_fvar();
    let point = dev.kernel().fvar(point_fv);
    let endo_ty = dev.arrow(carrier, carrier);
    let up_fv = dev.fresh_fvar();
    let up = dev.kernel().fvar(up_fv);
    let down_fv = dev.fresh_fvar();
    let down = dev.kernel().fvar(down_fv);
    let map_ty = dev.arrow(int_ty, carrier);

    // `∀ x, down (up x) = x` — `left_inverse`.
    let left_inverse_ty = {
        let x_fv = dev.fresh_fvar();
        let x = dev.kernel().fvar(x_fv);
        let inner = dev.apply(up, &[x]);
        let outer = dev.apply(down, &[inner]);
        let body = dev.eq_at(u_lvl, carrier, outer, x);
        dev.pi_fv(x_fv, carrier, body)
    };
    // `∀ x, up (down x) = x` — `right_inverse`.
    let right_inverse_ty = {
        let x_fv = dev.fresh_fvar();
        let x = dev.kernel().fvar(x_fv);
        let inner = dev.apply(down, &[x]);
        let outer = dev.apply(up, &[inner]);
        let body = dev.eq_at(u_lvl, carrier, outer, x);
        dev.pi_fv(x_fv, carrier, body)
    };
    let left_inverse_fv = dev.fresh_fvar();
    let left_inverse = dev.kernel().fvar(left_inverse_fv);
    let right_inverse_fv = dev.fresh_fvar();
    let right_inverse = dev.kernel().fvar(right_inverse_fv);

    let iter_const = dev.kernel().const_(cat.iter, vec![u_lvl]);
    let f_map = dev.apply(iter_const, &[carrier, point, up, down]);

    let hom_zero_ty = |d: &mut CharDev<'_>, m: ExprId, weaken_zero: bool| {
        if weaken_zero {
            d.true_ty()
        } else {
            let applied = d.apply(m, &[int_zero]);
            d.eq_at(u_lvl, carrier, applied, point)
        }
    };
    let hom_succ_ty = |d: &mut CharDev<'_>, m: ExprId| {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let shifted = plus_one(d, t);
        let left = d.apply(m, &[shifted]);
        let inner = d.apply(m, &[t]);
        let right = d.apply(up, &[inner]);
        let body = d.eq_at(u_lvl, carrier, left, right);
        d.pi_fv(t_fv, int_ty, body)
    };
    let hom_pred_ty = |d: &mut CharDev<'_>, m: ExprId| {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let shifted = minus_one(d, t);
        let left = d.apply(m, &[shifted]);
        let inner = d.apply(m, &[t]);
        let right = d.apply(down, &[inner]);
        let body = d.eq_at(u_lvl, carrier, left, right);
        d.pi_fv(t_fv, int_ty, body)
    };

    // ---- existence -----------------------------------------------------------
    let hom_zero_f_ty = hom_zero_ty(dev, f_map, false);
    let hom_succ_f_ty = hom_succ_ty(dev, f_map);
    let hom_pred_f_ty = hom_pred_ty(dev, f_map);
    let shifts_f_ty = dev.and_of(hom_succ_f_ty, hom_pred_f_ty);
    let existence_ty = dev.and_of(hom_zero_f_ty, shifts_f_ty);

    let hom_zero_f_proof = {
        let head = dev.kernel().const_(cat.iter_zero, vec![u_lvl]);
        dev.apply(head, &[carrier, point, up, down])
    };
    let hom_succ_f_proof = {
        let head = dev.kernel().const_(cat.iter_succ, vec![u_lvl]);
        let t_fv = dev.fresh_fvar();
        let t = dev.kernel().fvar(t_fv);
        let body = dev.apply(head, &[carrier, point, up, down, right_inverse, t]);
        dev.lam_fv(t_fv, int_ty, body)
    };
    let hom_pred_f_proof = {
        let head = dev.kernel().const_(cat.iter_pred, vec![u_lvl]);
        let t_fv = dev.fresh_fvar();
        let t = dev.kernel().fvar(t_fv);
        let body = dev.apply(head, &[carrier, point, up, down, left_inverse, t]);
        dev.lam_fv(t_fv, int_ty, body)
    };
    let shifts_f_proof = dev.and_intro(
        hom_succ_f_ty,
        hom_pred_f_ty,
        hom_succ_f_proof,
        hom_pred_f_proof,
    );
    let existence_proof =
        dev.and_intro(hom_zero_f_ty, shifts_f_ty, hom_zero_f_proof, shifts_f_proof);

    // ---- uniqueness ------------------------------------------------------
    let g_fv = dev.fresh_fvar();
    let g = dev.kernel().fvar(g_fv);
    let weaken_g_zero = weaken == Weakening::IntInitialDropUniqueZero;
    let hom_zero_g_ty = hom_zero_ty(dev, g, weaken_g_zero);
    let hom_succ_g_ty = hom_succ_ty(dev, g);
    let hom_pred_g_ty = hom_pred_ty(dev, g);
    let shifts_g_ty = dev.and_of(hom_succ_g_ty, hom_pred_g_ty);
    let preserves_g_ty = dev.and_of(hom_zero_g_ty, shifts_g_ty);
    let hyp_fv = dev.fresh_fvar();
    let hyp = dev.kernel().fvar(hyp_fv);
    let t_fv = dev.fresh_fvar();
    let t = dev.kernel().fvar(t_fv);
    let equation_ty = {
        let left = dev.apply(g, &[t]);
        let right = dev.apply(f_map, &[t]);
        dev.eq_at(u_lvl, carrier, left, right)
    };
    let tail = dev.pi_fv(t_fv, int_ty, equation_ty);
    let implication = dev.arrow(preserves_g_ty, tail);
    let uniqueness_ty = dev.pi_fv(g_fv, map_ty, implication);

    let uniqueness_proof = {
        let gz = dev.and_left(hom_zero_g_ty, shifts_g_ty, hyp);
        let g_rest = dev.and_right(hom_zero_g_ty, shifts_g_ty, hyp);
        let g_up = dev.and_left(hom_succ_g_ty, hom_pred_g_ty, g_rest);
        let g_down = dev.and_right(hom_succ_g_ty, hom_pred_g_ty, g_rest);
        let g_zero = dev.apply(g, &[int_zero]);
        let f_zero = dev.apply(f_map, &[int_zero]);
        let gz_symm = dev.symm_at(u_lvl, carrier, g_zero, point, gz);
        let agree_zero = dev.trans_at(
            u_lvl,
            carrier,
            f_zero,
            point,
            g_zero,
            hom_zero_f_proof,
            gz_symm,
        );
        let head = dev.kernel().const_(int.rec_unique, vec![u_lvl]);
        let applied = dev.apply(
            head,
            &[
                carrier,
                f_map,
                g,
                up,
                down,
                agree_zero,
                hom_succ_f_proof,
                g_up,
                hom_pred_f_proof,
                g_down,
                t,
            ],
        );
        let f_t = dev.apply(f_map, &[t]);
        let g_t = dev.apply(g, &[t]);
        let flipped = dev.symm_at(u_lvl, carrier, f_t, g_t, applied);
        let inner = dev.lam_fv(t_fv, int_ty, flipped);
        let with_hyp = dev.lam_fv(hyp_fv, preserves_g_ty, inner);
        dev.lam_fv(g_fv, map_ty, with_hyp)
    };

    let conclusion = dev.and_of(existence_ty, uniqueness_ty);
    let body = dev.and_intro(
        existence_ty,
        uniqueness_ty,
        existence_proof,
        uniqueness_proof,
    );
    let binders = [
        (carrier_fv, sort_u),
        (point_fv, carrier),
        (up_fv, endo_ty),
        (down_fv, endo_ty),
        (left_inverse_fv, left_inverse_ty),
        (right_inverse_fv, right_inverse_ty),
    ];
    let statement = dev.close_pi(&binders, conclusion);
    let value = dev.close_lam(&binders, body);
    dev.declare_theorem_u(names.initial, vec![names.uparam], statement, value)?;
    Ok(names)
}
