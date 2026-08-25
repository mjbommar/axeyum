//! The quotient-form geometric tail bound, `CReal.geom_tail_bounded_div`.
//!
//! ## Why `PosBound (1 − x) k` is data, not a hypothesis on `x`
//!
//! [`power.rs`](super::power)'s own module documentation is explicit that
//! [`CRealPrelude::geom_tail_bounded`] stops at the multiplied-through form
//! `(1 − x) · tail ≤ xᵐ`, precisely because turning it into a bound on `tail`
//! alone needs `inv (1 − x)`, and `CReal.inv` needs a **witnessed**
//! [`CRealPrelude::pos_bound`] — a rational modulus `k` together with a proof
//! that every sample of `1 − x` from index `k` onward is at least `1/(k+1)`.
//! `0 ≤ x` says nothing about how close `x` is to `1`; `x` could be `Equiv`
//! to `one` itself, in which case `1 − x` is not apart from zero and no such
//! `k` exists. Deriving one from `x < 1` (`CReal.lt`, an `Exists`) would work
//! for a caller who already has it, but there is no way to *manufacture* one
//! from `0 ≤ x` alone — over `CReal`, `le` is undecidable, `Apart` is an `Or`
//! whose `Or.rec` does not eliminate into `Type`, and this kernel has no
//! Markov principle. So "`x` bounded away from `1`" is carried as the same
//! kind of data [`CRealPrelude::inv`] and
//! [`CRealPrelude::le_of_mul_le_mul_left`] already carry: a `PosBound (add
//! one (neg x)) k` witness, taken as a hypothesis rather than derived. A
//! caller who already knows `x < 1` gets one for free via
//! [`CRealPrelude::pos_bound_of_lt`] (mirroring `cancellation.rs`'s own
//! remark that this asks for nothing a `0 < c` caller does not already have).
//!
//! This is a genuinely per-construction decision, not a house convention:
//! `CReal.sqrt` needs no such witness because its clamp and fixed schedule
//! make it total over every input, with no apartness-from-zero anywhere in
//! its construction.
//!
//! ## The derivation
//!
//! [`declare_geom_tail_bounded_div`] takes `h_dom : le (mul a tail) (pow x
//! m)` ([`CRealPrelude::geom_tail_bounded`], `a := add one (neg x)`) and
//! multiplies through by `inv a k h` (nonnegative,
//! [`CRealPrelude::inv_nonneg`]) via
//! [`CRealPrelude::mul_le_mul_of_nonneg_left`], giving `le (mul inv (mul a
//! tail)) (mul inv (pow x m))`. The left side collapses to `tail` by the same
//! `mul inv (mul c w) ≈ w` identity `cancellation.rs::declare_
//! le_of_mul_le_mul_left` uses internally (reproduced here as [`cancel_left`]
//! rather than imported — it is a private `fn` there, per this slice's
//! constraint of not editing that file, and the precedent for reproducing a
//! sibling module's private helper verbatim is `cancellation.rs` itself,
//! which reproduces several of `inverse.rs`'s). [`CRealPrelude::le_congr`]
//! transports the inequality across that one `Equiv`, landing directly on
//! `le tail (mul inv (pow x m))` — the quotient form, `tail ≤ xᵐ / (1 − x)`.
//!
//! This does **not** go through
//! [`CRealPrelude::le_of_mul_le_mul_left`]'s own `le (mul c x) (mul c y) →
//! le x y` wrapper: that shape needs `geom_tail_bounded`'s right-hand side
//! `pow x m` already rewritten as `mul a (mul inv (pow x m))` before the
//! wrapper applies, which itself needs the same cancellation identity run in
//! the opposite orientation (`mul_inv_cancel` commuted) — strictly more work
//! than applying `mul_le_mul_of_nonneg_left` once and cancelling the side
//! that is already in the right shape.

use super::{CRealPrelude, creal_ty};
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

// --- small local term builders, verbatim in shape to every other `creal/*`
// module's own copies (see e.g. `power.rs`, `cancellation.rs`) -------------

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

fn cinv(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, k: ExprId, h: ExprId) -> ExprId {
    d.const_app(p.inv, &[x, k, h])
}

fn pos_bound_of(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, k: ExprId) -> ExprId {
    d.const_app(p.pos_bound, &[x, k])
}

/// `λ i, CReal.pow x i` — verbatim copy of `power.rs::pow_fn`, reproduced so
/// this file's own `sumRange` applications are built from the identical
/// closure shape `geom_tail_bounded`'s own statement uses (both built the
/// same way, from a fresh bound variable via `lam_fv`, so the kernel accepts
/// them as the same term up to alpha-equivalence when this file applies
/// `p.geom_tail_bounded`).
fn pow_fn(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let body = d.const_app(p.pow, &[x, i]);
    let nat = d.nat_ty();
    d.lam_fv(i_fv, nat, body)
}

/// `Equiv (mul inv_expr (mul c w)) w`, given `cancel_proof : Equiv (mul c
/// inv_expr) one`. Verbatim copy of `cancellation.rs::cancel_left` (private
/// there): `mul inv_expr (mul c w) ≈ mul (mul inv_expr c) w` (`mul_assoc`,
/// reversed) `≈ mul (mul c inv_expr) w` (`mul_comm`) `≈ mul one w`
/// (`cancel_proof`) `≈ mul w one` (`mul_comm`) `≈ w` (`mul_one`).
fn cancel_left(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    inv_expr: ExprId,
    c: ExprId,
    w: ExprId,
    cancel_proof: ExprId,
) -> ExprId {
    let cw = cmul(d, p, c, w);
    let start = cmul(d, p, inv_expr, cw);

    let inv_c = cmul(d, p, inv_expr, c);
    let step_a_target = cmul(d, p, inv_c, w);
    let assoc = d.lemma(p.mul_assoc, &[inv_expr, c, w]);
    let step_a = d.lemma(p.equiv_symm, &[step_a_target, start, assoc]);

    let c_inv = cmul(d, p, c, inv_expr);
    let comm_ic = d.lemma(p.mul_comm, &[inv_expr, c]);
    let refl_w = d.lemma(p.equiv_refl, &[w]);
    let step_b_target = cmul(d, p, c_inv, w);
    let step_b = d.lemma(p.mul_congr, &[inv_c, c_inv, w, w, comm_ic, refl_w]);

    let one = d.kernel().const_(p.one, vec![]);
    let step_c_target = cmul(d, p, one, w);
    let step_c = d.lemma(p.mul_congr, &[c_inv, one, w, w, cancel_proof, refl_w]);

    let step_d_target = cmul(d, p, w, one);
    let step_d = d.lemma(p.mul_comm, &[one, w]);

    let step_e = d.lemma(p.mul_one, &[w]);

    echain(
        d,
        p,
        start,
        &[
            (step_a_target, step_a),
            (step_b_target, step_b),
            (step_c_target, step_c),
            (step_d_target, step_d),
            (w, step_e),
        ],
    )
}

/// `Equiv`-chain composition. Verbatim copy of `cancellation.rs::echain`
/// (private there, and identical in shape to every other `creal/*` module's
/// own private copy — see e.g. `power.rs::echain`, `series.rs::echain`).
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

/// `CReal.geom_tail_bounded_div : ∀ x, le zero x → ∀ k (h : PosBound (add one
/// (neg x)) k) m n, le (add (sumRange (fun j => pow x j) (Nat.add m n)) (neg
/// (sumRange (fun j => pow x j) m))) (mul (inv (add one (neg x)) k h) (pow x
/// m))`. See the module documentation for the derivation and for why `h` is
/// data rather than a hypothesis on `x`.
fn declare_geom_tail_bounded_div(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let nat_add = d.prelude().add;

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let h0_fv = d.fresh_fvar();
    let h0 = d.kernel().fvar(h0_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let one = d.kernel().const_(p.one, vec![]);
    let neg_x = cneg(d, p, x);
    let a = cadd(d, p, one, neg_x); // a = 1 - x
    let hyp_pos_bound = pos_bound_of(d, p, a, k);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let mn = d.const_app(nat_add, &[m, n]);
    let f = pow_fn(d, p, x);
    let sum_f_m = d.const_app(p.sum_range, &[f, m]);
    let sum_f_mn = d.const_app(p.sum_range, &[f, mn]);
    let neg_sum_f_m = cneg(d, p, sum_f_m);
    let tail = cadd(d, p, sum_f_mn, neg_sum_f_m);

    let pow_m = d.const_app(p.pow, &[x, m]);

    let hyp0 = {
        let zero_c = czero(d, p);
        cle(d, p, zero_c, x)
    };

    // h_dom : le (mul a tail) pow_m
    let h_dom = d.lemma(p.geom_tail_bounded, &[x, h0, m, n]);

    let inv_expr = cinv(d, p, a, k, h);
    let inv_nonneg_fact = d.lemma(p.inv_nonneg, &[a, k, h]);

    let lhs_mul = cmul(d, p, a, tail);
    // step1 : le (mul inv_expr lhs_mul) (mul inv_expr pow_m)
    let step1 = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[inv_expr, lhs_mul, pow_m, inv_nonneg_fact, h_dom],
    );

    // cancel_proof : Equiv (mul a inv_expr) one
    let cancel_proof = d.lemma(p.mul_inv_cancel, &[a, k, h]);
    // eq_tail : Equiv (mul inv_expr (mul a tail)) tail
    let eq_tail = cancel_left(d, p, inv_expr, a, tail, cancel_proof);

    let mul_inv_lhs = cmul(d, p, inv_expr, lhs_mul);
    let mul_inv_pow_m = cmul(d, p, inv_expr, pow_m);
    let refl_rhs = d.lemma(p.equiv_refl, &[mul_inv_pow_m]);
    // proof_inner : le tail mul_inv_pow_m
    let proof_inner = d.lemma(
        p.le_congr,
        &[
            mul_inv_lhs,
            tail,
            mul_inv_pow_m,
            mul_inv_pow_m,
            eq_tail,
            refl_rhs,
            step1,
        ],
    );

    let stmt_inner = cle(d, p, tail, mul_inv_pow_m);

    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt_inner);
        let with_m = d.pi_fv(m_fv, nat, inner);
        // `h_fv` escapes into `with_m` through `mul_inv_pow_m` (via
        // `inv_expr`), so this Pi must be genuinely dependent (`pi_fv`), not
        // `d.arrow` -- the same trap `inv_nonneg`'s own `ty` names.
        let with_h = d.pi_fv(h_fv, hyp_pos_bound, with_m);
        let with_k = d.pi_fv(k_fv, nat, with_h);
        let with_h0 = d.arrow(hyp0, with_k);
        d.pi_fv(x_fv, carrier, with_h0)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof_inner);
        let with_m = d.lam_fv(m_fv, nat, inner);
        let with_h = d.lam_fv(h_fv, hyp_pos_bound, with_m);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        let with_h0 = d.lam_fv(h0_fv, hyp0, with_k);
        d.lam_fv(x_fv, carrier, with_h0)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.geom_tail_bounded_div,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit `CReal.geom_tail_bounded_div`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_geometric(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_geom_tail_bounded_div(d, p)
}
