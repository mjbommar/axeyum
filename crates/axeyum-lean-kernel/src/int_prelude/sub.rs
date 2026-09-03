//! `Int.sub a b := add a (neg b)`, and the two distributivity lemmas the
//! `ModEq` family needs and did not have: `Int.mul_neg` and `Int.mul_sub`.
//!
//! `Int.left_distrib` only distributes `mul` over `add`; `Int.modEq_iff_dvd`
//! needs `b - a = n*((b/n)-(a/n))`, which needs `mul` to distribute over
//! `sub` too. Both new lemmas are short derivations from already-proved
//! facts (`mul_comm`, `mul_assoc`, `neg_one_mul`, `left_distrib`) — no case
//! split on `Int`'s constructors, unlike most of `algebra.rs`.
//!
//! `Int.sub` is stated (and its callers state their goals) as the *folded*
//! application `Int.sub a b`, but every proof here works with the *unfolded*
//! `add a (neg b)` throughout and only folds back at the boundary. This is
//! safe because `Int.sub` is a plain, non-recursive `Definition`
//! (`ReducibilityHint::Regular`): the kernel's definitional-equality check
//! unfolds it wherever needed, exactly the idiom `Int.dvd`/`Int.ModEq`
//! already rely on (`dvd.rs`, `modeq.rs`) — state folded, prove unfolded, let
//! `add_declaration`'s defeq check bridge the two.

use super::defs::DERIVED_HEIGHT;
use super::ops::IntDev;
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::nat_prelude::NatOps;

/// Admit `Int.sub : Int → Int → Int := fun a b => add a (neg b)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection (a malformed statement, or a name
/// conflict).
pub(super) fn declare_sub_definition(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let anon = d.anon_name();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let neg_b = d.ineg(b);
    let body = d.iadd(a, neg_b);
    let value = {
        let inner = d.lam_fv(b_fv, int_ty, body);
        d.lam_fv(a_fv, int_ty, inner)
    };
    let ty = {
        let inner = d.kernel().pi(anon, int_ty, int_ty, BinderInfo::Default);
        d.kernel().pi(anon, int_ty, inner, BinderInfo::Default)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.sub,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT),
    })
}

/// `Int.mul_neg : ∀ a b, Eq Int (mul a (neg b)) (neg (mul a b))`.
///
/// Chain: `a*(-b) = (-b)*a = ((-1)*b)*a = (-1)*(b*a) = -(b*a) = -(a*b)`, using
/// only `mul_comm`, `mul_assoc` and `neg_one_mul` — no case split.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_mul_neg(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mul_neg, 2, &|d, v| {
        let (n, y) = (v[0], v[1]);
        let neg_y = d.ineg(y);
        let start = d.imul(n, neg_y);

        let one = d.ione();
        let neg_one = d.ineg(one);

        // neg_y = mul neg_one y
        let mul_negone_y = d.imul(neg_one, y);
        let neg_one_mul_y = d.const_app(p.neg_one_mul, &[y]);
        let neg_y_eq = d.isymm(mul_negone_y, neg_y, neg_one_mul_y);

        // step1: mul n (neg y) = mul (neg y) n
        let s1_rhs = d.imul(neg_y, n);
        let s1_proof = d.const_app(p.mul_comm, &[n, neg_y]);

        // step2: mul (neg y) n = mul (mul neg_one y) n
        let s2_rhs = d.imul(mul_negone_y, n);
        let s2_proof = d.icongr(neg_y, mul_negone_y, neg_y_eq, &|d, x| d.imul(x, n));

        // step3: mul (mul neg_one y) n = mul neg_one (mul y n)
        let mul_y_n = d.imul(y, n);
        let s3_rhs = d.imul(neg_one, mul_y_n);
        let s3_proof = d.const_app(p.mul_assoc, &[neg_one, y, n]);

        // step4: mul neg_one (mul y n) = neg (mul y n)
        let s4_rhs = d.ineg(mul_y_n);
        let s4_proof = d.const_app(p.neg_one_mul, &[mul_y_n]);

        // step5: neg (mul y n) = neg (mul n y)
        let mul_n_y = d.imul(n, y);
        let s5_rhs = d.ineg(mul_n_y);
        let mul_comm_yn = d.const_app(p.mul_comm, &[y, n]);
        let s5_proof = d.icongr(mul_y_n, mul_n_y, mul_comm_yn, &|d, x| d.ineg(x));

        let (_, proof) = d.ichain(
            start,
            &[
                (s1_rhs, s1_proof),
                (s2_rhs, s2_proof),
                (s3_rhs, s3_proof),
                (s4_rhs, s4_proof),
                (s5_rhs, s5_proof),
            ],
        );
        let stmt = d.ieq(start, s5_rhs);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.mul_sub :
/// ∀ a x y, Eq Int (mul a (sub x y)) (sub (mul a x) (mul a y))`.
///
/// By `ring::int::declare` (ring-tactic-2, ADR-1582) rather than the hand
/// `left_distrib`/`mul_neg` chain this file used to carry.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check, or `UnknownConst` if the ring producer declined.
pub(super) fn declare_mul_sub(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    crate::ring::int::declare(d, &p, p.mul_sub, 3, &|d, v| {
        let (n, x, y) = (v[0], v[1], v[2]);
        let sub_xy = d.isub(x, y);
        let lhs = d.imul(n, sub_xy);
        let mul_nx = d.imul(n, x);
        let mul_ny = d.imul(n, y);
        let rhs = d.isub(mul_nx, mul_ny);
        d.ieq(lhs, rhs)
    })
}
