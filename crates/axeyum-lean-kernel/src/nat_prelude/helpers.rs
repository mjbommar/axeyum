//! Small proof-term combinators shared by the divisibility and gcd scripts.

use super::ops::{NatDev, NatOps};
use crate::expr::ExprId;

/// Apply an equality between `Nat -> Nat` functions to one argument.
pub(super) fn apply_nat_function_equality(
    d: &mut NatDev<'_>,
    left: ExprId,
    right: ExprId,
    equality: ExprId,
    argument: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let carrier = d.arrow(nat, nat);
    let left_value = d.apply(left, &[argument]);
    let logic = d.prelude().logic;
    let motive = {
        let candidate_fv = d.fresh_fvar();
        let candidate = d.kernel().fvar(candidate_fv);
        let candidate_value = d.apply(candidate, &[argument]);
        let conclusion = d.eq(left_value, candidate_value);
        let candidate_equality = {
            let one = d.level_one();
            let eq = d.kernel().const_(logic.eq, vec![one]);
            d.apply(eq, &[carrier, left, candidate])
        };
        let proof_fv = d.fresh_fvar();
        let with_proof = d.lam_fv(proof_fv, candidate_equality, conclusion);
        d.lam_fv(candidate_fv, carrier, with_proof)
    };
    let base = d.refl(left_value);
    let zero = d.kernel().level_zero();
    let one = d.level_one();
    let rec = d.kernel().const_(logic.eq_rec, vec![zero, one]);
    d.apply(rec, &[carrier, left, motive, base, right, equality])
}

/// Project the forward implication from a checked `Iff` proof.
pub(super) fn iff_forward(
    d: &mut NatDev<'_>,
    left: ExprId,
    right: ExprId,
    proof: ExprId,
) -> ExprId {
    let logic = d.prelude().logic;
    let iff_ty = d.const_app(logic.iff, &[left, right]);
    let target = d.arrow(left, right);
    let motive = {
        let proof_fv = d.fresh_fvar();
        d.lam_fv(proof_fv, iff_ty, target)
    };
    let minor = {
        let forward_fv = d.fresh_fvar();
        let forward = d.kernel().fvar(forward_fv);
        let reverse_ty = d.arrow(right, left);
        let reverse_fv = d.fresh_fvar();
        let with_reverse = d.lam_fv(reverse_fv, reverse_ty, forward);
        d.lam_fv(forward_fv, target, with_reverse)
    };
    let zero = d.kernel().level_zero();
    let rec = d.kernel().const_(logic.iff_rec, vec![zero]);
    d.apply(rec, &[left, right, motive, minor, proof])
}

/// Project the reverse implication from a checked `Iff` proof.
pub(super) fn iff_reverse(
    d: &mut NatDev<'_>,
    left: ExprId,
    right: ExprId,
    proof: ExprId,
) -> ExprId {
    let logic = d.prelude().logic;
    let iff_ty = d.const_app(logic.iff, &[left, right]);
    let target = d.arrow(right, left);
    let motive = {
        let proof_fv = d.fresh_fvar();
        d.lam_fv(proof_fv, iff_ty, target)
    };
    let minor = {
        let forward_ty = d.arrow(left, right);
        let forward_fv = d.fresh_fvar();
        let reverse_fv = d.fresh_fvar();
        let reverse = d.kernel().fvar(reverse_fv);
        let with_reverse = d.lam_fv(reverse_fv, target, reverse);
        d.lam_fv(forward_fv, forward_ty, with_reverse)
    };
    let zero = d.kernel().level_zero();
    let rec = d.kernel().const_(logic.iff_rec, vec![zero]);
    d.apply(rec, &[left, right, motive, minor, proof])
}

pub(super) fn and_left(d: &mut NatDev<'_>, left: ExprId, right: ExprId, proof: ExprId) -> ExprId {
    let logic = d.prelude().logic;
    let and_ty = d.const_app(logic.and, &[left, right]);
    let motive = {
        let pair_fv = d.fresh_fvar();
        d.lam_fv(pair_fv, and_ty, left)
    };
    let minor = {
        let left_fv = d.fresh_fvar();
        let left_proof = d.kernel().fvar(left_fv);
        let right_fv = d.fresh_fvar();
        let with_right = d.lam_fv(right_fv, right, left_proof);
        d.lam_fv(left_fv, left, with_right)
    };
    let zero = d.kernel().level_zero();
    let rec = d.kernel().const_(logic.and_rec, vec![zero]);
    d.apply(rec, &[left, right, motive, minor, proof])
}

pub(super) fn and_right(d: &mut NatDev<'_>, left: ExprId, right: ExprId, proof: ExprId) -> ExprId {
    let logic = d.prelude().logic;
    let and_ty = d.const_app(logic.and, &[left, right]);
    let motive = {
        let pair_fv = d.fresh_fvar();
        d.lam_fv(pair_fv, and_ty, right)
    };
    let minor = {
        let left_fv = d.fresh_fvar();
        let right_fv = d.fresh_fvar();
        let right_proof = d.kernel().fvar(right_fv);
        let with_right = d.lam_fv(right_fv, right, right_proof);
        d.lam_fv(left_fv, left, with_right)
    };
    let zero = d.kernel().level_zero();
    let rec = d.kernel().const_(logic.and_rec, vec![zero]);
    d.apply(rec, &[left, right, motive, minor, proof])
}

pub(super) fn transport_dvd_left(
    d: &mut NatDev<'_>,
    from: ExprId,
    to: ExprId,
    equality: ExprId,
    value: ExprId,
    proof: ExprId,
) -> ExprId {
    let motive = d.eq_motive(from, &|d, candidate| d.dvd(candidate, value));
    d.transport(from, motive, proof, to, equality)
}

pub(super) fn transport_dvd_right(
    d: &mut NatDev<'_>,
    divisor: ExprId,
    from: ExprId,
    to: ExprId,
    equality: ExprId,
    proof: ExprId,
) -> ExprId {
    let motive = d.eq_motive(from, &|d, candidate| d.dvd(divisor, candidate));
    d.transport(from, motive, proof, to, equality)
}
