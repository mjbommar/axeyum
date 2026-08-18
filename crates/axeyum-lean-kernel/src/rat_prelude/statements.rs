//! The **statement** of every rational law, in one place — the same discipline
//! `int_prelude::statements` keeps, so a law's type is written once and cannot
//! drift between the theorem and anything that consumes it.

use super::RatPrelude;
use super::ops::{radd, rle, rlt, rmul, rneg, rone, rzero};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// `le a a`.
pub(super) fn le_refl(d: &mut IntDev<'_>, p: RatPrelude, v: &[ExprId]) -> ExprId {
    rle(d, p, v[0], v[0])
}

/// `le a b → le b c → le a c`.
pub(super) fn le_trans(d: &mut IntDev<'_>, p: RatPrelude, v: &[ExprId]) -> ExprId {
    let conclusion = rle(d, p, v[0], v[2]);
    let second = rle(d, p, v[1], v[2]);
    let first = rle(d, p, v[0], v[1]);
    let after_second = d.arrow(second, conclusion);
    d.arrow(first, after_second)
}

/// `Not (lt a a)`.
pub(super) fn lt_irrefl(d: &mut IntDev<'_>, p: RatPrelude, v: &[ExprId]) -> ExprId {
    let strict = rlt(d, p, v[0], v[0]);
    d.not(strict)
}

/// `lt a b → lt b c → lt a c`.
pub(super) fn lt_trans(d: &mut IntDev<'_>, p: RatPrelude, v: &[ExprId]) -> ExprId {
    let conclusion = rlt(d, p, v[0], v[2]);
    let second = rlt(d, p, v[1], v[2]);
    let first = rlt(d, p, v[0], v[1]);
    let after_second = d.arrow(second, conclusion);
    d.arrow(first, after_second)
}

/// `lt a b → le b c → lt a c`.
pub(super) fn lt_of_lt_of_le(d: &mut IntDev<'_>, p: RatPrelude, v: &[ExprId]) -> ExprId {
    let conclusion = rlt(d, p, v[0], v[2]);
    let second = rle(d, p, v[1], v[2]);
    let first = rlt(d, p, v[0], v[1]);
    let after_second = d.arrow(second, conclusion);
    d.arrow(first, after_second)
}

/// `le a b → lt b c → lt a c`.
pub(super) fn lt_of_le_of_lt(d: &mut IntDev<'_>, p: RatPrelude, v: &[ExprId]) -> ExprId {
    let conclusion = rlt(d, p, v[0], v[2]);
    let second = rlt(d, p, v[1], v[2]);
    let first = rle(d, p, v[0], v[1]);
    let after_second = d.arrow(second, conclusion);
    d.arrow(first, after_second)
}

/// `lt a b → le a b`.
pub(super) fn le_of_lt(d: &mut IntDev<'_>, p: RatPrelude, v: &[ExprId]) -> ExprId {
    let conclusion = rle(d, p, v[0], v[1]);
    let hypothesis = rlt(d, p, v[0], v[1]);
    d.arrow(hypothesis, conclusion)
}

/// `le a b → le c e → le (add a c) (add b e)`.
pub(super) fn add_le_add(d: &mut IntDev<'_>, p: RatPrelude, v: &[ExprId]) -> ExprId {
    let left = radd(d, v[0], v[2]);
    let right = radd(d, v[1], v[3]);
    let conclusion = rle(d, p, left, right);
    let second = rle(d, p, v[2], v[3]);
    let first = rle(d, p, v[0], v[1]);
    let after_second = d.arrow(second, conclusion);
    d.arrow(first, after_second)
}

/// `le a b → lt c e → lt (add a c) (add b e)`.
pub(super) fn add_lt_add_of_le_of_lt(d: &mut IntDev<'_>, p: RatPrelude, v: &[ExprId]) -> ExprId {
    let left = radd(d, v[0], v[2]);
    let right = radd(d, v[1], v[3]);
    let conclusion = rlt(d, p, left, right);
    let second = rlt(d, p, v[2], v[3]);
    let first = rle(d, p, v[0], v[1]);
    let after_second = d.arrow(second, conclusion);
    d.arrow(first, after_second)
}

/// `Eq Rat (add a b) (add b a)`.
pub(super) fn add_comm(d: &mut IntDev<'_>, _p: RatPrelude, v: &[ExprId]) -> ExprId {
    let left = radd(d, v[0], v[1]);
    let right = radd(d, v[1], v[0]);
    super::ops::req(d, left, right)
}

/// `Eq Rat (add (add a b) c) (add a (add b c))`.
pub(super) fn add_assoc(d: &mut IntDev<'_>, _p: RatPrelude, v: &[ExprId]) -> ExprId {
    let inner_left = radd(d, v[0], v[1]);
    let left = radd(d, inner_left, v[2]);
    let inner_right = radd(d, v[1], v[2]);
    let right = radd(d, v[0], inner_right);
    super::ops::req(d, left, right)
}

/// `Eq Rat (add a zero) a`.
pub(super) fn add_zero(d: &mut IntDev<'_>, p: RatPrelude, v: &[ExprId]) -> ExprId {
    let zero = rzero(d, p);
    let left = radd(d, v[0], zero);
    super::ops::req(d, left, v[0])
}

/// `Eq Rat (add a (neg a)) zero`.
pub(super) fn add_neg(d: &mut IntDev<'_>, p: RatPrelude, v: &[ExprId]) -> ExprId {
    let negated = rneg(d, v[0]);
    let left = radd(d, v[0], negated);
    let zero = rzero(d, p);
    super::ops::req(d, left, zero)
}

/// `le zero a → le b c → le (mul a b) (mul a c)`.
pub(super) fn mul_le_mul_of_nonneg_left(d: &mut IntDev<'_>, p: RatPrelude, v: &[ExprId]) -> ExprId {
    let left = rmul(d, v[0], v[1]);
    let right = rmul(d, v[0], v[2]);
    let conclusion = rle(d, p, left, right);
    let second = rle(d, p, v[1], v[2]);
    let zero = rzero(d, p);
    let first = rle(d, p, zero, v[0]);
    let after_second = d.arrow(second, conclusion);
    d.arrow(first, after_second)
}

/// `lt zero one`.
pub(super) fn zero_lt_one(d: &mut IntDev<'_>, p: RatPrelude, _v: &[ExprId]) -> ExprId {
    let zero = rzero(d, p);
    let one = rone(d, p);
    rlt(d, p, zero, one)
}

/// `Eq Rat (mul a b) (mul b a)`.
pub(super) fn mul_comm(d: &mut IntDev<'_>, _p: RatPrelude, v: &[ExprId]) -> ExprId {
    let left = rmul(d, v[0], v[1]);
    let right = rmul(d, v[1], v[0]);
    super::ops::req(d, left, right)
}

/// `Eq Rat (mul (mul a b) c) (mul a (mul b c))`.
pub(super) fn mul_assoc(d: &mut IntDev<'_>, _p: RatPrelude, v: &[ExprId]) -> ExprId {
    let inner_left = rmul(d, v[0], v[1]);
    let left = rmul(d, inner_left, v[2]);
    let inner_right = rmul(d, v[1], v[2]);
    let right = rmul(d, v[0], inner_right);
    super::ops::req(d, left, right)
}

/// `Eq Rat (mul a one) a`.
pub(super) fn mul_one(d: &mut IntDev<'_>, p: RatPrelude, v: &[ExprId]) -> ExprId {
    let one = rone(d, p);
    let left = rmul(d, v[0], one);
    super::ops::req(d, left, v[0])
}

/// `Eq Rat (mul a zero) zero`.
pub(super) fn mul_zero(d: &mut IntDev<'_>, p: RatPrelude, v: &[ExprId]) -> ExprId {
    let zero = rzero(d, p);
    let left = rmul(d, v[0], zero);
    let right = rzero(d, p);
    super::ops::req(d, left, right)
}

/// `Eq Rat (mul a (add b c)) (add (mul a b) (mul a c))`.
pub(super) fn left_distrib(d: &mut IntDev<'_>, _p: RatPrelude, v: &[ExprId]) -> ExprId {
    let sum = radd(d, v[1], v[2]);
    let left = rmul(d, v[0], sum);
    let first = rmul(d, v[0], v[1]);
    let second = rmul(d, v[0], v[2]);
    let right = radd(d, first, second);
    super::ops::req(d, left, right)
}

/// `le zero a → le zero b → le zero (mul a b)`.
pub(super) fn mul_nonneg(d: &mut IntDev<'_>, p: RatPrelude, v: &[ExprId]) -> ExprId {
    let zero = rzero(d, p);
    let product = rmul(d, v[0], v[1]);
    let conclusion = rle(d, p, zero, product);
    let second = rle(d, p, zero, v[1]);
    let first = rle(d, p, zero, v[0]);
    let after_second = d.arrow(second, conclusion);
    d.arrow(first, after_second)
}

/// `le zero (mul a a)`.
pub(super) fn sq_nonneg(d: &mut IntDev<'_>, p: RatPrelude, v: &[ExprId]) -> ExprId {
    let zero = rzero(d, p);
    let square = rmul(d, v[0], v[0]);
    rle(d, p, zero, square)
}
