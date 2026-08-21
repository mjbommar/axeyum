//! The **statement** of every integer law, in one place.
//!
//! Each function builds the body of `∀ (x_0 … x_{n-1} : Int), …` for the law
//! it names, given those `n` variables. Both routes go through here: a law that
//! is still asserted is declared as an `Axiom` whose type is this body under an
//! `Int` telescope, and a law that has been *derived* is declared as a
//! `Theorem` with exactly the same type. Sharing the builder is what makes the
//! before/after axiom accounting honest — a discharged law keeps its type to
//! the byte, so no downstream proof term has to change and no statement can
//! quietly weaken as it moves from assumption to consequence.

use super::ops::IntDev;
use crate::BinderInfo;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// `le a a`.
pub(super) fn le_refl(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    d.ile(v[0], v[0])
}

/// `le a b → le b c → le a c`.
pub(super) fn le_trans(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let conclusion = d.ile(v[0], v[2]);
    let second = d.ile(v[1], v[2]);
    let first = d.ile(v[0], v[1]);
    let after_second = d.arrow(second, conclusion);
    d.arrow(first, after_second)
}

/// `Not (lt a a)`.
pub(super) fn lt_irrefl(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let strict = d.ilt(v[0], v[0]);
    d.not(strict)
}

/// `lt a b → lt b c → lt a c`.
pub(super) fn lt_trans(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let conclusion = d.ilt(v[0], v[2]);
    let second = d.ilt(v[1], v[2]);
    let first = d.ilt(v[0], v[1]);
    let after_second = d.arrow(second, conclusion);
    d.arrow(first, after_second)
}

/// `lt a b → le b c → lt a c`.
pub(super) fn lt_of_lt_of_le(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let conclusion = d.ilt(v[0], v[2]);
    let second = d.ile(v[1], v[2]);
    let first = d.ilt(v[0], v[1]);
    let after_second = d.arrow(second, conclusion);
    d.arrow(first, after_second)
}

/// `le a b → lt b c → lt a c`.
pub(super) fn lt_of_le_of_lt(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let conclusion = d.ilt(v[0], v[2]);
    let second = d.ilt(v[1], v[2]);
    let first = d.ile(v[0], v[1]);
    let after_second = d.arrow(second, conclusion);
    d.arrow(first, after_second)
}

/// `lt a b → le a b`.
pub(super) fn le_of_lt(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let conclusion = d.ile(v[0], v[1]);
    let hypothesis = d.ilt(v[0], v[1]);
    d.arrow(hypothesis, conclusion)
}

/// `le a b → le c d → le (add a c) (add b d)`.
pub(super) fn add_le_add(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let left = d.iadd(v[0], v[2]);
    let right = d.iadd(v[1], v[3]);
    let conclusion = d.ile(left, right);
    let second = d.ile(v[2], v[3]);
    let first = d.ile(v[0], v[1]);
    let after_second = d.arrow(second, conclusion);
    d.arrow(first, after_second)
}

/// `le a b → lt c d → lt (add a c) (add b d)`.
pub(super) fn add_lt_add_of_le_of_lt(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let left = d.iadd(v[0], v[2]);
    let right = d.iadd(v[1], v[3]);
    let conclusion = d.ilt(left, right);
    let second = d.ilt(v[2], v[3]);
    let first = d.ile(v[0], v[1]);
    let after_second = d.arrow(second, conclusion);
    d.arrow(first, after_second)
}

/// `Eq Int (add a b) (add b a)`.
pub(super) fn add_comm(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let left = d.iadd(v[0], v[1]);
    let right = d.iadd(v[1], v[0]);
    d.ieq(left, right)
}

/// `Eq Int (add (add a b) c) (add a (add b c))`.
pub(super) fn add_assoc(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let inner_left = d.iadd(v[0], v[1]);
    let left = d.iadd(inner_left, v[2]);
    let inner_right = d.iadd(v[1], v[2]);
    let right = d.iadd(v[0], inner_right);
    d.ieq(left, right)
}

/// `Eq Int (add a zero) a`.
pub(super) fn add_zero(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let zero = d.izero();
    let left = d.iadd(v[0], zero);
    d.ieq(left, v[0])
}

/// `Eq Int (add a (neg a)) zero`.
pub(super) fn add_neg(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let negated = d.ineg(v[0]);
    let left = d.iadd(v[0], negated);
    let zero = d.izero();
    d.ieq(left, zero)
}

/// `Eq Int (add (add a b) (neg b)) a`.
pub(super) fn add_neg_cancel_right(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let sum = d.iadd(v[0], v[1]);
    let negated = d.ineg(v[1]);
    let left = d.iadd(sum, negated);
    d.ieq(left, v[0])
}

/// `le zero a → le b c → le (mul a b) (mul a c)`.
pub(super) fn mul_le_mul_of_nonneg_left(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let left = d.imul(v[0], v[1]);
    let right = d.imul(v[0], v[2]);
    let conclusion = d.ile(left, right);
    let second = d.ile(v[1], v[2]);
    let zero = d.izero();
    let first = d.ile(zero, v[0]);
    let after_second = d.arrow(second, conclusion);
    d.arrow(first, after_second)
}

/// `lt zero one`.
pub(super) fn zero_lt_one(d: &mut IntDev<'_>, _v: &[ExprId]) -> ExprId {
    let zero = d.izero();
    let one = d.ione();
    d.ilt(zero, one)
}

/// `Eq Int (mul a b) (mul b a)`.
pub(super) fn mul_comm(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let left = d.imul(v[0], v[1]);
    let right = d.imul(v[1], v[0]);
    d.ieq(left, right)
}

/// `Eq Int (mul (mul a b) c) (mul a (mul b c))`.
pub(super) fn mul_assoc(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let inner_left = d.imul(v[0], v[1]);
    let left = d.imul(inner_left, v[2]);
    let inner_right = d.imul(v[1], v[2]);
    let right = d.imul(v[0], inner_right);
    d.ieq(left, right)
}

/// `Eq Int (mul a one) a`.
pub(super) fn mul_one(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let one = d.ione();
    let left = d.imul(v[0], one);
    d.ieq(left, v[0])
}

/// `Eq Int (mul a zero) zero`.
pub(super) fn mul_zero(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let zero = d.izero();
    let left = d.imul(v[0], zero);
    let right = d.izero();
    d.ieq(left, right)
}

/// `Eq Int (mul a (add b c)) (add (mul a b) (mul a c))`.
pub(super) fn left_distrib(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let sum = d.iadd(v[1], v[2]);
    let left = d.imul(v[0], sum);
    let first = d.imul(v[0], v[1]);
    let second = d.imul(v[0], v[2]);
    let right = d.iadd(first, second);
    d.ieq(left, right)
}

/// `le zero a → le zero b → le zero (mul a b)`.
pub(super) fn mul_nonneg(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let zero = d.izero();
    let product = d.imul(v[0], v[1]);
    let conclusion = d.ile(zero, product);
    let second = d.ile(zero, v[1]);
    let first = d.ile(zero, v[0]);
    let after_second = d.arrow(second, conclusion);
    d.arrow(first, after_second)
}

/// `le zero (mul a a)`.
pub(super) fn sq_nonneg(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let zero = d.izero();
    let square = d.imul(v[0], v[0]);
    d.ile(zero, square)
}

/// `Not (And (lt zero a) (lt a one))`.
pub(super) fn no_int_between(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let zero = d.izero();
    let one = d.ione();
    let lower = d.ilt(zero, v[0]);
    let upper = d.ilt(v[0], one);
    let both = d.and(lower, upper);
    d.not(both)
}

/// `Or (le a b) (le b a)`.
pub(super) fn le_total(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let forward = d.ile(v[0], v[1]);
    let backward = d.ile(v[1], v[0]);
    d.or(forward, backward)
}

/// `le a b → Not (Eq Int a b) → lt a b`.
pub(super) fn lt_of_le_of_ne(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let conclusion = d.ilt(v[0], v[1]);
    let equality = d.ieq(v[0], v[1]);
    let distinct = d.not(equality);
    let bound = d.ile(v[0], v[1]);
    let after_distinct = d.arrow(distinct, conclusion);
    d.arrow(bound, after_distinct)
}

/// `Or (Eq Int a b) (Not (Eq Int a b))`.
pub(super) fn eq_em(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let equality = d.ieq(v[0], v[1]);
    let distinct = d.not(equality);
    d.or(equality, distinct)
}

/// `lt zero k → ∃ q r, t = k*q+r ∧ 0 ≤ r ∧ r < k`.
pub(super) fn euclidean_decomposition(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let (t, k) = (v[0], v[1]);
    let int_ty = d.int_ty();
    let one_level = d.level_one();
    let exists_name = d.int().logic.exists_;
    let anon = d.anon_name();

    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let product = d.imul(k, q);
    let sum = d.iadd(product, r);
    let equation = d.ieq(t, sum);
    let zero = d.izero();
    let lower = d.ile(zero, r);
    let upper = d.ilt(r, k);
    let bounds = d.and(lower, upper);
    let facts = d.and(equation, bounds);

    let r_predicate = d.lam_fv(r_fv, int_ty, facts);
    let exists = d.kernel().const_(exists_name, vec![one_level]);
    let exists_r = d.apply(exists, &[int_ty, r_predicate]);
    let q_predicate = d.lam_fv(q_fv, int_ty, exists_r);
    let exists = d.kernel().const_(exists_name, vec![one_level]);
    let exists_q = d.apply(exists, &[int_ty, q_predicate]);

    let positive = d.ilt(zero, k);
    d.kernel().pi(anon, positive, exists_q, BinderInfo::Default)
}
