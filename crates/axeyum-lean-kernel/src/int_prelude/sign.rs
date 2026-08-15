//! Sign bookkeeping for `Int.negOfNat`, and the two ring laws that need nothing
//! else.
//!
//! `Int.negOfNat k` is *stuck* on a variable `k`: it is a `Nat.rec`, so it only
//! computes once `k` is split into `0` or `succ j`. Every branch of `Int.mul`
//! with mixed signs produces one, so a product of three integers leaves a
//! `negOfNat` under another operation in six of its eight branches and nothing
//! reduces further.
//!
//! The four lemmas below are exactly that unsticking, one per surrounding
//! operation and sign, and each is a two-case `Nat.rec` in which both branches
//! close by `Eq.refl` or by one `Nat` rewrite. With them, `Int.mul_assoc` is
//! eight branches of `Nat.mul_assoc` — it never needs the `subNatNat` borrow at
//! all, which is why it is derived here rather than in [`super::sub_nat_nat`].

use super::ops::{IntDev, Shape, case_split};
use super::statements;
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// `Nat.zero_mul x : Eq Nat (0 * x) 0`.
fn zero_mul(d: &mut IntDev<'_>, x: ExprId) -> ExprId {
    let name = d.int().nat.zero_mul;
    d.const_app(name, &[x])
}

/// `Nat.mul_assoc a b c : Eq Nat ((a*b)*c) (a*(b*c))`.
fn nat_mul_assoc(d: &mut IntDev<'_>, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
    let name = d.int().nat.mul_assoc;
    d.const_app(name, &[a, b, c])
}

/// Both sides of a law whose two arguments are a `Nat`-indexed pair: a proof of
/// `Eq Int (ofNat t) (negOfNat t)` given `h : Eq Nat t 0`.
///
/// `negOfNat 0` ι-reduces to `ofNat 0`, so the two rewritten sides are the
/// *same* term and the composition needs no further step.
fn of_nat_eq_neg_of_nat(d: &mut IntDev<'_>, t: ExprId, h: ExprId) -> ExprId {
    let zero = d.zero();
    let left = d.of_nat(t);
    let middle = d.of_nat(zero);
    let right = d.neg_of_nat(t);
    let forward = d.nat_eq_to_int(t, zero, h, &|d, x| d.of_nat(x));
    let backward = {
        let step = d.nat_eq_to_int(t, zero, h, &|d, x| d.neg_of_nat(x));
        let negated = d.neg_of_nat(zero);
        d.isymm(right, negated, step)
    };
    d.itrans(left, middle, right, forward, backward)
}

/// Declare the four `negOfNat`-against-`Int.mul` lemmas.
pub(super) fn declare_sign_lemmas(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    // mul_ofNat_negOfNat : ofNat m * negOfNat k = negOfNat (m*k).
    // k = 0: both sides ι-reduce to `ofNat 0`. k = succ j: both to
    // `negOfNat (m * succ j)`. Neither branch uses the inductive hypothesis;
    // the recursion is only there to expose the constructor.
    d.theorem(p.mul_of_nat_neg_of_nat, 2, &|d, v| {
        let (m, k) = (v[0], v[1]);
        let motive = |d: &mut IntDev<'_>, t: ExprId| {
            let scale = d.of_nat(m);
            let negated = d.neg_of_nat(t);
            let left = d.imul(scale, negated);
            let product = NatOps::mul(d, m, t);
            let right = d.neg_of_nat(product);
            d.ieq(left, right)
        };
        let stmt = motive(d, k);
        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                let value = d.of_nat(zero);
                d.irefl(value)
            },
            &|d, j, _ih| {
                let successor = d.succ(j);
                let product = NatOps::mul(d, m, successor);
                let value = d.neg_of_nat(product);
                d.irefl(value)
            },
            k,
        );
        (stmt, proof)
    })?;

    // mul_negOfNat_ofNat : negOfNat k * ofNat n = negOfNat (k*n).
    // At `k = 0` the two sides are `ofNat (0*n)` and `negOfNat (0*n)`, and
    // `Nat.zero_mul` collapses both to the same `0`.
    d.theorem(p.mul_neg_of_nat_of_nat, 2, &|d, v| {
        let (k, n) = (v[0], v[1]);
        let motive = |d: &mut IntDev<'_>, t: ExprId| {
            let negated = d.neg_of_nat(t);
            let scale = d.of_nat(n);
            let left = d.imul(negated, scale);
            let product = NatOps::mul(d, t, n);
            let right = d.neg_of_nat(product);
            d.ieq(left, right)
        };
        let stmt = motive(d, k);
        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                let product = NatOps::mul(d, zero, n);
                let collapse = zero_mul(d, n);
                of_nat_eq_neg_of_nat(d, product, collapse)
            },
            &|d, j, _ih| {
                let successor = d.succ(j);
                let product = NatOps::mul(d, successor, n);
                let value = d.neg_of_nat(product);
                d.irefl(value)
            },
            k,
        );
        (stmt, proof)
    })?;

    // mul_negSucc_negOfNat : negSucc m * negOfNat k = ofNat ((m+1)*k).
    d.theorem(p.mul_neg_succ_neg_of_nat, 2, &|d, v| {
        let (m, k) = (v[0], v[1]);
        let motive = |d: &mut IntDev<'_>, t: ExprId| {
            let scale = d.neg_succ(m);
            let negated = d.neg_of_nat(t);
            let left = d.imul(scale, negated);
            let successor = d.succ(m);
            let product = NatOps::mul(d, successor, t);
            let right = d.of_nat(product);
            d.ieq(left, right)
        };
        let stmt = motive(d, k);
        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                let value = d.of_nat(zero);
                d.irefl(value)
            },
            &|d, j, _ih| {
                let left = d.succ(m);
                let right = d.succ(j);
                let product = NatOps::mul(d, left, right);
                let value = d.of_nat(product);
                d.irefl(value)
            },
            k,
        );
        (stmt, proof)
    })?;

    // mul_negOfNat_negSucc : negOfNat k * negSucc n = ofNat (k*(n+1)).
    d.theorem(p.mul_neg_of_nat_neg_succ, 2, &|d, v| {
        let (k, n) = (v[0], v[1]);
        let motive = |d: &mut IntDev<'_>, t: ExprId| {
            let negated = d.neg_of_nat(t);
            let scale = d.neg_succ(n);
            let left = d.imul(negated, scale);
            let successor = d.succ(n);
            let product = NatOps::mul(d, t, successor);
            let right = d.of_nat(product);
            d.ieq(left, right)
        };
        let stmt = motive(d, k);
        let proof = d.induct(
            &motive,
            &|d| {
                // `negOfNat (0*(n+1))` against `ofNat (0*(n+1))`, symmetrically
                // to the `mul_negOfNat_ofNat` base case.
                let zero = d.zero();
                let successor = d.succ(n);
                let product = NatOps::mul(d, zero, successor);
                let collapse = zero_mul(d, successor);
                let step = of_nat_eq_neg_of_nat(d, product, collapse);
                let left = d.of_nat(product);
                let right = d.neg_of_nat(product);
                d.isymm(left, right, step)
            },
            &|d, j, _ih| {
                let left = d.succ(j);
                let right = d.succ(n);
                let product = NatOps::mul(d, left, right);
                let value = d.of_nat(product);
                d.irefl(value)
            },
            k,
        );
        (stmt, proof)
    })?;

    Ok(())
}

/// Declare `Int.mul_assoc`.
///
/// Eight branches, each one application of `Nat.mul_assoc` to the two magnitudes
/// the branch's sign combination produces, wrapped in whichever constructor the
/// product lands in — `ofNat` when the number of negative factors is even,
/// `negOfNat` when it is odd. The four lemmas above are what let the middle
/// product be *named* at all in the six branches where it is a stuck
/// `negOfNat`.
pub(super) fn declare_mul_assoc(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mul_assoc, 3, &|d, v| {
        let stmt = statements::mul_assoc(d, v);
        let proof = case_split(d, v, &statements::mul_assoc, &|d, b| {
            let (m, n, q) = (b[0].1, b[1].1, b[2].1);
            let p = d.int();
            let lift_of_nat: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId = &|d, x| d.of_nat(x);
            let lift_neg: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId = &|d, x| d.neg_of_nat(x);
            match (b[0].0, b[1].0, b[2].0) {
                // (+,+,+): both sides are `ofNat` of a triple `Nat` product.
                (Shape::OfNat, Shape::OfNat, Shape::OfNat) => {
                    let left = {
                        let inner = NatOps::mul(d, m, n);
                        NatOps::mul(d, inner, q)
                    };
                    let right = {
                        let inner = NatOps::mul(d, n, q);
                        NatOps::mul(d, m, inner)
                    };
                    let step = nat_mul_assoc(d, m, n, q);
                    d.nat_eq_to_int(left, right, step, lift_of_nat)
                }
                // (+,+,−): the right side is `ofNat m * negOfNat (n*(q+1))`.
                (Shape::OfNat, Shape::OfNat, Shape::NegSucc) => {
                    let sq = d.succ(q);
                    let inner = NatOps::mul(d, n, sq);
                    let start = {
                        let mn = NatOps::mul(d, m, n);
                        let product = NatOps::mul(d, mn, sq);
                        d.neg_of_nat(product)
                    };
                    let middle = {
                        let product = NatOps::mul(d, m, inner);
                        d.neg_of_nat(product)
                    };
                    let end = {
                        let scale = d.of_nat(m);
                        let negated = d.neg_of_nat(inner);
                        d.imul(scale, negated)
                    };
                    let first = {
                        let lhs = {
                            let mn = NatOps::mul(d, m, n);
                            NatOps::mul(d, mn, sq)
                        };
                        let rhs = NatOps::mul(d, m, inner);
                        let step = nat_mul_assoc(d, m, n, sq);
                        d.nat_eq_to_int(lhs, rhs, step, lift_neg)
                    };
                    let second = {
                        let step = d.const_app(p.mul_of_nat_neg_of_nat, &[m, inner]);
                        d.isymm(end, middle, step)
                    };
                    d.itrans(start, middle, end, first, second)
                }
                // (+,−,+): a stuck `negOfNat` on each side.
                (Shape::OfNat, Shape::NegSucc, Shape::OfNat) => {
                    let sn = d.succ(n);
                    let scaled = NatOps::mul(d, m, sn);
                    let inner = NatOps::mul(d, sn, q);
                    let start = {
                        let negated = d.neg_of_nat(scaled);
                        let right = d.of_nat(q);
                        d.imul(negated, right)
                    };
                    let first_stop = {
                        let product = NatOps::mul(d, scaled, q);
                        d.neg_of_nat(product)
                    };
                    let second_stop = {
                        let product = NatOps::mul(d, m, inner);
                        d.neg_of_nat(product)
                    };
                    let end = {
                        let scale = d.of_nat(m);
                        let negated = d.neg_of_nat(inner);
                        d.imul(scale, negated)
                    };
                    let first = d.const_app(p.mul_neg_of_nat_of_nat, &[scaled, q]);
                    let second = {
                        let lhs = NatOps::mul(d, scaled, q);
                        let rhs = NatOps::mul(d, m, inner);
                        let step = nat_mul_assoc(d, m, sn, q);
                        d.nat_eq_to_int(lhs, rhs, step, lift_neg)
                    };
                    let third = {
                        let step = d.const_app(p.mul_of_nat_neg_of_nat, &[m, inner]);
                        d.isymm(end, second_stop, step)
                    };
                    let (_, proof) = d.ichain(
                        start,
                        &[(first_stop, first), (second_stop, second), (end, third)],
                    );
                    proof
                }
                // (+,−,−): two negative factors, so the product is non-negative.
                (Shape::OfNat, Shape::NegSucc, Shape::NegSucc) => {
                    let sn = d.succ(n);
                    let sq = d.succ(q);
                    let scaled = NatOps::mul(d, m, sn);
                    let start = {
                        let negated = d.neg_of_nat(scaled);
                        let right = d.neg_succ(q);
                        d.imul(negated, right)
                    };
                    let middle = {
                        let product = NatOps::mul(d, scaled, sq);
                        d.of_nat(product)
                    };
                    let end = {
                        let inner = NatOps::mul(d, sn, sq);
                        let product = NatOps::mul(d, m, inner);
                        d.of_nat(product)
                    };
                    let first = d.const_app(p.mul_neg_of_nat_neg_succ, &[scaled, q]);
                    let second = {
                        let lhs = NatOps::mul(d, scaled, sq);
                        let rhs = {
                            let inner = NatOps::mul(d, sn, sq);
                            NatOps::mul(d, m, inner)
                        };
                        let step = nat_mul_assoc(d, m, sn, sq);
                        d.nat_eq_to_int(lhs, rhs, step, lift_of_nat)
                    };
                    d.itrans(start, middle, end, first, second)
                }
                // (−,+,+): one negative factor.
                (Shape::NegSucc, Shape::OfNat, Shape::OfNat) => {
                    let sm = d.succ(m);
                    let scaled = NatOps::mul(d, sm, n);
                    let start = {
                        let negated = d.neg_of_nat(scaled);
                        let right = d.of_nat(q);
                        d.imul(negated, right)
                    };
                    let middle = {
                        let product = NatOps::mul(d, scaled, q);
                        d.neg_of_nat(product)
                    };
                    let end = {
                        let inner = NatOps::mul(d, n, q);
                        let product = NatOps::mul(d, sm, inner);
                        d.neg_of_nat(product)
                    };
                    let first = d.const_app(p.mul_neg_of_nat_of_nat, &[scaled, q]);
                    let second = {
                        let lhs = NatOps::mul(d, scaled, q);
                        let rhs = {
                            let inner = NatOps::mul(d, n, q);
                            NatOps::mul(d, sm, inner)
                        };
                        let step = nat_mul_assoc(d, sm, n, q);
                        d.nat_eq_to_int(lhs, rhs, step, lift_neg)
                    };
                    d.itrans(start, middle, end, first, second)
                }
                // (−,+,−): two negative factors.
                (Shape::NegSucc, Shape::OfNat, Shape::NegSucc) => {
                    let sm = d.succ(m);
                    let sq = d.succ(q);
                    let scaled = NatOps::mul(d, sm, n);
                    let inner = NatOps::mul(d, n, sq);
                    let start = {
                        let negated = d.neg_of_nat(scaled);
                        let right = d.neg_succ(q);
                        d.imul(negated, right)
                    };
                    let first_stop = {
                        let product = NatOps::mul(d, scaled, sq);
                        d.of_nat(product)
                    };
                    let second_stop = {
                        let product = NatOps::mul(d, sm, inner);
                        d.of_nat(product)
                    };
                    let end = {
                        let scale = d.neg_succ(m);
                        let negated = d.neg_of_nat(inner);
                        d.imul(scale, negated)
                    };
                    let first = d.const_app(p.mul_neg_of_nat_neg_succ, &[scaled, q]);
                    let second = {
                        let lhs = NatOps::mul(d, scaled, sq);
                        let rhs = NatOps::mul(d, sm, inner);
                        let step = nat_mul_assoc(d, sm, n, sq);
                        d.nat_eq_to_int(lhs, rhs, step, lift_of_nat)
                    };
                    let third = {
                        let step = d.const_app(p.mul_neg_succ_neg_of_nat, &[m, inner]);
                        d.isymm(end, second_stop, step)
                    };
                    let (_, proof) = d.ichain(
                        start,
                        &[(first_stop, first), (second_stop, second), (end, third)],
                    );
                    proof
                }
                // (−,−,+): two negative factors, and the left association has
                // already computed to `ofNat`.
                (Shape::NegSucc, Shape::NegSucc, Shape::OfNat) => {
                    let sm = d.succ(m);
                    let sn = d.succ(n);
                    let inner = NatOps::mul(d, sn, q);
                    let start = {
                        let product = {
                            let scaled = NatOps::mul(d, sm, sn);
                            NatOps::mul(d, scaled, q)
                        };
                        d.of_nat(product)
                    };
                    let middle = {
                        let product = NatOps::mul(d, sm, inner);
                        d.of_nat(product)
                    };
                    let end = {
                        let scale = d.neg_succ(m);
                        let negated = d.neg_of_nat(inner);
                        d.imul(scale, negated)
                    };
                    let first = {
                        let lhs = {
                            let scaled = NatOps::mul(d, sm, sn);
                            NatOps::mul(d, scaled, q)
                        };
                        let rhs = NatOps::mul(d, sm, inner);
                        let step = nat_mul_assoc(d, sm, sn, q);
                        d.nat_eq_to_int(lhs, rhs, step, lift_of_nat)
                    };
                    let second = {
                        let step = d.const_app(p.mul_neg_succ_neg_of_nat, &[m, inner]);
                        d.isymm(end, middle, step)
                    };
                    d.itrans(start, middle, end, first, second)
                }
                // (−,−,−): three negative factors.
                (Shape::NegSucc, Shape::NegSucc, Shape::NegSucc) => {
                    let sm = d.succ(m);
                    let sn = d.succ(n);
                    let sq = d.succ(q);
                    let left = {
                        let scaled = NatOps::mul(d, sm, sn);
                        NatOps::mul(d, scaled, sq)
                    };
                    let right = {
                        let inner = NatOps::mul(d, sn, sq);
                        NatOps::mul(d, sm, inner)
                    };
                    let step = nat_mul_assoc(d, sm, sn, sq);
                    d.nat_eq_to_int(left, right, step, lift_neg)
                }
            }
        });
        (stmt, proof)
    })?;
    Ok(())
}
