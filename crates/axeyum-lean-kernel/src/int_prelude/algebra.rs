//! The **ring** laws of `ℤ` that this development derives, each from the
//! corresponding axiom-free `Nat` law.
//!
//! Two shapes recur:
//!
//! - A branch where both arguments have the same sign reduces to `Nat`
//!   arithmetic inside one constructor, so the proof is the `Nat` lemma pushed
//!   through `Int.ofNat`, `Int.negSucc` or `Int.negOfNat` by
//!   [`IntDev::nat_eq_to_int`](super::ops::IntDev::nat_eq_to_int).
//! - A branch where the two `Int.add` cases are *literally the same term* — the
//!   mixed-sign cases both reduce to `Int.subNatNat m (succ n)` — needs no
//!   argument at all: `Eq.refl` closes it.
//!
//! `add_neg` is the one law that needs a genuine lemma rather than a transport:
//! `Int.subNatNat n n = 0`, which holds because `Nat.sub_self` collapses both
//! the scrutinee and the non-negative branch of `subNatNat` at once.

use super::ops::{IntDev, Shape, case_split};
use super::statements;
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// `fun t : Nat => Nat.rec.{1} (fun _ => Int) (Int.ofNat t) (fun k _ => Int.negSucc k) t`,
/// applied to `t`.
///
/// This is exactly `Int.subNatNat n n` with the *single* occurrence `Nat.sub n n`
/// abstracted: `subNatNat` puts that difference in both its non-negative value
/// and its scrutinee, so the diagonal is a one-hole context and one rewrite by
/// `Nat.sub_self` closes both.
fn diagonal(d: &mut IntDev<'_>, t: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let motive = d.kernel().lam(anon, nat, int_ty, BinderInfo::Default);
    let minor_zero = d.of_nat(t);
    let minor_succ = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let ih_fv = d.fresh_fvar();
        let body = d.neg_succ(k);
        let inner = d.lam_fv(ih_fv, int_ty, body);
        d.lam_fv(k_fv, nat, inner)
    };
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[motive, minor_zero, minor_succ, t])
}

/// A proof of `Eq Int (Int.subNatNat t t) Int.zero`.
fn sub_nat_nat_self(d: &mut IntDev<'_>, t: ExprId) -> ExprId {
    let difference = d.sub(t, t);
    let zero = d.zero();
    let sub_self = d.int().nat.sub_self;
    let collapse = d.const_app(sub_self, &[t]);
    d.nat_eq_to_int(difference, zero, collapse, &diagonal)
}

/// Declare every ring law this development derives.
pub(super) fn declare_algebra_theorems(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    // add_zero : ∀ a, add a zero = a. Both branches hold by ι/δ alone:
    // `Nat.add x zero ≡ x` for the non-negative one, and `Nat.sub x zero ≡ x`
    // makes `subNatNat 0 (succ m)` reduce straight back to `negSucc m`.
    d.int_theorem(p.add_zero, 1, &|d, v| {
        let stmt = statements::add_zero(d, v);
        let proof = case_split(d, v, &statements::add_zero, &|d, b| {
            let value = d.branch_term(b[0]);
            d.irefl(value)
        });
        (stmt, proof)
    })?;

    // add_comm : ∀ a b, add a b = add b a.
    d.int_theorem(p.add_comm, 2, &|d, v| {
        let stmt = statements::add_comm(d, v);
        let proof = case_split(d, v, &statements::add_comm, &|d, b| {
            let (m, n) = (b[0].1, b[1].1);
            let commute = d.int().nat.add_comm;
            match (b[0].0, b[1].0) {
                (Shape::OfNat, Shape::OfNat) => {
                    let left = NatOps::add(d, m, n);
                    let right = NatOps::add(d, n, m);
                    let step = d.const_app(commute, &[m, n]);
                    d.nat_eq_to_int(left, right, step, &|d, x| d.of_nat(x))
                }
                (Shape::NegSucc, Shape::NegSucc) => {
                    let left = NatOps::add(d, m, n);
                    let right = NatOps::add(d, n, m);
                    let step = d.const_app(commute, &[m, n]);
                    d.nat_eq_to_int(left, right, step, &|d, x| {
                        let successor = d.succ(x);
                        d.neg_succ(successor)
                    })
                }
                // Both mixed cases of `Int.add` are the same `subNatNat` term.
                (Shape::OfNat, Shape::NegSucc) => {
                    let successor = d.succ(n);
                    let value = d.sub_nat_nat(m, successor);
                    d.irefl(value)
                }
                (Shape::NegSucc, Shape::OfNat) => {
                    let successor = d.succ(m);
                    let value = d.sub_nat_nat(n, successor);
                    d.irefl(value)
                }
            }
        });
        (stmt, proof)
    })?;

    // add_neg : ∀ a, add a (neg a) = zero.
    //
    // `Int.neg (ofNat n)` is `Int.negOfNat n`, which is *stuck* on a variable
    // `n`, so the non-negative branch splits `n` as well: at `0` both summands
    // are `ofNat 0`, and at `succ k` the sum is the diagonal `subNatNat`.
    d.int_theorem(p.add_neg, 1, &|d, v| {
        let stmt = statements::add_neg(d, v);
        let proof = case_split(d, v, &statements::add_neg, &|d, b| {
            let n = b[0].1;
            match b[0].0 {
                Shape::OfNat => d.induct(
                    &|d, x| {
                        let value = d.of_nat(x);
                        statements::add_neg(d, &[value])
                    },
                    &|d| {
                        let zero = d.izero();
                        d.irefl(zero)
                    },
                    &|d, j, _ih| {
                        let successor = d.succ(j);
                        sub_nat_nat_self(d, successor)
                    },
                    n,
                ),
                Shape::NegSucc => {
                    let successor = d.succ(n);
                    sub_nat_nat_self(d, successor)
                }
            }
        });
        (stmt, proof)
    })?;

    // mul_zero : ∀ a, mul a zero = zero — `Nat.mul x zero ≡ zero` and
    // `Int.negOfNat 0 ≡ Int.ofNat 0`, so both branches are `Eq.refl`.
    d.int_theorem(p.mul_zero, 1, &|d, v| {
        let stmt = statements::mul_zero(d, v);
        let proof = case_split(d, v, &statements::mul_zero, &|d, _b| {
            let zero = d.izero();
            d.irefl(zero)
        });
        (stmt, proof)
    })?;

    // mul_one : ∀ a, mul a one = a.
    d.int_theorem(p.mul_one, 1, &|d, v| {
        let stmt = statements::mul_one(d, v);
        let proof = case_split(d, v, &statements::mul_one, &|d, b| {
            let n = b[0].1;
            let unit = d.num(1);
            let mul_one = d.int().nat.mul_one;
            match b[0].0 {
                Shape::OfNat => {
                    let left = NatOps::mul(d, n, unit);
                    let step = d.const_app(mul_one, &[n]);
                    d.nat_eq_to_int(left, n, step, &|d, x| d.of_nat(x))
                }
                Shape::NegSucc => {
                    let successor = d.succ(n);
                    let left = NatOps::mul(d, successor, unit);
                    let step = d.const_app(mul_one, &[successor]);
                    d.nat_eq_to_int(left, successor, step, &|d, x| d.neg_of_nat(x))
                }
            }
        });
        (stmt, proof)
    })?;

    // mul_comm : ∀ a b, mul a b = mul b a. Every branch is `Nat.mul_comm`
    // pushed through the constructor that branch's product lands in.
    d.int_theorem(p.mul_comm, 2, &|d, v| {
        let stmt = statements::mul_comm(d, v);
        let proof = case_split(d, v, &statements::mul_comm, &|d, b| {
            let commute = d.int().nat.mul_comm;
            let lift_of_nat: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId = &|d, x| d.of_nat(x);
            let lift_neg: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId = &|d, x| d.neg_of_nat(x);
            // The `Nat` factors of this branch, and the constructor its
            // product lands in: negative exactly when the signs differ.
            let (left_factor, right_factor, lift) = match (b[0].0, b[1].0) {
                (Shape::OfNat, Shape::OfNat) => (b[0].1, b[1].1, lift_of_nat),
                (Shape::OfNat, Shape::NegSucc) => {
                    let successor = d.succ(b[1].1);
                    (b[0].1, successor, lift_neg)
                }
                (Shape::NegSucc, Shape::OfNat) => {
                    let successor = d.succ(b[0].1);
                    (successor, b[1].1, lift_neg)
                }
                (Shape::NegSucc, Shape::NegSucc) => {
                    let left = d.succ(b[0].1);
                    let right = d.succ(b[1].1);
                    (left, right, lift_of_nat)
                }
            };
            let left = NatOps::mul(d, left_factor, right_factor);
            let right = NatOps::mul(d, right_factor, left_factor);
            let step = d.const_app(commute, &[left_factor, right_factor]);
            d.nat_eq_to_int(left, right, step, lift)
        });
        (stmt, proof)
    })?;

    // mul_nonneg : ∀ a b, 0 ≤ a → 0 ≤ b → 0 ≤ a*b. Only one of the four
    // branches survives: `Int.le zero (negSucc _)` reduces to `False`, so a
    // negative factor refutes its own hypothesis, and the surviving branch is
    // `Nat.zero_le`.
    d.int_theorem(p.mul_nonneg, 2, &|d, v| {
        let stmt = statements::mul_nonneg(d, v);
        let proof = case_split(d, v, &statements::mul_nonneg, &|d, b| {
            let left = d.branch_term(b[0]);
            let right = d.branch_term(b[1]);
            let zero = d.izero();
            let first = d.ile(zero, left);
            let second = d.ile(zero, right);
            let product = d.imul(left, right);
            let goal = d.ile(zero, product);
            let (m, n) = (b[0].1, b[1].1);
            with_hypotheses(d, &[first, second], &|d, h| match (b[0].0, b[1].0) {
                (Shape::OfNat, Shape::OfNat) => {
                    let magnitude = NatOps::mul(d, m, n);
                    let name = d.int().nat.zero_le;
                    d.const_app(name, &[magnitude])
                }
                (Shape::OfNat, Shape::NegSucc) => d.absurd(goal, h[1]),
                (Shape::NegSucc, _) => d.absurd(goal, h[0]),
            })
        });
        (stmt, proof)
    })?;

    Ok(())
}

/// `fun (h_0 : tys[0]) … => body(h_0, …)` — the same binder helper the order
/// module uses, kept local so neither module has to depend on the other.
fn with_hypotheses(
    d: &mut IntDev<'_>,
    tys: &[ExprId],
    body: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> ExprId,
) -> ExprId {
    let fvs: Vec<u64> = (0..tys.len()).map(|_| d.fresh_fvar()).collect();
    let hypotheses: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    let mut term = body(d, &hypotheses);
    for (index, &fv) in fvs.iter().enumerate().rev() {
        term = d.lam_fv(fv, tys[index], term);
    }
    term
}
