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
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::linarith::int as linarith;
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

    // one_mul : ∀ a, mul one a = a, obtained from commutativity and the
    // already checked right-unit law. Keeping this derivation explicit makes
    // the dependency visible in the exported theorem capsule.
    d.int_theorem(p.one_mul, 1, &|d, v| {
        let stmt = statements::one_mul(d, v);
        let one = d.ione();
        let left = d.imul(one, v[0]);
        let middle = d.imul(v[0], one);
        let commute = d.const_app(p.mul_comm, &[one, v[0]]);
        let identity = d.const_app(p.mul_one, &[v[0]]);
        let proof = d.itrans(left, middle, v[0], commute, identity);
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

    // mul_pos : ∀ a b, 0 < a → 0 < b → 0 < a*b. Same branch shape as
    // `mul_nonneg` — only `(OfNat, OfNat)` survives — but the surviving branch
    // needs an actual argument, because no strict positive-product lemma
    // exists over `Nat` here: `0 < m` is `Nat.le 1 m`, so `m*1 ≤ m*n`
    // (`Nat.mul_le_mul_left` at the hypothesis `1 ≤ n`) rewritten along
    // `Nat.mul_one` gives `m ≤ m*n`, and `Nat.le_trans` chains that under
    // `1 ≤ m` to `1 ≤ m*n`, i.e. `0 < m*n`. No new `Nat` lemma.
    d.int_theorem(p.mul_pos, 2, &|d, v| {
        let stmt = statements::mul_pos(d, v);
        let proof = case_split(d, v, &statements::mul_pos, &|d, b| {
            let left = d.branch_term(b[0]);
            let right = d.branch_term(b[1]);
            let zero = d.izero();
            let first = d.ilt(zero, left);
            let second = d.ilt(zero, right);
            let product = d.imul(left, right);
            let goal = d.ilt(zero, product);
            let (m, n) = (b[0].1, b[1].1);
            with_hypotheses(d, &[first, second], &|d, h| match (b[0].0, b[1].0) {
                (Shape::OfNat, Shape::OfNat) => {
                    let one = d.num(1);
                    let m1 = NatOps::mul(d, m, one);
                    let mn = NatOps::mul(d, m, n);
                    let step1 = {
                        let name = d.int().nat.mul_le_mul_left;
                        d.const_app(name, &[m, one, n, h[1]])
                    };
                    let mul_one_eq = {
                        let name = d.int().nat.mul_one;
                        d.const_app(name, &[m])
                    };
                    let rewritten =
                        d.nat_rewrite(m1, m, mul_one_eq, step1, &|d, t| NatOps::le(d, t, mn));
                    let name = d.int().nat.le_trans;
                    d.const_app(name, &[one, m, mn, h[0], rewritten])
                }
                (Shape::OfNat, Shape::NegSucc) => d.absurd(goal, h[1]),
                (Shape::NegSucc, _) => d.absurd(goal, h[0]),
            })
        });
        (stmt, proof)
    })?;

    // sq_nonneg : ∀ a, 0 ≤ a*a. Unconditional, unlike `mul_nonneg` — and the
    // reason it is unconditional is structural rather than argued: `Int.mul`
    // sends *both* same-sign branches into `Int.ofNat` (`ofNat m * ofNat m` is
    // `ofNat (m*m)`, `negSucc m * negSucc m` is `ofNat (succ m * succ m)`), and
    // a square is always same-sign. So neither branch has a hypothesis to use
    // or refute; both are `Nat.zero_le` at the magnitude the branch produced.
    d.int_theorem(p.sq_nonneg, 1, &|d, v| {
        let stmt = statements::sq_nonneg(d, v);
        let proof = case_split(d, v, &statements::sq_nonneg, &|d, b| {
            let n = b[0].1;
            let magnitude = match b[0].0 {
                Shape::OfNat => NatOps::mul(d, n, n),
                Shape::NegSucc => {
                    let successor = d.succ(n);
                    NatOps::mul(d, successor, successor)
                }
            };
            let name = d.int().nat.zero_le;
            d.const_app(name, &[magnitude])
        });
        (stmt, proof)
    })?;

    Ok(())
}

/// `Eq Nat ((n+1)+(q+1)) (((n+q)+1)+1)` — the carry that every branch mixing
/// two `negSucc`s produces, since `Int.add (negSucc n) (negSucc q)` normalises
/// its magnitude one way and `Nat.add` on two successors normalises it the
/// other.
fn two_successors(d: &mut IntDev<'_>, n: ExprId, q: ExprId) -> ExprId {
    let raised = {
        let flat = NatOps::add(d, n, q);
        d.succ(flat)
    };
    let successor = d.succ(n);
    let shifted = NatOps::add(d, successor, q);
    let step = {
        let name = d.int().nat.succ_add;
        d.const_app(name, &[n, q])
    };
    // `(n+1)+(q+1)` is definitionally `((n+1)+q)+1`, so lifting `Nat.succ_add`
    // under one `Nat.succ` already lands on both sides of the statement.
    d.congr(shifted, raised, step, &|d, t| d.succ(t))
}

/// Declare `Int.add_assoc`.
///
/// Eight branches. The three that mix signs on both sides are the ones the
/// borrow blocked, and each is now one application of the `subNatNat`
/// re-association lemmas plus, at most, a `Nat` carry.
pub(super) fn declare_add_assoc(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.add_assoc, 3, &|d, v| {
        let stmt = statements::add_assoc(d, v);
        let proof = case_split(d, v, &statements::add_assoc, &|d, b| {
            let (m, n, q) = (b[0].1, b[1].1, b[2].1);
            let p = d.int();
            match (b[0].0, b[1].0, b[2].0) {
                // (+,+,+): `Nat.add_assoc` under `ofNat`.
                (Shape::OfNat, Shape::OfNat, Shape::OfNat) => {
                    let left = {
                        let inner = NatOps::add(d, m, n);
                        NatOps::add(d, inner, q)
                    };
                    let right = {
                        let inner = NatOps::add(d, n, q);
                        NatOps::add(d, m, inner)
                    };
                    let step = {
                        let name = p.nat.add_assoc;
                        d.const_app(name, &[m, n, q])
                    };
                    d.nat_eq_to_int(left, right, step, &|d, x| d.of_nat(x))
                }
                // (+,+,−): the right association is a `subNatNat` absorbing an
                // `ofNat` on its left.
                (Shape::OfNat, Shape::OfNat, Shape::NegSucc) => {
                    let sq = d.succ(q);
                    let step = d.const_app(p.of_nat_add_sub_nat_nat, &[m, n, sq]);
                    let from = {
                        let scale = d.of_nat(m);
                        let borrowed = d.sub_nat_nat(n, sq);
                        d.iadd(scale, borrowed)
                    };
                    let to = {
                        let sum = NatOps::add(d, m, n);
                        d.sub_nat_nat(sum, sq)
                    };
                    d.isymm(from, to, step)
                }
                // (+,−,+): both sides absorb an `ofNat`, from opposite sides.
                (Shape::OfNat, Shape::NegSucc, Shape::OfNat) => {
                    let sn = d.succ(n);
                    let start = {
                        let borrowed = d.sub_nat_nat(m, sn);
                        let scale = d.of_nat(q);
                        d.iadd(borrowed, scale)
                    };
                    let middle = {
                        let sum = NatOps::add(d, m, q);
                        d.sub_nat_nat(sum, sn)
                    };
                    let end = {
                        let scale = d.of_nat(m);
                        let borrowed = d.sub_nat_nat(q, sn);
                        d.iadd(scale, borrowed)
                    };
                    let first = d.const_app(p.sub_nat_nat_add_of_nat, &[m, sn, q]);
                    let second = {
                        let step = d.const_app(p.of_nat_add_sub_nat_nat, &[m, q, sn]);
                        d.isymm(end, middle, step)
                    };
                    d.itrans(start, middle, end, first, second)
                }
                // (+,−,−): a `subNatNat` absorbing a `negSucc`, then the carry.
                (Shape::OfNat, Shape::NegSucc, Shape::NegSucc) => {
                    let sn = d.succ(n);
                    let sq = d.succ(q);
                    let start = {
                        let borrowed = d.sub_nat_nat(m, sn);
                        let negative = d.neg_succ(q);
                        d.iadd(borrowed, negative)
                    };
                    let middle = {
                        let sum = NatOps::add(d, sn, sq);
                        d.sub_nat_nat(m, sum)
                    };
                    let end = {
                        let raised = {
                            let flat = NatOps::add(d, n, q);
                            d.succ(flat)
                        };
                        let doubled = d.succ(raised);
                        d.sub_nat_nat(m, doubled)
                    };
                    let first = d.const_app(p.sub_nat_nat_add_neg_succ, &[m, sn, q]);
                    let second = {
                        let carry = two_successors(d, n, q);
                        let from = NatOps::add(d, sn, sq);
                        let to = {
                            let raised = {
                                let flat = NatOps::add(d, n, q);
                                d.succ(flat)
                            };
                            d.succ(raised)
                        };
                        d.nat_eq_to_int(from, to, carry, &|d, t| d.sub_nat_nat(m, t))
                    };
                    d.itrans(start, middle, end, first, second)
                }
                // (−,+,+): both sides are the same `subNatNat` absorbing `ofNat q`.
                (Shape::NegSucc, Shape::OfNat, Shape::OfNat) => {
                    let sm = d.succ(m);
                    d.const_app(p.sub_nat_nat_add_of_nat, &[n, sm, q])
                }
                // (−,+,−): both sides absorb a `negSucc`, from opposite sides,
                // and the two excesses differ by `Nat.add_comm`.
                (Shape::NegSucc, Shape::OfNat, Shape::NegSucc) => {
                    let sm = d.succ(m);
                    let sq = d.succ(q);
                    let start = {
                        let borrowed = d.sub_nat_nat(n, sm);
                        let negative = d.neg_succ(q);
                        d.iadd(borrowed, negative)
                    };
                    let middle = {
                        let sum = NatOps::add(d, sm, sq);
                        d.sub_nat_nat(n, sum)
                    };
                    let swapped = {
                        let sum = NatOps::add(d, sq, sm);
                        d.sub_nat_nat(n, sum)
                    };
                    let end = {
                        let negative = d.neg_succ(m);
                        let borrowed = d.sub_nat_nat(n, sq);
                        d.iadd(negative, borrowed)
                    };
                    let first = d.const_app(p.sub_nat_nat_add_neg_succ, &[n, sm, q]);
                    let second = {
                        let from = NatOps::add(d, sm, sq);
                        let to = NatOps::add(d, sq, sm);
                        let h = {
                            let name = p.nat.add_comm;
                            d.const_app(name, &[sm, sq])
                        };
                        d.nat_eq_to_int(from, to, h, &|d, t| d.sub_nat_nat(n, t))
                    };
                    let third = {
                        let step = d.const_app(p.neg_succ_add_sub_nat_nat, &[m, n, sq]);
                        d.isymm(end, swapped, step)
                    };
                    let (_, proof) =
                        d.ichain(start, &[(middle, first), (swapped, second), (end, third)]);
                    proof
                }
                // (−,−,+): the left association has already carried, so the
                // `Nat` step runs the other way.
                (Shape::NegSucc, Shape::NegSucc, Shape::OfNat) => {
                    let sm = d.succ(m);
                    let sn = d.succ(n);
                    let start = {
                        let raised = {
                            let flat = NatOps::add(d, m, n);
                            d.succ(flat)
                        };
                        let doubled = d.succ(raised);
                        d.sub_nat_nat(q, doubled)
                    };
                    let middle = {
                        let sum = NatOps::add(d, sn, sm);
                        d.sub_nat_nat(q, sum)
                    };
                    let end = {
                        let negative = d.neg_succ(m);
                        let borrowed = d.sub_nat_nat(q, sn);
                        d.iadd(negative, borrowed)
                    };
                    let first = {
                        // `((m+n)+1)+1 = (n+1)+(m+1)`: commute, then uncarry.
                        let flat = NatOps::add(d, m, n);
                        let swapped = NatOps::add(d, n, m);
                        let commute = {
                            let name = p.nat.add_comm;
                            d.const_app(name, &[m, n])
                        };
                        let lifted = d.congr(flat, swapped, commute, &|d, t| {
                            let raised = d.succ(t);
                            d.succ(raised)
                        });
                        let carry = two_successors(d, n, m);
                        let from = {
                            let raised = d.succ(flat);
                            d.succ(raised)
                        };
                        let via = {
                            let raised = d.succ(swapped);
                            d.succ(raised)
                        };
                        let to = NatOps::add(d, sn, sm);
                        let uncarry = d.symm(to, via, carry);
                        let (_, joined) = d.chain(from, &[(via, lifted), (to, uncarry)]);
                        d.nat_eq_to_int(from, to, joined, &|d, t| d.sub_nat_nat(q, t))
                    };
                    let second = {
                        let step = d.const_app(p.neg_succ_add_sub_nat_nat, &[m, q, sn]);
                        d.isymm(end, middle, step)
                    };
                    d.itrans(start, middle, end, first, second)
                }
                // (−,−,−): entirely inside `negSucc`, so it is `Nat.add_assoc`
                // with one `Nat.succ_add` to line the carries up.
                (Shape::NegSucc, Shape::NegSucc, Shape::NegSucc) => {
                    let flat = NatOps::add(d, m, n);
                    let raised = d.succ(flat);
                    let start = NatOps::add(d, raised, q);
                    let via = {
                        let inner = NatOps::add(d, flat, q);
                        d.succ(inner)
                    };
                    let step_one = {
                        let name = p.nat.succ_add;
                        d.const_app(name, &[flat, q])
                    };
                    let end = {
                        let inner = NatOps::add(d, n, q);
                        let bumped = d.succ(inner);
                        NatOps::add(d, m, bumped)
                    };
                    let step_two = {
                        let regroup = {
                            let name = p.nat.add_assoc;
                            d.const_app(name, &[m, n, q])
                        };
                        let from = NatOps::add(d, flat, q);
                        let to = {
                            let inner = NatOps::add(d, n, q);
                            NatOps::add(d, m, inner)
                        };
                        d.congr(from, to, regroup, &|d, t| d.succ(t))
                    };
                    let (_, joined) = d.chain(start, &[(via, step_one), (end, step_two)]);
                    d.nat_eq_to_int(start, end, joined, &|d, t| {
                        let bumped = d.succ(t);
                        d.neg_succ(bumped)
                    })
                }
            }
        });
        (stmt, proof)
    })?;

    // add_neg_cancel_right : ∀ a b, (a+b)+(-b) = a.  This is deliberately
    // derived here rather than imported from Mathlib: reassociate, discharge
    // `b + -b` with `add_neg`, then remove the resulting zero.
    linarith::declare(d, &p, p.add_neg_cancel_right, 2, &|d, v| {
        let stmt = statements::add_neg_cancel_right(d, v);
        (vec![], stmt)
    })?;
    Ok(())
}

/// Declare `Int.left_distrib`.
///
/// Eight branches again, but the shape is uniform: reduce `b + c` to whichever
/// normal form its two signs give, push the scale through it with the
/// `subNatNat` multiplication lemmas, and re-assemble the right-hand side with
/// the `negOfNat` addition lemmas. `Nat.left_distrib` is the only arithmetic.
pub(super) fn declare_left_distrib(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.left_distrib, 3, &|d, v| {
        let stmt = statements::left_distrib(d, v);
        let proof = case_split(d, v, &statements::left_distrib, &|d, b| {
            let (m, n, q) = (b[0].1, b[1].1, b[2].1);
            let p = d.int();
            // The magnitude of the scale, and the constructor a *positive*
            // product lands in for this sign of `a`.
            let negative_scale = matches!(b[0].0, Shape::NegSucc);
            let scale = if negative_scale { d.succ(m) } else { m };
            match (b[1].0, b[2].0) {
                // Both summands non-negative: one `Nat.left_distrib`, wrapped in
                // `ofNat` or `negOfNat` according to the scale's sign.
                (Shape::OfNat, Shape::OfNat) => {
                    let sum = NatOps::add(d, n, q);
                    let joined = NatOps::mul(d, scale, sum);
                    let split = {
                        let left = NatOps::mul(d, scale, n);
                        let right = NatOps::mul(d, scale, q);
                        NatOps::add(d, left, right)
                    };
                    let step = {
                        let name = p.nat.left_distrib;
                        d.const_app(name, &[scale, n, q])
                    };
                    if negative_scale {
                        let start = d.neg_of_nat(joined);
                        let middle = d.neg_of_nat(split);
                        let first = d.nat_eq_to_int(joined, split, step, &|d, t| d.neg_of_nat(t));
                        let end = {
                            let left = NatOps::mul(d, scale, n);
                            let right = NatOps::mul(d, scale, q);
                            let a = d.neg_of_nat(left);
                            let c = d.neg_of_nat(right);
                            d.iadd(a, c)
                        };
                        let second = {
                            let left = NatOps::mul(d, scale, n);
                            let right = NatOps::mul(d, scale, q);
                            let regroup = d.const_app(p.neg_of_nat_add_neg_of_nat, &[left, right]);
                            d.isymm(end, middle, regroup)
                        };
                        d.itrans(start, middle, end, first, second)
                    } else {
                        d.nat_eq_to_int(joined, split, step, &|d, t| d.of_nat(t))
                    }
                }
                // `b + c` normalises to `subNatNat n (q+1)`.
                (Shape::OfNat, Shape::NegSucc) => {
                    let sq = d.succ(q);
                    let scaled_left = NatOps::mul(d, scale, n);
                    let scaled_right = NatOps::mul(d, scale, sq);
                    if negative_scale {
                        let start = {
                            let negative = d.neg_succ(m);
                            let borrowed = d.sub_nat_nat(n, sq);
                            d.imul(negative, borrowed)
                        };
                        let middle = d.sub_nat_nat(scaled_right, scaled_left);
                        let end = {
                            let a = d.neg_of_nat(scaled_left);
                            let c = d.of_nat(scaled_right);
                            d.iadd(a, c)
                        };
                        let first = d.const_app(p.neg_succ_mul_sub_nat_nat, &[m, n, sq]);
                        let second = {
                            let step =
                                d.const_app(p.neg_of_nat_add_of_nat, &[scaled_left, scaled_right]);
                            d.isymm(end, middle, step)
                        };
                        d.itrans(start, middle, end, first, second)
                    } else {
                        let start = {
                            let positive = d.of_nat(m);
                            let borrowed = d.sub_nat_nat(n, sq);
                            d.imul(positive, borrowed)
                        };
                        let middle = d.sub_nat_nat(scaled_left, scaled_right);
                        let end = {
                            let a = d.of_nat(scaled_left);
                            let c = d.neg_of_nat(scaled_right);
                            d.iadd(a, c)
                        };
                        let first = d.const_app(p.of_nat_mul_sub_nat_nat, &[m, n, sq]);
                        let second = {
                            let step =
                                d.const_app(p.of_nat_add_neg_of_nat, &[scaled_left, scaled_right]);
                            d.isymm(end, middle, step)
                        };
                        d.itrans(start, middle, end, first, second)
                    }
                }
                // `b + c` normalises to `subNatNat q (n+1)`.
                (Shape::NegSucc, Shape::OfNat) => {
                    let sn = d.succ(n);
                    let scaled_left = NatOps::mul(d, scale, q);
                    let scaled_right = NatOps::mul(d, scale, sn);
                    if negative_scale {
                        let start = {
                            let negative = d.neg_succ(m);
                            let borrowed = d.sub_nat_nat(q, sn);
                            d.imul(negative, borrowed)
                        };
                        let middle = d.sub_nat_nat(scaled_right, scaled_left);
                        let end = {
                            let a = d.of_nat(scaled_right);
                            let c = d.neg_of_nat(scaled_left);
                            d.iadd(a, c)
                        };
                        let first = d.const_app(p.neg_succ_mul_sub_nat_nat, &[m, q, sn]);
                        let second = {
                            let step =
                                d.const_app(p.of_nat_add_neg_of_nat, &[scaled_right, scaled_left]);
                            d.isymm(end, middle, step)
                        };
                        d.itrans(start, middle, end, first, second)
                    } else {
                        let start = {
                            let positive = d.of_nat(m);
                            let borrowed = d.sub_nat_nat(q, sn);
                            d.imul(positive, borrowed)
                        };
                        let middle = d.sub_nat_nat(scaled_left, scaled_right);
                        let end = {
                            let a = d.neg_of_nat(scaled_right);
                            let c = d.of_nat(scaled_left);
                            d.iadd(a, c)
                        };
                        let first = d.const_app(p.of_nat_mul_sub_nat_nat, &[m, q, sn]);
                        let second = {
                            let step =
                                d.const_app(p.neg_of_nat_add_of_nat, &[scaled_right, scaled_left]);
                            d.isymm(end, middle, step)
                        };
                        d.itrans(start, middle, end, first, second)
                    }
                }
                // Both summands negative: `b + c` is `negSucc ((n+q)+1)`, and
                // the scaled magnitudes need the same carry `add_assoc` used.
                (Shape::NegSucc, Shape::NegSucc) => {
                    let sn = d.succ(n);
                    let sq = d.succ(q);
                    let doubled = {
                        let flat = NatOps::add(d, n, q);
                        let raised = d.succ(flat);
                        d.succ(raised)
                    };
                    let joined = NatOps::mul(d, scale, doubled);
                    let split = {
                        let left = NatOps::mul(d, scale, sn);
                        let right = NatOps::mul(d, scale, sq);
                        NatOps::add(d, left, right)
                    };
                    let distributed = {
                        let carry = two_successors(d, n, q);
                        let from = NatOps::add(d, sn, sq);
                        let restored = d.symm(from, doubled, carry);
                        let via = NatOps::mul(d, scale, from);
                        let lifted =
                            d.congr(doubled, from, restored, &|d, t| NatOps::mul(d, scale, t));
                        let final_step = {
                            let name = p.nat.left_distrib;
                            d.const_app(name, &[scale, sn, sq])
                        };
                        let (_, proof) = d.chain(joined, &[(via, lifted), (split, final_step)]);
                        proof
                    };
                    if negative_scale {
                        d.nat_eq_to_int(joined, split, distributed, &|d, t| d.of_nat(t))
                    } else {
                        let start = d.neg_of_nat(joined);
                        let middle = d.neg_of_nat(split);
                        let first =
                            d.nat_eq_to_int(joined, split, distributed, &|d, t| d.neg_of_nat(t));
                        let end = {
                            let left = NatOps::mul(d, scale, sn);
                            let right = NatOps::mul(d, scale, sq);
                            let a = d.neg_of_nat(left);
                            let c = d.neg_of_nat(right);
                            d.iadd(a, c)
                        };
                        let second = {
                            let left = NatOps::mul(d, scale, sn);
                            let right = NatOps::mul(d, scale, sq);
                            let regroup = d.const_app(p.neg_of_nat_add_neg_of_nat, &[left, right]);
                            d.isymm(end, middle, regroup)
                        };
                        d.itrans(start, middle, end, first, second)
                    }
                }
            }
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

/// `Int.le (negOfNat x) (ofNat y)` for every pair of naturals — a non-positive
/// integer never exceeds a non-negative one.
///
/// `Int.negOfNat x` is *stuck* on a variable `x`, so the goal does not reduce
/// until `x` is split: at `0` it is `Nat.le 0 y` and at `succ k` it is `True`.
fn neg_of_nat_le_of_nat(d: &mut IntDev<'_>, x: ExprId, y: ExprId) -> ExprId {
    let motive = |d: &mut IntDev<'_>, t: ExprId| {
        let negative = d.neg_of_nat(t);
        let positive = d.of_nat(y);
        d.ile(negative, positive)
    };
    d.induct(
        &motive,
        &|d| {
            let name = d.int().nat.zero_le;
            d.const_app(name, &[y])
        },
        &|d, _j, _ih| d.true_intro(),
        x,
    )
}

/// `h : Nat.le y x  ⊢  Int.le (negOfNat x) (negOfNat y)` — negation reverses
/// the order.
///
/// Both `negOfNat` applications are stuck, so this splits `x` and then `y`,
/// carrying the hypothesis inside each motive. Three of the four branches close
/// on the spot; the fourth is `Nat.le_of_succ_le_succ`.
fn neg_of_nat_antitone(d: &mut IntDev<'_>, x: ExprId, y: ExprId, h: ExprId) -> ExprId {
    let outer = |d: &mut IntDev<'_>, t: ExprId| {
        let hypothesis = NatOps::le(d, y, t);
        let left = d.neg_of_nat(t);
        let right = d.neg_of_nat(y);
        let conclusion = d.ile(left, right);
        d.arrow(hypothesis, conclusion)
    };
    let implication = d.induct(
        &outer,
        // x = 0: the bound forces y = 0 too.
        &|d| {
            let inner = |d: &mut IntDev<'_>, u: ExprId| {
                let zero = d.zero();
                let hypothesis = NatOps::le(d, u, zero);
                let left = d.neg_of_nat(zero);
                let right = d.neg_of_nat(u);
                let conclusion = d.ile(left, right);
                d.arrow(hypothesis, conclusion)
            };
            d.induct(
                &inner,
                &|d| {
                    let zero = d.zero();
                    let hypothesis = NatOps::le(d, zero, zero);
                    with_hypotheses(d, &[hypothesis], &|d, _| {
                        let zero = d.zero();
                        let name = d.int().nat.le_refl;
                        d.const_app(name, &[zero])
                    })
                },
                &|d, j, _ih| {
                    let successor = d.succ(j);
                    let zero = d.zero();
                    let hypothesis = NatOps::le(d, successor, zero);
                    let left = d.neg_of_nat(zero);
                    let right = d.neg_of_nat(successor);
                    let goal = d.ile(left, right);
                    with_hypotheses(d, &[hypothesis], &|d, hs| {
                        let name = d.int().nat.not_succ_le_zero;
                        let refuted = d.const_app(name, &[j, hs[0]]);
                        d.absurd(goal, refuted)
                    })
                },
                y,
            )
        },
        // x = succ i: `negOfNat (succ i)` is `negSucc i`.
        &|d, i, _ih| {
            let inner = |d: &mut IntDev<'_>, u: ExprId| {
                let successor = d.succ(i);
                let hypothesis = NatOps::le(d, u, successor);
                let left = d.neg_of_nat(successor);
                let right = d.neg_of_nat(u);
                let conclusion = d.ile(left, right);
                d.arrow(hypothesis, conclusion)
            };
            d.induct(
                &inner,
                &|d| {
                    let successor = d.succ(i);
                    let zero = d.zero();
                    let hypothesis = NatOps::le(d, zero, successor);
                    with_hypotheses(d, &[hypothesis], &|d, _| d.true_intro())
                },
                &|d, j, _ih| {
                    let bound = d.succ(i);
                    let successor = d.succ(j);
                    let hypothesis = NatOps::le(d, successor, bound);
                    with_hypotheses(d, &[hypothesis], &|d, hs| {
                        let name = d.int().nat.le_of_succ_le_succ;
                        d.const_app(name, &[j, i, hs[0]])
                    })
                },
                y,
            )
        },
        x,
    );
    d.apply(implication, &[h])
}

/// Declare `Int.mul_le_mul_of_nonneg_left`.
pub(super) fn declare_ordered_multiplication(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    // mul_le_mul_of_nonneg_left : ∀ a b c, 0 ≤ a → b ≤ c → a*b ≤ a*c.
    //
    // `0 ≤ a` reduces to `False` when `a` is negative, so only the four
    // branches with `a = ofNat m` survive — and of those, one is refuted by the
    // second hypothesis and the other three are `Nat.mul_le_mul_left` pushed
    // through whichever constructor the products land in.
    d.int_theorem(p.mul_le_mul_of_nonneg_left, 3, &|d, v| {
        let stmt = statements::mul_le_mul_of_nonneg_left(d, v);
        let proof = case_split(d, v, &statements::mul_le_mul_of_nonneg_left, &|d, b| {
            let scale = d.branch_term(b[0]);
            let lower = d.branch_term(b[1]);
            let upper = d.branch_term(b[2]);
            let zero = d.izero();
            let nonnegative = d.ile(zero, scale);
            let bound = d.ile(lower, upper);
            let left = d.imul(scale, lower);
            let right = d.imul(scale, upper);
            let goal = d.ile(left, right);
            let (m, x, y) = (b[0].1, b[1].1, b[2].1);
            with_hypotheses(d, &[nonnegative, bound], &|d, h| {
                match (b[0].0, b[1].0, b[2].0) {
                    // A negative scale refutes `0 ≤ a` outright.
                    (Shape::NegSucc, _, _) => d.absurd(goal, h[0]),
                    (Shape::OfNat, Shape::OfNat, Shape::OfNat) => {
                        let name = d.int().nat.mul_le_mul_left;
                        d.const_app(name, &[m, x, y, h[1]])
                    }
                    // `ofNat x ≤ negSucc y` is `False`.
                    (Shape::OfNat, Shape::OfNat, Shape::NegSucc) => d.absurd(goal, h[1]),
                    (Shape::OfNat, Shape::NegSucc, Shape::OfNat) => {
                        let successor = d.succ(x);
                        let magnitude = NatOps::mul(d, m, successor);
                        let product = NatOps::mul(d, m, y);
                        neg_of_nat_le_of_nat(d, magnitude, product)
                    }
                    (Shape::OfNat, Shape::NegSucc, Shape::NegSucc) => {
                        // `negSucc x ≤ negSucc y` is `y ≤ x`, so scaling gives
                        // `m*(y+1) ≤ m*(x+1)` and negation reverses it back.
                        let lower_successor = d.succ(x);
                        let upper_successor = d.succ(y);
                        let lifted = {
                            let name = d.int().nat.le_succ_succ;
                            d.const_app(name, &[y, x, h[1]])
                        };
                        let scaled = {
                            let name = d.int().nat.mul_le_mul_left;
                            d.const_app(name, &[m, upper_successor, lower_successor, lifted])
                        };
                        let bigger = NatOps::mul(d, m, lower_successor);
                        let smaller = NatOps::mul(d, m, upper_successor);
                        neg_of_nat_antitone(d, bigger, smaller, scaled)
                    }
                }
            })
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.pow_add : ∀ (a : Int) (m n : Nat), Eq Int (pow a (add m n)) (mul (pow a m) (pow a n))`
/// — induction on `n`, mirroring `Nat.pow_add`'s own proof shape
/// (`nat_prelude/algebra.rs`) exactly: both `Nat.add` and `Int.pow` recurse on
/// their SECOND/exponent argument, so the base case is `mul_one` reversed and
/// the step is IH, `mul_assoc`, then `pow_succ` back — no new proof technique,
/// only every carrier promoted from `Nat` to `Int`.
///
/// Quantifies over one `Int` and two `Nat`s, so — like [`super::defs::declare_pow_equations`]'s
/// `pow_succ` — it is declared by hand rather than through
/// [`IntDev::int_theorem`].
///
/// # Errors
///
/// Returns the kernel's rejection if the constructed proof does not check.
pub(super) fn declare_pow_add(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let nat = d.nat_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| {
        let sum = NatOps::add(d, m, x);
        let lhs = d.ipow(a, sum);
        let pow_m = d.ipow(a, m);
        let pow_x = d.ipow(a, x);
        let rhs = d.imul(pow_m, pow_x);
        d.ieq(lhs, rhs)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let stmt_inner = motive(d, n);

    let proof_inner = d.induct(
        &motive,
        &|d| {
            // `a^(m+0)` computes to `a^m`; goal is `a^m = a^m * a^0`, i.e.
            // `mul_one` reversed (`a^0` is defeq to `Int.one`, so a literal
            // `one` closes it, exactly as `Nat.pow_add`'s own base case uses a
            // literal `1` rather than the symbolic `pow_x`).
            let pow_m = d.ipow(a, m);
            let one = d.ione();
            let product = d.imul(pow_m, one);
            let h = d.const_app(p.mul_one, &[pow_m]);
            d.isymm(product, pow_m, h)
        },
        &|d, j, ih| {
            // `a^(m + succ j)` computes to `a^(m+j) * a`.
            let pow_m = d.ipow(a, m);
            let pow_j = d.ipow(a, j);
            let sum_mj = NatOps::add(d, m, j);
            let pow_sum = d.ipow(a, sum_mj);
            let start = d.imul(pow_sum, a);
            let ih_applied = d.imul(pow_m, pow_j);
            let after_ih = d.imul(ih_applied, a);
            let h_ih = d.icongr(pow_sum, ih_applied, ih, &|d, t| d.imul(t, a));
            let inner = d.imul(pow_j, a);
            let associated = d.imul(pow_m, inner);
            let h_assoc = d.const_app(p.mul_assoc, &[pow_m, pow_j, a]);
            let succ_j = d.succ(j);
            let pow_succ_j = d.ipow(a, succ_j);
            let end = d.imul(pow_m, pow_succ_j);
            let h_pow = d.const_app(p.pow_succ, &[a, j]);
            let h_pow_rev = d.isymm(pow_succ_j, inner, h_pow);
            let h_end = d.icongr(inner, pow_succ_j, h_pow_rev, &|d, t| d.imul(pow_m, t));
            let (_, proof) = d.ichain(
                start,
                &[(after_ih, h_ih), (associated, h_assoc), (end, h_end)],
            );
            proof
        },
        n,
    );

    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt_inner);
        let inner2 = d.pi_fv(m_fv, nat, inner);
        d.pi_fv(a_fv, int_ty, inner2)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof_inner);
        let inner2 = d.lam_fv(m_fv, nat, inner);
        d.lam_fv(a_fv, int_ty, inner2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pow_add,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Int.pow_mul : ∀ (a : Int) (m n : Nat), Eq Int (pow a (m*n)) (pow (pow a
/// m) n)` — induction on `n`. Both directions of the base case compute (`m*0`
/// and `n=0` both hit `pow _ 0 ≡ 1` definitionally), and the step chains
/// `pow_add` then the induction hypothesis through `mul m (succ j) ≡ add (mul
/// m j) m` and `pow (pow a m) (succ j) ≡ mul (pow (pow a m) j) (pow a m)`,
/// both definitional (`Nat.mul`/`Int.pow` both recurse on their SECOND
/// argument).
///
/// Quantifies over one `Int` and two `Nat`s, so — like [`declare_pow_add`] —
/// it is declared by hand rather than through [`IntDev::int_theorem`].
///
/// # Errors
///
/// Returns the kernel's rejection if the constructed proof does not check.
pub(super) fn declare_pow_mul(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let nat = d.nat_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| {
        let prod = NatOps::mul(d, m, x);
        let lhs = d.ipow(a, prod);
        let pow_a_m = d.ipow(a, m);
        let rhs = d.ipow(pow_a_m, x);
        d.ieq(lhs, rhs)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let stmt_inner = motive(d, n);

    let proof_inner = d.induct(
        &motive,
        &|d| {
            let one = d.ione();
            d.irefl(one)
        },
        &|d, j, ih| {
            let mj = NatOps::mul(d, m, j);
            let pow_a_mj = d.ipow(a, mj);
            let sum = NatOps::add(d, mj, m);
            let start = d.ipow(a, sum);
            let pow_a_m = d.ipow(a, m);
            let after_pow_add = d.imul(pow_a_mj, pow_a_m);
            let h_pow_add = d.const_app(p.pow_add, &[a, mj, m]);
            let pow_pam_j = d.ipow(pow_a_m, j);
            let after_ih = d.imul(pow_pam_j, pow_a_m);
            let h_ih = d.icongr(pow_a_mj, pow_pam_j, ih, &|d, t| d.imul(t, pow_a_m));
            let (_, proof) = d.ichain(start, &[(after_pow_add, h_pow_add), (after_ih, h_ih)]);
            proof
        },
        n,
    );

    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt_inner);
        let inner2 = d.pi_fv(m_fv, nat, inner);
        d.pi_fv(a_fv, int_ty, inner2)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof_inner);
        let inner2 = d.lam_fv(m_fv, nat, inner);
        d.lam_fv(a_fv, int_ty, inner2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pow_mul,
        uparams: vec![],
        ty,
        value,
    })
}
