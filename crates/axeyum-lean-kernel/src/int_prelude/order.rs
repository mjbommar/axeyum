//! The **order** laws of `ℤ`, derived from the axiom-free `Nat` order.
//!
//! `Int.le` and `Int.lt` are four-case definitions (see [`super::defs`]), so
//! every proof here is the same shape: split both (or all three) arguments with
//! `Int.rec`, and in each branch the goal has *already* ι-reduced to a `Nat`
//! statement, to `True`, or to `False`. The same-sign branches are the
//! corresponding `Nat` lemma — with the arguments **swapped** in the
//! `negSucc`/`negSucc` branch, because `-(m+1) ≤ -(n+1)` is `n ≤ m` — and the
//! mixed branches are discharged by `True.intro` or by `False.rec` on a
//! hypothesis that reduced to `False`.

use super::ops::{Branch, IntDev, Shape, case_split};
use super::statements;
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

// --- Nat order combinators the branches need --------------------------------

/// `Nat.le.refl n : Nat.le n n`.
fn nat_le_refl(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let name = d.int().nat.le_refl;
    d.const_app(name, &[n])
}

/// `Nat.le.step n m h : Nat.le n (succ m)`, from `h : Nat.le n m`.
fn nat_le_step(d: &mut IntDev<'_>, n: ExprId, m: ExprId, h: ExprId) -> ExprId {
    let name = d.int().nat.le_step;
    d.const_app(name, &[n, m, h])
}

/// `Nat.le n (succ n)`.
fn nat_le_self_succ(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let refl = nat_le_refl(d, n);
    nat_le_step(d, n, n, refl)
}

/// `Nat.le_trans a b c h1 h2 : Nat.le a c`.
fn nat_le_trans(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let name = d.int().nat.le_trans;
    d.const_app(name, &[a, b, c, h1, h2])
}

/// `Nat.lt_of_lt_of_le a b c h1 h2 : Nat.lt a c`.
fn nat_lt_of_lt_of_le(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let name = d.int().nat.lt_of_lt_of_le;
    d.const_app(name, &[a, b, c, h1, h2])
}

/// `Nat.lt_of_le_of_lt a b c h1 h2 : Nat.lt a c`.
fn nat_lt_of_le_of_lt(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let name = d.int().nat.lt_of_le_of_lt;
    d.const_app(name, &[a, b, c, h1, h2])
}

/// `h : Nat.lt m n ⊢ Nat.le m n`. The `Nat` prelude has no `le_of_lt`, so this
/// is `m ≤ succ m ≤ n` through `Nat.le_trans`.
fn nat_le_of_lt(d: &mut IntDev<'_>, m: ExprId, n: ExprId, h: ExprId) -> ExprId {
    let successor = d.succ(m);
    let step = nat_le_self_succ(d, m);
    nat_le_trans(d, m, successor, n, step, h)
}

/// `h1 : Nat.lt a b`, `h2 : Nat.lt b c ⊢ Nat.lt a c`.
fn nat_lt_trans(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let weakened = nat_le_of_lt(d, b, c, h2);
    nat_lt_of_lt_of_le(d, a, b, c, h1, weakened)
}

// --- branch plumbing --------------------------------------------------------

/// `fun (h_0 : tys[0]) … (h_{n-1} : tys[n-1]) => body(h_0, …)`.
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

/// The three constructor terms of a three-way branch.
fn triple(d: &mut IntDev<'_>, b: &[Branch]) -> (ExprId, ExprId, ExprId) {
    let first = d.branch_term(b[0]);
    let second = d.branch_term(b[1]);
    let third = d.branch_term(b[2]);
    (first, second, third)
}

/// A transitivity-shaped law: `rel1 a b → rel2 b c → rel3 a c`, where each
/// relation is `Int.le` or `Int.lt`, proved by case analysis on `a`, `b`, `c`.
///
/// `same_sign` builds the non-negative branch's proof from the two `Nat`
/// hypotheses; `same_sign_negative` builds the doubly-negative one, where the
/// order reverses.
#[allow(clippy::too_many_arguments)]
fn transitivity_proof(
    d: &mut IntDev<'_>,
    targets: &[ExprId],
    statement: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> ExprId,
    first_is_lt: bool,
    second_is_lt: bool,
    conclusion_is_lt: bool,
    same_sign: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId, ExprId, ExprId, ExprId) -> ExprId,
    negative: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId, ExprId, ExprId, ExprId) -> ExprId,
) -> ExprId {
    case_split(d, targets, statement, &|d, b| {
        let (first, second, third) = triple(d, b);
        let h1_ty = if first_is_lt {
            d.ilt(first, second)
        } else {
            d.ile(first, second)
        };
        let h2_ty = if second_is_lt {
            d.ilt(second, third)
        } else {
            d.ile(second, third)
        };
        let goal = if conclusion_is_lt {
            d.ilt(first, third)
        } else {
            d.ile(first, third)
        };
        let shapes = (b[0].0, b[1].0, b[2].0);
        let (m, n, p) = (b[0].1, b[1].1, b[2].1);
        with_hypotheses(d, &[h1_ty, h2_ty], &|d, h| match shapes {
            (Shape::OfNat, Shape::OfNat, Shape::OfNat) => same_sign(d, m, n, p, h[0], h[1]),
            (Shape::NegSucc, Shape::NegSucc, Shape::NegSucc) => negative(d, p, n, m, h[1], h[0]),
            // `a` non-negative and `b` negative: the first hypothesis reduced
            // to `False`.
            (Shape::OfNat, Shape::NegSucc, _) => d.absurd(goal, h[0]),
            // `b` non-negative and `c` negative: the second reduced to `False`.
            (_, Shape::OfNat, Shape::NegSucc) => d.absurd(goal, h[1]),
            // `a` negative and `c` non-negative: the goal itself reduced to
            // `True`.
            (Shape::NegSucc, _, Shape::OfNat) => d.true_intro(),
        })
    })
}

/// Declare every order law this development derives.
pub(super) fn declare_order_theorems(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    // le_refl : ∀ a, le a a
    d.int_theorem(p.le_refl, 1, &|d, v| {
        let stmt = statements::le_refl(d, v);
        let proof = case_split(d, v, &statements::le_refl, &|d, b| nat_le_refl(d, b[0].1));
        (stmt, proof)
    })?;

    // lt_irrefl : ∀ a, Not (lt a a)
    d.int_theorem(p.lt_irrefl, 1, &|d, v| {
        let stmt = statements::lt_irrefl(d, v);
        let proof = case_split(d, v, &statements::lt_irrefl, &|d, b| {
            let name = d.int().nat.lt_irrefl;
            d.const_app(name, &[b[0].1])
        });
        (stmt, proof)
    })?;

    // zero_lt_one : lt zero one — `Nat.le 1 1`, i.e. reflexivity.
    d.int_theorem(p.zero_lt_one, 0, &|d, v| {
        let stmt = statements::zero_lt_one(d, v);
        let one = d.num(1);
        let proof = nat_le_refl(d, one);
        (stmt, proof)
    })?;

    // le_of_lt : ∀ a b, lt a b → le a b
    d.int_theorem(p.le_of_lt, 2, &|d, v| {
        let stmt = statements::le_of_lt(d, v);
        let proof = case_split(d, v, &statements::le_of_lt, &|d, b| {
            let left = d.branch_term(b[0]);
            let right = d.branch_term(b[1]);
            let hypothesis = d.ilt(left, right);
            let goal = d.ile(left, right);
            let (m, n) = (b[0].1, b[1].1);
            with_hypotheses(d, &[hypothesis], &|d, h| match (b[0].0, b[1].0) {
                (Shape::OfNat, Shape::OfNat) => nat_le_of_lt(d, m, n, h[0]),
                (Shape::NegSucc, Shape::NegSucc) => nat_le_of_lt(d, n, m, h[0]),
                (Shape::OfNat, Shape::NegSucc) => d.absurd(goal, h[0]),
                (Shape::NegSucc, Shape::OfNat) => d.true_intro(),
            })
        });
        (stmt, proof)
    })?;

    // le_trans : ∀ a b c, le a b → le b c → le a c
    d.int_theorem(p.le_trans, 3, &|d, v| {
        let stmt = statements::le_trans(d, v);
        let proof = transitivity_proof(
            d,
            v,
            &statements::le_trans,
            false,
            false,
            false,
            &nat_le_trans,
            &nat_le_trans,
        );
        (stmt, proof)
    })?;

    // lt_trans : ∀ a b c, lt a b → lt b c → lt a c
    d.int_theorem(p.lt_trans, 3, &|d, v| {
        let stmt = statements::lt_trans(d, v);
        let proof = transitivity_proof(
            d,
            v,
            &statements::lt_trans,
            true,
            true,
            true,
            &nat_lt_trans,
            &nat_lt_trans,
        );
        (stmt, proof)
    })?;

    // lt_of_lt_of_le : ∀ a b c, lt a b → le b c → lt a c
    // Reversing the branch swaps which hypothesis is strict, so the negative
    // branch uses `lt_of_le_of_lt`.
    d.int_theorem(p.lt_of_lt_of_le, 3, &|d, v| {
        let stmt = statements::lt_of_lt_of_le(d, v);
        let proof = transitivity_proof(
            d,
            v,
            &statements::lt_of_lt_of_le,
            true,
            false,
            true,
            &nat_lt_of_lt_of_le,
            &nat_lt_of_le_of_lt,
        );
        (stmt, proof)
    })?;

    // lt_of_le_of_lt : ∀ a b c, le a b → lt b c → lt a c
    d.int_theorem(p.lt_of_le_of_lt, 3, &|d, v| {
        let stmt = statements::lt_of_le_of_lt(d, v);
        let proof = transitivity_proof(
            d,
            v,
            &statements::lt_of_le_of_lt,
            false,
            true,
            true,
            &nat_lt_of_le_of_lt,
            &nat_lt_of_lt_of_le,
        );
        (stmt, proof)
    })?;

    // le_total : ∀ a b, Or (le a b) (le b a)
    d.int_theorem(p.le_total, 2, &|d, v| {
        let stmt = statements::le_total(d, v);
        let proof = case_split(d, v, &statements::le_total, &|d, b| {
            let left = d.branch_term(b[0]);
            let right = d.branch_term(b[1]);
            let forward = d.ile(left, right);
            let backward = d.ile(right, left);
            let (m, n) = (b[0].1, b[1].1);
            let name = d.int().nat.le_total;
            match (b[0].0, b[1].0) {
                (Shape::OfNat, Shape::OfNat) => d.const_app(name, &[m, n]),
                (Shape::NegSucc, Shape::NegSucc) => d.const_app(name, &[n, m]),
                (Shape::OfNat, Shape::NegSucc) => {
                    let trivial = d.true_intro();
                    d.or_inr(forward, backward, trivial)
                }
                (Shape::NegSucc, Shape::OfNat) => {
                    let trivial = d.true_intro();
                    d.or_inl(forward, backward, trivial)
                }
            }
        });
        (stmt, proof)
    })?;

    // no_int_between : ∀ x, Not (And (lt zero x) (lt x one)) — the integer fact
    // the ordered field `R` lacks.
    d.int_theorem(p.no_int_between, 1, &|d, v| {
        let stmt = statements::no_int_between(d, v);
        let proof = case_split(d, v, &statements::no_int_between, &|d, b| {
            let value = d.branch_term(b[0]);
            let zero = d.izero();
            let one = d.ione();
            let lower = d.ilt(zero, value);
            let upper = d.ilt(value, one);
            let both = d.and(lower, upper);
            let n = b[0].1;
            with_hypotheses(d, &[both], &|d, h| {
                let low = d.and_left(lower, upper, h[0]);
                match b[0].0 {
                    // `0 < ofNat n` is `1 ≤ n` and `ofNat n < 1` is
                    // `succ n ≤ 1`, hence `n ≤ 0`; chaining gives `1 ≤ 0`.
                    Shape::OfNat => {
                        let high = d.and_right(lower, upper, h[0]);
                        let nat_zero = d.zero();
                        let one_nat = d.num(1);
                        let descend = d.int().nat.le_of_succ_le_succ;
                        let bounded = d.const_app(descend, &[n, nat_zero, high]);
                        let absurdity = nat_le_trans(d, one_nat, n, nat_zero, low, bounded);
                        let contradiction = d.int().nat.not_succ_le_zero;
                        d.const_app(contradiction, &[nat_zero, absurdity])
                    }
                    // `0 < negSucc n` already reduced to `False`.
                    Shape::NegSucc => low,
                }
            })
        });
        (stmt, proof)
    })?;

    // lt_of_le_of_ne : ∀ a b, le a b → Not (Eq Int a b) → lt a b — the
    // antisymmetry half of a linear order. In a same-sign branch `Nat`'s
    // `lt_or_eq_of_le` splits the bound, and the equal case is pushed back up
    // through the constructor to contradict the disequality.
    d.int_theorem(p.lt_of_le_of_ne, 2, &|d, v| {
        let stmt = statements::lt_of_le_of_ne(d, v);
        let proof = case_split(d, v, &statements::lt_of_le_of_ne, &|d, b| {
            let left = d.branch_term(b[0]);
            let right = d.branch_term(b[1]);
            let bound = d.ile(left, right);
            let equality = d.ieq(left, right);
            let distinct = d.not(equality);
            let goal = d.ilt(left, right);
            let (m, n) = (b[0].1, b[1].1);
            with_hypotheses(d, &[bound, distinct], &|d, h| match (b[0].0, b[1].0) {
                (Shape::OfNat, Shape::NegSucc) => d.absurd(goal, h[0]),
                (Shape::NegSucc, Shape::OfNat) => d.true_intro(),
                (Shape::OfNat, Shape::OfNat) => {
                    let split = d.int().nat.lt_or_eq_of_le;
                    let disjunction = d.const_app(split, &[m, n, h[0]]);
                    let strict = NatOps::lt(d, m, n);
                    let equal = d.eq(m, n);
                    d.or_elim(
                        strict,
                        equal,
                        goal,
                        disjunction,
                        &|_d, strict_proof| strict_proof,
                        &|d, equal_proof| {
                            let lifted = d.nat_eq_to_int(m, n, equal_proof, &|d, x| d.of_nat(x));
                            let refuted = d.kernel().app(h[1], lifted);
                            d.absurd(goal, refuted)
                        },
                    )
                }
                (Shape::NegSucc, Shape::NegSucc) => {
                    // `negSucc m ≤ negSucc n` is `n ≤ m`, so the disjunction
                    // and the lifted equality both run the other way.
                    let split = d.int().nat.lt_or_eq_of_le;
                    let disjunction = d.const_app(split, &[n, m, h[0]]);
                    let strict = NatOps::lt(d, n, m);
                    let equal = d.eq(n, m);
                    d.or_elim(
                        strict,
                        equal,
                        goal,
                        disjunction,
                        &|_d, strict_proof| strict_proof,
                        &|d, equal_proof| {
                            let lifted = d.nat_eq_to_int(n, m, equal_proof, &|d, x| d.neg_succ(x));
                            let reversed = d.isymm(right, left, lifted);
                            let refuted = d.kernel().app(h[1], reversed);
                            d.absurd(goal, refuted)
                        },
                    )
                }
            })
        });
        (stmt, proof)
    })?;

    Ok(())
}
