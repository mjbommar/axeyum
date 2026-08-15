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

use super::ops::{Branch, IntDev, Shape, case_split, exists_elim};

use super::statements;
use super::sub_nat_nat::by_borrow;
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

// --- the order as a difference ----------------------------------------------
//
// `Int.le a b` is a four-case definition, so proving `a ≤ b → a+c ≤ b+d` by
// case analysis means sixteen branches over an `Int.add` that is itself stuck
// on `subNatNat` in half of them. The way out is to stop reasoning about `le`
// structurally at all: `a ≤ b` **iff** `b = a + ofNat i` for some natural `i`,
// and once both hypotheses are in that form the conclusion is one ring
// rearrangement plus the trivial direction of the same equivalence. That is
// four short lemmas here and no case analysis at all in the two laws.

/// `fun (i : Nat) => Eq Int upper (Int.add lower (Int.ofNat (offset i)))`.
fn shift_predicate(
    d: &mut IntDev<'_>,
    lower: ExprId,
    upper: ExprId,
    offset: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let magnitude = offset(d, i);
    let value = d.of_nat(magnitude);
    let shifted = d.iadd(lower, value);
    let body = d.ieq(upper, shifted);
    d.lam_fv(i_fv, nat, body)
}

/// `Exists.{1} Nat predicate`.
fn shift_exists(d: &mut IntDev<'_>, predicate: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let name = d.int().logic.exists_;
    let exists = d.kernel().const_(name, vec![one]);
    d.apply(exists, &[nat, predicate])
}

/// `Exists.intro.{1} Nat predicate witness proof`.
fn shift_intro(d: &mut IntDev<'_>, predicate: ExprId, witness: ExprId, proof: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let name = d.int().logic.exists_intro;
    let intro = d.kernel().const_(name, vec![one]);
    d.apply(intro, &[nat, predicate, witness, proof])
}

/// `∀ (i : Nat), le a (a + ofNat i)` for the `a` in `v[0]`.
fn le_shift_statement(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let value = d.of_nat(i);
    let shifted = d.iadd(v[0], value);
    let body = d.ile(v[0], shifted);
    d.pi_fv(i_fv, nat, body)
}

/// `∀ (i : Nat), lt a (a + ofNat (i+1))` for the `a` in `v[0]`.
fn lt_shift_statement(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let successor = d.succ(i);
    let value = d.of_nat(successor);
    let shifted = d.iadd(v[0], value);
    let body = d.ilt(v[0], shifted);
    d.pi_fv(i_fv, nat, body)
}

/// `le a b → ∃ (i : Nat), b = a + ofNat i`.
fn le_dest_statement(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let predicate = shift_predicate(d, v[0], v[1], &|_d, i| i);
    let conclusion = shift_exists(d, predicate);
    let hypothesis = d.ile(v[0], v[1]);
    d.arrow(hypothesis, conclusion)
}

/// `lt a b → ∃ (i : Nat), b = a + ofNat (i+1)`.
fn lt_dest_statement(d: &mut IntDev<'_>, v: &[ExprId]) -> ExprId {
    let predicate = shift_predicate(d, v[0], v[1], &|d, i| d.succ(i));
    let conclusion = shift_exists(d, predicate);
    let hypothesis = d.ilt(v[0], v[1]);
    d.arrow(hypothesis, conclusion)
}

/// `Nat.le j m` from `hj : i+(j+1) = m+1` — the negative branch of both shift
/// lemmas, where the borrow fired and the two magnitudes have to be compared
/// through `Nat.succ_injective`.
fn bound_from_borrow(d: &mut IntDev<'_>, i: ExprId, j: ExprId, m: ExprId, hj: ExprId) -> ExprId {
    let shifted = NatOps::add(d, i, j);
    let collapsed = {
        let name = d.int().nat.succ_injective;
        d.const_app(name, &[shifted, m, hj])
    };
    let base = {
        let name = d.int().nat.le_add_right;
        d.const_app(name, &[j, i])
    };
    let swapped = NatOps::add(d, j, i);
    let commute = {
        let name = d.int().nat.add_comm;
        d.const_app(name, &[j, i])
    };
    let reordered = d.nat_rewrite(swapped, shifted, commute, base, &|d, t| NatOps::le(d, j, t));
    d.nat_rewrite(shifted, m, collapsed, reordered, &|d, t| {
        NatOps::le(d, j, t)
    })
}

/// Declare the four lemmas that present `Int.le` and `Int.lt` as an explicit
/// non-negative difference.
pub(super) fn declare_difference_lemmas(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    // le_ofNat_add : le a (a + ofNat i).
    d.int_theorem(p.le_of_nat_add, 1, &|d, v| {
        let stmt = le_shift_statement(d, v);
        let proof = case_split(d, v, &le_shift_statement, &|d, b| {
            let m = b[0].1;
            let nat = d.nat_ty();
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let body = match b[0].0 {
                Shape::OfNat => {
                    let name = d.int().nat.le_add_right;
                    d.const_app(name, &[m, i])
                }
                Shape::NegSucc => {
                    let successor = d.succ(m);
                    by_borrow(
                        d,
                        i,
                        successor,
                        &|d, z| {
                            let negative = d.neg_succ(m);
                            d.ile(negative, z)
                        },
                        // The borrow did not fire: `negSucc m ≤ ofNat _` is `True`.
                        &|d, _j, _hj| d.true_intro(),
                        &|d, j, hj| bound_from_borrow(d, i, j, m, hj),
                    )
                }
            };
            d.lam_fv(i_fv, nat, body)
        });
        (stmt, proof)
    })?;

    // lt_ofNat_add : lt a (a + ofNat (i+1)).
    d.int_theorem(p.lt_of_nat_add, 1, &|d, v| {
        let stmt = lt_shift_statement(d, v);
        let proof = case_split(d, v, &lt_shift_statement, &|d, b| {
            let m = b[0].1;
            let nat = d.nat_ty();
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let body = match b[0].0 {
                Shape::OfNat => {
                    let sum = NatOps::add(d, m, i);
                    let base = {
                        let name = d.int().nat.le_add_right;
                        d.const_app(name, &[m, i])
                    };
                    let name = d.int().nat.le_succ_succ;
                    d.const_app(name, &[m, sum, base])
                }
                Shape::NegSucc => {
                    let successor = d.succ(m);
                    let raised = d.succ(i);
                    by_borrow(
                        d,
                        raised,
                        successor,
                        &|d, z| {
                            let negative = d.neg_succ(m);
                            d.ilt(negative, z)
                        },
                        &|d, _j, _hj| d.true_intro(),
                        // `lt (negSucc m) (negSucc j)` is `Nat.le (j+1) m`, so
                        // the bound has to be lifted before it is transported.
                        &|d, j, hj| {
                            let collapsed = {
                                let shifted = NatOps::add(d, raised, j);
                                let name = d.int().nat.succ_injective;
                                d.const_app(name, &[shifted, m, hj])
                            };
                            let base = {
                                let name = d.int().nat.le_add_right;
                                d.const_app(name, &[j, i])
                            };
                            let swapped = NatOps::add(d, j, i);
                            let flat = NatOps::add(d, i, j);
                            let commute = {
                                let name = d.int().nat.add_comm;
                                d.const_app(name, &[j, i])
                            };
                            let reordered = d.nat_rewrite(swapped, flat, commute, base, &|d, t| {
                                NatOps::le(d, j, t)
                            });
                            let lifted = {
                                let name = d.int().nat.le_succ_succ;
                                d.const_app(name, &[j, flat, reordered])
                            };
                            // `(i+1)+j` is `(i+j)+1` by `Nat.succ_add`, which is
                            // where the collapsed hypothesis lives.
                            let shifted = NatOps::add(d, raised, j);
                            let carry = {
                                let name = d.int().nat.succ_add;
                                d.const_app(name, &[i, j])
                            };
                            let bumped = d.succ(flat);
                            let restored = d.symm(shifted, bumped, carry);
                            let (_, joined) =
                                d.chain(bumped, &[(shifted, restored), (m, collapsed)]);
                            d.nat_rewrite(bumped, m, joined, lifted, &|d, t| {
                                let raised = d.succ(j);
                                NatOps::le(d, raised, t)
                            })
                        },
                    )
                }
            };
            d.lam_fv(i_fv, nat, body)
        });
        (stmt, proof)
    })?;

    // le_dest : le a b → ∃ i, b = a + ofNat i.
    d.int_theorem(p.le_dest, 2, &|d, v| {
        let stmt = le_dest_statement(d, v);
        let proof = case_split(d, v, &le_dest_statement, &|d, b| {
            let left = d.branch_term(b[0]);
            let right = d.branch_term(b[1]);
            let hypothesis = d.ile(left, right);
            let predicate = shift_predicate(d, left, right, &|_d, i| i);
            let goal = shift_exists(d, predicate);
            let (m, n) = (b[0].1, b[1].1);
            with_hypotheses(d, &[hypothesis], &|d, h| match (b[0].0, b[1].0) {
                // `Nat.le_dest` already produces the difference.
                (Shape::OfNat, Shape::OfNat) => {
                    let witness = {
                        let name = d.int().nat.le_dest;
                        d.const_app(name, &[m, n, h[0]])
                    };
                    let difference = {
                        let nat = d.nat_ty();
                        let k_fv = d.fresh_fvar();
                        let k = d.kernel().fvar(k_fv);
                        let sum = NatOps::add(d, m, k);
                        let body = d.eq(sum, n);
                        d.lam_fv(k_fv, nat, body)
                    };
                    let minor = {
                        let nat = d.nat_ty();
                        let k_fv = d.fresh_fvar();
                        let k = d.kernel().fvar(k_fv);
                        let sum = NatOps::add(d, m, k);
                        let equation = d.eq(sum, n);
                        let h_fv = d.fresh_fvar();
                        let hk = d.kernel().fvar(h_fv);
                        let lifted = d.nat_eq_to_int(sum, n, hk, &|d, t| d.of_nat(t));
                        let from = d.of_nat(sum);
                        let to = d.of_nat(n);
                        let flipped = d.isymm(from, to, lifted);
                        let body = shift_intro(d, predicate, k, flipped);
                        let with_h = d.lam_fv(h_fv, equation, body);
                        d.lam_fv(k_fv, nat, with_h)
                    };
                    exists_elim(d, difference, goal, witness, minor)
                }
                // `ofNat m ≤ negSucc n` reduced to `False`.
                (Shape::OfNat, Shape::NegSucc) => d.absurd(goal, h[0]),
                // Every negative integer is below every non-negative one, and
                // the gap is `(m+1)+n`.
                (Shape::NegSucc, Shape::OfNat) => {
                    let successor = d.succ(m);
                    let gap = NatOps::add(d, successor, n);
                    let characterisation = {
                        let name = d.int().sub_nat_nat_add_left;
                        d.const_app(name, &[successor, n])
                    };
                    let borrowed = d.sub_nat_nat(gap, successor);
                    let value = d.of_nat(n);
                    let flipped = d.isymm(borrowed, value, characterisation);
                    shift_intro(d, predicate, gap, flipped)
                }
                // `negSucc m ≤ negSucc n` is `n ≤ m`; the gap is `m-n`.
                (Shape::NegSucc, Shape::NegSucc) => {
                    let witness = {
                        let name = d.int().nat.le_dest;
                        d.const_app(name, &[n, m, h[0]])
                    };
                    let difference = {
                        let nat = d.nat_ty();
                        let k_fv = d.fresh_fvar();
                        let k = d.kernel().fvar(k_fv);
                        let sum = NatOps::add(d, n, k);
                        let body = d.eq(sum, m);
                        d.lam_fv(k_fv, nat, body)
                    };
                    let minor = {
                        let nat = d.nat_ty();
                        let k_fv = d.fresh_fvar();
                        let k = d.kernel().fvar(k_fv);
                        let sum = NatOps::add(d, n, k);
                        let equation = d.eq(sum, m);
                        let h_fv = d.fresh_fvar();
                        let hk = d.kernel().fvar(h_fv);
                        let raised = d.succ(n);
                        let characterisation = {
                            let name = d.int().sub_nat_nat_add_right;
                            d.const_app(name, &[k, raised])
                        };
                        // `k+(n+1) = m+1`: commute, then re-attach the successor.
                        let source = NatOps::add(d, k, raised);
                        let swapped = {
                            let flat = NatOps::add(d, n, k);
                            d.succ(flat)
                        };
                        let commute = {
                            let name = d.int().nat.add_comm;
                            d.const_app(name, &[k, n])
                        };
                        let flat = NatOps::add(d, k, n);
                        let reordered = d.congr(flat, sum, commute, &|d, t| d.succ(t));
                        let target = d.succ(m);
                        let finish = d.congr(sum, m, hk, &|d, t| d.succ(t));
                        let (_, joined) =
                            d.chain(source, &[(swapped, reordered), (target, finish)]);
                        let located =
                            d.nat_rewrite(source, target, joined, characterisation, &|d, t| {
                                let borrowed = d.sub_nat_nat(k, t);
                                let value = d.neg_succ(n);
                                d.ieq(borrowed, value)
                            });
                        let borrowed = d.sub_nat_nat(k, target);
                        let value = d.neg_succ(n);
                        let flipped = d.isymm(borrowed, value, located);
                        let body = shift_intro(d, predicate, k, flipped);
                        let with_h = d.lam_fv(h_fv, equation, body);
                        d.lam_fv(k_fv, nat, with_h)
                    };
                    exists_elim(d, difference, goal, witness, minor)
                }
            })
        });
        (stmt, proof)
    })?;

    // lt_dest : lt a b → ∃ i, b = a + ofNat (i+1). The same four branches with
    // `Nat.le_dest` applied to the strict bound, whose difference is therefore
    // one more than the non-strict one.
    d.int_theorem(p.lt_dest, 2, &|d, v| {
        let stmt = lt_dest_statement(d, v);
        let proof = case_split(d, v, &lt_dest_statement, &|d, b| {
            let left = d.branch_term(b[0]);
            let right = d.branch_term(b[1]);
            let hypothesis = d.ilt(left, right);
            let predicate = shift_predicate(d, left, right, &|d, i| d.succ(i));
            let goal = shift_exists(d, predicate);
            let (m, n) = (b[0].1, b[1].1);
            with_hypotheses(d, &[hypothesis], &|d, h| match (b[0].0, b[1].0) {
                (Shape::OfNat, Shape::OfNat) => {
                    let raised = d.succ(m);
                    let witness = {
                        let name = d.int().nat.le_dest;
                        d.const_app(name, &[raised, n, h[0]])
                    };
                    let difference = {
                        let nat = d.nat_ty();
                        let k_fv = d.fresh_fvar();
                        let k = d.kernel().fvar(k_fv);
                        let sum = NatOps::add(d, raised, k);
                        let body = d.eq(sum, n);
                        d.lam_fv(k_fv, nat, body)
                    };
                    let minor = {
                        let nat = d.nat_ty();
                        let k_fv = d.fresh_fvar();
                        let k = d.kernel().fvar(k_fv);
                        let sum = NatOps::add(d, raised, k);
                        let equation = d.eq(sum, n);
                        let h_fv = d.fresh_fvar();
                        let hk = d.kernel().fvar(h_fv);
                        let flat = NatOps::add(d, m, k);
                        let bumped = d.succ(flat);
                        let carry = {
                            let name = d.int().nat.succ_add;
                            d.const_app(name, &[m, k])
                        };
                        let restored = d.symm(sum, bumped, carry);
                        let (_, joined) = d.chain(bumped, &[(sum, restored), (n, hk)]);
                        let lifted = d.nat_eq_to_int(bumped, n, joined, &|d, t| d.of_nat(t));
                        let from = d.of_nat(bumped);
                        let to = d.of_nat(n);
                        let flipped = d.isymm(from, to, lifted);
                        let body = shift_intro(d, predicate, k, flipped);
                        let with_h = d.lam_fv(h_fv, equation, body);
                        d.lam_fv(k_fv, nat, with_h)
                    };
                    exists_elim(d, difference, goal, witness, minor)
                }
                (Shape::OfNat, Shape::NegSucc) => d.absurd(goal, h[0]),
                (Shape::NegSucc, Shape::OfNat) => {
                    let successor = d.succ(m);
                    let gap = NatOps::add(d, m, n);
                    let characterisation = {
                        let name = d.int().sub_nat_nat_add_left;
                        d.const_app(name, &[successor, n])
                    };
                    let source = NatOps::add(d, successor, n);
                    let target = d.succ(gap);
                    let carry = {
                        let name = d.int().nat.succ_add;
                        d.const_app(name, &[m, n])
                    };
                    let located =
                        d.nat_rewrite(source, target, carry, characterisation, &|d, t| {
                            let borrowed = d.sub_nat_nat(t, successor);
                            let value = d.of_nat(n);
                            d.ieq(borrowed, value)
                        });
                    let borrowed = d.sub_nat_nat(target, successor);
                    let value = d.of_nat(n);
                    let flipped = d.isymm(borrowed, value, located);
                    shift_intro(d, predicate, gap, flipped)
                }
                // `negSucc m < negSucc n` is `n+1 ≤ m`; the gap is `m-n`, and
                // the witness is one less than it because the predicate already
                // adds a successor.
                (Shape::NegSucc, Shape::NegSucc) => {
                    let raised = d.succ(n);
                    let witness = {
                        let name = d.int().nat.le_dest;
                        d.const_app(name, &[raised, m, h[0]])
                    };
                    let difference = {
                        let nat = d.nat_ty();
                        let k_fv = d.fresh_fvar();
                        let k = d.kernel().fvar(k_fv);
                        let sum = NatOps::add(d, raised, k);
                        let body = d.eq(sum, m);
                        d.lam_fv(k_fv, nat, body)
                    };
                    let minor = {
                        let nat = d.nat_ty();
                        let k_fv = d.fresh_fvar();
                        let k = d.kernel().fvar(k_fv);
                        let sum = NatOps::add(d, raised, k);
                        let equation = d.eq(sum, m);
                        let h_fv = d.fresh_fvar();
                        let hk = d.kernel().fvar(h_fv);
                        let bumped = d.succ(k);
                        let characterisation = {
                            let name = d.int().sub_nat_nat_add_right;
                            d.const_app(name, &[bumped, raised])
                        };
                        // `(k+1)+(n+1) = m+1`, read right to left: uncarry to
                        // `((k+n)+1)+1`, commute, then use `(n+1)+k = m`.
                        let source = NatOps::add(d, bumped, raised);
                        let flat = NatOps::add(d, k, n);
                        let swapped_flat = NatOps::add(d, n, k);
                        let uncarried = {
                            let shifted = NatOps::add(d, bumped, n);
                            let raised_flat = d.succ(flat);
                            let carry = {
                                let name = d.int().nat.succ_add;
                                d.const_app(name, &[k, n])
                            };
                            d.congr(shifted, raised_flat, carry, &|d, t| d.succ(t))
                        };
                        let doubled = {
                            let inner = d.succ(flat);
                            d.succ(inner)
                        };
                        let swapped = {
                            let inner = d.succ(swapped_flat);
                            d.succ(inner)
                        };
                        let reordered = {
                            let commute = {
                                let name = d.int().nat.add_comm;
                                d.const_app(name, &[k, n])
                            };
                            d.congr(flat, swapped_flat, commute, &|d, t| {
                                let inner = d.succ(t);
                                d.succ(inner)
                            })
                        };
                        let target = d.succ(m);
                        let finish = {
                            let carry = {
                                let name = d.int().nat.succ_add;
                                d.const_app(name, &[n, k])
                            };
                            let bumped_swapped = d.succ(swapped_flat);
                            let lowered = d.symm(sum, bumped_swapped, carry);
                            let (_, joined) = d.chain(bumped_swapped, &[(sum, lowered), (m, hk)]);
                            d.congr(bumped_swapped, m, joined, &|d, t| d.succ(t))
                        };
                        let (_, joined) = d.chain(
                            source,
                            &[(doubled, uncarried), (swapped, reordered), (target, finish)],
                        );
                        let located =
                            d.nat_rewrite(source, target, joined, characterisation, &|d, t| {
                                let borrowed = d.sub_nat_nat(bumped, t);
                                let value = d.neg_succ(n);
                                d.ieq(borrowed, value)
                            });
                        let borrowed = d.sub_nat_nat(bumped, target);
                        let value = d.neg_succ(n);
                        let flipped = d.isymm(borrowed, value, located);
                        let body = shift_intro(d, predicate, k, flipped);
                        let with_h = d.lam_fv(h_fv, equation, body);
                        d.lam_fv(k_fv, nat, with_h)
                    };
                    exists_elim(d, difference, goal, witness, minor)
                }
            })
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `Eq Int ((a+i)+(c+j)) ((a+c)+(i+j))` — the only ring rearrangement the two
/// additive order laws need, and the reason they had to wait for `add_assoc`.
fn add_shuffle(d: &mut IntDev<'_>, a: ExprId, i: ExprId, c: ExprId, j: ExprId) -> ExprId {
    let p = d.int();
    let start = {
        let left = d.iadd(a, i);
        let right = d.iadd(c, j);
        d.iadd(left, right)
    };
    let regrouped = {
        let tail = d.iadd(c, j);
        let inner = d.iadd(i, tail);
        d.iadd(a, inner)
    };
    let first = {
        let left = d.iadd(a, i);
        let tail = d.iadd(c, j);
        let _ = (left, tail);
        let tail = d.iadd(c, j);
        d.const_app(p.add_assoc, &[a, i, tail])
    };
    let flattened = {
        let head = d.iadd(i, c);
        let inner = d.iadd(head, j);
        d.iadd(a, inner)
    };
    let second = {
        let head = d.iadd(i, c);
        let from = {
            let tail = d.iadd(c, j);
            d.iadd(i, tail)
        };
        let to = d.iadd(head, j);
        let step = d.const_app(p.add_assoc, &[i, c, j]);
        let flipped = d.isymm(to, from, step);
        d.icongr(from, to, flipped, &|d, x| d.iadd(a, x))
    };
    let commuted = {
        let head = d.iadd(c, i);
        let inner = d.iadd(head, j);
        d.iadd(a, inner)
    };
    let third = {
        let from = d.iadd(i, c);
        let to = d.iadd(c, i);
        let step = d.const_app(p.add_comm, &[i, c]);
        d.icongr(from, to, step, &|d, x| {
            let inner = d.iadd(x, j);
            d.iadd(a, inner)
        })
    };
    let nested = {
        let tail = d.iadd(i, j);
        let inner = d.iadd(c, tail);
        d.iadd(a, inner)
    };
    let fourth = {
        let head = d.iadd(c, i);
        let from = d.iadd(head, j);
        let to = {
            let tail = d.iadd(i, j);
            d.iadd(c, tail)
        };
        let step = d.const_app(p.add_assoc, &[c, i, j]);
        d.icongr(from, to, step, &|d, x| d.iadd(a, x))
    };
    let end = {
        let head = d.iadd(a, c);
        let tail = d.iadd(i, j);
        d.iadd(head, tail)
    };
    let fifth = {
        let tail = d.iadd(i, j);
        let step = d.const_app(p.add_assoc, &[a, c, tail]);
        d.isymm(end, nested, step)
    };
    let (_, proof) = d.ichain(
        start,
        &[
            (regrouped, first),
            (flattened, second),
            (commuted, third),
            (nested, fourth),
            (end, fifth),
        ],
    );
    proof
}

/// Declare `Int.add_le_add` and `Int.add_lt_add_of_le_of_lt`.
///
/// Both are the same three moves: destructure each hypothesis into an explicit
/// non-negative gap, re-associate `(a+i)+(c+j)` into `(a+c)+(i+j)`, and read the
/// conclusion off the trivial direction. `Int.rec` never appears.
pub(super) fn declare_additive_order(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    d.int_theorem(p.add_le_add, 4, &|d, v| {
        let (a, b, c, e) = (v[0], v[1], v[2], v[3]);
        let stmt = statements::add_le_add(d, v);
        let first_hypothesis = d.ile(a, b);
        let second_hypothesis = d.ile(c, e);
        let base_sum = d.iadd(a, c);
        let goal = {
            let right = d.iadd(b, e);
            d.ile(base_sum, right)
        };
        let proof = with_hypotheses(d, &[first_hypothesis, second_hypothesis], &|d, h| {
            let outer = shift_predicate(d, a, b, &|_d, i| i);
            let outer_witness = d.const_app(p.le_dest, &[a, b, h[0]]);
            let outer_minor = {
                let nat = d.nat_ty();
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let gap = d.of_nat(i);
                let equation = {
                    let shifted = d.iadd(a, gap);
                    d.ieq(b, shifted)
                };
                let hi_fv = d.fresh_fvar();
                let hi = d.kernel().fvar(hi_fv);
                let inner = shift_predicate(d, c, e, &|_d, j| j);
                let inner_witness = d.const_app(p.le_dest, &[c, e, h[1]]);
                let inner_minor = {
                    let j_fv = d.fresh_fvar();
                    let j = d.kernel().fvar(j_fv);
                    let second_gap = d.of_nat(j);
                    let inner_equation = {
                        let shifted = d.iadd(c, second_gap);
                        d.ieq(e, shifted)
                    };
                    let hj_fv = d.fresh_fvar();
                    let hj = d.kernel().fvar(hj_fv);
                    let total = NatOps::add(d, i, j);
                    let base = d.const_app(p.le_of_nat_add, &[base_sum, total]);
                    let body = assemble(d, a, gap, c, second_gap, b, e, base, hi, hj, false);
                    let with_hj = d.lam_fv(hj_fv, inner_equation, body);
                    d.lam_fv(j_fv, nat, with_hj)
                };
                let body = exists_elim(d, inner, goal, inner_witness, inner_minor);
                let with_hi = d.lam_fv(hi_fv, equation, body);
                d.lam_fv(i_fv, nat, with_hi)
            };
            exists_elim(d, outer, goal, outer_witness, outer_minor)
        });
        (stmt, proof)
    })?;

    d.int_theorem(p.add_lt_add_of_le_of_lt, 4, &|d, v| {
        let (a, b, c, e) = (v[0], v[1], v[2], v[3]);
        let stmt = statements::add_lt_add_of_le_of_lt(d, v);
        let first_hypothesis = d.ile(a, b);
        let second_hypothesis = d.ilt(c, e);
        let base_sum = d.iadd(a, c);
        let goal = {
            let right = d.iadd(b, e);
            d.ilt(base_sum, right)
        };
        let proof = with_hypotheses(d, &[first_hypothesis, second_hypothesis], &|d, h| {
            let outer = shift_predicate(d, a, b, &|_d, i| i);
            let outer_witness = d.const_app(p.le_dest, &[a, b, h[0]]);
            let outer_minor = {
                let nat = d.nat_ty();
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let gap = d.of_nat(i);
                let equation = {
                    let shifted = d.iadd(a, gap);
                    d.ieq(b, shifted)
                };
                let hi_fv = d.fresh_fvar();
                let hi = d.kernel().fvar(hi_fv);
                let inner = shift_predicate(d, c, e, &|d, j| d.succ(j));
                let inner_witness = d.const_app(p.lt_dest, &[c, e, h[1]]);
                let inner_minor = {
                    let j_fv = d.fresh_fvar();
                    let j = d.kernel().fvar(j_fv);
                    let raised = d.succ(j);
                    let second_gap = d.of_nat(raised);
                    let inner_equation = {
                        let shifted = d.iadd(c, second_gap);
                        d.ieq(e, shifted)
                    };
                    let hj_fv = d.fresh_fvar();
                    let hj = d.kernel().fvar(hj_fv);
                    let total = NatOps::add(d, i, j);
                    let base = d.const_app(p.lt_of_nat_add, &[base_sum, total]);
                    let body = assemble(d, a, gap, c, second_gap, b, e, base, hi, hj, true);
                    let with_hj = d.lam_fv(hj_fv, inner_equation, body);
                    d.lam_fv(j_fv, nat, with_hj)
                };
                let body = exists_elim(d, inner, goal, inner_witness, inner_minor);
                let with_hi = d.lam_fv(hi_fv, equation, body);
                d.lam_fv(i_fv, nat, with_hi)
            };
            exists_elim(d, outer, goal, outer_witness, outer_minor)
        });
        (stmt, proof)
    })?;

    Ok(())
}

/// Shared tail of both additive order laws: rearrange the shifted sum and
/// substitute the two upper bounds back in.
///
/// `base` proves the relation between `a+c` and `(a+c)+(i+j)`; `hi` and `hj`
/// name the two upper bounds as shifts. `strict` only selects which relation the
/// motives are built with.
#[allow(clippy::too_many_arguments)]
fn assemble(
    d: &mut IntDev<'_>,
    a: ExprId,
    gap: ExprId,
    c: ExprId,
    second_gap: ExprId,
    upper: ExprId,
    second_upper: ExprId,
    base: ExprId,
    hi: ExprId,
    hj: ExprId,
    strict: bool,
) -> ExprId {
    let base_sum = d.iadd(a, c);
    let relate = move |d: &mut IntDev<'_>, x: ExprId| {
        if strict {
            d.ilt(base_sum, x)
        } else {
            d.ile(base_sum, x)
        }
    };
    let shuffle = add_shuffle(d, a, gap, c, second_gap);
    let shifted_left = d.iadd(a, gap);
    let shifted_right = d.iadd(c, second_gap);
    let split = d.iadd(shifted_left, shifted_right);
    let joined = {
        let total = d.iadd(gap, second_gap);
        d.iadd(base_sum, total)
    };
    let unshuffle = d.isymm(split, joined, shuffle);
    let rearranged = d.int_eq_rewrite(joined, split, unshuffle, base, &relate);
    let with_upper = {
        let flipped = d.isymm(upper, shifted_left, hi);
        d.int_eq_rewrite(shifted_left, upper, flipped, rearranged, &|d, x| {
            let right = d.iadd(x, shifted_right);
            relate(d, right)
        })
    };
    let flipped = d.isymm(second_upper, shifted_right, hj);
    d.int_eq_rewrite(shifted_right, second_upper, flipped, with_upper, &|d, x| {
        let right = d.iadd(upper, x);
        relate(d, right)
    })
}
