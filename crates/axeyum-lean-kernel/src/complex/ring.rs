//! A **commutative-ring calculus over `CReal`**, producing `CReal.Equiv` proof
//! terms — the layer that makes ℂ's ring laws cheap.
//!
//! Nothing here is a declaration. Every function returns a *proof term*, in the
//! same style as [`shifted_bound_le`](crate::creal) and
//! [`rsum_perm`](crate::rat_prelude): the ℂ development consumes them inline, so
//! the `CReal` namespace is untouched and the trusted surface is unchanged (a
//! term built from checked theorems has their union footprint, which is empty).
//!
//! # Why ℂ needs it and ℝ did not
//!
//! `CReal`'s own laws are each an *analytic* statement — an estimate at an index
//! — so they were proved one at a time against Bishop's modulus. Every ℂ law, by
//! contrast, is an *algebraic* identity in the components: the real part of
//! `(z·w)·v` and of `z·(w·v)` are the same four monomials of `CReal`s in a
//! different order, and no analysis is involved at all. Deriving each of those
//! by hand from `add_comm`/`add_assoc`/`mul_comm`/`mul_assoc`/`left_distrib`
//! plus five congruence lemmas is where a development this shape goes wrong
//! silently, so it is done once, by decision procedure.
//!
//! # The decision procedure
//!
//! Normal form is a **sorted multiset of signed monomials**, a monomial being a
//! sorted list of atoms; that is the free commutative ring on the atoms with ℤ
//! coefficients, represented additively. Two expressions are `Equiv` iff their
//! normal forms are equal, so [`ring_proof`] normalizes both sides and glues the
//! two proofs with `Equiv.trans`/`Equiv.symm`. Coefficients are *not* collected
//! — `x + x` stays two monomials — because nothing here needs them and a
//! coefficient would drag ℕ-arithmetic into a ring proof; opposite pairs **are**
//! cancelled, which is what `mul_conj`'s imaginary part needs.
//!
//! # `fold`, once, for both operations
//!
//! `add` and `mul` are the same commutative monoid with different names, so the
//! reassociation machinery ([`fold_append`], [`fold_pull`], [`fold_perm`]) is
//! written once against an [`Op`] tag. It is the shape of
//! [`rsum_perm`](crate::rat_prelude) and `iprod_perm`, one level up and over a
//! *defined* equality rather than `Eq`, which is exactly the transcription
//! ADR-0512 predicted would be needed.
//!
//! Like `rsum_perm`, the permutation and the final normal-form comparison
//! **panic** on a mismatch rather than building a term the kernel will reject a
//! thousand nodes deep: a wrong rearrangement is a bug in the caller, and the
//! Rust message names the two lists.

// Proof-term builders take the whole shape of the lemma they apply, so the
// argument counts follow the kernel's lemma signatures rather than any Rust
// convention.
#![allow(
    clippy::doc_markdown,
    clippy::large_types_passed_by_value,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use crate::CRealPrelude;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

// --- the raw CReal operations ------------------------------------------------

/// `CReal.add a b`.
pub(crate) fn cadd(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.add, &[a, b])
}

/// `CReal.mul a b`.
pub(crate) fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.mul, &[a, b])
}

/// `CReal.neg a`.
pub(crate) fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    d.const_app(p.neg, &[a])
}

/// `CReal.zero`.
pub(crate) fn czero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

/// `CReal.one`.
pub(crate) fn cone(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.one, vec![])
}

/// The proposition `CReal.Equiv a b`.
pub(crate) fn ceq(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.equiv, &[a, b])
}

/// `CReal.Equiv.refl a`.
pub(crate) fn crefl(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    d.lemma(p.equiv_refl, &[a])
}

/// `CReal.Equiv.symm`.
pub(crate) fn csymm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    h: ExprId,
) -> ExprId {
    d.lemma(p.equiv_symm, &[a, b, h])
}

/// `CReal.Equiv.trans`.
pub(crate) fn ctrans(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    first: ExprId,
    second: ExprId,
) -> ExprId {
    d.lemma(p.equiv_trans, &[a, b, c, first, second])
}

/// Fold a chain of `Equiv` steps from `start`, returning the endpoint and the
/// composite proof. The mirror of `rchain` at `CReal.Equiv`.
pub(crate) fn cchain(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    start: ExprId,
    steps: &[(ExprId, ExprId)],
) -> (ExprId, ExprId) {
    let mut current = start;
    let mut proof = crefl(d, p, start);
    for &(next, step) in steps {
        proof = ctrans(d, p, start, current, next, proof, step);
        current = next;
    }
    (current, proof)
}

// --- the two commutative monoids, as one ------------------------------------

/// Which commutative monoid a fold is over.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Op {
    /// `CReal.add`, unit `CReal.zero`.
    Add,
    /// `CReal.mul`, unit `CReal.one`.
    Mul,
}

fn op_term(d: &mut IntDev<'_>, p: CRealPrelude, op: Op, a: ExprId, b: ExprId) -> ExprId {
    match op {
        Op::Add => cadd(d, p, a, b),
        Op::Mul => cmul(d, p, a, b),
    }
}

fn op_unit(d: &mut IntDev<'_>, p: CRealPrelude, op: Op) -> ExprId {
    match op {
        Op::Add => czero(d, p),
        Op::Mul => cone(d, p),
    }
}

/// `Equiv (op a b) (op b a)`.
fn op_comm(d: &mut IntDev<'_>, p: CRealPrelude, op: Op, a: ExprId, b: ExprId) -> ExprId {
    let name = match op {
        Op::Add => p.add_comm,
        Op::Mul => p.mul_comm,
    };
    d.lemma(name, &[a, b])
}

/// `Equiv (op (op a b) c) (op a (op b c))`.
fn op_assoc(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    op: Op,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> ExprId {
    let name = match op {
        Op::Add => p.add_assoc,
        Op::Mul => p.mul_assoc,
    };
    d.lemma(name, &[a, b, c])
}

/// `Equiv a a' → Equiv b b' → Equiv (op a b) (op a' b')`.
fn op_congr(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    op: Op,
    a: ExprId,
    a2: ExprId,
    b: ExprId,
    b2: ExprId,
    left: ExprId,
    right: ExprId,
) -> ExprId {
    let name = match op {
        Op::Add => p.add_congr,
        Op::Mul => p.mul_congr,
    };
    d.lemma(name, &[a, a2, b, b2, left, right])
}

/// `Equiv (op a unit) a` — `add_zero` / `mul_one`.
fn op_unit_right(d: &mut IntDev<'_>, p: CRealPrelude, op: Op, a: ExprId) -> ExprId {
    let name = match op {
        Op::Add => p.add_zero,
        Op::Mul => p.mul_one,
    };
    d.lemma(name, &[a])
}

/// `Equiv (op unit a) a` — one `comm` away from [`op_unit_right`], and the
/// orientation neither package states.
fn op_unit_left(d: &mut IntDev<'_>, p: CRealPrelude, op: Op, a: ExprId) -> ExprId {
    let unit = op_unit(d, p, op);
    let flipped = op_term(d, p, op, a, unit);
    let start = op_term(d, p, op, unit, a);
    let commute = op_comm(d, p, op, unit, a);
    let collapse = op_unit_right(d, p, op, a);
    ctrans(d, p, start, flipped, a, commute, collapse)
}

/// `a0 op (a1 op (… op a_{n-1}))`, right-nested, with the **unit** for the
/// empty list.
pub(crate) fn fold(d: &mut IntDev<'_>, p: CRealPrelude, op: Op, atoms: &[ExprId]) -> ExprId {
    let Some((&last, front)) = atoms.split_last() else {
        return op_unit(d, p, op);
    };
    let mut acc = last;
    for &atom in front.iter().rev() {
        acc = op_term(d, p, op, atom, acc);
    }
    acc
}

/// `Equiv (op (fold xs) (fold ys)) (fold (xs ++ ys))`.
fn fold_append(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    op: Op,
    xs: &[ExprId],
    ys: &[ExprId],
) -> ExprId {
    if xs.is_empty() {
        let right = fold(d, p, op, ys);
        return op_unit_left(d, p, op, right);
    }
    if ys.is_empty() {
        let left = fold(d, p, op, xs);
        return op_unit_right(d, p, op, left);
    }
    if xs.len() == 1 {
        // `op xs[0] (fold ys)` IS `fold (xs ++ ys)`, syntactically.
        let whole = fold(d, p, op, ys);
        let joined = op_term(d, p, op, xs[0], whole);
        return crefl(d, p, joined);
    }
    let head = xs[0];
    let rest = &xs[1..];
    let rest_fold = fold(d, p, op, rest);
    let ys_fold = fold(d, p, op, ys);
    let start = {
        let left = op_term(d, p, op, head, rest_fold);
        op_term(d, p, op, left, ys_fold)
    };
    let regrouped = {
        let inner = op_term(d, p, op, rest_fold, ys_fold);
        op_term(d, p, op, head, inner)
    };
    let assoc = op_assoc(d, p, op, head, rest_fold, ys_fold);
    let mut joined: Vec<ExprId> = rest.to_vec();
    joined.extend_from_slice(ys);
    let joined_fold = fold(d, p, op, &joined);
    let inner_proof = fold_append(d, p, op, rest, ys);
    let inner_start = op_term(d, p, op, rest_fold, ys_fold);
    let head_refl = crefl(d, p, head);
    let lifted = op_congr(
        d,
        p,
        op,
        head,
        head,
        inner_start,
        joined_fold,
        head_refl,
        inner_proof,
    );
    let target = op_term(d, p, op, head, joined_fold);
    ctrans(d, p, start, regrouped, target, assoc, lifted)
}

/// `Equiv (fold xs) (op xs[i] (fold rest))`, `rest` being `xs` without `i`.
///
/// # Panics
///
/// Panics on an empty list or an out-of-range index.
fn fold_pull(d: &mut IntDev<'_>, p: CRealPrelude, op: Op, xs: &[ExprId], i: usize) -> ExprId {
    assert!(i < xs.len(), "fold_pull index out of range");
    if xs.len() == 1 {
        // `fold [x]` is `x`; the target writes `op x unit`.
        let whole = xs[0];
        let unit = op_unit(d, p, op);
        let padded = op_term(d, p, op, whole, unit);
        let collapse = op_unit_right(d, p, op, whole);
        return csymm(d, p, padded, whole, collapse);
    }
    if i == 0 {
        let whole = fold(d, p, op, xs);
        return crefl(d, p, whole);
    }
    let head = xs[0];
    let tail = &xs[1..];
    let chosen = xs[i];
    let mut tail_rest: Vec<ExprId> = tail.to_vec();
    tail_rest.remove(i - 1);
    let tail_fold = fold(d, p, op, tail);
    let tail_rest_fold = fold(d, p, op, &tail_rest);
    let inner = fold_pull(d, p, op, tail, i - 1);

    let start = op_term(d, p, op, head, tail_fold);
    let pulled = op_term(d, p, op, chosen, tail_rest_fold);
    let head_refl = crefl(d, p, head);
    let first = op_congr(d, p, op, head, head, tail_fold, pulled, head_refl, inner);
    let nested = op_term(d, p, op, head, pulled);
    let flat_head = op_term(d, p, op, head, chosen);
    let flat = op_term(d, p, op, flat_head, tail_rest_fold);
    let assoc = op_assoc(d, p, op, head, chosen, tail_rest_fold);
    let second = csymm(d, p, flat, nested, assoc);
    let commuted_head = op_term(d, p, op, chosen, head);
    let commute = op_comm(d, p, op, head, chosen);
    let rest_refl = crefl(d, p, tail_rest_fold);
    let third = op_congr(
        d,
        p,
        op,
        flat_head,
        commuted_head,
        tail_rest_fold,
        tail_rest_fold,
        commute,
        rest_refl,
    );
    let commuted = op_term(d, p, op, commuted_head, tail_rest_fold);
    let fourth = op_assoc(d, p, op, chosen, head, tail_rest_fold);
    let regrouped = {
        let inner_sum = op_term(d, p, op, head, tail_rest_fold);
        op_term(d, p, op, chosen, inner_sum)
    };
    let mut steps = vec![
        (nested, first),
        (flat, second),
        (commuted, third),
        (regrouped, fourth),
    ];
    if tail_rest.is_empty() {
        // `fold (head :: [])` is `head`, but the chain has reached
        // `op chosen (op head unit)`.
        let padded = op_term(d, p, op, head, tail_rest_fold);
        let collapse = op_unit_right(d, p, op, head);
        let chosen_refl = crefl(d, p, chosen);
        let trimmed = op_congr(
            d,
            p,
            op,
            chosen,
            chosen,
            padded,
            head,
            chosen_refl,
            collapse,
        );
        let target = op_term(d, p, op, chosen, head);
        steps.push((target, trimmed));
    }
    let (_, proof) = cchain(d, p, start, &steps);
    proof
}

/// `Equiv (fold xs) (fold ys)` when `ys` is a permutation of `xs`.
///
/// # Panics
///
/// Panics if `ys` is not a permutation of `xs`.
pub(crate) fn fold_perm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    op: Op,
    xs: &[ExprId],
    ys: &[ExprId],
) -> ExprId {
    assert_eq!(xs.len(), ys.len(), "fold_perm needs equal lengths");
    if xs.is_empty() {
        let unit = op_unit(d, p, op);
        return crefl(d, p, unit);
    }
    if xs.len() == 1 {
        assert_eq!(xs[0], ys[0], "fold_perm was given a non-permutation");
        return crefl(d, p, xs[0]);
    }
    let target = ys[0];
    let position = xs
        .iter()
        .position(|&x| x == target)
        .expect("fold_perm was given a non-permutation");
    let mut rest: Vec<ExprId> = xs.to_vec();
    rest.remove(position);
    let pull = fold_pull(d, p, op, xs, position);
    let rest_fold = fold(d, p, op, &rest);
    let tail_fold = fold(d, p, op, &ys[1..]);
    let inner = fold_perm(d, p, op, &rest, &ys[1..]);
    let head_refl = crefl(d, p, target);
    let lifted = op_congr(
        d, p, op, target, target, rest_fold, tail_fold, head_refl, inner,
    );
    let start = fold(d, p, op, xs);
    let middle = op_term(d, p, op, target, rest_fold);
    let end = op_term(d, p, op, target, tail_fold);
    ctrans(d, p, start, middle, end, pull, lifted)
}

// --- the derived group and ring identities ----------------------------------

/// `Equiv (add zero a) a`.
fn zero_add(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    op_unit_left(d, p, Op::Add, a)
}

/// `Equiv (mul zero a) zero`.
fn zero_mul(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    let zero = czero(d, p);
    let start = cmul(d, p, zero, a);
    let flipped = cmul(d, p, a, zero);
    let commute = d.lemma(p.mul_comm, &[zero, a]);
    let collapse = d.lemma(p.mul_zero, &[a]);
    ctrans(d, p, start, flipped, zero, commute, collapse)
}

/// `Equiv (add (neg a) a) zero` — the orientation `add_neg` does not state.
fn neg_add_cancel(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    let negated = cneg(d, p, a);
    let start = cadd(d, p, negated, a);
    let flipped = cadd(d, p, a, negated);
    let zero = czero(d, p);
    let commute = d.lemma(p.add_comm, &[negated, a]);
    let collapse = d.lemma(p.add_neg, &[a]);
    ctrans(d, p, start, flipped, zero, commute, collapse)
}

/// `Equiv (neg zero) zero`.
fn neg_zero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let zero = czero(d, p);
    let negated = cneg(d, p, zero);
    let padded = cadd(d, p, zero, negated);
    let expand = zero_add(d, p, negated);
    let back = csymm(d, p, padded, negated, expand);
    let collapse = d.lemma(p.add_neg, &[zero]);
    ctrans(d, p, negated, padded, zero, back, collapse)
}

/// From `Equiv (add a b) zero`, conclude `Equiv (neg a) b` — uniqueness of the
/// additive inverse, and the lever every sign identity below goes through.
fn neg_eq_of_add_zero(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    hypothesis: ExprId,
) -> ExprId {
    let zero = czero(d, p);
    let negated = cneg(d, p, a);
    let sum = cadd(d, p, a, b);

    let padded = cadd(d, p, negated, zero);
    let collapse = d.lemma(p.add_zero, &[negated]);
    let expand = csymm(d, p, padded, negated, collapse);

    let back = csymm(d, p, sum, zero, hypothesis);
    let neg_refl = crefl(d, p, negated);
    let widened = cadd(d, p, negated, sum);
    let step2 = op_congr(d, p, Op::Add, negated, negated, zero, sum, neg_refl, back);

    let regrouped = {
        let inner = cadd(d, p, negated, a);
        cadd(d, p, inner, b)
    };
    let assoc = d.lemma(p.add_assoc, &[negated, a, b]);
    let step3 = csymm(d, p, regrouped, widened, assoc);

    let cancel = neg_add_cancel(d, p, a);
    let b_refl = crefl(d, p, b);
    let inner_left = cadd(d, p, negated, a);
    let step4 = op_congr(d, p, Op::Add, inner_left, zero, b, b, cancel, b_refl);
    let with_zero = cadd(d, p, zero, b);
    let step5 = zero_add(d, p, b);

    let (_, proof) = cchain(
        d,
        p,
        negated,
        &[
            (padded, expand),
            (widened, step2),
            (regrouped, step3),
            (with_zero, step4),
            (b, step5),
        ],
    );
    proof
}

/// `Equiv (neg (neg a)) a`.
fn neg_neg(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    let negated = cneg(d, p, a);
    let cancel = neg_add_cancel(d, p, a);
    neg_eq_of_add_zero(d, p, negated, a, cancel)
}

/// `Equiv (neg (add a b)) (add (neg a) (neg b))`.
fn neg_add(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let na = cneg(d, p, a);
    let nb = cneg(d, p, b);
    let zero = czero(d, p);

    // `(a + b) + ((−a) + (−b)) ~ 0`, by reassociation into `a + (−a + (b + −b))`.
    let left = cadd(d, p, a, b);
    let right = cadd(d, p, na, nb);
    let start = cadd(d, p, left, right);
    let joined = fold_append(d, p, Op::Add, &[a, b], &[na, nb]);
    let listed = fold(d, p, Op::Add, &[a, b, na, nb]);
    let sorted = fold(d, p, Op::Add, &[a, na, b, nb]);
    let permuted = fold_perm(d, p, Op::Add, &[a, b, na, nb], &[a, na, b, nb]);

    let inner_pair = cadd(d, p, b, nb);
    let pair_zero = d.lemma(p.add_neg, &[b]);
    let na_refl = crefl(d, p, na);
    let inner = op_congr(d, p, Op::Add, na, na, inner_pair, zero, na_refl, pair_zero);
    let a_refl = crefl(d, p, a);
    let inner_start = cadd(d, p, na, inner_pair);
    let inner_end = cadd(d, p, na, zero);
    let lifted = op_congr(d, p, Op::Add, a, a, inner_start, inner_end, a_refl, inner);
    let stage = cadd(d, p, a, inner_end);
    let trim_inner = d.lemma(p.add_zero, &[na]);
    let a_refl2 = crefl(d, p, a);
    let trimmed = op_congr(d, p, Op::Add, a, a, inner_end, na, a_refl2, trim_inner);
    let pair = cadd(d, p, a, na);
    let finish = d.lemma(p.add_neg, &[a]);
    let (_, to_zero) = cchain(
        d,
        p,
        start,
        &[
            (listed, joined),
            (sorted, permuted),
            (stage, lifted),
            (pair, trimmed),
            (zero, finish),
        ],
    );
    neg_eq_of_add_zero(d, p, left, right, to_zero)
}

/// `Equiv (mul (add a b) c) (add (mul a c) (mul b c))`.
fn right_distrib(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
    let sum = cadd(d, p, a, b);
    let start = cmul(d, p, sum, c);
    let flipped = cmul(d, p, c, sum);
    let commute = d.lemma(p.mul_comm, &[sum, c]);
    let ca = cmul(d, p, c, a);
    let cb = cmul(d, p, c, b);
    let expanded = cadd(d, p, ca, cb);
    let distrib = d.lemma(p.left_distrib, &[c, a, b]);
    let ac = cmul(d, p, a, c);
    let bc = cmul(d, p, b, c);
    let target = cadd(d, p, ac, bc);
    let left_swap = d.lemma(p.mul_comm, &[c, a]);
    let right_swap = d.lemma(p.mul_comm, &[c, b]);
    let swapped = op_congr(d, p, Op::Add, ca, ac, cb, bc, left_swap, right_swap);
    let (_, proof) = cchain(
        d,
        p,
        start,
        &[(flipped, commute), (expanded, distrib), (target, swapped)],
    );
    proof
}

/// `Equiv (mul (neg a) b) (neg (mul a b))`.
fn neg_mul(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let na = cneg(d, p, a);
    let ab = cmul(d, p, a, b);
    let nab = cmul(d, p, na, b);
    let zero = czero(d, p);

    let start = cadd(d, p, ab, nab);
    let factored = {
        let inner = cadd(d, p, a, na);
        cmul(d, p, inner, b)
    };
    let expand = right_distrib(d, p, a, na, b);
    let back = csymm(d, p, factored, start, expand);
    let inner_sum = cadd(d, p, a, na);
    let cancel = d.lemma(p.add_neg, &[a]);
    let b_refl = crefl(d, p, b);
    let collapsed = cmul(d, p, zero, b);
    let step = op_congr(d, p, Op::Mul, inner_sum, zero, b, b, cancel, b_refl);
    let finish = zero_mul(d, p, b);
    let (_, to_zero) = cchain(
        d,
        p,
        start,
        &[(factored, back), (collapsed, step), (zero, finish)],
    );
    let uniqueness = neg_eq_of_add_zero(d, p, ab, nab, to_zero);
    let negated_product = cneg(d, p, ab);
    csymm(d, p, negated_product, nab, uniqueness)
}

/// `Equiv (mul a (neg b)) (neg (mul a b))`.
fn mul_neg(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let nb = cneg(d, p, b);
    let start = cmul(d, p, a, nb);
    let flipped = cmul(d, p, nb, a);
    let commute = d.lemma(p.mul_comm, &[a, nb]);
    let ba = cmul(d, p, b, a);
    let pulled = cneg(d, p, ba);
    let pull = neg_mul(d, p, b, a);
    let ab = cmul(d, p, a, b);
    let target = cneg(d, p, ab);
    let swap = d.lemma(p.mul_comm, &[b, a]);
    let lifted = d.lemma(p.neg_congr, &[ba, ab, swap]);
    let (_, proof) = cchain(
        d,
        p,
        start,
        &[(flipped, commute), (pulled, pull), (target, lifted)],
    );
    proof
}

// --- the normal form ---------------------------------------------------------

/// One signed monomial: a **sorted** list of atoms, and a sign.
///
/// Field order is load-bearing: the derived `Ord` sorts by atoms first, so
/// monomials over the same atoms with opposite signs land adjacent and
/// [`canonicalize`] can cancel them in one pass.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(crate) struct Mono {
    atoms: Vec<ExprId>,
    neg: bool,
}

/// A formal expression over `CReal`, in the language the normalizer decides.
///
/// [`RExpr::Zero`] and [`RExpr::One`] are the *constants* `CReal.zero` and
/// `CReal.one`, not atoms: the whole point is that `x · 1` and `x · 0` collapse.
#[derive(Clone, Debug)]
pub(crate) enum RExpr {
    /// An opaque `CReal` term — a variable, or anything the calculus should not
    /// look inside.
    Atom(ExprId),
    /// `CReal.zero`.
    Zero,
    /// `CReal.one`.
    One,
    /// `CReal.add`.
    Add(Box<RExpr>, Box<RExpr>),
    /// `CReal.mul`.
    Mul(Box<RExpr>, Box<RExpr>),
    /// `CReal.neg`.
    Neg(Box<RExpr>),
}

impl RExpr {
    /// `a + b`.
    pub(crate) fn add(a: RExpr, b: RExpr) -> RExpr {
        RExpr::Add(Box::new(a), Box::new(b))
    }
    /// `a · b`.
    pub(crate) fn mul(a: RExpr, b: RExpr) -> RExpr {
        RExpr::Mul(Box::new(a), Box::new(b))
    }
    /// `−a`.
    pub(crate) fn neg(a: RExpr) -> RExpr {
        RExpr::Neg(Box::new(a))
    }
}

/// Render a formal expression as the `CReal` term it denotes.
pub(crate) fn render(d: &mut IntDev<'_>, p: CRealPrelude, e: &RExpr) -> ExprId {
    match e {
        RExpr::Atom(a) => *a,
        RExpr::Zero => czero(d, p),
        RExpr::One => cone(d, p),
        RExpr::Add(a, b) => {
            let left = render(d, p, a);
            let right = render(d, p, b);
            cadd(d, p, left, right)
        }
        RExpr::Mul(a, b) => {
            let left = render(d, p, a);
            let right = render(d, p, b);
            cmul(d, p, left, right)
        }
        RExpr::Neg(a) => {
            let inner = render(d, p, a);
            cneg(d, p, inner)
        }
    }
}

fn mono_term(d: &mut IntDev<'_>, p: CRealPrelude, m: &Mono) -> ExprId {
    let product = fold(d, p, Op::Mul, &m.atoms);
    if m.neg { cneg(d, p, product) } else { product }
}

fn mono_terms(d: &mut IntDev<'_>, p: CRealPrelude, monos: &[Mono]) -> Vec<ExprId> {
    monos.iter().map(|m| mono_term(d, p, m)).collect()
}

/// The canonical term of a monomial multiset: `zero` when empty.
pub(crate) fn sum_term(d: &mut IntDev<'_>, p: CRealPrelude, monos: &[Mono]) -> ExprId {
    let terms = mono_terms(d, p, monos);
    fold(d, p, Op::Add, &terms)
}

fn flip(monos: &[Mono]) -> Vec<Mono> {
    monos
        .iter()
        .map(|m| Mono {
            atoms: m.atoms.clone(),
            neg: !m.neg,
        })
        .collect()
}

/// `Equiv (neg (sum_term monos)) (sum_term (flip monos))`.
fn neg_sum(d: &mut IntDev<'_>, p: CRealPrelude, monos: &[Mono]) -> ExprId {
    match monos {
        [] => neg_zero(d, p),
        [m] => {
            let product = fold(d, p, Op::Mul, &m.atoms);
            if m.neg {
                // `neg (neg P) ~ P`.
                neg_neg(d, p, product)
            } else {
                // `neg P` is already the flipped monomial's term.
                let negated = cneg(d, p, product);
                crefl(d, p, negated)
            }
        }
        [head, rest @ ..] => {
            let head_term = mono_term(d, p, head);
            let rest_term = sum_term(d, p, rest);
            let split = neg_add(d, p, head_term, rest_term);
            let negated_head = cneg(d, p, head_term);
            let negated_rest = cneg(d, p, rest_term);
            let head_slice = std::slice::from_ref(head);
            let head_proof = neg_sum(d, p, head_slice);
            let rest_proof = neg_sum(d, p, rest);
            let flipped_head = flip(head_slice);
            let flipped_rest = flip(rest);
            let flipped_head_term = sum_term(d, p, &flipped_head);
            let flipped_rest_term = sum_term(d, p, &flipped_rest);
            let lifted = op_congr(
                d,
                p,
                Op::Add,
                negated_head,
                flipped_head_term,
                negated_rest,
                flipped_rest_term,
                head_proof,
                rest_proof,
            );
            let joint = cadd(d, p, head_term, rest_term);
            let start = cneg(d, p, joint);
            let middle = cadd(d, p, negated_head, negated_rest);
            let end = cadd(d, p, flipped_head_term, flipped_rest_term);
            ctrans(d, p, start, middle, end, split, lifted)
        }
    }
}

fn mul_mono_mono(d: &mut IntDev<'_>, p: CRealPrelude, m: &Mono, n: &Mono) -> (Mono, ExprId) {
    let mut concat: Vec<ExprId> = m.atoms.clone();
    concat.extend_from_slice(&n.atoms);
    let mut sorted = concat.clone();
    sorted.sort_unstable();
    let result = Mono {
        atoms: sorted.clone(),
        neg: m.neg != n.neg,
    };

    let left = fold(d, p, Op::Mul, &m.atoms);
    let right = fold(d, p, Op::Mul, &n.atoms);
    let raw = cmul(d, p, left, right);
    let concat_fold = fold(d, p, Op::Mul, &concat);
    let sorted_fold = fold(d, p, Op::Mul, &sorted);
    let append = fold_append(d, p, Op::Mul, &m.atoms, &n.atoms);
    let permute = fold_perm(d, p, Op::Mul, &concat, &sorted);
    let base = ctrans(d, p, raw, concat_fold, sorted_fold, append, permute);

    let proof = match (m.neg, n.neg) {
        (false, false) => base,
        (true, false) => {
            let negated_left = cneg(d, p, left);
            let start = cmul(d, p, negated_left, right);
            let pulled = cneg(d, p, raw);
            let pull = neg_mul(d, p, left, right);
            let target = cneg(d, p, sorted_fold);
            let lifted = d.lemma(p.neg_congr, &[raw, sorted_fold, base]);
            let (_, proof) = cchain(d, p, start, &[(pulled, pull), (target, lifted)]);
            proof
        }
        (false, true) => {
            let negated_right = cneg(d, p, right);
            let start = cmul(d, p, left, negated_right);
            let pulled = cneg(d, p, raw);
            let pull = mul_neg(d, p, left, right);
            let target = cneg(d, p, sorted_fold);
            let lifted = d.lemma(p.neg_congr, &[raw, sorted_fold, base]);
            let (_, proof) = cchain(d, p, start, &[(pulled, pull), (target, lifted)]);
            proof
        }
        (true, true) => {
            let negated_left = cneg(d, p, left);
            let negated_right = cneg(d, p, right);
            let start = cmul(d, p, negated_left, negated_right);
            let inner_start = cmul(d, p, left, negated_right);
            let once = cneg(d, p, inner_start);
            let first = neg_mul(d, p, left, negated_right);
            let inner = mul_neg(d, p, left, right);
            let inner_end = cneg(d, p, raw);
            let second = d.lemma(p.neg_congr, &[inner_start, inner_end, inner]);
            let twice = cneg(d, p, inner_end);
            let third = neg_neg(d, p, raw);
            let (_, proof) = cchain(
                d,
                p,
                start,
                &[
                    (once, first),
                    (twice, second),
                    (raw, third),
                    (sorted_fold, base),
                ],
            );
            proof
        }
    };
    (result, proof)
}

fn mul_mono_sum(d: &mut IntDev<'_>, p: CRealPrelude, m: &Mono, ns: &[Mono]) -> (Vec<Mono>, ExprId) {
    let head_term = mono_term(d, p, m);
    match ns {
        [] => {
            let proof = d.lemma(p.mul_zero, &[head_term]);
            (Vec::new(), proof)
        }
        [n] => {
            let (result, proof) = mul_mono_mono(d, p, m, n);
            (vec![result], proof)
        }
        [n, rest @ ..] => {
            let first_term = mono_term(d, p, n);
            let rest_term = sum_term(d, p, rest);
            let sum = cadd(d, p, first_term, rest_term);
            let start = cmul(d, p, head_term, sum);
            let distrib = d.lemma(p.left_distrib, &[head_term, first_term, rest_term]);
            let left_product = cmul(d, p, head_term, first_term);
            let right_product = cmul(d, p, head_term, rest_term);
            let expanded = cadd(d, p, left_product, right_product);

            let (first_result, first_proof) = mul_mono_mono(d, p, m, n);
            let (rest_result, rest_proof) = mul_mono_sum(d, p, m, rest);
            let first_canon = mono_term(d, p, &first_result);
            let rest_canon = sum_term(d, p, &rest_result);
            let lifted = op_congr(
                d,
                p,
                Op::Add,
                left_product,
                first_canon,
                right_product,
                rest_canon,
                first_proof,
                rest_proof,
            );
            let paired = cadd(d, p, first_canon, rest_canon);

            let rest_terms = mono_terms(d, p, &rest_result);
            let join = fold_append(d, p, Op::Add, &[first_canon], &rest_terms);
            let mut result = vec![first_result];
            result.extend(rest_result);
            let joined = sum_term(d, p, &result);

            let (_, proof) = cchain(
                d,
                p,
                start,
                &[(expanded, distrib), (paired, lifted), (joined, join)],
            );
            (result, proof)
        }
    }
}

fn mul_sum_sum(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    ms: &[Mono],
    ns: &[Mono],
) -> (Vec<Mono>, ExprId) {
    match ms {
        [] => {
            let right = sum_term(d, p, ns);
            let proof = zero_mul(d, p, right);
            (Vec::new(), proof)
        }
        [m] => mul_mono_sum(d, p, m, ns),
        [m, rest @ ..] => {
            let head_term = mono_term(d, p, m);
            let rest_term = sum_term(d, p, rest);
            let right = sum_term(d, p, ns);
            let sum = cadd(d, p, head_term, rest_term);
            let start = cmul(d, p, sum, right);
            let distrib = right_distrib(d, p, head_term, rest_term, right);
            let left_product = cmul(d, p, head_term, right);
            let right_product = cmul(d, p, rest_term, right);
            let expanded = cadd(d, p, left_product, right_product);

            let (first_result, first_proof) = mul_mono_sum(d, p, m, ns);
            let (rest_result, rest_proof) = mul_sum_sum(d, p, rest, ns);
            let first_canon = sum_term(d, p, &first_result);
            let rest_canon = sum_term(d, p, &rest_result);
            let lifted = op_congr(
                d,
                p,
                Op::Add,
                left_product,
                first_canon,
                right_product,
                rest_canon,
                first_proof,
                rest_proof,
            );
            let paired = cadd(d, p, first_canon, rest_canon);

            let first_terms = mono_terms(d, p, &first_result);
            let rest_terms = mono_terms(d, p, &rest_result);
            let join = fold_append(d, p, Op::Add, &first_terms, &rest_terms);
            let mut result = first_result;
            result.extend(rest_result);
            let joined = sum_term(d, p, &result);

            let (_, proof) = cchain(
                d,
                p,
                start,
                &[(expanded, distrib), (paired, lifted), (joined, join)],
            );
            (result, proof)
        }
    }
}

/// `(normal form, proof of `Equiv (render e) (sum_term normal form)`)`.
fn normalize(d: &mut IntDev<'_>, p: CRealPrelude, e: &RExpr) -> (Vec<Mono>, ExprId) {
    match e {
        RExpr::Atom(a) => {
            let monos = vec![Mono {
                atoms: vec![*a],
                neg: false,
            }];
            let proof = crefl(d, p, *a);
            (monos, proof)
        }
        RExpr::Zero => {
            let zero = czero(d, p);
            let proof = crefl(d, p, zero);
            (Vec::new(), proof)
        }
        RExpr::One => {
            let one = cone(d, p);
            let proof = crefl(d, p, one);
            (
                vec![Mono {
                    atoms: Vec::new(),
                    neg: false,
                }],
                proof,
            )
        }
        RExpr::Neg(inner) => {
            let (monos, proof) = normalize(d, p, inner);
            let source = render(d, p, inner);
            let canon = sum_term(d, p, &monos);
            let start = cneg(d, p, source);
            let middle = cneg(d, p, canon);
            let lifted = d.lemma(p.neg_congr, &[source, canon, proof]);
            let flipped = flip(&monos);
            let end = sum_term(d, p, &flipped);
            let distribute = neg_sum(d, p, &monos);
            let composite = ctrans(d, p, start, middle, end, lifted, distribute);
            (flipped, composite)
        }
        RExpr::Add(a, b) => {
            let (ma, pa) = normalize(d, p, a);
            let (mb, pb) = normalize(d, p, b);
            let source_a = render(d, p, a);
            let source_b = render(d, p, b);
            let canon_a = sum_term(d, p, &ma);
            let canon_b = sum_term(d, p, &mb);
            let start = cadd(d, p, source_a, source_b);
            let middle = cadd(d, p, canon_a, canon_b);
            let lifted = op_congr(d, p, Op::Add, source_a, canon_a, source_b, canon_b, pa, pb);
            let terms_a = mono_terms(d, p, &ma);
            let terms_b = mono_terms(d, p, &mb);
            let join = fold_append(d, p, Op::Add, &terms_a, &terms_b);
            let mut result = ma;
            result.extend(mb);
            let end = sum_term(d, p, &result);
            let composite = ctrans(d, p, start, middle, end, lifted, join);
            (result, composite)
        }
        RExpr::Mul(a, b) => {
            let (ma, pa) = normalize(d, p, a);
            let (mb, pb) = normalize(d, p, b);
            let source_a = render(d, p, a);
            let source_b = render(d, p, b);
            let canon_a = sum_term(d, p, &ma);
            let canon_b = sum_term(d, p, &mb);
            let start = cmul(d, p, source_a, source_b);
            let middle = cmul(d, p, canon_a, canon_b);
            let lifted = op_congr(d, p, Op::Mul, source_a, canon_a, source_b, canon_b, pa, pb);
            let (result, expand) = mul_sum_sum(d, p, &ma, &mb);
            let end = sum_term(d, p, &result);
            let composite = ctrans(d, p, start, middle, end, lifted, expand);
            (result, composite)
        }
    }
}

/// Sort the multiset and cancel opposite pairs.
///
/// Returns the canonical multiset and a proof that the original sum is
/// `Equiv` to it.
fn canonicalize(d: &mut IntDev<'_>, p: CRealPrelude, monos: &[Mono]) -> (Vec<Mono>, ExprId) {
    let mut current: Vec<Mono> = monos.to_vec();
    let start = sum_term(d, p, &current);
    let mut steps: Vec<(ExprId, ExprId)> = Vec::new();

    // Sort once: the derived `Ord` puts equal-atom monomials adjacent.
    let mut sorted = current.clone();
    sorted.sort();
    if sorted != current {
        let from = mono_terms(d, p, &current);
        let to = mono_terms(d, p, &sorted);
        let permute = fold_perm(d, p, Op::Add, &from, &to);
        let target = sum_term(d, p, &sorted);
        steps.push((target, permute));
        current = sorted;
    }

    // Cancel adjacent opposite pairs until none remain. Removing two adjacent
    // entries from a sorted list leaves it sorted, so no re-sort is needed.
    while let Some(index) = (0..current.len().saturating_sub(1))
        .find(|&i| current[i].atoms == current[i + 1].atoms && current[i].neg != current[i + 1].neg)
    {
        let mut reordered = vec![current[index].clone(), current[index + 1].clone()];
        for (position, mono) in current.iter().enumerate() {
            if position != index && position != index + 1 {
                reordered.push(mono.clone());
            }
        }
        let from = mono_terms(d, p, &current);
        let to = mono_terms(d, p, &reordered);
        let permute = fold_perm(d, p, Op::Add, &from, &to);
        let moved = sum_term(d, p, &reordered);
        steps.push((moved, permute));

        let first = mono_term(d, p, &reordered[0]);
        let second = mono_term(d, p, &reordered[1]);
        let product = fold(d, p, Op::Mul, &reordered[0].atoms);
        let pair_zero = if reordered[0].neg {
            neg_add_cancel(d, p, product)
        } else {
            d.lemma(p.add_neg, &[product])
        };
        let zero = czero(d, p);
        let rest = &reordered[2..];
        let remainder: Vec<Mono> = rest.to_vec();
        if remainder.is_empty() {
            steps.push((zero, pair_zero));
        } else {
            let rest_term = sum_term(d, p, &remainder);
            let regrouped = {
                let pair = cadd(d, p, first, second);
                cadd(d, p, pair, rest_term)
            };
            let nested = {
                let inner = cadd(d, p, second, rest_term);
                cadd(d, p, first, inner)
            };
            let assoc = d.lemma(p.add_assoc, &[first, second, rest_term]);
            let regroup = csymm(d, p, regrouped, nested, assoc);
            steps.push((regrouped, regroup));

            let pair = cadd(d, p, first, second);
            let rest_refl = crefl(d, p, rest_term);
            let collapsed = cadd(d, p, zero, rest_term);
            let collapse = op_congr(
                d,
                p,
                Op::Add,
                pair,
                zero,
                rest_term,
                rest_term,
                pair_zero,
                rest_refl,
            );
            steps.push((collapsed, collapse));
            let trim = zero_add(d, p, rest_term);
            steps.push((rest_term, trim));
        }
        current = remainder;
    }

    let (_, proof) = cchain(d, p, start, &steps);
    (current, proof)
}

/// A proof of `CReal.Equiv (render lhs) (render rhs)`.
///
/// # Panics
///
/// Panics when the two normal forms differ — the identity is **not** a
/// consequence of the commutative-ring laws, and the caller is wrong. The
/// message names both normal forms rather than letting the kernel reject an
/// enormous term with a type mismatch.
pub(crate) fn ring_proof(d: &mut IntDev<'_>, p: CRealPrelude, lhs: &RExpr, rhs: &RExpr) -> ExprId {
    let left_source = render(d, p, lhs);
    let right_source = render(d, p, rhs);

    let (raw_left, left_proof) = normalize(d, p, lhs);
    let raw_left_term = sum_term(d, p, &raw_left);
    let (canon_left, left_canon_proof) = canonicalize(d, p, &raw_left);
    let canon_left_term = sum_term(d, p, &canon_left);
    let full_left = ctrans(
        d,
        p,
        left_source,
        raw_left_term,
        canon_left_term,
        left_proof,
        left_canon_proof,
    );

    let (raw_right, right_proof) = normalize(d, p, rhs);
    let raw_right_term = sum_term(d, p, &raw_right);
    let (canon_right, right_canon_proof) = canonicalize(d, p, &raw_right);
    let canon_right_term = sum_term(d, p, &canon_right);
    let full_right = ctrans(
        d,
        p,
        right_source,
        raw_right_term,
        canon_right_term,
        right_proof,
        right_canon_proof,
    );

    assert_eq!(
        canon_left, canon_right,
        "ring_proof: the two sides have different normal forms, so the identity \
         does not follow from the commutative-ring laws"
    );
    let back = csymm(d, p, right_source, canon_right_term, full_right);
    ctrans(
        d,
        p,
        left_source,
        canon_left_term,
        right_source,
        full_left,
        back,
    )
}
