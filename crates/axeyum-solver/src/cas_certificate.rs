//! The **trusted, independent checker** for the `cas-*` route certificates
//! (ADR-0386).
//!
//! This module is the "trusted small checking" half of the CAS bridge. The
//! discovery half ([`crate::cas_poly`]) normalizes terms with `axeyum-cas`'s
//! `MvPoly` — a canonical `BTreeMap` polynomial engine with exact ℚ
//! coefficients, multivariate division and GCD. Nothing in *this* module may
//! depend on that engine, and nothing here does: the only imports are
//! `axeyum_ir` and the certificate types. A `cas-*` route's `unsat` is emitted
//! **only after** the corresponding `check_*` function below re-derives the
//! refutation from the original assertion list, so an `MvPoly` bug cannot by
//! itself produce a wrong verdict.
//!
//! # What the checker re-derives
//!
//! It never trusts the certificate's own numbers. Given only `arena` and the
//! caller's `assertions`, it
//!
//! 1. re-scans the top-level conjuncts and confirms the cited assertion is one
//!    of them and has the cited shape;
//! 2. re-expands the arithmetic terms into a canonical sum of monomials with its
//!    own [`expand`] — a flat sort-and-merge expander that shares no code with
//!    `MvPoly`, keys monomials by [`TermId`] rather than by a variable name, and
//!    builds its own opaque-atom abstraction from scratch;
//! 3. checks the refutation condition against *that* expansion, re-reading every
//!    cited integer bound off the conjunct claimed to assert it.
//!
//! The certificate's stored normal form is compared against the re-derivation,
//! so a printed certificate is auditable, but the verdict depends only on the
//! checker's own result.
//!
//! # Why abstracting non-polynomial subterms is sound
//!
//! [`expand`] maps every subterm outside the `+ − × ÷ᶜ` fragment (a `div`, a
//! `mod`, an `abs`, an `ite`, an uninterpreted application, …) to an opaque
//! atom. Both refutations are of the form "this polynomial in the atoms is
//! identically zero / has no integer solution **for every** assignment of values
//! to the atoms", which is a *stronger* statement than the one about the
//! original terms — whatever the abstracted subterms denote, they denote *some*
//! value, and the conclusion holds at that value too. Over-abstraction can only
//! make a refutation fail to fire, never fire wrongly.
//!
//! The one direction that would be unsound is collapsing two *different*
//! subterms onto the same atom. [`TermArena`] is hash-consed, so distinct
//! [`TermId`]s are distinct syntactic terms, and [`expand`] interns atoms by
//! `TermId`: two atoms are identified exactly when they are the same term.

use std::collections::BTreeSet;

use axeyum_ir::{Op, Rational, Sort, TermArena, TermId, TermNode};

use crate::cas_poly::{
    CasIdentityCertificate, CasIntBound, CasIntUnitsCertificate, CasIntUnitsKind,
};

/// Ceiling on distinct opaque atoms in one expansion.
pub(crate) const MAX_ATOMS: usize = 512;
/// Ceiling on monomials in an intermediate or final expansion. A product of two
/// dense polynomials multiplies term counts, so this bounds the whole expansion.
pub(crate) const MAX_MONOMIALS: usize = 4096;
/// Ceiling on visited term nodes, so the walk is bounded by a deterministic step
/// count rather than a wall clock (determinism is a public API promise).
pub(crate) const MAX_STEPS: u32 = 200_000;
/// Ceiling on recursion depth, so a pathologically deep left-nested sum cannot
/// exhaust the stack (`deep_nesting_no_abort` guards this class).
pub(crate) const MAX_DEPTH: u32 = 256;

/// A monomial keyed by the [`TermId`] of each opaque atom, sorted ascending by
/// that id, with every exponent `> 0`. The empty vector is the constant monomial.
pub type AtomMonomial = Vec<(TermId, u32)>;

/// A polynomial as a canonical, sorted list of `(monomial, nonzero coefficient)`
/// pairs. Two expansions are equal iff the terms they denote are equal as
/// polynomials in the atoms.
pub type AtomPoly = Vec<(AtomMonomial, Rational)>;

/// The independent expansion of `term` into a canonical sum of monomials over
/// opaque atoms, or `None` when the term leaves the fragment or a ceiling trips.
///
/// This is a deliberately plain algorithm — recursive descent producing a `Vec`
/// of monomials, then one sort-and-merge canonicalization — chosen so it shares
/// no structure with the `MvPoly` engine whose answer it checks.
///
/// `atoms` is threaded so several terms expand over one shared abstraction; pass
/// the same set to expand both sides of an equality.
#[must_use]
pub fn expand(arena: &TermArena, term: TermId, atoms: &mut BTreeSet<TermId>) -> Option<AtomPoly> {
    let mut steps = MAX_STEPS;
    expand_inner(arena, term, atoms, &mut steps, 0)
}

fn expand_inner(
    arena: &TermArena,
    term: TermId,
    atoms: &mut BTreeSet<TermId>,
    steps: &mut u32,
    depth: u32,
) -> Option<AtomPoly> {
    if depth > MAX_DEPTH {
        return None;
    }
    *steps = steps.checked_sub(1)?;

    match arena.node(term) {
        TermNode::IntConst(value) => Some(constant(Rational::checked_new(*value, 1)?)),
        TermNode::RealConst(value) => Some(constant(*value)),
        TermNode::App { op, args } => match op {
            Op::IntAdd | Op::RealAdd => {
                let mut acc: AtomPoly = Vec::new();
                for &arg in args {
                    let part = expand_inner(arena, arg, atoms, steps, depth + 1)?;
                    acc = add(acc, part)?;
                }
                Some(acc)
            }
            Op::IntSub | Op::RealSub => {
                let mut iter = args.iter();
                let &first = iter.next()?;
                let mut acc = expand_inner(arena, first, atoms, steps, depth + 1)?;
                for &arg in iter {
                    let part = expand_inner(arena, arg, atoms, steps, depth + 1)?;
                    acc = add(acc, negate(part)?)?;
                }
                Some(acc)
            }
            Op::IntNeg | Op::RealNeg => {
                let [inner] = &**args else { return None };
                negate(expand_inner(arena, *inner, atoms, steps, depth + 1)?)
            }
            Op::IntMul | Op::RealMul => {
                let mut acc = constant(Rational::integer(1));
                for &arg in args {
                    let part = expand_inner(arena, arg, atoms, steps, depth + 1)?;
                    acc = multiply(&acc, &part)?;
                }
                Some(acc)
            }
            // `/` by a nonzero rational literal is exact scaling. Every other
            // divisor — including a literal zero, whose SMT-LIB value is
            // unspecified — falls through to the opaque-atom case below.
            Op::RealDiv if divisors_are_nonzero_literals(arena, args) => {
                let mut iter = args.iter();
                let &first = iter.next()?;
                let mut acc = expand_inner(arena, first, atoms, steps, depth + 1)?;
                for &arg in iter {
                    let TermNode::RealConst(value) = arena.node(arg) else {
                        return None;
                    };
                    let scale = Rational::checked_new(value.denominator(), value.numerator())?;
                    acc = multiply(&acc, &constant(scale))?;
                }
                Some(acc)
            }
            _ => atom(arena, term, atoms),
        },
        _ => atom(arena, term, atoms),
    }
}

/// True when every divisor operand (all but the first) is a nonzero real literal.
fn divisors_are_nonzero_literals(arena: &TermArena, args: &[TermId]) -> bool {
    args.len() >= 2
        && args[1..]
            .iter()
            .all(|&arg| matches!(arena.node(arg), TermNode::RealConst(v) if !v.is_zero()))
}

/// Interns `term` as an opaque atom; only `Int`/`Real`-sorted terms qualify, so
/// a stray `Bool`/`BitVec` operand declines instead of being abstracted.
fn atom(arena: &TermArena, term: TermId, atoms: &mut BTreeSet<TermId>) -> Option<AtomPoly> {
    if !matches!(arena.sort_of(term), Sort::Int | Sort::Real) {
        return None;
    }
    if !atoms.contains(&term) {
        if atoms.len() >= MAX_ATOMS {
            return None;
        }
        atoms.insert(term);
    }
    Some(vec![(vec![(term, 1)], Rational::integer(1))])
}

fn constant(value: Rational) -> AtomPoly {
    if value.is_zero() {
        Vec::new()
    } else {
        vec![(Vec::new(), value)]
    }
}

fn add(mut left: AtomPoly, right: AtomPoly) -> Option<AtomPoly> {
    if left.len().checked_add(right.len())? > MAX_MONOMIALS.saturating_mul(2) {
        return None;
    }
    left.extend(right);
    let merged = canonicalize(left)?;
    (merged.len() <= MAX_MONOMIALS).then_some(merged)
}

fn negate(poly: AtomPoly) -> Option<AtomPoly> {
    poly.into_iter()
        .map(|(mono, coeff)| Some((mono, coeff.checked_neg()?)))
        .collect()
}

fn multiply(left: &AtomPoly, right: &AtomPoly) -> Option<AtomPoly> {
    if left.len().checked_mul(right.len())? > MAX_MONOMIALS.saturating_mul(2) {
        return None;
    }
    let mut out: AtomPoly = Vec::with_capacity(left.len().saturating_mul(right.len()));
    for (left_mono, left_coeff) in left {
        for (right_mono, right_coeff) in right {
            let coeff = left_coeff.checked_mul(*right_coeff)?;
            if coeff.is_zero() {
                continue;
            }
            out.push((mono_mul(left_mono, right_mono)?, coeff));
        }
    }
    let merged = canonicalize(out)?;
    (merged.len() <= MAX_MONOMIALS).then_some(merged)
}

fn mono_mul(left: &AtomMonomial, right: &AtomMonomial) -> Option<AtomMonomial> {
    let mut out = left.clone();
    for (term, exp) in right {
        match out.iter_mut().find(|(other, _)| other == term) {
            Some(slot) => slot.1 = slot.1.checked_add(*exp)?,
            None => out.push((*term, *exp)),
        }
    }
    out.sort_unstable();
    Some(out)
}

/// Sorts monomials, merges like terms, and drops zero coefficients — the single
/// canonicalization step that makes `AtomPoly` equality mean polynomial equality.
///
/// `None` on a coefficient sum outside the exact `i128` rational range: a form
/// that cannot be canonicalized is never returned as if it were canonical.
fn canonicalize(mut poly: AtomPoly) -> Option<AtomPoly> {
    for (mono, _) in &mut poly {
        mono.retain(|(_, exp)| *exp > 0);
        mono.sort_unstable();
    }
    poly.sort_by(|left, right| left.0.cmp(&right.0));
    let mut out: AtomPoly = Vec::with_capacity(poly.len());
    for (mono, coeff) in poly {
        match out.last_mut() {
            Some((last_mono, last_coeff)) if *last_mono == mono => {
                *last_coeff = last_coeff.checked_add(coeff)?;
            }
            _ => out.push((mono, coeff)),
        }
    }
    out.retain(|(_, coeff)| !coeff.is_zero());
    Some(out)
}

// --- conjunct scanning -------------------------------------------------------

/// The top-level conjuncts of `assertions`: each assertion, with `and` spines of
/// any arity flattened. Every returned term is asserted **true**, which is what
/// makes a bound read off one of them a usable fact.
#[must_use]
pub fn top_conjuncts(arena: &TermArena, assertions: &[TermId]) -> Vec<TermId> {
    let mut out = Vec::new();
    let mut work: Vec<TermId> = assertions.iter().rev().copied().collect();
    let mut budget = MAX_STEPS;
    while let Some(term) = work.pop() {
        let Some(next) = budget.checked_sub(1) else {
            break;
        };
        budget = next;
        match arena.node(term) {
            TermNode::App {
                op: Op::BoolAnd,
                args,
            } => work.extend(args.iter().rev().copied()),
            _ => out.push(term),
        }
    }
    out
}

/// Matches `not (= lhs rhs)`.
#[must_use]
pub fn match_disequality(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [inner] = &**args else { return None };
    match_equality(arena, *inner)
}

/// Matches `(= lhs rhs)`.
#[must_use]
pub fn match_equality(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return None;
    };
    let [lhs, rhs] = &**args else { return None };
    Some((*lhs, *rhs))
}

// --- certificate checks ------------------------------------------------------

/// Re-verifies a [`CasIdentityCertificate`] against the original assertions.
///
/// Returns `true` only when the cited assertion really is a top-level conjunct
/// asserting `not (= lhs rhs)` **and** this module's own expansion proves the
/// two sides equal as polynomials in their opaque atoms — which makes the
/// disequality unsatisfiable, hence the whole assertion list `unsat`.
#[must_use]
pub fn check_cas_identity_certificate(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &CasIdentityCertificate,
) -> bool {
    if !top_conjuncts(arena, assertions).contains(&cert.assertion) {
        return false;
    }
    let Some((lhs, rhs)) = match_disequality(arena, cert.assertion) else {
        return false;
    };
    if (lhs, rhs) != (cert.lhs, cert.rhs) {
        return false;
    }
    let mut atoms = BTreeSet::new();
    let (Some(left), Some(right)) = (
        expand(arena, lhs, &mut atoms),
        expand(arena, rhs, &mut atoms),
    ) else {
        return false;
    };
    if left != right {
        return false;
    }
    // The verdict already follows from `left == right`. This comparison pins the
    // artifact an auditor reads to the artifact the checker verified.
    cert.normal_form == left
}

/// Re-verifies a [`CasIntUnitsCertificate`] against the original assertions.
///
/// Every number in the certificate is re-derived here: the equation is
/// re-expanded, its `k·m = c` shape re-established, and each cited bound
/// re-read off the conjunct that is claimed to assert it.
#[must_use]
#[allow(
    clippy::too_many_lines,
    reason = "one function per refutation kind would split the shared re-derivation \
              of the k·m = c shape, which is exactly the part that must not drift"
)]
pub fn check_cas_int_units_certificate(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &CasIntUnitsCertificate,
) -> bool {
    let conjuncts = top_conjuncts(arena, assertions);
    if !conjuncts.contains(&cert.equation) {
        return false;
    }
    let Some((lhs, rhs)) = match_equality(arena, cert.equation) else {
        return false;
    };
    if arena.sort_of(lhs) != Sort::Int || arena.sort_of(rhs) != Sort::Int {
        return false;
    }
    let mut atoms = BTreeSet::new();
    let (Some(left), Some(right)) = (
        expand(arena, lhs, &mut atoms),
        expand(arena, rhs, &mut atoms),
    ) else {
        return false;
    };
    let Some(negated) = negate(right) else {
        return false;
    };
    let Some(difference) = add(left, negated) else {
        return false;
    };
    // `difference = 0` must have the shape `k·m − c` with `m` a single
    // non-constant monomial, i.e. the equation asserts `k·m = c`.
    let Some((monomial, coefficient, constant_value)) = split_single_monomial(&difference) else {
        return false;
    };
    if coefficient == 0 {
        return false;
    }
    let Some(target) = constant_value.checked_neg() else {
        return false;
    };
    if cert.monomial != monomial || (cert.coefficient, cert.constant) != (coefficient, target) {
        return false;
    }
    // Every refutation below argues over ℤ ("a factor of a nonzero integer
    // divides it", "a product is zero only if a factor is"), so every atom of
    // the monomial must be integer-valued. It always is — an `Int`-sorted
    // expression's `+ − ×` leaves are `Int`-sorted — but the argument is stated
    // rather than assumed.
    if !monomial
        .iter()
        .all(|(atom, _)| arena.sort_of(*atom) == Sort::Int)
    {
        return false;
    }

    // `checked_rem`/`checked_div` throughout: `i128::MIN / -1` and
    // `i128::MIN % -1` both panic, and a pathological coefficient must make the
    // checker *decline*, never abort the process.
    match cert.kind {
        // `k·m = c` with `k ∤ c`: `m` is an integer (a product of integer-sorted
        // atoms), so `k·m` ranges over multiples of `k` only, and `c` is not one.
        CasIntUnitsKind::CoefficientNonDivisor => {
            target.checked_rem(coefficient).is_some_and(|rem| rem != 0)
        }
        // `k·m = c ≠ 0` forces every atom `a` of `m` to satisfy `|a| ≥ 1` (a zero
        // atom makes the product zero) and hence `|a| ≤ |a|^e ≤ |c/k|` (each
        // factor of a nonzero integer divides it). A cited bound that puts an
        // atom outside `[−|c/k|, |c/k|]` refutes the equation.
        CasIntUnitsKind::DivisorBound => {
            if target == 0 || target.checked_rem(coefficient) != Some(0) {
                return false;
            }
            let Some(limit) = target.checked_div(coefficient).and_then(i128::checked_abs) else {
                return false;
            };
            cert.bounds.iter().any(|bound| {
                monomial.iter().any(|(atom, _)| *atom == bound.atom)
                    && bound_is_asserted(arena, &conjuncts, bound)
                    && (bound.lower.is_some_and(|lower| lower > limit)
                        || bound.upper.is_some_and(|upper| upper < -limit))
            })
        }
        // `k·m = 0` with `k ≠ 0` forces some atom of `m` to be zero. When every
        // atom is bounded away from zero the equation has no solution.
        CasIntUnitsKind::ZeroProduct => {
            if target != 0 {
                return false;
            }
            monomial.iter().all(|(atom, _)| {
                cert.bounds.iter().any(|bound| {
                    bound.atom == *atom
                        && bound_is_asserted(arena, &conjuncts, bound)
                        && (bound.lower.is_some_and(|lower| lower >= 1)
                            || bound.upper.is_some_and(|upper| upper <= -1))
                })
            })
        }
    }
}

/// Splits `poly` into `(monomial, coefficient, constant)` when it is exactly one
/// non-constant monomial plus an optional constant term, both with integer
/// coefficients.
fn split_single_monomial(poly: &AtomPoly) -> Option<(AtomMonomial, i128, i128)> {
    let mut monomial: Option<(AtomMonomial, i128)> = None;
    let mut constant_value = 0i128;
    for (mono, coeff) in poly {
        if !coeff.is_integer() {
            return None;
        }
        let value = coeff.numerator();
        if mono.is_empty() {
            constant_value = value;
        } else if monomial.is_some() {
            return None;
        } else {
            monomial = Some((mono.clone(), value));
        }
    }
    let (mono, coeff) = monomial?;
    Some((mono, coeff, constant_value))
}

/// True when the conjunct the certificate names is really asserted and really
/// entails the bound the certificate claims.
fn bound_is_asserted(arena: &TermArena, conjuncts: &[TermId], bound: &CasIntBound) -> bool {
    if !conjuncts.contains(&bound.source) {
        return false;
    }
    if bound.lower.is_none() && bound.upper.is_none() {
        return false;
    }
    let (lower, upper) = derive_bound(arena, bound.source, bound.atom);
    // A claimed lower bound is valid when the source proves an at-least-as-large
    // one; symmetrically for the upper bound.
    let lower_ok = bound
        .lower
        .is_none_or(|claim| lower.is_some_and(|derived| derived >= claim));
    let upper_ok = bound
        .upper
        .is_none_or(|claim| upper.is_some_and(|derived| derived <= claim));
    lower_ok && upper_ok
}

/// The `(lower, upper)` integer bounds on `subject` that the asserted conjunct
/// `source` entails directly, if any.
///
/// Only literal comparisons whose non-constant side is *syntactically* `subject`
/// are read. `source` is a top-level conjunct, hence asserted true, so what this
/// returns is a fact about every model of the query.
#[must_use]
pub fn derive_bound(
    arena: &TermArena,
    source: TermId,
    subject: TermId,
) -> (Option<i128>, Option<i128>) {
    let TermNode::App { op, args } = arena.node(source) else {
        return (None, None);
    };
    let [left, right] = &**args else {
        return (None, None);
    };
    // Orient so `subject` is the left operand; `flipped` records that the
    // comparison must then be read in the mirrored direction.
    let (constant_side, flipped) = if *left == subject {
        (*right, false)
    } else if *right == subject {
        (*left, true)
    } else {
        return (None, None);
    };
    let TermNode::IntConst(bound) = arena.node(constant_side) else {
        return (None, None);
    };
    let bound = *bound;
    match (op, flipped) {
        // `subject ≥ n` / `n ≤ subject`
        (Op::IntGe, false) | (Op::IntLe, true) => (Some(bound), None),
        // `subject > n` / `n < subject`
        (Op::IntGt, false) | (Op::IntLt, true) => (bound.checked_add(1), None),
        // `subject ≤ n` / `n ≥ subject`
        (Op::IntLe, false) | (Op::IntGe, true) => (None, Some(bound)),
        // `subject < n` / `n > subject`
        (Op::IntLt, false) | (Op::IntGt, true) => (None, bound.checked_sub(1)),
        (Op::Eq, _) => (Some(bound), Some(bound)),
        _ => (None, None),
    }
}

#[cfg(test)]
mod tests {
    use axeyum_ir::{Rational, Sort, TermArena};

    use super::{derive_bound, expand, top_conjuncts};
    use std::collections::BTreeSet;

    /// `(a+b)²` and `a² + 2ab + b²` must expand to the same canonical form —
    /// this is the whole basis of the identity refutation, checked without
    /// `MvPoly` anywhere in the loop.
    #[test]
    fn binomial_square_expands_to_the_same_canonical_form() {
        let mut arena = TermArena::new();
        let a = arena.int_var("a").unwrap();
        let b = arena.int_var("b").unwrap();
        let sum = arena.int_add(a, b).unwrap();
        let squared = arena.int_mul(sum, sum).unwrap();
        let aa = arena.int_mul(a, a).unwrap();
        let bb = arena.int_mul(b, b).unwrap();
        let ab = arena.int_mul(a, b).unwrap();
        let two = arena.int_const(2);
        let two_ab = arena.int_mul(two, ab).unwrap();
        let expanded = {
            let partial = arena.int_add(aa, two_ab).unwrap();
            arena.int_add(partial, bb).unwrap()
        };

        let mut atoms = BTreeSet::new();
        let left = expand(&arena, squared, &mut atoms).expect("expand lhs");
        let right = expand(&arena, expanded, &mut atoms).expect("expand rhs");
        assert_eq!(left, right);
        assert_eq!(left.len(), 3, "{left:?}");
        assert_eq!(atoms.len(), 2);
    }

    /// A near miss must NOT collapse: the expander is only useful if it
    /// distinguishes `2ab` from `3ab`.
    #[test]
    fn near_miss_does_not_expand_to_the_same_form() {
        let mut arena = TermArena::new();
        let a = arena.int_var("a").unwrap();
        let b = arena.int_var("b").unwrap();
        let sum = arena.int_add(a, b).unwrap();
        let squared = arena.int_mul(sum, sum).unwrap();
        let aa = arena.int_mul(a, a).unwrap();
        let bb = arena.int_mul(b, b).unwrap();
        let ab = arena.int_mul(a, b).unwrap();
        let three = arena.int_const(3);
        let three_ab = arena.int_mul(three, ab).unwrap();
        let expanded = {
            let partial = arena.int_add(aa, three_ab).unwrap();
            arena.int_add(partial, bb).unwrap()
        };

        let mut atoms = BTreeSet::new();
        let left = expand(&arena, squared, &mut atoms).expect("expand lhs");
        let right = expand(&arena, expanded, &mut atoms).expect("expand rhs");
        assert_ne!(left, right);
    }

    /// A `div` term is opaque: `3·(div x 3)` must not expand to `x`.
    #[test]
    fn integer_division_is_an_opaque_atom() {
        let mut arena = TermArena::new();
        let x = arena.int_var("x").unwrap();
        let three = arena.int_const(3);
        let quotient = arena.int_div(x, three).unwrap();
        let scaled = arena.int_mul(three, quotient).unwrap();

        let mut atoms = BTreeSet::new();
        let left = expand(&arena, scaled, &mut atoms).expect("expand");
        let right = expand(&arena, x, &mut atoms).expect("expand");
        assert_ne!(left, right);
        assert_eq!(atoms.len(), 2, "the quotient and `x` are separate atoms");
    }

    /// Real division by a nonzero literal folds; by a variable it does not.
    #[test]
    fn real_division_folds_only_for_nonzero_literals() {
        let mut arena = TermArena::new();
        let a = arena.real_var("a").unwrap();
        let b = arena.real_var("b").unwrap();
        let two = arena.real_const(Rational::integer(2));
        let zero = arena.real_const(Rational::zero());
        let half = arena.real_div(a, two).unwrap();
        let by_var = arena.real_div(a, b).unwrap();
        let by_zero = arena.real_div(a, zero).unwrap();

        let mut atoms = BTreeSet::new();
        let folded = expand(&arena, half, &mut atoms).expect("expand a/2");
        assert_eq!(folded.len(), 1);
        assert_eq!(folded[0].1, Rational::new(1, 2));
        assert_eq!(atoms.len(), 1, "only `a` became an atom");

        let opaque = expand(&arena, by_var, &mut atoms).expect("expand a/b");
        assert_eq!(opaque[0].0.len(), 1);
        assert!(atoms.contains(&by_var), "a/b is opaque");

        expand(&arena, by_zero, &mut atoms).expect("expand a/0");
        assert!(atoms.contains(&by_zero), "a/0 is opaque, never folded");
    }

    /// A bit-vector term is outside the fragment and outside the atom rule.
    #[test]
    fn bitvector_terms_decline() {
        let mut arena = TermArena::new();
        let symbol = arena.declare("x", Sort::BitVec(8)).unwrap();
        let x = arena.var(symbol);
        let mut atoms = BTreeSet::new();
        assert!(expand(&arena, x, &mut atoms).is_none());
    }

    #[test]
    fn bounds_are_read_in_both_orientations() {
        let mut arena = TermArena::new();
        let a = arena.int_var("a").unwrap();
        let two = arena.int_const(2);
        let ge = arena.int_ge(a, two).unwrap();
        let le_flipped = arena.int_le(two, a).unwrap();
        let le = arena.int_le(a, two).unwrap();
        let eq = arena.eq(a, two).unwrap();

        assert_eq!(derive_bound(&arena, ge, a), (Some(2), None));
        assert_eq!(derive_bound(&arena, le_flipped, a), (Some(2), None));
        assert_eq!(derive_bound(&arena, le, a), (None, Some(2)));
        assert_eq!(derive_bound(&arena, eq, a), (Some(2), Some(2)));
        // A bound on a different term says nothing about `a`.
        let b = arena.int_var("b").unwrap();
        assert_eq!(derive_bound(&arena, ge, b), (None, None));
    }

    #[test]
    fn conjunct_collection_flattens_and_spines() {
        let mut arena = TermArena::new();
        let a = arena.int_var("a").unwrap();
        let b = arena.int_var("b").unwrap();
        let one = arena.int_const(1);
        let left = arena.int_ge(a, one).unwrap();
        let right = arena.int_ge(b, one).unwrap();
        let conjunction = arena.and(left, right).unwrap();
        assert_eq!(top_conjuncts(&arena, &[conjunction]), vec![left, right]);
    }
}
