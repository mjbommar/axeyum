//! Gröbner bases over ℚ via `Buchberger`'s algorithm.
//!
//! This module adds ideal-theoretic reasoning on top of the sparse multivariate
//! polynomial [`MvPoly`]: given a finite set of generators
//! it computes a **Gröbner basis** of the ideal they span, reduces a polynomial
//! to its normal form modulo a basis, and decides **ideal membership**. It is the
//! multivariate analogue of the univariate `gcd`/`divrem` machinery the crate
//! already has: where `gcd` certifies "is this a common factor", a Gröbner basis
//! certifies "is this in the ideal".
//!
//! # Monomial order
//!
//! Everything here uses the **pure lexicographic order** (`lex`) that
//! [`MvPoly`] itself uses: variables are ranked
//! alphabetically ascending with the alphabetically-*first* variable the most
//! significant, so monomial `a > b` iff at the first variable (scanning
//! most-significant-first) where their exponents differ, `a` has the larger
//! exponent. `lex` is a well-order on the monomials in finitely many variables,
//! which is exactly what makes multivariate division and the reduction loop
//! terminate.
//!
//! # Algorithm and references
//!
//! The construction is textbook `Buchberger` (1965): repeatedly form the
//! S-polynomial of each pair in the current basis, reduce it modulo the basis,
//! and adjoin any nonzero remainder, iterating to a fixed point; then trim to the
//! unique **reduced** Gröbner basis. Correctness (`Buchberger`'s criterion — a
//! basis is Gröbner iff every S-polynomial reduces to zero) and termination
//! (`Dickson`'s lemma — the ascending chain of leading-term ideals stabilises)
//! follow Cox, Little, and O'Shea, *Ideals, Varieties, and Algorithms*, chapter 2
//! (§2.6 the division algorithm, §2.7 `Dickson`'s lemma, §2.9 `Buchberger`'s
//! criterion and algorithm, §2.10 reduced bases).
//!
//! # Building on [`MvPoly`]
//!
//! All ring arithmetic (add/sub/mul, exact overflow reporting) is delegated to
//! [`MvPoly`]. `MvPoly` does not publicly expose its
//! leading term under `lex`, an iterator over its terms, or a monomial-level
//! `lcm`/division, so this module reconstructs a polynomial's terms through the
//! public [`MvPoly::to_cas_expr`](crate::mvpoly::MvPoly::to_cas_expr) rendering
//! and re-implements the small monomial helpers (`lcm`, divisibility, quotient,
//! `lex` comparison) locally — none of which touch `mvpoly.rs`.
//!
//! # Overflow and termination guard
//!
//! Every fallible step returns `None` on the underlying `i128`/`u32` overflow
//! rather than panicking. `Dickson`'s lemma guarantees termination, but as a
//! defensive guard against a pathological input (or a bug) the loops carry a
//! generous iteration cap and return `None` if it is ever exceeded — an honest
//! "gave up" rather than a hang. No `unsafe`, no `unwrap`/`expect` on fallible
//! paths.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

use axeyum_ir::Rational;

use crate::CasExpr;
use crate::mvpoly::{Monomial, MvPoly};

/// A monomial's exponent map: variable name → exponent, every exponent `> 0`.
///
/// The empty map is the constant monomial `1`. This local representation exists
/// because [`Monomial`] exposes no way to enumerate the variables it mentions,
/// which the leading-term selection and monomial `lcm` both need.
type Exponents = BTreeMap<String, u32>;

/// Defensive cap on reduction steps for a single normal-form computation.
///
/// Each step strictly lowers the `lex`-leading monomial of the running dividend,
/// so `lex` being a well-order already guarantees termination; this bound only
/// exists so a bug or pathological input yields `None` instead of a hang.
const MAX_REDUCTION_STEPS: u64 = 1_000_000;

/// Defensive cap on the number of S-polynomial pairs processed by `Buchberger`'s
/// main loop. `Dickson`'s lemma guarantees the basis stops growing; exceeding
/// this bound returns `None`.
const MAX_PAIR_ITERATIONS: u64 = 5_000_000;

/// Defensive cap on the intermediate basis size during `Buchberger`'s algorithm.
const MAX_BASIS_SIZE: usize = 100_000;

// --- Monomial helpers (local; operate on `Exponents`) -----------------------

/// The unit map `{ 1 }` used as the identity for monomial products.
fn unit_map() -> BTreeMap<Exponents, Rational> {
    let mut map = BTreeMap::new();
    map.insert(Exponents::new(), Rational::integer(1));
    map
}

/// Compare two monomials under the pure lexicographic order (alphabetically-first
/// variable most significant), matching [`MvPoly`](crate::mvpoly::MvPoly)'s order.
fn lex_cmp(left: &Exponents, right: &Exponents) -> Ordering {
    let mut vars: BTreeSet<&str> = BTreeSet::new();
    vars.extend(left.keys().map(String::as_str));
    vars.extend(right.keys().map(String::as_str));
    for var in vars {
        let mine = left.get(var).copied().unwrap_or(0);
        let theirs = right.get(var).copied().unwrap_or(0);
        match mine.cmp(&theirs) {
            Ordering::Equal => {}
            unequal => return unequal,
        }
    }
    Ordering::Equal
}

/// The least common multiple of two monomials (per variable, the larger
/// exponent).
fn monomial_lcm(left: &Exponents, right: &Exponents) -> Exponents {
    let mut result = left.clone();
    for (var, exp) in right {
        let slot = result.entry(var.clone()).or_insert(0);
        *slot = (*slot).max(*exp);
    }
    result
}

/// Returns `true` iff `divisor` divides `target` (every divisor exponent is `≤`
/// the corresponding target exponent).
fn monomial_divides(divisor: &Exponents, target: &Exponents) -> bool {
    divisor
        .iter()
        .all(|(var, exp)| target.get(var).copied().unwrap_or(0) >= *exp)
}

/// The quotient monomial `target / divisor`, assuming `divisor` divides `target`
/// (guaranteed at every call site). Saturating subtraction keeps it panic-free.
fn monomial_quotient(target: &Exponents, divisor: &Exponents) -> Exponents {
    let mut result = Exponents::new();
    for (var, exp) in target {
        let reduced = exp.saturating_sub(divisor.get(var).copied().unwrap_or(0));
        if reduced > 0 {
            result.insert(var.clone(), reduced);
        }
    }
    result
}

// --- Term extraction (via the public `MvPoly` surface) ----------------------

/// Expand a [`CasExpr`] over the polynomial fragment into a canonical map from
/// [`Exponents`] to nonzero [`Rational`] coefficient, or `None` on a
/// non-polynomial head (`Div`/`Unary`) or `i128`/`u32` overflow.
///
/// This is the workaround for [`MvPoly`](crate::mvpoly::MvPoly) not exposing a
/// term iterator: applied to
/// [`MvPoly::to_cas_expr`](crate::mvpoly::MvPoly::to_cas_expr) it recovers the
/// polynomial's terms in a form whose per-monomial variables are inspectable.
fn expand(expr: &CasExpr) -> Option<BTreeMap<Exponents, Rational>> {
    match expr {
        CasExpr::Const(value) => {
            let mut terms = BTreeMap::new();
            if !value.is_zero() {
                terms.insert(Exponents::new(), *value);
            }
            Some(terms)
        }
        CasExpr::Var(name) => {
            let mut mono = Exponents::new();
            mono.insert(name.clone(), 1);
            let mut terms = BTreeMap::new();
            terms.insert(mono, Rational::integer(1));
            Some(terms)
        }
        CasExpr::Add(parts) => {
            let mut acc = BTreeMap::new();
            for part in parts {
                let expanded = expand(part)?;
                acc = add_maps(&acc, &expanded)?;
            }
            Some(acc)
        }
        CasExpr::Mul(factors) => {
            let mut acc = unit_map();
            for factor in factors {
                let expanded = expand(factor)?;
                acc = mul_maps(&acc, &expanded)?;
            }
            Some(acc)
        }
        CasExpr::Neg(inner) => {
            let expanded = expand(inner)?;
            let mut acc = BTreeMap::new();
            for (mono, coeff) in expanded {
                acc.insert(mono, coeff.checked_neg()?);
            }
            Some(acc)
        }
        CasExpr::Pow(base, exp) => {
            let expanded = expand(base)?;
            let mut acc = unit_map();
            for _ in 0..*exp {
                acc = mul_maps(&acc, &expanded)?;
            }
            Some(acc)
        }
        CasExpr::Div(..) | CasExpr::Unary(..) => None,
    }
}

/// Sum of two canonical term maps, dropping cancelled monomials. `None` on
/// coefficient overflow.
fn add_maps(
    left: &BTreeMap<Exponents, Rational>,
    right: &BTreeMap<Exponents, Rational>,
) -> Option<BTreeMap<Exponents, Rational>> {
    let mut out = left.clone();
    for (mono, coeff) in right {
        let combined = match out.get(mono).copied() {
            Some(existing) => existing.checked_add(*coeff)?,
            None => *coeff,
        };
        if combined.is_zero() {
            out.remove(mono);
        } else {
            out.insert(mono.clone(), combined);
        }
    }
    Some(out)
}

/// Product of two canonical term maps, dropping cancelled monomials. `None` on
/// `i128`/`u32` overflow.
fn mul_maps(
    left: &BTreeMap<Exponents, Rational>,
    right: &BTreeMap<Exponents, Rational>,
) -> Option<BTreeMap<Exponents, Rational>> {
    let mut out: BTreeMap<Exponents, Rational> = BTreeMap::new();
    for (left_mono, left_coeff) in left {
        for (right_mono, right_coeff) in right {
            let mut mono = left_mono.clone();
            for (var, exp) in right_mono {
                let slot = mono.entry(var.clone()).or_insert(0);
                *slot = slot.checked_add(*exp)?;
            }
            let coeff = left_coeff.checked_mul(*right_coeff)?;
            let combined = match out.get(&mono).copied() {
                Some(existing) => existing.checked_add(coeff)?,
                None => coeff,
            };
            if combined.is_zero() {
                out.remove(&mono);
            } else {
                out.insert(mono, combined);
            }
        }
    }
    Some(out)
}

/// The `lex`-leading `(monomial, coefficient)` of `poly`, or `None` if `poly` is
/// the zero polynomial (or on overflow while recovering its terms).
fn leading_term(poly: &MvPoly) -> Option<(Exponents, Rational)> {
    let terms = expand(&poly.to_cas_expr())?;
    terms
        .into_iter()
        .max_by(|left, right| lex_cmp(&left.0, &right.0))
}

/// Build the single-term polynomial `coeff · monomial` as an
/// [`MvPoly`](crate::mvpoly::MvPoly). `None` on overflow.
fn single_term(exponents: &Exponents, coeff: Rational) -> Option<MvPoly> {
    let factors: Vec<(&str, u32)> = exponents
        .iter()
        .map(|(var, exp)| (var.as_str(), *exp))
        .collect();
    MvPoly::from_terms([(Monomial::from_powers(&factors), coeff)])
}

/// `poly` rescaled so its `lex`-leading coefficient is `1`. `None` on overflow or
/// if `poly` is zero (which has no leading coefficient).
fn make_monic(poly: &MvPoly) -> Option<MvPoly> {
    let (_, leading_coeff) = leading_term(poly)?;
    let inverse = Rational::integer(1).checked_div(leading_coeff)?;
    poly.mul(&MvPoly::constant(inverse))
}

// --- S-polynomials ----------------------------------------------------------

/// The S-polynomial of `first` and `second`:
/// `S = (lcm / lt(first)) · first − (lcm / lt(second)) · second`, where `lcm` is
/// the least common multiple of the two leading monomials and `lt` denotes the
/// leading term (coefficient included). By construction the shared leading term
/// `lcm` cancels, isolating the lower-order interaction `Buchberger`'s criterion
/// tests. `None` if either input is zero, or on overflow.
fn s_polynomial(first: &MvPoly, second: &MvPoly) -> Option<MvPoly> {
    let (first_mono, first_coeff) = leading_term(first)?;
    let (second_mono, second_coeff) = leading_term(second)?;
    let lcm = monomial_lcm(&first_mono, &second_mono);
    let first_factor = single_term(
        &monomial_quotient(&lcm, &first_mono),
        Rational::integer(1).checked_div(first_coeff)?,
    )?;
    let second_factor = single_term(
        &monomial_quotient(&lcm, &second_mono),
        Rational::integer(1).checked_div(second_coeff)?,
    )?;
    first_factor.mul(first)?.sub(&second_factor.mul(second)?)
}

// --- Public API -------------------------------------------------------------

/// Reduce `poly` to its **normal form** (multivariate remainder) modulo `basis`
/// under the `lex` monomial order.
///
/// This is the multivariate division algorithm of Cox–Little–O'Shea §2.3: while
/// the running dividend is nonzero, if some nonzero element of `basis` has a
/// leading monomial dividing the dividend's `lex`-leading monomial, cancel that
/// leading term by subtracting the appropriate multiple of that element;
/// otherwise move the leading term into the remainder. Each step strictly lowers
/// the dividend's `lex`-leading monomial, so the loop terminates (`lex` is a
/// well-order).
///
/// The remainder has no monomial divisible by any basis leading monomial. When
/// `basis` is a Gröbner basis this normal form is unique, so `reduce` returning
/// the zero polynomial is exactly ideal membership. Zero elements of `basis` are
/// ignored. Returns `None` on `i128`/`u32` overflow or if the defensive step cap
/// is exceeded.
pub fn reduce(poly: &MvPoly, basis: &[MvPoly]) -> Option<MvPoly> {
    // Precompute each nonzero divisor's leading term once.
    let leads: Vec<(&MvPoly, Exponents, Rational)> = basis
        .iter()
        .filter(|element| !element.is_zero())
        .map(|element| {
            let (mono, coeff) = leading_term(element)?;
            Some((element, mono, coeff))
        })
        .collect::<Option<Vec<_>>>()?;

    let mut remainder = MvPoly::zero();
    let mut current = poly.clone();
    let mut steps: u64 = 0;
    while !current.is_zero() {
        steps += 1;
        if steps > MAX_REDUCTION_STEPS {
            return None;
        }
        let (lead_mono, lead_coeff) = leading_term(&current)?;
        let mut cancelled = false;
        for (element, element_mono, element_coeff) in &leads {
            if monomial_divides(element_mono, &lead_mono) {
                let quotient_mono = monomial_quotient(&lead_mono, element_mono);
                let quotient_coeff = lead_coeff.checked_div(*element_coeff)?;
                let factor = single_term(&quotient_mono, quotient_coeff)?;
                current = current.sub(&factor.mul(element)?)?;
                cancelled = true;
                break;
            }
        }
        if !cancelled {
            let lead = single_term(&lead_mono, lead_coeff)?;
            remainder = remainder.add(&lead)?;
            current = current.sub(&lead)?;
        }
    }
    Some(remainder)
}

/// A **Gröbner basis**, under the `lex` order, of the ideal generated by
/// `generators`, computed by `Buchberger`'s algorithm and trimmed to the unique
/// **reduced** basis (every leading coefficient `1`, and no element's leading
/// monomial divides any term of another).
///
/// The main loop maintains a work queue of index pairs: for each pair it forms
/// the S-polynomial (see `s_polynomial`), reduces it modulo the current basis
/// (see [`reduce`]), and — if the remainder is nonzero — adjoins it and enqueues
/// its pairings with the existing elements. `Dickson`'s lemma guarantees the
/// basis stops growing, so the queue drains (Cox–Little–O'Shea §2.7, §2.9).
///
/// The empty generator set (or one of only zero polynomials) generates the zero
/// ideal and yields the empty basis. Returns `None` on `i128`/`u32` overflow or
/// if a defensive iteration cap is exceeded.
pub fn groebner_basis(generators: &[MvPoly]) -> Option<Vec<MvPoly>> {
    let mut basis: Vec<MvPoly> = generators
        .iter()
        .filter(|generator| !generator.is_zero())
        .cloned()
        .collect();
    if basis.is_empty() {
        return Some(Vec::new());
    }

    let mut pairs: VecDeque<(usize, usize)> = VecDeque::new();
    for higher in 1..basis.len() {
        for lower in 0..higher {
            pairs.push_back((lower, higher));
        }
    }

    let mut iterations: u64 = 0;
    while let Some((lower, higher)) = pairs.pop_front() {
        iterations += 1;
        if iterations > MAX_PAIR_ITERATIONS {
            return None;
        }
        let s_poly = s_polynomial(&basis[lower], &basis[higher])?;
        let remainder = reduce(&s_poly, &basis)?;
        if !remainder.is_zero() {
            let new_index = basis.len();
            for existing in 0..new_index {
                pairs.push_back((existing, new_index));
            }
            basis.push(remainder);
            if basis.len() > MAX_BASIS_SIZE {
                return None;
            }
        }
    }

    reduced_basis(&basis)
}

/// Decide **ideal membership**: whether `poly` lies in the ideal generated by
/// `basis_or_generators`.
///
/// The generators need not already be a Gröbner basis — one is computed
/// internally with [`groebner_basis`] — because ideal membership is only decided
/// by reduction modulo a *Gröbner* basis: `poly` is in the ideal iff its normal
/// form there is zero (Cox–Little–O'Shea §2.9, the ideal-membership algorithm).
/// Returns `None` on `i128`/`u32` overflow or if an iteration cap is exceeded.
pub fn ideal_contains(basis_or_generators: &[MvPoly], poly: &MvPoly) -> Option<bool> {
    let basis = groebner_basis(basis_or_generators)?;
    Some(reduce(poly, &basis)?.is_zero())
}

/// Trim a Gröbner basis to the unique reduced Gröbner basis: make every element
/// monic, drop elements whose leading monomial is divisible by another's, then
/// replace each survivor by its normal form modulo the others
/// (Cox–Little–O'Shea §2.10). `None` on overflow.
fn reduced_basis(basis: &[MvPoly]) -> Option<Vec<MvPoly>> {
    let mut monic: Vec<MvPoly> = Vec::with_capacity(basis.len());
    for element in basis {
        if element.is_zero() {
            continue;
        }
        monic.push(make_monic(element)?);
    }

    // Minimalize: remove one redundant element at a time (one-at-a-time removal
    // keeps exactly one representative when two share a leading monomial).
    loop {
        let mut redundant: Option<usize> = None;
        for (index, element) in monic.iter().enumerate() {
            let (lead_mono, _) = leading_term(element)?;
            let divisible = monic
                .iter()
                .enumerate()
                .filter(|(other_index, _)| *other_index != index)
                .any(|(_, other)| {
                    leading_term(other)
                        .is_some_and(|(other_mono, _)| monomial_divides(&other_mono, &lead_mono))
                });
            if divisible {
                redundant = Some(index);
                break;
            }
        }
        match redundant {
            Some(index) => {
                monic.remove(index);
            }
            None => break,
        }
    }

    // Inter-reduce: each survivor's leading term is indivisible by the others'
    // (minimality), so reducing modulo the others leaves the leading term — and
    // thus monicity — intact while normalising the lower-order tail.
    let mut reduced = monic;
    let count = reduced.len();
    let mut index = 0;
    while index < count {
        let others: Vec<MvPoly> = reduced
            .iter()
            .enumerate()
            .filter(|(other_index, _)| *other_index != index)
            .map(|(_, element)| element.clone())
            .collect();
        reduced[index] = reduce(&reduced[index], &others)?;
        index += 1;
    }
    Some(reduced)
}

#[cfg(test)]
mod tests {
    use super::{groebner_basis, ideal_contains, reduce, s_polynomial};
    use crate::mvpoly::{Monomial, MvPoly};
    use crate::{ZeroTest, equal};
    use axeyum_ir::Rational;

    /// Integer-rational shorthand.
    fn ri(value: i128) -> Rational {
        Rational::integer(value)
    }

    /// A single-term polynomial from `(variable, exponent)` factors.
    fn term(coeff: i128, factors: &[(&str, u32)]) -> MvPoly {
        MvPoly::from_terms([(Monomial::from_powers(factors), ri(coeff))]).expect("no overflow")
    }

    /// The variable polynomial `x`.
    fn var_x() -> MvPoly {
        MvPoly::var("x")
    }

    /// The variable polynomial `y`.
    fn var_y() -> MvPoly {
        MvPoly::var("y")
    }

    /// `x - c`.
    fn x_minus(c: i128) -> MvPoly {
        var_x().sub(&MvPoly::constant(ri(c))).unwrap()
    }

    /// `y - c`.
    fn y_minus(c: i128) -> MvPoly {
        var_y().sub(&MvPoly::constant(ri(c))).unwrap()
    }

    /// Assert two polynomials are certified equal through the crate's zero-test.
    fn assert_certified_equal(left: &MvPoly, right: &MvPoly) {
        match equal(&left.to_cas_expr(), &right.to_cas_expr()) {
            ZeroTest::Certified { equal: true, .. } => {}
            other => panic!("not certified equal: {other:?}"),
        }
    }

    #[test]
    fn single_polynomial_basis_is_its_monic_self() {
        // 2x^2 - 2  →  reduced Gröbner basis {x^2 - 1}.
        let poly = term(2, &[("x", 2)]).sub(&MvPoly::constant(ri(2))).unwrap();
        let basis = groebner_basis(std::slice::from_ref(&poly)).unwrap();
        assert_eq!(basis.len(), 1);
        let x_squared_minus_one = term(1, &[("x", 2)]).sub(&MvPoly::constant(ri(1))).unwrap();
        assert_eq!(basis[0], x_squared_minus_one);
        // The original generator reduces to zero modulo its own basis.
        assert!(reduce(&poly, &basis).unwrap().is_zero());
    }

    #[test]
    fn ideal_membership_for_x_squared_minus_one_and_x_minus_one() {
        // <x^2 - 1, x - 1> = <x - 1> (since x^2 - 1 = (x + 1)(x - 1)).
        let gens = [
            term(1, &[("x", 2)]).sub(&MvPoly::constant(ri(1))).unwrap(),
            x_minus(1),
        ];

        // The reduced basis collapses to {x - 1}.
        let basis = groebner_basis(&gens).unwrap();
        assert_eq!(basis.len(), 1);
        assert_eq!(basis[0], x_minus(1));

        // Members: x - 1, x^2 - 1, and (x - 1)·(x + 3).
        assert_eq!(ideal_contains(&gens, &x_minus(1)), Some(true));
        assert_eq!(ideal_contains(&gens, &gens[0]), Some(true));
        let multiple = x_minus(1)
            .mul(&var_x().add(&MvPoly::constant(ri(3))).unwrap())
            .unwrap();
        assert_eq!(ideal_contains(&gens, &multiple), Some(true));

        // Non-members: x = (x - 1) + 1 and the unit 1 are not in <x - 1>.
        assert_eq!(ideal_contains(&gens, &var_x()), Some(false));
        assert_eq!(ideal_contains(&gens, &MvPoly::constant(ri(1))), Some(false));
    }

    #[test]
    fn circle_and_diagonal_reduce_generators_and_s_polynomial() {
        // Generators {x^2 + y^2 - 1, x - y}.
        let circle = term(1, &[("x", 2)])
            .add(&term(1, &[("y", 2)]))
            .unwrap()
            .sub(&MvPoly::constant(ri(1)))
            .unwrap();
        let diagonal = var_x().sub(&var_y()).unwrap();
        let gens = [circle.clone(), diagonal.clone()];

        let basis = groebner_basis(&gens).unwrap();
        assert!(!basis.is_empty());

        // Both generators lie in the ideal, so reduce to zero modulo the basis.
        assert!(reduce(&circle, &basis).unwrap().is_zero());
        assert!(reduce(&diagonal, &basis).unwrap().is_zero());
        assert_eq!(ideal_contains(&gens, &circle), Some(true));
        assert_eq!(ideal_contains(&gens, &diagonal), Some(true));

        // The S-polynomial of the generators is in the ideal by construction.
        let s_poly = s_polynomial(&circle, &diagonal).unwrap();
        assert_eq!(ideal_contains(&gens, &s_poly), Some(true));
    }

    #[test]
    fn linear_system_ideal_pins_the_solution() {
        // {x + y - 3, x - y - 1}  ⇒  x = 2, y = 1.
        let first = var_x()
            .add(&var_y())
            .unwrap()
            .sub(&MvPoly::constant(ri(3)))
            .unwrap();
        let second = var_x()
            .sub(&var_y())
            .unwrap()
            .sub(&MvPoly::constant(ri(1)))
            .unwrap();
        let gens = [first, second];

        // The ideal encodes the solution: it contains x - 2 and y - 1.
        assert_eq!(ideal_contains(&gens, &x_minus(2)), Some(true));
        assert_eq!(ideal_contains(&gens, &y_minus(1)), Some(true));
        // But not a shifted, false constraint.
        assert_eq!(ideal_contains(&gens, &x_minus(3)), Some(false));

        // The reduced basis is exactly {x - 2, y - 1} (up to ordering).
        let basis = groebner_basis(&gens).unwrap();
        assert_eq!(basis.len(), 2);
        assert!(basis.contains(&x_minus(2)));
        assert!(basis.contains(&y_minus(1)));
    }

    #[test]
    fn buchberger_classic_example_terminates_and_reduces_generators() {
        // Cox–Little–O'Shea's worked example {x^3 - 2xy, x^2 y - 2y^2 + x}.
        let first = term(1, &[("x", 3)])
            .sub(&term(2, &[("x", 1), ("y", 1)]))
            .unwrap();
        let second = term(1, &[("x", 2), ("y", 1)])
            .sub(&term(2, &[("y", 2)]))
            .unwrap()
            .add(&var_x())
            .unwrap();
        let gens = [first.clone(), second.clone()];

        let basis = groebner_basis(&gens).unwrap();
        assert!(!basis.is_empty());

        // Every input generator reduces to zero modulo the basis.
        assert!(reduce(&first, &basis).unwrap().is_zero());
        assert!(reduce(&second, &basis).unwrap().is_zero());

        // Buchberger's criterion: every S-polynomial of basis pairs reduces to
        // zero modulo the basis.
        for (i, left) in basis.iter().enumerate() {
            for right in &basis[i + 1..] {
                let s_poly = s_polynomial(left, right).unwrap();
                assert!(reduce(&s_poly, &basis).unwrap().is_zero());
            }
        }
    }

    #[test]
    fn reduce_of_an_ideal_multiple_is_zero() {
        // (x - 1)·(x + 5) reduces to zero modulo {x - 1}.
        let multiple = x_minus(1)
            .mul(&var_x().add(&MvPoly::constant(ri(5))).unwrap())
            .unwrap();
        let remainder = reduce(&multiple, std::slice::from_ref(&x_minus(1))).unwrap();
        assert!(remainder.is_zero());
    }

    #[test]
    fn reduced_basis_certifies_generator_membership_via_recombination() {
        // A cross-check that the certified zero-test agrees with reduction.
        let gens = [
            term(1, &[("x", 2)]).sub(&var_y()).unwrap(), // x^2 - y
            term(1, &[("y", 2)]).sub(&var_x()).unwrap(), // y^2 - x
        ];
        let basis = groebner_basis(&gens).unwrap();
        for generator in &gens {
            assert!(reduce(generator, &basis).unwrap().is_zero());
            assert_eq!(ideal_contains(&gens, generator), Some(true));
        }
        // A basis element reduces to itself's normal form (zero difference).
        let zero = reduce(&basis[0], &basis).unwrap();
        assert_certified_equal(&zero, &MvPoly::zero());
    }
}
