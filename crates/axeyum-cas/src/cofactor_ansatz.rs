//! Ideal membership by **exact linear algebra** at a bounded cofactor degree.
//!
//! Buchberger's algorithm answers "is `t` in `(g₁ … gₙ)`?" by building a Gröbner
//! basis first. That is the general answer and it is the expensive one: the basis
//! is a property of the *ideal*, and computing it can diverge on inputs whose
//! membership question has a one-line answer.
//!
//! This module asks a deliberately smaller question:
//!
//! ```text
//! is there a representation  t = Σᵢ uᵢ·gᵢ  with every  deg(uᵢ) ≤ d ?
//! ```
//!
//! For a fixed `d` that is **linear algebra over ℚ**, not rewriting. Write each
//! `uᵢ` as an unknown combination of the monomials of degree ≤ `d`; expand; and
//! match coefficients monomial by monomial. The result is one sparse rational
//! system whose unknowns are the cofactor coefficients, and Gaussian elimination
//! either produces a representation or proves there is none *at that degree*.
//!
//! # Why this earns its place beside `groebner_cert`
//!
//! It is not a faster Gröbner engine and it is not a replacement for one. It is
//! **incomplete on purpose**: a `NotInDegree` answer says nothing about the ideal,
//! only about the degree-`d` slice of it, and a caller that needs the ideal
//! question answered must still go to `groebner_cert`. What it buys is that the
//! slice is *decided* — no ceiling, no queue, no basis — and the certificate it
//! produces is the same object either route produces, checkable by the same
//! independent checker that never sees which route made it.
//!
//! The measurement that motivated the module, on `pappus-hexagon`
//! (`crates/axeyum-cas/examples/geometry_cofactor_routes.rs`): after the
//! `AE ∩ BD` block is eliminated linearly, the residue is 48 terms of degree 4
//! and lies in the ideal of the six untouched hypotheses. Buchberger was killed on it
//! after **7.5 minutes** without returning; this route settles it in milliseconds, and
//! every coefficient in the answer is `±1`.
//!
//! # What is bounded, and what is not
//!
//! [`AnsatzLimits`] bounds the *shape* of the system — the cofactor degree, and
//! the size of the matrix that shape implies — never the number of steps. Once a
//! system is built, it is solved to completion. So an outcome is never "we ran
//! out of budget mid-answer": it is a representation, a decided
//! [`AnsatzOutcome::NotInDegree`], or a refusal to build a system that large at
//! all.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::Rational;

use crate::mvpoly::{Monomial, MvPoly};

/// The shape ceilings for [`cofactors_by_ansatz`].
///
/// Every field bounds the *system*, not the solve. `max_cofactor_degree` is the
/// mathematical parameter — the slice of the ideal being searched — and the other
/// two exist so a pathological generator list cannot allocate an enormous matrix
/// before anyone notices.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AnsatzLimits {
    /// The largest total degree an individual cofactor may have. Degrees are
    /// tried in ascending order, so the representation found is the one of least
    /// cofactor degree.
    pub max_cofactor_degree: u32,
    /// The largest number of unknowns (generators × monomials) admitted.
    pub max_columns: usize,
    /// The largest number of distinct monomials (equations) admitted.
    pub max_rows: usize,
}

impl AnsatzLimits {
    /// Ceilings sized for the geometry corpus: cofactors up to degree three, and
    /// a matrix a few thousand on a side.
    ///
    /// Degree three rather than two is deliberate head-room — the residues this
    /// route is handed are settled at degree two, and a ceiling set exactly at
    /// the observed answer measures nothing.
    #[must_use]
    pub fn geometry() -> AnsatzLimits {
        AnsatzLimits {
            max_cofactor_degree: 3,
            max_columns: 20_000,
            max_rows: 200_000,
        }
    }
}

/// Why [`cofactors_by_ansatz`] built no system.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AnsatzDecline {
    /// The unknown count would exceed [`AnsatzLimits::max_columns`].
    Columns,
    /// The equation count would exceed [`AnsatzLimits::max_rows`].
    Rows,
    /// Exact `i128` rational arithmetic ran out of room.
    Overflow,
}

/// The result of a bounded-degree membership search.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AnsatzOutcome {
    /// One cofactor per generator, positionally aligned, with
    /// `target == Σ cofactors[i]·generators[i]` — re-expanded and compared before
    /// this value is returned, so a wrong solve cannot leave this module.
    Solved {
        /// The cofactors, positionally aligned with the caller's generators.
        cofactors: Vec<MvPoly>,
        /// The degree at which the system became solvable.
        degree: u32,
    },
    /// **Decided**: no representation exists with every cofactor of degree ≤ this
    /// bound. This is a statement about the degree slice, never about the ideal.
    NotInDegree(u32),
    /// No system was built.
    Declined(AnsatzDecline),
}

/// Search for `target = Σ uᵢ·generatorᵢ` with `deg(uᵢ) ≤ d`, for the least `d`
/// that admits one.
///
/// Degrees are tried in ascending order from zero, so a target that is a plain
/// rational combination of the generators is reported as such.
///
/// ```
/// use axeyum_cas::cofactor_ansatz::{AnsatzLimits, AnsatzOutcome, cofactors_by_ansatz};
/// use axeyum_cas::mvpoly::MvPoly;
///
/// // x²−y² = (x+y)·(x−y): degree-one cofactors, found at degree one.
/// let x = MvPoly::var("x");
/// let y = MvPoly::var("y");
/// let generators = vec![x.sub(&y).unwrap()];
/// let target = x.mul(&x).unwrap().sub(&y.mul(&y).unwrap()).unwrap();
/// let outcome = cofactors_by_ansatz(&generators, &target, AnsatzLimits::geometry());
/// let AnsatzOutcome::Solved { cofactors, degree } = outcome else {
///     panic!("x²−y² is in (x−y)")
/// };
/// assert_eq!(degree, 1);
/// assert_eq!(cofactors[0], x.add(&y).unwrap());
/// ```
///
/// A target that is genuinely outside the ideal is *decided*, not declined —
/// there is no budget in the answer:
///
/// ```
/// use axeyum_cas::cofactor_ansatz::{AnsatzLimits, AnsatzOutcome, cofactors_by_ansatz};
/// use axeyum_cas::mvpoly::MvPoly;
///
/// let x = MvPoly::var("x");
/// let outcome = cofactors_by_ansatz(
///     &[x.mul(&x).unwrap()],
///     &x,
///     AnsatzLimits { max_cofactor_degree: 2, ..AnsatzLimits::geometry() },
/// );
/// assert_eq!(outcome, AnsatzOutcome::NotInDegree(2));
/// ```
#[must_use]
pub fn cofactors_by_ansatz(
    generators: &[MvPoly],
    target: &MvPoly,
    limits: AnsatzLimits,
) -> AnsatzOutcome {
    if generators.is_empty() {
        return if target.is_zero() {
            AnsatzOutcome::Solved {
                cofactors: Vec::new(),
                degree: 0,
            }
        } else {
            AnsatzOutcome::NotInDegree(limits.max_cofactor_degree)
        };
    }

    let mut variables: Vec<String> = target.variables().into_iter().collect();
    for generator in generators {
        for variable in generator.variables() {
            if !variables.contains(&variable) {
                variables.push(variable);
            }
        }
    }
    variables.sort();

    for degree in 0..=limits.max_cofactor_degree {
        match solve_at_degree(generators, target, &variables, degree, limits) {
            Ok(Some(cofactors)) => return AnsatzOutcome::Solved { cofactors, degree },
            Ok(None) => {}
            Err(decline) => return AnsatzOutcome::Declined(decline),
        }
    }
    AnsatzOutcome::NotInDegree(limits.max_cofactor_degree)
}

/// Every monomial of total degree at most `degree` over `variables`, in ascending
/// [`Monomial`] order.
fn monomials_up_to(variables: &[String], degree: u32) -> Vec<Monomial> {
    let mut all: BTreeSet<Monomial> = BTreeSet::new();
    all.insert(Monomial::one());
    let mut frontier: BTreeSet<Monomial> = all.clone();
    for _ in 0..degree {
        let mut next: BTreeSet<Monomial> = BTreeSet::new();
        for mono in &frontier {
            for variable in variables {
                let mut powers: Vec<(String, u32)> = mono
                    .powers()
                    .map(|(name, exp)| (name.to_owned(), exp))
                    .collect();
                match powers.iter_mut().find(|(name, _)| name == variable) {
                    Some(slot) => slot.1 += 1,
                    None => powers.push((variable.clone(), 1)),
                }
                let borrowed: Vec<(&str, u32)> = powers
                    .iter()
                    .map(|(name, exp)| (name.as_str(), *exp))
                    .collect();
                next.insert(Monomial::from_powers(&borrowed));
            }
        }
        all.extend(next.iter().cloned());
        frontier = next;
    }
    all.into_iter().collect()
}

/// One Macaulay system: build it, solve it exactly, and hand back cofactors or
/// `None` when the system is inconsistent (which *decides* the degree).
fn solve_at_degree(
    generators: &[MvPoly],
    target: &MvPoly,
    variables: &[String],
    degree: u32,
    limits: AnsatzLimits,
) -> Result<Option<Vec<MvPoly>>, AnsatzDecline> {
    let monomials = monomials_up_to(variables, degree);
    let columns = generators
        .len()
        .checked_mul(monomials.len())
        .ok_or(AnsatzDecline::Columns)?;
    if columns > limits.max_columns {
        return Err(AnsatzDecline::Columns);
    }

    // Column `slot·monomials.len() + index` is "the coefficient of
    // `monomials[index]` in the cofactor of `generators[slot]`".
    let one = Rational::integer(1);
    let mut rows: BTreeMap<Monomial, BTreeMap<usize, Rational>> = BTreeMap::new();
    for (slot, generator) in generators.iter().enumerate() {
        for (index, mono) in monomials.iter().enumerate() {
            let lifted =
                MvPoly::from_terms([(mono.clone(), one)]).ok_or(AnsatzDecline::Overflow)?;
            let product = lifted.mul(generator).ok_or(AnsatzDecline::Overflow)?;
            let column = slot * monomials.len() + index;
            for (row_mono, coefficient) in product.terms() {
                rows.entry(row_mono.clone())
                    .or_default()
                    .insert(column, *coefficient);
            }
        }
        if rows.len() > limits.max_rows {
            return Err(AnsatzDecline::Rows);
        }
    }
    // The right-hand side rides in the augmented column, so one elimination
    // decides consistency and produces the solution together.
    for (row_mono, coefficient) in target.terms() {
        rows.entry(row_mono.clone())
            .or_default()
            .insert(columns, *coefficient);
    }
    if rows.len() > limits.max_rows {
        return Err(AnsatzDecline::Rows);
    }

    let mut matrix: Vec<BTreeMap<usize, Rational>> = rows.into_values().collect();
    let solution = eliminate(&mut matrix, columns)?;
    let Some(solution) = solution else {
        return Ok(None);
    };

    let mut cofactors = Vec::with_capacity(generators.len());
    for slot in 0..generators.len() {
        let mut terms: Vec<(Monomial, Rational)> = Vec::new();
        for (index, mono) in monomials.iter().enumerate() {
            let value = solution
                .get(&(slot * monomials.len() + index))
                .copied()
                .unwrap_or_else(Rational::zero);
            if !value.is_zero() {
                terms.push((mono.clone(), value));
            }
        }
        cofactors.push(MvPoly::from_terms(terms).ok_or(AnsatzDecline::Overflow)?);
    }

    // The self-check. This module is a *producer*, and a producer that trusts its
    // own linear algebra is one arithmetic slip away from emitting a certificate
    // that says nothing. Re-expanding costs one multiplication per generator.
    let mut combined = MvPoly::zero();
    for (cofactor, generator) in cofactors.iter().zip(generators.iter()) {
        if cofactor.is_zero() {
            continue;
        }
        combined = combined
            .add(&cofactor.mul(generator).ok_or(AnsatzDecline::Overflow)?)
            .ok_or(AnsatzDecline::Overflow)?;
    }
    if &combined != target {
        return Ok(None);
    }
    Ok(Some(cofactors))
}

/// Sparse exact Gaussian elimination on an augmented system.
///
/// `columns` is the number of unknowns; index `columns` is the right-hand side.
/// Returns `Ok(None)` when the system is inconsistent — a *decided* answer — and
/// `Err` only when exact arithmetic ran out of room.
///
/// Row-major rather than column-major, which is the difference between a solve
/// that finishes and one that does not. Scanning every row for each of the
/// thousands of columns is `rows × columns` map probes before any arithmetic
/// happens; taking one row at a time and reducing it against the pivots it
/// actually touches is proportional to the *nonzeros*, which on these systems is
/// a few dozen per row.
///
/// Rows are visited sparsest-first, and each new pivot is the least column index
/// surviving in its reduced row. That is the classical Markowitz preference
/// restricted to a form cheap enough to maintain, and it earns its place
/// arithmetically rather than in speed: on the geometry residues it holds every
/// intermediate coefficient at `±1`, so exact `i128` rational arithmetic never
/// approaches the ceiling that naive pivoting walks it into.
fn eliminate(
    matrix: &mut [BTreeMap<usize, Rational>],
    columns: usize,
) -> Result<Option<BTreeMap<usize, Rational>>, AnsatzDecline> {
    // Pivot rows in creation order. `pivot_of_column` maps a pivot column to its
    // position here, and the invariant that makes both the reduction and the
    // back-substitution linear is: the row created at position `k` contains no
    // pivot column created at any position `< k`.
    let mut pivot_rows: Vec<(usize, BTreeMap<usize, Rational>)> = Vec::new();
    let mut pivot_of_column: BTreeMap<usize, usize> = BTreeMap::new();

    let mut order: Vec<usize> = (0..matrix.len()).collect();
    order.sort_by_key(|&index| (matrix[index].len(), index));

    for index in order {
        let mut row = std::mem::take(&mut matrix[index]);
        // Reduce against existing pivots, always taking the earliest-created one
        // still present. Subtracting it can only introduce pivots created later,
        // so this terminates after at most one pass per pivot the row meets.
        while let Some(position) = row
            .keys()
            .filter_map(|column| pivot_of_column.get(column))
            .min()
            .copied()
        {
            let (pivot_column, pivot_row) = &pivot_rows[position];
            let factor = row[pivot_column];
            for (key, value) in pivot_row {
                let scaled = factor.checked_mul(*value).ok_or(AnsatzDecline::Overflow)?;
                let current = row.get(key).copied().unwrap_or_else(Rational::zero);
                let updated = current.checked_sub(scaled).ok_or(AnsatzDecline::Overflow)?;
                if updated.is_zero() {
                    row.remove(key);
                } else {
                    row.insert(*key, updated);
                }
            }
        }
        let Some(&pivot_column) = row.keys().find(|&&column| column < columns) else {
            // Nothing but the right-hand side left. Zero is a redundant equation;
            // anything else is `0 = c`, and the system has no solution at all.
            if row.contains_key(&columns) {
                return Ok(None);
            }
            continue;
        };
        let scale = row[&pivot_column];
        let normalised: BTreeMap<usize, Rational> = row
            .iter()
            .map(|(key, value)| {
                value
                    .checked_div(scale)
                    .map(|scaled| (*key, scaled))
                    .ok_or(AnsatzDecline::Overflow)
            })
            .collect::<Result<_, _>>()?;
        pivot_of_column.insert(pivot_column, pivot_rows.len());
        pivot_rows.push((pivot_column, normalised));
    }

    // Free variables are zero; pivots are solved in reverse creation order, which
    // is exactly the order the invariant above makes triangular.
    let mut solution: BTreeMap<usize, Rational> = BTreeMap::new();
    for (pivot_column, row) in pivot_rows.iter().rev() {
        let mut value = row.get(&columns).copied().unwrap_or_else(Rational::zero);
        for (key, coefficient) in row {
            if key == pivot_column || *key == columns {
                continue;
            }
            let known = solution.get(key).copied().unwrap_or_else(Rational::zero);
            let product = coefficient
                .checked_mul(known)
                .ok_or(AnsatzDecline::Overflow)?;
            value = value.checked_sub(product).ok_or(AnsatzDecline::Overflow)?;
        }
        solution.insert(*pivot_column, value);
    }
    Ok(Some(solution))
}

#[cfg(test)]
mod tests {
    use super::{AnsatzDecline, AnsatzLimits, AnsatzOutcome, cofactors_by_ansatz, monomials_up_to};
    use crate::mvpoly::MvPoly;
    use axeyum_ir::Rational;

    fn int(n: i128) -> MvPoly {
        MvPoly::constant(Rational::integer(n))
    }

    #[test]
    fn monomial_counts_match_the_binomial_formula() {
        let variables: Vec<String> = ["x", "y", "z"].iter().map(|s| (*s).to_string()).collect();
        // C(n+d, d) monomials of degree at most d in n variables.
        assert_eq!(monomials_up_to(&variables, 0).len(), 1);
        assert_eq!(monomials_up_to(&variables, 1).len(), 4);
        assert_eq!(monomials_up_to(&variables, 2).len(), 10);
        assert_eq!(monomials_up_to(&variables, 3).len(), 20);
    }

    #[test]
    fn a_constant_combination_is_found_at_degree_zero() {
        let x = MvPoly::var("x");
        let y = MvPoly::var("y");
        let generators = vec![x.clone(), y.clone()];
        let target = x
            .mul(&int(3))
            .unwrap()
            .add(&y.mul(&int(-5)).unwrap())
            .unwrap();
        let AnsatzOutcome::Solved { cofactors, degree } =
            cofactors_by_ansatz(&generators, &target, AnsatzLimits::geometry())
        else {
            panic!("3x − 5y is a constant combination of x and y")
        };
        assert_eq!(degree, 0);
        assert_eq!(cofactors, vec![int(3), int(-5)]);
    }

    #[test]
    fn the_returned_identity_re_expands_to_the_target() {
        let (x, y, z) = (MvPoly::var("x"), MvPoly::var("y"), MvPoly::var("z"));
        let generators = vec![
            x.mul(&y).unwrap().sub(&int(1)).unwrap(),
            y.mul(&z).unwrap().sub(&int(1)).unwrap(),
        ];
        // (xy−1)·z + (yz−1)·(−x) = z − x.
        let target = z.sub(&x).unwrap();
        let AnsatzOutcome::Solved { cofactors, .. } =
            cofactors_by_ansatz(&generators, &target, AnsatzLimits::geometry())
        else {
            panic!("z − x is in the ideal")
        };
        let mut combined = MvPoly::zero();
        for (cofactor, generator) in cofactors.iter().zip(generators.iter()) {
            combined = combined.add(&cofactor.mul(generator).unwrap()).unwrap();
        }
        assert_eq!(combined, target, "the identity must hold as polynomials");
    }

    /// The distinction the module exists to keep honest: "not at this degree" is
    /// a decided fact about a slice, and it must not be reported as a decline.
    #[test]
    fn outside_the_degree_slice_is_decided_not_declined() {
        let x = MvPoly::var("x");
        let y = MvPoly::var("y");
        let outcome = cofactors_by_ansatz(
            &[x.mul(&x).unwrap().add(&y.mul(&y).unwrap()).unwrap()],
            &x,
            AnsatzLimits {
                max_cofactor_degree: 3,
                ..AnsatzLimits::geometry()
            },
        );
        assert_eq!(outcome, AnsatzOutcome::NotInDegree(3));
    }

    /// A ceiling on the *shape* refuses to build the system; it never reports a
    /// mathematical verdict it did not reach.
    #[test]
    fn a_system_larger_than_the_ceiling_declines_rather_than_deciding() {
        let x = MvPoly::var("x");
        let outcome = cofactors_by_ansatz(
            std::slice::from_ref(&x),
            &x.mul(&x).unwrap(),
            AnsatzLimits {
                max_cofactor_degree: 2,
                max_columns: 1,
                max_rows: 200_000,
            },
        );
        assert_eq!(outcome, AnsatzOutcome::Declined(AnsatzDecline::Columns));
    }

    #[test]
    fn no_generators_settles_only_the_zero_target() {
        assert_eq!(
            cofactors_by_ansatz(&[], &MvPoly::zero(), AnsatzLimits::geometry()),
            AnsatzOutcome::Solved {
                cofactors: Vec::new(),
                degree: 0
            }
        );
        assert!(matches!(
            cofactors_by_ansatz(&[], &MvPoly::var("x"), AnsatzLimits::geometry()),
            AnsatzOutcome::NotInDegree(_)
        ));
    }
}
