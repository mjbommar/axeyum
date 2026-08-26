//! Complete SAT encoding for bounded `GF(2)` tensor rank.
//!
//! For each proposed rank-one summand the primary variables are the three
//! factor vectors. Every target coefficient is constrained to the XOR of the
//! corresponding triple products. Search is untrusted: SAT models are lifted
//! into the portable CAS artifact and replayed coefficient by coefficient.

use axeyum_cas::gf2_tensor::{
    GF2_TENSOR_DECOMPOSITION_SCHEMA, Gf2RankOneTerm, Gf2Tensor, Gf2TensorCheck,
    Gf2TensorCheckLimits, Gf2TensorDecomposition, Gf2TensorError, check_gf2_tensor_decomposition,
};
use axeyum_cnf::{CnfAssignment, CnfClause, CnfFormula, CnfLit, CnfVar};

/// Stable admission policy for bounded-rank encoding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TensorRankEncodingLimits {
    /// Largest dense target coefficient volume.
    pub max_coefficients: usize,
    /// Largest admitted rank budget.
    pub max_rank: usize,
    /// Largest generated CNF variable count.
    pub max_variables: usize,
    /// Largest generated clause count.
    pub max_clauses: usize,
}

impl Default for TensorRankEncodingLimits {
    fn default() -> Self {
        Self {
            max_coefficients: 16 * 1024 * 1024,
            max_rank: 1_000_000,
            max_variables: 16_000_000,
            max_clauses: 16_000_000,
        }
    }
}

/// Malformed input, resource decline, or rejected model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TensorRankEncodingError {
    /// The target tensor is malformed or exceeds its dense admission limit.
    Tensor(Gf2TensorError),
    /// A stable encoding ceiling was exceeded.
    LimitExceeded {
        /// Resource name.
        resource: &'static str,
        /// First observed value beyond the ceiling.
        observed: usize,
        /// Configured ceiling.
        limit: usize,
    },
    /// The CNF layer rejected construction or evaluation.
    Cnf(String),
    /// A purported satisfying model failed CNF or tensor replay.
    InvalidModel(String),
    /// A witness does not fit this target or rank budget.
    InvalidWitness(String),
}

impl From<Gf2TensorError> for TensorRankEncodingError {
    fn from(value: Gf2TensorError) -> Self {
        Self::Tensor(value)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct FactorLayout {
    a: Vec<Vec<usize>>,
    b: Vec<Vec<usize>>,
    c: Vec<Vec<usize>>,
}

/// One admitted first-factor stabilizer orbit in a normalized matrix-tensor encoding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TensorFirstFactorOrbit {
    /// Support of the canonical matrix-rank normal form in row-major order.
    pub support: Vec<usize>,
    /// CNF selector that is true exactly for this normal form.
    pub selector: CnfVar,
}

/// Exact CNF question “does `target` have rank at most `budget`?”.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TensorRankEncoding {
    formula: CnfFormula,
    target: Gf2Tensor,
    layout: FactorLayout,
    budget: usize,
    ordered_from: Option<usize>,
    first_factor_orbits: Vec<TensorFirstFactorOrbit>,
}

impl TensorRankEncoding {
    /// Exact deterministic formula.
    pub fn formula(&self) -> &CnfFormula {
        &self.formula
    }

    /// Rank budget represented by the formula.
    pub fn budget(&self) -> usize {
        self.budget
    }

    /// Complete admitted orbit list for normalized first-factor search.
    ///
    /// The list is empty for generic and term-order-only encodings. For a
    /// normalized matrix tensor, selectors are one-hot and each entry binds
    /// the canonical row-major support to its exact CNF variable.
    pub fn first_factor_orbits(&self) -> &[TensorFirstFactorOrbit] {
        &self.first_factor_orbits
    }

    /// Lift and independently replay a satisfying CNF model.
    ///
    /// Zero summands are removed, so the returned artifact states its actual
    /// rank rather than the padded budget.
    ///
    /// # Errors
    ///
    /// Refuses a wrong-width or non-satisfying model and any decomposition that
    /// fails the independent CAS coefficient checker.
    pub fn lift_model(
        &self,
        model: &CnfAssignment,
    ) -> Result<Gf2TensorDecomposition, TensorRankEncodingError> {
        if !self.formula.evaluate(model.values()).map_err(|error| {
            TensorRankEncodingError::Cnf(format!("formula evaluation: {error:?}"))
        })? {
            return Err(TensorRankEncodingError::InvalidModel(
                "assignment does not satisfy the tensor-rank formula".to_owned(),
            ));
        }
        let mut terms = Vec::new();
        for term in 0..self.budget {
            let factor = Gf2RankOneTerm {
                a: selected(&self.layout.a[term], model.values()),
                b: selected(&self.layout.b[term], model.values()),
                c: selected(&self.layout.c[term], model.values()),
            };
            if !factor.a.is_empty() && !factor.b.is_empty() && !factor.c.is_empty() {
                terms.push(factor);
            }
        }
        let decomposition = Gf2TensorDecomposition {
            schema: GF2_TENSOR_DECOMPOSITION_SCHEMA.to_owned(),
            dimensions: self.target.dimensions,
            terms,
        };
        match check_gf2_tensor_decomposition(
            &self.target,
            &decomposition,
            Gf2TensorCheckLimits::default(),
        ) {
            Ok(Gf2TensorCheck::Verified { .. }) => Ok(decomposition),
            other => Err(TensorRankEncodingError::InvalidModel(format!(
                "lifted decomposition replay: {other:?}"
            ))),
        }
    }

    /// Add unit clauses pinning a known decomposition into this exact formula.
    ///
    /// # Errors
    ///
    /// Refuses a malformed/non-replaying witness or one larger than the budget.
    pub fn formula_with_witness(
        &self,
        witness: &Gf2TensorDecomposition,
    ) -> Result<CnfFormula, TensorRankEncodingError> {
        if witness.terms.len() > self.budget {
            return Err(TensorRankEncodingError::InvalidWitness(format!(
                "witness rank {} exceeds budget {}",
                witness.terms.len(),
                self.budget
            )));
        }
        if !matches!(
            check_gf2_tensor_decomposition(&self.target, witness, Gf2TensorCheckLimits::default()),
            Ok(Gf2TensorCheck::Verified { .. })
        ) {
            return Err(TensorRankEncodingError::InvalidWitness(
                "witness does not replay against the target".to_owned(),
            ));
        }
        let mut formula = self.formula.clone();
        let mut supplied_terms = witness.terms.iter().map(Some).collect::<Vec<_>>();
        supplied_terms.resize(self.budget, None);
        if let Some(ordered_from) = self.ordered_from {
            supplied_terms[ordered_from..].sort_by_key(|term| {
                let mut bits = Vec::with_capacity(self.target.dimensions.iter().sum());
                for (dimension, support) in [
                    (
                        self.target.dimensions[0],
                        term.map(|item| item.a.as_slice()),
                    ),
                    (
                        self.target.dimensions[1],
                        term.map(|item| item.b.as_slice()),
                    ),
                    (
                        self.target.dimensions[2],
                        term.map(|item| item.c.as_slice()),
                    ),
                ] {
                    bits.extend(
                        (0..dimension)
                            .map(|index| support.is_some_and(|entries| entries.contains(&index))),
                    );
                }
                bits
            });
        }
        if !self.first_factor_orbits.is_empty() {
            let Some(Some(first)) = supplied_terms.first() else {
                return Err(TensorRankEncodingError::InvalidWitness(
                    "normalized formula needs a nonzero first summand".to_owned(),
                ));
            };
            if first.b.is_empty()
                || first.c.is_empty()
                || !self.first_factor_orbits.iter().any(|orbit| {
                    orbit.support.len() == first.a.len()
                        && orbit.support.iter().all(|index| first.a.contains(index))
                })
            {
                return Err(TensorRankEncodingError::InvalidWitness(
                    "first summand is not in an admitted matrix rank-normal form".to_owned(),
                ));
            }
        }
        for (term, &supplied) in supplied_terms.iter().enumerate() {
            for (variables, support) in [
                (&self.layout.a[term], supplied.map(|item| item.a.as_slice())),
                (&self.layout.b[term], supplied.map(|item| item.b.as_slice())),
                (&self.layout.c[term], supplied.map(|item| item.c.as_slice())),
            ] {
                for (index, &variable) in variables.iter().enumerate() {
                    let value = support.is_some_and(|entries| entries.contains(&index));
                    let literal = CnfLit::positive(cnf_var(variable)?);
                    formula
                        .add_clause(CnfClause::new(vec![if value {
                            literal
                        } else {
                            literal.negated()
                        }]))
                        .map_err(|error| TensorRankEncodingError::Cnf(format!("pin: {error:?}")))?;
                }
            }
        }
        Ok(formula)
    }
}

fn selected(variables: &[usize], values: &[bool]) -> Vec<usize> {
    variables
        .iter()
        .enumerate()
        .filter_map(|(index, &variable)| values[variable].then_some(index))
        .collect()
}

fn cnf_var(index: usize) -> Result<CnfVar, TensorRankEncodingError> {
    CnfVar::new(index).map_err(|error| TensorRankEncodingError::Cnf(format!("variable: {error:?}")))
}

#[derive(Debug)]
struct Builder {
    variables: usize,
    clauses: Vec<Vec<(usize, bool)>>,
    limits: TensorRankEncodingLimits,
}

impl Builder {
    fn variable(&mut self) -> Result<usize, TensorRankEncodingError> {
        self.variables = self.variables.saturating_add(1);
        if self.variables > self.limits.max_variables {
            return Err(TensorRankEncodingError::LimitExceeded {
                resource: "variables",
                observed: self.variables,
                limit: self.limits.max_variables,
            });
        }
        Ok(self.variables - 1)
    }

    fn variables(&mut self, count: usize) -> Result<Vec<usize>, TensorRankEncodingError> {
        (0..count).map(|_| self.variable()).collect()
    }

    fn clause(&mut self, literals: &[(usize, bool)]) -> Result<(), TensorRankEncodingError> {
        self.clauses.push(literals.to_vec());
        if self.clauses.len() > self.limits.max_clauses {
            return Err(TensorRankEncodingError::LimitExceeded {
                resource: "clauses",
                observed: self.clauses.len(),
                limit: self.limits.max_clauses,
            });
        }
        Ok(())
    }

    fn and3(&mut self, a: usize, b: usize, c: usize) -> Result<usize, TensorRankEncodingError> {
        let output = self.variable()?;
        self.clause(&[(output, true), (a, false)])?;
        self.clause(&[(output, true), (b, false)])?;
        self.clause(&[(output, true), (c, false)])?;
        self.clause(&[(a, true), (b, true), (c, true), (output, false)])?;
        Ok(output)
    }

    fn xor(&mut self, a: usize, b: usize) -> Result<usize, TensorRankEncodingError> {
        let output = self.variable()?;
        self.clause(&[(a, true), (b, true), (output, true)])?;
        self.clause(&[(a, false), (b, false), (output, true)])?;
        self.clause(&[(a, false), (b, true), (output, false)])?;
        self.clause(&[(a, true), (b, false), (output, false)])?;
        Ok(output)
    }

    fn parity(&mut self, terms: &[usize], value: bool) -> Result<(), TensorRankEncodingError> {
        let Some((&first, rest)) = terms.split_first() else {
            if value {
                self.clause(&[])?;
            }
            return Ok(());
        };
        let mut parity = first;
        for &term in rest {
            parity = self.xor(parity, term)?;
        }
        self.clause(&[(parity, !value)])
    }

    fn equivalent(&mut self, left: usize, right: usize) -> Result<usize, TensorRankEncodingError> {
        let equal = self.variable()?;
        self.clause(&[(equal, true), (left, true), (right, false)])?;
        self.clause(&[(equal, true), (left, false), (right, true)])?;
        self.clause(&[(equal, false), (left, false), (right, false)])?;
        self.clause(&[(equal, false), (left, true), (right, true)])?;
        Ok(equal)
    }

    fn conjunction(&mut self, left: usize, right: usize) -> Result<usize, TensorRankEncodingError> {
        let both = self.variable()?;
        self.clause(&[(both, true), (left, false)])?;
        self.clause(&[(both, true), (right, false)])?;
        self.clause(&[(left, true), (right, true), (both, false)])?;
        Ok(both)
    }

    /// Enforce `left <= right` lexicographically with `false < true`.
    fn lex_le(&mut self, left: &[usize], right: &[usize]) -> Result<(), TensorRankEncodingError> {
        debug_assert_eq!(left.len(), right.len());
        let mut equal_prefix = None;
        for (index, (&left_bit, &right_bit)) in left.iter().zip(right).enumerate() {
            let mut forbidden = vec![(left_bit, true), (right_bit, false)];
            if let Some(prefix) = equal_prefix {
                forbidden.push((prefix, true));
            }
            self.clause(&forbidden)?;
            if index + 1 < left.len() {
                let equal_bit = self.equivalent(left_bit, right_bit)?;
                equal_prefix = Some(match equal_prefix {
                    None => equal_bit,
                    Some(prefix) => self.conjunction(prefix, equal_bit)?,
                });
            }
        }
        Ok(())
    }

    fn finish(self) -> Result<CnfFormula, TensorRankEncodingError> {
        let mut formula = CnfFormula::new(self.variables);
        for clause in self.clauses {
            let literals = clause
                .into_iter()
                .map(|(variable, negated)| {
                    let literal = CnfLit::positive(cnf_var(variable)?);
                    Ok(if negated { literal.negated() } else { literal })
                })
                .collect::<Result<Vec<_>, TensorRankEncodingError>>()?;
            formula
                .add_clause(CnfClause::new(literals))
                .map_err(|error| TensorRankEncodingError::Cnf(format!("finish: {error:?}")))?;
        }
        Ok(formula)
    }
}

/// Encode the complete bounded-rank question for an arbitrary `GF(2)` tensor.
///
/// # Errors
///
/// Refuses malformed targets and any construction exceeding explicit limits.
pub fn encode_tensor_rank(
    target: &Gf2Tensor,
    budget: usize,
    limits: TensorRankEncodingLimits,
) -> Result<TensorRankEncoding, TensorRankEncodingError> {
    encode_tensor_rank_internal(target, budget, limits, None, Vec::new())
}

/// Encode bounded rank with a complete lexicographic breaker for the
/// permutation symmetry among rank-one summands.
///
/// Sorting does not remove any decomposition because tensor addition is
/// commutative. The order compares the concatenated `a`, `b`, and `c` factor
/// bits with `false < true`; padded zero summands consequently occur first.
///
/// # Errors
///
/// Refuses malformed targets and any construction exceeding explicit limits.
pub fn encode_tensor_rank_with_ordered_terms(
    target: &Gf2Tensor,
    budget: usize,
    limits: TensorRankEncodingLimits,
) -> Result<TensorRankEncoding, TensorRankEncodingError> {
    encode_tensor_rank_internal(target, budget, limits, Some(0), Vec::new())
}

/// Encode matrix-multiplication tensor rank after normalizing one nonzero
/// summand under the natural change-of-basis stabilizer.
///
/// A nonzero `m x n` first-factor matrix has rank `q >= 1` and invertible row
/// and column transformations send it to `diag(I_q, 0)`. The corresponding
/// coupled transformations of the other two factors preserve the matrix
/// multiplication tensor. Thus some summand may be placed in slot zero with
/// one of these `min(m,n)` forms. Remaining slots are lexicographically
/// ordered; slot zero deliberately is not compared with them.
///
/// # Errors
///
/// Refuses zero dimensions, a zero budget, arithmetic overflow, or a
/// construction exceeding explicit limits.
pub fn encode_matrix_tensor_rank_with_normalized_first_factor(
    m: usize,
    n: usize,
    p: usize,
    budget: usize,
    limits: TensorRankEncodingLimits,
) -> Result<TensorRankEncoding, TensorRankEncodingError> {
    let target = Gf2Tensor::matrix_multiplication(m, n, p)?;
    if budget == 0 {
        return Err(TensorRankEncodingError::InvalidWitness(
            "a nonzero matrix tensor cannot normalize a term at rank zero".to_owned(),
        ));
    }
    let forms = (1..=m.min(n))
        .map(|rank| (0..rank).map(|index| index * n + index).collect())
        .collect();
    encode_tensor_rank_internal(&target, budget, limits, Some(1), forms)
}

fn add_first_factor_normalization(
    builder: &mut Builder,
    layout: &FactorLayout,
    forms: Vec<Vec<usize>>,
) -> Result<Vec<TensorFirstFactorOrbit>, TensorRankEncodingError> {
    if forms.is_empty() {
        return Ok(Vec::new());
    }
    let selectors = builder.variables(forms.len())?;
    builder.clause(
        &selectors
            .iter()
            .copied()
            .map(|selector| (selector, false))
            .collect::<Vec<_>>(),
    )?;
    for left in 0..selectors.len() {
        for right in left + 1..selectors.len() {
            builder.clause(&[(selectors[left], true), (selectors[right], true)])?;
        }
    }
    for (form, &selector) in forms.iter().zip(&selectors) {
        for (index, &variable) in layout.a[0].iter().enumerate() {
            builder.clause(&[(selector, true), (variable, !form.contains(&index))])?;
        }
    }
    builder.clause(
        &layout.b[0]
            .iter()
            .copied()
            .map(|variable| (variable, false))
            .collect::<Vec<_>>(),
    )?;
    builder.clause(
        &layout.c[0]
            .iter()
            .copied()
            .map(|variable| (variable, false))
            .collect::<Vec<_>>(),
    )?;
    forms
        .into_iter()
        .zip(selectors)
        .map(|(support, selector)| {
            Ok(TensorFirstFactorOrbit {
                support,
                selector: cnf_var(selector)?,
            })
        })
        .collect()
}

fn encode_tensor_rank_internal(
    target: &Gf2Tensor,
    budget: usize,
    limits: TensorRankEncodingLimits,
    ordered_from: Option<usize>,
    first_factor_forms: Vec<Vec<usize>>,
) -> Result<TensorRankEncoding, TensorRankEncodingError> {
    if budget > limits.max_rank {
        return Err(TensorRankEncodingError::LimitExceeded {
            resource: "rank",
            observed: budget,
            limit: limits.max_rank,
        });
    }
    let coefficients = target.dense_coefficients(limits.max_coefficients)?;
    let mut builder = Builder {
        variables: 0,
        clauses: Vec::new(),
        limits,
    };
    let mut layout = FactorLayout {
        a: Vec::with_capacity(budget),
        b: Vec::with_capacity(budget),
        c: Vec::with_capacity(budget),
    };
    for _ in 0..budget {
        layout.a.push(builder.variables(target.dimensions[0])?);
        layout.b.push(builder.variables(target.dimensions[1])?);
        layout.c.push(builder.variables(target.dimensions[2])?);
    }
    let first_factor_orbits =
        add_first_factor_normalization(&mut builder, &layout, first_factor_forms)?;
    if let Some(ordered_from) = ordered_from {
        for term in ordered_from..budget.saturating_sub(1) {
            let left = [
                &layout.a[term][..],
                &layout.b[term][..],
                &layout.c[term][..],
            ]
            .concat();
            let right = [
                &layout.a[term + 1][..],
                &layout.b[term + 1][..],
                &layout.c[term + 1][..],
            ]
            .concat();
            builder.lex_le(&left, &right)?;
        }
    }
    let [a_dimension, b_dimension, c_dimension] = target.dimensions;
    for a in 0..a_dimension {
        for b in 0..b_dimension {
            for c in 0..c_dimension {
                let mut products = Vec::with_capacity(budget);
                for term in 0..budget {
                    products.push(builder.and3(
                        layout.a[term][a],
                        layout.b[term][b],
                        layout.c[term][c],
                    )?);
                }
                let index = (a * b_dimension + b) * c_dimension + c;
                builder.parity(&products, coefficients[index])?;
            }
        }
    }
    let formula = builder.finish()?;
    Ok(TensorRankEncoding {
        formula,
        target: target.clone(),
        layout,
        budget,
        ordered_from,
        first_factor_orbits,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_cnf::cube::{boolean_product_cubes, covering_formula};
    use axeyum_cnf::{
        ProofSolveOutcome, SatResult, check_drat, solve_with_drat_proof, solve_with_rustsat_batsat,
    };

    fn strassen() -> Gf2TensorDecomposition {
        Gf2TensorDecomposition {
            schema: GF2_TENSOR_DECOMPOSITION_SCHEMA.to_owned(),
            dimensions: [4, 4, 4],
            terms: vec![
                Gf2RankOneTerm {
                    a: vec![0, 3],
                    b: vec![0, 3],
                    c: vec![0, 3],
                },
                Gf2RankOneTerm {
                    a: vec![2, 3],
                    b: vec![0],
                    c: vec![2, 3],
                },
                Gf2RankOneTerm {
                    a: vec![0],
                    b: vec![1, 3],
                    c: vec![1, 3],
                },
                Gf2RankOneTerm {
                    a: vec![3],
                    b: vec![0, 2],
                    c: vec![0, 2],
                },
                Gf2RankOneTerm {
                    a: vec![0, 1],
                    b: vec![3],
                    c: vec![0, 1],
                },
                Gf2RankOneTerm {
                    a: vec![0, 2],
                    b: vec![0, 1],
                    c: vec![3],
                },
                Gf2RankOneTerm {
                    a: vec![1, 3],
                    b: vec![2, 3],
                    c: vec![0],
                },
            ],
        }
    }

    #[test]
    fn pinned_strassen_model_lifts_and_replays() {
        let target = Gf2Tensor::matrix_multiplication(2, 2, 2).unwrap();
        let encoding = encode_tensor_rank(&target, 7, TensorRankEncodingLimits::default()).unwrap();
        let pinned = encoding.formula_with_witness(&strassen()).unwrap();
        let SatResult::Sat(model) = solve_with_rustsat_batsat(&pinned).unwrap() else {
            panic!("pinned Strassen witness must be satisfiable");
        };
        let lifted = encoding.lift_model(&model).unwrap();
        assert_eq!(lifted.terms.len(), 7);
    }

    #[test]
    fn ordered_terms_accept_an_unsorted_witness_and_lift_canonically() {
        let target = Gf2Tensor::matrix_multiplication(2, 2, 2).unwrap();
        let encoding =
            encode_tensor_rank_with_ordered_terms(&target, 8, TensorRankEncodingLimits::default())
                .unwrap();
        let mut witness = strassen();
        witness.terms.reverse();
        let pinned = encoding.formula_with_witness(&witness).unwrap();
        let SatResult::Sat(model) = solve_with_rustsat_batsat(&pinned).unwrap() else {
            panic!("term sorting must preserve a padded decomposition");
        };
        let lifted = encoding.lift_model(&model).unwrap();
        assert_eq!(lifted.terms.len(), 7);
        assert!(lifted.terms.windows(2).all(|pair| {
            let bits = |term: &Gf2RankOneTerm| {
                [
                    (0..4).map(|i| term.a.contains(&i)).collect::<Vec<_>>(),
                    (0..4).map(|i| term.b.contains(&i)).collect::<Vec<_>>(),
                    (0..4).map(|i| term.c.contains(&i)).collect::<Vec<_>>(),
                ]
                .concat()
            };
            bits(&pair[0]) <= bits(&pair[1])
        }));
    }

    #[test]
    fn lexicographic_breaker_matches_all_two_bit_pairs() {
        let mut builder = Builder {
            variables: 0,
            clauses: Vec::new(),
            limits: TensorRankEncodingLimits::default(),
        };
        let left = builder.variables(2).unwrap();
        let right = builder.variables(2).unwrap();
        builder.lex_le(&left, &right).unwrap();
        let base = builder.finish().unwrap();

        for left_value in 0_u8..4 {
            for right_value in 0_u8..4 {
                let mut formula = base.clone();
                for (variables, value) in [(&left, left_value), (&right, right_value)] {
                    for (offset, &variable) in variables.iter().enumerate() {
                        let bit = value & (1 << (1 - offset)) != 0;
                        let literal = CnfLit::positive(cnf_var(variable).unwrap());
                        formula
                            .add_clause(CnfClause::new(vec![if bit {
                                literal
                            } else {
                                literal.negated()
                            }]))
                            .unwrap();
                    }
                }
                assert_eq!(
                    matches!(
                        solve_with_rustsat_batsat(&formula).unwrap(),
                        SatResult::Sat(_)
                    ),
                    left_value <= right_value,
                    "left={left_value:02b} right={right_value:02b}"
                );
            }
        }
    }

    #[test]
    fn matrix_first_factor_normalization_preserves_strassen_and_padding() {
        let encoding = encode_matrix_tensor_rank_with_normalized_first_factor(
            2,
            2,
            2,
            8,
            TensorRankEncodingLimits::default(),
        )
        .unwrap();
        assert_eq!(
            encoding
                .first_factor_orbits()
                .iter()
                .map(|orbit| (orbit.support.clone(), orbit.selector.dimacs()))
                .collect::<Vec<_>>(),
            vec![(vec![0], 97), (vec![0, 3], 98)]
        );
        let cubes = boolean_product_cubes(
            &encoding
                .first_factor_orbits()
                .iter()
                .map(|orbit| orbit.selector)
                .collect::<Vec<_>>(),
        )
        .unwrap();
        let covering = covering_formula(encoding.formula(), &cubes).unwrap();
        let ProofSolveOutcome::Unsat(covering_proof) = solve_with_drat_proof(&covering) else {
            panic!("one-hot orbit product must be exhaustive");
        };
        assert_eq!(check_drat(&covering, &covering_proof), Ok(true));
        let pinned = encoding.formula_with_witness(&strassen()).unwrap();
        let SatResult::Sat(model) = solve_with_rustsat_batsat(&pinned).unwrap() else {
            panic!("normalized Strassen witness must remain satisfiable");
        };
        assert_eq!(encoding.lift_model(&model).unwrap().terms.len(), 7);

        let mut malformed = strassen();
        malformed.terms.swap(0, 1);
        assert!(matches!(
            encoding.formula_with_witness(&malformed),
            Err(TensorRankEncodingError::InvalidWitness(message))
                if message.contains("rank-normal form")
        ));
    }

    #[test]
    fn rank_zero_distinguishes_zero_and_nonzero_tensors() {
        let zero = Gf2Tensor {
            dimensions: [1, 1, 1],
            ones: Vec::new(),
        };
        let one = Gf2Tensor {
            dimensions: [1, 1, 1],
            ones: vec![[0, 0, 0]],
        };
        let zero_encoding =
            encode_tensor_rank(&zero, 0, TensorRankEncodingLimits::default()).unwrap();
        let one_encoding =
            encode_tensor_rank(&one, 0, TensorRankEncodingLimits::default()).unwrap();
        assert!(zero_encoding.formula().clauses().is_empty());
        assert_eq!(one_encoding.formula().clauses().len(), 1);
        assert!(one_encoding.formula().clauses()[0].lits().is_empty());
    }

    #[test]
    fn matrix_boundary_shapes_are_deterministic() {
        let small = Gf2Tensor::matrix_multiplication(2, 2, 2).unwrap();
        let small_encoding =
            encode_tensor_rank(&small, 6, TensorRankEncodingLimits::default()).unwrap();
        assert_eq!(small_encoding.formula().variable_count(), 776);
        assert_eq!(small_encoding.formula().clauses().len(), 2_880);

        let boundary = Gf2Tensor::matrix_multiplication(3, 2, 4).unwrap();
        let boundary_encoding =
            encode_tensor_rank(&boundary, 19, TensorRankEncodingLimits::default()).unwrap();
        assert!(boundary_encoding.first_factor_orbits().is_empty());
        assert_eq!(boundary_encoding.formula().variable_count(), 21_806);
        assert_eq!(boundary_encoding.formula().clauses().len(), 85_824);
    }

    #[test]
    fn rank_and_formula_limits_fail_closed() {
        let target = Gf2Tensor::matrix_multiplication(1, 1, 1).unwrap();
        let limits = TensorRankEncodingLimits {
            max_rank: 0,
            ..TensorRankEncodingLimits::default()
        };
        assert_eq!(
            encode_tensor_rank(&target, 1, limits),
            Err(TensorRankEncodingError::LimitExceeded {
                resource: "rank",
                observed: 1,
                limit: 0,
            })
        );
        let limits = TensorRankEncodingLimits {
            max_variables: 3,
            ..TensorRankEncodingLimits::default()
        };
        assert_eq!(
            encode_tensor_rank(&target, 1, limits),
            Err(TensorRankEncodingError::LimitExceeded {
                resource: "variables",
                observed: 4,
                limit: 3,
            })
        );
    }
}
