//! Deterministic, liftable lowering from Boolean ANF systems to CNF.
//!
//! Every source variable keeps the same zero-based CNF index. Nonlinear
//! monomials receive shared Tseitin conjunction variables, and equation parity
//! receives an XOR chain. SAT models lift by projection and are replayed against
//! the original [`BooleanAnfSystem`]. A checked refutation of the resulting CNF
//! therefore certifies that the source system has no Boolean solution.

use std::collections::BTreeMap;

use axeyum_cas::boolean_anf::{BooleanAnfError, BooleanAnfSystem};
use axeyum_cnf::{CnfAssignment, CnfClause, CnfError, CnfFormula, CnfLit, CnfVar};

/// Stable admission limits for Boolean-ANF-to-CNF lowering.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BooleanAnfCnfLimits {
    /// Largest admitted source or resulting CNF variable count.
    pub max_variables: usize,
    /// Largest admitted resulting clause count.
    pub max_clauses: usize,
    /// Largest admitted degree of one source monomial.
    pub max_monomial_degree: usize,
}

impl Default for BooleanAnfCnfLimits {
    fn default() -> Self {
        Self {
            max_variables: 5_000_000,
            max_clauses: 25_000_000,
            max_monomial_degree: 1_000_000,
        }
    }
}

/// A malformed input, exceeded lowering budget, or invalid SAT handoff.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BooleanAnfCnfError {
    /// The source system evaluator rejected the lifted assignment.
    Anf(BooleanAnfError),
    /// The CNF layer rejected a variable, clause, or assignment.
    Cnf(CnfError),
    /// A stable construction ceiling was exceeded.
    LimitExceeded {
        /// Resource name.
        resource: &'static str,
        /// First value known to exceed the limit.
        observed: usize,
        /// Configured limit.
        limit: usize,
    },
    /// A requested source unit lies outside the projected source prefix.
    SourceVariableOutOfRange {
        /// Offending zero-based index.
        variable: usize,
        /// Number of source variables.
        source_variables: usize,
    },
    /// The supplied model did not satisfy the exact generated CNF.
    InvalidModel,
    /// CNF projection did not satisfy the source ANF system.
    ReplayFailed,
}

/// A clause over source variables in a Boolean-ANF/CNF definitional extension.
///
/// Each pair is a zero-based source-variable index and its required polarity:
/// `true` denotes the positive literal and `false` its negation.
pub type BooleanAnfSourceClause = Vec<(usize, bool)>;

impl From<BooleanAnfError> for BooleanAnfCnfError {
    fn from(value: BooleanAnfError) -> Self {
        Self::Anf(value)
    }
}

impl From<CnfError> for BooleanAnfCnfError {
    fn from(value: CnfError) -> Self {
        Self::Cnf(value)
    }
}

/// Exact CNF plus the source-variable projection required for model replay.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BooleanAnfCnfEncoding {
    formula: CnfFormula,
    source_variables: usize,
}

impl BooleanAnfCnfEncoding {
    /// The deterministic definitional-extension CNF.
    pub fn formula(&self) -> &CnfFormula {
        &self.formula
    }

    /// Add units for a partial assignment of source variables.
    ///
    /// # Errors
    ///
    /// Refuses an index outside the source-variable prefix.
    pub fn formula_with_source_units(
        &self,
        units: &[(usize, bool)],
    ) -> Result<CnfFormula, BooleanAnfCnfError> {
        let mut formula = self.formula.clone();
        for &(index, value) in units {
            if index >= self.source_variables {
                return Err(BooleanAnfCnfError::SourceVariableOutOfRange {
                    variable: index,
                    source_variables: self.source_variables,
                });
            }
            let literal = CnfLit::positive(CnfVar::new(index)?);
            formula.add_clause(CnfClause::new(vec![if value {
                literal
            } else {
                literal.negated()
            }]))?;
        }
        Ok(formula)
    }

    /// Add arbitrary clauses over the projected source-variable prefix.
    ///
    /// This is the checked front door for composing a Boolean-ANF system with
    /// independently justified CNF-side restrictions without depending on the
    /// private variables introduced by the definitional extension.
    ///
    /// # Errors
    ///
    /// Refuses every literal whose index is outside the source-variable
    /// prefix. Empty clauses are retained and therefore make the formula
    /// unsatisfiable.
    pub fn formula_with_source_clauses(
        &self,
        clauses: &[BooleanAnfSourceClause],
    ) -> Result<CnfFormula, BooleanAnfCnfError> {
        let mut formula = self.formula.clone();
        for clause in clauses {
            let literals = clause
                .iter()
                .map(|&(index, positive)| {
                    if index >= self.source_variables {
                        return Err(BooleanAnfCnfError::SourceVariableOutOfRange {
                            variable: index,
                            source_variables: self.source_variables,
                        });
                    }
                    let literal = CnfLit::positive(CnfVar::new(index)?);
                    Ok(if positive { literal } else { literal.negated() })
                })
                .collect::<Result<Vec<_>, BooleanAnfCnfError>>()?;
            formula.add_clause(CnfClause::new(literals))?;
        }
        Ok(formula)
    }

    /// Project a satisfying CNF model and replay every source equation.
    ///
    /// # Errors
    ///
    /// Refuses a wrong-size/non-satisfying model or a failed source replay.
    pub fn lift_source_assignment(
        &self,
        system: &BooleanAnfSystem,
        model: &CnfAssignment,
    ) -> Result<Vec<bool>, BooleanAnfCnfError> {
        if model.satisfies(&self.formula) != Ok(true) {
            return Err(BooleanAnfCnfError::InvalidModel);
        }
        let source = model.values()[..self.source_variables].to_vec();
        if !system.evaluate(&source)? {
            return Err(BooleanAnfCnfError::ReplayFailed);
        }
        Ok(source)
    }
}

#[derive(Debug)]
struct Builder {
    variables: usize,
    clauses: Vec<Vec<(usize, bool)>>,
    limits: BooleanAnfCnfLimits,
}

impl Builder {
    fn variable(&mut self) -> Result<usize, BooleanAnfCnfError> {
        self.variables = self.variables.saturating_add(1);
        if self.variables > self.limits.max_variables {
            return Err(BooleanAnfCnfError::LimitExceeded {
                resource: "variables",
                observed: self.variables,
                limit: self.limits.max_variables,
            });
        }
        Ok(self.variables - 1)
    }

    fn clause(&mut self, literals: &[(usize, bool)]) -> Result<(), BooleanAnfCnfError> {
        self.clauses.push(literals.to_vec());
        if self.clauses.len() > self.limits.max_clauses {
            return Err(BooleanAnfCnfError::LimitExceeded {
                resource: "clauses",
                observed: self.clauses.len(),
                limit: self.limits.max_clauses,
            });
        }
        Ok(())
    }

    fn and_equiv(
        &mut self,
        output: usize,
        left: usize,
        right: usize,
    ) -> Result<(), BooleanAnfCnfError> {
        self.clause(&[(left, true), (right, true), (output, false)])?;
        self.clause(&[(left, false), (output, true)])?;
        self.clause(&[(right, false), (output, true)])
    }

    fn xor_equiv(
        &mut self,
        output: usize,
        left: usize,
        right: usize,
    ) -> Result<(), BooleanAnfCnfError> {
        self.clause(&[(left, true), (right, true), (output, true)])?;
        self.clause(&[(left, false), (right, false), (output, true)])?;
        self.clause(&[(left, false), (right, true), (output, false)])?;
        self.clause(&[(left, true), (right, false), (output, false)])
    }

    fn parity_equals(&mut self, terms: &[usize], value: bool) -> Result<(), BooleanAnfCnfError> {
        let Some((&first, rest)) = terms.split_first() else {
            if value {
                self.clause(&[])?;
            }
            return Ok(());
        };
        let mut parity = first;
        for &term in rest {
            let next = self.variable()?;
            self.xor_equiv(next, parity, term)?;
            parity = next;
        }
        self.clause(&[(parity, !value)])
    }

    fn finish(self) -> Result<CnfFormula, BooleanAnfCnfError> {
        let mut formula = CnfFormula::new(self.variables);
        for clause in self.clauses {
            let literals = clause
                .into_iter()
                .map(|(index, negated)| {
                    let variable = CnfVar::new(index)?;
                    let literal = CnfLit::positive(variable);
                    Ok(if negated { literal.negated() } else { literal })
                })
                .collect::<Result<Vec<_>, BooleanAnfCnfError>>()?;
            formula.add_clause(CnfClause::new(literals))?;
        }
        Ok(formula)
    }
}

/// Lower a conjunction of Boolean polynomial equations to an exact CNF.
///
/// Identical nonlinear monomials share one deterministic conjunction chain.
/// The construction is a definitional extension: projecting any satisfying
/// CNF assignment gives a source solution, and every source solution uniquely
/// extends through the generated gates.
///
/// # Errors
///
/// Refuses a source or generated formula exceeding the explicit limits.
pub fn encode_boolean_anf_cnf(
    system: &BooleanAnfSystem,
    limits: BooleanAnfCnfLimits,
) -> Result<BooleanAnfCnfEncoding, BooleanAnfCnfError> {
    if system.variable_count() > limits.max_variables {
        return Err(BooleanAnfCnfError::LimitExceeded {
            resource: "variables",
            observed: system.variable_count(),
            limit: limits.max_variables,
        });
    }
    let mut builder = Builder {
        variables: system.variable_count(),
        clauses: Vec::new(),
        limits,
    };
    let mut monomial_variables = BTreeMap::<Vec<usize>, usize>::new();
    for equation in system.equations() {
        let mut constant = false;
        let mut terms = Vec::new();
        for monomial in equation.monomials() {
            match monomial {
                [] => constant ^= true,
                [variable] => terms.push(*variable),
                factors => {
                    if factors.len() > limits.max_monomial_degree {
                        return Err(BooleanAnfCnfError::LimitExceeded {
                            resource: "monomial_degree",
                            observed: factors.len(),
                            limit: limits.max_monomial_degree,
                        });
                    }
                    let variable = if let Some(&variable) = monomial_variables.get(factors) {
                        variable
                    } else {
                        let mut product = factors[0];
                        for end in 2..=factors.len() {
                            let prefix = &factors[..end];
                            if let Some(&variable) = monomial_variables.get(prefix) {
                                product = variable;
                            } else {
                                let next = builder.variable()?;
                                builder.and_equiv(next, product, factors[end - 1])?;
                                monomial_variables.insert(prefix.to_vec(), next);
                                product = next;
                            }
                        }
                        product
                    };
                    terms.push(variable);
                }
            }
        }
        builder.parity_equals(&terms, constant)?;
    }
    Ok(BooleanAnfCnfEncoding {
        formula: builder.finish()?,
        source_variables: system.variable_count(),
    })
}

#[cfg(test)]
mod tests {
    use axeyum_cas::boolean_anf::{BooleanAnfLimits, BooleanAnfPolynomial};
    use axeyum_cnf::{ProofSolveOutcome, check_drat, solve_with_drat_proof};

    use super::*;

    fn polynomial(monomials: &[&[usize]], constant: bool) -> BooleanAnfPolynomial {
        let mut result = if constant {
            BooleanAnfPolynomial::one()
        } else {
            BooleanAnfPolynomial::zero()
        };
        for factors in monomials {
            let mut term = BooleanAnfPolynomial::one();
            for &variable in *factors {
                term = term
                    .product(&BooleanAnfPolynomial::variable(variable), 64)
                    .unwrap();
            }
            result.xor_assign(&term);
        }
        result
    }

    #[test]
    fn exhaustive_source_models_equal_projected_cnf_models() {
        let mut system = BooleanAnfSystem::new(3, BooleanAnfLimits::default()).unwrap();
        system
            .add_equation(polynomial(&[&[0, 1], &[2]], true))
            .unwrap();
        system
            .add_equation(polynomial(&[&[0, 1], &[0, 2]], false))
            .unwrap();
        let encoding = encode_boolean_anf_cnf(&system, BooleanAnfCnfLimits::default()).unwrap();
        for source_bits in 0..8 {
            let source = (0..3)
                .map(|bit| ((source_bits >> bit) & 1) != 0)
                .collect::<Vec<_>>();
            let source_sat = system.evaluate(&source).unwrap();
            let auxiliaries = encoding.formula().variable_count() - 3;
            let cnf_sat = (0..1_usize << auxiliaries).any(|packed| {
                let mut assignment = source.clone();
                assignment.extend((0..auxiliaries).map(|bit| ((packed >> bit) & 1) != 0));
                encoding.formula().evaluate(&assignment) == Ok(true)
            });
            assert_eq!(cnf_sat, source_sat, "source_bits={source_bits}");
        }
    }

    #[test]
    fn sat_models_project_and_replay_the_source_system() {
        let mut system = BooleanAnfSystem::new(2, BooleanAnfLimits::default()).unwrap();
        system.add_equation(polynomial(&[&[0, 1]], true)).unwrap();
        let encoding = encode_boolean_anf_cnf(&system, BooleanAnfCnfLimits::default()).unwrap();
        let ProofSolveOutcome::Sat(model) = solve_with_drat_proof(encoding.formula()) else {
            panic!("x0*x1=1 must be satisfiable");
        };
        assert_eq!(
            encoding.lift_source_assignment(&system, &model).unwrap(),
            vec![true, true]
        );
    }

    #[test]
    fn unsat_source_system_has_a_checked_cnf_refutation() {
        let mut system = BooleanAnfSystem::new(1, BooleanAnfLimits::default()).unwrap();
        system
            .add_equation(BooleanAnfPolynomial::variable(0))
            .unwrap();
        system.add_equation(polynomial(&[&[0]], true)).unwrap();
        let encoding = encode_boolean_anf_cnf(&system, BooleanAnfCnfLimits::default()).unwrap();
        let ProofSolveOutcome::Unsat(proof) = solve_with_drat_proof(encoding.formula()) else {
            panic!("x=0 and x=1 must be unsatisfiable");
        };
        assert_eq!(check_drat(encoding.formula(), &proof), Ok(true));
    }

    #[test]
    fn contradictory_source_unit_is_checked_and_out_of_range_is_refused() {
        let mut system = BooleanAnfSystem::new(1, BooleanAnfLimits::default()).unwrap();
        system
            .add_equation(BooleanAnfPolynomial::variable(0))
            .unwrap();
        let encoding = encode_boolean_anf_cnf(&system, BooleanAnfCnfLimits::default()).unwrap();
        let pinned = encoding.formula_with_source_units(&[(0, true)]).unwrap();
        let ProofSolveOutcome::Unsat(proof) = solve_with_drat_proof(&pinned) else {
            panic!("x=0 plus source unit x=1 must be unsatisfiable");
        };
        assert_eq!(check_drat(&pinned, &proof), Ok(true));
        assert!(matches!(
            encoding.formula_with_source_units(&[(1, false)]),
            Err(BooleanAnfCnfError::SourceVariableOutOfRange {
                variable: 1,
                source_variables: 1
            })
        ));
    }

    #[test]
    fn source_clauses_compose_without_exposing_extension_variables() {
        let system = BooleanAnfSystem::new(2, BooleanAnfLimits::default()).unwrap();
        let encoding = encode_boolean_anf_cnf(&system, BooleanAnfCnfLimits::default()).unwrap();
        let restricted = encoding
            .formula_with_source_clauses(&[vec![(0, true), (1, true)]])
            .unwrap();
        assert_eq!(restricted.clauses().len(), 1);
        assert_eq!(restricted.evaluate(&[false, false]), Ok(false));
        assert_eq!(restricted.evaluate(&[true, false]), Ok(true));
        assert!(matches!(
            encoding.formula_with_source_clauses(&[vec![(2, true)]]),
            Err(BooleanAnfCnfError::SourceVariableOutOfRange {
                variable: 2,
                source_variables: 2
            })
        ));
    }

    #[test]
    fn monomial_sharing_is_deterministic_and_limits_fail_closed() {
        let mut system = BooleanAnfSystem::new(3, BooleanAnfLimits::default()).unwrap();
        system
            .add_equation(polynomial(&[&[0, 1, 2]], false))
            .unwrap();
        system
            .add_equation(polynomial(&[&[0, 1, 2], &[0]], false))
            .unwrap();
        let encoding = encode_boolean_anf_cnf(&system, BooleanAnfCnfLimits::default()).unwrap();
        assert_eq!(encoding.formula().variable_count(), 6);
        assert_eq!(
            encoding.formula().to_dimacs(),
            encode_boolean_anf_cnf(&system, BooleanAnfCnfLimits::default())
                .unwrap()
                .formula()
                .to_dimacs()
        );
        assert!(matches!(
            encode_boolean_anf_cnf(
                &system,
                BooleanAnfCnfLimits {
                    max_monomial_degree: 2,
                    ..BooleanAnfCnfLimits::default()
                }
            ),
            Err(BooleanAnfCnfError::LimitExceeded {
                resource: "monomial_degree",
                ..
            })
        ));
    }
}
