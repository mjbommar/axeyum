//! Deterministic weighted-at-most constraints over an existing CNF.
//!
//! The encoding is a capped dynamic program.  Layer `i` carries exactly one
//! state for the accumulated weight of the first `i` literals, with every sum
//! above the requested bound merged into one overflow state.  Transition
//! implications cover both values of each input literal; exactly-one state
//! constraints make the extension functional.  The final overflow state is
//! forbidden.

use crate::{CnfClause, CnfError, CnfFormula, CnfLit, CnfVar};

/// Stable construction limits for weighted CNF composition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WeightedAtMostLimits {
    /// Maximum auxiliary state variables.
    pub max_auxiliary_variables: usize,
    /// Maximum clauses added to the source formula.
    pub max_added_clauses: usize,
    /// Maximum admitted bound; state width is `bound + 2`.
    pub max_bound: u64,
}

impl Default for WeightedAtMostLimits {
    fn default() -> Self {
        Self {
            max_auxiliary_variables: 1_000_000,
            max_added_clauses: 10_000_000,
            max_bound: 100_000,
        }
    }
}

/// Invalid literals, arithmetic overflow, or an exceeded construction limit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WeightedAtMostError {
    /// A weighted literal references a variable outside the source formula.
    SourceVariableOutOfRange {
        /// Offending zero-based variable index.
        variable: usize,
        /// Source formula variable count.
        source_variables: usize,
    },
    /// A stable construction ceiling was exceeded.
    LimitExceeded {
        /// Resource name.
        resource: &'static str,
        /// First value known to exceed the ceiling.
        observed: usize,
        /// Configured ceiling.
        limit: usize,
    },
    /// CNF construction failed.
    Cnf(CnfError),
    /// A supplied full assignment does not satisfy the composed formula.
    InvalidModel,
}

impl From<CnfError> for WeightedAtMostError {
    fn from(value: CnfError) -> Self {
        Self::Cnf(value)
    }
}

/// Source CNF conjoined with a weighted-at-most definitional extension.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WeightedAtMostEncoding {
    formula: CnfFormula,
    source_variables: usize,
}

impl WeightedAtMostEncoding {
    /// The composed deterministic CNF.
    pub fn formula(&self) -> &CnfFormula {
        &self.formula
    }

    /// Project a full satisfying model to the source formula's variables.
    ///
    /// # Errors
    ///
    /// Refuses a model that does not satisfy the composed formula.
    pub fn project_source_model(&self, values: &[bool]) -> Result<Vec<bool>, WeightedAtMostError> {
        if !self.formula.evaluate(values)? {
            return Err(WeightedAtMostError::InvalidModel);
        }
        Ok(values[..self.source_variables].to_vec())
    }
}

fn add_clause(
    formula: &mut CnfFormula,
    added: &mut usize,
    limit: usize,
    lits: Vec<CnfLit>,
) -> Result<(), WeightedAtMostError> {
    *added = added.saturating_add(1);
    if *added > limit {
        return Err(WeightedAtMostError::LimitExceeded {
            resource: "added_clauses",
            observed: *added,
            limit,
        });
    }
    formula.add_clause(CnfClause::new(lits))?;
    Ok(())
}

fn constrain_state_layers(
    formula: &mut CnfFormula,
    states: &[Vec<CnfVar>],
    added: &mut usize,
    limit: usize,
) -> Result<(), WeightedAtMostError> {
    for layer in states {
        add_clause(
            formula,
            added,
            limit,
            layer.iter().copied().map(CnfLit::positive).collect(),
        )?;
        for left in 0..layer.len() {
            for right in left + 1..layer.len() {
                add_clause(
                    formula,
                    added,
                    limit,
                    vec![
                        CnfLit::positive(layer[left]).negated(),
                        CnfLit::positive(layer[right]).negated(),
                    ],
                )?;
            }
        }
    }
    Ok(())
}

fn constrain_transitions(
    formula: &mut CnfFormula,
    states: &[Vec<CnfVar>],
    terms: &[(CnfLit, u64)],
    bound: u64,
    added: &mut usize,
    limit: usize,
) -> Result<(), WeightedAtMostError> {
    let overflow = states[0].len() - 1;
    for (index, &(literal, weight)) in terms.iter().enumerate() {
        for state in 0..states[0].len() {
            let weighted = u64::try_from(state)
                .unwrap_or(u64::MAX)
                .saturating_add(weight);
            let next = usize::try_from(weighted.min(bound + 1)).unwrap_or(overflow);
            let previous = CnfLit::positive(states[index][state]);
            add_clause(
                formula,
                added,
                limit,
                vec![
                    previous.negated(),
                    literal.negated(),
                    CnfLit::positive(states[index + 1][next]),
                ],
            )?;
            add_clause(
                formula,
                added,
                limit,
                vec![
                    previous.negated(),
                    literal,
                    CnfLit::positive(states[index + 1][state]),
                ],
            )?;
        }
    }
    Ok(())
}

/// Conjoin `sum(weight_i * literal_i) <= bound` with `source`.
///
/// Zero-weight literals are ignored. Every satisfying source assignment whose
/// weighted sum is within the bound extends uniquely through the state layers;
/// every satisfying composed assignment projects to such a source assignment.
///
/// # Errors
///
/// Refuses out-of-range source literals, arithmetic overflow, or a construction
/// exceeding the explicit limits.
pub fn encode_weighted_at_most(
    source: &CnfFormula,
    terms: &[(CnfLit, u64)],
    bound: u64,
    limits: WeightedAtMostLimits,
) -> Result<WeightedAtMostEncoding, WeightedAtMostError> {
    if bound > limits.max_bound {
        return Err(WeightedAtMostError::LimitExceeded {
            resource: "bound",
            observed: usize::try_from(bound).unwrap_or(usize::MAX),
            limit: usize::try_from(limits.max_bound).unwrap_or(usize::MAX),
        });
    }
    for &(literal, _) in terms {
        if literal.var().index() >= source.variable_count() {
            return Err(WeightedAtMostError::SourceVariableOutOfRange {
                variable: literal.var().index(),
                source_variables: source.variable_count(),
            });
        }
    }
    let terms: Vec<(CnfLit, u64)> = terms
        .iter()
        .copied()
        .filter(|(_, weight)| *weight != 0)
        .collect();
    let state_count_u64 = bound
        .checked_add(2)
        .ok_or(WeightedAtMostError::LimitExceeded {
            resource: "bound",
            observed: usize::MAX,
            limit: usize::try_from(limits.max_bound).unwrap_or(usize::MAX),
        })?;
    let state_count =
        usize::try_from(state_count_u64).map_err(|_| WeightedAtMostError::LimitExceeded {
            resource: "state_count",
            observed: usize::MAX,
            limit: limits.max_auxiliary_variables,
        })?;
    let layers = terms.len().saturating_add(1);
    let auxiliary = layers.saturating_mul(state_count);
    if auxiliary > limits.max_auxiliary_variables {
        return Err(WeightedAtMostError::LimitExceeded {
            resource: "auxiliary_variables",
            observed: auxiliary,
            limit: limits.max_auxiliary_variables,
        });
    }
    let total_variables = source.variable_count().saturating_add(auxiliary);
    let mut formula = CnfFormula::new(total_variables);
    for clause in source.clauses() {
        formula.add_clause(clause.clone())?;
    }
    let mut added = 0;
    let states = (0..layers)
        .map(|layer| {
            (0..state_count)
                .map(|state| CnfVar::new(source.variable_count() + layer * state_count + state))
                .collect::<Result<Vec<_>, CnfError>>()
        })
        .collect::<Result<Vec<_>, CnfError>>()?;
    constrain_state_layers(&mut formula, &states, &mut added, limits.max_added_clauses)?;
    add_clause(
        &mut formula,
        &mut added,
        limits.max_added_clauses,
        vec![CnfLit::positive(states[0][0])],
    )?;
    for &state in &states[0][1..] {
        add_clause(
            &mut formula,
            &mut added,
            limits.max_added_clauses,
            vec![CnfLit::positive(state).negated()],
        )?;
    }
    let overflow = state_count - 1;
    constrain_transitions(
        &mut formula,
        &states,
        &terms,
        bound,
        &mut added,
        limits.max_added_clauses,
    )?;
    add_clause(
        &mut formula,
        &mut added,
        limits.max_added_clauses,
        vec![CnfLit::positive(states[layers - 1][overflow]).negated()],
    )?;
    Ok(WeightedAtMostEncoding {
        formula,
        source_variables: source.variable_count(),
    })
}

#[cfg(test)]
mod tests {
    use crate::{ProofSolveOutcome, solve_with_drat_proof};

    use super::*;

    #[test]
    fn exhaustive_projection_matches_weighted_sum() {
        let source = CnfFormula::new(3);
        let terms = [
            (CnfLit::positive(CnfVar::new(0).unwrap()), 1),
            (CnfLit::positive(CnfVar::new(1).unwrap()), 2),
            (CnfLit::positive(CnfVar::new(2).unwrap()).negated(), 3),
        ];
        let encoding =
            encode_weighted_at_most(&source, &terms, 3, WeightedAtMostLimits::default()).unwrap();
        for packed in 0..8 {
            let source_values: Vec<bool> = (0..3).map(|bit| ((packed >> bit) & 1) != 0).collect();
            let expected = u64::from(source_values[0])
                + 2 * u64::from(source_values[1])
                + 3 * u64::from(!source_values[2])
                <= 3;
            let mut pinned = encoding.formula().clone();
            for (index, value) in source_values.iter().copied().enumerate() {
                let literal = CnfLit::positive(CnfVar::new(index).unwrap());
                pinned
                    .add_clause(CnfClause::new(vec![if value {
                        literal
                    } else {
                        literal.negated()
                    }]))
                    .unwrap();
            }
            let observed = matches!(solve_with_drat_proof(&pinned), ProofSolveOutcome::Sat(_));
            assert_eq!(observed, expected, "source assignment {packed:03b}");
        }
    }

    #[test]
    fn checked_refutation_and_limits_fail_closed() {
        let x = CnfVar::new(0).unwrap();
        let mut source = CnfFormula::new(1);
        source
            .add_clause(CnfClause::new(vec![CnfLit::positive(x)]))
            .unwrap();
        let encoding = encode_weighted_at_most(
            &source,
            &[(CnfLit::positive(x), 4)],
            3,
            WeightedAtMostLimits::default(),
        )
        .unwrap();
        let ProofSolveOutcome::Unsat(proof) = solve_with_drat_proof(encoding.formula()) else {
            panic!("forced weight four exceeds bound three");
        };
        assert_eq!(
            crate::check_drat_backward(encoding.formula(), &proof),
            Ok(true)
        );
        assert!(matches!(
            encode_weighted_at_most(
                &source,
                &[(CnfLit::positive(CnfVar::new(1).unwrap()), 1)],
                1,
                WeightedAtMostLimits::default()
            ),
            Err(WeightedAtMostError::SourceVariableOutOfRange { .. })
        ));
    }
}
