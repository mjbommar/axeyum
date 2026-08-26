//! Canonical multivariate Boolean polynomials and ANF interchange.
//!
//! Variables range over `GF(2)` with `x² = x`. A polynomial is a sorted set of
//! square-free monomials: symmetric difference is addition, and multiplication
//! unions variable sets before cancelling duplicate products. This compact
//! representation is suitable for algebraic synthesis front ends and is
//! independent of any SAT or computer-algebra backend.

use std::collections::BTreeSet;

/// A stable resource policy for Boolean ANF construction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BooleanAnfLimits {
    /// Largest admitted variable index plus one.
    pub max_variables: usize,
    /// Largest admitted monomial population in one polynomial.
    pub max_monomials_per_polynomial: usize,
    /// Largest admitted equation count in a system.
    pub max_equations: usize,
    /// Largest admitted sum of equation monomial counts.
    pub max_total_monomials: usize,
}

impl Default for BooleanAnfLimits {
    fn default() -> Self {
        Self {
            max_variables: 5_000_000,
            max_monomials_per_polynomial: 5_000_000,
            max_equations: 25_000_000,
            max_total_monomials: 25_000_000,
        }
    }
}

/// A malformed or resource-inadmissible Boolean ANF operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BooleanAnfError {
    /// A variable lies outside the declared system domain.
    VariableOutOfRange {
        /// Variable index.
        variable: usize,
        /// Declared variable count.
        variable_count: usize,
    },
    /// A stable construction ceiling was exceeded.
    LimitExceeded {
        /// Resource name.
        resource: &'static str,
        /// First value known to exceed the limit.
        observed: usize,
        /// Configured limit.
        limit: usize,
    },
}

/// A canonical square-free polynomial over `GF(2)`.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct BooleanAnfPolynomial {
    monomials: BTreeSet<Vec<usize>>,
}

impl BooleanAnfPolynomial {
    /// The zero polynomial.
    pub fn zero() -> Self {
        Self::default()
    }

    /// The constant-one polynomial.
    pub fn one() -> Self {
        Self {
            monomials: BTreeSet::from([Vec::new()]),
        }
    }

    /// A single variable.
    pub fn variable(variable: usize) -> Self {
        Self {
            monomials: BTreeSet::from([vec![variable]]),
        }
    }

    /// Number of nonzero monomials.
    pub fn monomial_count(&self) -> usize {
        self.monomials.len()
    }

    /// Canonical square-free monomials in lexicographic factor order.
    ///
    /// An empty factor slice is the constant-one monomial. The outer iterator
    /// is deterministic because the representation is a [`BTreeSet`].
    pub fn monomials(&self) -> impl ExactSizeIterator<Item = &[usize]> {
        self.monomials.iter().map(Vec::as_slice)
    }

    /// Whether this is identically zero.
    pub fn is_zero(&self) -> bool {
        self.monomials.is_empty()
    }

    /// Add another polynomial in place (symmetric difference).
    pub fn xor_assign(&mut self, other: &Self) {
        for monomial in &other.monomials {
            if !self.monomials.remove(monomial) {
                self.monomials.insert(monomial.clone());
            }
        }
    }

    /// Add one to this polynomial.
    pub fn toggle_constant(&mut self) {
        let constant = Vec::new();
        if !self.monomials.remove(&constant) {
            self.monomials.insert(constant);
        }
    }

    /// Multiply in the Boolean quotient ring, refusing monomial explosion.
    ///
    /// # Errors
    ///
    /// Returns [`BooleanAnfError::LimitExceeded`] when the canonical product
    /// grows beyond `max_monomials`.
    pub fn product(&self, other: &Self, max_monomials: usize) -> Result<Self, BooleanAnfError> {
        let mut result = BTreeSet::new();
        for left in &self.monomials {
            for right in &other.monomials {
                let mut monomial = left.clone();
                monomial.extend(right);
                monomial.sort_unstable();
                monomial.dedup();
                if !result.remove(&monomial) {
                    result.insert(monomial);
                    if result.len() > max_monomials {
                        return Err(BooleanAnfError::LimitExceeded {
                            resource: "monomials_per_polynomial",
                            observed: result.len(),
                            limit: max_monomials,
                        });
                    }
                }
            }
        }
        Ok(Self { monomials: result })
    }

    /// Evaluate under a complete Boolean assignment.
    ///
    /// # Errors
    ///
    /// Returns [`BooleanAnfError::VariableOutOfRange`] when the assignment does
    /// not cover a variable occurring in this polynomial.
    pub fn evaluate(&self, assignment: &[bool]) -> Result<bool, BooleanAnfError> {
        let mut value = false;
        for monomial in &self.monomials {
            let mut term = true;
            for &variable in monomial {
                let Some(&assigned) = assignment.get(variable) else {
                    return Err(BooleanAnfError::VariableOutOfRange {
                        variable,
                        variable_count: assignment.len(),
                    });
                };
                term &= assigned;
            }
            value ^= term;
        }
        Ok(value)
    }

    fn max_variable(&self) -> Option<usize> {
        self.monomials
            .iter()
            .flat_map(|monomial| monomial.iter().copied())
            .max()
    }

    fn write_bosphorus(&self, output: &mut String) {
        if self.is_zero() {
            output.push('0');
            return;
        }
        for (index, monomial) in self.monomials.iter().enumerate() {
            if index != 0 {
                output.push_str(" + ");
            }
            if monomial.is_empty() {
                output.push('1');
            } else {
                for (factor, variable) in monomial.iter().enumerate() {
                    if factor != 0 {
                        output.push('*');
                    }
                    output.push_str("x(");
                    output.push_str(&variable.to_string());
                    output.push(')');
                }
            }
        }
    }

    /// Serialize one polynomial in Bosphorus's ANF expression syntax.
    pub fn to_bosphorus(&self) -> String {
        let mut output = String::new();
        self.write_bosphorus(&mut output);
        output
    }
}

/// A conjunction of Boolean polynomial equations `p = 0`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BooleanAnfSystem {
    variable_count: usize,
    equations: Vec<BooleanAnfPolynomial>,
    total_monomials: usize,
    limits: BooleanAnfLimits,
}

impl BooleanAnfSystem {
    /// Create an empty system over variables `x(0)..x(variable_count-1)`.
    ///
    /// # Errors
    ///
    /// Returns [`BooleanAnfError::LimitExceeded`] when `variable_count` exceeds
    /// the configured ceiling.
    pub fn new(variable_count: usize, limits: BooleanAnfLimits) -> Result<Self, BooleanAnfError> {
        if variable_count > limits.max_variables {
            return Err(BooleanAnfError::LimitExceeded {
                resource: "variables",
                observed: variable_count,
                limit: limits.max_variables,
            });
        }
        Ok(Self {
            variable_count,
            equations: Vec::new(),
            total_monomials: 0,
            limits,
        })
    }

    /// Number of declared variables.
    pub fn variable_count(&self) -> usize {
        self.variable_count
    }

    /// Equations in deterministic insertion order.
    pub fn equations(&self) -> &[BooleanAnfPolynomial] {
        &self.equations
    }

    /// Add `polynomial = 0`, enforcing the declared domain and resource policy.
    ///
    /// # Errors
    ///
    /// Returns [`BooleanAnfError::VariableOutOfRange`] for an undeclared
    /// variable, or [`BooleanAnfError::LimitExceeded`] for any size ceiling.
    pub fn add_equation(
        &mut self,
        polynomial: BooleanAnfPolynomial,
    ) -> Result<(), BooleanAnfError> {
        if let Some(variable) = polynomial
            .max_variable()
            .filter(|&variable| variable >= self.variable_count)
        {
            return Err(BooleanAnfError::VariableOutOfRange {
                variable,
                variable_count: self.variable_count,
            });
        }
        if polynomial.monomial_count() > self.limits.max_monomials_per_polynomial {
            return Err(BooleanAnfError::LimitExceeded {
                resource: "monomials_per_polynomial",
                observed: polynomial.monomial_count(),
                limit: self.limits.max_monomials_per_polynomial,
            });
        }
        let equations = self.equations.len().saturating_add(1);
        if equations > self.limits.max_equations {
            return Err(BooleanAnfError::LimitExceeded {
                resource: "equations",
                observed: equations,
                limit: self.limits.max_equations,
            });
        }
        let total = self
            .total_monomials
            .saturating_add(polynomial.monomial_count());
        if total > self.limits.max_total_monomials {
            return Err(BooleanAnfError::LimitExceeded {
                resource: "total_monomials",
                observed: total,
                limit: self.limits.max_total_monomials,
            });
        }
        self.total_monomials = total;
        self.equations.push(polynomial);
        Ok(())
    }

    /// Serialize in Bosphorus's portable line-oriented ANF syntax.
    pub fn to_bosphorus_anf(&self) -> String {
        let mut output = String::new();
        for equation in &self.equations {
            equation.write_bosphorus(&mut output);
            output.push('\n');
        }
        output
    }

    /// Check every equation under a complete assignment.
    ///
    /// # Errors
    ///
    /// Returns [`BooleanAnfError::VariableOutOfRange`] unless the assignment
    /// has exactly the declared width.
    pub fn evaluate(&self, assignment: &[bool]) -> Result<bool, BooleanAnfError> {
        if assignment.len() != self.variable_count {
            return Err(BooleanAnfError::VariableOutOfRange {
                variable: assignment.len().min(self.variable_count),
                variable_count: self.variable_count,
            });
        }
        for equation in &self.equations {
            if equation.evaluate(assignment)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn boolean_product_is_square_free_and_cancels() {
        let x = BooleanAnfPolynomial::variable(0);
        let mut x_plus_y = x.clone();
        x_plus_y.xor_assign(&BooleanAnfPolynomial::variable(1));
        let product = x.product(&x_plus_y, 10).unwrap();
        assert_eq!(product.evaluate(&[true, false]), Ok(true));
        assert_eq!(product.evaluate(&[true, true]), Ok(false));
        assert_eq!(product.to_bosphorus(), "x(0) + x(0)*x(1)");
    }

    #[test]
    fn system_round_trips_bosphorus_syntax_and_checks_assignments() {
        let mut equation = BooleanAnfPolynomial::variable(0);
        equation.xor_assign(&BooleanAnfPolynomial::variable(1));
        equation.toggle_constant();
        let mut system = BooleanAnfSystem::new(2, BooleanAnfLimits::default()).unwrap();
        system.add_equation(equation).unwrap();
        assert_eq!(system.to_bosphorus_anf(), "1 + x(0) + x(1)\n");
        assert_eq!(system.evaluate(&[false, true]), Ok(true));
        assert_eq!(system.evaluate(&[false, false]), Ok(false));
    }
}
