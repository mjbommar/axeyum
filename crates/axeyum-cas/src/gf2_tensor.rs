//! Exact checking of rank-one tensor decompositions over `GF(2)`.
//!
//! Search tools may propose a decomposition, but acceptance is a direct
//! coefficient-by-coefficient replay against a separately constructed sparse
//! target tensor.  Supports use zero-based basis indices; repeated indices are
//! rejected instead of being silently normalised.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

/// Version tag for portable decomposition artifacts.
pub const GF2_TENSOR_DECOMPOSITION_SCHEMA: &str = "axeyum.gf2-tensor-decomposition.v1";

/// Admission limits for tensor replay.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Gf2TensorCheckLimits {
    /// Largest dense coefficient volume admitted.
    pub max_coefficients: usize,
    /// Largest number of rank-one summands admitted.
    pub max_terms: usize,
    /// Largest total number of support indices across all summands.
    pub max_support_entries: usize,
}

impl Default for Gf2TensorCheckLimits {
    fn default() -> Self {
        Self {
            max_coefficients: 16 * 1024 * 1024,
            max_terms: 1_000_000,
            max_support_entries: 16 * 1024 * 1024,
        }
    }
}

/// One sparse tensor over `GF(2)`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Gf2Tensor {
    /// Dimensions of the three tensor modes.
    pub dimensions: [usize; 3],
    /// Coordinates whose coefficient is one; all omitted coordinates are zero.
    pub ones: Vec<[usize; 3]>,
}

impl Gf2Tensor {
    /// Construct the structure tensor for full multiplication of polynomials of
    /// degree below `n`: `sum_(i,j<n) a_i tensor b_j tensor c_(i+j)`.
    ///
    /// # Errors
    ///
    /// Returns an error when `n` is zero or dimension arithmetic overflows.
    pub fn full_polynomial_multiplication(n: usize) -> Result<Self, Gf2TensorError> {
        if n == 0 {
            return Err(Gf2TensorError::ZeroDimension { mode: 0 });
        }
        let output = n
            .checked_mul(2)
            .and_then(|value| value.checked_sub(1))
            .ok_or(Gf2TensorError::DimensionOverflow)?;
        let mut ones =
            Vec::with_capacity(n.checked_mul(n).ok_or(Gf2TensorError::DimensionOverflow)?);
        for left in 0..n {
            for right in 0..n {
                ones.push([left, right, left + right]);
            }
        }
        Ok(Self {
            dimensions: [n, n, output],
            ones,
        })
    }

    /// Construct the structure tensor for multiplying an `m x n` matrix by an
    /// `n x p` matrix.
    ///
    /// Row-major basis indices are `a(i,j) = i*n+j`, `b(j,k) = j*p+k`, and
    /// `c(i,k) = i*p+k`. Thus the tensor dimensions are
    /// `[m*n, n*p, m*p]` and its nonzero coefficients are exactly
    /// `(a(i,j), b(j,k), c(i,k))`.
    ///
    /// # Errors
    ///
    /// Returns an error for a zero matrix dimension or arithmetic overflow.
    pub fn matrix_multiplication(m: usize, n: usize, p: usize) -> Result<Self, Gf2TensorError> {
        for (mode, dimension) in [m, n, p].into_iter().enumerate() {
            if dimension == 0 {
                return Err(Gf2TensorError::ZeroDimension { mode });
            }
        }
        let a_dimension = m.checked_mul(n).ok_or(Gf2TensorError::DimensionOverflow)?;
        let b_dimension = n.checked_mul(p).ok_or(Gf2TensorError::DimensionOverflow)?;
        let c_dimension = m.checked_mul(p).ok_or(Gf2TensorError::DimensionOverflow)?;
        let entries = m
            .checked_mul(n)
            .and_then(|value| value.checked_mul(p))
            .ok_or(Gf2TensorError::DimensionOverflow)?;
        let mut ones = Vec::with_capacity(entries);
        for i in 0..m {
            for j in 0..n {
                for k in 0..p {
                    ones.push([i * n + j, j * p + k, i * p + k]);
                }
            }
        }
        Ok(Self {
            dimensions: [a_dimension, b_dimension, c_dimension],
            ones,
        })
    }

    /// Validate and expand this sparse tensor in lexicographic dense order.
    ///
    /// # Errors
    ///
    /// Refuses zero dimensions, arithmetic overflow, duplicate/out-of-range
    /// coordinates, or a coefficient volume above `max_coefficients`.
    pub fn dense_coefficients(&self, max_coefficients: usize) -> Result<Vec<bool>, Gf2TensorError> {
        for (mode, &dimension) in self.dimensions.iter().enumerate() {
            if dimension == 0 {
                return Err(Gf2TensorError::ZeroDimension { mode });
            }
        }
        let volume = self
            .dimensions
            .into_iter()
            .try_fold(1_usize, usize::checked_mul)
            .ok_or(Gf2TensorError::DimensionOverflow)?;
        if volume > max_coefficients {
            return Err(Gf2TensorError::LimitExceeded {
                resource: "coefficients",
                observed: volume,
                limit: max_coefficients,
            });
        }
        expected_coefficients(self, volume)
    }
}

/// A rank-one tensor represented by the supports of its three factor vectors.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Gf2RankOneTerm {
    /// Nonzero coordinates in the first factor.
    pub a: Vec<usize>,
    /// Nonzero coordinates in the second factor.
    pub b: Vec<usize>,
    /// Nonzero coordinates in the third factor.
    pub c: Vec<usize>,
}

/// Portable claimed decomposition artifact.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Gf2TensorDecomposition {
    /// Must equal [`GF2_TENSOR_DECOMPOSITION_SCHEMA`].
    pub schema: String,
    /// Dimensions bound into the claimed decomposition.
    pub dimensions: [usize; 3],
    /// Rank-one summands whose XOR is claimed to equal the target.
    pub terms: Vec<Gf2RankOneTerm>,
}

/// A completed coefficient replay.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Gf2TensorCheck {
    /// Every coefficient matched.
    Verified {
        /// Number of rank-one terms.
        rank: usize,
        /// Number of target coefficients replayed.
        coefficients_checked: usize,
    },
    /// The first lexicographic coefficient mismatch.
    Failed {
        /// Mismatching tensor coordinate.
        coordinate: [usize; 3],
        /// Target coefficient.
        expected: bool,
        /// Coefficient obtained from the decomposition.
        observed: bool,
    },
}

/// Malformed or inadmissibly large input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Gf2TensorError {
    /// Artifact version is not supported.
    UnsupportedSchema(String),
    /// Target and decomposition dimensions differ.
    DimensionMismatch {
        /// Dimensions of the target.
        target: [usize; 3],
        /// Dimensions declared by the decomposition.
        decomposition: [usize; 3],
    },
    /// A tensor mode has dimension zero.
    ZeroDimension {
        /// Zero-dimensional mode.
        mode: usize,
    },
    /// Dimension arithmetic overflowed `usize`.
    DimensionOverflow,
    /// An admission limit was exceeded before replay.
    LimitExceeded {
        /// Stable name of the exceeded limit.
        resource: &'static str,
        /// Observed value.
        observed: usize,
        /// Configured maximum.
        limit: usize,
    },
    /// A sparse support contains an out-of-range index.
    SupportOutOfRange {
        /// Rank-one term number, or `None` for the target tensor.
        term: Option<usize>,
        /// Tensor mode.
        mode: usize,
        /// Bad index.
        index: usize,
        /// Dimension of that mode.
        dimension: usize,
    },
    /// A sparse support repeats an index or target coordinate.
    DuplicateEntry {
        /// Rank-one term number, or `None` for the target tensor.
        term: Option<usize>,
        /// Tensor mode for a support duplicate; `None` for a target-coordinate duplicate.
        mode: Option<usize>,
    },
}

fn dense_index(dimensions: [usize; 3], coordinate: [usize; 3]) -> usize {
    (coordinate[0] * dimensions[1] + coordinate[1]) * dimensions[2] + coordinate[2]
}

fn validate_support(
    support: &[usize],
    dimension: usize,
    term: usize,
    mode: usize,
) -> Result<(), Gf2TensorError> {
    let mut seen = BTreeSet::new();
    for &index in support {
        if index >= dimension {
            return Err(Gf2TensorError::SupportOutOfRange {
                term: Some(term),
                mode,
                index,
                dimension,
            });
        }
        if !seen.insert(index) {
            return Err(Gf2TensorError::DuplicateEntry {
                term: Some(term),
                mode: Some(mode),
            });
        }
    }
    Ok(())
}

fn expected_coefficients(target: &Gf2Tensor, volume: usize) -> Result<Vec<bool>, Gf2TensorError> {
    let mut expected = vec![false; volume];
    for &coordinate in &target.ones {
        for (mode, &index) in coordinate.iter().enumerate() {
            if index >= target.dimensions[mode] {
                return Err(Gf2TensorError::SupportOutOfRange {
                    term: None,
                    mode,
                    index,
                    dimension: target.dimensions[mode],
                });
            }
        }
        let index = dense_index(target.dimensions, coordinate);
        if expected[index] {
            return Err(Gf2TensorError::DuplicateEntry {
                term: None,
                mode: None,
            });
        }
        expected[index] = true;
    }
    Ok(expected)
}

/// Check a claimed rank-one decomposition by exact coefficient replay.
///
/// # Errors
///
/// Returns an error for version or dimension mismatch, malformed sparse input,
/// arithmetic overflow, or work beyond an explicit admission limit.
pub fn check_gf2_tensor_decomposition(
    target: &Gf2Tensor,
    decomposition: &Gf2TensorDecomposition,
    limits: Gf2TensorCheckLimits,
) -> Result<Gf2TensorCheck, Gf2TensorError> {
    if decomposition.schema != GF2_TENSOR_DECOMPOSITION_SCHEMA {
        return Err(Gf2TensorError::UnsupportedSchema(
            decomposition.schema.clone(),
        ));
    }
    if target.dimensions != decomposition.dimensions {
        return Err(Gf2TensorError::DimensionMismatch {
            target: target.dimensions,
            decomposition: decomposition.dimensions,
        });
    }
    for (mode, &dimension) in target.dimensions.iter().enumerate() {
        if dimension == 0 {
            return Err(Gf2TensorError::ZeroDimension { mode });
        }
    }
    let volume = target
        .dimensions
        .into_iter()
        .try_fold(1_usize, usize::checked_mul)
        .ok_or(Gf2TensorError::DimensionOverflow)?;
    if volume > limits.max_coefficients {
        return Err(Gf2TensorError::LimitExceeded {
            resource: "coefficients",
            observed: volume,
            limit: limits.max_coefficients,
        });
    }
    if decomposition.terms.len() > limits.max_terms {
        return Err(Gf2TensorError::LimitExceeded {
            resource: "terms",
            observed: decomposition.terms.len(),
            limit: limits.max_terms,
        });
    }
    let support_entries = decomposition
        .terms
        .iter()
        .try_fold(0_usize, |total, term| {
            total
                .checked_add(term.a.len())
                .and_then(|value| value.checked_add(term.b.len()))
                .and_then(|value| value.checked_add(term.c.len()))
        })
        .ok_or(Gf2TensorError::DimensionOverflow)?;
    if support_entries > limits.max_support_entries {
        return Err(Gf2TensorError::LimitExceeded {
            resource: "support_entries",
            observed: support_entries,
            limit: limits.max_support_entries,
        });
    }

    let expected = expected_coefficients(target, volume)?;

    let mut observed = vec![false; volume];
    for (term_index, term) in decomposition.terms.iter().enumerate() {
        validate_support(&term.a, target.dimensions[0], term_index, 0)?;
        validate_support(&term.b, target.dimensions[1], term_index, 1)?;
        validate_support(&term.c, target.dimensions[2], term_index, 2)?;
        for &a in &term.a {
            for &b in &term.b {
                for &c in &term.c {
                    let index = dense_index(target.dimensions, [a, b, c]);
                    observed[index] = !observed[index];
                }
            }
        }
    }

    for (index, (&expected_coefficient, &observed_coefficient)) in
        expected.iter().zip(&observed).enumerate()
    {
        if expected_coefficient != observed_coefficient {
            let ab = index / target.dimensions[2];
            return Ok(Gf2TensorCheck::Failed {
                coordinate: [
                    ab / target.dimensions[1],
                    ab % target.dimensions[1],
                    index % target.dimensions[2],
                ],
                expected: expected_coefficient,
                observed: observed_coefficient,
            });
        }
    }
    Ok(Gf2TensorCheck::Verified {
        rank: decomposition.terms.len(),
        coefficients_checked: volume,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn schoolbook(n: usize) -> Gf2TensorDecomposition {
        let mut terms = Vec::new();
        for a in 0..n {
            for b in 0..n {
                terms.push(Gf2RankOneTerm {
                    a: vec![a],
                    b: vec![b],
                    c: vec![a + b],
                });
            }
        }
        Gf2TensorDecomposition {
            schema: GF2_TENSOR_DECOMPOSITION_SCHEMA.to_owned(),
            dimensions: [n, n, 2 * n - 1],
            terms,
        }
    }

    #[test]
    fn schoolbook_full_multiplication_replays() {
        let target = Gf2Tensor::full_polynomial_multiplication(3).unwrap();
        assert_eq!(
            check_gf2_tensor_decomposition(
                &target,
                &schoolbook(3),
                Gf2TensorCheckLimits::default(),
            ),
            Ok(Gf2TensorCheck::Verified {
                rank: 9,
                coefficients_checked: 45,
            })
        );
    }

    #[test]
    fn one_mutated_factor_fails_at_the_first_coefficient() {
        let target = Gf2Tensor::full_polynomial_multiplication(2).unwrap();
        let mut decomposition = schoolbook(2);
        decomposition.terms[0].c[0] = 1;
        assert_eq!(
            check_gf2_tensor_decomposition(
                &target,
                &decomposition,
                Gf2TensorCheckLimits::default(),
            ),
            Ok(Gf2TensorCheck::Failed {
                coordinate: [0, 0, 0],
                expected: true,
                observed: false,
            })
        );
    }

    #[test]
    fn duplicate_support_is_rejected_not_cancelled() {
        let target = Gf2Tensor::full_polynomial_multiplication(1).unwrap();
        let mut decomposition = schoolbook(1);
        decomposition.terms[0].a.push(0);
        assert_eq!(
            check_gf2_tensor_decomposition(
                &target,
                &decomposition,
                Gf2TensorCheckLimits::default(),
            ),
            Err(Gf2TensorError::DuplicateEntry {
                term: Some(0),
                mode: Some(0),
            })
        );
    }

    #[test]
    fn resource_limit_declines_before_allocating() {
        let target = Gf2Tensor::full_polynomial_multiplication(3).unwrap();
        let limits = Gf2TensorCheckLimits {
            max_coefficients: 44,
            ..Gf2TensorCheckLimits::default()
        };
        assert_eq!(
            check_gf2_tensor_decomposition(&target, &schoolbook(3), limits),
            Err(Gf2TensorError::LimitExceeded {
                resource: "coefficients",
                observed: 45,
                limit: 44,
            })
        );
    }

    /// Karatsuba's rank-3 decomposition of the degree-2 (`n=2`) full
    /// multiplication tensor over `GF(2)`: with `m0 = a0*b0`,
    /// `m1 = (a0+a1)*(b0+b1)`, `m2 = a1*b1`, the product coefficients are
    /// `c0 = m0`, `c1 = m0+m1+m2`, `c2 = m2` -- three bilinear multiplications
    /// where `schoolbook(2)` above uses four (`n^2` for `n=2`).  Each rank-one
    /// term below is one `m_i`: its `c` support is exactly the set of output
    /// coefficients that XOR in that multiplication's value.
    fn karatsuba_degree_2_decomposition() -> Gf2TensorDecomposition {
        Gf2TensorDecomposition {
            schema: GF2_TENSOR_DECOMPOSITION_SCHEMA.to_owned(),
            dimensions: [2, 2, 3],
            terms: vec![
                Gf2RankOneTerm {
                    a: vec![0],
                    b: vec![0],
                    c: vec![0, 1],
                },
                Gf2RankOneTerm {
                    a: vec![0, 1],
                    b: vec![0, 1],
                    c: vec![1],
                },
                Gf2RankOneTerm {
                    a: vec![1],
                    b: vec![1],
                    c: vec![1, 2],
                },
            ],
        }
    }

    #[test]
    fn karatsuba_degree_2_replays_at_rank_three() {
        let target = Gf2Tensor::full_polynomial_multiplication(2).unwrap();
        assert_eq!(
            check_gf2_tensor_decomposition(
                &target,
                &karatsuba_degree_2_decomposition(),
                Gf2TensorCheckLimits::default(),
            ),
            Ok(Gf2TensorCheck::Verified {
                rank: 3,
                coefficients_checked: 12,
            })
        );
    }

    /// Negative control: drop the cross term `m1`, leaving only `m0` and
    /// `m2`. The remaining pair no longer reconstructs `c1 = m0+m1+m2`, and
    /// the checker must name the exact coordinate and both values rather than
    /// merely declining.
    #[test]
    fn karatsuba_degree_2_dropped_cross_term_is_rejected() {
        let target = Gf2Tensor::full_polynomial_multiplication(2).unwrap();
        let mut decomposition = karatsuba_degree_2_decomposition();
        decomposition.terms.remove(1);
        assert_eq!(
            check_gf2_tensor_decomposition(
                &target,
                &decomposition,
                Gf2TensorCheckLimits::default(),
            ),
            Ok(Gf2TensorCheck::Failed {
                coordinate: [0, 0, 1],
                expected: false,
                observed: true,
            })
        );
    }

    #[test]
    fn matrix_multiplication_uses_row_major_basis_indices() {
        let target = Gf2Tensor::matrix_multiplication(2, 3, 4).unwrap();
        assert_eq!(target.dimensions, [6, 12, 8]);
        assert_eq!(target.ones.len(), 24);
        assert_eq!(target.ones[0], [0, 0, 0]);
        assert_eq!(target.ones[3], [0, 3, 3]);
        assert_eq!(target.ones[4], [1, 4, 0]);
        assert_eq!(target.ones[23], [5, 11, 7]);
        let dense = target.dense_coefficients(576).unwrap();
        assert_eq!(dense.iter().filter(|&&coefficient| coefficient).count(), 24);
    }
}
