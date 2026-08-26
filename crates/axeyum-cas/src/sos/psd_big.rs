//! Resource-bounded exact PSD checking over arbitrary-precision rationals.
//!
//! This is the wide counterpart of [`super::psd::is_psd`].  It uses the same
//! symmetric `LDL^T` elimination rule but cannot overflow: instead, explicit
//! dimension, input-size, and intermediate-size limits turn excessive work into
//! a decline with no mathematical verdict.

use num_rational::BigRational;
use num_traits::{Signed, Zero};

/// Admission limits for arbitrary-precision PSD checking.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BigPsdLimits {
    /// Largest admitted matrix dimension.
    pub max_dimension: usize,
    /// Largest total encoded numerator/denominator byte count in the input.
    pub max_input_bytes: usize,
    /// Largest numerator or denominator bit length admitted during elimination.
    pub max_intermediate_bits: usize,
}

impl Default for BigPsdLimits {
    fn default() -> Self {
        Self {
            max_dimension: 2_048,
            max_input_bytes: 512 * 1024 * 1024,
            max_intermediate_bits: 1_000_000,
        }
    }
}

/// Why an exact arbitrary-precision PSD check declined.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BigPsdDecline {
    /// Matrix dimension exceeded policy.
    Dimension {
        /// Observed dimension.
        observed: usize,
        /// Admitted maximum.
        limit: usize,
    },
    /// Input encoding exceeded policy.
    InputBytes {
        /// Observed bytes, or the first value known to exceed the limit.
        observed: usize,
        /// Admitted maximum.
        limit: usize,
    },
    /// An exact intermediate grew beyond policy.
    IntermediateBits {
        /// Elimination pivot at which growth was observed.
        pivot: usize,
        /// Observed numerator or denominator bits.
        observed: usize,
        /// Admitted maximum.
        limit: usize,
    },
}

/// Result of an arbitrary-precision exact PSD decision.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BigPsd {
    /// The matrix is PSD.
    Yes {
        /// Nonzero exact pivots in elimination order.
        pivots: Vec<BigRational>,
        /// Number of structurally zero pivots.
        zero_pivots: usize,
        /// Largest numerator or denominator encountered, in bits.
        max_intermediate_bits: usize,
    },
    /// The matrix is not PSD, with a checked local reason.
    No(String),
    /// Policy prevented a verdict.
    Declined(BigPsdDecline),
}

fn integer_bits(value: &num_bigint::BigInt) -> usize {
    value.to_signed_bytes_le().len().saturating_mul(8)
}

fn rational_bits(value: &BigRational) -> usize {
    integer_bits(value.numer()).max(integer_bits(value.denom()))
}

fn admitted_intermediate(
    value: &BigRational,
    pivot: usize,
    limits: BigPsdLimits,
    maximum: &mut usize,
) -> Result<(), BigPsdDecline> {
    let bits = rational_bits(value);
    *maximum = (*maximum).max(bits);
    if bits > limits.max_intermediate_bits {
        Err(BigPsdDecline::IntermediateBits {
            pivot,
            observed: bits,
            limit: limits.max_intermediate_bits,
        })
    } else {
        Ok(())
    }
}

/// Decide whether a rational symmetric matrix is PSD with exact `BigInt` arithmetic.
///
/// The algorithm performs `LDL^T`-style symmetric elimination. A zero pivot is
/// admissible only when the remainder of its row is zero; otherwise the associated
/// two-by-two principal minor is negative.
#[must_use]
#[allow(clippy::needless_range_loop)]
pub fn is_psd_big(matrix: &[Vec<BigRational>], limits: BigPsdLimits) -> BigPsd {
    let n = matrix.len();
    if n > limits.max_dimension {
        return BigPsd::Declined(BigPsdDecline::Dimension {
            observed: n,
            limit: limits.max_dimension,
        });
    }
    let mut input_bytes = 0_usize;
    let mut maximum_bits = 0_usize;
    for (row_index, row) in matrix.iter().enumerate() {
        if row.len() != n {
            return BigPsd::No(format!(
                "row {row_index} has {} entries in a {n}-by-{n} matrix",
                row.len()
            ));
        }
        for value in row {
            let bytes =
                value.numer().to_signed_bytes_le().len() + value.denom().to_signed_bytes_le().len();
            input_bytes = input_bytes.saturating_add(bytes);
            if input_bytes > limits.max_input_bytes {
                return BigPsd::Declined(BigPsdDecline::InputBytes {
                    observed: input_bytes,
                    limit: limits.max_input_bytes,
                });
            }
            maximum_bits = maximum_bits.max(rational_bits(value));
        }
    }
    for i in 0..n {
        for j in 0..i {
            if matrix[i][j] != matrix[j][i] {
                return BigPsd::No(format!("the matrix is not symmetric at ({i}, {j})"));
            }
        }
    }

    let mut work = matrix.to_vec();
    let mut pivots = Vec::new();
    let mut zero_pivots = 0_usize;
    for k in 0..n {
        let pivot = work[k][k].clone();
        if pivot.is_negative() {
            return BigPsd::No(format!("pivot {k} is negative ({pivot})"));
        }
        if pivot.is_zero() {
            if let Some(j) = ((k + 1)..n).find(|&j| !work[k][j].is_zero()) {
                return BigPsd::No(format!(
                    "pivot {k} is zero while entry ({k}, {j}) is nonzero"
                ));
            }
            zero_pivots += 1;
            continue;
        }
        pivots.push(pivot.clone());
        for i in (k + 1)..n {
            let factor = &work[i][k] / &pivot;
            if let Err(reason) = admitted_intermediate(&factor, k, limits, &mut maximum_bits) {
                return BigPsd::Declined(reason);
            }
            if factor.is_zero() {
                continue;
            }
            for j in k..n {
                let updated = &work[i][j] - &factor * &work[k][j];
                if let Err(reason) = admitted_intermediate(&updated, k, limits, &mut maximum_bits) {
                    return BigPsd::Declined(reason);
                }
                work[i][j] = updated;
            }
        }
    }
    BigPsd::Yes {
        pivots,
        zero_pivots,
        max_intermediate_bits: maximum_bits,
    }
}

#[cfg(test)]
mod tests {
    use num_bigint::BigInt;

    use super::*;

    fn integer(value: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(value))
    }

    fn matrix(rows: &[&[i64]]) -> Vec<Vec<BigRational>> {
        rows.iter()
            .map(|row| row.iter().map(|&value| integer(value)).collect())
            .collect()
    }

    #[test]
    fn large_diagonal_matrix_is_psd_without_i128_ceiling() {
        let large = BigInt::from(10_u8).pow(80);
        let matrix = vec![
            vec![BigRational::from_integer(large.clone()), integer(0)],
            vec![integer(0), BigRational::from_integer(large)],
        ];
        assert!(matches!(
            is_psd_big(&matrix, BigPsdLimits::default()),
            BigPsd::Yes { zero_pivots: 0, .. }
        ));
    }

    #[test]
    fn singular_psd_and_indefinite_controls_are_distinguished() {
        assert!(matches!(
            is_psd_big(&matrix(&[&[1, 2], &[2, 4]]), BigPsdLimits::default()),
            BigPsd::Yes { zero_pivots: 1, .. }
        ));
        assert!(matches!(
            is_psd_big(&matrix(&[&[1, 2], &[2, 1]]), BigPsdLimits::default()),
            BigPsd::No(_)
        ));
    }

    #[test]
    fn intermediate_growth_limit_declines() {
        let limits = BigPsdLimits {
            max_intermediate_bits: 1,
            ..BigPsdLimits::default()
        };
        assert!(matches!(
            is_psd_big(&matrix(&[&[2, 1], &[1, 2]]), limits),
            BigPsd::Declined(BigPsdDecline::IntermediateBits { .. })
        ));
    }
}
