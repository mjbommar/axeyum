//! Exact rational positive-semidefiniteness, by symmetric elimination.
//!
//! No square roots and no floating point: the test is `LDL^T` rather than
//! Cholesky precisely so that a semidefinite (singular) matrix is decidable in
//! the rationals. `crate::matrix::cholesky_decomposition` cannot be used here --
//! it introduces surds and rejects every matrix with a zero pivot, which is
//! exactly the case a moment matrix lands in.
//!
//! The rule for a zero pivot is the whole content of the semidefinite case: if
//! `M[k][k] = 0` and some `M[k][j] != 0` with `j > k`, the two-by-two principal
//! minor on `{k, j}` is `[[0, a], [a, b]]` with determinant `-a^2 < 0`, so the
//! matrix is not PSD. Otherwise the row and column are identically zero and the
//! elimination continues.
//!
//! Every step is `checked_*`; an overflow is reported as [`Psd::Overflow`] and
//! is a **decline**, never a verdict. An overflowed elimination says nothing
//! about the matrix, and reporting it as `NotPsd` would turn a resource limit
//! into a mathematical claim.

use axeyum_ir::Rational;

/// The outcome of an exact PSD test.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Psd {
    /// The matrix is positive semidefinite, with the diagonal `D` of the
    /// factorisation reported so a caller can see the rank and see that every
    /// pivot really was nonnegative.
    Yes {
        /// The nonzero pivots encountered, in elimination order.
        pivots: Vec<Rational>,
        /// How many pivots were exactly zero, i.e. the corank.
        zero_pivots: usize,
    },
    /// The matrix is not positive semidefinite, with the reason.
    No(String),
    /// Exact arithmetic ran out of range; nothing is claimed.
    Overflow,
}

/// Decide whether a symmetric rational matrix is positive semidefinite.
///
/// A non-square or non-symmetric input is [`Psd::No`] with a message rather than
/// a panic: this runs over committed artifacts, and a malformed file must be
/// rejected, not crash the gate.
// Index arithmetic is the point here, not an accident: symmetric elimination
// reads `work[k][j]` while writing `work[i][j]`, and the symmetry test compares
// `matrix[i][j]` against `matrix[j][i]`. Neither is expressible as an iterator
// over one row, and rewriting them as one would obscure the two-index structure
// the correctness argument is stated in.
#[allow(clippy::needless_range_loop)]
#[must_use]
pub fn is_psd(matrix: &[Vec<Rational>]) -> Psd {
    let n = matrix.len();
    for (row_index, row) in matrix.iter().enumerate() {
        if row.len() != n {
            return Psd::No(format!(
                "row {row_index} has {} entries in a {n}-by-{n} matrix",
                row.len()
            ));
        }
    }
    for i in 0..n {
        for j in 0..i {
            if matrix[i][j] != matrix[j][i] {
                return Psd::No(format!("the matrix is not symmetric at ({i}, {j})"));
            }
        }
    }

    let mut work: Vec<Vec<Rational>> = matrix.to_vec();
    let mut pivots = Vec::new();
    let mut zero_pivots = 0usize;

    for k in 0..n {
        let pivot = work[k][k];
        if pivot.numerator() < 0 {
            return Psd::No(format!(
                "pivot {k} is negative ({}/{}), so the leading principal submatrix is indefinite",
                pivot.numerator(),
                pivot.denominator()
            ));
        }
        if pivot.is_zero() {
            for j in (k + 1)..n {
                if !work[k][j].is_zero() {
                    return Psd::No(format!(
                        "pivot {k} is zero while entry ({k}, {j}) is not, so the principal minor on \
                         those two indices has a negative determinant"
                    ));
                }
            }
            zero_pivots += 1;
            continue;
        }
        pivots.push(pivot);
        for i in (k + 1)..n {
            let Some(factor) = work[i][k].checked_div(pivot) else {
                return Psd::Overflow;
            };
            if factor.is_zero() {
                continue;
            }
            for j in k..n {
                let Some(delta) = factor.checked_mul(work[k][j]) else {
                    return Psd::Overflow;
                };
                let Some(updated) = work[i][j].checked_sub(delta) else {
                    return Psd::Overflow;
                };
                work[i][j] = updated;
            }
        }
    }

    Psd::Yes {
        pivots,
        zero_pivots,
    }
}

#[cfg(test)]
mod tests {
    use super::{Psd, is_psd};
    use axeyum_ir::Rational;

    fn matrix(rows: &[&[i128]]) -> Vec<Vec<Rational>> {
        rows.iter()
            .map(|row| row.iter().map(|value| Rational::integer(*value)).collect())
            .collect()
    }

    #[test]
    fn identity_is_positive_definite() {
        assert!(matches!(
            is_psd(&matrix(&[&[1, 0], &[0, 1]])),
            Psd::Yes { zero_pivots: 0, .. }
        ));
    }

    #[test]
    fn a_rank_one_gram_matrix_is_semidefinite_not_definite() {
        // [[1, 2], [2, 4]] = v v^T for v = (1, 2): PSD with one zero pivot.
        let Psd::Yes { zero_pivots, .. } = is_psd(&matrix(&[&[1, 2], &[2, 4]])) else {
            panic!("a rank-one Gram matrix must be PSD");
        };
        assert_eq!(zero_pivots, 1);
    }

    #[test]
    fn a_negative_eigenvalue_is_rejected() {
        assert!(matches!(is_psd(&matrix(&[&[1, 2], &[2, 1]])), Psd::No(_)));
    }

    #[test]
    fn a_zero_diagonal_with_a_nonzero_off_diagonal_is_rejected() {
        // This is the case Cholesky cannot see and the reason this module runs
        // LDL^T: [[0, 1], [1, 1]] has determinant -1.
        assert!(matches!(is_psd(&matrix(&[&[0, 1], &[1, 1]])), Psd::No(_)));
    }

    #[test]
    fn a_zero_row_is_accepted() {
        assert!(matches!(
            is_psd(&matrix(&[&[0, 0], &[0, 3]])),
            Psd::Yes { zero_pivots: 1, .. }
        ));
    }

    #[test]
    fn a_non_symmetric_matrix_is_rejected_rather_than_symmetrised() {
        assert!(matches!(is_psd(&matrix(&[&[1, 1], &[0, 1]])), Psd::No(_)));
    }

    #[test]
    fn a_ragged_matrix_is_rejected_rather_than_panicking() {
        let ragged = vec![
            vec![Rational::integer(1)],
            vec![Rational::integer(0), Rational::integer(1)],
        ];
        assert!(matches!(is_psd(&ragged), Psd::No(_)));
    }
}
