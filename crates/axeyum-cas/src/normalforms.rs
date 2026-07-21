//! Integer matrix normal forms: Hermite (HNF) and Smith (SNF).
//!
//! Both routines operate on **integer** matrices — a [`Matrix`] every entry of
//! which is an integer-valued [`CasExpr::Const`]. Any non-integer or non-constant
//! entry makes the whole computation decline (`None`). Internally the work is done
//! on a plain `Vec<Vec<i128>>` grid with exclusively `checked_*` arithmetic, so an
//! intermediate that would leave the `i128` range yields an honest `None` rather
//! than a panic or a wrapped (wrong) value.
//!
//! # What is computed
//!
//! - [`hermite_normal_form`] returns `(U, H)` with `U * A = H`, where `H` is in
//!   row-style Hermite normal form (upper-triangular, strictly positive pivots,
//!   every entry above a pivot reduced into `0..pivot` so the pivot is the strict
//!   maximum of its column above it) and `U` is **unimodular** (an integer matrix
//!   with `det(U) = +/-1`).
//! - [`smith_normal_form`] returns `(U, D, V)` with `U * A * V = D`, where `D` is
//!   diagonal with the invariant-factor divisibility chain
//!   `d_1 | d_2 | ... | d_r` (trailing zeros for a rank-deficient matrix) and both
//!   `U` and `V` are unimodular.
//!
//! # Algorithms
//!
//! Hermite form is produced by integer row reduction in the Kannan-Bachem style:
//! for each column the extended Euclidean algorithm ([`extended_gcd`]) drives a
//! sequence of unimodular `2x2` row operations that collapse the column at and
//! below the pivot to a single gcd, after which the rows above the pivot are
//! back-reduced modulo the pivot. Smith form alternates the same row reduction
//! with the analogous column reduction; when the current pivot fails to divide a
//! later entry, that entry's row is folded into the pivot row to propagate the
//! gcd (the classic divisibility fix-up). Every operation is unimodular, so the
//! accumulated transforms stay unimodular by construction.
//!
//! # Certificate
//!
//! The search is intricate, so each answer is re-checked by a cheap independent
//! test before it is returned. The identity (`U * A = H`, or `U * A * V = D`) is
//! recomputed with the crate's own certified [`Matrix::mul`] and confirmed
//! entrywise with the decidable zero-test [`equal`]; the transforms are confirmed
//! unimodular with [`Matrix::determinant`] and a certified `det = +/-1` check.
//! A result is returned only when all of these certificates hold.
//!
//! # Limitations
//!
//! The unimodularity certificate uses cofactor [`Matrix::determinant`], which is
//! `O(n!)`, so certification is intended for small dimensions. The reduction loop
//! is bounded by an iteration cap; a pathological input that would exceed it
//! declines with `None` rather than running unbounded.

use crate::ntheory::extended_gcd;
use crate::{CasExpr, Matrix, ZeroTest, equal};

/// A dense integer grid in row-major nested form (the internal working
/// representation shared by the reduction routines).
type IntGrid = Vec<Vec<i128>>;

/// The exact integer value of an entry, or `None` if it is not an integer-valued
/// [`CasExpr::Const`].
fn integer_value(expr: &CasExpr) -> Option<i128> {
    match expr {
        CasExpr::Const(value) if value.is_integer() => Some(value.numerator()),
        _ => None,
    }
}

/// Convert a matrix to an `i128` grid, declining if any entry is non-integer or
/// non-constant.
fn to_int_grid(matrix: &Matrix) -> Option<Vec<Vec<i128>>> {
    let mut grid = Vec::with_capacity(matrix.rows());
    for row in 0..matrix.rows() {
        let mut converted = Vec::with_capacity(matrix.cols());
        for col in 0..matrix.cols() {
            converted.push(integer_value(matrix.get(row, col)?)?);
        }
        grid.push(converted);
    }
    Some(grid)
}

/// Build a `rows x cols` matrix of integer constants from a grid, declining if
/// the grid shape does not match.
fn grid_to_matrix(grid: &[Vec<i128>], rows: usize, cols: usize) -> Option<Matrix> {
    let mut data = Vec::with_capacity(rows.checked_mul(cols)?);
    for row in grid {
        for &value in row {
            data.push(CasExpr::int(value));
        }
    }
    Matrix::new(rows, cols, data)
}

/// The `size x size` integer identity grid.
fn identity_grid(size: usize) -> Vec<Vec<i128>> {
    let mut grid = vec![vec![0i128; size]; size];
    for (index, row) in grid.iter_mut().enumerate() {
        row[index] = 1;
    }
    grid
}

/// Two distinct rows of a grid as simultaneous mutable references (caller
/// guarantees `first != second`).
fn two_rows_mut(
    grid: &mut [Vec<i128>],
    first: usize,
    second: usize,
) -> (&mut Vec<i128>, &mut Vec<i128>) {
    debug_assert!(first != second, "two_rows_mut requires distinct rows");
    if first < second {
        let (head, tail) = grid.split_at_mut(second);
        (&mut head[first], &mut tail[0])
    } else {
        let (head, tail) = grid.split_at_mut(first);
        (&mut tail[0], &mut head[second])
    }
}

/// A unimodular `2x2` transform `((a11, a12), (a21, a22))` applied to a pair of
/// rows or columns.
type Transform = (i128, i128, i128, i128);

/// Replace rows `first` and `second` in place with the unimodular combination
/// carried by `transform`, applying the same coefficients to both rows. `None`
/// on overflow.
fn combine_rows(
    grid: &mut [Vec<i128>],
    first: usize,
    second: usize,
    transform: Transform,
) -> Option<()> {
    let (a11, a12, a21, a22) = transform;
    let (row_first, row_second) = two_rows_mut(grid, first, second);
    for (upper, lower) in row_first.iter_mut().zip(row_second.iter_mut()) {
        let prior_upper = *upper;
        let prior_lower = *lower;
        let new_upper = a11
            .checked_mul(prior_upper)?
            .checked_add(a12.checked_mul(prior_lower)?)?;
        let new_lower = a21
            .checked_mul(prior_upper)?
            .checked_add(a22.checked_mul(prior_lower)?)?;
        *upper = new_upper;
        *lower = new_lower;
    }
    Some(())
}

/// Replace columns `first` and `second` in place with the unimodular combination
/// carried by `transform`, applying the same coefficients to both columns. `None`
/// on overflow.
fn combine_columns(
    grid: &mut [Vec<i128>],
    first: usize,
    second: usize,
    transform: Transform,
) -> Option<()> {
    let (a11, a12, a21, a22) = transform;
    for row in grid.iter_mut() {
        let prior_first = row[first];
        let prior_second = row[second];
        let new_first = a11
            .checked_mul(prior_first)?
            .checked_add(a12.checked_mul(prior_second)?)?;
        let new_second = a21
            .checked_mul(prior_first)?
            .checked_add(a22.checked_mul(prior_second)?)?;
        row[first] = new_first;
        row[second] = new_second;
    }
    Some(())
}

/// Swap columns `first` and `second` across every row.
fn swap_columns(grid: &mut [Vec<i128>], first: usize, second: usize) {
    for row in grid.iter_mut() {
        row.swap(first, second);
    }
}

/// Add `factor` times row `source` into row `target` (`target += factor *
/// source`). `None` on overflow.
fn add_row_multiple(
    grid: &mut [Vec<i128>],
    target: usize,
    source: usize,
    factor: i128,
) -> Option<()> {
    let (row_target, row_source) = two_rows_mut(grid, target, source);
    for (accumulator, addend) in row_target.iter_mut().zip(row_source.iter()) {
        *accumulator = accumulator.checked_add(factor.checked_mul(*addend)?)?;
    }
    Some(())
}

/// Negate every entry of row `index` in place. `None` on overflow (a lone
/// `i128::MIN`).
fn negate_row(grid: &mut [Vec<i128>], index: usize) -> Option<()> {
    for entry in &mut grid[index] {
        *entry = entry.checked_neg()?;
    }
    Some(())
}

/// Reduce column `col` of `primary` with a unimodular row operation so that the
/// pivot row holds `gcd(primary[pivot_row][col], primary[other_row][col])` and
/// the other row holds `0`, applying the identical operation to `aux`.
///
/// The caller guarantees `primary[other_row][col] != 0`, so the gcd is positive
/// and the divisions are exact. `None` on overflow.
fn reduce_rows_by_gcd(
    primary: &mut [Vec<i128>],
    aux: &mut [Vec<i128>],
    pivot_row: usize,
    other_row: usize,
    col: usize,
) -> Option<()> {
    let pivot_value = primary[pivot_row][col];
    let other_value = primary[other_row][col];
    let (gcd_value, bezout_pivot, bezout_other) = extended_gcd(pivot_value, other_value);
    let pivot_ratio = pivot_value.checked_div(gcd_value)?;
    let other_ratio = other_value.checked_div(gcd_value)?;
    let transform = (
        bezout_pivot,
        bezout_other,
        other_ratio.checked_neg()?,
        pivot_ratio,
    );
    combine_rows(primary, pivot_row, other_row, transform)?;
    combine_rows(aux, pivot_row, other_row, transform)?;
    Some(())
}

/// Reduce row `row` of `primary` with a unimodular column operation so that the
/// pivot column holds `gcd(primary[row][pivot_col], primary[row][other_col])` and
/// the other column holds `0`, applying the identical operation to `aux`.
///
/// The caller guarantees `primary[row][other_col] != 0`. `None` on overflow.
fn reduce_columns_by_gcd(
    primary: &mut [Vec<i128>],
    aux: &mut [Vec<i128>],
    pivot_col: usize,
    other_col: usize,
    row: usize,
) -> Option<()> {
    let pivot_value = primary[row][pivot_col];
    let other_value = primary[row][other_col];
    let (gcd_value, bezout_pivot, bezout_other) = extended_gcd(pivot_value, other_value);
    let pivot_ratio = pivot_value.checked_div(gcd_value)?;
    let other_ratio = other_value.checked_div(gcd_value)?;
    let transform = (
        bezout_pivot,
        bezout_other,
        other_ratio.checked_neg()?,
        pivot_ratio,
    );
    combine_columns(primary, pivot_col, other_col, transform)?;
    combine_columns(aux, pivot_col, other_col, transform)?;
    Some(())
}

/// The first `(row, col)` with `row >= start` and `col >= start` whose entry is
/// nonzero, or `None` if the trailing submatrix is entirely zero.
fn find_nonzero(
    grid: &[Vec<i128>],
    start: usize,
    rows: usize,
    cols: usize,
) -> Option<(usize, usize)> {
    for (row_index, row) in grid.iter().enumerate().take(rows).skip(start) {
        for (col_index, &value) in row.iter().enumerate().take(cols).skip(start) {
            if value != 0 {
                return Some((row_index, col_index));
            }
        }
    }
    None
}

/// Compute the Hermite grids `(left, hermite)` with `left * a = hermite`.
fn hermite_grids(a: &[Vec<i128>], rows: usize, cols: usize) -> Option<(IntGrid, IntGrid)> {
    let mut hermite = a.to_vec();
    let mut left = identity_grid(rows);
    let mut pivot_row = 0usize;
    for col in 0..cols {
        if pivot_row >= rows {
            break;
        }
        // Collapse the column at and below the pivot into a single gcd.
        for lower in (pivot_row + 1)..rows {
            if hermite[lower][col] != 0 {
                reduce_rows_by_gcd(&mut hermite, &mut left, pivot_row, lower, col)?;
            }
        }
        if hermite[pivot_row][col] == 0 {
            // No pivot in this column; it stays a non-pivot column.
            continue;
        }
        if hermite[pivot_row][col] < 0 {
            negate_row(&mut hermite, pivot_row)?;
            negate_row(&mut left, pivot_row)?;
        }
        let pivot = hermite[pivot_row][col];
        // Back-reduce every row above the pivot into the range `0..pivot`.
        for above in 0..pivot_row {
            let entry = hermite[above][col];
            if entry != 0 {
                let quotient = entry.div_euclid(pivot);
                if quotient != 0 {
                    let factor = quotient.checked_neg()?;
                    add_row_multiple(&mut hermite, above, pivot_row, factor)?;
                    add_row_multiple(&mut left, above, pivot_row, factor)?;
                }
            }
        }
        pivot_row += 1;
    }
    Some((left, hermite))
}

/// Compute the Smith grids `(left, work, right)` with `left * a * right = work`.
fn smith_grids(a: &[Vec<i128>], rows: usize, cols: usize) -> Option<(IntGrid, IntGrid, IntGrid)> {
    let mut work = a.to_vec();
    let mut left = identity_grid(rows);
    let mut right = identity_grid(cols);
    let limit = rows.min(cols);
    // Generous bound on the number of pivot-refinement iterations; every gcd step
    // strictly shrinks the pivot, so real inputs finish far below this cap.
    let cap = 1000usize.saturating_add(rows.saturating_mul(cols).saturating_mul(1000));
    let mut steps = 0usize;
    'positions: for pos in 0..limit {
        loop {
            steps += 1;
            if steps > cap {
                return None;
            }
            if work[pos][pos] == 0 {
                match find_nonzero(&work, pos, rows, cols) {
                    Some((pivot_row, pivot_col)) => {
                        if pivot_row != pos {
                            work.swap(pos, pivot_row);
                            left.swap(pos, pivot_row);
                        }
                        if pivot_col != pos {
                            swap_columns(&mut work, pos, pivot_col);
                            swap_columns(&mut right, pos, pivot_col);
                        }
                    }
                    None => break 'positions,
                }
            }
            // Clear the pivot column below the pivot, then the pivot row to its
            // right. A column operation can re-dirty the column, so we re-check.
            for lower in (pos + 1)..rows {
                if work[lower][pos] != 0 {
                    reduce_rows_by_gcd(&mut work, &mut left, pos, lower, pos)?;
                }
            }
            for right_col in (pos + 1)..cols {
                if work[pos][right_col] != 0 {
                    reduce_columns_by_gcd(&mut work, &mut right, pos, right_col, pos)?;
                }
            }
            if ((pos + 1)..rows).any(|lower| work[lower][pos] != 0) {
                continue;
            }
            if ((pos + 1)..cols).any(|right_col| work[pos][right_col] != 0) {
                continue;
            }
            if work[pos][pos] < 0 {
                negate_row(&mut work, pos)?;
                negate_row(&mut left, pos)?;
            }
            let pivot = work[pos][pos];
            // Divisibility fix-up: if the pivot fails to divide a later entry, fold
            // that entry's row into the pivot row and reduce again.
            let mut adjusted = false;
            // `pivot > 0` here, so the remainder test never overflows (signed
            // `i128` has no inherent `is_multiple_of`; that method is unsigned-only).
            'search: for lower in (pos + 1)..rows {
                for right_col in (pos + 1)..cols {
                    if work[lower][right_col] % pivot != 0 {
                        add_row_multiple(&mut work, pos, lower, 1)?;
                        add_row_multiple(&mut left, pos, lower, 1)?;
                        adjusted = true;
                        break 'search;
                    }
                }
            }
            if !adjusted {
                break;
            }
        }
    }
    Some((left, work, right))
}

/// Certify that `product` and `target` agree in shape and, entrywise, are
/// decidably equal via the zero-test [`equal`].
fn certify_product_equals(product: &Matrix, target: &Matrix) -> bool {
    if product.rows() != target.rows() || product.cols() != target.cols() {
        return false;
    }
    for row in 0..product.rows() {
        for col in 0..product.cols() {
            let (Some(left_entry), Some(right_entry)) =
                (product.get(row, col), target.get(row, col))
            else {
                return false;
            };
            if !matches!(
                equal(left_entry, right_entry),
                ZeroTest::Certified { equal: true, .. }
            ) {
                return false;
            }
        }
    }
    true
}

/// Certify that `matrix` is unimodular by confirming `det(matrix) = +/-1` via the
/// certified [`Matrix::determinant`] and the zero-test.
fn is_unimodular(matrix: &Matrix) -> bool {
    let Some(determinant) = matrix.determinant() else {
        return false;
    };
    let is_one = matches!(
        equal(&determinant, &CasExpr::one()),
        ZeroTest::Certified { equal: true, .. }
    );
    let is_neg_one = matches!(
        equal(&determinant, &CasExpr::int(-1)),
        ZeroTest::Certified { equal: true, .. }
    );
    is_one || is_neg_one
}

/// The Hermite normal form of an integer matrix.
///
/// Returns `(U, H)` such that `U * A = H`, where `H` is upper-triangular with
/// strictly positive pivots (each pivot the strict maximum of its column above
/// it) and `U` is unimodular (`det(U) = +/-1`). `A` may be rectangular or
/// rank-deficient.
///
/// Returns `None` if any entry of `matrix` is not an integer-valued
/// [`CasExpr::Const`], if the exact `i128` reduction overflows, or if the
/// independent certificate (`U * A = H` entrywise and `det(U) = +/-1`) fails to
/// hold.
#[must_use]
pub fn hermite_normal_form(matrix: &Matrix) -> Option<(Matrix, Matrix)> {
    let rows = matrix.rows();
    let cols = matrix.cols();
    let grid = to_int_grid(matrix)?;
    let (left_grid, hermite_grid) = hermite_grids(&grid, rows, cols)?;
    let unimodular = grid_to_matrix(&left_grid, rows, rows)?;
    let hermite = grid_to_matrix(&hermite_grid, rows, cols)?;
    let product = unimodular.mul(matrix)?;
    if !certify_product_equals(&product, &hermite) {
        return None;
    }
    if !is_unimodular(&unimodular) {
        return None;
    }
    Some((unimodular, hermite))
}

/// The Smith normal form of an integer matrix.
///
/// Returns `(U, D, V)` such that `U * A * V = D`, where `D` is diagonal with the
/// invariant-factor divisibility chain `d_1 | d_2 | ... | d_r` (and trailing
/// zeros for a rank-deficient `A`), and both `U` and `V` are unimodular
/// (`det = +/-1`). `A` may be rectangular or rank-deficient.
///
/// Returns `None` if any entry of `matrix` is not an integer-valued
/// [`CasExpr::Const`], if the exact `i128` reduction overflows or exceeds the
/// iteration cap, or if the independent certificate (`U * A * V = D` entrywise
/// and `det(U) = det(V) = +/-1`) fails to hold.
#[must_use]
pub fn smith_normal_form(matrix: &Matrix) -> Option<(Matrix, Matrix, Matrix)> {
    let rows = matrix.rows();
    let cols = matrix.cols();
    let grid = to_int_grid(matrix)?;
    let (left_grid, diagonal_grid, right_grid) = smith_grids(&grid, rows, cols)?;
    let left = grid_to_matrix(&left_grid, rows, rows)?;
    let diagonal = grid_to_matrix(&diagonal_grid, rows, cols)?;
    let right = grid_to_matrix(&right_grid, cols, cols)?;
    let product = left.mul(matrix)?.mul(&right)?;
    if !certify_product_equals(&product, &diagonal) {
        return None;
    }
    if !is_unimodular(&left) || !is_unimodular(&right) {
        return None;
    }
    Some((left, diagonal, right))
}

#[cfg(test)]
mod tests {
    use super::{hermite_normal_form, smith_normal_form};
    use crate::{CasExpr, Matrix, ZeroTest, equal};

    /// Build an integer matrix from `i128` rows.
    fn matrix_of(rows: &[&[i128]]) -> Matrix {
        let data: Vec<Vec<CasExpr>> = rows
            .iter()
            .map(|row| row.iter().map(|&value| CasExpr::int(value)).collect())
            .collect();
        Matrix::from_rows(data).expect("rectangular integer matrix")
    }

    /// The exact integer value of entry `(row, col)`.
    fn entry_at(matrix: &Matrix, row: usize, col: usize) -> i128 {
        match matrix.get(row, col).expect("index in bounds") {
            CasExpr::Const(value) => {
                assert_eq!(value.denominator(), 1, "entry is integral");
                value.numerator()
            }
            other => panic!("non-constant entry: {other:?}"),
        }
    }

    /// Assert two matrices are certified equal entrywise via the zero-test.
    fn assert_certified_equal(left: &Matrix, right: &Matrix) {
        assert_eq!(left.rows(), right.rows(), "row count mismatch");
        assert_eq!(left.cols(), right.cols(), "column count mismatch");
        for row in 0..left.rows() {
            for col in 0..left.cols() {
                let decision = equal(
                    left.get(row, col).expect("in bounds"),
                    right.get(row, col).expect("in bounds"),
                );
                assert!(
                    matches!(decision, ZeroTest::Certified { equal: true, .. }),
                    "entry ({row}, {col}) not certified equal"
                );
            }
        }
    }

    /// Assert `matrix` is unimodular via the certified determinant.
    fn assert_unimodular(matrix: &Matrix) {
        let determinant = matrix.determinant().expect("square matrix");
        let is_one = matches!(
            equal(&determinant, &CasExpr::one()),
            ZeroTest::Certified { equal: true, .. }
        );
        let is_neg_one = matches!(
            equal(&determinant, &CasExpr::int(-1)),
            ZeroTest::Certified { equal: true, .. }
        );
        assert!(is_one || is_neg_one, "det must be +/-1, got {determinant}");
    }

    #[test]
    fn hermite_textbook_matrix() {
        let a = matrix_of(&[&[2, 3, 6, 2], &[5, 6, 1, 6], &[8, 3, 1, 1]]);
        let (unimodular, hermite) = hermite_normal_form(&a).expect("integer HNF exists");

        // The defining identity, re-checked with the certified product.
        assert_certified_equal(&unimodular.mul(&a).expect("conformable"), &hermite);
        assert_unimodular(&unimodular);

        // H is upper-triangular with strictly positive pivots, and every entry
        // above a pivot is reduced into `0..pivot`.
        for row in 0..hermite.rows() {
            for col in 0..row.min(hermite.cols()) {
                assert_eq!(
                    entry_at(&hermite, row, col),
                    0,
                    "H must be upper-triangular"
                );
            }
            let pivot = entry_at(&hermite, row, row);
            assert!(pivot > 0, "pivot ({row},{row}) must be positive");
            for above in 0..row {
                let over = entry_at(&hermite, above, row);
                assert!(over >= 0 && over < pivot, "entry above pivot in range");
            }
        }
    }

    #[test]
    fn hermite_second_matrix() {
        let a = matrix_of(&[&[2, 4, 4], &[-6, 6, 12], &[10, 4, 16]]);
        let (unimodular, hermite) = hermite_normal_form(&a).expect("integer HNF exists");

        assert_certified_equal(&unimodular.mul(&a).expect("conformable"), &hermite);
        assert_unimodular(&unimodular);

        for row in 0..hermite.rows() {
            for col in 0..row {
                assert_eq!(
                    entry_at(&hermite, row, col),
                    0,
                    "H must be upper-triangular"
                );
            }
            assert!(entry_at(&hermite, row, row) > 0, "positive pivot");
        }
    }

    #[test]
    fn smith_first_matrix() {
        let a = matrix_of(&[&[2, 4, 4], &[-6, 6, 12], &[10, -4, -16]]);
        let (left, diagonal, right) = smith_normal_form(&a).expect("integer SNF exists");

        // U * A * V = D, re-checked with the certified product.
        assert_certified_equal(
            &left
                .mul(&a)
                .expect("conformable")
                .mul(&right)
                .expect("conformable"),
            &diagonal,
        );
        assert_unimodular(&left);
        assert_unimodular(&right);

        // D is diagonal.
        for row in 0..diagonal.rows() {
            for col in 0..diagonal.cols() {
                if row != col {
                    assert_eq!(
                        entry_at(&diagonal, row, col),
                        0,
                        "off-diagonal must be zero"
                    );
                }
            }
        }

        let d0 = entry_at(&diagonal, 0, 0);
        let d1 = entry_at(&diagonal, 1, 1);
        let d2 = entry_at(&diagonal, 2, 2);
        // Divisibility chain d1 | d2 | d3.
        assert!(d0 != 0 && d1 % d0 == 0, "d1 | d2");
        assert!(d1 != 0 && d2 % d1 == 0, "d2 | d3");
        // The product of invariant factors is |det(A)| = 144; the true SNF is
        // diag(2, 6, 12).
        assert_eq!(d0 * d1 * d2, 144);
        assert_eq!((d0, d1, d2), (2, 6, 12));
    }

    #[test]
    fn smith_diagonal_restructures_gcd_lcm() {
        // diag(2, 3, 4) has SNF diag(1, 2, 12): gcd(entries)=1, then 6 and 4
        // restructure to gcd 2 and lcm 12.
        let a = matrix_of(&[&[2, 0, 0], &[0, 3, 0], &[0, 0, 4]]);
        let (left, diagonal, right) = smith_normal_form(&a).expect("integer SNF exists");

        assert_certified_equal(
            &left
                .mul(&a)
                .expect("conformable")
                .mul(&right)
                .expect("conformable"),
            &diagonal,
        );
        assert_unimodular(&left);
        assert_unimodular(&right);

        let d0 = entry_at(&diagonal, 0, 0);
        let d1 = entry_at(&diagonal, 1, 1);
        let d2 = entry_at(&diagonal, 2, 2);
        assert_eq!((d0, d1, d2), (1, 2, 12));
        assert!(d1 % d0 == 0 && d2 % d1 == 0, "divisibility chain");
        assert_eq!(d0 * d1 * d2, 24);
    }

    #[test]
    fn smith_of_identity_is_identity() {
        let a = Matrix::identity(3);
        let (left, diagonal, right) = smith_normal_form(&a).expect("integer SNF exists");

        assert_certified_equal(
            &left
                .mul(&a)
                .expect("conformable")
                .mul(&right)
                .expect("conformable"),
            &diagonal,
        );
        assert_certified_equal(&diagonal, &Matrix::identity(3));
        assert_unimodular(&left);
        assert_unimodular(&right);
    }

    #[test]
    fn smith_rank_deficient_has_trailing_zero() {
        // [[1,2],[2,4]] has rank 1: SNF is diag(1, 0).
        let a = matrix_of(&[&[1, 2], &[2, 4]]);
        let (left, diagonal, right) = smith_normal_form(&a).expect("integer SNF exists");

        assert_certified_equal(
            &left
                .mul(&a)
                .expect("conformable")
                .mul(&right)
                .expect("conformable"),
            &diagonal,
        );
        assert_unimodular(&left);
        assert_unimodular(&right);

        assert_eq!(entry_at(&diagonal, 0, 0), 1);
        assert_eq!(
            entry_at(&diagonal, 1, 1),
            0,
            "trailing invariant factor is zero"
        );
        assert_eq!(entry_at(&diagonal, 0, 1), 0);
        assert_eq!(entry_at(&diagonal, 1, 0), 0);
    }

    #[test]
    fn declines_non_integer_entries() {
        let a = Matrix::from_rows(vec![
            vec![CasExpr::rat(1, 2), CasExpr::int(1)],
            vec![CasExpr::int(0), CasExpr::int(1)],
        ])
        .expect("rectangular");
        assert!(hermite_normal_form(&a).is_none());
        assert!(smith_normal_form(&a).is_none());
    }

    #[test]
    fn declines_non_constant_entries() {
        let a = Matrix::from_rows(vec![
            vec![CasExpr::var("x"), CasExpr::int(1)],
            vec![CasExpr::int(0), CasExpr::int(1)],
        ])
        .expect("rectangular");
        assert!(hermite_normal_form(&a).is_none());
        assert!(smith_normal_form(&a).is_none());
    }
}
