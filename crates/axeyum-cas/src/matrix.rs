//! Symbolic dense linear algebra over the [`CasExpr`](crate::CasExpr) fragment.
//!
//! A [`Matrix`] holds a dense, row-major grid of symbolic entries. Ring
//! operations (`add`, `sub`, `mul`, `determinant`) are carried out with exact
//! `CasExpr` arithmetic and each result entry is pushed through
//! [`expand`](crate::expand) to keep it in canonical polynomial form (falling
//! back to the un-expanded expression when `expand` declines, e.g. on overflow
//! or a transcendental head). This preserves the proof-carrying discipline of
//! the crate: symbolic identities such as `det(A·B) = det(A)·det(B)` are decided
//! by the certified zero-test [`equal`](crate::equal) rather than by string
//! comparison.
//!
//! Two field-level operations, [`Matrix::rref`] and [`Matrix::solve`], require
//! the entries to be **rational constants** (each a [`CasExpr::Const`]); they run
//! exact Gaussian elimination over [`Rational`] and decline (returning `None`)
//! on any non-constant entry.
//!
//! # Determinant strategy
//!
//! [`Matrix::determinant`] uses cofactor (`Laplace`) expansion, which needs only
//! `+`, `−`, and `×` and therefore works for arbitrary symbolic entries. It is
//! `O(n!)` and so intended for small matrices. A fraction-free `Bareiss`
//! elimination would be `O(n³)`, but Bareiss relies on *exact division* of
//! intermediate results, and `CasExpr` exposes no exact-division primitive over
//! the symbolic ring; a Bareiss variant is therefore deferred to a later phase.

use axeyum_ir::Rational;

use crate::{CasExpr, expand};

/// A dense matrix whose entries are symbolic [`CasExpr`] values, stored in
/// row-major order.
///
/// Structural equality (`PartialEq`) compares entries as `CasExpr` trees, so two
/// matrices are equal only if their entries are *syntactically* identical after
/// whatever construction produced them. To compare up to symbolic value-equality,
/// test each entry pair with [`equal`](crate::equal).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Matrix {
    rows: usize,
    cols: usize,
    /// Row-major entries: entry `(row, col)` lives at index `row * cols + col`.
    data: Vec<CasExpr>,
}

/// Expand `expr` to canonical form, falling back to the input when
/// [`expand`](crate::expand) declines (non-polynomial head or overflow). The
/// fallback is always value-equal to the input, so correctness is preserved even
/// when canonicalization is unavailable.
fn simplify_entry(expr: CasExpr) -> CasExpr {
    match expand(&expr) {
        Some(canonical) => canonical,
        None => expr,
    }
}

/// Whether an entry certifiably equals zero via the zero-test.
fn is_certified_zero_entry(entry: &CasExpr) -> bool {
    matches!(
        crate::equal(entry, &CasExpr::zero()),
        crate::ZeroTest::Certified { equal: true, .. }
    )
}

/// Extract the exact rational value of a constant entry, or `None` if the entry
/// is not a bare [`CasExpr::Const`].
fn as_rational(expr: &CasExpr) -> Option<Rational> {
    match expr {
        CasExpr::Const(value) => Some(*value),
        _ => None,
    }
}

/// The submatrix (`minor`) obtained by deleting the first row and column
/// `skip_col` of `rows`.
fn minor(rows: &[Vec<CasExpr>], skip_col: usize) -> Vec<Vec<CasExpr>> {
    rows[1..]
        .iter()
        .map(|row| {
            row.iter()
                .enumerate()
                .filter_map(|(col, entry)| {
                    if col == skip_col {
                        None
                    } else {
                        Some(entry.clone())
                    }
                })
                .collect()
        })
        .collect()
}

/// Cofactor (`Laplace`) expansion of a square grid along its first row. Uses only
/// `+`, `−`, `×`, so it is valid for arbitrary symbolic entries; the result is an
/// un-simplified `CasExpr` sum which the caller canonicalizes.
fn cofactor_det(rows: &[Vec<CasExpr>]) -> CasExpr {
    match rows.len() {
        0 => CasExpr::one(),
        1 => rows[0][0].clone(),
        _ => {
            let terms: Vec<CasExpr> = rows[0]
                .iter()
                .enumerate()
                .map(|(col, entry)| {
                    let sub = cofactor_det(&minor(rows, col));
                    let product = entry.clone() * sub;
                    if col % 2 == 0 { product } else { -product }
                })
                .collect();
            CasExpr::Add(terms)
        }
    }
}

/// Reduce a rational grid to reduced row echelon form (`RREF`) in place using
/// Gauss–Jordan elimination with exact [`Rational`] arithmetic. Returns `None`
/// only if the exact `i128` rational arithmetic overflows; otherwise `Some(())`.
fn reduce_to_rref(grid: &mut [Vec<Rational>]) -> Option<()> {
    let row_count = grid.len();
    if row_count == 0 {
        return Some(());
    }
    let col_count = grid[0].len();
    let mut pivot_row = 0usize;
    for pivot_col in 0..col_count {
        if pivot_row >= row_count {
            break;
        }
        // Select a row at or below `pivot_row` with a non-zero entry in this
        // column; if none exists this column has no pivot, so move on.
        let Some(selected) =
            (pivot_row..row_count).find(|&candidate| !grid[candidate][pivot_col].is_zero())
        else {
            continue;
        };
        grid.swap(pivot_row, selected);
        // Scale the pivot row so the pivot becomes exactly 1.
        let pivot_value = grid[pivot_row][pivot_col];
        for entry in &mut grid[pivot_row] {
            *entry = entry.checked_div(pivot_value)?;
        }
        // Eliminate this column from every other row.
        let pivot_snapshot = grid[pivot_row].clone();
        for (index, row) in grid.iter_mut().enumerate() {
            if index == pivot_row {
                continue;
            }
            let factor = row[pivot_col];
            if factor.is_zero() {
                continue;
            }
            for (entry, pivot_entry) in row.iter_mut().zip(pivot_snapshot.iter()) {
                let scaled = factor.checked_mul(*pivot_entry)?;
                *entry = entry.checked_sub(scaled)?;
            }
        }
        pivot_row += 1;
    }
    Some(())
}

impl Matrix {
    /// Construct a matrix from a flat row-major `data` vector, or `None` if
    /// `data.len()` is not exactly `rows * cols` (or that product overflows).
    #[must_use]
    pub fn new(rows: usize, cols: usize, data: Vec<CasExpr>) -> Option<Matrix> {
        if data.len() != rows.checked_mul(cols)? {
            return None;
        }
        Some(Matrix { rows, cols, data })
    }

    /// Construct a matrix from a vector of rows. Returns `None` if the rows are
    /// ragged (differing lengths). An empty outer vector yields a `0 × 0` matrix.
    #[must_use]
    pub fn from_rows(rows_data: Vec<Vec<CasExpr>>) -> Option<Matrix> {
        let rows = rows_data.len();
        let cols = rows_data.first().map_or(0, Vec::len);
        if rows_data.iter().any(|row| row.len() != cols) {
            return None;
        }
        let data = rows_data.into_iter().flatten().collect();
        Some(Matrix { rows, cols, data })
    }

    /// The `n × n` identity matrix.
    #[must_use]
    pub fn identity(n: usize) -> Matrix {
        let mut data = Vec::with_capacity(n.saturating_mul(n));
        for row in 0..n {
            for col in 0..n {
                data.push(if row == col {
                    CasExpr::one()
                } else {
                    CasExpr::zero()
                });
            }
        }
        Matrix {
            rows: n,
            cols: n,
            data,
        }
    }

    /// The `rows × cols` matrix of zeros.
    #[must_use]
    pub fn zeros(rows: usize, cols: usize) -> Matrix {
        let data = vec![CasExpr::zero(); rows.saturating_mul(cols)];
        Matrix { rows, cols, data }
    }

    /// The number of rows.
    #[must_use]
    pub fn rows(&self) -> usize {
        self.rows
    }

    /// The number of columns.
    #[must_use]
    pub fn cols(&self) -> usize {
        self.cols
    }

    /// A reference to entry `(row, col)`, or `None` if the indices are out of
    /// bounds.
    #[must_use]
    pub fn get(&self, row: usize, col: usize) -> Option<&CasExpr> {
        if row >= self.rows || col >= self.cols {
            return None;
        }
        self.data.get(row * self.cols + col)
    }

    /// Entry `(row, col)`, assuming in-bounds indices (private helper for the
    /// arithmetic kernels, which only ever generate valid indices).
    fn at(&self, row: usize, col: usize) -> &CasExpr {
        &self.data[row * self.cols + col]
    }

    /// The transpose, whose entry `(i, j)` is `self`'s entry `(j, i)`.
    #[must_use]
    pub fn transpose(&self) -> Matrix {
        let mut data = Vec::with_capacity(self.data.len());
        for col in 0..self.cols {
            for row in 0..self.rows {
                data.push(self.at(row, col).clone());
            }
        }
        Matrix {
            rows: self.cols,
            cols: self.rows,
            data,
        }
    }

    /// Whether every off-diagonal entry is (certifiably) zero. `false` if not square.
    #[must_use]
    pub fn is_diagonal(&self) -> bool {
        self.rows == self.cols && self.all_where(|i, j, e| i == j || is_certified_zero_entry(e))
    }

    /// Whether every strictly-below-diagonal entry is zero (upper-triangular).
    /// `false` if not square.
    #[must_use]
    pub fn is_upper_triangular(&self) -> bool {
        self.rows == self.cols && self.all_where(|i, j, e| i <= j || is_certified_zero_entry(e))
    }

    /// Whether every strictly-above-diagonal entry is zero (lower-triangular).
    /// `false` if not square.
    #[must_use]
    pub fn is_lower_triangular(&self) -> bool {
        self.rows == self.cols && self.all_where(|i, j, e| i >= j || is_certified_zero_entry(e))
    }

    /// Whether the matrix is the identity (`1` on the diagonal, `0` off it). `false`
    /// if not square.
    #[must_use]
    pub fn is_identity(&self) -> bool {
        self.rows == self.cols
            && self.all_where(|i, j, e| {
                let target = if i == j {
                    CasExpr::int(1)
                } else {
                    CasExpr::zero()
                };
                matches!(
                    crate::equal(e, &target),
                    crate::ZeroTest::Certified { equal: true, .. }
                )
            })
    }

    /// Test a predicate `(row, col, entry)` on every entry.
    fn all_where(&self, predicate: impl Fn(usize, usize, &CasExpr) -> bool) -> bool {
        (0..self.rows).all(|i| (0..self.cols).all(|j| predicate(i, j, self.at(i, j))))
    }

    /// Entry-wise sum `self + other`, each result entry canonicalized via
    /// [`expand`](crate::expand). Returns `None` if the shapes differ.
    #[must_use]
    pub fn add(&self, other: &Matrix) -> Option<Matrix> {
        if self.rows != other.rows || self.cols != other.cols {
            return None;
        }
        let data = self
            .data
            .iter()
            .zip(other.data.iter())
            .map(|(left, right)| simplify_entry(left.clone() + right.clone()))
            .collect();
        Some(Matrix {
            rows: self.rows,
            cols: self.cols,
            data,
        })
    }

    /// Entry-wise difference `self − other`, each result entry canonicalized via
    /// [`expand`](crate::expand). Returns `None` if the shapes differ.
    #[must_use]
    pub fn sub(&self, other: &Matrix) -> Option<Matrix> {
        if self.rows != other.rows || self.cols != other.cols {
            return None;
        }
        let data = self
            .data
            .iter()
            .zip(other.data.iter())
            .map(|(left, right)| simplify_entry(left.clone() - right.clone()))
            .collect();
        Some(Matrix {
            rows: self.rows,
            cols: self.cols,
            data,
        })
    }

    /// The **Hadamard** (entry-wise) product `self ∘ other`, each entry
    /// canonicalized. `None` if the shapes differ.
    #[must_use]
    pub fn hadamard(&self, other: &Matrix) -> Option<Matrix> {
        if self.rows != other.rows || self.cols != other.cols {
            return None;
        }
        let data = self
            .data
            .iter()
            .zip(&other.data)
            .map(|(a, b)| simplify_entry(a.clone() * b.clone()))
            .collect();
        Some(Matrix {
            rows: self.rows,
            cols: self.cols,
            data,
        })
    }

    /// The **Kronecker** product `self ⊗ other` — the `(rows·other.rows) ×
    /// (cols·other.cols)` block matrix whose `(i,j)` block is `self[i][j]·other`.
    #[must_use]
    pub fn kronecker(&self, other: &Matrix) -> Matrix {
        let rows = self.rows * other.rows;
        let cols = self.cols * other.cols;
        let mut data = Vec::with_capacity(rows * cols);
        for i in 0..rows {
            for j in 0..cols {
                let entry = self.at(i / other.rows, j / other.cols).clone()
                    * other.at(i % other.rows, j % other.cols).clone();
                data.push(simplify_entry(entry));
            }
        }
        Matrix { rows, cols, data }
    }

    /// Matrix product `self · other`, each result entry canonicalized via
    /// [`expand`](crate::expand). Returns `None` if `self.cols != other.rows`.
    #[must_use]
    pub fn mul(&self, other: &Matrix) -> Option<Matrix> {
        if self.cols != other.rows {
            return None;
        }
        let mut data = Vec::with_capacity(self.rows.saturating_mul(other.cols));
        for row in 0..self.rows {
            for col in 0..other.cols {
                let products: Vec<CasExpr> = (0..self.cols)
                    .map(|inner| self.at(row, inner).clone() * other.at(inner, col).clone())
                    .collect();
                data.push(simplify_entry(CasExpr::Add(products)));
            }
        }
        Some(Matrix {
            rows: self.rows,
            cols: other.cols,
            data,
        })
    }

    /// The exact symbolic determinant of a square matrix, via cofactor
    /// (`Laplace`) expansion, canonicalized with [`expand`](crate::expand).
    ///
    /// Returns `None` if the matrix is not square. The algorithm uses only
    /// `+`, `−`, `×` (no division), so it is correct for arbitrary symbolic
    /// entries, but it is `O(n!)` and therefore meant for small matrices — see
    /// the module-level note on why fraction-free `Bareiss` elimination is not
    /// used here.
    #[must_use]
    pub fn determinant(&self) -> Option<CasExpr> {
        if self.rows != self.cols {
            return None;
        }
        let raw = cofactor_det(&self.to_grid());
        Some(simplify_entry(raw))
    }

    /// The `(i, j)` cofactor `(−1)^{i+j}·M_{ij}` where `M_{ij}` is the minor
    /// determinant (delete row `i`, column `j`). Valid for arbitrary symbolic
    /// entries. `None` if the matrix is not square or smaller than `1×1`.
    #[must_use]
    pub fn cofactor(&self, row: usize, col: usize) -> Option<CasExpr> {
        if self.rows != self.cols || self.rows == 0 || row >= self.rows || col >= self.cols {
            return None;
        }
        let grid = self.to_grid();
        // Submatrix with `row` and `col` removed.
        let sub: Vec<Vec<CasExpr>> = grid
            .iter()
            .enumerate()
            .filter(|(r, _)| *r != row)
            .map(|(_, source)| {
                source
                    .iter()
                    .enumerate()
                    .filter(|(c, _)| *c != col)
                    .map(|(_, entry)| entry.clone())
                    .collect()
            })
            .collect();
        let minor_det = cofactor_det(&sub);
        let signed = if (row + col).is_multiple_of(2) {
            minor_det
        } else {
            -minor_det
        };
        Some(simplify_entry(signed))
    }

    /// The **adjugate** (classical adjoint) — the transpose of the cofactor matrix,
    /// satisfying `M·adj(M) = det(M)·I`. Valid for arbitrary symbolic square
    /// matrices. `None` if not square.
    #[must_use]
    pub fn adjugate(&self) -> Option<Matrix> {
        if self.rows != self.cols {
            return None;
        }
        let n = self.rows;
        let mut rows: Vec<Vec<CasExpr>> = Vec::with_capacity(n);
        for i in 0..n {
            let mut row = Vec::with_capacity(n);
            for j in 0..n {
                // adj[i][j] = cofactor(j, i) (transpose).
                row.push(self.cofactor(j, i)?);
            }
            rows.push(row);
        }
        Matrix::from_rows(rows)
    }

    /// The matrix power `Mᵏ` (with `M⁰ = I`) of a square matrix, by repeated
    /// multiplication. `None` if the matrix is not square.
    #[must_use]
    pub fn pow(&self, exponent: u32) -> Option<Matrix> {
        if self.rows != self.cols {
            return None;
        }
        let mut result = Matrix::identity(self.rows);
        for _ in 0..exponent {
            result = result.mul(self)?;
        }
        Some(result)
    }

    /// Whether the matrix equals its transpose (entrywise, up to certified
    /// value-equality). `false` if not square.
    #[must_use]
    pub fn is_symmetric(&self) -> bool {
        if self.rows != self.cols {
            return false;
        }
        for i in 0..self.rows {
            for j in (i + 1)..self.cols {
                if !matches!(
                    crate::equal(self.at(i, j), self.at(j, i)),
                    crate::ZeroTest::Certified { equal: true, .. }
                ) {
                    return false;
                }
            }
        }
        true
    }

    /// This matrix as a nested row grid of cloned `CasExpr` entries.
    fn to_grid(&self) -> Vec<Vec<CasExpr>> {
        (0..self.rows)
            .map(|row| {
                (0..self.cols)
                    .map(|col| self.at(row, col).clone())
                    .collect()
            })
            .collect()
    }

    /// The determinant of a **rational-constant** square matrix by **Bareiss**
    /// fraction-free Gaussian elimination — `O(n³)` with exact intermediate results
    /// (unlike the `O(n!)` [`determinant`](Self::determinant) cofactor expansion, so
    /// preferable for larger matrices). `None` if the matrix is not square, has a
    /// non-constant entry, or on overflow.
    #[must_use]
    pub fn bareiss_determinant(&self) -> Option<CasExpr> {
        if self.rows != self.cols {
            return None;
        }
        let n = self.rows;
        let mut m = self.to_rational_grid()?;
        let mut sign = 1i128;
        let mut previous = Rational::integer(1);
        for k in 0..n {
            if m[k][k].is_zero() {
                // Pivot: swap in a nonzero row below; a zero column ⇒ det 0.
                match (k + 1..n).find(|&r| !m[r][k].is_zero()) {
                    Some(r) => {
                        m.swap(k, r);
                        sign = -sign;
                    }
                    None => return Some(CasExpr::zero()),
                }
            }
            let pivot = m[k][k];
            for i in (k + 1)..n {
                for j in (k + 1)..n {
                    let cross = pivot
                        .checked_mul(m[i][j])?
                        .checked_sub(m[i][k].checked_mul(m[k][j])?)?;
                    m[i][j] = cross.checked_div(previous)?;
                }
            }
            previous = pivot;
        }
        let det = m[n - 1][n - 1].checked_mul(Rational::integer(sign))?;
        Some(CasExpr::Const(det))
    }

    /// This matrix as a nested grid of exact rationals, or `None` if any entry is
    /// not a bare [`CasExpr::Const`].
    fn to_rational_grid(&self) -> Option<Vec<Vec<Rational>>> {
        let mut grid = Vec::with_capacity(self.rows);
        for row in 0..self.rows {
            let mut converted = Vec::with_capacity(self.cols);
            for col in 0..self.cols {
                converted.push(as_rational(self.at(row, col))?);
            }
            grid.push(converted);
        }
        Some(grid)
    }

    /// The reduced row echelon form (`RREF`), for a matrix whose entries are all
    /// rational constants.
    ///
    /// Returns `None` if any entry is non-constant (a [`CasExpr`] other than
    /// [`CasExpr::Const`]) or if exact `i128` rational arithmetic overflows.
    /// Elimination is exact Gauss–Jordan over [`Rational`].
    #[must_use]
    pub fn rref(&self) -> Option<Matrix> {
        let mut grid = self.to_rational_grid()?;
        reduce_to_rref(&mut grid)?;
        let mut data = Vec::with_capacity(self.rows.saturating_mul(self.cols));
        for row in &grid {
            for value in row {
                data.push(CasExpr::Const(*value));
            }
        }
        Some(Matrix {
            rows: self.rows,
            cols: self.cols,
            data,
        })
    }

    /// Solve the linear system `self · x = rhs` for a **square, rational-constant**
    /// coefficient matrix `self` and rational-constant right-hand side `rhs`.
    ///
    /// `rhs` is treated as a stack of column vectors (shape `n × k`), and the
    /// returned matrix is the solution `x` of the same shape. Returns `None` when:
    /// `self` is not square; `rhs` has a different number of rows than `self`;
    /// either operand has a non-constant entry; `self` is singular (no unique
    /// solution); or exact `i128` rational arithmetic overflows.
    ///
    /// The method augments `[self | rhs]`, reduces to `RREF`, and confirms the
    /// left block became the identity (which holds iff `self` is invertible); the
    /// right block is then the exact solution.
    #[must_use]
    pub fn solve(&self, rhs: &Matrix) -> Option<Matrix> {
        if self.rows != self.cols || rhs.rows != self.rows {
            return None;
        }
        let size = self.rows;
        let width = rhs.cols;
        let left = self.to_rational_grid()?;
        let right = rhs.to_rational_grid()?;

        // Build the augmented grid `[left | right]`.
        let mut aug: Vec<Vec<Rational>> = Vec::with_capacity(size);
        for (left_row, right_row) in left.iter().zip(right.iter()) {
            let mut combined = left_row.clone();
            combined.extend_from_slice(right_row);
            aug.push(combined);
        }
        reduce_to_rref(&mut aug)?;

        // The left block must be the identity for a unique solution to exist.
        for (row_idx, row) in aug.iter().enumerate().take(size) {
            for (col_idx, value) in row.iter().enumerate().take(size) {
                let expected = if row_idx == col_idx {
                    Rational::integer(1)
                } else {
                    Rational::zero()
                };
                if *value != expected {
                    return None;
                }
            }
        }

        // The right block is the solution.
        let mut data = Vec::with_capacity(size.saturating_mul(width));
        for row in aug.iter().take(size) {
            for value in row.iter().skip(size).take(width) {
                data.push(CasExpr::Const(*value));
            }
        }
        Some(Matrix {
            rows: size,
            cols: width,
            data,
        })
    }

    /// A basis for the (right) null space `{x : self·x = 0}` of a
    /// **rational-constant** matrix, each basis vector returned as an `n × 1`
    /// column [`Matrix`] (where `n = self.cols()`).
    ///
    /// An empty result means the null space is trivial (only the zero vector).
    /// The construction is the standard free-variable reading of the reduced row
    /// echelon form: each non-pivot ("free") column yields one basis vector with a
    /// `1` in that free coordinate and `−rref[row][free]` in each pivot coordinate.
    /// Every returned vector `v` satisfies `self·v = 0` exactly, which the caller
    /// can re-check with the certified matrix product.
    ///
    /// Returns `None` if any entry is non-constant (a [`CasExpr`] other than
    /// [`CasExpr::Const`]) or if exact `i128` rational arithmetic overflows.
    #[must_use]
    pub fn null_space(&self) -> Option<Vec<Matrix>> {
        let mut grid = self.to_rational_grid()?;
        reduce_to_rref(&mut grid)?;
        let width = self.cols;

        // The pivot column of each pivot row, in row order. Gauss–Jordan places
        // the pivot rows first (rows `0..pivot_count`), so `pivot_cols[r]` is the
        // pivot column of `grid[r]`. Zero rows have no pivot and are skipped.
        let mut pivot_cols: Vec<usize> = Vec::new();
        let mut is_pivot = vec![false; width];
        for row in &grid {
            if let Some(col) = (0..width).find(|&c| !row[c].is_zero()) {
                pivot_cols.push(col);
                is_pivot[col] = true;
            }
        }

        let mut basis = Vec::new();
        for free in (0..width).filter(|&c| !is_pivot[c]) {
            let mut coords = vec![Rational::zero(); width];
            coords[free] = Rational::integer(1);
            for (row_index, &pivot_col) in pivot_cols.iter().enumerate() {
                coords[pivot_col] = grid[row_index][free].checked_neg()?;
            }
            let data = coords.into_iter().map(CasExpr::Const).collect();
            basis.push(Matrix {
                rows: width,
                cols: 1,
                data,
            });
        }
        Some(basis)
    }

    /// The LU decomposition of a **square, invertible, rational-constant** matrix
    /// with partial pivoting: returns `(P, L, U)` with `P·A = L·U`, where `P` is a
    /// permutation matrix, `L` is unit-lower-triangular, and `U` is
    /// upper-triangular. Exact Doolittle elimination over [`Rational`].
    ///
    /// The identity `P·A = L·U` is the certificate — re-multiply and compare with
    /// the certified matrix product. Returns `None` if the matrix is not square, is
    /// non-constant, is singular (no nonzero pivot in some column), or on overflow.
    #[must_use]
    pub fn lu(&self) -> Option<(Matrix, Matrix, Matrix)> {
        if self.rows != self.cols {
            return None;
        }
        let n = self.rows;
        let mut upper = self.to_rational_grid()?;
        let mut lower = vec![vec![Rational::zero(); n]; n];
        let mut permutation: Vec<usize> = (0..n).collect();

        for pivot_col in 0..n {
            // Partial pivot: a nonzero entry at or below the diagonal.
            let pivot_row = (pivot_col..n).find(|&row| !upper[row][pivot_col].is_zero())?;
            if pivot_row != pivot_col {
                upper.swap(pivot_col, pivot_row);
                lower.swap(pivot_col, pivot_row);
                permutation.swap(pivot_col, pivot_row);
            }
            lower[pivot_col][pivot_col] = Rational::integer(1);
            let pivot_snapshot = upper[pivot_col].clone();
            let pivot_value = pivot_snapshot[pivot_col];
            for row in (pivot_col + 1)..n {
                let factor = upper[row][pivot_col].checked_div(pivot_value)?;
                lower[row][pivot_col] = factor;
                for (col, target) in upper[row].iter_mut().enumerate().skip(pivot_col) {
                    let scaled = factor.checked_mul(pivot_snapshot[col])?;
                    *target = target.checked_sub(scaled)?;
                }
            }
        }

        let from_grid = |grid: &[Vec<Rational>]| -> Matrix {
            let data = grid
                .iter()
                .flat_map(|row| row.iter().map(|value| CasExpr::Const(*value)))
                .collect();
            Matrix {
                rows: n,
                cols: n,
                data,
            }
        };
        // Permutation matrix: row i selects original row permutation[i].
        let mut perm_data = vec![CasExpr::zero(); n * n];
        for (row, &source) in permutation.iter().enumerate() {
            perm_data[row * n + source] = CasExpr::one();
        }
        let permutation_matrix = Matrix {
            rows: n,
            cols: n,
            data: perm_data,
        };
        Some((permutation_matrix, from_grid(&lower), from_grid(&upper)))
    }
}

impl std::fmt::Display for Matrix {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for row in 0..self.rows {
            if row > 0 {
                writeln!(formatter)?;
            }
            formatter.write_str("[")?;
            for col in 0..self.cols {
                if col > 0 {
                    formatter.write_str(", ")?;
                }
                write!(formatter, "{}", self.at(row, col))?;
            }
            formatter.write_str("]")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::Matrix;
    use crate::{CasExpr, ZeroTest, equal};

    /// A named symbolic variable.
    fn var(name: &str) -> CasExpr {
        CasExpr::var(name)
    }

    /// An integer constant entry.
    fn konst(value: i128) -> CasExpr {
        CasExpr::int(value)
    }

    /// Assert two `CasExpr` values are certified equal by the decidable zero-test.
    fn assert_expr_equal(left: &CasExpr, right: &CasExpr) {
        match equal(left, right) {
            ZeroTest::Certified {
                equal: is_equal,
                witness,
            } => {
                assert!(is_equal, "expected equal; difference witness = {witness:?}");
            }
            ZeroTest::Unknown => panic!("expected a decidable (Certified) result"),
        }
    }

    /// Assert two matrices have the same shape and certified-equal entries.
    fn assert_matrix_equal(left: &Matrix, right: &Matrix) {
        assert_eq!(left.rows(), right.rows(), "row count mismatch");
        assert_eq!(left.cols(), right.cols(), "column count mismatch");
        for row in 0..left.rows() {
            for col in 0..left.cols() {
                assert_expr_equal(
                    left.get(row, col).expect("in bounds"),
                    right.get(row, col).expect("in bounds"),
                );
            }
        }
    }

    #[test]
    fn identity_is_multiplicative_unit() {
        // A · I = A and I · A = A for a symbolic 2×2 matrix.
        let matrix = Matrix::from_rows(vec![vec![var("a"), var("b")], vec![var("c"), var("d")]])
            .expect("rectangular");
        let identity = Matrix::identity(2);
        assert_matrix_equal(&matrix.mul(&identity).expect("conformable"), &matrix);
        assert_matrix_equal(&identity.mul(&matrix).expect("conformable"), &matrix);
    }

    #[test]
    fn determinant_of_identity_is_one() {
        for size in 1..=4 {
            let det = Matrix::identity(size).determinant().expect("square");
            assert_expr_equal(&det, &CasExpr::one());
        }
    }

    #[test]
    fn determinant_two_by_two_numeric() {
        // det [[1, 2], [3, 4]] = 1·4 − 2·3 = −2.
        let matrix = Matrix::from_rows(vec![vec![konst(1), konst(2)], vec![konst(3), konst(4)]])
            .expect("rectangular");
        assert_expr_equal(&matrix.determinant().expect("square"), &konst(-2));
    }

    #[test]
    fn determinant_two_by_two_symbolic() {
        // det [[a, b], [c, d]] = a·d − b·c.
        let matrix = Matrix::from_rows(vec![vec![var("a"), var("b")], vec![var("c"), var("d")]])
            .expect("rectangular");
        let claimed = var("a") * var("d") - var("b") * var("c");
        assert_expr_equal(&matrix.determinant().expect("square"), &claimed);
    }

    #[test]
    fn determinant_three_by_three_numeric() {
        // A well-known example with determinant −306.
        let matrix = Matrix::from_rows(vec![
            vec![konst(6), konst(1), konst(1)],
            vec![konst(4), konst(-2), konst(5)],
            vec![konst(2), konst(8), konst(7)],
        ])
        .expect("rectangular");
        assert_expr_equal(&matrix.determinant().expect("square"), &konst(-306));
    }

    #[test]
    fn determinant_three_by_three_symbolic() {
        // The circulant-like matrix [[x,1,0],[0,x,1],[1,0,x]] has det = x³ + 1.
        let matrix = Matrix::from_rows(vec![
            vec![var("x"), konst(1), konst(0)],
            vec![konst(0), var("x"), konst(1)],
            vec![konst(1), konst(0), var("x")],
        ])
        .expect("rectangular");
        let claimed = var("x").pow(3) + konst(1);
        assert_expr_equal(&matrix.determinant().expect("square"), &claimed);
    }

    #[test]
    fn determinant_of_non_square_is_none() {
        let matrix = Matrix::from_rows(vec![
            vec![konst(1), konst(2), konst(3)],
            vec![konst(4), konst(5), konst(6)],
        ])
        .expect("rectangular");
        assert!(matrix.determinant().is_none());
    }

    #[test]
    fn determinant_is_multiplicative_numeric() {
        // det(A·B) = det(A)·det(B) for concrete 2×2 matrices, certified by `equal`.
        let first = Matrix::from_rows(vec![vec![konst(1), konst(2)], vec![konst(3), konst(4)]])
            .expect("rectangular");
        let second = Matrix::from_rows(vec![vec![konst(0), konst(1)], vec![konst(5), konst(6)]])
            .expect("rectangular");
        let product = first.mul(&second).expect("conformable");
        let lhs = product.determinant().expect("square");
        let rhs = first.determinant().expect("square") * second.determinant().expect("square");
        assert_expr_equal(&lhs, &rhs);
    }

    #[test]
    fn determinant_is_multiplicative_symbolic() {
        // det(A·B) = det(A)·det(B) with fully symbolic 2×2 entries (Cauchy–Binet).
        let first = Matrix::from_rows(vec![vec![var("a"), var("b")], vec![var("c"), var("d")]])
            .expect("rectangular");
        let second = Matrix::from_rows(vec![vec![var("e"), var("f")], vec![var("g"), var("h")]])
            .expect("rectangular");
        let product = first.mul(&second).expect("conformable");
        let lhs = product.determinant().expect("square");
        let rhs = first.determinant().expect("square") * second.determinant().expect("square");
        assert_expr_equal(&lhs, &rhs);
    }

    #[test]
    fn transpose_is_an_involution() {
        let matrix = Matrix::from_rows(vec![
            vec![var("a"), var("b"), var("c")],
            vec![var("d"), var("e"), var("f")],
        ])
        .expect("rectangular");
        // Transpose swaps the shape...
        let transposed = matrix.transpose();
        assert_eq!(transposed.rows(), matrix.cols());
        assert_eq!(transposed.cols(), matrix.rows());
        // ...and applying it twice returns the original, exactly (no arithmetic).
        assert_eq!(matrix.transpose().transpose(), matrix);
    }

    #[test]
    fn add_and_sub_are_inverse() {
        let first = Matrix::from_rows(vec![vec![var("a"), konst(2)], vec![konst(3), var("b")]])
            .expect("rectangular");
        let second = Matrix::from_rows(vec![vec![konst(5), var("c")], vec![var("d"), konst(7)]])
            .expect("rectangular");
        let sum = first.add(&second).expect("same shape");
        let recovered = sum.sub(&second).expect("same shape");
        assert_matrix_equal(&recovered, &first);
    }

    #[test]
    fn add_shape_mismatch_is_none() {
        let first = Matrix::zeros(2, 2);
        let second = Matrix::zeros(2, 3);
        assert!(first.add(&second).is_none());
        assert!(first.sub(&second).is_none());
    }

    #[test]
    fn mul_shape_mismatch_is_none() {
        let first = Matrix::zeros(2, 3);
        let second = Matrix::zeros(2, 2);
        assert!(first.mul(&second).is_none());
    }

    #[test]
    fn mul_numeric_known_product() {
        // [[1,2],[3,4]] · [[0,1],[5,6]] = [[10,13],[20,27]].
        let first = Matrix::from_rows(vec![vec![konst(1), konst(2)], vec![konst(3), konst(4)]])
            .expect("rectangular");
        let second = Matrix::from_rows(vec![vec![konst(0), konst(1)], vec![konst(5), konst(6)]])
            .expect("rectangular");
        let expected =
            Matrix::from_rows(vec![vec![konst(10), konst(13)], vec![konst(20), konst(27)]])
                .expect("rectangular");
        assert_matrix_equal(&first.mul(&second).expect("conformable"), &expected);
    }

    #[test]
    fn rref_of_singular_numeric_matrix() {
        // The classic rank-2 matrix reduces to [[1,0,-1],[0,1,2],[0,0,0]].
        let matrix = Matrix::from_rows(vec![
            vec![konst(1), konst(2), konst(3)],
            vec![konst(4), konst(5), konst(6)],
            vec![konst(7), konst(8), konst(9)],
        ])
        .expect("rectangular");
        let expected = Matrix::from_rows(vec![
            vec![konst(1), konst(0), konst(-1)],
            vec![konst(0), konst(1), konst(2)],
            vec![konst(0), konst(0), konst(0)],
        ])
        .expect("rectangular");
        assert_matrix_equal(&matrix.rref().expect("constant entries"), &expected);
    }

    #[test]
    fn rref_declines_non_constant_entries() {
        let matrix = Matrix::from_rows(vec![vec![var("x"), konst(1)], vec![konst(2), konst(3)]])
            .expect("rectangular");
        assert!(matrix.rref().is_none());
    }

    #[test]
    fn solve_recovers_solution_and_substitutes_back() {
        // A·x = rhs with A = [[1,1],[1,-1]], rhs = [[3],[1]] → x = [[2],[1]].
        let coeff = Matrix::from_rows(vec![vec![konst(1), konst(1)], vec![konst(1), konst(-1)]])
            .expect("rectangular");
        let rhs = Matrix::from_rows(vec![vec![konst(3)], vec![konst(1)]]).expect("column");
        let solution = coeff.solve(&rhs).expect("nonsingular");
        assert_matrix_equal(
            &solution,
            &Matrix::from_rows(vec![vec![konst(2)], vec![konst(1)]]).expect("column"),
        );
        // Substitute back: A·x must equal rhs entry-for-entry (certified).
        let reconstructed = coeff.mul(&solution).expect("conformable");
        assert_matrix_equal(&reconstructed, &rhs);
    }

    #[test]
    fn solve_with_rational_solution() {
        // A = [[2,1],[1,3]], rhs = [[1],[2]] → x = [[1/5],[3/5]].
        let coeff = Matrix::from_rows(vec![vec![konst(2), konst(1)], vec![konst(1), konst(3)]])
            .expect("rectangular");
        let rhs = Matrix::from_rows(vec![vec![konst(1)], vec![konst(2)]]).expect("column");
        let solution = coeff.solve(&rhs).expect("nonsingular");
        let expected = Matrix::from_rows(vec![vec![CasExpr::rat(1, 5)], vec![CasExpr::rat(3, 5)]])
            .expect("column");
        assert_matrix_equal(&solution, &expected);
        // And it satisfies the system.
        assert_matrix_equal(&coeff.mul(&solution).expect("conformable"), &rhs);
    }

    #[test]
    fn solve_multiple_right_hand_sides() {
        // Solving against the identity computes the inverse; A·A⁻¹ = I.
        let coeff = Matrix::from_rows(vec![vec![konst(4), konst(7)], vec![konst(2), konst(6)]])
            .expect("rectangular");
        let inverse = coeff.solve(&Matrix::identity(2)).expect("nonsingular");
        assert_matrix_equal(
            &coeff.mul(&inverse).expect("conformable"),
            &Matrix::identity(2),
        );
    }

    #[test]
    fn solve_singular_is_none() {
        let coeff = Matrix::from_rows(vec![vec![konst(1), konst(2)], vec![konst(2), konst(4)]])
            .expect("rectangular");
        let rhs = Matrix::from_rows(vec![vec![konst(1)], vec![konst(2)]]).expect("column");
        assert!(coeff.solve(&rhs).is_none());
    }

    #[test]
    fn solve_non_constant_is_none() {
        let coeff = Matrix::from_rows(vec![vec![var("x"), konst(1)], vec![konst(0), konst(1)]])
            .expect("rectangular");
        let rhs = Matrix::from_rows(vec![vec![konst(1)], vec![konst(1)]]).expect("column");
        assert!(coeff.solve(&rhs).is_none());
    }

    #[test]
    fn constructors_validate_shape() {
        // Wrong-length flat data is rejected.
        assert!(Matrix::new(2, 2, vec![konst(1), konst(2), konst(3)]).is_none());
        // Ragged rows are rejected.
        assert!(Matrix::from_rows(vec![vec![konst(1), konst(2)], vec![konst(3)]]).is_none());
        // A well-formed construction round-trips through the accessors.
        let matrix = Matrix::new(2, 2, vec![konst(1), konst(2), konst(3), konst(4)])
            .expect("correct length");
        assert_eq!(matrix.rows(), 2);
        assert_eq!(matrix.cols(), 2);
        assert_expr_equal(matrix.get(1, 0).expect("in bounds"), &konst(3));
        assert!(matrix.get(2, 0).is_none());
    }

    #[test]
    fn display_puts_rows_on_separate_lines() {
        let matrix = Matrix::from_rows(vec![vec![konst(1), konst(2)], vec![konst(3), konst(4)]])
            .expect("rectangular");
        assert_eq!(format!("{matrix}"), "[1, 2]\n[3, 4]");
    }
}
