//! The cup product on simplicial cohomology over `F_2` and `Q`, via the
//! Alexander-Whitney diagonal on cocycle representatives (item 8, wave four).
//!
//! # What this computes
//!
//! A cochain of degree `p` is represented as a length-`n_p` column [`Matrix`]
//! (one coefficient per `p`-simplex, in the complex's own canonical order).
//! The coboundary `delta^p : C^p -> C^{p+1}` is `boundary_matrix(complex, p +
//! 1)` **transposed** (exactly [`super::cohomology`]'s own convention: `d_k`
//! maps `C_k -> C_{k-1}`, so `d_k^T` maps `C^{k-1} -> C^k`). A basis of
//! `H^p(complex; R)` -- a genuine extension of a basis of the coboundary
//! image `B^p = im(delta^{p-1})` to a basis of the cocycle kernel `Z^p =
//! ker(delta^p)` -- is chosen the SAME way [`super::induced`] chooses a
//! homology basis (`super::induced::choose_homology_basis`, reused
//! verbatim for `R = Q`; `choose_cohomology_basis_mod2` mirrors it entry
//! for entry for `R = F_2`, since no general matrix null-space/rref over
//! `F_2` exists elsewhere in this crate -- `gf2.rs`/`gfp.rs` are univariate
//! polynomial arithmetic, not matrix linear algebra).
//!
//! The **cup product** of cocycle representatives `alpha` (degree `p`) and
//! `beta` (degree `q`) is the Alexander-Whitney diagonal
//! (`alexander_whitney_cup`): for every `(p+q)`-simplex `sigma = [v_0 < v_1
//! < ... < v_{p+q}]` (the complex's own sorted vertex order, the total order
//! AW is stated over), `(alpha ∪ beta)(sigma) = alpha(front_p(sigma)) *
//! beta(back_q(sigma))`, where `front_p` is the first `p + 1` vertices and
//! `back_q` the last `q + 1` (sharing vertex `v_p`). [`cup_product_q`] and
//! [`cup_product_f2`] compute this on every pair of the two degrees' chosen
//! cocycle bases, express each product's class in the degree-`(p+q)` basis by
//! the same `[boundary_basis | homology_basis]` solve [`super::induced`] uses
//! for induced maps, and record the whole table.
//!
//! # What is certified
//!
//! [`CupProductCertificate::verify`] re-derives every claim:
//!
//! - every recorded basis at degrees `p`, `q`, `p+q` matches one freshly
//!   rebuilt (same `R`-specific basis-selection algorithm);
//! - every recorded basis vector at every one of those three degrees is a
//!   genuine cocycle (`delta * v = 0`, checked directly);
//! - each recorded basis is a genuine EXTENSION of its boundary basis to the
//!   FULL cocycle space, not a proper subspace of it (a rank identity against
//!   the freshly computed cocycle-space dimension, mirroring
//!   [`super::induced`]'s `basis_is_a_genuine_extension`);
//! - every recorded table entry is recomputed fresh (rebuild the AW cochain,
//!   check it is itself a cocycle, solve for its class) and compared;
//! - **graded commutativity up to sign**: for every basis pair `(alpha_i,
//!   beta_j)`, `beta_j ∪ alpha_i` is recomputed fresh and checked to equal
//!   `(-1)^{pq} * (alpha_i ∪ beta_j)`'s recorded class (over `F_2` the sign
//!   is always `+1`, since `-1 = 1 mod 2` -- so this specializes to plain
//!   commutativity there, which is exactly what makes RP^2's `alpha ∪ alpha
//!   != 0` fixture meaningful rather than vacuous).
//!
//! What is **not** independently re-derived: given the bases are already
//! confirmed genuine, `solve_via_rref`/`solve_mod2`'s answer is the UNIQUE
//! coefficient vector of a full-column-rank consistent system, so re-running
//! it and comparing catches a forged `table` entry but not a bug shared
//! between production and the same solve routine (the caveat every certified
//! producer in this crate states for its own linear-solve step).
//!
//! # The finding the item names: a ring distinguishes what a group cannot
//!
//! The torus (`fixtures::torus_7v`) and the wedge `S^1 v S^1 v S^2`
//! (`wedge_two_circles_and_a_sphere`) have IDENTICAL Betti numbers `(1, 2,
//! 1)` -- so no group-valued invariant (homology, at any coefficient ring)
//! can tell them apart. Their cup product rings differ: the torus's two
//! `H^1` generators cup to a nonzero class in `H^2` (the standard fact that
//! its cohomology ring is the exterior algebra on two degree-1 generators),
//! while the wedge's two `H^1` generators (one per circle summand) cup to
//! ZERO -- structurally, because every `2`-simplex of the wedge belongs to
//! the sphere summand alone, so a cocycle supported on one circle's edges
//! always pairs to `0` against any `2`-simplex's front/back faces (no
//! `2`-simplex ever touches a circle edge at all, and the two circles share
//! only the wedge basepoint, a `0`-simplex). `alpha ∪ alpha` for the
//! generator of `H^1(RP^2; F_2)` is nonzero (`RP^2`'s `F_2` cohomology ring
//! is the truncated polynomial ring `F_2[alpha]/(alpha^3)`).
//!
//! # Cost profile
//!
//! The `F_2` linear algebra here (`rref_mod2_inplace`, `null_space_mod2`)
//! is a plain bit-grid Gauss-Jordan, `O(rows * cols^2)` like
//! `super::coefficients::rank_mod2`; the `Q` path reuses [`super::induced`]'s
//! existing `O(n^2)`-rank-call greedy basis selection. No fixture exercised
//! here approaches the parent module's own unimodularity-ceiling scale (the
//! largest is the 7-vertex/21-edge/14-triangle torus).

use std::collections::BTreeMap;

use axeyum_ir::Rational;

use super::induced::{choose_homology_basis, columns_to_matrix, rank_of_columns, solve_via_rref};
use super::{SimplicialComplex, boundary_matrix, is_zero_matrix};
use crate::normalforms::certify_product_equals;
use crate::{CasExpr, Matrix};

// ---------------------------------------------------------------------
// GF(2) linear algebra: a plain bit-grid Gauss-Jordan, mirroring the Q
// path's `Matrix::rref`/`Matrix::null_space` step for step, since no general
// matrix null-space/rref over F_2 exists elsewhere in this crate.
// ---------------------------------------------------------------------

/// The exact rational value of a constant entry, or `None` for a non-constant
/// one.
fn as_rational(expr: &CasExpr) -> Option<Rational> {
    match expr {
        CasExpr::Const(value) => Some(*value),
        _ => None,
    }
}

/// One entry reduced mod 2 (`0` or `1`), or `None` if it is not an
/// integer-valued constant.
fn mod2_of(expr: &CasExpr) -> Option<u8> {
    let value = as_rational(expr)?;
    if value.denominator() != 1 {
        return None;
    }
    Some(u8::from(value.numerator().rem_euclid(2) != 0))
}

/// `matrix` as a `rows x cols` bit grid, each entry reduced mod 2.
fn matrix_to_bits(matrix: &Matrix) -> Option<Vec<Vec<u8>>> {
    let mut grid = Vec::with_capacity(matrix.rows());
    for row in 0..matrix.rows() {
        let mut bits = Vec::with_capacity(matrix.cols());
        for col in 0..matrix.cols() {
            bits.push(mod2_of(matrix.get(row, col)?)?);
        }
        grid.push(bits);
    }
    Some(grid)
}

/// Whether every entry of a column vector is `0` mod 2.
fn is_zero_bits(vector: &Matrix) -> Option<bool> {
    for row in 0..vector.rows() {
        if mod2_of(vector.get(row, 0)?)? != 0 {
            return Some(false);
        }
    }
    Some(true)
}

/// `matrix * vector` mod 2, as a fresh column [`Matrix`] of `0`/`1` entries.
/// Returns `None` on a shape mismatch or a non-integer entry.
fn mat_vec_mod2(matrix: &Matrix, vector: &Matrix) -> Option<Matrix> {
    if matrix.cols() != vector.rows() || vector.cols() != 1 {
        return None;
    }
    let grid = matrix_to_bits(matrix)?;
    let mut vector_bits = Vec::with_capacity(vector.rows());
    for row in 0..vector.rows() {
        vector_bits.push(mod2_of(vector.get(row, 0)?)?);
    }
    let mut data = Vec::with_capacity(matrix.rows());
    for row_bits in &grid {
        let mut acc = 0u8;
        for (&bit, &v) in row_bits.iter().zip(vector_bits.iter()) {
            acc ^= bit & v;
        }
        data.push(CasExpr::int(i128::from(acc)));
    }
    Matrix::new(matrix.rows(), 1, data)
}

/// Reduce `grid` (`rows` equal-length rows, `cols` columns) to reduced row
/// echelon form over `F_2` in place (Gauss-Jordan via XOR, since `1` is the
/// only nonzero scalar). Returns the pivot column of each pivot row, in row
/// order.
fn rref_mod2_inplace(grid: &mut [Vec<u8>], cols: usize) -> Vec<usize> {
    let rows = grid.len();
    let mut pivot_cols = Vec::new();
    let mut pivot_row = 0usize;
    for col in 0..cols {
        if pivot_row >= rows {
            break;
        }
        let Some(selected) = (pivot_row..rows).find(|&row| grid[row][col] == 1) else {
            continue;
        };
        grid.swap(pivot_row, selected);
        let pivot_snapshot = grid[pivot_row].clone();
        for (row, bits) in grid.iter_mut().enumerate() {
            if row != pivot_row && bits[col] == 1 {
                for (entry, pivot_entry) in bits.iter_mut().zip(pivot_snapshot.iter()) {
                    *entry ^= pivot_entry;
                }
            }
        }
        pivot_cols.push(col);
        pivot_row += 1;
    }
    pivot_cols
}

/// A basis of `{x : matrix . x = 0 mod 2}`, each vector an `n x 1` [`Matrix`]
/// of `0`/`1` entries (`n = matrix.cols()`) -- the `F_2` analog of
/// [`Matrix::null_space`], same free-variable construction (mod 2, negation
/// is the identity, so the free coordinate's own reduced-row entry is used
/// directly rather than negated).
fn null_space_mod2(matrix: &Matrix) -> Option<Vec<Matrix>> {
    let width = matrix.cols();
    let mut grid = matrix_to_bits(matrix)?;
    let pivot_cols = rref_mod2_inplace(&mut grid, width);
    let mut is_pivot = vec![false; width];
    for &col in &pivot_cols {
        is_pivot[col] = true;
    }
    let mut basis = Vec::new();
    for free in (0..width).filter(|&c| !is_pivot[c]) {
        let mut coords = vec![0u8; width];
        coords[free] = 1;
        for (row_index, &pivot_col) in pivot_cols.iter().enumerate() {
            coords[pivot_col] = grid[row_index][free];
        }
        let data: Vec<CasExpr> = coords
            .into_iter()
            .map(|bit| CasExpr::int(i128::from(bit)))
            .collect();
        basis.push(Matrix::new(width, 1, data)?);
    }
    Some(basis)
}

/// The rank, over `F_2`, of the span of a list of `n x 1` column vectors
/// (`0` for an empty list).
fn rank_of_columns_mod2(columns: &[Matrix], rows: usize) -> Option<usize> {
    if columns.is_empty() {
        return Some(0);
    }
    let cols = columns.len();
    let mut grid = vec![vec![0u8; cols]; rows];
    for (r, row) in grid.iter_mut().enumerate() {
        for (c, column) in columns.iter().enumerate() {
            row[c] = mod2_of(column.get(r, 0)?)?;
        }
    }
    Some(rref_mod2_inplace(&mut grid, cols).len())
}

/// Greedily choose a basis for the column span of `image_source` mod 2
/// (`B^p = im(delta^{p-1})`), the `F_2` analog of
/// [`super::induced::choose_boundary_basis`].
fn choose_boundary_basis_mod2(image_source: &Matrix) -> Option<Vec<Matrix>> {
    let rows = image_source.rows();
    let mut chosen: Vec<Matrix> = Vec::new();
    let mut rank_so_far = 0usize;
    for c in 0..image_source.cols() {
        let mut column_data = Vec::with_capacity(rows);
        for r in 0..rows {
            column_data.push(CasExpr::int(i128::from(mod2_of(image_source.get(r, c)?)?)));
        }
        let candidate = Matrix::new(rows, 1, column_data)?;
        let mut trial = chosen.clone();
        trial.push(candidate.clone());
        let new_rank = rank_of_columns_mod2(&trial, rows)?;
        if new_rank > rank_so_far {
            chosen.push(candidate);
            rank_so_far = new_rank;
        }
    }
    Some(chosen)
}

/// Choose a genuine basis of `B^p` and a genuine extension of it to a basis
/// of `Z^p = ker(delta^p)`, over `F_2` -- the `F_2` analog of
/// `super::induced::choose_homology_basis`, mirrored entry for entry
/// (`kernel_source` plays the role `boundary_k` does there: its columns are
/// the space the cocycle kernel lives in; `image_source` plays the role
/// `boundary_next` does: its column span is the coboundary image).
fn choose_cohomology_basis_mod2(
    kernel_source: &Matrix,
    image_source: &Matrix,
) -> Option<(Vec<Matrix>, Vec<Matrix>)> {
    let rows = kernel_source.cols();
    let boundary_basis = choose_boundary_basis_mod2(image_source)?;
    let z_basis = null_space_mod2(kernel_source)?;
    let mut accumulated = boundary_basis.clone();
    let mut rank_so_far = rank_of_columns_mod2(&accumulated, rows)?;
    let mut homology_basis = Vec::new();
    for candidate in z_basis {
        let mut trial = accumulated.clone();
        trial.push(candidate.clone());
        let new_rank = rank_of_columns_mod2(&trial, rows)?;
        if new_rank > rank_so_far {
            homology_basis.push(candidate.clone());
            accumulated.push(candidate);
            rank_so_far = new_rank;
        }
    }
    Some((boundary_basis, homology_basis))
}

/// Solve `basis[0] * c_0 + ... = target` mod 2 for the unique coefficient
/// vector `c`, the `F_2` analog of [`super::induced`]'s `solve_via_rref`
/// (same augmented-elimination recipe, mod 2). Assumes `basis`'s columns are
/// linearly independent (guaranteed by construction); returns `None` if
/// `target` is not actually in their span, or on a shape mismatch.
fn solve_mod2(basis: &[Matrix], target: &Matrix) -> Option<Vec<u8>> {
    let rows = target.rows();
    let cols = basis.len();
    if cols == 0 {
        return if is_zero_bits(target)? {
            Some(Vec::new())
        } else {
            None
        };
    }
    let mut grid = vec![vec![0u8; cols + 1]; rows];
    for (r, row) in grid.iter_mut().enumerate() {
        for (c, column) in basis.iter().enumerate() {
            row[c] = mod2_of(column.get(r, 0)?)?;
        }
        row[cols] = mod2_of(target.get(r, 0)?)?;
    }
    rref_mod2_inplace(&mut grid, cols + 1);
    let mut coefficients = Vec::with_capacity(cols);
    for (j, row) in grid.iter().enumerate().take(cols) {
        if row[j] != 1 {
            return None; // not a pivot here: basis was not full column rank
        }
        coefficients.push(row[cols]);
    }
    for row in grid.iter().skip(cols) {
        if row[cols] != 0 {
            return None; // target was never in basis's span
        }
    }
    Some(coefficients)
}

// ---------------------------------------------------------------------
// Ring-dispatched cohomology basis and linear-solve helpers, shared by the
// producer and `verify`. `modulus` is `None` for `Q` and `Some(2)` for `F_2`
// (the only two coefficient rings this module supports).
// ---------------------------------------------------------------------

/// `(boundary_basis, homology_basis)` of `H^dim(complex; R)`, `R` selected by
/// `modulus` (`None` = `Q`, `Some(2)` = `F_2`).
fn cohomology_basis(
    complex: &SimplicialComplex,
    dim: usize,
    modulus: Option<i128>,
) -> Option<(Vec<Matrix>, Vec<Matrix>)> {
    let delta_here = boundary_matrix(complex, dim + 1)?.transpose();
    let delta_prev = if dim == 0 {
        Matrix::zeros(complex.count(0), 0)
    } else {
        boundary_matrix(complex, dim)?.transpose()
    };
    match modulus {
        None => choose_homology_basis(&delta_here, &delta_prev),
        Some(2) => choose_cohomology_basis_mod2(&delta_here, &delta_prev),
        _ => None,
    }
}

/// Whether `v` is a genuine cocycle of `delta` (`delta . v = 0`) over `R`.
fn is_cocycle(delta: &Matrix, v: &Matrix, modulus: Option<i128>) -> Option<bool> {
    match modulus {
        None => Some(is_zero_matrix(&delta.mul(v)?)),
        Some(2) => is_zero_bits(&mat_vec_mod2(delta, v)?),
        _ => None,
    }
}

/// The rank, over `R`, of the span of `columns` (each an `n x 1` [`Matrix`]).
fn rank_of(columns: &[Matrix], rows: usize, modulus: Option<i128>) -> Option<usize> {
    match modulus {
        None => rank_of_columns(columns, rows),
        Some(2) => rank_of_columns_mod2(columns, rows),
        _ => None,
    }
}

/// Whether `boundary_basis` extended by `homology_basis` is a genuine basis
/// of the FULL cocycle space `ker(kernel_source)`, not a proper subspace of
/// it: both lists together must be linearly independent (their combined rank
/// equals their combined length) AND that combined length must equal the
/// freshly-computed dimension of the cocycle space itself.
fn basis_is_genuine_extension(
    kernel_source: &Matrix,
    boundary_basis: &[Matrix],
    homology_basis: &[Matrix],
    modulus: Option<i128>,
) -> Option<bool> {
    let rows = kernel_source.cols();
    let full_z_dim = match modulus {
        None => kernel_source.null_space()?.len(),
        Some(2) => null_space_mod2(kernel_source)?.len(),
        _ => return None,
    };
    let combined: Vec<Matrix> = boundary_basis
        .iter()
        .cloned()
        .chain(homology_basis.iter().cloned())
        .collect();
    let rank = rank_of(&combined, rows, modulus)?;
    Some(rank == combined.len() && combined.len() == full_z_dim)
}

/// Solve for the coordinates of `target` in the `[boundary_basis |
/// homology_basis]` basis of the cocycle space, over `R`, returning the
/// FULL coefficient vector (boundary-part first, then homology-part).
fn solve_in_combined_basis(
    combined: &[Matrix],
    target: &Matrix,
    rows: usize,
    modulus: Option<i128>,
) -> Option<Vec<Rational>> {
    match modulus {
        None => {
            let stacked = columns_to_matrix(combined, rows)?;
            solve_via_rref(&stacked, target)
        }
        Some(2) => {
            let bits = solve_mod2(combined, target)?;
            Some(
                bits.into_iter()
                    .map(|bit| Rational::integer(i128::from(bit)))
                    .collect(),
            )
        }
        _ => None,
    }
}

/// The Alexander-Whitney cup product cochain `alpha ∪ beta` of a degree-`p`
/// cochain `alpha` and a degree-`q` cochain `beta`, over `complex`'s
/// `(p+q)`-simplices: `(alpha ∪ beta)(sigma) = alpha(front) * beta(back)`
/// where `front`/`back` are the first `p+1` / last `q+1` vertices of
/// `sigma`'s own sorted vertex list (the complex's total order). `modulus`,
/// if `Some(m)`, reduces every output entry mod `m` (multiplying two `0`/`1`
/// entries never needs reduction, but this stays general).
///
/// Returns `None` if `alpha`/`beta` are not the right length, if a
/// front/back face is somehow absent from the complex (should not happen:
/// every face of a `(p+q)`-simplex is itself a simplex, since a
/// `SimplicialComplex` is closed under faces), or on an arithmetic overflow.
fn alexander_whitney_cup(
    complex: &SimplicialComplex,
    p: usize,
    q: usize,
    alpha: &Matrix,
    beta: &Matrix,
    modulus: Option<i128>,
) -> Option<Matrix> {
    let pq_simplices = complex.simplices(p + q);
    let p_index: BTreeMap<Vec<usize>, usize> = complex
        .simplices(p)
        .into_iter()
        .enumerate()
        .map(|(i, face)| (face, i))
        .collect();
    let q_index: BTreeMap<Vec<usize>, usize> = complex
        .simplices(q)
        .into_iter()
        .enumerate()
        .map(|(i, face)| (face, i))
        .collect();
    let mut data = Vec::with_capacity(pq_simplices.len());
    for simplex in &pq_simplices {
        let front: Vec<usize> = simplex[0..=p].to_vec();
        let back: Vec<usize> = simplex[p..].to_vec();
        let &front_idx = p_index.get(&front)?;
        let &back_idx = q_index.get(&back)?;
        let a = as_rational(alpha.get(front_idx, 0)?)?;
        let b = as_rational(beta.get(back_idx, 0)?)?;
        let mut product = a.checked_mul(b)?;
        if let Some(m) = modulus {
            product = Rational::integer(product.numerator().rem_euclid(m));
        }
        data.push(CasExpr::Const(product));
    }
    Matrix::new(pq_simplices.len(), 1, data)
}

/// A checkable certificate of the cup product `H^p(complex; R) x H^q(complex;
/// R) -> H^{p+q}(complex; R)` on the chosen cocycle bases, `R` being `Q`
/// (`modulus = None`) or `F_2` (`modulus = Some(2)`). See the module
/// documentation for what [`verify`](Self::verify) re-derives.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CupProductCertificate {
    /// `None` for `Q`, `Some(2)` for `F_2`.
    pub modulus: Option<i128>,
    /// The first cup factor's degree.
    pub p: usize,
    /// The second cup factor's degree.
    pub q: usize,
    /// `(boundary_basis, homology_basis)` of `H^p`.
    pub basis_alpha: (Vec<Matrix>, Vec<Matrix>),
    /// `(boundary_basis, homology_basis)` of `H^q`.
    pub basis_beta: (Vec<Matrix>, Vec<Matrix>),
    /// `(boundary_basis, homology_basis)` of `H^{p+q}`.
    pub basis_gamma: (Vec<Matrix>, Vec<Matrix>),
    /// `table[i][j]` = the coordinates (in `H^{p+q}`'s `homology_basis`) of
    /// `basis_alpha.1[i] ∪ basis_beta.1[j]`.
    pub table: Vec<Vec<Vec<Rational>>>,
}

/// The result of a successful [`CupProductCertificate::verify`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CupProductReport {
    /// The recomputed multiplication table, identical to the certificate's
    /// own on success.
    pub table: Vec<Vec<Vec<Rational>>>,
}

/// Compute the cup product certificate of degrees `(p, q)` over `R` selected
/// by `modulus`.
fn cup_product(
    complex: &SimplicialComplex,
    p: usize,
    q: usize,
    modulus: Option<i128>,
) -> Option<CupProductCertificate> {
    let (b_alpha, h_alpha) = cohomology_basis(complex, p, modulus)?;
    let (b_beta, h_beta) = cohomology_basis(complex, q, modulus)?;
    let (b_gamma, h_gamma) = cohomology_basis(complex, p + q, modulus)?;
    let rows_gamma = complex.count(p + q);
    let combined_gamma: Vec<Matrix> = b_gamma
        .iter()
        .cloned()
        .chain(h_gamma.iter().cloned())
        .collect();

    let mut table = Vec::with_capacity(h_alpha.len());
    for alpha in &h_alpha {
        let mut row = Vec::with_capacity(h_beta.len());
        for beta in &h_beta {
            let gamma = alexander_whitney_cup(complex, p, q, alpha, beta, modulus)?;
            let coefficients =
                solve_in_combined_basis(&combined_gamma, &gamma, rows_gamma, modulus)?;
            row.push(coefficients[b_gamma.len()..].to_vec());
        }
        table.push(row);
    }

    Some(CupProductCertificate {
        modulus,
        p,
        q,
        basis_alpha: (b_alpha, h_alpha),
        basis_beta: (b_beta, h_beta),
        basis_gamma: (b_gamma, h_gamma),
        table,
    })
}

/// Compute the cup product `H^p(complex; Q) x H^q(complex; Q) -> H^{p+q}(complex; Q)`.
#[must_use]
pub fn cup_product_q(
    complex: &SimplicialComplex,
    p: usize,
    q: usize,
) -> Option<CupProductCertificate> {
    cup_product(complex, p, q, None)
}

/// Compute the cup product `H^p(complex; F_2) x H^q(complex; F_2) -> H^{p+q}(complex; F_2)`.
#[must_use]
pub fn cup_product_f2(
    complex: &SimplicialComplex,
    p: usize,
    q: usize,
) -> Option<CupProductCertificate> {
    cup_product(complex, p, q, Some(2))
}

/// Guard: every entry of a recorded basis vector list matches one freshly
/// rebuilt, entrywise.
fn bases_match(rebuilt: &[Matrix], recorded: &[Matrix], name: &str) -> Result<(), String> {
    if rebuilt.len() != recorded.len() {
        return Err(format!(
            "{name} basis length mismatch: rebuilt {}, recorded {}",
            rebuilt.len(),
            recorded.len()
        ));
    }
    for (i, (r, c)) in rebuilt.iter().zip(recorded.iter()).enumerate() {
        if !certify_product_equals(r, c) {
            return Err(format!(
                "{name} basis vector {i} does not match the recorded one"
            ));
        }
    }
    Ok(())
}

/// Recompute and check one table entry `(i, j)`: rebuild `alpha ∪ beta`,
/// confirm it is a cocycle, solve for its class in the `H^{p+q}` basis,
/// compare to the recorded entry, and check graded commutativity against the
/// independently recomputed `beta ∪ alpha`. Returns the recomputed
/// coordinates on success. Factored out of [`CupProductCertificate::verify`]
/// so that function stays a readable top-level checklist.
#[allow(clippy::too_many_arguments)]
fn check_table_entry(
    complex: &SimplicialComplex,
    p: usize,
    q: usize,
    i: usize,
    j: usize,
    alpha: &Matrix,
    beta: &Matrix,
    delta_pq: &Matrix,
    combined_gamma: &[Matrix],
    rows_gamma: usize,
    boundary_gamma_len: usize,
    modulus: Option<i128>,
    sign_odd: bool,
    recorded: &[Rational],
) -> Result<Vec<Rational>, String> {
    let gamma = alexander_whitney_cup(complex, p, q, alpha, beta, modulus)
        .ok_or_else(|| format!("could not build the cup product cochain at ({i},{j})"))?;
    if !is_cocycle(delta_pq, &gamma, modulus).unwrap_or(false) {
        return Err(format!(
            "the cup product cochain at ({i},{j}) is not a cocycle"
        ));
    }
    let coefficients = solve_in_combined_basis(combined_gamma, &gamma, rows_gamma, modulus)
        .ok_or_else(|| {
            format!("cup product class at ({i},{j}) is not expressible in the H^(p+q) basis")
        })?;
    let tail = coefficients[boundary_gamma_len..].to_vec();
    if tail != recorded {
        return Err(format!("cup product table entry ({i},{j}) mismatch"));
    }

    // Graded commutativity: beta ∪ alpha == (-1)^{pq} * (alpha ∪ beta).
    let swapped = alexander_whitney_cup(complex, q, p, beta, alpha, modulus)
        .ok_or_else(|| format!("could not build the swapped cup product at ({i},{j})"))?;
    let swapped_coefficients =
        solve_in_combined_basis(combined_gamma, &swapped, rows_gamma, modulus)
            .ok_or_else(|| format!("swapped cup product class at ({i},{j}) is not expressible"))?;
    let swapped_tail = &swapped_coefficients[boundary_gamma_len..];
    for (r, (&expected_before_sign, &actual)) in tail.iter().zip(swapped_tail.iter()).enumerate() {
        let expected = if sign_odd && modulus.is_none() {
            expected_before_sign
                .checked_neg()
                .ok_or_else(|| "sign negation overflow".to_string())?
        } else {
            expected_before_sign
        };
        if expected != actual {
            return Err(format!(
                "graded commutativity fails at ({i},{j}), coordinate {r}"
            ));
        }
    }
    Ok(tail)
}

/// Guard: every basis vector at each of the three degrees (`p`, `q`, `p+q`)
/// is a genuine cocycle, and each degree's basis is a genuine extension of
/// its own boundary basis to the FULL cocycle space (not a proper subspace
/// of it). Factored out of [`CupProductCertificate::verify`] so that
/// function stays a readable top-level checklist.
#[allow(clippy::similar_names)] // delta_p/delta_q/delta_pq name the p, q, p+q degrees, not accidental near-duplicates
fn bases_are_cocycles_and_genuine_extensions(
    delta_p: &Matrix,
    delta_q: &Matrix,
    delta_pq: &Matrix,
    basis_alpha: &(Vec<Matrix>, Vec<Matrix>),
    basis_beta: &(Vec<Matrix>, Vec<Matrix>),
    basis_gamma: &(Vec<Matrix>, Vec<Matrix>),
    modulus: Option<i128>,
) -> Result<(), String> {
    for (name, delta, basis) in [
        ("H^p", delta_p, &basis_alpha.1),
        ("H^q", delta_q, &basis_beta.1),
        ("H^(p+q)", delta_pq, &basis_gamma.1),
    ] {
        for (i, v) in basis.iter().enumerate() {
            if !is_cocycle(delta, v, modulus).unwrap_or(false) {
                return Err(format!("{name} basis vector {i} is not a cocycle"));
            }
        }
    }

    for (name, kernel_source, boundary_basis, homology_basis) in [
        ("H^p", delta_p, &basis_alpha.0, &basis_alpha.1),
        ("H^q", delta_q, &basis_beta.0, &basis_beta.1),
        ("H^(p+q)", delta_pq, &basis_gamma.0, &basis_gamma.1),
    ] {
        if !basis_is_genuine_extension(kernel_source, boundary_basis, homology_basis, modulus)
            .unwrap_or(false)
        {
            return Err(format!(
                "{name} basis is not a genuine extension of the boundary basis to the full cocycle space"
            ));
        }
    }
    Ok(())
}

impl CupProductCertificate {
    /// Re-derive every claim in this certificate from `complex` alone. See
    /// the module documentation for exactly what each guard would miss if it
    /// were absent.
    ///
    /// # Errors
    ///
    /// Returns a distinct, descriptive `Err(String)` for whichever guard
    /// fails first.
    #[allow(clippy::similar_names)] // delta_p/delta_q/delta_pq name the p, q, p+q degrees, not accidental near-duplicates
    pub fn verify(&self, complex: &SimplicialComplex) -> Result<CupProductReport, String> {
        let modulus = self.modulus;
        if !matches!(modulus, None | Some(2)) {
            return Err("only Q (None) and F_2 (Some(2)) are supported".to_string());
        }

        // `delta_*` doubles as each degree's "kernel source": the matrix
        // whose null space is the cocycle space at that degree.
        let delta_p = boundary_matrix(complex, self.p + 1)
            .ok_or("could not build delta^p")?
            .transpose();
        let delta_q = boundary_matrix(complex, self.q + 1)
            .ok_or("could not build delta^q")?
            .transpose();
        let delta_pq = boundary_matrix(complex, self.p + self.q + 1)
            .ok_or("could not build delta^(p+q)")?
            .transpose();

        let (b_alpha, h_alpha) =
            cohomology_basis(complex, self.p, modulus).ok_or("could not rebuild H^p basis")?;
        let (b_beta, h_beta) =
            cohomology_basis(complex, self.q, modulus).ok_or("could not rebuild H^q basis")?;
        let (b_gamma, h_gamma) = cohomology_basis(complex, self.p + self.q, modulus)
            .ok_or("could not rebuild H^(p+q) basis")?;

        bases_match(&b_alpha, &self.basis_alpha.0, "H^p boundary")?;
        bases_match(&h_alpha, &self.basis_alpha.1, "H^p homology")?;
        bases_match(&b_beta, &self.basis_beta.0, "H^q boundary")?;
        bases_match(&h_beta, &self.basis_beta.1, "H^q homology")?;
        bases_match(&b_gamma, &self.basis_gamma.0, "H^(p+q) boundary")?;
        bases_match(&h_gamma, &self.basis_gamma.1, "H^(p+q) homology")?;

        bases_are_cocycles_and_genuine_extensions(
            &delta_p,
            &delta_q,
            &delta_pq,
            &self.basis_alpha,
            &self.basis_beta,
            &self.basis_gamma,
            modulus,
        )?;

        let rows_gamma = complex.count(self.p + self.q);
        let combined_gamma: Vec<Matrix> = self
            .basis_gamma
            .0
            .iter()
            .cloned()
            .chain(self.basis_gamma.1.iter().cloned())
            .collect();
        let boundary_gamma_len = self.basis_gamma.0.len();

        if self.table.len() != h_alpha.len() {
            return Err(format!(
                "table row count mismatch: recorded {}, H^p dimension {}",
                self.table.len(),
                h_alpha.len()
            ));
        }
        let sign_odd = (self.p * self.q) % 2 == 1;
        let mut recomputed_table = Vec::with_capacity(h_alpha.len());
        for (i, alpha) in h_alpha.iter().enumerate() {
            if self.table[i].len() != h_beta.len() {
                return Err(format!(
                    "table row {i} column count mismatch: recorded {}, H^q dimension {}",
                    self.table[i].len(),
                    h_beta.len()
                ));
            }
            let mut row = Vec::with_capacity(h_beta.len());
            for (j, beta) in h_beta.iter().enumerate() {
                let tail = check_table_entry(
                    complex,
                    self.p,
                    self.q,
                    i,
                    j,
                    alpha,
                    beta,
                    &delta_pq,
                    &combined_gamma,
                    rows_gamma,
                    boundary_gamma_len,
                    modulus,
                    sign_odd,
                    &self.table[i][j],
                )?;
                row.push(tail);
            }
            recomputed_table.push(row);
        }

        Ok(CupProductReport {
            table: recomputed_table,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{CupProductCertificate, cup_product_f2, cup_product_q};
    use crate::homology::SimplicialComplex;
    use crate::homology::coefficients::homology_with_coefficients;
    use crate::homology::fixtures::rp2_6v;
    use axeyum_ir::Rational;

    fn complex_of(maximal: &[&[usize]]) -> SimplicialComplex {
        let owned: Vec<Vec<usize>> = maximal.iter().map(|s| s.to_vec()).collect();
        SimplicialComplex::from_maximal_simplices(&owned).expect("valid complex")
    }

    /// `S^1 v S^1 v S^2`: two 3-vertex circles and a tetrahedron boundary,
    /// all sharing vertex `0` as the sole common (wedge) point, otherwise
    /// vertex-disjoint. Betti numbers `(1, 2, 1)`, identical to
    /// `fixtures::torus_7v` -- the whole point of this fixture.
    fn wedge_two_circles_and_a_sphere() -> SimplicialComplex {
        complex_of(&[
            // Circle 1: vertices {0, 1, 2}.
            &[0, 1],
            &[1, 2],
            &[0, 2],
            // Circle 2: vertices {0, 3, 4}, disjoint from circle 1 except at 0.
            &[0, 3],
            &[3, 4],
            &[0, 4],
            // S^2: the tetrahedron boundary on {0, 5, 6, 7}, disjoint from
            // both circles except at 0.
            &[0, 5, 6],
            &[0, 5, 7],
            &[0, 6, 7],
            &[5, 6, 7],
        ])
    }

    fn nonzero(entries: &[Rational]) -> bool {
        entries.iter().any(|value| !value.is_zero())
    }

    #[test]
    fn wedge_has_identical_betti_numbers_to_the_torus() {
        let wedge = wedge_two_circles_and_a_sphere();
        let certificate =
            homology_with_coefficients(&wedge).expect("coefficient homology of the wedge");
        assert_eq!(certificate.integer.betti[&0], 1);
        assert_eq!(certificate.integer.betti[&1], 2);
        assert_eq!(certificate.integer.betti[&2], 1);
        for k in 0..=2 {
            assert_eq!(certificate.integer.torsion[&k], Vec::<i128>::new());
        }
    }

    /// THE finding this item names: identical homology, different rings.
    #[test]
    fn torus_and_wedge_have_the_same_homology_but_different_cup_products() {
        let torus = crate::homology::fixtures::torus_7v();
        let wedge = wedge_two_circles_and_a_sphere();

        let torus_table = cup_product_q(&torus, 1, 1).expect("torus cup product H^1 x H^1 -> H^2");
        assert_eq!(torus_table.basis_alpha.1.len(), 2, "H^1(T^2; Q) has rank 2");
        torus_table
            .verify(&torus)
            .expect("torus certificate verifies");
        let torus_nonzero = torus_table
            .table
            .iter()
            .flatten()
            .any(|entry| nonzero(entry));
        assert!(
            torus_nonzero,
            "the torus's H^1 generators must have a nonzero cup product somewhere in the table"
        );

        let wedge_table = cup_product_q(&wedge, 1, 1).expect("wedge cup product H^1 x H^1 -> H^2");
        assert_eq!(
            wedge_table.basis_alpha.1.len(),
            2,
            "H^1(wedge; Q) has rank 2"
        );
        wedge_table
            .verify(&wedge)
            .expect("wedge certificate verifies");
        for row in &wedge_table.table {
            for entry in row {
                assert!(
                    !nonzero(entry),
                    "the wedge's cup product must vanish, got {entry:?}"
                );
            }
        }

        assert_ne!(
            torus_table.table, wedge_table.table,
            "the torus and the wedge must have different cup product tables"
        );
    }

    /// `RP^2` over `F_2`: `alpha ∪ alpha != 0` for the generator of `H^1`.
    #[test]
    fn rp2_generator_squares_to_a_nonzero_class_over_f2() {
        let rp2 = rp2_6v();
        let certificate = cup_product_f2(&rp2, 1, 1).expect("RP^2 cup product H^1 x H^1 -> H^2");
        assert_eq!(
            certificate.basis_alpha.1.len(),
            1,
            "H^1(RP^2; F_2) is 1-dimensional"
        );
        assert_eq!(
            certificate.basis_gamma.1.len(),
            1,
            "H^2(RP^2; F_2) is 1-dimensional"
        );
        certificate.verify(&rp2).expect("certificate verifies");
        assert!(
            nonzero(&certificate.table[0][0]),
            "alpha ∪ alpha must be nonzero over F_2, got {:?}",
            certificate.table[0][0]
        );
    }

    /// A cochain-level sanity check independent of the wedge/torus
    /// distinction above: on a single filled triangle (contractible), `H^1`
    /// is trivial, so there is nothing to cup -- the table is `0 x 0`,
    /// exercised so the degenerate case is not silently unreachable.
    #[test]
    fn a_contractible_complex_has_an_empty_h1_cup_table() {
        let triangle = complex_of(&[&[0, 1, 2]]);
        let certificate = cup_product_q(&triangle, 1, 1).expect("cup product on a filled triangle");
        assert_eq!(certificate.basis_alpha.1.len(), 0);
        assert_eq!(certificate.table.len(), 0);
        certificate.verify(&triangle).expect("certificate verifies");
    }

    // ---- forged-certificate controls ----

    /// ADVERSARIAL. Forge only a table entry, leaving every basis genuine:
    /// `verify` recomputes the same cup product fresh and disagrees.
    #[test]
    fn verify_refuses_a_forged_table_entry() {
        let rp2 = rp2_6v();
        let mut forged: CupProductCertificate =
            cup_product_f2(&rp2, 1, 1).expect("RP^2 cup product H^1 x H^1 -> H^2");
        assert!(
            forged.verify(&rp2).is_ok(),
            "genuine certificate must verify"
        );
        forged.table[0][0] = vec![Rational::integer(0)]; // the true value is 1
        let err = forged
            .verify(&rp2)
            .expect_err("a forged table entry must be refused");
        assert!(err.contains("table entry"), "got: {err}");
    }

    /// ADVERSARIAL. Forge a basis vector (still a genuine cocycle, since it
    /// is copied from a DIFFERENT genuine basis vector at the same degree
    /// where one exists, or a scaled one otherwise) so the recorded basis no
    /// longer matches what the producer would have chosen: `bases_match`
    /// refuses via the recorded-vs-rebuilt entrywise comparison.
    #[test]
    fn verify_refuses_a_forged_basis_vector() {
        let rp2 = rp2_6v();
        let mut forged: CupProductCertificate =
            cup_product_f2(&rp2, 1, 1).expect("RP^2 cup product H^1 x H^1 -> H^2");
        assert!(
            forged.verify(&rp2).is_ok(),
            "genuine certificate must verify"
        );
        // Zero out the one H^1 basis vector: caught by `bases_match`
        // (the freshly rebuilt basis no longer agrees entrywise) -- NOT by
        // `is_cocycle` (the zero cochain is trivially a cocycle), which is
        // exactly why `bases_are_cocycles_and_genuine_extensions_*` below
        // are direct unit tests of that guard function instead: any
        // certificate-level basis forgery hits `bases_match` first.
        let width = forged.basis_alpha.1[0].rows();
        forged.basis_alpha.1[0] = crate::Matrix::zeros(width, 1);
        let err = forged
            .verify(&rp2)
            .expect_err("a forged basis vector must be refused");
        assert!(err.contains("basis vector"), "got: {err}");
    }

    /// Direct unit test of `bases_are_cocycles_and_genuine_extensions`,
    /// isolated from `verify` (and so from `bases_match`, which -- as the
    /// test above notes -- would pre-empt any certificate-level forgery
    /// before this guard is ever reached). A claimed `H^p` basis vector that
    /// is not actually a cocycle (`delta * v != 0`) must be refused by name.
    #[test]
    fn bases_are_cocycles_and_genuine_extensions_refuses_a_non_cocycle_vector() {
        use super::bases_are_cocycles_and_genuine_extensions;
        use crate::{CasExpr, Matrix};
        // delta: C^1 (dim 2) -> C^2 (dim 1), matrix [[1, 1]]. ker(delta) is
        // the 1-dimensional span of (1, -1).
        let delta = Matrix::new(1, 2, vec![CasExpr::int(1), CasExpr::int(1)]).expect("1x2");
        // A claimed homology-basis vector (1, 0): NOT a cocycle, since
        // delta . (1, 0) = [1] != 0.
        let not_a_cocycle = Matrix::new(2, 1, vec![CasExpr::int(1), CasExpr::int(0)]).expect("2x1");
        let bad_basis: (Vec<Matrix>, Vec<Matrix>) = (Vec::new(), vec![not_a_cocycle]);
        let err = bases_are_cocycles_and_genuine_extensions(
            &delta, &delta, &delta, &bad_basis, &bad_basis, &bad_basis, None,
        )
        .expect_err("a non-cocycle basis vector must be refused");
        assert!(err.contains("cocycle"), "got: {err}");

        // POSITIVE CONTROL: the genuine generator (1, -1) IS admitted.
        let genuine_cocycle =
            Matrix::new(2, 1, vec![CasExpr::int(1), CasExpr::int(-1)]).expect("2x1");
        let good_basis: (Vec<Matrix>, Vec<Matrix>) = (Vec::new(), vec![genuine_cocycle]);
        assert!(
            bases_are_cocycles_and_genuine_extensions(
                &delta,
                &delta,
                &delta,
                &good_basis,
                &good_basis,
                &good_basis,
                None,
            )
            .is_ok()
        );
    }

    /// Direct unit test of `bases_are_cocycles_and_genuine_extensions`'s
    /// genuine-extension check, isolated the same way: an EMPTY claimed
    /// basis for a cocycle space that is genuinely 1-dimensional must be
    /// refused (it satisfies `is_cocycle` vacuously -- there is nothing to
    /// check -- so only the extension-rank guard can catch this).
    #[test]
    fn bases_are_cocycles_and_genuine_extensions_refuses_an_incomplete_basis() {
        use super::bases_are_cocycles_and_genuine_extensions;
        use crate::{CasExpr, Matrix};
        let delta = Matrix::new(1, 2, vec![CasExpr::int(1), CasExpr::int(1)]).expect("1x2");
        let empty_basis: (Vec<Matrix>, Vec<Matrix>) = (Vec::new(), Vec::new());
        let err = bases_are_cocycles_and_genuine_extensions(
            &delta,
            &delta,
            &delta,
            &empty_basis,
            &empty_basis,
            &empty_basis,
            None,
        )
        .expect_err("an empty basis must be refused when the cocycle space is nontrivial");
        assert!(err.contains("genuine extension"), "got: {err}");
    }

    /// ADVERSARIAL, isolated to graded commutativity: forge the table so
    /// `alpha ∪ beta` and a swapped `beta ∪ alpha` (computed independently
    /// inside `verify`) disagree. Uses the torus (two DISTINCT `H^1`
    /// generators, so `p == q == 1` still gives a meaningful, non-symmetric
    /// forgery target since the genuine table is symmetric up to sign here:
    /// `(-1)^{1*1} = -1`, so `alpha_0 ∪ alpha_1 = -(alpha_1 ∪ alpha_0)`).
    #[test]
    fn verify_refuses_a_table_that_breaks_graded_commutativity() {
        let torus = crate::homology::fixtures::torus_7v();
        let mut forged: CupProductCertificate =
            cup_product_q(&torus, 1, 1).expect("torus cup product H^1 x H^1 -> H^2");
        assert!(
            forged.verify(&torus).is_ok(),
            "genuine certificate must verify"
        );
        // Flip the sign of one off-diagonal entry: still a valid H^2 class
        // shape-wise, but no longer consistent with delta(gamma)=0 solved
        // fresh, OR (if it happens to still solve, since H^2 is 1-dim here
        // and negation is the only other option) inconsistent with the
        // independently recomputed swapped product's sign relationship.
        if let Some(entry) = forged.table[0][1].first_mut() {
            *entry = entry.checked_neg().expect("negation");
        }
        let err = forged.verify(&torus).expect_err(
            "a sign-broken table entry must be refused (by the table-match or commutativity guard)",
        );
        assert!(
            err.contains("table entry") || err.contains("commutativity"),
            "got: {err}"
        );
    }

    /// Direct unit test of `check_table_entry`'s graded-commutativity check,
    /// isolated from the table-mismatch check above (guard 10): as
    /// `verify_refuses_a_table_that_breaks_graded_commutativity` shows, any
    /// CERTIFICATE-level forgery that reaches this check must first survive
    /// the table-mismatch guard, and graded commutativity at the
    /// cohomology-class level is a genuine theorem for any two actual cocycle
    /// representatives -- so once `alpha`/`beta` are genuine cocycles (which
    /// `bases_are_cocycles_and_genuine_extensions` already guarantees) and
    /// the recorded entry matches the fresh recomputation (which the
    /// table-mismatch guard already guarantees), this check can never
    /// actually fire from a forged certificate field. Mutation-tested:
    /// neutralizing it killed zero tests for exactly that reason. What it
    /// DOES guard against is a bug in the swap/sign computation itself, which
    /// this test exercises directly by calling `check_table_entry` with a
    /// deliberately wrong `sign_odd` (not itself a certificate field, an
    /// argument the caller computes from `p`/`q`) against the genuine,
    /// self-consistent recorded entry.
    #[test]
    fn check_table_entry_refuses_a_wrong_sign_odd_parameter() {
        use super::check_table_entry;
        let torus = crate::homology::fixtures::torus_7v();
        let genuine = cup_product_q(&torus, 1, 1).expect("torus cup product H^1 x H^1 -> H^2");
        assert!(
            genuine.verify(&torus).is_ok(),
            "genuine certificate must verify"
        );
        assert!(
            nonzero(&genuine.table[0][1]),
            "need a nonzero off-diagonal entry to distinguish a sign flip"
        );

        let delta_pq = super::boundary_matrix(&torus, 3)
            .expect("delta^(p+q) builds")
            .transpose();
        let combined_gamma: Vec<crate::Matrix> = genuine
            .basis_gamma
            .0
            .iter()
            .cloned()
            .chain(genuine.basis_gamma.1.iter().cloned())
            .collect();
        let rows_gamma = torus.count(2);
        let boundary_gamma_len = genuine.basis_gamma.0.len();
        let alpha = &genuine.basis_alpha.1[0];
        let beta = &genuine.basis_beta.1[1];
        let recorded = &genuine.table[0][1];

        // POSITIVE CONTROL: the correct sign_odd (true, since p * q = 1 is
        // odd) is admitted.
        assert!(
            check_table_entry(
                &torus,
                1,
                1,
                0,
                1,
                alpha,
                beta,
                &delta_pq,
                &combined_gamma,
                rows_gamma,
                boundary_gamma_len,
                None,
                true,
                recorded,
            )
            .is_ok()
        );

        // ADVERSARIAL: the wrong sign_odd (false) must be refused, since the
        // genuine off-diagonal entry is nonzero so the negated and
        // unnegated values differ.
        let err = check_table_entry(
            &torus,
            1,
            1,
            0,
            1,
            alpha,
            beta,
            &delta_pq,
            &combined_gamma,
            rows_gamma,
            boundary_gamma_len,
            None,
            false,
            recorded,
        )
        .expect_err("a wrong sign_odd must be refused by the graded commutativity check");
        assert!(err.contains("commutativity"), "got: {err}");
    }

    // Silence an unused-import warning if `CupProductCertificate` is only
    // ever named via `cup_product_f2`/`cup_product_q`'s return type in some
    // configurations.
    #[allow(dead_code)]
    fn _type_is_named(_: Option<CupProductCertificate>) {}
}
