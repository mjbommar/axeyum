//! Simplicial maps and their induced maps on homology over `Q`.
//!
//! # What this computes
//!
//! A vertex map `f : V(X) -> V(Y)` between two [`SimplicialComplex`]es is
//! **simplicial** ([`is_simplicial`]) if the image of every face of `X`
//! (vertices mapped through `f`, deduplicated) is itself a face of `Y` --
//! images may collapse dimension (several vertices of a face landing on one
//! vertex of `Y`), which is allowed, just not required to preserve dimension.
//!
//! Such a map induces a **chain map** `f_# : C_k(X) -> C_k(Y)` at every degree
//! ([`build_chain_map`]): a non-degenerate `k`-simplex (`f` injective on its
//! vertices) maps to the corresponding `k`-simplex of `Y` with sign equal to
//! the parity of the permutation reordering the images back into ascending
//! order (the same convention [`super::boundary_matrix`] implicitly relies
//! on: both bases are the SORTED vertex tuple); a degenerate simplex maps to
//! `0`, the standard convention. `f_#` commutes with the boundary
//! (`d'_k . f_#(k) = f_#(k-1) . d_k`) whenever `f` is simplicial -- checked
//! directly rather than assumed.
//!
//! The **induced map** on `H_k(-; Q)` ([`induced_homology`]) needs a basis of
//! each `H_k`, chosen deterministically: `choose_homology_basis` takes the
//! kernel of `d_k` ([`Matrix::null_space`], itself deterministic: free
//! variables in ascending column order) and greedily keeps the vectors that
//! increase the rank of the accumulated set, seeded by a basis of the
//! boundary space `B_k = im(d_{k+1})` chosen the same way from the columns of
//! `d_{k+1}`. This yields, for each of `X` and `Y`, a genuine basis of `Z_k`
//! split into a `B_k`-part and an extension (the `H_k` representatives). For
//! each domain basis cycle `z_i`, `f_#(z_i)` is a cycle of `Y` (guaranteed by
//! the commutation identity); `solve_via_rref` expresses it uniquely in the
//! combined `[B_k(Y) basis | H_k(Y) basis]` basis of `Z_k(Y)` via one
//! augmented [`Matrix::rref`], and the `H_k(Y)`-tail of that coefficient
//! vector is the `i`-th column of the induced matrix. **The rank of that
//! matrix is the invariant this module treats as the headline claim** (it is
//! basis-independent, unlike the matrix's individual entries).
//!
//! # What is certified
//!
//! [`SimplicialMapCertificate::verify`] re-derives every claim from
//! `(vertex_map, domain, codomain)` alone:
//!
//! - the map is re-checked simplicial (`is_simplicial`);
//! - every recorded chain map is rebuilt fresh and compared entrywise
//!   (`chain_maps_match`, the same rebuild-and-compare pattern
//!   `super::boundaries_match` uses for boundary matrices);
//! - `d'_k . f_#(k) = f_#(k-1) . d_k` holds at every degree
//!   (`chain_map_commutes`), an algebraic identity independent of how the
//!   chain map was built;
//! - every recorded basis vector is a genuine cycle (`basis_vectors_are_cycles`);
//! - each recorded homology basis genuinely extends a genuine basis of the
//!   boundary space to a basis of the FULL kernel -- not a proper subspace of
//!   it -- via a rank identity (`basis_is_a_genuine_extension`);
//! - every recorded induced matrix is rebuilt fresh (by the same
//!   deterministic `solve_via_rref` construction, over the now-verified
//!   bases and chain maps) and compared entrywise (`induced_matches`), and
//!   its recorded rank is recomputed and compared.
//!
//! What is **not** re-derived independently of `solve_via_rref` itself: given
//! the bases and chain maps are already confirmed correct by the guards
//! above, `solve_via_rref`'s answer is the UNIQUE coefficient vector solving
//! a consistent full-column-rank linear system, so re-running it and
//! comparing catches a forged `induced` field but not a bug shared between
//! production and verification (the same caveat the parent module's own doc
//! comment states for `Matrix::determinant`).
//!
//! # Cost profile
//!
//! The `Q` linear algebra (`null_space`, `rref`) is exact `Rational`
//! Gauss-Jordan; the greedy basis selection re-runs a rank computation once
//! per candidate column, so `choose_homology_basis` is `O(n^2)` rank calls
//! for `n` candidates, each itself polynomial. The largest fixture exercised
//! here is the 6-vertex/6-edge hexagon wrapping the 3-vertex/3-edge triangle
//! (the degree-two map test); see [`super::coefficients`]'s doc comment for
//! the whole-suite release timing.

use std::collections::BTreeMap;

use axeyum_ir::Rational;

use crate::homology::coefficients::rank_over_q;
use crate::normalforms::{certify_product_equals, smith_normal_form};
use crate::{CasExpr, Matrix};

use super::{SimplicialComplex, boundary_matrix, diagonal_rank, is_zero_matrix, torsion_factors};

/// Whether `vertex_map` sends every face of `domain` (at every dimension,
/// including vertices) to a face of `codomain`. `false` if `vertex_map` does
/// not cover every vertex `domain` actually uses.
#[must_use]
pub fn is_simplicial(
    vertex_map: &BTreeMap<usize, usize>,
    domain: &SimplicialComplex,
    codomain: &SimplicialComplex,
) -> bool {
    for k in 0..=domain.max_dimension() {
        for face in domain.simplices(k) {
            let Some(mut image): Option<Vec<usize>> =
                face.iter().map(|v| vertex_map.get(v).copied()).collect()
            else {
                return false;
            };
            image.sort_unstable();
            image.dedup();
            if !codomain.contains_face(&image) {
                return false;
            }
        }
    }
    true
}

/// The sign of the permutation that sorts `values` into ascending order
/// (parity of the inversion count), for a sequence of pairwise-distinct
/// values.
fn permutation_sign(values: &[usize]) -> i128 {
    let n = values.len();
    let mut inversions = 0usize;
    for i in 0..n {
        for j in (i + 1)..n {
            if values[i] > values[j] {
                inversions += 1;
            }
        }
    }
    if inversions.is_multiple_of(2) { 1 } else { -1 }
}

/// Build the chain map `f_#(k) : C_k(domain) -> C_k(codomain)` from a
/// (already simplicial) vertex map. Returns `None` if `vertex_map` does not
/// cover a vertex of some `k`-simplex, or on a shape overflow.
#[must_use]
pub fn build_chain_map(
    vertex_map: &BTreeMap<usize, usize>,
    domain: &SimplicialComplex,
    codomain: &SimplicialComplex,
    k: usize,
) -> Option<Matrix> {
    let domain_simplices = domain.simplices(k);
    let codomain_simplices = codomain.simplices(k);
    let row_index: BTreeMap<Vec<usize>, usize> = codomain_simplices
        .iter()
        .cloned()
        .enumerate()
        .map(|(i, face)| (face, i))
        .collect();
    let rows = codomain_simplices.len();
    let cols = domain_simplices.len();
    let mut data = vec![CasExpr::zero(); rows.checked_mul(cols)?];
    for (col_idx, simplex) in domain_simplices.iter().enumerate() {
        let images: Option<Vec<usize>> =
            simplex.iter().map(|v| vertex_map.get(v).copied()).collect();
        let images = images?;
        let mut sorted_images = images.clone();
        sorted_images.sort_unstable();
        sorted_images.dedup();
        if sorted_images.len() != images.len() {
            continue; // degenerate simplex: the chain map sends it to 0.
        }
        let sign = permutation_sign(&images);
        if let Some(&row_idx) = row_index.get(&sorted_images) {
            data[row_idx * cols + col_idx] = CasExpr::int(sign);
        }
        // If the image is genuinely absent from `codomain` this leaves a `0`
        // column entry; `induced_homology` refuses such a map up front via
        // `is_simplicial`, so this branch is unreachable through the public
        // producer, but the function stays total rather than panicking.
    }
    Matrix::new(rows, cols, data)
}

/// One column of `matrix` as an `n x 1` [`Matrix`].
fn column_vector(matrix: &Matrix, col: usize) -> Option<Matrix> {
    let rows = matrix.rows();
    let mut data = Vec::with_capacity(rows);
    for row in 0..rows {
        data.push(matrix.get(row, col)?.clone());
    }
    Matrix::new(rows, 1, data)
}

/// Stack a list of `n x 1` column vectors side by side into an `n x m`
/// matrix. Returns `None` on a shape mismatch or overflow.
fn columns_to_matrix(columns: &[Matrix], rows: usize) -> Option<Matrix> {
    let cols = columns.len();
    let mut data = vec![CasExpr::zero(); rows.checked_mul(cols)?];
    for (c, column) in columns.iter().enumerate() {
        if column.rows() != rows || column.cols() != 1 {
            return None;
        }
        for r in 0..rows {
            data[r * cols + c] = column.get(r, 0)?.clone();
        }
    }
    Matrix::new(rows, cols, data)
}

/// The rank of the span of a list of `n x 1` column vectors (`0` for an
/// empty list).
fn rank_of_columns(columns: &[Matrix], rows: usize) -> Option<usize> {
    if columns.is_empty() {
        return Some(0);
    }
    rank_over_q(&columns_to_matrix(columns, rows)?)
}

/// Greedily choose a basis for the column span of `boundary_next` (i.e. of
/// `B_k = im(d_{k+1})`), by walking its columns left to right and keeping
/// each one that increases the accumulated rank. Deterministic (fixed
/// column order).
fn choose_boundary_basis(boundary_next: &Matrix) -> Option<Vec<Matrix>> {
    let rows = boundary_next.rows();
    let mut chosen: Vec<Matrix> = Vec::new();
    let mut rank_so_far = 0usize;
    for c in 0..boundary_next.cols() {
        let candidate = column_vector(boundary_next, c)?;
        let mut trial = chosen.clone();
        trial.push(candidate.clone());
        let new_rank = rank_of_columns(&trial, rows)?;
        if new_rank > rank_so_far {
            chosen.push(candidate);
            rank_so_far = new_rank;
        }
    }
    Some(chosen)
}

/// Choose a genuine basis of `B_k` (via [`choose_boundary_basis`] on
/// `d_{k+1}`) and a genuine extension of it to a basis of `Z_k = ker(d_k)`
/// (via [`Matrix::null_space`] of `d_k`, walked in its own deterministic
/// order and kept whenever it increases the accumulated rank). Returns
/// `(boundary_basis, homology_basis)`, both lists of `n_k x 1` column
/// vectors of length `d_k.cols()`.
fn choose_homology_basis(
    boundary_k: &Matrix,
    boundary_next: &Matrix,
) -> Option<(Vec<Matrix>, Vec<Matrix>)> {
    let rows = boundary_k.cols(); // n_k
    let boundary_basis = choose_boundary_basis(boundary_next)?;
    let z_basis = boundary_k.null_space()?;
    let mut accumulated = boundary_basis.clone();
    let mut rank_so_far = rank_of_columns(&accumulated, rows)?;
    let mut homology_basis = Vec::new();
    for candidate in z_basis {
        let mut trial = accumulated.clone();
        trial.push(candidate.clone());
        let new_rank = rank_of_columns(&trial, rows)?;
        if new_rank > rank_so_far {
            homology_basis.push(candidate.clone());
            accumulated.push(candidate);
            rank_so_far = new_rank;
        }
    }
    Some((boundary_basis, homology_basis))
}

/// Solve `basis * c = target` for the unique `c`, assuming `basis`'s columns
/// are linearly independent and `target` lies in their span (both guaranteed
/// by the caller's construction, and reconfirmed by the residual check
/// below). Returns `None` if that assumption fails (a genuine inconsistency,
/// or a shape/overflow problem) -- this is the one place a caller can detect
/// "target was not actually in the span" instead of silently misreading a
/// row.
fn solve_via_rref(basis: &Matrix, target: &Matrix) -> Option<Vec<Rational>> {
    let rows = basis.rows();
    let cols = basis.cols();
    if cols == 0 {
        return if is_zero_matrix(target) {
            Some(Vec::new())
        } else {
            None
        };
    }
    let mut augmented_data = Vec::with_capacity(rows * (cols + 1));
    for r in 0..rows {
        for c in 0..cols {
            augmented_data.push(basis.get(r, c)?.clone());
        }
        augmented_data.push(target.get(r, 0)?.clone());
    }
    let augmented = Matrix::new(rows, cols + 1, augmented_data)?;
    let reduced = augmented.rref()?;

    let mut coefficients = Vec::with_capacity(cols);
    for j in 0..cols {
        let CasExpr::Const(pivot) = reduced.get(j, j)? else {
            return None;
        };
        if *pivot != Rational::integer(1) {
            return None; // not a pivot here: `basis` was not full column rank
        }
        let CasExpr::Const(value) = reduced.get(j, cols)? else {
            return None;
        };
        coefficients.push(*value);
    }
    // Consistency: every row past the basis's rank must have a zero
    // right-hand side, or `target` was never in `basis`'s span.
    for r in cols..rows {
        let CasExpr::Const(value) = reduced.get(r, cols)? else {
            return None;
        };
        if !value.is_zero() {
            return None;
        }
    }
    Some(coefficients)
}

/// A checkable certificate of a simplicial map's chain map and its induced
/// map on `H_*(-; Q)`. See the module documentation for what
/// [`verify`](Self::verify) re-derives.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SimplicialMapCertificate {
    /// The vertex map, domain vertex id to codomain vertex id.
    pub vertex_map: BTreeMap<usize, usize>,
    /// `domain.max_dimension()` at the time this certificate was built.
    pub max_dimension: usize,
    /// The chain map `f_#(k)` for `k` in `0..=max_dimension`.
    pub chain_maps: BTreeMap<usize, Matrix>,
    /// The chosen `H_k(domain; Q)` basis (cycle representatives), for `k` in
    /// `0..=max_dimension`.
    pub basis_domain: BTreeMap<usize, Vec<Matrix>>,
    /// The chosen `H_k(codomain; Q)` basis (cycle representatives), for `k`
    /// in `0..=max_dimension`.
    pub basis_codomain: BTreeMap<usize, Vec<Matrix>>,
    /// The induced map `f_*(k) : H_k(domain; Q) -> H_k(codomain; Q)` as a
    /// `b_k(codomain) x b_k(domain)` matrix over the two chosen bases, for
    /// `k` in `0..=max_dimension`.
    pub induced: BTreeMap<usize, Matrix>,
    /// `rank(f_*(k))`, the basis-independent invariant, for `k` in
    /// `0..=max_dimension`.
    pub induced_rank: BTreeMap<usize, usize>,
}

/// The result of a successful [`SimplicialMapCertificate::verify`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InducedReport {
    /// `rank(f_*(k))`, recomputed, for `k` in `0..=max_dimension`.
    pub induced_rank: BTreeMap<usize, usize>,
}

/// Compute the induced map on `H_*(-; Q)` of a simplicial vertex map.
///
/// Returns `None` if `vertex_map` is not simplicial ([`is_simplicial`]), or
/// if any step of the construction declines (an `i128` rational overflow;
/// not expected for the sizes this module targets).
#[must_use]
pub fn induced_homology(
    vertex_map: &BTreeMap<usize, usize>,
    domain: &SimplicialComplex,
    codomain: &SimplicialComplex,
) -> Option<SimplicialMapCertificate> {
    if !is_simplicial(vertex_map, domain, codomain) {
        return None;
    }
    let max_dim = domain.max_dimension();

    let mut chain_maps = BTreeMap::new();
    for k in 0..=max_dim {
        chain_maps.insert(k, build_chain_map(vertex_map, domain, codomain, k)?);
    }

    let mut basis_domain = BTreeMap::new();
    let mut basis_codomain = BTreeMap::new();
    let mut induced = BTreeMap::new();
    let mut induced_rank = BTreeMap::new();

    for k in 0..=max_dim {
        let d_domain_k = boundary_matrix(domain, k)?;
        let d_domain_next = boundary_matrix(domain, k + 1)?;
        let d_codomain_k = boundary_matrix(codomain, k)?;
        let d_codomain_next = boundary_matrix(codomain, k + 1)?;

        let (_, h_basis_x) = choose_homology_basis(&d_domain_k, &d_domain_next)?;
        let (b_basis_y, h_basis_y) = choose_homology_basis(&d_codomain_k, &d_codomain_next)?;

        let rows_y = d_codomain_k.cols(); // n_k(codomain)
        let combined_y: Vec<Matrix> = b_basis_y
            .iter()
            .cloned()
            .chain(h_basis_y.iter().cloned())
            .collect();
        let q_y = columns_to_matrix(&combined_y, rows_y)?;

        let chain_map_k = chain_maps.get(&k)?;
        let b_k_x = h_basis_x.len();
        let b_k_y = h_basis_y.len();
        let mut data = vec![CasExpr::zero(); b_k_y.checked_mul(b_k_x)?];
        for (i, z) in h_basis_x.iter().enumerate() {
            let image = chain_map_k.mul(z)?;
            let coefficients = solve_via_rref(&q_y, &image)?;
            for j in 0..b_k_y {
                let value = coefficients[b_basis_y.len() + j];
                data[j * b_k_x + i] = CasExpr::Const(value);
            }
        }
        let induced_matrix = Matrix::new(b_k_y, b_k_x, data)?;
        let rank = rank_over_q(&induced_matrix)?;

        basis_domain.insert(k, h_basis_x);
        basis_codomain.insert(k, h_basis_y);
        induced.insert(k, induced_matrix);
        induced_rank.insert(k, rank);
    }

    Some(SimplicialMapCertificate {
        vertex_map: vertex_map.clone(),
        max_dimension: max_dim,
        chain_maps,
        basis_domain,
        basis_codomain,
        induced,
        induced_rank,
    })
}

/// Guard: every recorded chain map is rebuilt fresh from `vertex_map` and the
/// two complexes and matches entrywise.
fn chain_maps_match(
    certificate: &SimplicialMapCertificate,
    domain: &SimplicialComplex,
    codomain: &SimplicialComplex,
) -> Result<(), String> {
    for k in 0..=certificate.max_dimension {
        let rebuilt = build_chain_map(&certificate.vertex_map, domain, codomain, k)
            .ok_or_else(|| format!("could not rebuild the chain map at degree {k}"))?;
        let Some(recorded) = certificate.chain_maps.get(&k) else {
            return Err(format!("certificate has no chain map at degree {k}"));
        };
        if rebuilt.rows() != recorded.rows() || rebuilt.cols() != recorded.cols() {
            return Err(format!("chain map shape mismatch at degree {k}"));
        }
        for row in 0..rebuilt.rows() {
            for col in 0..rebuilt.cols() {
                if rebuilt.get(row, col) != recorded.get(row, col) {
                    return Err(format!(
                        "chain map entry mismatch at degree {k}, ({row}, {col})"
                    ));
                }
            }
        }
    }
    Ok(())
}

/// Guard: `d'_k . f_#(k) = f_#(k-1) . d_k` for `k` in `1..=max_dimension`.
fn chain_map_commutes(
    certificate: &SimplicialMapCertificate,
    domain: &SimplicialComplex,
    codomain: &SimplicialComplex,
) -> Result<(), String> {
    for k in 1..=certificate.max_dimension {
        let d_domain_k =
            boundary_matrix(domain, k).ok_or_else(|| format!("could not rebuild domain d_{k}"))?;
        let d_codomain_k = boundary_matrix(codomain, k)
            .ok_or_else(|| format!("could not rebuild codomain d_{k}"))?;
        let f_k = certificate
            .chain_maps
            .get(&k)
            .ok_or_else(|| format!("no chain map at degree {k}"))?;
        let f_k_minus_1 = certificate
            .chain_maps
            .get(&(k - 1))
            .ok_or_else(|| format!("no chain map at degree {}", k - 1))?;
        let left = d_codomain_k
            .mul(f_k)
            .ok_or_else(|| format!("d'_{k} . f_#({k}) failed to multiply"))?;
        let right = f_k_minus_1
            .mul(&d_domain_k)
            .ok_or_else(|| format!("f_#({}) . d_{k} failed to multiply", k - 1))?;
        let difference = left
            .sub(&right)
            .ok_or_else(|| format!("shape mismatch comparing commutation at degree {k}"))?;
        if !is_zero_matrix(&difference) {
            return Err(format!(
                "f does not commute with the boundary at degree {k}"
            ));
        }
    }
    Ok(())
}

/// Guard: every recorded basis vector (domain and codomain, every degree) is
/// a genuine cycle.
fn basis_vectors_are_cycles(
    certificate: &SimplicialMapCertificate,
    domain: &SimplicialComplex,
    codomain: &SimplicialComplex,
) -> Result<(), String> {
    for k in 0..=certificate.max_dimension {
        let d_domain_k =
            boundary_matrix(domain, k).ok_or_else(|| format!("could not rebuild domain d_{k}"))?;
        for z in certificate.basis_domain.get(&k).into_iter().flatten() {
            let image = d_domain_k
                .mul(z)
                .ok_or_else(|| format!("d_{k} . z failed to multiply (domain, degree {k})"))?;
            if !is_zero_matrix(&image) {
                return Err(format!(
                    "a recorded domain basis vector at degree {k} is not a cycle"
                ));
            }
        }
        let d_codomain_k = boundary_matrix(codomain, k)
            .ok_or_else(|| format!("could not rebuild codomain d_{k}"))?;
        for w in certificate.basis_codomain.get(&k).into_iter().flatten() {
            let image = d_codomain_k
                .mul(w)
                .ok_or_else(|| format!("d_{k} . w failed to multiply (codomain, degree {k})"))?;
            if !is_zero_matrix(&image) {
                return Err(format!(
                    "a recorded codomain basis vector at degree {k} is not a cycle"
                ));
            }
        }
    }
    Ok(())
}

/// Guard: at every degree, the recorded homology basis (domain and
/// codomain) genuinely extends a genuine basis of `B_k` to a basis of the
/// FULL kernel `Z_k` -- not merely to some independent subset of it. This
/// pins down both that the recorded basis size equals `b_k` and that it
/// is linearly independent from the boundary space.
fn basis_is_a_genuine_extension(
    certificate: &SimplicialMapCertificate,
    domain: &SimplicialComplex,
    codomain: &SimplicialComplex,
) -> Result<(), String> {
    let check_one = |label: &str,
                     complex: &SimplicialComplex,
                     recorded_basis: &[Matrix],
                     k: usize|
     -> Result<(), String> {
        let d_k = boundary_matrix(complex, k)
            .ok_or_else(|| format!("could not rebuild {label} d_{k}"))?;
        let d_next = boundary_matrix(complex, k + 1)
            .ok_or_else(|| format!("could not rebuild {label} d_{}", k + 1))?;
        let rows = d_k.cols();
        let boundary_basis = choose_boundary_basis(&d_next).ok_or_else(|| {
            format!("could not choose a boundary basis for {label} at degree {k}")
        })?;
        let boundary_rank = rank_of_columns(&boundary_basis, rows).ok_or_else(|| {
            format!("rank_over_q declined for {label} boundary basis at degree {k}")
        })?;
        let mut combined = boundary_basis;
        combined.extend(recorded_basis.iter().cloned());
        let combined_rank = rank_of_columns(&combined, rows).ok_or_else(|| {
            format!("rank_over_q declined for {label} combined basis at degree {k}")
        })?;
        if combined_rank != boundary_rank + recorded_basis.len() {
            return Err(format!(
                "{label} homology basis at degree {k} is not independent of the boundary space"
            ));
        }
        let rank_d_k =
            rank_over_q(&d_k).ok_or_else(|| format!("rank_over_q declined for {label} d_{k}"))?;
        let dim_z_k = rows
            .checked_sub(rank_d_k)
            .ok_or_else(|| format!("rank(d_{k}) exceeds n_{k} for {label}"))?;
        if combined_rank != dim_z_k {
            return Err(format!(
                "{label} homology basis at degree {k} does not extend to the full kernel (combined rank {combined_rank}, dim Z_{k} = {dim_z_k})"
            ));
        }
        Ok(())
    };

    for k in 0..=certificate.max_dimension {
        let domain_basis = certificate
            .basis_domain
            .get(&k)
            .cloned()
            .unwrap_or_default();
        check_one("domain", domain, &domain_basis, k)?;
        let codomain_basis = certificate
            .basis_codomain
            .get(&k)
            .cloned()
            .unwrap_or_default();
        check_one("codomain", codomain, &codomain_basis, k)?;
    }
    Ok(())
}

/// Guard: every recorded induced matrix (and its rank) is rebuilt fresh from
/// the now-verified chain maps and bases, and matches.
fn induced_matches(
    certificate: &SimplicialMapCertificate,
    codomain: &SimplicialComplex,
) -> Result<BTreeMap<usize, usize>, String> {
    let mut recomputed_rank = BTreeMap::new();
    for k in 0..=certificate.max_dimension {
        let d_codomain_k = boundary_matrix(codomain, k)
            .ok_or_else(|| format!("could not rebuild codomain d_{k}"))?;
        let d_codomain_next = boundary_matrix(codomain, k + 1)
            .ok_or_else(|| format!("could not rebuild codomain d_{}", k + 1))?;
        let (b_basis_y, _) = choose_homology_basis(&d_codomain_k, &d_codomain_next)
            .ok_or_else(|| format!("could not choose the codomain boundary basis at degree {k}"))?;
        let h_basis_x = certificate
            .basis_domain
            .get(&k)
            .cloned()
            .unwrap_or_default();
        let h_basis_y = certificate
            .basis_codomain
            .get(&k)
            .cloned()
            .unwrap_or_default();
        let rows_y = d_codomain_k.cols();
        let combined_y: Vec<Matrix> = b_basis_y
            .iter()
            .cloned()
            .chain(h_basis_y.iter().cloned())
            .collect();
        let q_y = columns_to_matrix(&combined_y, rows_y)
            .ok_or_else(|| format!("could not stack the codomain basis at degree {k}"))?;
        let chain_map_k = certificate
            .chain_maps
            .get(&k)
            .ok_or_else(|| format!("no chain map at degree {k}"))?;
        let b_k_x = h_basis_x.len();
        let b_k_y = h_basis_y.len();
        let mut data =
            vec![CasExpr::zero(); b_k_y.checked_mul(b_k_x).ok_or("induced shape overflow")?];
        for (i, z) in h_basis_x.iter().enumerate() {
            let image = chain_map_k
                .mul(z)
                .ok_or_else(|| format!("f_#({k}) . z failed to multiply"))?;
            let coefficients = solve_via_rref(&q_y, &image).ok_or_else(|| {
                format!("could not express f_#(z_{i}) in the codomain basis at degree {k}")
            })?;
            for j in 0..b_k_y {
                data[j * b_k_x + i] = CasExpr::Const(coefficients[b_basis_y.len() + j]);
            }
        }
        let rebuilt = Matrix::new(b_k_y, b_k_x, data)
            .ok_or_else(|| format!("could not build the rebuilt induced matrix at degree {k}"))?;
        let Some(recorded) = certificate.induced.get(&k) else {
            return Err(format!("certificate has no induced matrix at degree {k}"));
        };
        if rebuilt.rows() != recorded.rows() || rebuilt.cols() != recorded.cols() {
            return Err(format!("induced matrix shape mismatch at degree {k}"));
        }
        for row in 0..rebuilt.rows() {
            for col in 0..rebuilt.cols() {
                if rebuilt.get(row, col) != recorded.get(row, col) {
                    return Err(format!(
                        "induced matrix entry mismatch at degree {k}, ({row}, {col})"
                    ));
                }
            }
        }
        let recomputed = rank_over_q(&rebuilt)
            .ok_or_else(|| format!("rank_over_q declined for the induced matrix at degree {k}"))?;
        let Some(&claimed) = certificate.induced_rank.get(&k) else {
            return Err(format!("certificate has no induced rank at degree {k}"));
        };
        if recomputed != claimed {
            return Err(format!(
                "induced rank mismatch at degree {k}: recomputed {recomputed}, certificate claims {claimed}"
            ));
        }
        recomputed_rank.insert(k, recomputed);
    }
    Ok(recomputed_rank)
}

impl SimplicialMapCertificate {
    /// Re-derive every claim in this certificate from `(vertex_map, domain,
    /// codomain)` alone. See the module documentation for exactly what each
    /// guard would miss if it were absent.
    ///
    /// # Errors
    ///
    /// Returns a distinct, descriptive `Err(String)` for whichever guard
    /// fails first: the map is not simplicial, a chain map does not match a
    /// fresh rebuild, the chain map fails to commute with the boundary, a
    /// basis vector is not a cycle, a basis fails to extend the boundary
    /// space to the full kernel, or an induced matrix (or its rank) does not
    /// match a fresh rebuild.
    pub fn verify(
        &self,
        domain: &SimplicialComplex,
        codomain: &SimplicialComplex,
    ) -> Result<InducedReport, String> {
        if !is_simplicial(&self.vertex_map, domain, codomain) {
            return Err("the recorded vertex map is not simplicial".to_string());
        }
        if domain.max_dimension() != self.max_dimension {
            return Err(format!(
                "recorded max_dimension {} does not match domain.max_dimension() {}",
                self.max_dimension,
                domain.max_dimension()
            ));
        }
        chain_maps_match(self, domain, codomain)?;
        chain_map_commutes(self, domain, codomain)?;
        basis_vectors_are_cycles(self, domain, codomain)?;
        basis_is_a_genuine_extension(self, domain, codomain)?;
        let induced_rank = induced_matches(self, codomain)?;
        Ok(InducedReport { induced_rank })
    }
}

// =============================================================================
// Wave three: induced maps on `H_*(-; Z)`, including the torsion part.
// =============================================================================
//
// A homomorphism `H_k(X; Z) -> H_k(Y; Z)` between two graded abelian groups
// `Z^{f_X} (+) T_X` and `Z^{f_Y} (+) T_Y` (`T_*` the torsion subgroup) is, in
// full generality, a 2x2 block matrix `[[A, B], [C, D]]` (free->free,
// torsion->free, free->torsion, torsion->torsion). Block `B` (torsion ->
// free) is ALWAYS zero: a finite-order element cannot map to a nonzero
// element of a torsion-free group. This module reports `A` (`free_part`) and
// `D` (`torsion_part`) -- exactly the two pieces the brief asks for -- and
// certifies `B = 0` as a guard; the mixed block `C` (free -> torsion) is
// computed internally (it has to be, since the algorithm below derives all
// four blocks from one uniform construction) but not separately reported.
//
// # Deriving explicit `H_k(Z)` generators from two Smith forms
//
// Given `d_k`'s own Smith form `U * d_k * V = D` (`U`, `V` unimodular), the
// "kernel columns" of `V` (those at the zero-diagonal positions of `D`) are a
// genuine Z-BASIS of `Z_k = ker(d_k)` -- not merely a Q-spanning set, because
// `V` is unimodular over Z. Call this basis `z_basis` (an `n_k x m` integer
// matrix, `m = n_k - rank(d_k)`).
//
// To locate `B_k = im(d_{k+1})` inside `Z_k`, take `d_{k+1}`'s OWN (fresh,
// independent) Smith form `U' * d_{k+1} * V' = D'`. The identity `d_{k+1} .
// V' = U'^{-1} . D'` means the `i`-th generator of `B_k` (`i` up to
// `rank(d_{k+1})`) is simply `d_{k+1}` applied to the `i`-th column of `V'`
// -- computable directly, with no matrix inverse needed. Expressing each of
// these `rank(d_{k+1})` generators in `z_basis` coordinates (solved via
// [`solve_via_rref`], reused from the `Q` construction above -- exact because
// every boundary genuinely lies in `Z_k`) gives an `m x rank(d_{k+1})`
// "relations" matrix `R`. `H_k(Z) = Z^m / im(R)` by construction, and Smith
// form of `R` itself (`P * R * Q = diag(f_1, ..., f_s, 0, ...)`) diagonalizes
// exactly this quotient: in the `P`-transformed coordinate system, index `i
// < s` is torsion with modulus `f_i` (or, when `f_i = 1`, the trivial group
// -- dropped entirely, since `Z/1 = 0` is not a summand) and index `i >= s`
// is a free `Z` coordinate.
//
// `P` is unimodular, so `P^{-1}` (needed to turn "which coordinate" back into
// an actual cycle vector in `C_k`) is computed via [`Matrix::solve`] against
// the identity -- exact, since `det(P) = +/-1` makes every Cramer's-rule
// denominator `+/-1`. This is a full matrix inverse via Gauss-Jordan, so this
// module targets the SAME small hand-triangulated fixtures the rest of this
// crate's induced-map work does (RP^2, circles, the icosahedron below), not
// the hundreds-of-simplices scale [`super::super`]'s own ceiling work now
// reaches -- there has been no need to reuse `mul_int_fast` here since every
// fixture this module is tested on solves in well under the same modest
// budget the existing `Q` construction above already runs at.
//
// # What is certified
//
// [`IntegerInducedCertificate::verify`] re-derives every claim via
// [`compute_induced_block`] -- the SAME function the producer calls, at every
// degree, fresh from `(vertex_map, domain, codomain)` alone -- and additionally
// checks four things no rebuild-and-compare alone would catch:
//
// - every recorded generator column (domain and codomain) is a genuine cycle
//   (`d_k . g = 0`), independent of how [`smith_presentation`] built it;
// - the torsion->free block `B` is exactly zero (`cross_block_is_zero`) --
//   the "not secretly not a homomorphism" check described above;
// - every torsion entry `t` at `(row, col)` satisfies `(t * modulus_X(col))
//   mod modulus_Y(row) == 0` -- a torsion homomorphism `Z/a -> Z/b` must send
//   the generator to an element whose order divides `gcd(a, ...)`, and this
//   is the concrete integer form of that constraint;
// - the domain's and codomain's torsion coefficients, recomputed here via
//   the relations-matrix Smith form, equal the SAME complex's already-
//   independently-derived `Z` homology torsion from [`super::homology`] (a
//   fresh call, not a copy) -- a genuinely separate derivation of the same
//   invariant, matching this crate's UCT-style cross-checks elsewhere.

/// `matrix`'s entries at rows `row_start..row_end` and columns
/// `col_start..col_end`, as a `(row_end - row_start) x (col_end -
/// col_start)` matrix.
fn submatrix(
    matrix: &Matrix,
    row_start: usize,
    row_end: usize,
    col_start: usize,
    col_end: usize,
) -> Option<Matrix> {
    let height = row_end.checked_sub(row_start)?;
    let width = col_end.checked_sub(col_start)?;
    let mut data = vec![CasExpr::zero(); height.checked_mul(width)?];
    for (i, r) in (row_start..row_end).enumerate() {
        for (j, c) in (col_start..col_end).enumerate() {
            data[i * width + j] = matrix.get(r, c)?.clone();
        }
    }
    Matrix::new(height, width, data)
}

/// Every entry of `matrix` reduced modulo the corresponding entry of
/// `moduli` (one modulus per row). Returns `None` on a row-count mismatch or
/// a non-integer entry.
fn reduce_rows_mod(matrix: &Matrix, moduli: &[i128]) -> Option<Matrix> {
    if matrix.rows() != moduli.len() {
        return None;
    }
    let cols = matrix.cols();
    let mut data = Vec::with_capacity(matrix.rows() * cols);
    for (r, &modulus) in moduli.iter().enumerate() {
        for c in 0..cols {
            let CasExpr::Const(value) = matrix.get(r, c)? else {
                return None;
            };
            if value.denominator() != 1 {
                return None;
            }
            data.push(CasExpr::int(value.numerator().rem_euclid(modulus)));
        }
    }
    Matrix::new(matrix.rows(), cols, data)
}

/// The internal Smith-form derivation of `H_k(complex; Z)`'s presentation --
/// everything [`finalize_basis`] needs to build actual generator vectors.
/// Kept separate from [`IntegerHomologyBasis`] (the certificate-facing
/// summary) because [`compute_induced_block`] needs `z_basis` and `p` (to
/// project a chain map's image onto this basis) but the certificate itself
/// only needs to store and compare the smaller summary.
struct SmithPresentation {
    /// `n_k x m`: a Z-basis of `Z_k = ker(d_k)` (`m = n_k - rank(d_k)`).
    z_basis: Matrix,
    /// `m x m` unimodular left transform from the Smith form of the
    /// "relations" matrix (`B_k`'s generators expressed in `z_basis`
    /// coordinates).
    p: Matrix,
    /// The torsion coefficients (`> 1`) of that relations matrix's Smith
    /// diagonal, in divisibility order -- genuine torsion summands.
    torsion: Vec<i128>,
    /// How many of the relations matrix's leading nonzero diagonal entries
    /// are exactly `1` (trivial: `Z/1 = 0`, not a summand, so these
    /// `z_basis`/`p`-derived coordinates carry no information and are
    /// dropped from every reported generator list).
    null_count: usize,
}

/// Derive `complex`'s `SmithPresentation` at degree `k`, via two fresh,
/// independent [`smith_normal_form`] calls (`d_k` and `d_{k+1}`) -- see the
/// module documentation for the construction. Returns `None` if either
/// boundary matrix fails to reduce, if a boundary generator does not
/// actually lie in `z_basis`'s span (would mean a bug upstream, since every
/// boundary is a cycle by construction), or on a shape/overflow decline.
fn smith_presentation(complex: &SimplicialComplex, k: usize) -> Option<SmithPresentation> {
    let d_k = boundary_matrix(complex, k)?;
    let (_, d_k_diag, v_k) = smith_normal_form(&d_k)?;
    let rank_k = diagonal_rank(&d_k_diag)?;
    let n_k = v_k.cols();
    let m = n_k.checked_sub(rank_k)?;
    let z_basis = submatrix(&v_k, 0, v_k.rows(), rank_k, n_k)?;

    let d_next = boundary_matrix(complex, k + 1)?;
    let (_, d_next_diag, v_next) = smith_normal_form(&d_next)?;
    let rank_next = diagonal_rank(&d_next_diag)?;
    let v_next_first = submatrix(&v_next, 0, v_next.rows(), 0, rank_next)?;
    let boundary_gens = d_next.mul_fast_or_symbolic(&v_next_first)?;

    let mut relation_data = vec![CasExpr::zero(); m.checked_mul(rank_next)?];
    for col in 0..rank_next {
        let target = column_vector(&boundary_gens, col)?;
        let coeffs = solve_via_rref(&z_basis, &target)?;
        if coeffs.len() != m {
            return None;
        }
        for (row, value) in coeffs.iter().enumerate() {
            if value.denominator() != 1 {
                return None; // would mean a boundary generator was not actually in Z_k
            }
            relation_data[row * rank_next + col] = CasExpr::int(value.numerator());
        }
    }
    let relations = Matrix::new(m, rank_next, relation_data)?;
    let (p, diag, _q) = smith_normal_form(&relations)?;
    let s = diagonal_rank(&diag)?;
    let torsion = torsion_factors(&diag)?;
    let null_count = s.checked_sub(torsion.len())?;

    Some(SmithPresentation {
        z_basis,
        p,
        torsion,
        null_count,
    })
}

/// A Z-module presentation of `H_k(complex; Z)`, ready to certify and to
/// feed through a chain map: the KEPT generator cycle vectors (torsion
/// generators first, in divisibility order, then free generators), the
/// torsion moduli for the first `torsion.len()` columns, and the free rank
/// (`generators.cols() - torsion.len()`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntegerHomologyBasis {
    /// `n_k x (torsion.len() + free_rank)`: the kept generator cycle
    /// vectors, torsion columns first.
    pub generators: Matrix,
    /// The torsion coefficients (`> 1`), in divisibility order, one per
    /// leading column of `generators`.
    pub torsion: Vec<i128>,
    /// The free rank (the number of trailing columns of `generators`).
    pub free_rank: usize,
}

/// Build the actual generator matrix from a [`SmithPresentation`]: `z_basis
/// . P^{-1}`, with the leading `null_count` (trivial, `Z/1 = 0`) columns
/// dropped. `P^{-1}` is computed via [`Matrix::solve`] against the identity
/// (exact, since `P` is unimodular).
fn finalize_basis(raw: &SmithPresentation) -> Option<IntegerHomologyBasis> {
    let m = raw.p.rows();
    let p_inv = raw.p.solve(&Matrix::identity(m))?;
    let full_generators = raw.z_basis.mul_fast_or_symbolic(&p_inv)?;
    let keep_start = raw.null_count;
    let generators = submatrix(&full_generators, 0, full_generators.rows(), keep_start, m)?;
    let kept = m.checked_sub(keep_start)?;
    let free_rank = kept.checked_sub(raw.torsion.len())?;
    Some(IntegerHomologyBasis {
        generators,
        torsion: raw.torsion.clone(),
        free_rank,
    })
}

/// The full derivation at one degree `k`, shared by the producer
/// ([`induced_homology_z`]) and the verifier
/// ([`IntegerInducedCertificate::verify`]) so both call the exact same code.
struct InducedBlockAtK {
    basis_x: IntegerHomologyBasis,
    basis_y: IntegerHomologyBasis,
    /// `free_rank(Y) x free_rank(X)`: the free->free block (`A`).
    free_part: Matrix,
    /// `torsion_Y.len() x torsion_X.len()`: the torsion->torsion block
    /// (`D`), each entry already reduced mod that row's codomain modulus.
    torsion_part: Matrix,
    /// Whether the torsion->free block (`B`) is exactly zero -- must always
    /// be `true` for a genuine group homomorphism.
    cross_block_is_zero: bool,
}

fn compute_induced_block(
    vertex_map: &BTreeMap<usize, usize>,
    domain: &SimplicialComplex,
    codomain: &SimplicialComplex,
    k: usize,
) -> Option<InducedBlockAtK> {
    let raw_x = smith_presentation(domain, k)?;
    let raw_y = smith_presentation(codomain, k)?;
    let basis_x = finalize_basis(&raw_x)?;
    let basis_y = finalize_basis(&raw_y)?;

    let f_k = build_chain_map(vertex_map, domain, codomain, k)?;
    let images = f_k.mul_fast_or_symbolic(&basis_x.generators)?; // n_k(Y) x g_x

    let m_y = raw_y.p.rows();
    let g_x = images.cols();
    let mut y_coords_data = vec![CasExpr::zero(); m_y.checked_mul(g_x)?];
    for col in 0..g_x {
        let target = column_vector(&images, col)?;
        let coeffs = solve_via_rref(&raw_y.z_basis, &target)?;
        if coeffs.len() != m_y {
            return None;
        }
        for (row, value) in coeffs.iter().enumerate() {
            if value.denominator() != 1 {
                return None; // would mean f(g_x) is not actually a cycle of Y
            }
            y_coords_data[row * g_x + col] = CasExpr::int(value.numerator());
        }
    }
    let y_coords = Matrix::new(m_y, g_x, y_coords_data)?;
    let transformed = raw_y.p.mul_fast_or_symbolic(&y_coords)?; // m_y x g_x

    let tx = basis_x.torsion.len();
    // `transformed`'s ROWS are in Y's FULL (un-reindexed) v'-coordinate
    // space (`0..m_y`), unlike `basis_x.generators`'s already-reindexed
    // COLUMNS (torsion first, then free, starting at index 0 -- that
    // reindexing happened inside `finalize_basis`, which this function does
    // NOT re-run for the codomain's `transformed`). So the torsion ROWS are
    // `[raw_y.null_count, raw_y.null_count + ty)`, not `[0, ty)`: the
    // leading `raw_y.null_count` rows are the trivial (`Z/1 = 0`, "always
    // congruent to 0 mod 1") coordinates, which are skipped, not zero-
    // indexed. The free ROWS start at `m_y - basis_y.free_rank`, which
    // equals `raw_y.null_count + ty` algebraically (`free_rank = m - s`,
    // `s = null_count + ty`), so that boundary needed no such fix.
    let torsion_y_start = raw_y.null_count;
    let free_y_start = m_y.checked_sub(basis_y.free_rank)?;

    let torsion_block_raw = submatrix(&transformed, torsion_y_start, free_y_start, 0, tx)?;
    let torsion_part = reduce_rows_mod(&torsion_block_raw, &basis_y.torsion)?;

    let free_part = submatrix(&transformed, free_y_start, m_y, tx, g_x)?;

    let cross_block = submatrix(&transformed, free_y_start, m_y, 0, tx)?;
    let cross_block_is_zero = is_zero_matrix(&cross_block);

    Some(InducedBlockAtK {
        basis_x,
        basis_y,
        free_part,
        torsion_part,
        cross_block_is_zero,
    })
}

/// A checkable certificate of a simplicial map's induced map on `H_*(-;
/// Z)`, including the torsion part. See the module documentation for what
/// [`verify`](Self::verify) re-derives.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntegerInducedCertificate {
    /// The vertex map, domain vertex id to codomain vertex id.
    pub vertex_map: BTreeMap<usize, usize>,
    /// `domain.max_dimension()` at the time this certificate was built.
    pub max_dimension: usize,
    /// The domain's `H_k(Z)` presentation, for `k` in `0..=max_dimension`.
    pub domain_basis: BTreeMap<usize, IntegerHomologyBasis>,
    /// The codomain's `H_k(Z)` presentation, for `k` in `0..=max_dimension`.
    pub codomain_basis: BTreeMap<usize, IntegerHomologyBasis>,
    /// The free->free block of the induced map, for `k` in
    /// `0..=max_dimension`.
    pub free_part: BTreeMap<usize, Matrix>,
    /// The torsion->torsion block of the induced map, for `k` in
    /// `0..=max_dimension`.
    pub torsion_part: BTreeMap<usize, Matrix>,
}

/// The result of a successful [`IntegerInducedCertificate::verify`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntegerInducedReport {
    /// The free->free block, recomputed.
    pub free_part: BTreeMap<usize, Matrix>,
    /// The torsion->torsion block, recomputed.
    pub torsion_part: BTreeMap<usize, Matrix>,
}

/// Compute the induced map on `H_*(-; Z)` of a simplicial vertex map,
/// including the torsion part.
///
/// Returns `None` if `vertex_map` is not simplicial, if the torsion->free
/// block of the induced map is ever nonzero (would mean the constructed map
/// is not actually a group homomorphism -- not expected for a genuine chain
/// map, since that block's vanishing follows from `f_#` commuting with the
/// boundary), or if any step of the Smith-form construction declines.
#[must_use]
pub fn induced_homology_z(
    vertex_map: &BTreeMap<usize, usize>,
    domain: &SimplicialComplex,
    codomain: &SimplicialComplex,
) -> Option<IntegerInducedCertificate> {
    if !is_simplicial(vertex_map, domain, codomain) {
        return None;
    }
    let max_dim = domain.max_dimension();

    let mut domain_basis = BTreeMap::new();
    let mut codomain_basis = BTreeMap::new();
    let mut free_part = BTreeMap::new();
    let mut torsion_part = BTreeMap::new();

    for k in 0..=max_dim {
        let block = compute_induced_block(vertex_map, domain, codomain, k)?;
        if !block.cross_block_is_zero {
            return None;
        }
        domain_basis.insert(k, block.basis_x);
        codomain_basis.insert(k, block.basis_y);
        free_part.insert(k, block.free_part);
        torsion_part.insert(k, block.torsion_part);
    }

    Some(IntegerInducedCertificate {
        vertex_map: vertex_map.clone(),
        max_dimension: max_dim,
        domain_basis,
        codomain_basis,
        free_part,
        torsion_part,
    })
}

/// Guard: every generator column of `basis` (domain or codomain, at degree
/// `k`) is a genuine cycle of `complex`'s own `d_k`.
fn generators_are_cycles(
    basis: &IntegerHomologyBasis,
    complex: &SimplicialComplex,
    k: usize,
    label: &str,
) -> Result<(), String> {
    let d_k =
        boundary_matrix(complex, k).ok_or_else(|| format!("could not rebuild {label} d_{k}"))?;
    for col in 0..basis.generators.cols() {
        let g = column_vector(&basis.generators, col)
            .ok_or_else(|| format!("could not extract {label} generator column {col}"))?;
        let image = d_k
            .mul_fast_or_symbolic(&g)
            .ok_or_else(|| format!("d_{k} . g failed to multiply ({label}, column {col})"))?;
        if !is_zero_matrix(&image) {
            return Err(format!(
                "{label} generator column {col} at degree {k} is not a cycle"
            ));
        }
    }
    Ok(())
}

/// Guard: every torsion entry `t` at `(row, col)` of `torsion_part`
/// satisfies `(t * modulus_X(col)) mod modulus_Y(row) == 0` -- the concrete
/// integer form of "a homomorphism out of a finite cyclic group must send
/// the generator to an element whose order divides the generator's order".
fn torsion_entries_are_consistent(
    torsion_part: &Matrix,
    domain_torsion: &[i128],
    codomain_torsion: &[i128],
    k: usize,
) -> Result<(), String> {
    for row in 0..codomain_torsion.len() {
        let modulus_y = codomain_torsion[row];
        for col in 0..domain_torsion.len() {
            let modulus_x = domain_torsion[col];
            let CasExpr::Const(entry) = torsion_part.get(row, col).ok_or_else(|| {
                format!("torsion part missing entry ({row}, {col}) at degree {k}")
            })?
            else {
                return Err(format!(
                    "torsion part entry ({row}, {col}) at degree {k} is not a constant"
                ));
            };
            let value = entry.numerator();
            if (value * modulus_x).rem_euclid(modulus_y) != 0 {
                return Err(format!(
                    "torsion entry ({row}, {col}) at degree {k} is not a well-defined homomorphism: {value} * {modulus_x} is not 0 mod {modulus_y}"
                ));
            }
        }
    }
    Ok(())
}

/// Guard: the torsion coefficients recomputed here (via the relations-matrix
/// Smith form) equal the SAME complex's independently-derived `Z` homology
/// torsion from a fresh [`super::homology`] call -- a genuinely separate
/// derivation of the same invariant.
fn torsion_cross_checks_hold(
    basis: &IntegerHomologyBasis,
    complex: &SimplicialComplex,
    k: usize,
    label: &str,
) -> Result<(), String> {
    let certificate = super::homology(complex)
        .ok_or_else(|| format!("{label} homology() declined at degree {k}"))?;
    let expected_torsion = certificate.torsion.get(&k).cloned().unwrap_or_default();
    if basis.torsion != expected_torsion {
        return Err(format!(
            "{label} torsion at degree {k} ({:?}) disagrees with the independently-derived Z homology ({:?})",
            basis.torsion, expected_torsion
        ));
    }
    // `k` beyond `complex.max_dimension()` is a legitimate case (the domain
    // can have higher dimension than the codomain, e.g. collapsing onto a
    // point): `H_k = 0` there, so the expected Betti number is `0`, not a
    // missing-entry error.
    let expected_free_rank = certificate.betti.get(&k).copied().unwrap_or(0);
    if basis.free_rank != expected_free_rank {
        return Err(format!(
            "{label} free rank at degree {k} ({}) disagrees with the independently-derived Betti number ({expected_free_rank})",
            basis.free_rank
        ));
    }
    Ok(())
}

impl IntegerInducedCertificate {
    /// Re-derive every claim in this certificate from `(vertex_map, domain,
    /// codomain)` alone, via [`compute_induced_block`] -- the SAME function
    /// [`induced_homology_z`] calls -- at every degree, plus the additional
    /// algebraic checks described in the module documentation.
    ///
    /// # Errors
    ///
    /// Returns a distinct, descriptive `Err(String)` for whichever check
    /// fails first: the map is not simplicial, a degree mismatch, a
    /// rebuild-and-compare mismatch on either basis or either block, a
    /// generator that is not a genuine cycle, a nonzero torsion->free block,
    /// an inconsistent torsion entry, or a torsion/free-rank cross-check
    /// against the independently-derived `Z` homology.
    pub fn verify(
        &self,
        domain: &SimplicialComplex,
        codomain: &SimplicialComplex,
    ) -> Result<IntegerInducedReport, String> {
        if !is_simplicial(&self.vertex_map, domain, codomain) {
            return Err("the recorded vertex map is not simplicial".to_string());
        }
        if domain.max_dimension() != self.max_dimension {
            return Err(format!(
                "recorded max_dimension {} does not match domain.max_dimension() {}",
                self.max_dimension,
                domain.max_dimension()
            ));
        }

        let mut free_part = BTreeMap::new();
        let mut torsion_part = BTreeMap::new();

        for k in 0..=self.max_dimension {
            let block =
                compute_induced_block(&self.vertex_map, domain, codomain, k).ok_or_else(|| {
                    format!("could not rebuild the integer induced map at degree {k}")
                })?;
            if !block.cross_block_is_zero {
                return Err(format!(
                    "the torsion->free block is nonzero at degree {k} (not a genuine group homomorphism)"
                ));
            }

            let Some(recorded_x) = self.domain_basis.get(&k) else {
                return Err(format!("certificate has no domain basis at degree {k}"));
            };
            if recorded_x.torsion != block.basis_x.torsion
                || recorded_x.free_rank != block.basis_x.free_rank
                || !certify_product_equals(&recorded_x.generators, &block.basis_x.generators)
            {
                return Err(format!("domain H_k(Z) basis mismatch at degree {k}"));
            }
            let Some(recorded_y) = self.codomain_basis.get(&k) else {
                return Err(format!("certificate has no codomain basis at degree {k}"));
            };
            if recorded_y.torsion != block.basis_y.torsion
                || recorded_y.free_rank != block.basis_y.free_rank
                || !certify_product_equals(&recorded_y.generators, &block.basis_y.generators)
            {
                return Err(format!("codomain H_k(Z) basis mismatch at degree {k}"));
            }

            generators_are_cycles(&block.basis_x, domain, k, "domain")?;
            generators_are_cycles(&block.basis_y, codomain, k, "codomain")?;
            torsion_cross_checks_hold(&block.basis_x, domain, k, "domain")?;
            torsion_cross_checks_hold(&block.basis_y, codomain, k, "codomain")?;

            let Some(recorded_free) = self.free_part.get(&k) else {
                return Err(format!("certificate has no free part at degree {k}"));
            };
            if !certify_product_equals(recorded_free, &block.free_part) {
                return Err(format!("free part mismatch at degree {k}"));
            }
            let Some(recorded_torsion) = self.torsion_part.get(&k) else {
                return Err(format!("certificate has no torsion part at degree {k}"));
            };
            if !certify_product_equals(recorded_torsion, &block.torsion_part) {
                return Err(format!("torsion part mismatch at degree {k}"));
            }
            torsion_entries_are_consistent(
                recorded_torsion,
                &block.basis_x.torsion,
                &block.basis_y.torsion,
                k,
            )?;

            free_part.insert(k, block.free_part);
            torsion_part.insert(k, block.torsion_part);
        }

        Ok(IntegerInducedReport {
            free_part,
            torsion_part,
        })
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::{induced_homology, induced_homology_z, is_simplicial};
    use crate::homology::SimplicialComplex;
    use crate::homology::fixtures::{circle, hexagon_circle, point, rp2_6v};

    fn identity_map(complex: &SimplicialComplex) -> BTreeMap<usize, usize> {
        (0..=complex.max_dimension())
            .flat_map(|k| complex.simplices(k))
            .flatten()
            .map(|v| (v, v))
            .collect()
    }

    #[test]
    fn the_identity_map_induces_the_identity_on_h1() {
        let complex = circle();
        let vertex_map = identity_map(&complex);
        let certificate =
            induced_homology(&vertex_map, &complex, &complex).expect("identity is simplicial");
        certificate
            .verify(&complex, &complex)
            .expect("certificate verifies");
        assert_eq!(certificate.induced_rank[&0], 1);
        assert_eq!(certificate.induced_rank[&1], 1);
        // The induced map on H_1 is a 1x1 matrix; the identity induces +/-1
        // depending on the deterministic basis sign, never 0.
        let entry = certificate.induced[&1].get(0, 0).expect("1x1 matrix");
        let crate::CasExpr::Const(value) = entry else {
            panic!("expected a constant entry")
        };
        assert!(
            *value == axeyum_ir::Rational::integer(1) || *value == axeyum_ir::Rational::integer(-1),
            "identity map should induce +/-1 on H_1, got {value:?}"
        );
    }

    #[test]
    fn collapsing_a_circle_to_a_point_induces_zero_on_h1() {
        let domain = circle();
        let codomain = point();
        let vertex_map: BTreeMap<usize, usize> = [(0, 0), (1, 0), (2, 0)].into_iter().collect();
        assert!(is_simplicial(&vertex_map, &domain, &codomain));
        let certificate =
            induced_homology(&vertex_map, &domain, &codomain).expect("collapse is simplicial");
        certificate
            .verify(&domain, &codomain)
            .expect("certificate verifies");
        // H_1(point) = 0, so the induced map has 0 rows: trivially the zero
        // map into the trivial group.
        assert_eq!(certificate.basis_codomain[&1].len(), 0);
        assert_eq!(certificate.induced[&1].rows(), 0);
        assert_eq!(certificate.induced_rank[&1], 0);
    }

    #[test]
    fn the_degree_two_wrap_induces_multiplication_by_two_on_h1() {
        let domain = hexagon_circle(); // 6-vertex circle
        let codomain = circle(); // 3-vertex circle
        let vertex_map: BTreeMap<usize, usize> = (0..6).map(|v| (v, v % 3)).collect();
        assert!(is_simplicial(&vertex_map, &domain, &codomain));
        let certificate =
            induced_homology(&vertex_map, &domain, &codomain).expect("degree-2 wrap is simplicial");
        certificate
            .verify(&domain, &codomain)
            .expect("certificate verifies");
        assert_eq!(certificate.induced_rank[&0], 1);
        assert_eq!(certificate.induced_rank[&1], 1);
        let entry = certificate.induced[&1].get(0, 0).expect("1x1 matrix");
        let crate::CasExpr::Const(value) = entry else {
            panic!("expected a constant entry")
        };
        assert_eq!(
            value.numerator().unsigned_abs(),
            2,
            "expected |entry| = 2, got {value:?}"
        );
        assert_eq!(value.denominator(), 1);
    }

    #[test]
    fn a_non_simplicial_vertex_map_is_refused() {
        let domain = circle();
        // Two isolated points: no edge, so an identity vertex map cannot
        // send the domain's edges anywhere.
        let codomain = SimplicialComplex::from_maximal_simplices(&[vec![0], vec![1], vec![2]])
            .expect("valid complex");
        let vertex_map: BTreeMap<usize, usize> = [(0, 0), (1, 1), (2, 2)].into_iter().collect();
        assert!(!is_simplicial(&vertex_map, &domain, &codomain));
        assert!(induced_homology(&vertex_map, &domain, &codomain).is_none());
    }

    /// ADVERSARIAL. Forge only the recorded chain map at degree 1, leaving
    /// everything else genuine. `chain_maps_match` catches it before
    /// `chain_map_commutes` even runs (a forged entry would very likely also
    /// break commutation, but this isolates the rebuild-and-compare guard
    /// specifically). Confirmed by mutation: disabling only
    /// `chain_maps_match` leaves every other test in this module green.
    #[test]
    fn verify_refuses_a_forged_chain_map_entry() {
        let complex = circle();
        let vertex_map = identity_map(&complex);
        let mut certificate =
            induced_homology(&vertex_map, &complex, &complex).expect("identity is simplicial");
        assert!(certificate.verify(&complex, &complex).is_ok());

        let chain_map_1 = certificate.chain_maps.get_mut(&1).expect("degree 1 exists");
        // Flip one entry's sign: still a plausible-looking +/-1 entry, but
        // no longer what `build_chain_map` actually produces for the
        // identity map.
        let current = chain_map_1.get(0, 0).cloned().expect("in bounds");
        let crate::CasExpr::Const(value) = current else {
            panic!("expected a constant entry")
        };
        let flipped = crate::CasExpr::Const(-value);
        *chain_map_1 = crate::Matrix::new(
            chain_map_1.rows(),
            chain_map_1.cols(),
            (0..chain_map_1.rows() * chain_map_1.cols())
                .map(|i| {
                    if i == 0 {
                        flipped.clone()
                    } else {
                        chain_map_1
                            .get(i / chain_map_1.cols(), i % chain_map_1.cols())
                            .cloned()
                            .unwrap()
                    }
                })
                .collect(),
        )
        .expect("same shape");

        let err = certificate
            .verify(&complex, &complex)
            .expect_err("a forged chain map entry must be refused");
        assert!(err.contains("chain map"), "got: {err}");
    }

    /// ADVERSARIAL. Forge only the recorded `induced_rank`, leaving the
    /// `induced` matrix itself genuine. `induced_matches` recomputes the
    /// rank from the (genuine, rebuilt) matrix and disagrees. Confirmed by
    /// mutation: disabling only the rank-comparison check in
    /// `induced_matches` leaves every other test in this module green.
    #[test]
    fn verify_refuses_a_forged_induced_rank_with_the_matrix_genuine() {
        let domain = hexagon_circle();
        let codomain = circle();
        let vertex_map: BTreeMap<usize, usize> = (0..6).map(|v| (v, v % 3)).collect();
        let mut certificate =
            induced_homology(&vertex_map, &domain, &codomain).expect("degree-2 wrap is simplicial");
        assert!(certificate.verify(&domain, &codomain).is_ok());

        certificate.induced_rank.insert(1, 0); // the genuine rank is 1
        let err = certificate
            .verify(&domain, &codomain)
            .expect_err("a forged induced rank must be refused");
        assert!(err.contains("induced rank"), "got: {err}");
    }

    /// ADVERSARIAL. Forge the domain homology basis at degree 1 to a vector
    /// that is NOT a cycle (does not satisfy `d_1 . z = 0`), isolating
    /// `basis_vectors_are_cycles`.
    #[test]
    fn verify_refuses_a_basis_vector_that_is_not_a_cycle() {
        let complex = circle();
        let vertex_map = identity_map(&complex);
        let mut certificate =
            induced_homology(&vertex_map, &complex, &complex).expect("identity is simplicial");
        assert!(certificate.verify(&complex, &complex).is_ok());

        let basis = certificate
            .basis_domain
            .get_mut(&1)
            .expect("degree 1 exists");
        assert_eq!(basis.len(), 1, "circle has b_1 = 1");
        // Replace the genuine cycle (edges summing with zero boundary) with
        // the standard basis vector e_0 (a single edge alone), whose
        // boundary is generally nonzero.
        let rows = basis[0].rows();
        let mut data = vec![crate::CasExpr::zero(); rows];
        data[0] = crate::CasExpr::one();
        basis[0] = crate::Matrix::new(rows, 1, data).expect("column vector");

        let err = certificate
            .verify(&complex, &complex)
            .expect_err("a non-cycle basis vector must be refused");
        assert!(err.contains("not a cycle"), "got: {err}");
    }

    /// ADVERSARIAL, isolating `basis_is_a_genuine_extension` specifically --
    /// this guard had no forgery test at all (item 8 wave three's starting
    /// gap). Two disjoint circles have `b_1 = 2` and an EMPTY boundary space
    /// at degree 1 (no 2-simplices anywhere in the complex), so truncating
    /// the recorded basis to just ONE of the two independent cycle
    /// directions is still (a) a genuine cycle and (b) trivially
    /// independent of the (empty) boundary space -- it fails ONLY the
    /// "extends to the FULL kernel" half of the guard, which
    /// `basis_vectors_are_cycles` cannot catch (both tests would pass a
    /// basis that is cycle-valid but simply too small). Confirmed by
    /// mutation: disabling only the `combined_rank != dim_z_k` check (while
    /// keeping the independence check) leaves every other test in this
    /// module green.
    #[test]
    fn verify_refuses_a_basis_that_is_independent_but_does_not_span_the_full_kernel() {
        let complex = SimplicialComplex::from_maximal_simplices(&[
            vec![0, 1],
            vec![1, 2],
            vec![0, 2],
            vec![3, 4],
            vec![4, 5],
            vec![3, 5],
        ])
        .expect("two disjoint circles");
        let vertex_map = identity_map(&complex);
        let mut certificate =
            induced_homology(&vertex_map, &complex, &complex).expect("identity is simplicial");
        assert!(
            certificate.verify(&complex, &complex).is_ok(),
            "genuine certificate must verify"
        );
        assert_eq!(
            certificate.basis_domain[&1].len(),
            2,
            "two disjoint circles have b_1 = 2"
        );

        let basis = certificate
            .basis_domain
            .get_mut(&1)
            .expect("degree 1 exists");
        basis.truncate(1); // drop one of the two independent cycle directions

        let err = certificate
            .verify(&complex, &complex)
            .expect_err("an incomplete-but-independent basis must be refused");
        assert!(
            err.contains("does not extend to the full kernel"),
            "got: {err}"
        );
    }

    // ---- wave three: induced maps on H_*(Z), including torsion ----

    #[test]
    fn the_degree_two_wrap_induces_multiplication_by_two_on_h1_z() {
        let domain = hexagon_circle();
        let codomain = circle();
        let vertex_map: BTreeMap<usize, usize> = (0..6).map(|v| (v, v % 3)).collect();
        let certificate = induced_homology_z(&vertex_map, &domain, &codomain)
            .expect("degree-2 wrap is simplicial");
        let report = certificate
            .verify(&domain, &codomain)
            .expect("certificate verifies");
        // Both circles have torsion-free H_1(Z) = Z: no torsion generators
        // at all, so this exercises the pure free-part path.
        assert_eq!(certificate.domain_basis[&1].torsion, Vec::<i128>::new());
        assert_eq!(certificate.codomain_basis[&1].torsion, Vec::<i128>::new());
        assert_eq!(certificate.domain_basis[&1].free_rank, 1);
        assert_eq!(certificate.codomain_basis[&1].free_rank, 1);
        let free = &report.free_part[&1];
        assert_eq!((free.rows(), free.cols()), (1, 1));
        let crate::CasExpr::Const(value) = free.get(0, 0).expect("1x1") else {
            panic!("expected a constant entry")
        };
        assert_eq!(
            value.numerator().unsigned_abs(),
            2,
            "expected |entry| = 2, got {value:?}"
        );
    }

    #[test]
    fn the_identity_map_on_rp2_induces_the_identity_on_the_z2_torsion_of_h1() {
        let complex = rp2_6v();
        let vertex_map = identity_map(&complex);
        let certificate =
            induced_homology_z(&vertex_map, &complex, &complex).expect("identity is simplicial");
        certificate
            .verify(&complex, &complex)
            .expect("certificate verifies");
        assert_eq!(certificate.domain_basis[&1].torsion, vec![2]);
        assert_eq!(certificate.codomain_basis[&1].torsion, vec![2]);
        let torsion = &certificate.torsion_part[&1];
        assert_eq!((torsion.rows(), torsion.cols()), (1, 1));
        let crate::CasExpr::Const(value) = torsion.get(0, 0).expect("1x1") else {
            panic!("expected a constant entry")
        };
        assert_eq!(
            value.numerator(),
            1,
            "the identity map must induce 1 (mod 2) on the torsion generator, not 0"
        );

        // H_2(RP^2; Z) = 0: no free part and no torsion at that degree.
        assert_eq!(certificate.domain_basis[&2].free_rank, 0);
        assert_eq!(certificate.domain_basis[&2].torsion, Vec::<i128>::new());
        assert_eq!(
            (
                certificate.free_part[&2].rows(),
                certificate.free_part[&2].cols()
            ),
            (0, 0)
        );
    }

    #[test]
    fn collapsing_rp2_to_a_point_induces_the_zero_map_into_a_trivial_group() {
        let domain = rp2_6v();
        let codomain = point();
        let vertex_map: BTreeMap<usize, usize> = (0..6).map(|v| (v, 0)).collect();
        assert!(is_simplicial(&vertex_map, &domain, &codomain));
        let certificate =
            induced_homology_z(&vertex_map, &domain, &codomain).expect("collapse is simplicial");
        certificate
            .verify(&domain, &codomain)
            .expect("certificate verifies");
        // H_1(point) = H_2(point) = 0: the codomain has no torsion and no
        // free part at either degree, so both blocks are empty (0 rows).
        assert_eq!(certificate.codomain_basis[&1].free_rank, 0);
        assert_eq!(certificate.codomain_basis[&1].torsion, Vec::<i128>::new());
        assert_eq!(certificate.torsion_part[&1].rows(), 0);
        assert_eq!(certificate.free_part[&1].rows(), 0);
        assert_eq!(certificate.codomain_basis[&2].free_rank, 0);
        assert_eq!(certificate.torsion_part[&2].rows(), 0);
        assert_eq!(certificate.free_part[&2].rows(), 0);
    }

    /// A forged `free_part` (or `torsion_part`) must be refused, with every
    /// basis and every other block left genuine.
    #[test]
    fn verify_refuses_a_forged_integer_induced_matrix() {
        let complex = rp2_6v();
        let vertex_map = identity_map(&complex);
        let mut certificate =
            induced_homology_z(&vertex_map, &complex, &complex).expect("identity is simplicial");
        assert!(certificate.verify(&complex, &complex).is_ok());

        let torsion = certificate.torsion_part.get_mut(&1).expect("degree 1");
        *torsion = crate::Matrix::new(1, 1, vec![crate::CasExpr::int(0)]).expect("1x1");
        let err = certificate
            .verify(&complex, &complex)
            .expect_err("a forged torsion part must be refused");
        assert!(err.contains("torsion part mismatch"), "got: {err}");
    }

    /// ADVERSARIAL. Forge only `torsion_part` to an entry that is not a
    /// well-defined homomorphism (`2 mod 2 != 0` would be fine, but here we
    /// build a domain/codomain pair with DIFFERENT torsion moduli so a
    /// mismatched entry is detectable): the degree-2 wrap's domain `Z_2`
    /// torsion-free case does not exercise this, so instead corrupt RP^2's
    /// self-map torsion entry to `1` while claiming (falsely, by
    /// overwriting only the entry, not the recorded moduli) a modulus
    /// mismatch is impossible here since both sides are Z/2 -- this test
    /// instead calls `torsion_entries_are_consistent` directly with a
    /// hand-built inconsistent case, isolating the guard the way the parent
    /// module's own hard-to-isolate guards are tested.
    #[test]
    fn torsion_entries_are_consistent_refuses_an_algebraically_impossible_entry() {
        use super::torsion_entries_are_consistent;
        // Domain torsion modulus 2, codomain torsion modulus 4: an entry of
        // 1 would need `1 * 2 = 2` to be `0 mod 4`, which it is not.
        let torsion_part = crate::Matrix::new(1, 1, vec![crate::CasExpr::int(1)]).expect("1x1");
        let err = torsion_entries_are_consistent(&torsion_part, &[2], &[4], 1)
            .expect_err("an algebraically impossible entry must be refused");
        assert!(
            err.contains("not a well-defined homomorphism"),
            "got: {err}"
        );

        // POSITIVE CONTROL: an entry of 0 is always consistent (0 * m = 0
        // for any modulus).
        let zero_part = crate::Matrix::new(1, 1, vec![crate::CasExpr::int(0)]).expect("1x1");
        assert!(torsion_entries_are_consistent(&zero_part, &[2], &[4], 1).is_ok());
    }
}
