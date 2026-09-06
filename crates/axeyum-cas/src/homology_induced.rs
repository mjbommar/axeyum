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
use crate::{CasExpr, Matrix};

use super::{SimplicialComplex, boundary_matrix, is_zero_matrix};

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

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::{induced_homology, is_simplicial};
    use crate::homology::SimplicialComplex;
    use crate::homology::fixtures::{circle, hexagon_circle, point};

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
}
