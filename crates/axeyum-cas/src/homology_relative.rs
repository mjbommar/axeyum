//! Relative simplicial homology `H_k(K, L)` for a subcomplex `L` of `K`, with
//! the long exact sequence of the pair certified as an exactness guard (item
//! 8, wave four).
//!
//! # What this computes
//!
//! `L` is a **subcomplex** of `K` ([`is_subcomplex`]) when every face of `L`,
//! at every dimension, is also a face of `K` (a `SimplicialComplex` is always
//! closed under faces by construction, so this one check is the whole
//! condition). [`relative_homology`] refuses (`None`) by name whenever this
//! fails -- checked directly, not inferred from a downstream shape mismatch.
//!
//! The **relative chain group** `C_k(K, L)` has basis the `k`-simplices of
//! `K` that are NOT simplices of `L` ([`relative_simplices`]); the relative
//! boundary map `d_k^{rel} : C_k(K,L) -> C_{k-1}(K,L)` is the submatrix of
//! `K`'s own `d_k` obtained by keeping only the rows and columns indexed by
//! those simplices ([`relative_boundary_matrix`]) -- because `L` is closed
//! under faces, a face of an `(L)`-simplex removed by the restriction can
//! never reappear as a face of a `(K \ L)`-simplex, which is exactly why this
//! submatrix construction, rather than some quotient-specific bookkeeping, is
//! the correct relative boundary map (the standard fact that `C_*(K)/C_*(L)`
//! has `K \ L`'s simplices as a basis with the induced differential).
//! [`relative_homology`] runs [`smith_normal_form`] on every `d_k^{rel}`
//! exactly as [`super::homology`] does for the absolute case, and reads off
//! Betti numbers and torsion the same rank-nullity way.
//!
//! # The long exact sequence, as a guard rather than a separate feature
//!
//! For every dimension `k` the pair `(K, L)` gives three maps over `Q`
//! (chosen deterministically, reusing [`super::induced`]'s basis-selection
//! and induced-matrix machinery verbatim rather than re-deriving it):
//!
//! - `i_* : H_k(L; Q) -> H_k(K; Q)`, induced by the chain-level inclusion
//!   `C_k(L) -> C_k(K)` (`inclusion_chain_map`) -- the identity map on the
//!   shared simplices, so it trivially commutes with the boundary;
//! - `j_* : H_k(K; Q) -> H_k(K,L; Q)`, induced by the chain-level quotient
//!   projection `C_k(K) -> C_k(K)/C_k(L)` (`quotient_chain_map`), which
//!   commutes with the boundary because `d^{rel}` is *defined* as the
//!   quotient of `d^K`;
//! - `delta : H_k(K,L; Q) -> H_{k-1}(L; Q)` (`connecting_map`), the
//!   connecting homomorphism: lift a relative cycle representative to an
//!   actual chain of `K` (zero on `L`'s simplices), take `K`'s own boundary,
//!   and -- after checking directly that the result is supported entirely on
//!   `L`'s simplices (the defining property of a relative cycle, and a
//!   genuine soundness guard: a bug upstream that failed to keep this true
//!   would be caught here, not silently miscounted) -- read that boundary
//!   chain as an `L`-cycle and express its class in `H_{k-1}(L; Q)`.
//!
//! `Q` is a field, so **exactness at each node is a rank identity**
//! (`les_exactness_holds`): for consecutive maps `f : A -> B` and
//! `g : B -> C` with `g . f = 0`, exactness at `B` (`im(f) = ker(g)`) holds
//! iff `rank(f) + rank(g) = dim(B)` (rank-nullity: `dim ker(g) = dim(B) -
//! rank(g)`, and exactness demands that kernel be exactly `im(f)`, of
//! dimension `rank(f)`). This module checks that identity at every node of
//! the sequence `... -> H_k(L) -> H_k(K) -> H_k(K,L) -> H_{k-1}(L) -> ...`
//! for `k` in `0..=(max_dimension + 1)`, treating a dimension beyond either
//! complex's own `max_dimension` as the zero group (which [`super::induced`]'s
//! basis machinery already produces correctly from an empty boundary matrix,
//! no special-casing needed). **The dimension each identity checks against is
//! the CERTIFICATE's own claimed Betti number** at that node (`betti`,
//! `k_cert.betti`, or `l_cert.betti`), not a value this guard silently
//! recomputes on the side -- so a certificate whose recorded relative Betti
//! number disagrees with the actual rank of the freshly-built `Q` maps is
//! refused here specifically, which is what
//! `verify_refuses_a_relative_betti_number_the_exactness_identity_rejects`
//! (below) exercises directly against `les_exactness_holds`, isolated from
//! every other guard.
//!
//! # What is certified
//!
//! [`RelativeHomologyCertificate::verify`] re-derives every claim:
//!
//! - `L` is still a subcomplex of `K` ([`is_subcomplex`]);
//! - every recorded relative simplex count matches one recomputed from `K`
//!   and `L` directly;
//! - every recorded relative boundary matrix matches one freshly rebuilt
//!   (the same submatrix-of-`K` construction);
//! - `d_{k-1}^{rel} . d_k^{rel} = 0` for every consecutive pair, on the
//!   freshly rebuilt matrices (reusing `super::compositions_are_zero`
//!   verbatim -- it is already generic over any `BTreeMap<usize, Matrix>` of
//!   boundary-shaped matrices, not specific to the absolute case);
//! - every recorded relative Smith triple is a genuine factorization (`U .
//!   d_k^{rel} . V = D`, `U`/`V` unimodular, `D` in Smith form -- the same
//!   guard `super::smith_factorizations_hold` runs for the absolute case,
//!   reused here on the relative Smith map);
//! - every recorded relative Betti number and torsion coefficient list is
//!   recomputed from the Smith diagonals alone and compared;
//! - the recorded relative Euler characteristic equals `|K \ L|`'s own
//!   alternating simplex count;
//! - the two WRAPPED absolute certificates (`K`'s own homology, `L`'s own
//!   homology) verify via [`super::HomologyCertificate::verify`] wholesale;
//! - the long exact sequence's rank identity holds at every node
//!   (`les_exactness_holds`), checked against the certificate's own
//!   recorded Betti numbers at every one of the three complexes.
//!
//! # Fixtures and what the LES catches that a lone Betti number cannot
//!
//! `H_2(D^2, S^1) = Z`, `H_1(D^2, S^1) = 0` (the disc relative to its
//! boundary circle): this is the standard computation that identifies
//! relative homology of a cone pair with the *reduced* homology of the
//! one-point suspension, and it is the smallest fixture that actually needs
//! a non-trivial connecting map (`delta_2` is an isomorphism `H_2(D,S^1) ->
//! H_1(S^1)`, since `D` itself is contractible so `i_*` and `j_*` alone carry
//! no information at `k = 1, 2`). `(K, empty L)` recovers the absolute
//! homology of `K` exactly (`C_k(K, empty) = C_k(K)` since no simplex is
//! removed, so every relative Betti number, torsion coefficient and the
//! Euler characteristic match `K`'s own absolute certificate verbatim -- this
//! is checked directly, not merely asserted). A non-subcomplex `L` (some face
//! of `L` absent from `K`) is refused. A forged relative Betti number is
//! refused by the exactness guard specifically (see above).
//!
//! # Cost profile
//!
//! Same `Q` linear algebra as [`super::induced`] (`null_space`, `rref`),
//! tripled (once each for `K`, `L`, and the relative pair) plus the
//! connecting map's own per-basis-vector lift/restrict/solve, so this module
//! costs a small constant factor more than [`super::induced`] at the same
//! complex size; see that module's and the parent module's doc comments for
//! the underlying costs. No fixture here approaches the parent module's own
//! unimodularity-ceiling scale.

use std::collections::BTreeMap;

use crate::normalforms::{certify_product_equals, smith_normal_form};
use crate::{CasExpr, Matrix, ZeroTest, equal};

use super::induced::{
    choose_homology_basis, columns_to_matrix, induced_map_from_chain_map, solve_via_rref,
};
use super::{
    HomologyCertificate, SimplicialComplex, SmithData, boundary_matrix, compositions_are_zero,
    diagonal_rank, homology, smith_factorizations_hold, torsion_factors,
};

/// Whether every face of `l`, at every dimension, is also a face of `k` --
/// the whole content of "`l` is a subcomplex of `k`" (`SimplicialComplex` is
/// always closed under faces by construction, so nothing else needs
/// checking).
#[must_use]
pub fn is_subcomplex(l: &SimplicialComplex, k: &SimplicialComplex) -> bool {
    for dim in 0..=l.max_dimension() {
        for face in l.simplices(dim) {
            if !k.contains_face(&face) {
                return false;
            }
        }
    }
    true
}

/// The `dim`-simplices of `k` that are NOT simplices of `l`, in `k`'s own
/// canonical order -- the basis of `C_dim(K, L)`.
#[must_use]
pub fn relative_simplices(
    k: &SimplicialComplex,
    l: &SimplicialComplex,
    dim: usize,
) -> Vec<Vec<usize>> {
    k.simplices(dim)
        .into_iter()
        .filter(|face| !l.contains_face(face))
        .collect()
}

/// The relative boundary matrix `d_dim^{rel} : C_dim(K,L) -> C_{dim-1}(K,L)`:
/// the submatrix of `boundary_matrix(k, dim)` restricted to the rows and
/// columns indexed by `k`'s simplices that are not `l`'s. Returns `None` on a
/// shape overflow (as [`boundary_matrix`] does).
#[must_use]
pub fn relative_boundary_matrix(
    k: &SimplicialComplex,
    l: &SimplicialComplex,
    dim: usize,
) -> Option<Matrix> {
    let full = boundary_matrix(k, dim)?;
    let row_simplices = if dim == 0 {
        Vec::new()
    } else {
        k.simplices(dim - 1)
    };
    let col_simplices = k.simplices(dim);
    let keep_rows: Vec<usize> = row_simplices
        .iter()
        .enumerate()
        .filter(|(_, face)| !l.contains_face(face))
        .map(|(i, _)| i)
        .collect();
    let keep_cols: Vec<usize> = col_simplices
        .iter()
        .enumerate()
        .filter(|(_, face)| !l.contains_face(face))
        .map(|(i, _)| i)
        .collect();
    let rows = keep_rows.len();
    let cols = keep_cols.len();
    let mut data = Vec::with_capacity(rows.checked_mul(cols)?);
    for &r in &keep_rows {
        for &c in &keep_cols {
            data.push(full.get(r, c)?.clone());
        }
    }
    Matrix::new(rows, cols, data)
}

/// `(boundary_basis, homology_basis)` of `H_dim(K, L; Q)`, via
/// [`choose_homology_basis`] on the relative boundary matrices at `dim` and
/// `dim + 1`.
fn relative_q_basis(
    k: &SimplicialComplex,
    l: &SimplicialComplex,
    dim: usize,
) -> Option<(Vec<Matrix>, Vec<Matrix>)> {
    let d_here = relative_boundary_matrix(k, l, dim)?;
    let d_next = relative_boundary_matrix(k, l, dim + 1)?;
    choose_homology_basis(&d_here, &d_next)
}

/// `(boundary_basis, homology_basis)` of `H_dim(complex; Q)`.
fn absolute_q_basis(complex: &SimplicialComplex, dim: usize) -> Option<(Vec<Matrix>, Vec<Matrix>)> {
    let d_here = boundary_matrix(complex, dim)?;
    let d_next = boundary_matrix(complex, dim + 1)?;
    choose_homology_basis(&d_here, &d_next)
}

/// The chain-level inclusion `C_dim(L) -> C_dim(K)`: rows are `k`'s
/// `dim`-simplices, columns are `l`'s, entry `1` where the same simplex
/// occurs in both (which it must, at the column's position, since `l` is a
/// subcomplex of `k`), `0` elsewhere. This is literally the identity map on
/// shared basis vectors, so it commutes with the boundary map trivially (both
/// complexes assign the same face-removal boundary formula to the same
/// simplex).
fn inclusion_chain_map(k: &SimplicialComplex, l: &SimplicialComplex, dim: usize) -> Option<Matrix> {
    let k_simplices = k.simplices(dim);
    let l_simplices = l.simplices(dim);
    let row_index: BTreeMap<Vec<usize>, usize> = k_simplices
        .iter()
        .cloned()
        .enumerate()
        .map(|(i, face)| (face, i))
        .collect();
    let rows = k_simplices.len();
    let cols = l_simplices.len();
    let mut data = vec![CasExpr::zero(); rows.checked_mul(cols)?];
    for (col_idx, face) in l_simplices.iter().enumerate() {
        let row_idx = *row_index.get(face)?;
        data[row_idx * cols + col_idx] = CasExpr::one();
    }
    Matrix::new(rows, cols, data)
}

/// The chain-level quotient projection `C_dim(K) -> C_dim(K,L)`: rows are the
/// relative simplices (`K \ L`), columns are `K`'s full `dim`-simplices,
/// entry `1` where a `K`-simplex is also a relative one (at the matching
/// row), `0` for a column that is one of `L`'s simplices (killed by the
/// quotient) or does not match the row. Commutes with the boundary because
/// [`relative_boundary_matrix`] is *defined* as this projection's induced map
/// on the boundary.
fn quotient_chain_map(k: &SimplicialComplex, l: &SimplicialComplex, dim: usize) -> Option<Matrix> {
    let k_simplices = k.simplices(dim);
    let relative = relative_simplices(k, l, dim);
    let row_index: BTreeMap<Vec<usize>, usize> = relative
        .iter()
        .cloned()
        .enumerate()
        .map(|(i, face)| (face, i))
        .collect();
    let rows = relative.len();
    let cols = k_simplices.len();
    let mut data = vec![CasExpr::zero(); rows.checked_mul(cols)?];
    for (col_idx, face) in k_simplices.iter().enumerate() {
        if let Some(&row_idx) = row_index.get(face) {
            data[row_idx * cols + col_idx] = CasExpr::one();
        }
    }
    Matrix::new(rows, cols, data)
}

/// `i_*(dim) : H_dim(L; Q) -> H_dim(K; Q)`, the induced map of
/// `inclusion_chain_map`, reusing [`induced_map_from_chain_map`] verbatim.
fn inclusion_induced(k: &SimplicialComplex, l: &SimplicialComplex, dim: usize) -> Option<Matrix> {
    let chain_map = inclusion_chain_map(k, l, dim)?;
    let (_, h_l) = absolute_q_basis(l, dim)?;
    let (b_k, h_k) = absolute_q_basis(k, dim)?;
    let rows_k = k.count(dim);
    induced_map_from_chain_map(&chain_map, &h_l, &b_k, &h_k, rows_k)
}

/// `j_*(dim) : H_dim(K; Q) -> H_dim(K,L; Q)`, the induced map of
/// `quotient_chain_map`, reusing [`induced_map_from_chain_map`] verbatim.
fn quotient_induced(k: &SimplicialComplex, l: &SimplicialComplex, dim: usize) -> Option<Matrix> {
    let chain_map = quotient_chain_map(k, l, dim)?;
    let (_, h_k) = absolute_q_basis(k, dim)?;
    let (b_rel, h_rel) = relative_q_basis(k, l, dim)?;
    let rows_rel = relative_simplices(k, l, dim).len();
    induced_map_from_chain_map(&chain_map, &h_k, &b_rel, &h_rel, rows_rel)
}

/// `delta(dim) : H_dim(K,L; Q) -> H_{dim-1}(L; Q)`, the connecting
/// homomorphism: lift each relative homology basis cycle to a `K`-chain
/// (zero on `L`'s simplices), take `K`'s own boundary, check the result is
/// supported entirely on `L`'s simplices (the defining property of a relative
/// cycle -- returns `None`, a genuine decline, if this ever fails), read the
/// `L`-supported part as an `L`-chain, and express its class in `H_{dim-1}(L;
/// Q)` via [`super::induced`]'s own `solve_via_rref` machinery (through
/// [`induced_map_from_chain_map`], fed the identity map on `L`'s own chain
/// group at `dim - 1` since no further chain map is needed once the lift is
/// already an `L`-chain).
///
/// `dim == 0` returns a genuine `0 x h_rel` matrix (the target `H_{-1}(L)` is
/// the zero group), matching the LES's own truncation at the bottom.
fn connecting_map(k: &SimplicialComplex, l: &SimplicialComplex, dim: usize) -> Option<Matrix> {
    let (_, h_rel) = relative_q_basis(k, l, dim)?;
    if dim == 0 {
        return Matrix::new(0, h_rel.len(), Vec::new());
    }
    let lower = dim - 1;
    let (b_l, h_l) = absolute_q_basis(l, lower)?;
    let rows_l = l.count(lower);
    let combined_l: Vec<Matrix> = b_l.iter().cloned().chain(h_l.iter().cloned()).collect();
    let q_l = columns_to_matrix(&combined_l, rows_l)?;

    let k_simplices_dim = k.simplices(dim);
    let k_row_index_lower: BTreeMap<Vec<usize>, usize> = k
        .simplices(lower)
        .iter()
        .cloned()
        .enumerate()
        .map(|(i, face)| (face, i))
        .collect();
    let relative_dim = relative_simplices(k, l, dim);
    let d_k_here = boundary_matrix(k, dim)?;
    let l_simplices_lower = l.simplices(lower);

    let mut data = vec![CasExpr::zero(); h_l.len().checked_mul(h_rel.len())?];
    for (i, z_rel) in h_rel.iter().enumerate() {
        // Lift z_rel (an n_relative(dim) x 1 vector) into K's full n_dim(K)
        // chain space: zero on L's simplices, z_rel's value on K \ L's.
        let mut lifted_data = vec![CasExpr::zero(); k_simplices_dim.len()];
        for (row, face) in relative_dim.iter().enumerate() {
            let k_col = k_simplices_dim.iter().position(|f| f == face)?;
            lifted_data[k_col] = z_rel.get(row, 0)?.clone();
        }
        let lifted = Matrix::new(k_simplices_dim.len(), 1, lifted_data)?;
        let boundary_of_lift = d_k_here.mul(&lifted)?;

        // Every entry at a row that is NOT one of L's simplices must be
        // certifiably zero: this is the relative-cycle condition itself.
        let mut l_chain_data = Vec::with_capacity(l_simplices_lower.len());
        for face in &l_simplices_lower {
            let &k_row = k_row_index_lower.get(face)?;
            l_chain_data.push(boundary_of_lift.get(k_row, 0)?.clone());
        }
        for (k_row, face) in k.simplices(lower).iter().enumerate() {
            if !l.contains_face(face) {
                let entry = boundary_of_lift.get(k_row, 0)?;
                if !matches!(
                    equal(entry, &CasExpr::zero()),
                    ZeroTest::Certified { equal: true, .. }
                ) {
                    return None; // not actually a relative cycle
                }
            }
        }
        let l_chain = Matrix::new(l_simplices_lower.len(), 1, l_chain_data)?;
        let coefficients = solve_via_rref(&q_l, &l_chain)?;
        for j in 0..h_l.len() {
            data[j * h_rel.len() + i] = CasExpr::Const(coefficients[b_l.len() + j]);
        }
    }
    Matrix::new(h_l.len(), h_rel.len(), data)
}

/// The rank of `matrix` over `Q` (reusing [`super::coefficients::rank_over_q`]),
/// or `0` for a `0`-column matrix (the trivial map from the zero space).
fn q_rank(matrix: &Matrix) -> Option<usize> {
    if matrix.cols() == 0 {
        return Some(0);
    }
    super::coefficients::rank_over_q(matrix)
}

/// Guard: the long exact sequence's rank identity holds at every node, for
/// `k` in `0..=(max_dim + 1)`, checked against the CLAIMED Betti numbers
/// (`relative_betti`, `k_betti`, `l_betti`) rather than a value silently
/// recomputed on the side -- see the module doc for why this is what makes a
/// forged relative Betti number specifically an exactness-guard finding.
#[allow(clippy::similar_names)] // dim_k/dim_l name the K- and L-sides of the pair, not accidental near-duplicates
fn les_exactness_holds(
    k_complex: &SimplicialComplex,
    l_complex: &SimplicialComplex,
    max_dim: usize,
    relative_betti: &BTreeMap<usize, usize>,
    k_betti: &BTreeMap<usize, usize>,
    l_betti: &BTreeMap<usize, usize>,
) -> Result<(), String> {
    for k in 0..=(max_dim + 1) {
        let i_star = inclusion_induced(k_complex, l_complex, k)
            .ok_or_else(|| format!("could not build i_* at dimension {k}"))?;
        let j_star = quotient_induced(k_complex, l_complex, k)
            .ok_or_else(|| format!("could not build j_* at dimension {k}"))?;
        let delta_k = connecting_map(k_complex, l_complex, k)
            .ok_or_else(|| format!("could not build delta at dimension {k}"))?;
        let delta_next = connecting_map(k_complex, l_complex, k + 1)
            .ok_or_else(|| format!("could not build delta at dimension {}", k + 1))?;

        let rank_i = q_rank(&i_star).ok_or_else(|| format!("i_* rank declined at {k}"))?;
        let rank_j = q_rank(&j_star).ok_or_else(|| format!("j_* rank declined at {k}"))?;
        let rank_delta_k = q_rank(&delta_k).ok_or_else(|| format!("delta rank declined at {k}"))?;
        let rank_delta_next =
            q_rank(&delta_next).ok_or_else(|| format!("delta rank declined at {}", k + 1))?;

        let dim_k = *k_betti.get(&k).unwrap_or(&0);
        let dim_l = *l_betti.get(&k).unwrap_or(&0);
        let dim_relative = *relative_betti.get(&k).unwrap_or(&0);

        if rank_i + rank_j != dim_k {
            return Err(format!(
                "LES exactness fails at H_{k}(K): rank(i_*) + rank(j_*) = {rank_i} + {rank_j} != dim H_{k}(K) = {dim_k}"
            ));
        }
        if rank_j + rank_delta_k != dim_relative {
            return Err(format!(
                "LES exactness fails at H_{k}(K,L): rank(j_*) + rank(delta) = {rank_j} + {rank_delta_k} != dim H_{k}(K,L) = {dim_relative}"
            ));
        }
        if rank_delta_next + rank_i != dim_l {
            return Err(format!(
                "LES exactness fails at H_{k}(L): rank(delta) + rank(i_*) = {rank_delta_next} + {rank_i} != dim H_{k}(L) = {dim_l}"
            ));
        }
    }
    Ok(())
}

/// A checkable certificate of the relative simplicial homology of a pair
/// `(K, L)`. See the module documentation for what
/// [`verify`](Self::verify) re-derives.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelativeHomologyCertificate {
    /// `k.max_dimension()` at the time this certificate was built.
    pub max_dimension: usize,
    /// `|relative_simplices(k, l, dim)|` for `dim` in `0..=max_dimension`.
    pub relative_counts: BTreeMap<usize, usize>,
    /// The recorded Smith factorization of `d_dim^{rel}` for `dim` in
    /// `0..=(max_dimension + 1)`.
    pub smith: BTreeMap<usize, SmithData>,
    /// `b_dim(K, L)` for `dim` in `0..=max_dimension`.
    pub betti: BTreeMap<usize, usize>,
    /// The torsion coefficients of `H_dim(K, L)`, for `dim` in
    /// `0..=max_dimension`.
    pub torsion: BTreeMap<usize, Vec<i128>>,
    /// The alternating sum of `relative_counts`.
    pub euler_characteristic: i128,
    /// `K`'s own absolute homology certificate, reused wholesale.
    pub k_cert: HomologyCertificate,
    /// `L`'s own absolute homology certificate, reused wholesale.
    pub l_cert: HomologyCertificate,
}

/// The result of a successful [`RelativeHomologyCertificate::verify`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelativeHomologyReport {
    /// `b_dim(K, L)`, recomputed.
    pub betti: BTreeMap<usize, usize>,
    /// The torsion coefficients of `H_dim(K, L)`, recomputed.
    pub torsion: BTreeMap<usize, Vec<i128>>,
}

/// Rebuild `d_dim^{rel}` for every `dim` in `0..=(max_dimension + 1)`
/// directly from `k` and `l`.
fn rebuild_relative_boundaries(
    k: &SimplicialComplex,
    l: &SimplicialComplex,
    max_dimension: usize,
) -> Option<BTreeMap<usize, Matrix>> {
    let mut rebuilt = BTreeMap::new();
    for dim in 0..=(max_dimension + 1) {
        rebuilt.insert(dim, relative_boundary_matrix(k, l, dim)?);
    }
    Some(rebuilt)
}

/// Compute the relative simplicial homology of the pair `(K, L)`.
///
/// Returns `None` if `l` is not a subcomplex of `k` ([`is_subcomplex`]), or
/// under the same conditions [`homology`] and [`smith_normal_form`] do.
#[must_use]
#[allow(clippy::many_single_char_names)] // k, l name the pair; u, d, v are the standard Smith triple
pub fn relative_homology(
    k: &SimplicialComplex,
    l: &SimplicialComplex,
) -> Option<RelativeHomologyCertificate> {
    if !is_subcomplex(l, k) {
        return None;
    }
    let max_dim = k.max_dimension();

    let mut relative_counts = BTreeMap::new();
    for dim in 0..=max_dim {
        relative_counts.insert(dim, relative_simplices(k, l, dim).len());
    }

    let mut smith = BTreeMap::new();
    for dim in 0..=(max_dim + 1) {
        let boundary = relative_boundary_matrix(k, l, dim)?;
        let (u, d, v) = smith_normal_form(&boundary)?;
        smith.insert(dim, SmithData { boundary, u, d, v });
    }

    let rank_at = |dim: usize| -> Option<usize> {
        smith
            .get(&dim)
            .map_or(Some(0), |triple| diagonal_rank(&triple.d))
    };

    let mut betti = BTreeMap::new();
    for dim in 0..=max_dim {
        let n = *relative_counts.get(&dim)? as i128;
        let r_here = rank_at(dim)? as i128;
        let r_next = rank_at(dim + 1)? as i128;
        let b = n - r_here - r_next;
        betti.insert(dim, usize::try_from(b).ok()?);
    }

    let mut torsion = BTreeMap::new();
    for dim in 0..=max_dim {
        let coefficients = match smith.get(&(dim + 1)) {
            Some(triple) => torsion_factors(&triple.d)?,
            None => Vec::new(),
        };
        torsion.insert(dim, coefficients);
    }

    let euler_characteristic: i128 = relative_counts
        .iter()
        .map(|(&dim, &count)| {
            let count = count as i128;
            if dim % 2 == 0 { count } else { -count }
        })
        .sum();

    let k_cert = homology(k)?;
    let l_cert = homology(l)?;

    Some(RelativeHomologyCertificate {
        max_dimension: max_dim,
        relative_counts,
        smith,
        betti,
        torsion,
        euler_characteristic,
        k_cert,
        l_cert,
    })
}

/// Guard: every recorded `relative_counts` value matches one recomputed
/// directly from `k` and `l`.
fn relative_counts_match(
    certificate: &RelativeHomologyCertificate,
    k: &SimplicialComplex,
    l: &SimplicialComplex,
) -> Result<(), String> {
    for dim in 0..=certificate.max_dimension {
        let actual = relative_simplices(k, l, dim).len();
        let Some(&claimed) = certificate.relative_counts.get(&dim) else {
            return Err(format!(
                "certificate has no recorded relative count at dimension {dim}"
            ));
        };
        if actual != claimed {
            return Err(format!(
                "relative simplex count mismatch at dimension {dim}: actual {actual}, certificate claims {claimed}"
            ));
        }
    }
    Ok(())
}

/// Guard: the certificate's recorded relative boundary matrices match the
/// freshly rebuilt ones.
fn relative_boundaries_match(
    certificate: &RelativeHomologyCertificate,
    rebuilt: &BTreeMap<usize, Matrix>,
) -> Result<(), String> {
    for (dim, boundary) in rebuilt {
        let Some(triple) = certificate.smith.get(dim) else {
            return Err(format!(
                "certificate is missing a relative Smith triple at dimension {dim}"
            ));
        };
        if !certify_product_equals(boundary, &triple.boundary) {
            return Err(format!(
                "recorded relative boundary at dimension {dim} does not match the one rebuilt from (K, L)"
            ));
        }
    }
    Ok(())
}

/// The recomputed `(betti, torsion)` from [`relative_betti_and_torsion_match`].
type RelativeBettiAndTorsion = (BTreeMap<usize, usize>, BTreeMap<usize, Vec<i128>>);

/// Guard: recompute every relative Betti number and torsion list from the
/// recorded Smith diagonals alone and compare to the certificate's claims.
fn relative_betti_and_torsion_match(
    certificate: &RelativeHomologyCertificate,
) -> Result<RelativeBettiAndTorsion, String> {
    let diag_rank = |dim: usize| -> Result<usize, String> {
        match certificate.smith.get(&dim) {
            Some(triple) => diagonal_rank(&triple.d)
                .ok_or_else(|| format!("non-integer diagonal entry in D at dimension {dim}")),
            None => Ok(0),
        }
    };

    let mut betti = BTreeMap::new();
    for dim in 0..=certificate.max_dimension {
        let Some(&n) = certificate.relative_counts.get(&dim) else {
            return Err(format!("no relative count at dimension {dim}"));
        };
        let n = n as i128;
        let r_here = diag_rank(dim)? as i128;
        let r_next = diag_rank(dim + 1)? as i128;
        let recomputed = n - r_here - r_next;
        let Ok(recomputed) = usize::try_from(recomputed) else {
            return Err(format!(
                "recomputed a negative relative betti number at dimension {dim}"
            ));
        };
        let Some(&claimed) = certificate.betti.get(&dim) else {
            return Err(format!(
                "certificate has no recorded betti at dimension {dim}"
            ));
        };
        if recomputed != claimed {
            return Err(format!(
                "relative betti number mismatch at dimension {dim}: recomputed {recomputed}, certificate claims {claimed}"
            ));
        }
        betti.insert(dim, recomputed);
    }

    let mut torsion = BTreeMap::new();
    for dim in 0..=certificate.max_dimension {
        let recomputed = match certificate.smith.get(&(dim + 1)) {
            Some(triple) => torsion_factors(&triple.d).ok_or_else(|| {
                format!("non-integer diagonal entry in D at dimension {}", dim + 1)
            })?,
            None => Vec::new(),
        };
        let claimed = certificate.torsion.get(&dim).cloned().unwrap_or_default();
        if recomputed != claimed {
            return Err(format!(
                "relative torsion mismatch at dimension {dim}: recomputed {recomputed:?}, certificate claims {claimed:?}"
            ));
        }
        torsion.insert(dim, recomputed);
    }

    Ok((betti, torsion))
}

/// Guard: the recorded relative Euler characteristic equals the alternating
/// sum of `relative_counts`.
fn relative_euler_characteristic_matches(
    certificate: &RelativeHomologyCertificate,
) -> Result<(), String> {
    let computed: i128 = certificate
        .relative_counts
        .iter()
        .map(|(&dim, &count)| {
            let count = count as i128;
            if dim % 2 == 0 { count } else { -count }
        })
        .sum();
    if computed != certificate.euler_characteristic {
        return Err(format!(
            "recorded relative euler characteristic {} does not match the recomputed {computed}",
            certificate.euler_characteristic
        ));
    }
    Ok(())
}

impl RelativeHomologyCertificate {
    /// Re-derive every claim in this certificate from `(k, l)` alone,
    /// independently of [`relative_homology`], the producer. See the module
    /// documentation for exactly which guards this runs.
    ///
    /// # Errors
    ///
    /// Returns a distinct, descriptive `Err(String)` for whichever guard
    /// fails first.
    pub fn verify(
        &self,
        k: &SimplicialComplex,
        l: &SimplicialComplex,
    ) -> Result<RelativeHomologyReport, String> {
        if !is_subcomplex(l, k) {
            return Err("l is not a subcomplex of k".to_string());
        }
        relative_counts_match(self, k, l)?;
        let rebuilt = rebuild_relative_boundaries(k, l, self.max_dimension)
            .ok_or_else(|| "could not rebuild relative boundaries".to_string())?;
        relative_boundaries_match(self, &rebuilt)?;
        compositions_are_zero(&rebuilt, self.max_dimension)?;
        smith_factorizations_hold(&self.smith)?;
        let (betti, torsion) = relative_betti_and_torsion_match(self)?;
        relative_euler_characteristic_matches(self)?;

        let k_report = self.k_cert.verify(k)?;
        let l_report = self.l_cert.verify(l)?;

        les_exactness_holds(
            k,
            l,
            self.max_dimension,
            &self.betti,
            &k_report.betti,
            &l_report.betti,
        )?;

        Ok(RelativeHomologyReport { betti, torsion })
    }
}

#[cfg(test)]
mod tests {
    use super::{
        RelativeHomologyCertificate, connecting_map, is_subcomplex, les_exactness_holds,
        relative_homology,
    };
    use crate::homology::fixtures::sphere_boundary;
    use crate::homology::{SimplicialComplex, homology};
    use std::collections::BTreeMap;

    fn complex_of(maximal: &[&[usize]]) -> SimplicialComplex {
        let owned: Vec<Vec<usize>> = maximal.iter().map(|s| s.to_vec()).collect();
        SimplicialComplex::from_maximal_simplices(&owned).expect("valid complex")
    }

    /// The empty complex: no faces at all.
    fn empty_complex() -> SimplicialComplex {
        SimplicialComplex::from_maximal_simplices(&[]).expect("valid complex")
    }

    fn betti_vec(map: &BTreeMap<usize, usize>, max_dim: usize) -> Vec<usize> {
        (0..=max_dim).map(|k| map[&k]).collect()
    }

    // ---- evaluation tests ----

    /// `H_2(D^2, S^1) = Z`, `H_1(D^2, S^1) = 0`: the filled disc (a single
    /// triangle) relative to its boundary circle. The disc is contractible,
    /// so this is the smallest fixture whose connecting map at dimension 2
    /// is a genuine isomorphism (not merely a zero map filling out the
    /// identity trivially).
    #[test]
    fn disc_relative_to_its_boundary_circle_has_h2_z_and_h1_zero() {
        let disc = complex_of(&[&[0, 1, 2]]);
        let boundary = complex_of(&[&[0, 1], &[1, 2], &[0, 2]]);
        assert!(is_subcomplex(&boundary, &disc));
        let certificate =
            relative_homology(&disc, &boundary).expect("relative homology of (D^2, S^1)");
        assert_eq!(betti_vec(&certificate.betti, 2), vec![0, 0, 1]);
        assert_eq!(certificate.torsion[&1], Vec::<i128>::new());
        assert_eq!(certificate.torsion[&2], Vec::<i128>::new());
        certificate
            .verify(&disc, &boundary)
            .expect("certificate verifies");
    }

    /// The torus relative to one of its meridian circles (an edge cycle
    /// already present in the 7-vertex triangulation): `H_1` drops by
    /// exactly the meridian's own class, `H_2` is unaffected (the meridian is
    /// 1-dimensional, so it removes nothing from the relative 2-chains).
    #[test]
    fn torus_relative_to_a_meridian_circle() {
        let torus = crate::homology::fixtures::torus_7v();
        // A 3-edge cycle using existing edges of the 7-vertex triangulation:
        // 0-1, 1-2, 0-2 are all edges of torus_7v (0,1,3 and 0,2,3 and 0,1,5
        // etc. share these). Confirm first, then build the subcomplex.
        let meridian = complex_of(&[&[0, 1], &[1, 2], &[0, 2]]);
        assert!(is_subcomplex(&meridian, &torus));
        let certificate =
            relative_homology(&torus, &meridian).expect("relative homology of (T^2, circle)");
        certificate
            .verify(&torus, &meridian)
            .expect("certificate verifies");
        // H_2(T^2, circle) = H_2(T^2) = Z (a 1-dimensional subcomplex removes
        // nothing at dimension 2).
        assert_eq!(certificate.betti[&2], 1);
    }

    /// `(K, empty)` recovers `K`'s own absolute homology exactly: no simplex
    /// is removed, so the relative chain complex IS the absolute one.
    #[test]
    fn relative_to_the_empty_complex_recovers_absolute_homology() {
        let torus = crate::homology::fixtures::torus_7v();
        let empty = empty_complex();
        assert!(is_subcomplex(&empty, &torus));
        let relative =
            relative_homology(&torus, &empty).expect("relative homology of (T^2, empty)");
        relative
            .verify(&torus, &empty)
            .expect("certificate verifies");
        let absolute = homology(&torus).expect("absolute homology of T^2");
        assert_eq!(relative.betti, absolute.betti);
        assert_eq!(relative.torsion, absolute.torsion);
        assert_eq!(relative.euler_characteristic, absolute.euler_characteristic);
    }

    /// A non-subcomplex (some face of the claimed "subcomplex" is absent from
    /// K) is refused by name, both via `is_subcomplex` directly and via
    /// `relative_homology`'s decline.
    #[test]
    fn a_non_subcomplex_is_refused() {
        let disc = complex_of(&[&[0, 1, 2]]);
        // An edge {0, 3} where vertex 3 is not even in the disc.
        let not_a_subcomplex = complex_of(&[&[0, 3]]);
        assert!(!is_subcomplex(&not_a_subcomplex, &disc));
        assert!(relative_homology(&disc, &not_a_subcomplex).is_none());

        // POSITIVE CONTROL: a genuine subcomplex (the disc's own boundary
        // edge {0,1}) is accepted.
        let genuine_subcomplex = complex_of(&[&[0, 1]]);
        assert!(is_subcomplex(&genuine_subcomplex, &disc));
        assert!(relative_homology(&disc, &genuine_subcomplex).is_some());
    }

    /// `S^2` relative to one of its own 2-faces (a single triangle removed
    /// from the tetrahedron boundary): `H_2(S^2, pt-triangle)` is still `Z`
    /// (the sphere's own fundamental class still generates it, since the
    /// removed simplex is a face of the relative chain group's own boundary
    /// map, not of `S^2` itself -- exercised here mainly to give the LES
    /// guard a fixture with nontrivial `H_2` on both sides at once).
    #[test]
    fn sphere_boundary_relative_to_a_vertex_matches_reduced_homology_pattern() {
        let sphere = sphere_boundary(2);
        let vertex = complex_of(&[&[0]]);
        assert!(is_subcomplex(&vertex, &sphere));
        let certificate =
            relative_homology(&sphere, &vertex).expect("relative homology of (S^2, pt)");
        certificate
            .verify(&sphere, &vertex)
            .expect("certificate verifies");
        // H_*(S^2, pt) matches REDUCED homology of S^2: b_0 = 0, b_2 = 1.
        assert_eq!(certificate.betti[&0], 0);
        assert_eq!(certificate.betti[&2], 1);
    }

    // ---- forged-certificate / guard-isolation controls ----

    /// ADVERSARIAL, isolated to `les_exactness_holds` directly (bypassing
    /// every other guard `verify` runs, exactly as this crate's existing UCT
    /// guard tests do for the analogous claim): forge only the relative
    /// Betti number the exactness identity is checked against, leaving the
    /// actual `Q` maps (built fresh from the genuine `K`, `L`) untouched. The
    /// rank identity at `H_k(K, L)` then disagrees with the forged claim.
    #[test]
    fn verify_refuses_a_relative_betti_number_the_exactness_identity_rejects() {
        let disc = complex_of(&[&[0, 1, 2]]);
        let boundary_circle = complex_of(&[&[0, 1], &[1, 2], &[0, 2]]);
        let genuine =
            relative_homology(&disc, &boundary_circle).expect("relative homology of (D^2, S^1)");
        let k_cert = homology(&disc).expect("homology of D^2");
        let l_cert = homology(&boundary_circle).expect("homology of S^1");

        // POSITIVE CONTROL: the genuine betti numbers are admitted.
        assert!(
            les_exactness_holds(
                &disc,
                &boundary_circle,
                genuine.max_dimension,
                &genuine.betti,
                &k_cert.betti,
                &l_cert.betti,
            )
            .is_ok()
        );

        let mut forged_betti = genuine.betti.clone();
        forged_betti.insert(2, 0); // H_2(D^2, S^1) is Z (dimension 1), not 0
        let err = les_exactness_holds(
            &disc,
            &boundary_circle,
            genuine.max_dimension,
            &forged_betti,
            &k_cert.betti,
            &l_cert.betti,
        )
        .expect_err("a forged relative betti number must be refused by the exactness identity");
        assert!(err.contains("LES exactness"), "got: {err}");
    }

    /// ADVERSARIAL, isolated to `les_exactness_holds`'s `H_k(K)` node identity
    /// specifically: forge only the wrapped `K`-side betti number fed in,
    /// leaving `relative_betti` and `l_betti` genuine. Mutation-tested:
    /// neutralizing this one node's check (before this test existed) killed
    /// nothing, because the only existing forgery test for this function
    /// targets the `H_k(K,L)` node instead.
    #[test]
    fn verify_refuses_a_k_betti_number_the_exactness_identity_rejects() {
        let disc = complex_of(&[&[0, 1, 2]]);
        let boundary_circle = complex_of(&[&[0, 1], &[1, 2], &[0, 2]]);
        let genuine =
            relative_homology(&disc, &boundary_circle).expect("relative homology of (D^2, S^1)");
        let k_cert = homology(&disc).expect("homology of D^2");
        let l_cert = homology(&boundary_circle).expect("homology of S^1");

        // POSITIVE CONTROL: the genuine betti numbers are admitted.
        assert!(
            les_exactness_holds(
                &disc,
                &boundary_circle,
                genuine.max_dimension,
                &genuine.betti,
                &k_cert.betti,
                &l_cert.betti,
            )
            .is_ok()
        );

        let mut forged_k_betti = k_cert.betti.clone();
        forged_k_betti.insert(0, 99); // the disc has exactly one component, not 99
        let err = les_exactness_holds(
            &disc,
            &boundary_circle,
            genuine.max_dimension,
            &genuine.betti,
            &forged_k_betti,
            &l_cert.betti,
        )
        .expect_err("a forged K-side betti number must be refused at the H_k(K) node");
        assert!(err.contains("H_0(K)"), "got: {err}");
    }

    /// ADVERSARIAL, isolated to `les_exactness_holds`'s `H_k(L)` node identity
    /// specifically: forge only the wrapped `L`-side betti number fed in,
    /// leaving `relative_betti` and `k_betti` genuine. Mutation-tested:
    /// neutralizing this one node's check (before this test existed) killed
    /// nothing, for the same reason as the `H_k(K)` node above -- the module's
    /// existing forgery tests target the `H_k(K,L)` and `H_k(K)` nodes, never
    /// this one.
    #[test]
    fn verify_refuses_an_l_betti_number_the_exactness_identity_rejects() {
        let disc = complex_of(&[&[0, 1, 2]]);
        let boundary_circle = complex_of(&[&[0, 1], &[1, 2], &[0, 2]]);
        let genuine =
            relative_homology(&disc, &boundary_circle).expect("relative homology of (D^2, S^1)");
        let k_cert = homology(&disc).expect("homology of D^2");
        let l_cert = homology(&boundary_circle).expect("homology of S^1");

        // POSITIVE CONTROL: the genuine betti numbers are admitted.
        assert!(
            les_exactness_holds(
                &disc,
                &boundary_circle,
                genuine.max_dimension,
                &genuine.betti,
                &k_cert.betti,
                &l_cert.betti,
            )
            .is_ok()
        );

        let mut forged_l_betti = l_cert.betti.clone();
        forged_l_betti.insert(0, 99); // the boundary circle has exactly one component, not 99
        let err = les_exactness_holds(
            &disc,
            &boundary_circle,
            genuine.max_dimension,
            &genuine.betti,
            &k_cert.betti,
            &forged_l_betti,
        )
        .expect_err("a forged L-side betti number must be refused at the H_k(L) node");
        assert!(err.contains("H_0(L)"), "got: {err}");
    }

    /// Direct unit test of `connecting_map` at the disc/circle fixture: the
    /// connecting map at dimension 2 is rank 1 (an isomorphism `H_2(D,S^1) ->
    /// H_1(S^1)`, both one-dimensional), which is the specific claim that
    /// makes this fixture non-degenerate (a fixture where `delta` is
    /// everywhere the zero map would not exercise `connecting_map`'s lift/
    /// restrict/solve logic at all).
    #[test]
    fn connecting_map_is_an_isomorphism_for_the_disc_and_its_boundary() {
        let disc = complex_of(&[&[0, 1, 2]]);
        let boundary_circle = complex_of(&[&[0, 1], &[1, 2], &[0, 2]]);
        let delta_2 = connecting_map(&disc, &boundary_circle, 2).expect("delta_2 builds");
        assert_eq!(delta_2.rows(), 1, "H_1(S^1) is 1-dimensional");
        assert_eq!(delta_2.cols(), 1, "H_2(D^2, S^1) is 1-dimensional");
        let entry = delta_2.get(0, 0).expect("in bounds");
        let is_nonzero = !matches!(
            crate::equal(entry, &crate::CasExpr::zero()),
            crate::ZeroTest::Certified { equal: true, .. }
        );
        assert!(
            is_nonzero,
            "delta_2 must be an isomorphism, got a zero entry"
        );
    }

    /// Direct unit test of `relative_boundaries_match`-guarded verification:
    /// a certificate for one pair, checked against an unrelated pair, is
    /// refused via the relative-count or boundary mismatch.
    #[test]
    fn verify_refuses_a_certificate_checked_against_an_unrelated_pair() {
        let disc = complex_of(&[&[0, 1, 2]]);
        let boundary_circle = complex_of(&[&[0, 1], &[1, 2], &[0, 2]]);
        let genuine: RelativeHomologyCertificate =
            relative_homology(&disc, &boundary_circle).expect("relative homology of (D^2, S^1)");
        assert!(genuine.verify(&disc, &boundary_circle).is_ok());

        let other_disc = complex_of(&[&[3, 4, 5]]);
        let other_boundary = complex_of(&[&[3, 4]]);
        let err = genuine
            .verify(&other_disc, &other_boundary)
            .expect_err("a certificate for one pair must be refused against an unrelated one");
        assert!(
            err.contains("relative simplex count")
                || err.contains("relative boundary")
                || err.contains("betti"),
            "got: {err}"
        );
    }

    /// Isolates `verify`'s OWN `is_subcomplex` re-check, distinct from
    /// `relative_homology`'s producer-side refusal (`a_non_subcomplex_is_refused`,
    /// above) and from `verify_refuses_a_certificate_checked_against_an_unrelated_pair`
    /// (which passes a genuine subcomplex pair, just an unrelated one -- it
    /// never reaches this branch at all). A genuine certificate checked
    /// against the SAME `K` but a non-subcomplex `L` must be refused by name,
    /// before any other guard runs.
    #[test]
    fn verify_refuses_when_checked_against_a_non_subcomplex_l() {
        let disc = complex_of(&[&[0, 1, 2]]);
        let boundary_circle = complex_of(&[&[0, 1], &[1, 2], &[0, 2]]);
        let genuine =
            relative_homology(&disc, &boundary_circle).expect("relative homology of (D^2, S^1)");
        assert!(genuine.verify(&disc, &boundary_circle).is_ok());

        // Vertex 3 is not in the disc at all.
        let not_a_subcomplex = complex_of(&[&[1, 2, 3]]);
        let err = genuine.verify(&disc, &not_a_subcomplex).expect_err(
            "a non-subcomplex L must be refused directly by verify's own is_subcomplex check",
        );
        assert!(err.contains("subcomplex"), "got: {err}");
    }

    /// ADVERSARIAL: forge only the recorded relative Euler characteristic.
    #[test]
    fn verify_refuses_a_forged_relative_euler_characteristic() {
        let disc = complex_of(&[&[0, 1, 2]]);
        let boundary_circle = complex_of(&[&[0, 1], &[1, 2], &[0, 2]]);
        let mut forged =
            relative_homology(&disc, &boundary_circle).expect("relative homology of (D^2, S^1)");
        forged.euler_characteristic = 99;
        let err = forged
            .verify(&disc, &boundary_circle)
            .expect_err("a forged relative euler characteristic must be refused");
        assert!(err.contains("euler characteristic"), "got: {err}");
    }

    /// ADVERSARIAL: forge only a relative torsion coefficient.
    #[test]
    fn verify_refuses_a_forged_relative_torsion_coefficient() {
        let disc = complex_of(&[&[0, 1, 2]]);
        let boundary_circle = complex_of(&[&[0, 1], &[1, 2], &[0, 2]]);
        let mut forged =
            relative_homology(&disc, &boundary_circle).expect("relative homology of (D^2, S^1)");
        forged.torsion.insert(1, vec![5]); // H_1(D^2, S^1) = 0, no torsion at all
        let err = forged
            .verify(&disc, &boundary_circle)
            .expect_err("a forged relative torsion coefficient must be refused");
        assert!(err.contains("torsion"), "got: {err}");
    }

    /// ADVERSARIAL: forge only the recorded relative Betti number, leaving
    /// every Smith triple genuine. Caught by `relative_betti_and_torsion_match`
    /// (recomputed straight from the recorded Smith diagonal), BEFORE the LES
    /// exactness guard even runs -- distinct from
    /// `verify_refuses_a_relative_betti_number_the_exactness_identity_rejects`,
    /// which isolates `les_exactness_holds` directly and bypasses this guard
    /// entirely.
    #[test]
    fn verify_refuses_a_forged_relative_betti_number() {
        let disc = complex_of(&[&[0, 1, 2]]);
        let boundary_circle = complex_of(&[&[0, 1], &[1, 2], &[0, 2]]);
        let mut forged =
            relative_homology(&disc, &boundary_circle).expect("relative homology of (D^2, S^1)");
        forged.betti.insert(2, 0); // H_2(D^2, S^1) = Z, dimension 1, not 0
        let err = forged
            .verify(&disc, &boundary_circle)
            .expect_err("a forged relative betti number must be refused");
        assert!(err.contains("betti"), "got: {err}");
    }

    /// ADVERSARIAL, isolated to `relative_counts_match`: forge only the
    /// summary `relative_counts` field, leaving every Smith triple (and so
    /// every boundary matrix) exactly as recorded for the genuine pair --
    /// mirrors `super::tests::verify_refuses_a_forged_simplex_count_with_every_boundary_genuine`
    /// in the parent module.
    #[test]
    fn verify_refuses_a_forged_relative_count_with_every_boundary_genuine() {
        let disc = complex_of(&[&[0, 1, 2]]);
        let boundary_circle = complex_of(&[&[0, 1], &[1, 2], &[0, 2]]);
        let mut forged =
            relative_homology(&disc, &boundary_circle).expect("relative homology of (D^2, S^1)");
        forged.relative_counts.insert(1, 99); // K \ L has 0 edges, not 99
        let err = forged
            .verify(&disc, &boundary_circle)
            .expect_err("a forged relative count must be refused");
        assert!(
            err.contains("relative simplex count") || err.contains("relative count"),
            "got: {err}"
        );
    }

    /// ADVERSARIAL: forge only the WRAPPED `K` homology certificate (a
    /// betti number), leaving the relative Smith data, counts, torsion and
    /// Euler characteristic all genuine -- isolates the
    /// `self.k_cert.verify(k)?` reuse in `verify` (mirrors
    /// `coefficients::tests::verify_refuses_when_the_wrapped_integer_certificate_is_forged`).
    #[test]
    fn verify_refuses_when_the_wrapped_k_certificate_is_forged() {
        let disc = complex_of(&[&[0, 1, 2]]);
        let boundary_circle = complex_of(&[&[0, 1], &[1, 2], &[0, 2]]);
        let mut forged =
            relative_homology(&disc, &boundary_circle).expect("relative homology of (D^2, S^1)");
        forged.k_cert.betti.insert(0, 99); // the disc has exactly one component
        let err = forged
            .verify(&disc, &boundary_circle)
            .expect_err("a forged wrapped K certificate must be refused");
        assert!(err.contains("betti"), "got: {err}");
    }

    /// ADVERSARIAL, isolated to `relative_boundaries_match`: forge only the
    /// recorded Smith triple's `boundary` field at one dimension, leaving `U`,
    /// `D`, `V`, the counts, betti, torsion and euler characteristic all
    /// genuine. Mutation-tested: neutralizing this guard's mismatch check
    /// alone (before this test existed) killed nothing, because every other
    /// existing forged-certificate test happens to forge a field this guard
    /// does not read. `relative_boundaries_match` runs BEFORE
    /// `smith_factorizations_hold` in `verify`, so this must be refused here
    /// specifically, before the (now self-inconsistent) `U . boundary . V = D`
    /// factorization is ever checked.
    #[test]
    fn verify_refuses_a_forged_relative_boundary_matrix() {
        let torus = crate::homology::fixtures::torus_7v();
        let meridian = complex_of(&[&[0, 1], &[1, 2], &[0, 2]]);
        let mut forged =
            relative_homology(&torus, &meridian).expect("relative homology of (T^2, circle)");
        assert!(
            forged.verify(&torus, &meridian).is_ok(),
            "genuine certificate must verify"
        );

        let triple = forged
            .smith
            .get_mut(&1)
            .expect("dimension 1 smith data exists");
        assert!(
            triple.boundary.rows() > 0 && triple.boundary.cols() > 0,
            "fixture needs a non-degenerate dimension-1 relative boundary matrix"
        );
        let rows = triple.boundary.rows();
        let cols = triple.boundary.cols();
        let mut data = Vec::with_capacity(rows * cols);
        for r in 0..rows {
            for c in 0..cols {
                if r == 0 && c == 0 {
                    // Every genuine boundary entry here is -1, 0, or 1; 999
                    // cannot coincide with the real one.
                    data.push(crate::CasExpr::int(999));
                } else {
                    data.push(triple.boundary.get(r, c).expect("in bounds").clone());
                }
            }
        }
        triple.boundary = crate::Matrix::new(rows, cols, data).expect("same shape");

        let err = forged
            .verify(&torus, &meridian)
            .expect_err("a forged relative boundary matrix must be refused");
        assert!(err.contains("relative boundary"), "got: {err}");
    }

    /// The `L` counterpart of the test above.
    #[test]
    fn verify_refuses_when_the_wrapped_l_certificate_is_forged() {
        let disc = complex_of(&[&[0, 1, 2]]);
        let boundary_circle = complex_of(&[&[0, 1], &[1, 2], &[0, 2]]);
        let mut forged =
            relative_homology(&disc, &boundary_circle).expect("relative homology of (D^2, S^1)");
        forged.l_cert.betti.insert(0, 99); // the boundary circle has exactly one component
        let err = forged
            .verify(&disc, &boundary_circle)
            .expect_err("a forged wrapped L certificate must be refused");
        assert!(err.contains("betti"), "got: {err}");
    }
}
