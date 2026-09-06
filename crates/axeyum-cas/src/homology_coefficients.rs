//! Simplicial homology with coefficients in `F_2` and `Q`, beside the `Z`
//! homology in the parent module, cross-checked by the universal coefficient
//! theorem (UCT).
//!
//! # What this computes
//!
//! [`homology_with_coefficients`] runs [`super::homology`] first (the `Z`
//! answer), then computes the rank of every boundary matrix `d_k` two more
//! ways: mod 2 by a small local Gaussian elimination (`rank_mod2`, since no
//! public general-matrix rank over `F_2` exists elsewhere in this crate --
//! `gf2.rs` and `gfp.rs` are univariate polynomial arithmetic, not matrix
//! rank), and over `Q` by the existing [`Matrix::rref`] (`rank_over_q`).
//! Betti numbers at each coefficient ring follow the same rank-nullity formula
//! the parent module uses for `Z`: `b_k = n_k - rank(d_k) - rank(d_{k+1})`.
//!
//! # What is certified
//!
//! [`CoefficientHomologyCertificate::verify`] re-derives every claim:
//!
//! - the underlying `Z` homology verifies via [`super::HomologyCertificate::verify`]
//!   (boundary provenance, `d . d = 0`, the Smith factorizations, and the
//!   Euler characteristic -- reused wholesale rather than re-checked here);
//! - every recorded `rank_mod2`/`rank_over_q` value is recomputed from a
//!   freshly rebuilt boundary matrix and compared (`ranks_match`);
//! - every recorded Betti number at each ring is recomputed from those ranks
//!   and compared (`betti_match`);
//! - the **universal coefficient theorem** is checked as an independent
//!   cross-validation, not a copy of the same numbers: `b_k(F_2) = b_k(Z) +
//!   t_k + t_{k-1}`, where `t_k` is the count of *even* torsion coefficients
//!   of `H_k` (from the already-verified `Z` certificate), and `b_k(Q) =
//!   b_k(Z)` (`uct_holds`). Because `rank_mod2` is a genuinely separate
//!   implementation from the Smith-form rank the `Z` certificate uses, a bug
//!   in either one that changed a rank value would, for every fixture tested
//!   here, break this identity -- this is the guard that actually earns its
//!   keep, not the rank-recomputation guard above (which only catches a
//!   forged *certificate*, not a wrong *implementation* shared between
//!   production and verification).
//!
//! # Cost profile
//!
//! `rank_mod2` is `O(rows * cols^2)` bit-elimination; `rank_over_q` is exact
//! `Rational` Gauss-Jordan via the existing `rref`. Both are cheaper than the
//! Smith-form/cofactor-determinant path the `Z` certificate needs, so this
//! module does not change the module's overall cost profile (see the parent
//! module's doc comment).

use std::collections::BTreeMap;

use crate::normalforms::int_entry;
use crate::{CasExpr, Matrix};

use super::{
    HomologyCertificate, SimplicialComplex, boundary_matrix, homology, rebuild_boundaries,
};

/// The rank of an integer-entry matrix over `F_2`, by Gaussian elimination on
/// a plain bit grid (`0`/`1` per entry, mod 2). Returns `None` if any entry is
/// not an integer-valued constant.
fn rank_mod2(matrix: &Matrix) -> Option<usize> {
    let rows = matrix.rows();
    let cols = matrix.cols();
    let mut grid: Vec<Vec<u8>> = Vec::with_capacity(rows);
    for row in 0..rows {
        let mut bits = Vec::with_capacity(cols);
        for col in 0..cols {
            let value = int_entry(matrix, row, col)?;
            bits.push(u8::from(value.rem_euclid(2) != 0));
        }
        grid.push(bits);
    }
    let mut rank = 0usize;
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
        pivot_row += 1;
        rank += 1;
    }
    Some(rank)
}

/// The rank of a rational-constant matrix over `Q`: the number of non-zero
/// rows of its [`Matrix::rref`]. Returns `None` on a non-constant entry or
/// `i128` rational overflow (from `rref` itself).
pub(crate) fn rank_over_q(matrix: &Matrix) -> Option<usize> {
    let echelon = matrix.rref()?;
    let mut rank = 0usize;
    for row in 0..echelon.rows() {
        let mut nonzero = false;
        for col in 0..echelon.cols() {
            match echelon.get(row, col) {
                Some(CasExpr::Const(value)) => {
                    if !value.is_zero() {
                        nonzero = true;
                        break;
                    }
                }
                _ => return None,
            }
        }
        if nonzero {
            rank += 1;
        }
    }
    Some(rank)
}

/// `b_k = n_k - rank(d_k) - rank(d_{k+1})` for `k` in `0..=max_dim`, given a
/// rank function over ranks already computed for `k` in `0..=(max_dim + 1)`.
fn betti_from_ranks(
    simplex_counts: &BTreeMap<usize, usize>,
    ranks: &BTreeMap<usize, usize>,
    max_dim: usize,
) -> Option<BTreeMap<usize, usize>> {
    let mut betti = BTreeMap::new();
    for k in 0..=max_dim {
        let n_k = *simplex_counts.get(&k)? as i128;
        let r_k = *ranks.get(&k)? as i128;
        let r_k1 = *ranks.get(&(k + 1))? as i128;
        let b = n_k - r_k - r_k1;
        betti.insert(k, usize::try_from(b).ok()?);
    }
    Some(betti)
}

/// A checkable certificate of the homology of a [`SimplicialComplex`] over
/// `F_2` and `Q`, beside the `Z` homology it wraps. See the module
/// documentation for what [`verify`](Self::verify) actually re-derives.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoefficientHomologyCertificate {
    /// The highest dimension `k` for which the complex has any `k`-simplex.
    pub max_dimension: usize,
    /// `rank(d_k) mod 2` for `k` in `0..=(max_dimension + 1)`.
    pub rank_f2: BTreeMap<usize, usize>,
    /// `rank(d_k)` over `Q` for `k` in `0..=(max_dimension + 1)`.
    pub rank_q: BTreeMap<usize, usize>,
    /// `b_k(F_2)` for `k` in `0..=max_dimension`.
    pub betti_f2: BTreeMap<usize, usize>,
    /// `b_k(Q)` for `k` in `0..=max_dimension`.
    pub betti_q: BTreeMap<usize, usize>,
    /// The underlying `Z` homology certificate, reused for the UCT guard.
    pub integer: HomologyCertificate,
}

/// The result of a successful [`CoefficientHomologyCertificate::verify`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoefficientHomologyReport {
    /// `b_k(F_2)`, recomputed.
    pub betti_f2: BTreeMap<usize, usize>,
    /// `b_k(Q)`, recomputed.
    pub betti_q: BTreeMap<usize, usize>,
}

/// Compute the homology of `complex` over `F_2` and `Q`, beside its `Z`
/// homology (via [`super::homology`]).
///
/// Returns `None` under the same conditions [`super::homology`] does, or if
/// `rank_mod2`/`rank_over_q` decline on a boundary matrix (not expected for
/// the integer-entry matrices [`boundary_matrix`] builds).
#[must_use]
pub fn homology_with_coefficients(
    complex: &SimplicialComplex,
) -> Option<CoefficientHomologyCertificate> {
    let integer = homology(complex)?;
    let max_dim = integer.max_dimension;

    let mut rank_f2 = BTreeMap::new();
    let mut rank_q = BTreeMap::new();
    for k in 0..=(max_dim + 1) {
        let boundary = boundary_matrix(complex, k)?;
        rank_f2.insert(k, rank_mod2(&boundary)?);
        rank_q.insert(k, rank_over_q(&boundary)?);
    }

    let betti_f2 = betti_from_ranks(&integer.simplex_counts, &rank_f2, max_dim)?;
    let betti_q = betti_from_ranks(&integer.simplex_counts, &rank_q, max_dim)?;

    Some(CoefficientHomologyCertificate {
        max_dimension: max_dim,
        rank_f2,
        rank_q,
        betti_f2,
        betti_q,
        integer,
    })
}

/// Guard: every recorded `rank_f2`/`rank_q` value matches one recomputed from
/// a freshly rebuilt boundary matrix (independent of anything the certificate
/// under test recorded).
fn ranks_match(
    certificate: &CoefficientHomologyCertificate,
    rebuilt: &BTreeMap<usize, Matrix>,
) -> Result<(), String> {
    for (k, boundary) in rebuilt {
        let recomputed_f2 =
            rank_mod2(boundary).ok_or_else(|| format!("rank_mod2 declined at dimension {k}"))?;
        let Some(&claimed_f2) = certificate.rank_f2.get(k) else {
            return Err(format!(
                "certificate has no recorded rank_f2 at dimension {k}"
            ));
        };
        if recomputed_f2 != claimed_f2 {
            return Err(format!(
                "rank_f2 mismatch at dimension {k}: recomputed {recomputed_f2}, certificate claims {claimed_f2}"
            ));
        }

        let recomputed_q = rank_over_q(boundary)
            .ok_or_else(|| format!("rank_over_q declined at dimension {k}"))?;
        let Some(&claimed_q) = certificate.rank_q.get(k) else {
            return Err(format!(
                "certificate has no recorded rank_q at dimension {k}"
            ));
        };
        if recomputed_q != claimed_q {
            return Err(format!(
                "rank_q mismatch at dimension {k}: recomputed {recomputed_q}, certificate claims {claimed_q}"
            ));
        }
    }
    Ok(())
}

/// The recomputed `(betti_f2, betti_q)` maps from [`betti_match`].
type BettiF2AndQ = (BTreeMap<usize, usize>, BTreeMap<usize, usize>);

/// Guard: every recorded `betti_f2`/`betti_q` matches one recomputed from the
/// (already re-derived) ranks via rank-nullity.
fn betti_match(
    certificate: &CoefficientHomologyCertificate,
    simplex_counts: &BTreeMap<usize, usize>,
) -> Result<BettiF2AndQ, String> {
    let recomputed_f2 = betti_from_ranks(
        simplex_counts,
        &certificate.rank_f2,
        certificate.max_dimension,
    )
    .ok_or_else(|| "betti_f2 rank-nullity arithmetic failed".to_string())?;
    if recomputed_f2 != certificate.betti_f2 {
        return Err(format!(
            "betti_f2 mismatch: recomputed {recomputed_f2:?}, certificate claims {:?}",
            certificate.betti_f2
        ));
    }
    let recomputed_q = betti_from_ranks(
        simplex_counts,
        &certificate.rank_q,
        certificate.max_dimension,
    )
    .ok_or_else(|| "betti_q rank-nullity arithmetic failed".to_string())?;
    if recomputed_q != certificate.betti_q {
        return Err(format!(
            "betti_q mismatch: recomputed {recomputed_q:?}, certificate claims {:?}",
            certificate.betti_q
        ));
    }
    Ok((recomputed_f2, recomputed_q))
}

/// Guard: the universal coefficient theorem, checked against the
/// already-verified `Z` homology -- `b_k(F_2) = b_k(Z) + t_k + t_{k-1}` (`t_k`
/// = count of even torsion coefficients of `H_k`), and `b_k(Q) = b_k(Z)`.
fn uct_holds(
    certificate: &CoefficientHomologyCertificate,
    integer_betti: &BTreeMap<usize, usize>,
    integer_torsion: &BTreeMap<usize, Vec<i128>>,
) -> Result<(), String> {
    let even_torsion_count = |k: usize| -> i128 {
        integer_torsion.get(&k).map_or(0, |factors| {
            factors.iter().filter(|&&f| f % 2 == 0).count() as i128
        })
    };
    for k in 0..=certificate.max_dimension {
        let b_z = *integer_betti
            .get(&k)
            .ok_or_else(|| format!("no integer betti number at dimension {k}"))?
            as i128;
        let t_k = even_torsion_count(k);
        let t_k_minus_1 = if k == 0 { 0 } else { even_torsion_count(k - 1) };
        let expected_f2 = b_z + t_k + t_k_minus_1;
        let actual_f2 = *certificate
            .betti_f2
            .get(&k)
            .ok_or_else(|| format!("no betti_f2 at dimension {k}"))?
            as i128;
        if actual_f2 != expected_f2 {
            return Err(format!(
                "UCT (F_2) fails at dimension {k}: b_{k}(F_2) = {actual_f2}, but b_{k}(Z) + t_{k} + t_{{{k}-1}} = {expected_f2}"
            ));
        }
        let actual_q = *certificate
            .betti_q
            .get(&k)
            .ok_or_else(|| format!("no betti_q at dimension {k}"))? as i128;
        if actual_q != b_z {
            return Err(format!(
                "UCT (Q) fails at dimension {k}: b_{k}(Q) = {actual_q}, but b_{k}(Z) = {b_z}"
            ));
        }
    }
    Ok(())
}

impl CoefficientHomologyCertificate {
    /// Re-derive every claim in this certificate from `complex` alone. See
    /// the module documentation for exactly what each guard would miss if it
    /// were absent.
    ///
    /// # Errors
    ///
    /// Returns a distinct, descriptive `Err(String)` for whichever guard
    /// fails first: a failure of the wrapped `Z` certificate's own `verify`,
    /// a rank mismatch, a Betti-number mismatch, or a universal-coefficient
    /// inconsistency.
    pub fn verify(&self, complex: &SimplicialComplex) -> Result<CoefficientHomologyReport, String> {
        let integer_report = self.integer.verify(complex)?;
        let rebuilt = rebuild_boundaries(complex, self.max_dimension)
            .map_err(|e| format!("could not rebuild boundaries: {e}"))?;
        ranks_match(self, &rebuilt)?;
        let (betti_f2, betti_q) = betti_match(self, &self.integer.simplex_counts)?;
        uct_holds(self, &integer_report.betti, &integer_report.torsion)?;
        Ok(CoefficientHomologyReport { betti_f2, betti_q })
    }
}

#[cfg(test)]
mod tests {
    use super::{CoefficientHomologyCertificate, homology_with_coefficients, uct_holds};
    use crate::homology::fixtures::{
        circle, filled_triangle, klein_bottle_9v, rp2_6v, sphere, torus_7v,
    };

    fn betti_vec(map: &std::collections::BTreeMap<usize, usize>, max_dim: usize) -> Vec<usize> {
        (0..=max_dim).map(|k| map[&k]).collect()
    }

    #[test]
    fn rp2_has_betti_one_one_one_over_f2_and_one_zero_zero_over_q() {
        let complex = rp2_6v();
        let certificate = homology_with_coefficients(&complex).expect("coefficient homology");
        assert_eq!(betti_vec(&certificate.betti_f2, 2), vec![1, 1, 1]);
        assert_eq!(betti_vec(&certificate.betti_q, 2), vec![1, 0, 0]);
        certificate.verify(&complex).expect("certificate verifies");
    }

    #[test]
    fn klein_bottle_has_betti_one_two_one_over_f2() {
        let complex = klein_bottle_9v();
        let certificate = homology_with_coefficients(&complex).expect("coefficient homology");
        assert_eq!(betti_vec(&certificate.betti_f2, 2), vec![1, 2, 1]);
        certificate.verify(&complex).expect("certificate verifies");
    }

    #[test]
    fn torus_is_unchanged_over_z_f2_and_q() {
        let complex = torus_7v();
        let certificate = homology_with_coefficients(&complex).expect("coefficient homology");
        let integer_vec = betti_vec(&certificate.integer.betti, 2);
        assert_eq!(integer_vec, vec![1, 2, 1]);
        assert_eq!(betti_vec(&certificate.betti_f2, 2), vec![1, 2, 1]);
        assert_eq!(betti_vec(&certificate.betti_q, 2), vec![1, 2, 1]);
        certificate.verify(&complex).expect("certificate verifies");
    }

    #[test]
    fn circle_matches_across_all_three_coefficient_rings() {
        let complex = circle();
        let certificate = homology_with_coefficients(&complex).expect("coefficient homology");
        assert_eq!(betti_vec(&certificate.integer.betti, 1), vec![1, 1]);
        assert_eq!(betti_vec(&certificate.betti_f2, 1), vec![1, 1]);
        assert_eq!(betti_vec(&certificate.betti_q, 1), vec![1, 1]);
        certificate.verify(&complex).expect("certificate verifies");
    }

    /// ADVERSARIAL. Forge only `betti_f2`, leaving every rank and the
    /// wrapped `Z` certificate genuine: `betti_from_ranks` on the recorded
    /// ranks no longer matches, so `betti_match` refuses before `uct_holds`
    /// is even reached. Confirmed by mutation: disabling only the
    /// `recomputed_f2 != certificate.betti_f2` check leaves every other test
    /// in this module green.
    #[test]
    fn verify_refuses_a_forged_betti_f2_with_every_rank_genuine() {
        let complex = rp2_6v();
        let genuine = homology_with_coefficients(&complex).expect("coefficient homology");
        assert!(
            genuine.verify(&complex).is_ok(),
            "genuine certificate must verify"
        );

        let mut forged = genuine.clone();
        forged.betti_f2.insert(1, 0); // RP^2 has b_1(F_2) = 1, not 0
        let err = forged
            .verify(&complex)
            .expect_err("a forged betti_f2 must be refused");
        assert!(
            err.contains("betti_f2"),
            "reason should name betti_f2, got: {err}"
        );
    }

    /// Direct unit test of `uct_holds`, isolated from `verify` (and so from
    /// `ranks_match`/`betti_match`, which recompute ranks from the SAME
    /// `rank_mod2`/`rank_over_q` a bug would live in, and so could never
    /// distinguish a self-consistently wrong implementation from a correct
    /// one -- only the independent `Z` homology this guard cross-checks
    /// against can). Confirmed by mutation: disabling only the call to
    /// `uct_holds` in `verify` leaves every fixture test above green (they
    /// only ever pass GENUINE certificates through `verify`).
    #[test]
    fn uct_holds_refuses_an_inconsistent_torsion_count() {
        let complex = rp2_6v();
        let genuine = homology_with_coefficients(&complex).expect("coefficient homology");
        // Genuine: b_1(F_2) = 1 = b_1(Z) + t_1 + t_0 = 0 + 1 + 0 (t_1 counts
        // the one even torsion coefficient of H_1, which is Z/2).
        assert_eq!(genuine.integer.torsion[&1], vec![2]);
        assert_eq!(genuine.betti_f2[&1], 1);

        let mut wrong_torsion = genuine.integer.torsion.clone();
        wrong_torsion.insert(1, Vec::new()); // erase H_1's Z/2 torsion
        let err = uct_holds(&genuine, &genuine.integer.betti, &wrong_torsion)
            .expect_err("an inconsistent torsion count must be refused");
        assert!(err.contains("UCT"), "got: {err}");

        // POSITIVE CONTROL: the genuine torsion is admitted.
        assert!(uct_holds(&genuine, &genuine.integer.betti, &genuine.integer.torsion).is_ok());
    }

    /// Direct unit test of the certificate refusing a wrapped `Z` certificate
    /// that itself fails to verify (forged Betti number in `integer`),
    /// isolated from every guard in THIS module.
    #[test]
    fn verify_refuses_when_the_wrapped_integer_certificate_is_forged() {
        let complex = circle();
        let mut certificate = homology_with_coefficients(&complex).expect("coefficient homology");
        certificate.integer.betti.insert(0, 99);
        let err = certificate
            .verify(&complex)
            .expect_err("a forged wrapped Z certificate must be refused");
        assert!(err.contains("betti"), "got: {err}");
    }

    #[test]
    fn contractible_complexes_are_unchanged_across_all_three_rings() {
        for complex in [filled_triangle(), sphere()] {
            let certificate = homology_with_coefficients(&complex).expect("coefficient homology");
            assert_eq!(certificate.integer.betti, certificate.betti_f2);
            assert_eq!(certificate.integer.betti, certificate.betti_q);
            certificate.verify(&complex).expect("certificate verifies");
        }
    }

    /// Positive control isolating `rank_mod2`/`rank_over_q` against a hand
    /// computation, so the two guard tests above are not the only place
    /// these functions are exercised.
    #[test]
    fn a_single_self_loop_free_edge_matrix_has_rank_one_over_both_rings() {
        use super::{rank_mod2, rank_over_q};
        use crate::{CasExpr, Matrix};
        // d_1 of a single edge {0,1}: 2 rows (vertices), 1 column (the
        // edge), entries +1/-1. Rank 1 over both F_2 and Q.
        let d1 = Matrix::new(2, 1, vec![CasExpr::int(1), CasExpr::int(-1)]).expect("2x1");
        assert_eq!(rank_mod2(&d1), Some(1));
        assert_eq!(rank_over_q(&d1), Some(1));

        // The zero matrix has rank 0 over both.
        let zero = Matrix::zeros(2, 1);
        assert_eq!(rank_mod2(&zero), Some(0));
        assert_eq!(rank_over_q(&zero), Some(0));
    }

    // Silence an unused-import warning if `CoefficientHomologyCertificate` is
    // only ever named via `homology_with_coefficients`'s return type.
    #[allow(dead_code)]
    fn _type_is_named(_: Option<CoefficientHomologyCertificate>) {}
}
