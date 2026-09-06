//! Simplicial cohomology over `Z`, by Smith form of the transposed boundary
//! matrices, cross-checked against the universal coefficient theorem for
//! cohomology.
//!
//! # What this computes
//!
//! The coboundary map `delta^k : C^k -> C^{k+1}` is the transpose of the
//! boundary map `d_{k+1} : C_{k+1} -> C_k` (both bases are the same simplex
//! sets, just read as a cochain rather than a chain). [`cohomology`] builds
//! `d_k^T` for every `k` in `0..=(max_dimension + 1)` and runs
//! [`smith_normal_form`] on it **independently** of the `Z` homology
//! certificate's own Smith data for `d_k` (a fresh call, not a transpose of
//! the recorded triple) -- Smith form is essentially unique, so this is a
//! genuine second derivation of the same invariant-factor chain, not a copy.
//!
//! From these diagonals:
//!
//! - the free rank of `H^n` is `n_n - rank(d_n^T) - rank(d_{n+1}^T)`, the same
//!   rank-nullity formula the parent module uses for `H_n`, applied to the
//!   coboundary maps;
//! - the torsion of `H^n` is the invariant factors of `d_n^T` greater than
//!   `1` (i.e. of `delta^{n-1}`).
//!
//! # What is certified
//!
//! [`CohomologyCertificate::verify`] re-derives every claim:
//!
//! - the wrapped `Z` homology certificate verifies via
//!   [`super::HomologyCertificate::verify`] (reused wholesale);
//! - every recorded coboundary Smith triple is rebuilt from a freshly
//!   transposed boundary matrix and re-checked as a genuine factorization
//!   (`U . d_k^T . V = D`, `U`/`V` unimodular, `D` in Smith form -- reusing
//!   `crate::normalforms`'s own certified guards, exactly as the parent
//!   module's `smith_factorizations_hold` does);
//! - every recorded free rank / torsion list is recomputed from those
//!   diagonals and compared;
//! - the **universal coefficient theorem for cohomology** is checked against
//!   the already-verified `Z` homology: `H^n`'s free rank equals `b_n`, and
//!   `H^n`'s torsion equals `H_{n-1}`'s torsion (`uct_cohomology_holds`).
//!   Since the coboundary Smith form is computed independently (a fresh
//!   `smith_normal_form` call on a transposed matrix, not a copy of the
//!   chain-side answer), a bug specific to that second call path -- a
//!   transpose bug, or a Smith-form bug that only manifests on the
//!   transposed shape -- would break this identity even though every other
//!   guard here is a pure self-consistency check.
//!
//! # Cost profile
//!
//! Doubles the Smith-form work the parent module does (one more
//! `smith_normal_form` call per dimension, on a matrix of the same shape
//! transposed), so the same cofactor/Bareiss unimodularity cost applies; see
//! the parent module's doc comment. This module's own largest exercised
//! transpose is the Klein bottle's 27x27 `d_1^T` (an extra unimodularity
//! check beside the parent module's own on `d_1` itself); see
//! [`super::coefficients`]'s doc comment for the whole-suite release timing.

use std::collections::BTreeMap;

use crate::normalforms::{
    certifies_smith_shape, certify_product_equals, is_unimodular, smith_normal_form,
};

use super::{
    HomologyCertificate, SimplicialComplex, SmithData, boundary_matrix, diagonal_rank, homology,
    torsion_factors,
};

/// A checkable certificate of the simplicial cohomology of a
/// [`SimplicialComplex`] over `Z`, backed by an independent Smith
/// factorization of every transposed boundary matrix. See the module
/// documentation for what [`verify`](Self::verify) re-derives.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CohomologyCertificate {
    /// The highest dimension `k` for which the complex has any `k`-simplex.
    pub max_dimension: usize,
    /// The recorded Smith factorization of `d_k^T` for `k` in
    /// `0..=(max_dimension + 1)` (`SmithData::boundary` holds `d_k^T`, not
    /// `d_k`).
    pub coboundary_smith: BTreeMap<usize, SmithData>,
    /// The free rank of `H^n`, for `n` in `0..=max_dimension`.
    pub free_rank: BTreeMap<usize, usize>,
    /// The torsion coefficients of `H^n` (invariant factors of `d_n^T`
    /// greater than `1`), for `n` in `0..=max_dimension`.
    pub torsion: BTreeMap<usize, Vec<i128>>,
    /// The wrapped `Z` homology certificate, reused for the UCT guard.
    pub integer: HomologyCertificate,
}

/// The result of a successful [`CohomologyCertificate::verify`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CohomologyReport {
    /// `H^n`'s free rank, recomputed.
    pub free_rank: BTreeMap<usize, usize>,
    /// `H^n`'s torsion, recomputed.
    pub torsion: BTreeMap<usize, Vec<i128>>,
}

/// Compute the simplicial cohomology of `complex` over `Z`.
///
/// Returns `None` if [`super::homology`] declines, or if `smith_normal_form`
/// declines on any transposed boundary matrix (not expected for the sizes
/// this module targets).
#[must_use]
pub fn cohomology(complex: &SimplicialComplex) -> Option<CohomologyCertificate> {
    let integer = homology(complex)?;
    let max_dim = integer.max_dimension;

    let mut coboundary_smith = BTreeMap::new();
    for k in 0..=(max_dim + 1) {
        let d_k = boundary_matrix(complex, k)?;
        let transposed = d_k.transpose();
        let (u, d, v) = smith_normal_form(&transposed)?;
        coboundary_smith.insert(
            k,
            SmithData {
                boundary: transposed,
                u,
                d,
                v,
            },
        );
    }

    let rank_at = |k: usize| -> Option<usize> {
        coboundary_smith
            .get(&k)
            .map_or(Some(0), |data| diagonal_rank(&data.d))
    };

    let mut free_rank = BTreeMap::new();
    for n in 0..=max_dim {
        let n_n = *integer.simplex_counts.get(&n)? as i128;
        let r_n = rank_at(n)? as i128;
        let r_n1 = rank_at(n + 1)? as i128;
        let b = n_n - r_n - r_n1;
        free_rank.insert(n, usize::try_from(b).ok()?);
    }

    let mut torsion = BTreeMap::new();
    for n in 0..=max_dim {
        let coefficients = match coboundary_smith.get(&n) {
            Some(data) => torsion_factors(&data.d)?,
            None => Vec::new(),
        };
        torsion.insert(n, coefficients);
    }

    Some(CohomologyCertificate {
        max_dimension: max_dim,
        coboundary_smith,
        free_rank,
        torsion,
        integer,
    })
}

/// Guard: every recorded coboundary Smith triple is a genuine factorization
/// of the FRESHLY-TRANSPOSED boundary matrix -- boundary provenance,
/// `U . d_k^T . V = D`, `U`/`V` unimodular, and `D` in Smith normal form.
fn coboundary_smith_holds(
    certificate: &CohomologyCertificate,
    complex: &SimplicialComplex,
) -> Result<(), String> {
    for k in 0..=(certificate.max_dimension + 1) {
        let d_k = boundary_matrix(complex, k)
            .ok_or_else(|| format!("could not rebuild d_{k} to transpose"))?;
        let transposed = d_k.transpose();
        let Some(data) = certificate.coboundary_smith.get(&k) else {
            return Err(format!(
                "certificate has no coboundary Smith data at dimension {k}"
            ));
        };
        if !certify_product_equals(&transposed, &data.boundary) {
            return Err(format!(
                "recorded coboundary at dimension {k} does not match d_{k}^T rebuilt from the complex"
            ));
        }
        let product = data
            .u
            .mul(&data.boundary)
            .and_then(|partial| partial.mul(&data.v))
            .ok_or_else(|| format!("U * d_{k}^T * V failed to multiply"))?;
        if !certify_product_equals(&product, &data.d) {
            return Err(format!("U * d_{k}^T * V != D at dimension {k}"));
        }
        if !is_unimodular(&data.u) {
            return Err(format!(
                "U at dimension {k} is not unimodular (det != +/-1)"
            ));
        }
        if !is_unimodular(&data.v) {
            return Err(format!(
                "V at dimension {k} is not unimodular (det != +/-1)"
            ));
        }
        if !certifies_smith_shape(&data.d) {
            return Err(format!(
                "D at dimension {k} is not in Smith normal form (not diagonal, or the divisibility chain fails)"
            ));
        }
    }
    Ok(())
}

/// The recomputed free rank and torsion from [`free_rank_and_torsion_match`].
type FreeRankAndTorsion = (BTreeMap<usize, usize>, BTreeMap<usize, Vec<i128>>);

/// Guard: recompute every free rank and torsion list from the recorded
/// coboundary diagonals alone and compare to what the certificate claims.
fn free_rank_and_torsion_match(
    certificate: &CohomologyCertificate,
    simplex_counts: &BTreeMap<usize, usize>,
) -> Result<FreeRankAndTorsion, String> {
    let rank_at = |k: usize| -> Result<usize, String> {
        match certificate.coboundary_smith.get(&k) {
            Some(data) => diagonal_rank(&data.d)
                .ok_or_else(|| format!("non-integer diagonal entry in D at dimension {k}")),
            None => Ok(0),
        }
    };

    let mut free_rank = BTreeMap::new();
    for n in 0..=certificate.max_dimension {
        let n_n = *simplex_counts
            .get(&n)
            .ok_or_else(|| format!("no simplex count at dimension {n}"))? as i128;
        let r_n = rank_at(n)? as i128;
        let r_n1 = rank_at(n + 1)? as i128;
        let recomputed = n_n - r_n - r_n1;
        let Ok(recomputed) = usize::try_from(recomputed) else {
            return Err(format!("recomputed a negative free rank at dimension {n}"));
        };
        let Some(&claimed) = certificate.free_rank.get(&n) else {
            return Err(format!(
                "certificate has no recorded free rank at dimension {n}"
            ));
        };
        if recomputed != claimed {
            return Err(format!(
                "free rank mismatch at dimension {n}: recomputed {recomputed}, certificate claims {claimed}"
            ));
        }
        free_rank.insert(n, recomputed);
    }

    let mut torsion = BTreeMap::new();
    for n in 0..=certificate.max_dimension {
        let recomputed = match certificate.coboundary_smith.get(&n) {
            Some(data) => torsion_factors(&data.d)
                .ok_or_else(|| format!("non-integer diagonal entry in D at dimension {n}"))?,
            None => Vec::new(),
        };
        let claimed = certificate.torsion.get(&n).cloned().unwrap_or_default();
        if recomputed != claimed {
            return Err(format!(
                "torsion mismatch at dimension {n}: recomputed {recomputed:?}, certificate claims {claimed:?}"
            ));
        }
        torsion.insert(n, recomputed);
    }

    Ok((free_rank, torsion))
}

/// Guard: the universal coefficient theorem for cohomology, checked against
/// the already-verified `Z` homology -- `H^n`'s free rank equals `b_n`, and
/// `H^n`'s torsion equals `H_{n-1}`'s torsion.
fn uct_cohomology_holds(
    certificate: &CohomologyCertificate,
    integer_betti: &BTreeMap<usize, usize>,
    integer_torsion: &BTreeMap<usize, Vec<i128>>,
) -> Result<(), String> {
    for n in 0..=certificate.max_dimension {
        let b_n = *integer_betti
            .get(&n)
            .ok_or_else(|| format!("no integer betti number at dimension {n}"))?;
        let free_rank = *certificate
            .free_rank
            .get(&n)
            .ok_or_else(|| format!("no free rank at dimension {n}"))?;
        if free_rank != b_n {
            return Err(format!(
                "UCT (cohomology) fails at dimension {n}: free rank of H^{n} is {free_rank}, but b_{n} = {b_n}"
            ));
        }
        let expected_torsion = if n == 0 {
            Vec::new()
        } else {
            integer_torsion.get(&(n - 1)).cloned().unwrap_or_default()
        };
        let actual_torsion = certificate.torsion.get(&n).cloned().unwrap_or_default();
        if actual_torsion != expected_torsion {
            return Err(format!(
                "UCT (cohomology) fails at dimension {n}: torsion of H^{n} is {actual_torsion:?}, but torsion of H_{{{n}-1}} is {expected_torsion:?}"
            ));
        }
    }
    Ok(())
}

impl CohomologyCertificate {
    /// Re-derive every claim in this certificate from `complex` alone. See
    /// the module documentation for exactly what each guard would miss if it
    /// were absent.
    ///
    /// # Errors
    ///
    /// Returns a distinct, descriptive `Err(String)` for whichever guard
    /// fails first: a failure of the wrapped `Z` certificate's own `verify`,
    /// a broken coboundary Smith factorization, a free-rank or torsion
    /// mismatch, or a universal-coefficient inconsistency.
    pub fn verify(&self, complex: &SimplicialComplex) -> Result<CohomologyReport, String> {
        let integer_report = self.integer.verify(complex)?;
        coboundary_smith_holds(self, complex)?;
        let (free_rank, torsion) = free_rank_and_torsion_match(self, &self.integer.simplex_counts)?;
        uct_cohomology_holds(self, &integer_report.betti, &integer_report.torsion)?;
        Ok(CohomologyReport { free_rank, torsion })
    }
}

#[cfg(test)]
mod tests {
    use super::{cohomology, uct_cohomology_holds};
    use crate::homology::fixtures::{circle, klein_bottle_9v, rp2_6v, torus_7v};

    #[test]
    fn rp2_cohomology_is_z_zero_z_mod_2() {
        let complex = rp2_6v();
        let certificate = cohomology(&complex).expect("cohomology of RP^2");
        // H^0 = Z
        assert_eq!(certificate.free_rank[&0], 1);
        assert_eq!(certificate.torsion[&0], Vec::<i128>::new());
        // H^1 = 0
        assert_eq!(certificate.free_rank[&1], 0);
        assert_eq!(certificate.torsion[&1], Vec::<i128>::new());
        // H^2 = Z/2
        assert_eq!(certificate.free_rank[&2], 0);
        assert_eq!(certificate.torsion[&2], vec![2]);
        certificate.verify(&complex).expect("certificate verifies");
    }

    #[test]
    fn klein_bottle_h2_is_z_mod_2() {
        let complex = klein_bottle_9v();
        let certificate = cohomology(&complex).expect("cohomology of the Klein bottle");
        assert_eq!(certificate.free_rank[&2], 0);
        assert_eq!(certificate.torsion[&2], vec![2]);
        certificate.verify(&complex).expect("certificate verifies");
    }

    #[test]
    fn torus_cohomology_matches_homology_no_torsion() {
        let complex = torus_7v();
        let certificate = cohomology(&complex).expect("cohomology of the torus");
        for k in 0..=2 {
            assert_eq!(certificate.free_rank[&k], certificate.integer.betti[&k]);
            assert_eq!(certificate.torsion[&k], Vec::<i128>::new());
        }
        certificate.verify(&complex).expect("certificate verifies");
    }

    #[test]
    fn circle_cohomology_matches_homology() {
        let complex = circle();
        let certificate = cohomology(&complex).expect("cohomology of a circle");
        assert_eq!(certificate.free_rank[&0], 1);
        assert_eq!(certificate.free_rank[&1], 1);
        certificate.verify(&complex).expect("certificate verifies");
    }

    /// ADVERSARIAL. Forge only `torsion`, leaving every coboundary Smith
    /// triple genuine: `free_rank_and_torsion_match` recomputes from the
    /// (genuine) recorded diagonals and disagrees with the forged claim.
    /// Confirmed by mutation: disabling only the torsion-comparison check in
    /// `free_rank_and_torsion_match` leaves every other test in this module
    /// green.
    #[test]
    fn verify_refuses_a_forged_torsion_with_every_smith_triple_genuine() {
        let complex = rp2_6v();
        let genuine = cohomology(&complex).expect("cohomology of RP^2");
        assert!(
            genuine.verify(&complex).is_ok(),
            "genuine certificate must verify"
        );

        let mut forged = genuine.clone();
        forged.torsion.insert(2, vec![3]); // H^2(RP^2) is Z/2, not Z/3
        let err = forged
            .verify(&complex)
            .expect_err("a forged torsion claim must be refused");
        assert!(
            err.contains("torsion"),
            "reason should name torsion, got: {err}"
        );
    }

    /// Direct unit test of `uct_cohomology_holds`, isolated from `verify`
    /// (and so from `free_rank_and_torsion_match`, which recomputes from the
    /// SAME coboundary Smith diagonal a bug in the transpose/Smith-form path
    /// would live in -- only the independent `Z` homology this guard
    /// cross-checks against can catch that class of bug). Confirmed by
    /// mutation: disabling only the call to `uct_cohomology_holds` in
    /// `verify` leaves every fixture test above green.
    #[test]
    fn uct_cohomology_holds_refuses_a_free_rank_torsion_mismatch() {
        let complex = rp2_6v();
        let genuine = cohomology(&complex).expect("cohomology of RP^2");
        // Genuine: free_rank[2] = 0 = b_2(Z), torsion[2] = torsion(H_1) = [2].
        assert_eq!(genuine.integer.betti[&2], 0);
        assert_eq!(genuine.integer.torsion[&1], vec![2]);

        let mut wrong_betti = genuine.integer.betti.clone();
        wrong_betti.insert(2, 1); // b_2(Z) is 0, not 1
        let err = uct_cohomology_holds(&genuine, &wrong_betti, &genuine.integer.torsion)
            .expect_err("a free-rank mismatch against b_n must be refused");
        assert!(err.contains("free rank"), "got: {err}");

        let mut wrong_torsion = genuine.integer.torsion.clone();
        wrong_torsion.insert(1, Vec::new()); // torsion(H_1) is [2], not empty
        let err = uct_cohomology_holds(&genuine, &genuine.integer.betti, &wrong_torsion)
            .expect_err("a torsion mismatch against H_{n-1} must be refused");
        assert!(err.contains("torsion"), "got: {err}");

        // POSITIVE CONTROL: the genuine pair is admitted.
        assert!(
            uct_cohomology_holds(&genuine, &genuine.integer.betti, &genuine.integer.torsion)
                .is_ok()
        );
    }
}
