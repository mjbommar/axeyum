//! Deterministic sparse search for Lemire half-degree candidates.

use core::fmt;

use crate::gf2::{Gf2Error, Gf2Limits, Gf2Poly, IrreducibilityCertificate, certify_irreducible};

/// Explicit ceilings for one degree's sparse search.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SparseSearchLimits {
    /// Largest even number of nonleading terms to enumerate (including one).
    pub max_tail_terms: usize,
    /// Maximum candidates tested for this degree.
    pub max_candidates: u64,
    /// Per-candidate arithmetic and certificate limits.
    pub arithmetic: Gf2Limits,
}

impl Default for SparseSearchLimits {
    fn default() -> Self {
        Self {
            max_tail_terms: 4,
            max_candidates: 2_000_000,
            arithmetic: Gf2Limits::default(),
        }
    }
}

/// One deterministic sparse-search result.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SparseSearchOutcome {
    /// The first candidate in the specified enumeration order was certified.
    Found {
        /// Portable irreducibility certificate.
        certificate: IrreducibilityCertificate,
        /// Candidate count including the successful candidate.
        candidates_tested: u64,
        /// Number of nonleading terms in the successful polynomial.
        tail_terms: usize,
    },
    /// Every candidate through `max_tail_terms` was reducible.
    Exhausted {
        /// Complete number of candidates tested.
        candidates_tested: u64,
    },
    /// Enumeration stopped before completing the configured sparse layers.
    CandidateLimit {
        /// Number of candidates tested before the decline.
        candidates_tested: u64,
        /// Configured candidate ceiling.
        limit: u64,
    },
}

/// Invalid search policy or bounded arithmetic decline.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SparseSearchError {
    /// `max_tail_terms` must be a positive even number.
    InvalidTailTerms,
    /// Candidate construction or checking declined under its arithmetic limits.
    Arithmetic(Gf2Error),
}

impl fmt::Display for SparseSearchError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidTailTerms => {
                write!(formatter, "max_tail_terms must be a positive even number")
            }
            Self::Arithmetic(error) => write!(formatter, "GF(2) arithmetic declined: {error}"),
        }
    }
}

impl std::error::Error for SparseSearchError {}

impl From<Gf2Error> for SparseSearchError {
    fn from(error: Gf2Error) -> Self {
        Self::Arithmetic(error)
    }
}

/// Enumerate sparse half-degree candidates in a stable order.
///
/// For `n > 1`, every irreducible must have constant coefficient one and an odd
/// total number of terms (otherwise `x` or `x+1` divides it).  The search
/// therefore tries `x^n+x^k+1` in ascending `k`, then pentanomials in
/// lexicographic exponent order, then larger odd selections if allowed.  It
/// returns the first dual-checkable certificate producer result; it does not
/// claim a polynomial exists beyond the searched sparse layers.
///
/// # Errors
///
/// Returns [`SparseSearchError::InvalidTailTerms`] for a malformed policy, or a
/// typed arithmetic/resource decline from candidate construction or checking.
pub fn search_sparse_half_degree(
    degree: usize,
    limits: SparseSearchLimits,
) -> Result<SparseSearchOutcome, SparseSearchError> {
    if limits.max_tail_terms == 0 || !limits.max_tail_terms.is_multiple_of(2) {
        return Err(SparseSearchError::InvalidTailTerms);
    }
    if degree == 0 {
        return Err(SparseSearchError::Arithmetic(Gf2Error::NotPositiveDegree));
    }
    if degree == 1 {
        if limits.max_candidates == 0 {
            return Ok(SparseSearchOutcome::CandidateLimit {
                candidates_tested: 0,
                limit: 0,
            });
        }
        let polynomial = Gf2Poly::from_exponents(&[1], limits.arithmetic)?;
        let certificate = certify_irreducible(&polynomial, limits.arithmetic)?.ok_or(
            SparseSearchError::Arithmetic(Gf2Error::InvalidCertificate(
                "linear candidate was not certified",
            )),
        )?;
        return Ok(SparseSearchOutcome::Found {
            certificate,
            candidates_tested: 1,
            tail_terms: 0,
        });
    }

    let maximum_exponent = degree / 2;
    let mut candidates_tested = 0_u64;
    for selected_count in (1..limits.max_tail_terms).step_by(2) {
        if selected_count > maximum_exponent {
            break;
        }
        let mut selected: Vec<usize> = (1..=selected_count).collect();
        loop {
            if candidates_tested >= limits.max_candidates {
                return Ok(SparseSearchOutcome::CandidateLimit {
                    candidates_tested,
                    limit: limits.max_candidates,
                });
            }
            let mut exponents = Vec::with_capacity(selected_count + 2);
            exponents.push(0);
            exponents.extend_from_slice(&selected);
            exponents.push(degree);
            let polynomial = Gf2Poly::from_exponents(&exponents, limits.arithmetic)?;
            candidates_tested += 1;
            if let Some(certificate) = certify_irreducible(&polynomial, limits.arithmetic)? {
                return Ok(SparseSearchOutcome::Found {
                    certificate,
                    candidates_tested,
                    tail_terms: selected_count + 1,
                });
            }
            if !next_combination(&mut selected, maximum_exponent) {
                break;
            }
        }
    }
    Ok(SparseSearchOutcome::Exhausted { candidates_tested })
}

fn next_combination(selected: &mut [usize], maximum: usize) -> bool {
    for index in (0..selected.len()).rev() {
        let remaining = selected.len() - 1 - index;
        let maximum_here = maximum - remaining;
        if selected[index] >= maximum_here {
            continue;
        }
        selected[index] += 1;
        for following in index + 1..selected.len() {
            selected[following] = selected[following - 1] + 1;
        }
        return true;
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gf2::check_irreducible_certificate;
    use crate::gf2_independent::{
        IndependentCheckLimits, check_irreducible_certificate_independent,
    };

    #[test]
    fn stable_search_finds_and_dual_checks_small_degrees() {
        let limits = SparseSearchLimits::default();
        for degree in 1..=24 {
            let SparseSearchOutcome::Found { certificate, .. } =
                search_sparse_half_degree(degree, limits).unwrap()
            else {
                panic!("sparse search did not find degree {degree}");
            };
            check_irreducible_certificate(&certificate, limits.arithmetic).unwrap();
            check_irreducible_certificate_independent(
                &certificate,
                IndependentCheckLimits::default(),
            )
            .unwrap();
            assert!(
                certificate
                    .polynomial
                    .exponents()
                    .into_iter()
                    .all(|exponent| exponent == degree || exponent <= degree / 2)
            );
        }
    }

    #[test]
    fn candidate_limit_is_not_reported_as_exhaustion() {
        let limits = SparseSearchLimits {
            max_candidates: 0,
            ..SparseSearchLimits::default()
        };
        assert_eq!(
            search_sparse_half_degree(20, limits).unwrap(),
            SparseSearchOutcome::CandidateLimit {
                candidates_tested: 0,
                limit: 0
            }
        );
    }

    #[test]
    fn malformed_tail_policy_is_rejected() {
        let limits = SparseSearchLimits {
            max_tail_terms: 3,
            ..SparseSearchLimits::default()
        };
        assert_eq!(
            search_sparse_half_degree(20, limits),
            Err(SparseSearchError::InvalidTailTerms)
        );
    }

    #[test]
    fn combination_order_is_lexicographic_and_complete() {
        let mut selected = vec![1, 2, 3];
        let mut observed = vec![selected.clone()];
        while next_combination(&mut selected, 5) {
            observed.push(selected.clone());
        }
        assert_eq!(observed.len(), 10);
        assert_eq!(observed[1], vec![1, 2, 4]);
        assert_eq!(observed[9], vec![3, 4, 5]);
    }
}
