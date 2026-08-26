//! Exact, instance-bound dual certificates for the Lovász theta clique bound.
//!
//! For an undirected graph `G`, this module checks the dual of
//!
//! `max <J, X>` subject to `trace(X) = 1`, `X_ij = 0` for every non-edge,
//! and `X` positive semidefinite.
//!
//! A certificate supplies a rational `t` and a symmetric matrix `Y` supported
//! only on non-edges. If `t I + Y - J` is positive semidefinite, weak duality
//! gives `omega(G) <= theta(G) <= t`. The checker reconstructs this slack from
//! the graph and sparse multipliers; it never accepts a detached PSD matrix.

use std::collections::BTreeSet;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use super::psd_big::{BigPsd, BigPsdDecline, BigPsdLimits, is_psd_big};

/// One symmetric dual multiplier, supported on a graph non-edge.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NonedgeMultiplier {
    /// Smaller endpoint.
    pub u: usize,
    /// Larger endpoint.
    pub v: usize,
    /// Entry placed in both `(u,v)` and `(v,u)` of the dual matrix.
    pub value: BigRational,
}

/// Sparse exact dual data for the standard theta clique relaxation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ThetaCliqueDual {
    /// Dual objective and claimed rational upper bound.
    pub bound: BigRational,
    /// Nonzero multipliers; omitted non-edges have multiplier zero.
    pub nonedge_multipliers: Vec<NonedgeMultiplier>,
}

/// Result of checking an exact theta dual against its graph instance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ThetaDualCheck {
    /// The reconstructed slack is PSD, so the stated rational bound follows.
    Verified {
        /// Exact PSD decision record for the reconstructed slack.
        slack: BigPsd,
    },
    /// Malformed data or an exactly non-PSD slack refuted the certificate.
    Rejected(String),
    /// Explicit resource policy prevented a mathematical verdict.
    Declined(BigPsdDecline),
}

fn integer(value: i8) -> BigRational {
    BigRational::from_integer(BigInt::from(value))
}

/// Check a theta clique dual against a symmetric loop-free adjacency matrix.
///
/// `adjacency[u][v]` is true exactly for graph edges. Rows must be square,
/// symmetric, and false on the diagonal. Multiplier pairs must be canonical
/// (`u < v`), unique, in range, and actual non-edges.
#[must_use]
pub fn check_theta_clique_dual(
    adjacency: &[Vec<bool>],
    certificate: &ThetaCliqueDual,
    limits: BigPsdLimits,
) -> ThetaDualCheck {
    let n = adjacency.len();
    if certificate.bound.is_negative() {
        return ThetaDualCheck::Rejected("theta bound is negative".to_owned());
    }
    for (u, row) in adjacency.iter().enumerate() {
        if row.len() != n {
            return ThetaDualCheck::Rejected(format!(
                "adjacency row {u} has {} entries for order {n}",
                row.len()
            ));
        }
        if row[u] {
            return ThetaDualCheck::Rejected(format!("self-loop at vertex {u}"));
        }
        for v in 0..u {
            if row[v] != adjacency[v][u] {
                return ThetaDualCheck::Rejected(format!("asymmetric adjacency at ({u}, {v})"));
            }
        }
    }

    let mut slack = vec![vec![BigRational::zero(); n]; n];
    for (u, row) in slack.iter_mut().enumerate() {
        row[u] = &certificate.bound - BigRational::one();
        for (v, value) in row.iter_mut().enumerate() {
            if u != v {
                *value = integer(-1);
            }
        }
    }

    let mut seen = BTreeSet::new();
    for multiplier in &certificate.nonedge_multipliers {
        let (u, v) = (multiplier.u, multiplier.v);
        if u >= n || v >= n {
            return ThetaDualCheck::Rejected(format!(
                "multiplier endpoint ({u}, {v}) is outside graph order {n}"
            ));
        }
        if u >= v {
            return ThetaDualCheck::Rejected(format!(
                "multiplier pair ({u}, {v}) is not canonical"
            ));
        }
        if adjacency[u][v] {
            return ThetaDualCheck::Rejected(format!("multiplier pair ({u}, {v}) is an edge"));
        }
        if !seen.insert((u, v)) {
            return ThetaDualCheck::Rejected(format!("duplicate multiplier pair ({u}, {v})"));
        }
        slack[u][v] += &multiplier.value;
        slack[v][u] += &multiplier.value;
    }

    match is_psd_big(&slack, limits) {
        yes @ BigPsd::Yes { .. } => ThetaDualCheck::Verified { slack: yes },
        BigPsd::No(reason) => ThetaDualCheck::Rejected(format!("dual slack is not PSD: {reason}")),
        BigPsd::Declined(reason) => ThetaDualCheck::Declined(reason),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rational(value: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(value))
    }

    fn graph(order: usize, edges: &[(usize, usize)]) -> Vec<Vec<bool>> {
        let mut adjacency = vec![vec![false; order]; order];
        for &(u, v) in edges {
            adjacency[u][v] = true;
            adjacency[v][u] = true;
        }
        adjacency
    }

    #[test]
    fn complete_graph_bound_is_bound_to_edges_and_exact_psd() {
        let k3 = graph(3, &[(0, 1), (0, 2), (1, 2)]);
        let certificate = ThetaCliqueDual {
            bound: rational(3),
            nonedge_multipliers: vec![],
        };
        assert!(matches!(
            check_theta_clique_dual(&k3, &certificate, BigPsdLimits::default()),
            ThetaDualCheck::Verified { .. }
        ));

        let false_bound = ThetaCliqueDual {
            bound: rational(2),
            nonedge_multipliers: vec![],
        };
        assert!(matches!(
            check_theta_clique_dual(&k3, &false_bound, BigPsdLimits::default()),
            ThetaDualCheck::Rejected(_)
        ));
    }

    #[test]
    fn empty_graph_has_exact_bound_one_with_nonedge_multipliers() {
        let certificate = ThetaCliqueDual {
            bound: rational(1),
            nonedge_multipliers: vec![
                NonedgeMultiplier {
                    u: 0,
                    v: 1,
                    value: rational(1),
                },
                NonedgeMultiplier {
                    u: 0,
                    v: 2,
                    value: rational(1),
                },
                NonedgeMultiplier {
                    u: 1,
                    v: 2,
                    value: rational(1),
                },
            ],
        };
        assert!(matches!(
            check_theta_clique_dual(&graph(3, &[]), &certificate, BigPsdLimits::default()),
            ThetaDualCheck::Verified { .. }
        ));
    }

    #[test]
    fn malformed_or_instance_detached_multipliers_fail_closed() {
        let path = graph(3, &[(0, 1), (1, 2)]);
        for multiplier in [
            NonedgeMultiplier {
                u: 0,
                v: 1,
                value: rational(1),
            },
            NonedgeMultiplier {
                u: 2,
                v: 0,
                value: rational(1),
            },
            NonedgeMultiplier {
                u: 0,
                v: 3,
                value: rational(1),
            },
        ] {
            let certificate = ThetaCliqueDual {
                bound: rational(3),
                nonedge_multipliers: vec![multiplier],
            };
            assert!(matches!(
                check_theta_clique_dual(&path, &certificate, BigPsdLimits::default()),
                ThetaDualCheck::Rejected(_)
            ));
        }

        let duplicate = ThetaCliqueDual {
            bound: rational(3),
            nonedge_multipliers: vec![
                NonedgeMultiplier {
                    u: 0,
                    v: 2,
                    value: rational(1),
                },
                NonedgeMultiplier {
                    u: 0,
                    v: 2,
                    value: rational(1),
                },
            ],
        };
        assert!(matches!(
            check_theta_clique_dual(&path, &duplicate, BigPsdLimits::default()),
            ThetaDualCheck::Rejected(_)
        ));
    }

    #[test]
    fn malformed_graph_and_resource_decline_are_distinct() {
        let mut malformed = graph(2, &[]);
        malformed[0][1] = true;
        let certificate = ThetaCliqueDual {
            bound: rational(2),
            nonedge_multipliers: vec![],
        };
        assert!(matches!(
            check_theta_clique_dual(&malformed, &certificate, BigPsdLimits::default()),
            ThetaDualCheck::Rejected(_)
        ));

        let limits = BigPsdLimits {
            max_dimension: 1,
            ..BigPsdLimits::default()
        };
        assert!(matches!(
            check_theta_clique_dual(&graph(2, &[(0, 1)]), &certificate, limits),
            ThetaDualCheck::Declined(BigPsdDecline::Dimension { .. })
        ));

        let negative = ThetaCliqueDual {
            bound: rational(-1),
            nonedge_multipliers: vec![],
        };
        assert!(matches!(
            check_theta_clique_dual(&[], &negative, BigPsdLimits::default()),
            ThetaDualCheck::Rejected(_)
        ));
    }
}
