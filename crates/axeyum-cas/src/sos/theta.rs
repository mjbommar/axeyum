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
use serde::Deserialize;

use super::psd_big::{BigPsd, BigPsdDecline, BigPsdLimits, is_psd_big};

/// Maximum graph order admitted by the portable edge-list front door.
/// Matches the default exact-PSD dimension envelope.
pub const MAX_THETA_ARTIFACT_GRAPH_ORDER: usize = 2_048;

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

/// Exact rational as canonical signed-decimal numerator and positive denominator.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RationalText {
    /// Canonical base-ten integer, with no leading `+` or redundant zeroes.
    pub numerator: String,
    /// Canonical positive base-ten integer.
    pub denominator: String,
}

/// One sparse multiplier in the portable theta-dual artifact.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NonedgeMultiplierText {
    /// Zero-based smaller endpoint.
    pub u: usize,
    /// Zero-based larger endpoint.
    pub v: usize,
    /// Exact multiplier.
    pub value: RationalText,
}

/// Portable, instance-separate exact theta-dual artifact.
///
/// The graph is deliberately not embedded. The checker receives its bytes as a
/// separate input, so replacing the target instance cannot be hidden inside a
/// self-consistent certificate.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ThetaCliqueDualArtifactV1 {
    /// Must equal `axeyum.theta-clique-dual.v1`.
    pub schema: String,
    /// Exact objective / upper bound.
    pub bound: RationalText,
    /// Sparse non-edge multipliers.
    pub nonedge_multipliers: Vec<NonedgeMultiplierText>,
}

fn parse_rational_text(value: &RationalText) -> Result<BigRational, String> {
    let numerator = value
        .numerator
        .parse::<BigInt>()
        .map_err(|error| format!("invalid rational numerator: {error}"))?;
    let denominator = value
        .denominator
        .parse::<BigInt>()
        .map_err(|error| format!("invalid rational denominator: {error}"))?;
    if numerator.to_string() != value.numerator {
        return Err("rational numerator is not canonical decimal".to_owned());
    }
    if denominator <= BigInt::zero() || denominator.to_string() != value.denominator {
        return Err("rational denominator is not canonical positive decimal".to_owned());
    }
    let rational = BigRational::new(numerator.clone(), denominator.clone());
    if rational.numer() != &numerator || rational.denom() != &denominator {
        return Err("rational is not in lowest terms".to_owned());
    }
    Ok(rational)
}

/// Convert a strictly parsed portable artifact into the checker-native dual.
///
/// # Errors
///
/// Rejects an unknown schema, non-canonical rational text, a non-positive
/// denominator, or a fraction that is not in lowest terms. Graph-relative
/// endpoint/support checks remain the responsibility of
/// [`check_theta_clique_dual`].
pub fn theta_dual_from_artifact(
    artifact: &ThetaCliqueDualArtifactV1,
) -> Result<ThetaCliqueDual, String> {
    if artifact.schema != "axeyum.theta-clique-dual.v1" {
        return Err(format!(
            "unsupported theta-dual schema {:?}",
            artifact.schema
        ));
    }
    let bound = parse_rational_text(&artifact.bound)?;
    let nonedge_multipliers = artifact
        .nonedge_multipliers
        .iter()
        .map(|entry| {
            Ok(NonedgeMultiplier {
                u: entry.u,
                v: entry.v,
                value: parse_rational_text(&entry.value)?,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    Ok(ThetaCliqueDual {
        bound,
        nonedge_multipliers,
    })
}

/// Parse the simple one-based edge-list format used by the Krpan--Povh archive.
///
/// The first line is `n m`; exactly `m` subsequent non-empty lines must each
/// contain two endpoints. Edges may be written in either orientation, but
/// loops, duplicates, out-of-range endpoints, comments, and trailing payload
/// are rejected.
///
/// # Errors
///
/// Returns a precise syntax or graph-integrity error without constructing a
/// partial adjacency matrix.
pub fn parse_simple_edge_list(input: &str) -> Result<Vec<Vec<bool>>, String> {
    let mut lines = input.lines();
    let header = lines.next().ok_or("graph is empty")?;
    let header_fields: Vec<_> = header.split_whitespace().collect();
    if header_fields.len() != 2 {
        return Err("graph header must contain exactly n and m".to_owned());
    }
    let order = header_fields[0]
        .parse::<usize>()
        .map_err(|error| format!("invalid graph order: {error}"))?;
    let declared_edges = header_fields[1]
        .parse::<usize>()
        .map_err(|error| format!("invalid graph edge count: {error}"))?;
    if order > MAX_THETA_ARTIFACT_GRAPH_ORDER {
        return Err(format!(
            "graph order {order} exceeds artifact limit {MAX_THETA_ARTIFACT_GRAPH_ORDER}"
        ));
    }
    let maximum_edges = order
        .checked_mul(order.saturating_sub(1))
        .and_then(|value| value.checked_div(2))
        .ok_or("graph edge-cap arithmetic overflow")?;
    if declared_edges > maximum_edges {
        return Err(format!(
            "graph declares {declared_edges} edges but order {order} admits at most {maximum_edges}"
        ));
    }
    let mut adjacency = vec![vec![false; order]; order];
    let mut seen = BTreeSet::new();
    for (line_index, line) in lines.enumerate() {
        if line.trim().is_empty() {
            return Err(format!("blank graph line {}", line_index + 2));
        }
        let fields: Vec<_> = line.split_whitespace().collect();
        if fields.len() != 2 {
            return Err(format!(
                "graph line {} must contain exactly two endpoints",
                line_index + 2
            ));
        }
        let left = fields[0]
            .parse::<usize>()
            .map_err(|error| format!("invalid endpoint on line {}: {error}", line_index + 2))?;
        let right = fields[1]
            .parse::<usize>()
            .map_err(|error| format!("invalid endpoint on line {}: {error}", line_index + 2))?;
        if left == 0 || right == 0 || left > order || right > order {
            return Err(format!("endpoint out of range on line {}", line_index + 2));
        }
        if left == right {
            return Err(format!("self-loop on line {}", line_index + 2));
        }
        let pair = if left < right {
            (left - 1, right - 1)
        } else {
            (right - 1, left - 1)
        };
        if !seen.insert(pair) {
            return Err(format!("duplicate edge on line {}", line_index + 2));
        }
        adjacency[pair.0][pair.1] = true;
        adjacency[pair.1][pair.0] = true;
    }
    if seen.len() != declared_edges {
        return Err(format!(
            "graph declares {declared_edges} edges but contains {}",
            seen.len()
        ));
    }
    Ok(adjacency)
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

    #[test]
    fn strict_external_formats_round_trip_to_a_checked_dual() {
        let adjacency = parse_simple_edge_list("3 2\n2 1\n2 3\n").unwrap();
        let artifact: ThetaCliqueDualArtifactV1 = serde_json::from_str(
            r#"{
                "schema":"axeyum.theta-clique-dual.v1",
                "bound":{"numerator":"2","denominator":"1"},
                "nonedge_multipliers":[
                    {"u":0,"v":2,"value":{"numerator":"2","denominator":"1"}}
                ]
            }"#,
        )
        .unwrap();
        let certificate = theta_dual_from_artifact(&artifact).unwrap();
        assert!(matches!(
            check_theta_clique_dual(&adjacency, &certificate, BigPsdLimits::default()),
            ThetaDualCheck::Verified { .. }
        ));
    }

    #[test]
    fn external_formats_reject_ambiguous_or_detached_data() {
        for malformed in [
            "3 1\n1 1\n",
            "3 2\n1 2\n2 1\n",
            "3 2\n1 2\n",
            "3 1\n1 4\n",
            "3 1\n1 2 extra\n",
            "2049 0\n",
            "3 4\n",
        ] {
            assert!(parse_simple_edge_list(malformed).is_err(), "{malformed:?}");
        }
        for malformed in [
            r#"{"schema":"wrong","bound":{"numerator":"1","denominator":"1"},"nonedge_multipliers":[]}"#,
            r#"{"schema":"axeyum.theta-clique-dual.v1","bound":{"numerator":"01","denominator":"1"},"nonedge_multipliers":[]}"#,
            r#"{"schema":"axeyum.theta-clique-dual.v1","bound":{"numerator":"1","denominator":"2"},"nonedge_multipliers":[{"u":0,"v":1,"value":{"numerator":"2","denominator":"4"}}]}"#,
            r#"{"schema":"axeyum.theta-clique-dual.v1","bound":{"numerator":"1","denominator":"0"},"nonedge_multipliers":[]}"#,
        ] {
            let artifact: ThetaCliqueDualArtifactV1 = serde_json::from_str(malformed).unwrap();
            assert!(theta_dual_from_artifact(&artifact).is_err(), "{malformed}");
        }
        assert!(serde_json::from_str::<ThetaCliqueDualArtifactV1>(
            r#"{"schema":"axeyum.theta-clique-dual.v1","bound":{"numerator":"1","denominator":"1","extra":0},"nonedge_multipliers":[]}"#
        )
        .is_err());
    }
}
