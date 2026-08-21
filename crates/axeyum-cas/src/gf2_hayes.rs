//! Exact bounded Hayes type-II class computations over `GF(2)`.
//!
//! This module supplies the reusable algebra behind the Lemire endpoint
//! experiment. Search and asymptotic conjectures remain untrusted: the public
//! general operations compute exact integral class counts using two modular
//! transforms and CRT, with explicit admission limits and residue checks.  A
//! specialized odd-endpoint route uses its sharper proved population bound to
//! recover the same integer from one admitted transform prime.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt;
use std::sync::{Mutex, OnceLock};

use num_bigint::{BigInt, BigUint};
use num_traits::ToPrimitive;
use serde::{Deserialize, Serialize};

const PRIME_ONE: u64 = 998_244_353;
const PRIME_TWO: u64 = 1_004_535_809;
// `3` is a primitive root and `p-1 = 70 * 2^30`, so this prime supports
// every principal-unit NTT admitted by the odd-endpoint runner below.
const ODD_ENDPOINT_SINGLE_PRIME: u64 = 75_161_927_681;
const PRIMITIVE_ROOT: u64 = 3;
const POWER_SUM_CHARACTER_BLOCK: usize = 1 << 15;

struct CharacterMobiusTable {
    rows: Vec<Vec<u64>>,
    dimensions: Vec<usize>,
    unit_to_index: BTreeMap<u64, usize>,
}

/// Resource admission for an exact Hayes transform.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct HayesLimits {
    /// Largest admitted coefficient-prefix length.
    pub max_ell: usize,
    /// Largest admitted target degree.
    pub max_degree: usize,
    /// Largest admitted principal-unit group order.
    pub max_group_order: usize,
    /// Largest admitted number of retained modular table cells.
    pub max_table_cells: usize,
}

impl Default for HayesLimits {
    fn default() -> Self {
        Self {
            max_ell: 23,
            max_degree: 48,
            max_group_order: 1 << 23,
            max_table_cells: 610_000_000,
        }
    }
}

/// Resource admission for the exact cyclic/Foulkes compression ledger.
///
/// The orthogonality certificate retains one Ramanujan sum for every residue
/// and recomputes its scalar product against every divisor of `degree`.
/// Keeping this limit separate from [`HayesLimits`] allows the representation
/// ledger to reach the degree-400 finite handoff without admitting a Hayes
/// transform of comparable size.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct SawinFoulkesLimits {
    /// Largest admitted polynomial degree.
    pub max_degree: usize,
    /// Largest admitted residue-by-divisor orthogonality table.
    pub max_orthogonality_cells: usize,
}

/// Resource admission for the exact Tuxanidy--Wang least-period diagnostic.
///
/// The operation multiplies characteristic-delta functions in the group
/// algebra `GF(2)[Z/(2^n-1)]`.  Its work depends on the intermediate support,
/// so both the cyclic domain and the exact number of toggled cells are
/// admitted explicitly.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct TuxanidyPeriodLimits {
    /// Largest admitted extension/polynomial degree.
    pub max_degree: usize,
    /// Largest admitted cyclic group order `2^degree-1`.
    pub max_cyclic_order: usize,
    /// Largest admitted number of exact parity-toggle cells.
    pub max_convolution_cells: usize,
}

impl Default for TuxanidyPeriodLimits {
    fn default() -> Self {
        Self {
            max_degree: 14,
            max_cyclic_order: (1 << 14) - 1,
            max_convolution_cells: 250_000_000,
        }
    }
}

impl Default for SawinFoulkesLimits {
    fn default() -> Self {
        Self {
            max_degree: 10_000,
            max_orthogonality_cells: 1_000_000,
        }
    }
}

/// A typed decline or failed invariant from an exact Hayes computation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HayesError {
    /// The requested parameters exceed the caller's explicit limits.
    ResourceLimit {
        /// Name of the limited quantity.
        resource: &'static str,
        /// Requested quantity.
        requested: usize,
        /// Admitted maximum.
        limit: usize,
    },
    /// A parameter is outside the mathematical representation domain.
    InvalidParameter(String),
    /// An exact internal invariant failed.
    Invariant(String),
}

impl fmt::Display for HayesError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ResourceLimit {
                resource,
                requested,
                limit,
            } => write!(
                formatter,
                "{resource} resource limit exceeded: requested {requested}, limit {limit}"
            ),
            Self::InvalidParameter(message) | Self::Invariant(message) => {
                formatter.write_str(message)
            }
        }
    }
}

impl std::error::Error for HayesError {}

/// Exact endpoint discrepancies for one coefficient-prefix length.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct EndpointDiscrepancies {
    /// Number of prescribed zero coefficients.
    pub ell: usize,
    /// `Delta_(ell, 2 ell + 1)`.
    pub odd: i128,
    /// `Delta_(ell, 2 ell + 2)`.
    pub even: i128,
}

impl EndpointDiscrepancies {
    /// Whether both observed discrepancies satisfy the candidate `2^ell` bound.
    #[must_use]
    pub fn satisfies_candidate_bound(self) -> bool {
        let Ok(shift) = u32::try_from(self.ell) else {
            return false;
        };
        let Some(bound) = 1_u128.checked_shl(shift) else {
            return false;
        };
        self.odd.unsigned_abs() <= bound && self.even.unsigned_abs() <= bound
    }
}

/// One exact-conductor contribution to the endpoint discrepancy.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConductorLayer {
    /// Exact conductor exponent `j + 1` is represented by this level `j`.
    pub level: usize,
    /// `T_(j,n) = 2^j Delta_(j,n) - 2^(j-1) Delta_(j-1,n)`.
    pub value: i128,
}

/// Exact degree distribution of the nontrivial binary Hayes `L`-polynomials.
///
/// A character of exact level `j` has conductor `x^(j+1)`.  Because every
/// character over `GF(2)` is even, primitivity makes its `L`-polynomial have
/// exact degree `j-1`.  The kernel of the restriction from level `j` to
/// level `j-1` has order two, so there are exactly `2^(j-1)` characters at
/// exact level `j`.  Thus the number of `L`-polynomials of degree `d` is
/// `2^d` for `1 <= d < ell`; the one nontrivial level-one character has
/// degree zero and contributes nothing to the aggregate degree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryHayesLDegreeDistribution {
    /// Hayes coefficient-prefix level.
    pub ell: usize,
    /// `(degree, character count)` for every positive degree below `ell`.
    pub positive_degree_counts: Vec<(usize, BigUint)>,
    /// Number `2^ell-1` of nontrivial characters, including degree zero.
    pub nontrivial_character_count: BigUint,
    /// Exact sum of all nontrivial `L`-polynomial degrees.
    pub aggregate_degree: BigUint,
    /// Closed form `(ell-2)2^ell+2` for the aggregate degree.
    pub aggregate_degree_closed_form: BigUint,
}

/// Exact witness that a functional-equation root number does not determine
/// the high Hayes power sum used at the Lemire endpoint.
///
/// Character values are retained in the integral basis
/// `1,zeta,...,zeta^(phi-1)` of `Z[zeta]`, where `zeta` has the reported
/// power-of-two order and `phi=order/2`.  Thus equality and inequality below
/// are exact coefficient-vector statements, not modular or floating-point
/// comparisons.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HayesRootNumberFibreWitness {
    /// Exact conductor level of both primitive characters.
    pub level: usize,
    /// Power-sum degree compared inside the fibre.
    pub degree: usize,
    /// Order of the common primitive root used for the integral basis.
    pub cyclotomic_order: usize,
    /// First mixed-radix character index.
    pub left_character: usize,
    /// Second mixed-radix character index.
    pub right_character: usize,
    /// Common leading `L`-coefficient, which fixes the root number.
    pub common_leading_coefficient: Vec<i128>,
    /// Exact logarithmic power sum for the first character.
    pub left_power_sum: Vec<i128>,
    /// Exact logarithmic power sum for the second character.
    pub right_power_sum: Vec<i128>,
}

/// Bounded exact audit of root-number fibres among primitive Hayes characters.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HayesRootNumberFibreReport {
    /// Exact conductor level.
    pub level: usize,
    /// Compared logarithmic power-sum degree.
    pub degree: usize,
    /// Number `2^(level-1)` of primitive characters inspected.
    pub primitive_character_count: usize,
    /// Number of distinct exact leading-coefficient fibres.
    pub leading_coefficient_fibre_count: usize,
    /// Number of fibres containing more than one endpoint power sum.
    pub varying_power_sum_fibre_count: usize,
    /// First exact witness, when root-number data are insufficient.
    pub witness: Option<HayesRootNumberFibreWitness>,
}

/// One exact normalized `2`-adic Newton slope.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct HayesTwoAdicNewtonSlope {
    /// Reduced numerator of the slope with `v_2(2)=1`.
    pub numerator: usize,
    /// Positive reduced denominator of the slope.
    pub denominator: usize,
    /// Number of reciprocal roots on this segment.
    pub multiplicity: usize,
}

/// Exact Newton polygon of one primitive Hayes character.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HayesCharacterTwoAdicNewtonRow {
    /// Mixed-radix character index.
    pub character: usize,
    /// Exact multiplicative order of the character.
    pub character_order: usize,
    /// `v_(1-zeta)` of every `L`-coefficient; `None` denotes zero.
    pub coefficient_uniformizer_valuations: Vec<Option<usize>>,
    /// Normalized lower Newton-polygon slopes in increasing order.
    pub slopes: Vec<HayesTwoAdicNewtonSlope>,
}

/// Exact primitive-character Newton polygons at one Hayes conductor level.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HayesConductorTwoAdicNewtonReport {
    /// Exact conductor level.
    pub level: usize,
    /// Frobenius power used for the trace comparison.
    pub degree: usize,
    /// Ambient power-of-two cyclotomic order.
    pub cyclotomic_order: usize,
    /// Ramification index `phi(cyclotomic_order)` above two.
    pub two_adic_ramification_index: usize,
    /// Number `2^(level-1)` of primitive characters.
    pub primitive_character_count: usize,
    /// One exact Newton polygon per primitive character.
    pub characters: Vec<HayesCharacterTwoAdicNewtonRow>,
    /// Smallest normalized slope occurring in the conductor layer.
    pub minimum_slope_numerator: usize,
    /// Denominator of the smallest normalized slope.
    pub minimum_slope_denominator: usize,
    /// Total reciprocal-root multiplicity at the smallest slope.
    pub minimum_slope_multiplicity: usize,
    /// Integral ceiling of `degree * minimum_slope`.
    pub minimum_power_valuation_ceiling: usize,
    /// Independently reconstructed exact conductor-layer trace.
    pub direct_conductor_trace: i128,
    /// Exact `2`-adic valuation of that trace; `None` denotes zero.
    pub direct_conductor_trace_two_adic_valuation: Option<u32>,
}

/// Exact trace statistics for character Galois orbits of one order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HayesGaloisOrbitOrderRow {
    /// Exact multiplicative order of every character in these orbits.
    pub character_order: usize,
    /// Number of Galois orbits of this order and exact conductor level.
    pub orbit_count: usize,
    /// Largest absolute integral orbit trace.
    pub maximum_absolute_trace: u128,
    /// Signed sum of every orbit trace in this exact-order layer.
    pub signed_trace_sum: i128,
}

/// Exact Galois-orbit decomposition of one Hayes conductor-layer trace.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HayesGaloisOrbitTraceReport {
    /// Exact conductor level.
    pub level: usize,
    /// Logarithmic power-sum degree.
    pub degree: usize,
    /// Number `2^(level-1)` of primitive characters.
    pub primitive_character_count: usize,
    /// Number of rational Galois orbits.
    pub orbit_count: usize,
    /// Candidate one-unit allowance `2^ceil(degree/2)` per orbit.
    pub candidate_orbit_allowance: u128,
    /// Largest exact absolute orbit trace.
    pub maximum_absolute_orbit_trace: u128,
    /// Number of orbits violating the candidate allowance.
    pub candidate_violation_count: usize,
    /// Candidate allowance `4(level-1)2^ceil(degree/2)` per exact-order layer.
    pub order_layer_candidate_allowance: u128,
    /// Largest absolute signed exact-order layer trace.
    pub maximum_absolute_order_layer_trace: u128,
    /// Number of exact-order layers violating their candidate allowance.
    pub order_layer_candidate_violation_count: usize,
    /// Smallest integral coefficient multiplying
    /// `(level-1)2^ceil(degree/2)` that covers every exact-order layer.
    pub required_order_layer_coefficient: u128,
    /// Sum of all exact integral orbit traces.
    pub reconstructed_conductor_trace: i128,
    /// Independent conductor-layer trace from class populations.
    pub direct_conductor_trace: i128,
    /// Orbit statistics partitioned by exact character order.
    pub orders: Vec<HayesGaloisOrbitOrderRow>,
}

/// Exact Galois-closed primitive trace packets induced by a generalized
/// Fomenko coefficient-zero restriction.
///
/// Restricting a Hayes character to the subgroup of principal units whose
/// first `t` coefficients vanish has kernel `E_t^dual`.  A restriction fibre
/// is not generally rational, so each fibre is closed under odd-power
/// cyclotomic Galois action before its integral trace is reconstructed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HayesFomenkoRestrictionPacketReport {
    /// Exact conductor level.
    pub level: usize,
    /// Coefficients `x^1..=x^restriction_level` killed in the subgroup.
    pub restriction_level: usize,
    /// Logarithmic power-sum degree.
    pub degree: usize,
    /// Size `2^restriction_level` of the restriction kernel.
    pub restriction_kernel_size: usize,
    /// Number `2^(level-1)` of primitive characters.
    pub primitive_character_count: usize,
    /// Number of Galois-closed restriction packets.
    pub packet_count: usize,
    /// Largest number of characters in one packet.
    pub maximum_packet_size: usize,
    /// Candidate one-unit allowance `2^ceil(degree/2)` per packet.
    pub square_root_allowance: u128,
    /// Largest exact absolute packet trace.
    pub maximum_absolute_packet_trace: u128,
    /// Sum of absolute packet traces before the final signed conductor sum.
    pub packetwise_absolute_trace: u128,
    /// Packets exceeding `square_root_allowance`.
    pub square_root_violation_count: usize,
    /// Smallest integer coefficient multiplying `square_root_allowance` that
    /// covers every fibre.
    pub required_square_root_coefficient: u128,
    /// Sum of all exact fibre traces.
    pub reconstructed_conductor_trace: i128,
    /// Independent exact-conductor trace from the population transform.
    pub direct_conductor_trace: i128,
}

/// Exact size obstruction to extending the Gorodetsky--Kovaleva monomial
/// symmetry to a complete primitive Hayes conductor layer.
///
/// Over `GF(2)`, every special power-sum character
/// `chi_(k,psi)(f)=psi(p_(-k)(f))` is quadratic.  Products of such characters
/// therefore remain in the order-two subgroup of the Hayes character group.
/// This report counts the primitive part of that subgroup exactly, without
/// assuming that the special characters generate all of it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HayesPowerSumCharacterCoverage {
    /// Exact conductor level.
    pub level: usize,
    /// Number `2^(level-1)` of primitive characters at this level.
    pub primitive_character_count: usize,
    /// Primitive characters of order exactly two.
    pub primitive_quadratic_character_count: usize,
    /// Primitive characters of order greater than two.
    pub primitive_higher_order_character_count: usize,
    /// Number of primitive single-monomial characters `chi_(k,psi)` whose
    /// conductor is exactly this level: one for odd level, zero for even.
    pub primitive_single_monomial_character_count: usize,
    /// Largest possible primitive coverage of the multiplicative span of all
    /// binary power-sum characters through this level.  This is an upper
    /// bound, equal to the primitive quadratic count.
    pub maximum_power_sum_span_coverage: usize,
}

/// Compute the exact binary Hayes `L`-degree distribution.
///
/// This replays the conductor-count proof behind the binary pattern
/// `d_j=2^j` observed by Gao.  It also exposes the aggregate degree entering
/// the standard characterwise Weil error: asymptotically it is
/// `(ell-2)2^ell`, so this exact refinement does not remove the linear factor
/// at Lemire's half-degree endpoint.
///
/// # Errors
///
/// Returns a resource decline when `ell` exceeds `limits.max_ell`, or a
/// parameter error when `ell` is zero.
pub fn binary_hayes_l_degree_distribution(
    ell: usize,
    limits: HayesLimits,
) -> Result<BinaryHayesLDegreeDistribution, HayesError> {
    if ell == 0 {
        return Err(HayesError::InvalidParameter(
            "binary Hayes L-degree distribution requires positive ell".to_owned(),
        ));
    }
    if ell > limits.max_ell {
        return Err(HayesError::ResourceLimit {
            resource: "ell",
            requested: ell,
            limit: limits.max_ell,
        });
    }

    let group_order = BigUint::from(1_u8) << ell;
    let positive_degree_counts = (1..ell)
        .map(|degree| (degree, BigUint::from(1_u8) << degree))
        .collect::<Vec<_>>();
    let aggregate_degree = positive_degree_counts
        .iter()
        .fold(BigUint::from(0_u8), |sum, (degree, count)| {
            sum + BigUint::from(*degree) * count
        });
    let aggregate_degree_closed_form = if ell == 1 {
        BigUint::from(0_u8)
    } else {
        BigUint::from(ell - 2) * &group_order + BigUint::from(2_u8)
    };
    if aggregate_degree != aggregate_degree_closed_form {
        return Err(HayesError::Invariant(
            "binary Hayes L-degree sum disagrees with its closed form".to_owned(),
        ));
    }

    Ok(BinaryHayesLDegreeDistribution {
        ell,
        positive_degree_counts,
        nontrivial_character_count: group_order - BigUint::from(1_u8),
        aggregate_degree,
        aggregate_degree_closed_form,
    })
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct PowerTwoCyclotomicInteger(Vec<i128>);

impl PowerTwoCyclotomicInteger {
    fn zero(order: usize) -> Self {
        Self(vec![0; order / 2])
    }

    fn root_power(order: usize, exponent: usize) -> Self {
        let phi = order / 2;
        let reduced = exponent % order;
        let mut coefficients = vec![0; phi];
        if reduced < phi {
            coefficients[reduced] = 1;
        } else {
            coefficients[reduced - phi] = -1;
        }
        Self(coefficients)
    }

    fn add_assign(&mut self, other: &Self) -> Result<(), HayesError> {
        if self.0.len() != other.0.len() {
            return Err(HayesError::Invariant(
                "cyclotomic addition used incompatible bases".to_owned(),
            ));
        }
        for (left, right) in self.0.iter_mut().zip(&other.0) {
            *left = left.checked_add(*right).ok_or_else(|| {
                HayesError::InvalidParameter("cyclotomic coefficient overflow".to_owned())
            })?;
        }
        Ok(())
    }

    fn subtract_assign(&mut self, other: &Self) -> Result<(), HayesError> {
        if self.0.len() != other.0.len() {
            return Err(HayesError::Invariant(
                "cyclotomic subtraction used incompatible bases".to_owned(),
            ));
        }
        for (left, right) in self.0.iter_mut().zip(&other.0) {
            *left = left.checked_sub(*right).ok_or_else(|| {
                HayesError::InvalidParameter("cyclotomic coefficient overflow".to_owned())
            })?;
        }
        Ok(())
    }

    fn scale(&self, scalar: i128) -> Result<Self, HayesError> {
        self.0
            .iter()
            .map(|coefficient| {
                coefficient.checked_mul(scalar).ok_or_else(|| {
                    HayesError::InvalidParameter("cyclotomic scaling overflow".to_owned())
                })
            })
            .collect::<Result<Vec<_>, _>>()
            .map(Self)
    }

    fn conjugate(&self) -> Result<Self, HayesError> {
        let order = self.0.len() * 2;
        let mut conjugate = Self::zero(order);
        for (exponent, coefficient) in self.0.iter().copied().enumerate() {
            let root = Self::root_power(order, (order - exponent) % order).scale(coefficient)?;
            conjugate.add_assign(&root)?;
        }
        Ok(conjugate)
    }

    fn multiply(&self, other: &Self) -> Result<Self, HayesError> {
        if self.0.len() != other.0.len() {
            return Err(HayesError::Invariant(
                "cyclotomic multiplication used incompatible bases".to_owned(),
            ));
        }
        let phi = self.0.len();
        let mut product = vec![0_i128; phi];
        for (left_degree, left) in self.0.iter().copied().enumerate() {
            for (right_degree, right) in other.0.iter().copied().enumerate() {
                let raw = left.checked_mul(right).ok_or_else(|| {
                    HayesError::InvalidParameter("cyclotomic product overflow".to_owned())
                })?;
                let degree = left_degree + right_degree;
                let (slot, signed) = if degree < phi {
                    (degree, raw)
                } else {
                    (
                        degree - phi,
                        raw.checked_neg().ok_or_else(|| {
                            HayesError::InvalidParameter("cyclotomic product overflow".to_owned())
                        })?,
                    )
                };
                product[slot] = product[slot].checked_add(signed).ok_or_else(|| {
                    HayesError::InvalidParameter("cyclotomic product overflow".to_owned())
                })?;
            }
        }
        Ok(Self(product))
    }

    /// Valuation at the unique prime `(1-zeta)` above two.
    ///
    /// If `a=(1-zeta)b` in the basis `1,zeta,...,zeta^(e-1)`, where
    /// `zeta^e=-1`, then
    ///
    /// ```text
    /// a_0=b_0+b_(e-1),  a_i=b_i-b_(i-1).
    /// ```
    ///
    /// Thus divisibility is equivalent to
    /// `a_0-sum_(i>0)a_i` being even, and the quotient is recovered
    /// triangularly.  Repetition gives the exact valuation without choosing
    /// a floating-point embedding or factoring an integer norm.
    fn uniformizer_valuation(&self) -> Result<Option<usize>, HayesError> {
        if self.0.iter().all(|coefficient| *coefficient == 0) {
            return Ok(None);
        }
        let mut current = self.0.clone();
        let mut valuation = 0_usize;
        loop {
            let tail_sum = current
                .iter()
                .skip(1)
                .try_fold(0_i128, |sum, coefficient| {
                    sum.checked_add(*coefficient).ok_or_else(|| {
                        HayesError::InvalidParameter(
                            "cyclotomic uniformizer division overflow".to_owned(),
                        )
                    })
                })?;
            let numerator = current[0].checked_sub(tail_sum).ok_or_else(|| {
                HayesError::InvalidParameter("cyclotomic uniformizer division overflow".to_owned())
            })?;
            if numerator % 2 != 0 {
                return Ok(Some(valuation));
            }
            let mut quotient = vec![0_i128; current.len()];
            quotient[0] = numerator / 2;
            for index in 1..current.len() {
                quotient[index] =
                    quotient[index - 1]
                        .checked_add(current[index])
                        .ok_or_else(|| {
                            HayesError::InvalidParameter(
                                "cyclotomic uniformizer division overflow".to_owned(),
                            )
                        })?;
            }
            current = quotient;
            valuation = valuation.checked_add(1).ok_or_else(|| {
                HayesError::InvalidParameter("cyclotomic uniformizer valuation overflow".to_owned())
            })?;
        }
    }

    #[cfg(test)]
    fn field_norm(&self) -> Result<BigInt, HayesError> {
        let order = self.0.len() * 2;
        let columns = (0..self.0.len())
            .map(|column| {
                self.multiply(&Self::root_power(order, column))
                    .map(|product| product.0.into_iter().map(BigInt::from).collect::<Vec<_>>())
            })
            .collect::<Result<Vec<_>, _>>()?;
        let matrix = columns[0]
            .iter()
            .enumerate()
            .map(|(row, _)| columns.iter().map(|column| column[row].clone()).collect())
            .collect();
        integer_determinant_bareiss(matrix)
    }
}

fn two_adic_newton_slopes(
    coefficients: &[PowerTwoCyclotomicInteger],
) -> Result<Vec<HayesTwoAdicNewtonSlope>, HayesError> {
    let Some(first) = coefficients.first() else {
        return Err(HayesError::InvalidParameter(
            "Newton polygon requires a nonempty coefficient vector".to_owned(),
        ));
    };
    let ramification_index = first.0.len();
    let mut hull = Vec::<(usize, usize)>::new();
    for (degree, coefficient) in coefficients.iter().enumerate() {
        let Some(valuation) = coefficient.uniformizer_valuation()? else {
            continue;
        };
        while hull.len() >= 2 {
            let (left_degree, left_value) = hull[hull.len() - 2];
            let (middle_degree, middle_value) = hull[hull.len() - 1];
            let left_rise = i128::try_from(middle_value)
                .and_then(|middle| i128::try_from(left_value).map(|left| middle - left))
                .map_err(|_| {
                    HayesError::InvalidParameter("Newton valuation does not fit i128".to_owned())
                })?;
            let right_rise = i128::try_from(valuation)
                .and_then(|right| i128::try_from(middle_value).map(|middle| right - middle))
                .map_err(|_| {
                    HayesError::InvalidParameter("Newton valuation does not fit i128".to_owned())
                })?;
            let left_run = i128::try_from(middle_degree - left_degree).map_err(|_| {
                HayesError::InvalidParameter("Newton segment does not fit i128".to_owned())
            })?;
            let right_run = i128::try_from(degree - middle_degree).map_err(|_| {
                HayesError::InvalidParameter("Newton segment does not fit i128".to_owned())
            })?;
            if left_rise.checked_mul(right_run).ok_or_else(|| {
                HayesError::InvalidParameter("Newton cross product overflow".to_owned())
            })? < right_rise.checked_mul(left_run).ok_or_else(|| {
                HayesError::InvalidParameter("Newton cross product overflow".to_owned())
            })? {
                break;
            }
            hull.pop();
        }
        hull.push((degree, valuation));
    }
    if hull.first().map(|point| point.0) != Some(0)
        || hull.last().map(|point| point.0) != Some(coefficients.len() - 1)
    {
        return Err(HayesError::Invariant(
            "Newton polygon omits a nonzero endpoint coefficient".to_owned(),
        ));
    }
    hull.windows(2)
        .map(|segment| {
            let horizontal = segment[1].0 - segment[0].0;
            let vertical = segment[1].1.checked_sub(segment[0].1).ok_or_else(|| {
                HayesError::Invariant("Newton polygon has a negative slope".to_owned())
            })?;
            let denominator = ramification_index.checked_mul(horizontal).ok_or_else(|| {
                HayesError::InvalidParameter("Newton slope denominator overflow".to_owned())
            })?;
            let common = gcd_usize(vertical, denominator);
            Ok(HayesTwoAdicNewtonSlope {
                numerator: vertical / common,
                denominator: denominator / common,
                multiplicity: horizontal,
            })
        })
        .collect()
}

fn character_root_exponent(
    mut character: usize,
    mut class: usize,
    factors: &[PrincipalUnitFactor],
    order: usize,
) -> Result<usize, HayesError> {
    let mut exponent = 0_usize;
    for factor in factors {
        let character_coordinate = character % factor.order;
        let class_coordinate = class % factor.order;
        character /= factor.order;
        class /= factor.order;
        let term = character_coordinate
            .checked_mul(class_coordinate)
            .and_then(|value| value.checked_mul(order / factor.order))
            .ok_or_else(|| {
                HayesError::InvalidParameter("cyclotomic exponent overflow".to_owned())
            })?;
        exponent = exponent.checked_add(term).ok_or_else(|| {
            HayesError::InvalidParameter("cyclotomic exponent overflow".to_owned())
        })? % order;
    }
    if character != 0 || class != 0 {
        return Err(HayesError::Invariant(
            "cyclotomic character evaluation left unused coordinates".to_owned(),
        ));
    }
    Ok(exponent)
}

fn exact_character_l_coefficients(
    level: usize,
    character: usize,
) -> Result<(usize, Vec<PowerTwoCyclotomicInteger>), HayesError> {
    let factors = principal_unit_factors(level);
    let order = factors.iter().map(|factor| factor.order).max().unwrap_or(1);
    let mut unit_to_index = BTreeMap::new();
    for index in 0..(1_usize << level) {
        let mut quotient = index;
        let mut unit = 1_u64;
        for factor in &factors {
            let coordinate = quotient % factor.order;
            quotient /= factor.order;
            let generator = 1 | (1_u64 << factor.odd_degree);
            for _ in 0..coordinate {
                unit = unit_multiply(unit, generator, level);
            }
        }
        if unit_to_index.insert(unit, index).is_some() {
            return Err(HayesError::Invariant(format!(
                "level {level}: exact cyclotomic class decomposition is not injective"
            )));
        }
    }
    if unit_to_index.len() != 1_usize << level {
        return Err(HayesError::Invariant(format!(
            "level {level}: exact cyclotomic class decomposition is incomplete"
        )));
    }
    let mut coefficients = Vec::with_capacity(level);
    coefficients.push(PowerTwoCyclotomicInteger::root_power(order, 0));
    for polynomial_degree in 1..level {
        let mut coefficient = PowerTwoCyclotomicInteger::zero(order);
        for tail in 0..(1_u64 << polynomial_degree) {
            let unit = 1 | (tail << 1);
            let class = unit_to_index[&unit];
            let exponent = character_root_exponent(character, class, &factors, order)?;
            coefficient.add_assign(&PowerTwoCyclotomicInteger::root_power(order, exponent))?;
        }
        coefficients.push(coefficient);
    }
    Ok((order, coefficients))
}

fn validate_primitive_functional_equation(
    coefficients: &[PowerTwoCyclotomicInteger],
) -> Result<(), HayesError> {
    let l_degree = coefficients.len() - 1;
    let leading = &coefficients[l_degree];
    for coefficient_degree in 0..=l_degree {
        let scale = 1_i128
            .checked_shl(u32::try_from(coefficient_degree).map_err(|_| {
                HayesError::InvalidParameter(
                    "functional-equation coefficient degree exceeds u32".to_owned(),
                )
            })?)
            .ok_or_else(|| {
                HayesError::InvalidParameter(
                    "functional-equation power of two exceeds i128".to_owned(),
                )
            })?;
        let left = coefficients[l_degree - coefficient_degree].scale(scale)?;
        let right = leading.multiply(&coefficients[coefficient_degree].conjugate()?)?;
        if left != right {
            return Err(HayesError::Invariant(format!(
                "primitive Hayes functional equation failed at coefficient {coefficient_degree}"
            )));
        }
    }
    Ok(())
}

fn logarithmic_power_sum(
    coefficients: &[PowerTwoCyclotomicInteger],
    degree: usize,
) -> Result<PowerTwoCyclotomicInteger, HayesError> {
    let order = coefficients
        .first()
        .map_or(2, |coefficient| coefficient.0.len() * 2);
    let mut powers = vec![PowerTwoCyclotomicInteger::zero(order); degree + 1];
    for current in 1..=degree {
        let mut value = if current < coefficients.len() {
            let mut scaled = PowerTwoCyclotomicInteger::zero(order);
            for _ in 0..current {
                scaled.add_assign(&coefficients[current])?;
            }
            scaled
        } else {
            PowerTwoCyclotomicInteger::zero(order)
        };
        for (earlier, earlier_power) in powers.iter().enumerate().take(current).skip(1) {
            let coefficient_degree = current - earlier;
            if coefficient_degree >= coefficients.len() {
                continue;
            }
            value.subtract_assign(&earlier_power.multiply(&coefficients[coefficient_degree])?)?;
        }
        powers[current] = value;
    }
    Ok(powers.swap_remove(degree))
}

fn cyclotomic_integer_residue(
    value: &PowerTwoCyclotomicInteger,
    modulus: u64,
) -> Result<u64, HayesError> {
    let order = value.0.len() * 2;
    if !(modulus - 1).is_multiple_of(order as u64) {
        return Err(HayesError::Invariant(
            "audit prime does not contain the required cyclotomic roots".to_owned(),
        ));
    }
    let root = mod_pow(PRIMITIVE_ROOT, (modulus - 1) / order as u64, modulus);
    let mut result = 0_u64;
    let mut power = 1_u64;
    for coefficient in &value.0 {
        let reduced = u64::try_from(coefficient.rem_euclid(i128::from(modulus))).map_err(|_| {
            HayesError::Invariant("reduced cyclotomic coefficient does not fit u64".to_owned())
        })?;
        result = add_mod(result, multiply_mod(reduced, power, modulus), modulus);
        power = multiply_mod(power, root, modulus);
    }
    Ok(result)
}

/// Group primitive Hayes characters by their exact leading `L`-coefficient
/// and compare a high logarithmic power sum within each group.
///
/// The functional equation determines the root number from that leading
/// coefficient.  A returned witness therefore proves that root-number data
/// alone cannot recover the endpoint trace.  This is a bounded obstruction,
/// not a bound on the connected character sum.
///
/// # Errors
///
/// Rejects levels below two, generic transform-limit violations, a quadratic
/// exact-enumeration work estimate above `limits.max_table_cells`, and
/// arithmetic overflow in the integral cyclotomic ring.
pub fn hayes_root_number_fibre_report(
    level: usize,
    degree: usize,
    limits: HayesLimits,
) -> Result<HayesRootNumberFibreReport, HayesError> {
    if level < 2 || degree == 0 {
        return Err(HayesError::InvalidParameter(
            "root-number fibre audit requires level at least two and positive degree".to_owned(),
        ));
    }
    admit(level, degree, limits)?;
    let group_order = 1_usize << level;
    let exact_work_cells = group_order.checked_mul(group_order).ok_or_else(|| {
        HayesError::InvalidParameter("root-number fibre work estimate overflow".to_owned())
    })?;
    check_limit(
        "root_number_fibre_cells",
        exact_work_cells,
        limits.max_table_cells,
    )?;
    let factors = principal_unit_factors(level);
    let (prime_one_powers, _) = character_power_sums_residue(level, degree, PRIME_ONE)?;
    let (prime_two_powers, _) = character_power_sums_residue(level, degree, PRIME_TWO)?;
    let mut fibres =
        BTreeMap::<PowerTwoCyclotomicInteger, Vec<(usize, PowerTwoCyclotomicInteger)>>::new();
    for character in 1..group_order {
        if mixed_radix_character_conductor(character, &factors)? != Some(level) {
            continue;
        }
        let (_, coefficients) = exact_character_l_coefficients(level, character)?;
        validate_primitive_functional_equation(&coefficients)?;
        let leading = coefficients[level - 1].clone();
        let power = logarithmic_power_sum(&coefficients, degree)?;
        if cyclotomic_integer_residue(&power, PRIME_ONE)? != prime_one_powers[character]
            || cyclotomic_integer_residue(&power, PRIME_TWO)? != prime_two_powers[character]
        {
            return Err(HayesError::Invariant(format!(
                "exact cyclotomic power sum disagrees with both-prime transform at character {character}"
            )));
        }
        fibres.entry(leading).or_default().push((character, power));
    }
    let mut varying_power_sum_fibre_count = 0_usize;
    let mut witness = None;
    for (leading, entries) in &fibres {
        let Some((left_character, left_power)) = entries.first() else {
            continue;
        };
        if let Some((right_character, right_power)) = entries
            .iter()
            .skip(1)
            .find(|(_, power)| power != left_power)
        {
            varying_power_sum_fibre_count += 1;
            if witness.is_none() {
                witness = Some(HayesRootNumberFibreWitness {
                    level,
                    degree,
                    cyclotomic_order: leading.0.len() * 2,
                    left_character: *left_character,
                    right_character: *right_character,
                    common_leading_coefficient: leading.0.clone(),
                    left_power_sum: left_power.0.clone(),
                    right_power_sum: right_power.0.clone(),
                });
            }
        }
    }
    let primitive_character_count = fibres.values().map(Vec::len).sum();
    Ok(HayesRootNumberFibreReport {
        level,
        degree,
        primitive_character_count,
        leading_coefficient_fibre_count: fibres.len(),
        varying_power_sum_fibre_count,
        witness,
    })
}

fn mixed_radix_character_order(
    mut character: usize,
    factors: &[PrincipalUnitFactor],
) -> Result<usize, HayesError> {
    let mut order = 1_usize;
    for factor in factors {
        let coordinate = character % factor.order;
        character /= factor.order;
        if coordinate == 0 {
            continue;
        }
        let coordinate_valuation = 1_usize << coordinate.trailing_zeros();
        order = order.max(factor.order / coordinate_valuation);
    }
    if character != 0 {
        return Err(HayesError::Invariant(
            "character-order calculation left unused coordinates".to_owned(),
        ));
    }
    Ok(order)
}

fn primitive_two_adic_newton_rows(
    level: usize,
    factors: &[PrincipalUnitFactor],
    cyclotomic_order: usize,
) -> Result<Vec<HayesCharacterTwoAdicNewtonRow>, HayesError> {
    let group_order = 1_usize << level;
    let mut characters = Vec::with_capacity(1_usize << (level - 1));
    for character in 1..group_order {
        if mixed_radix_character_conductor(character, factors)? != Some(level) {
            continue;
        }
        let (coefficient_order, coefficients) = exact_character_l_coefficients(level, character)?;
        if coefficient_order != cyclotomic_order {
            return Err(HayesError::Invariant(
                "primitive character changed the ambient cyclotomic order".to_owned(),
            ));
        }
        validate_primitive_functional_equation(&coefficients)?;
        let coefficient_uniformizer_valuations = coefficients
            .iter()
            .map(PowerTwoCyclotomicInteger::uniformizer_valuation)
            .collect::<Result<Vec<_>, _>>()?;
        let slopes = two_adic_newton_slopes(&coefficients)?;
        if slopes.iter().map(|slope| slope.multiplicity).sum::<usize>() != level - 1 {
            return Err(HayesError::Invariant(
                "Newton slopes do not cover the primitive L-degree".to_owned(),
            ));
        }
        characters.push(HayesCharacterTwoAdicNewtonRow {
            character,
            character_order: mixed_radix_character_order(character, factors)?,
            coefficient_uniformizer_valuations,
            slopes,
        });
    }
    Ok(characters)
}

/// Compute every primitive-character `2`-adic Newton polygon at one exact
/// Hayes conductor and compare its minimum slope with the integral conductor
/// trace.
///
/// The coefficient field is `Q(zeta_(2^r))`, where two is totally ramified
/// and `(1-zeta)` is its unique uniformizer.  Coefficient valuations are
/// obtained by exact repeated division in the integral cyclotomic basis.  A
/// lower convex hull then gives slopes normalized by
/// `v_2(2)=1`.  No complex or floating-point root approximation is used.
///
/// This is a bounded diagnostic for the normalized odd-endpoint congruence.
/// It identifies which positive Newton slopes can survive a requested
/// Frobenius power, but it does not prove a uniform slope distribution or the
/// cancellation among minimal-slope character orbits.
///
/// # Errors
///
/// Rejects levels below two, zero Frobenius degree, transform-limit or exact
/// enumeration work excess, arithmetic overflow, a malformed Newton polygon,
/// or disagreement with the independent exact conductor trace.
pub fn hayes_conductor_two_adic_newton_report(
    level: usize,
    degree: usize,
    limits: HayesLimits,
) -> Result<HayesConductorTwoAdicNewtonReport, HayesError> {
    if level < 2 || degree == 0 {
        return Err(HayesError::InvalidParameter(
            "two-adic Newton audit requires level at least two and positive degree".to_owned(),
        ));
    }
    admit(level, degree, limits)?;
    let group_order = 1_usize << level;
    let primitive_character_count = 1_usize << (level - 1);
    let exact_work_cells = primitive_character_count
        .checked_mul(group_order)
        .and_then(|value| value.checked_mul(level))
        .ok_or_else(|| {
            HayesError::InvalidParameter("two-adic Newton work estimate overflow".to_owned())
        })?;
    check_limit(
        "hayes_two_adic_newton_cells",
        exact_work_cells,
        limits.max_table_cells,
    )?;
    let factors = principal_unit_factors(level);
    let cyclotomic_order = factors.iter().map(|factor| factor.order).max().unwrap_or(2);
    let two_adic_ramification_index = cyclotomic_order / 2;
    let characters = primitive_two_adic_newton_rows(level, &factors, cyclotomic_order)?;
    if characters.len() != primitive_character_count {
        return Err(HayesError::Invariant(format!(
            "two-adic Newton audit found {} primitive characters, expected {primitive_character_count}",
            characters.len()
        )));
    }

    let minimum = characters
        .iter()
        .filter_map(|row| row.slopes.first().copied())
        .min_by(|left, right| {
            let left_cross = (left.numerator as u128) * (right.denominator as u128);
            let right_cross = (right.numerator as u128) * (left.denominator as u128);
            left_cross.cmp(&right_cross)
        })
        .ok_or_else(|| HayesError::Invariant("Newton audit has no slopes".to_owned()))?;
    let minimum_slope_multiplicity = characters
        .iter()
        .filter_map(|row| row.slopes.first())
        .filter(|slope| {
            (slope.numerator as u128) * (minimum.denominator as u128)
                == (minimum.numerator as u128) * (slope.denominator as u128)
        })
        .map(|slope| slope.multiplicity)
        .sum();
    let scaled_minimum = degree.checked_mul(minimum.numerator).ok_or_else(|| {
        HayesError::InvalidParameter("Newton power valuation overflow".to_owned())
    })?;
    let minimum_power_valuation_ceiling = scaled_minimum
        .checked_add(minimum.denominator - 1)
        .ok_or_else(|| {
            HayesError::InvalidParameter("Newton power valuation overflow".to_owned())
        })?
        / minimum.denominator;
    let direct_conductor_trace = conductor_layers(level, degree, limits)?[level - 1].value;
    let direct_conductor_trace_two_adic_valuation = (direct_conductor_trace != 0)
        .then_some(direct_conductor_trace.unsigned_abs().trailing_zeros());
    let minimum_power_valuation_ceiling_u32 = u32::try_from(minimum_power_valuation_ceiling)
        .map_err(|_| {
            HayesError::InvalidParameter("Newton power valuation does not fit u32".to_owned())
        })?;
    if direct_conductor_trace_two_adic_valuation
        .is_some_and(|valuation| valuation < minimum_power_valuation_ceiling_u32)
    {
        return Err(HayesError::Invariant(
            "exact conductor trace lies below its Newton-slope valuation floor".to_owned(),
        ));
    }

    Ok(HayesConductorTwoAdicNewtonReport {
        level,
        degree,
        cyclotomic_order,
        two_adic_ramification_index,
        primitive_character_count,
        characters,
        minimum_slope_numerator: minimum.numerator,
        minimum_slope_denominator: minimum.denominator,
        minimum_slope_multiplicity,
        minimum_power_valuation_ceiling,
        direct_conductor_trace,
        direct_conductor_trace_two_adic_valuation,
    })
}

fn signed_crt_residue(first: u64, second: u64) -> Result<i128, HayesError> {
    let value = crt(first, PRIME_ONE, second, PRIME_TWO)?;
    let modulus = u128::from(PRIME_ONE) * u128::from(PRIME_TWO);
    let value = i128::try_from(value).map_err(|_| {
        HayesError::InvalidParameter("signed CRT value does not fit i128".to_owned())
    })?;
    if value
        > i128::try_from(modulus / 2).map_err(|_| {
            HayesError::InvalidParameter("signed CRT midpoint does not fit i128".to_owned())
        })?
    {
        value
            .checked_sub(i128::try_from(modulus).map_err(|_| {
                HayesError::InvalidParameter("signed CRT modulus does not fit i128".to_owned())
            })?)
            .ok_or_else(|| HayesError::InvalidParameter("signed CRT underflow".to_owned()))
    } else {
        Ok(value)
    }
}

struct RawGaloisOrbitTraces {
    primitive_character_count: usize,
    orbit_count: usize,
    maximum_absolute_orbit_trace: u128,
    candidate_violation_count: usize,
    reconstructed_conductor_trace: i128,
    orders: BTreeMap<usize, (usize, u128, i128)>,
}

fn raw_galois_orbit_traces(
    level: usize,
    factors: &[PrincipalUnitFactor],
    candidate_orbit_allowance: u128,
    prime_one_powers: &[u64],
    prime_two_powers: &[u64],
) -> Result<RawGaloisOrbitTraces, HayesError> {
    let group_order = 1_usize << level;
    let group_exponent = factors.iter().map(|factor| factor.order).max().unwrap_or(1);
    let crt_modulus = u128::from(PRIME_ONE) * u128::from(PRIME_TWO);
    let mut visited = BTreeSet::new();
    let mut orders = BTreeMap::<usize, (usize, u128, i128)>::new();
    let mut orbit_count = 0_usize;
    let mut maximum_absolute_orbit_trace = 0_u128;
    let mut candidate_violation_count = 0_usize;
    let mut reconstructed_conductor_trace = 0_i128;
    for character in 1..group_order {
        if visited.contains(&character)
            || mixed_radix_character_conductor(character, factors)? != Some(level)
        {
            continue;
        }
        let character_order = mixed_radix_character_order(character, factors)?;
        let mut orbit = BTreeSet::new();
        for multiplier in (1..group_exponent).step_by(2) {
            orbit.insert(power_mixed_radix_index(character, multiplier, factors)?);
        }
        if orbit.len() != character_order / 2 {
            return Err(HayesError::Invariant(format!(
                "character {character}: Galois orbit has the wrong size"
            )));
        }
        for member in &orbit {
            if mixed_radix_character_conductor(*member, factors)? != Some(level) {
                return Err(HayesError::Invariant(format!(
                    "character {character}: Galois orbit changes conductor"
                )));
            }
        }
        visited.extend(orbit.iter().copied());
        let first = orbit.iter().fold(0_u64, |sum, member| {
            add_mod(sum, prime_one_powers[*member], PRIME_ONE)
        });
        let second = orbit.iter().fold(0_u64, |sum, member| {
            add_mod(sum, prime_two_powers[*member], PRIME_TWO)
        });
        let trace = signed_crt_residue(first, second)?;
        let ordinary_bound = candidate_orbit_allowance
            .checked_mul((level - 1) as u128)
            .and_then(|value| value.checked_mul(orbit.len() as u128))
            .ok_or_else(|| HayesError::InvalidParameter("orbit Weil bound overflow".to_owned()))?;
        if ordinary_bound
            .checked_mul(2)
            .is_none_or(|twice| twice >= crt_modulus)
            || trace.unsigned_abs() > ordinary_bound
        {
            return Err(HayesError::InvalidParameter(format!(
                "character {character}: orbit trace is not uniquely certified by the CRT Weil envelope"
            )));
        }
        let magnitude = trace.unsigned_abs();
        maximum_absolute_orbit_trace = maximum_absolute_orbit_trace.max(magnitude);
        candidate_violation_count += usize::from(magnitude > candidate_orbit_allowance);
        reconstructed_conductor_trace = reconstructed_conductor_trace
            .checked_add(trace)
            .ok_or_else(|| HayesError::InvalidParameter("conductor trace overflow".to_owned()))?;
        let row = orders.entry(character_order).or_default();
        row.0 += 1;
        row.1 = row.1.max(magnitude);
        row.2 = row
            .2
            .checked_add(trace)
            .ok_or_else(|| HayesError::InvalidParameter("order-layer trace overflow".to_owned()))?;
        orbit_count += 1;
    }
    Ok(RawGaloisOrbitTraces {
        primitive_character_count: visited.len(),
        orbit_count,
        maximum_absolute_orbit_trace,
        candidate_violation_count,
        reconstructed_conductor_trace,
        orders,
    })
}

/// Decompose one exact-conductor Hayes trace into rational Galois orbits.
///
/// Odd powers act on a power-of-two-valued character through the Galois group
/// of its cyclotomic value field.  Summing each orbit is therefore an exact
/// integer Ramanujan projection.  The report tests the theorem candidate
///
/// ```text
/// abs(sum_(chi in orbit) S_degree(chi)) <= 2^ceil(degree/2)
/// ```
///
/// without extrapolating a passing finite row into a universal estimate.
/// Two independent transform primes reconstruct every signed orbit trace, and
/// their total must reproduce the independently computed conductor layer.
///
/// # Errors
///
/// Propagates transform admission failures and declines if the ordinary
/// characterwise Weil envelope is too large for unique signed CRT recovery.
pub fn hayes_galois_orbit_trace_report(
    level: usize,
    degree: usize,
    limits: HayesLimits,
) -> Result<HayesGaloisOrbitTraceReport, HayesError> {
    if level < 2 {
        return Err(HayesError::InvalidParameter(
            "Galois-orbit trace audit requires level at least two".to_owned(),
        ));
    }
    admit(level, degree, limits)?;
    let factors = principal_unit_factors(level);
    let candidate_shift = u32::try_from(degree.div_ceil(2)).map_err(|_| {
        HayesError::InvalidParameter("orbit allowance shift exceeds u32".to_owned())
    })?;
    let candidate_orbit_allowance = 1_u128
        .checked_shl(candidate_shift)
        .ok_or_else(|| HayesError::InvalidParameter("orbit allowance exceeds u128".to_owned()))?;
    let (prime_one_powers, _) = character_power_sums_residue(level, degree, PRIME_ONE)?;
    let (prime_two_powers, _) = character_power_sums_residue(level, degree, PRIME_TWO)?;
    let raw = raw_galois_orbit_traces(
        level,
        &factors,
        candidate_orbit_allowance,
        &prime_one_powers,
        &prime_two_powers,
    )?;
    let primitive_character_count = raw.primitive_character_count;
    if primitive_character_count != 1_usize << (level - 1) {
        return Err(HayesError::Invariant(
            "Galois orbits do not partition the primitive character family".to_owned(),
        ));
    }
    let orbit_count = raw.orbit_count;
    let maximum_absolute_orbit_trace = raw.maximum_absolute_orbit_trace;
    let candidate_violation_count = raw.candidate_violation_count;
    let reconstructed_conductor_trace = raw.reconstructed_conductor_trace;
    let direct_conductor_trace = conductor_layers(level, degree, limits)?[level - 1].value;
    if reconstructed_conductor_trace != direct_conductor_trace {
        return Err(HayesError::Invariant(format!(
            "Galois orbit sum {reconstructed_conductor_trace} does not recover conductor trace {direct_conductor_trace}"
        )));
    }
    let order_layer_base_allowance = candidate_orbit_allowance
        .checked_mul((level - 1) as u128)
        .ok_or_else(|| HayesError::InvalidParameter("order-layer allowance overflow".to_owned()))?;
    let order_layer_candidate_allowance = order_layer_base_allowance
        .checked_mul(4)
        .ok_or_else(|| HayesError::InvalidParameter("order-layer allowance overflow".to_owned()))?;
    let orders = raw
        .orders
        .into_iter()
        .map(
            |(character_order, (orbit_count, maximum_absolute_trace, signed_trace_sum))| {
                HayesGaloisOrbitOrderRow {
                    character_order,
                    orbit_count,
                    maximum_absolute_trace,
                    signed_trace_sum,
                }
            },
        )
        .collect::<Vec<_>>();
    let maximum_absolute_order_layer_trace = orders
        .iter()
        .map(|row| row.signed_trace_sum.unsigned_abs())
        .max()
        .unwrap_or(0);
    let order_layer_candidate_violation_count = orders
        .iter()
        .filter(|row| row.signed_trace_sum.unsigned_abs() > order_layer_candidate_allowance)
        .count();
    let required_order_layer_coefficient =
        maximum_absolute_order_layer_trace.div_ceil(order_layer_base_allowance);
    Ok(HayesGaloisOrbitTraceReport {
        level,
        degree,
        primitive_character_count,
        orbit_count,
        candidate_orbit_allowance,
        maximum_absolute_orbit_trace,
        candidate_violation_count,
        order_layer_candidate_allowance,
        maximum_absolute_order_layer_trace,
        order_layer_candidate_violation_count,
        required_order_layer_coefficient,
        reconstructed_conductor_trace,
        direct_conductor_trace,
        orders,
    })
}

/// Group primitive Hayes traces through Fomenko's restriction map and Galois.
///
/// Let `H_t` be the subgroup of principal units congruent to one modulo
/// `x^(t+1)`, where `t=restriction_level`.  Restriction from the character
/// group of `E_level` to `H_t^dual` is surjective and has kernel equal to the
/// inflated character group of `E_t`, of size `2^t`.  Kernel translation
/// preserves exact conductor above `t`.  Since an individual restriction
/// fibre is generally cyclotomic rather than rational, this operation takes
/// its full odd-power Galois closure before exact integer reconstruction.
///
/// The report tests the strongest useful finite candidate
///
/// ```text
/// abs(sum_(psi in packet(chi)) S_degree(psi)) <= 2^ceil(degree/2).
/// ```
///
/// It does not extrapolate a passing row.  Every signed packet trace is
/// reconstructed from two independent transform primes, certified against
/// the ordinary packetwise Weil envelope, and the signed total must equal
/// the independently computed exact-conductor layer.
///
/// # Errors
///
/// Propagates transform admission failures and declines if the CRT modulus is
/// too small for unique reconstruction under the ordinary Weil envelope.
#[allow(clippy::too_many_lines)]
pub fn hayes_fomenko_restriction_packet_report(
    level: usize,
    restriction_level: usize,
    degree: usize,
    limits: HayesLimits,
) -> Result<HayesFomenkoRestrictionPacketReport, HayesError> {
    if level < 2 || restriction_level == 0 || restriction_level >= level {
        return Err(HayesError::InvalidParameter(
            "Fomenko restriction audit requires 1<=restriction_level<level".to_owned(),
        ));
    }
    admit(level, degree, limits)?;
    let factors = principal_unit_factors(level);
    let source_factors = principal_unit_factors(restriction_level);
    let restriction_kernel_size = 1_usize << restriction_level;
    let mut kernel_characters = Vec::with_capacity(restriction_kernel_size);
    for source_character in 0..restriction_kernel_size {
        let character =
            verschiebung_embed_mixed_radix_index(source_character, &source_factors, &factors)?;
        if mixed_radix_character_conductor(character, &factors)?
            .is_some_and(|conductor| conductor > restriction_level)
        {
            return Err(HayesError::Invariant(
                "restriction kernel contains a character above its quotient level".to_owned(),
            ));
        }
        kernel_characters.push(character);
    }

    let shift = u32::try_from(degree.div_ceil(2)).map_err(|_| {
        HayesError::InvalidParameter("Fomenko allowance shift exceeds u32".to_owned())
    })?;
    let square_root_allowance = 1_u128.checked_shl(shift).ok_or_else(|| {
        HayesError::InvalidParameter("Fomenko square-root allowance exceeds u128".to_owned())
    })?;
    let ordinary_family_bound = square_root_allowance
        .checked_mul((level - 1) as u128)
        .and_then(|value| value.checked_mul(1_u128 << (level - 1)))
        .ok_or_else(|| HayesError::InvalidParameter("Fomenko Weil envelope overflow".to_owned()))?;
    let crt_modulus = u128::from(PRIME_ONE) * u128::from(PRIME_TWO);
    if ordinary_family_bound
        .checked_mul(2)
        .is_none_or(|width| width >= crt_modulus)
    {
        return Err(HayesError::InvalidParameter(
            "Fomenko packet traces are not uniquely certified by the CRT Weil envelope".to_owned(),
        ));
    }

    let group_order = 1_usize << level;
    let group_exponent = factors.iter().map(|factor| factor.order).max().unwrap_or(1);
    let packet_work = group_order
        .checked_mul(restriction_kernel_size)
        .and_then(|value| value.checked_mul(group_exponent))
        .ok_or_else(|| HayesError::InvalidParameter("Fomenko packet work overflow".to_owned()))?;
    check_limit(
        "fomenko_restriction_packet_cells",
        packet_work,
        limits.max_table_cells,
    )?;
    let (prime_one_powers, _) = character_power_sums_residue(level, degree, PRIME_ONE)?;
    let (prime_two_powers, _) = character_power_sums_residue(level, degree, PRIME_TWO)?;
    let mut visited = BTreeSet::new();
    let mut packet_count = 0_usize;
    let mut maximum_packet_size = 0_usize;
    let mut maximum_absolute_packet_trace = 0_u128;
    let mut packetwise_absolute_trace = 0_u128;
    let mut square_root_violation_count = 0_usize;
    let mut reconstructed_conductor_trace = 0_i128;
    for character in 0..group_order {
        if visited.contains(&character)
            || mixed_radix_character_conductor(character, &factors)? != Some(level)
        {
            continue;
        }
        let mut packet = BTreeSet::new();
        for multiplier in (1..group_exponent).step_by(2) {
            let conjugate = power_mixed_radix_index(character, multiplier, &factors)?;
            for kernel_character in &kernel_characters {
                packet.insert(add_mixed_radix_indices(
                    conjugate,
                    *kernel_character,
                    &factors,
                )?);
            }
        }
        for member in &packet {
            if mixed_radix_character_conductor(*member, &factors)? != Some(level) {
                return Err(HayesError::Invariant(
                    "Fomenko packet does not preserve the primitive level".to_owned(),
                ));
            }
        }
        visited.extend(packet.iter().copied());
        let first = packet.iter().fold(0_u64, |sum, member| {
            add_mod(sum, prime_one_powers[*member], PRIME_ONE)
        });
        let second = packet.iter().fold(0_u64, |sum, member| {
            add_mod(sum, prime_two_powers[*member], PRIME_TWO)
        });
        let trace = signed_crt_residue(first, second)?;
        let ordinary_packet_bound = square_root_allowance
            .checked_mul((level - 1) as u128)
            .and_then(|value| value.checked_mul(packet.len() as u128))
            .ok_or_else(|| {
                HayesError::InvalidParameter("Fomenko packet envelope overflow".to_owned())
            })?;
        if trace.unsigned_abs() > ordinary_packet_bound {
            return Err(HayesError::Invariant(format!(
                "level={level}, degree={degree}, character={character}: Fomenko packet trace {trace} exceeds ordinary Weil envelope {ordinary_packet_bound}"
            )));
        }
        let magnitude = trace.unsigned_abs();
        maximum_packet_size = maximum_packet_size.max(packet.len());
        maximum_absolute_packet_trace = maximum_absolute_packet_trace.max(magnitude);
        packetwise_absolute_trace = packetwise_absolute_trace
            .checked_add(magnitude)
            .ok_or_else(|| {
                HayesError::InvalidParameter("Fomenko absolute total overflow".to_owned())
            })?;
        square_root_violation_count += usize::from(magnitude > square_root_allowance);
        reconstructed_conductor_trace = reconstructed_conductor_trace
            .checked_add(trace)
            .ok_or_else(|| {
                HayesError::InvalidParameter("Fomenko trace total overflow".to_owned())
            })?;
        packet_count += 1;
    }
    let primitive_character_count = visited.len();
    if primitive_character_count != 1_usize << (level - 1) {
        return Err(HayesError::Invariant(
            "Fomenko packets do not partition the primitive character family".to_owned(),
        ));
    }
    let direct_conductor_trace = conductor_layers(level, degree, limits)?[level - 1].value;
    if reconstructed_conductor_trace != direct_conductor_trace {
        return Err(HayesError::Invariant(format!(
            "Fomenko packet sum {reconstructed_conductor_trace} does not recover conductor trace {direct_conductor_trace}"
        )));
    }
    Ok(HayesFomenkoRestrictionPacketReport {
        level,
        restriction_level,
        degree,
        restriction_kernel_size,
        primitive_character_count,
        packet_count,
        maximum_packet_size,
        square_root_allowance,
        maximum_absolute_packet_trace,
        packetwise_absolute_trace,
        square_root_violation_count,
        required_square_root_coefficient: maximum_absolute_packet_trace
            .div_ceil(square_root_allowance),
        reconstructed_conductor_trace,
        direct_conductor_trace,
    })
}

/// Count how much of one primitive Hayes layer can possibly be reached by
/// binary monomial power-sum characters and their products.
///
/// The special character used by Gorodetsky--Kovaleva takes values through
/// the unique nontrivial additive character of `GF(2)`, hence has order two.
/// Its conductor is `x^(k+1)` only for odd `k`; for even `k`, Frobenius gives
/// `p_(-k)=p_(-k/2)` after repeatedly removing powers of two.  Consequently
/// there is one primitive single-monomial character at odd level and none at
/// even level, while the span of every such character is contained in the
/// quadratic subgroup.
///
/// The routine independently enumerates the mixed-radix character group and
/// checks the closed-form primitive quadratic count: `2^((level-1)/2)` for
/// odd level and zero for even level.  It is a representation audit, not a
/// character-sum estimate.
///
/// # Errors
///
/// Returns a resource decline outside the caller's level limit, a parameter
/// error at level zero, or an invariant failure if enumeration disagrees with
/// the group-theoretic count.
pub fn hayes_power_sum_character_coverage(
    level: usize,
    limits: HayesLimits,
) -> Result<HayesPowerSumCharacterCoverage, HayesError> {
    if level == 0 {
        return Err(HayesError::InvalidParameter(
            "power-sum character coverage requires positive level".to_owned(),
        ));
    }
    check_limit("ell", level, limits.max_ell)?;
    let shift = u32::try_from(level).map_err(|_| {
        HayesError::InvalidParameter("power-sum coverage level exceeds u32".to_owned())
    })?;
    let group_order = 1_usize.checked_shl(shift).ok_or_else(|| {
        HayesError::InvalidParameter("power-sum coverage group order overflow".to_owned())
    })?;
    check_limit("group_order", group_order, limits.max_group_order)?;
    let factors = principal_unit_factors(level);
    let mut primitive_character_count = 0_usize;
    let mut primitive_quadratic_character_count = 0_usize;
    for character in 1..group_order {
        if mixed_radix_character_conductor(character, &factors)? != Some(level) {
            continue;
        }
        primitive_character_count += 1;
        if mixed_radix_character_order(character, &factors)? == 2 {
            primitive_quadratic_character_count += 1;
        }
    }
    let expected_primitive = 1_usize << (level - 1);
    if primitive_character_count != expected_primitive {
        return Err(HayesError::Invariant(format!(
            "level {level}: primitive character count {primitive_character_count} != {expected_primitive}"
        )));
    }
    let expected_quadratic = if level % 2 == 1 {
        1_usize << ((level - 1) / 2)
    } else {
        0
    };
    if primitive_quadratic_character_count != expected_quadratic {
        return Err(HayesError::Invariant(format!(
            "level {level}: primitive quadratic count {primitive_quadratic_character_count} != {expected_quadratic}"
        )));
    }
    let primitive_single_monomial_character_count = level % 2;
    Ok(HayesPowerSumCharacterCoverage {
        level,
        primitive_character_count,
        primitive_quadratic_character_count,
        primitive_higher_order_character_count: primitive_character_count
            - primitive_quadratic_character_count,
        primitive_single_monomial_character_count,
        maximum_power_sum_span_coverage: primitive_quadratic_character_count,
    })
}

/// Necessary divisibility test for supersingularity of one exact-conductor
/// Carlitz cohomology component.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExactConductorSupersingularityDivisibility {
    /// Exact Hayes conductor level.
    pub level: usize,
    /// Even Frobenius power at which the trace is tested.
    pub degree: usize,
    /// Exact conductor-layer trace, up to the immaterial global sign.
    pub trace: i128,
    /// Necessary divisor `2^(degree/2)` for a supersingular component.
    pub necessary_divisor: BigUint,
    /// Remainder of the trace magnitude modulo the necessary divisor.
    pub magnitude_remainder: BigUint,
}

impl ExactConductorSupersingularityDivisibility {
    /// Whether this exact trace rules out supersingularity of the whole
    /// conductor component.
    #[must_use]
    pub fn obstructs_supersingularity(&self) -> bool {
        self.magnitude_remainder != BigUint::from(0_u8)
    }
}

/// Unconditional endpoint budget supplied by the ordinary Weil bound away
/// from the highest conductor levels.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LowConductorWeilSplit {
    /// Number of prescribed zero coefficients.
    pub ell: usize,
    /// Levels `1..=cutoff` covered by the ordinary characterwise bound.
    pub cutoff: usize,
    /// Number of highest levels left for a cancellation-preserving argument.
    pub unresolved_top_levels: usize,
    /// Upper bound for the covered levels after division by `2^ell`.
    pub scaled_discrepancy_bound: BigUint,
    /// Half of the candidate endpoint budget, `2^(ell-1)`.
    pub half_candidate_budget: BigUint,
}

/// Exact-conductor level annihilated by translation `alpha -> alpha + 1`.
///
/// Let `j = 2^v_2(degree)`, the least nonzero binary place of `degree`.
/// If the first `j-1` characteristic coefficients of `alpha` vanish, Lucas'
/// theorem gives
///
/// ```text
/// binomial(degree, i) = 0  (mod 2),  1 <= i < j,
/// binomial(degree, j) = 1  (mod 2).
/// ```
///
/// Substitution `x -> x+1` therefore preserves those first `j-1` zeroes and
/// toggles coefficient `j`.  Translation is an involution of `GF(2^degree)`,
/// so the two coefficient fibres have equal size and `T_(j,degree)=0`.
/// `degree = 0` has no such level.
#[must_use]
pub const fn translation_paired_conductor_level(degree: usize) -> Option<usize> {
    if degree == 0 {
        None
    } else {
        Some(1_usize << degree.trailing_zeros())
    }
}

/// Split the endpoint conductor sum into an unconditionally controlled low
/// part and only logarithmically many unresolved highest levels.
///
/// At either endpoint `n in {2 ell+1, 2 ell+2}`, the `2^(j-1)` characters of
/// exact level `j` have `L`-degree at most `j-1`.  The Riemann hypothesis for
/// function-field Dirichlet `L`-functions therefore gives
///
/// ```text
/// |T_(j,n)| <= (j-1) 2^(j-1) 2^(n/2)
///            <= (j-1) 2^(j-1+ell+1).
/// ```
///
/// After the conductor telescope is divided by `2^ell`, levels through `J`
/// contribute at most
///
/// ```text
/// 2 sum_(j=2)^J (j-1)2^(j-1)
///   = 2 ((J-2)2^J + 2).
/// ```
///
/// Taking the unresolved top width to be `ceil(log2 ell)+2` makes this no
/// larger than `2^(ell-1)`.  This is an unconditional reduction, not a bound
/// on the remaining top levels.
///
/// # Errors
///
/// Returns a typed parameter error when `ell` is smaller than two or an exact
/// shift cannot be represented by the host.
pub fn low_conductor_weil_split(ell: usize) -> Result<LowConductorWeilSplit, HayesError> {
    if ell < 2 {
        return Err(HayesError::InvalidParameter(
            "low-conductor splitting requires ell at least two".to_owned(),
        ));
    }
    let ceil_log_two = usize::BITS as usize - (ell - 1).leading_zeros() as usize;
    let unresolved_top_levels = ceil_log_two
        .checked_add(2)
        .ok_or_else(|| HayesError::InvalidParameter("top-level width overflow".to_owned()))?
        .min(ell);
    let cutoff = ell - unresolved_top_levels;
    let layer_sum = if cutoff < 2 {
        BigUint::from(0_u8)
    } else {
        (BigUint::from(cutoff - 2) << cutoff) + BigUint::from(2_u8)
    };
    let scaled_discrepancy_bound = BigUint::from(2_u8) * layer_sum;
    let half_candidate_budget = BigUint::from(1_u8) << (ell - 1);
    if scaled_discrepancy_bound > half_candidate_budget {
        return Err(HayesError::Invariant(
            "low-conductor Weil split exceeds its half-budget".to_owned(),
        ));
    }
    Ok(LowConductorWeilSplit {
        ell,
        cutoff,
        unresolved_top_levels,
        scaled_discrepancy_bound,
        half_candidate_budget,
    })
}

impl ConductorLayer {
    /// Whether this observed layer satisfies the constant-one square-root target.
    ///
    /// This checks `value^2 <= 2^(2*level-2+degree)` exactly. It is a
    /// diagnostic for one supplied finite value, not a proof for other levels
    /// or degrees.
    #[must_use]
    pub fn satisfies_square_root_bound(self, degree: usize) -> bool {
        if self.level == 0 {
            return false;
        }
        let Some(exponent) = self
            .level
            .checked_mul(2)
            .and_then(|value| value.checked_sub(2))
            .and_then(|value| value.checked_add(degree))
        else {
            return false;
        };
        let magnitude = BigUint::from(self.value.unsigned_abs());
        &magnitude * &magnitude <= (BigUint::from(1_u8) << exponent)
    }
}

/// One cyclic factor in the principal-unit decomposition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrincipalUnitFactor {
    /// Odd degree of the generator `1 + x^odd_degree`.
    pub odd_degree: usize,
    /// Order of that generator modulo `x^(ell+1)`.
    pub order: usize,
}

/// Deterministic cyclic decomposition of `E_ell`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrincipalUnitStructure {
    /// Truncation level in `(1+x GF(2)[x])/(x^(ell+1))`.
    pub ell: usize,
    /// Exact group order, `2^ell`.
    pub group_order: usize,
    /// Ordered cyclic factors, one for each odd generator degree.
    pub factors: Vec<PrincipalUnitFactor>,
}

/// Exact multiplicative energy of one bounded principal-unit interval.
///
/// Put `V_d = {1 + a_1 x + ... + a_d x^d}` inside `E_ell`.  If `r(e)` is
/// the number of ordered pairs `(a,b) in V_d^2` with `ab=e`, then
/// `pair_product_energy` is `sum_e r(e)^2`.  Equivalently, it counts ordered
/// quadruples `(a,b,c,f)` satisfying `ab=cf mod x^(ell+1)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrincipalUnitProductEnergyReport {
    /// Principal-unit truncation level.
    pub ell: usize,
    /// Largest admitted polynomial degree in `V_d`.
    pub degree: usize,
    /// Number of elements in `V_d`, exactly `2^degree`.
    pub set_size: BigUint,
    /// Number of ordered pairs in `V_d^2`, exactly `2^(2 degree)`.
    pub ordered_pair_count: BigUint,
    /// Exact collision count `sum_e r(e)^2`.
    pub pair_product_energy: BigUint,
    /// Exact nonprincipal Fourier fourth-moment numerator
    /// `2^ell pair_product_energy - set_size^4`.
    pub centered_fourier_fourth_moment_numerator: BigUint,
    /// Whether products have degree below the truncation modulus, so every
    /// modular collision is an ordinary polynomial equality.
    pub ordinary_product_regime: bool,
}

/// Exact mixed multiplicative energy of two bounded principal-unit intervals.
///
/// Put `V_a = {1 + a_1 x + ... + a_a x^a}` and define `V_b` similarly.  If
/// `r(e)` counts ordered pairs `(u,v) in V_a x V_b` with `uv=e`, then
/// `pair_product_energy` is `sum_e r(e)^2`.  The mixed Fourier numerator is
/// the integral identity
///
/// ```text
/// sum_(chi != 1) |sum_(u in V_a) chi(u)|^2 |sum_(v in V_b) chi(v)|^2
///   = 2^ell pair_product_energy - |V_a|^2 |V_b|^2.
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrincipalUnitMixedProductEnergyReport {
    /// Principal-unit truncation level.
    pub ell: usize,
    /// Degree of the first interval supplied by the caller.
    pub left_degree: usize,
    /// Degree of the second interval supplied by the caller.
    pub right_degree: usize,
    /// Number of elements in the first interval.
    pub left_set_size: BigUint,
    /// Number of elements in the second interval.
    pub right_set_size: BigUint,
    /// Number of ordered pairs in `V_a x V_b`.
    pub ordered_pair_count: BigUint,
    /// Exact collision count `sum_e r(e)^2`.
    pub pair_product_energy: BigUint,
    /// Exact nonprincipal mixed Fourier-moment numerator.
    pub centered_fourier_mixed_moment_numerator: BigUint,
    /// Whether products have degree at most the truncation level, so modular
    /// collisions are ordinary polynomial equalities.
    pub ordinary_product_regime: bool,
}

/// Exact additive energy of an inverted principal-unit interval.
///
/// Put `V_d={1+a_1 x+...+a_d x^d}` and let `A=V_d^(-1)` in the additive
/// group `x GF(2)[x]/(x^(ell+1))`.  The energy counts ordered quadruples
/// `(a,b,c,f)` in `A^4` satisfying `a+b=c+f`.  In Bagshaw's notation for
/// the modulus `x^(ell+1)`, this is `E^inv_(F,2)(d+1)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrincipalUnitInverseAdditiveEnergyReport {
    /// Principal-unit truncation level.
    pub ell: usize,
    /// Largest nonconstant degree in `V_d`.
    pub interval_degree: usize,
    /// Polynomial cutoff in `deg h < cutoff`, exactly `interval_degree+1`.
    pub polynomial_degree_cutoff: usize,
    /// Number of inverted interval elements, exactly `2^interval_degree`.
    pub set_size: BigUint,
    /// Exact additive quadruple count.
    pub additive_energy: BigUint,
    /// Exact fourth moment of the unnormalized additive Walsh spectrum.
    pub fourth_walsh_moment: BigUint,
    /// Largest absolute Walsh coefficient.
    pub maximum_walsh_amplitude: u128,
}

/// Exact inverse-additive energy after the modulus can no longer wrap.
///
/// For `A,B,C,D in V_d`, clearing the odd denominators gives
///
/// ```text
/// A^(-1)+B^(-1) = C^(-1)+D^(-1)  (mod x^(ell+1))
/// iff
/// (A+B)CD = (C+D)AB               (mod x^(ell+1)).
/// ```
///
/// Both cross-products have degree at most `3d`.  Hence the congruence is an
/// ordinary polynomial equality for every `ell>=3d`.  This report computes
/// that stable value without allocating the ambient group of size `2^ell`:
/// it buckets ordered pairs by the reduced fraction `(A+B)/(AB)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrincipalUnitInverseAdditiveNoWrapReport {
    /// Largest nonconstant degree in `V_d`.
    pub interval_degree: usize,
    /// First principal-unit level at which congruence is equality, `3d`.
    pub minimum_stable_ell: usize,
    /// Number of ordered pairs `(A,B)`, exactly `2^(2d)`.
    pub ordered_pair_count: BigUint,
    /// Number of distinct reduced rational functions `(A+B)/(AB)`.
    pub reduced_fraction_count: usize,
    /// Largest multiplicity of one reduced rational function.
    pub maximum_fraction_multiplicity: u128,
    /// Stable additive energy for every `ell>=3d`.
    pub additive_energy: BigUint,
}

/// Explicit divisor bound for the stabilized inverse-additive energy.
///
/// A collision class with reduced denominator `q` has multiplicity at most
/// the ternary polynomial-divisor function `tau_3(q)`, and `deg q<=2d`.
/// Splitting irreducible factors at `split_degree=R` gives
///
/// ```text
/// tau_3(q) <= (2d+1)^(2^(R+2)) * 3^(floor(2d/(R+1))).
/// ```
///
/// Taking `R=floor(log2(d)/2)` (and at least one) makes the extra base-two
/// exponent `o(d)`, so `E_inv<=2^(2d+o(d))` whenever `ell>=3d`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrincipalUnitInverseAdditiveNoWrapBoundReport {
    /// Largest nonconstant degree in `V_d`.
    pub interval_degree: usize,
    /// First stable principal-unit level, `3d`.
    pub minimum_stable_ell: usize,
    /// Factor-degree split `R` used in the explicit divisor estimate.
    pub split_degree: usize,
    /// Explicit upper bound for every collision-class multiplicity.
    pub maximum_multiplicity_bound: BigUint,
    /// Explicit energy bound `2^(2d) * maximum_multiplicity_bound`.
    pub additive_energy_bound: BigUint,
}

impl PrincipalUnitInverseAdditiveNoWrapBoundReport {
    /// Smallest integer `e` with `additive_energy_bound<=2^e`.
    #[must_use]
    pub fn ceiling_energy_exponent(&self) -> Option<usize> {
        let bits = usize::try_from(self.additive_energy_bound.bits()).ok()?;
        if bits == 0 {
            return Some(0);
        }
        let floor = bits - 1;
        if self.additive_energy_bound == (BigUint::from(1_u8) << floor) {
            Some(floor)
        } else {
            Some(bits)
        }
    }
}

/// One valuation stratum in the explicit wrapped inverse-energy proof for
/// `GF(2)[x]/(x^r)`.
///
/// The stratum contains ordered pairs `(A,B)` with
/// `v_x(A^(-1)+B^(-1))=v_x(A+B)=s`.  Its contribution bounds
/// `sum_a I(a)^2` by the exact pair population times a uniform fibre bound
/// obtained from Padé approximation, lift counting, and polynomial divisors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryPrimePowerInverseEnergyStratum {
    /// Exact positive `x`-adic valuation `s`.
    pub valuation: usize,
    /// Padé denominator degree bound
    /// `k=min(r-s-1,ceil((r+m)/2))`.
    pub approximation_degree: usize,
    /// Exponent `L` in the upper bound `2^L` for lift polynomials `t`.
    pub lift_choice_exponent: usize,
    /// Degree bound for the nonzero polynomial being factored.
    pub factor_polynomial_degree_bound: usize,
    /// Explicit upper bound for the number of ordered factorizations.
    pub factorization_count_bound: BigUint,
    /// Exact number of ordered interval pairs in this valuation stratum.
    pub ordered_pair_count: BigUint,
    /// Bound contributed to the additive energy by this stratum.
    pub energy_contribution_bound: BigUint,
}

/// Explicit characteristic-two inverse-additive-energy theorem for the
/// prime-power modulus `x^r`, including the wrapped range.
///
/// Let `U_m={A in GF(2)[x]: deg A<m, A(0)=1}`.  This report proves an
/// explicit upper bound for
///
/// ```text
/// #{(A,B,C,D) in U_m^4:
///     A^(-1)+B^(-1)=C^(-1)+D^(-1) (mod x^r)}.
/// ```
///
/// It is the special-modulus internal reproof of Bagshaw's fourth inverse
/// energy input.  Unlike the no-wrap report, it is valid for every `1<=m<=r`,
/// including `3m=r`; all divisor losses remain explicit `BigUint` factors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryPrimePowerInverseEnergyBoundReport {
    /// Modulus degree `r` in `x^r`.
    pub modulus_degree: usize,
    /// Polynomial cutoff `m` in `deg A<m`.
    pub polynomial_degree_cutoff: usize,
    /// Interval size, exactly `2^(m-1)`.
    pub set_size: BigUint,
    /// Diagonal `a=0` contribution, exactly `set_size^2`.
    pub diagonal_energy: BigUint,
    /// Explicit nonzero-valuation contributions.
    pub strata: Vec<BinaryPrimePowerInverseEnergyStratum>,
    /// Sum of the diagonal and every stratum bound.
    pub additive_energy_bound: BigUint,
}

impl BinaryPrimePowerInverseEnergyBoundReport {
    /// Smallest integer `e` with `additive_energy_bound<=2^e`.
    #[must_use]
    pub fn ceiling_energy_exponent(&self) -> Option<usize> {
        let bits = usize::try_from(self.additive_energy_bound.bits()).ok()?;
        if bits == 0 {
            return Some(0);
        }
        let floor = bits - 1;
        if self.additive_energy_bound == (BigUint::from(1_u8) << floor) {
            Some(floor)
        } else {
            Some(bits)
        }
    }
}

/// Exact exponent substitution in Bagshaw's characteristic-free `k=2`
/// bilinear-energy lemma.
///
/// If interval cardinalities have base-two exponents `m,n`, the modulus has
/// degree `r`, and `E_2(m)<=2^em`, `E_2(n)<=2^en`, the lemma gives
///
/// ```text
/// log2 |W| <= m+n + (em+en+r-4m-4n)/8.
/// ```
///
/// Energy exponents are supplied over a caller-selected common denominator
/// `D`; the returned bilinear exponent and target are exact numerators over
/// `8D`.  This checks exponent arithmetic only, not the analytic hypotheses
/// or suppressed constants.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BinaryBilinearEnergyExponentReport {
    /// Base-two logarithm of the left interval cardinality.
    pub left_interval_exponent: usize,
    /// Base-two logarithm of the right interval cardinality.
    pub right_interval_exponent: usize,
    /// Modulus degree `r`.
    pub modulus_degree: usize,
    /// Common denominator `D` of the two supplied energy exponents.
    pub energy_exponent_denominator: usize,
    /// Bound exponent numerator over denominator `8D`.
    pub bound_exponent_numerator: u128,
    /// Target exponent numerator over denominator `8D`.
    pub target_exponent_numerator: u128,
    /// `target-bound` over denominator `8D`.
    pub deficit_numerator: i128,
    /// Whether the energy substitution is strictly below the target exponent.
    pub strict_saving: bool,
}

/// Loss-aware bilinear exponent report fed by the explicit wrapped binary
/// prime-power energy envelope rather than an idealized energy exponent.
///
/// The final exponents use denominator `8D`, where `D` is the caller's
/// denominator for an additional analytic loss exponent.  This keeps the
/// divisor envelope, suppressed constants, and any chosen epsilon reserve
/// distinct from the formal Hölder substitution.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BinaryBilinearExplicitEnergyExponentReport {
    /// Left interval cardinality exponent `d`, for cutoff `m=d+1`.
    pub left_interval_exponent: usize,
    /// Right interval cardinality exponent `d`, for cutoff `m=d+1`.
    pub right_interval_exponent: usize,
    /// Modulus degree `r` in `x^r`.
    pub modulus_degree: usize,
    /// Ceiling exponent of the proved left energy envelope.
    pub left_energy_ceiling_exponent: usize,
    /// Ceiling exponent of the proved right energy envelope.
    pub right_energy_ceiling_exponent: usize,
    /// Numerator of the caller-supplied extra analytic loss.
    pub analytic_loss_exponent_numerator: usize,
    /// Denominator `D` of the caller-supplied extra analytic loss.
    pub analytic_loss_exponent_denominator: usize,
    /// Final bound exponent numerator over denominator `8D`.
    pub bound_exponent_numerator: u128,
    /// Target exponent numerator over denominator `8D`.
    pub target_exponent_numerator: u128,
    /// `target-bound` over denominator `8D`.
    pub deficit_numerator: i128,
    /// Whether the explicit envelope plus reserve lies below the target.
    pub strict_saving: bool,
}

/// Exact exponent ledger for Bagshaw's Type-I Case 1 after replacing the
/// odd-characteristic square-root complete-sum exponent by the proved binary
/// exponent `kappa(r0)=r0-ceil((r0-1)/3)`.
///
/// The case has `0<=u<=2r0/3` and `r0<=N-u`.  Completion changes the
/// published exponent `N-r0/2` to `N-r0+kappa(r0)`, independently of `u`.
/// This is an arithmetic audit of the source proof, not a certificate that
/// all of Bagshaw's odd-characteristic argument has been ported.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BinaryTypeOneCaseOneExponentReport {
    /// Cumulative Möbius cutoff `N`.
    pub mobius_degree_cutoff: usize,
    /// Effective modulus degree `r0`.
    pub effective_modulus_degree: usize,
    /// Largest integer `u` in the Case-1 range.
    pub maximum_admissible_u: usize,
    /// Proved complete binary Kloosterman exponent `kappa(r0)`.
    pub complete_kloosterman_exponent: usize,
    /// Binary-completion bound exponent `N-r0+kappa(r0)`.
    pub bound_exponent: u128,
    /// Trivial exponent `N`.
    pub trivial_exponent: u128,
    /// `trivial-bound`; a positive value is a power saving.
    pub deficit: i128,
    /// Whether the replacement retains a strict power saving.
    pub strict_saving: bool,
}

/// Exact endpoint optimization for Bagshaw's Type-I Case 2 with the proved
/// binary complete-sum exponent.
///
/// On the integer range `u<=r0/3` and `r0/3<=N-u<=r0`, the two available
/// exponent bounds are
///
/// ```text
/// A(u)=(3N+r0-u)/4,       B(u)=u+kappa(r0).
/// ```
///
/// The combined bound is the maximum over admissible `u` of `min(A(u),B(u))`.
/// All reported exponents are exact numerators over denominator four.  This
/// report audits exponent arithmetic only and grants no theorem credit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BinaryTypeOneCaseTwoExponentReport {
    /// Cumulative Möbius cutoff `N`.
    pub mobius_degree_cutoff: usize,
    /// Effective modulus degree `r0`.
    pub effective_modulus_degree: usize,
    /// Smallest admissible integer `u`.
    pub minimum_admissible_u: usize,
    /// Largest admissible integer `u`.
    pub maximum_admissible_u: usize,
    /// Smallest `u` attaining the worst combined bound.
    pub worst_admissible_u: usize,
    /// Proved complete binary Kloosterman exponent `kappa(r0)`.
    pub complete_kloosterman_exponent: usize,
    /// Whether Axeyum has an internal wrapped `q=2,F=x^r` energy theorem for
    /// the `A(u)` input across this full case.
    pub wrapped_energy_input_available: bool,
    /// Whether the displayed quarter-exponent omits the explicit divisor
    /// envelope and any analytic epsilon reserve.
    pub suppressed_energy_loss: bool,
    /// Numerator `3N+r0-u` of the energy bound at the worst `u`.
    pub energy_bound_quarters: u128,
    /// Numerator `4u+4kappa(r0)` of the completion bound at the worst `u`.
    pub completion_bound_quarters: u128,
    /// Worst combined exponent numerator over denominator four.
    pub bound_exponent_quarters: u128,
    /// Trivial exponent numerator `4N`.
    pub trivial_exponent_quarters: u128,
    /// `trivial-bound`, in quarters; a positive value is a power saving.
    pub deficit_quarters: i128,
    /// Whether the replacement retains a strict power saving on the full case.
    pub strict_saving: bool,
}

/// Exact exponent ledger for Bagshaw's Type-I Case 5 after inserting the
/// proved binary wild-Kloosterman bound.
///
/// All exponents are measured in sixths.  If `n` is the Möbius cutoff,
/// `r0` the effective modulus degree, and
/// `kappa=r0-ceil((r0-1)/3)`, the worst off-diagonal term has exponent
/// `2n/3+kappa/2=(4n+3kappa)/6`.  The trivial exponent is `n`.
/// This report checks only exponent arithmetic; it does not assert that the
/// surrounding odd-characteristic Vaughan proof has been ported.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BinaryTypeOneCaseFiveExponentReport {
    /// Degree cutoff in the Möbius sum.
    pub mobius_degree_cutoff: usize,
    /// Degree of `F/(a,F)` in Bagshaw's notation.
    pub effective_modulus_degree: usize,
    /// Proved complete binary Kloosterman exponent `kappa`.
    pub complete_kloosterman_exponent: usize,
    /// Numerator of the worst Type-I bound over denominator six.
    pub bound_exponent_sixths: u128,
    /// Numerator of the trivial exponent over denominator six.
    pub trivial_exponent_sixths: u128,
    /// `trivial-bound`, in sixths; a positive value is a saving.
    pub deficit_sixths: i128,
    /// Whether the inserted binary exponent gives any strict saving.
    pub strict_saving: bool,
}

/// Zero-epsilon endpoint calibration for the published inverse-Möbius
/// exponents, expressed over a common denominator 48.
///
/// For cumulative cutoff `N`, Bagshaw's published odd-characteristic bound
/// has exponent maximum `max(15N/16, 2N/3+r/4)`.  The report compares that
/// formal exponent with the Lemire target `ell`.  It is deliberately named a
/// calibration: the published theorem does not apply at `q=2`, and constants
/// and epsilon losses are omitted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EndpointInverseMobiusExponentCalibrationReport {
    /// Principal-unit level.
    pub ell: usize,
    /// Endpoint polynomial degree, `2ell+1` or `2ell+2`.
    pub endpoint_degree: usize,
    /// Convolution interval degree `d`.
    pub interval_degree: usize,
    /// Exact-degree Möbius index `k=endpoint_degree-d`.
    pub exact_mobius_degree: usize,
    /// Largest cumulative cutoff needed by `H_k=C_(k+1)-2C_k+C_(k-1)`.
    pub cumulative_cutoff: usize,
    /// Whether the cutoff exceeds the modulus degree `ell+1`.
    ///
    /// This is always true at the two Lemire endpoints.  Bagshaw's Type-I
    /// Case 5 requires `N<=r0<=ell+1`, so it is empty for these reports.
    pub cumulative_cutoff_exceeds_modulus: bool,
    /// Numerator `45N` for `15N/16`, over denominator 48.
    pub fifteen_sixteenths_exponent_48ths: u128,
    /// Numerator `32N+12r` for `2N/3+r/4`, over denominator 48.
    pub mixed_exponent_48ths: u128,
    /// Larger calibrated exponent numerator, over denominator 48.
    pub bound_exponent_48ths: u128,
    /// Lemire target exponent numerator `48ell`.
    pub target_exponent_48ths: u128,
    /// `target-bound`, in forty-eighths; positive means pointwise closure.
    pub deficit_48ths: i128,
    /// Whether the zero-epsilon pointwise calibration lies strictly below
    /// `2^ell` before constants and the sum over `d` are restored.
    pub strict_pointwise_closure: bool,
}

/// One source-level Vaughan range in the endpoint Möbius audit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum EndpointVaughanCase {
    /// Direct arithmetic-progression bound when `16r0<7N`.
    SmallEffectiveModulus,
    /// Type-I Case 1: long inner interval, binary complete-sum replacement.
    TypeOneCaseOne,
    /// Type-I Case 2: energy/completion max-min range.
    TypeOneCaseTwo,
    /// Type-I Case 3: balanced `k=2` bilinear-energy range.
    TypeOneCaseThree,
    /// Type-I Case 4: short inner interval and smaller outer variable.
    TypeOneCaseFour,
    /// Type-I Case 5: short inner interval and larger outer variable.
    TypeOneCaseFive,
    /// Type-II Case 1: both variables between one third and one modulus.
    TypeTwoCaseOne,
    /// Type-II Case 2: one variable at least one modulus.
    TypeTwoCaseTwo,
    /// Type-II Case 3: both variables at least one modulus.
    TypeTwoCaseThree,
}

impl EndpointVaughanCase {
    const ALL: [Self; 9] = [
        Self::SmallEffectiveModulus,
        Self::TypeOneCaseOne,
        Self::TypeOneCaseTwo,
        Self::TypeOneCaseThree,
        Self::TypeOneCaseFour,
        Self::TypeOneCaseFive,
        Self::TypeTwoCaseOne,
        Self::TypeTwoCaseTwo,
        Self::TypeTwoCaseThree,
    ];
}

/// Aggregate coverage and worst main exponent for one Vaughan range.
///
/// Exponents are exact numerators over denominator sixteen.  Each row retains
/// both the ideal source exponent and a second exponent using Axeyum's proved
/// finite wrapped-energy envelope.  The remaining analytic/Vaughan-weight
/// reserve and constants are still separate, so this is not theorem credit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EndpointVaughanCaseRow {
    /// Source case represented by this row.
    pub case: EndpointVaughanCase,
    /// Number of effective-modulus/variable samples assigned to this case.
    pub sample_count: u128,
    /// Largest main exponent numerator over denominator sixteen, if nonempty.
    pub worst_bound_sixteenths: Option<u128>,
    /// Effective modulus degree attaining the recorded worst value.
    pub worst_effective_modulus_degree: Option<usize>,
    /// Vaughan variable `u` or `v` attaining the recorded worst value.
    pub worst_split_degree: Option<usize>,
    /// Largest exponent after replacing every `k=2` ideal energy exponent by
    /// the ceiling of Axeyum's explicit wrapped binary energy envelope.
    pub worst_explicit_energy_bound_sixteenths: Option<u128>,
    /// Effective modulus attaining the explicit-energy worst value.
    pub worst_explicit_energy_effective_modulus_degree: Option<usize>,
    /// Vaughan split attaining the explicit-energy worst value.
    pub worst_explicit_energy_split_degree: Option<usize>,
}

/// Exhaustive endpoint Vaughan range table for one convolution order.
///
/// The report covers all `1<=r0<=ell+1`, Type-I splits
/// `0<=u<=floor(2r0/3)`, and the symmetry-reduced Type-II splits
/// `r0/3<v<=min(N-r0/3,N/2)`.  The identity frequency `r0=0` is deliberately
/// separate from Vaughan's coprime-frequency proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EndpointVaughanRangeReport {
    /// Principal-unit level `ell`.
    pub ell: usize,
    /// Endpoint degree `2ell+1` or `2ell+2`.
    pub endpoint_degree: usize,
    /// Convolution interval degree `d`.
    pub interval_degree: usize,
    /// Cumulative Möbius cutoff `N=endpoint_degree-d+1`.
    pub cumulative_cutoff: usize,
    /// Original modulus degree `r=ell+1`.
    pub modulus_degree: usize,
    /// One row for each source case, including empty rows.
    pub rows: Vec<EndpointVaughanCaseRow>,
    /// Worst case after all effective moduli and splits are enumerated.
    pub worst_case: EndpointVaughanCase,
    /// Worst main exponent numerator over denominator sixteen.
    pub worst_bound_sixteenths: u128,
    /// Lemire target exponent numerator `16ell`.
    pub target_exponent_sixteenths: u128,
    /// `target-bound` over denominator sixteen.
    pub deficit_sixteenths: i128,
    /// Worst bound after inserting the proved finite divisor envelope in
    /// every inverse-energy input, still before analytic/Vaughan-weight loss.
    pub worst_explicit_energy_bound_sixteenths: u128,
    /// `target-explicit_energy_bound` over denominator sixteen.
    pub explicit_energy_deficit_sixteenths: i128,
}

impl EndpointVaughanRangeReport {
    /// A successful report has assigned every enumerated split; uncovered
    /// splits fail construction instead of producing a partial table.
    #[must_use]
    pub const fn all_ranges_covered(&self) -> bool {
        true
    }

    /// Whether endpoint inequalities make Type-I Cases 4 and 5 empty.
    #[must_use]
    pub fn short_inner_type_one_cases_empty(&self) -> bool {
        self.rows.iter().all(|row| {
            !matches!(
                row.case,
                EndpointVaughanCase::TypeOneCaseFour | EndpointVaughanCase::TypeOneCaseFive
            ) || row.sample_count == 0
        })
    }

    /// The ideal column suppresses the energy envelope, while both columns
    /// still leave analytic/Vaughan-weight constants and convolution weights
    /// separate.
    #[must_use]
    pub const fn suppressed_losses_remain(&self) -> bool {
        true
    }

    /// Whether the proved wrapped inverse-energy envelope, including its
    /// finite divisor factor, is below the pointwise target before the
    /// separate analytic/Vaughan-weight reserve is charged.
    #[must_use]
    pub const fn strict_pointwise_explicit_energy_closure(&self) -> bool {
        self.explicit_energy_deficit_sixteenths > 0
    }

    /// Whether the zero-loss pointwise main exponent is below `2^ell`.
    #[must_use]
    pub const fn strict_pointwise_main_term_closure(&self) -> bool {
        self.deficit_sixteenths > 0
    }
}

/// End-to-end Vaughan range table across every endpoint convolution order.
///
/// Entries are ordered by increasing interval degree `1<=d<ell`.  As with
/// [`EndpointVaughanRangeReport`], the table contains both ideal and explicit-
/// energy exponents but deliberately does not absorb the remaining analytic,
/// constant, or convolution-weight losses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EndpointVaughanTableReport {
    /// Principal-unit level `ell`.
    pub ell: usize,
    /// Endpoint degree `2ell+1` or `2ell+2`.
    pub endpoint_degree: usize,
    /// One exhaustive range report for every `1<=d<ell`.
    pub convolution_orders: Vec<EndpointVaughanRangeReport>,
    /// First `d` with a strict zero-loss pointwise main-exponent saving.
    pub first_strict_pointwise_degree: Option<usize>,
    /// First `d` whose pointwise exponent remains strict after inserting the
    /// explicit wrapped inverse-energy envelope.
    pub first_strict_explicit_energy_degree: Option<usize>,
}

impl EndpointVaughanTableReport {
    /// Whether every endpoint convolution order is represented.
    #[must_use]
    pub fn all_convolution_orders_present(&self) -> bool {
        self.convolution_orders.len() == self.ell.saturating_sub(1)
            && self
                .convolution_orders
                .iter()
                .enumerate()
                .all(|(index, report)| report.interval_degree == index + 1)
    }

    /// Even the explicit-energy column leaves analytic/Vaughan-weight losses
    /// separate, so the table is not endpoint theorem credit.
    #[must_use]
    pub const fn suppressed_losses_remain(&self) -> bool {
        true
    }
}

/// One pointwise tail bound after restoring a loss reserve and the factor `d`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OddEndpointVaughanTailOrder {
    /// Convolution interval degree `d`.
    pub interval_degree: usize,
    /// Exhaustive Vaughan main exponent numerator over denominator sixteen.
    pub main_bound_sixteenths: u128,
    /// Main exponent after inserting the exact finite divisor envelope in
    /// every wrapped inverse-energy input.
    pub explicit_energy_bound_sixteenths: u128,
    /// Caller-selected reserve numerator over denominator sixteen.
    pub loss_reserve_sixteenths: u128,
    /// `ceil(log2(d))`, used to restore the convolution weight.
    pub convolution_weight_ceiling_bits: usize,
    /// Integer ceiling of the resulting base-two exponent.
    pub total_ceiling_bits: usize,
    /// Conservative power-of-two absolute bound for this order.
    pub absolute_bound: BigUint,
    /// Conservative bound obtained from the explicit-energy exponent.
    pub explicit_energy_absolute_bound: BigUint,
}

/// Margin ledger for a buffered large-`d` tail at the odd Lemire endpoint.
///
/// The endpoint identity is `N_(2ell+1)(1)=1+(2ell+1)I_(2ell+1)(1)`.  Hence
/// an absolute discrepancy at most `2^(ell+1)-2` proves positivity.  After
/// charging the selected tail pointwise, `residual_low_block_budget` is the
/// exact absolute budget that a cancellation-preserving argument must meet on
/// the complementary block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OddEndpointVaughanTailBudgetReport {
    /// Principal-unit level `ell`.
    pub ell: usize,
    /// Odd endpoint degree `2ell+1`.
    pub endpoint_degree: usize,
    /// First interval degree charged pointwise.
    pub tail_start_degree: usize,
    /// Uniform caller reserve added to every main exponent, in sixteenths.
    pub loss_reserve_sixteenths: u128,
    /// Pointwise rows for `tail_start_degree<=d<ell`.
    pub tail_orders: Vec<OddEndpointVaughanTailOrder>,
    /// Largest integer absolute discrepancy sufficient for odd positivity.
    pub endpoint_absolute_budget: BigUint,
    /// Sum of the conservative pointwise tail bounds.
    pub tail_absolute_bound: BigUint,
    /// Tail bound after inserting the explicit inverse-energy envelope.
    pub explicit_energy_tail_absolute_bound: BigUint,
    /// Budget left for the absolute value of the low/medium signed block.
    pub residual_low_block_budget: Option<BigUint>,
    /// Residual budget after charging the explicit-energy tail.
    pub explicit_energy_residual_low_block_budget: Option<BigUint>,
}

impl OddEndpointVaughanTailBudgetReport {
    /// Whether the pointwise tail leaves any nonnegative residual budget.
    #[must_use]
    pub fn tail_fits_endpoint_budget(&self) -> bool {
        self.residual_low_block_budget.is_some()
    }

    /// Whether the explicit-energy pointwise tail fits before the separate
    /// analytic/Vaughan-weight reserve has been justified.
    #[must_use]
    pub fn explicit_energy_tail_fits_endpoint_budget(&self) -> bool {
        self.explicit_energy_residual_low_block_budget.is_some()
    }
}

/// Uniform wild-Kloosterman bound for the binary principal-unit group.
///
/// Put `R = GF(2)[x]/(x^(ell+1))`, let `psi` read the coefficient of
/// `x^ell`, and for `c in R` define
///
/// ```text
/// K_2(c) = sum_(u in R^x) psi(u^(-1) + c u).
/// ```
///
/// Since the residue field is binary, `R^x = 1+xR`.  The report bounds every
/// frequency `c`, including non-units; no finite transform is needed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrincipalUnitKloostermanBoundReport {
    /// Principal-unit truncation level, so the local-ring modulus is `x^(ell+1)`.
    pub ell: usize,
    /// Local-ring modulus exponent, exactly `ell+1`.
    pub modulus_exponent: usize,
    /// Precision `ceil((ell+1)/3)` at which the phase is affine on cosets.
    pub affine_coset_precision: usize,
    /// Precision `ceil(ell/3)` modulo which all stationary cosets agree.
    pub stationary_congruence_precision: usize,
    /// Maximum number of contributing affine cosets, `2^(c-s)`.
    pub max_contributing_cosets: BigUint,
    /// Uniform bound `|K_2(c)| <= 2^(ell+1-ceil(ell/3))`.
    pub max_abs_kloosterman_sum: BigUint,
    /// Consequent bound for the centered multiplicity of `V_(ell-1)^2`.
    ///
    /// If `r(e)=#{(a,b) in V_(ell-1)^2:ab=e}`, then
    /// `|r(e)-2^(ell-2)|` is at most this value.
    pub max_abs_top_product_deviation: BigUint,
}

/// Explicit assumption whose arithmetic consequences Axeyum can check.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConductorBoundAssumption {
    /// Constant `C` in `|T_(j,n)| <= C j^a 2^((n+j)/2)`.
    pub constant: usize,
    /// Polynomial conductor exponent `a`.
    pub power: usize,
    /// First `ell` at which the symbolic bound is used.
    pub threshold: usize,
    /// Largest degree covered by separate finite certificates.
    pub finite_max_degree: usize,
}

impl Default for ConductorBoundAssumption {
    fn default() -> Self {
        Self {
            constant: 8,
            power: 12,
            threshold: 194,
            finite_max_degree: 400,
        }
    }
}

/// Checked arithmetic implication from a conductor estimate to endpoint positivity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct SufficientBoundReport {
    /// Assumption checked by the exact arithmetic route.
    pub assumption: ConductorBoundAssumption,
    /// First odd endpoint degree discharged by the symbolic estimate.
    pub first_odd_degree: usize,
    /// First even endpoint degree discharged by the symbolic estimate.
    pub first_even_degree: usize,
}

/// A polynomial-times-`2^(3 ell)` fourth-moment endpoint estimate.
///
/// The mathematical assumption is
///
/// ```text
/// sum_e |N_n(e) - 2^(n-ell)|^4
///     <= constant * ell^power * 2^(3 ell)
/// ```
///
/// Here `N_n(e) = sum Lambda(F)` over degree-`n` monic polynomials in class
/// `e`; it is the Mangoldt population, not the unweighted irreducible count.
/// The later Hayes/Mobius step removes proper prime powers before concluding
/// irreducible positivity.
///
/// at `n in {2 ell + 1, 2 ell + 2}` from `threshold` onward.  Axeyum checks
/// only the arithmetic consequence of that assumption.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct FourthMomentBoundAssumption {
    /// Polynomial prefactor constant.
    pub constant: usize,
    /// Polynomial exponent on `ell`.
    pub power: usize,
    /// First `ell` at which the estimate is assumed.
    pub threshold: usize,
    /// Largest degree covered by separate finite certificates.
    pub finite_max_degree: usize,
}

impl Default for FourthMomentBoundAssumption {
    fn default() -> Self {
        Self {
            constant: 64,
            power: 2,
            threshold: 200,
            finite_max_degree: 400,
        }
    }
}

/// Checked arithmetic implication from a fourth-moment estimate to endpoint
/// irreducible positivity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct FourthMomentBoundReport {
    /// Assumption checked by the exact arithmetic route.
    pub assumption: FourthMomentBoundAssumption,
    /// First odd endpoint degree discharged by the symbolic estimate.
    pub first_odd_degree: usize,
    /// First even endpoint degree discharged by the symbolic estimate.
    pub first_even_degree: usize,
}

/// Exact weak fourth-moment threshold using the proved proper-power envelope.
///
/// If `mu=2^(n-ell)` is the uniform Mangoldt-class mean and `P_n` is the
/// proved proper-prime-power upper bound in the identity class, then
///
/// ```text
/// M_4=sum_e |N_n(e)-mu|^4 < (mu-P_n)^4
/// ```
///
/// implies `N_n(1)>P_n`, hence a shaped irreducible exists.  The superficially
/// weaker threshold `M_4<mu^4` proves only `N_n(1)>0`; at the odd endpoint it
/// still permits the bad value `N_n(1)=1`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WeakFourthMomentEndpointLedger {
    /// Lemire endpoint degree `n`.
    pub degree: usize,
    /// Number of prescribed leading coefficients.
    pub ell: usize,
    /// Uniform Mangoldt-class mean `mu=2^(n-ell)`.
    pub main_mangoldt_term: BigUint,
    /// Exact odd proper-power contribution or proved even upper bound `P_n`.
    pub proper_prime_power_upper_bound: BigUint,
    /// Strict discrepancy margin `mu-P_n`.
    pub irreducible_margin: BigUint,
    /// The positivity-only threshold `mu^4`, retained to prevent conflation.
    pub positivity_only_fourth_moment_threshold: BigUint,
    /// Exact strict irreducibility threshold `(mu-P_n)^4`.
    pub strict_irreducible_fourth_moment_threshold: BigUint,
    /// Unit scale `2^ell*mu^3` in the Hast--Matei fourth-moment normalization.
    pub wild_fourth_moment_unit_scale: BigUint,
    /// Numerator of the exact sufficient wild constant
    /// `C < numerator/denominator` in `M_4 <= C*2^ell*mu^3`.
    pub sufficient_wild_constant_numerator: BigUint,
    /// Denominator of the exact sufficient wild constant.
    pub sufficient_wild_constant_denominator: BigUint,
    /// `Sigma(ell)=sum_(j=2)^ell 2^(j-1)(j-1)^2` in the proved `M_2` bound.
    pub second_moment_weil_factor: BigUint,
    /// Proved upper bound `M_2<=mu*Sigma(ell)`.
    pub second_moment_upper_bound: BigUint,
    /// Numerator of the sufficient root-kurtosis threshold
    /// `R_0 < numerator/denominator`.
    pub sufficient_root_ratio_numerator: BigUint,
    /// Denominator of the sufficient root-kurtosis threshold.
    pub sufficient_root_ratio_denominator: BigUint,
    /// Whether the old strong target `R_0<=4` is strictly sufficient here.
    pub strong_connected_target_has_strict_reserve: bool,
}

/// A linear local concentration bound on every Witt cylinder.
///
/// The mathematical assumption is `R_j(b) <= ell` for every cylinder in the
/// two endpoint distributions once `ell >= threshold`.  Only the root case is
/// needed by the arithmetic implication; retaining the local statement makes
/// the target compatible with a future Carleson or martingale proof.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct WittCylinderLinearBoundAssumption {
    /// First `ell` at which the concentration estimate is assumed.
    pub threshold: usize,
    /// Largest degree covered by separate finite certificates.
    pub finite_max_degree: usize,
}

impl Default for WittCylinderLinearBoundAssumption {
    fn default() -> Self {
        Self {
            threshold: 200,
            finite_max_degree: 400,
        }
    }
}

/// Checked implication from linear Witt-cylinder concentration to endpoint
/// irreducible positivity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct WittCylinderLinearBoundReport {
    /// Assumption checked by the exact arithmetic route.
    pub assumption: WittCylinderLinearBoundAssumption,
    /// Derived fourth-moment envelope checked by the existing endpoint route.
    pub derived_fourth_moment: FourthMomentBoundReport,
}

/// A unit-variance-square upper bound on the connected fourth cumulant.
///
/// The mathematical assumption is `2^ell M_4 - 3 M_2^2 <= M_2^2` at both
/// Lemire endpoints.  Equivalently, the root concentration ratio is at most
/// four.  Unlike a pointwise convolution-order estimate, this retains every
/// signed cross-order cancellation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConnectedCumulantBoundAssumption {
    /// First `ell` at which the connected estimate is assumed.
    pub threshold: usize,
    /// Largest degree covered by separate finite certificates.
    pub finite_max_degree: usize,
}

impl Default for ConnectedCumulantBoundAssumption {
    fn default() -> Self {
        Self {
            threshold: 200,
            finite_max_degree: 400,
        }
    }
}

/// Checked implication from connected-cumulant domination to endpoint
/// irreducible positivity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConnectedCumulantBoundReport {
    /// Assumption checked by the exact arithmetic route.
    pub assumption: ConnectedCumulantBoundAssumption,
    /// Derived fourth-moment envelope checked by the endpoint route.
    pub derived_fourth_moment: FourthMomentBoundReport,
}

/// A constant-one square-root bound on every exact-conductor family.
///
/// The mathematical assumption is
/// `T_(j,n)^2 <= 2^(2j-2+n)` for `1 <= j <= ell` at the two endpoint
/// degrees.  The rational fields provide a checked upper approximation to
/// `sqrt(2)` for the odd endpoint; they are arithmetic witnesses rather than
/// part of the conjectured character-sum estimate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct SquareRootLayerBoundAssumption {
    /// First `ell` at which the family estimate is assumed.
    pub threshold: usize,
    /// Largest degree covered by separate finite certificates.
    pub finite_max_degree: usize,
    /// Numerator of a strict rational upper bound for `sqrt(2)`.
    pub sqrt_two_upper_numerator: usize,
    /// Denominator of a strict rational upper bound for `sqrt(2)`.
    pub sqrt_two_upper_denominator: usize,
}

impl Default for SquareRootLayerBoundAssumption {
    fn default() -> Self {
        Self {
            threshold: 22,
            finite_max_degree: 400,
            sqrt_two_upper_numerator: 99,
            sqrt_two_upper_denominator: 70,
        }
    }
}

/// Exact arithmetic implication from the constant-one family estimate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct SquareRootLayerBoundReport {
    /// Assumption checked by the arithmetic route.
    pub assumption: SquareRootLayerBoundAssumption,
    /// First odd endpoint discharged by the symbolic argument.
    pub first_odd_degree: usize,
    /// First even endpoint discharged by the symbolic argument.
    pub first_even_degree: usize,
}

/// A polynomial-loss square-root sup bound on every conductor martingale layer.
///
/// For `D_[j]=P_j D-P_(j-1)D`, the mathematical assumption is
///
/// ```text
/// max_e |D_[j](e)|^2
///   <= C ell^a (j-1)^2 2^(j-1+n-2ell),       2 <= j <= ell,
/// ```
///
/// at both Lemire endpoint degrees.  The constant is stored as the integer
/// `C`; a rational constant would add no proof power because a larger integer
/// ceiling can always be used.  This is an unproved arithmetic hypothesis,
/// not a consequence of the exact finite diagnostic below.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConductorLayerSupBoundAssumption {
    /// Integer constant `C` in the squared layer bound.
    pub squared_constant: usize,
    /// Polynomial loss exponent `a`.
    pub polynomial_power: usize,
    /// First `ell` at which the bound is assumed.
    pub threshold: usize,
    /// Largest degree covered by separate finite certificates.
    pub finite_max_degree: usize,
}

impl Default for ConductorLayerSupBoundAssumption {
    fn default() -> Self {
        Self {
            squared_constant: 4,
            polynomial_power: 4,
            threshold: 200,
            finite_max_degree: 400,
        }
    }
}

/// Checked implication from conductor-layer delocalization to endpoint
/// irreducible positivity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConductorLayerSupBoundReport {
    /// Assumption checked by the arithmetic route.
    pub assumption: ConductorLayerSupBoundAssumption,
    /// Coarse integer constant in
    /// `M_4 <= constant ell^power 2^(3ell)`.
    pub derived_fourth_moment_constant: usize,
    /// Polynomial power in the derived fourth-moment envelope.
    pub derived_fourth_moment_power: usize,
    /// Last conductor level already supplied by the individual Weil bound at
    /// the assumption threshold.
    ///
    /// Indeed the triangle estimate is the requested layer estimate with
    /// squared constant `2^(j-1)`.  Thus every level satisfying
    /// `2^(j-1)<=C ell^a` is unconditional.  The report uses a conservative
    /// exact lower power of two at `ell=threshold`.
    pub individual_weil_proved_through_level_at_threshold: usize,
    /// Existing exact endpoint implication fed by the derived envelope.
    pub derived_fourth_moment: FourthMomentBoundReport,
}

/// Exact Fourier second moment for one conductor family.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactConductorSecondMoment {
    /// Exact conductor level `j` in `T_(j,n)`.
    pub level: usize,
    /// Extension degree `n`.
    pub degree: usize,
    /// `sum_(chi exact level j) |S_chi(n)|^2`.
    pub value: u128,
}

/// Exact Cauchy--Schwarz ledger for the connected top-conductor character
/// family.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConnectedTopSecondMomentCauchy {
    /// Coefficient-prefix length.
    pub ell: usize,
    /// Endpoint degree.
    pub degree: usize,
    /// First exact conductor level in the connected family.
    pub first_top_level: usize,
    /// Number of characters in the union of the top conductor families.
    pub character_count: BigUint,
    /// Exact sum of `|S_chi(degree)|^2` over those characters.
    pub exact_second_moment: BigUint,
    /// Square of the Cauchy upper bound.
    pub cauchy_bound_square: BigUint,
    /// Square of the connected trace allowance.
    pub connected_allowance_square: BigUint,
    /// Largest integral second moment for which Cauchy would close.
    pub maximum_second_moment_for_candidate: BigUint,
    /// Smallest integer factor by which the observed second moment would have
    /// to improve before Cauchy could close.
    pub required_second_moment_saving_ceiling: BigUint,
}

impl ConnectedTopSecondMomentCauchy {
    /// Whether Cauchy with the exact finite second moment proves the connected
    /// trace candidate.
    #[must_use]
    pub fn proves_connected_top_candidate(&self) -> bool {
        self.cauchy_bound_square <= self.connected_allowance_square
    }
}

impl ExactConductorSecondMoment {
    /// Whether Cauchy--Schwarz with this moment proves the layer target.
    ///
    /// The required inequality is `value <= 2^(level-1+degree)` because
    /// there are `2^(level-1)` characters of exact level `level`.
    #[must_use]
    pub fn proves_square_root_layer_bound(self) -> bool {
        let Some(exponent) = self
            .level
            .checked_sub(1)
            .and_then(|value| value.checked_add(self.degree))
            .and_then(|value| u32::try_from(value).ok())
        else {
            return false;
        };
        let Some(bound) = 1_u128.checked_shl(exponent) else {
            return false;
        };
        self.value <= bound
    }
}

/// Exact full-family Parseval diagnostic for one Hayes coefficient level.
///
/// If `N_e(degree)` is the Mangoldt population of the principal-unit class
/// `e` and `mu = 2^(degree-ell)`, then `total_squared_deviation` is
///
/// ```text
/// sum_e (N_e(degree) - mu)^2
///   = 2^(-ell) sum_(chi != 1) |S_chi(degree)|^2.
/// ```
///
/// In particular, the identity class is nonempty whenever the total squared
/// deviation is strictly smaller than `mu^2`.  This sufficient condition is
/// deliberately reported separately from the exact value: failure of the
/// condition is not a counterexample to identity-class positivity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct IdentityClassFourierVariance {
    /// Number of prescribed leading zero coefficients.
    pub ell: usize,
    /// Extension degree `n`.
    pub degree: usize,
    /// Uniform class mean `2^(degree-ell)`.
    pub uniform_mean: u128,
    /// `sum_e (N_e(degree) - uniform_mean)^2` over all `2^ell` classes.
    pub total_squared_deviation: u128,
}

impl IdentityClassFourierVariance {
    /// Whether the exact Parseval value forces the identity class positive.
    #[must_use]
    pub fn proves_identity_class_positive(self) -> bool {
        let Some(mean_squared) = self.uniform_mean.checked_mul(self.uniform_mean) else {
            return false;
        };
        self.total_squared_deviation < mean_squared
    }
}

/// Exact Mangoldt populations of every principal-unit class.
///
/// `counts` uses the mixed-radix coordinate order returned by
/// [`principal_unit_structure`]: the first factor varies fastest.  Coordinate
/// zero is the identity class.  Keeping the compact coordinate order avoids a
/// second `O(2^ell)` table of polynomial representatives.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClassPopulationDistribution {
    /// Coefficient-prefix length.
    pub ell: usize,
    /// Extension degree `n`.
    pub degree: usize,
    /// Exact class populations in stable mixed-radix order.
    pub counts: Vec<u128>,
}

/// Exact Fourier `L^2` mass at one Efron--Stein coordinate weight.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EfronSteinSpectralWeightMass {
    /// Sum of `log2(order)` over the nontrivial cyclic coordinates.
    pub weight: usize,
    /// Number of characters having exactly this coordinate-support weight.
    pub character_count: usize,
    /// Exact sum of squared unnormalized Fourier magnitudes on those characters.
    pub spectral_second_moment: BigUint,
}

/// Exact Efron--Stein support decomposition of a Hayes discrepancy spectrum.
///
/// The cyclic factors of `E_ell` are treated as product coordinates.  For
/// every coordinate subset `S`, subgroup Parseval computes the Fourier mass
/// supported inside `S`; Boolean-lattice Mobius inversion then recovers the
/// exact mass whose support is precisely `S`.  No roots of unity or
/// floating-point transforms enter the retained masses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EfronSteinSpectralWeightReport {
    /// Coefficient-prefix length.
    pub ell: usize,
    /// Endpoint degree.
    pub degree: usize,
    /// `log2(order)` of each stable mixed-radix cyclic factor.
    pub factor_weights: Vec<usize>,
    /// Exact full spectral second moment `2^ell M_2`.
    pub total_spectral_second_moment: BigUint,
    /// Exact masses grouped by coordinate-support weight.
    pub weights: Vec<EfronSteinSpectralWeightMass>,
}

impl EfronSteinSpectralWeightReport {
    /// Evaluate the conditional weight-graded hypercontractive proxy
    ///
    /// ```text
    /// (sum_w C^(w/4) sqrt(f_w))^4,
    /// f_w=mass_w/total_mass.
    /// ```
    ///
    /// The exact masses are converted only for this finite diagnostic.  The
    /// result is conditional on a separate per-weight `(2,4)` theorem with
    /// constant `C`; it is not a certified upper bound supplied by this CAS.
    #[must_use]
    pub fn conditional_hypercontractive_root_ratio_proxy(&self, constant: f64) -> Option<f64> {
        if !constant.is_finite()
            || constant <= 0.0
            || self.total_spectral_second_moment == BigUint::from(0_u8)
        {
            return None;
        }
        let total = self.total_spectral_second_moment.to_f64()?;
        let mut sum = 0.0_f64;
        for row in &self.weights {
            let fraction = row.spectral_second_moment.to_f64()? / total;
            sum += constant.powf(row.weight.to_f64()? / 4.0) * fraction.sqrt();
        }
        Some(sum.powi(4))
    }
}

/// Exact raw fibre-product and connected virtual-count decomposition of one
/// Hayes population map.
///
/// If `N_e` is the fibre size above class `e`, then `sum_e N_e^r` counts the
/// `r`-fold fibre product.  Centering and subtracting the three pairings turns
/// these positive counts into the signed fourth cumulant.  The final value is
/// therefore a virtual Frobenius trace, not the cardinality of an off-diagonal
/// variety.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HayesConnectedFibreProductReport {
    /// Coefficient-prefix length.
    pub ell: usize,
    /// Polynomial degree.
    pub degree: usize,
    /// `sum_e N_e^2`.
    pub raw_pair_fibre_count: BigUint,
    /// `sum_e N_e^3`.
    pub raw_triple_fibre_count: BigUint,
    /// `sum_e N_e^4`.
    pub raw_quadruple_fibre_count: BigUint,
    /// `M_2=sum_e (N_e-mu)^2`.
    pub centered_second_moment: BigUint,
    /// `M_4=sum_e (N_e-mu)^4`.
    pub centered_fourth_moment: BigUint,
    /// `2^ell M_4-3M_2^2`, the signed connected virtual count.
    pub connected_fourth_cumulant: BigInt,
}

/// Exact comparison between the ordinary pointwise character fourth moment
/// and the product-constrained fourth moment entering the Hayes cumulant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HayesCharacterFourthMomentComparison {
    /// Coefficient-prefix length.
    pub ell: usize,
    /// Polynomial degree.
    pub degree: usize,
    /// `sum_chi |S_chi|^4`, reconstructed from spatial autocorrelations.
    pub pointwise_character_fourth_moment: BigUint,
    /// `sum_chi S_chi S_(chi^-1) = 2^ell M_2` by Parseval.
    pub character_second_moment: BigUint,
    /// One Wick contraction `(sum_chi S_chi S_(chi^-1))^2`.
    pub single_wick_pairing: BigUint,
    /// Sum of the three equal Wick contractions.
    pub three_wick_pairings: BigUint,
    /// `sum_(chi_1...chi_4=1) product_i S_(chi_i) = 2^(3ell) M_4`.
    pub product_constrained_fourth_moment: BigUint,
    /// Connected constrained numerator `2^(2ell) K_4` after subtracting the
    /// three Wick pairings.
    pub connected_product_constrained_numerator: BigInt,
}

/// Exact geometric budget for an Adams-operation identity-fibre proof of the
/// connected fourth-moment bound.
///
/// The product-one character fibre has dimension `3*ell`; its unrestricted
/// compactly-supported cohomology can reach degree `6*ell`.  After removing
/// the Adams weight factor `2^(2*degree)`, a mixed connected complex of
/// weights at most zero whose compactly-supported cohomology vanishes above
/// degree `4*ell` and has total Betti number at most `ell^4` would bound the
/// connected trace by the exact allowance recorded here.  This is a
/// sufficient-target ledger, not a claim that such a complex or any of those
/// properties has been proved.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HayesAdamsIdentityFibreRequirement {
    /// Coefficient-prefix length.
    pub ell: usize,
    /// Endpoint power-sum degree.
    pub degree: usize,
    /// Dimension `3*ell` of the product-one four-character fibre.
    pub identity_fibre_dimension: usize,
    /// Unrestricted top compactly-supported cohomology degree `6*ell`.
    pub ambient_max_cohomology_degree: usize,
    /// Dimension `2*ell` of every Wick pairing diagonal.
    pub wick_pairing_dimension: usize,
    /// Required top compactly-supported cohomology degree `4*ell`.
    pub required_max_cohomology_degree: usize,
    /// Required cohomological degree drop `2*ell` after Wick subtraction.
    pub required_cohomology_degree_drop: usize,
    /// Polynomial normalized Betti budget `ell^4`.
    pub normalized_betti_budget: BigUint,
    /// Weight-zero allowance `ell^4 * 2^(2*ell)`.
    pub normalized_connected_trace_allowance: BigUint,
    /// Unnormalized allowance `ell^4 * 2^(2*ell+2*degree)`.
    pub connected_trace_allowance: BigUint,
}

/// One coefficient in the cyclic/Foulkes decomposition of the long-cycle
/// virtual character.
///
/// With `F_(n,r)=Ind_(C_n)^(S_n) theta_r`, the coefficient of `F_(n,r)` is
/// `c_n(r)/phi(n)`.  The numerator is retained as an exact signed integer and
/// the common denominator is stored once in
/// [`SawinFoulkesEndpointLedger::coefficient_denominator`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FoulkesRamanujanCoefficient {
    /// Residue `r` modulo `n` indexing the cyclic character `theta_r`.
    pub residue: usize,
    /// Ramanujan sum `c_n(r)`.
    pub numerator: BigInt,
}

/// One coefficient after grouping equal induced cyclic characters.
///
/// The `n` residue-indexed Foulkes modules have only `tau(n)` distinct
/// characters.  Grouping by `gcd(n,r)` turns the rational Ramanujan
/// coefficients into the integral formula
///
/// ```text
/// p_n=sum_(k|n) mu(k) F_(n,n/k).
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FoulkesDistinctCoefficient {
    /// Divisor `k` of `n`.
    pub divisor: usize,
    /// Canonical residue `n/k` for the distinct induced cyclic character.
    pub cyclic_character_residue: usize,
    /// Grouped coefficient, expected to equal `mu(k)`.
    pub coefficient: BigInt,
}

/// One independently checked power-sum coefficient after substituting the
/// cyclic/Foulkes decomposition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FoulkesPowerSumCoefficient {
    /// Divisor `d` of `n` indexing the power sum `p_d^(n/d)`.
    pub divisor: usize,
    /// Exact numerator `sum_(r mod n) c_n(r)c_d(r)`.
    pub numerator: BigInt,
    /// Expected numerator: `n*phi(n)` for `d=n`, and zero otherwise.
    pub expected_numerator: BigInt,
}

/// Exact endpoint ledger for the long-cycle/cyclic-Foulkes compression of
/// Sawin's short-interval geometry.
///
/// This report proves the representation identity
///
/// ```text
/// p_n = sum_(r mod n) c_n(r)/phi(n) Ind_(C_n)^(S_n) theta_r
/// ```
///
/// by Ramanujan orthogonality and proves that the coefficient `l1` mass is
/// `2^omega(n)`.  It then inserts a caller-supplied *hypothetical* uniform
/// bound on each cyclic eigenspace into Sawin's exact weight exponent.  The
/// resulting endpoint comparison is conditional: this operation does not
/// prove the missing cyclic-eigenspace cohomology bound.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SawinFoulkesEndpointLedger {
    /// Polynomial degree `n`.
    pub degree: usize,
    /// Lemire/Hayes level `ell=ceil(n/2)-1`.
    pub ell: usize,
    /// Number `n-ell` of free short-interval coefficients.
    pub interval_dimension: usize,
    /// Number `ell` of prescribed leading coefficients.
    pub fixed_leading_coefficient_count: usize,
    /// Numerator `W` of Sawin's exact exponent `2^(W/2)` at `q=2`.
    pub sawin_weight_exponent_numerator: usize,
    /// Exact exponent `2h-W=floor(ell/2)` left after squaring the endpoint
    /// comparison against the main term `2^h`.
    pub squared_exponential_margin_exponent: usize,
    /// Euler totient `phi(n)`, the common coefficient denominator.
    pub coefficient_denominator: BigUint,
    /// Number `omega(n)` of distinct prime factors.
    pub distinct_prime_factor_count: usize,
    /// Exact coefficient numerators `c_n(r)`.
    pub coefficients: Vec<FoulkesRamanujanCoefficient>,
    /// Integral coefficients after grouping the `tau(n)` distinct Foulkes
    /// characters.
    pub distinct_coefficients: Vec<FoulkesDistinctCoefficient>,
    /// Orthogonality certificate for every divisor power-sum term.
    pub reconstructed_power_sum_coefficients: Vec<FoulkesPowerSumCoefficient>,
    /// Exact numerator `sum_r |c_n(r)|` of the coefficient `l1` mass.
    pub coefficient_l1_numerator: BigUint,
    /// Exact normalized coefficient mass `2^omega(n)`.
    pub coefficient_l1_mass: BigUint,
    /// Caller-supplied hypothetical uniform cyclic-eigenspace Betti bound.
    pub assumed_uniform_cyclic_betti_bound: BigUint,
    /// Square of `2^omega(n)` times the hypothetical Betti bound.
    pub assumed_squared_total_cost: BigUint,
    /// Exact squared exponential margin `2^floor(ell/2)`.
    pub squared_exponential_margin: BigUint,
    /// Main Mangoldt term `2^(n-ell)`.
    pub main_mangoldt_term: BigUint,
    /// Exact odd proper-power contribution or proved even upper bound.
    pub proper_prime_power_upper_bound: BigUint,
    /// Main term remaining after proper prime powers are removed.
    pub irreducible_margin: BigUint,
    /// Square of the complete hypothetical Sawin error, including `2^W`.
    pub assumed_squared_absolute_error: BigUint,
    /// Square of the remaining irreducible margin.
    pub squared_irreducible_margin: BigUint,
    /// Whether the hypothetical bound leaves a strict proper-power reserve.
    pub conditional_endpoint_closure: bool,
    /// Sawin's published generic single-representation Betti bound
    /// `3(n+2)^(n+ell)`.
    pub published_generic_single_betti_bound: BigUint,
    /// Square of the generic bound after the Foulkes coefficient mass.
    pub published_generic_squared_total_cost: BigUint,
    /// Whether the published generic bound leaves a proper-power reserve.
    pub published_generic_endpoint_closure: bool,
    /// Wan--Zhang's 2026 complete-intersection bound
    /// `binom(n-1,ell-1)(ell+1)^n` for the ordered-root variety.
    pub wan_zhang_complete_intersection_betti_bound: BigUint,
    /// Square of the Wan--Zhang bound after the Foulkes coefficient mass.
    pub wan_zhang_squared_total_cost: BigUint,
    /// Whether the Wan--Zhang bound leaves a proper-power reserve.
    pub wan_zhang_endpoint_closure: bool,
}

/// Exact long-cycle fixed-locus and Euler-trace ledger at a Lemire endpoint.
///
/// Let `c=(1 2 ... n)` act on Sawin's ordered-root short-interval variety
/// `X_(n,ell,0)`.  A `c`-fixed tuple has every root equal to one scalar `a`,
/// so its `j`th prescribed elementary symmetric function is
/// `binom(n,j) a^j`.  Lucas's theorem makes the least positive `j` with odd
/// binomial coefficient equal to the lowest set bit of `n`.  Consequently the
/// fixed locus is a point when that index is at most `ell`, and an affine line
/// otherwise.
///
/// Both loci have compactly supported Euler characteristic one.  More
/// generally, write `n=2^a b` with `b` odd.  The Deligne--Lusztig finite-order
/// trace formula first fixes the order-`b` part of the cycle and leaves the
/// order-`2^a` part acting on that locus.  When `b>1`, the first `ell`
/// coefficients of `G(x)^b` force the degree-`2^a` block polynomial to be
/// `G(x)=x^(2^a)`, so the reduced locus is a point.  Thus every non-power-of-two
/// degree also has total cycle Euler trace one by that route.
///
/// Uniformly, however, `X_(n,ell,0)` is a homogeneous affine cone.  Its vertex
/// contributes one, while its punctured part is a `G_m`-torsor over the
/// projectivization and has zero unweighted equivariant Euler trace.  This
/// proves total cycle Euler trace one even at power-of-two degrees.  The top
/// compactly supported cohomology is the one-dimensional trivial `S_n`
/// representation, and subtraction gives zero alternating trace on all
/// non-top cohomology.  With `r`th Frobenius inserted, the `G_m` factor is
/// `2^r-1`, not zero, so the argument supplies no weighted cancellation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SawinLongCycleEulerReport {
    /// Polynomial degree `n`.
    pub degree: usize,
    /// Lemire/Hayes level `ell=ceil(n/2)-1`.
    pub ell: usize,
    /// Dimension `n-ell` of the ordered-root complete intersection.
    pub interval_dimension: usize,
    /// Least positive `j` for which `binom(n,j)` is odd.
    pub first_odd_binomial_index: usize,
    /// Whether one prescribed equation forces the common fixed root to zero.
    pub has_active_odd_binomial_constraint: bool,
    /// Full-cycle fixed-locus dimension: zero for a point and one for an
    /// affine line.
    pub full_cycle_fixed_locus_dimension: usize,
    /// Compactly supported Euler characteristic of the fixed locus.
    pub fixed_locus_compact_euler_characteristic: i8,
    /// Order `2^a` of the characteristic-two part of the long cycle.
    pub wild_cycle_order: usize,
    /// Odd order `b` of the prime-to-characteristic part of the long cycle.
    pub tame_cycle_order: usize,
    /// Dimension of the locus fixed by the prime-to-characteristic part.
    pub tame_fixed_locus_dimension: usize,
    /// Whether Deligne--Lusztig reduction collapses the cycle trace to a point.
    pub cycle_trace_reduced_to_point: bool,
    /// Cycle trace of the cone vertex.
    pub cone_vertex_cycle_trace: i8,
    /// Alternating cycle trace of the punctured cone, using
    /// `chi_c(G_m)=0`.
    pub punctured_cone_alternating_cycle_trace: i8,
    /// Value `n` of the power-sum character `p_n` on an `n`-cycle.
    pub power_sum_value_on_long_cycle: usize,
    /// Centralizer order `n` of an `n`-cycle in `S_n`.
    pub long_cycle_centralizer_order: usize,
    /// Scalar in `<chi,p_n>=scalar*Tr(c|chi)`, certified to equal one.
    pub power_sum_projection_scalar: usize,
    /// Top compactly supported cohomological degree `2(n-ell)`.
    pub top_compact_cohomology_degree: usize,
    /// Long-cycle trace on the one-dimensional trivial top cohomology.
    pub top_cycle_trace: i8,
    /// Alternating total long-cycle trace.
    pub total_alternating_cycle_trace: i8,
    /// Alternating long-cycle trace on all non-top cohomology.
    pub non_top_alternating_cycle_trace: i8,
    /// Multiplicative factor `2^1-1` retained by the punctured cone after one
    /// binary Frobenius is inserted.
    pub binary_frobenius_projective_trace_factor: usize,
    /// Explicit boundary: Euler cancellation alone certifies no
    /// Frobenius-weighted trace estimate.
    pub frobenius_weighted_cancellation_certified: bool,
}

/// Projective eigenline obstruction to a free long-cycle quotient.
///
/// A projective point fixed by the full cycle need only be an eigenline, not
/// an affine fixed vector.  Over the algebraic closure, the cyclic shift has
/// one eigenline for every root of `z^b-1`.  For an eigenvalue of order
/// `e|b`, the first potentially nonzero prescribed coefficient has index
/// `e*2^a`.  At the half-degree endpoint this exceeds `ell` exactly when
/// `e=b`: every proper divisor of odd `b` is at most `b/3`.  The surviving
/// primitive eigenlines have root polynomial
///
/// ```text
/// product_(i=0)^(n-1) (x-lambda^i A) = x^n-A^n.
/// ```
///
/// Hence the reduced fixed locus has `phi(b)` geometric points (including one
/// when `b=1`).  It is certified reduced only when `n` is odd; at even degree
/// the cycle is wild and the fixed scheme may carry nilpotents.  In particular
/// the projective action is never free.
///
/// At odd degree, put `a_i=A*lambda^i` on a surviving primitive eigenline.
/// Since
///
/// ```text
/// product_i (1-u*a_i) = 1-u^n*A^n,
/// ```
///
/// the `j`th Jacobian row of the equations `e_1=...=e_ell=0` is
/// `((a_i)^(j-1))_i`.  These are `ell` distinct Vandermonde rows, so the
/// endpoint fibre is smooth there.  Fourier modes show that, after removing
/// the radial direction, the relative cycle weights on its projective tangent
/// space are `lambda^1,...,lambda^(n-ell-1)`.  None is one, so the fixed points
/// are transverse.  This local calculation still does not bound the different
/// correspondence `Frob*c`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SawinTameEigenlineLocalStatus {
    /// The cycle has nontrivial characteristic-two order, so the report makes
    /// no reducedness, smoothness, or transversality claim.
    NotCertifiedWild,
    /// The odd-order cycle eigenlines are smooth and their fixed points are
    /// transverse, by the Vandermonde Jacobian and tangent-weight calculation.
    SmoothTransverse,
}

/// Exact projective long-cycle eigenline and tame local-geometry report.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SawinProjectiveEigenlineReport {
    /// Polynomial degree `n`.
    pub degree: usize,
    /// Lemire/Hayes level `ell=ceil(n/2)-1`.
    pub ell: usize,
    /// Order `2^a` of the wild part of the cycle.
    pub wild_cycle_order: usize,
    /// Odd order `b` of the tame part of the cycle.
    pub tame_cycle_order: usize,
    /// Number `phi(b)` of primitive tame eigenvalues.
    pub primitive_tame_eigenvalue_count: usize,
    /// Number of geometric points in the reduced projective fixed locus.
    pub reduced_projective_fixed_point_count: usize,
    /// Whether the full cycle is tame, making its projective fixed scheme
    /// reduced and the ordinary Lefschetz fixed-point formula applicable.
    pub projective_fixed_scheme_reduced_certified: bool,
    /// Ordinary long-cycle trace on projective cohomology in the tame case.
    pub tame_projective_euler_trace: Option<usize>,
    /// Rank `ell` of the endpoint Jacobian at every surviving eigenline.
    ///
    /// This is certified only in the tame odd-degree case, where the
    /// eigenvalue orbit is separable.  The Jacobian rows are the first `ell`
    /// Vandermonde rows `((lambda^i)^(j-1))_i`.
    pub tame_eigenline_jacobian_rank: Option<usize>,
    /// Dimension `n-ell` of the affine tangent space at a tame eigenline.
    pub tame_affine_tangent_dimension: Option<usize>,
    /// Dimension `n-ell-1` of the projective tangent space at a tame
    /// eigenline.
    pub tame_projective_tangent_dimension: Option<usize>,
    /// Exponents of the nontrivial long-cycle eigenvalues on the projective
    /// tangent space, relative to the eigenvalue of the fixed line.
    ///
    /// For odd endpoint degree these are exactly `1..n-ell`.
    pub tame_projective_tangent_weight_exponents: Vec<usize>,
    /// Complementary relative weights on the normal space in projective
    /// space.  For odd endpoint degree these are exactly `n-ell..n`.
    pub tame_projective_normal_weight_exponents: Vec<usize>,
    /// Scheme-theoretic local status at the surviving cycle eigenlines.
    pub tame_eigenline_local_status: SawinTameEigenlineLocalStatus,
    /// Explicit rejection of a free projective cyclic-torsor reduction.
    pub projective_long_cycle_action_free: bool,
    /// Explicit boundary: this fixed-locus calculation proves no weighted
    /// Frobenius trace estimate.
    pub frobenius_weighted_trace_bound_certified: bool,
}

/// Scheme-theoretic status of the odd-endpoint `Frob*c` fixed locus.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SawinOddFrobeniusCycleLocalStatus {
    /// Every projective fixed point is smooth, the zero differential of
    /// Frobenius makes the fixed intersection transverse, and its local
    /// intersection multiplicity is one.
    SmoothTransverseUnitTerms,
}

/// Exact local geometry of the odd-endpoint `Frob*c` fixed locus.
///
/// A point fixed by binary Frobenius followed by an `n`-cycle is determined
/// by one element whose Frobenius orbit has degree `e|n`; its coordinate
/// polynomial is `Q^(n/e)`.  When `n` is odd, every multiplicity `n/e` is
/// odd.  If `e<n`, then `e<=n/3<=ell-1`, and the first `e` zero coefficients
/// recover `Q` triangularly, forcing `Q=x^e`.  Thus every proper-orbit stratum
/// is the affine cone vertex, while every nonvertex point has `n` distinct
/// coordinates.
///
/// On the zero-coefficient fibre, the Jacobian rows at a point with
/// coordinates `a_i` are `(a_i^(j-1))_i`.  They therefore have rank `ell` at
/// every nonvertex fixed point.  Absolute Frobenius has zero differential, so
/// the graph of `Frob*c` meets the diagonal transversely there and every local
/// intersection term is one.  This removes singular local terms but does not
/// bound their global sum.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SawinOddFrobeniusCycleFixedLocusReport {
    /// Odd endpoint degree `n=2ell+1`.
    pub degree: usize,
    /// Lemire/Hayes level `ell=(n-1)/2`.
    pub ell: usize,
    /// Proper Frobenius-orbit degrees `e|n`.
    pub proper_orbit_degrees: Vec<usize>,
    /// Largest proper orbit degree (one when `n` is prime).
    pub largest_proper_orbit_degree: usize,
    /// Every proper-orbit fixed stratum collapses to the affine cone vertex.
    pub proper_orbit_strata_collapse_to_vertex_certified: bool,
    /// Every nonvertex fixed point has exact Frobenius orbit degree `n`.
    pub nonvertex_exact_orbit_degree_certified: bool,
    /// Rank `ell` of the zero-coefficient Jacobian at every nonvertex point.
    pub nonvertex_jacobian_rank: usize,
    /// Complete scheme-theoretic local status of the projective fixed locus.
    pub projective_local_status: SawinOddFrobeniusCycleLocalStatus,
    /// Explicit boundary: smooth transverse local terms give no numerical
    /// estimate for their global Frobenius trace.
    pub frobenius_weighted_trace_bound_certified: bool,
}

/// One repeated-root stratum selected by a long-cycle Frobenius condition.
///
/// If the distinct-root orbit has degree `e|n`, its characteristic polynomial
/// is `Q(x)^(n/e)`.  In characteristic two, writing the multiplicity as
/// `2^v a` with `a` odd shows that only coefficient indices divisible by
/// `2^v` can be nonzero.  When `v=0`, the first `e` coefficients of `Q^a`
/// determine the coefficients of `Q` triangularly.  Thus the low-
/// characteristic failure on these long-cycle strata is confined to genuine
/// Frobenius-square proper powers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HastMateiLongCycleStratum {
    /// Degree `e` of the distinct-root orbit/base polynomial.
    pub base_degree: usize,
    /// Uniform root multiplicity `n/e`.
    pub multiplicity: usize,
    /// Lowest set bit `2^v` of the multiplicity.
    pub frobenius_coefficient_stride: usize,
    /// Whether the multiplicity is odd.
    pub odd_multiplicity: bool,
    /// Whether the first `e` output coefficients recover `Q` triangularly.
    pub triangular_base_recovery_certified: bool,
    /// Whether the stratum consists of characteristic-two squares.
    pub frobenius_square_stratum: bool,
}

/// Exact endpoint translation of the Hast--Matei variance geometry.
///
/// The report separates two facts that must not be conflated.  First, the
/// top-weight `X_(2,n,h)` representation contributes only `ell-1` hook
/// characters to a pair of long cycles.  Second, even this idealized leading
/// second moment does not give a pointwise endpoint bound after Cauchy.  It
/// also classifies every repeated-root stratum compatible with a long-cycle
/// Frobenius condition, isolating the characteristic-two obstruction to
/// Frobenius-square proper powers.  No bound on the full connected trace is
/// asserted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HastMateiLongCycleEndpointReport {
    /// Polynomial degree `n`.
    pub degree: usize,
    /// Lemire/Hayes level `ell=ceil(n/2)-1`.
    pub ell: usize,
    /// Short-interval tail degree `h=n-ell-1=floor(n/2)`.
    pub short_interval_tail_degree: usize,
    /// Number `n-h-1=ell` of equal-leading-coefficient equations.
    pub coefficient_equation_count: usize,
    /// Repeated-root threshold `n-h-2=ell-1` in Hast--Matei.
    pub repeated_root_threshold: usize,
    /// Number `ell-1` of hook representations surviving on two long cycles.
    pub top_weight_long_cycle_hook_count: usize,
    /// Frobenius exponent `n-1` on the top weight piece.
    pub top_weight_frobenius_exponent: usize,
    /// Idealized top-weight contribution `(ell-1)2^n` to the global variance.
    pub top_weight_global_second_moment: BigUint,
    /// Square of the identity-class mean `2^(n-ell)`.
    pub squared_identity_class_mean: BigUint,
    /// Numerator `ell-1` in the squared Cauchy/main ratio.
    pub pointwise_deficit_numerator: usize,
    /// Denominator `2^(n-2ell)` in the squared Cauchy/main ratio.
    pub pointwise_deficit_denominator: BigUint,
    /// Whether the idealized top-weight second moment alone closes endpoint.
    pub top_weight_second_moment_alone_closes_endpoint: bool,
    /// Long-cycle-compatible repeated-root strata below the singular cutoff.
    pub repeated_root_strata: Vec<HastMateiLongCycleStratum>,
    /// Explicit theorem boundary: no connected Frobenius trace bound follows.
    pub connected_frobenius_trace_bound_certified: bool,
}

/// Exact least-period reduction of the Lemire class indicator.
///
/// For `N=2^n-1`, let `delta_j` be the indicator of the `n`-bit residues of
/// Hamming weight `j`.  Fourier inversion of the characteristic elementary
/// symmetric functions gives the coefficient function
///
/// ```text
/// Gamma_(n,ell) = product_(j=1)^ell (delta_0 + delta_j)
/// ```
///
/// in `GF(2)[Z/N]`.  On `GF(2^n)^*`, its Fourier transform is exactly
/// `product_j (1+sigma_j)`, the indicator that the first `ell` coefficients
/// of the degree-`n` characteristic polynomial vanish.  The
/// Tuxanidy--Wang support theorem therefore proves Lemire at degree `n` if
/// the least period of `Gamma` does not divide
/// `lcm_(d|n,d<n)(2^d-1) = N/Phi_n(2)`.  The exact (rather than merely
/// sufficient) support test applies one difference for every maximal proper
/// subfield.  If `p` runs over the distinct prime divisors of `n`, put
/// `T_p=2^(n/p)-1`; then
///
/// ```text
/// product_(p|n) (1+tau_(T_p)) Gamma != 0
/// ```
///
/// if and only if the common coefficient-zero set contains an element of
/// exact degree `n`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TuxanidyLemirePeriodReport {
    /// Target polynomial degree `n`.
    pub degree: usize,
    /// Lemire prefix length `ell=ceil(n/2)-1`.
    pub ell: usize,
    /// Cyclic group order `N=2^n-1`.
    pub cyclic_order: usize,
    /// Support sizes of the factors `delta_0+delta_j`, `1<=j<=ell`.
    pub factor_support_sizes: Vec<usize>,
    /// Support size of the exact group-algebra product `Gamma`.
    pub convolution_support_size: usize,
    /// Least positive translation period of `Gamma`.
    pub least_period: usize,
    /// `lcm_(d|n,d<n)(2^d-1)`, equal to `N/Phi_n(2)`.
    pub proper_subfield_exponent_lcm: usize,
    /// Translation periods `2^(n/p)-1` of the maximal proper subfields,
    /// ordered by the distinct prime divisors `p` of `n`.
    pub maximal_proper_subfield_periods: Vec<usize>,
    /// Support size after applying every maximal-subfield difference
    /// `1+tau_(2^(n/p)-1)`.
    pub exact_degree_difference_support_size: usize,
    /// First nonzero coefficient of the exact-degree difference, if any.
    pub first_exact_degree_difference_witness: Option<usize>,
    /// Whether the computed period is the maximum `N`.
    pub maximum_least_period: bool,
    /// Whether the exact Tuxanidy--Wang sufficient condition holds.
    pub period_criterion_holds: bool,
    /// Logical relation between the older single-period condition and the
    /// exact maximal-subfield criterion at this degree.
    pub period_criterion_relation: TuxanidyPeriodCriterionRelation,
    /// Explicit epistemic boundary between the cited general implication and
    /// the still-open universal period statement.
    pub theorem_boundary: TuxanidyPeriodTheoremBoundary,
    /// Exact number of parity-toggle cells used by the convolution.
    pub convolution_cells: usize,
}

/// The theorem boundary retained by a Tuxanidy--Lemire period report.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TuxanidyPeriodTheoremBoundary {
    /// Fourier inversion certifies the maximal-subfield difference
    /// equivalence; the report does not certify its universal nonvanishing.
    ExactDegreeDifferenceCertifiedUniversalNonvanishingOpen,
}

/// Relation between the common-period and exact maximal-subfield tests.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TuxanidyPeriodCriterionRelation {
    /// Proper subfields are nested, so the one maximal-subfield period is
    /// equivalent to exact-degree support.
    ExactPrimePowerDegree,
    /// The common exponent subgroup overcovers the union of proper subfields;
    /// failure of its period remains sufficient but is not necessary.
    SufficientOnlyMixedDivisorDegree,
}

impl TuxanidyLemirePeriodReport {
    /// Whether the exact maximal-subfield difference proves that an
    /// admissible element of degree `n` exists in this bounded row.
    #[must_use]
    pub const fn exact_degree_support_criterion_holds(&self) -> bool {
        self.exact_degree_difference_support_size != 0
    }
}

/// Hypothetical polynomial bound on every effective cyclic Foulkes Betti
/// multiplicity beyond one degree threshold.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SawinFoulkesPolynomialBettiAssumption {
    /// First degree governed by the assumption.
    pub threshold: usize,
    /// Exponent `a` in `B(n,r)<=n^a`.
    pub polynomial_power: u32,
}

impl Default for SawinFoulkesPolynomialBettiAssumption {
    fn default() -> Self {
        Self {
            threshold: 401,
            polynomial_power: 4,
        }
    }
}

/// One residue-class base check for the polynomial cyclic-Betti implication.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SawinFoulkesPolynomialBaseRow {
    /// Base degree for one of the twelve floor/ceiling residue classes.
    pub degree: usize,
    /// Coarse squared cost `n^(2(a+1))`.
    pub squared_polynomial_cost: BigUint,
    /// Squared half-main allowance `2^(floor((ceil(n/2)-1)/2)-2)`.
    pub squared_half_main_margin: BigUint,
    /// Exact odd proper-power contribution or proved even upper bound.
    pub proper_prime_power_upper_bound: BigUint,
    /// Half of the main Mangoldt term.
    pub half_main_mangoldt_term: BigUint,
}

/// Checked arithmetic implication from a polynomial cyclic-Betti theorem to
/// every Lemire degree beyond a finite handoff.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SawinFoulkesPolynomialBettiReport {
    /// Hypothetical theorem whose arithmetic consequence was checked.
    pub assumption: SawinFoulkesPolynomialBettiAssumption,
    /// Exponent `2(a+1)` after using `2^omega(n)<=n` and squaring.
    pub squared_polynomial_power: u32,
    /// Twelve exact base inequalities covering every floor/ceiling residue.
    pub base_rows: Vec<SawinFoulkesPolynomialBaseRow>,
    /// Left side `(threshold+12)^(2(a+1))` of the induction-step ratio.
    pub step_left: BigUint,
    /// Right side `8 threshold^(2(a+1))` of the induction-step ratio.
    pub step_right: BigUint,
}

/// Exact Möbius sums in every principal-unit class.
///
/// `values[e]` is the signed sum of the polynomial Möbius function over all
/// degree-`degree` monic polynomials whose leading-coefficient class is `e`.
/// The stable mixed-radix class order is the same as for
/// [`ClassPopulationDistribution`], so coordinate zero is the identity.
///
/// This is a diagnostic for parity-breaking decompositions.  It does not
/// assert cancellation beyond the admitted finite degree.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClassMobiusDistribution {
    /// Coefficient-prefix length.
    pub ell: usize,
    /// Polynomial degree.
    pub degree: usize,
    /// Exact signed Möbius sum in every class.
    pub values: Vec<i128>,
}

/// Additive Fourier spectrum of classwise Möbius sums after unit inversion.
///
/// Coordinate `a` stores
///
/// ```text
/// H_degree(a)=sum_(e in E_ell) M_degree(e)
///                 (-1)^<a,e^(-1)-1>,
/// ```
///
/// where the coefficients of `e^(-1)-1` in degrees `1..=ell` are packed
/// low-degree first.  This is a finite diagnostic; it makes no universal
/// cancellation claim.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct InverseAdditiveMobiusSpectrum {
    /// Coefficient-prefix length.
    pub ell: usize,
    /// Polynomial degree.
    pub degree: usize,
    /// Exact signed Walsh coefficients in packed additive-frequency order.
    pub values: Vec<i128>,
}

/// Exact finite stationary-fibre diagnostic for the binary
/// Berlekamp/inverse phase.
///
/// For monic constant-one polynomials `f` of the requested degree, put
///
/// ```text
/// w_a(f)=mu(f)(-1)^<a,f^(-1)-1>.
/// ```
///
/// On the squarefree locus, Berlekamp's characteristic-two Pellet formula
/// identifies `mu(f)` with the additive Berlekamp-discriminant phase (up to
/// the fixed degree sign).  Squareful inputs have weight zero.  The shift
/// subspace toggles the first `shift_dimension` free coefficients of `f`.
/// The same/opposite counts and their difference give the exact derivative
/// correlation over that subspace; no asymptotic cancellation is asserted.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryBerlekampInversePhaseReport {
    /// Principal-unit modulus is `x^(ell+1)`.
    pub ell: usize,
    /// Degree of the monic constant-one polynomials.
    pub degree: usize,
    /// Packed additive frequency, low coefficient first.
    pub frequency: usize,
    /// Number of low free coefficients toggled by the shift subspace.
    pub shift_dimension: usize,
    /// Total number `2^(degree-1)` of monic constant-one inputs.
    pub input_count: u128,
    /// Number of squarefree inputs, equivalently nonzero phase weights.
    pub squarefree_count: u128,
    /// Exact combined phase sum `B_degree(frequency)`.
    pub phase_sum: i128,
    /// Ordered nonzero pairs in one shift coset having the same phase sign.
    pub stationary_same_sign_pairs: u128,
    /// Ordered nonzero pairs in one shift coset having opposite phase signs.
    pub oscillating_opposite_sign_pairs: u128,
    /// Exact nonnegative shift-subspace correlation energy.
    pub shift_subspace_energy: u128,
    /// Cauchy upper bound for `phase_sum^2`: number of cosets times energy.
    pub cauchy_square_bound: u128,
    /// Trivial upper bound `squarefree_count^2` for `phase_sum^2`.
    pub trivial_square_bound: u128,
}

/// Exact characteristic-two Möbius-sign comparison for one binary
/// polynomial.
///
/// On the squarefree locus this compares three equivalent signs: direct
/// factorization, the Stickelberger--Swan integral discriminant modulo eight,
/// and the Arf invariant of the second trace form.  The Kronecker character
/// of the discriminant also encodes squareful inputs as Möbius value zero;
/// those inputs still do not receive an Arf sign.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BinarySecondTraceArfReport {
    /// Packed monic binary polynomial.
    pub polynomial: u64,
    /// Polynomial degree.
    pub degree: usize,
    /// Exact polynomial Möbius value in `{-1,0,1}`.
    pub mobius: i8,
    /// Integral-lift discriminant modulo eight on the squarefree locus.
    pub integral_discriminant_mod_eight: Option<u8>,
    /// Integral-lift discriminant modulo eight on every input, computed by
    /// fraction-free integer elimination.
    pub integral_discriminant_residue_mod_eight: u8,
    /// Whether the integral discriminant is odd, checked independently by
    /// the binary derivative gcd.
    pub integral_discriminant_is_odd: bool,
    /// Kronecker character `(2/Disc(F))` in `{-1,0,1}`.  The value is zero
    /// for an even discriminant, so it includes the squareful Möbius zero.
    pub kronecker_two_discriminant: i8,
    /// Dimension of the nondegenerate second-trace space: the whole algebra
    /// in even degree and its trace-zero subspace in odd degree.
    pub trace_form_dimension: usize,
    /// Rank of the polar form on that space.
    pub polar_rank: usize,
    /// Radical dimension of the polar form.
    pub radical_dimension: usize,
    /// Arf invariant on the squarefree locus.
    pub arf_invariant: Option<u8>,
    /// Degree-class correction, one for degrees `3,4,5,6 mod 8`.
    pub arf_degree_correction: u8,
    /// Common Berlekamp/Swan phase bit on the squarefree locus.
    pub sign_phase: Option<u8>,
}

/// One exact pairwise-difference type for second-trace quadratic forms.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BinarySecondTraceDifferenceType {
    /// Rank of the polar form of `Q_f+Q_g` on the common coefficient space.
    pub polar_rank: usize,
    /// Dimension of its radical.
    pub radical_dimension: usize,
    /// Whether `Q_f+Q_g` is nonzero on the polar radical.
    pub phase_nontrivial_on_radical: bool,
    /// Number of unordered distinct polynomial pairs of this type.
    pub pair_count: u128,
    /// Input-coefficient coset of the first stable witness.
    pub first_input_coset: usize,
    /// Inverse-coefficient coset of the first stable witness.
    pub first_inverse_coset: usize,
    /// First packed polynomial in the stable witness pair.
    pub first_left_polynomial: u64,
    /// Second packed polynomial in the stable witness pair.
    pub first_right_polynomial: u64,
}

/// One pair attaining the minimum polar rank among nonzero quadratic Gauss
/// correlations in simultaneous buckets.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BinarySecondTraceDifferenceWitness {
    /// Input-coefficient coset.
    pub input_coset: usize,
    /// Inverse-coefficient coset.
    pub inverse_coset: usize,
    /// First packed polynomial.
    pub left_polynomial: u64,
    /// Second packed polynomial.
    pub right_polynomial: u64,
    /// XOR of the packed polynomials.
    pub polynomial_difference: u64,
    /// Polar rank of the quadratic-form difference.
    pub polar_rank: usize,
}

/// Pairwise second-trace geometry inside simultaneous coefficient/inverse
/// buckets.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinarySecondTraceBucketDifferenceReport {
    /// Principal-unit modulus level.
    pub ell: usize,
    /// Polynomial degree.
    pub degree: usize,
    /// Number of free low coefficient bits in each input bucket.
    pub interval_degree: usize,
    /// Nonempty simultaneous coefficient/inverse buckets.
    pub occupied_bucket_count: usize,
    /// Squarefree polynomials retained across those buckets.
    pub squarefree_count: usize,
    /// Unordered distinct pairs compared within buckets.
    pub unordered_pair_count: u128,
    /// Stable rank/radical type table.
    pub types: Vec<BinarySecondTraceDifferenceType>,
    /// Minimum rank among pairs whose quadratic Gauss sum is nonzero.
    pub minimum_nonzero_gauss_rank: Option<usize>,
    /// Every pair attaining `minimum_nonzero_gauss_rank`.
    pub minimum_rank_witnesses: Vec<BinarySecondTraceDifferenceWitness>,
}

/// Exact four-term additive Fourier expansion of the real character modulo
/// eight.
///
/// Coefficients are in the basis `1,zeta_8,zeta_8^2,zeta_8^3`, using
/// `zeta_8^4=-1`.  The Gauss identity is
///
/// ```text
/// sum_(a=1,3,5,7) (2/a) zeta_8^(aD)
///   = 2 (2/D) (zeta_8-zeta_8^3).
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BinaryDyadicCharacterFourierReport {
    /// Input residue modulo eight.
    pub residue: u8,
    /// Kronecker character `(2/residue)`.
    pub kronecker_two: i8,
    /// Exact left-hand side in the cyclotomic basis.
    pub gauss_sum_basis: [i8; 4],
    /// Exact right-hand side in the same basis.
    pub expected_basis: [i8; 4],
}

/// One residue row in the auxiliary-unit quadratic projector over
/// `(Z/8Z)^x`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DyadicAuxiliaryProjectorResidue {
    /// Discriminant residue modulo eight.
    pub discriminant_residue: u8,
    /// Exact projector sum in the basis `1,zeta_8,zeta_8^2,zeta_8^3`.
    pub projector_cyclotomic_basis: [i8; 4],
    /// Closed-form right side `2(zeta_8-zeta_8^3)chi_8(D)`.
    pub expected_projector_cyclotomic_basis: [i8; 4],
    /// Exact normalized quadratic Gauss sum over the auxiliary unit group.
    pub normalized_gauss_cyclotomic_basis: [i8; 4],
    /// Size of the radical of the normalized phase polarization.
    pub radical_size: usize,
    /// Whether the normalized phase is trivial on its radical.
    pub phase_trivial_on_radical: bool,
}

/// Exact characteristic-two auxiliary-unit projector and polarization table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DyadicAuxiliaryQuadraticProjectorReport {
    /// Stable rows for `D=0,...,7`.
    pub residues: Vec<DyadicAuxiliaryProjectorResidue>,
}

/// A concrete failure of additivity for a normalized mod-four phase.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DyadicFibreModFourAdditivityWitness {
    /// First binary fibre coordinate.
    pub left: usize,
    /// Second binary fibre coordinate.
    pub right: usize,
    /// Normalized phase at `left`.
    pub left_phase_mod_four: u8,
    /// Normalized phase at `right`.
    pub right_phase_mod_four: u8,
    /// Normalized phase at `left xor right`.
    pub xor_phase_mod_four: u8,
    /// Sum of the two input phases modulo four.
    pub expected_xor_phase_mod_four: u8,
}

/// Exact obstruction to a projection-preserving central-extension model of
/// the pinned nonquadratic dyadic fibre.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DyadicFibreProjectionObstructionReport {
    /// Degree of each monic constant-one polynomial.
    pub polynomial_degree: usize,
    /// Number of affine binary fibre coordinates.
    pub fibre_dimension: usize,
    /// Coordinate mask relating the two discriminants.
    pub paired_coordinate_shift: usize,
    /// Full-support coefficient of the product-discriminant phase modulo eight.
    pub full_support_coefficient_mod_eight: u8,
    /// Lexicographically first exact additivity failure.
    pub witness: DyadicFibreModFourAdditivityWitness,
}

/// Coefficient counts at one support degree in the multilinear discriminant
/// polynomial modulo eight.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BinaryDiscriminantAnfDegreeRow {
    /// Number of coefficient variables in the monomial.
    pub support_degree: usize,
    /// Coefficients congruent to `1,3,5,7 mod 8`.
    pub odd_coefficient_count: usize,
    /// Coefficients congruent to `2 or 6 mod 8`.
    pub twice_odd_coefficient_count: usize,
    /// Coefficients congruent to `4 mod 8`.
    pub four_coefficient_count: usize,
}

/// Exact algebraic normal form of the integral binary discriminant phase
/// modulo eight, summarized by support degree and 2-adic valuation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryDiscriminantAnfReport {
    /// Degree of the monic constant-one polynomial family.
    pub polynomial_degree: usize,
    /// Free coefficient count, exactly `polynomial_degree-1`.
    pub variable_count: usize,
    /// Number of multilinear coefficients, exactly `2^variable_count`.
    pub coefficient_count: usize,
    /// Coefficient modulo eight of the monomial containing every free bit.
    pub full_support_coefficient_mod_eight: u8,
    /// Largest support degree carrying an odd coefficient.
    pub max_odd_support_degree: Option<usize>,
    /// Largest support degree carrying a coefficient twice an odd number.
    pub max_twice_odd_support_degree: Option<usize>,
    /// Largest support degree carrying coefficient four.
    pub max_four_support_degree: Option<usize>,
    /// Exact coefficient counts by monomial support degree.
    pub rows: Vec<BinaryDiscriminantAnfDegreeRow>,
}

impl BinaryBerlekampInversePhaseReport {
    /// Whether this shift-subspace Cauchy step improves on the trivial bound.
    #[must_use]
    pub const fn improves_trivial_bound(&self) -> bool {
        self.cauchy_square_bound < self.trivial_square_bound
    }
}

/// Exact annihilator-average of the combined Berlekamp/inverse shift energy.
///
/// Input cosets fix coefficients above `shift_dimension`; inverse cosets fix
/// inverse coefficients above `interval_degree`.  If `b_(C,D)` is the signed
/// Möbius sum in one simultaneous coset, `signed_coset_energy` is
/// `sum_(C,D)b_(C,D)^2`.  Additive orthogonality identifies this with the
/// average of [`BinaryBerlekampInversePhaseReport::shift_subspace_energy`]
/// over the annihilator of `W_interval_degree`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BinaryBerlekampShiftCorrelation {
    /// Packed shift in coefficients `x^1..=x^shift_dimension`.
    pub shift: usize,
    /// `x`-adic valuation of the actual shift polynomial; `None` for zero.
    pub valuation: Option<usize>,
    /// Number of ordered squarefree pairs surviving the inverse-coset test.
    pub supported_pairs: u128,
    /// Signed sum of `mu(f)mu(f+h)` over those pairs.
    pub signed_correlation: i128,
    /// Modulus degree after cancelling the common valuation of `h` and the
    /// inverse difference; absent for the diagonal shift.
    pub artin_schreier_modulus_degree: Option<usize>,
    /// Dimension of the kernel of `z -> z^2+h z` in that quotient.
    pub artin_schreier_kernel_dimension: Option<usize>,
    /// Proved unsigned support ceiling from the Artin--Schreier fibres.
    pub support_upper_bound: u128,
}

/// Witness fibre for the largest observed product-discriminant phase degree.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BinaryDyadicAutocorrelationFibreWitness {
    /// Packed low-coefficient shift.
    pub shift: usize,
    /// Fixed high-coefficient input coset.
    pub input_coset: usize,
    /// Exact packed inverse difference.
    pub inverse_difference: u64,
    /// Binary dimension of the affine fibre.
    pub fibre_dimension: usize,
    /// Largest support degree with an odd ANF coefficient.
    pub max_odd_support_degree: Option<usize>,
    /// Largest support degree with coefficient twice an odd number.
    pub max_twice_odd_support_degree: Option<usize>,
    /// Largest support degree with coefficient four.
    pub max_four_support_degree: Option<usize>,
    /// Exact dyadic-character sum on the fibre.
    pub signed_correlation: i128,
}

/// Aggregate product-discriminant correlation at one common `x`-adic
/// valuation of the shift and inverse difference.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BinaryDyadicValuationCorrelation {
    /// Common positive valuation.
    pub valuation: usize,
    /// Number of normalized parameters `h_0/w_0` in this layer.
    pub normalized_parameter_count: usize,
    /// Sum of absolute normalized-parameter correlations in this layer.
    pub parameterwise_absolute_correlation: u128,
    /// Signed correlation after combining the complete layer.
    pub signed_correlation: i128,
}

/// Modular support of the connected Witt spectrum at one exact conductor.
///
/// The two prime columns describe exact transforms over the corresponding
/// finite fields.  They are a finite diagnostic of complex character support,
/// not a proof that simultaneous modular vanishing is cyclotomic vanishing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BinaryConnectedWittConductorSpectrum {
    /// Exact principal-unit character conductor; absent for the trivial row.
    pub exact_conductor: Option<usize>,
    /// Characters in this conductor row.
    pub character_count: usize,
    /// Nonzero transform values modulo `998244353`.
    pub prime_one_nonzero_count: usize,
    /// Nonzero transform values modulo `1004535809`.
    pub prime_two_nonzero_count: usize,
    /// Characters nonzero in both modular transforms.
    pub jointly_nonzero_count: usize,
    /// Characters on which the two modular zero tests disagree.
    pub zero_status_disagreement_count: usize,
}

/// One primitive additive modulo-eight phase in the connected Witt spectrum.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryConnectedWittAdditivePhaseSpectrum {
    /// Odd multiplier `1,3,5,7` in `zeta_8^(multiplier*residue)`.
    pub multiplier: u8,
    /// Number of transform values nonzero modulo the first native prime.
    pub prime_one_nonzero_count: usize,
    /// Number of transform values nonzero modulo the second native prime.
    pub prime_two_nonzero_count: usize,
    /// Characters on which the two modular zero tests disagree.
    pub zero_status_disagreement_count: usize,
    /// Modular support classified by exact principal-unit conductor.
    pub conductor_spectra: Vec<BinaryConnectedWittConductorSpectrum>,
}

/// One connected signed spectrum after embedding every normalized valuation
/// layer into the common truncated 2-typical Witt group.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryConnectedWittSpectrumReport {
    /// Principal-unit level of the common target group.
    pub ell: usize,
    /// Number of signed normalized `(valuation,parameter)` inputs.
    pub normalized_parameter_count: usize,
    /// Occupied target Witt classes after blockwise Verschiebung embedding.
    pub embedded_support_count: usize,
    /// Signed sum of the embedded function, equal to the off-diagonal energy.
    pub signed_total: i128,
    /// Sum of absolute embedded class values.
    pub embedded_absolute_sum: u128,
    /// Exact spatial second moment of the embedded signed function.
    pub spatial_second_moment: BigUint,
    /// Exact spectral second moment, including the principal character.
    pub spectral_second_moment: BigUint,
    /// Exact spectral fourth moment from the group autocorrelation identity.
    pub spectral_fourth_moment: BigUint,
    /// Total product-discriminant phase populations at residues `0..=7`.
    pub phase_residue_totals: [u128; 8],
    /// Primitive additive phase spectra whose Gauss combination reconstructs
    /// the signed dyadic spectrum character by character.
    pub additive_phase_spectra: Vec<BinaryConnectedWittAdditivePhaseSpectrum>,
    /// Complementary-family autocorrelation at the identity shift.
    pub phase_complementarity_identity: BigUint,
    /// Largest absolute complementary-family autocorrelation away from the
    /// identity shift.
    pub phase_complementarity_max_off_identity: BigUint,
    /// Sum of squares of all complementary-family autocorrelations.
    ///
    /// The four primitive phases are complementary exactly when this equals
    /// `phase_complementarity_identity^2`.
    pub phase_complementarity_square_sum: BigUint,
    /// Modular spectrum rows in stable conductor order.
    pub conductor_spectra: Vec<BinaryConnectedWittConductorSpectrum>,
}

/// Exact restricted `Z/8` product-discriminant phases on all affine
/// Artin--Schreier fibres contributing to one annihilator energy.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryDyadicAutocorrelationFibreReport {
    /// Principal-unit modulus is `x^(ell+1)`.
    pub ell: usize,
    /// Polynomial degree.
    pub degree: usize,
    /// Low-coefficient/inverse-interval dimension.
    pub interval_degree: usize,
    /// Number of nonzero shifts.
    pub nonzero_shift_count: usize,
    /// Number of nonempty exact affine fibres.
    pub fibre_count: usize,
    /// Total points across all fibres and nonzero shifts.
    pub total_fibre_points: u128,
    /// Largest affine-fibre dimension.
    pub max_fibre_dimension: usize,
    /// Fibres whose product-discriminant phase is at most quadratic modulo
    /// eight in the recovered affine coordinates.
    pub at_most_quadratic_fibre_count: usize,
    /// Total points in the at-most-quadratic fibres.
    pub at_most_quadratic_fibre_points: u128,
    /// Sum of squared correlations on the at-most-quadratic fibres.
    pub at_most_quadratic_correlation_square_sum: BigUint,
    /// Fibres whose primitive modulo-eight Walsh spectrum is exactly flat.
    pub generalized_bent_fibre_count: usize,
    /// Total points in the generalized-bent fibres.
    pub generalized_bent_fibre_points: u128,
    /// Total points in the complementary nonquadratic fibres.
    pub nonquadratic_fibre_points: u128,
    /// Signed dyadic-character correlation on the nonquadratic fibres.
    pub nonquadratic_signed_correlation: i128,
    /// Sum of absolute fibre correlations on the nonquadratic fibres.
    pub nonquadratic_absolute_correlation: u128,
    /// Sum of squared correlations on the nonquadratic fibres.
    pub nonquadratic_correlation_square_sum: BigUint,
    /// Sum of absolute correlations before combining any exact fibres.
    pub fibrewise_absolute_correlation: u128,
    /// Sum of squared signed correlations before combining exact fibres.
    ///
    /// Subtracting `total_fibre_points` gives the exact within-fibre
    /// off-diagonal dyadic correlation.  This is the nonnegative counting
    /// half of the proposed connected square-root estimate; no sign or
    /// asymptotic claim is attached to the finite value.
    pub fibre_correlation_square_sum: BigUint,
    /// Fibres with nonzero signed correlation.
    pub nonzero_fibre_correlation_count: usize,
    /// Nonzero fibres whose correlation magnitude is an exact power of two.
    pub power_of_two_magnitude_fibre_count: usize,
    /// Number of exact `(shift,inverse difference)` parameter pairs after
    /// combining the high-coefficient input cosets.
    pub shift_inverse_pair_count: usize,
    /// Absolute correlation after that first parameter aggregation.
    pub shift_inverse_pairwise_absolute_correlation: u128,
    /// Number of normalized Artin--Schreier parameters `(valuation,h_0/w_0)`,
    /// where `h_0/w_0=f(f+h)` in the corresponding truncated quotient.
    pub normalized_parameter_count: usize,
    /// Absolute correlation after grouping by the normalized parameters.
    pub normalized_parameterwise_absolute_correlation: u128,
    /// Absolute correlation after grouping only by common `x`-adic valuation.
    pub valuationwise_absolute_correlation: u128,
    /// Exact signed and intermediate absolute values at each valuation.
    pub valuation_correlations: Vec<BinaryDyadicValuationCorrelation>,
    /// Connected signed Witt embedding and spectrum before absolute values.
    pub connected_witt_spectrum: BinaryConnectedWittSpectrumReport,
    /// Fibres attaining their full affine dimension as ANF support degree.
    pub full_degree_fibre_count: usize,
    /// Largest restricted ANF support degree.
    pub max_phase_support_degree: usize,
    /// Sum of all nonzero-shift dyadic character correlations.
    pub off_diagonal_signed_correlation: i128,
    /// Witness for `max_phase_support_degree`.
    pub worst_fibre: Option<BinaryDyadicAutocorrelationFibreWitness>,
}

impl BinaryDyadicAutocorrelationFibreReport {
    /// Exact within-fibre off-diagonal dyadic correlation.
    ///
    /// If `c_F=sum_(x in F) epsilon(x)`, then this returns
    /// `sum_F c_F^2-sum_F #F`.  A nonpositive value is precisely the proposed
    /// counting inequality `sum_F c_F^2<=total_fibre_points`.
    #[must_use]
    pub fn within_fibre_off_diagonal_correlation(&self) -> BigInt {
        BigInt::from(self.fibre_correlation_square_sum.clone())
            - BigInt::from(self.total_fibre_points)
    }

    /// Whether this finite row satisfies the proposed nonpositive
    /// within-fibre off-diagonal correlation inequality.
    #[must_use]
    pub fn satisfies_nonpositive_within_fibre_correlation(&self) -> bool {
        self.fibre_correlation_square_sum <= BigUint::from(self.total_fibre_points)
    }
}

/// Kernel size of one binary truncated Artin--Schreier shift map.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BinaryArtinSchreierKernelReport {
    /// Quotient ring is `GF(2)[x]/x^modulus_degree`.
    pub modulus_degree: usize,
    /// Valuation of `h`; `None` means `h=0` in the quotient.
    pub shift_valuation: Option<usize>,
    /// Binary dimension of `ker(z -> z^2+h z)`.
    pub kernel_dimension: usize,
    /// Exact kernel size `2^kernel_dimension`.
    pub kernel_size: u128,
}

/// Exact parallelogram identity for principal-unit inverse differences.
///
/// In a characteristic-two truncated polynomial ring, put
/// `delta_h(f)=f^(-1)+(f+h)^(-1)`.  Clearing the four unit denominators gives
///
/// ```text
/// delta_h(f)=delta_h(f+t)  <=>  h t(t+h)=0.
/// ```
///
/// The right side is independent of `f`.  Consequently the square of every
/// exact inverse-difference fibre sum is a restricted four-shift correlation
/// over the parallelogram `f,f+h,f+t,f+h+t`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BinaryInverseDifferenceParallelogramReport {
    /// Principal-unit modulus is `x^(ell+1)`.
    pub ell: usize,
    /// Packed constant-one input unit `f`.
    pub input_unit: u64,
    /// Packed zero-constant shift `h`.
    pub first_shift: u64,
    /// Packed zero-constant translation `t`.
    pub second_shift: u64,
    /// `delta_h(f)` in the quotient ring.
    pub inverse_difference: u64,
    /// `delta_h(f+t)` in the quotient ring.
    pub translated_inverse_difference: u64,
    /// Reduced product `h t(t+h)`.
    pub annihilator_product: u64,
    /// Whether the two inverse differences agree.
    pub inverse_differences_equal: bool,
    /// Whether `h t(t+h)` vanishes in the quotient.
    pub annihilator_product_vanishes: bool,
}

/// Exact annihilator-average of the combined Berlekamp/inverse shift energy.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryBerlekampAnnihilatorEnergyReport {
    /// Principal-unit modulus is `x^(ell+1)`.
    pub ell: usize,
    /// Degree of the monic constant-one polynomials.
    pub degree: usize,
    /// Annihilator consists of frequencies whose first this-many bits vanish.
    pub interval_degree: usize,
    /// Number of low polynomial coefficients toggled by the shift subspace.
    pub shift_dimension: usize,
    /// Total number `2^(degree-1)` of monic constant-one inputs.
    pub input_count: u128,
    /// Number `2^(ell-interval_degree)` of annihilator frequencies.
    pub annihilator_frequency_count: u128,
    /// Number of nonempty simultaneous input/inverse cosets.
    pub occupied_coset_count: usize,
    /// Input-coset index attaining the largest ratio `b_(C,D)^2/population`.
    pub worst_input_coset: usize,
    /// Inverse-coset index attaining the largest ratio.
    pub worst_inverse_coset: usize,
    /// Signed square in the worst ratio.
    pub worst_bucket_signed_square: BigUint,
    /// Squarefree population in the worst ratio.
    pub worst_bucket_population: u128,
    /// Exact signed sum with inverse residue in `V_interval_degree`.
    pub inverse_interval_phase_sum: i128,
    /// `sum_(C,D)b_(C,D)^2`, retaining Möbius/Berlekamp cancellation.
    pub signed_coset_energy: BigUint,
    /// Same collision count after replacing every Möbius weight by its support.
    pub unsigned_collision_count: BigUint,
    /// Exact number `(2^degree-(-1)^degree)/3` of squarefree inputs.
    pub diagonal_squarefree_count: u128,
    /// Sum of all nonzero-shift signed correlations.
    pub off_diagonal_signed_correlation: i128,
    /// Sum of shift energies over all annihilator frequencies.
    pub averaged_shift_energy: BigUint,
    /// Cauchy bound for `inverse_interval_phase_sum^2`.
    pub fibre_cauchy_square_bound: BigUint,
    /// Exact correlations for every packed low-coefficient shift.
    pub shift_correlations: Vec<BinaryBerlekampShiftCorrelation>,
}

/// Exact finite diagnostic for sign-reversing translations inside the
/// simultaneous input/inverse cosets.
///
/// For one bucket write `w(m)` for its value in `{-1,0,1}` on the low
/// coefficient cube.  Every nonzero translation `t` gives the rigorous
/// triangle bound
///
/// ```text
/// abs(sum_m w(m))
///   <= (1/2) sum_m abs(w(m)+w(m+t)).
/// ```
///
/// This report minimizes the right-hand side separately in every finite
/// bucket.  It diagnoses a possible involution proof; it does not extrapolate
/// the observed minima to unenumerated degrees.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryBerlekampInvolutionDefectReport {
    /// Principal-unit modulus is `x^(ell+1)`.
    pub ell: usize,
    /// Degree of the monic constant-one polynomials.
    pub degree: usize,
    /// Dimension of the low-coefficient and inverse-interval cubes.
    pub interval_degree: usize,
    /// Number of nonempty simultaneous cosets.
    pub occupied_bucket_count: usize,
    /// Buckets whose exact signed sum is zero.
    pub zero_signed_bucket_count: usize,
    /// Buckets admitting a translation with zero defect.
    pub exactly_sign_reversed_bucket_count: usize,
    /// Buckets where the best translation triangle bound is exact.
    pub exact_triangle_bucket_count: usize,
    /// Input-coset witness maximizing `minimum_defect^2/population`.
    pub worst_input_coset: usize,
    /// Inverse-coset witness maximizing `minimum_defect^2/population`.
    pub worst_inverse_coset: usize,
    /// Best nonzero translation for the witness bucket.
    pub worst_bucket_translation: usize,
    /// Exact signed magnitude in the witness bucket.
    pub worst_bucket_signed_magnitude: u128,
    /// Minimum translation defect in the witness bucket.
    pub worst_bucket_minimum_defect: u128,
    /// Squarefree population in the witness bucket.
    pub worst_bucket_population: u128,
    /// Whether every enumerated minimum satisfies
    /// `minimum_defect^2<=2d*population`.
    pub finite_defect_candidate_holds: bool,
}

/// One truncated 2-typical Witt block of a binary principal unit.
///
/// The block indexed by odd `m` is `W_L(GF(2))`, hence its additive group is
/// cyclic of order `2^L`.  `coordinate` is the exponent of `1+x^m`; its
/// binary digits are the Witt slots at degrees `m,2m,4m,...`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryWittBlockCoordinate {
    /// Odd block index `m`.
    pub odd_degree: usize,
    /// Number of admitted 2-typical slots.
    pub length: usize,
    /// Coordinate in `Z/2^length`.
    pub coordinate: usize,
    /// Active slot degrees `m*2^j`, in increasing order.
    pub active_slot_degrees: Vec<usize>,
    /// Highest active slot degree, absent for the zero block coordinate.
    pub highest_active_slot: Option<usize>,
}

/// Checked conversion of one binary principal unit to truncated 2-typical
/// Witt blocks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryPrincipalUnitWittReport {
    /// Truncation level modulo `x^(ell+1)`.
    pub ell: usize,
    /// Packed constant-one principal unit.
    pub unit: u64,
    /// Stable mixed-radix index used by the native transforms.
    pub mixed_radix_index: usize,
    /// Odd-indexed 2-typical blocks.
    pub blocks: Vec<BinaryWittBlockCoordinate>,
}

/// Exact size ledger for the maximal elementary-abelian quotient of the
/// binary 2-typical Witt blocks.
///
/// On a block `Z/2^L`, the first-slot map is reduction modulo two.  Taking
/// the product over all odd block indices gives a surjection
///
/// ```text
/// E_ell -> GF(2)^ceil(ell/2).
/// ```
///
/// This is the direct many-block analogue of the low-coordinate character
/// maps used for a fixed number of prescribed coefficients.  Every
/// homomorphism from `E_ell` to an elementary abelian binary group kills
/// `2 E_ell`, hence factors through this quotient.  The report therefore
/// keeps the *minimum possible* kernel of any such maximal-rank map explicit;
/// it is a structural ledger, not a character-sum estimate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryWittFirstSlotProjectionReport {
    /// Principal-unit truncation level.
    pub ell: usize,
    /// Odd degrees indexing the target coordinates.
    pub first_slot_degrees: Vec<usize>,
    /// Lengths of the corresponding truncated Witt blocks.
    pub block_lengths: Vec<usize>,
    /// Order of the source principal-unit group, `2^ell`.
    pub source_order: usize,
    /// Order of the first-slot image, `2^ceil(ell/2)`.
    pub image_order: usize,
    /// Binary rank of the maximal elementary-abelian quotient `E_ell/2E_ell`.
    pub maximal_elementary_quotient_rank: usize,
    /// Order of every fibre, `2^floor(ell/2)`.
    pub kernel_order: usize,
    /// Binary dimension of the kernel, `floor(ell/2)`.
    pub kernel_dimension: usize,
    /// Minimum kernel dimension among homomorphisms from `E_ell` to an
    /// elementary abelian binary group.
    pub minimum_elementary_kernel_dimension: usize,
}

/// Projection of simultaneous Möbius cosets onto one order-two character.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryOrderTwoCharacterProjection {
    /// Bit mask selecting the odd Witt blocks on which the character is real
    /// and nontrivial.
    pub character_mask: usize,
    /// Exact conductor, the largest selected odd block index; absent for the
    /// trivial character.
    pub exact_conductor: Option<usize>,
    /// `sum_(C,D) (sum_(f in C,D) mu(f) chi(f))^2`.
    pub signed_coset_energy: BigUint,
    /// Largest signed square attained by an occupied simultaneous coset.
    pub worst_bucket_signed_square: BigUint,
    /// Squarefree population of that witness coset.
    pub worst_bucket_population: u128,
}

/// Aggregate order-two projection energy at one exact conductor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryOrderTwoConductorEnergy {
    /// Exact conductor; absent only for the trivial character.
    pub exact_conductor: Option<usize>,
    /// Number of characters in this row.
    pub character_count: usize,
    /// Sum of their simultaneous-coset energies.
    pub projected_energy: BigUint,
}

/// Exact exceptional-real-character diagnostic for the simultaneous
/// input/inverse cosets.
///
/// Every order-two character of the principal-unit group is a sign on the
/// parity of selected odd Witt-block coordinates.  The report retains every
/// such projection and checks Parseval on the quotient by squares exactly.
/// It is a bounded diagnostic, not a uniform cancellation theorem.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryBerlekampOrderTwoProjectionReport {
    /// Principal-unit modulus is `x^(ell+1)`.
    pub ell: usize,
    /// Degree of the monic constant-one polynomials.
    pub degree: usize,
    /// Dimension of the inverse interval.
    pub interval_degree: usize,
    /// Dimension of the low-coefficient shift cube.
    pub shift_dimension: usize,
    /// Odd Witt block indices, in character-mask bit order.
    pub odd_block_degrees: Vec<usize>,
    /// Number of order-two characters.
    pub character_count: usize,
    /// Number of occupied simultaneous cosets.
    pub occupied_bucket_count: usize,
    /// One row for every order-two character, trivial row first.
    pub projections: Vec<BinaryOrderTwoCharacterProjection>,
    /// The same projected energies grouped by exact conductor.
    pub conductor_energies: Vec<BinaryOrderTwoConductorEnergy>,
    /// Sum of all order-two projected energies.
    pub total_projected_energy: BigUint,
    /// Energy after splitting every simultaneous coset by the parities of all
    /// Witt-block coordinates.
    pub witt_parity_fibre_energy: BigUint,
}

impl BinaryBerlekampAnnihilatorEnergyReport {
    /// Whether the Berlekamp signs strictly reduce simultaneous-coset energy.
    #[must_use]
    pub fn has_signed_collision_cancellation(&self) -> bool {
        self.signed_coset_energy < self.unsigned_collision_count
    }

    /// Experimental connected off-diagonal square bound
    /// `2^(degree+shift_dimension+1)`.
    ///
    /// This is the square-root scale of the complete `(f,h)` family with a
    /// factor two.  It is deliberately a finite diagnostic, not a proved
    /// estimate for unenumerated degrees.
    ///
    /// # Errors
    ///
    /// Returns a typed parameter error if the exponent overflows.
    pub fn connected_off_diagonal_candidate_bound(&self) -> Result<BigUint, HayesError> {
        let exponent = self
            .degree
            .checked_add(self.shift_dimension)
            .and_then(|value| value.checked_add(1))
            .ok_or_else(|| {
                HayesError::InvalidParameter(
                    "connected off-diagonal candidate exponent overflow".to_owned(),
                )
            })?;
        Ok(BigUint::from(1_u8) << exponent)
    }

    /// Whether this finite row satisfies the experimental connected
    /// off-diagonal square bound.
    ///
    /// # Errors
    ///
    /// Returns any error from [`Self::connected_off_diagonal_candidate_bound`].
    pub fn satisfies_connected_off_diagonal_candidate(&self) -> Result<bool, HayesError> {
        let magnitude = BigUint::from(self.off_diagonal_signed_correlation.unsigned_abs());
        Ok(magnitude.pow(2) <= self.connected_off_diagonal_candidate_bound()?)
    }

    /// Whether the connected candidate alone would force
    /// `signed_coset_energy<=2^degree` using the exact squarefree diagonal.
    ///
    /// This checks only the arithmetic implication.  Callers must separately
    /// establish [`Self::satisfies_connected_off_diagonal_candidate`] or prove
    /// its universal analogue.
    ///
    /// # Errors
    ///
    /// Returns any error from [`Self::connected_off_diagonal_candidate_bound`].
    pub fn connected_candidate_implies_degree_scale_energy(&self) -> Result<bool, HayesError> {
        let target = BigUint::from(1_u8) << self.degree;
        let diagonal = BigUint::from(self.diagonal_squarefree_count);
        if diagonal > target {
            return Ok(false);
        }
        Ok(self.connected_off_diagonal_candidate_bound()? <= (target - diagonal).pow(2))
    }
}

/// Conditional exponent ledger for one endpoint convolution term using the
/// annihilator-averaged Berlekamp shift energy.
///
/// Every exponent is an exact numerator over denominator thirty-two.  The two
/// energy inputs are numerators over denominator sixteen for degrees `k` and
/// `k-1`, where `k=endpoint_degree-interval_degree`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BinaryBerlekampAggregateExponentLedger {
    /// Coefficient-prefix length.
    pub ell: usize,
    /// Endpoint degree `n`.
    pub endpoint_degree: usize,
    /// Convolution order `d`.
    pub interval_degree: usize,
    /// Shift-subspace dimension `s`.
    pub shift_dimension: usize,
    /// Exact-degree index `k=n-d`.
    pub mobius_degree: usize,
    /// Assumed exponent numerator over sixteen for `E_(s,d)(k)`.
    pub energy_exponent_sixteenths: u128,
    /// Assumed exponent numerator over sixteen for `E_(s,d)(k-1)`.
    pub previous_energy_exponent_sixteenths: u128,
    /// Cauchy exponent for the `B_k` fibre, over thirty-two.
    pub phase_bound_thirty_seconds: u128,
    /// Cauchy exponent for the `B_(k-1)` fibre, over thirty-two.
    pub previous_phase_bound_thirty_seconds: u128,
    /// Bound for the weighted `d(H_k)` term after `H_k=B_k-B_(k-1)`.
    pub weighted_term_bound_thirty_seconds: u128,
    /// Target exponent `ell`, over thirty-two.
    pub target_thirty_seconds: u128,
    /// `target-weighted_term_bound`, over thirty-two.
    pub deficit_thirty_seconds: i128,
}

impl BinaryBerlekampAggregateExponentLedger {
    /// Whether the conditional pointwise term has a strict binary saving.
    #[must_use]
    pub const fn closes_strictly(&self) -> bool {
        self.deficit_thirty_seconds > 0
    }
}

impl InverseAdditiveMobiusSpectrum {
    /// Recover `sum_(u in V_d) M_degree(u^(-1))` by additive orthogonality.
    ///
    /// # Errors
    ///
    /// Rejects `d=0` and `d>=ell`, and reports a failed exact divisibility
    /// invariant.
    pub fn inverse_interval_fibre_sum(&self, d: usize) -> Result<i128, HayesError> {
        if d == 0 || d >= self.ell {
            return Err(HayesError::InvalidParameter(format!(
                "inverse interval degree must satisfy 1<=d<ell, got d={d}, ell={}",
                self.ell
            )));
        }
        let stride = 1_usize << d;
        let denominator = 1_i128 << (self.ell - d);
        let frequency_sum = self
            .values
            .iter()
            .step_by(stride)
            .try_fold(0_i128, |sum, value| {
                sum.checked_add(*value).ok_or_else(|| {
                    HayesError::InvalidParameter(
                        "inverse-additive annihilator sum exceeds i128".to_owned(),
                    )
                })
            })?;
        if frequency_sum % denominator != 0 {
            return Err(HayesError::Invariant(format!(
                "inverse-additive annihilator sum {frequency_sum} is not divisible by {denominator}"
            )));
        }
        Ok(frequency_sum / denominator)
    }
}

/// One exact low-bit-annihilator layer in the order-regrouped Fourier sum.
///
/// `annihilator_depth=v` means that the first `v` packed Fourier bits vanish,
/// while bit `v` is nonzero; the zero frequency is assigned depth `ell`.
/// This is the nesting relevant to `W_d^perp`.  It is not, by itself, the
/// multiplicative exact-conductor filtration used elsewhere in this module.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct InverseMobiusFourierLayer {
    /// Largest interval degree `d` for which this frequency lies in
    /// `W_d^perp`.
    pub annihilator_depth: usize,
    /// Number of packed frequencies in the layer.
    pub frequency_count: u128,
    /// Signed numerator after summing every eligible convolution order.
    pub weighted_numerator: i128,
}

/// Exact Fourier regrouping of the signed endpoint Möbius convolution.
///
/// The common denominator is `2^ell`.  Thus `regrouped_numerator` divided by
/// `denominator` is exactly the identity-class discrepancy.  The three
/// absolute numerators expose, without claiming a uniform bound, how much
/// cancellation is lost by taking absolute values cellwise, orderwise, or
/// after regrouping by annihilator depth.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct InverseMobiusFourierRegroupReport {
    /// Coefficient-prefix length.
    pub ell: usize,
    /// Endpoint or other target degree.
    pub degree: usize,
    /// Common Fourier normalization denominator `2^ell`.
    pub denominator: u128,
    /// Layers in increasing annihilator depth `0..=ell`.
    pub layers: Vec<InverseMobiusFourierLayer>,
    /// Exact signed numerator after every layer is combined.
    pub regrouped_numerator: i128,
    /// Exact normalized identity-class discrepancy.
    pub discrepancy: i128,
    /// Sum of absolute numerators before either `d` or frequency is combined.
    pub cellwise_absolute_numerator: u128,
    /// Sum of absolute numerators after frequencies are combined for each `d`.
    pub orderwise_absolute_numerator: u128,
    /// Sum of absolute numerators after all eligible `d` are combined in each
    /// annihilator-depth layer.
    pub layerwise_absolute_numerator: u128,
}

/// Joint conductor/order Fourier regrouping of the connected top trace.
///
/// Every quantity is already scaled to the common selected-trace identity
/// `2^ell Delta_ell-2^coarse Delta_coarse`; there is no remaining Fourier
/// denominator.  The absolute totals show the loss from stopping at different
/// stages of the exact regrouping without asserting an asymptotic bound.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConnectedTopInverseMobiusFourierRegroupReport {
    /// Fine coefficient-prefix length.
    pub ell: usize,
    /// Endpoint degree.
    pub degree: usize,
    /// First retained exact-conductor level.
    pub first_top_level: usize,
    /// Coarse quotient level `first_top_level-1`.
    pub coarse_level: usize,
    /// Number `2^coarse_level` of inflated coarse frequencies cancelled
    /// identically by the connected projector.
    pub cancelled_coarse_frequency_count: u128,
    /// Structural upper bound `2^ell-2^coarse_level` on the remaining
    /// additive-frequency support.
    pub high_frequency_support_bound: u128,
    /// Fine-domain layers after combining conductors and Möbius orders at
    /// every frequency.
    pub layers: Vec<InverseMobiusFourierLayer>,
    /// Exact selected connected top-conductor trace.
    pub connected_trace: i128,
    /// Absolute total before conductors, orders, or frequencies are combined.
    pub cellwise_absolute_numerator: u128,
    /// Absolute total after frequencies and conductors are combined for each
    /// Möbius order.
    pub orderwise_absolute_numerator: u128,
    /// Absolute total after conductors and orders are combined frequencywise.
    pub frequencywise_absolute_numerator: u128,
    /// Absolute total after the frequencywise sums are further grouped by
    /// annihilator depth.
    pub layerwise_absolute_numerator: u128,
    /// Exact sum of squares of the connected frequency numerators.
    pub frequency_square_sum: BigUint,
    /// Cauchy square using the full structural high-frequency support bound.
    pub frequency_cauchy_bound_square: BigUint,
    /// Square of the selected connected trace allowance.
    pub connected_allowance_square: BigUint,
    /// Largest frequency square sum for which structural-support Cauchy would
    /// prove the connected trace allowance.
    pub maximum_frequency_square_sum_for_candidate: BigUint,
    /// Smallest integral factor by which the exact square sum would have to
    /// improve for structural-support Cauchy to close.
    pub required_frequency_square_sum_saving_ceiling: BigUint,
}

impl ConnectedTopInverseMobiusFourierRegroupReport {
    /// Whether structural-support Cauchy proves the connected trace candidate.
    #[must_use]
    pub fn frequency_cauchy_proves_candidate(&self) -> bool {
        self.frequency_cauchy_bound_square <= self.connected_allowance_square
    }
}

/// One exact low-degree term in the identity-class Möbius convolution.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct MobiusConvolutionTerm {
    /// Degree `d` of the interval factor `V_d`.
    pub interval_degree: usize,
    /// `d sum_(u in V_d) M_(degree-d)(u^(-1))`.
    pub value: i128,
}

/// Exact decomposition of an identity-class Mangoldt discrepancy.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct IdentityClassMobiusConvolution {
    /// Coefficient-prefix length.
    pub ell: usize,
    /// Target degree.
    pub degree: usize,
    /// Uniform identity-class mean `2^(degree-ell)`.
    pub uniform_mean: u128,
    /// Exact identity-class Mangoldt population.
    pub mangoldt_population: u128,
    /// `mangoldt_population-uniform_mean`.
    pub discrepancy: i128,
    /// Exact signed terms for `1<=d<ell`.
    pub terms: Vec<MobiusConvolutionTerm>,
}

/// One convolution-order contribution after the connected top-conductor
/// projector is applied.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConnectedTopMobiusConvolutionTerm {
    /// Interval degree `d`.
    pub interval_degree: usize,
    /// Fine level-`ell` Möbius-convolution term.
    pub fine_value: i128,
    /// Coarse level-`a-1` term, or zero once `d>=a-1`.
    pub coarse_value: i128,
    /// `2^ell fine_value-2^(a-1) coarse_value`.
    pub connected_value: BigInt,
}

/// Exact Möbius-order decomposition of the connected top-conductor trace.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConnectedTopMobiusConvolutionReport {
    /// Fine coefficient-prefix length.
    pub ell: usize,
    /// Endpoint degree.
    pub degree: usize,
    /// First retained exact-conductor level `a`.
    pub first_top_level: usize,
    /// Coarse quotient level `a-1`.
    pub coarse_level: usize,
    /// Contributions in increasing interval degree.
    pub terms: Vec<ConnectedTopMobiusConvolutionTerm>,
    /// First interval degree with a nonzero connected contribution.
    pub first_nonzero_interval_degree: Option<usize>,
    /// Number of nonzero connected order contributions.
    pub nonzero_order_count: usize,
    /// Signed sum of every connected order.
    pub signed_connected_trace: BigInt,
    /// Sum of absolute connected order contributions.
    pub orderwise_absolute_trace: BigUint,
}

/// One symmetric convolution-order cell in the connected fourth cumulant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConnectedOrderCumulantCell {
    /// Nondecreasing interval degrees indexing this symmetric cell.
    pub interval_degrees: [usize; 4],
    /// Number of ordered quadruples represented by this cell.
    pub permutation_multiplicity: usize,
    /// `sum_e T_a(e)T_b(e)T_c(e)T_d(e)`.
    pub raw_fourth_sum: BigInt,
    /// Sum of the three covariance pairings for this order quadruple.
    pub pairing_sum: BigInt,
    /// `2^ell raw_fourth_sum-pairing_sum`.
    pub connected_numerator: BigInt,
}

/// Exact decomposition of the endpoint fourth cumulant by convolution order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConnectedOrderCumulantReport {
    /// Coefficient-prefix length.
    pub ell: usize,
    /// Endpoint degree.
    pub degree: usize,
    /// Number of interval orders, exactly `ell-1`.
    pub order_count: usize,
    /// Symmetric order cells in lexicographic order.
    pub cells: Vec<ConnectedOrderCumulantCell>,
    /// Sum of cells with their permutation multiplicities.
    pub reconstructed_fourth_cumulant_numerator: BigInt,
    /// Direct `2^ell M_4-3M_2^2` control from the class distribution.
    pub direct_fourth_cumulant_numerator: BigInt,
}

/// Exact removal of proper prime powers from one identity-class population.
///
/// The checked identity is
///
/// ```text
/// mangoldt_population
///   = proper_prime_power_population + degree * irreducible_count.
/// ```
///
/// Thus `irreducible_count != 0` is an exact finite certificate that the
/// identity Hayes class contains a monic irreducible of the requested degree.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct IdentityClassIrreducibleReport {
    /// Coefficient-prefix length.
    pub ell: usize,
    /// Target polynomial degree.
    pub degree: usize,
    /// Exact identity-class Mangoldt population `N_degree(1)`.
    pub mangoldt_population: u128,
    /// Weighted contribution from powers of irreducibles of proper degree.
    pub proper_prime_power_population: u128,
    /// Number of monic irreducibles of `degree` in the identity class.
    pub irreducible_count: u128,
}

impl IdentityClassIrreducibleReport {
    /// Whether the exact subtraction proves a degree-`degree` irreducible.
    #[must_use]
    pub const fn proves_irreducible_exists(self) -> bool {
        self.irreducible_count != 0
    }
}

/// Exact odd-endpoint residue together with the Carlitz `2`-rank ledger.
///
/// For `n=2 ell+1`, the proved prime-power reduction gives
///
/// ```text
/// N_n(1)=1+n I_n(1).
/// ```
///
/// Hence a nonzero residue `I_n(1) mod 8` proves the requested irreducible
/// exists in that one row.  The associated binary Carlitz curve satisfies
///
/// ```text
/// #C_ell(GF(2^n))=1+2^ell N_n(1).
/// ```
///
/// Recovering `I_n(1) mod 8` geometrically therefore requires the point count
/// modulo `2^(ell+3)`.  Deuring--Shafarevich gives `2`-rank zero for this
/// one-branch-point `2`-group cover, but that only controls the zeta numerator
/// modulo two and does not supply the required normalized three bits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct OddEndpointTwoAdicReport {
    /// Coefficient-prefix length.
    pub ell: usize,
    /// Odd endpoint degree `2 ell+1`.
    pub degree: usize,
    /// Exact identity-class Mangoldt population `N_degree(1)`.
    pub mangoldt_population: u128,
    /// Exact number `I_degree(1)` of shaped irreducibles.
    pub irreducible_count: u128,
    /// `I_degree(1) mod 8`.
    pub irreducible_residue_mod_8: u8,
    /// `I_degree(1) mod 16`.
    pub irreducible_residue_mod_16: u8,
    /// Exact `2`-adic valuation of `I_degree(1)`, or `None` when it is zero.
    pub irreducible_two_adic_valuation: Option<u32>,
    /// Order `2^ell` of the Carlitz Galois group.
    pub carlitz_galois_group_order: u128,
    /// The unique finite branch stabilizer, also of order `2^ell`.
    pub ramified_place_stabilizer_order: u128,
    /// The Deuring--Shafarevich `2`-rank of the Carlitz curve, exactly zero.
    pub carlitz_two_rank: usize,
    /// Bits of raw point-count precision needed to recover the residue mod 8.
    pub required_curve_point_modulus_bits: usize,
    /// Exact curve point count from the point-population identity.
    pub curve_point_count: u128,
    /// Exact point-count residue modulo `2^(ell+3)`.
    pub curve_point_residue_at_required_precision: u128,
}

impl OddEndpointTwoAdicReport {
    /// Whether this exact row proves the odd Lemire endpoint by its residue.
    #[must_use]
    pub const fn proves_odd_endpoint_by_modulo_eight(self) -> bool {
        self.irreducible_residue_mod_8 != 0
    }
}

/// One proper divisor in the odd-endpoint prime-power reduction.
///
/// If the target is `n = 2 ell + 1`, every exponent `n / prime_degree`
/// below is odd.  It is therefore coprime to the order `2^ell` of the Hayes
/// principal-unit group, so taking that power is an automorphism of the
/// group.  A prime power can land in the identity class only when the prime
/// itself is in the identity class.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct OddEndpointProperDivisor {
    /// Degree of the irreducible underlying the proper prime power.
    pub prime_degree: usize,
    /// Prime-power exponent `(2 ell + 1) / prime_degree`.
    pub exponent: usize,
}

/// Structural certificate for the proper-prime-power term at an odd endpoint.
///
/// For `n = 2 ell + 1`, every proper divisor of `n` is at most `ell`: the
/// quotient is an odd integer at least three.  In that degree range, the only
/// monic irreducible in the identity class modulo `x^(ell+1)` is `x` itself.
/// Combined with the odd-power automorphism above, this proves exactly
///
/// ```text
/// N_n(1) = 1 + n I_n(1).
/// ```
///
/// Consequently `N_n(1) > 1` is sufficient and necessary for an
/// identity-class irreducible at the odd endpoint.  This report records every
/// proper divisor so a consumer can replay the finite arithmetic rather than
/// trusting a coarse bound on prime powers.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OddEndpointPrimePowerReduction {
    /// Number of prescribed leading zero coefficients.
    pub ell: usize,
    /// Odd endpoint degree `2 ell + 1`.
    pub degree: usize,
    /// Exact order `2^ell` of the principal-unit group.
    pub group_order: usize,
    /// Every proper divisor of `degree`, in increasing order.
    pub proper_divisors: Vec<OddEndpointProperDivisor>,
    /// Exact weighted proper-prime-power population, always one.
    pub proper_prime_power_population: u128,
}

/// Exact diagnostic for the lower-bound sieve at the Lemire half interval.
///
/// For `m = floor(degree/2)`, let `S` contain the monic constant-one binary
/// polynomials `x^degree + a_m x^m + ... + a_1 x + 1`.  The report checks the
/// identity
///
/// ```text
/// sum_(f in S) sum_(D | f, deg D <= m) mu(D) = 1.
/// ```
///
/// `candidate_weight` is the same truncated Möbius weight for one supplied
/// multiset of *distinct-factor degrees*. Equal entries are allowed because
/// different irreducible factors can have the same degree; multiplicities of
/// one factor must be omitted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HalfIntervalMobiusSieveReport {
    /// Degree of every polynomial in the interval.
    pub degree: usize,
    /// Truncation level `floor(degree/2)`.
    pub cutoff: usize,
    /// Number `2^cutoff` of polynomials in the interval.
    pub interval_size: BigInt,
    /// Exact aggregate truncated Möbius weight; always one when admitted.
    pub total_weight: BigInt,
    /// Distinct irreducible-factor degrees supplied by the caller.
    pub distinct_factor_degrees: Vec<usize>,
    /// Truncated Möbius weight of that factor-degree pattern.
    pub candidate_weight: BigInt,
}

impl OddEndpointPrimePowerReduction {
    /// Whether a supplied exact Mangoldt population proves a new prime.
    #[must_use]
    pub const fn population_proves_irreducible_exists(&self, population: u128) -> bool {
        population > self.proper_prime_power_population
    }
}

/// Fourier energy contributed by one exact conductor to the squared class
/// discrepancy.
///
/// For `D_e = N_e - mu`, put `f_e = D_e^2`.  Characters of `E_ell` that
/// factor through `E_level` form a nested filtration.  The cumulative field is
/// the exact unnormalised Fourier energy of `f` on that subspace; subtracting
/// the preceding cumulative value gives the energy of characters of exact
/// conductor `level + 1`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SquaredDeviationConductorLevel {
    /// Principal-unit truncation level.
    pub level: usize,
    /// `sum_(chi factoring through E_level) |sum_e D_e^2 chi(e)|^2`.
    pub cumulative_fourier_energy: BigUint,
    /// Difference from the cumulative energy at `level - 1`.
    pub exact_fourier_energy: BigUint,
    /// Haar refinement energy before the factor `2^(level-1)`.
    pub haar_difference_square_sum: BigUint,
}

/// Exact conductor filtration of the fourth central moment.
///
/// The two endpoint identities checked by this object are
///
/// ```text
/// C_0   = M_2^2,
/// C_ell = 2^ell M_4,
/// ```
///
/// where `C_j` is the cumulative Fourier energy through conductor level `j`.
/// This exposes where the connected fourth moment lives without introducing
/// complex or floating-point character values.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FourthMomentConductorDecomposition {
    /// Coefficient-prefix length.
    pub ell: usize,
    /// Extension degree.
    pub degree: usize,
    /// `M_2 = sum_e D_e^2`.
    pub second_moment: BigUint,
    /// `M_4 = sum_e D_e^4`.
    pub fourth_moment: BigUint,
    /// Exact-conductor levels in increasing order.
    pub levels: Vec<SquaredDeviationConductorLevel>,
}

/// One exact factor in the conductor martingale product for root kurtosis.
///
/// With `C_j` the cumulative Fourier energy of `D^2`, the factor is
/// `C_j/C_(j-1)=1+q_j`, where `q_j=E_j/C_(j-1)` and `0<=q_j<=1`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConductorKurtosisFactor {
    /// Exact conductor level `j`.
    pub level: usize,
    /// Numerator `C_j` of `1+q_j`.
    pub factor_numerator: BigUint,
    /// Denominator `C_(j-1)` of `1+q_j`.
    pub factor_denominator: BigUint,
    /// Numerator `E_j=C_j-C_(j-1)` of `q_j`.
    pub imbalance_numerator: BigUint,
    /// Denominator `C_(j-1)` of `q_j`.
    pub imbalance_denominator: BigUint,
}

/// Exact multiplicative conductor decomposition of root kurtosis.
///
/// The factors telescope to
///
/// ```text
/// product_(j=1)^ell (1+q_j) = 2^ell M_4 / M_2^2.
/// ```
///
/// This is an identity and an exact finite diagnostic.  It does not bound any
/// `q_j` uniformly.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConductorKurtosisProductReport {
    /// Coefficient-prefix length.
    pub ell: usize,
    /// Endpoint degree.
    pub degree: usize,
    /// Exact conductor factors in increasing order.
    pub factors: Vec<ConductorKurtosisFactor>,
    /// Numerator `2^ell M_4` of the root ratio.
    pub root_ratio_numerator: BigUint,
    /// Denominator `M_2^2` of the root ratio.
    pub root_ratio_denominator: BigUint,
}

/// Largest raw population imbalance across one binary Witt refinement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PopulationRefinementLevel {
    /// Quotient level being split over `E_(level-1)`.
    pub level: usize,
    /// Parent cylinder attaining the largest sibling difference.
    pub witness_parent: usize,
    /// `max_parent |N(child_0)-N(child_1)|`.
    pub maximum_sibling_difference: u128,
}

/// Exact `L1` Haar triangle ledger for one class-population distribution.
///
/// If `H_j(b)` is the signed difference between the two children of a
/// level-`j-1` cylinder, then every leaf discrepancy has the exact expansion
///
/// ```text
/// N(e)-2^(degree-ell)
///   = sum_(j=1)^ell sign_j(e) H_j(parent_j(e)) / 2^(ell-j+1).
/// ```
///
/// Thus `sum_j 2^(j-1) max_b |H_j(b)| <= 2^(2ell)` implies the desired
/// `max_e |N(e)-2^(degree-ell)| <= 2^ell`.  This report checks the expansion
/// leaf by leaf before exposing that sufficient finite diagnostic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PopulationRefinementTriangleReport {
    /// Coefficient-prefix length.
    pub ell: usize,
    /// Extension degree.
    pub degree: usize,
    /// Exact refinement levels in increasing order.
    pub levels: Vec<PopulationRefinementLevel>,
    /// `sum_j 2^(j-1) max_b |H_j(b)|`.
    pub triangle_numerator: BigUint,
    /// Numerator target `2^(2ell)`.
    pub candidate_target_numerator: BigUint,
    /// Actual maximum leaf discrepancy, independently computed.
    pub actual_maximum_absolute_deviation: u128,
    /// `sum_j 2^(j-1) |H_j(1)|` along the identity-class path only.
    pub identity_path_triangle_numerator: BigUint,
    /// First level in the connected logarithmic top-conductor window.
    pub connected_top_first_level: usize,
    /// Signed sum `sum_(j>=first) 2^(j-1) H_j(1)`.
    pub connected_top_signed_numerator: BigInt,
    /// Candidate connected bound `2^(2ell-2)`.
    pub connected_top_candidate_numerator: BigUint,
}

/// Exact finite normalization of one conductor-layer sup norm.
///
/// If `H_j(b)` is the level-`j` sibling population difference, then
/// `D_[j](e)=sign_j(e)H_j(b)/2^(ell-j+1)`.  Consequently the squared
/// constant required by the no-polynomial-loss conductor bound is exactly
///
/// ```text
/// max_b |H_j(b)|^2 2^(j-1) / ((j-1)^2 2^n).
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConductorLayerSupNormLevel {
    /// Exact conductor level `j`.
    pub level: usize,
    /// Parent cylinder attaining the maximum sibling difference.
    pub witness_parent: usize,
    /// Exact maximum `max_b |H_j(b)|`.
    pub maximum_sibling_difference: u128,
    /// Numerator of the exact required squared constant.
    pub squared_constant_numerator: BigUint,
    /// Denominator of the exact required squared constant.
    pub squared_constant_denominator: BigUint,
}

/// Bounded exact diagnostic for the conductor-layer square-root constant.
///
/// This report measures finite rows only.  Its maximum ratio is suitable for
/// falsification and regression testing, but never certifies the uniform
/// assumption used by [`check_conductor_layer_sup_bound_sufficiency`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConductorLayerSupNormDiagnostic {
    /// Coefficient-prefix length.
    pub ell: usize,
    /// Endpoint degree.
    pub degree: usize,
    /// Exact levels `2..=ell`.
    pub levels: Vec<ConductorLayerSupNormLevel>,
    /// Level attaining the largest exact ratio.
    pub witness_level: usize,
    /// Numerator of that largest ratio.
    pub maximum_squared_constant_numerator: BigUint,
    /// Denominator of that largest ratio.
    pub maximum_squared_constant_denominator: BigUint,
}

/// Exact fixed-conductor sibling difference propagated in the degree.
///
/// The level-`j` Hayes `L`-polynomials have degree `j-1`, so their Fourier
/// inverse `Delta_j(.;n)` satisfies the same group-ring recurrence.  This
/// report seeds that recurrence from exact small-degree populations, checks
/// its first propagated row independently, and retains the target row as
/// arbitrary-precision integers.  It avoids allocating the ambient endpoint
/// group `E_ell`, because the level layer depends only on `(j,n)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FixedConductorSiblingRecurrenceReport {
    /// Exact conductor level `j`.
    pub level: usize,
    /// Target polynomial degree `n`.
    pub degree: usize,
    /// Order `2^j` of the level group.
    pub group_order: usize,
    /// Number `j-1` of exact seed rows.
    pub seed_count: usize,
    /// First recurrence degree checked against a fresh population transform.
    pub independently_checked_degree: usize,
    /// Class attaining the largest sibling-difference magnitude.
    pub witness_class: usize,
    /// Packed principal unit of the witness class.
    pub witness_unit: u64,
    /// Exact peak `max_b |Delta_j(b;n)|`.
    pub maximum_sibling_difference: BigUint,
    /// Numerator of the exact required squared constant.
    pub squared_constant_numerator: BigUint,
    /// Denominator of the exact required squared constant.
    pub squared_constant_denominator: BigUint,
}

impl FixedConductorSiblingRecurrenceReport {
    /// Whether this row violates an integer squared-constant ceiling.
    #[must_use]
    pub fn violates_squared_constant(&self, squared_constant: usize) -> bool {
        self.squared_constant_numerator
            > BigUint::from(squared_constant) * &self.squared_constant_denominator
    }
}

impl ConductorLayerSupNormDiagnostic {
    /// Test a finite row against an integer squared-constant ceiling.
    ///
    /// This is deliberately labelled as a diagnostic: success on a bounded
    /// row does not establish a uniform theorem.
    #[must_use]
    pub fn satisfies_squared_constant(&self, squared_constant: usize) -> bool {
        squared_constant > 0
            && self.maximum_squared_constant_numerator
                <= BigUint::from(squared_constant) * &self.maximum_squared_constant_denominator
    }
}

/// Symbolic endpoint implication of the proposed square-root-fibre envelope.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PopulationRefinementEnvelopeImplication {
    /// Coefficient-prefix length.
    pub ell: usize,
    /// One of the two Lemire endpoint degrees.
    pub degree: usize,
    /// Triangle bound obtained by substituting the envelope at every level.
    pub envelope_triangle_numerator: BigUint,
    /// Required numerator `2^(2ell)`.
    pub candidate_target_numerator: BigUint,
}

/// Hybrid endpoint implication using the proved individual Weil estimate at
/// low conductor and the proposed square-root-fibre estimate only in a top
/// conductor window.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PopulationRefinementHybridImplication {
    /// Coefficient-prefix length.
    pub ell: usize,
    /// One of the two Lemire endpoint degrees.
    pub degree: usize,
    /// First level at which the square-root-fibre estimate is used.
    pub first_square_root_fibre_level: usize,
    /// Number of top levels requiring the square-root-fibre estimate.
    pub square_root_fibre_level_count: usize,
    /// Contribution from the proved individual Weil estimate.
    pub weil_triangle_numerator: BigUint,
    /// Contribution from the proposed square-root-fibre estimate.
    pub square_root_fibre_triangle_numerator: BigUint,
    /// Required numerator `2^(2ell)`.
    pub candidate_target_numerator: BigUint,
}

/// Exact Haar-triangle implication of a polynomial saving over Weil only in
/// the top conductor window.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PopulationRefinementTopPolynomialImplication {
    /// Coefficient-prefix length.
    pub ell: usize,
    /// Endpoint degree `2ell+1` or `2ell+2`.
    pub degree: usize,
    /// First level on which the top-polynomial assumption is used.
    pub first_top_level: usize,
    /// Number of levels in the assumed top window.
    pub top_level_count: usize,
    /// Common integer denominator used to compare the triangle contributions.
    pub common_denominator: usize,
    /// Scaled contribution of the proved individual-Weil low levels.
    pub low_weil_scaled_numerator: BigUint,
    /// Scaled contribution of the assumed top-polynomial levels.
    pub top_polynomial_scaled_numerator: BigUint,
    /// Scaled target `common_denominator * 2^(2ell)`.
    pub candidate_target_scaled_numerator: BigUint,
}

/// Symbolic implication from one connected top-conductor trace bound.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PopulationRefinementConnectedTopImplication {
    /// Coefficient-prefix length.
    pub ell: usize,
    /// One of the two Lemire endpoint degrees.
    pub degree: usize,
    /// First level in the connected top-conductor window.
    pub first_top_level: usize,
    /// Number of levels retained inside the connected trace.
    pub top_level_count: usize,
    /// Proved low-conductor contribution from individual Weil estimates.
    pub low_weil_triangle_numerator: BigUint,
    /// Sum of the proved individual Weil envelopes over the connected top
    /// window, before retaining cancellation between conductor levels.
    pub connected_top_individual_weil_numerator: BigUint,
    /// Assumed connected top-trace bound `2^(2ell-2)`.
    pub connected_top_assumption_numerator: BigUint,
    /// Smallest integer factor by which the separate top-level Weil envelope
    /// must improve to reach the connected assumption.
    pub connected_top_required_saving_ceiling: BigUint,
    /// Required Haar numerator `2^(2ell)`.
    pub candidate_target_numerator: BigUint,
}

/// Sharp one-sided implication from the connected identity-path trace.
///
/// Unlike [`PopulationRefinementConnectedTopImplication`], this report does
/// not spend a symmetric absolute-value reserve. Lemire needs only a lower
/// bound for the identity population, so the connected trace may be
/// arbitrarily positive. Its exact permitted negative magnitude is the full
/// Haar target after subtracting the proved low-conductor Weil envelope.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PopulationRefinementOneSidedConnectedImplication {
    /// Coefficient-prefix length.
    pub ell: usize,
    /// Endpoint degree 2ell+1 or 2ell+2.
    pub degree: usize,
    /// First level retained inside the connected identity-path trace.
    pub first_top_level: usize,
    /// Number of levels retained without intermediate absolute values.
    pub top_level_count: usize,
    /// Proved absolute envelope for the lower conductor levels.
    pub low_weil_triangle_numerator: BigUint,
    /// Individual-Weil envelope on the connected levels, retained only to
    /// price the improvement requested from a future theorem.
    pub connected_top_individual_weil_numerator: BigUint,
    /// Exact allowed negative magnitude for the signed connected trace.
    ///
    /// The open premise is `connected_trace > -negative_allowance`.
    pub negative_allowance_numerator: BigUint,
    /// Smallest integer saving over the separate connected-level Weil
    /// envelope that reaches the one-sided allowance.
    pub required_saving_ceiling: BigUint,
    /// Haar discrepancy target 2^(2ell).
    pub candidate_target_numerator: BigUint,
}

/// Exact Carlitz-cyclotomic geometry underlying the connected top trace.
///
/// Hayes level `j` is the Galois group of the Carlitz field of conductor
/// `t^(j+1)`.  The connected window from level `a` through `ell` is therefore
/// the relative first cohomology of the tower
/// `K_(t^(ell+1))/K_(t^a)`.  This report checks that its dimension reproduces
/// the sum of the individual Weil envelopes exactly.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CarlitzConnectedTopGeometry {
    /// Coefficient-prefix length and fine Hayes level.
    pub ell: usize,
    /// Endpoint degree `2ell+1` or `2ell+2`.
    pub degree: usize,
    /// Fine Carlitz conductor exponent `ell+1`.
    pub fine_conductor_exponent: usize,
    /// Coarse Carlitz conductor exponent `a`.
    pub coarse_conductor_exponent: usize,
    /// Number of quadratic Artin--Schreier steps in the relative tower.
    pub artin_schreier_step_count: usize,
    /// Degree `2^ell` of the fine cyclotomic extension.
    pub fine_galois_degree: BigUint,
    /// Degree `2^(a-1)` of the coarse cyclotomic extension.
    pub coarse_galois_degree: BigUint,
    /// Degree `2^step_count` of the relative extension.
    pub relative_extension_degree: BigUint,
    /// Twice the genus of the fine cyclotomic curve.
    pub fine_twice_genus: BigUint,
    /// Twice the genus of the coarse cyclotomic curve.
    pub coarse_twice_genus: BigUint,
    /// Dimension of the relative first cohomology.
    pub relative_first_cohomology_dimension: BigUint,
    /// Dimension of the relative Jacobian quotient.
    pub relative_abelian_dimension: BigUint,
    /// Cramer--Xing's guaranteed `2`-adic trace-divisibility exponent
    /// `ceil(degree / relative_abelian_dimension)` for a `2`-rank-zero
    /// abelian variety over `GF(2^degree)`.
    pub p_zero_trace_divisibility_exponent: usize,
    /// Corresponding guaranteed trace divisor.
    pub p_zero_trace_divisor: BigUint,
    /// Integer relative Hasse--Weil envelope using `2^ceil(degree/2)`.
    pub integer_relative_weil_numerator: BigUint,
    /// Connected trace allowance `2^(2ell-2)`.
    pub connected_top_allowance_numerator: BigUint,
    /// Smallest integral saving over relative Hasse--Weil required by the
    /// endpoint ledger.
    pub required_saving_ceiling: BigUint,
    /// Selected one-sided allowance after spending the complete proved
    /// low-conductor Weil envelope.
    pub one_sided_negative_allowance_numerator: BigUint,
    /// Smallest integral saving over relative Hasse--Weil required by the
    /// selected one-sided premise.
    pub one_sided_required_saving_ceiling: BigUint,
}

impl PopulationRefinementConnectedTopImplication {
    /// Whether the proved low part and assumed connected top part close the
    /// exact endpoint triangle.
    #[must_use]
    pub fn proves_candidate_discrepancy_bound(&self) -> bool {
        &self.low_weil_triangle_numerator + &self.connected_top_assumption_numerator
            <= self.candidate_target_numerator
    }
}

impl PopulationRefinementOneSidedConnectedImplication {
    /// Whether a supplied signed connected trace satisfies the strict
    /// one-sided premise that closes the identity-population lower bound.
    #[must_use]
    pub fn trace_closes_candidate(&self, connected_trace: &BigInt) -> bool {
        connected_trace > &-BigInt::from(self.negative_allowance_numerator.clone())
    }

    /// Whether the allowance exactly spends the target not already reserved
    /// for the proved low-conductor envelope.
    #[must_use]
    pub fn has_exact_allowance_partition(&self) -> bool {
        &self.low_weil_triangle_numerator + &self.negative_allowance_numerator
            == self.candidate_target_numerator
    }
}

impl PopulationRefinementHybridImplication {
    /// Whether the hybrid assumptions close the exact endpoint triangle.
    #[must_use]
    pub fn proves_candidate_discrepancy_bound(&self) -> bool {
        &self.weil_triangle_numerator + &self.square_root_fibre_triangle_numerator
            <= self.candidate_target_numerator
    }
}

impl PopulationRefinementTopPolynomialImplication {
    /// Whether the proved low part and assumed top part close the endpoint
    /// Haar triangle.
    #[must_use]
    pub fn proves_candidate_discrepancy_bound(&self) -> bool {
        &self.low_weil_scaled_numerator + &self.top_polynomial_scaled_numerator
            <= self.candidate_target_scaled_numerator
    }
}

impl PopulationRefinementEnvelopeImplication {
    /// Whether the proposed envelope alone closes this endpoint.
    #[must_use]
    pub fn proves_candidate_discrepancy_bound(&self) -> bool {
        self.envelope_triangle_numerator <= self.candidate_target_numerator
    }
}

impl PopulationRefinementTriangleReport {
    /// Whether the exact Haar triangle ledger proves the `2^ell` discrepancy
    /// bound for this finite distribution.
    #[must_use]
    pub fn proves_candidate_discrepancy_bound(&self) -> bool {
        self.triangle_numerator <= self.candidate_target_numerator
    }

    /// Whether every finite level satisfies
    /// `H_j^* <= 3j 2^ceil((degree-j)/2)`.
    ///
    /// This checks only the supplied finite distribution.  It does not infer
    /// the same bound at another degree or conductor.
    #[must_use]
    pub fn satisfies_square_root_fibre_envelope(&self) -> bool {
        self.levels.iter().all(|row| {
            let residual = self.degree - row.level;
            let exponent = residual.div_ceil(2);
            BigUint::from(row.maximum_sibling_difference)
                <= ((BigUint::from(3_u8) * BigUint::from(row.level)) << exponent)
        })
    }

    /// Whether the exact finite connected top trace satisfies
    /// `abs(trace) <= 2^(2ell-2)`.
    #[must_use]
    pub fn satisfies_connected_top_candidate(&self) -> bool {
        self.connected_top_signed_numerator.magnitude() <= &self.connected_top_candidate_numerator
    }
}

/// Substitute the proposed raw-refinement square-root envelope into the exact
/// Haar triangle at a Lemire endpoint.
///
/// The assumption is
///
/// ```text
/// max_b |H_j(b)| <= 3j 2^ceil((degree-j)/2),  1<=j<=ell.
/// ```
///
/// This operation proves only the arithmetic implication.  It does not prove
/// the displayed analytic envelope.
///
/// # Errors
///
/// Rejects zero `ell`, a non-endpoint degree, or host-width overflow.
pub fn population_refinement_envelope_implication(
    ell: usize,
    degree: usize,
) -> Result<PopulationRefinementEnvelopeImplication, HayesError> {
    let doubled = ell.checked_mul(2).ok_or_else(|| {
        HayesError::InvalidParameter("refinement envelope ell overflow".to_owned())
    })?;
    if ell == 0 || !matches!(degree.checked_sub(doubled), Some(1 | 2)) {
        return Err(HayesError::InvalidParameter(
            "refinement envelope implication requires degree=2ell+1 or 2ell+2".to_owned(),
        ));
    }
    let mut envelope_triangle_numerator = BigUint::from(0_u8);
    for level in 1..=ell {
        let exponent = (degree - level).div_ceil(2);
        let maximum = (BigUint::from(3_u8) * BigUint::from(level)) << exponent;
        envelope_triangle_numerator += maximum << (level - 1);
    }
    Ok(PopulationRefinementEnvelopeImplication {
        ell,
        degree,
        envelope_triangle_numerator,
        candidate_target_numerator: BigUint::from(1_u8) << doubled,
    })
}

/// Minimize the conductor window on which the proposed square-root-fibre
/// estimate is needed in the exact Haar triangle.
///
/// For `j < first_square_root_fibre_level`, this substitutes the proved
/// individual-character Weil consequence
///
/// ```text
/// H_j^* <= (j-1) 2^ceil(degree/2).
/// ```
///
/// At the remaining top levels it substitutes
///
/// ```text
/// H_j^* <= 3j 2^ceil((degree-j)/2).
/// ```
///
/// The returned split uses the fewest top levels for which the latter bound
/// makes the endpoint triangle close.  It is an implication ledger: the Weil
/// part is proved, while the square-root-fibre part remains an assumption.
///
/// # Errors
///
/// Rejects zero `ell`, a non-endpoint degree, or host-width overflow.
pub fn population_refinement_hybrid_implication(
    ell: usize,
    degree: usize,
) -> Result<PopulationRefinementHybridImplication, HayesError> {
    let doubled = ell
        .checked_mul(2)
        .ok_or_else(|| HayesError::InvalidParameter("hybrid refinement ell overflow".to_owned()))?;
    if ell == 0 || !matches!(degree.checked_sub(doubled), Some(1 | 2)) {
        return Err(HayesError::InvalidParameter(
            "hybrid refinement implication requires degree=2ell+1 or 2ell+2".to_owned(),
        ));
    }
    let target = BigUint::from(1_u8) << doubled;
    let weil_scale = BigUint::from(1_u8) << degree.div_ceil(2);
    for first_family_level in (1..=ell + 1).rev() {
        let mut weil = BigUint::from(0_u8);
        let mut family = BigUint::from(0_u8);
        for level in 1..=ell {
            let maximum = if level < first_family_level {
                BigUint::from(level - 1) * &weil_scale
            } else {
                let exponent = (degree - level).div_ceil(2);
                (BigUint::from(3_u8) * BigUint::from(level)) << exponent
            };
            let contribution = maximum << (level - 1);
            if level < first_family_level {
                weil += contribution;
            } else {
                family += contribution;
            }
        }
        if &weil + &family <= target {
            return Ok(PopulationRefinementHybridImplication {
                ell,
                degree,
                first_square_root_fibre_level: first_family_level,
                square_root_fibre_level_count: ell + 1 - first_family_level,
                weil_triangle_numerator: weil,
                square_root_fibre_triangle_numerator: family,
                candidate_target_numerator: target,
            });
        }
    }
    Err(HayesError::Invariant(
        "full square-root-fibre envelope did not close the endpoint".to_owned(),
    ))
}

/// Substitute the residual top-conductor polynomial saving into the exact
/// Haar triangle.
///
/// On the top window
///
/// ```text
/// ell - 4 ceil(log2 ell) <= j <= ell
/// ```
///
/// the sole assumption is the integer inequality
///
/// ```text
/// (12 ell H_j^*)^2 <= 25 (j-1)^2 2^degree.          (TOP-POLY)
/// ```
///
/// Equivalently, `H_j^* <= (j-1) 2^(degree/2)/(2.4 ell)`.  Below that
/// window the operation uses the proved individual-character Weil estimate.
/// For odd degree, `sqrt(2)<3/2` converts both contributions to rational
/// integer upper bounds; no floating-point comparison is used.  The report
/// proves only this arithmetic implication, not `(TOP-POLY)` itself.
///
/// # Errors
///
/// Rejects `ell<200`, a non-endpoint degree, or host-width overflow.
pub fn population_refinement_top_polynomial_implication(
    ell: usize,
    degree: usize,
) -> Result<PopulationRefinementTopPolynomialImplication, HayesError> {
    let doubled = ell.checked_mul(2).ok_or_else(|| {
        HayesError::InvalidParameter("top-polynomial refinement ell overflow".to_owned())
    })?;
    if ell < 200 || !matches!(degree.checked_sub(doubled), Some(1 | 2)) {
        return Err(HayesError::InvalidParameter(
            "top-polynomial implication requires ell>=200 and degree=2ell+1 or 2ell+2".to_owned(),
        ));
    }
    let ceil_log = ell.ilog2() as usize + usize::from(!ell.is_power_of_two());
    let top_width = 4_usize
        .checked_mul(ceil_log)
        .ok_or_else(|| HayesError::InvalidParameter("top-polynomial window overflow".to_owned()))?;
    let first_top_level = ell.checked_sub(top_width).ok_or_else(|| {
        HayesError::InvalidParameter("top-polynomial window underflow".to_owned())
    })?;
    if first_top_level == 0 {
        return Err(HayesError::InvalidParameter(
            "top-polynomial window reaches level zero".to_owned(),
        ));
    }

    let odd_degree = !degree.is_multiple_of(2);
    let common_denominator = if odd_degree {
        8_usize.checked_mul(ell)
    } else {
        12_usize.checked_mul(ell)
    }
    .ok_or_else(|| {
        HayesError::InvalidParameter("top-polynomial denominator overflow".to_owned())
    })?;
    let low_coefficient = 12_usize.checked_mul(ell).ok_or_else(|| {
        HayesError::InvalidParameter("top-polynomial low coefficient overflow".to_owned())
    })?;
    let base_exponent = ell + usize::from(!odd_degree);
    let mut low_weil_scaled_numerator = BigUint::from(0_u8);
    let mut top_polynomial_scaled_numerator = BigUint::from(0_u8);
    for level in 1..=ell {
        let exponent = base_exponent.checked_add(level - 1).ok_or_else(|| {
            HayesError::InvalidParameter("top-polynomial exponent overflow".to_owned())
        })?;
        let weighted = BigUint::from(level - 1) << exponent;
        if level < first_top_level {
            low_weil_scaled_numerator += BigUint::from(low_coefficient) * weighted;
        } else {
            top_polynomial_scaled_numerator += BigUint::from(5_u8) * weighted;
        }
    }
    Ok(PopulationRefinementTopPolynomialImplication {
        ell,
        degree,
        first_top_level,
        top_level_count: ell + 1 - first_top_level,
        common_denominator,
        low_weil_scaled_numerator,
        top_polynomial_scaled_numerator,
        candidate_target_scaled_numerator: BigUint::from(common_denominator) << doubled,
    })
}

/// Combine the proved low-conductor Weil bounds with one connected signed
/// top-conductor trace assumption.
///
/// Put `L=ceil(log2(ell))+1` and `a=ell-L`.  The low levels `j<a` are bounded
/// individually by `(j-1)2^ceil(degree/2)`.  The sole remaining assumption is
///
/// ```text
/// |sum_(j=a)^ell 2^(j-1) H_j(1)| <= 2^(2ell-2).
/// ```
///
/// The connected sum is exactly
///
/// ```text
/// 2^ell N_ell(1) - 2^(a-1) N_(a-1)(1),
/// ```
///
/// so no absolute value is taken between its conductor levels.  For every
/// `ell>=200` the proved low part is less than half the target and the assumed
/// connected part is one quarter of it.
///
/// # Errors
///
/// Rejects `ell<4`, a non-endpoint degree, or host-width overflow.
pub fn population_refinement_connected_top_implication(
    ell: usize,
    degree: usize,
) -> Result<PopulationRefinementConnectedTopImplication, HayesError> {
    let doubled = ell.checked_mul(2).ok_or_else(|| {
        HayesError::InvalidParameter("connected refinement ell overflow".to_owned())
    })?;
    if ell < 4 || !matches!(degree.checked_sub(doubled), Some(1 | 2)) {
        return Err(HayesError::InvalidParameter(
            "connected refinement implication requires ell>=4 and degree=2ell+1 or 2ell+2"
                .to_owned(),
        ));
    }
    let ceil_log = ell.ilog2() as usize + usize::from(!ell.is_power_of_two());
    let top_level_count = ceil_log + 2;
    let first_top_level = ell.checked_sub(ceil_log + 1).ok_or_else(|| {
        HayesError::InvalidParameter("connected refinement window underflow".to_owned())
    })?;
    if first_top_level == 0 {
        return Err(HayesError::InvalidParameter(
            "connected refinement window reaches level zero".to_owned(),
        ));
    }
    let weil_scale = BigUint::from(1_u8) << degree.div_ceil(2);
    let mut low_weil_triangle_numerator = BigUint::from(0_u8);
    let mut connected_top_individual_weil_numerator = BigUint::from(0_u8);
    for level in 1..first_top_level {
        low_weil_triangle_numerator += (BigUint::from(level - 1) * &weil_scale) << (level - 1);
    }
    for level in first_top_level..=ell {
        connected_top_individual_weil_numerator +=
            (BigUint::from(level - 1) * &weil_scale) << (level - 1);
    }
    let connected_top_assumption_numerator = BigUint::from(1_u8) << (doubled - 2);
    let connected_top_required_saving_ceiling = (&connected_top_individual_weil_numerator
        + &connected_top_assumption_numerator
        - BigUint::from(1_u8))
        / &connected_top_assumption_numerator;
    Ok(PopulationRefinementConnectedTopImplication {
        ell,
        degree,
        first_top_level,
        top_level_count,
        low_weil_triangle_numerator,
        connected_top_individual_weil_numerator,
        connected_top_assumption_numerator,
        connected_top_required_saving_ceiling,
        candidate_target_numerator: BigUint::from(1_u8) << doubled,
    })
}

/// Retain the top identity-path increments as one signed trace and charge the
/// proved Weil envelope only below that window.
///
/// If a=ell-ceil(log2(ell))-1, Haar telescoping gives
///
///     C = sum_(j=a)^ell 2^(j-1) H_j(1)
///       = 2^ell N_ell(1) - 2^(a-1) N_(a-1)(1).
///
/// The lower levels have absolute value at most `W_low`, computed exactly by
/// [`population_refinement_connected_top_implication`]. Therefore the sole
/// premise
///
///     C > -(2^(2ell) - W_low)
///
/// implies `N_ell(1) > 2^(degree-ell)-2^ell`. This is strictly weaker than
/// the earlier symmetric assumption abs(C)<=2^(2ell-2) and weaker in logical
/// shape than a separate bound on every top-level sibling maximum. The
/// operation proves only this arithmetic implication, not the displayed
/// trace premise.
///
/// # Errors
///
/// Rejects the same invalid endpoints as
/// [`population_refinement_connected_top_implication`] and fails if its
/// proved low-conductor envelope exhausts the Haar target.
pub fn population_refinement_one_sided_connected_implication(
    ell: usize,
    degree: usize,
) -> Result<PopulationRefinementOneSidedConnectedImplication, HayesError> {
    let symmetric = population_refinement_connected_top_implication(ell, degree)?;
    if symmetric.low_weil_triangle_numerator >= symmetric.candidate_target_numerator {
        return Err(HayesError::Invariant(
            "low-conductor Weil envelope exhausts the one-sided Haar target".to_owned(),
        ));
    }
    let negative_allowance_numerator =
        &symmetric.candidate_target_numerator - &symmetric.low_weil_triangle_numerator;
    let required_saving_ceiling = (&symmetric.connected_top_individual_weil_numerator
        + &negative_allowance_numerator
        - BigUint::from(1_u8))
        / &negative_allowance_numerator;
    Ok(PopulationRefinementOneSidedConnectedImplication {
        ell,
        degree,
        first_top_level: symmetric.first_top_level,
        top_level_count: symmetric.top_level_count,
        low_weil_triangle_numerator: symmetric.low_weil_triangle_numerator,
        connected_top_individual_weil_numerator: symmetric.connected_top_individual_weil_numerator,
        negative_allowance_numerator,
        required_saving_ceiling,
        candidate_target_numerator: symmetric.candidate_target_numerator,
    })
}

fn carlitz_twice_genus(level: usize) -> BigUint {
    if level <= 1 {
        BigUint::from(0_u8)
    } else {
        (BigUint::from(level - 2) << level) + BigUint::from(2_u8)
    }
}

/// Re-express the connected top-conductor target as a relative trace in the
/// binary Carlitz cyclotomic tower.
///
/// If coherent torsion generators satisfy
/// `C_t(lambda_(r+1))=lambda_r`, then `y_(r+1)=lambda_(r+1)/t` obeys
///
/// ```text
/// y_(r+1)^2 + y_(r+1) = lambda_r/t^2.
/// ```
///
/// Thus every adjacent field in the returned window is a quadratic
/// Artin--Schreier step.  The genus formula
/// `2g_j=(j-2)2^j+2` then makes the relative cohomology dimension equal to
/// the exact sum of separate conductor-level Weil degrees.
///
/// Deuring--Shafarevich gives `2`-rank zero at the fine and coarse levels.
/// Since the coarse Jacobian is an isogeny factor of the fine Jacobian, the
/// relative quotient also has `2`-rank zero.  Cramer--Xing's general
/// `2`-rank-zero trace theorem then guarantees divisibility only by
///
/// ```text
/// 2^ceil(degree / relative_abelian_dimension).
/// ```
///
/// The report prices that exponent exactly.  It is one throughout the Lemire
/// endpoint range, so zero `2`-rank supplies only parity and can improve the
/// integral relative Hasse--Weil envelope by at most one.
///
/// # Errors
///
/// Rejects the same invalid endpoints as
/// [`population_refinement_connected_top_implication`].
pub fn carlitz_connected_top_geometry(
    ell: usize,
    degree: usize,
) -> Result<CarlitzConnectedTopGeometry, HayesError> {
    let implication = population_refinement_connected_top_implication(ell, degree)?;
    let one_sided = population_refinement_one_sided_connected_implication(ell, degree)?;
    let fine_level = ell;
    let coarse_level = implication.first_top_level - 1;
    let fine_twice_genus = carlitz_twice_genus(fine_level);
    let coarse_twice_genus = carlitz_twice_genus(coarse_level);
    let fine_galois_degree = BigUint::from(1_u8) << fine_level;
    let coarse_galois_degree = BigUint::from(1_u8) << coarse_level;
    let relative_extension_degree = BigUint::from(1_u8) << implication.top_level_count;
    if &coarse_galois_degree * &relative_extension_degree != fine_galois_degree {
        return Err(HayesError::Invariant(
            "Carlitz relative tower degrees do not multiply".to_owned(),
        ));
    }
    let relative_first_cohomology_dimension = &fine_twice_genus - &coarse_twice_genus;
    if relative_first_cohomology_dimension.bit(0) {
        return Err(HayesError::Invariant(
            "Carlitz relative cohomology dimension is odd".to_owned(),
        ));
    }
    let relative_abelian_dimension: BigUint = &relative_first_cohomology_dimension >> 1_usize;
    let relative_abelian_dimension_usize = relative_abelian_dimension.to_usize();
    let p_zero_trace_divisibility_exponent = match relative_abelian_dimension_usize {
        Some(0) => {
            return Err(HayesError::Invariant(
                "Carlitz relative Jacobian quotient has dimension zero".to_owned(),
            ));
        }
        Some(dimension) => degree.div_ceil(dimension),
        // A positive BigUint that does not fit usize is larger than `degree`.
        None => 1,
    };
    let p_zero_trace_divisor = BigUint::from(1_u8) << p_zero_trace_divisibility_exponent;
    let integer_relative_weil_numerator =
        &relative_first_cohomology_dimension << degree.div_ceil(2);
    if integer_relative_weil_numerator != implication.connected_top_individual_weil_numerator {
        return Err(HayesError::Invariant(
            "Carlitz relative genus does not reproduce the top Weil envelope".to_owned(),
        ));
    }
    Ok(CarlitzConnectedTopGeometry {
        ell,
        degree,
        fine_conductor_exponent: fine_level + 1,
        coarse_conductor_exponent: coarse_level + 1,
        artin_schreier_step_count: implication.top_level_count,
        fine_galois_degree,
        coarse_galois_degree,
        relative_extension_degree,
        fine_twice_genus,
        coarse_twice_genus,
        relative_first_cohomology_dimension,
        relative_abelian_dimension,
        p_zero_trace_divisibility_exponent,
        p_zero_trace_divisor,
        integer_relative_weil_numerator,
        connected_top_allowance_numerator: implication.connected_top_assumption_numerator,
        required_saving_ceiling: implication.connected_top_required_saving_ceiling,
        one_sided_negative_allowance_numerator: one_sided.negative_allowance_numerator,
        one_sided_required_saving_ceiling: one_sided.required_saving_ceiling,
    })
}

impl FourthMomentConductorDecomposition {
    /// Expose the exact conductor martingale product for root kurtosis.
    ///
    /// Each binary refinement splits a nonnegative parent mass into `u,v`, so
    /// `C_(j-1)<=C_j<=2C_(j-1)`.  The returned factors record the equivalent
    /// exact identity `C_j/C_(j-1)=1+E_j/C_(j-1)` and fail closed if either
    /// inequality or the endpoint telescope is violated.
    ///
    /// # Errors
    ///
    /// Returns an invariant error for an empty/zero-energy decomposition, a
    /// broken conductor chain, a factor outside `[1,2]`, or a failed endpoint
    /// reconstruction.
    pub fn kurtosis_product(&self) -> Result<ConductorKurtosisProductReport, HayesError> {
        let mut previous = self.second_moment.pow(2);
        if previous == BigUint::from(0_u8) {
            return Err(HayesError::Invariant(
                "conductor kurtosis product has zero second moment".to_owned(),
            ));
        }
        let mut factors = Vec::with_capacity(self.levels.len());
        for row in &self.levels {
            if row.cumulative_fourier_energy != &previous + &row.exact_fourier_energy {
                return Err(HayesError::Invariant(format!(
                    "conductor kurtosis chain breaks at level {}",
                    row.level
                )));
            }
            if row.cumulative_fourier_energy > (&previous << 1_usize) {
                return Err(HayesError::Invariant(format!(
                    "conductor kurtosis factor exceeds two at level {}",
                    row.level
                )));
            }
            factors.push(ConductorKurtosisFactor {
                level: row.level,
                factor_numerator: row.cumulative_fourier_energy.clone(),
                factor_denominator: previous.clone(),
                imbalance_numerator: row.exact_fourier_energy.clone(),
                imbalance_denominator: previous.clone(),
            });
            previous.clone_from(&row.cumulative_fourier_energy);
        }
        if factors.len() != self.ell {
            return Err(HayesError::Invariant(format!(
                "conductor kurtosis product has {} factors, expected {}",
                factors.len(),
                self.ell
            )));
        }
        let root_ratio_numerator = (BigUint::from(1_u8) << self.ell) * &self.fourth_moment;
        let root_ratio_denominator = self.second_moment.pow(2);
        if previous != root_ratio_numerator {
            return Err(HayesError::Invariant(
                "conductor kurtosis product misses the fourth-moment endpoint".to_owned(),
            ));
        }
        Ok(ConductorKurtosisProductReport {
            ell: self.ell,
            degree: self.degree,
            factors,
            root_ratio_numerator,
            root_ratio_denominator,
        })
    }

    /// Test the buffered geometric conductor estimate implying `R_0<=4`.
    ///
    /// Put `h=ceil(ell/2)`.  The finite diagnostic checks
    ///
    /// ```text
    /// sum_(j<h) E_j <= (3/2) 2^(h-ell) M_2^2,
    /// E_j             <= (3/2) 2^(j-ell) M_2^2  (j>=h).
    /// ```
    ///
    /// Summing the geometric tail and the buffered low block gives exactly
    /// `sum_j E_j<=3 M_2^2`.  Finite success does not prove either inequality
    /// uniformly.
    #[must_use]
    pub fn satisfies_connected_geometric_split(&self) -> bool {
        let split = self.ell.div_ceil(2);
        let second_square = self.second_moment.pow(2);
        let three_second_square = BigUint::from(3_u8) * &second_square;
        let low = self
            .levels
            .iter()
            .filter(|level| level.level < split)
            .fold(BigUint::from(0_u8), |sum, level| {
                sum + &level.exact_fourier_energy
            });
        let low_shift = self.ell - split + 1;
        if (low << low_shift) > three_second_square {
            return false;
        }
        self.levels
            .iter()
            .filter(|level| level.level >= split)
            .all(|level| {
                (&level.exact_fourier_energy << (self.ell - level.level + 1)) <= three_second_square
            })
    }
}

/// Worst local `L2/L1` concentration on one Witt-cylinder level.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WittCylinderConcentrationLevel {
    /// Principal-unit truncation level defining the cylinders.
    pub level: usize,
    /// Number of cylinders, exactly `2^level`.
    pub cylinder_count: usize,
    /// Full classes below each cylinder, exactly `2^(ell-level)`.
    pub descendant_count: usize,
    /// Cylinder attaining the largest exact concentration ratio.
    pub witness_cylinder: usize,
    /// Numerator `descendant_count * sum_(e below b) D_e^4`.
    pub maximum_ratio_numerator: BigUint,
    /// Denominator `(sum_(e below b) D_e^2)^2`.
    pub maximum_ratio_denominator: BigUint,
    /// Cylinder attaining the largest max-to-average squared discrepancy.
    pub dominance_witness_cylinder: usize,
    /// Numerator `descendant_count * max_(e below b) D_e^2`.
    pub maximum_dominance_numerator: BigUint,
    /// Denominator `sum_(e below b) D_e^2`.
    pub maximum_dominance_denominator: BigUint,
}

/// Local concentration ledger for squared discrepancies on every Witt cylinder.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WittCylinderConcentrationReport {
    /// Coefficient-prefix length.
    pub ell: usize,
    /// Endpoint degree.
    pub degree: usize,
    /// Levels `0..=ell` in increasing order.
    pub levels: Vec<WittCylinderConcentrationLevel>,
}

impl WittCylinderConcentrationReport {
    /// Whether every measured cylinder satisfies the conjectural linear bound.
    ///
    /// This checks a finite report only and grants no universal theorem credit.
    #[must_use]
    pub fn satisfies_linear_ceiling(&self) -> bool {
        let ceiling = BigUint::from(self.ell);
        self.levels.iter().all(|level| {
            level.maximum_ratio_denominator != BigUint::from(0_u8)
                && level.maximum_ratio_numerator <= &ceiling * &level.maximum_ratio_denominator
        })
    }

    /// Whether max-to-average dominance proves the linear concentration bound.
    ///
    /// Since `sum f_e^2 <= (max f_e) sum f_e`, this strictly stronger finite
    /// diagnostic implies [`Self::satisfies_linear_ceiling`].
    #[must_use]
    pub fn satisfies_linear_dominance_ceiling(&self) -> bool {
        let ceiling = BigUint::from(self.ell);
        self.levels.iter().all(|level| {
            level.maximum_dominance_denominator != BigUint::from(0_u8)
                && level.maximum_dominance_numerator
                    <= &ceiling * &level.maximum_dominance_denominator
        })
    }

    /// Whether the measured root ratio is at most four.
    ///
    /// This is exactly the finite form of connected-cumulant domination; it
    /// does not extrapolate the observation to unmeasured endpoints.
    #[must_use]
    pub fn root_ratio_at_most_four(&self) -> bool {
        self.levels.first().is_some_and(|root| {
            root.maximum_ratio_denominator != BigUint::from(0_u8)
                && root.maximum_ratio_numerator
                    <= BigUint::from(4_u8) * &root.maximum_ratio_denominator
        })
    }
}

impl ClassPopulationDistribution {
    /// Largest admitted exponent for an exact central absolute power sum.
    ///
    /// The distribution itself already has `2^ell` entries.  Bounding the
    /// exponent prevents an otherwise tiny input from constructing
    /// arbitrarily large intermediate bignums after that expensive transform.
    pub const MAX_CENTRAL_POWER: u32 = 64;

    /// Uniform population mean `2^(degree-ell)`.
    #[must_use]
    pub fn uniform_mean(&self) -> Option<u128> {
        let shift = u32::try_from(self.degree.checked_sub(self.ell)?).ok()?;
        1_u128.checked_shl(shift)
    }

    /// Largest absolute class deviation from the uniform mean.
    #[must_use]
    pub fn maximum_absolute_deviation(&self) -> Option<u128> {
        let mean = self.uniform_mean()?;
        self.counts.iter().map(|count| count.abs_diff(mean)).max()
    }

    /// Exact `sum_e |N_e - mu|^power` over all classes.
    ///
    /// Even powers are the central moments used by the higher-moment route to
    /// an `L^infinity` estimate.  Odd powers are retained as absolute moments,
    /// so the result is always nonnegative and has one unambiguous meaning.
    ///
    /// # Errors
    ///
    /// Returns [`HayesError::InvalidParameter`] unless `power` is in
    /// `1..=MAX_CENTRAL_POWER`, or if this distribution has no exact uniform
    /// mean.
    pub fn central_absolute_power_sum(&self, power: u32) -> Result<BigUint, HayesError> {
        if !(1..=Self::MAX_CENTRAL_POWER).contains(&power) {
            return Err(HayesError::InvalidParameter(format!(
                "central absolute power must be in 1..={}, got {power}",
                Self::MAX_CENTRAL_POWER
            )));
        }
        let mean = self.uniform_mean().ok_or_else(|| {
            HayesError::InvalidParameter("class distribution has no exact uniform mean".to_owned())
        })?;
        Ok(self
            .counts
            .iter()
            .map(|count| BigUint::from(count.abs_diff(mean)).pow(power))
            .sum())
    }

    /// Decompose the exact Fourier second moment by Efron--Stein coordinate
    /// support weight.
    ///
    /// For a subset `S` of the stable cyclic factors, let `B_S(y)` be the sum
    /// of the discrepancies over the fibre with selected coordinates `y`.
    /// Subgroup Parseval gives
    ///
    /// ```text
    /// sum_(supp chi subset S) |Dhat(chi)|^2
    ///   = |E_S| sum_y B_S(y)^2.
    /// ```
    ///
    /// Mobius inversion on the Boolean subset lattice recovers exact-support
    /// masses, which are then grouped by
    /// `weight=sum_(i in supp chi) log2(order_i)`.
    ///
    /// # Errors
    ///
    /// Returns a resource decline before the subset projections, or a typed
    /// invariant/parameter error from the exact population distribution.
    #[allow(clippy::too_many_lines)]
    pub fn efron_stein_spectral_weight_report(
        &self,
        max_projection_cells: usize,
    ) -> Result<EfronSteinSpectralWeightReport, HayesError> {
        let factors = principal_unit_factors(self.ell);
        let factor_count = factors.len();
        let factor_shift = u32::try_from(factor_count).map_err(|_| {
            HayesError::InvalidParameter("Efron--Stein factor count exceeds u32".to_owned())
        })?;
        let subset_count = 1_usize.checked_shl(factor_shift).ok_or_else(|| {
            HayesError::InvalidParameter("Efron--Stein subset count overflow".to_owned())
        })?;
        let work = subset_count.checked_mul(self.counts.len()).ok_or_else(|| {
            HayesError::InvalidParameter("Efron--Stein projection work overflow".to_owned())
        })?;
        check_limit("efron_stein_projection_cells", work, max_projection_cells)?;
        let mean = self.uniform_mean().ok_or_else(|| {
            HayesError::InvalidParameter("class distribution has no exact uniform mean".to_owned())
        })?;
        let factor_weights = factors
            .iter()
            .map(|factor| factor.order.trailing_zeros() as usize)
            .collect::<Vec<_>>();
        if factor_weights.iter().sum::<usize>() != self.ell {
            return Err(HayesError::Invariant(
                "Efron--Stein factor weights do not sum to ell".to_owned(),
            ));
        }
        let discrepancies = self
            .counts
            .iter()
            .map(|count| BigInt::from(*count) - BigInt::from(mean))
            .collect::<Vec<_>>();
        let mut exact_support_masses = vec![BigUint::from(0_u8); subset_count];
        let mut grouped = BTreeMap::<usize, (usize, BigUint)>::new();
        for subset in 0..subset_count {
            let mut selected_group_order = 1_usize;
            let mut character_count = 1_usize;
            let mut weight = 0_usize;
            for (factor_index, factor) in factors.iter().enumerate() {
                if subset & (1_usize << factor_index) != 0 {
                    selected_group_order = selected_group_order
                        .checked_mul(factor.order)
                        .ok_or_else(|| {
                            HayesError::InvalidParameter(
                                "Efron--Stein selected group order overflow".to_owned(),
                            )
                        })?;
                    character_count =
                        character_count
                            .checked_mul(factor.order - 1)
                            .ok_or_else(|| {
                                HayesError::InvalidParameter(
                                    "Efron--Stein character count overflow".to_owned(),
                                )
                            })?;
                    weight = weight
                        .checked_add(factor_weights[factor_index])
                        .ok_or_else(|| {
                            HayesError::InvalidParameter(
                                "Efron--Stein support weight overflow".to_owned(),
                            )
                        })?;
                }
            }
            let mut buckets = vec![BigInt::from(0_i8); selected_group_order];
            for (class, discrepancy) in discrepancies.iter().enumerate() {
                let mut quotient = class;
                let mut selected_index = 0_usize;
                let mut selected_stride = 1_usize;
                for (factor_index, factor) in factors.iter().enumerate() {
                    let coordinate = quotient % factor.order;
                    quotient /= factor.order;
                    if subset & (1_usize << factor_index) != 0 {
                        selected_index += coordinate * selected_stride;
                        selected_stride *= factor.order;
                    }
                }
                if quotient != 0 || selected_stride != selected_group_order {
                    return Err(HayesError::Invariant(
                        "Efron--Stein projection left a mixed-radix coordinate".to_owned(),
                    ));
                }
                buckets[selected_index] += discrepancy;
            }
            let cumulative_mass = BigUint::from(selected_group_order)
                * buckets
                    .into_iter()
                    .map(|value| value.magnitude().pow(2))
                    .sum::<BigUint>();
            let mut exact_mass = BigInt::from(cumulative_mass);
            if subset != 0 {
                let mut proper = (subset - 1) & subset;
                loop {
                    exact_mass -= BigInt::from(exact_support_masses[proper].clone());
                    if proper == 0 {
                        break;
                    }
                    proper = (proper - 1) & subset;
                }
            }
            let exact_mass = exact_mass.to_biguint().ok_or_else(|| {
                HayesError::Invariant("Efron--Stein exact-support mass is negative".to_owned())
            })?;
            exact_support_masses[subset].clone_from(&exact_mass);
            let entry = grouped
                .entry(weight)
                .or_insert_with(|| (0, BigUint::from(0_u8)));
            entry.0 = entry.0.checked_add(character_count).ok_or_else(|| {
                HayesError::InvalidParameter("Efron--Stein grouped count overflow".to_owned())
            })?;
            entry.1 += exact_mass;
        }
        if grouped.values().map(|entry| entry.0).sum::<usize>() != self.counts.len() {
            return Err(HayesError::Invariant(
                "Efron--Stein character weights miss the dual group".to_owned(),
            ));
        }
        let total_spectral_second_moment =
            BigUint::from(self.counts.len()) * self.central_absolute_power_sum(2)?;
        if exact_support_masses.iter().sum::<BigUint>() != total_spectral_second_moment {
            return Err(HayesError::Invariant(
                "Efron--Stein support masses miss Parseval".to_owned(),
            ));
        }
        let weights = grouped
            .into_iter()
            .map(|(weight, (character_count, spectral_second_moment))| {
                EfronSteinSpectralWeightMass {
                    weight,
                    character_count,
                    spectral_second_moment,
                }
            })
            .collect();
        Ok(EfronSteinSpectralWeightReport {
            ell: self.ell,
            degree: self.degree,
            factor_weights,
            total_spectral_second_moment,
            weights,
        })
    }

    /// Expand the centred fourth cumulant into exact positive fibre-product
    /// counts and check their signed inclusion--exclusion reconstruction.
    ///
    /// This is the point-counting bridge for geometric attacks.  In
    /// particular, callers must not reinterpret `connected_fourth_cumulant`
    /// as the number of points of a single off-diagonal variety: its defining
    /// combination is virtual and may be negative.
    ///
    /// # Errors
    ///
    /// Returns a parameter error if the distribution has no exact uniform
    /// mean or an invariant failure if the raw fibre products do not recover
    /// the independently computed centred moments and cumulant.
    pub fn connected_fibre_product_report(
        &self,
    ) -> Result<HayesConnectedFibreProductReport, HayesError> {
        let mean = self.uniform_mean().ok_or_else(|| {
            HayesError::InvalidParameter("class distribution has no exact uniform mean".to_owned())
        })?;
        let group_order = BigInt::from(self.counts.len());
        let mean = BigInt::from(mean);
        let total = self
            .counts
            .iter()
            .map(|count| BigInt::from(*count))
            .sum::<BigInt>();
        let raw = |power: u32| {
            self.counts
                .iter()
                .map(|count| BigUint::from(*count).pow(power))
                .sum::<BigUint>()
        };
        let raw_pair_fibre_count = raw(2);
        let raw_triple_fibre_count = raw(3);
        let raw_quadruple_fibre_count = raw(4);
        let reconstructed_second = BigInt::from(raw_pair_fibre_count.clone())
            - BigInt::from(2_u8) * &mean * &total
            + &group_order * mean.pow(2);
        let reconstructed_fourth = BigInt::from(raw_quadruple_fibre_count.clone())
            - BigInt::from(4_u8) * &mean * BigInt::from(raw_triple_fibre_count.clone())
            + BigInt::from(6_u8) * mean.pow(2) * BigInt::from(raw_pair_fibre_count.clone())
            - BigInt::from(4_u8) * mean.pow(3) * &total
            + &group_order * mean.pow(4);
        let centered_second_moment = self.central_absolute_power_sum(2)?;
        let centered_fourth_moment = self.central_absolute_power_sum(4)?;
        if reconstructed_second != BigInt::from(centered_second_moment.clone())
            || reconstructed_fourth != BigInt::from(centered_fourth_moment.clone())
        {
            return Err(HayesError::Invariant(
                "raw fibre products do not reconstruct centered moments".to_owned(),
            ));
        }
        let connected_fourth_cumulant = BigInt::from(self.counts.len())
            * BigInt::from(centered_fourth_moment.clone())
            - BigInt::from(3_u8) * BigInt::from(centered_second_moment.clone()).pow(2);
        if connected_fourth_cumulant != self.fourth_cumulant_numerator()? {
            return Err(HayesError::Invariant(
                "fibre-product cumulant disagrees with direct cumulant".to_owned(),
            ));
        }
        Ok(HayesConnectedFibreProductReport {
            ell: self.ell,
            degree: self.degree,
            raw_pair_fibre_count,
            raw_triple_fibre_count,
            raw_quadruple_fibre_count,
            centered_second_moment,
            centered_fourth_moment,
            connected_fourth_cumulant,
        })
    }

    /// Compare the diagonal fourth moment controlled by ordinary family
    /// monodromy with the product-constrained contraction required here.
    ///
    /// For the Fourier transform `S_chi` of the centred class distribution,
    /// Parseval and convolution give
    ///
    /// ```text
    /// sum_chi |S_chi|^4 = G sum_h (sum_e D_e D_(e+h))^2,
    /// sum_(chi_1...chi_4=1) product_i S_(chi_i) = G^3 M_4.
    /// ```
    ///
    /// These are different tensor contractions.  The second contains every
    /// product-constrained quadruple, while the first sees only the pointwise
    /// diagonal.  `max_autocorrelation_cells` bounds the explicit `G^2`
    /// spatial reconstruction before work begins.
    ///
    /// # Errors
    ///
    /// Returns a resource decline before the autocorrelation table, or a
    /// parameter/invariant error inherited from the exact distribution.
    pub fn character_fourth_moment_comparison(
        &self,
        max_autocorrelation_cells: usize,
    ) -> Result<HayesCharacterFourthMomentComparison, HayesError> {
        let group_order = self.counts.len();
        let work = group_order.checked_mul(group_order).ok_or_else(|| {
            HayesError::InvalidParameter("character fourth-moment work overflow".to_owned())
        })?;
        check_limit(
            "character_fourth_moment_autocorrelation_cells",
            work,
            max_autocorrelation_cells,
        )?;
        let mean = self.uniform_mean().ok_or_else(|| {
            HayesError::InvalidParameter("class distribution has no exact uniform mean".to_owned())
        })?;
        let discrepancies = self
            .counts
            .iter()
            .map(|count| BigInt::from(*count) - BigInt::from(mean))
            .collect::<Vec<_>>();
        let factors = principal_unit_factors(self.ell);
        let mut autocorrelation_square_sum = BigUint::from(0_u8);
        for shift in 0..group_order {
            let mut correlation = BigInt::from(0_i8);
            for class in 0..group_order {
                let shifted = add_mixed_radix_indices(class, shift, &factors)?;
                correlation += &discrepancies[class] * &discrepancies[shifted];
            }
            autocorrelation_square_sum += correlation.magnitude().pow(2);
        }
        let group_order_big = BigUint::from(group_order);
        let pointwise_character_fourth_moment = &group_order_big * autocorrelation_square_sum;
        let centered_second = self.central_absolute_power_sum(2)?;
        let character_second_moment = &group_order_big * centered_second;
        let single_wick_pairing = character_second_moment.pow(2);
        let three_wick_pairings = BigUint::from(3_u8) * &single_wick_pairing;
        let centered_fourth = self.central_absolute_power_sum(4)?;
        let product_constrained_fourth_moment = group_order_big.pow(3) * centered_fourth;
        let connected_product_constrained_numerator =
            BigInt::from(group_order_big.pow(2)) * self.fourth_cumulant_numerator()?;
        if BigInt::from(product_constrained_fourth_moment.clone())
            - BigInt::from(three_wick_pairings.clone())
            != connected_product_constrained_numerator
        {
            return Err(HayesError::Invariant(
                "identity-fibre convolution minus Wick pairings misses the connected cumulant"
                    .to_owned(),
            ));
        }
        Ok(HayesCharacterFourthMomentComparison {
            ell: self.ell,
            degree: self.degree,
            pointwise_character_fourth_moment,
            character_second_moment,
            single_wick_pairing,
            three_wick_pairings,
            product_constrained_fourth_moment,
            connected_product_constrained_numerator,
        })
    }

    /// Experimental endpoint envelope `64 ell^2 2^(3 ell)` for the fourth
    /// central moment.
    ///
    /// This is deliberately an observed candidate, not a theorem.  The method
    /// rejects non-endpoint degrees so a caller cannot silently generalize the
    /// finite diagnostic beyond `n in {2 ell + 1, 2 ell + 2}`.
    ///
    /// # Errors
    ///
    /// Returns [`HayesError::InvalidParameter`] outside the two Lemire
    /// endpoints or if an exponent calculation cannot be represented.
    pub fn fourth_moment_candidate_bound(&self) -> Result<BigUint, HayesError> {
        let odd = self
            .ell
            .checked_mul(2)
            .and_then(|value| value.checked_add(1));
        let even = self
            .ell
            .checked_mul(2)
            .and_then(|value| value.checked_add(2));
        if Some(self.degree) != odd && Some(self.degree) != even {
            return Err(HayesError::InvalidParameter(format!(
                "fourth-moment candidate is endpoint-only: ell={}, degree={}",
                self.ell, self.degree
            )));
        }
        let exponent = self.ell.checked_mul(3).ok_or_else(|| {
            HayesError::InvalidParameter("fourth-moment exponent overflow".to_owned())
        })?;
        Ok((BigUint::from(64_u8) * BigUint::from(self.ell).pow(2)) << exponent)
    }

    /// Whether this exact endpoint distribution meets the experimental
    /// fourth-moment envelope.
    ///
    /// # Errors
    ///
    /// Returns any parameter error from [`Self::fourth_moment_candidate_bound`]
    /// or [`Self::central_absolute_power_sum`].
    pub fn satisfies_fourth_moment_candidate(&self) -> Result<bool, HayesError> {
        Ok(self.central_absolute_power_sum(4)? <= self.fourth_moment_candidate_bound()?)
    }

    /// Whether this exact endpoint fourth moment alone proves an irreducible
    /// in the identity class after removing proper prime powers.
    ///
    /// This checks the strict and endpoint-specific threshold
    /// `M_4<(2^(n-ell)-P_n)^4`, not the insufficient positivity-only bound
    /// `M_4<2^(4(n-ell))`.
    ///
    /// # Errors
    ///
    /// Returns a typed endpoint or exact-moment error.
    pub fn fourth_moment_proves_identity_class_irreducible(&self) -> Result<bool, HayesError> {
        let ledger = weak_fourth_moment_endpoint_ledger(self.ell, self.degree)?;
        Ok(self.central_absolute_power_sum(4)? < ledger.strict_irreducible_fourth_moment_threshold)
    }

    /// Whether the exact fourth moment alone forces every class discrepancy
    /// to be at most `2^ell`.
    ///
    /// This uses `max_e |N_e-mu|^4 <= sum_e |N_e-mu|^4`.  It certifies only
    /// the supplied finite distribution; it does not extrapolate the observed
    /// fourth-moment envelope.
    ///
    /// # Errors
    ///
    /// Returns a typed parameter error if the exact moment or shift cannot be
    /// represented.
    pub fn fourth_moment_proves_candidate_discrepancy_bound(&self) -> Result<bool, HayesError> {
        let exponent = self.ell.checked_mul(4).ok_or_else(|| {
            HayesError::InvalidParameter("fourth-moment threshold overflow".to_owned())
        })?;
        Ok(self.central_absolute_power_sum(4)? <= (BigUint::from(1_u8) << exponent))
    }

    /// Signed numerator of the centered fourth cumulant.
    ///
    /// With `G=2^ell`, `M_2=sum_e D_e^2`, and `M_4=sum_e D_e^4`, this returns
    ///
    /// ```text
    /// G M_4 - 3 M_2^2.
    /// ```
    ///
    /// Dividing by `G^2` gives the usual fourth cumulant of a uniformly chosen
    /// class discrepancy.  Keeping the integer numerator makes the Gaussian
    /// pairing cancellation exact and rounding-free.
    ///
    /// # Errors
    ///
    /// Returns any typed error from the exact second or fourth central power
    /// sums.
    pub fn fourth_cumulant_numerator(&self) -> Result<BigInt, HayesError> {
        let second = self.central_absolute_power_sum(2)?;
        let fourth = self.central_absolute_power_sum(4)?;
        let group_order = BigUint::from(self.counts.len());
        Ok(BigInt::from(group_order * fourth) - BigInt::from(BigUint::from(3_u8) * second.pow(2)))
    }

    /// Whether the finite connected fourth cumulant is at most `M_2^2`.
    ///
    /// This is equivalent to `2^ell M_4 <= 4 M_2^2`, or root concentration
    /// at most four.  It is a bounded diagnostic, not a uniform proof.
    ///
    /// # Errors
    ///
    /// Returns any typed error from the exact central moments.
    pub fn connected_cumulant_at_most_second_moment_square(&self) -> Result<bool, HayesError> {
        let second = self.central_absolute_power_sum(2)?;
        let cumulant = self.fourth_cumulant_numerator()?;
        Ok(cumulant <= BigInt::from(second.pow(2)))
    }

    /// Decompose the Fourier energy of the squared discrepancies by conductor.
    ///
    /// If `pi_j: E_ell -> E_j` is truncation and
    /// `B_j(b) = sum_(pi_j(e)=b) D_e^2`, finite-group Parseval gives
    ///
    /// ```text
    /// C_j = 2^j sum_(b in E_j) B_j(b)^2.
    /// ```
    ///
    /// Consequently no roots of unity or numerical Fourier arithmetic are
    /// needed.  The method checks monotonicity of the nested Fourier spaces and
    /// both endpoint identities exactly.
    ///
    /// `max_projection_cells` is an explicit work limit for the `ell * 2^ell`
    /// class-to-quotient projections.  It is checked before bucket allocation.
    ///
    /// # Errors
    ///
    /// Returns a typed resource decline when the requested projection work is
    /// too large, a parameter error for a malformed distribution, or an
    /// invariant error if Parseval or conductor nesting fails.
    pub fn fourth_moment_conductor_decomposition(
        &self,
        max_projection_cells: usize,
    ) -> Result<FourthMomentConductorDecomposition, HayesError> {
        let expected_classes = 1_usize
            .checked_shl(u32::try_from(self.ell).map_err(|_| {
                HayesError::InvalidParameter("ell exceeds the host shift domain".to_owned())
            })?)
            .ok_or_else(|| {
                HayesError::InvalidParameter("ell exceeds the host shift domain".to_owned())
            })?;
        if self.counts.len() != expected_classes {
            return Err(HayesError::InvalidParameter(format!(
                "class distribution has {} entries, expected 2^{}={expected_classes}",
                self.counts.len(),
                self.ell
            )));
        }
        let projection_cells = self
            .ell
            .checked_mul(expected_classes)
            .ok_or_else(|| HayesError::InvalidParameter("projection work overflow".to_owned()))?;
        check_limit(
            "fourth_moment_projection_cells",
            projection_cells,
            max_projection_cells,
        )?;

        let mean = self.uniform_mean().ok_or_else(|| {
            HayesError::InvalidParameter("class distribution has no exact uniform mean".to_owned())
        })?;
        let squared_deviations = self
            .counts
            .iter()
            .map(|count| BigUint::from(count.abs_diff(mean)).pow(2))
            .collect::<Vec<_>>();
        let second_moment = squared_deviations.iter().cloned().sum::<BigUint>();
        let fourth_moment = squared_deviations
            .iter()
            .map(|value| value.pow(2))
            .sum::<BigUint>();
        let full_factors = principal_unit_factors(self.ell);
        let mut previous = second_moment.pow(2);
        let mut levels = Vec::with_capacity(self.ell);

        for level in 1..=self.ell {
            let quotient_factors = principal_unit_factors(level);
            let quotient_order = 1_usize << level;
            let mut buckets = vec![BigUint::from(0_u8); quotient_order];
            for (index, value) in squared_deviations.iter().enumerate() {
                let quotient_index =
                    project_mixed_radix_index(index, &full_factors, &quotient_factors)?;
                buckets[quotient_index] += value;
            }
            let cumulative = BigUint::from(quotient_order)
                * buckets.iter().map(|bucket| bucket.pow(2)).sum::<BigUint>();
            if cumulative < previous {
                return Err(HayesError::Invariant(format!(
                    "squared-discrepancy Fourier energy decreases at level {level}"
                )));
            }
            let exact = &cumulative - &previous;
            let haar_difference_square_sum =
                witt_haar_difference_square_sum(level, &quotient_factors, buckets)?;
            if (&haar_difference_square_sum << (level - 1)) != exact {
                return Err(HayesError::Invariant(format!(
                    "Haar refinement energy disagrees with conductor level {level}"
                )));
            }
            levels.push(SquaredDeviationConductorLevel {
                level,
                cumulative_fourier_energy: cumulative.clone(),
                exact_fourier_energy: exact,
                haar_difference_square_sum,
            });
            previous = cumulative;
        }

        let expected_full = BigUint::from(expected_classes) * &fourth_moment;
        if previous != expected_full {
            return Err(HayesError::Invariant(
                "full squared-discrepancy Fourier energy does not equal 2^ell M_4".to_owned(),
            ));
        }
        Ok(FourthMomentConductorDecomposition {
            ell: self.ell,
            degree: self.degree,
            second_moment,
            fourth_moment,
            levels,
        })
    }

    /// Build the exact `L1` Haar triangle ledger for the raw Mangoldt class
    /// populations.
    ///
    /// At each quotient level the method aggregates the full class counts,
    /// pairs the two children of every parent cylinder, and records the
    /// largest absolute sibling difference.  It then reconstructs every
    /// original leaf count from the signed differences and the root total.
    /// The reconstruction is an invariant check independent of the final
    /// triangle comparison.
    ///
    /// `max_projection_cells` bounds both quotient aggregation and leafwise
    /// reconstruction work before any level table is allocated.
    ///
    /// # Errors
    ///
    /// Returns a typed resource decline, rejects a malformed distribution, or
    /// fails closed if a quotient is not binary or the Haar expansion does not
    /// reconstruct every population exactly.
    pub fn population_refinement_triangle(
        &self,
        max_projection_cells: usize,
    ) -> Result<PopulationRefinementTriangleReport, HayesError> {
        if self.ell == 0 {
            return Err(HayesError::InvalidParameter(
                "population refinement requires ell>=1".to_owned(),
            ));
        }
        let ell_shift = u32::try_from(self.ell)
            .map_err(|_| HayesError::InvalidParameter("refinement ell exceeds u32".to_owned()))?;
        let expected_classes = 1_usize.checked_shl(ell_shift).ok_or_else(|| {
            HayesError::InvalidParameter("refinement class count overflow".to_owned())
        })?;
        if self.counts.len() != expected_classes {
            return Err(HayesError::InvalidParameter(
                "refinement ledger received a malformed distribution".to_owned(),
            ));
        }
        let work = self
            .ell
            .checked_mul(expected_classes)
            .and_then(|cells| cells.checked_mul(2))
            .ok_or_else(|| {
                HayesError::InvalidParameter("refinement projection work overflow".to_owned())
            })?;
        check_limit(
            "population_refinement_projection_cells",
            work,
            max_projection_cells,
        )?;
        let mean = self.uniform_mean().ok_or_else(|| {
            HayesError::InvalidParameter("refinement distribution has no uniform mean".to_owned())
        })?;
        let total = self.counts.iter().try_fold(0_u128, |sum, count| {
            sum.checked_add(*count).ok_or_else(|| {
                HayesError::InvalidParameter("refinement population total overflow".to_owned())
            })
        })?;
        let full_factors = principal_unit_factors(self.ell);
        let mut reconstruction = vec![BigInt::from(total); expected_classes];
        let mut triangle_numerator = BigUint::from(0_u8);
        let mut identity_path_triangle_numerator = BigUint::from(0_u8);
        let ceil_log = self.ell.ilog2() as usize + usize::from(!self.ell.is_power_of_two());
        let connected_top_first_level = self.ell.saturating_sub(ceil_log + 1).max(1);
        let mut connected_top_signed_numerator = BigInt::from(0_u8);
        let mut levels = Vec::with_capacity(self.ell);

        for level in 1..=self.ell {
            let level_factors = principal_unit_factors(level);
            let step =
                raw_population_refinement_step(&self.counts, &full_factors, &level_factors, level)?;
            let weight = BigUint::from(1_u8) << (level - 1);
            triangle_numerator += BigUint::from(step.report.maximum_sibling_difference) * &weight;
            let signed_weight = BigInt::from(weight);
            let identity_difference = &step.signed_child_differences[0];
            identity_path_triangle_numerator +=
                identity_difference.magnitude() * signed_weight.magnitude();
            if level >= connected_top_first_level {
                connected_top_signed_numerator += identity_difference * &signed_weight;
            }
            for (index, reconstructed) in reconstruction.iter_mut().enumerate() {
                let child = project_mixed_radix_index(index, &full_factors, &level_factors)?;
                *reconstructed += &step.signed_child_differences[child] * &signed_weight;
            }
            levels.push(step.report);
        }

        let actual_maximum_absolute_deviation = validate_population_refinement_reconstruction(
            &reconstruction,
            &self.counts,
            expected_classes,
            mean,
            &triangle_numerator,
        )?;
        let direct_connected_top = connected_top_direct_trace(
            &self.counts,
            &full_factors,
            self.ell,
            connected_top_first_level,
        )?;
        if connected_top_signed_numerator != direct_connected_top {
            return Err(HayesError::Invariant(
                "connected top refinement sum does not telescope".to_owned(),
            ));
        }

        Ok(PopulationRefinementTriangleReport {
            ell: self.ell,
            degree: self.degree,
            levels,
            triangle_numerator,
            candidate_target_numerator: BigUint::from(1_u8) << (2 * self.ell),
            actual_maximum_absolute_deviation,
            identity_path_triangle_numerator,
            connected_top_first_level,
            connected_top_signed_numerator,
            connected_top_candidate_numerator: BigUint::from(1_u8) << (2 * self.ell - 2),
        })
    }

    /// Normalize the exact refinement sup norms at the square-root scale.
    ///
    /// The method reuses [`Self::population_refinement_triangle`], then checks
    /// the level-one consequence of the degree-zero conductor family and
    /// returns the exact rational constant required at every remaining level.
    /// It performs no floating-point arithmetic and makes no extrapolation
    /// from the admitted finite distribution.
    ///
    /// # Errors
    ///
    /// Propagates the refinement report's typed declines and fails closed if
    /// the level-one sibling difference is nonzero or the report is empty.
    pub fn conductor_layer_sup_norm_diagnostic(
        &self,
        max_projection_cells: usize,
    ) -> Result<ConductorLayerSupNormDiagnostic, HayesError> {
        let refinement = self.population_refinement_triangle(max_projection_cells)?;
        let first = refinement.levels.first().ok_or_else(|| {
            HayesError::Invariant("conductor sup diagnostic has no levels".to_owned())
        })?;
        if first.level != 1 || first.maximum_sibling_difference != 0 {
            return Err(HayesError::Invariant(
                "exact conductor level one must have zero population difference".to_owned(),
            ));
        }

        let mut levels = Vec::with_capacity(refinement.levels.len().saturating_sub(1));
        let mut witness_level = 0_usize;
        let mut maximum_numerator = BigUint::from(0_u8);
        let mut maximum_denominator = BigUint::from(1_u8);
        for row in refinement.levels.iter().skip(1) {
            let level_minus_one = row.level - 1;
            let difference = BigUint::from(row.maximum_sibling_difference);
            let numerator = difference.pow(2) << level_minus_one;
            let denominator = BigUint::from(level_minus_one).pow(2) << self.degree;
            if &numerator * &maximum_denominator > &maximum_numerator * &denominator {
                witness_level = row.level;
                maximum_numerator.clone_from(&numerator);
                maximum_denominator.clone_from(&denominator);
            }
            levels.push(ConductorLayerSupNormLevel {
                level: row.level,
                witness_parent: row.witness_parent,
                maximum_sibling_difference: row.maximum_sibling_difference,
                squared_constant_numerator: numerator,
                squared_constant_denominator: denominator,
            });
        }
        if levels.is_empty() {
            return Err(HayesError::InvalidParameter(
                "conductor sup diagnostic requires ell at least two".to_owned(),
            ));
        }
        Ok(ConductorLayerSupNormDiagnostic {
            ell: self.ell,
            degree: self.degree,
            levels,
            witness_level,
            maximum_squared_constant_numerator: maximum_numerator,
            maximum_squared_constant_denominator: maximum_denominator,
        })
    }

    /// Measure local fourth-over-second concentration on every Witt cylinder.
    ///
    /// For `f_e=D_e^2` and a level-`j` cylinder `b`, this records the largest
    /// exact ratio
    ///
    /// ```text
    /// 2^(ell-j) sum_(e below b) f_e^2
    /// --------------------------------.
    ///       (sum_(e below b) f_e)^2
    /// ```
    ///
    /// The ratio is one for a constant cylinder and its excess is the
    /// normalized Haar square energy below that cylinder.  This finite ledger
    /// does not assert a uniform Carleson bound.
    ///
    /// # Errors
    ///
    /// Returns a typed resource decline before projection or an invariant
    /// error for a malformed class distribution.
    pub fn witt_cylinder_concentration(
        &self,
        max_projection_cells: usize,
    ) -> Result<WittCylinderConcentrationReport, HayesError> {
        let expected_classes = 1_usize
            .checked_shl(u32::try_from(self.ell).map_err(|_| {
                HayesError::InvalidParameter("cylinder level exceeds u32".to_owned())
            })?)
            .ok_or_else(|| {
                HayesError::InvalidParameter("cylinder class count overflow".to_owned())
            })?;
        if self.counts.len() != expected_classes {
            return Err(HayesError::InvalidParameter(
                "cylinder ledger received a malformed distribution".to_owned(),
            ));
        }
        let work = self
            .ell
            .checked_add(1)
            .and_then(|levels| levels.checked_mul(expected_classes))
            .ok_or_else(|| {
                HayesError::InvalidParameter("cylinder projection work overflow".to_owned())
            })?;
        check_limit("witt_cylinder_projection_cells", work, max_projection_cells)?;
        let mean = self.uniform_mean().ok_or_else(|| {
            HayesError::InvalidParameter("cylinder distribution has no uniform mean".to_owned())
        })?;
        let squared = self
            .counts
            .iter()
            .map(|count| BigUint::from(count.abs_diff(mean)).pow(2))
            .collect::<Vec<_>>();
        let full_factors = principal_unit_factors(self.ell);
        let mut levels = Vec::with_capacity(self.ell + 1);
        for level in 0..=self.ell {
            let cylinder_count = 1_usize << level;
            let descendant_count = 1_usize << (self.ell - level);
            let quotient_factors = principal_unit_factors(level);
            let mut masses = vec![BigUint::from(0_u8); cylinder_count];
            let mut square_masses = vec![BigUint::from(0_u8); cylinder_count];
            let mut maxima = vec![BigUint::from(0_u8); cylinder_count];
            for (index, value) in squared.iter().enumerate() {
                let cylinder = if level == 0 {
                    0
                } else {
                    project_mixed_radix_index(index, &full_factors, &quotient_factors)?
                };
                masses[cylinder] += value;
                square_masses[cylinder] += value.pow(2);
                maxima[cylinder] = maxima[cylinder].clone().max(value.clone());
            }
            let mut witness = 0_usize;
            let mut maximum_numerator = BigUint::from(0_u8);
            let mut maximum_denominator = BigUint::from(1_u8);
            let mut dominance_witness = 0_usize;
            let mut maximum_dominance_numerator = BigUint::from(0_u8);
            let mut maximum_dominance_denominator = BigUint::from(1_u8);
            for cylinder in 0..cylinder_count {
                if masses[cylinder] == BigUint::from(0_u8) {
                    continue;
                }
                let numerator = BigUint::from(descendant_count) * &square_masses[cylinder];
                let denominator = masses[cylinder].pow(2);
                if &numerator * &maximum_denominator > &maximum_numerator * &denominator {
                    witness = cylinder;
                    maximum_numerator = numerator;
                    maximum_denominator = denominator;
                }
                let dominance_numerator = BigUint::from(descendant_count) * &maxima[cylinder];
                let dominance_denominator = masses[cylinder].clone();
                if &dominance_numerator * &maximum_dominance_denominator
                    > &maximum_dominance_numerator * &dominance_denominator
                {
                    dominance_witness = cylinder;
                    maximum_dominance_numerator = dominance_numerator;
                    maximum_dominance_denominator = dominance_denominator;
                }
            }
            levels.push(WittCylinderConcentrationLevel {
                level,
                cylinder_count,
                descendant_count,
                witness_cylinder: witness,
                maximum_ratio_numerator: maximum_numerator,
                maximum_ratio_denominator: maximum_denominator,
                dominance_witness_cylinder: dominance_witness,
                maximum_dominance_numerator,
                maximum_dominance_denominator,
            });
        }
        Ok(WittCylinderConcentrationReport {
            ell: self.ell,
            degree: self.degree,
            levels,
        })
    }

    /// Whether every class has positive Mangoldt population.
    #[must_use]
    pub fn all_classes_positive(&self) -> bool {
        self.counts.iter().all(|count| *count != 0)
    }
}

/// Return the exact cyclic structure used by the finite Fourier transform.
///
/// # Errors
///
/// Returns [`HayesError::InvalidParameter`] for an invalid truncation level or
/// [`HayesError::ResourceLimit`] before constructing an over-limit group.
pub fn principal_unit_structure(
    ell: usize,
    limits: HayesLimits,
) -> Result<PrincipalUnitStructure, HayesError> {
    if ell == 0 {
        return Err(HayesError::InvalidParameter(
            "ell must be positive".to_owned(),
        ));
    }
    check_limit("ell", ell, limits.max_ell)?;
    let shift = u32::try_from(ell).map_err(|_| {
        HayesError::InvalidParameter("ell exceeds the host shift domain".to_owned())
    })?;
    let group_order = 1_usize.checked_shl(shift).ok_or_else(|| {
        HayesError::InvalidParameter("ell exceeds the host shift domain".to_owned())
    })?;
    check_limit("group_order", group_order, limits.max_group_order)?;
    let factors = principal_unit_factors(ell);
    let recovered_order = factors
        .iter()
        .try_fold(1_usize, |product, factor| product.checked_mul(factor.order));
    if recovered_order != Some(group_order) {
        return Err(HayesError::Invariant(
            "principal-unit factor orders do not recover 2^ell".to_owned(),
        ));
    }
    Ok(PrincipalUnitStructure {
        ell,
        group_order,
        factors,
    })
}

fn principal_unit_from_mixed_radix_index(
    mut index: usize,
    factors: &[PrincipalUnitFactor],
    ell: usize,
) -> Result<u64, HayesError> {
    let mut unit = 1_u64;
    for factor in factors {
        let mut coordinate = index % factor.order;
        index /= factor.order;
        let mut power = 1 | (1_u64 << factor.odd_degree);
        while coordinate != 0 {
            if coordinate & 1 != 0 {
                unit = unit_multiply(unit, power, ell);
            }
            coordinate >>= 1;
            if coordinate != 0 {
                power = unit_multiply(power, power, ell);
            }
        }
    }
    if index != 0 {
        return Err(HayesError::InvalidParameter(
            "principal-unit mixed-radix index is out of range".to_owned(),
        ));
    }
    Ok(unit)
}

fn principal_unit_index_table(
    ell: usize,
    limits: HayesLimits,
) -> Result<(Vec<PrincipalUnitFactor>, BTreeMap<u64, usize>), HayesError> {
    let structure = principal_unit_structure(ell, limits)?;
    let work = structure
        .group_order
        .checked_mul(ell.max(1))
        .ok_or_else(|| HayesError::InvalidParameter("Witt conversion work overflow".to_owned()))?;
    check_limit("witt_conversion_cells", work, limits.max_table_cells)?;
    let mut unit_to_index = BTreeMap::new();
    for index in 0..structure.group_order {
        let unit = principal_unit_from_mixed_radix_index(index, &structure.factors, ell)?;
        if unit_to_index.insert(unit, index).is_some() {
            return Err(HayesError::Invariant(
                "2-typical Witt coordinates are not injective".to_owned(),
            ));
        }
    }
    if unit_to_index.len() != structure.group_order {
        return Err(HayesError::Invariant(
            "2-typical Witt coordinates are incomplete".to_owned(),
        ));
    }
    Ok((structure.factors, unit_to_index))
}

/// Convert a packed binary principal unit to its truncated 2-typical Witt
/// blocks and reconstruct it as an invariant check.
///
/// # Errors
///
/// Rejects a non-unit, bits beyond the truncation, or a request exceeding the
/// explicit group/table limits.
pub fn binary_principal_unit_witt_report(
    unit: u64,
    ell: usize,
    limits: HayesLimits,
) -> Result<BinaryPrincipalUnitWittReport, HayesError> {
    if ell == 0 || ell > 63 {
        return Err(HayesError::InvalidParameter(
            "Witt conversion requires 1<=ell<=63".to_owned(),
        ));
    }
    check_limit("ell", ell, limits.max_ell)?;
    let mask = if ell == 63 {
        u64::MAX
    } else {
        (1_u64 << (ell + 1)) - 1
    };
    if unit & 1 == 0 || unit & !mask != 0 {
        return Err(HayesError::InvalidParameter(
            "Witt conversion requires a packed constant-one truncated unit".to_owned(),
        ));
    }
    let (factors, unit_to_index) = principal_unit_index_table(ell, limits)?;
    let mixed_radix_index = *unit_to_index.get(&unit).ok_or_else(|| {
        HayesError::Invariant("principal unit has no 2-typical Witt coordinates".to_owned())
    })?;
    let mut quotient = mixed_radix_index;
    let mut blocks = Vec::with_capacity(factors.len());
    for factor in &factors {
        let coordinate = quotient % factor.order;
        quotient /= factor.order;
        let length = factor.order.trailing_zeros() as usize;
        let active_slot_degrees = (0..length)
            .filter(|&slot| coordinate >> slot & 1 != 0)
            .map(|slot| factor.odd_degree << slot)
            .collect::<Vec<_>>();
        let highest_active_slot = active_slot_degrees.last().copied();
        blocks.push(BinaryWittBlockCoordinate {
            odd_degree: factor.odd_degree,
            length,
            coordinate,
            active_slot_degrees,
            highest_active_slot,
        });
    }
    if quotient != 0
        || principal_unit_from_mixed_radix_index(mixed_radix_index, &factors, ell)? != unit
    {
        return Err(HayesError::Invariant(
            "2-typical Witt coordinate roundtrip failed".to_owned(),
        ));
    }
    Ok(BinaryPrincipalUnitWittReport {
        ell,
        unit,
        mixed_radix_index,
        blocks,
    })
}

/// Compute the exact source, image, and kernel sizes of the maximal
/// elementary-abelian quotient of the 2-typical Witt blocks.
///
/// Each cyclic factor has power-of-two order `2^L`.  Reduction of its
/// coordinate modulo two is a surjective homomorphism to `GF(2)`, with kernel
/// order `2^(L-1)`.  The product map therefore has one target bit for every
/// odd degree at most `ell` and kernel dimension
/// `sum(L-1)=ell-ceil(ell/2)=floor(ell/2)`.  Conversely, every homomorphism
/// to a binary vector space kills doubles.  On each cyclic block its image
/// therefore has rank at most one, so this first-slot map realizes
/// `E_ell/2E_ell` and has the smallest kernel possible for any elementary-
/// abelian target.
///
/// # Errors
///
/// Rejects an invalid or over-limit truncation and fails closed if the native
/// factorization does not have the required power-of-two block structure or
/// if the independently accumulated source/image/kernel orders disagree.
pub fn binary_witt_first_slot_projection_report(
    ell: usize,
    limits: HayesLimits,
) -> Result<BinaryWittFirstSlotProjectionReport, HayesError> {
    let structure = principal_unit_structure(ell, limits)?;
    let mut first_slot_degrees = Vec::with_capacity(structure.factors.len());
    let mut block_lengths = Vec::with_capacity(structure.factors.len());
    let mut image_order = 1_usize;
    let mut kernel_order = 1_usize;
    let mut kernel_dimension = 0_usize;

    for factor in &structure.factors {
        if !factor.order.is_power_of_two() || factor.order < 2 {
            return Err(HayesError::Invariant(
                "first-slot projection requires nontrivial binary Witt blocks".to_owned(),
            ));
        }
        let length = factor.order.trailing_zeros() as usize;
        first_slot_degrees.push(factor.odd_degree);
        block_lengths.push(length);
        image_order = image_order.checked_mul(2).ok_or_else(|| {
            HayesError::InvalidParameter("first-slot image order overflow".to_owned())
        })?;
        kernel_order = kernel_order.checked_mul(factor.order / 2).ok_or_else(|| {
            HayesError::InvalidParameter("first-slot kernel order overflow".to_owned())
        })?;
        kernel_dimension = kernel_dimension.checked_add(length - 1).ok_or_else(|| {
            HayesError::InvalidParameter("first-slot kernel dimension overflow".to_owned())
        })?;
    }

    let kernel_shift = u32::try_from(kernel_dimension).map_err(|_| {
        HayesError::InvalidParameter("first-slot kernel dimension exceeds u32".to_owned())
    })?;
    if image_order.checked_mul(kernel_order) != Some(structure.group_order)
        || first_slot_degrees.len() != ell.div_ceil(2)
        || kernel_dimension != ell / 2
        || kernel_order != 1_usize.checked_shl(kernel_shift).unwrap_or(0)
    {
        return Err(HayesError::Invariant(
            "first-slot source/image/kernel ledger is inconsistent".to_owned(),
        ));
    }

    Ok(BinaryWittFirstSlotProjectionReport {
        ell,
        first_slot_degrees,
        block_lengths,
        source_order: structure.group_order,
        image_order,
        maximal_elementary_quotient_rank: ell.div_ceil(2),
        kernel_order,
        kernel_dimension,
        minimum_elementary_kernel_dimension: ell / 2,
    })
}

/// Bound every binary wild Kloosterman sum at principal-unit level `ell`.
///
/// Write `m=ell+1`, `c=ceil(m/3)`, and `s=ceil((m-1)/3)`.  On a coset modulo
/// `x^c`, the phase `u^-1 + z u` is an affine additive character: in
/// characteristic two the first non-zero mixed term in the second difference
/// of `u^-1` has total degree three, and `3c>=m`.  Hence each coset contributes
/// either zero or its full size `2^(m-c)`.
///
/// If two cosets contribute and their representatives first differ in degree
/// `d<s`, take a variation of degree `m-1-2d`.  The leading mixed term in the
/// second difference is then the non-zero top coefficient of `z^2 y`; every
/// other term has larger valuation.  This contradicts stationarity.  Thus all
/// contributing cosets agree modulo `x^s`, so there are at most `2^(c-s)` of
/// them and
///
/// ```text
/// |K_2(z)| <= 2^(c-s) 2^(m-c) = 2^(m-s).
/// ```
///
/// Orthogonality for `V_(ell-1)^2` gives
/// `r(e)-2^(ell-2)=(+/-)K_2(z(e))/4`, yielding the final report field.
///
/// # Errors
///
/// Rejects `ell<2`, host-width overflow, or a caller limit before allocating
/// any transform table.
pub fn principal_unit_kloosterman_bound(
    ell: usize,
    limits: HayesLimits,
) -> Result<PrincipalUnitKloostermanBoundReport, HayesError> {
    if ell < 2 {
        return Err(HayesError::InvalidParameter(
            "principal-unit Kloosterman bounds require ell at least two".to_owned(),
        ));
    }
    let _structure = principal_unit_structure(ell, limits)?;
    let modulus_exponent = ell.checked_add(1).ok_or_else(|| {
        HayesError::InvalidParameter("Kloosterman modulus exponent overflow".to_owned())
    })?;
    let affine_coset_precision = modulus_exponent.div_ceil(3);
    let stationary_congruence_precision = ell.div_ceil(3);
    let contributing_exponent = affine_coset_precision
        .checked_sub(stationary_congruence_precision)
        .ok_or_else(|| {
            HayesError::Invariant(
                "Kloosterman stationary precision exceeds affine precision".to_owned(),
            )
        })?;
    let kloosterman_exponent = modulus_exponent
        .checked_sub(stationary_congruence_precision)
        .ok_or_else(|| {
            HayesError::Invariant(
                "Kloosterman stationary precision exceeds modulus exponent".to_owned(),
            )
        })?;
    let deviation_exponent = kloosterman_exponent.checked_sub(2).ok_or_else(|| {
        HayesError::Invariant("Kloosterman product-deviation exponent underflow".to_owned())
    })?;
    Ok(PrincipalUnitKloostermanBoundReport {
        ell,
        modulus_exponent,
        affine_coset_precision,
        stationary_congruence_precision,
        max_contributing_cosets: BigUint::from(1_u8) << contributing_exponent,
        max_abs_kloosterman_sum: BigUint::from(1_u8) << kloosterman_exponent,
        max_abs_top_product_deviation: BigUint::from(1_u8) << deviation_exponent,
    })
}

/// Compute the exact additive energy of `V_d^(-1)` modulo `x^(ell+1)`.
///
/// The inverse interval is embedded in the additive coefficient group by
/// deleting its constant coefficient.  An integral Walsh transform gives
///
/// ```text
/// sum_a |sum_(u in V_d) (-1)^<a,u^(-1)-1>|^4
///   = 2^ell E_add(V_d^(-1)).
/// ```
///
/// This is the exact `q=2`, prime-power-modulus diagnostic required by the
/// characteristic-free Hölder step in bilinear inverse-sum arguments.  It is
/// not the multiplicative product energy returned by
/// [`principal_unit_product_energy`].
///
/// # Errors
///
/// Rejects a zero interval degree, a degree at least `ell`, a caller resource
/// limit, or a failed inversion, transform, or Parseval invariant.
pub fn principal_unit_inverse_additive_energy(
    ell: usize,
    interval_degree: usize,
    limits: HayesLimits,
) -> Result<PrincipalUnitInverseAdditiveEnergyReport, HayesError> {
    if interval_degree == 0 || interval_degree >= ell {
        return Err(HayesError::InvalidParameter(format!(
            "inverse-additive energy requires 1<=degree<ell, got degree={interval_degree}, ell={ell}"
        )));
    }
    admit_any_positive_degree(ell, interval_degree, limits)?;
    let group_order = 1_usize << ell;
    let mut indicator = vec![0_i128; group_order];
    for tail in 0..1_u64 << interval_degree {
        let unit = 1 | (tail << 1);
        let inverse = principal_unit_inverse(unit, ell);
        let packed = usize::try_from(inverse >> 1).map_err(|_| {
            HayesError::InvalidParameter("packed inverse unit does not fit usize".to_owned())
        })?;
        if packed >= group_order || indicator[packed] != 0 {
            return Err(HayesError::Invariant(
                "inverse interval is not embedded injectively in additive coordinates".to_owned(),
            ));
        }
        indicator[packed] = 1;
    }
    checked_walsh_transform(&mut indicator)?;
    let maximum_walsh_amplitude = indicator
        .iter()
        .map(|value| value.unsigned_abs())
        .max()
        .ok_or_else(|| HayesError::Invariant("inverse Walsh spectrum is empty".to_owned()))?;
    let fourth_walsh_moment = indicator.iter().fold(BigUint::from(0_u8), |sum, value| {
        let magnitude = BigUint::from(value.unsigned_abs());
        sum + magnitude.pow(4)
    });
    let group_order_big = BigUint::from(group_order);
    if &fourth_walsh_moment % &group_order_big != BigUint::from(0_u8) {
        return Err(HayesError::Invariant(
            "inverse Walsh fourth moment is not divisible by the group order".to_owned(),
        ));
    }
    let additive_energy = &fourth_walsh_moment / &group_order_big;
    let set_size = BigUint::from(1_u8) << interval_degree;
    let polynomial_degree_cutoff = interval_degree.checked_add(1).ok_or_else(|| {
        HayesError::InvalidParameter("inverse-energy polynomial cutoff overflow".to_owned())
    })?;
    Ok(PrincipalUnitInverseAdditiveEnergyReport {
        ell,
        interval_degree,
        polynomial_degree_cutoff,
        set_size,
        additive_energy,
        fourth_walsh_moment,
        maximum_walsh_amplitude,
    })
}

/// Compute the stable inverse-additive energy by exact rational reduction.
///
/// This is an algebraically independent route from
/// [`principal_unit_inverse_additive_energy`].  It never constructs truncated
/// inverses or a Walsh transform.  Instead, for every ordered pair in
/// `V_d^2`, it reduces `(A+B)/(AB)` by the binary-polynomial gcd and counts
/// equal reduced fractions.  The resulting sum of squared multiplicities is
/// the inverse-additive energy for every `ell>=3d`.
///
/// # Errors
///
/// Rejects `d=0`, a packed-polynomial degree beyond the `u64` representation,
/// a caller degree/pair-count limit, or a failed exact polynomial division.
pub fn principal_unit_inverse_additive_energy_no_wrap(
    interval_degree: usize,
    limits: HayesLimits,
) -> Result<PrincipalUnitInverseAdditiveNoWrapReport, HayesError> {
    if interval_degree == 0 {
        return Err(HayesError::InvalidParameter(
            "no-wrap inverse-additive energy requires a positive degree".to_owned(),
        ));
    }
    check_limit("degree", interval_degree, limits.max_degree)?;
    if interval_degree > 31 {
        return Err(HayesError::InvalidParameter(format!(
            "no-wrap packed polynomial degree {interval_degree} exceeds 31"
        )));
    }
    let pair_exponent = interval_degree.checked_mul(2).ok_or_else(|| {
        HayesError::InvalidParameter("no-wrap pair-count exponent overflow".to_owned())
    })?;
    let pair_count = 1_usize
        .checked_shl(u32::try_from(pair_exponent).map_err(|_| {
            HayesError::InvalidParameter("no-wrap pair-count shift overflow".to_owned())
        })?)
        .ok_or_else(|| {
            HayesError::InvalidParameter("no-wrap pair count exceeds the host width".to_owned())
        })?;
    check_limit("table_cells", pair_count, limits.max_table_cells)?;
    let minimum_stable_ell = interval_degree
        .checked_mul(3)
        .ok_or_else(|| HayesError::InvalidParameter("no-wrap degree bound overflow".to_owned()))?;

    let set_size = 1_u64 << interval_degree;
    let mut fractions = BTreeMap::<(u64, u64), u128>::new();
    for left_tail in 0..set_size {
        let left = 1 | (left_tail << 1);
        for right_tail in 0..set_size {
            let right = 1 | (right_tail << 1);
            let numerator = left ^ right;
            let denominator = polynomial_multiply_packed(left, right);
            let common = polynomial_gcd_packed(numerator, denominator);
            let reduced_numerator = polynomial_exact_divide_packed(numerator, common)?;
            let reduced_denominator = polynomial_exact_divide_packed(denominator, common)?;
            *fractions
                .entry((reduced_numerator, reduced_denominator))
                .or_default() += 1;
        }
    }
    let maximum_fraction_multiplicity = fractions.values().copied().max().ok_or_else(|| {
        HayesError::Invariant("no-wrap rational-function table is empty".to_owned())
    })?;
    let additive_energy = fractions.values().fold(BigUint::from(0_u8), |sum, count| {
        sum + BigUint::from(*count).pow(2)
    });
    Ok(PrincipalUnitInverseAdditiveNoWrapReport {
        interval_degree,
        minimum_stable_ell,
        ordered_pair_count: BigUint::from(1_u8) << pair_exponent,
        reduced_fraction_count: fractions.len(),
        maximum_fraction_multiplicity,
        additive_energy,
    })
}

/// Prove an explicit `2^(2d+o(d))` upper bound in the no-wrap regime.
///
/// Write `A=ga` and `B=gb` with `(a,b)=1`, and put `h=(g,a+b)`.  Exact
/// reduction gives
///
/// ```text
/// (A+B)/(AB) = ((a+b)/h) / ((g/h)ab).
/// ```
///
/// For a fixed reduced fraction `p/q`, choosing a preimage therefore chooses
/// an ordered factorization `q=cab`; after that, `h=(a+b)/p` and `g=hc` are
/// forced.  The collision multiplicity is at most `tau_3(q)`.  Moreover,
/// `deg q<=2d` because `deg g+max(deg a,deg b)<=d`.
///
/// To bound `tau_3`, split irreducible factors at degree `R`.  There are fewer
/// than `2^(R+1)` low-degree irreducibles, and each has at most
/// `(2d+1)^2` exponent allocations among three factors.  The high-degree
/// factors have total multiplicity at most `floor(2d/(R+1))`, and
/// `binomial(e+2,2)<=3^e`.  Multiplying this maximum multiplicity by the
/// `2^(2d)` ordered pairs proves the returned energy bound.
///
/// # Errors
///
/// Rejects `d=0`, a caller degree limit, or checked-arithmetic overflow.
pub fn principal_unit_inverse_additive_energy_no_wrap_bound(
    interval_degree: usize,
    limits: HayesLimits,
) -> Result<PrincipalUnitInverseAdditiveNoWrapBoundReport, HayesError> {
    if interval_degree == 0 {
        return Err(HayesError::InvalidParameter(
            "no-wrap inverse-energy bound requires a positive degree".to_owned(),
        ));
    }
    check_limit("degree", interval_degree, limits.max_degree)?;
    let twice_degree = interval_degree.checked_mul(2).ok_or_else(|| {
        HayesError::InvalidParameter("no-wrap divisor degree overflow".to_owned())
    })?;
    let minimum_stable_ell = interval_degree
        .checked_mul(3)
        .ok_or_else(|| HayesError::InvalidParameter("no-wrap stable level overflow".to_owned()))?;
    let floor_log_two = usize::BITS as usize - 1 - interval_degree.leading_zeros() as usize;
    let split_degree = (floor_log_two / 2).max(1);
    let low_allocation_exponent = 1_usize
        .checked_shl(u32::try_from(split_degree + 2).map_err(|_| {
            HayesError::InvalidParameter("low-factor exponent shift overflow".to_owned())
        })?)
        .ok_or_else(|| {
            HayesError::InvalidParameter("low-factor exponent exceeds host width".to_owned())
        })?;
    let low_allocation_exponent = u32::try_from(low_allocation_exponent).map_err(|_| {
        HayesError::InvalidParameter("low-factor exponent exceeds BigUint::pow".to_owned())
    })?;
    let high_factor_count = twice_degree / (split_degree + 1);
    let high_factor_count = u32::try_from(high_factor_count).map_err(|_| {
        HayesError::InvalidParameter("high-factor exponent exceeds BigUint::pow".to_owned())
    })?;
    let base = twice_degree.checked_add(1).ok_or_else(|| {
        HayesError::InvalidParameter("low-factor allocation base overflow".to_owned())
    })?;
    let maximum_multiplicity_bound = BigUint::from(base).pow(low_allocation_exponent)
        * BigUint::from(3_u8).pow(high_factor_count);
    let additive_energy_bound = &maximum_multiplicity_bound << twice_degree;
    Ok(PrincipalUnitInverseAdditiveNoWrapBoundReport {
        interval_degree,
        minimum_stable_ell,
        split_degree,
        maximum_multiplicity_bound,
        additive_energy_bound,
    })
}

fn binary_irreducible_counts_through(degree: usize) -> Result<Vec<BigUint>, HayesError> {
    let mut counts = vec![BigUint::from(0_u8); degree + 1];
    for current in 1..=degree {
        let mut numerator = BigUint::from(1_u8) << current;
        for (divisor, count) in counts.iter().enumerate().take(current).skip(1) {
            if current.is_multiple_of(divisor) {
                numerator -= BigUint::from(divisor) * count;
            }
        }
        let divisor = BigUint::from(current);
        if &numerator % &divisor != BigUint::from(0_u8) {
            return Err(HayesError::Invariant(
                "binary irreducible-count recurrence is not integral".to_owned(),
            ));
        }
        counts[current] = numerator / divisor;
    }
    Ok(counts)
}

fn balanced_factor_exponent_product(
    total_exponent: usize,
    factors: usize,
) -> Result<BigUint, HayesError> {
    debug_assert!(factors > 0 && factors <= total_exponent);
    let quotient = total_exponent / factors;
    let remainder = total_exponent % factors;
    let high_exponent = u32::try_from(remainder).map_err(|_| {
        HayesError::InvalidParameter("balanced divisor exponent exceeds u32".to_owned())
    })?;
    let low_exponent = u32::try_from(factors - remainder).map_err(|_| {
        HayesError::InvalidParameter("balanced divisor exponent exceeds u32".to_owned())
    })?;
    Ok(BigUint::from(quotient + 2).pow(high_exponent)
        * BigUint::from(quotient + 1).pow(low_exponent))
}

/// Exact maximum of the monic-divisor count over nonzero binary polynomials
/// of degree at most `degree`.
///
/// If `Q=prod_P P^e_P`, then `tau(Q)=prod_P(e_P+1)`.  For each irreducible
/// degree `j`, the recurrence `2^j=sum_(d|j)d I_d` supplies the exact number
/// `I_j` of available factors.  At fixed total exponent and factor count the
/// product is maximized by balanced exponents, after which a degree-knapsack
/// combines the independent `j`-blocks.  Thus this is an exact optimization,
/// not an asymptotic divisor estimate.
fn compute_binary_polynomial_divisor_envelopes(degree: usize) -> Result<Vec<BigUint>, HayesError> {
    let irreducible_counts = binary_irreducible_counts_through(degree)?;
    let mut maximum_by_degree = vec![None::<BigUint>; degree + 1];
    maximum_by_degree[0] = Some(BigUint::from(1_u8));
    for (factor_degree, irreducible_count) in irreducible_counts
        .iter()
        .enumerate()
        .take(degree + 1)
        .skip(1)
    {
        let maximum_total_exponent = degree / factor_degree;
        let cap = BigUint::from(maximum_total_exponent);
        let available = if irreducible_count >= &cap {
            maximum_total_exponent
        } else {
            usize::try_from(irreducible_count.clone()).map_err(|_| {
                HayesError::InvalidParameter("irreducible count exceeds usize".to_owned())
            })?
        };
        let mut local = vec![BigUint::from(0_u8); maximum_total_exponent + 1];
        local[0] = BigUint::from(1_u8);
        for (total_exponent, maximum) in local.iter_mut().enumerate().skip(1) {
            for factors in 1..=available.min(total_exponent) {
                let candidate = balanced_factor_exponent_product(total_exponent, factors)?;
                if candidate > *maximum {
                    *maximum = candidate;
                }
            }
        }
        let previous = maximum_by_degree;
        maximum_by_degree = vec![None::<BigUint>; degree + 1];
        for (used, current) in previous.into_iter().enumerate() {
            let Some(current) = current else {
                continue;
            };
            for (total_exponent, local_bound) in local.iter().enumerate() {
                let added = factor_degree.checked_mul(total_exponent).ok_or_else(|| {
                    HayesError::InvalidParameter("divisor knapsack degree overflow".to_owned())
                })?;
                let Some(target) = used.checked_add(added).filter(|&value| value <= degree) else {
                    continue;
                };
                let candidate = &current * local_bound;
                if maximum_by_degree[target]
                    .as_ref()
                    .is_none_or(|best| candidate > *best)
                {
                    maximum_by_degree[target] = Some(candidate);
                }
            }
        }
    }
    let mut prefix_maximum = Vec::with_capacity(degree + 1);
    let mut maximum = BigUint::from(0_u8);
    for value in maximum_by_degree {
        if let Some(value) = value {
            maximum = maximum.max(value);
        }
        prefix_maximum.push(maximum.clone());
    }
    if prefix_maximum.first() != Some(&BigUint::from(1_u8)) {
        return Err(HayesError::Invariant(
            "divisor knapsack lost its zero state".to_owned(),
        ));
    }
    Ok(prefix_maximum)
}

static BINARY_POLYNOMIAL_DIVISOR_ENVELOPES: OnceLock<Mutex<Vec<BigUint>>> = OnceLock::new();

fn binary_polynomial_divisor_envelope(degree: usize) -> Result<BigUint, HayesError> {
    let cache =
        BINARY_POLYNOMIAL_DIVISOR_ENVELOPES.get_or_init(|| Mutex::new(vec![BigUint::from(1_u8)]));
    {
        let values = cache.lock().map_err(|_| {
            HayesError::Invariant("binary divisor-envelope cache is poisoned".to_owned())
        })?;
        if let Some(value) = values.get(degree) {
            return Ok(value.clone());
        }
    }
    let computed = compute_binary_polynomial_divisor_envelopes(degree)?;
    let value = computed[degree].clone();
    let mut values = cache.lock().map_err(|_| {
        HayesError::Invariant("binary divisor-envelope cache is poisoned".to_owned())
    })?;
    if computed.len() > values.len() {
        *values = computed;
    }
    Ok(value)
}

/// Prove an explicit inverse-additive-energy bound for the wrapped binary
/// prime-power modulus `x^r`.
///
/// For a nonzero inverse sum `a`, put `s=v_x(a)`.  Linear algebra supplies
/// nonzero polynomials `u,v` with
///
/// ```text
/// au=v (mod x^r),  deg u<=k,  deg v<=r-k-1,
/// k=min(r-s-1,ceil((r+m)/2)).
/// ```
///
/// Clearing denominators and lifting the congruence gives
///
/// ```text
/// (vA+u)(vB+u)=u^2+t v x^r.
/// ```
///
/// The right side is nonzero for `x^r`: if `h=v_x(u)`, then
/// `h<r-s`, while its two summands have distinct valuations `2h` and at
/// least `r+s+h`.  Thus every solution injects into an ordered polynomial
/// factorization.  The report bounds lift choices and factorization counts
/// explicitly and sums them against the exact population of every valuation
/// stratum.  No odd-characteristic estimate or hidden `epsilon` is used.
///
/// # Errors
///
/// Rejects `r=0`, `m=0`, `m>r`, a caller degree limit, or arithmetic
/// overflow.
pub fn binary_prime_power_inverse_additive_energy_bound(
    modulus_degree: usize,
    polynomial_degree_cutoff: usize,
    limits: HayesLimits,
) -> Result<BinaryPrimePowerInverseEnergyBoundReport, HayesError> {
    if modulus_degree == 0
        || polynomial_degree_cutoff == 0
        || polynomial_degree_cutoff > modulus_degree
    {
        return Err(HayesError::InvalidParameter(format!(
            "binary prime-power inverse energy requires 1<=m<=r, got m={polynomial_degree_cutoff}, r={modulus_degree}"
        )));
    }
    check_limit("degree", modulus_degree, limits.max_degree)?;
    let interval_exponent = polynomial_degree_cutoff - 1;
    let set_size = BigUint::from(1_u8) << interval_exponent;
    let diagonal_energy = &set_size * &set_size;
    let approximation_midpoint = modulus_degree
        .checked_add(polynomial_degree_cutoff)
        .ok_or_else(|| HayesError::InvalidParameter("energy midpoint overflow".to_owned()))?
        .div_ceil(2);
    let twice_cutoff = polynomial_degree_cutoff.checked_mul(2).ok_or_else(|| {
        HayesError::InvalidParameter("energy cutoff exponent overflow".to_owned())
    })?;
    let mut strata = Vec::with_capacity(interval_exponent);
    let mut additive_energy_bound = diagonal_energy.clone();
    for valuation in 1..polynomial_degree_cutoff {
        let approximation_degree = (modulus_degree - valuation - 1).min(approximation_midpoint);
        let lift_from_linear = approximation_degree
            .checked_add(polynomial_degree_cutoff)
            .ok_or_else(|| HayesError::InvalidParameter("lift degree overflow".to_owned()))?
            .saturating_sub(modulus_degree);
        let lift_from_quadratic =
            twice_cutoff.saturating_sub(approximation_degree.checked_add(2).ok_or_else(|| {
                HayesError::InvalidParameter("quadratic lift degree overflow".to_owned())
            })?);
        let lift_choice_exponent = lift_from_linear.max(lift_from_quadratic);
        let factor_linear_degree = modulus_degree
            .checked_sub(approximation_degree)
            .and_then(|value| value.checked_add(polynomial_degree_cutoff))
            .and_then(|value| value.checked_sub(2))
            .ok_or_else(|| {
                HayesError::InvalidParameter("factor linear degree overflow".to_owned())
            })?;
        let factor_degree = approximation_degree.max(factor_linear_degree);
        let factor_polynomial_degree_bound = factor_degree.checked_mul(2).ok_or_else(|| {
            HayesError::InvalidParameter("factor polynomial degree overflow".to_owned())
        })?;
        let divisor_cells = factor_polynomial_degree_bound
            .checked_add(1)
            .and_then(|value| value.checked_mul(value))
            .ok_or_else(|| {
                HayesError::InvalidParameter("divisor-envelope work estimate overflow".to_owned())
            })?;
        check_limit("table_cells", divisor_cells, limits.max_table_cells)?;
        let factorization_count_bound =
            binary_polynomial_divisor_envelope(factor_polynomial_degree_bound)?;
        let pair_exponent = twice_cutoff
            .checked_sub(valuation)
            .and_then(|value| value.checked_sub(2))
            .ok_or_else(|| HayesError::Invariant("valuation pair exponent underflow".to_owned()))?;
        let ordered_pair_count = BigUint::from(1_u8) << pair_exponent;
        let fibre_bound = &factorization_count_bound << lift_choice_exponent;
        let energy_contribution_bound = &ordered_pair_count * fibre_bound;
        additive_energy_bound += &energy_contribution_bound;
        strata.push(BinaryPrimePowerInverseEnergyStratum {
            valuation,
            approximation_degree,
            lift_choice_exponent,
            factor_polynomial_degree_bound,
            factorization_count_bound,
            ordered_pair_count,
            energy_contribution_bound,
        });
    }
    Ok(BinaryPrimePowerInverseEnergyBoundReport {
        modulus_degree,
        polynomial_degree_cutoff,
        set_size,
        diagonal_energy,
        strata,
        additive_energy_bound,
    })
}

/// Substitute arbitrary rational energy exponents into the `k=2` bilinear
/// Hölder bound and compare the result with an integer target exponent.
///
/// # Errors
///
/// Rejects a zero denominator or checked-arithmetic overflow.
pub fn binary_bilinear_energy_exponent(
    left_interval_exponent: usize,
    right_interval_exponent: usize,
    modulus_degree: usize,
    left_energy_exponent_numerator: usize,
    right_energy_exponent_numerator: usize,
    energy_exponent_denominator: usize,
    target_exponent: usize,
) -> Result<BinaryBilinearEnergyExponentReport, HayesError> {
    if energy_exponent_denominator == 0 {
        return Err(HayesError::InvalidParameter(
            "energy exponent denominator must be positive".to_owned(),
        ));
    }
    let left = u128::try_from(left_interval_exponent).map_err(|_| {
        HayesError::InvalidParameter("left interval exponent exceeds u128".to_owned())
    })?;
    let right = u128::try_from(right_interval_exponent).map_err(|_| {
        HayesError::InvalidParameter("right interval exponent exceeds u128".to_owned())
    })?;
    let modulus = u128::try_from(modulus_degree)
        .map_err(|_| HayesError::InvalidParameter("modulus degree exceeds u128".to_owned()))?;
    let denominator = u128::try_from(energy_exponent_denominator).map_err(|_| {
        HayesError::InvalidParameter("energy exponent denominator exceeds u128".to_owned())
    })?;
    let energy_sum = u128::try_from(left_energy_exponent_numerator)
        .ok()
        .and_then(|value| {
            u128::try_from(right_energy_exponent_numerator)
                .ok()
                .and_then(|right_value| value.checked_add(right_value))
        })
        .ok_or_else(|| HayesError::InvalidParameter("energy exponent sum overflow".to_owned()))?;
    // Over denominator 8D, the two interval main terms and the `-4m-4n`
    // normalization combine to `D(4m+4n+r)`.
    let normalized = left
        .checked_add(right)
        .and_then(|sum| sum.checked_mul(4))
        .and_then(|sum| sum.checked_add(modulus))
        .and_then(|sum| sum.checked_mul(denominator))
        .ok_or_else(|| {
            HayesError::InvalidParameter("bilinear normalized exponent overflow".to_owned())
        })?;
    let bound_exponent_numerator = normalized.checked_add(energy_sum).ok_or_else(|| {
        HayesError::InvalidParameter("bilinear bound exponent overflow".to_owned())
    })?;
    let target_exponent_numerator = u128::try_from(target_exponent)
        .ok()
        .and_then(|target| target.checked_mul(8))
        .and_then(|target| target.checked_mul(denominator))
        .ok_or_else(|| {
            HayesError::InvalidParameter("bilinear target exponent overflow".to_owned())
        })?;
    let deficit_numerator = if target_exponent_numerator >= bound_exponent_numerator {
        i128::try_from(target_exponent_numerator - bound_exponent_numerator).map_err(|_| {
            HayesError::InvalidParameter("bilinear exponent deficit exceeds i128".to_owned())
        })?
    } else {
        -i128::try_from(bound_exponent_numerator - target_exponent_numerator).map_err(|_| {
            HayesError::InvalidParameter("bilinear exponent deficit exceeds i128".to_owned())
        })?
    };
    Ok(BinaryBilinearEnergyExponentReport {
        left_interval_exponent,
        right_interval_exponent,
        modulus_degree,
        energy_exponent_denominator,
        bound_exponent_numerator,
        target_exponent_numerator,
        deficit_numerator,
        strict_saving: deficit_numerator > 0,
    })
}

/// Feed the explicit wrapped `GF(2)[x]/(x^r)` energy envelopes into the
/// `k=2` bilinear Hölder ledger and add a caller-selected analytic reserve.
///
/// # Errors
///
/// Rejects interval cutoffs larger than `r`, a zero loss denominator, caller
/// resource limits, or checked-arithmetic overflow.
pub fn binary_bilinear_explicit_prime_power_energy_exponent(
    left_interval_exponent: usize,
    right_interval_exponent: usize,
    modulus_degree: usize,
    analytic_loss_exponent_numerator: usize,
    analytic_loss_exponent_denominator: usize,
    target_exponent: usize,
    limits: HayesLimits,
) -> Result<BinaryBilinearExplicitEnergyExponentReport, HayesError> {
    if analytic_loss_exponent_denominator == 0 {
        return Err(HayesError::InvalidParameter(
            "analytic loss exponent denominator must be positive".to_owned(),
        ));
    }
    let left_cutoff = left_interval_exponent
        .checked_add(1)
        .ok_or_else(|| HayesError::InvalidParameter("left interval cutoff overflow".to_owned()))?;
    let right_cutoff = right_interval_exponent
        .checked_add(1)
        .ok_or_else(|| HayesError::InvalidParameter("right interval cutoff overflow".to_owned()))?;
    let left_energy =
        binary_prime_power_inverse_additive_energy_bound(modulus_degree, left_cutoff, limits)?;
    let right_energy =
        binary_prime_power_inverse_additive_energy_bound(modulus_degree, right_cutoff, limits)?;
    let left_energy_ceiling_exponent = left_energy.ceiling_energy_exponent().ok_or_else(|| {
        HayesError::InvalidParameter("left energy exponent exceeds usize".to_owned())
    })?;
    let right_energy_ceiling_exponent =
        right_energy.ceiling_energy_exponent().ok_or_else(|| {
            HayesError::InvalidParameter("right energy exponent exceeds usize".to_owned())
        })?;
    let base = binary_bilinear_energy_exponent(
        left_interval_exponent,
        right_interval_exponent,
        modulus_degree,
        left_energy_ceiling_exponent,
        right_energy_ceiling_exponent,
        1,
        target_exponent,
    )?;
    let loss_denominator = u128::try_from(analytic_loss_exponent_denominator).map_err(|_| {
        HayesError::InvalidParameter("analytic loss denominator exceeds u128".to_owned())
    })?;
    let loss_numerator = u128::try_from(analytic_loss_exponent_numerator).map_err(|_| {
        HayesError::InvalidParameter("analytic loss numerator exceeds u128".to_owned())
    })?;
    let bound_exponent_numerator = base
        .bound_exponent_numerator
        .checked_mul(loss_denominator)
        .and_then(|value| {
            loss_numerator
                .checked_mul(8)
                .and_then(|loss| value.checked_add(loss))
        })
        .ok_or_else(|| {
            HayesError::InvalidParameter("loss-aware bilinear bound overflow".to_owned())
        })?;
    let target_exponent_numerator = base
        .target_exponent_numerator
        .checked_mul(loss_denominator)
        .ok_or_else(|| {
            HayesError::InvalidParameter("loss-aware bilinear target overflow".to_owned())
        })?;
    let deficit_numerator = checked_exponent_deficit(
        target_exponent_numerator,
        bound_exponent_numerator,
        "loss-aware bilinear",
    )?;
    Ok(BinaryBilinearExplicitEnergyExponentReport {
        left_interval_exponent,
        right_interval_exponent,
        modulus_degree,
        left_energy_ceiling_exponent,
        right_energy_ceiling_exponent,
        analytic_loss_exponent_numerator,
        analytic_loss_exponent_denominator,
        bound_exponent_numerator,
        target_exponent_numerator,
        deficit_numerator,
        strict_saving: deficit_numerator > 0,
    })
}

fn binary_complete_kloosterman_exponent(
    effective_modulus_degree: usize,
) -> Result<usize, HayesError> {
    if effective_modulus_degree == 0 {
        return Err(HayesError::InvalidParameter(
            "effective modulus degree must be positive".to_owned(),
        ));
    }
    let stationary_precision = (effective_modulus_degree - 1).div_ceil(3);
    effective_modulus_degree
        .checked_sub(stationary_precision)
        .ok_or_else(|| {
            HayesError::Invariant(
                "stationary precision exceeds effective modulus degree".to_owned(),
            )
        })
}

fn checked_exponent_deficit(target: u128, bound: u128, context: &str) -> Result<i128, HayesError> {
    if target >= bound {
        i128::try_from(target - bound).map_err(|_| {
            HayesError::InvalidParameter(format!("{context} exponent deficit exceeds i128"))
        })
    } else {
        i128::try_from(bound - target)
            .map(|value| -value)
            .map_err(|_| {
                HayesError::InvalidParameter(format!("{context} exponent deficit exceeds i128"))
            })
    }
}

/// Audit Bagshaw Type-I Case 1 with the binary complete-sum exponent.
///
/// # Errors
///
/// Rejects zero degrees, an empty Case-1 range (`N<r0`), or arithmetic
/// overflow.
pub fn binary_type_one_case_one_exponent(
    mobius_degree_cutoff: usize,
    effective_modulus_degree: usize,
) -> Result<BinaryTypeOneCaseOneExponentReport, HayesError> {
    if mobius_degree_cutoff == 0
        || effective_modulus_degree == 0
        || mobius_degree_cutoff < effective_modulus_degree
    {
        return Err(HayesError::InvalidParameter(format!(
            "Type-I Case 1 requires N>=r0>=1, got N={mobius_degree_cutoff}, r0={effective_modulus_degree}"
        )));
    }
    let maximum_admissible_u = effective_modulus_degree
        .checked_sub(effective_modulus_degree.div_ceil(3))
        .ok_or_else(|| HayesError::Invariant("Case-1 range underflow".to_owned()))?
        .min(mobius_degree_cutoff - effective_modulus_degree);
    let complete_kloosterman_exponent =
        binary_complete_kloosterman_exponent(effective_modulus_degree)?;
    let bound_exponent = u128::try_from(mobius_degree_cutoff - effective_modulus_degree)
        .ok()
        .and_then(|value| {
            u128::try_from(complete_kloosterman_exponent)
                .ok()
                .and_then(|kappa| value.checked_add(kappa))
        })
        .ok_or_else(|| HayesError::InvalidParameter("Case-1 exponent exceeds u128".to_owned()))?;
    let trivial_exponent = u128::try_from(mobius_degree_cutoff)
        .map_err(|_| HayesError::InvalidParameter("Case-1 cutoff exceeds u128".to_owned()))?;
    let deficit = checked_exponent_deficit(trivial_exponent, bound_exponent, "Case-1")?;
    Ok(BinaryTypeOneCaseOneExponentReport {
        mobius_degree_cutoff,
        effective_modulus_degree,
        maximum_admissible_u,
        complete_kloosterman_exponent,
        bound_exponent,
        trivial_exponent,
        deficit,
        strict_saving: deficit > 0,
    })
}

/// Audit and exactly optimize Bagshaw Type-I Case 2 with the binary
/// complete-sum exponent.
///
/// # Errors
///
/// Rejects zero degrees, an empty integer Case-2 range, or arithmetic
/// overflow.
pub fn binary_type_one_case_two_exponent(
    mobius_degree_cutoff: usize,
    effective_modulus_degree: usize,
) -> Result<BinaryTypeOneCaseTwoExponentReport, HayesError> {
    if mobius_degree_cutoff == 0 || effective_modulus_degree == 0 {
        return Err(HayesError::InvalidParameter(format!(
            "Type-I Case 2 requires N,r0>=1, got N={mobius_degree_cutoff}, r0={effective_modulus_degree}"
        )));
    }
    let minimum_admissible_u = mobius_degree_cutoff.saturating_sub(effective_modulus_degree);
    let one_third_ceiling = effective_modulus_degree.div_ceil(3);
    let maximum_from_lower_y = mobius_degree_cutoff
        .checked_sub(one_third_ceiling)
        .ok_or_else(|| {
            HayesError::InvalidParameter(format!(
                "Type-I Case 2 has empty range for N={mobius_degree_cutoff}, r0={effective_modulus_degree}"
            ))
        })?;
    let maximum_admissible_u = (effective_modulus_degree / 3).min(maximum_from_lower_y);
    if minimum_admissible_u > maximum_admissible_u {
        return Err(HayesError::InvalidParameter(format!(
            "Type-I Case 2 has empty range for N={mobius_degree_cutoff}, r0={effective_modulus_degree}"
        )));
    }

    let complete_kloosterman_exponent =
        binary_complete_kloosterman_exponent(effective_modulus_degree)?;
    let cutoff = u128::try_from(mobius_degree_cutoff)
        .map_err(|_| HayesError::InvalidParameter("Case-2 cutoff exceeds u128".to_owned()))?;
    let modulus = u128::try_from(effective_modulus_degree)
        .map_err(|_| HayesError::InvalidParameter("Case-2 modulus exceeds u128".to_owned()))?;
    let kappa = u128::try_from(complete_kloosterman_exponent)
        .map_err(|_| HayesError::InvalidParameter("Case-2 kappa exceeds u128".to_owned()))?;
    let energy_base = cutoff
        .checked_mul(3)
        .and_then(|value| value.checked_add(modulus))
        .ok_or_else(|| {
            HayesError::InvalidParameter("Case-2 energy exponent overflow".to_owned())
        })?;
    let completion_base = kappa.checked_mul(4).ok_or_else(|| {
        HayesError::InvalidParameter("Case-2 completion exponent overflow".to_owned())
    })?;
    let intersection_numerator = energy_base.saturating_sub(completion_base);
    let lower = u128::try_from(minimum_admissible_u).map_err(|_| {
        HayesError::InvalidParameter("Case-2 lower endpoint exceeds u128".to_owned())
    })?;
    let upper = u128::try_from(maximum_admissible_u).map_err(|_| {
        HayesError::InvalidParameter("Case-2 upper endpoint exceeds u128".to_owned())
    })?;
    let floor_intersection = (intersection_numerator / 5).clamp(lower, upper);
    let ceil_intersection = intersection_numerator.div_ceil(5).clamp(lower, upper);
    let candidates = [lower, upper, floor_intersection, ceil_intersection];

    let mut best: Option<(u128, u128, u128)> = None;
    for candidate in candidates {
        let energy = energy_base.checked_sub(candidate).ok_or_else(|| {
            HayesError::Invariant("Case-2 candidate exceeds energy base".to_owned())
        })?;
        let completion = candidate
            .checked_mul(4)
            .and_then(|value| value.checked_add(completion_base))
            .ok_or_else(|| {
                HayesError::InvalidParameter("Case-2 completion exponent overflow".to_owned())
            })?;
        let combined = energy.min(completion);
        if best.is_none_or(|(best_u, _, best_combined)| {
            combined > best_combined || (combined == best_combined && candidate < best_u)
        }) {
            best = Some((candidate, energy, combined));
        }
    }
    let (worst_u, energy_bound_quarters, bound_exponent_quarters) = best.ok_or_else(|| {
        HayesError::Invariant("nonempty Case-2 range produced no candidates".to_owned())
    })?;
    let completion_bound_quarters = worst_u
        .checked_mul(4)
        .and_then(|value| value.checked_add(completion_base))
        .ok_or_else(|| {
            HayesError::InvalidParameter("Case-2 completion exponent overflow".to_owned())
        })?;
    let trivial_exponent_quarters = cutoff.checked_mul(4).ok_or_else(|| {
        HayesError::InvalidParameter("Case-2 trivial exponent overflow".to_owned())
    })?;
    let deficit_quarters =
        checked_exponent_deficit(trivial_exponent_quarters, bound_exponent_quarters, "Case-2")?;
    Ok(BinaryTypeOneCaseTwoExponentReport {
        mobius_degree_cutoff,
        effective_modulus_degree,
        minimum_admissible_u,
        maximum_admissible_u,
        worst_admissible_u: usize::try_from(worst_u).map_err(|_| {
            HayesError::Invariant("bounded Case-2 optimizer does not fit usize".to_owned())
        })?,
        complete_kloosterman_exponent,
        wrapped_energy_input_available: true,
        suppressed_energy_loss: true,
        energy_bound_quarters,
        completion_bound_quarters,
        bound_exponent_quarters,
        trivial_exponent_quarters,
        deficit_quarters,
        strict_saving: deficit_quarters > 0,
    })
}

/// Check the Type-I Case-5 exponent obtained from the binary complete-sum
/// estimate.
///
/// The case being audited has `n<=r0`.  A non-positive deficit proves that
/// this direct substitution supplies no strict power saving at that point.
///
/// # Errors
///
/// Rejects zero degrees, `n>r0`, or checked-arithmetic overflow.
pub fn binary_type_one_case_five_exponent(
    mobius_degree_cutoff: usize,
    effective_modulus_degree: usize,
) -> Result<BinaryTypeOneCaseFiveExponentReport, HayesError> {
    if mobius_degree_cutoff == 0
        || effective_modulus_degree == 0
        || mobius_degree_cutoff > effective_modulus_degree
    {
        return Err(HayesError::InvalidParameter(format!(
            "Type-I Case 5 requires 1<=n<=r0, got n={mobius_degree_cutoff}, r0={effective_modulus_degree}"
        )));
    }
    let complete_kloosterman_exponent =
        binary_complete_kloosterman_exponent(effective_modulus_degree)?;
    let n = u128::try_from(mobius_degree_cutoff).map_err(|_| {
        HayesError::InvalidParameter("Möbius degree cutoff does not fit u128".to_owned())
    })?;
    let kappa = u128::try_from(complete_kloosterman_exponent).map_err(|_| {
        HayesError::InvalidParameter("Kloosterman exponent does not fit u128".to_owned())
    })?;
    let bound_exponent_sixths = n
        .checked_mul(4)
        .and_then(|value| {
            kappa
                .checked_mul(3)
                .and_then(|term| value.checked_add(term))
        })
        .ok_or_else(|| HayesError::InvalidParameter("Type-I exponent overflow".to_owned()))?;
    let trivial_exponent_sixths = n.checked_mul(6).ok_or_else(|| {
        HayesError::InvalidParameter("Type-I trivial exponent overflow".to_owned())
    })?;
    let deficit_sixths = i128::try_from(trivial_exponent_sixths)
        .and_then(|target| i128::try_from(bound_exponent_sixths).map(|bound| target - bound))
        .map_err(|_| HayesError::InvalidParameter("Type-I deficit does not fit i128".to_owned()))?;
    Ok(BinaryTypeOneCaseFiveExponentReport {
        mobius_degree_cutoff,
        effective_modulus_degree,
        complete_kloosterman_exponent,
        bound_exponent_sixths,
        trivial_exponent_sixths,
        deficit_sixths,
        strict_saving: deficit_sixths > 0,
    })
}

/// Calibrate one Lemire convolution order against Bagshaw's published
/// zero-epsilon exponent pair.
///
/// This arithmetic report grants no characteristic-two theorem credit.  It
/// identifies which interval degrees would remain uncovered even if the
/// published odd-characteristic exponents were independently reproved over
/// `GF(2)` with no epsilon or constant loss.
///
/// # Errors
///
/// Rejects `ell<2`, a non-endpoint degree, `d=0`, `d>=ell`, or arithmetic
/// overflow.
pub fn endpoint_inverse_mobius_exponent_calibration(
    ell: usize,
    endpoint_degree: usize,
    interval_degree: usize,
) -> Result<EndpointInverseMobiusExponentCalibrationReport, HayesError> {
    if ell < 2 || interval_degree == 0 || interval_degree >= ell {
        return Err(HayesError::InvalidParameter(format!(
            "endpoint calibration requires ell>=2 and 1<=d<ell, got ell={ell}, d={interval_degree}"
        )));
    }
    let odd_endpoint = ell
        .checked_mul(2)
        .and_then(|value| value.checked_add(1))
        .ok_or_else(|| HayesError::InvalidParameter("odd endpoint degree overflow".to_owned()))?;
    let even_endpoint = odd_endpoint
        .checked_add(1)
        .ok_or_else(|| HayesError::InvalidParameter("even endpoint degree overflow".to_owned()))?;
    if endpoint_degree != odd_endpoint && endpoint_degree != even_endpoint {
        return Err(HayesError::InvalidParameter(format!(
            "endpoint degree must be {odd_endpoint} or {even_endpoint}, got {endpoint_degree}"
        )));
    }
    let exact_mobius_degree = endpoint_degree
        .checked_sub(interval_degree)
        .ok_or_else(|| HayesError::Invariant("interval degree exceeds endpoint".to_owned()))?;
    let cumulative_cutoff = exact_mobius_degree.checked_add(1).ok_or_else(|| {
        HayesError::InvalidParameter("cumulative Möbius cutoff overflow".to_owned())
    })?;
    let modulus_degree = ell
        .checked_add(1)
        .ok_or_else(|| HayesError::InvalidParameter("modulus degree overflow".to_owned()))?;
    let n = u128::try_from(cumulative_cutoff).map_err(|_| {
        HayesError::InvalidParameter("cumulative cutoff does not fit u128".to_owned())
    })?;
    let r = u128::try_from(modulus_degree)
        .map_err(|_| HayesError::InvalidParameter("modulus degree does not fit u128".to_owned()))?;
    let target = u128::try_from(ell)
        .map_err(|_| HayesError::InvalidParameter("ell does not fit u128".to_owned()))?;
    let fifteen_sixteenths_exponent_48ths = n.checked_mul(45).ok_or_else(|| {
        HayesError::InvalidParameter("15/16 calibration exponent overflow".to_owned())
    })?;
    let mixed_exponent_48ths = n
        .checked_mul(32)
        .and_then(|value| r.checked_mul(12).and_then(|term| value.checked_add(term)))
        .ok_or_else(|| {
            HayesError::InvalidParameter("mixed calibration exponent overflow".to_owned())
        })?;
    let bound_exponent_48ths = fifteen_sixteenths_exponent_48ths.max(mixed_exponent_48ths);
    let target_exponent_48ths = target.checked_mul(48).ok_or_else(|| {
        HayesError::InvalidParameter("endpoint target exponent overflow".to_owned())
    })?;
    let deficit_48ths = i128::try_from(target_exponent_48ths)
        .and_then(|target| i128::try_from(bound_exponent_48ths).map(|bound| target - bound))
        .map_err(|_| {
            HayesError::InvalidParameter(
                "endpoint calibration deficit does not fit i128".to_owned(),
            )
        })?;
    Ok(EndpointInverseMobiusExponentCalibrationReport {
        ell,
        endpoint_degree,
        interval_degree,
        exact_mobius_degree,
        cumulative_cutoff,
        cumulative_cutoff_exceeds_modulus: cumulative_cutoff > modulus_degree,
        fifteen_sixteenths_exponent_48ths,
        mixed_exponent_48ths,
        bound_exponent_48ths,
        target_exponent_48ths,
        deficit_48ths,
        strict_pointwise_closure: deficit_48ths > 0,
    })
}

struct EndpointVaughanAccumulator {
    rows: BTreeMap<EndpointVaughanCase, EndpointVaughanCaseRow>,
}

impl EndpointVaughanAccumulator {
    fn new() -> Self {
        Self {
            rows: EndpointVaughanCase::ALL
                .into_iter()
                .map(|case| {
                    (
                        case,
                        EndpointVaughanCaseRow {
                            case,
                            sample_count: 0,
                            worst_bound_sixteenths: None,
                            worst_effective_modulus_degree: None,
                            worst_split_degree: None,
                            worst_explicit_energy_bound_sixteenths: None,
                            worst_explicit_energy_effective_modulus_degree: None,
                            worst_explicit_energy_split_degree: None,
                        },
                    )
                })
                .collect(),
        }
    }

    fn record(
        &mut self,
        case: EndpointVaughanCase,
        bound: u128,
        explicit_energy_bound: u128,
        effective_modulus_degree: usize,
        split_degree: Option<usize>,
    ) -> Result<(), HayesError> {
        let row = self.rows.get_mut(&case).ok_or_else(|| {
            HayesError::Invariant("Vaughan case missing from row table".to_owned())
        })?;
        row.sample_count = row
            .sample_count
            .checked_add(1)
            .ok_or_else(|| HayesError::InvalidParameter("Vaughan row count overflow".to_owned()))?;
        if row
            .worst_bound_sixteenths
            .is_none_or(|current| bound > current)
        {
            row.worst_bound_sixteenths = Some(bound);
            row.worst_effective_modulus_degree = Some(effective_modulus_degree);
            row.worst_split_degree = split_degree;
        }
        if row
            .worst_explicit_energy_bound_sixteenths
            .is_none_or(|current| explicit_energy_bound > current)
        {
            row.worst_explicit_energy_bound_sixteenths = Some(explicit_energy_bound);
            row.worst_explicit_energy_effective_modulus_degree = Some(effective_modulus_degree);
            row.worst_explicit_energy_split_degree = split_degree;
        }
        Ok(())
    }

    fn into_rows(mut self) -> Result<Vec<EndpointVaughanCaseRow>, HayesError> {
        EndpointVaughanCase::ALL
            .into_iter()
            .map(|case| {
                self.rows.remove(&case).ok_or_else(|| {
                    HayesError::Invariant("Vaughan row disappeared after enumeration".to_owned())
                })
            })
            .collect()
    }
}

fn endpoint_explicit_energy_ceiling(
    effective_modulus_degree: usize,
    bagshaw_degree_cutoff: usize,
    limits: HayesLimits,
    cache: &mut BTreeMap<(usize, usize), usize>,
) -> Result<usize, HayesError> {
    if bagshaw_degree_cutoff == 0 {
        return Ok(0);
    }
    let key = (effective_modulus_degree, bagshaw_degree_cutoff);
    if let Some(&exponent) = cache.get(&key) {
        return Ok(exponent);
    }
    let report = binary_prime_power_inverse_additive_energy_bound(
        effective_modulus_degree,
        bagshaw_degree_cutoff,
        limits,
    )?;
    let exponent = report.ceiling_energy_exponent().ok_or_else(|| {
        HayesError::InvalidParameter("endpoint energy ceiling exceeds usize".to_owned())
    })?;
    cache.insert(key, exponent);
    Ok(exponent)
}

fn endpoint_type_one_case_bound(
    cutoff: usize,
    effective_modulus_degree: usize,
    split: usize,
    kappa: usize,
    limits: HayesLimits,
    energy_cache: &mut BTreeMap<(usize, usize), usize>,
) -> Result<(EndpointVaughanCase, u128, u128), HayesError> {
    let inner = cutoff
        .checked_sub(split)
        .ok_or_else(|| HayesError::Invariant("Type-I split exceeds cutoff".to_owned()))?;
    let n = u128::try_from(cutoff)
        .map_err(|_| HayesError::InvalidParameter("Type-I cutoff exceeds u128".to_owned()))?;
    let r0 = u128::try_from(effective_modulus_degree).map_err(|_| {
        HayesError::InvalidParameter("Type-I effective modulus exceeds u128".to_owned())
    })?;
    let u = u128::try_from(split)
        .map_err(|_| HayesError::InvalidParameter("Type-I split exceeds u128".to_owned()))?;
    let kappa = u128::try_from(kappa)
        .map_err(|_| HayesError::InvalidParameter("Type-I kappa exceeds u128".to_owned()))?;
    if inner >= effective_modulus_degree {
        let bound = n
            .checked_sub(r0)
            .and_then(|value| value.checked_add(kappa))
            .and_then(|value| value.checked_mul(16))
            .ok_or_else(|| HayesError::InvalidParameter("Case-1 exponent overflow".to_owned()))?;
        return Ok((EndpointVaughanCase::TypeOneCaseOne, bound, bound));
    }
    let inner = u128::try_from(inner)
        .map_err(|_| HayesError::InvalidParameter("Type-I inner exceeds u128".to_owned()))?;
    if u.checked_mul(3).is_some_and(|value| value <= r0) {
        if inner.checked_mul(3).is_none_or(|value| value < r0) {
            return Err(HayesError::Invariant(
                "Type-I Case 2 violates its lower inner endpoint".to_owned(),
            ));
        }
        let energy = n
            .checked_mul(3)
            .and_then(|value| value.checked_add(r0))
            .and_then(|value| value.checked_sub(u))
            .and_then(|value| value.checked_mul(4))
            .ok_or_else(|| HayesError::InvalidParameter("Case-2 energy overflow".to_owned()))?;
        let completion = u
            .checked_add(kappa)
            .and_then(|value| value.checked_mul(16))
            .ok_or_else(|| HayesError::InvalidParameter("Case-2 completion overflow".to_owned()))?;
        let explicit_energy_exponent = u128::try_from(endpoint_explicit_energy_ceiling(
            effective_modulus_degree,
            split,
            limits,
            energy_cache,
        )?)
        .map_err(|_| {
            HayesError::InvalidParameter("Case-2 energy ceiling exceeds u128".to_owned())
        })?;
        let explicit_energy = n
            .checked_mul(3)
            .and_then(|value| u.checked_mul(3).and_then(|term| value.checked_sub(term)))
            .and_then(|value| value.checked_add(r0))
            .and_then(|value| value.checked_add(explicit_energy_exponent))
            .and_then(|value| value.checked_mul(4))
            .ok_or_else(|| {
                HayesError::InvalidParameter("Case-2 explicit energy overflow".to_owned())
            })?;
        return Ok((
            EndpointVaughanCase::TypeOneCaseTwo,
            energy.min(completion),
            explicit_energy.min(completion),
        ));
    }
    if inner.checked_mul(3).is_some_and(|value| value >= r0) {
        let left_energy = u128::try_from(endpoint_explicit_energy_ceiling(
            effective_modulus_degree,
            split,
            limits,
            energy_cache,
        )?)
        .map_err(|_| HayesError::InvalidParameter("Case-3 left energy exceeds u128".to_owned()))?;
        let right_energy = u128::try_from(endpoint_explicit_energy_ceiling(
            effective_modulus_degree,
            cutoff - split,
            limits,
            energy_cache,
        )?)
        .map_err(|_| HayesError::InvalidParameter("Case-3 right energy exceeds u128".to_owned()))?;
        let bound = n
            .checked_mul(15)
            .ok_or_else(|| HayesError::InvalidParameter("Case-3 exponent overflow".to_owned()))?;
        let explicit = n
            .checked_mul(8)
            .and_then(|value| {
                left_energy
                    .checked_add(right_energy)
                    .and_then(|energy| energy.checked_add(r0))
                    .and_then(|energy| energy.checked_mul(2))
                    .and_then(|energy| value.checked_add(energy))
            })
            .ok_or_else(|| {
                HayesError::InvalidParameter("Case-3 explicit energy overflow".to_owned())
            })?;
        return Ok((EndpointVaughanCase::TypeOneCaseThree, bound, explicit));
    }
    Err(HayesError::Invariant(
        "Lemire endpoint unexpectedly reaches Type-I Case 4 or 5".to_owned(),
    ))
}

fn enumerate_endpoint_type_one(
    cutoff: usize,
    effective_modulus_degree: usize,
    accumulator: &mut EndpointVaughanAccumulator,
    limits: HayesLimits,
    energy_cache: &mut BTreeMap<(usize, usize), usize>,
) -> Result<(), HayesError> {
    let kappa = binary_complete_kloosterman_exponent(effective_modulus_degree)?;
    let maximum_split = effective_modulus_degree - effective_modulus_degree.div_ceil(3);
    for split in 0..=maximum_split {
        let (case, bound, explicit_energy_bound) = endpoint_type_one_case_bound(
            cutoff,
            effective_modulus_degree,
            split,
            kappa,
            limits,
            energy_cache,
        )?;
        accumulator.record(
            case,
            bound,
            explicit_energy_bound,
            effective_modulus_degree,
            Some(split),
        )?;
    }
    Ok(())
}

fn endpoint_type_two_case_bound(
    cutoff: usize,
    effective_modulus_degree: usize,
    split: usize,
    limits: HayesLimits,
    energy_cache: &mut BTreeMap<(usize, usize), usize>,
) -> Result<Option<(EndpointVaughanCase, u128, u128)>, HayesError> {
    let inner = cutoff - split;
    let n = u128::try_from(cutoff)
        .map_err(|_| HayesError::InvalidParameter("Type-II cutoff exceeds u128".to_owned()))?;
    let r0 = u128::try_from(effective_modulus_degree).map_err(|_| {
        HayesError::InvalidParameter("Type-II effective modulus exceeds u128".to_owned())
    })?;
    let v = u128::try_from(split)
        .map_err(|_| HayesError::InvalidParameter("Type-II split exceeds u128".to_owned()))?;
    let inner_u128 = u128::try_from(inner)
        .map_err(|_| HayesError::InvalidParameter("Type-II inner exceeds u128".to_owned()))?;
    let above_one_third = v.checked_mul(3).is_some_and(|value| value > r0);
    let upper_left = v.checked_mul(3).and_then(|value| value.checked_add(r0));
    let upper_right = n.checked_mul(3);
    if !above_one_third
        || upper_left
            .zip(upper_right)
            .is_none_or(|(left, right)| left > right)
    {
        return Ok(None);
    }
    if v > inner_u128 {
        return Ok(None);
    }
    if v <= r0 && inner_u128 <= r0 {
        let left_energy = u128::try_from(endpoint_explicit_energy_ceiling(
            effective_modulus_degree,
            split,
            limits,
            energy_cache,
        )?)
        .map_err(|_| {
            HayesError::InvalidParameter("Type-II Case-1 left energy exceeds u128".to_owned())
        })?;
        let right_energy = u128::try_from(endpoint_explicit_energy_ceiling(
            effective_modulus_degree,
            inner,
            limits,
            energy_cache,
        )?)
        .map_err(|_| {
            HayesError::InvalidParameter("Type-II Case-1 right energy exceeds u128".to_owned())
        })?;
        let bound = n
            .checked_mul(15)
            .ok_or_else(|| HayesError::InvalidParameter("Type-II Case-1 overflow".to_owned()))?;
        let explicit = n
            .checked_mul(8)
            .and_then(|value| {
                left_energy
                    .checked_add(right_energy)
                    .and_then(|energy| energy.checked_add(r0))
                    .and_then(|energy| energy.checked_mul(2))
                    .and_then(|energy| value.checked_add(energy))
            })
            .ok_or_else(|| {
                HayesError::InvalidParameter("Type-II Case-1 explicit energy overflow".to_owned())
            })?;
        return Ok(Some((EndpointVaughanCase::TypeTwoCaseOne, bound, explicit)));
    }
    if v <= r0 && inner_u128 >= r0 {
        let bound = n
            .checked_mul(16)
            .and_then(|value| v.checked_mul(2).and_then(|term| value.checked_sub(term)))
            .and_then(|value| r0.checked_mul(2).and_then(|term| value.checked_sub(term)))
            .ok_or_else(|| HayesError::InvalidParameter("Type-II Case-2 overflow".to_owned()))?;
        let energy = u128::try_from(endpoint_explicit_energy_ceiling(
            effective_modulus_degree,
            split,
            limits,
            energy_cache,
        )?)
        .map_err(|_| {
            HayesError::InvalidParameter("Type-II Case-2 energy exceeds u128".to_owned())
        })?;
        let explicit = n
            .checked_sub(v)
            .and_then(|value| value.checked_mul(16))
            .and_then(|value| {
                energy
                    .checked_mul(4)
                    .and_then(|term| value.checked_add(term))
            })
            .ok_or_else(|| {
                HayesError::InvalidParameter("Type-II Case-2 explicit energy overflow".to_owned())
            })?;
        return Ok(Some((EndpointVaughanCase::TypeTwoCaseTwo, bound, explicit)));
    }
    if v >= r0 && inner_u128 >= r0 {
        let bound = n
            .checked_mul(16)
            .and_then(|value| r0.checked_mul(4).and_then(|term| value.checked_sub(term)))
            .ok_or_else(|| HayesError::InvalidParameter("Type-II Case-3 overflow".to_owned()))?;
        return Ok(Some((EndpointVaughanCase::TypeTwoCaseThree, bound, bound)));
    }
    Err(HayesError::Invariant(
        "symmetry-reduced Type-II split is uncovered".to_owned(),
    ))
}

fn enumerate_endpoint_type_two(
    cutoff: usize,
    effective_modulus_degree: usize,
    accumulator: &mut EndpointVaughanAccumulator,
    limits: HayesLimits,
    energy_cache: &mut BTreeMap<(usize, usize), usize>,
) -> Result<(), HayesError> {
    for split in 0..=cutoff {
        if let Some((case, bound, explicit_energy_bound)) = endpoint_type_two_case_bound(
            cutoff,
            effective_modulus_degree,
            split,
            limits,
            energy_cache,
        )? {
            accumulator.record(
                case,
                bound,
                explicit_energy_bound,
                effective_modulus_degree,
                Some(split),
            )?;
        }
    }
    Ok(())
}

fn enumerate_endpoint_vaughan_rows(
    cutoff: usize,
    modulus_degree: usize,
    limits: HayesLimits,
    energy_cache: &mut BTreeMap<(usize, usize), usize>,
) -> Result<Vec<EndpointVaughanCaseRow>, HayesError> {
    let maximum_factor_polynomial_degree = modulus_degree
        .checked_mul(4)
        .and_then(|value| value.checked_sub(4))
        .ok_or_else(|| {
            HayesError::InvalidParameter("endpoint divisor-envelope degree overflow".to_owned())
        })?;
    let divisor_cells = maximum_factor_polynomial_degree
        .checked_add(1)
        .and_then(|value| value.checked_mul(value))
        .ok_or_else(|| {
            HayesError::InvalidParameter("endpoint divisor-envelope work overflow".to_owned())
        })?;
    check_limit("table_cells", divisor_cells, limits.max_table_cells)?;
    let _ = binary_polynomial_divisor_envelope(maximum_factor_polynomial_degree)?;
    let n = u128::try_from(cutoff)
        .map_err(|_| HayesError::InvalidParameter("Vaughan cutoff exceeds u128".to_owned()))?;
    let mut accumulator = EndpointVaughanAccumulator::new();
    for effective_modulus_degree in 1..=modulus_degree {
        let r0 = u128::try_from(effective_modulus_degree).map_err(|_| {
            HayesError::InvalidParameter("effective modulus exceeds u128".to_owned())
        })?;
        let small = r0.checked_mul(16).zip(n.checked_mul(7)).ok_or_else(|| {
            HayesError::InvalidParameter("small-modulus threshold overflow".to_owned())
        })?;
        if small.0 < small.1 {
            let bound = r0
                .checked_mul(16)
                .and_then(|value| n.checked_mul(8).and_then(|term| value.checked_add(term)))
                .ok_or_else(|| {
                    HayesError::InvalidParameter("small-modulus exponent overflow".to_owned())
                })?;
            accumulator.record(
                EndpointVaughanCase::SmallEffectiveModulus,
                bound,
                bound,
                effective_modulus_degree,
                None,
            )?;
        } else {
            enumerate_endpoint_type_one(
                cutoff,
                effective_modulus_degree,
                &mut accumulator,
                limits,
                energy_cache,
            )?;
            enumerate_endpoint_type_two(
                cutoff,
                effective_modulus_degree,
                &mut accumulator,
                limits,
                energy_cache,
            )?;
        }
    }
    accumulator.into_rows()
}

/// Enumerate the complete source-level Vaughan range table for one Lemire
/// endpoint convolution order.
///
/// The ideal column uses Bagshaw's characteristic-free energy lines.  The
/// explicit column replaces every `k=2` line by the ceiling of Axeyum's proved
/// wrapped binary energy bound, including its exact finite divisor envelope.
/// Both use the binary complete-sum replacement and leave the remaining
/// analytic/Vaughan-weight constants and polynomial convolution weights out.
///
/// # Errors
///
/// Rejects invalid endpoint parameters, a caller degree limit, an uncovered
/// Vaughan split, or checked-arithmetic overflow.
pub fn endpoint_vaughan_range_report(
    ell: usize,
    endpoint_degree: usize,
    interval_degree: usize,
    limits: HayesLimits,
) -> Result<EndpointVaughanRangeReport, HayesError> {
    let mut energy_cache = BTreeMap::new();
    endpoint_vaughan_range_report_with_energy_cache(
        ell,
        endpoint_degree,
        interval_degree,
        limits,
        &mut energy_cache,
    )
}

fn endpoint_vaughan_range_report_with_energy_cache(
    ell: usize,
    endpoint_degree: usize,
    interval_degree: usize,
    limits: HayesLimits,
    energy_cache: &mut BTreeMap<(usize, usize), usize>,
) -> Result<EndpointVaughanRangeReport, HayesError> {
    let calibration =
        endpoint_inverse_mobius_exponent_calibration(ell, endpoint_degree, interval_degree)?;
    let modulus_degree = ell
        .checked_add(1)
        .ok_or_else(|| HayesError::InvalidParameter("Vaughan modulus overflow".to_owned()))?;
    check_limit("degree", modulus_degree, limits.max_degree)?;
    let cumulative_cutoff = calibration.cumulative_cutoff;
    if cumulative_cutoff <= modulus_degree {
        return Err(HayesError::Invariant(
            "Lemire endpoint cutoff does not exceed its modulus".to_owned(),
        ));
    }
    let rows =
        enumerate_endpoint_vaughan_rows(cumulative_cutoff, modulus_degree, limits, energy_cache)?;
    let worst_row = rows
        .iter()
        .filter_map(|row| row.worst_bound_sixteenths.map(|bound| (row, bound)))
        .max_by(|(left_row, left_bound), (right_row, right_bound)| {
            left_bound
                .cmp(right_bound)
                .then_with(|| right_row.case.cmp(&left_row.case))
        })
        .ok_or_else(|| HayesError::Invariant("Vaughan table has no samples".to_owned()))?;
    let worst_case = worst_row.0.case;
    let worst_bound_sixteenths = worst_row.1;
    let target_exponent_sixteenths = u128::try_from(ell)
        .ok()
        .and_then(|value| value.checked_mul(16))
        .ok_or_else(|| HayesError::InvalidParameter("Vaughan target overflow".to_owned()))?;
    let deficit_sixteenths = checked_exponent_deficit(
        target_exponent_sixteenths,
        worst_bound_sixteenths,
        "endpoint Vaughan",
    )?;
    let worst_explicit_energy_bound_sixteenths = rows
        .iter()
        .filter_map(|row| row.worst_explicit_energy_bound_sixteenths)
        .max()
        .ok_or_else(|| HayesError::Invariant("Vaughan explicit table has no samples".to_owned()))?;
    let explicit_energy_deficit_sixteenths = checked_exponent_deficit(
        target_exponent_sixteenths,
        worst_explicit_energy_bound_sixteenths,
        "endpoint explicit-energy Vaughan",
    )?;
    Ok(EndpointVaughanRangeReport {
        ell,
        endpoint_degree,
        interval_degree,
        cumulative_cutoff,
        modulus_degree,
        rows,
        worst_case,
        worst_bound_sixteenths,
        target_exponent_sixteenths,
        deficit_sixteenths,
        worst_explicit_energy_bound_sixteenths,
        explicit_energy_deficit_sixteenths,
    })
}

/// Enumerate every convolution order in one Lemire endpoint Vaughan audit.
///
/// # Errors
///
/// Rejects invalid endpoint parameters, a caller degree limit, any uncovered
/// source range, or checked-arithmetic overflow.
pub fn endpoint_vaughan_range_table(
    ell: usize,
    endpoint_degree: usize,
    limits: HayesLimits,
) -> Result<EndpointVaughanTableReport, HayesError> {
    if ell < 2 {
        return Err(HayesError::InvalidParameter(
            "endpoint Vaughan table requires ell>=2".to_owned(),
        ));
    }
    let mut convolution_orders = Vec::with_capacity(ell - 1);
    let mut energy_cache = BTreeMap::new();
    for interval_degree in 1..ell {
        convolution_orders.push(endpoint_vaughan_range_report_with_energy_cache(
            ell,
            endpoint_degree,
            interval_degree,
            limits,
            &mut energy_cache,
        )?);
    }
    let first_strict_pointwise_degree = convolution_orders
        .iter()
        .find(|report| report.strict_pointwise_main_term_closure())
        .map(|report| report.interval_degree);
    let first_strict_explicit_energy_degree = convolution_orders
        .iter()
        .find(|report| report.strict_pointwise_explicit_energy_closure())
        .map(|report| report.interval_degree);
    Ok(EndpointVaughanTableReport {
        ell,
        endpoint_degree,
        convolution_orders,
        first_strict_pointwise_degree,
        first_strict_explicit_energy_degree,
    })
}

fn convolution_weight_ceiling_bits(interval_degree: usize) -> usize {
    if interval_degree <= 1 {
        0
    } else {
        usize::BITS as usize - (interval_degree - 1).leading_zeros() as usize
    }
}

/// Charge a buffered large-`d` tail against the exact odd-endpoint budget.
///
/// The caller reserve is an exponent numerator over denominator sixteen.  It
/// is where a future application must place the remaining analytic
/// Vaughan-weight loss and constants.  The report separately charges both
/// the ideal source exponent and Axeyum's explicit energy envelope, restores
/// `ceil(log2(d))`, and rounds each pointwise bound upward before summing.
///
/// # Errors
///
/// Rejects `ell<2`, a tail start outside `1<=d<ell`, caller limits, or checked
/// arithmetic overflow inherited from the exhaustive Vaughan table.
pub fn odd_endpoint_vaughan_tail_budget(
    ell: usize,
    tail_start_degree: usize,
    loss_reserve_sixteenths: u128,
    limits: HayesLimits,
) -> Result<OddEndpointVaughanTailBudgetReport, HayesError> {
    if ell < 2 || tail_start_degree == 0 || tail_start_degree >= ell {
        return Err(HayesError::InvalidParameter(format!(
            "odd endpoint tail requires ell>=2 and 1<=start<ell, got ell={ell}, start={tail_start_degree}"
        )));
    }
    let endpoint_degree = ell
        .checked_mul(2)
        .and_then(|value| value.checked_add(1))
        .ok_or_else(|| HayesError::InvalidParameter("odd endpoint degree overflow".to_owned()))?;
    let table = endpoint_vaughan_range_table(ell, endpoint_degree, limits)?;
    let mut tail_orders = Vec::with_capacity(ell - tail_start_degree);
    let mut tail_absolute_bound = BigUint::from(0_u8);
    let mut explicit_energy_tail_absolute_bound = BigUint::from(0_u8);
    for report in table
        .convolution_orders
        .into_iter()
        .skip(tail_start_degree - 1)
    {
        let convolution_weight_ceiling_bits =
            convolution_weight_ceiling_bits(report.interval_degree);
        let weight_sixteenths = u128::try_from(convolution_weight_ceiling_bits)
            .ok()
            .and_then(|value| value.checked_mul(16))
            .ok_or_else(|| {
                HayesError::InvalidParameter("tail convolution weight overflow".to_owned())
            })?;
        let total_sixteenths = report
            .worst_bound_sixteenths
            .checked_add(loss_reserve_sixteenths)
            .and_then(|value| value.checked_add(weight_sixteenths))
            .ok_or_else(|| HayesError::InvalidParameter("tail exponent overflow".to_owned()))?;
        let total_ceiling_bits = usize::try_from(total_sixteenths.div_ceil(16))
            .map_err(|_| HayesError::InvalidParameter("tail exponent exceeds usize".to_owned()))?;
        let absolute_bound = BigUint::from(1_u8) << total_ceiling_bits;
        let explicit_total_sixteenths = report
            .worst_explicit_energy_bound_sixteenths
            .checked_add(loss_reserve_sixteenths)
            .and_then(|value| value.checked_add(weight_sixteenths))
            .ok_or_else(|| {
                HayesError::InvalidParameter("explicit-energy tail exponent overflow".to_owned())
            })?;
        let explicit_total_ceiling_bits = usize::try_from(explicit_total_sixteenths.div_ceil(16))
            .map_err(|_| {
            HayesError::InvalidParameter("explicit-energy tail exponent exceeds usize".to_owned())
        })?;
        let explicit_energy_absolute_bound = BigUint::from(1_u8) << explicit_total_ceiling_bits;
        tail_absolute_bound += &absolute_bound;
        explicit_energy_tail_absolute_bound += &explicit_energy_absolute_bound;
        tail_orders.push(OddEndpointVaughanTailOrder {
            interval_degree: report.interval_degree,
            main_bound_sixteenths: report.worst_bound_sixteenths,
            explicit_energy_bound_sixteenths: report.worst_explicit_energy_bound_sixteenths,
            loss_reserve_sixteenths,
            convolution_weight_ceiling_bits,
            total_ceiling_bits,
            absolute_bound,
            explicit_energy_absolute_bound,
        });
    }
    let uniform_mean = BigUint::from(1_u8)
        << ell.checked_add(1).ok_or_else(|| {
            HayesError::InvalidParameter("odd endpoint uniform exponent overflow".to_owned())
        })?;
    let endpoint_absolute_budget = uniform_mean - BigUint::from(2_u8);
    let residual_low_block_budget = (tail_absolute_bound <= endpoint_absolute_budget)
        .then(|| &endpoint_absolute_budget - &tail_absolute_bound);
    let explicit_energy_residual_low_block_budget = (explicit_energy_tail_absolute_bound
        <= endpoint_absolute_budget)
        .then(|| &endpoint_absolute_budget - &explicit_energy_tail_absolute_bound);
    Ok(OddEndpointVaughanTailBudgetReport {
        ell,
        endpoint_degree,
        tail_start_degree,
        loss_reserve_sixteenths,
        tail_orders,
        endpoint_absolute_budget,
        tail_absolute_bound,
        explicit_energy_tail_absolute_bound,
        residual_low_block_budget,
        explicit_energy_residual_low_block_budget,
    })
}

/// Compute the exact mixed product-collision energy of `V_a V_b` in `E_ell`.
///
/// Write `a=min(left_degree,right_degree)` and
/// `b=max(left_degree,right_degree)`.  Gcd reduction of the two `V_a`
/// factors gives
///
/// ```text
/// #{(u,v,w,y) in V_a x V_b x V_a x V_b : uv=wy}
///   = (a+2) 2^(a+b-1),                              a+b<=ell,
///   = 2^(2a+2b-ell) + (ell-b) 2^(a+b-1),            a+b>ell.
/// ```
///
/// At `a+b=ell` the expressions agree.  The returned Fourier numerator is
/// the mixed finite-group Parseval identity documented on
/// [`PrincipalUnitMixedProductEnergyReport`].
///
/// # Errors
///
/// Rejects `ell=0`, a zero interval degree, an interval degree at least
/// `ell`, host-width overflow, or a caller limit before constructing any
/// large table.
pub fn principal_unit_mixed_product_energy(
    ell: usize,
    left_degree: usize,
    right_degree: usize,
    limits: HayesLimits,
) -> Result<PrincipalUnitMixedProductEnergyReport, HayesError> {
    if left_degree == 0 || right_degree == 0 {
        return Err(HayesError::InvalidParameter(
            "principal-unit mixed product energy requires positive degrees".to_owned(),
        ));
    }
    if left_degree >= ell || right_degree >= ell {
        return Err(HayesError::InvalidParameter(
            "principal-unit mixed product energy requires degrees smaller than ell".to_owned(),
        ));
    }
    check_limit("degree", left_degree, limits.max_degree)?;
    check_limit("degree", right_degree, limits.max_degree)?;
    let structure = principal_unit_structure(ell, limits)?;
    let (a, b) = if left_degree <= right_degree {
        (left_degree, right_degree)
    } else {
        (right_degree, left_degree)
    };
    let degree_sum = a.checked_add(b).ok_or_else(|| {
        HayesError::InvalidParameter("mixed product-energy degree overflow".to_owned())
    })?;
    let centered_exponent = degree_sum.checked_sub(1).ok_or_else(|| {
        HayesError::InvalidParameter("mixed product-energy exponent underflow".to_owned())
    })?;

    let left_set_size = BigUint::from(1_u8) << left_degree;
    let right_set_size = BigUint::from(1_u8) << right_degree;
    let ordered_pair_count = BigUint::from(1_u8) << degree_sum;
    let ordinary_product_regime = degree_sum <= ell;
    let pair_product_energy = if ordinary_product_regime {
        BigUint::from(a + 2) << centered_exponent
    } else {
        let uniform_exponent = degree_sum
            .checked_mul(2)
            .and_then(|value| value.checked_sub(ell))
            .ok_or_else(|| {
                HayesError::InvalidParameter(
                    "mixed uniform product-energy exponent overflow".to_owned(),
                )
            })?;
        (BigUint::from(1_u8) << uniform_exponent) + (BigUint::from(ell - b) << centered_exponent)
    };
    let group_order = BigUint::from(structure.group_order);
    let all_character_moment = &group_order * &pair_product_energy;
    let principal_moment = left_set_size.pow(2) * right_set_size.pow(2);
    if all_character_moment < principal_moment {
        return Err(HayesError::Invariant(
            "mixed product-energy Parseval numerator is negative".to_owned(),
        ));
    }
    let centered_fourier_mixed_moment_numerator = all_character_moment - principal_moment;

    Ok(PrincipalUnitMixedProductEnergyReport {
        ell,
        left_degree,
        right_degree,
        left_set_size,
        right_set_size,
        ordered_pair_count,
        pair_product_energy,
        centered_fourier_mixed_moment_numerator,
        ordinary_product_regime,
    })
}

/// Compute the exact product-collision energy of `V_d` inside `E_ell`.
///
/// For `1 <= d < ell`, unique reduction of a pair `(a,c)` by its polynomial
/// gcd gives the ordinary-product identity
///
/// ```text
/// #{(a,b,c,f) in V_d^4 : ab=cf} = (d+2) 2^(2d-1).
/// ```
///
/// Once `2d>ell`, projection modulo `x^(ell+1)` adds the uniform collision
/// term and leaves an exact centered term:
///
/// ```text
/// #{ab=cf mod x^(ell+1)}
///   = 2^(4d-ell) + (ell-d) 2^(2d-1).
/// ```
///
/// At `2d=ell` the ordinary formula applies and agrees with the second
/// expression.  The returned Fourier numerator is the integral Parseval
/// identity
///
/// ```text
/// sum_(chi != 1) |sum_(a in V_d) chi(a)|^4
///   = 2^ell pair_product_energy - |V_d|^4.
/// ```
///
/// # Errors
///
/// Rejects `ell=0`, `degree=0`, `degree>=ell`, host-width overflow, or a
/// caller limit before constructing any large table.
pub fn principal_unit_product_energy(
    ell: usize,
    degree: usize,
    limits: HayesLimits,
) -> Result<PrincipalUnitProductEnergyReport, HayesError> {
    let mixed = principal_unit_mixed_product_energy(ell, degree, degree, limits)?;

    Ok(PrincipalUnitProductEnergyReport {
        ell,
        degree,
        set_size: mixed.left_set_size,
        ordered_pair_count: mixed.ordered_pair_count,
        pair_product_energy: mixed.pair_product_energy,
        centered_fourier_fourth_moment_numerator: mixed.centered_fourier_mixed_moment_numerator,
        ordinary_product_regime: mixed.ordinary_product_regime,
    })
}

/// Check that an explicit conductor estimate would finish the endpoint proof.
///
/// This proves only the arithmetic implication. It does not prove the supplied
/// estimate for `T_(j,n)`.
///
/// # Errors
///
/// Returns an error when the assumption is malformed, the finite range leaves
/// a gap, or any exact base or induction inequality fails.
pub fn check_conductor_bound_sufficiency(
    assumption: ConductorBoundAssumption,
) -> Result<SufficientBoundReport, HayesError> {
    let ConductorBoundAssumption {
        constant,
        power,
        threshold,
        finite_max_degree,
    } = assumption;
    if constant == 0 || threshold < 2 {
        return Err(HayesError::InvalidParameter(
            "constant must be positive and threshold must be at least two".to_owned(),
        ));
    }
    let power = u32::try_from(power).map_err(|_| {
        HayesError::InvalidParameter("power does not fit the exact exponent domain".to_owned())
    })?;
    let twice_threshold = threshold.checked_mul(2).ok_or_else(|| {
        HayesError::InvalidParameter("threshold degree calculation overflow".to_owned())
    })?;
    if twice_threshold > finite_max_degree {
        return Err(HayesError::InvalidParameter(
            "finite remainder exceeds the checked degree range".to_owned(),
        ));
    }
    let rounded_sum = (1..=threshold).fold(BigUint::from(0_u8), |sum, level| {
        sum + BigUint::from(level).pow(power) * (BigUint::from(1_u8) << level.div_ceil(2))
    });
    let twice_constant = BigUint::from(2_u8) * BigUint::from(constant);
    let base_left = &twice_constant * rounded_sum;
    let base_right = BigUint::from(1_u8) << threshold;
    if base_left > base_right {
        return Err(HayesError::Invariant(
            "base endpoint inequality does not hold".to_owned(),
        ));
    }
    for (name, level) in [("even", threshold), ("odd", threshold + 1)] {
        let new_term = &twice_constant
            * BigUint::from(level + 1).pow(power)
            * (BigUint::from(1_u8) << (level / 2 + 1));
        if new_term > (BigUint::from(1_u8) << level) {
            return Err(HayesError::Invariant(format!(
                "{name} induction seed does not hold"
            )));
        }
    }
    if BigUint::from(2_u8) * BigUint::from(threshold + 1).pow(power)
        < BigUint::from(threshold + 3).pow(power)
    {
        return Err(HayesError::Invariant(
            "two-step induction ratio is not monotone at the threshold".to_owned(),
        ));
    }

    let first_odd_degree = twice_threshold.checked_add(1).ok_or_else(|| {
        HayesError::InvalidParameter("odd endpoint degree calculation overflow".to_owned())
    })?;
    let first_even_degree = twice_threshold.checked_add(2).ok_or_else(|| {
        HayesError::InvalidParameter("even endpoint degree calculation overflow".to_owned())
    })?;
    if BigUint::from(first_odd_degree).pow(6) >= (BigUint::from(1_u8) << (first_odd_degree - 3)) {
        return Err(HayesError::Invariant(
            "odd proper-divisor margin does not hold".to_owned(),
        ));
    }
    if BigUint::from(first_even_degree).pow(6) >= (BigUint::from(1_u8) << (first_even_degree - 6)) {
        return Err(HayesError::Invariant(
            "even proper-divisor margin does not hold".to_owned(),
        ));
    }
    if BigUint::from(first_odd_degree + 2).pow(6)
        >= BigUint::from(4_u8) * BigUint::from(first_odd_degree).pow(6)
    {
        return Err(HayesError::Invariant(
            "proper-divisor induction ratio is not monotone".to_owned(),
        ));
    }
    Ok(SufficientBoundReport {
        assumption,
        first_odd_degree,
        first_even_degree,
    })
}

/// Compute the exact weak fourth-moment endpoint ledger using the proved
/// proper-power envelope.
///
/// The proved second-moment estimate is
///
/// ```text
/// M_2 <= mu Sigma(ell),
/// Sigma(ell)=sum_(j=2)^ell 2^(j-1)(j-1)^2.
/// ```
///
/// Since `R_0=2^ell M_4/M_2^2`, the strict rational condition
///
/// ```text
/// R_0 < 2^ell (mu-P_n)^4 / (mu Sigma(ell))^2
/// ```
///
/// implies the exact irreducibility threshold.  This function proves only
/// that arithmetic implication; it does not establish a bound on `R_0`.
///
/// # Errors
///
/// Rejects non-endpoint parameters and checked exponent overflow.
pub fn weak_fourth_moment_endpoint_ledger(
    ell: usize,
    degree: usize,
) -> Result<WeakFourthMomentEndpointLedger, HayesError> {
    if ell == 0 {
        return Err(HayesError::InvalidParameter(
            "weak fourth-moment ledger requires ell at least one".to_owned(),
        ));
    }
    let odd_degree = ell
        .checked_mul(2)
        .and_then(|value| value.checked_add(1))
        .ok_or_else(|| HayesError::InvalidParameter("weak endpoint degree overflow".to_owned()))?;
    let even_degree = odd_degree
        .checked_add(1)
        .ok_or_else(|| HayesError::InvalidParameter("weak endpoint degree overflow".to_owned()))?;
    if degree != odd_degree && degree != even_degree {
        return Err(HayesError::InvalidParameter(format!(
            "weak fourth-moment ledger is endpoint-only: ell={ell}, degree={degree}"
        )));
    }
    let main_exponent = degree.checked_sub(ell).ok_or_else(|| {
        HayesError::InvalidParameter("weak fourth-moment main exponent underflow".to_owned())
    })?;
    let main_mangoldt_term = BigUint::from(1_u8) << main_exponent;
    let proper_prime_power_upper_bound = endpoint_proper_prime_power_upper_bound(degree, ell)?;
    if proper_prime_power_upper_bound >= main_mangoldt_term {
        return Err(HayesError::Invariant(
            "proper powers exhaust the weak fourth-moment main term".to_owned(),
        ));
    }
    let irreducible_margin = &main_mangoldt_term - &proper_prime_power_upper_bound;
    let positivity_only_fourth_moment_threshold = main_mangoldt_term.pow(4);
    let strict_irreducible_fourth_moment_threshold = irreducible_margin.pow(4);
    let wild_fourth_moment_unit_scale = (BigUint::from(1_u8) << ell) * main_mangoldt_term.pow(3);
    let sufficient_wild_constant_numerator = strict_irreducible_fourth_moment_threshold.clone();
    let sufficient_wild_constant_denominator = wild_fourth_moment_unit_scale.clone();
    let mut second_moment_weil_factor = BigUint::from(0_u8);
    for level in 2..=ell {
        second_moment_weil_factor += BigUint::from(level - 1).pow(2) << (level - 1);
    }
    let second_moment_upper_bound = &main_mangoldt_term * &second_moment_weil_factor;
    let sufficient_root_ratio_numerator =
        (BigUint::from(1_u8) << ell) * &strict_irreducible_fourth_moment_threshold;
    let sufficient_root_ratio_denominator = second_moment_upper_bound.pow(2);
    let strong_connected_target_has_strict_reserve =
        BigUint::from(4_u8) * &sufficient_root_ratio_denominator < sufficient_root_ratio_numerator;
    Ok(WeakFourthMomentEndpointLedger {
        degree,
        ell,
        main_mangoldt_term,
        proper_prime_power_upper_bound,
        irreducible_margin,
        positivity_only_fourth_moment_threshold,
        strict_irreducible_fourth_moment_threshold,
        wild_fourth_moment_unit_scale,
        sufficient_wild_constant_numerator,
        sufficient_wild_constant_denominator,
        second_moment_weil_factor,
        second_moment_upper_bound,
        sufficient_root_ratio_numerator,
        sufficient_root_ratio_denominator,
        strong_connected_target_has_strict_reserve,
    })
}

/// Check that a fourth central-moment estimate would finish the endpoint proof.
///
/// The norm inequality `max |Delta_e|^4 <= sum |Delta_e|^4` first reduces the
/// assumed envelope to `|Delta_e| <= 2^ell`.  The remaining exact checks are
/// the finite-range handoff and the proper-divisor margins in Hayes Möbius
/// inversion.  This function does not prove the fourth-moment estimate.
///
/// # Errors
///
/// Returns an error for a malformed assumption, a finite-range gap, or a
/// failed exact seed or monotonicity inequality.
pub fn check_fourth_moment_bound_sufficiency(
    assumption: FourthMomentBoundAssumption,
) -> Result<FourthMomentBoundReport, HayesError> {
    let FourthMomentBoundAssumption {
        constant,
        power,
        threshold,
        finite_max_degree,
    } = assumption;
    if constant == 0 || threshold < 3 {
        return Err(HayesError::InvalidParameter(
            "constant must be positive and threshold must be at least three".to_owned(),
        ));
    }
    let power = u32::try_from(power).map_err(|_| {
        HayesError::InvalidParameter("power does not fit the exact exponent domain".to_owned())
    })?;
    let twice_threshold = threshold.checked_mul(2).ok_or_else(|| {
        HayesError::InvalidParameter("threshold degree calculation overflow".to_owned())
    })?;
    if twice_threshold > finite_max_degree {
        return Err(HayesError::InvalidParameter(
            "finite remainder exceeds the checked degree range".to_owned(),
        ));
    }

    let polynomial = BigUint::from(constant) * BigUint::from(threshold).pow(power);
    if polynomial > (BigUint::from(1_u8) << threshold) {
        return Err(HayesError::Invariant(
            "fourth-moment envelope does not imply the discrepancy bound at the threshold"
                .to_owned(),
        ));
    }
    if BigUint::from(threshold + 1).pow(power)
        > BigUint::from(2_u8) * BigUint::from(threshold).pow(power)
    {
        return Err(HayesError::Invariant(
            "fourth-moment envelope induction ratio is not monotone".to_owned(),
        ));
    }

    let first_odd_degree = twice_threshold.checked_add(1).ok_or_else(|| {
        HayesError::InvalidParameter("odd endpoint degree calculation overflow".to_owned())
    })?;
    let first_even_degree = twice_threshold.checked_add(2).ok_or_else(|| {
        HayesError::InvalidParameter("even endpoint degree calculation overflow".to_owned())
    })?;
    if BigUint::from(first_odd_degree).pow(6) >= (BigUint::from(1_u8) << (first_odd_degree - 3)) {
        return Err(HayesError::Invariant(
            "odd proper-divisor margin does not hold".to_owned(),
        ));
    }
    if BigUint::from(first_even_degree).pow(6) >= (BigUint::from(1_u8) << (first_even_degree - 6)) {
        return Err(HayesError::Invariant(
            "even proper-divisor margin does not hold".to_owned(),
        ));
    }
    if BigUint::from(first_odd_degree + 2).pow(6)
        >= BigUint::from(4_u8) * BigUint::from(first_odd_degree).pow(6)
    {
        return Err(HayesError::Invariant(
            "proper-divisor induction ratio is not monotone".to_owned(),
        ));
    }

    Ok(FourthMomentBoundReport {
        assumption,
        first_odd_degree,
        first_even_degree,
    })
}

/// Check that linear Witt-cylinder concentration would finish the endpoint proof.
///
/// The proved second-moment estimate is
///
/// ```text
/// M_2 <= 2^(n-ell) sum_(j=2)^ell 2^(j-1) (j-1)^2
///     <= ell^2 2^n.
/// ```
///
/// The assumed root inequality `R_0 <= ell` therefore gives
/// `M_4 <= 16 ell^5 2^(3ell)` for both `n=2ell+1` and
/// `n=2ell+2`.  The existing fourth-moment implication checks the finite
/// handoff and proper-power margins.  This function does not prove the local
/// concentration assumption.
///
/// # Errors
///
/// Returns an error when the finite handoff or the derived exact endpoint
/// inequalities fail.
pub fn check_witt_cylinder_linear_bound_sufficiency(
    assumption: WittCylinderLinearBoundAssumption,
) -> Result<WittCylinderLinearBoundReport, HayesError> {
    let derived_fourth_moment =
        check_fourth_moment_bound_sufficiency(FourthMomentBoundAssumption {
            constant: 16,
            power: 5,
            threshold: assumption.threshold,
            finite_max_degree: assumption.finite_max_degree,
        })?;
    Ok(WittCylinderLinearBoundReport {
        assumption,
        derived_fourth_moment,
    })
}

/// Check that connected fourth-cumulant domination finishes the endpoint proof.
///
/// The assumption gives `M_4 <= 4 M_2^2 / 2^ell`.  Combining it with the
/// proved `M_2 <= ell^2 2^n` envelope yields
/// `M_4 <= 64 ell^4 2^(3ell)` simultaneously for `n=2ell+1` and
/// `n=2ell+2`.  This function checks only that arithmetic consequence.
///
/// # Errors
///
/// Returns an error when the finite handoff or any derived endpoint inequality
/// fails.
pub fn check_connected_cumulant_bound_sufficiency(
    assumption: ConnectedCumulantBoundAssumption,
) -> Result<ConnectedCumulantBoundReport, HayesError> {
    let derived_fourth_moment =
        check_fourth_moment_bound_sufficiency(FourthMomentBoundAssumption {
            constant: 64,
            power: 4,
            threshold: assumption.threshold,
            finite_max_degree: assumption.finite_max_degree,
        })?;
    Ok(ConnectedCumulantBoundReport {
        assumption,
        derived_fourth_moment,
    })
}

/// Compute the exact cohomological cutoff and Betti budget for a connected
/// Adams identity-fibre proof.
///
/// Write `G=2^ell`.  For the centred character power sums, the connected
/// convolution numerator is `G^2 K_4`.  The sufficient geometric estimate
///
/// ```text
/// abs(G^2 K_4) <= ell^4 * 2^(2*ell+2*degree)
/// ```
///
/// gives `K_4<=ell^4*2^(2*degree)`.  Together with the proved
/// `M_2<=ell^2*2^degree`, this yields
/// `M_4<=64*ell^4*2^(3*ell)` at either Lemire endpoint, exactly the envelope
/// consumed by [`check_connected_cumulant_bound_sufficiency`].  Geometrically,
/// the displayed estimate would follow after removing the Adams weight
/// `2^(2*degree)` from a mixed complex of weights at most zero whose compactly
/// supported cohomology vanishes above degree `4*ell` and whose normalized
/// total Betti number is at most `ell^4`.
///
/// # Errors
///
/// Returns a parameter error away from the two Lemire endpoints or if a
/// dimension/exponent calculation overflows.
pub fn hayes_adams_identity_fibre_requirement(
    ell: usize,
    degree: usize,
) -> Result<HayesAdamsIdentityFibreRequirement, HayesError> {
    let twice_ell = ell
        .checked_mul(2)
        .ok_or_else(|| HayesError::InvalidParameter("Adams endpoint degree overflow".to_owned()))?;
    if ell == 0 || !matches!(degree.checked_sub(twice_ell), Some(1 | 2)) {
        return Err(HayesError::InvalidParameter(
            "Adams identity-fibre budget requires degree in {2*ell+1,2*ell+2}".to_owned(),
        ));
    }
    let identity_fibre_dimension = ell.checked_mul(3).ok_or_else(|| {
        HayesError::InvalidParameter("Adams identity-fibre dimension overflow".to_owned())
    })?;
    let wick_pairing_dimension = ell.checked_mul(2).ok_or_else(|| {
        HayesError::InvalidParameter("Adams pairing dimension overflow".to_owned())
    })?;
    let ambient_max_cohomology_degree = ell.checked_mul(6).ok_or_else(|| {
        HayesError::InvalidParameter("Adams ambient cohomology degree overflow".to_owned())
    })?;
    let required_max_cohomology_degree = ell.checked_mul(4).ok_or_else(|| {
        HayesError::InvalidParameter("Adams required cohomology degree overflow".to_owned())
    })?;
    let normalized_betti_budget = BigUint::from(ell).pow(4);
    let normalized_shift = u32::try_from(wick_pairing_dimension).map_err(|_| {
        HayesError::InvalidParameter("Adams normalized allowance shift exceeds u32".to_owned())
    })?;
    let weight_shift = degree
        .checked_mul(2)
        .and_then(|value| u32::try_from(value).ok())
        .ok_or_else(|| {
            HayesError::InvalidParameter("Adams weight allowance shift exceeds u32".to_owned())
        })?;
    let normalized_connected_trace_allowance = &normalized_betti_budget << normalized_shift;
    let connected_trace_allowance = &normalized_connected_trace_allowance << weight_shift;
    Ok(HayesAdamsIdentityFibreRequirement {
        ell,
        degree,
        identity_fibre_dimension,
        ambient_max_cohomology_degree,
        wick_pairing_dimension,
        required_max_cohomology_degree,
        required_cohomology_degree_drop: wick_pairing_dimension,
        normalized_betti_budget,
        normalized_connected_trace_allowance,
        connected_trace_allowance,
    })
}

fn gcd_usize(mut left: usize, mut right: usize) -> usize {
    while right != 0 {
        let remainder = left % right;
        left = right;
        right = remainder;
    }
    left
}

fn factor_usize(mut value: usize) -> Vec<(usize, usize)> {
    let mut factors = Vec::new();
    let mut prime = 2_usize;
    while prime <= value / prime {
        if value.is_multiple_of(prime) {
            let mut exponent = 0_usize;
            while value.is_multiple_of(prime) {
                value /= prime;
                exponent += 1;
            }
            factors.push((prime, exponent));
        }
        prime = if prime == 2 { 3 } else { prime + 2 };
    }
    if value > 1 {
        factors.push((value, 1));
    }
    factors
}

fn divisors_from_factorization(factors: &[(usize, usize)]) -> Result<Vec<usize>, HayesError> {
    let mut divisors = vec![1_usize];
    for &(prime, exponent) in factors {
        let original = divisors.clone();
        let mut power = 1_usize;
        for _ in 0..exponent {
            power = power.checked_mul(prime).ok_or_else(|| {
                HayesError::InvalidParameter("Foulkes divisor power overflow".to_owned())
            })?;
            for divisor in &original {
                divisors.push(divisor.checked_mul(power).ok_or_else(|| {
                    HayesError::InvalidParameter("Foulkes divisor overflow".to_owned())
                })?);
            }
        }
    }
    divisors.sort_unstable();
    Ok(divisors)
}

fn euler_phi_usize(value: usize, factors: &[(usize, usize)]) -> Result<usize, HayesError> {
    let mut result = value;
    for &(prime, _) in factors {
        result = result
            .checked_div(prime)
            .and_then(|quotient| quotient.checked_mul(prime - 1))
            .ok_or_else(|| {
                HayesError::InvalidParameter("Foulkes Euler totient overflow".to_owned())
            })?;
    }
    Ok(result)
}

fn mobius_usize(value: usize) -> i8 {
    let factors = factor_usize(value);
    if factors.iter().any(|(_, exponent)| *exponent > 1) {
        0
    } else if factors.len().is_multiple_of(2) {
        1
    } else {
        -1
    }
}

fn ramanujan_sum_usize(modulus: usize, residue: usize) -> Result<BigInt, HayesError> {
    let common = gcd_usize(modulus, residue);
    let divisors = divisors_from_factorization(&factor_usize(common))?;
    let mut sum = BigInt::from(0_u8);
    for divisor in divisors {
        let quotient = modulus.checked_div(divisor).ok_or_else(|| {
            HayesError::Invariant("Ramanujan divisor does not divide modulus".to_owned())
        })?;
        sum += BigInt::from(divisor) * BigInt::from(mobius_usize(quotient));
    }
    Ok(sum)
}

fn ramanujan_sum_closed_form(modulus: usize, residue: usize) -> Result<BigInt, HayesError> {
    let quotient = modulus / gcd_usize(modulus, residue);
    let mobius = mobius_usize(quotient);
    if mobius == 0 {
        return Ok(BigInt::from(0_u8));
    }
    let modulus_phi = euler_phi_usize(modulus, &factor_usize(modulus))?;
    let quotient_phi = euler_phi_usize(quotient, &factor_usize(quotient))?;
    let ratio = modulus_phi.checked_div(quotient_phi).ok_or_else(|| {
        HayesError::Invariant("Ramanujan closed-form totient ratio is not integral".to_owned())
    })?;
    Ok(BigInt::from(mobius) * BigInt::from(ratio))
}

struct FoulkesCompressionCertificate {
    coefficient_denominator: BigUint,
    distinct_prime_factor_count: usize,
    coefficients: Vec<FoulkesRamanujanCoefficient>,
    distinct_coefficients: Vec<FoulkesDistinctCoefficient>,
    reconstructed_power_sum_coefficients: Vec<FoulkesPowerSumCoefficient>,
    coefficient_l1_numerator: BigUint,
    coefficient_l1_mass: BigUint,
}

fn certify_foulkes_compression(
    degree: usize,
    limits: SawinFoulkesLimits,
) -> Result<FoulkesCompressionCertificate, HayesError> {
    if degree > limits.max_degree {
        return Err(HayesError::ResourceLimit {
            resource: "sawin_foulkes_degree",
            requested: degree,
            limit: limits.max_degree,
        });
    }
    let factors = factor_usize(degree);
    let divisors = divisors_from_factorization(&factors)?;
    let orthogonality_cells = degree.checked_mul(divisors.len()).ok_or_else(|| {
        HayesError::InvalidParameter("Foulkes orthogonality cell count overflow".to_owned())
    })?;
    if orthogonality_cells > limits.max_orthogonality_cells {
        return Err(HayesError::ResourceLimit {
            resource: "sawin_foulkes_orthogonality_cells",
            requested: orthogonality_cells,
            limit: limits.max_orthogonality_cells,
        });
    }

    let phi = euler_phi_usize(degree, &factors)?;
    let coefficients = (0..degree)
        .map(|residue| {
            let numerator = ramanujan_sum_usize(degree, residue)?;
            if numerator != ramanujan_sum_closed_form(degree, residue)? {
                return Err(HayesError::Invariant(format!(
                    "independent Ramanujan formulas disagree at residue {residue}"
                )));
            }
            Ok(FoulkesRamanujanCoefficient { residue, numerator })
        })
        .collect::<Result<Vec<_>, HayesError>>()?;
    let coefficient_l1_numerator = coefficients.iter().fold(BigUint::from(0_u8), |sum, row| {
        sum + row.numerator.magnitude()
    });
    let distinct_prime_factor_count = factors.len();
    let coefficient_l1_mass = BigUint::from(1_u8) << distinct_prime_factor_count;
    let coefficient_denominator = BigUint::from(phi);
    if coefficient_l1_numerator != &coefficient_denominator * &coefficient_l1_mass {
        return Err(HayesError::Invariant(
            "Foulkes coefficient l1 mass does not equal 2^omega(n)".to_owned(),
        ));
    }

    let distinct_coefficients = certify_distinct_foulkes_coefficients(
        degree,
        phi,
        &divisors,
        &coefficients,
        &coefficient_l1_mass,
    )?;
    let reconstructed_power_sum_coefficients =
        certify_foulkes_power_sum_coefficients(degree, phi, &divisors, &coefficients)?;
    Ok(FoulkesCompressionCertificate {
        coefficient_denominator,
        distinct_prime_factor_count,
        coefficients,
        distinct_coefficients,
        reconstructed_power_sum_coefficients,
        coefficient_l1_numerator,
        coefficient_l1_mass,
    })
}

fn certify_distinct_foulkes_coefficients(
    degree: usize,
    phi: usize,
    divisors: &[usize],
    coefficients: &[FoulkesRamanujanCoefficient],
    coefficient_l1_mass: &BigUint,
) -> Result<Vec<FoulkesDistinctCoefficient>, HayesError> {
    let mut distinct_coefficients = Vec::with_capacity(divisors.len());
    for &divisor in divisors {
        let cyclic_character_residue = degree / divisor;
        let grouped_numerator = coefficients
            .iter()
            .filter(|row| gcd_usize(degree, row.residue) == cyclic_character_residue)
            .fold(BigInt::from(0_u8), |sum, row| sum + &row.numerator);
        let coefficient = BigInt::from(mobius_usize(divisor));
        if grouped_numerator != &coefficient * BigInt::from(phi) {
            return Err(HayesError::Invariant(format!(
                "grouped Foulkes coefficient is not mu({divisor})"
            )));
        }
        distinct_coefficients.push(FoulkesDistinctCoefficient {
            divisor,
            cyclic_character_residue,
            coefficient,
        });
    }
    let nonzero_count = distinct_coefficients
        .iter()
        .filter(|row| row.coefficient != BigInt::from(0_u8))
        .count();
    if BigUint::from(nonzero_count) != *coefficient_l1_mass {
        return Err(HayesError::Invariant(
            "nonzero distinct Foulkes count does not equal 2^omega(n)".to_owned(),
        ));
    }
    Ok(distinct_coefficients)
}

fn certify_foulkes_power_sum_coefficients(
    degree: usize,
    phi: usize,
    divisors: &[usize],
    coefficients: &[FoulkesRamanujanCoefficient],
) -> Result<Vec<FoulkesPowerSumCoefficient>, HayesError> {
    let expected_diagonal = BigInt::from(degree) * BigInt::from(phi);
    let mut result = Vec::with_capacity(divisors.len());
    for &divisor in divisors {
        let mut numerator = BigInt::from(0_u8);
        for row in coefficients {
            numerator += &row.numerator * ramanujan_sum_usize(divisor, row.residue)?;
        }
        let expected_numerator = if divisor == degree {
            expected_diagonal.clone()
        } else {
            BigInt::from(0_u8)
        };
        if numerator != expected_numerator {
            return Err(HayesError::Invariant(format!(
                "Foulkes orthogonality failed at divisor {divisor}"
            )));
        }
        result.push(FoulkesPowerSumCoefficient {
            divisor,
            numerator,
            expected_numerator,
        });
    }
    Ok(result)
}

fn endpoint_proper_prime_power_upper_bound(
    degree: usize,
    ell: usize,
) -> Result<BigUint, HayesError> {
    let odd_degree = ell
        .checked_mul(2)
        .and_then(|value| value.checked_add(1))
        .ok_or_else(|| HayesError::InvalidParameter("Foulkes odd endpoint overflow".to_owned()))?;
    if degree == odd_degree {
        return Ok(BigUint::from(1_u8));
    }
    let even_degree = odd_degree
        .checked_add(1)
        .ok_or_else(|| HayesError::InvalidParameter("Foulkes even endpoint overflow".to_owned()))?;
    if degree != even_degree {
        return Err(HayesError::Invariant(
            "Foulkes degree is not a Lemire endpoint".to_owned(),
        ));
    }
    // For k=2, an irreducible P of degree ell+1 has P(0)=1.  Its truncated
    // class therefore determines P injectively, and <P>^2=1 places it in the
    // 2-torsion subgroup of order 2^ceil(ell/2).
    let half_degree = degree / 2;
    let square_power_bound = BigUint::from(half_degree) << ell.div_ceil(2);

    // Every odd k>=3 layer is empty.  Indeed d=degree/k<=ell, odd powering is
    // an automorphism of the principal-unit 2-group, and <P>^k=1 forces
    // P=x^d, which is not irreducible because degree is even and d>=2.  Thus
    // the remaining exponents are even k>=4, with d<=degree/4=(ell+1)/2.
    let higher_power_bound = BigUint::from(degree) << (ell + 1).div_ceil(2);
    Ok(square_power_bound + higher_power_bound)
}

/// Certify the long-cycle fixed locus and its exact non-top Euler
/// cancellation at a Lemire endpoint.
///
/// The character identity used here is
///
/// ```text
/// <chi,p_n> = (1/n!) sum_(g in S_n) chi(g) p_n(g)
///           = Tr(c | chi),
/// ```
///
/// because there are `(n-1)!` long cycles and `p_n(c)=n`.  For the geometric
/// fixed locus, Lucas's theorem says that the first odd entry in row `n` of
/// Pascal's triangle occurs at `lowbit(n)`.  At
/// `ell=ceil(n/2)-1`, this is at most `ell` for every odd `n` and every even
/// non-power of two.  The sole affine-line case is therefore an even power of
/// two; its compactly supported Euler characteristic is still one.
///
/// For `n=2^a b`, Deligne--Lusztig's finite-order formula replaces the trace
/// of the full cycle by the trace of its `2`-power part on the locus fixed by
/// its odd part.  If `b>1`, a triangular leading-coefficient calculation on
/// `G(x)^b` makes that locus a point.  Subtracting the trivial one-dimensional
/// top cohomology then proves exact zero alternating trace on the non-top
/// complex away from powers of two.  At powers of two the odd part is the
/// identity, so that route alone gives no trace conclusion.
///
/// The homogeneous-cone decomposition closes the unweighted power-of-two row:
/// the vertex has trace one and the punctured `G_m`-torsor has alternating
/// trace zero.  Frobenius changes the fibre trace from zero to `2^r-1`, so no
/// Frobenius-weighted cancellation is certified.
///
/// # Errors
///
/// Declines degrees below five (where Sawin's strict top-cohomology hypothesis
/// is not available), degrees above the caller's explicit Foulkes
/// limit, arithmetic overflow, or a failed endpoint/fixed-locus invariant.
pub fn sawin_long_cycle_euler_report(
    degree: usize,
    limits: SawinFoulkesLimits,
) -> Result<SawinLongCycleEulerReport, HayesError> {
    if degree < 5 {
        return Err(HayesError::InvalidParameter(
            "Sawin long-cycle Euler report requires degree at least five".to_owned(),
        ));
    }
    if degree > limits.max_degree {
        return Err(HayesError::ResourceLimit {
            resource: "sawin_long_cycle_fixed_locus_degree",
            requested: degree,
            limit: limits.max_degree,
        });
    }

    let ell = degree.div_ceil(2).checked_sub(1).ok_or_else(|| {
        HayesError::InvalidParameter("Sawin long-cycle endpoint level underflow".to_owned())
    })?;
    let interval_dimension = degree.checked_sub(ell).ok_or_else(|| {
        HayesError::InvalidParameter("Sawin long-cycle interval underflow".to_owned())
    })?;
    let first_odd_binomial_index =
        1_usize
            .checked_shl(degree.trailing_zeros())
            .ok_or_else(|| {
                HayesError::InvalidParameter(
                    "Sawin long-cycle lowest-set-bit computation overflow".to_owned(),
                )
            })?;
    let has_active_odd_binomial_constraint = first_odd_binomial_index <= ell;
    let full_cycle_fixed_locus_dimension = usize::from(!has_active_odd_binomial_constraint);
    let expected_affine_line = degree.is_power_of_two();
    if (full_cycle_fixed_locus_dimension == 1) != expected_affine_line {
        return Err(HayesError::Invariant(
            "Sawin long-cycle fixed-locus classification failed".to_owned(),
        ));
    }

    let wild_cycle_order = first_odd_binomial_index;
    let tame_cycle_order = degree / wild_cycle_order;
    let cycle_trace_reduced_to_point = tame_cycle_order > 1;
    let tame_fixed_locus_dimension = if cycle_trace_reduced_to_point {
        0
    } else {
        interval_dimension
    };
    if cycle_trace_reduced_to_point && ell < wild_cycle_order {
        return Err(HayesError::Invariant(
            "Sawin tame fixed locus lacks enough triangular constraints".to_owned(),
        ));
    }

    let top_compact_cohomology_degree = interval_dimension.checked_mul(2).ok_or_else(|| {
        HayesError::InvalidParameter("Sawin top cohomology degree overflow".to_owned())
    })?;
    let sawin_singular_offset = degree / 2 - ell / 2 + 1;
    if sawin_singular_offset >= interval_dimension {
        return Err(HayesError::Invariant(
            "Sawin strict top-cohomology hypothesis failed".to_owned(),
        ));
    }
    let fixed_locus_compact_euler_characteristic = 1_i8;
    let top_cycle_trace = 1_i8;
    let cone_vertex_cycle_trace = 1_i8;
    let punctured_cone_alternating_cycle_trace = 0_i8;
    let total_alternating_cycle_trace = cone_vertex_cycle_trace
        .checked_add(punctured_cone_alternating_cycle_trace)
        .ok_or_else(|| HayesError::Invariant("Sawin cone Euler trace overflow".to_owned()))?;
    let non_top_alternating_cycle_trace = total_alternating_cycle_trace
        .checked_sub(top_cycle_trace)
        .ok_or_else(|| HayesError::Invariant("Sawin non-top trace underflow".to_owned()))?;

    Ok(SawinLongCycleEulerReport {
        degree,
        ell,
        interval_dimension,
        first_odd_binomial_index,
        has_active_odd_binomial_constraint,
        full_cycle_fixed_locus_dimension,
        fixed_locus_compact_euler_characteristic,
        wild_cycle_order,
        tame_cycle_order,
        tame_fixed_locus_dimension,
        cycle_trace_reduced_to_point,
        cone_vertex_cycle_trace,
        punctured_cone_alternating_cycle_trace,
        power_sum_value_on_long_cycle: degree,
        long_cycle_centralizer_order: degree,
        power_sum_projection_scalar: 1,
        top_compact_cohomology_degree,
        top_cycle_trace,
        total_alternating_cycle_trace,
        non_top_alternating_cycle_trace,
        binary_frobenius_projective_trace_factor: 1,
        frobenius_weighted_cancellation_certified: false,
    })
}

/// Certify the full-cycle eigenlines contained in the projective endpoint
/// fibre and reject a free cyclic quotient.
///
/// This operation deliberately distinguishes affine fixed vectors from
/// projective fixed lines.  It reuses the checked tame/wild factorization in
/// [`sawin_long_cycle_euler_report`].  The reduced fixed-point count is the
/// number of primitive roots of the odd part `b` of `n`.  For every divisor
/// `e|b`, it checks the endpoint inequality `e*2^a>ell` exactly when `e=b`.
///
/// # Errors
///
/// Declines exactly when the underlying long-cycle report declines, or when
/// an endpoint/eigenvalue invariant fails.
pub fn sawin_projective_eigenline_report(
    degree: usize,
    limits: SawinFoulkesLimits,
) -> Result<SawinProjectiveEigenlineReport, HayesError> {
    let euler = sawin_long_cycle_euler_report(degree, limits)?;
    if degree != euler.wild_cycle_order * euler.tame_cycle_order {
        return Err(HayesError::Invariant(
            "Sawin projective eigenline factorization failed".to_owned(),
        ));
    }

    let tame_factors = factor_usize(euler.tame_cycle_order);
    let tame_divisors = divisors_from_factorization(&tame_factors)?;
    let mut surviving_orders = Vec::new();
    for order in tame_divisors {
        let first_nonzero_index = order.checked_mul(euler.wild_cycle_order).ok_or_else(|| {
            HayesError::InvalidParameter(
                "Sawin projective eigenline coefficient index overflow".to_owned(),
            )
        })?;
        if first_nonzero_index > euler.ell {
            surviving_orders.push(order);
        }
    }
    let eigenline_root_polynomial_has_endpoint_shape =
        surviving_orders == vec![euler.tame_cycle_order];
    if !eigenline_root_polynomial_has_endpoint_shape {
        return Err(HayesError::Invariant(
            "Sawin projective eigenline endpoint shape failed".to_owned(),
        ));
    }
    let primitive_tame_eigenvalue_count = euler_phi_usize(euler.tame_cycle_order, &tame_factors)?;
    let reduced_projective_fixed_point_count = primitive_tame_eigenvalue_count;
    let projective_fixed_scheme_reduced_certified = euler.wild_cycle_order == 1;
    let tame_projective_euler_trace =
        projective_fixed_scheme_reduced_certified.then_some(reduced_projective_fixed_point_count);
    let (
        tame_eigenline_jacobian_rank,
        tame_affine_tangent_dimension,
        tame_projective_tangent_dimension,
        tame_projective_tangent_weight_exponents,
        tame_projective_normal_weight_exponents,
        tame_eigenline_local_status,
    ) = if projective_fixed_scheme_reduced_certified {
        let affine_tangent_dimension = degree.checked_sub(euler.ell).ok_or_else(|| {
            HayesError::Invariant("Sawin tame tangent dimension underflow".to_owned())
        })?;
        let projective_tangent_dimension =
            affine_tangent_dimension.checked_sub(1).ok_or_else(|| {
                HayesError::Invariant("Sawin tame projective tangent underflow".to_owned())
            })?;
        let tangent_weights = (1..affine_tangent_dimension).collect::<Vec<_>>();
        let normal_weights = (affine_tangent_dimension..degree).collect::<Vec<_>>();
        if tangent_weights.len() != projective_tangent_dimension
            || normal_weights.len() != euler.ell
            || tangent_weights
                .iter()
                .chain(normal_weights.iter())
                .copied()
                .ne(1..degree)
        {
            return Err(HayesError::Invariant(
                "Sawin tame tangent-weight partition failed".to_owned(),
            ));
        }
        (
            Some(euler.ell),
            Some(affine_tangent_dimension),
            Some(projective_tangent_dimension),
            tangent_weights,
            normal_weights,
            SawinTameEigenlineLocalStatus::SmoothTransverse,
        )
    } else {
        (
            None,
            None,
            None,
            Vec::new(),
            Vec::new(),
            SawinTameEigenlineLocalStatus::NotCertifiedWild,
        )
    };

    Ok(SawinProjectiveEigenlineReport {
        degree,
        ell: euler.ell,
        wild_cycle_order: euler.wild_cycle_order,
        tame_cycle_order: euler.tame_cycle_order,
        primitive_tame_eigenvalue_count,
        reduced_projective_fixed_point_count,
        projective_fixed_scheme_reduced_certified,
        tame_projective_euler_trace,
        tame_eigenline_jacobian_rank,
        tame_affine_tangent_dimension,
        tame_projective_tangent_dimension,
        tame_projective_tangent_weight_exponents,
        tame_projective_normal_weight_exponents,
        tame_eigenline_local_status,
        projective_long_cycle_action_free: false,
        frobenius_weighted_trace_bound_certified: false,
    })
}

/// Certify that the odd-endpoint projective `Frob*c` fixed locus has no
/// repeated-root or singular local terms.
///
/// For a proper orbit degree `e|n`, oddness of `n` makes the multiplicity
/// `n/e` odd.  Its first `e` powered coefficients recover the monic base
/// polynomial triangularly.  Since every proper divisor of an odd `n` is at
/// most `n/3<=ell-1`, the endpoint zero prefix forces that base polynomial to
/// be `x^e`, hence the full tuple is the cone vertex.  All projective fixed
/// points consequently have `n` distinct coordinates.  The endpoint
/// Jacobian is Vandermonde there, and the zero differential of Frobenius makes
/// the fixed-point intersections transverse with local term one.
///
/// This is a local theorem only.  The returned report deliberately leaves the
/// global Frobenius-weighted trace bound uncertified.
///
/// # Errors
///
/// Rejects even degrees, degrees below five, excessive divisor populations,
/// or a failed endpoint/divisor invariant.
pub fn sawin_odd_frobenius_cycle_fixed_locus_report(
    degree: usize,
    limits: SawinFoulkesLimits,
) -> Result<SawinOddFrobeniusCycleFixedLocusReport, HayesError> {
    if degree < 5 || degree.is_multiple_of(2) {
        return Err(HayesError::InvalidParameter(
            "Sawin odd Frobenius-cycle fixed-locus report requires odd degree at least five"
                .to_owned(),
        ));
    }
    let ell = (degree - 1) / 2;
    let divisors = divisors_from_factorization(&factor_usize(degree))?;
    if divisors.len() > limits.max_orthogonality_cells {
        return Err(HayesError::ResourceLimit {
            resource: "sawin_odd_frobenius_cycle_divisors",
            requested: divisors.len(),
            limit: limits.max_orthogonality_cells,
        });
    }
    let proper_orbit_degrees = divisors
        .into_iter()
        .filter(|&divisor| divisor < degree)
        .collect::<Vec<_>>();
    let largest_proper_orbit_degree = proper_orbit_degrees.last().copied().unwrap_or(0);
    let proper_orbit_triangular_recovery_certified = proper_orbit_degrees
        .iter()
        .all(|&e| degree.is_multiple_of(e) && !(degree / e).is_multiple_of(2) && e < ell);
    if !proper_orbit_triangular_recovery_certified {
        return Err(HayesError::Invariant(
            "Sawin odd Frobenius-cycle proper-orbit reduction failed".to_owned(),
        ));
    }

    Ok(SawinOddFrobeniusCycleFixedLocusReport {
        degree,
        ell,
        proper_orbit_degrees,
        largest_proper_orbit_degree,
        proper_orbit_strata_collapse_to_vertex_certified: true,
        nonvertex_exact_orbit_degree_certified: true,
        nonvertex_jacobian_rank: ell,
        projective_local_status: SawinOddFrobeniusCycleLocalStatus::SmoothTransverseUnitTerms,
        frobenius_weighted_trace_bound_certified: false,
    })
}

fn hast_matei_long_cycle_strata(
    degree: usize,
    repeated_root_threshold: usize,
    limits: SawinFoulkesLimits,
) -> Result<Vec<HastMateiLongCycleStratum>, HayesError> {
    let divisors = divisors_from_factorization(&factor_usize(degree))?;
    if divisors.len() > limits.max_orthogonality_cells {
        return Err(HayesError::ResourceLimit {
            resource: "hast_matei_repeated_root_divisors",
            requested: divisors.len(),
            limit: limits.max_orthogonality_cells,
        });
    }
    let mut rows = Vec::new();
    for base_degree in divisors {
        if base_degree == degree || base_degree > repeated_root_threshold {
            continue;
        }
        let multiplicity = degree / base_degree;
        if base_degree * multiplicity != degree {
            return Err(HayesError::Invariant(
                "Hast--Matei divisor does not divide the degree".to_owned(),
            ));
        }
        let frobenius_coefficient_stride = 1_usize
            .checked_shl(multiplicity.trailing_zeros())
            .ok_or_else(|| {
                HayesError::InvalidParameter(
                    "Hast--Matei Frobenius stride calculation overflow".to_owned(),
                )
            })?;
        let odd_multiplicity = multiplicity % 2 == 1;
        rows.push(HastMateiLongCycleStratum {
            base_degree,
            multiplicity,
            frobenius_coefficient_stride,
            odd_multiplicity,
            triangular_base_recovery_certified: odd_multiplicity,
            frobenius_square_stratum: !odd_multiplicity,
        });
    }
    if rows
        .iter()
        .any(|row| !row.triangular_base_recovery_certified && !row.frobenius_square_stratum)
    {
        return Err(HayesError::Invariant(
            "Hast--Matei long-cycle stratum classification failed".to_owned(),
        ));
    }
    Ok(rows)
}

/// Translate Hast--Matei's two-polynomial top weight to the Lemire endpoint
/// and classify the low-characteristic long-cycle repeated-root strata.
///
/// For `h=floor(n/2)` their cutoff is
/// `n-h-2=ell-1`.  An `n`-cycle has nonzero irreducible character only on
/// hooks `(n-j,1^j)`; exactly `ell-1` of those satisfy the cutoff.  Therefore
/// the idealized top-weight global second moment is `(ell-1)2^n`.  Cauchy
/// compares this with the squared class mean `2^(2(n-ell))`, leaving squared
/// ratio `(ell-1)/2^(n-2ell)`, which fails throughout the unresolved range.
///
/// A repeated-root tuple compatible with the long-cycle Frobenius condition
/// has one orbit of degree `e|n` and polynomial `Q^(n/e)`.  For odd
/// multiplicity, the coefficient of `Q` at index `j` occurs with coefficient
/// `n/e=1` modulo two in the index-`j` coefficient of the power, while all
/// other terms use earlier coefficients.  Hence the first `e` coefficients
/// recover `Q` triangularly.  Even multiplicity gives an actual Frobenius
/// square.  This confines the failure of Hast--Matei's characteristic-free
/// fibre argument on the selected long-cycle strata, but does not control the
/// connected fourfold virtual trace.
///
/// # Errors
///
/// Declines degrees below nine (the first endpoint in Hast--Matei's stated
/// `h<=n-5` range), degrees above the caller's explicit limit,
/// arithmetic overflow, or a failed endpoint/divisor invariant.
pub fn hast_matei_long_cycle_endpoint_report(
    degree: usize,
    limits: SawinFoulkesLimits,
) -> Result<HastMateiLongCycleEndpointReport, HayesError> {
    if degree < 9 {
        return Err(HayesError::InvalidParameter(
            "Hast--Matei endpoint report requires degree at least nine".to_owned(),
        ));
    }
    if degree > limits.max_degree {
        return Err(HayesError::ResourceLimit {
            resource: "hast_matei_endpoint_degree",
            requested: degree,
            limit: limits.max_degree,
        });
    }

    let ell = degree.div_ceil(2).checked_sub(1).ok_or_else(|| {
        HayesError::InvalidParameter("Hast--Matei endpoint level underflow".to_owned())
    })?;
    let short_interval_tail_degree = degree
        .checked_sub(ell)
        .and_then(|value| value.checked_sub(1))
        .ok_or_else(|| {
            HayesError::InvalidParameter("Hast--Matei tail degree underflow".to_owned())
        })?;
    if short_interval_tail_degree != degree / 2 {
        return Err(HayesError::Invariant(
            "Hast--Matei endpoint tail is not floor(n/2)".to_owned(),
        ));
    }
    let coefficient_equation_count = degree
        .checked_sub(short_interval_tail_degree)
        .and_then(|value| value.checked_sub(1))
        .ok_or_else(|| {
            HayesError::InvalidParameter("Hast--Matei equation count underflow".to_owned())
        })?;
    if coefficient_equation_count != ell {
        return Err(HayesError::Invariant(
            "Hast--Matei equation count does not equal ell".to_owned(),
        ));
    }
    let repeated_root_threshold = coefficient_equation_count - 1;
    let top_weight_long_cycle_hook_count = repeated_root_threshold;
    let top_weight_frobenius_exponent = degree - 1;
    let top_weight_global_second_moment = BigUint::from(top_weight_long_cycle_hook_count) << degree;
    let class_mean_exponent = degree.checked_sub(ell).ok_or_else(|| {
        HayesError::InvalidParameter("Hast--Matei class mean underflow".to_owned())
    })?;
    let squared_class_mean_exponent = class_mean_exponent.checked_mul(2).ok_or_else(|| {
        HayesError::InvalidParameter("Hast--Matei squared mean overflow".to_owned())
    })?;
    let squared_identity_class_mean = BigUint::from(1_u8) << squared_class_mean_exponent;
    let pointwise_denominator_exponent = degree
        .checked_sub(ell.checked_mul(2).ok_or_else(|| {
            HayesError::InvalidParameter("Hast--Matei endpoint denominator overflow".to_owned())
        })?)
        .ok_or_else(|| {
            HayesError::Invariant("Hast--Matei endpoint denominator is negative".to_owned())
        })?;
    let pointwise_deficit_denominator = BigUint::from(1_u8) << pointwise_denominator_exponent;
    let pointwise_deficit_numerator = top_weight_long_cycle_hook_count;
    let top_weight_second_moment_alone_closes_endpoint =
        BigUint::from(pointwise_deficit_numerator) < pointwise_deficit_denominator;

    let repeated_root_strata =
        hast_matei_long_cycle_strata(degree, repeated_root_threshold, limits)?;

    Ok(HastMateiLongCycleEndpointReport {
        degree,
        ell,
        short_interval_tail_degree,
        coefficient_equation_count,
        repeated_root_threshold,
        top_weight_long_cycle_hook_count,
        top_weight_frobenius_exponent,
        top_weight_global_second_moment,
        squared_identity_class_mean,
        pointwise_deficit_numerator,
        pointwise_deficit_denominator,
        top_weight_second_moment_alone_closes_endpoint,
        repeated_root_strata,
        connected_frobenius_trace_bound_certified: false,
    })
}

fn hamming_weight_masks(degree: usize, weight: usize) -> Result<Vec<usize>, HayesError> {
    if weight == 0 || weight >= degree {
        return Err(HayesError::InvalidParameter(
            "characteristic-delta weight must lie strictly between zero and degree".to_owned(),
        ));
    }
    let domain_end = 1_usize
        .checked_shl(u32::try_from(degree).map_err(|_| {
            HayesError::InvalidParameter("Tuxanidy degree does not fit a machine shift".to_owned())
        })?)
        .ok_or_else(|| {
            HayesError::InvalidParameter("Tuxanidy binary domain overflow".to_owned())
        })?;
    let mut mask = (1_usize << weight) - 1;
    let mut masks = Vec::new();
    while mask < domain_end {
        masks.push(mask);
        let low_bit = mask & mask.wrapping_neg();
        let ripple = mask.checked_add(low_bit).ok_or_else(|| {
            HayesError::InvalidParameter("Tuxanidy mask enumeration overflow".to_owned())
        })?;
        mask = (((ripple ^ mask) >> 2) / low_bit) | ripple;
    }
    Ok(masks)
}

fn lcm_usize_checked(left: usize, right: usize) -> Result<usize, HayesError> {
    left.checked_div(gcd_usize(left, right))
        .and_then(|quotient| quotient.checked_mul(right))
        .ok_or_else(|| HayesError::InvalidParameter("Tuxanidy LCM overflow".to_owned()))
}

struct CharacteristicDeltaConvolution {
    coefficients: Vec<bool>,
    factor_support_sizes: Vec<usize>,
    cells: usize,
}

struct ExactDegreeDifferenceCertificate {
    maximal_proper_subfield_periods: Vec<usize>,
    support_size: usize,
    first_witness: Option<usize>,
    criterion_holds: bool,
    period_criterion_relation: TuxanidyPeriodCriterionRelation,
    total_cells: usize,
}

fn exact_degree_difference_certificate(
    degree: usize,
    cyclic_order: usize,
    coefficients: &[bool],
    base_cells: usize,
    maximum_cells: usize,
) -> Result<ExactDegreeDifferenceCertificate, HayesError> {
    let degree_factors = factor_usize(degree);
    let maximal_proper_subfield_periods = degree_factors
        .iter()
        .map(|&(prime, _)| {
            1_usize
                .checked_shl(u32::try_from(degree / prime).map_err(|_| {
                    HayesError::InvalidParameter(
                        "Tuxanidy maximal-subfield shift overflow".to_owned(),
                    )
                })?)
                .and_then(|value| value.checked_sub(1))
                .ok_or_else(|| {
                    HayesError::InvalidParameter(
                        "Tuxanidy maximal-subfield period overflow".to_owned(),
                    )
                })
        })
        .collect::<Result<Vec<_>, HayesError>>()?;
    let difference_cells = cyclic_order
        .checked_mul(maximal_proper_subfield_periods.len())
        .ok_or_else(|| {
            HayesError::InvalidParameter("Tuxanidy difference work overflow".to_owned())
        })?;
    let total_cells = base_cells
        .checked_add(difference_cells)
        .ok_or_else(|| HayesError::InvalidParameter("Tuxanidy total work overflow".to_owned()))?;
    if total_cells > maximum_cells {
        return Err(HayesError::ResourceLimit {
            resource: "tuxanidy_period_convolution_cells",
            requested: total_cells,
            limit: maximum_cells,
        });
    }

    let mut difference = coefficients.to_vec();
    let mut scratch = vec![false; cyclic_order];
    for &period in &maximal_proper_subfield_periods {
        for (index, output) in scratch.iter_mut().enumerate() {
            *output = difference[index] ^ difference[(index + period) % cyclic_order];
        }
        std::mem::swap(&mut difference, &mut scratch);
    }
    let support_size = difference.iter().filter(|present| **present).count();
    let first_witness = difference.iter().position(|present| *present);
    let period_criterion_relation = if degree_factors.len() == 1 {
        TuxanidyPeriodCriterionRelation::ExactPrimePowerDegree
    } else {
        TuxanidyPeriodCriterionRelation::SufficientOnlyMixedDivisorDegree
    };
    Ok(ExactDegreeDifferenceCertificate {
        maximal_proper_subfield_periods,
        support_size,
        first_witness,
        criterion_holds: support_size != 0,
        period_criterion_relation,
        total_cells,
    })
}

fn tuxanidy_proper_subfield_exponent(
    degree: usize,
    cyclic_order: usize,
) -> Result<usize, HayesError> {
    let mut exponent = 1_usize;
    for divisor in positive_divisors(degree)
        .into_iter()
        .filter(|divisor| *divisor != degree)
    {
        let subfield_order = 1_usize
            .checked_shl(u32::try_from(divisor).map_err(|_| {
                HayesError::InvalidParameter("Tuxanidy subfield shift overflow".to_owned())
            })?)
            .and_then(|value| value.checked_sub(1))
            .ok_or_else(|| {
                HayesError::InvalidParameter("Tuxanidy subfield order overflow".to_owned())
            })?;
        exponent = lcm_usize_checked(exponent, subfield_order)?;
    }
    if !cyclic_order.is_multiple_of(exponent) || exponent >= cyclic_order {
        return Err(HayesError::Invariant(
            "Tuxanidy proper-subfield exponent is not a proper divisor".to_owned(),
        ));
    }
    Ok(exponent)
}

fn characteristic_delta_convolution(
    degree: usize,
    maximum_weight: usize,
    cyclic_order: usize,
    maximum_cells: usize,
) -> Result<CharacteristicDeltaConvolution, HayesError> {
    let mut convolution = vec![false; cyclic_order];
    convolution[0] = true;
    let mut support_size = 1_usize;
    let mut cells = 0_usize;
    let mut factor_support_sizes = Vec::with_capacity(maximum_weight);

    for weight in 1..=maximum_weight {
        let mut factor = hamming_weight_masks(degree, weight)?;
        factor.push(0);
        factor.sort_unstable();
        if factor.windows(2).any(|pair| pair[0] == pair[1]) {
            return Err(HayesError::Invariant(
                "Tuxanidy characteristic-delta factor has duplicate support".to_owned(),
            ));
        }
        factor_support_sizes.push(factor.len());
        let step_cells = support_size.checked_mul(factor.len()).ok_or_else(|| {
            HayesError::InvalidParameter("Tuxanidy convolution work overflow".to_owned())
        })?;
        cells = cells.checked_add(step_cells).ok_or_else(|| {
            HayesError::InvalidParameter("Tuxanidy convolution work overflow".to_owned())
        })?;
        if cells > maximum_cells {
            return Err(HayesError::ResourceLimit {
                resource: "tuxanidy_period_convolution_cells",
                requested: cells,
                limit: maximum_cells,
            });
        }

        let mut next = vec![false; cyclic_order];
        for (left, present) in convolution.iter().copied().enumerate() {
            if present {
                for right in factor.iter().copied() {
                    let raw = left.checked_add(right).ok_or_else(|| {
                        HayesError::InvalidParameter("Tuxanidy cyclic sum overflow".to_owned())
                    })?;
                    let slot = if raw >= cyclic_order {
                        raw - cyclic_order
                    } else {
                        raw
                    };
                    next[slot] = !next[slot];
                }
            }
        }
        support_size = next.iter().filter(|present| **present).count();
        convolution = next;
    }

    Ok(CharacteristicDeltaConvolution {
        coefficients: convolution,
        factor_support_sizes,
        cells,
    })
}

/// Compute the exact Tuxanidy--Wang least-period diagnostic for the Lemire
/// coefficient class.
///
/// Over `GF(2)`, the function `1+sigma_j(alpha)` is the indicator that the
/// `j`-th leading coefficient of the degree-`n` characteristic polynomial of
/// `alpha` vanishes.  Its inverse DFT is `delta_0+delta_j`; multiplying these
/// indicators therefore gives the cyclic convolution retained here.  By the
/// Tuxanidy--Wang support criterion, a period not dividing
/// `lcm_(d|n,d<n)(2^d-1)` forces the common zero set to contain an element of
/// exact degree `n`, whose minimal polynomial is the required irreducible.
/// More sharply, multiplying the Fourier transform by
/// `product_(p|n)(1+alpha^(2^(n/p)-1))` removes exactly the union of maximal
/// proper subfields.  On the group-algebra side this is the iterated
/// translation difference reported by this operation.
///
/// The implication is a general algebraic theorem.  This operation computes
/// only one bounded row and deliberately does not certify that either the
/// maximum-period pattern or the weaker exact difference is nonzero for every
/// degree.
///
/// # Errors
///
/// Declines degrees below three, degrees or cyclic domains above the caller's
/// limits, a convolution exceeding the admitted exact cell count, arithmetic
/// overflow, or an internal period/factor invariant failure.
pub fn tuxanidy_lemire_period_report(
    degree: usize,
    limits: TuxanidyPeriodLimits,
) -> Result<TuxanidyLemirePeriodReport, HayesError> {
    if degree < 3 {
        return Err(HayesError::InvalidParameter(
            "Tuxanidy--Lemire period report requires degree at least three".to_owned(),
        ));
    }
    if degree > limits.max_degree {
        return Err(HayesError::ResourceLimit {
            resource: "tuxanidy_period_degree",
            requested: degree,
            limit: limits.max_degree,
        });
    }
    let shift = u32::try_from(degree).map_err(|_| {
        HayesError::InvalidParameter("Tuxanidy degree does not fit a machine shift".to_owned())
    })?;
    let cyclic_order = 1_usize
        .checked_shl(shift)
        .and_then(|value| value.checked_sub(1))
        .ok_or_else(|| HayesError::InvalidParameter("Tuxanidy cyclic order overflow".to_owned()))?;
    if cyclic_order > limits.max_cyclic_order {
        return Err(HayesError::ResourceLimit {
            resource: "tuxanidy_period_cyclic_order",
            requested: cyclic_order,
            limit: limits.max_cyclic_order,
        });
    }
    let ell = degree.div_ceil(2) - 1;
    let convolution =
        characteristic_delta_convolution(degree, ell, cyclic_order, limits.max_convolution_cells)?;

    let least_period = positive_divisors(cyclic_order)
        .into_iter()
        .find(|period| {
            convolution
                .coefficients
                .iter()
                .copied()
                .enumerate()
                .all(|(index, value)| {
                    value == convolution.coefficients[(index + period) % cyclic_order]
                })
        })
        .ok_or_else(|| {
            HayesError::Invariant("Tuxanidy convolution has no cyclic period".to_owned())
        })?;
    if cyclic_order % least_period != 0 {
        return Err(HayesError::Invariant(
            "Tuxanidy least period does not divide the cyclic order".to_owned(),
        ));
    }

    let proper_subfield_exponent_lcm = tuxanidy_proper_subfield_exponent(degree, cyclic_order)?;
    let period_criterion_holds = !proper_subfield_exponent_lcm.is_multiple_of(least_period);

    let exact_degree = exact_degree_difference_certificate(
        degree,
        cyclic_order,
        &convolution.coefficients,
        convolution.cells,
        limits.max_convolution_cells,
    )?;
    if period_criterion_holds && !exact_degree.criterion_holds {
        return Err(HayesError::Invariant(
            "Tuxanidy period criterion does not imply the exact-degree difference".to_owned(),
        ));
    }
    if exact_degree.period_criterion_relation
        == TuxanidyPeriodCriterionRelation::ExactPrimePowerDegree
        && period_criterion_holds != exact_degree.criterion_holds
    {
        return Err(HayesError::Invariant(
            "prime-power period and exact-degree criteria disagree".to_owned(),
        ));
    }

    Ok(TuxanidyLemirePeriodReport {
        degree,
        ell,
        cyclic_order,
        factor_support_sizes: convolution.factor_support_sizes,
        convolution_support_size: convolution
            .coefficients
            .iter()
            .filter(|present| **present)
            .count(),
        least_period,
        proper_subfield_exponent_lcm,
        maximal_proper_subfield_periods: exact_degree.maximal_proper_subfield_periods,
        exact_degree_difference_support_size: exact_degree.support_size,
        first_exact_degree_difference_witness: exact_degree.first_witness,
        maximum_least_period: least_period == cyclic_order,
        period_criterion_holds,
        period_criterion_relation: exact_degree.period_criterion_relation,
        theorem_boundary:
            TuxanidyPeriodTheoremBoundary::ExactDegreeDifferenceCertifiedUniversalNonvanishingOpen,
        convolution_cells: exact_degree.total_cells,
    })
}

fn biguint_binomial(n: usize, k: usize) -> BigUint {
    if k > n {
        return BigUint::from(0_u8);
    }
    let k = k.min(n - k);
    let mut value = BigUint::from(1_u8);
    for index in 1..=k {
        value *= n - k + index;
        value /= index;
    }
    value
}

fn wan_zhang_endpoint_betti_cost(
    degree: usize,
    ell: usize,
    coefficient_l1_mass: &BigUint,
    sawin_weight_exponent_numerator: usize,
    squared_irreducible_margin: &BigUint,
) -> Result<(BigUint, BigUint, bool), HayesError> {
    let exponent = u32::try_from(degree).map_err(|_| {
        HayesError::InvalidParameter("Wan--Zhang Betti exponent exceeds u32".to_owned())
    })?;
    let bound = biguint_binomial(degree - 1, ell - 1) * BigUint::from(ell + 1).pow(exponent);
    let total_cost = coefficient_l1_mass * &bound;
    let squared_total_cost = &total_cost * &total_cost;
    let squared_error = &squared_total_cost << sawin_weight_exponent_numerator;
    let closes = squared_error < *squared_irreducible_margin;
    Ok((bound, squared_total_cost, closes))
}

struct ExistingSawinBettiCosts {
    generic_bound: BigUint,
    generic_squared_total_cost: BigUint,
    generic_closes: bool,
    wan_zhang_bound: BigUint,
    wan_zhang_squared_total_cost: BigUint,
    wan_zhang_closes: bool,
}

fn existing_sawin_betti_costs(
    degree: usize,
    ell: usize,
    coefficient_l1_mass: &BigUint,
    sawin_weight_exponent_numerator: usize,
    squared_irreducible_margin: &BigUint,
) -> Result<ExistingSawinBettiCosts, HayesError> {
    let generic_exponent = u32::try_from(degree.checked_add(ell).ok_or_else(|| {
        HayesError::InvalidParameter("Sawin generic Betti exponent overflow".to_owned())
    })?)
    .map_err(|_| {
        HayesError::InvalidParameter("Sawin generic Betti exponent exceeds u32".to_owned())
    })?;
    let generic_bound = BigUint::from(3_u8) * BigUint::from(degree + 2).pow(generic_exponent);
    let generic_total_cost = coefficient_l1_mass * &generic_bound;
    let generic_squared_total_cost = &generic_total_cost * &generic_total_cost;
    let generic_squared_error = &generic_squared_total_cost << sawin_weight_exponent_numerator;
    let (wan_zhang_bound, wan_zhang_squared_total_cost, wan_zhang_closes) =
        wan_zhang_endpoint_betti_cost(
            degree,
            ell,
            coefficient_l1_mass,
            sawin_weight_exponent_numerator,
            squared_irreducible_margin,
        )?;
    Ok(ExistingSawinBettiCosts {
        generic_bound,
        generic_squared_total_cost,
        generic_closes: generic_squared_error < *squared_irreducible_margin,
        wan_zhang_bound,
        wan_zhang_squared_total_cost,
        wan_zhang_closes,
    })
}

/// Certify the cyclic/Foulkes long-cycle identity and evaluate its exact
/// Lemire endpoint margin under a hypothetical cyclic Betti bound.
///
/// For `ell=ceil(n/2)-1`, Sawin's characteristic-two weight exponent has
/// numerator
///
/// ```text
/// W=(n-ell)+floor(n/2)-floor(ell/2)+1
///   =2(n-ell)-floor(ell/2).
/// ```
///
/// Hence squaring the comparison with the main term leaves precisely
/// `2^floor(ell/2)`.  If every cyclic eigenspace had total Betti multiplicity
/// at most `B`, the Foulkes triangle proves an irreducible exactly when
///
/// ```text
/// (2^omega(n) B)^2 2^W < (2^h-P_n)^2,
/// ```
///
/// where `P_n=1` at the odd endpoint and the even endpoint uses the proved
/// square/higher-power envelope.  The function checks this implication and
/// also inserts Sawin's published generic bound and Wan--Zhang's sharper 2026
/// complete-intersection bound to demonstrate whether existing geometry
/// suffices.  It does not establish the caller-supplied `B`.
///
/// # Errors
///
/// Declines degrees below the asymptotic endpoint range, a zero hypothetical
/// bound, resource-limit violations, arithmetic overflow, or any failed
/// Ramanujan orthogonality/coefficient-mass invariant.
pub fn sawin_foulkes_endpoint_ledger(
    degree: usize,
    assumed_uniform_cyclic_betti_bound: BigUint,
    limits: SawinFoulkesLimits,
) -> Result<SawinFoulkesEndpointLedger, HayesError> {
    if degree < 3 {
        return Err(HayesError::InvalidParameter(
            "Sawin/Foulkes endpoint ledger requires degree at least three".to_owned(),
        ));
    }
    if assumed_uniform_cyclic_betti_bound == BigUint::from(0_u8) {
        return Err(HayesError::InvalidParameter(
            "Sawin/Foulkes hypothetical Betti bound must be positive".to_owned(),
        ));
    }
    let FoulkesCompressionCertificate {
        coefficient_denominator,
        distinct_prime_factor_count,
        coefficients,
        distinct_coefficients,
        reconstructed_power_sum_coefficients,
        coefficient_l1_numerator,
        coefficient_l1_mass,
    } = certify_foulkes_compression(degree, limits)?;

    let ell = degree.div_ceil(2).checked_sub(1).ok_or_else(|| {
        HayesError::InvalidParameter("Sawin/Foulkes endpoint level underflow".to_owned())
    })?;
    let interval_dimension = degree.checked_sub(ell).ok_or_else(|| {
        HayesError::InvalidParameter("Sawin/Foulkes interval dimension underflow".to_owned())
    })?;
    let sawin_weight_exponent_numerator = interval_dimension
        .checked_add(degree / 2)
        .and_then(|value| value.checked_sub(ell / 2))
        .and_then(|value| value.checked_add(1))
        .ok_or_else(|| HayesError::InvalidParameter("Sawin weight exponent overflow".to_owned()))?;
    let twice_interval_dimension = interval_dimension.checked_mul(2).ok_or_else(|| {
        HayesError::InvalidParameter("Sawin squared main exponent overflow".to_owned())
    })?;
    let squared_exponential_margin_exponent = twice_interval_dimension
        .checked_sub(sawin_weight_exponent_numerator)
        .ok_or_else(|| HayesError::Invariant("Sawin endpoint margin is negative".to_owned()))?;
    if squared_exponential_margin_exponent != ell / 2 {
        return Err(HayesError::Invariant(
            "Sawin endpoint margin does not simplify to floor(ell/2)".to_owned(),
        ));
    }
    let squared_exponential_margin = BigUint::from(1_u8) << squared_exponential_margin_exponent;
    let assumed_total_cost = &coefficient_l1_mass * &assumed_uniform_cyclic_betti_bound;
    let assumed_squared_total_cost = &assumed_total_cost * &assumed_total_cost;
    let assumed_squared_absolute_error =
        &assumed_squared_total_cost << sawin_weight_exponent_numerator;
    let main_mangoldt_term = BigUint::from(1_u8) << interval_dimension;
    let proper_prime_power_upper_bound = endpoint_proper_prime_power_upper_bound(degree, ell)?;
    let irreducible_margin = if proper_prime_power_upper_bound < main_mangoldt_term {
        &main_mangoldt_term - &proper_prime_power_upper_bound
    } else {
        BigUint::from(0_u8)
    };
    let squared_irreducible_margin = &irreducible_margin * &irreducible_margin;
    let conditional_endpoint_closure = assumed_squared_absolute_error < squared_irreducible_margin;

    let existing_betti = existing_sawin_betti_costs(
        degree,
        ell,
        &coefficient_l1_mass,
        sawin_weight_exponent_numerator,
        &squared_irreducible_margin,
    )?;

    Ok(SawinFoulkesEndpointLedger {
        degree,
        ell,
        interval_dimension,
        fixed_leading_coefficient_count: ell,
        sawin_weight_exponent_numerator,
        squared_exponential_margin_exponent,
        coefficient_denominator,
        distinct_prime_factor_count,
        coefficients,
        distinct_coefficients,
        reconstructed_power_sum_coefficients,
        coefficient_l1_numerator,
        coefficient_l1_mass,
        assumed_uniform_cyclic_betti_bound,
        assumed_squared_total_cost,
        squared_exponential_margin,
        main_mangoldt_term,
        proper_prime_power_upper_bound,
        irreducible_margin,
        assumed_squared_absolute_error,
        squared_irreducible_margin,
        conditional_endpoint_closure,
        published_generic_single_betti_bound: existing_betti.generic_bound,
        published_generic_squared_total_cost: existing_betti.generic_squared_total_cost,
        published_generic_endpoint_closure: existing_betti.generic_closes,
        wan_zhang_complete_intersection_betti_bound: existing_betti.wan_zhang_bound,
        wan_zhang_squared_total_cost: existing_betti.wan_zhang_squared_total_cost,
        wan_zhang_endpoint_closure: existing_betti.wan_zhang_closes,
    })
}

/// Check that a polynomial cyclic-Foulkes Betti bound closes every endpoint
/// after a finite handoff.
///
/// Since every distinct prime divisor is at least two,
/// `2^omega(n)<=rad(n)<=n`.  Under `B(n,r)<=n^a`, the squared Foulkes cost is
/// therefore at most `n^(2(a+1))`.  Reserving half of the main term for proper
/// prime powers leaves the normalized squared error allowance
///
/// ```text
/// 2^(floor((ceil(n/2)-1)/2)-2).
/// ```
///
/// All floor/ceiling patterns repeat when `n` increases by twelve.  The error
/// allowance then grows by eight, while its polynomial ratio decreases.  For
/// proper powers, the odd contribution remains one; at the even endpoint both
/// the square term and the surviving even-exponent higher-power term grow by
/// less than `16`, while half the main term grows by `64`.  Twelve base rows plus the
/// checked polynomial step therefore prove the arithmetic implication for all
/// `n` at or above `threshold`.  This function does not prove the polynomial
/// Betti assumption itself.
///
/// # Errors
///
/// Returns an error if parameters overflow or any strict base/step inequality
/// fails.
pub fn check_sawin_foulkes_polynomial_betti_sufficiency(
    assumption: SawinFoulkesPolynomialBettiAssumption,
) -> Result<SawinFoulkesPolynomialBettiReport, HayesError> {
    if assumption.threshold < 13 {
        return Err(HayesError::InvalidParameter(
            "Sawin/Foulkes polynomial implication requires threshold at least thirteen".to_owned(),
        ));
    }
    let squared_polynomial_power = assumption
        .polynomial_power
        .checked_add(1)
        .and_then(|value| value.checked_mul(2))
        .ok_or_else(|| {
            HayesError::InvalidParameter(
                "Sawin/Foulkes polynomial implication exponent overflow".to_owned(),
            )
        })?;
    let last_base = assumption.threshold.checked_add(11).ok_or_else(|| {
        HayesError::InvalidParameter("Sawin/Foulkes base block overflow".to_owned())
    })?;
    let mut base_rows = Vec::with_capacity(12);
    for degree in assumption.threshold..=last_base {
        let ell = degree.div_ceil(2) - 1;
        let squared_polynomial_cost = BigUint::from(degree).pow(squared_polynomial_power);
        let half_margin_exponent = (ell / 2).checked_sub(2).ok_or_else(|| {
            HayesError::InvalidParameter(
                "Sawin/Foulkes half-main squared margin underflow".to_owned(),
            )
        })?;
        let squared_half_main_margin = BigUint::from(1_u8) << half_margin_exponent;
        if squared_polynomial_cost >= squared_half_main_margin {
            return Err(HayesError::InvalidParameter(format!(
                "Sawin/Foulkes polynomial implication fails at base degree {degree}"
            )));
        }
        let interval_dimension = degree - ell;
        let half_main_mangoldt_term = BigUint::from(1_u8) << (interval_dimension - 1);
        let proper_prime_power_upper_bound = endpoint_proper_prime_power_upper_bound(degree, ell)?;
        if proper_prime_power_upper_bound >= half_main_mangoldt_term {
            return Err(HayesError::InvalidParameter(format!(
                "Sawin/Foulkes proper-power reserve fails at base degree {degree}"
            )));
        }
        base_rows.push(SawinFoulkesPolynomialBaseRow {
            degree,
            squared_polynomial_cost,
            squared_half_main_margin,
            proper_prime_power_upper_bound,
            half_main_mangoldt_term,
        });
    }

    let next_degree = assumption.threshold.checked_add(12).ok_or_else(|| {
        HayesError::InvalidParameter("Sawin/Foulkes induction step overflow".to_owned())
    })?;
    let step_left = BigUint::from(next_degree).pow(squared_polynomial_power);
    let step_right =
        BigUint::from(8_u8) * BigUint::from(assumption.threshold).pow(squared_polynomial_power);
    if step_left >= step_right {
        return Err(HayesError::InvalidParameter(
            "Sawin/Foulkes polynomial implication induction step is not strict".to_owned(),
        ));
    }

    Ok(SawinFoulkesPolynomialBettiReport {
        assumption,
        squared_polynomial_power,
        base_rows,
        step_left,
        step_right,
    })
}

/// Check that a constant-one exact-conductor estimate implies endpoint positivity.
///
/// The even endpoint uses the class restriction on the square proper-divisor
/// term: if `n = 2m`, then `<P>^2 = 1 (mod x^(ell+1))` fixes the first
/// `floor(ell/2)` coefficients of `P`.  This replaces the coarse `2^m`
/// estimate by `m * 2^(m-floor(ell/2))`.  All remaining proper-divisor terms
/// are bounded by `n * 2^ceil(n/3)`.
///
/// This function proves only the arithmetic implication. It does not prove
/// `T_(j,n)^2 <= 2^(2j-2+n)`.
///
/// # Errors
///
/// Returns an error for malformed rational witnesses, a gap before the
/// finite range, or a failed exact seed/monotonicity inequality.
pub fn check_square_root_layer_bound_sufficiency(
    assumption: SquareRootLayerBoundAssumption,
) -> Result<SquareRootLayerBoundReport, HayesError> {
    let SquareRootLayerBoundAssumption {
        threshold,
        finite_max_degree,
        sqrt_two_upper_numerator: numerator,
        sqrt_two_upper_denominator: denominator,
    } = assumption;
    if threshold < 4 || numerator == 0 || denominator == 0 {
        return Err(HayesError::InvalidParameter(
            "threshold must be at least four and the rational witness must be positive".to_owned(),
        ));
    }
    let twice_threshold = threshold.checked_mul(2).ok_or_else(|| {
        HayesError::InvalidParameter("threshold degree calculation overflow".to_owned())
    })?;
    if twice_threshold > finite_max_degree {
        return Err(HayesError::InvalidParameter(
            "finite remainder exceeds the checked degree range".to_owned(),
        ));
    }
    let numerator_big = BigUint::from(numerator);
    let denominator_big = BigUint::from(denominator);
    if &numerator_big * &numerator_big <= BigUint::from(2_u8) * &denominator_big * &denominator_big
    {
        return Err(HayesError::InvalidParameter(
            "rational witness is not a strict upper bound for sqrt(2)".to_owned(),
        ));
    }
    let twice_denominator = denominator.checked_mul(2).ok_or_else(|| {
        HayesError::InvalidParameter("rational witness calculation overflow".to_owned())
    })?;
    let odd_margin_numerator = twice_denominator.checked_sub(numerator).ok_or_else(|| {
        HayesError::InvalidParameter("sqrt(2) upper bound must be smaller than two".to_owned())
    })?;
    if odd_margin_numerator == 0 {
        return Err(HayesError::InvalidParameter(
            "sqrt(2) upper bound must be smaller than two".to_owned(),
        ));
    }

    // Increasing ell by three multiplies the coarse proper-divisor
    // exponential by four and the endpoint margin by eight.  These three
    // residue-class seeds therefore cover every later odd endpoint.
    for ell in threshold..threshold + 3 {
        let degree = ell
            .checked_mul(2)
            .and_then(|value| value.checked_add(1))
            .ok_or_else(|| {
                HayesError::InvalidParameter("odd endpoint calculation overflow".to_owned())
            })?;
        let proper = BigUint::from(degree) << degree.div_ceil(3);
        let left = BigUint::from(denominator) * proper;
        let right = BigUint::from(odd_margin_numerator) << ell;
        if left >= right {
            return Err(HayesError::Invariant(
                "odd proper-divisor seed does not fit the family-bound margin".to_owned(),
            ));
        }
        if degree <= 6 {
            return Err(HayesError::Invariant(
                "odd proper-divisor monotonicity has not started".to_owned(),
            ));
        }
    }

    // At an even endpoint, reserve one 2^ell half-margin for the square
    // term and one for all exponents k >= 3.  Two and three seeds cover the
    // respective parity and residue recurrences.
    for ell in threshold..threshold + 2 {
        let half_degree = ell + 1;
        let fixed_coefficients = ell / 2;
        let square_term = BigUint::from(half_degree) << (half_degree - fixed_coefficients);
        if square_term >= (BigUint::from(1_u8) << ell) {
            return Err(HayesError::Invariant(
                "even square proper-divisor seed exceeds its half-margin".to_owned(),
            ));
        }
        if half_degree <= 2 {
            return Err(HayesError::Invariant(
                "even square-term monotonicity has not started".to_owned(),
            ));
        }
    }
    for ell in threshold..threshold + 3 {
        let degree = ell
            .checked_mul(2)
            .and_then(|value| value.checked_add(2))
            .ok_or_else(|| {
                HayesError::InvalidParameter("even endpoint calculation overflow".to_owned())
            })?;
        let other_terms = BigUint::from(degree) << degree.div_ceil(3);
        if other_terms >= (BigUint::from(1_u8) << ell) {
            return Err(HayesError::Invariant(
                "even nonsquare proper-divisor seed exceeds its half-margin".to_owned(),
            ));
        }
        if degree <= 6 {
            return Err(HayesError::Invariant(
                "even proper-divisor monotonicity has not started".to_owned(),
            ));
        }
    }

    Ok(SquareRootLayerBoundReport {
        assumption,
        first_odd_degree: twice_threshold + 1,
        first_even_degree: twice_threshold + 2,
    })
}

/// Check that polynomial-loss conductor-layer delocalization finishes Lemire.
///
/// The proved exact-conductor second moment is
///
/// ```text
/// ||D_[j]||_2^2 <= 2^(n-ell+j-1) (j-1)^2.
/// ```
///
/// Combining it with the assumed sup bound and
/// `||f||_4 <= ||f||_infinity^(1/2)||f||_2^(1/2)` gives
///
/// ```text
/// ||D_[j]||_4
///   <= C^(1/4) ell^(a/4) (j-1) 2^((j-1)/2+n/2-3ell/4).
/// ```
///
/// Minkowski and
/// `sum_(r<ell) r 2^(r/2) < (5/2) ell 2^(ell/2)` then give, for both endpoint
/// parities,
///
/// ```text
/// M_4 <= 625 C ell^(a+4) 2^(3ell).
/// ```
///
/// The factor `625` uses only the rational inequality `1+sqrt(2)<5/2`;
/// no floating-point or asymptotic comparison enters the checker.  The
/// resulting envelope is passed to the existing proper-power-aware endpoint
/// implication.  This function proves the implication only, not the assumed
/// conductor-layer estimate.
///
/// # Errors
///
/// Rejects a zero constant or exponent/constant overflow, and propagates any
/// finite-handoff or exact endpoint failure from the fourth-moment checker.
pub fn check_conductor_layer_sup_bound_sufficiency(
    assumption: ConductorLayerSupBoundAssumption,
) -> Result<ConductorLayerSupBoundReport, HayesError> {
    if assumption.squared_constant == 0 {
        return Err(HayesError::InvalidParameter(
            "conductor-layer squared constant must be positive".to_owned(),
        ));
    }
    let derived_fourth_moment_constant =
        assumption
            .squared_constant
            .checked_mul(625)
            .ok_or_else(|| {
                HayesError::InvalidParameter(
                    "conductor-layer fourth-moment constant overflow".to_owned(),
                )
            })?;
    let derived_fourth_moment_power =
        assumption.polynomial_power.checked_add(4).ok_or_else(|| {
            HayesError::InvalidParameter("conductor-layer fourth-moment power overflow".to_owned())
        })?;
    let derived_fourth_moment =
        check_fourth_moment_bound_sufficiency(FourthMomentBoundAssumption {
            constant: derived_fourth_moment_constant,
            power: derived_fourth_moment_power,
            threshold: assumption.threshold,
            finite_max_degree: assumption.finite_max_degree,
        })?;
    if assumption.threshold == 0 {
        return Err(HayesError::InvalidParameter(
            "conductor-layer threshold must be positive".to_owned(),
        ));
    }
    let constant_log = usize::try_from(
        usize::BITS - 1 - assumption.squared_constant.leading_zeros(),
    )
    .map_err(|_| {
        HayesError::InvalidParameter(
            "conductor-layer constant logarithm does not fit usize".to_owned(),
        )
    })?;
    let threshold_log = usize::try_from(usize::BITS - 1 - assumption.threshold.leading_zeros())
        .map_err(|_| {
            HayesError::InvalidParameter(
                "conductor-layer threshold logarithm does not fit usize".to_owned(),
            )
        })?;
    let individual_weil_proved_through_level_at_threshold = assumption
        .polynomial_power
        .checked_mul(threshold_log)
        .and_then(|value| value.checked_add(constant_log))
        .and_then(|value| value.checked_add(1))
        .ok_or_else(|| {
            HayesError::InvalidParameter("conductor-layer Weil prefix overflow".to_owned())
        })?;
    Ok(ConductorLayerSupBoundReport {
        assumption,
        derived_fourth_moment_constant,
        derived_fourth_moment_power,
        individual_weil_proved_through_level_at_threshold,
        derived_fourth_moment,
    })
}

struct FixedConductorRecurrenceGroup {
    order: usize,
    units: Vec<u64>,
    unit_to_index: BTreeMap<u64, usize>,
    addition: Vec<usize>,
    generator: usize,
}

fn fixed_conductor_recurrence_group(
    level: usize,
    limits: HayesLimits,
) -> Result<FixedConductorRecurrenceGroup, HayesError> {
    let structure = principal_unit_structure(level, limits)?;
    let order = structure.group_order;
    let (_, unit_to_index) = principal_unit_index_table(level, limits)?;
    let units = (0..order)
        .map(|index| principal_unit_from_mixed_radix_index(index, &structure.factors, level))
        .collect::<Result<Vec<_>, _>>()?;
    let mut addition = vec![0_usize; order * order];
    for left in 0..order {
        for right in 0..order {
            let product = unit_multiply(units[left], units[right], level);
            addition[left * order + right] = *unit_to_index.get(&product).ok_or_else(|| {
                HayesError::Invariant("fixed-conductor product has no mixed-radix index".to_owned())
            })?;
        }
    }
    let generator_unit = 1_u64
        .checked_shl(u32::try_from(level).map_err(|_| {
            HayesError::InvalidParameter("fixed-conductor level exceeds u32".to_owned())
        })?)
        .map(|value| value | 1)
        .ok_or_else(|| {
            HayesError::InvalidParameter("fixed-conductor generator overflow".to_owned())
        })?;
    let generator = *unit_to_index
        .get(&generator_unit)
        .ok_or_else(|| HayesError::Invariant("fixed-conductor generator is absent".to_owned()))?;
    Ok(FixedConductorRecurrenceGroup {
        order,
        units,
        unit_to_index,
        addition,
        generator,
    })
}

fn fixed_conductor_first_recurrence_degree(level: usize) -> Result<usize, HayesError> {
    if level < 2 {
        return Err(HayesError::InvalidParameter(
            "fixed-conductor recurrence requires level at least two".to_owned(),
        ));
    }
    level
        .checked_mul(2)
        .and_then(|value| value.checked_sub(1))
        .ok_or_else(|| {
            HayesError::InvalidParameter("fixed-conductor recurrence degree overflow".to_owned())
        })
}

/// Propagate one exact-conductor sibling-difference row to an arbitrary degree.
///
/// If `Delta_j(n)` denotes the level-`j` sibling-difference vector, logarithmic
/// differentiation of the degree-`j-1` Hayes `L`-polynomials gives
///
/// ```text
/// Delta_j(n) = -sum_(d=1)^(j-1) A_d * Delta_j(n-d),
/// A_d = sum_(u in V_d) [u].
/// ```
///
/// The operation constructs `Delta_j(j),...,Delta_j(2j-2)` by the independent
/// exact population transform, checks the first recurrence row at `2j-1`
/// against another fresh transform, and then uses `BigInt` recurrence.  The
/// admitted work bound is conservative `degree * |E_j|^2`.
///
/// # Errors
///
/// Rejects levels below two, degrees below `2j-1`, packed-unit overflow, or a
/// request above the supplied group/table limits, and fails closed if the
/// first propagated row differs from the independent population transform.
pub fn fixed_conductor_sibling_recurrence(
    level: usize,
    degree: usize,
    limits: HayesLimits,
) -> Result<FixedConductorSiblingRecurrenceReport, HayesError> {
    let first_recurrence_degree = fixed_conductor_first_recurrence_degree(level)?;
    if degree < first_recurrence_degree {
        return Err(HayesError::InvalidParameter(format!(
            "fixed-conductor recurrence requires degree at least {first_recurrence_degree}"
        )));
    }
    check_limit("degree", degree, limits.max_degree)?;
    let group = fixed_conductor_recurrence_group(level, limits)?;
    let group_order = group.order;
    let work = degree
        .checked_mul(group_order)
        .and_then(|value| value.checked_mul(group_order))
        .ok_or_else(|| {
            HayesError::InvalidParameter("fixed-conductor recurrence work overflow".to_owned())
        })?;
    check_limit(
        "fixed_conductor_recurrence_cells",
        work,
        limits.max_table_cells,
    )?;
    let direct = |target_degree: usize| -> Result<Vec<BigInt>, HayesError> {
        let distribution = class_population_distribution(level, target_degree, limits)?;
        Ok((0..group_order)
            .map(|class| {
                let sibling = group.addition[class * group_order + group.generator];
                BigInt::from(distribution.counts[class])
                    - BigInt::from(distribution.counts[sibling])
            })
            .collect())
    };
    let mut blocks = vec![Vec::new(); level];
    for (block_degree, block) in blocks.iter_mut().enumerate().skip(1) {
        let size = 1_usize << block_degree;
        block.reserve(size);
        for mask in 0..size {
            let unit = 1_u64 | ((mask as u64) << 1);
            block.push(*group.unit_to_index.get(&unit).ok_or_else(|| {
                HayesError::Invariant("fixed-conductor coefficient block is absent".to_owned())
            })?);
        }
    }
    let seed_count = level - 1;
    let mut history = VecDeque::with_capacity(seed_count);
    for seed_degree in level..(level + seed_count) {
        history.push_back(direct(seed_degree)?);
    }
    for current_degree in first_recurrence_degree..=degree {
        let mut next = vec![BigInt::from(0_u8); group_order];
        for lag in 1..level {
            let previous = &history[history.len() - lag];
            for &shift in &blocks[lag] {
                for (class, value) in previous.iter().enumerate() {
                    if value == &BigInt::from(0_u8) {
                        continue;
                    }
                    let output = group.addition[class * group_order + shift];
                    next[output] -= value;
                }
            }
        }
        if current_degree == first_recurrence_degree && next != direct(current_degree)? {
            return Err(HayesError::Invariant(
                "fixed-conductor recurrence disagrees with independent population transform"
                    .to_owned(),
            ));
        }
        history.pop_front();
        history.push_back(next);
    }
    let target = history.back().ok_or_else(|| {
        HayesError::Invariant("fixed-conductor recurrence has no target row".to_owned())
    })?;
    let (witness_class, maximum_sibling_difference) = target
        .iter()
        .enumerate()
        .map(|(class, value)| (class, value.magnitude().clone()))
        .max_by(|left, right| left.1.cmp(&right.1))
        .ok_or_else(|| {
            HayesError::Invariant("fixed-conductor recurrence target is empty".to_owned())
        })?;
    let squared_constant_numerator = maximum_sibling_difference.pow(2) << (level - 1);
    let squared_constant_denominator = BigUint::from(level - 1).pow(2) << degree;
    Ok(FixedConductorSiblingRecurrenceReport {
        level,
        degree,
        group_order,
        seed_count,
        independently_checked_degree: first_recurrence_degree,
        witness_class,
        witness_unit: group.units[witness_class],
        maximum_sibling_difference,
        squared_constant_numerator,
        squared_constant_denominator,
    })
}

/// Compute the exact identity-class population `N_n(1)`.
///
/// The result counts elements of `GF(2^degree)` whose characteristic
/// polynomial is in the identity type-II class modulo `x^(ell+1)`.
///
/// # Errors
///
/// Returns a typed resource decline before allocation, rejects parameters
/// outside the exact CRT domain, and reports failed transform invariants.
pub fn identity_class_count(
    ell: usize,
    degree: usize,
    limits: HayesLimits,
) -> Result<u128, HayesError> {
    admit(ell, degree, limits)?;
    let first = identity_class_residue(ell, degree, PRIME_ONE)?;
    let second = identity_class_residue(ell, degree, PRIME_TWO)?;
    let upper_bound = 1_u128
        .checked_shl(u32::try_from(degree).map_err(|_| {
            HayesError::InvalidParameter("degree does not fit the shift domain".to_owned())
        })?)
        .ok_or_else(|| {
            HayesError::InvalidParameter("degree exceeds the exact u128 count domain".to_owned())
        })?;
    let crt_modulus = u128::from(PRIME_ONE) * u128::from(PRIME_TWO);
    if upper_bound >= crt_modulus {
        return Err(HayesError::InvalidParameter(format!(
            "2^{degree} does not fit uniquely below the CRT modulus"
        )));
    }
    let exact = crt(first, PRIME_ONE, second, PRIME_TWO)?;
    if exact > upper_bound {
        return Err(HayesError::Invariant(format!(
            "recovered count {exact} exceeds 2^{degree}"
        )));
    }
    Ok(exact)
}

/// Compute the exact odd Lemire endpoint using one NTT prime.
///
/// For `degree = 2*ell+1`, the only proper-degree element in the identity
/// class is zero, with Mangoldt weight one.  Hence
///
/// ```text
/// N_degree(1) = 1 + degree * I_degree(1),
/// ```
///
/// and there are at most `2^ell` candidate irreducible polynomials (the
/// constant coefficient is forced to one).  Consequently
/// `N_degree(1) <= 1 + degree*2^ell`.  When that upper bound is smaller than
/// `ODD_ENDPOINT_SINGLE_PRIME`, one transform residue is already the unique
/// nonnegative integer count; a second CRT transform is unnecessary.
///
/// # Errors
///
/// Returns a typed resource decline, rejects levels whose rigorous upper
/// bound reaches the single-prime modulus, and fails closed unless the exact
/// odd-endpoint prime-power identity is integral.
pub fn odd_endpoint_irreducible_count_single_ntt(
    ell: usize,
    limits: HayesLimits,
) -> Result<IdentityClassIrreducibleReport, HayesError> {
    let reduction = odd_endpoint_prime_power_reduction(ell, limits)?;
    let degree = reduction.degree;
    admit(ell, degree, limits)?;
    let candidate_count = 1_u128
        .checked_shl(u32::try_from(ell).map_err(|_| {
            HayesError::InvalidParameter("odd endpoint level does not fit a shift".to_owned())
        })?)
        .ok_or_else(|| {
            HayesError::InvalidParameter("odd endpoint candidate count overflow".to_owned())
        })?;
    let population_upper_bound = candidate_count
        .checked_mul(degree as u128)
        .and_then(|value| value.checked_add(1))
        .ok_or_else(|| {
            HayesError::InvalidParameter("odd endpoint population bound overflow".to_owned())
        })?;
    if population_upper_bound >= u128::from(ODD_ENDPOINT_SINGLE_PRIME) {
        return Err(HayesError::ResourceLimit {
            resource: "odd-endpoint single-prime uniqueness bound",
            requested: usize::try_from(population_upper_bound).unwrap_or(usize::MAX),
            limit: usize::try_from(ODD_ENDPOINT_SINGLE_PRIME - 1).unwrap_or(usize::MAX),
        });
    }

    let mangoldt_population = u128::from(identity_class_residue(
        ell,
        degree,
        ODD_ENDPOINT_SINGLE_PRIME,
    )?);
    if mangoldt_population > population_upper_bound {
        return Err(HayesError::Invariant(format!(
            "odd endpoint population {mangoldt_population} exceeds its bound {population_upper_bound}"
        )));
    }
    let weighted_irreducibles = mangoldt_population
        .checked_sub(reduction.proper_prime_power_population)
        .ok_or_else(|| {
            HayesError::Invariant(
                "odd endpoint population omits the proved proper-power contribution".to_owned(),
            )
        })?;
    if !weighted_irreducibles.is_multiple_of(degree as u128) {
        return Err(HayesError::Invariant(
            "odd endpoint population does not have the form 1+nI".to_owned(),
        ));
    }
    let irreducible_count = weighted_irreducibles / degree as u128;
    if irreducible_count > candidate_count {
        return Err(HayesError::Invariant(
            "odd endpoint irreducible count exceeds the candidate population".to_owned(),
        ));
    }
    Ok(IdentityClassIrreducibleReport {
        ell,
        degree,
        mangoldt_population,
        proper_prime_power_population: reduction.proper_prime_power_population,
        irreducible_count,
    })
}

/// Compute one exact odd-endpoint modulo-eight certificate and replay the
/// Carlitz Deuring--Shafarevich precision ledger.
///
/// The binary Carlitz cover of conductor `t^(ell+1)` has Galois group of
/// order `2^ell`, one totally ramified finite place, and split infinity.  The
/// Deuring--Shafarevich formula therefore gives
///
/// ```text
/// gamma(C_ell)-1 = 2^ell(0-1)+(2^ell-1) = -1,
/// gamma(C_ell)=0.
/// ```
///
/// This is an exact structural fact, but not the desired congruence: after
/// the factor `2^ell` in the point-population identity, recovering the three
/// normalized residue bits requires the raw point count modulo `2^(ell+3)`.
/// The operation consequently certifies a bounded row without promoting the
/// observed universal modulo-eight nonvanishing pattern to a theorem.
///
/// # Errors
///
/// Propagates the exact odd-endpoint transform's typed failures, rejects
/// arithmetic overflow, or fails closed if the Deuring--Shafarevich and
/// point-population identities do not replay exactly.
pub fn odd_endpoint_two_adic_report(
    ell: usize,
    limits: HayesLimits,
) -> Result<OddEndpointTwoAdicReport, HayesError> {
    let exact = odd_endpoint_irreducible_count_single_ntt(ell, limits)?;
    let group_order = 1_u128
        .checked_shl(u32::try_from(ell).map_err(|_| {
            HayesError::InvalidParameter("Carlitz level does not fit a shift".to_owned())
        })?)
        .ok_or_else(|| HayesError::InvalidParameter("Carlitz group order overflow".to_owned()))?;
    let group_order_signed = i128::try_from(group_order).map_err(|_| {
        HayesError::InvalidParameter("Carlitz group order does not fit i128".to_owned())
    })?;
    let two_rank_minus_one = (-group_order_signed)
        .checked_add(group_order_signed - 1)
        .ok_or_else(|| {
            HayesError::InvalidParameter("Deuring--Shafarevich sum overflow".to_owned())
        })?;
    let carlitz_two_rank = usize::try_from(two_rank_minus_one + 1).map_err(|_| {
        HayesError::Invariant("Carlitz Deuring--Shafarevich rank is negative".to_owned())
    })?;
    if carlitz_two_rank != 0 {
        return Err(HayesError::Invariant(
            "one-branch-point Carlitz cover does not have 2-rank zero".to_owned(),
        ));
    }

    let required_curve_point_modulus_bits = ell.checked_add(3).ok_or_else(|| {
        HayesError::InvalidParameter("Carlitz point precision overflow".to_owned())
    })?;
    let required_curve_point_modulus = 1_u128
        .checked_shl(
            u32::try_from(required_curve_point_modulus_bits).map_err(|_| {
                HayesError::InvalidParameter(
                    "Carlitz point modulus does not fit a shift".to_owned(),
                )
            })?,
        )
        .ok_or_else(|| HayesError::InvalidParameter("Carlitz point modulus overflow".to_owned()))?;
    let curve_point_count = group_order
        .checked_mul(exact.mangoldt_population)
        .and_then(|value| value.checked_add(1))
        .ok_or_else(|| HayesError::InvalidParameter("Carlitz point count overflow".to_owned()))?;
    let reconstructed_irreducibles = ((curve_point_count - 1) / group_order)
        .checked_sub(1)
        .ok_or_else(|| {
            HayesError::Invariant("Carlitz point count omits the ramified contribution".to_owned())
        })?
        / exact.degree as u128;
    if reconstructed_irreducibles != exact.irreducible_count {
        return Err(HayesError::Invariant(
            "Carlitz point residue does not reconstruct the odd irreducible count".to_owned(),
        ));
    }
    let irreducible_residue_mod_8 = u8::try_from(exact.irreducible_count % 8)
        .map_err(|_| HayesError::Invariant("modulo-eight residue does not fit u8".to_owned()))?;
    let irreducible_residue_mod_16 = u8::try_from(exact.irreducible_count % 16)
        .map_err(|_| HayesError::Invariant("modulo-sixteen residue does not fit u8".to_owned()))?;

    Ok(OddEndpointTwoAdicReport {
        ell,
        degree: exact.degree,
        mangoldt_population: exact.mangoldt_population,
        irreducible_count: exact.irreducible_count,
        irreducible_residue_mod_8,
        irreducible_residue_mod_16,
        irreducible_two_adic_valuation: (exact.irreducible_count != 0)
            .then_some(exact.irreducible_count.trailing_zeros()),
        carlitz_galois_group_order: group_order,
        ramified_place_stabilizer_order: group_order,
        carlitz_two_rank,
        required_curve_point_modulus_bits,
        curve_point_count,
        curve_point_residue_at_required_precision: curve_point_count % required_curve_point_modulus,
    })
}

/// Compute every exact principal-unit class population.
///
/// This is the inverse-Fourier companion of [`identity_class_count`].  It is
/// intended for bounded `L^infinity` and higher-moment diagnostics: a caller
/// that needs only the identity coordinate should use the cheaper scalar API.
/// Both modular distributions are reconstructed entrywise, and the exact
/// total is checked to be `2^degree`.
///
/// # Errors
///
/// Returns a typed resource decline before allocation, rejects parameters
/// outside the two-prime CRT uniqueness domain, and reports transform,
/// reconstruction, or population-conservation failures.
pub fn class_population_distribution(
    ell: usize,
    degree: usize,
    limits: HayesLimits,
) -> Result<ClassPopulationDistribution, HayesError> {
    admit(ell, degree, limits)?;
    class_population_distribution_admitted(ell, degree)
}

/// Compute exact signed Möbius sums in every principal-unit class.
///
/// In character coordinates this computes the coefficient of `z^degree` in
/// `A_chi(z)^(-1)` by the exact recurrence
///
/// ```text
/// M_0(chi)=1,
/// M_n(chi)=-sum_(1<=d<=n) A_d(chi) M_(n-d)(chi).
/// ```
///
/// Two modular transforms are reconstructed as signed integers.  The method
/// checks the coarse absolute bound `2^degree` for every class and the global
/// Euler-product identity `sum_e M_1(e)=-2`, `sum_e M_degree(e)=0` for
/// `degree>1`.
///
/// # Errors
///
/// Returns a typed resource decline before allocation, rejects parameters
/// outside the signed CRT domain, and reports failed transform, bound, or
/// conservation invariants.
pub fn class_mobius_distribution(
    ell: usize,
    degree: usize,
    limits: HayesLimits,
) -> Result<ClassMobiusDistribution, HayesError> {
    admit_any_positive_degree(ell, degree, limits)?;
    let magnitude_bound = 1_u128
        .checked_shl(u32::try_from(degree).map_err(|_| {
            HayesError::InvalidParameter("degree does not fit the shift domain".to_owned())
        })?)
        .ok_or_else(|| {
            HayesError::InvalidParameter("degree exceeds the exact i128 count domain".to_owned())
        })?;
    let crt_modulus = u128::from(PRIME_ONE) * u128::from(PRIME_TWO);
    let signed_width = magnitude_bound.checked_mul(2).ok_or_else(|| {
        HayesError::InvalidParameter("signed Möbius uniqueness bound overflow".to_owned())
    })?;
    if signed_width >= crt_modulus || crt_modulus > i128::MAX as u128 {
        return Err(HayesError::InvalidParameter(format!(
            "signed Möbius values bounded by 2^{degree} do not fit uniquely below the CRT modulus"
        )));
    }

    let first = class_mobius_residue(ell, degree, PRIME_ONE)?;
    let second = class_mobius_residue(ell, degree, PRIME_TWO)?;
    if first.len() != second.len() {
        return Err(HayesError::Invariant(
            "class-Möbius residue tables have different lengths".to_owned(),
        ));
    }
    let half_modulus = crt_modulus / 2;
    let mut values = Vec::with_capacity(first.len());
    let mut recovered_total = 0_i128;
    for (first_residue, second_residue) in first.into_iter().zip(second) {
        let unsigned = crt(first_residue, PRIME_ONE, second_residue, PRIME_TWO)?;
        let value = if unsigned <= half_modulus {
            i128::try_from(unsigned).map_err(|_| {
                HayesError::Invariant("positive Möbius CRT value exceeds i128".to_owned())
            })?
        } else {
            i128::try_from(unsigned).map_err(|_| {
                HayesError::Invariant("negative Möbius CRT residue exceeds i128".to_owned())
            })? - i128::try_from(crt_modulus)
                .map_err(|_| HayesError::Invariant("Möbius CRT modulus exceeds i128".to_owned()))?
        };
        if value.unsigned_abs() > magnitude_bound {
            return Err(HayesError::Invariant(format!(
                "recovered class Möbius magnitude {} exceeds 2^{degree}",
                value.unsigned_abs()
            )));
        }
        recovered_total = recovered_total.checked_add(value).ok_or_else(|| {
            HayesError::InvalidParameter("class-Möbius total exceeds i128".to_owned())
        })?;
        values.push(value);
    }
    let expected_total = if degree == 1 { -2 } else { 0 };
    if recovered_total != expected_total {
        return Err(HayesError::Invariant(format!(
            "class Möbius sums total {recovered_total}, expected {expected_total}"
        )));
    }

    Ok(ClassMobiusDistribution {
        ell,
        degree,
        values,
    })
}

/// Compute the additive Fourier spectrum of Möbius sums after unit inversion.
///
/// This is the exact Fourier bridge used by the Lemire endpoint reduction.
/// If `W_d` is the additive coefficient subspace in degrees `1..=d`, then
/// orthogonality gives
///
/// ```text
/// sum_(u in V_d) M_degree(u^(-1))
///   = 2^(d-ell) sum_(a in W_d^perp) H_degree(a).
/// ```
///
/// The operation checks that inversion is a permutation and verifies Walsh
/// Parseval exactly with unbounded integers.  It proves only the finite
/// requested identity, not a bound uniform in `ell`.
///
/// # Errors
///
/// Returns the same typed admission and reconstruction failures as
/// [`class_mobius_distribution`], or an invariant error if the unit indexing,
/// checked Walsh transform, or Parseval identity fails.
pub fn inverse_additive_mobius_spectrum(
    ell: usize,
    degree: usize,
    limits: HayesLimits,
) -> Result<InverseAdditiveMobiusSpectrum, HayesError> {
    let distribution = class_mobius_distribution(ell, degree, limits)?;
    let factors = principal_unit_factors(ell);
    let mut additive_values = vec![0_i128; distribution.values.len()];
    let mut occupied = vec![false; distribution.values.len()];
    for (index, value) in distribution.values.iter().copied().enumerate() {
        let mut quotient = index;
        let mut unit = 1_u64;
        for factor in &factors {
            let exponent = quotient % factor.order;
            quotient /= factor.order;
            let generator = 1 | (1_u64 << factor.odd_degree);
            for _ in 0..exponent {
                unit = unit_multiply(unit, generator, ell);
            }
        }
        if quotient != 0 {
            return Err(HayesError::Invariant(format!(
                "ell={ell}: mixed-radix unit index leaves a quotient"
            )));
        }
        let inverse = principal_unit_inverse(unit, ell);
        let packed = usize::try_from(inverse >> 1).map_err(|_| {
            HayesError::InvalidParameter("packed inverse unit does not fit usize".to_owned())
        })?;
        if packed >= additive_values.len() || occupied[packed] {
            return Err(HayesError::Invariant(format!(
                "ell={ell}: unit inversion is not a permutation of additive coordinates"
            )));
        }
        occupied[packed] = true;
        additive_values[packed] = value;
    }
    if occupied.iter().any(|entry| !entry) {
        return Err(HayesError::Invariant(format!(
            "ell={ell}: unit inversion misses an additive coordinate"
        )));
    }

    let source_energy = additive_values
        .iter()
        .fold(BigUint::from(0_u8), |sum, value| {
            let magnitude = BigUint::from(value.unsigned_abs());
            sum + &magnitude * &magnitude
        });
    checked_walsh_transform(&mut additive_values)?;
    let spectrum_energy = additive_values
        .iter()
        .fold(BigUint::from(0_u8), |sum, value| {
            let magnitude = BigUint::from(value.unsigned_abs());
            sum + &magnitude * &magnitude
        });
    let expected_energy = BigUint::from(additive_values.len()) * source_energy;
    if spectrum_energy != expected_energy {
        return Err(HayesError::Invariant(
            "inverse-additive Mobius spectrum fails Walsh Parseval".to_owned(),
        ));
    }
    Ok(InverseAdditiveMobiusSpectrum {
        ell,
        degree,
        values: additive_values,
    })
}

fn binary_quotient_multiply(left: u64, mut right: u64, modulus: u64, degree: usize) -> u64 {
    let mask = (1_u64 << degree) - 1;
    let reduction = modulus & mask;
    let mut shifted = left & mask;
    let mut product = 0_u64;
    while right != 0 {
        if right & 1 != 0 {
            product ^= shifted;
        }
        right >>= 1;
        let carry = (shifted >> (degree - 1)) & 1;
        shifted = (shifted << 1) & mask;
        if carry != 0 {
            shifted ^= reduction;
        }
    }
    product
}

fn binary_second_trace_value(element: u64, modulus: u64, degree: usize) -> u8 {
    let columns = (0..degree)
        .map(|column| binary_quotient_multiply(element, 1_u64 << column, modulus, degree))
        .collect::<Vec<_>>();
    let mut second_trace = 0_u8;
    for left in 0..degree {
        for right in left + 1..degree {
            let diagonal = ((columns[left] >> left) & 1) * ((columns[right] >> right) & 1);
            let cross = ((columns[right] >> left) & 1) * ((columns[left] >> right) & 1);
            second_trace ^= u8::try_from(diagonal ^ cross).unwrap_or(0);
        }
    }
    second_trace
}

fn binary_algebra_trace(element: u64, modulus: u64, degree: usize) -> u8 {
    (0..degree).fold(0_u8, |trace, column| {
        let product = binary_quotient_multiply(element, 1_u64 << column, modulus, degree);
        trace ^ u8::try_from((product >> column) & 1).unwrap_or(0)
    })
}

fn binary_matrix_rank(mut rows: Vec<u64>, dimension: usize) -> usize {
    let mut rank = 0_usize;
    for column in 0..dimension {
        let Some(pivot) = (rank..rows.len()).find(|&row| (rows[row] >> column) & 1 != 0) else {
            continue;
        };
        rows.swap(rank, pivot);
        for row in 0..rows.len() {
            if row != rank && (rows[row] >> column) & 1 != 0 {
                rows[row] ^= rows[rank];
            }
        }
        rank += 1;
    }
    rank
}

fn binary_matrix_nullspace_basis(mut rows: Vec<u64>, dimension: usize) -> Vec<u64> {
    let mut pivot_columns = Vec::new();
    let mut rank = 0_usize;
    for column in 0..dimension {
        let Some(pivot) = (rank..rows.len()).find(|&row| (rows[row] >> column) & 1 != 0) else {
            continue;
        };
        rows.swap(rank, pivot);
        for row in 0..rows.len() {
            if row != rank && (rows[row] >> column) & 1 != 0 {
                rows[row] ^= rows[rank];
            }
        }
        pivot_columns.push(column);
        rank += 1;
    }
    let pivot_mask = pivot_columns
        .iter()
        .fold(0_u64, |mask, &column| mask | (1_u64 << column));
    let mut basis = Vec::with_capacity(dimension - rank);
    for free_column in 0..dimension {
        if pivot_mask >> free_column & 1 != 0 {
            continue;
        }
        let mut vector = 1_u64 << free_column;
        for (row, &pivot_column) in pivot_columns.iter().enumerate() {
            if rows[row] >> free_column & 1 != 0 {
                vector |= 1_u64 << pivot_column;
            }
        }
        basis.push(vector);
    }
    basis
}

fn binary_second_trace_space_basis(modulus: u64, degree: usize) -> Result<Vec<u64>, HayesError> {
    if degree.is_multiple_of(2) {
        return Ok((0..degree).map(|index| 1_u64 << index).collect());
    }
    let trace_bits = (0..degree).fold(0_u64, |bits, index| {
        bits | (u64::from(binary_algebra_trace(1_u64 << index, modulus, degree)) << index)
    });
    let pivot = usize::try_from(trace_bits.trailing_zeros())
        .map_err(|_| HayesError::InvalidParameter("second-trace pivot exceeds usize".to_owned()))?;
    if pivot >= degree {
        return Err(HayesError::Invariant(
            "odd-degree algebra trace is zero".to_owned(),
        ));
    }
    Ok((0..degree)
        .filter(|&index| index != pivot)
        .map(|index| {
            (1_u64 << index)
                ^ if (trace_bits >> index) & 1 != 0 {
                    1_u64 << pivot
                } else {
                    0
                }
        })
        .collect())
}

fn binary_second_trace_polar(left: u64, right: u64, modulus: u64, degree: usize) -> u8 {
    binary_second_trace_value(left, modulus, degree)
        ^ binary_second_trace_value(right, modulus, degree)
        ^ binary_second_trace_value(left ^ right, modulus, degree)
}

fn binary_second_trace_arf(
    modulus: u64,
    degree: usize,
    mut basis: Vec<u64>,
) -> Result<u8, HayesError> {
    let mut arf = 0_u8;
    while let Some(left) = basis.pop() {
        let partner = basis
            .iter()
            .position(|&right| binary_second_trace_polar(left, right, modulus, degree) != 0)
            .ok_or_else(|| HayesError::Invariant("second trace form has a radical".to_owned()))?;
        let right = basis.swap_remove(partner);
        arf ^= binary_second_trace_value(left, modulus, degree)
            & binary_second_trace_value(right, modulus, degree);
        for vector in &mut basis {
            let pair_left = binary_second_trace_polar(*vector, left, modulus, degree);
            let pair_right = binary_second_trace_polar(*vector, right, modulus, degree);
            if pair_right != 0 {
                *vector ^= left;
            }
            if pair_left != 0 {
                *vector ^= right;
            }
        }
    }
    Ok(arf)
}

fn determinant_mod_eight(mut matrix: Vec<Vec<u8>>) -> Result<u8, HayesError> {
    let dimension = matrix.len();
    let mut determinant = 1_u8;
    for column in 0..dimension {
        let pivot = (column..dimension)
            .find(|&row| matrix[row][column] % 2 == 1)
            .ok_or_else(|| {
                HayesError::Invariant("odd resultant matrix is singular mod 2".to_owned())
            })?;
        if pivot != column {
            matrix.swap(pivot, column);
            determinant = (8 - determinant) % 8;
        }
        let pivot_value = matrix[column][column] % 8;
        determinant = (determinant * pivot_value) % 8;
        let inverse = pivot_value;
        let pivot_row = matrix[column].clone();
        for row in matrix.iter_mut().skip(column + 1) {
            let factor = (row[column] * inverse) % 8;
            for (entry, value) in row.iter_mut().enumerate().skip(column) {
                *value = (*value + 8 - (factor * pivot_row[entry]) % 8) % 8;
            }
        }
    }
    Ok(determinant)
}

fn integer_determinant_bareiss(mut matrix: Vec<Vec<BigInt>>) -> Result<BigInt, HayesError> {
    let dimension = matrix.len();
    if dimension == 0 {
        return Ok(BigInt::from(1));
    }
    let zero = BigInt::from(0);
    let mut sign = BigInt::from(1);
    let mut previous = BigInt::from(1);
    for column in 0..dimension.saturating_sub(1) {
        let Some(pivot) = (column..dimension).find(|&row| matrix[row][column] != zero) else {
            return Ok(zero);
        };
        if pivot != column {
            matrix.swap(pivot, column);
            sign = -sign;
        }
        let pivot_value = matrix[column][column].clone();
        for row in column + 1..dimension {
            for entry in column + 1..dimension {
                let numerator = &pivot_value * &matrix[row][entry]
                    - &matrix[row][column] * &matrix[column][entry];
                let quotient = &numerator / &previous;
                if &quotient * &previous != numerator {
                    return Err(HayesError::Invariant(
                        "Bareiss resultant division is not exact".to_owned(),
                    ));
                }
                matrix[row][entry] = quotient;
            }
        }
        previous = pivot_value;
    }
    Ok(sign * &matrix[dimension - 1][dimension - 1])
}

fn binary_integral_discriminant_residue_mod_eight(
    polynomial: u64,
    degree: usize,
) -> Result<u8, HayesError> {
    if degree <= 1 {
        return Ok(1);
    }
    let derivative_degree = degree - 1;
    let size = degree + derivative_degree;
    let polynomial_descending = (0..=degree)
        .rev()
        .map(|index| BigInt::from((polynomial >> index) & 1))
        .collect::<Vec<_>>();
    let derivative_descending = (0..=derivative_degree)
        .rev()
        .map(|index| {
            let source = index + 1;
            if (polynomial >> source) & 1 != 0 {
                BigInt::from(source)
            } else {
                BigInt::from(0)
            }
        })
        .collect::<Vec<_>>();
    let mut matrix = vec![vec![BigInt::from(0); size]; size];
    for shift in 0..derivative_degree {
        matrix[shift][shift..shift + polynomial_descending.len()]
            .clone_from_slice(&polynomial_descending);
    }
    for shift in 0..degree {
        let row = derivative_degree + shift;
        matrix[row][shift..shift + derivative_descending.len()]
            .clone_from_slice(&derivative_descending);
    }
    let mut discriminant = integer_determinant_bareiss(matrix)?;
    if !(degree * (degree - 1) / 2).is_multiple_of(2) {
        discriminant = -discriminant;
    }
    let modulus = BigInt::from(8);
    let mut residue = discriminant % &modulus;
    if residue < BigInt::from(0) {
        residue += &modulus;
    }
    u8::try_from(residue)
        .map_err(|_| HayesError::Invariant("integral discriminant residue exceeds u8".to_owned()))
}

fn binary_integral_discriminant_mod_eight(
    polynomial: u64,
    degree: usize,
) -> Result<u8, HayesError> {
    if degree <= 1 {
        return Ok(1);
    }
    let derivative_degree = (1..=degree)
        .rev()
        .find(|&index| (polynomial >> index) & 1 != 0)
        .map(|index| index - 1)
        .ok_or_else(|| HayesError::Invariant("constant polynomial has no derivative".to_owned()))?;
    let size = degree + derivative_degree;
    let polynomial_descending = (0..=degree)
        .rev()
        .map(|index| u8::try_from((polynomial >> index) & 1).unwrap_or(0))
        .collect::<Vec<_>>();
    let derivative_descending = (0..=derivative_degree)
        .rev()
        .map(|index| {
            let source = index + 1;
            if (polynomial >> source) & 1 != 0 {
                u8::try_from(source % 8).unwrap_or(0)
            } else {
                0
            }
        })
        .collect::<Vec<_>>();
    let mut matrix = vec![vec![0_u8; size]; size];
    for shift in 0..derivative_degree {
        matrix[shift][shift..shift + polynomial_descending.len()]
            .copy_from_slice(&polynomial_descending);
    }
    for shift in 0..degree {
        let row = derivative_degree + shift;
        matrix[row][shift..shift + derivative_descending.len()]
            .copy_from_slice(&derivative_descending);
    }
    let resultant = determinant_mod_eight(matrix)?;
    if (degree * (degree - 1) / 2).is_multiple_of(2) {
        Ok(resultant)
    } else {
        Ok((8 - resultant) % 8)
    }
}

fn binary_formal_derivative(polynomial: u64, degree: usize) -> u64 {
    (1..=degree)
        .filter(|exponent| !exponent.is_multiple_of(2))
        .filter(|exponent| polynomial >> exponent & 1 != 0)
        .fold(0_u64, |derivative, exponent| {
            derivative | (1_u64 << (exponent - 1))
        })
}

const fn kronecker_two_mod_eight(residue: u8) -> i8 {
    match residue % 8 {
        1 | 7 => 1,
        3 | 5 => -1,
        _ => 0,
    }
}

fn add_zeta_eight_power(basis: &mut [i8; 4], exponent: u8, coefficient: i8) {
    let exponent = usize::from(exponent % 8);
    let (slot, sign) = if exponent < 4 {
        (exponent, 1_i8)
    } else {
        (exponent - 4, -1_i8)
    };
    basis[slot] += sign * coefficient;
}

/// Expand the real dyadic character as four exact additive phases in
/// `Z[zeta_8]`.
///
/// # Errors
///
/// Returns an invariant failure only if the exact cyclotomic Gauss identity
/// fails internally.
pub fn binary_dyadic_character_fourier_report(
    residue: u8,
) -> Result<BinaryDyadicCharacterFourierReport, HayesError> {
    let residue = residue % 8;
    let kronecker_two = kronecker_two_mod_eight(residue);
    let mut gauss_sum_basis = [0_i8; 4];
    for (multiplier, coefficient) in [(1_u8, 1_i8), (3, -1), (5, -1), (7, 1)] {
        let exponent = usize::from((multiplier * residue) % 8);
        let (basis, sign) = if exponent < 4 {
            (exponent, 1)
        } else {
            (exponent - 4, -1)
        };
        gauss_sum_basis[basis] += sign * coefficient;
    }
    let expected_basis = [0, 2 * kronecker_two, 0, -2 * kronecker_two];
    if gauss_sum_basis != expected_basis {
        return Err(HayesError::Invariant(
            "dyadic character Fourier identity failed".to_owned(),
        ));
    }
    Ok(BinaryDyadicCharacterFourierReport {
        residue,
        kronecker_two,
        gauss_sum_basis,
        expected_basis,
    })
}

/// Certify the auxiliary-unit quadratic Gauss projector over
/// `(Z/8Z)^x=<3,5>`.
///
/// Write `a=3^u 5^v=1+2u+4v (mod 8)` and
/// `chi_8(a)=(-1)^(u+v)`.  For each `D mod 8`, the normalized phase
///
/// ```text
/// Q_D(u,v)=chi_8(a) zeta_8^((a-1)D)
/// ```
///
/// has polarization `(-1)^(D u u')`.  Odd `D` gives radical `{u=0}`
/// on which the phase is trivial and hence a Gauss sum of squared magnitude
/// eight; even `D` gives a nontrivial linear character and zero sum.  Summing
/// the unnormalized auxiliary phases recovers the Kronecker character.
///
/// # Errors
///
/// Returns an invariant failure if any group, polarization, radical, or
/// cyclotomic projector identity fails.
pub fn dyadic_auxiliary_quadratic_projector_report()
-> Result<DyadicAuxiliaryQuadraticProjectorReport, HayesError> {
    let mut residues = Vec::with_capacity(8);
    for discriminant_residue in 0_u8..8 {
        let mut projector = [0_i8; 4];
        let mut normalized_gauss = [0_i8; 4];
        let mut phase_exponents = [0_u8; 4];
        for u in 0_u8..=1 {
            for v in 0_u8..=1 {
                let index = usize::from(u | (v << 1));
                let unit = (1 + 2 * u + 4 * v) % 8;
                let character = if (u + v).is_multiple_of(2) {
                    1_i8
                } else {
                    -1_i8
                };
                add_zeta_eight_power(&mut projector, unit * discriminant_residue, character);
                let phase = (4 * ((u + v) % 2) + (unit + 7) % 8 * discriminant_residue) % 8;
                phase_exponents[index] = phase;
                add_zeta_eight_power(&mut normalized_gauss, phase, 1);
            }
        }
        let expected = [
            0,
            2 * kronecker_two_mod_eight(discriminant_residue),
            0,
            -2 * kronecker_two_mod_eight(discriminant_residue),
        ];
        if projector != expected {
            return Err(HayesError::Invariant(
                "auxiliary-unit cyclotomic projector identity failed".to_owned(),
            ));
        }
        for left in 0_u8..4 {
            for right in 0_u8..4 {
                let polarization = (phase_exponents[usize::from(left ^ right)] + 8
                    - phase_exponents[usize::from(left)]
                    + 8
                    - phase_exponents[usize::from(right)])
                    % 8;
                let expected_polarization =
                    4 * (discriminant_residue % 2) * (left & 1) * (right & 1);
                if polarization != expected_polarization {
                    return Err(HayesError::Invariant(
                        "auxiliary-unit polarization identity failed".to_owned(),
                    ));
                }
            }
        }
        let mut radical_size = 0_usize;
        let mut phase_trivial_on_radical = true;
        for left in 0_u8..4 {
            let is_radical = (0_u8..4).all(|right| {
                let sum = usize::from(left ^ right);
                let polarization = (phase_exponents[sum] + 8 - phase_exponents[usize::from(left)]
                    + 8
                    - phase_exponents[usize::from(right)])
                    % 8;
                polarization == 0
            });
            if is_radical {
                radical_size += 1;
                phase_trivial_on_radical &= phase_exponents[usize::from(left)] == 0;
            }
        }
        let expected_radical_size = if discriminant_residue.is_multiple_of(2) {
            4
        } else {
            2
        };
        if radical_size != expected_radical_size
            || phase_trivial_on_radical == discriminant_residue.is_multiple_of(2)
            || (discriminant_residue.is_multiple_of(2) && normalized_gauss != [0_i8; 4])
        {
            return Err(HayesError::Invariant(
                "auxiliary-unit quadratic radical identity failed".to_owned(),
            ));
        }
        residues.push(DyadicAuxiliaryProjectorResidue {
            discriminant_residue,
            projector_cyclotomic_basis: projector,
            expected_projector_cyclotomic_basis: expected,
            normalized_gauss_cyclotomic_basis: normalized_gauss,
            radical_size,
            phase_trivial_on_radical,
        });
    }
    Ok(DyadicAuxiliaryQuadraticProjectorReport { residues })
}

/// Extract the exact mod-four additivity obstruction in the pinned worst
/// dyadic autocorrelation fibre.
///
/// For `t in F_2^7`, set
///
/// ```text
/// F_t = x^11 + 1 + sum_(j=0)^6 t_j x^(j+2),
/// D_t = disc(F_t) disc(F_(t xor 48)) mod 8,
/// d_t = D_t - D_0 mod 4.
/// ```
///
/// This is the `(ell,k,d)=(9,11,8)` fibre with packed shift `96`, input
/// coset zero, and inverse difference `192`.  If a group `G` admitted a
/// surjective homomorphism onto this additive fibre and `d` pulled back to a
/// homomorphism on `G`, then `d` itself would be additive after choosing
/// preimages.  The returned counterexample therefore rejects every such
/// projection-preserving central extension; it does not reject a joined law
/// whose multiplication genuinely mixes the fibre and auxiliary coordinates.
///
/// # Errors
///
/// Returns an invariant failure if the exact discriminant ANF does not have
/// the pinned full-support coefficient six, or if no additivity failure is
/// found.
pub fn pinned_dyadic_fibre_projection_obstruction_report()
-> Result<DyadicFibreProjectionObstructionReport, HayesError> {
    const DEGREE: usize = 11;
    const DIMENSION: usize = 7;
    const PAIRED_SHIFT: usize = 48;
    const SIZE: usize = 1 << DIMENSION;

    let polynomial = |coordinate: usize| {
        let mut packed = (1_u64 << DEGREE) | 1;
        for bit in 0..DIMENSION {
            packed |= u64::from((coordinate >> bit) & 1 != 0) << (bit + 2);
        }
        packed
    };
    let mut product_residues = vec![0_u8; SIZE];
    for (coordinate, product_residue) in product_residues.iter_mut().enumerate() {
        let left = binary_integral_discriminant_residue_mod_eight(polynomial(coordinate), DEGREE)?;
        let right = binary_integral_discriminant_residue_mod_eight(
            polynomial(coordinate ^ PAIRED_SHIFT),
            DEGREE,
        )?;
        *product_residue = (left * right) % 8;
    }
    let coefficients = mod_eight_anf_coefficients(&product_residues, DIMENSION)?;
    let full_support_coefficient_mod_eight = coefficients[SIZE - 1];
    if full_support_coefficient_mod_eight != 6 {
        return Err(HayesError::Invariant(
            "pinned product-discriminant full-support coefficient changed".to_owned(),
        ));
    }

    let origin = product_residues[0] % 4;
    let normalized = product_residues
        .iter()
        .map(|&value| (value % 4 + 4 - origin) % 4)
        .collect::<Vec<_>>();
    for left in 0..SIZE {
        for right in 0..SIZE {
            let expected = (normalized[left] + normalized[right]) % 4;
            let actual = normalized[left ^ right];
            if actual != expected {
                return Ok(DyadicFibreProjectionObstructionReport {
                    polynomial_degree: DEGREE,
                    fibre_dimension: DIMENSION,
                    paired_coordinate_shift: PAIRED_SHIFT,
                    full_support_coefficient_mod_eight,
                    witness: DyadicFibreModFourAdditivityWitness {
                        left,
                        right,
                        left_phase_mod_four: normalized[left],
                        right_phase_mod_four: normalized[right],
                        xor_phase_mod_four: actual,
                        expected_xor_phase_mod_four: expected,
                    },
                });
            }
        }
    }
    Err(HayesError::Invariant(
        "pinned product-discriminant phase unexpectedly became additive".to_owned(),
    ))
}

/// Recover the exact multilinear coefficient polynomial for the integral
/// discriminant modulo eight.
///
/// The free bits are the coefficients of `x^1,...,x^(degree-1)`.  An in-place
/// subset Möbius transform converts the discriminant truth table to its unique
/// multilinear algebraic normal form over `Z/8`; the inverse subset transform
/// must reconstruct every input before the valuation summary is returned.
///
/// # Errors
///
/// Rejects an unsupported degree or a truth table exceeding the caller's
/// explicit degree/table limits, and propagates an exact discriminant failure.
pub fn binary_discriminant_anf_report(
    degree: usize,
    limits: HayesLimits,
) -> Result<BinaryDiscriminantAnfReport, HayesError> {
    if degree == 0 || degree >= u64::BITS as usize {
        return Err(HayesError::InvalidParameter(
            "discriminant ANF requires 1<=degree<64".to_owned(),
        ));
    }
    check_limit("degree", degree, limits.max_degree)?;
    let variable_count = degree - 1;
    let coefficient_count = 1_usize
        .checked_shl(u32::try_from(variable_count).map_err(|_| {
            HayesError::InvalidParameter("discriminant ANF rank exceeds u32".to_owned())
        })?)
        .ok_or_else(|| HayesError::InvalidParameter("discriminant ANF size overflow".to_owned()))?;
    check_limit(
        "discriminant_anf_cells",
        coefficient_count,
        limits.max_table_cells,
    )?;
    let mut coefficients = Vec::with_capacity(coefficient_count);
    for middle in 0..coefficient_count {
        let middle_u64 = u64::try_from(middle).map_err(|_| {
            HayesError::InvalidParameter("discriminant ANF index exceeds u64".to_owned())
        })?;
        let polynomial = (1_u64 << degree) | (middle_u64 << 1) | 1;
        coefficients.push(binary_integral_discriminant_residue_mod_eight(
            polynomial, degree,
        )?);
    }
    let truth_table = coefficients.clone();
    for bit in 0..variable_count {
        for mask in 0..coefficient_count {
            if mask >> bit & 1 != 0 {
                coefficients[mask] = (coefficients[mask] + 8 - coefficients[mask ^ (1 << bit)]) % 8;
            }
        }
    }
    let mut reconstructed = coefficients.clone();
    for bit in 0..variable_count {
        for mask in 0..coefficient_count {
            if mask >> bit & 1 != 0 {
                reconstructed[mask] = (reconstructed[mask] + reconstructed[mask ^ (1 << bit)]) % 8;
            }
        }
    }
    if reconstructed != truth_table {
        return Err(HayesError::Invariant(
            "discriminant ANF does not reconstruct its truth table".to_owned(),
        ));
    }
    let full_support_coefficient_mod_eight = coefficients[coefficient_count - 1];
    let squarefree_count = binary_constant_one_squarefree_count(degree)?;
    if full_support_coefficient_mod_eight % 2 != u8::from(squarefree_count % 2 != 0)
        || full_support_coefficient_mod_eight.is_multiple_of(2)
    {
        return Err(HayesError::Invariant(
            "top discriminant ANF coefficient misses squarefree-count parity".to_owned(),
        ));
    }
    let mut rows = (0..=variable_count)
        .map(|support_degree| BinaryDiscriminantAnfDegreeRow {
            support_degree,
            odd_coefficient_count: 0,
            twice_odd_coefficient_count: 0,
            four_coefficient_count: 0,
        })
        .collect::<Vec<_>>();
    for (mask, coefficient) in coefficients.into_iter().enumerate() {
        let support_degree = mask.count_ones() as usize;
        let row = &mut rows[support_degree];
        match coefficient {
            1 | 3 | 5 | 7 => row.odd_coefficient_count += 1,
            2 | 6 => row.twice_odd_coefficient_count += 1,
            4 => row.four_coefficient_count += 1,
            0 => {}
            _ => unreachable!("coefficient reduced modulo eight"),
        }
    }
    let maximum = |select: fn(&BinaryDiscriminantAnfDegreeRow) -> usize| {
        rows.iter()
            .rev()
            .find(|row| select(row) != 0)
            .map(|row| row.support_degree)
    };
    Ok(BinaryDiscriminantAnfReport {
        polynomial_degree: degree,
        variable_count,
        coefficient_count,
        full_support_coefficient_mod_eight,
        max_odd_support_degree: maximum(|row| row.odd_coefficient_count),
        max_twice_odd_support_degree: maximum(|row| row.twice_odd_coefficient_count),
        max_four_support_degree: maximum(|row| row.four_coefficient_count),
        rows,
    })
}

fn mod_eight_anf_coefficients(
    truth_table: &[u8],
    variable_count: usize,
) -> Result<Vec<u8>, HayesError> {
    let expected = 1_usize
        .checked_shl(u32::try_from(variable_count).map_err(|_| {
            HayesError::InvalidParameter("mod-eight ANF rank exceeds u32".to_owned())
        })?)
        .ok_or_else(|| HayesError::InvalidParameter("mod-eight ANF size overflow".to_owned()))?;
    if truth_table.len() != expected || truth_table.iter().any(|&value| value >= 8) {
        return Err(HayesError::InvalidParameter(
            "mod-eight ANF truth table has the wrong shape".to_owned(),
        ));
    }
    let mut coefficients = truth_table.to_vec();
    for bit in 0..variable_count {
        for mask in 0..expected {
            if mask >> bit & 1 != 0 {
                coefficients[mask] = (coefficients[mask] + 8 - coefficients[mask ^ (1 << bit)]) % 8;
            }
        }
    }
    let mut reconstructed = coefficients.clone();
    for bit in 0..variable_count {
        for mask in 0..expected {
            if mask >> bit & 1 != 0 {
                reconstructed[mask] = (reconstructed[mask] + reconstructed[mask ^ (1 << bit)]) % 8;
            }
        }
    }
    if reconstructed != truth_table {
        return Err(HayesError::Invariant(
            "mod-eight ANF does not reconstruct its truth table".to_owned(),
        ));
    }
    Ok(coefficients)
}

fn affine_binary_coordinates(members: &[usize]) -> Result<BTreeMap<usize, usize>, HayesError> {
    let Some(&origin) = members.first() else {
        return Err(HayesError::InvalidParameter(
            "affine coordinate recovery requires a point".to_owned(),
        ));
    };
    let mut difference_to_coordinate = BTreeMap::from([(0_usize, 0_usize)]);
    let mut dimension = 0_usize;
    for &member in members {
        let difference = member ^ origin;
        if difference_to_coordinate.contains_key(&difference) {
            continue;
        }
        let coordinate_bit = 1_usize
            .checked_shl(u32::try_from(dimension).map_err(|_| {
                HayesError::InvalidParameter("affine fibre rank exceeds u32".to_owned())
            })?)
            .ok_or_else(|| HayesError::InvalidParameter("affine fibre size overflow".to_owned()))?;
        let existing = difference_to_coordinate
            .iter()
            .map(|(&vector, &coordinate)| (vector, coordinate))
            .collect::<Vec<_>>();
        for (vector, coordinate) in existing {
            difference_to_coordinate.insert(vector ^ difference, coordinate | coordinate_bit);
        }
        dimension += 1;
    }
    if difference_to_coordinate.len() != members.len()
        || members
            .iter()
            .any(|member| !difference_to_coordinate.contains_key(&(member ^ origin)))
    {
        return Err(HayesError::Invariant(
            "exact inverse-difference fibre is not affine".to_owned(),
        ));
    }
    Ok(difference_to_coordinate)
}

fn mod_eight_anf_maxima(coefficients: &[u8]) -> (Option<usize>, Option<usize>, Option<usize>) {
    let mut odd = None;
    let mut twice = None;
    let mut four = None;
    for (mask, &coefficient) in coefficients.iter().enumerate() {
        let support = mask.count_ones() as usize;
        match coefficient {
            1 | 3 | 5 | 7 => odd = Some(odd.map_or(support, |value: usize| value.max(support))),
            2 | 6 => twice = Some(twice.map_or(support, |value: usize| value.max(support))),
            4 => four = Some(four.map_or(support, |value: usize| value.max(support))),
            _ => {}
        }
    }
    (odd, twice, four)
}

struct BinaryDyadicDiscriminantData {
    squarefree_residue: Option<u8>,
    residue: u8,
    is_odd: bool,
    kronecker_two: i8,
}

fn binary_dyadic_discriminant_data(
    polynomial: u64,
    degree: usize,
    mobius: i8,
) -> Result<BinaryDyadicDiscriminantData, HayesError> {
    let derivative = binary_formal_derivative(polynomial, degree);
    let is_odd = polynomial_gcd_packed(polynomial, derivative) == 1;
    if is_odd != (mobius != 0) {
        return Err(HayesError::Invariant(
            "discriminant parity and factorization disagree on squarefreeness".to_owned(),
        ));
    }
    let residue = binary_integral_discriminant_residue_mod_eight(polynomial, degree)?;
    if residue % 2 != u8::from(is_odd) {
        return Err(HayesError::Invariant(
            "integer discriminant residue and binary derivative gcd disagree".to_owned(),
        ));
    }
    let squarefree_residue = is_odd
        .then(|| binary_integral_discriminant_mod_eight(polynomial, degree))
        .transpose()?;
    if squarefree_residue.is_some_and(|fast| fast != residue) {
        return Err(HayesError::Invariant(
            "modular and fraction-free discriminants disagree modulo eight".to_owned(),
        ));
    }
    let kronecker_two = kronecker_two_mod_eight(residue);
    let degree_sign = if degree.is_multiple_of(2) { 1 } else { -1 };
    if degree_sign * kronecker_two != mobius {
        return Err(HayesError::Invariant(
            "dyadic discriminant character and polynomial Mobius value disagree".to_owned(),
        ));
    }
    Ok(BinaryDyadicDiscriminantData {
        squarefree_residue,
        residue,
        is_odd,
        kronecker_two,
    })
}

/// Compare factorization, the dyadic discriminant character,
/// Stickelberger--Swan, and second-trace Arf signs for one monic constant-one
/// binary polynomial.
///
/// # Errors
///
/// Rejects an invalid packed polynomial or degree and any disagreement among
/// the three exact squarefree sign routes.
pub fn binary_second_trace_arf_report(
    polynomial: u64,
    degree: usize,
) -> Result<BinarySecondTraceArfReport, HayesError> {
    if degree == 0 || degree >= u64::BITS as usize {
        return Err(HayesError::InvalidParameter(
            "second-trace report requires 1<=degree<64".to_owned(),
        ));
    }
    if polynomial >> degree != 1 || polynomial & 1 == 0 {
        return Err(HayesError::InvalidParameter(
            "second-trace report requires a packed monic constant-one polynomial".to_owned(),
        ));
    }
    let mobius = binary_polynomial_mobius_from_bits(polynomial, degree)?;
    let dyadic = binary_dyadic_discriminant_data(polynomial, degree, mobius)?;
    let basis = binary_second_trace_space_basis(polynomial, degree)?;
    let dimension = basis.len();
    let polar_rows = basis
        .iter()
        .map(|&left| {
            basis
                .iter()
                .enumerate()
                .fold(0_u64, |row, (index, &right)| {
                    row | (u64::from(binary_second_trace_polar(left, right, polynomial, degree))
                        << index)
                })
        })
        .collect::<Vec<_>>();
    let polar_rank = binary_matrix_rank(polar_rows, dimension);
    let correction = u8::from(matches!(degree % 8, 3..=6));
    let (arf_invariant, sign_phase) = if mobius == 0 {
        (None, None)
    } else {
        let discriminant = dyadic.squarefree_residue.ok_or_else(|| {
            HayesError::Invariant("squarefree polynomial has no discriminant phase".to_owned())
        })?;
        if !matches!(discriminant, 1 | 5) || polar_rank != dimension {
            return Err(HayesError::Invariant(
                "squarefree second-trace invariants have the wrong shape".to_owned(),
            ));
        }
        let swan_phase = (discriminant - 1) / 4;
        let arf = binary_second_trace_arf(polynomial, degree, basis)?;
        if arf ^ correction != swan_phase {
            return Err(HayesError::Invariant(
                "Arf and Stickelberger--Swan phases disagree".to_owned(),
            ));
        }
        let expected_mobius = if (degree + usize::from(swan_phase)).is_multiple_of(2) {
            1
        } else {
            -1
        };
        if mobius != expected_mobius {
            return Err(HayesError::Invariant(
                "factorization and Stickelberger--Swan signs disagree".to_owned(),
            ));
        }
        (Some(arf), Some(swan_phase))
    };
    Ok(BinarySecondTraceArfReport {
        polynomial,
        degree,
        mobius,
        integral_discriminant_mod_eight: dyadic.squarefree_residue,
        integral_discriminant_residue_mod_eight: dyadic.residue,
        integral_discriminant_is_odd: dyadic.is_odd,
        kronecker_two_discriminant: dyadic.kronecker_two,
        trace_form_dimension: dimension,
        polar_rank,
        radical_dimension: dimension - polar_rank,
        arf_invariant,
        arf_degree_correction: correction,
        sign_phase,
    })
}

fn binary_polynomial_mobius_from_bits(polynomial: u64, degree: usize) -> Result<i8, HayesError> {
    let coefficients = (0..=degree)
        .map(|index| i128::from((polynomial >> index) & 1))
        .collect::<Vec<_>>();
    let factors = crate::gfp::factor_berlekamp(&coefficients, 2).ok_or_else(|| {
        HayesError::Invariant("binary Berlekamp factorization declined".to_owned())
    })?;
    if factors.iter().any(|(_, multiplicity)| *multiplicity != 1) {
        Ok(0)
    } else if factors.len().is_multiple_of(2) {
        Ok(1)
    } else {
        Ok(-1)
    }
}

struct BinaryBerlekampPhaseDomain {
    input_count: usize,
    coset_size: usize,
    residue_mask: u64,
    frequency: u64,
}

fn admit_binary_berlekamp_phase_domain(
    ell: usize,
    degree: usize,
    frequency: usize,
    shift_dimension: usize,
    limits: HayesLimits,
) -> Result<BinaryBerlekampPhaseDomain, HayesError> {
    admit_any_positive_degree(ell, degree, limits)?;
    if degree >= u64::BITS as usize || ell >= u64::BITS as usize {
        return Err(HayesError::InvalidParameter(
            "Berlekamp phase diagnostic requires ell,degree<64".to_owned(),
        ));
    }
    let free_coefficients = degree - 1;
    if shift_dimension > free_coefficients {
        return Err(HayesError::InvalidParameter(format!(
            "shift dimension {shift_dimension} exceeds {free_coefficients} free coefficients"
        )));
    }
    let frequency_count = 1_usize
        .checked_shl(u32::try_from(ell).map_err(|_| {
            HayesError::InvalidParameter("Berlekamp frequency shift exceeds u32".to_owned())
        })?)
        .ok_or_else(|| HayesError::InvalidParameter("Berlekamp frequency overflow".to_owned()))?;
    if frequency >= frequency_count {
        return Err(HayesError::InvalidParameter(format!(
            "frequency {frequency} is outside 0..{frequency_count}"
        )));
    }
    let input_count = 1_usize
        .checked_shl(u32::try_from(free_coefficients).map_err(|_| {
            HayesError::InvalidParameter("Berlekamp enumeration shift exceeds u32".to_owned())
        })?)
        .ok_or_else(|| HayesError::InvalidParameter("Berlekamp enumeration overflow".to_owned()))?;
    let factor_work = degree
        .checked_add(1)
        .and_then(|value| value.checked_mul(value))
        .and_then(|value| value.checked_mul(input_count))
        .ok_or_else(|| {
            HayesError::InvalidParameter("Berlekamp work estimate overflow".to_owned())
        })?;
    check_limit("berlekamp_phase_cells", factor_work, limits.max_table_cells)?;
    let coset_size = 1_usize
        .checked_shl(u32::try_from(shift_dimension).map_err(|_| {
            HayesError::InvalidParameter("Berlekamp coset shift exceeds u32".to_owned())
        })?)
        .ok_or_else(|| HayesError::InvalidParameter("Berlekamp coset size overflow".to_owned()))?;
    Ok(BinaryBerlekampPhaseDomain {
        input_count,
        coset_size,
        residue_mask: if ell + 1 == u64::BITS as usize {
            u64::MAX
        } else {
            (1_u64 << (ell + 1)) - 1
        },
        frequency: u64::try_from(frequency).map_err(|_| {
            HayesError::InvalidParameter("Berlekamp frequency exceeds u64".to_owned())
        })?,
    })
}

struct BinaryBerlekampPhaseSummary {
    positive: u128,
    negative: u128,
    stationary_same_sign_pairs: u128,
    oscillating_opposite_sign_pairs: u128,
    shift_subspace_energy: u128,
}

fn summarize_binary_berlekamp_phase_cosets(
    positive_by_coset: Vec<u128>,
    negative_by_coset: Vec<u128>,
) -> Result<BinaryBerlekampPhaseSummary, HayesError> {
    let mut summary = BinaryBerlekampPhaseSummary {
        positive: 0,
        negative: 0,
        stationary_same_sign_pairs: 0,
        oscillating_opposite_sign_pairs: 0,
        shift_subspace_energy: 0,
    };
    for (positive, negative) in positive_by_coset.into_iter().zip(negative_by_coset) {
        summary.positive = summary.positive.checked_add(positive).ok_or_else(|| {
            HayesError::InvalidParameter("Berlekamp positive count overflow".to_owned())
        })?;
        summary.negative = summary.negative.checked_add(negative).ok_or_else(|| {
            HayesError::InvalidParameter("Berlekamp negative count overflow".to_owned())
        })?;
        summary.stationary_same_sign_pairs = summary
            .stationary_same_sign_pairs
            .checked_add(positive * positive + negative * negative)
            .ok_or_else(|| {
                HayesError::InvalidParameter("Berlekamp stationary-pair count overflow".to_owned())
            })?;
        summary.oscillating_opposite_sign_pairs = summary
            .oscillating_opposite_sign_pairs
            .checked_add(2 * positive * negative)
            .ok_or_else(|| {
                HayesError::InvalidParameter("Berlekamp oscillating-pair count overflow".to_owned())
            })?;
        let imbalance = positive.abs_diff(negative);
        summary.shift_subspace_energy = summary
            .shift_subspace_energy
            .checked_add(imbalance * imbalance)
            .ok_or_else(|| {
                HayesError::InvalidParameter("Berlekamp shift energy overflow".to_owned())
            })?;
    }
    if summary
        .stationary_same_sign_pairs
        .checked_sub(summary.oscillating_opposite_sign_pairs)
        != Some(summary.shift_subspace_energy)
    {
        return Err(HayesError::Invariant(
            "Berlekamp stationary-pair counts do not recover shift energy".to_owned(),
        ));
    }
    Ok(summary)
}

/// Classify the kernel of `z -> z^2+h z` in a truncated binary local ring.
///
/// Write `r=modulus_degree` and `v=ord_x(h)`.  Factoring the map as
/// `z(z+h)` gives the exact dimension
///
/// ```text
/// dim ker = v+1       when 2v<r,
///           floor(r/2) when 2v>=r,
/// ```
///
/// while `h=0 mod x^r` has the second value.  Thus every nonempty affine
/// equation `f^2+h f=a mod x^r` has exactly the reported number of solutions.
///
/// # Errors
///
/// Rejects the zero ring and a kernel size outside the exact `u128` domain.
pub fn binary_artin_schreier_kernel_report(
    modulus_degree: usize,
    shift_valuation: Option<usize>,
) -> Result<BinaryArtinSchreierKernelReport, HayesError> {
    if modulus_degree == 0 {
        return Err(HayesError::InvalidParameter(
            "Artin--Schreier modulus degree must be positive".to_owned(),
        ));
    }
    let kernel_dimension = match shift_valuation.filter(|&value| value < modulus_degree) {
        Some(valuation) if valuation < modulus_degree - valuation => valuation + 1,
        Some(_) | None => modulus_degree / 2,
    };
    let kernel_size = 1_u128
        .checked_shl(u32::try_from(kernel_dimension).map_err(|_| {
            HayesError::InvalidParameter("Artin--Schreier kernel shift exceeds u32".to_owned())
        })?)
        .ok_or_else(|| {
            HayesError::InvalidParameter("Artin--Schreier kernel exceeds u128".to_owned())
        })?;
    Ok(BinaryArtinSchreierKernelReport {
        modulus_degree,
        shift_valuation,
        kernel_dimension,
        kernel_size,
    })
}

/// Check the inverse-difference parallelogram identity in
/// `GF(2)[x]/x^(ell+1)`.
///
/// # Errors
///
/// Rejects unsupported truncations, a non-unit input, shifts with nonzero
/// constant coefficient, or packed values outside the quotient.
pub fn binary_inverse_difference_parallelogram_report(
    ell: usize,
    input_unit: u64,
    first_shift: u64,
    second_shift: u64,
) -> Result<BinaryInverseDifferenceParallelogramReport, HayesError> {
    if ell == 0 || ell >= 32 {
        return Err(HayesError::InvalidParameter(
            "inverse-difference parallelogram requires 1<=ell<32".to_owned(),
        ));
    }
    let mask = (1_u64 << (ell + 1)) - 1;
    if input_unit & !mask != 0
        || first_shift & !mask != 0
        || second_shift & !mask != 0
        || input_unit & 1 == 0
        || first_shift & 1 != 0
        || second_shift & 1 != 0
    {
        return Err(HayesError::InvalidParameter(
            "parallelogram inputs have the wrong quotient or constant term".to_owned(),
        ));
    }
    let translated = input_unit ^ second_shift;
    let inverse_difference = principal_unit_inverse(input_unit, ell)
        ^ principal_unit_inverse(input_unit ^ first_shift, ell);
    let translated_inverse_difference = principal_unit_inverse(translated, ell)
        ^ principal_unit_inverse(translated ^ first_shift, ell);
    let first_product = polynomial_multiply_packed(first_shift, second_shift) & mask;
    let annihilator_product =
        polynomial_multiply_packed(first_product, first_shift ^ second_shift) & mask;
    let inverse_differences_equal = inverse_difference == translated_inverse_difference;
    let annihilator_product_vanishes = annihilator_product == 0;
    if inverse_differences_equal != annihilator_product_vanishes {
        return Err(HayesError::Invariant(
            "inverse-difference equality misses h*t*(t+h) annihilation".to_owned(),
        ));
    }
    Ok(BinaryInverseDifferenceParallelogramReport {
        ell,
        input_unit,
        first_shift,
        second_shift,
        inverse_difference,
        translated_inverse_difference,
        annihilator_product,
        inverse_differences_equal,
        annihilator_product_vanishes,
    })
}

fn binary_berlekamp_shift_correlations(
    mobius: &[i8],
    inverse_cosets: &[usize],
    ell: usize,
    degree: usize,
    interval_degree: usize,
    shift_dimension: usize,
    limits: HayesLimits,
) -> Result<Vec<BinaryBerlekampShiftCorrelation>, HayesError> {
    if mobius.len() != inverse_cosets.len() {
        return Err(HayesError::Invariant(
            "Berlekamp shift arrays have different lengths".to_owned(),
        ));
    }
    let shift_count = 1_usize
        .checked_shl(u32::try_from(shift_dimension).map_err(|_| {
            HayesError::InvalidParameter("Berlekamp correlation shift exceeds u32".to_owned())
        })?)
        .ok_or_else(|| {
            HayesError::InvalidParameter("Berlekamp correlation shift overflow".to_owned())
        })?;
    let work = mobius.len().checked_mul(shift_count).ok_or_else(|| {
        HayesError::InvalidParameter("Berlekamp correlation work overflow".to_owned())
    })?;
    check_limit("berlekamp_correlation_cells", work, limits.max_table_cells)?;
    let mut correlations = Vec::with_capacity(shift_count);
    for shift in 0..shift_count {
        let mut supported_pairs = 0_u128;
        let mut signed_correlation = 0_i128;
        for index in 0..mobius.len() {
            let other = index ^ shift;
            let left = mobius[index];
            let right = mobius[other];
            if left == 0 || right == 0 || inverse_cosets[index] != inverse_cosets[other] {
                continue;
            }
            supported_pairs = supported_pairs.checked_add(1).ok_or_else(|| {
                HayesError::InvalidParameter("Berlekamp supported-pair overflow".to_owned())
            })?;
            signed_correlation = signed_correlation
                .checked_add(i128::from(left) * i128::from(right))
                .ok_or_else(|| {
                    HayesError::InvalidParameter("Berlekamp correlation overflow".to_owned())
                })?;
        }
        let valuation = (shift != 0).then(|| shift.trailing_zeros() as usize + 1);
        let artin_schreier = valuation
            .map(|valuation| {
                binary_artin_schreier_kernel_report(
                    ell.checked_add(1)
                        .and_then(|value| value.checked_sub(valuation))
                        .ok_or_else(|| {
                            HayesError::InvalidParameter(
                                "Berlekamp Artin--Schreier modulus underflow".to_owned(),
                            )
                        })?,
                    Some(valuation),
                )
            })
            .transpose()?;
        let support_upper_bound = if let Some(report) = artin_schreier {
            let exponent = degree
                .checked_add(interval_degree)
                .and_then(|value| value.checked_sub(ell + 1))
                .and_then(|value| value.checked_add(report.kernel_dimension));
            exponent
                .and_then(|value| u32::try_from(value).ok())
                .and_then(|value| 1_u128.checked_shl(value))
                .unwrap_or(mobius.len() as u128)
                .min(mobius.len() as u128)
        } else {
            supported_pairs
        };
        if supported_pairs > support_upper_bound {
            return Err(HayesError::Invariant(
                "Berlekamp shift support exceeds its Artin--Schreier fibre bound".to_owned(),
            ));
        }
        correlations.push(BinaryBerlekampShiftCorrelation {
            shift,
            valuation,
            supported_pairs,
            signed_correlation,
            artin_schreier_modulus_degree: artin_schreier.map(|report| report.modulus_degree),
            artin_schreier_kernel_dimension: artin_schreier.map(|report| report.kernel_dimension),
            support_upper_bound,
        });
    }
    Ok(correlations)
}

fn check_binary_berlekamp_shift_totals(
    correlations: &[BinaryBerlekampShiftCorrelation],
    signed_coset_energy: &BigUint,
    unsigned_collision_count: &BigUint,
) -> Result<(), HayesError> {
    let signed_total = correlations.iter().try_fold(0_i128, |sum, correlation| {
        sum.checked_add(correlation.signed_correlation)
            .ok_or_else(|| {
                HayesError::InvalidParameter("Berlekamp correlation total overflow".to_owned())
            })
    })?;
    let unsigned_total = correlations.iter().try_fold(0_u128, |sum, correlation| {
        sum.checked_add(correlation.supported_pairs)
            .ok_or_else(|| HayesError::InvalidParameter("Berlekamp pair total overflow".to_owned()))
    })?;
    if BigInt::from(signed_total) != BigInt::from(signed_coset_energy.clone())
        || BigUint::from(unsigned_total) != *unsigned_collision_count
    {
        return Err(HayesError::Invariant(
            "Berlekamp shift correlations do not recover coset energies".to_owned(),
        ));
    }
    Ok(())
}

type BinaryBerlekampCosetBuckets = BTreeMap<(usize, usize), (i128, u128)>;

struct BinaryBerlekampCosetEnumeration {
    buckets: BinaryBerlekampCosetBuckets,
    mobius_values: Vec<i8>,
    inverse_cosets: Vec<usize>,
    inverse_interval_phase_sum: i128,
}

fn enumerate_binary_berlekamp_cosets(
    domain: &BinaryBerlekampPhaseDomain,
    degree: usize,
    ell: usize,
    interval_degree: usize,
) -> Result<BinaryBerlekampCosetEnumeration, HayesError> {
    let mut buckets = BinaryBerlekampCosetBuckets::new();
    let mut mobius_values = vec![0_i8; domain.input_count];
    let mut inverse_cosets = vec![0_usize; domain.input_count];
    let mut inverse_interval_phase_sum = 0_i128;
    for middle in 0..domain.input_count {
        let middle_u64 = u64::try_from(middle).map_err(|_| {
            HayesError::InvalidParameter("Berlekamp polynomial index exceeds u64".to_owned())
        })?;
        let polynomial = (1_u64 << degree) | (middle_u64 << 1) | 1;
        let mobius = binary_polynomial_mobius_from_bits(polynomial, degree)?;
        if mobius == 0 {
            continue;
        }
        let packed_inverse = principal_unit_inverse(polynomial & domain.residue_mask, ell) >> 1;
        let inverse_coset = usize::try_from(packed_inverse).map_err(|_| {
            HayesError::InvalidParameter("packed inverse coset exceeds usize".to_owned())
        })? >> interval_degree;
        mobius_values[middle] = mobius;
        inverse_cosets[middle] = inverse_coset;
        let entry = buckets
            .entry((middle / domain.coset_size, inverse_coset))
            .or_insert((0, 0));
        entry.0 = entry
            .0
            .checked_add(i128::from(mobius))
            .ok_or_else(|| HayesError::InvalidParameter("coset Mobius sum overflow".to_owned()))?;
        entry.1 = entry
            .1
            .checked_add(1)
            .ok_or_else(|| HayesError::InvalidParameter("coset population overflow".to_owned()))?;
        if inverse_coset == 0 {
            inverse_interval_phase_sum = inverse_interval_phase_sum
                .checked_add(i128::from(mobius))
                .ok_or_else(|| {
                    HayesError::InvalidParameter("inverse-interval phase sum overflow".to_owned())
                })?;
        }
    }
    Ok(BinaryBerlekampCosetEnumeration {
        buckets,
        mobius_values,
        inverse_cosets,
        inverse_interval_phase_sum,
    })
}

fn binary_second_trace_truth_tables(
    buckets: &BTreeMap<(usize, usize), Vec<usize>>,
    input_count: usize,
    degree: usize,
    vector_count: usize,
) -> Result<Vec<Option<Vec<u8>>>, HayesError> {
    let mut truth_tables = vec![None; input_count];
    for members in buckets.values() {
        for &middle in members {
            let middle_u64 = u64::try_from(middle).map_err(|_| {
                HayesError::InvalidParameter("second-trace index exceeds u64".to_owned())
            })?;
            let polynomial = (1_u64 << degree) | (middle_u64 << 1) | 1;
            truth_tables[middle] = Some(
                (0..vector_count)
                    .map(|vector| binary_second_trace_value(vector as u64, polynomial, degree))
                    .collect::<Vec<_>>(),
            );
        }
    }
    Ok(truth_tables)
}

fn binary_second_trace_difference_geometry(
    left: &[u8],
    right: &[u8],
    degree: usize,
) -> Result<(usize, usize, bool), HayesError> {
    let value = |vector: usize| left[vector] ^ right[vector];
    let polar_rows = (0..degree)
        .map(|row| {
            (0..degree).fold(0_u64, |bits, column| {
                let polar =
                    value(1 << row) ^ value(1 << column) ^ value((1 << row) ^ (1 << column));
                bits | (u64::from(polar) << column)
            })
        })
        .collect::<Vec<_>>();
    let polar_rank = binary_matrix_rank(polar_rows.clone(), degree);
    if !polar_rank.is_multiple_of(2) {
        return Err(HayesError::Invariant(
            "alternating second-trace difference has odd rank".to_owned(),
        ));
    }
    let radical_basis = binary_matrix_nullspace_basis(polar_rows, degree);
    let radical_dimension = radical_basis.len();
    let phase_nontrivial_on_radical = radical_basis.iter().try_fold(false, |found, &vector| {
        let vector = usize::try_from(vector).map_err(|_| {
            HayesError::InvalidParameter("second-trace radical vector exceeds usize".to_owned())
        })?;
        Ok::<_, HayesError>(found || value(vector) != 0)
    })?;
    let signed_gauss_sum = (0..left.len()).fold(0_i128, |sum, vector| {
        sum + if value(vector) == 0 { 1 } else { -1 }
    });
    let expected_magnitude = if phase_nontrivial_on_radical {
        0
    } else {
        1_i128 << (degree - polar_rank / 2)
    };
    if signed_gauss_sum.abs() != expected_magnitude {
        return Err(HayesError::Invariant(
            "second-trace difference Gauss classification failed".to_owned(),
        ));
    }
    Ok((polar_rank, radical_dimension, phase_nontrivial_on_radical))
}

type BinarySecondTraceDifferenceTypes = (
    Vec<BinarySecondTraceDifferenceType>,
    Option<usize>,
    Vec<BinarySecondTraceDifferenceWitness>,
);

fn classify_binary_second_trace_bucket_pairs(
    buckets: &BTreeMap<(usize, usize), Vec<usize>>,
    truth_tables: &[Option<Vec<u8>>],
    degree: usize,
    expected_pair_count: u128,
) -> Result<BinarySecondTraceDifferenceTypes, HayesError> {
    let mut type_counts = BTreeMap::<(usize, usize, bool), (u128, usize, usize, u64, u64)>::new();
    let mut minimum_rank = None;
    let mut minimum_witnesses = Vec::new();
    for (&(input_coset, inverse_coset), members) in buckets {
        for left_index in 0..members.len() {
            for right_index in left_index + 1..members.len() {
                let left = truth_tables[members[left_index]].as_ref().ok_or_else(|| {
                    HayesError::Invariant("missing left second-trace truth table".to_owned())
                })?;
                let right = truth_tables[members[right_index]].as_ref().ok_or_else(|| {
                    HayesError::Invariant("missing right second-trace truth table".to_owned())
                })?;
                let (rank, radical_dimension, nontrivial) =
                    binary_second_trace_difference_geometry(left, right, degree)?;
                let left_polynomial = (1_u64 << degree) | ((members[left_index] as u64) << 1) | 1;
                let right_polynomial = (1_u64 << degree) | ((members[right_index] as u64) << 1) | 1;
                if !nontrivial && minimum_rank.is_none_or(|minimum| rank <= minimum) {
                    if minimum_rank.is_none_or(|minimum| rank < minimum) {
                        minimum_rank = Some(rank);
                        minimum_witnesses.clear();
                    }
                    minimum_witnesses.push(BinarySecondTraceDifferenceWitness {
                        input_coset,
                        inverse_coset,
                        left_polynomial,
                        right_polynomial,
                        polynomial_difference: left_polynomial ^ right_polynomial,
                        polar_rank: rank,
                    });
                }
                type_counts
                    .entry((rank, radical_dimension, nontrivial))
                    .and_modify(|entry| entry.0 += 1)
                    .or_insert((
                        1,
                        input_coset,
                        inverse_coset,
                        left_polynomial,
                        right_polynomial,
                    ));
            }
        }
    }
    if type_counts.values().map(|entry| entry.0).sum::<u128>() != expected_pair_count {
        return Err(HayesError::Invariant(
            "second-trace difference types do not partition the pairs".to_owned(),
        ));
    }
    let types = type_counts
        .into_iter()
        .map(
            |((rank, radical_dimension, nontrivial), data)| BinarySecondTraceDifferenceType {
                polar_rank: rank,
                radical_dimension,
                phase_nontrivial_on_radical: nontrivial,
                pair_count: data.0,
                first_input_coset: data.1,
                first_inverse_coset: data.2,
                first_left_polynomial: data.3,
                first_right_polynomial: data.4,
            },
        )
        .collect();
    Ok((types, minimum_rank, minimum_witnesses))
}

/// Classify pairwise differences of second-trace quadratic forms inside each
/// simultaneous coefficient/inverse bucket.
///
/// This retains `Q_f(y)=T_2(m_y)` on the common coefficient space.  For every
/// unordered distinct squarefree pair it computes polar rank, tests the phase
/// on the radical, and independently verifies the binary quadratic Gauss sum.
/// The result is a structural diagnostic, not a cancellation theorem.
///
/// # Errors
///
/// Rejects invalid parameters, resource violations, or a failed exact Gauss
/// classification.
pub fn binary_second_trace_bucket_difference_report(
    ell: usize,
    degree: usize,
    interval_degree: usize,
    limits: HayesLimits,
) -> Result<BinarySecondTraceBucketDifferenceReport, HayesError> {
    if interval_degree == 0 || interval_degree >= ell {
        return Err(HayesError::InvalidParameter(format!(
            "second-trace bucket interval must satisfy 1<=d<ell, got d={interval_degree}, ell={ell}"
        )));
    }
    let domain = admit_binary_berlekamp_phase_domain(ell, degree, 0, interval_degree, limits)?;
    let enumeration = enumerate_binary_berlekamp_cosets(&domain, degree, ell, interval_degree)?;
    let mut buckets = BTreeMap::<(usize, usize), Vec<usize>>::new();
    for middle in 0..domain.input_count {
        if enumeration.mobius_values[middle] != 0 {
            buckets
                .entry((
                    middle / domain.coset_size,
                    enumeration.inverse_cosets[middle],
                ))
                .or_default()
                .push(middle);
        }
    }
    let squarefree_count = buckets.values().map(Vec::len).sum::<usize>();
    let unordered_pair_count = buckets.values().try_fold(0_u128, |total, members| {
        let population = u128::try_from(members.len()).map_err(|_| {
            HayesError::InvalidParameter("second-trace bucket population exceeds u128".to_owned())
        })?;
        total
            .checked_add(population.saturating_sub(1) * population / 2)
            .ok_or_else(|| {
                HayesError::InvalidParameter("second-trace pair count overflow".to_owned())
            })
    })?;
    let vector_count = 1_usize
        .checked_shl(u32::try_from(degree).map_err(|_| {
            HayesError::InvalidParameter("second-trace vector dimension exceeds u32".to_owned())
        })?)
        .ok_or_else(|| {
            HayesError::InvalidParameter("second-trace vector count overflow".to_owned())
        })?;
    let truth_cells = squarefree_count.checked_mul(vector_count).ok_or_else(|| {
        HayesError::InvalidParameter("second-trace truth-table work overflow".to_owned())
    })?;
    let pair_cells = usize::try_from(unordered_pair_count)
        .ok()
        .and_then(|pairs| pairs.checked_mul(vector_count))
        .ok_or_else(|| {
            HayesError::InvalidParameter("second-trace pair work overflow".to_owned())
        })?;
    let work = truth_cells.checked_add(pair_cells).ok_or_else(|| {
        HayesError::InvalidParameter("second-trace total work overflow".to_owned())
    })?;
    check_limit(
        "second_trace_difference_cells",
        work,
        limits.max_table_cells,
    )?;

    let truth_tables =
        binary_second_trace_truth_tables(&buckets, domain.input_count, degree, vector_count)?;
    let (types, minimum_nonzero_gauss_rank, minimum_rank_witnesses) =
        classify_binary_second_trace_bucket_pairs(
            &buckets,
            &truth_tables,
            degree,
            unordered_pair_count,
        )?;
    Ok(BinarySecondTraceBucketDifferenceReport {
        ell,
        degree,
        interval_degree,
        occupied_bucket_count: buckets.len(),
        squarefree_count,
        unordered_pair_count,
        types,
        minimum_nonzero_gauss_rank,
        minimum_rank_witnesses,
    })
}

struct BinaryBerlekampCosetSummary {
    signed_energy: BigUint,
    unsigned_collisions: BigUint,
    worst_bucket: (usize, usize, BigUint, u128),
}

fn summarize_binary_berlekamp_cosets(
    buckets: &BinaryBerlekampCosetBuckets,
) -> Result<BinaryBerlekampCosetSummary, HayesError> {
    let mut signed_energy = BigUint::from(0_u8);
    let mut unsigned_collisions = BigUint::from(0_u8);
    let mut worst_bucket = (0_usize, 0_usize, BigUint::from(0_u8), 1_u128);
    for (&(input_coset, inverse_coset), &(signed, population)) in buckets {
        let signed_square = BigUint::from(signed.unsigned_abs()).pow(2);
        signed_energy += &signed_square;
        unsigned_collisions += BigUint::from(population).pow(2);
        if &signed_square * BigUint::from(worst_bucket.3)
            > &worst_bucket.2 * BigUint::from(population)
        {
            worst_bucket = (input_coset, inverse_coset, signed_square, population);
        }
    }
    if signed_energy > unsigned_collisions {
        return Err(HayesError::Invariant(
            "signed Berlekamp coset energy exceeds unsigned collisions".to_owned(),
        ));
    }
    Ok(BinaryBerlekampCosetSummary {
        signed_energy,
        unsigned_collisions,
        worst_bucket,
    })
}

struct BinaryBerlekampInvolutionMinima {
    bucket_keys: Vec<(usize, usize)>,
    minimum_defects: Vec<u128>,
    best_translations: Vec<usize>,
}

fn binary_berlekamp_involution_minima(
    domain: &BinaryBerlekampPhaseDomain,
    enumeration: &BinaryBerlekampCosetEnumeration,
) -> Result<BinaryBerlekampInvolutionMinima, HayesError> {
    let bucket_keys = enumeration.buckets.keys().copied().collect::<Vec<_>>();
    let bucket_indices = bucket_keys
        .iter()
        .enumerate()
        .map(|(index, &key)| (key, index))
        .collect::<BTreeMap<_, _>>();
    let mut buckets_by_input = vec![Vec::<usize>::new(); domain.input_count / domain.coset_size];
    for (index, &(input_coset, _)) in bucket_keys.iter().enumerate() {
        buckets_by_input[input_coset].push(index);
    }
    let mut minimum_defects = vec![u128::MAX; bucket_keys.len()];
    let mut best_translations = vec![0_usize; bucket_keys.len()];
    for (input_coset, bucket_group) in buckets_by_input.iter().enumerate() {
        let offset = input_coset * domain.coset_size;
        for translation in 1..domain.coset_size {
            let mut defects = BTreeMap::<usize, u128>::new();
            for left in 0..domain.coset_size {
                let right = left ^ translation;
                if left >= right {
                    continue;
                }
                let left_index = offset + left;
                let right_index = offset + right;
                let left_mobius = enumeration.mobius_values[left_index];
                let right_mobius = enumeration.mobius_values[right_index];
                if left_mobius == 0 && right_mobius == 0 {
                    continue;
                }
                let left_inverse = enumeration.inverse_cosets[left_index];
                let right_inverse = enumeration.inverse_cosets[right_index];
                if left_mobius != 0 && right_mobius != 0 && left_inverse == right_inverse {
                    let bucket = *bucket_indices
                        .get(&(input_coset, left_inverse))
                        .ok_or_else(|| {
                            HayesError::Invariant(
                                "Berlekamp involution pair has no bucket".to_owned(),
                            )
                        })?;
                    let contribution = u128::from(
                        (i16::from(left_mobius) + i16::from(right_mobius)).unsigned_abs(),
                    );
                    let entry = defects.entry(bucket).or_insert(0);
                    *entry = entry.checked_add(contribution).ok_or_else(|| {
                        HayesError::InvalidParameter(
                            "Berlekamp involution defect overflow".to_owned(),
                        )
                    })?;
                } else {
                    for (mobius, inverse) in
                        [(left_mobius, left_inverse), (right_mobius, right_inverse)]
                    {
                        if mobius == 0 {
                            continue;
                        }
                        let bucket =
                            *bucket_indices.get(&(input_coset, inverse)).ok_or_else(|| {
                                HayesError::Invariant(
                                    "Berlekamp involution boundary has no bucket".to_owned(),
                                )
                            })?;
                        let entry = defects.entry(bucket).or_insert(0);
                        *entry = entry.checked_add(1).ok_or_else(|| {
                            HayesError::InvalidParameter(
                                "Berlekamp involution defect overflow".to_owned(),
                            )
                        })?;
                    }
                }
            }
            for &bucket in bucket_group {
                let defect = defects.get(&bucket).copied().unwrap_or(0);
                if defect < minimum_defects[bucket] {
                    minimum_defects[bucket] = defect;
                    best_translations[bucket] = translation;
                }
            }
        }
    }
    Ok(BinaryBerlekampInvolutionMinima {
        bucket_keys,
        minimum_defects,
        best_translations,
    })
}

/// Minimize exact sign-reversing-translation defects in every simultaneous
/// input/inverse coset.
///
/// The result is a bounded finite diagnostic for a possible involution lemma,
/// not universal theorem evidence.
///
/// # Errors
///
/// Returns the same domain, factorization, and resource-limit failures as
/// [`binary_berlekamp_annihilator_energy_report`].
pub fn binary_berlekamp_involution_defect_report(
    ell: usize,
    degree: usize,
    interval_degree: usize,
    limits: HayesLimits,
) -> Result<BinaryBerlekampInvolutionDefectReport, HayesError> {
    if interval_degree == 0 || interval_degree >= ell {
        return Err(HayesError::InvalidParameter(format!(
            "Berlekamp involution interval degree must satisfy 1<=d<ell, got d={interval_degree}, ell={ell}"
        )));
    }
    let domain = admit_binary_berlekamp_phase_domain(ell, degree, 0, interval_degree, limits)?;
    let enumeration = enumerate_binary_berlekamp_cosets(&domain, degree, ell, interval_degree)?;
    let minima = binary_berlekamp_involution_minima(&domain, &enumeration)?;

    let mut zero_signed_bucket_count = 0_usize;
    let mut exactly_sign_reversed_bucket_count = 0_usize;
    let mut exact_triangle_bucket_count = 0_usize;
    let mut finite_defect_candidate_holds = true;
    let mut worst = (0_usize, 0_usize, 0_usize, 0_u128, 0_u128, 1_u128);
    for (index, &(input_coset, inverse_coset)) in minima.bucket_keys.iter().enumerate() {
        let &(signed, population) = enumeration
            .buckets
            .get(&(input_coset, inverse_coset))
            .ok_or_else(|| HayesError::Invariant("Berlekamp bucket disappeared".to_owned()))?;
        let signed_magnitude = signed.unsigned_abs();
        let defect = minima.minimum_defects[index];
        if signed_magnitude > defect {
            return Err(HayesError::Invariant(
                "Berlekamp involution triangle bound misses the signed bucket".to_owned(),
            ));
        }
        zero_signed_bucket_count += usize::from(signed_magnitude == 0);
        exactly_sign_reversed_bucket_count += usize::from(defect == 0);
        exact_triangle_bucket_count += usize::from(defect == signed_magnitude);
        let defect_square = BigUint::from(defect).pow(2);
        let candidate_bound = BigUint::from(2 * interval_degree) * population;
        finite_defect_candidate_holds &= defect_square <= candidate_bound;
        if &defect_square * worst.5 > BigUint::from(worst.4).pow(2) * population {
            worst = (
                input_coset,
                inverse_coset,
                minima.best_translations[index],
                signed_magnitude,
                defect,
                population,
            );
        }
    }
    Ok(BinaryBerlekampInvolutionDefectReport {
        ell,
        degree,
        interval_degree,
        occupied_bucket_count: minima.bucket_keys.len(),
        zero_signed_bucket_count,
        exactly_sign_reversed_bucket_count,
        exact_triangle_bucket_count,
        worst_input_coset: worst.0,
        worst_inverse_coset: worst.1,
        worst_bucket_translation: worst.2,
        worst_bucket_signed_magnitude: worst.3,
        worst_bucket_minimum_defect: worst.4,
        worst_bucket_population: worst.5,
        finite_defect_candidate_holds,
    })
}

/// Enumerate the combined Berlekamp-discriminant and inverse-additive phase.
///
/// The domain consists of every monic constant-one binary polynomial `f` of
/// degree `degree`.  For each shift coset obtained by fixing coefficients
/// above `x^shift_dimension`, the operation counts positive and negative
/// squarefree phase weights.  Summing the squared coset imbalances gives
///
/// ```text
/// sum_coset (sum_(f in coset) w_a(f))^2
///   = sum_(h in H) sum_f w_a(f) w_a(f+h),
/// ```
///
/// the exact stationary-fibre energy for the low-coefficient shift subspace
/// `H`.  Cauchy then bounds the square of the complete phase sum by the
/// number of cosets times that energy.  This is a bounded diagnostic for a
/// possible van-der-Corput/Berlekamp lemma, not theorem credit.
///
/// # Errors
///
/// Rejects parameters outside the explicit Hayes limits or the packed `u64`
/// representation, charges the full factorization enumeration against
/// `max_table_cells`, and reports factorization/arithmetic invariant failures.
pub fn binary_berlekamp_inverse_phase_report(
    ell: usize,
    degree: usize,
    frequency: usize,
    shift_dimension: usize,
    limits: HayesLimits,
) -> Result<BinaryBerlekampInversePhaseReport, HayesError> {
    let domain =
        admit_binary_berlekamp_phase_domain(ell, degree, frequency, shift_dimension, limits)?;
    let coset_count = domain.input_count / domain.coset_size;
    let mut positive_by_coset = vec![0_u128; coset_count];
    let mut negative_by_coset = vec![0_u128; coset_count];
    for middle in 0..domain.input_count {
        let middle_u64 = u64::try_from(middle).map_err(|_| {
            HayesError::InvalidParameter("Berlekamp polynomial index exceeds u64".to_owned())
        })?;
        let polynomial = (1_u64 << degree) | (middle_u64 << 1) | 1;
        let mobius = binary_polynomial_mobius_from_bits(polynomial, degree)?;
        if mobius == 0 {
            continue;
        }
        let residue = polynomial & domain.residue_mask;
        let packed_inverse = principal_unit_inverse(residue, ell) >> 1;
        let character = if (packed_inverse & domain.frequency)
            .count_ones()
            .is_multiple_of(2)
        {
            1_i8
        } else {
            -1_i8
        };
        let coset = middle / domain.coset_size;
        if mobius * character > 0 {
            positive_by_coset[coset] += 1;
        } else {
            negative_by_coset[coset] += 1;
        }
    }
    let summary = summarize_binary_berlekamp_phase_cosets(positive_by_coset, negative_by_coset)?;
    let phase_sum = i128::try_from(summary.positive)
        .ok()
        .and_then(|value| {
            i128::try_from(summary.negative)
                .ok()
                .and_then(|negative| value.checked_sub(negative))
        })
        .ok_or_else(|| {
            HayesError::InvalidParameter("Berlekamp phase sum exceeds i128".to_owned())
        })?;
    let squarefree_count = summary
        .positive
        .checked_add(summary.negative)
        .ok_or_else(|| {
            HayesError::InvalidParameter("Berlekamp squarefree count overflow".to_owned())
        })?;
    let cauchy_square_bound = u128::try_from(coset_count)
        .ok()
        .and_then(|count| count.checked_mul(summary.shift_subspace_energy))
        .ok_or_else(|| {
            HayesError::InvalidParameter("Berlekamp Cauchy bound overflow".to_owned())
        })?;
    let trivial_square_bound = squarefree_count
        .checked_mul(squarefree_count)
        .ok_or_else(|| {
            HayesError::InvalidParameter("Berlekamp trivial bound overflow".to_owned())
        })?;
    if phase_sum
        .unsigned_abs()
        .checked_mul(phase_sum.unsigned_abs())
        .is_none_or(|square| square > cauchy_square_bound)
    {
        return Err(HayesError::Invariant(
            "Berlekamp shift Cauchy bound does not dominate the phase sum".to_owned(),
        ));
    }
    Ok(BinaryBerlekampInversePhaseReport {
        ell,
        degree,
        frequency,
        shift_dimension,
        input_count: u128::try_from(domain.input_count).map_err(|_| {
            HayesError::InvalidParameter("Berlekamp input count exceeds u128".to_owned())
        })?,
        squarefree_count,
        phase_sum,
        stationary_same_sign_pairs: summary.stationary_same_sign_pairs,
        oscillating_opposite_sign_pairs: summary.oscillating_opposite_sign_pairs,
        shift_subspace_energy: summary.shift_subspace_energy,
        cauchy_square_bound,
        trivial_square_bound,
    })
}

/// Count monic constant-one squarefree binary polynomials of exact degree.
///
/// There are `2^(k-1)` monic squarefree binary polynomials of degree `k>=2`.
/// Those divisible by `x` are exactly `xg` with `g` monic, constant one, and
/// squarefree of degree `k-1`.  With the degree-one seed this gives
///
/// ```text
/// Q_k = 2^(k-1)-Q_(k-1) = (2^k-(-1)^k)/3.
/// ```
///
/// # Errors
///
/// Rejects degree zero or a degree outside the exact `u128` shift domain.
pub fn binary_constant_one_squarefree_count(degree: usize) -> Result<u128, HayesError> {
    if degree == 0 {
        return Err(HayesError::InvalidParameter(
            "squarefree degree must be positive".to_owned(),
        ));
    }
    let power = 1_u128
        .checked_shl(u32::try_from(degree).map_err(|_| {
            HayesError::InvalidParameter("squarefree degree shift exceeds u32".to_owned())
        })?)
        .ok_or_else(|| HayesError::InvalidParameter("squarefree degree exceeds u128".to_owned()))?;
    let numerator = if degree.is_multiple_of(2) {
        power - 1
    } else {
        power + 1
    };
    if !numerator.is_multiple_of(3) {
        return Err(HayesError::Invariant(
            "constant-one squarefree formula is not integral".to_owned(),
        ));
    }
    Ok(numerator / 3)
}

/// Average the combined Berlekamp/inverse stationary energy over one
/// annihilator without enumerating its frequencies separately.
///
/// Let `H=W_shift_dimension` act on the free low coefficients of `f`, and let
/// `A=W_interval_degree^perp`.  Orthogonality gives the exact identity
///
/// ```text
/// sum_(a in A) E_H(a;k)
///   = |A| sum_(C,D) (sum_(f in C, f^(-1) in D) mu(f))^2,
/// ```
///
/// where `C` ranges over input cosets modulo `H` and `D` over inverse cosets
/// modulo `W_interval_degree`.  Applying Cauchy first inside shift cosets and
/// then across `A` yields
///
/// ```text
/// (sum_(f: f^(-1) in V_interval_degree) mu(f))^2
///   <= 2^(degree-1-shift_dimension) signed_coset_energy.
/// ```
///
/// This retains the Möbius/Berlekamp signs inside every simultaneous coset;
/// `unsigned_collision_count` exposes the loss from dropping them.
///
/// # Errors
///
/// Returns the same bounded-enumeration failures as
/// [`binary_berlekamp_inverse_phase_report`], rejects an invalid annihilator
/// degree, and checks the resulting exact Cauchy inequality.
pub fn binary_berlekamp_annihilator_energy_report(
    ell: usize,
    degree: usize,
    interval_degree: usize,
    shift_dimension: usize,
    limits: HayesLimits,
) -> Result<BinaryBerlekampAnnihilatorEnergyReport, HayesError> {
    if interval_degree == 0 || interval_degree >= ell {
        return Err(HayesError::InvalidParameter(format!(
            "annihilator interval degree must satisfy 1<=d<ell, got d={interval_degree}, ell={ell}"
        )));
    }
    let domain = admit_binary_berlekamp_phase_domain(ell, degree, 0, shift_dimension, limits)?;
    let input_count = domain.input_count;
    let enumeration = enumerate_binary_berlekamp_cosets(&domain, degree, ell, interval_degree)?;
    let summary = summarize_binary_berlekamp_cosets(&enumeration.buckets)?;
    let shift_correlations = binary_berlekamp_shift_correlations(
        &enumeration.mobius_values,
        &enumeration.inverse_cosets,
        ell,
        degree,
        interval_degree,
        shift_dimension,
        limits,
    )?;
    check_binary_berlekamp_shift_totals(
        &shift_correlations,
        &summary.signed_energy,
        &summary.unsigned_collisions,
    )?;
    let diagonal_squarefree_count = binary_constant_one_squarefree_count(degree)?;
    let diagonal = shift_correlations
        .first()
        .ok_or_else(|| HayesError::Invariant("Berlekamp shift table has no diagonal".to_owned()))?;
    if diagonal.shift != 0
        || diagonal.supported_pairs != diagonal_squarefree_count
        || diagonal.signed_correlation
            != i128::try_from(diagonal_squarefree_count).map_err(|_| {
                HayesError::InvalidParameter("squarefree diagonal exceeds i128".to_owned())
            })?
    {
        return Err(HayesError::Invariant(
            "Berlekamp zero shift disagrees with the squarefree formula".to_owned(),
        ));
    }
    let off_diagonal_signed_correlation =
        shift_correlations
            .iter()
            .skip(1)
            .try_fold(0_i128, |sum, entry| {
                sum.checked_add(entry.signed_correlation).ok_or_else(|| {
                    HayesError::InvalidParameter("off-diagonal correlation overflow".to_owned())
                })
            })?;
    let annihilator_frequency_count = 1_u128 << (ell - interval_degree);
    let averaged_shift_energy = BigUint::from(annihilator_frequency_count) * &summary.signed_energy;
    let coset_count = BigUint::from(1_u8) << (degree - 1 - shift_dimension);
    let fibre_cauchy_square_bound = coset_count * &summary.signed_energy;
    let exact_magnitude = BigUint::from(enumeration.inverse_interval_phase_sum.unsigned_abs());
    if &exact_magnitude * &exact_magnitude > fibre_cauchy_square_bound {
        return Err(HayesError::Invariant(
            "annihilator-energy Cauchy bound misses the exact fibre".to_owned(),
        ));
    }
    Ok(BinaryBerlekampAnnihilatorEnergyReport {
        ell,
        degree,
        interval_degree,
        shift_dimension,
        input_count: u128::try_from(input_count).map_err(|_| {
            HayesError::InvalidParameter("Berlekamp input count exceeds u128".to_owned())
        })?,
        annihilator_frequency_count,
        occupied_coset_count: enumeration.buckets.len(),
        worst_input_coset: summary.worst_bucket.0,
        worst_inverse_coset: summary.worst_bucket.1,
        worst_bucket_signed_square: summary.worst_bucket.2,
        worst_bucket_population: summary.worst_bucket.3,
        inverse_interval_phase_sum: enumeration.inverse_interval_phase_sum,
        signed_coset_energy: summary.signed_energy,
        unsigned_collision_count: summary.unsigned_collisions,
        diagonal_squarefree_count,
        off_diagonal_signed_correlation,
        averaged_shift_energy,
        fibre_cauchy_square_bound,
        shift_correlations,
    })
}

fn binary_berlekamp_witt_parity_classes(
    domain: &BinaryBerlekampPhaseDomain,
    degree: usize,
    factors: &[PrincipalUnitFactor],
    unit_to_index: &BTreeMap<u64, usize>,
) -> Result<Vec<usize>, HayesError> {
    let mut parity_classes = vec![0_usize; domain.input_count];
    for (middle, parity_class) in parity_classes.iter_mut().enumerate() {
        let middle_u64 = u64::try_from(middle).map_err(|_| {
            HayesError::InvalidParameter("Berlekamp Witt index exceeds u64".to_owned())
        })?;
        let polynomial = (1_u64 << degree) | (middle_u64 << 1) | 1;
        let residue = polynomial & domain.residue_mask;
        let mut quotient = *unit_to_index.get(&residue).ok_or_else(|| {
            HayesError::Invariant("Berlekamp residue has no Witt coordinate".to_owned())
        })?;
        for (block, factor) in factors.iter().enumerate() {
            let coordinate = quotient % factor.order;
            quotient /= factor.order;
            *parity_class |= (coordinate & 1) << block;
        }
        if quotient != 0 {
            return Err(HayesError::Invariant(
                "Berlekamp Witt parity decoding is incomplete".to_owned(),
            ));
        }
    }
    Ok(parity_classes)
}

fn binary_order_two_character_projections(
    domain: &BinaryBerlekampPhaseDomain,
    enumeration: &BinaryBerlekampCosetEnumeration,
    parity_classes: &[usize],
    factors: &[PrincipalUnitFactor],
    character_count: usize,
) -> Result<(Vec<BinaryOrderTwoCharacterProjection>, BigUint), HayesError> {
    let mut projections = Vec::with_capacity(character_count);
    let mut total_energy = BigUint::from(0_u8);
    for character_mask in 0..character_count {
        let mut signed_buckets = BTreeMap::<(usize, usize), i128>::new();
        for (middle, &parity_class) in parity_classes.iter().enumerate() {
            let mobius = enumeration.mobius_values[middle];
            if mobius == 0 {
                continue;
            }
            let sign = if (parity_class & character_mask).count_ones() % 2 == 0 {
                1
            } else {
                -1
            };
            let key = (
                middle / domain.coset_size,
                enumeration.inverse_cosets[middle],
            );
            let entry = signed_buckets.entry(key).or_default();
            *entry = entry
                .checked_add(sign * i128::from(mobius))
                .ok_or_else(|| {
                    HayesError::InvalidParameter("order-two bucket sum overflow".to_owned())
                })?;
        }
        let (energy, worst_square, worst_population) =
            binary_order_two_bucket_summary(&signed_buckets, &enumeration.buckets)?;
        let exact_conductor = factors
            .iter()
            .enumerate()
            .filter(|(block, _)| character_mask >> block & 1 != 0)
            .map(|(_, factor)| factor.odd_degree)
            .max();
        total_energy += &energy;
        projections.push(BinaryOrderTwoCharacterProjection {
            character_mask,
            exact_conductor,
            signed_coset_energy: energy,
            worst_bucket_signed_square: worst_square,
            worst_bucket_population: worst_population,
        });
    }
    Ok((projections, total_energy))
}

fn binary_order_two_bucket_summary(
    signed_buckets: &BTreeMap<(usize, usize), i128>,
    populations: &BinaryBerlekampCosetBuckets,
) -> Result<(BigUint, BigUint, u128), HayesError> {
    let mut energy = BigUint::from(0_u8);
    let mut worst_square = BigUint::from(0_u8);
    let mut worst_population = 1_u128;
    for (key, signed) in signed_buckets {
        let magnitude = BigUint::from(signed.unsigned_abs());
        let square = &magnitude * &magnitude;
        energy += &square;
        let population = populations
            .get(key)
            .ok_or_else(|| HayesError::Invariant("order-two bucket disappeared".to_owned()))?
            .1;
        if &square * BigUint::from(worst_population) > &worst_square * BigUint::from(population) {
            worst_square = square;
            worst_population = population;
        }
    }
    Ok((energy, worst_square, worst_population))
}

fn binary_witt_parity_fibre_energy(
    domain: &BinaryBerlekampPhaseDomain,
    enumeration: &BinaryBerlekampCosetEnumeration,
    parity_classes: &[usize],
) -> Result<BigUint, HayesError> {
    let mut fibres = BTreeMap::<(usize, usize, usize), i128>::new();
    for (middle, &parity_class) in parity_classes.iter().enumerate() {
        let mobius = enumeration.mobius_values[middle];
        if mobius == 0 {
            continue;
        }
        let key = (
            middle / domain.coset_size,
            enumeration.inverse_cosets[middle],
            parity_class,
        );
        let entry = fibres.entry(key).or_default();
        *entry = entry.checked_add(i128::from(mobius)).ok_or_else(|| {
            HayesError::InvalidParameter("Witt parity fibre sum overflow".to_owned())
        })?;
    }
    Ok(fibres
        .into_values()
        .map(|signed| BigUint::from(signed.unsigned_abs()).pow(2))
        .sum())
}

fn binary_order_two_conductor_energies(
    projections: &[BinaryOrderTwoCharacterProjection],
) -> Vec<BinaryOrderTwoConductorEnergy> {
    let mut totals = BTreeMap::<Option<usize>, (usize, BigUint)>::new();
    for projection in projections {
        let entry = totals
            .entry(projection.exact_conductor)
            .or_insert_with(|| (0, BigUint::from(0_u8)));
        entry.0 += 1;
        entry.1 += &projection.signed_coset_energy;
    }
    totals
        .into_iter()
        .map(|(exact_conductor, (character_count, projected_energy))| {
            BinaryOrderTwoConductorEnergy {
                exact_conductor,
                character_count,
                projected_energy,
            }
        })
        .collect()
}

/// Project every simultaneous input/inverse coset onto all order-two
/// principal-unit characters, grouped by the odd 2-typical Witt blocks.
///
/// The character selected by `mask` evaluates on a unit with block
/// coordinates `e_m` as `(-1)^(sum_(m in mask) e_m)`.  Its exact conductor is
/// therefore the largest selected odd block index.  The final invariant is
/// Parseval on the parity quotient of the Witt coordinates:
///
/// ```text
/// sum_chi sum_(C,D) |sum_f mu(f) chi(f)|^2
///   = #characters * sum_(C,D,p) |sum_(f: parity(f)=p) mu(f)|^2.
/// ```
///
/// # Errors
///
/// Returns the bounded-enumeration errors of the annihilator report and a
/// typed resource decline before constructing the character table.
pub fn binary_berlekamp_order_two_projection_report(
    ell: usize,
    degree: usize,
    interval_degree: usize,
    shift_dimension: usize,
    limits: HayesLimits,
) -> Result<BinaryBerlekampOrderTwoProjectionReport, HayesError> {
    if interval_degree == 0 || interval_degree >= ell {
        return Err(HayesError::InvalidParameter(format!(
            "order-two projection interval must satisfy 1<=d<ell, got d={interval_degree}, ell={ell}"
        )));
    }
    let domain = admit_binary_berlekamp_phase_domain(ell, degree, 0, shift_dimension, limits)?;
    let enumeration = enumerate_binary_berlekamp_cosets(&domain, degree, ell, interval_degree)?;
    let baseline = summarize_binary_berlekamp_cosets(&enumeration.buckets)?;
    let (factors, unit_to_index) = principal_unit_index_table(ell, limits)?;
    let block_count = factors.len();
    let character_count = 1_usize
        .checked_shl(u32::try_from(block_count).map_err(|_| {
            HayesError::InvalidParameter("order-two character rank exceeds u32".to_owned())
        })?)
        .ok_or_else(|| {
            HayesError::InvalidParameter("order-two character count overflow".to_owned())
        })?;
    let character_work = domain
        .input_count
        .checked_mul(character_count)
        .ok_or_else(|| {
            HayesError::InvalidParameter("order-two projection work overflow".to_owned())
        })?;
    check_limit(
        "berlekamp_order_two_projection_cells",
        character_work,
        limits.max_table_cells,
    )?;

    let parity_classes =
        binary_berlekamp_witt_parity_classes(&domain, degree, &factors, &unit_to_index)?;
    let (projections, total_projected_energy) = binary_order_two_character_projections(
        &domain,
        &enumeration,
        &parity_classes,
        &factors,
        character_count,
    )?;
    if projections
        .first()
        .is_none_or(|row| row.signed_coset_energy != baseline.signed_energy)
    {
        return Err(HayesError::Invariant(
            "trivial order-two projection misses the signed coset energy".to_owned(),
        ));
    }

    let witt_parity_fibre_energy =
        binary_witt_parity_fibre_energy(&domain, &enumeration, &parity_classes)?;
    if total_projected_energy != BigUint::from(character_count) * &witt_parity_fibre_energy {
        return Err(HayesError::Invariant(
            "order-two Witt quotient Parseval identity failed".to_owned(),
        ));
    }
    let conductor_energies = binary_order_two_conductor_energies(&projections);
    Ok(BinaryBerlekampOrderTwoProjectionReport {
        ell,
        degree,
        interval_degree,
        shift_dimension,
        odd_block_degrees: factors.iter().map(|factor| factor.odd_degree).collect(),
        character_count,
        occupied_bucket_count: enumeration.buckets.len(),
        projections,
        conductor_energies,
        total_projected_energy,
        witt_parity_fibre_energy,
    })
}

#[derive(Default)]
struct BinaryDyadicParameterSums {
    shift_inverse: BTreeMap<(usize, u64), i128>,
    normalized: BTreeMap<(usize, u64), i128>,
    normalized_residues: BTreeMap<(usize, u64), [u128; 8]>,
    valuation: BTreeMap<usize, i128>,
}

struct BinaryDyadicFibrePhase {
    dimension: usize,
    maxima: (Option<usize>, Option<usize>, Option<usize>),
    support_degree: usize,
    is_generalized_bent: bool,
    signed_correlation: i128,
    residue_counts: [u128; 8],
}

fn mod_eight_phase_is_generalized_bent(truth_table: &[u8]) -> bool {
    for shift in 1..truth_table.len() {
        let mut differences = [0_usize; 8];
        for (input, phase) in truth_table.iter().copied().enumerate() {
            let shifted = truth_table[input ^ shift];
            let difference = usize::from((shifted + 8 - phase) % 8);
            differences[difference] += 1;
        }
        if (0..4).any(|residue| differences[residue] != differences[residue + 4]) {
            return false;
        }
    }
    true
}

fn binary_dyadic_fibre_phase(
    shift: usize,
    members: &[usize],
    residues: &[u8],
) -> Result<BinaryDyadicFibrePhase, HayesError> {
    let coordinates = affine_binary_coordinates(members)?;
    let dimension = coordinates.len().ilog2() as usize;
    let origin = members[0];
    let mut truth_table = vec![0_u8; members.len()];
    let mut signed_correlation = 0_i128;
    let mut residue_counts = [0_u128; 8];
    for member in members.iter().copied() {
        let coordinate = coordinates[&(member ^ origin)];
        let phase = (residues[member] * residues[member ^ shift]) % 8;
        truth_table[coordinate] = phase;
        signed_correlation += i128::from(kronecker_two_mod_eight(phase));
        residue_counts[usize::from(phase)] += 1;
    }
    let coefficients = mod_eight_anf_coefficients(&truth_table, dimension)?;
    let maxima = mod_eight_anf_maxima(&coefficients);
    let support_degree = [maxima.0, maxima.1, maxima.2]
        .into_iter()
        .flatten()
        .max()
        .unwrap_or(0);
    let is_generalized_bent = mod_eight_phase_is_generalized_bent(&truth_table);
    Ok(BinaryDyadicFibrePhase {
        dimension,
        maxima,
        support_degree,
        is_generalized_bent,
        signed_correlation,
        residue_counts,
    })
}

#[derive(Clone, Copy)]
struct BinaryDyadicFibreKey {
    shift: usize,
    input_coset: usize,
    inverse_difference: u64,
}

fn record_binary_dyadic_fibre_statistics(
    key: BinaryDyadicFibreKey,
    population: usize,
    phase: &BinaryDyadicFibrePhase,
    report: &mut BinaryDyadicAutocorrelationFibreReport,
) -> Result<(), HayesError> {
    let population = u128::try_from(population)
        .map_err(|_| HayesError::InvalidParameter("dyadic fibre size exceeds u128".to_owned()))?;
    report.fibre_count += 1;
    report.total_fibre_points = report
        .total_fibre_points
        .checked_add(population)
        .ok_or_else(|| HayesError::InvalidParameter("dyadic fibre total overflow".to_owned()))?;
    report.max_fibre_dimension = report.max_fibre_dimension.max(phase.dimension);
    report.at_most_quadratic_fibre_count += usize::from(phase.support_degree <= 2);
    if phase.support_degree <= 2 {
        report.at_most_quadratic_fibre_points = report
            .at_most_quadratic_fibre_points
            .checked_add(population)
            .ok_or_else(|| {
                HayesError::InvalidParameter("quadratic fibre point overflow".to_owned())
            })?;
        report.at_most_quadratic_correlation_square_sum +=
            BigUint::from(phase.signed_correlation.unsigned_abs()).pow(2);
    }
    if phase.is_generalized_bent {
        report.generalized_bent_fibre_count += 1;
        report.generalized_bent_fibre_points = report
            .generalized_bent_fibre_points
            .checked_add(population)
            .ok_or_else(|| {
                HayesError::InvalidParameter("generalized-bent fibre total overflow".to_owned())
            })?;
    }
    if phase.support_degree > 2 {
        report.nonquadratic_fibre_points = report
            .nonquadratic_fibre_points
            .checked_add(population)
            .ok_or_else(|| {
                HayesError::InvalidParameter("nonquadratic fibre total overflow".to_owned())
            })?;
        report.nonquadratic_signed_correlation = report
            .nonquadratic_signed_correlation
            .checked_add(phase.signed_correlation)
            .ok_or_else(|| {
                HayesError::InvalidParameter("nonquadratic signed overflow".to_owned())
            })?;
        report.nonquadratic_absolute_correlation = report
            .nonquadratic_absolute_correlation
            .checked_add(phase.signed_correlation.unsigned_abs())
            .ok_or_else(|| {
                HayesError::InvalidParameter("nonquadratic absolute overflow".to_owned())
            })?;
        report.nonquadratic_correlation_square_sum +=
            BigUint::from(phase.signed_correlation.unsigned_abs()).pow(2);
    }
    report.full_degree_fibre_count += usize::from(phase.support_degree == phase.dimension);
    report.fibrewise_absolute_correlation = report
        .fibrewise_absolute_correlation
        .checked_add(phase.signed_correlation.unsigned_abs())
        .ok_or_else(|| HayesError::InvalidParameter("fibrewise correlation overflow".to_owned()))?;
    let magnitude = phase.signed_correlation.unsigned_abs();
    report.fibre_correlation_square_sum += BigUint::from(magnitude).pow(2);
    if magnitude != 0 {
        report.nonzero_fibre_correlation_count += 1;
        report.power_of_two_magnitude_fibre_count += usize::from(magnitude.is_power_of_two());
    }
    if phase.support_degree > report.max_phase_support_degree || report.worst_fibre.is_none() {
        report.max_phase_support_degree = phase.support_degree;
        report.worst_fibre = Some(BinaryDyadicAutocorrelationFibreWitness {
            shift: key.shift,
            input_coset: key.input_coset,
            inverse_difference: key.inverse_difference,
            fibre_dimension: phase.dimension,
            max_odd_support_degree: phase.maxima.0,
            max_twice_odd_support_degree: phase.maxima.1,
            max_four_support_degree: phase.maxima.2,
            signed_correlation: phase.signed_correlation,
        });
    }
    Ok(())
}

fn record_binary_dyadic_parameter_sum(
    key: BinaryDyadicFibreKey,
    ell: usize,
    representative: usize,
    phase: &BinaryDyadicFibrePhase,
    sums: &mut BinaryDyadicParameterSums,
) -> Result<(), HayesError> {
    let pair_entry = sums
        .shift_inverse
        .entry((key.shift, key.inverse_difference))
        .or_default();
    *pair_entry = pair_entry
        .checked_add(phase.signed_correlation)
        .ok_or_else(|| {
            HayesError::InvalidParameter("shift/inverse correlation overflow".to_owned())
        })?;
    let shift = u64::try_from(key.shift)
        .map_err(|_| HayesError::InvalidParameter("dyadic shift exceeds u64".to_owned()))?;
    let shift_polynomial = shift << 1;
    let valuation = shift_polynomial.trailing_zeros() as usize;
    if key.inverse_difference == 0
        || key.inverse_difference.trailing_zeros() as usize != valuation
        || valuation > ell
    {
        return Err(HayesError::Invariant(
            "shift and inverse difference have different valuations".to_owned(),
        ));
    }
    let quotient_ell = ell - valuation;
    let parameter = unit_multiply(
        shift_polynomial >> valuation,
        principal_unit_inverse(key.inverse_difference >> valuation, quotient_ell),
        quotient_ell,
    );
    let representative = u64::try_from(representative).map_err(|_| {
        HayesError::InvalidParameter("dyadic fibre representative exceeds u64".to_owned())
    })?;
    let quotient_mask = (1_u64 << (quotient_ell + 1)) - 1;
    let left = (1 | (representative << 1)) & quotient_mask;
    let right = (1 | ((representative ^ shift) << 1)) & quotient_mask;
    if parameter != unit_multiply(left, right, quotient_ell) {
        return Err(HayesError::Invariant(
            "normalized dyadic parameter is not the Artin--Schreier product f(f+h)".to_owned(),
        ));
    }
    let parameter_entry = sums.normalized.entry((valuation, parameter)).or_default();
    *parameter_entry = parameter_entry
        .checked_add(phase.signed_correlation)
        .ok_or_else(|| {
            HayesError::InvalidParameter("normalized parameter correlation overflow".to_owned())
        })?;
    let residue_entry = sums
        .normalized_residues
        .entry((valuation, parameter))
        .or_default();
    for (target, source) in residue_entry.iter_mut().zip(phase.residue_counts) {
        *target = target.checked_add(source).ok_or_else(|| {
            HayesError::InvalidParameter("normalized phase population overflow".to_owned())
        })?;
    }
    let valuation_entry = sums.valuation.entry(valuation).or_default();
    *valuation_entry = valuation_entry
        .checked_add(phase.signed_correlation)
        .ok_or_else(|| HayesError::InvalidParameter("valuation correlation overflow".to_owned()))?;
    Ok(())
}

fn accumulate_binary_dyadic_shift_fibres(
    shift: usize,
    domain: &BinaryBerlekampPhaseDomain,
    residues: &[u8],
    inverses: &[u64],
    report: &mut BinaryDyadicAutocorrelationFibreReport,
    parameter_sums: &mut BinaryDyadicParameterSums,
) -> Result<i128, HayesError> {
    let mut fibres = BTreeMap::<(usize, u64), Vec<usize>>::new();
    for middle in 0..domain.input_count {
        let inverse_difference = inverses[middle] ^ inverses[middle ^ shift];
        if inverse_difference >> (report.interval_degree + 1) == 0 {
            fibres
                .entry((middle / domain.coset_size, inverse_difference))
                .or_default()
                .push(middle);
        }
    }
    let mut shift_correlation = 0_i128;
    for ((input_coset, inverse_difference), members) in fibres {
        let phase = binary_dyadic_fibre_phase(shift, &members, residues)?;
        let key = BinaryDyadicFibreKey {
            shift,
            input_coset,
            inverse_difference,
        };
        record_binary_dyadic_fibre_statistics(key, members.len(), &phase, report)?;
        record_binary_dyadic_parameter_sum(key, report.ell, members[0], &phase, parameter_sums)?;
        shift_correlation = shift_correlation
            .checked_add(phase.signed_correlation)
            .ok_or_else(|| {
                HayesError::InvalidParameter("dyadic shift correlation overflow".to_owned())
            })?;
    }
    Ok(shift_correlation)
}

fn signed_map_absolute_sum<K: Ord>(values: &BTreeMap<K, i128>) -> Result<u128, HayesError> {
    values.values().try_fold(0_u128, |sum, value| {
        sum.checked_add(value.unsigned_abs()).ok_or_else(|| {
            HayesError::InvalidParameter("dyadic parameter absolute sum overflow".to_owned())
        })
    })
}

fn finalize_binary_dyadic_parameter_sums(
    report: &mut BinaryDyadicAutocorrelationFibreReport,
    sums: &BinaryDyadicParameterSums,
) -> Result<(), HayesError> {
    report.shift_inverse_pair_count = sums.shift_inverse.len();
    report.shift_inverse_pairwise_absolute_correlation =
        signed_map_absolute_sum(&sums.shift_inverse)?;
    report.normalized_parameter_count = sums.normalized.len();
    report.normalized_parameterwise_absolute_correlation =
        signed_map_absolute_sum(&sums.normalized)?;
    report.valuationwise_absolute_correlation = signed_map_absolute_sum(&sums.valuation)?;
    report.valuation_correlations = sums
        .valuation
        .iter()
        .map(|(&valuation, &signed_correlation)| {
            let layer = sums
                .normalized
                .iter()
                .filter(|((candidate, _), _)| *candidate == valuation)
                .map(|(_, value)| *value)
                .collect::<Vec<_>>();
            let parameterwise_absolute_correlation =
                layer.iter().try_fold(0_u128, |sum, value| {
                    sum.checked_add(value.unsigned_abs()).ok_or_else(|| {
                        HayesError::InvalidParameter(
                            "valuation parameter absolute sum overflow".to_owned(),
                        )
                    })
                })?;
            Ok(BinaryDyadicValuationCorrelation {
                valuation,
                normalized_parameter_count: layer.len(),
                parameterwise_absolute_correlation,
                signed_correlation,
            })
        })
        .collect::<Result<Vec<_>, HayesError>>()?;
    Ok(())
}

fn empty_binary_connected_witt_spectrum(ell: usize) -> BinaryConnectedWittSpectrumReport {
    BinaryConnectedWittSpectrumReport {
        ell,
        normalized_parameter_count: 0,
        embedded_support_count: 0,
        signed_total: 0,
        embedded_absolute_sum: 0,
        spatial_second_moment: BigUint::from(0_u8),
        spectral_second_moment: BigUint::from(0_u8),
        spectral_fourth_moment: BigUint::from(0_u8),
        phase_residue_totals: [0; 8],
        additive_phase_spectra: Vec::new(),
        phase_complementarity_identity: BigUint::from(0_u8),
        phase_complementarity_max_off_identity: BigUint::from(0_u8),
        phase_complementarity_square_sum: BigUint::from(0_u8),
        conductor_spectra: Vec::new(),
    }
}

fn verschiebung_embed_mixed_radix_index(
    mut source_index: usize,
    source_factors: &[PrincipalUnitFactor],
    target_factors: &[PrincipalUnitFactor],
) -> Result<usize, HayesError> {
    let mut source_factor_index = 0_usize;
    let mut target_index = 0_usize;
    let mut target_stride = 1_usize;
    for target in target_factors {
        let embedded_coordinate = if let Some(source) = source_factors.get(source_factor_index)
            && source.odd_degree == target.odd_degree
        {
            if !target.order.is_multiple_of(source.order) {
                return Err(HayesError::Invariant(
                    "target Witt block order is not a multiple of the source order".to_owned(),
                ));
            }
            let coordinate = source_index % source.order;
            source_index /= source.order;
            source_factor_index += 1;
            coordinate * (target.order / source.order)
        } else {
            0
        };
        target_index = target_index
            .checked_add(embedded_coordinate * target_stride)
            .ok_or_else(|| {
                HayesError::InvalidParameter("Witt embedding index overflow".to_owned())
            })?;
        target_stride = target_stride.checked_mul(target.order).ok_or_else(|| {
            HayesError::InvalidParameter("Witt embedding stride overflow".to_owned())
        })?;
    }
    if source_index != 0 || source_factor_index != source_factors.len() {
        return Err(HayesError::Invariant(
            "Witt Verschiebung embedding did not consume the source coordinates".to_owned(),
        ));
    }
    Ok(target_index)
}

fn add_mixed_radix_indices(
    mut left: usize,
    mut right: usize,
    factors: &[PrincipalUnitFactor],
) -> Result<usize, HayesError> {
    let mut result = 0_usize;
    let mut stride = 1_usize;
    for factor in factors {
        let coordinate = ((left % factor.order) + (right % factor.order)) % factor.order;
        left /= factor.order;
        right /= factor.order;
        result = result
            .checked_add(coordinate * stride)
            .ok_or_else(|| HayesError::InvalidParameter("Witt sum index overflow".to_owned()))?;
        stride = stride
            .checked_mul(factor.order)
            .ok_or_else(|| HayesError::InvalidParameter("Witt sum stride overflow".to_owned()))?;
    }
    if left != 0 || right != 0 {
        return Err(HayesError::Invariant(
            "Witt mixed-radix addition left unused coordinates".to_owned(),
        ));
    }
    Ok(result)
}

fn mixed_radix_character_conductor(
    mut character: usize,
    factors: &[PrincipalUnitFactor],
) -> Result<Option<usize>, HayesError> {
    let mut conductor = None;
    for factor in factors {
        let coordinate = character % factor.order;
        character /= factor.order;
        if coordinate != 0 {
            let length = factor.order.trailing_zeros() as usize;
            let valuation = coordinate.trailing_zeros() as usize;
            let slot = length.checked_sub(valuation + 1).ok_or_else(|| {
                HayesError::Invariant("Witt character valuation exceeds block length".to_owned())
            })?;
            let degree = factor
                .odd_degree
                .checked_shl(u32::try_from(slot).map_err(|_| {
                    HayesError::InvalidParameter("Witt conductor slot exceeds u32".to_owned())
                })?)
                .ok_or_else(|| {
                    HayesError::InvalidParameter("Witt conductor overflow".to_owned())
                })?;
            conductor = Some(conductor.map_or(degree, |current: usize| current.max(degree)));
        }
    }
    if character != 0 {
        return Err(HayesError::Invariant(
            "Witt conductor left unused character coordinates".to_owned(),
        ));
    }
    Ok(conductor)
}

fn connected_witt_conductor_spectra(
    target: &PrincipalUnitStructure,
    prime_one: &[u64],
    prime_two: &[u64],
) -> Result<Vec<BinaryConnectedWittConductorSpectrum>, HayesError> {
    let mut rows = BTreeMap::<Option<usize>, [usize; 5]>::new();
    for character in 0..target.group_order {
        let conductor = mixed_radix_character_conductor(character, &target.factors)?;
        let first_nonzero = prime_one[character] != 0;
        let second_nonzero = prime_two[character] != 0;
        let row = rows.entry(conductor).or_default();
        row[0] += 1;
        row[1] += usize::from(first_nonzero);
        row[2] += usize::from(second_nonzero);
        row[3] += usize::from(first_nonzero && second_nonzero);
        row[4] += usize::from(first_nonzero != second_nonzero);
    }
    Ok(rows
        .into_iter()
        .map(
            |(exact_conductor, counts)| BinaryConnectedWittConductorSpectrum {
                exact_conductor,
                character_count: counts[0],
                prime_one_nonzero_count: counts[1],
                prime_two_nonzero_count: counts[2],
                jointly_nonzero_count: counts[3],
                zero_status_disagreement_count: counts[4],
            },
        )
        .collect())
}

fn connected_witt_phase_transform(
    phase_spatial: &[[u128; 8]],
    target: &PrincipalUnitStructure,
    multiplier: u8,
    modulus: u64,
) -> Result<Vec<u64>, HayesError> {
    let root = mod_pow(PRIMITIVE_ROOT, (modulus - 1) / 8, modulus);
    let mut values = Vec::with_capacity(phase_spatial.len());
    for residues in phase_spatial {
        let mut value = 0_u64;
        for (residue, count) in residues.iter().copied().enumerate() {
            let exponent = (usize::from(multiplier) * residue) % 8;
            let count = u64::try_from(count % u128::from(modulus)).map_err(|_| {
                HayesError::Invariant("phase population residue exceeds u64".to_owned())
            })?;
            value = add_mod(
                value,
                multiply_mod(count, mod_pow(root, exponent as u64, modulus), modulus),
                modulus,
            );
        }
        values.push(value);
    }
    let dimensions = target
        .factors
        .iter()
        .map(|factor| factor.order)
        .collect::<Vec<_>>();
    group_transform(&mut values, &dimensions, modulus);
    Ok(values)
}

fn check_connected_witt_gauss_identity(
    signed: &[u64],
    phases: &[Vec<u64>],
    modulus: u64,
) -> Result<(), HayesError> {
    let root = mod_pow(PRIMITIVE_ROOT, (modulus - 1) / 8, modulus);
    let factor = multiply_mod(
        2,
        subtract_mod(root, mod_pow(root, 3, modulus), modulus),
        modulus,
    );
    for character in 0..signed.len() {
        let left = subtract_mod(
            add_mod(phases[0][character], phases[3][character], modulus),
            add_mod(phases[1][character], phases[2][character], modulus),
            modulus,
        );
        let right = multiply_mod(factor, signed[character], modulus);
        if left != right {
            return Err(HayesError::Invariant(
                "connected Witt phase spectra violate the dyadic Gauss identity".to_owned(),
            ));
        }
    }
    Ok(())
}

fn connected_witt_additive_phase_spectra(
    phase_spatial: &[[u128; 8]],
    target: &PrincipalUnitStructure,
    signed_prime_one: &[u64],
    signed_prime_two: &[u64],
) -> Result<Vec<BinaryConnectedWittAdditivePhaseSpectrum>, HayesError> {
    let multipliers = [1_u8, 3, 5, 7];
    let mut prime_one = Vec::with_capacity(4);
    let mut prime_two = Vec::with_capacity(4);
    for multiplier in multipliers {
        prime_one.push(connected_witt_phase_transform(
            phase_spatial,
            target,
            multiplier,
            PRIME_ONE,
        )?);
        prime_two.push(connected_witt_phase_transform(
            phase_spatial,
            target,
            multiplier,
            PRIME_TWO,
        )?);
    }
    check_connected_witt_gauss_identity(signed_prime_one, &prime_one, PRIME_ONE)?;
    check_connected_witt_gauss_identity(signed_prime_two, &prime_two, PRIME_TWO)?;
    multipliers
        .into_iter()
        .enumerate()
        .map(|(index, multiplier)| {
            let conductor_spectra =
                connected_witt_conductor_spectra(target, &prime_one[index], &prime_two[index])?;
            Ok(BinaryConnectedWittAdditivePhaseSpectrum {
                multiplier,
                prime_one_nonzero_count: prime_one[index]
                    .iter()
                    .filter(|value| **value != 0)
                    .count(),
                prime_two_nonzero_count: prime_two[index]
                    .iter()
                    .filter(|value| **value != 0)
                    .count(),
                zero_status_disagreement_count: prime_one[index]
                    .iter()
                    .zip(&prime_two[index])
                    .filter(|(first, second)| (**first == 0) != (**second == 0))
                    .count(),
                conductor_spectra,
            })
        })
        .collect()
}

fn connected_witt_phase_complementarity(
    phase_spatial: &[[u128; 8]],
    target: &PrincipalUnitStructure,
) -> Result<(BigUint, BigUint, BigUint), HayesError> {
    let signed_channels = phase_spatial
        .iter()
        .map(|residues| {
            std::array::from_fn::<BigInt, 4, _>(|residue| {
                BigInt::from(residues[residue]) - BigInt::from(residues[residue + 4])
            })
        })
        .collect::<Vec<_>>();
    let mut identity = BigUint::from(0_u8);
    let mut max_off_identity = BigUint::from(0_u8);
    let mut square_sum = BigUint::from(0_u8);
    for shift in 0..target.group_order {
        let mut correlation = BigInt::from(0_i8);
        for (index, channels) in signed_channels.iter().enumerate() {
            let shifted = add_mixed_radix_indices(index, shift, &target.factors)?;
            correlation += channels
                .iter()
                .zip(&signed_channels[shifted])
                .map(|(left, right)| left * right)
                .sum::<BigInt>();
        }
        let magnitude = correlation.magnitude();
        if shift == 0 {
            identity.clone_from(magnitude);
        } else if magnitude > &max_off_identity {
            max_off_identity.clone_from(magnitude);
        }
        square_sum += magnitude.pow(2);
    }
    Ok((identity, max_off_identity, square_sum))
}

#[allow(clippy::too_many_lines)]
fn binary_connected_witt_spectrum(
    ell: usize,
    sums: &BinaryDyadicParameterSums,
    limits: HayesLimits,
) -> Result<BinaryConnectedWittSpectrumReport, HayesError> {
    let target = principal_unit_structure(ell, limits)?;
    let moment_work = target
        .group_order
        .checked_mul(target.group_order)
        .ok_or_else(|| {
            HayesError::InvalidParameter("connected Witt moment work overflow".to_owned())
        })?;
    check_limit(
        "connected_witt_moment_cells",
        moment_work,
        limits.max_table_cells,
    )?;

    let mut source_levels = BTreeSet::new();
    for &(valuation, _) in sums.normalized.keys() {
        source_levels.insert(ell - valuation);
    }
    let mut source_tables = BTreeMap::new();
    for source_ell in source_levels {
        if source_ell != 0 {
            source_tables.insert(source_ell, principal_unit_index_table(source_ell, limits)?);
        }
    }

    let mut spatial = vec![0_i128; target.group_order];
    let mut phase_spatial = vec![[0_u128; 8]; target.group_order];
    for (&(valuation, parameter), &signed_correlation) in &sums.normalized {
        let source_ell = ell - valuation;
        let embedded_index = if source_ell == 0 {
            if parameter != 1 {
                return Err(HayesError::Invariant(
                    "level-zero normalized Witt parameter is not the identity".to_owned(),
                ));
            }
            0
        } else {
            let (source_factors, source_indices) = &source_tables[&source_ell];
            let source_index = *source_indices.get(&parameter).ok_or_else(|| {
                HayesError::Invariant("normalized parameter has no source Witt index".to_owned())
            })?;
            verschiebung_embed_mixed_radix_index(source_index, source_factors, &target.factors)?
        };
        spatial[embedded_index] = spatial[embedded_index]
            .checked_add(signed_correlation)
            .ok_or_else(|| {
                HayesError::InvalidParameter("connected Witt class overflow".to_owned())
            })?;
        let residues = sums
            .normalized_residues
            .get(&(valuation, parameter))
            .ok_or_else(|| {
                HayesError::Invariant("normalized parameter has no phase populations".to_owned())
            })?;
        for (target_count, source_count) in phase_spatial[embedded_index].iter_mut().zip(residues) {
            *target_count = target_count.checked_add(*source_count).ok_or_else(|| {
                HayesError::InvalidParameter("connected Witt phase population overflow".to_owned())
            })?;
        }
    }
    let dyadic_values = [0_i8, 1, 0, -1, 0, -1, 0, 1];
    for (signed, residues) in spatial.iter().zip(&phase_spatial) {
        let reconstructed = residues
            .iter()
            .enumerate()
            .map(|(residue, count)| BigInt::from(*count) * BigInt::from(dyadic_values[residue]))
            .sum::<BigInt>();
        if reconstructed != BigInt::from(*signed) {
            return Err(HayesError::Invariant(
                "connected Witt residue populations miss the signed class".to_owned(),
            ));
        }
    }
    let signed_total = spatial.iter().try_fold(0_i128, |sum, value| {
        sum.checked_add(*value)
            .ok_or_else(|| HayesError::InvalidParameter("connected Witt total overflow".to_owned()))
    })?;
    let expected_total = sums.valuation.values().try_fold(0_i128, |sum, value| {
        sum.checked_add(*value)
            .ok_or_else(|| HayesError::InvalidParameter("valuation total overflow".to_owned()))
    })?;
    if signed_total != expected_total {
        return Err(HayesError::Invariant(
            "connected Witt embedding changed the signed off-diagonal total".to_owned(),
        ));
    }
    let embedded_absolute_sum = spatial.iter().try_fold(0_u128, |sum, value| {
        sum.checked_add(value.unsigned_abs()).ok_or_else(|| {
            HayesError::InvalidParameter("connected Witt absolute sum overflow".to_owned())
        })
    })?;
    let spatial_second_moment = spatial
        .iter()
        .map(|value| BigUint::from(value.unsigned_abs()).pow(2))
        .sum::<BigUint>();
    let spectral_second_moment = BigUint::from(target.group_order) * &spatial_second_moment;

    let mut autocorrelation_square_sum = BigUint::from(0_u8);
    for shift in 0..target.group_order {
        let mut correlation = BigInt::from(0_i8);
        for (index, value) in spatial.iter().enumerate() {
            let shifted = add_mixed_radix_indices(index, shift, &target.factors)?;
            correlation += BigInt::from(*value) * BigInt::from(spatial[shifted]);
        }
        autocorrelation_square_sum += correlation.magnitude().pow(2);
    }
    let spectral_fourth_moment = BigUint::from(target.group_order) * autocorrelation_square_sum;

    let modular_spectrum = |modulus: u64| {
        let modulus_i128 = i128::from(modulus);
        let mut values = spatial
            .iter()
            .map(|value| {
                u64::try_from(value.rem_euclid(modulus_i128)).map_err(|_| {
                    HayesError::Invariant("signed modular residue exceeds u64".to_owned())
                })
            })
            .collect::<Result<Vec<_>, HayesError>>()?;
        let dimensions = target
            .factors
            .iter()
            .map(|factor| factor.order)
            .collect::<Vec<_>>();
        group_transform(&mut values, &dimensions, modulus);
        Ok::<Vec<u64>, HayesError>(values)
    };
    let prime_one = modular_spectrum(PRIME_ONE)?;
    let prime_two = modular_spectrum(PRIME_TWO)?;
    let conductor_spectra = connected_witt_conductor_spectra(&target, &prime_one, &prime_two)?;
    let additive_phase_spectra =
        connected_witt_additive_phase_spectra(&phase_spatial, &target, &prime_one, &prime_two)?;
    let (
        phase_complementarity_identity,
        phase_complementarity_max_off_identity,
        phase_complementarity_square_sum,
    ) = connected_witt_phase_complementarity(&phase_spatial, &target)?;
    let mut phase_residue_totals = [0_u128; 8];
    for residues in &phase_spatial {
        for (total, count) in phase_residue_totals.iter_mut().zip(residues) {
            *total = total.checked_add(*count).ok_or_else(|| {
                HayesError::InvalidParameter("connected phase total overflow".to_owned())
            })?;
        }
    }

    Ok(BinaryConnectedWittSpectrumReport {
        ell,
        normalized_parameter_count: sums.normalized.len(),
        embedded_support_count: spatial.iter().filter(|value| **value != 0).count(),
        signed_total,
        embedded_absolute_sum,
        spatial_second_moment,
        spectral_second_moment,
        spectral_fourth_moment,
        phase_residue_totals,
        additive_phase_spectra,
        phase_complementarity_identity,
        phase_complementarity_max_off_identity,
        phase_complementarity_square_sum,
        conductor_spectra,
    })
}

/// Restrict the dyadic product-discriminant phase to every exact affine
/// inverse-difference fibre in the nonzero-shift autocorrelation.
///
/// Since the degree signs cancel,
///
/// ```text
/// mu(f) mu(f+h) = chi_8(Disc(F) Disc(F+h)).
/// ```
///
/// The operation groups by input coset, shift, and exact inverse difference,
/// recovers binary affine coordinates, computes the unique `Z/8` ANF of the
/// product discriminant, and checks that its dyadic character reconstructs
/// every signed shift correlation.
///
/// # Errors
///
/// Returns the bounded Berlekamp-domain errors, a caller resource decline, or
/// an invariant failure if a claimed fibre is not affine or a phase sum does
/// not reconstruct the existing correlation ledger.
pub fn binary_dyadic_autocorrelation_fibre_report(
    ell: usize,
    degree: usize,
    interval_degree: usize,
    limits: HayesLimits,
) -> Result<BinaryDyadicAutocorrelationFibreReport, HayesError> {
    if interval_degree == 0 || interval_degree >= ell {
        return Err(HayesError::InvalidParameter(format!(
            "dyadic fibre interval must satisfy 1<=d<ell, got d={interval_degree}, ell={ell}"
        )));
    }
    let domain = admit_binary_berlekamp_phase_domain(ell, degree, 0, interval_degree, limits)?;
    let shift_count = 1_usize << interval_degree;
    let work = domain
        .input_count
        .checked_mul(shift_count)
        .ok_or_else(|| HayesError::InvalidParameter("dyadic fibre work overflow".to_owned()))?;
    check_limit("dyadic_fibre_cells", work, limits.max_table_cells)?;
    let mut residues = Vec::with_capacity(domain.input_count);
    let mut inverses = Vec::with_capacity(domain.input_count);
    for middle in 0..domain.input_count {
        let middle_u64 = u64::try_from(middle).map_err(|_| {
            HayesError::InvalidParameter("dyadic fibre index exceeds u64".to_owned())
        })?;
        let polynomial = (1_u64 << degree) | (middle_u64 << 1) | 1;
        residues.push(binary_integral_discriminant_residue_mod_eight(
            polynomial, degree,
        )?);
        inverses.push(principal_unit_inverse(
            polynomial & domain.residue_mask,
            ell,
        ));
    }
    let expected = binary_berlekamp_annihilator_energy_report(
        ell,
        degree,
        interval_degree,
        interval_degree,
        limits,
    )?;
    let mut report = BinaryDyadicAutocorrelationFibreReport {
        ell,
        degree,
        interval_degree,
        nonzero_shift_count: shift_count - 1,
        fibre_count: 0,
        total_fibre_points: 0,
        max_fibre_dimension: 0,
        at_most_quadratic_fibre_count: 0,
        at_most_quadratic_fibre_points: 0,
        at_most_quadratic_correlation_square_sum: BigUint::from(0_u8),
        generalized_bent_fibre_count: 0,
        generalized_bent_fibre_points: 0,
        nonquadratic_fibre_points: 0,
        nonquadratic_signed_correlation: 0,
        nonquadratic_absolute_correlation: 0,
        nonquadratic_correlation_square_sum: BigUint::from(0_u8),
        fibrewise_absolute_correlation: 0,
        fibre_correlation_square_sum: BigUint::from(0_u8),
        nonzero_fibre_correlation_count: 0,
        power_of_two_magnitude_fibre_count: 0,
        shift_inverse_pair_count: 0,
        shift_inverse_pairwise_absolute_correlation: 0,
        normalized_parameter_count: 0,
        normalized_parameterwise_absolute_correlation: 0,
        valuationwise_absolute_correlation: 0,
        valuation_correlations: Vec::new(),
        connected_witt_spectrum: empty_binary_connected_witt_spectrum(ell),
        full_degree_fibre_count: 0,
        max_phase_support_degree: 0,
        off_diagonal_signed_correlation: 0,
        worst_fibre: None,
    };
    let mut parameter_sums = BinaryDyadicParameterSums::default();
    for shift in 1..shift_count {
        let shift_correlation = accumulate_binary_dyadic_shift_fibres(
            shift,
            &domain,
            &residues,
            &inverses,
            &mut report,
            &mut parameter_sums,
        )?;
        if shift_correlation != expected.shift_correlations[shift].signed_correlation {
            return Err(HayesError::Invariant(
                "dyadic affine fibres miss the signed shift correlation".to_owned(),
            ));
        }
        report.off_diagonal_signed_correlation = report
            .off_diagonal_signed_correlation
            .checked_add(shift_correlation)
            .ok_or_else(|| {
                HayesError::InvalidParameter("dyadic off-diagonal overflow".to_owned())
            })?;
    }
    if report.off_diagonal_signed_correlation != expected.off_diagonal_signed_correlation {
        return Err(HayesError::Invariant(
            "dyadic fibres miss the total off-diagonal correlation".to_owned(),
        ));
    }
    finalize_binary_dyadic_parameter_sums(&mut report, &parameter_sums)?;
    report.connected_witt_spectrum = binary_connected_witt_spectrum(ell, &parameter_sums, limits)?;
    Ok(report)
}

/// Propagate candidate simultaneous-coset energy exponents into one exact
/// endpoint Möbius-convolution term.
///
/// If `E_(s,d)(k)<=2^e`, the annihilator-average identity and Cauchy give
///
/// ```text
/// |sum_(f^(-1) in V_d) mu(f)|
///   <= 2^((k-1-s+e)/2).
/// ```
///
/// The endpoint term uses `H_k=B_k-B_(k-1)`.  The ledger therefore takes the
/// larger of the two phase exponents, charges one bit for their sum, and
/// charges `ceil(log2(d))` bits for the convolution weight.  It remains
/// conditional on the supplied energy exponents.
///
/// # Errors
///
/// Rejects parameters outside the endpoint convolution domain and checked
/// arithmetic overflows.
pub fn binary_berlekamp_aggregate_exponent_ledger(
    ell: usize,
    endpoint_degree: usize,
    interval_degree: usize,
    shift_dimension: usize,
    energy_exponent_sixteenths: u128,
    previous_energy_exponent_sixteenths: u128,
) -> Result<BinaryBerlekampAggregateExponentLedger, HayesError> {
    if ell == 0 || interval_degree == 0 || interval_degree >= ell {
        return Err(HayesError::InvalidParameter(
            "Berlekamp aggregate ledger requires ell>0 and 1<=d<ell".to_owned(),
        ));
    }
    let mobius_degree = endpoint_degree
        .checked_sub(interval_degree)
        .filter(|&degree| degree >= 2)
        .ok_or_else(|| {
            HayesError::InvalidParameter(
                "endpoint degree must leave Mobius degree at least two".to_owned(),
            )
        })?;
    if shift_dimension > mobius_degree - 2 {
        return Err(HayesError::InvalidParameter(format!(
            "shift dimension {shift_dimension} leaves no free coefficients at degree {}",
            mobius_degree - 1
        )));
    }
    let phase_bound_thirty_seconds = u128::try_from(mobius_degree - 1 - shift_dimension)
        .ok()
        .and_then(|value| value.checked_mul(16))
        .and_then(|value| value.checked_add(energy_exponent_sixteenths))
        .ok_or_else(|| {
            HayesError::InvalidParameter("Berlekamp phase exponent overflow".to_owned())
        })?;
    let previous_phase_bound_thirty_seconds = u128::try_from(mobius_degree - 2 - shift_dimension)
        .ok()
        .and_then(|value| value.checked_mul(16))
        .and_then(|value| value.checked_add(previous_energy_exponent_sixteenths))
        .ok_or_else(|| {
            HayesError::InvalidParameter("previous Berlekamp phase exponent overflow".to_owned())
        })?;
    let convolution_weight_bits = if interval_degree == 1 {
        0
    } else {
        usize::BITS as usize - (interval_degree - 1).leading_zeros() as usize
    };
    let weighted_term_bound_thirty_seconds = phase_bound_thirty_seconds
        .max(previous_phase_bound_thirty_seconds)
        .checked_add(32)
        .and_then(|value| {
            u128::try_from(convolution_weight_bits)
                .ok()
                .and_then(|bits| bits.checked_mul(32))
                .and_then(|weight| value.checked_add(weight))
        })
        .ok_or_else(|| {
            HayesError::InvalidParameter("weighted Berlekamp exponent overflow".to_owned())
        })?;
    let target_thirty_seconds = u128::try_from(ell)
        .ok()
        .and_then(|value| value.checked_mul(32))
        .ok_or_else(|| HayesError::InvalidParameter("Berlekamp target overflow".to_owned()))?;
    Ok(BinaryBerlekampAggregateExponentLedger {
        ell,
        endpoint_degree,
        interval_degree,
        shift_dimension,
        mobius_degree,
        energy_exponent_sixteenths,
        previous_energy_exponent_sixteenths,
        phase_bound_thirty_seconds,
        previous_phase_bound_thirty_seconds,
        weighted_term_bound_thirty_seconds,
        target_thirty_seconds,
        deficit_thirty_seconds: checked_exponent_deficit(
            target_thirty_seconds,
            weighted_term_bound_thirty_seconds,
            "Berlekamp aggregate",
        )?,
    })
}

fn inverse_mobius_fourier_weight(interval_degree: usize) -> Result<i128, HayesError> {
    i128::try_from(interval_degree)
        .ok()
        .and_then(|degree| {
            degree.checked_mul(1_i128.checked_shl(u32::try_from(interval_degree).ok()?)?)
        })
        .ok_or_else(|| HayesError::InvalidParameter("Fourier regroup weight overflow".to_owned()))
}

struct InverseMobiusFourierNumerators {
    convolution: IdentityClassMobiusConvolution,
    denominator: u128,
    frequency_numerators: Vec<i128>,
    cellwise_absolute_numerator: u128,
    orderwise_absolute_numerator: u128,
}

fn accumulate_inverse_mobius_fourier_order(
    spectrum: &InverseAdditiveMobiusSpectrum,
    interval_degree: usize,
    frequency_numerators: &mut [i128],
) -> Result<(i128, u128), HayesError> {
    let stride = 1_usize
        .checked_shl(u32::try_from(interval_degree).map_err(|_| {
            HayesError::InvalidParameter("Fourier regroup stride exceeds u32".to_owned())
        })?)
        .ok_or_else(|| {
            HayesError::InvalidParameter("Fourier regroup stride overflow".to_owned())
        })?;
    let weight = inverse_mobius_fourier_weight(interval_degree)?;
    let mut order_numerator = 0_i128;
    let mut cellwise_absolute = 0_u128;
    for index in (0..spectrum.values.len()).step_by(stride) {
        let contribution = spectrum.values[index].checked_mul(weight).ok_or_else(|| {
            HayesError::InvalidParameter("Fourier cell contribution overflow".to_owned())
        })?;
        frequency_numerators[index] = frequency_numerators[index]
            .checked_add(contribution)
            .ok_or_else(|| {
                HayesError::InvalidParameter("Fourier frequency numerator overflow".to_owned())
            })?;
        order_numerator = order_numerator.checked_add(contribution).ok_or_else(|| {
            HayesError::InvalidParameter("Fourier order numerator overflow".to_owned())
        })?;
        cellwise_absolute = cellwise_absolute
            .checked_add(contribution.unsigned_abs())
            .ok_or_else(|| {
                HayesError::InvalidParameter("Fourier cellwise absolute sum overflow".to_owned())
            })?;
    }
    Ok((order_numerator, cellwise_absolute))
}

fn inverse_mobius_fourier_layers(
    ell: usize,
    frequency_numerators: &[i128],
) -> Result<Vec<InverseMobiusFourierLayer>, HayesError> {
    let mut layers = (0..=ell)
        .map(|annihilator_depth| InverseMobiusFourierLayer {
            annihilator_depth,
            frequency_count: 0,
            weighted_numerator: 0,
        })
        .collect::<Vec<_>>();
    for (frequency, numerator) in frequency_numerators.iter().copied().enumerate() {
        let depth = if frequency == 0 {
            ell
        } else {
            usize::try_from(frequency.trailing_zeros())
                .unwrap_or(ell)
                .min(ell)
        };
        let layer = &mut layers[depth];
        layer.frequency_count = layer.frequency_count.checked_add(1).ok_or_else(|| {
            HayesError::InvalidParameter("Fourier layer population overflow".to_owned())
        })?;
        layer.weighted_numerator =
            layer
                .weighted_numerator
                .checked_add(numerator)
                .ok_or_else(|| {
                    HayesError::InvalidParameter("Fourier layer numerator overflow".to_owned())
                })?;
    }
    Ok(layers)
}

fn inverse_mobius_fourier_numerators(
    ell: usize,
    degree: usize,
    limits: HayesLimits,
) -> Result<InverseMobiusFourierNumerators, HayesError> {
    let convolution = identity_class_mobius_convolution(ell, degree, limits)?;
    let denominator = 1_u128
        .checked_shl(u32::try_from(ell).map_err(|_| {
            HayesError::InvalidParameter("Fourier denominator shift exceeds u32".to_owned())
        })?)
        .ok_or_else(|| HayesError::InvalidParameter("Fourier denominator overflow".to_owned()))?;
    let denominator_i128 = i128::try_from(denominator)
        .map_err(|_| HayesError::InvalidParameter("Fourier denominator exceeds i128".to_owned()))?;
    let frequency_count = usize::try_from(denominator).map_err(|_| {
        HayesError::InvalidParameter("Fourier frequency count exceeds usize".to_owned())
    })?;
    let mut frequency_numerators = vec![0_i128; frequency_count];
    let mut cellwise_absolute_numerator = 0_u128;
    let mut orderwise_absolute_numerator = 0_u128;
    for term in &convolution.terms {
        let spectrum =
            inverse_additive_mobius_spectrum(ell, degree - term.interval_degree, limits)?;
        let (order_numerator, cellwise_absolute) = accumulate_inverse_mobius_fourier_order(
            &spectrum,
            term.interval_degree,
            &mut frequency_numerators,
        )?;
        let expected = term.value.checked_mul(denominator_i128).ok_or_else(|| {
            HayesError::InvalidParameter("expected Fourier order numerator overflow".to_owned())
        })?;
        if order_numerator != expected {
            return Err(HayesError::Invariant(format!(
                "Fourier regroup order d={} gives {order_numerator}, expected {expected}",
                term.interval_degree
            )));
        }
        cellwise_absolute_numerator = cellwise_absolute_numerator
            .checked_add(cellwise_absolute)
            .ok_or_else(|| {
                HayesError::InvalidParameter("Fourier cellwise total overflow".to_owned())
            })?;
        orderwise_absolute_numerator = orderwise_absolute_numerator
            .checked_add(order_numerator.unsigned_abs())
            .ok_or_else(|| {
                HayesError::InvalidParameter("Fourier orderwise total overflow".to_owned())
            })?;
    }
    Ok(InverseMobiusFourierNumerators {
        convolution,
        denominator,
        frequency_numerators,
        cellwise_absolute_numerator,
        orderwise_absolute_numerator,
    })
}

/// Regroup the exact signed Möbius convolution across Fourier frequencies.
///
/// If `v(a)` is the number of vanishing low bits of packed frequency `a`,
/// additive orthogonality gives the checked identity
///
/// ```text
/// 2^ell Delta_(ell,n)
///   = sum_a sum_(1<=d<=v(a), d<ell) d 2^d H_(n-d)(a).
/// ```
///
/// The returned layers combine all eligible `d` before taking an absolute
/// value.  They are finite diagnostics and make no uniform cancellation
/// claim.
///
/// # Errors
///
/// Returns a typed resource/representation decline from the exact spectra,
/// rejects the convolution domain, and fails if either the orderwise Fourier
/// bridge or the final regrouped identity does not reconstruct exactly.
pub fn inverse_mobius_fourier_regroup(
    ell: usize,
    degree: usize,
    limits: HayesLimits,
) -> Result<InverseMobiusFourierRegroupReport, HayesError> {
    let numerators = inverse_mobius_fourier_numerators(ell, degree, limits)?;
    let InverseMobiusFourierNumerators {
        convolution,
        denominator,
        frequency_numerators,
        cellwise_absolute_numerator,
        orderwise_absolute_numerator,
    } = numerators;
    let denominator_i128 = i128::try_from(denominator)
        .map_err(|_| HayesError::InvalidParameter("Fourier denominator exceeds i128".to_owned()))?;
    let layers = inverse_mobius_fourier_layers(ell, &frequency_numerators)?;
    let regrouped_numerator = layers.iter().try_fold(0_i128, |sum, layer| {
        sum.checked_add(layer.weighted_numerator).ok_or_else(|| {
            HayesError::InvalidParameter("Fourier regrouped numerator overflow".to_owned())
        })
    })?;
    let expected = convolution
        .discrepancy
        .checked_mul(denominator_i128)
        .ok_or_else(|| {
            HayesError::InvalidParameter("expected regrouped numerator overflow".to_owned())
        })?;
    if regrouped_numerator != expected {
        return Err(HayesError::Invariant(format!(
            "Fourier regroup gives {regrouped_numerator}, expected {expected}"
        )));
    }
    let layerwise_absolute_numerator = layers.iter().try_fold(0_u128, |sum, layer| {
        sum.checked_add(layer.weighted_numerator.unsigned_abs())
            .ok_or_else(|| {
                HayesError::InvalidParameter("Fourier layerwise total overflow".to_owned())
            })
    })?;
    Ok(InverseMobiusFourierRegroupReport {
        ell,
        degree,
        denominator,
        layers,
        regrouped_numerator,
        discrepancy: convolution.discrepancy,
        cellwise_absolute_numerator,
        orderwise_absolute_numerator,
        layerwise_absolute_numerator,
    })
}

fn connected_top_fourier_frequencies(
    fine: &InverseMobiusFourierNumerators,
    coarse: &InverseMobiusFourierNumerators,
) -> Result<(Vec<i128>, i128), HayesError> {
    if coarse.frequency_numerators.len() > fine.frequency_numerators.len() {
        return Err(HayesError::Invariant(
            "coarse Fourier data does not embed in the fine domain".to_owned(),
        ));
    }
    let mut frequencies = fine.frequency_numerators.clone();
    for (fine_value, coarse_value) in frequencies.iter_mut().zip(&coarse.frequency_numerators) {
        *fine_value = fine_value.checked_sub(*coarse_value).ok_or_else(|| {
            HayesError::InvalidParameter("connected Fourier frequency overflow".to_owned())
        })?;
    }
    let fine_scale = i128::try_from(fine.denominator)
        .map_err(|_| HayesError::InvalidParameter("fine denominator exceeds i128".to_owned()))?;
    let coarse_scale = i128::try_from(coarse.denominator)
        .map_err(|_| HayesError::InvalidParameter("coarse denominator exceeds i128".to_owned()))?;
    let connected_trace = fine
        .convolution
        .discrepancy
        .checked_mul(fine_scale)
        .and_then(|value| {
            coarse
                .convolution
                .discrepancy
                .checked_mul(coarse_scale)
                .and_then(|coarse_value| value.checked_sub(coarse_value))
        })
        .ok_or_else(|| {
            HayesError::InvalidParameter("connected Fourier trace overflow".to_owned())
        })?;
    let reconstructed = frequencies.iter().try_fold(0_i128, |sum, value| {
        sum.checked_add(*value).ok_or_else(|| {
            HayesError::InvalidParameter("connected Fourier reconstruction overflow".to_owned())
        })
    })?;
    if reconstructed != connected_trace {
        return Err(HayesError::Invariant(format!(
            "connected Fourier frequencies give {reconstructed}, expected {connected_trace}"
        )));
    }
    Ok((frequencies, connected_trace))
}

fn check_inverse_mobius_spectrum_quotient(
    ell: usize,
    coarse_level: usize,
    degree: usize,
    limits: HayesLimits,
) -> Result<(), HayesError> {
    for interval_degree in 1..coarse_level {
        let mobius_degree = degree - interval_degree;
        let fine = inverse_additive_mobius_spectrum(ell, mobius_degree, limits)?;
        let coarse = inverse_additive_mobius_spectrum(coarse_level, mobius_degree, limits)?;
        if fine.values[..coarse.values.len()] != coarse.values {
            return Err(HayesError::Invariant(format!(
                "coarse inverse spectrum fails quotient embedding at d={interval_degree}"
            )));
        }
    }
    Ok(())
}

struct ConnectedTopFourierNormLedger {
    square_sum: BigUint,
    cauchy_bound_square: BigUint,
    allowance_square: BigUint,
    maximum_square_sum: BigUint,
    required_saving_ceiling: BigUint,
}

fn connected_top_fourier_norm_ledger(
    frequencies: &[i128],
    support_bound: u128,
    allowance: &BigUint,
) -> ConnectedTopFourierNormLedger {
    let square_sum = frequencies.iter().fold(BigUint::from(0_u8), |sum, value| {
        let magnitude = BigUint::from(value.unsigned_abs());
        sum + &magnitude * &magnitude
    });
    let support = BigUint::from(support_bound);
    let cauchy_bound_square = &support * &square_sum;
    let allowance_square = allowance.pow(2);
    let maximum_square_sum = &allowance_square / &support;
    let required_saving_ceiling =
        (&square_sum + &maximum_square_sum - BigUint::from(1_u8)) / &maximum_square_sum;
    ConnectedTopFourierNormLedger {
        square_sum,
        cauchy_bound_square,
        allowance_square,
        maximum_square_sum,
        required_saving_ceiling,
    }
}

/// Combine the top-conductor quotient and every Möbius order in one additive
/// Fourier domain.
///
/// Projection `E_ell -> E_coarse` commutes with unit inversion.  Consequently
/// the coarse Walsh spectrum at each shared Möbius degree must equal the slice
/// of the fine spectrum whose higher frequency bits vanish.  This operation
/// checks that compatibility exactly, inflates the coarse contribution into
/// the fine domain, subtracts it frequencywise, and only then groups by
/// annihilator depth.
///
/// # Errors
///
/// Returns a typed admission or checked-arithmetic decline, rejects a
/// nonpositive coarse level, and fails closed if quotient compatibility or
/// any independent connected-trace reconstruction is violated.
pub fn connected_top_inverse_mobius_fourier_regroup(
    ell: usize,
    degree: usize,
    limits: HayesLimits,
) -> Result<ConnectedTopInverseMobiusFourierRegroupReport, HayesError> {
    let implication = population_refinement_connected_top_implication(ell, degree)?;
    let first_top_level = implication.first_top_level;
    let coarse_level = first_top_level.checked_sub(1).ok_or_else(|| {
        HayesError::InvalidParameter("connected top coarse level underflow".to_owned())
    })?;
    if coarse_level == 0 {
        return Err(HayesError::InvalidParameter(
            "connected Fourier regroup requires a positive coarse level".to_owned(),
        ));
    }
    check_inverse_mobius_spectrum_quotient(ell, coarse_level, degree, limits)?;
    let fine = inverse_mobius_fourier_numerators(ell, degree, limits)?;
    let coarse = inverse_mobius_fourier_numerators(coarse_level, degree, limits)?;
    let (frequency_numerators, connected_trace) =
        connected_top_fourier_frequencies(&fine, &coarse)?;
    if frequency_numerators[..coarse.frequency_numerators.len()]
        .iter()
        .any(|value| *value != 0)
    {
        return Err(HayesError::Invariant(
            "connected projector retains an inflated coarse frequency".to_owned(),
        ));
    }

    let connected_orders = connected_top_mobius_convolution(ell, degree, limits)?;
    if connected_orders.signed_connected_trace != BigInt::from(connected_trace) {
        return Err(HayesError::Invariant(
            "connected Fourier and order reconstructions disagree".to_owned(),
        ));
    }
    let orderwise_absolute_numerator =
        connected_orders
            .terms
            .iter()
            .try_fold(0_u128, |sum, term| {
                let magnitude = u128::try_from(term.connected_value.magnitude()).map_err(|_| {
                    HayesError::InvalidParameter(
                        "connected Fourier order magnitude exceeds u128".to_owned(),
                    )
                })?;
                sum.checked_add(magnitude).ok_or_else(|| {
                    HayesError::InvalidParameter(
                        "connected Fourier order total overflow".to_owned(),
                    )
                })
            })?;
    let cellwise_absolute_numerator = fine
        .cellwise_absolute_numerator
        .checked_add(coarse.cellwise_absolute_numerator)
        .ok_or_else(|| {
            HayesError::InvalidParameter("connected Fourier cellwise total overflow".to_owned())
        })?;
    let frequencywise_absolute_numerator =
        frequency_numerators.iter().try_fold(0_u128, |sum, value| {
            sum.checked_add(value.unsigned_abs()).ok_or_else(|| {
                HayesError::InvalidParameter(
                    "connected Fourier frequencywise total overflow".to_owned(),
                )
            })
        })?;
    let layers = inverse_mobius_fourier_layers(ell, &frequency_numerators)?;
    let layerwise_absolute_numerator = layers.iter().try_fold(0_u128, |sum, layer| {
        sum.checked_add(layer.weighted_numerator.unsigned_abs())
            .ok_or_else(|| {
                HayesError::InvalidParameter(
                    "connected Fourier layerwise total overflow".to_owned(),
                )
            })
    })?;
    let high_frequency_support_bound = fine.denominator - coarse.denominator;
    let norm = connected_top_fourier_norm_ledger(
        &frequency_numerators,
        high_frequency_support_bound,
        &implication.connected_top_assumption_numerator,
    );
    Ok(ConnectedTopInverseMobiusFourierRegroupReport {
        ell,
        degree,
        first_top_level,
        coarse_level,
        cancelled_coarse_frequency_count: coarse.denominator,
        high_frequency_support_bound,
        layers,
        connected_trace,
        cellwise_absolute_numerator,
        orderwise_absolute_numerator,
        frequencywise_absolute_numerator,
        layerwise_absolute_numerator,
        frequency_square_sum: norm.square_sum,
        frequency_cauchy_bound_square: norm.cauchy_bound_square,
        connected_allowance_square: norm.allowance_square,
        maximum_frequency_square_sum_for_candidate: norm.maximum_square_sum,
        required_frequency_square_sum_saving_ceiling: norm.required_saving_ceiling,
    })
}

fn symmetric_quadruple_multiplicity(indices: [usize; 4]) -> usize {
    let mut denominator = 1_usize;
    let mut run = 1_usize;
    for position in 1..4 {
        if indices[position] == indices[position - 1] {
            run += 1;
        } else {
            denominator *= match run {
                1 => 1,
                2 => 2,
                3 => 6,
                4 => 24,
                _ => unreachable!(),
            };
            run = 1;
        }
    }
    denominator *= match run {
        1 => 1,
        2 => 2,
        3 => 6,
        4 => 24,
        _ => unreachable!(),
    };
    24 / denominator
}

/// Expand the exact endpoint fourth cumulant into convolution-order cells.
///
/// For `1<=d<ell`, let
///
/// ```text
/// T_d(e)=d sum_(u in V_d) M_(degree-d)(e u^(-1)).
/// ```
///
/// The operation first checks `D_e=sum_d T_d(e)` against every exact class
/// discrepancy.  It then returns the symmetric tensor cells
///
/// ```text
/// 2^ell sum_e T_a T_b T_c T_d
///   -(C_ab C_cd+C_ac C_bd+C_ad C_bc),
/// C_ab=sum_e T_a T_b.
/// ```
///
/// Summing the cells with their permutation multiplicities reconstructs the
/// direct fourth-cumulant numerator exactly.  This is a finite diagnostic and
/// does not bound any cell uniformly.
///
/// # Errors
///
/// Returns typed parameter/resource declines or an invariant error if the
/// order decomposition fails either classwise or cumulant reconstruction.
#[allow(clippy::too_many_lines)]
pub fn connected_order_cumulant_report(
    ell: usize,
    degree: usize,
    limits: HayesLimits,
) -> Result<ConnectedOrderCumulantReport, HayesError> {
    admit(ell, degree, limits)?;
    let odd = ell.checked_mul(2).and_then(|value| value.checked_add(1));
    let even = ell.checked_mul(2).and_then(|value| value.checked_add(2));
    if Some(degree) != odd && Some(degree) != even {
        return Err(HayesError::InvalidParameter(
            "connected order cumulant is Lemire-endpoint-only".to_owned(),
        ));
    }
    let order_count = ell.saturating_sub(1);
    let group_order = 1_usize
        .checked_shl(u32::try_from(ell).map_err(|_| {
            HayesError::InvalidParameter("connected order level exceeds u32".to_owned())
        })?)
        .ok_or_else(|| HayesError::InvalidParameter("connected order group overflow".to_owned()))?;
    let mut tuple_count = 0_usize;
    for a in 0..order_count {
        for b in a..order_count {
            for c in b..order_count {
                tuple_count = tuple_count.checked_add(order_count - c).ok_or_else(|| {
                    HayesError::InvalidParameter("order tuple count overflow".to_owned())
                })?;
            }
        }
    }
    let interval_work = (1..ell).try_fold(0_usize, |sum, d| {
        sum.checked_add(1_usize << d)
            .ok_or_else(|| HayesError::InvalidParameter("order interval work overflow".to_owned()))
    })?;
    let work = group_order
        .checked_mul(interval_work.checked_add(tuple_count).ok_or_else(|| {
            HayesError::InvalidParameter("connected order work overflow".to_owned())
        })?)
        .ok_or_else(|| HayesError::InvalidParameter("connected order work overflow".to_owned()))?;
    check_limit(
        "connected_order_cumulant_cells",
        work,
        limits.max_table_cells,
    )?;

    let (factors, unit_indices) = principal_unit_index_table(ell, limits)?;
    let mut order_vectors = Vec::with_capacity(order_count);
    for interval_degree in 1..ell {
        let mobius = class_mobius_distribution(ell, degree - interval_degree, limits)?;
        let mut inverse_indices = Vec::with_capacity(1_usize << interval_degree);
        for tail in 0..1_u64 << interval_degree {
            let unit = 1 | (tail << 1);
            let inverse = principal_unit_inverse(unit, ell);
            inverse_indices.push(unit_indices[&inverse]);
        }
        let weight = i128::try_from(interval_degree)
            .map_err(|_| HayesError::InvalidParameter("interval degree exceeds i128".to_owned()))?;
        let mut values = Vec::with_capacity(group_order);
        for class in 0..group_order {
            let sum = inverse_indices.iter().try_fold(0_i128, |sum, inverse| {
                let shifted = add_mixed_radix_indices(class, *inverse, &factors)?;
                sum.checked_add(mobius.values[shifted]).ok_or_else(|| {
                    HayesError::InvalidParameter("order class sum overflow".to_owned())
                })
            })?;
            values.push(sum.checked_mul(weight).ok_or_else(|| {
                HayesError::InvalidParameter("weighted order class sum overflow".to_owned())
            })?);
        }
        order_vectors.push(values);
    }

    let distribution = class_population_distribution(ell, degree, limits)?;
    let mean = distribution.uniform_mean().ok_or_else(|| {
        HayesError::InvalidParameter("endpoint distribution has no uniform mean".to_owned())
    })?;
    for class in 0..group_order {
        let reconstructed = order_vectors.iter().try_fold(0_i128, |sum, values| {
            sum.checked_add(values[class]).ok_or_else(|| {
                HayesError::InvalidParameter("classwise order reconstruction overflow".to_owned())
            })
        })?;
        let expected = i128::try_from(distribution.counts[class])
            .and_then(|count| i128::try_from(mean).map(|mean| count - mean))
            .map_err(|_| {
                HayesError::InvalidParameter("class discrepancy exceeds i128".to_owned())
            })?;
        if reconstructed != expected {
            return Err(HayesError::Invariant(format!(
                "class {class}: order sum {reconstructed}, expected {expected}"
            )));
        }
    }

    let mut covariance = vec![vec![BigInt::from(0_i8); order_count]; order_count];
    for a in 0..order_count {
        for b in a..order_count {
            let value = (0..group_order)
                .map(|class| {
                    BigInt::from(order_vectors[a][class]) * BigInt::from(order_vectors[b][class])
                })
                .sum::<BigInt>();
            covariance[a][b].clone_from(&value);
            covariance[b][a] = value;
        }
    }
    let group_order_big = BigInt::from(group_order);
    let mut cells = Vec::with_capacity(tuple_count);
    let mut reconstructed = BigInt::from(0_i8);
    for a in 0..order_count {
        for b in a..order_count {
            for c in b..order_count {
                for d in c..order_count {
                    let raw = (0..group_order)
                        .map(|class| {
                            BigInt::from(order_vectors[a][class])
                                * BigInt::from(order_vectors[b][class])
                                * BigInt::from(order_vectors[c][class])
                                * BigInt::from(order_vectors[d][class])
                        })
                        .sum::<BigInt>();
                    let pairing = &covariance[a][b] * &covariance[c][d]
                        + &covariance[a][c] * &covariance[b][d]
                        + &covariance[a][d] * &covariance[b][c];
                    let connected = &group_order_big * &raw - &pairing;
                    let indices = [a, b, c, d];
                    let multiplicity = symmetric_quadruple_multiplicity(indices);
                    reconstructed += BigInt::from(multiplicity) * &connected;
                    cells.push(ConnectedOrderCumulantCell {
                        interval_degrees: [a + 1, b + 1, c + 1, d + 1],
                        permutation_multiplicity: multiplicity,
                        raw_fourth_sum: raw,
                        pairing_sum: pairing,
                        connected_numerator: connected,
                    });
                }
            }
        }
    }
    let direct = distribution.fourth_cumulant_numerator()?;
    if reconstructed != direct {
        return Err(HayesError::Invariant(format!(
            "order cumulant reconstructs {reconstructed}, expected {direct}"
        )));
    }
    Ok(ConnectedOrderCumulantReport {
        ell,
        degree,
        order_count,
        cells,
        reconstructed_fourth_cumulant_numerator: reconstructed,
        direct_fourth_cumulant_numerator: direct,
    })
}

/// Decompose one identity-class Mangoldt discrepancy into Möbius terms.
///
/// If `A_d` is the class distribution of monic degree-`d` polynomials and
/// `M=A^(-1)`, logarithmic differentiation gives
///
/// ```text
/// Lambda_n = sum_(1<=d<=n) d A_d M_(n-d).
/// ```
///
/// For `d>=ell`, `A_d` is uniform.  The ordinary polynomial Möbius totals
/// vanish above degree one, so the `d=n-1,n` terms combine to the uniform
/// mean and every other uniform term vanishes.  Consequently
///
/// ```text
/// Delta_(ell,n)
///   = sum_(1<=d<ell) d sum_(u in V_d) M_(n-d)(u^(-1)).
/// ```
///
/// This operation checks that exact identity.  It does not bound the signed
/// sum uniformly in `ell`.
///
/// # Errors
///
/// Returns a typed resource or representation decline, rejects
/// `degree<ell+1`, and reports failed transform, CRT, or reconstruction
/// invariants.
pub fn identity_class_mobius_convolution(
    ell: usize,
    degree: usize,
    limits: HayesLimits,
) -> Result<IdentityClassMobiusConvolution, HayesError> {
    admit(ell, degree, limits)?;
    if degree <= ell {
        return Err(HayesError::InvalidParameter(
            "Mobius convolution decomposition requires degree>=ell+1".to_owned(),
        ));
    }
    let first = identity_class_mobius_convolution_residue(ell, degree, PRIME_ONE)?;
    let second = identity_class_mobius_convolution_residue(ell, degree, PRIME_TWO)?;
    if first.len() != second.len() {
        return Err(HayesError::Invariant(
            "Mobius-convolution residue vectors have different lengths".to_owned(),
        ));
    }
    let crt_modulus = u128::from(PRIME_ONE) * u128::from(PRIME_TWO);
    let half_modulus = crt_modulus / 2;
    let power_bound = 1_u128
        .checked_shl(u32::try_from(degree).map_err(|_| {
            HayesError::InvalidParameter("degree does not fit the shift domain".to_owned())
        })?)
        .ok_or_else(|| {
            HayesError::InvalidParameter("degree exceeds the exact i128 domain".to_owned())
        })?;
    let mut terms = Vec::with_capacity(ell.saturating_sub(1));
    for (offset, (first_residue, second_residue)) in first.into_iter().zip(second).enumerate() {
        let interval_degree = offset + 1;
        let magnitude_bound = power_bound
            .checked_mul(interval_degree as u128)
            .ok_or_else(|| {
                HayesError::InvalidParameter("Mobius-convolution term bound overflow".to_owned())
            })?;
        if magnitude_bound
            .checked_mul(2)
            .is_none_or(|width| width >= crt_modulus)
        {
            return Err(HayesError::InvalidParameter(format!(
                "signed Mobius-convolution term at d={interval_degree} does not fit uniquely below the CRT modulus"
            )));
        }
        let unsigned = crt(first_residue, PRIME_ONE, second_residue, PRIME_TWO)?;
        let value = if unsigned <= half_modulus {
            i128::try_from(unsigned).map_err(|_| {
                HayesError::Invariant("positive convolution CRT value exceeds i128".to_owned())
            })?
        } else {
            i128::try_from(unsigned).map_err(|_| {
                HayesError::Invariant("negative convolution CRT residue exceeds i128".to_owned())
            })? - i128::try_from(crt_modulus).map_err(|_| {
                HayesError::Invariant("convolution CRT modulus exceeds i128".to_owned())
            })?
        };
        if value.unsigned_abs() > magnitude_bound {
            return Err(HayesError::Invariant(format!(
                "Mobius-convolution term {value} exceeds its coarse bound at d={interval_degree}"
            )));
        }
        terms.push(MobiusConvolutionTerm {
            interval_degree,
            value,
        });
    }

    let mangoldt_population = identity_class_count(ell, degree, limits)?;
    let uniform_mean = 1_u128 << (degree - ell);
    let discrepancy = i128::try_from(mangoldt_population).map_err(|_| {
        HayesError::InvalidParameter("Mangoldt population does not fit i128".to_owned())
    })? - i128::try_from(uniform_mean)
        .map_err(|_| HayesError::InvalidParameter("uniform mean does not fit i128".to_owned()))?;
    let reconstructed = terms.iter().try_fold(0_i128, |sum, term| {
        sum.checked_add(term.value).ok_or_else(|| {
            HayesError::InvalidParameter("Mobius-convolution sum exceeds i128".to_owned())
        })
    })?;
    if reconstructed != discrepancy {
        return Err(HayesError::Invariant(format!(
            "Mobius convolution reconstructs {reconstructed}, expected discrepancy {discrepancy}"
        )));
    }
    Ok(IdentityClassMobiusConvolution {
        ell,
        degree,
        uniform_mean,
        mangoldt_population,
        discrepancy,
        terms,
    })
}

/// Decompose the connected top-conductor trace by Möbius convolution order.
///
/// With `a=ell-ceil(log2(ell))-1`, the selected endpoint trace is
///
/// ```text
/// 2^ell Delta_ell-2^(a-1) Delta_(a-1).
/// ```
///
/// Applying [`identity_class_mobius_convolution`] at both levels gives an
/// exact signed contribution for every interval degree before any absolute
/// value is taken.  This is a bounded diagnostic: it does not estimate the
/// resulting order sum uniformly.
///
/// # Errors
///
/// Rejects endpoints whose connected window reaches level one, and propagates
/// any bounded convolution or invariant failure.
pub fn connected_top_mobius_convolution(
    ell: usize,
    degree: usize,
    limits: HayesLimits,
) -> Result<ConnectedTopMobiusConvolutionReport, HayesError> {
    let implication = population_refinement_connected_top_implication(ell, degree)?;
    let first_top_level = implication.first_top_level;
    let coarse_level = first_top_level.checked_sub(1).ok_or_else(|| {
        HayesError::InvalidParameter("connected top coarse level underflow".to_owned())
    })?;
    if coarse_level == 0 {
        return Err(HayesError::InvalidParameter(
            "connected Möbius decomposition requires a positive coarse level".to_owned(),
        ));
    }
    let fine = identity_class_mobius_convolution(ell, degree, limits)?;
    let coarse = identity_class_mobius_convolution(coarse_level, degree, limits)?;
    let fine_scale = BigInt::from(BigUint::from(1_u8) << ell);
    let coarse_scale = BigInt::from(BigUint::from(1_u8) << coarse_level);
    if &fine_scale * BigInt::from(fine.uniform_mean)
        != &coarse_scale * BigInt::from(coarse.uniform_mean)
    {
        return Err(HayesError::Invariant(
            "connected top fine/coarse main terms do not cancel".to_owned(),
        ));
    }
    let mut signed_connected_trace = BigInt::from(0_u8);
    let mut orderwise_absolute_trace = BigUint::from(0_u8);
    let mut terms = Vec::with_capacity(fine.terms.len());
    for fine_term in fine.terms {
        let coarse_value = coarse
            .terms
            .get(fine_term.interval_degree - 1)
            .map_or(0_i128, |term| term.value);
        let connected_value = &fine_scale * BigInt::from(fine_term.value)
            - &coarse_scale * BigInt::from(coarse_value);
        signed_connected_trace += &connected_value;
        orderwise_absolute_trace += connected_value.magnitude();
        terms.push(ConnectedTopMobiusConvolutionTerm {
            interval_degree: fine_term.interval_degree,
            fine_value: fine_term.value,
            coarse_value,
            connected_value,
        });
    }
    let direct = &fine_scale * BigInt::from(fine.mangoldt_population)
        - &coarse_scale * BigInt::from(coarse.mangoldt_population);
    if signed_connected_trace != direct {
        return Err(HayesError::Invariant(format!(
            "connected Möbius orders reconstruct {signed_connected_trace}, expected {direct}"
        )));
    }
    let first_nonzero_interval_degree = terms
        .iter()
        .find(|term| term.connected_value != BigInt::from(0_u8))
        .map(|term| term.interval_degree);
    let nonzero_order_count = terms
        .iter()
        .filter(|term| term.connected_value != BigInt::from(0_u8))
        .count();
    Ok(ConnectedTopMobiusConvolutionReport {
        ell,
        degree,
        first_top_level,
        coarse_level,
        terms,
        first_nonzero_interval_degree,
        nonzero_order_count,
        signed_connected_trace,
        orderwise_absolute_trace,
    })
}

/// Certify the exact proper-prime-power reduction at `n = 2 ell + 1`.
///
/// This operation is structural: it enumerates divisors and checks the
/// principal-unit group order, but performs no Fourier transform and allocates
/// no class table.  The caller's `ell`, degree, and group-order limits are
/// still enforced before the divisor scan.
///
/// # Errors
///
/// Rejects `ell = 0`, arithmetic outside the host representation, caller
/// limits, or any violation of the odd-endpoint divisor invariants.
pub fn odd_endpoint_prime_power_reduction(
    ell: usize,
    limits: HayesLimits,
) -> Result<OddEndpointPrimePowerReduction, HayesError> {
    if ell == 0 {
        return Err(HayesError::InvalidParameter(
            "ell must be positive".to_owned(),
        ));
    }
    check_limit("ell", ell, limits.max_ell)?;
    let degree = ell
        .checked_mul(2)
        .and_then(|value| value.checked_add(1))
        .ok_or_else(|| HayesError::InvalidParameter("odd endpoint degree overflow".to_owned()))?;
    check_limit("degree", degree, limits.max_degree)?;
    let shift = u32::try_from(ell).map_err(|_| {
        HayesError::InvalidParameter("ell exceeds the host shift domain".to_owned())
    })?;
    let group_order = 1_usize.checked_shl(shift).ok_or_else(|| {
        HayesError::InvalidParameter("ell exceeds the host shift domain".to_owned())
    })?;
    check_limit("group_order", group_order, limits.max_group_order)?;

    let mut proper_divisors = Vec::new();
    for prime_degree in positive_divisors(degree) {
        if prime_degree == degree {
            continue;
        }
        let exponent = degree / prime_degree;
        if prime_degree > ell || exponent < 3 || exponent.is_multiple_of(2) {
            return Err(HayesError::Invariant(format!(
                "odd endpoint divisor invariant failed: ell={ell}, degree={degree}, prime_degree={prime_degree}, exponent={exponent}"
            )));
        }
        proper_divisors.push(OddEndpointProperDivisor {
            prime_degree,
            exponent,
        });
    }
    if proper_divisors
        .first()
        .is_none_or(|term| term.prime_degree != 1 || term.exponent != degree)
    {
        return Err(HayesError::Invariant(
            "odd endpoint divisor list does not begin with the ramified x-power".to_owned(),
        ));
    }

    Ok(OddEndpointPrimePowerReduction {
        ell,
        degree,
        group_order,
        proper_divisors,
        proper_prime_power_population: 1,
    })
}

/// Check the exact half-interval truncated-Möbius identity and one factor pattern.
///
/// Every monic constant-one divisor `D` of degree `d <= m` divides exactly
/// `2^(m-d)` members of the degree-`degree` half interval.  Removing the
/// ramified prime `x` from the polynomial Euler product gives
///
/// ```text
/// product_(P != x) (1-u^deg(P)) = (1-2u)/(1-u) = 1-u-u^2-...,
/// ```
///
/// so the aggregate truncated weight is exactly one.  The caller-supplied
/// factor degrees expose whether this otherwise tempting lower-bound weight is
/// positive on a composite factorization pattern.
///
/// # Errors
///
/// Rejects degrees below two, caller limits, a zero factor degree, a
/// distinct-factor degree sum larger than the polynomial degree, or an
/// allocation-size overflow.
pub fn half_interval_mobius_sieve_report(
    degree: usize,
    distinct_factor_degrees: &[usize],
    limits: HayesLimits,
) -> Result<HalfIntervalMobiusSieveReport, HayesError> {
    if degree < 2 {
        return Err(HayesError::InvalidParameter(
            "half-interval sieve degree must be at least two".to_owned(),
        ));
    }
    check_limit("degree", degree, limits.max_degree)?;
    let cutoff = degree / 2;
    check_limit("ell", cutoff, limits.max_ell)?;
    if distinct_factor_degrees.contains(&0) {
        return Err(HayesError::InvalidParameter(
            "distinct irreducible-factor degrees must be positive".to_owned(),
        ));
    }
    let factor_degree_sum = distinct_factor_degrees
        .iter()
        .try_fold(0_usize, |sum, &factor_degree| {
            sum.checked_add(factor_degree)
        })
        .ok_or_else(|| HayesError::InvalidParameter("factor-degree sum overflow".to_owned()))?;
    if factor_degree_sum > degree {
        return Err(HayesError::InvalidParameter(format!(
            "distinct factor degrees sum to {factor_degree_sum}, exceeding degree {degree}"
        )));
    }

    // Coefficients through u^m of product_i (1-u^d_i), evaluated at u=1.
    // Descending updates ensure that each supplied distinct factor is selected
    // at most once even when several factors have the same degree.
    let coefficient_count = cutoff.checked_add(1).ok_or_else(|| {
        HayesError::InvalidParameter("Möbius coefficient count overflow".to_owned())
    })?;
    let mut coefficients = vec![BigInt::from(0_u8); coefficient_count];
    coefficients[0] = BigInt::from(1_u8);
    for &factor_degree in distinct_factor_degrees {
        if factor_degree > cutoff {
            continue;
        }
        for current_degree in (factor_degree..=cutoff).rev() {
            let selected = coefficients[current_degree - factor_degree].clone();
            coefficients[current_degree] -= selected;
        }
    }
    let candidate_weight = coefficients.into_iter().sum::<BigInt>();

    let interval_size = BigInt::from(1_u8) << cutoff;
    let nonconstant_geometric_sum = &interval_size - BigInt::from(1_u8);
    let total_weight = &interval_size - nonconstant_geometric_sum;
    if total_weight != BigInt::from(1_u8) {
        return Err(HayesError::Invariant(
            "half-interval truncated Möbius identity did not reconstruct one".to_owned(),
        ));
    }

    Ok(HalfIntervalMobiusSieveReport {
        degree,
        cutoff,
        interval_size,
        total_weight,
        distinct_factor_degrees: distinct_factor_degrees.to_vec(),
        candidate_weight,
    })
}

/// Remove every proper-prime-power contribution from the identity Hayes class.
///
/// This is exact finite-group Möbius inversion.  For every divisor `d` of the
/// target degree and every class `e`, it checks
///
/// ```text
/// N_d(e) = sum_(r | d) r * sum_(a^(d/r) = e) I_r(a),
/// ```
///
/// where `N_d` is the Mangoldt population and `I_r(a)` counts degree-`r`
/// monic irreducibles in class `a`.  All class powers are evaluated directly
/// in the mixed-radix principal-unit coordinates.  Search is not involved.
///
/// # Errors
///
/// Returns a typed resource decline before each transform, rejects zero or
/// out-of-range parameters, and fails closed if a population subtraction is
/// negative, is not divisible by its degree, or does not reconstruct exactly.
pub fn identity_class_irreducible_count(
    ell: usize,
    degree: usize,
    limits: HayesLimits,
) -> Result<IdentityClassIrreducibleReport, HayesError> {
    admit_any_positive_degree(ell, degree, limits)?;
    let factors = principal_unit_factors(ell);
    let divisors = positive_divisors(degree);
    let mut irreducibles = BTreeMap::<usize, Vec<u128>>::new();
    let mut target_mangoldt = 0_u128;
    let mut target_proper = 0_u128;
    let mut target_irreducible = 0_u128;

    for current_degree in divisors {
        admit_any_positive_degree(ell, current_degree, limits)?;
        let population = class_population_distribution_admitted(ell, current_degree)?;
        let mut proper = vec![0_u128; population.counts.len()];
        for (&prime_degree, counts) in irreducibles.range(..current_degree) {
            if !current_degree.is_multiple_of(prime_degree) {
                continue;
            }
            let exponent = current_degree / prime_degree;
            for (class_index, count) in counts.iter().copied().enumerate() {
                if count == 0 {
                    continue;
                }
                let powered = power_mixed_radix_index(class_index, exponent, &factors)?;
                let weighted = count.checked_mul(prime_degree as u128).ok_or_else(|| {
                    HayesError::InvalidParameter(
                        "proper-prime-power contribution exceeds u128".to_owned(),
                    )
                })?;
                proper[powered] = proper[powered].checked_add(weighted).ok_or_else(|| {
                    HayesError::InvalidParameter(
                        "proper-prime-power population exceeds u128".to_owned(),
                    )
                })?;
            }
        }

        let divisor = current_degree as u128;
        let mut current_irreducibles = Vec::with_capacity(population.counts.len());
        for (class_index, (mangoldt, proper_power)) in population
            .counts
            .iter()
            .copied()
            .zip(proper.iter().copied())
            .enumerate()
        {
            let weighted_new = mangoldt.checked_sub(proper_power).ok_or_else(|| {
                HayesError::Invariant(format!(
                    "degree {current_degree}, class {class_index}: proper prime powers exceed the Mangoldt population"
                ))
            })?;
            if !weighted_new.is_multiple_of(divisor) {
                return Err(HayesError::Invariant(format!(
                    "degree {current_degree}, class {class_index}: new-prime population is not divisible by the degree"
                )));
            }
            let count = weighted_new / divisor;
            let reconstructed = proper_power
                .checked_add(count.checked_mul(divisor).ok_or_else(|| {
                    HayesError::InvalidParameter(
                        "irreducible reconstruction exceeds u128".to_owned(),
                    )
                })?)
                .ok_or_else(|| {
                    HayesError::InvalidParameter(
                        "irreducible reconstruction exceeds u128".to_owned(),
                    )
                })?;
            if reconstructed != mangoldt {
                return Err(HayesError::Invariant(format!(
                    "degree {current_degree}, class {class_index}: irreducible reconstruction failed"
                )));
            }
            current_irreducibles.push(count);
        }

        if current_degree == degree {
            target_mangoldt = population.counts[0];
            target_proper = proper[0];
            target_irreducible = current_irreducibles[0];
        }
        irreducibles.insert(current_degree, current_irreducibles);
    }

    Ok(IdentityClassIrreducibleReport {
        ell,
        degree,
        mangoldt_population: target_mangoldt,
        proper_prime_power_population: target_proper,
        irreducible_count: target_irreducible,
    })
}

fn class_population_distribution_admitted(
    ell: usize,
    degree: usize,
) -> Result<ClassPopulationDistribution, HayesError> {
    let shift = u32::try_from(degree).map_err(|_| {
        HayesError::InvalidParameter("degree does not fit the shift domain".to_owned())
    })?;
    let total = 1_u128.checked_shl(shift).ok_or_else(|| {
        HayesError::InvalidParameter("degree exceeds the exact u128 count domain".to_owned())
    })?;
    let crt_modulus = u128::from(PRIME_ONE) * u128::from(PRIME_TWO);
    if total >= crt_modulus {
        return Err(HayesError::InvalidParameter(format!(
            "2^{degree} does not fit uniquely below the CRT modulus"
        )));
    }

    let first = class_population_residue(ell, degree, PRIME_ONE)?;
    let second = class_population_residue(ell, degree, PRIME_TWO)?;
    if first.len() != second.len() {
        return Err(HayesError::Invariant(
            "class-population residue tables have different lengths".to_owned(),
        ));
    }
    let mut counts = Vec::with_capacity(first.len());
    let mut recovered_total = 0_u128;
    for (first_residue, second_residue) in first.into_iter().zip(second) {
        let count = crt(first_residue, PRIME_ONE, second_residue, PRIME_TWO)?;
        if count > total {
            return Err(HayesError::Invariant(format!(
                "recovered class count {count} exceeds 2^{degree}"
            )));
        }
        recovered_total = recovered_total.checked_add(count).ok_or_else(|| {
            HayesError::InvalidParameter(
                "class-population total exceeds the exact u128 result domain".to_owned(),
            )
        })?;
        counts.push(count);
    }
    if recovered_total != total {
        return Err(HayesError::Invariant(format!(
            "class populations sum to {recovered_total}, expected 2^{degree}={total}"
        )));
    }

    Ok(ClassPopulationDistribution {
        ell,
        degree,
        counts,
    })
}

/// Compute both Lemire/Hayes endpoint discrepancies for `ell`.
///
/// # Errors
///
/// Returns the same typed parameter, resource, and invariant failures as
/// [`identity_class_count`].
pub fn endpoint_discrepancies(
    ell: usize,
    limits: HayesLimits,
) -> Result<EndpointDiscrepancies, HayesError> {
    let twice_ell = ell.checked_mul(2).ok_or_else(|| {
        HayesError::InvalidParameter("endpoint degree calculation overflow".to_owned())
    })?;
    let odd_degree = twice_ell.checked_add(1).ok_or_else(|| {
        HayesError::InvalidParameter("odd endpoint degree calculation overflow".to_owned())
    })?;
    let even_degree = twice_ell.checked_add(2).ok_or_else(|| {
        HayesError::InvalidParameter("even endpoint degree calculation overflow".to_owned())
    })?;
    let mut discrepancies = [0_i128; 2];
    for (slot, degree) in [odd_degree, even_degree].into_iter().enumerate() {
        let exact = i128::try_from(identity_class_count(ell, degree, limits)?).map_err(|_| {
            HayesError::InvalidParameter("identity-class count does not fit i128".to_owned())
        })?;
        let main_shift = u32::try_from(degree - ell).map_err(|_| {
            HayesError::InvalidParameter("main-term shift does not fit u32".to_owned())
        })?;
        let main_term = 1_i128.checked_shl(main_shift).ok_or_else(|| {
            HayesError::InvalidParameter("main term does not fit i128".to_owned())
        })?;
        discrepancies[slot] = exact - main_term;
    }
    Ok(EndpointDiscrepancies {
        ell,
        odd: discrepancies[0],
        even: discrepancies[1],
    })
}

/// Compute exact-conductor layers `T_(1,n),...,T_(ell,n)`.
///
/// # Errors
///
/// Returns a typed parameter or resource decline, or an invariant failure if
/// the exact layers do not telescope to the cumulative discrepancy.
pub fn conductor_layers(
    ell: usize,
    degree: usize,
    limits: HayesLimits,
) -> Result<Vec<ConductorLayer>, HayesError> {
    admit(ell, degree, limits)?;
    let mut previous_cumulative = 0_i128;
    let mut layers = Vec::with_capacity(ell);
    for level in 1..=ell {
        let exact = i128::try_from(identity_class_count(level, degree, limits)?).map_err(|_| {
            HayesError::InvalidParameter("identity-class count does not fit i128".to_owned())
        })?;
        let main_shift = u32::try_from(degree - level).map_err(|_| {
            HayesError::InvalidParameter("main-term shift does not fit u32".to_owned())
        })?;
        let main_term = 1_i128.checked_shl(main_shift).ok_or_else(|| {
            HayesError::InvalidParameter("main term does not fit i128".to_owned())
        })?;
        let cumulative = (1_i128 << level) * (exact - main_term);
        layers.push(ConductorLayer {
            level,
            value: cumulative - previous_cumulative,
        });
        previous_cumulative = cumulative;
    }
    if layers.iter().map(|layer| layer.value).sum::<i128>() != previous_cumulative {
        return Err(HayesError::Invariant(
            "conductor layers do not telescope to the cumulative discrepancy".to_owned(),
        ));
    }
    if let Some(paired_level) = translation_paired_conductor_level(degree)
        && paired_level <= ell
        && layers[paired_level - 1].value != 0
    {
        return Err(HayesError::Invariant(format!(
            "translation-paired conductor layer {paired_level} is nonzero"
        )));
    }
    Ok(layers)
}

/// Test a necessary even-power trace divisibility for supersingularity.
///
/// If every Frobenius eigenvalue of the exact level were `sqrt(2)` times a
/// root of unity, then at degree `2m` their integral trace would be divisible
/// by `2^m`.  A nonzero remainder is therefore a rigorous obstruction to
/// representing the whole component by supersingular quadratic
/// Artin--Schreier/Heisenberg factors.  A zero remainder is inconclusive.
///
/// # Errors
///
/// Rejects zero or odd `degree`, then propagates the bounded exact-conductor
/// computation's parameter and resource failures.
pub fn exact_conductor_supersingularity_divisibility(
    level: usize,
    degree: usize,
    limits: HayesLimits,
) -> Result<ExactConductorSupersingularityDivisibility, HayesError> {
    if degree == 0 || !degree.is_multiple_of(2) {
        return Err(HayesError::InvalidParameter(
            "supersingularity divisibility requires a positive even degree".to_owned(),
        ));
    }
    let trace = conductor_layers(level, degree, limits)?[level - 1].value;
    let necessary_divisor = BigUint::from(1_u8) << (degree / 2);
    let magnitude = BigUint::from(trace.unsigned_abs());
    let magnitude_remainder = &magnitude % &necessary_divisor;
    Ok(ExactConductorSupersingularityDivisibility {
        level,
        degree,
        trace,
        necessary_divisor,
        magnitude_remainder,
    })
}

/// Compute the exact Fourier second moment of one conductor family.
///
/// Two modular character tables are paired with their inverse characters;
/// checked CRT reconstruction uses the individual Weil bound only as an
/// a-priori uniqueness limit.  The returned value itself is exact.
///
/// # Errors
///
/// Returns a typed admission error, or declines when the two-prime CRT range
/// cannot uniquely represent the proven second-moment upper bound.
pub fn exact_conductor_second_moment(
    level: usize,
    degree: usize,
    limits: HayesLimits,
) -> Result<ExactConductorSecondMoment, HayesError> {
    admit(level, degree, limits)?;
    if level == 1 {
        return Ok(ExactConductorSecondMoment {
            level,
            degree,
            value: 0,
        });
    }
    let character_count = BigUint::from(1_u8) << (level - 1);
    let weil_factor = BigUint::from(level - 1).pow(2);
    let upper_bound = character_count * weil_factor * (BigUint::from(1_u8) << degree);
    let crt_modulus = BigUint::from(PRIME_ONE) * BigUint::from(PRIME_TWO);
    if upper_bound >= crt_modulus {
        return Err(HayesError::InvalidParameter(format!(
            "exact conductor second moment at level {level}, degree {degree} exceeds the CRT uniqueness range"
        )));
    }
    let first = exact_conductor_energy_residue(level, degree, PRIME_ONE)?;
    let second = exact_conductor_energy_residue(level, degree, PRIME_TWO)?;
    let exact = crt(first, PRIME_ONE, second, PRIME_TWO)?;
    if BigUint::from(exact) > upper_bound {
        return Err(HayesError::Invariant(
            "recovered second moment exceeds its Weil upper bound".to_owned(),
        ));
    }
    Ok(ExactConductorSecondMoment {
        level,
        degree,
        value: exact,
    })
}

/// Combine exact conductor-family second moments before applying one Cauchy
/// inequality to the connected top character sum.
///
/// This is a finite diagnostic and arithmetic implication.  It does not
/// extrapolate the observed moment or assert a uniform family estimate.
///
/// # Errors
///
/// Rejects invalid endpoints and propagates the exact second-moment CRT range
/// and resource declines.
pub fn connected_top_second_moment_cauchy(
    ell: usize,
    degree: usize,
    limits: HayesLimits,
) -> Result<ConnectedTopSecondMomentCauchy, HayesError> {
    let implication = population_refinement_connected_top_implication(ell, degree)?;
    let first_top_level = implication.first_top_level;
    let mut exact_second_moment = BigUint::from(0_u8);
    for level in first_top_level..=ell {
        exact_second_moment +=
            BigUint::from(exact_conductor_second_moment(level, degree, limits)?.value);
    }
    let character_count =
        (BigUint::from(1_u8) << ell) - (BigUint::from(1_u8) << (first_top_level - 1));
    let cauchy_bound_square = &character_count * &exact_second_moment;
    let connected_allowance_square = implication.connected_top_assumption_numerator.pow(2);
    let maximum_second_moment_for_candidate = &connected_allowance_square / &character_count;
    let required_second_moment_saving_ceiling =
        (&exact_second_moment + &maximum_second_moment_for_candidate - BigUint::from(1_u8))
            / &maximum_second_moment_for_candidate;
    Ok(ConnectedTopSecondMomentCauchy {
        ell,
        degree,
        first_top_level,
        character_count,
        exact_second_moment,
        cauchy_bound_square,
        connected_allowance_square,
        maximum_second_moment_for_candidate,
        required_second_moment_saving_ceiling,
    })
}

/// Compute the exact full-family squared deviation from uniformity.
///
/// The nontrivial character group is partitioned by exact conductor.  This
/// routine sums those exact second moments and divides by the principal-unit
/// group order using Parseval.  Exact divisibility is checked rather than
/// assumed.
///
/// # Errors
///
/// Returns any typed admission or CRT error from the conductor moments, an
/// overflow error outside the exact `u128` result domain, or an invariant error
/// if the reconstructed Fourier energy is not divisible by `2^ell`.
pub fn identity_class_fourier_variance(
    ell: usize,
    degree: usize,
    limits: HayesLimits,
) -> Result<IdentityClassFourierVariance, HayesError> {
    admit(ell, degree, limits)?;
    let shift = u32::try_from(ell).map_err(|_| {
        HayesError::InvalidParameter("ell exceeds the exact u128 shift domain".to_owned())
    })?;
    let group_order = 1_u128.checked_shl(shift).ok_or_else(|| {
        HayesError::InvalidParameter("ell exceeds the exact u128 shift domain".to_owned())
    })?;
    let mean_shift = degree.checked_sub(ell).ok_or_else(|| {
        HayesError::Invariant("admission accepted degree smaller than ell".to_owned())
    })?;
    let mean_shift = u32::try_from(mean_shift).map_err(|_| {
        HayesError::InvalidParameter("degree-ell exceeds the exact u128 shift domain".to_owned())
    })?;
    let uniform_mean = 1_u128.checked_shl(mean_shift).ok_or_else(|| {
        HayesError::InvalidParameter("degree-ell exceeds the exact u128 shift domain".to_owned())
    })?;

    let mut fourier_energy = 0_u128;
    for level in 1..=ell {
        fourier_energy = fourier_energy
            .checked_add(exact_conductor_second_moment(level, degree, limits)?.value)
            .ok_or_else(|| {
                HayesError::InvalidParameter(
                    "full-family Fourier energy exceeds the exact u128 result domain".to_owned(),
                )
            })?;
    }
    if !fourier_energy.is_multiple_of(group_order) {
        return Err(HayesError::Invariant(
            "full-family Fourier energy is not divisible by the group order".to_owned(),
        ));
    }

    Ok(IdentityClassFourierVariance {
        ell,
        degree,
        uniform_mean,
        total_squared_deviation: fourier_energy / group_order,
    })
}

fn admit(ell: usize, degree: usize, limits: HayesLimits) -> Result<(), HayesError> {
    if degree < ell {
        return Err(HayesError::InvalidParameter(format!(
            "degree {degree} is smaller than ell {ell}"
        )));
    }
    admit_any_positive_degree(ell, degree, limits)
}

fn admit_any_positive_degree(
    ell: usize,
    degree: usize,
    limits: HayesLimits,
) -> Result<(), HayesError> {
    if ell == 0 {
        return Err(HayesError::InvalidParameter(
            "ell must be positive".to_owned(),
        ));
    }
    if degree == 0 {
        return Err(HayesError::InvalidParameter(
            "degree must be positive".to_owned(),
        ));
    }
    check_limit("ell", ell, limits.max_ell)?;
    check_limit("degree", degree, limits.max_degree)?;
    let shift = u32::try_from(ell).map_err(|_| {
        HayesError::InvalidParameter("ell exceeds the host shift domain".to_owned())
    })?;
    let group_order = 1_usize.checked_shl(shift).ok_or_else(|| {
        HayesError::InvalidParameter("ell exceeds the host shift domain".to_owned())
    })?;
    check_limit("group_order", group_order, limits.max_group_order)?;
    let degree_rows = degree
        .checked_add(1)
        .ok_or_else(|| HayesError::InvalidParameter("degree row count overflow".to_owned()))?;
    let rows = ell
        .checked_add(degree_rows)
        .ok_or_else(|| HayesError::InvalidParameter("table row count overflow".to_owned()))?;
    let table_cells = rows
        .checked_mul(group_order)
        .ok_or_else(|| HayesError::InvalidParameter("table cell count overflow".to_owned()))?;
    check_limit("table_cells", table_cells, limits.max_table_cells)
}

fn check_limit(resource: &'static str, requested: usize, limit: usize) -> Result<(), HayesError> {
    if requested > limit {
        Err(HayesError::ResourceLimit {
            resource,
            requested,
            limit,
        })
    } else {
        Ok(())
    }
}

fn principal_unit_factors(ell: usize) -> Vec<PrincipalUnitFactor> {
    (1..=ell)
        .step_by(2)
        .map(|odd_degree| {
            let mut order = 1_usize;
            while odd_degree <= ell / order {
                order *= 2;
            }
            PrincipalUnitFactor { odd_degree, order }
        })
        .collect()
}

fn project_mixed_radix_index(
    index: usize,
    full_factors: &[PrincipalUnitFactor],
    quotient_factors: &[PrincipalUnitFactor],
) -> Result<usize, HayesError> {
    let mut quotient = index;
    let mut quotient_index = 0_usize;
    let mut quotient_stride = 1_usize;
    let mut quotient_factor_index = 0_usize;
    for factor in full_factors {
        let coordinate = quotient % factor.order;
        quotient /= factor.order;
        if let Some(quotient_factor) = quotient_factors.get(quotient_factor_index)
            && quotient_factor.odd_degree == factor.odd_degree
        {
            quotient_index = quotient_index
                .checked_add((coordinate % quotient_factor.order) * quotient_stride)
                .ok_or_else(|| {
                    HayesError::Invariant("projected class index overflow".to_owned())
                })?;
            quotient_stride = quotient_stride
                .checked_mul(quotient_factor.order)
                .ok_or_else(|| {
                    HayesError::Invariant("projected class stride overflow".to_owned())
                })?;
            quotient_factor_index += 1;
        }
    }
    if quotient != 0 || quotient_factor_index != quotient_factors.len() {
        return Err(HayesError::Invariant(
            "principal-unit coordinate projection is incomplete".to_owned(),
        ));
    }
    Ok(quotient_index)
}

struct RawPopulationRefinementStep {
    report: PopulationRefinementLevel,
    signed_child_differences: Vec<BigInt>,
}

fn validate_population_refinement_reconstruction(
    reconstruction: &[BigInt],
    counts: &[u128],
    expected_classes: usize,
    mean: u128,
    triangle_numerator: &BigUint,
) -> Result<u128, HayesError> {
    let group_order = BigInt::from(expected_classes);
    for (index, (reconstructed, count)) in reconstruction
        .iter()
        .zip(counts.iter().copied())
        .enumerate()
    {
        if reconstructed != &(BigInt::from(count) * &group_order) {
            return Err(HayesError::Invariant(format!(
                "population Haar expansion does not reconstruct class {index}"
            )));
        }
    }
    let maximum = counts
        .iter()
        .map(|count| count.abs_diff(mean))
        .max()
        .unwrap_or(0);
    let scaled_maximum = BigUint::from(maximum) * BigUint::from(expected_classes);
    if &scaled_maximum > triangle_numerator {
        return Err(HayesError::Invariant(
            "population Haar triangle does not dominate the actual discrepancy".to_owned(),
        ));
    }
    Ok(maximum)
}

fn connected_top_direct_trace(
    counts: &[u128],
    full_factors: &[PrincipalUnitFactor],
    ell: usize,
    first_top_level: usize,
) -> Result<BigInt, HayesError> {
    let coarse_level = first_top_level - 1;
    let coarse_factors = principal_unit_factors(coarse_level);
    let mut coarse_identity_population = 0_u128;
    for (index, count) in counts.iter().copied().enumerate() {
        if project_mixed_radix_index(index, full_factors, &coarse_factors)? == 0 {
            coarse_identity_population =
                coarse_identity_population
                    .checked_add(count)
                    .ok_or_else(|| {
                        HayesError::InvalidParameter(
                            "connected coarse identity population overflow".to_owned(),
                        )
                    })?;
        }
    }
    Ok((BigInt::from(counts[0]) << ell)
        - (BigInt::from(coarse_identity_population) << coarse_level))
}

fn raw_population_refinement_step(
    counts: &[u128],
    full_factors: &[PrincipalUnitFactor],
    level_factors: &[PrincipalUnitFactor],
    level: usize,
) -> Result<RawPopulationRefinementStep, HayesError> {
    let parent_factors = principal_unit_factors(level - 1);
    let level_order = 1_usize << level;
    let parent_order = 1_usize << (level - 1);
    let mut buckets = vec![0_u128; level_order];
    for (index, count) in counts.iter().copied().enumerate() {
        let child = project_mixed_radix_index(index, full_factors, level_factors)?;
        buckets[child] = buckets[child].checked_add(count).ok_or_else(|| {
            HayesError::InvalidParameter("refinement quotient population overflow".to_owned())
        })?;
    }
    let mut parent_children = vec![Vec::with_capacity(2); parent_order];
    for child in 0..level_order {
        let parent = if level == 1 {
            0
        } else {
            project_mixed_radix_index(child, level_factors, &parent_factors)?
        };
        parent_children[parent].push(child);
    }
    let mut signed_child_differences = vec![BigInt::from(0_u8); level_order];
    let mut witness_parent = 0_usize;
    let mut maximum_sibling_difference = 0_u128;
    for (parent, children) in parent_children.iter().enumerate() {
        if children.len() != 2 {
            return Err(HayesError::Invariant(format!(
                "population refinement level {level} is not binary"
            )));
        }
        let left = children[0];
        let right = children[1];
        let signed = BigInt::from(buckets[left]) - BigInt::from(buckets[right]);
        signed_child_differences[left].clone_from(&signed);
        signed_child_differences[right] = -signed;
        let magnitude = buckets[left].abs_diff(buckets[right]);
        if magnitude > maximum_sibling_difference {
            maximum_sibling_difference = magnitude;
            witness_parent = parent;
        }
    }
    Ok(RawPopulationRefinementStep {
        report: PopulationRefinementLevel {
            level,
            witness_parent,
            maximum_sibling_difference,
        },
        signed_child_differences,
    })
}

fn witt_haar_difference_square_sum(
    level: usize,
    quotient_factors: &[PrincipalUnitFactor],
    buckets: Vec<BigUint>,
) -> Result<BigUint, HayesError> {
    let parent_factors = principal_unit_factors(level - 1);
    let parent_order = 1_usize << (level - 1);
    let mut parent_children = vec![Vec::with_capacity(2); parent_order];
    for (child, mass) in buckets.into_iter().enumerate() {
        let parent = if level == 1 {
            0
        } else {
            project_mixed_radix_index(child, quotient_factors, &parent_factors)?
        };
        parent_children[parent].push(mass);
    }
    let mut square_sum = BigUint::from(0_u8);
    for children in parent_children {
        if children.len() != 2 {
            return Err(HayesError::Invariant(format!(
                "conductor level {level} does not split every Witt cylinder in two"
            )));
        }
        let difference = if children[0] >= children[1] {
            &children[0] - &children[1]
        } else {
            &children[1] - &children[0]
        };
        square_sum += difference.pow(2);
    }
    Ok(square_sum)
}

fn power_mixed_radix_index(
    index: usize,
    exponent: usize,
    factors: &[PrincipalUnitFactor],
) -> Result<usize, HayesError> {
    let mut quotient = index;
    let mut powered_index = 0_usize;
    let mut stride = 1_usize;
    for factor in factors {
        let coordinate = quotient % factor.order;
        quotient /= factor.order;
        let powered_coordinate = coordinate
            .checked_mul(exponent)
            .ok_or_else(|| HayesError::InvalidParameter("class-power overflow".to_owned()))?
            % factor.order;
        powered_index = powered_index
            .checked_add(powered_coordinate.checked_mul(stride).ok_or_else(|| {
                HayesError::InvalidParameter("class-power index overflow".to_owned())
            })?)
            .ok_or_else(|| HayesError::InvalidParameter("class-power index overflow".to_owned()))?;
        stride = stride.checked_mul(factor.order).ok_or_else(|| {
            HayesError::InvalidParameter("class-power stride overflow".to_owned())
        })?;
    }
    if quotient != 0 {
        return Err(HayesError::Invariant(
            "class-power input escaped the mixed-radix domain".to_owned(),
        ));
    }
    Ok(powered_index)
}

fn positive_divisors(value: usize) -> Vec<usize> {
    let mut low = Vec::new();
    let mut high = Vec::new();
    let mut divisor = 1_usize;
    while divisor <= value / divisor {
        if value.is_multiple_of(divisor) {
            low.push(divisor);
            let paired = value / divisor;
            if paired != divisor {
                high.push(paired);
            }
        }
        divisor += 1;
    }
    high.reverse();
    low.extend(high);
    low
}

fn identity_class_residue(ell: usize, target: usize, modulus: u64) -> Result<u64, HayesError> {
    let (character_values, _) = character_power_sums_residue(ell, target, modulus)?;
    let sum = character_values.iter().fold(0_u64, |accumulator, value| {
        add_mod(accumulator, *value, modulus)
    });
    let size = 1_usize << ell;
    Ok(multiply_mod(
        sum,
        mod_pow(size as u64, modulus - 2, modulus),
        modulus,
    ))
}

fn class_population_residue(
    ell: usize,
    target: usize,
    modulus: u64,
) -> Result<Vec<u64>, HayesError> {
    let (mut character_values, dimensions) = character_power_sums_residue(ell, target, modulus)?;
    invert_group_coordinates(&mut character_values, &dimensions)?;
    group_transform(&mut character_values, &dimensions, modulus);
    let inverse_order = mod_pow(character_values.len() as u64, modulus - 2, modulus);
    for value in &mut character_values {
        *value = multiply_mod(*value, inverse_order, modulus);
    }
    Ok(character_values)
}

fn class_mobius_residue(ell: usize, target: usize, modulus: u64) -> Result<Vec<u64>, HayesError> {
    let mut table = character_mobius_coefficients_through_residue(ell, target, modulus)?;
    let mut character_values = table.rows.swap_remove(target);
    invert_group_coordinates(&mut character_values, &table.dimensions)?;
    group_transform(&mut character_values, &table.dimensions, modulus);
    let inverse_order = mod_pow(character_values.len() as u64, modulus - 2, modulus);
    for value in &mut character_values {
        *value = multiply_mod(*value, inverse_order, modulus);
    }
    Ok(character_values)
}

fn identity_class_mobius_convolution_residue(
    ell: usize,
    target: usize,
    modulus: u64,
) -> Result<Vec<u64>, HayesError> {
    let mut table = character_mobius_coefficients_through_residue(ell, target - 1, modulus)?;
    let inverse_order = mod_pow((1_usize << ell) as u64, modulus - 2, modulus);
    let mut terms = Vec::with_capacity(ell.saturating_sub(1));
    for interval_degree in 1..ell {
        let row = &mut table.rows[target - interval_degree];
        invert_group_coordinates(row, &table.dimensions)?;
        group_transform(row, &table.dimensions, modulus);
        let mut fibre_sum = 0_u64;
        for tail in 0..1_u64 << interval_degree {
            let unit = 1 | (tail << 1);
            let inverse = principal_unit_inverse(unit, ell);
            fibre_sum = add_mod(
                fibre_sum,
                multiply_mod(row[table.unit_to_index[&inverse]], inverse_order, modulus),
                modulus,
            );
        }
        terms.push(multiply_mod(interval_degree as u64, fibre_sum, modulus));
    }
    Ok(terms)
}

fn character_mobius_coefficients_through_residue(
    ell: usize,
    target: usize,
    modulus: u64,
) -> Result<CharacterMobiusTable, HayesError> {
    let factors = principal_unit_factors(ell);
    let odd_degrees = factors
        .iter()
        .map(|factor| factor.odd_degree)
        .collect::<Vec<_>>();
    let dimensions = factors
        .iter()
        .map(|factor| factor.order)
        .collect::<Vec<_>>();
    let size = 1_usize << ell;
    let mut unit_to_index = BTreeMap::new();
    for index in 0..size {
        let mut quotient = index;
        let mut value = 1_u64;
        for (&odd, &dimension) in odd_degrees.iter().zip(&dimensions) {
            let exponent = quotient % dimension;
            quotient /= dimension;
            let generator = 1 | (1_u64 << odd);
            for _ in 0..exponent {
                value = unit_multiply(value, generator, ell);
            }
        }
        if unit_to_index.insert(value, index).is_some() {
            return Err(HayesError::Invariant(format!(
                "ell={ell}: principal-unit decomposition is not injective"
            )));
        }
    }
    if unit_to_index.len() != size {
        return Err(HayesError::Invariant(format!(
            "ell={ell}: principal-unit decomposition is incomplete"
        )));
    }

    let mut class_sums = vec![vec![0_u64; size]; ell];
    class_sums[0][0] = 1;
    group_transform(&mut class_sums[0], &dimensions, modulus);
    for (degree, class_sum) in class_sums.iter_mut().enumerate().skip(1) {
        for tail in 0..(1_u64 << degree) {
            let unit = 1 | (tail << 1);
            class_sum[unit_to_index[&unit]] = 1;
        }
        group_transform(class_sum, &dimensions, modulus);
    }
    let powers_of_two = (0..=target)
        .map(|degree| mod_pow(2, degree as u64, modulus))
        .collect::<Vec<_>>();

    let mut mobius = vec![vec![0_u64; size]; target + 1];
    mobius[0].fill(1);
    for degree in 1..=target {
        for character in 0..size {
            let mut value = 0_u64;
            for class_degree in 1..=degree {
                let class_sum = if class_degree < ell {
                    class_sums[class_degree][character]
                } else if character == 0 {
                    powers_of_two[class_degree]
                } else {
                    0
                };
                value = subtract_mod(
                    value,
                    multiply_mod(class_sum, mobius[degree - class_degree][character], modulus),
                    modulus,
                );
            }
            mobius[degree][character] = value;
        }
    }
    Ok(CharacterMobiusTable {
        rows: mobius,
        dimensions,
        unit_to_index,
    })
}

fn principal_unit_inverse(unit: u64, ell: usize) -> u64 {
    let mut inverse = 1_u64;
    for degree in 1..=ell {
        let coefficient = (1..=degree).fold(0_u64, |parity, left| {
            parity ^ (((unit >> left) & 1) & ((inverse >> (degree - left)) & 1))
        });
        inverse |= coefficient << degree;
    }
    inverse
}

fn invert_group_coordinates(values: &mut [u64], dimensions: &[usize]) -> Result<(), HayesError> {
    let mut inverted = vec![0_u64; values.len()];
    for (index, value) in values.iter().enumerate() {
        let mut quotient = index;
        let mut inverse_index = 0;
        let mut stride = 1;
        for &dimension in dimensions {
            let coordinate = quotient % dimension;
            quotient /= dimension;
            let inverse_coordinate = if coordinate == 0 {
                0
            } else {
                dimension - coordinate
            };
            inverse_index += inverse_coordinate * stride;
            stride = stride.checked_mul(dimension).ok_or_else(|| {
                HayesError::Invariant("group-coordinate stride overflow".to_owned())
            })?;
        }
        if quotient != 0 || inverse_index >= values.len() {
            return Err(HayesError::Invariant(
                "group-coordinate inversion escaped the transform domain".to_owned(),
            ));
        }
        inverted[inverse_index] = *value;
    }
    values.copy_from_slice(&inverted);
    Ok(())
}

fn character_power_sums_residue(
    ell: usize,
    target: usize,
    modulus: u64,
) -> Result<(Vec<u64>, Vec<usize>), HayesError> {
    let factors = principal_unit_factors(ell);
    let odd_degrees = factors
        .iter()
        .map(|factor| factor.odd_degree)
        .collect::<Vec<_>>();
    let dimensions = factors
        .iter()
        .map(|factor| factor.order)
        .collect::<Vec<_>>();
    let size = 1_usize << ell;
    let mut unit_to_index = vec![usize::MAX; size];
    for index in 0..size {
        let mut quotient = index;
        let mut value = 1_u64;
        for (&odd, &dimension) in odd_degrees.iter().zip(&dimensions) {
            let exponent = quotient % dimension;
            quotient /= dimension;
            let generator = 1 | (1_u64 << odd);
            for _ in 0..exponent {
                value = unit_multiply(value, generator, ell);
            }
        }
        let packed = (value >> 1) as usize;
        if packed >= size || unit_to_index[packed] != usize::MAX {
            return Err(HayesError::Invariant(format!(
                "ell={ell}: principal-unit decomposition is not injective"
            )));
        }
        unit_to_index[packed] = index;
    }
    if unit_to_index.contains(&usize::MAX) {
        return Err(HayesError::Invariant(format!(
            "ell={ell}: principal-unit decomposition is incomplete"
        )));
    }

    let mut class_sums = vec![vec![0_u64; size]; ell];
    class_sums[0][0] = 1;
    group_transform(&mut class_sums[0], &dimensions, modulus);
    for (degree, class_sum) in class_sums.iter_mut().enumerate().skip(1) {
        for tail in 0..(1_u64 << degree) {
            let unit = 1 | (tail << 1);
            class_sum[unit_to_index[(unit >> 1) as usize]] = 1;
        }
        group_transform(class_sum, &dimensions, modulus);
    }
    let powers_of_two = (0..=target)
        .map(|degree| mod_pow(2, degree as u64, modulus))
        .collect::<Vec<_>>();

    // For a nontrivial character, A_d(chi)=0 once d>=ell.  Thus the
    // logarithmic-derivative recurrence needs only the preceding ell-1 rows.
    // Process deterministic character blocks so that this circular history
    // is `ell * block_width`, rather than `ell * 2^ell`, cells.  Every
    // character recurrence is independent after the group transforms, so
    // blocking changes neither arithmetic nor output order.
    //
    // The trivial character is the closed series 1/(1-2z), whose power sum
    // is exactly 2^degree and therefore needs no recurrence history.
    let mut target_values = vec![0_u64; size];
    target_values[0] = powers_of_two[target];
    for block_start in (1..size).step_by(POWER_SUM_CHARACTER_BLOCK) {
        let block_end = block_start
            .saturating_add(POWER_SUM_CHARACTER_BLOCK)
            .min(size);
        let block_width = block_end - block_start;
        let history_cells = ell.checked_mul(block_width).ok_or_else(|| {
            HayesError::InvalidParameter("Hayes power-sum block size overflow".to_owned())
        })?;
        let mut mangoldt = vec![0_u64; history_cells];
        for degree in 1..=target {
            let row = degree % ell;
            for (offset, character) in (block_start..block_end).enumerate() {
                let mut value = if degree < ell {
                    multiply_mod(
                        degree as u64 % modulus,
                        class_sums[degree][character],
                        modulus,
                    )
                } else {
                    0
                };
                for (class_degree, class_sum) in
                    class_sums.iter().enumerate().take(degree.min(ell)).skip(1)
                {
                    let earlier = degree - class_degree;
                    if earlier == 0 {
                        continue;
                    }
                    let correction = multiply_mod(
                        mangoldt[(earlier % ell) * block_width + offset],
                        class_sum[character],
                        modulus,
                    );
                    value = subtract_mod(value, correction, modulus);
                }
                mangoldt[row * block_width + offset] = value;
            }
        }
        let target_row = (target % ell) * block_width;
        target_values[block_start..block_end]
            .copy_from_slice(&mangoldt[target_row..target_row + block_width]);
    }
    Ok((target_values, dimensions))
}

fn exact_conductor_energy_residue(
    level: usize,
    degree: usize,
    modulus: u64,
) -> Result<u64, HayesError> {
    let (current, current_dimensions) = character_power_sums_residue(level, degree, modulus)?;
    let (previous, previous_dimensions) = character_power_sums_residue(level - 1, degree, modulus)?;
    let current_energy = fourier_energy_residue(&current, &current_dimensions, modulus)?;
    let previous_energy = fourier_energy_residue(&previous, &previous_dimensions, modulus)?;
    Ok(subtract_mod(current_energy, previous_energy, modulus))
}

fn fourier_energy_residue(
    values: &[u64],
    dimensions: &[usize],
    modulus: u64,
) -> Result<u64, HayesError> {
    let expected = dimensions.iter().try_fold(1_usize, |product, dimension| {
        product.checked_mul(*dimension)
    });
    if expected != Some(values.len()) {
        return Err(HayesError::Invariant(
            "Fourier dimensions do not recover the character table size".to_owned(),
        ));
    }
    let mut energy = 0_u64;
    for (index, value) in values.iter().enumerate() {
        let mut quotient = index;
        let mut inverse_index = 0_usize;
        let mut stride = 1_usize;
        for dimension in dimensions {
            let coordinate = quotient % dimension;
            quotient /= dimension;
            let inverse_coordinate = if coordinate == 0 {
                0
            } else {
                dimension - coordinate
            };
            inverse_index += inverse_coordinate * stride;
            stride *= dimension;
        }
        energy = add_mod(
            energy,
            multiply_mod(*value, values[inverse_index], modulus),
            modulus,
        );
    }
    Ok(energy)
}

fn unit_multiply(mut left: u64, right: u64, ell: usize) -> u64 {
    let mut product = 0_u64;
    while left != 0 {
        let degree = left.trailing_zeros() as usize;
        left &= left - 1;
        product ^= right << degree;
    }
    let mask = if ell == 63 {
        u64::MAX
    } else {
        (1_u64 << (ell + 1)) - 1
    };
    product & mask
}

fn polynomial_multiply_packed(mut left: u64, right: u64) -> u64 {
    let mut product = 0_u64;
    while left != 0 {
        let degree = left.trailing_zeros();
        left &= left - 1;
        product ^= right << degree;
    }
    product
}

fn polynomial_remainder_packed(mut dividend: u64, divisor: u64) -> u64 {
    debug_assert_ne!(divisor, 0);
    let divisor_degree = divisor.ilog2();
    while dividend != 0 {
        let dividend_degree = dividend.ilog2();
        if dividend_degree < divisor_degree {
            break;
        }
        dividend ^= divisor << (dividend_degree - divisor_degree);
    }
    dividend
}

fn polynomial_gcd_packed(mut left: u64, mut right: u64) -> u64 {
    while right != 0 {
        let remainder = polynomial_remainder_packed(left, right);
        left = right;
        right = remainder;
    }
    left
}

fn polynomial_exact_divide_packed(mut dividend: u64, divisor: u64) -> Result<u64, HayesError> {
    if divisor == 0 {
        return Err(HayesError::Invariant(
            "binary polynomial exact division by zero".to_owned(),
        ));
    }
    let divisor_degree = divisor.ilog2();
    let mut quotient = 0_u64;
    while dividend != 0 {
        let dividend_degree = dividend.ilog2();
        if dividend_degree < divisor_degree {
            break;
        }
        let shift = dividend_degree - divisor_degree;
        quotient |= 1_u64 << shift;
        dividend ^= divisor << shift;
    }
    if dividend != 0 {
        return Err(HayesError::Invariant(
            "binary polynomial division left a nonzero remainder".to_owned(),
        ));
    }
    Ok(quotient)
}

fn group_transform(values: &mut [u64], dimensions: &[usize], modulus: u64) {
    let mut stride = 1;
    for &dimension in dimensions {
        let mut line = vec![0_u64; dimension];
        for base in (0..values.len()).step_by(stride * dimension) {
            for offset in 0..stride {
                for index in 0..dimension {
                    line[index] = values[base + offset + index * stride];
                }
                ntt(&mut line, modulus);
                for index in 0..dimension {
                    values[base + offset + index * stride] = line[index];
                }
            }
        }
        stride *= dimension;
    }
}

fn ntt(values: &mut [u64], modulus: u64) {
    let length = values.len();
    let mut target = 0;
    for index in 1..length {
        let mut bit = length >> 1;
        while target & bit != 0 {
            target ^= bit;
            bit >>= 1;
        }
        target ^= bit;
        if index < target {
            values.swap(index, target);
        }
    }
    let mut width = 2;
    while width <= length {
        let root = mod_pow(PRIMITIVE_ROOT, (modulus - 1) / width as u64, modulus);
        for start in (0..length).step_by(width) {
            let mut power = 1;
            for offset in 0..width / 2 {
                let left = values[start + offset];
                let right = multiply_mod(values[start + offset + width / 2], power, modulus);
                values[start + offset] = add_mod(left, right, modulus);
                values[start + offset + width / 2] = subtract_mod(left, right, modulus);
                power = multiply_mod(power, root, modulus);
            }
        }
        width *= 2;
    }
}

fn crt(
    first: u64,
    first_modulus: u64,
    second: u64,
    second_modulus: u64,
) -> Result<u128, HayesError> {
    let delta = subtract_mod(second, first % second_modulus, second_modulus);
    let inverse = mod_pow(
        first_modulus % second_modulus,
        second_modulus - 2,
        second_modulus,
    );
    let multiplier = multiply_mod(delta, inverse, second_modulus);
    let recovered = u128::from(first) + u128::from(first_modulus) * u128::from(multiplier);
    if recovered % u128::from(first_modulus) != u128::from(first)
        || recovered % u128::from(second_modulus) != u128::from(second)
    {
        return Err(HayesError::Invariant(
            "CRT reconstruction failed its residue check".to_owned(),
        ));
    }
    Ok(recovered)
}

fn mod_pow(mut base: u64, mut exponent: u64, modulus: u64) -> u64 {
    let mut result = 1_u64;
    while exponent != 0 {
        if exponent & 1 != 0 {
            result = multiply_mod(result, base, modulus);
        }
        base = multiply_mod(base, base, modulus);
        exponent >>= 1;
    }
    result
}

fn multiply_mod(left: u64, right: u64, modulus: u64) -> u64 {
    match u64::try_from((u128::from(left) * u128::from(right)) % u128::from(modulus)) {
        Ok(value) => value,
        Err(_) => unreachable!("a remainder modulo u64 must fit u64"),
    }
}

fn checked_walsh_transform(values: &mut [i128]) -> Result<(), HayesError> {
    if !values.len().is_power_of_two() {
        return Err(HayesError::Invariant(
            "Walsh transform length is not a power of two".to_owned(),
        ));
    }
    let mut width = 1;
    while width < values.len() {
        for start in (0..values.len()).step_by(width * 2) {
            for offset in 0..width {
                let left = values[start + offset];
                let right = values[start + width + offset];
                values[start + offset] = left.checked_add(right).ok_or_else(|| {
                    HayesError::InvalidParameter("Walsh sum exceeds i128".to_owned())
                })?;
                values[start + width + offset] = left.checked_sub(right).ok_or_else(|| {
                    HayesError::InvalidParameter("Walsh difference exceeds i128".to_owned())
                })?;
            }
        }
        width = width.checked_mul(2).ok_or_else(|| {
            HayesError::InvalidParameter("Walsh transform width overflow".to_owned())
        })?;
    }
    Ok(())
}

fn add_mod(left: u64, right: u64, modulus: u64) -> u64 {
    let sum = left + right;
    if sum >= modulus { sum - modulus } else { sum }
}

fn subtract_mod(left: u64, right: u64, modulus: u64) -> u64 {
    if left >= right {
        left - right
    } else {
        left + modulus - right
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn principal_unit_index_map(ell: usize) -> BTreeMap<u64, usize> {
        let factors = principal_unit_factors(ell);
        let mut map = BTreeMap::new();
        for index in 0..1_usize << ell {
            let mut quotient = index;
            let mut unit = 1_u64;
            for factor in &factors {
                let exponent = quotient % factor.order;
                quotient /= factor.order;
                let generator = 1 | (1_u64 << factor.odd_degree);
                for _ in 0..exponent {
                    unit = unit_multiply(unit, generator, ell);
                }
            }
            assert_eq!(quotient, 0);
            assert!(map.insert(unit, index).is_none());
        }
        map
    }

    fn unit_inverse(unit: u64, ell: usize) -> u64 {
        let mut inverse = 1_u64;
        for degree in 1..=ell {
            let coefficient = (1..=degree).fold(0_u64, |parity, left| {
                parity ^ (((unit >> left) & 1) & ((inverse >> (degree - left)) & 1))
            });
            inverse |= coefficient << degree;
        }
        inverse
    }

    fn direct_class_mobius_distribution(ell: usize, degree: usize) -> Vec<i128> {
        let unit_to_index = principal_unit_index_map(ell);
        let mut direct = vec![0_i128; 1_usize << ell];
        for lower in 0_u64..1_u64 << degree {
            let polynomial = (1_u64 << degree) | lower;
            let coefficients = (0..=degree)
                .map(|index| i128::from((polynomial >> index) & 1))
                .collect::<Vec<_>>();
            let factors = crate::gfp::factor_berlekamp(&coefficients, 2).unwrap();
            let mobius = if factors.iter().any(|(_, multiplicity)| *multiplicity != 1) {
                0
            } else if factors.len().is_multiple_of(2) {
                1
            } else {
                -1
            };
            let mut unit = 1_u64;
            for prefix_degree in 1..=ell.min(degree) {
                if polynomial >> (degree - prefix_degree) & 1 != 0 {
                    unit |= 1_u64 << prefix_degree;
                }
            }
            direct[unit_to_index[&unit]] += mobius;
        }
        direct
    }

    fn direct_unit_polynomial_inverse_spectrum(ell: usize, degree: usize) -> Vec<i128> {
        let mut spectrum = vec![0_i128; 1_usize << ell];
        for middle in 0_u64..1_u64 << degree.saturating_sub(1) {
            let polynomial = (1_u64 << degree) | (middle << 1) | 1;
            let coefficients = (0..=degree)
                .map(|index| i128::from((polynomial >> index) & 1))
                .collect::<Vec<_>>();
            let factors = crate::gfp::factor_berlekamp(&coefficients, 2).unwrap();
            let mobius = if factors.iter().any(|(_, multiplicity)| *multiplicity != 1) {
                0
            } else if factors.len().is_multiple_of(2) {
                1
            } else {
                -1
            };
            let mask = (1_u64 << (ell + 1)) - 1;
            let residue = polynomial & mask;
            let packed_inverse = principal_unit_inverse(residue, ell) >> 1;
            for (frequency, coefficient) in spectrum.iter_mut().enumerate() {
                let parity = (packed_inverse & frequency as u64).count_ones() % 2;
                let sign = if parity == 0 { 1 } else { -1 };
                *coefficient += sign * mobius;
            }
        }
        spectrum
    }

    const EXPECTED: &[(i128, i128)] = &[
        (0, 0),
        (-2, 0),
        (6, -8),
        (5, 12),
        (-19, 32),
        (-49, 32),
        (45, -40),
        (50, 75),
    ];

    #[test]
    fn endpoint_controls_are_exact() {
        let limits = HayesLimits::default();
        for (index, &(odd, even)) in EXPECTED.iter().enumerate() {
            assert_eq!(
                endpoint_discrepancies(index + 1, limits),
                Ok(EndpointDiscrepancies {
                    ell: index + 1,
                    odd,
                    even,
                })
            );
        }
    }

    #[test]
    fn principal_unit_structure_recovers_order() {
        let structure = principal_unit_structure(8, HayesLimits::default()).unwrap();
        assert_eq!(structure.group_order, 256);
        assert_eq!(
            structure.factors,
            vec![
                PrincipalUnitFactor {
                    odd_degree: 1,
                    order: 16,
                },
                PrincipalUnitFactor {
                    odd_degree: 3,
                    order: 4,
                },
                PrincipalUnitFactor {
                    odd_degree: 5,
                    order: 2,
                },
                PrincipalUnitFactor {
                    odd_degree: 7,
                    order: 2,
                },
            ]
        );
    }

    #[test]
    fn principal_unit_kloosterman_bound_matches_direct_sums_and_products() {
        let limits = HayesLimits::default();
        for ell in 2..=9 {
            let report = principal_unit_kloosterman_bound(ell, limits).unwrap();
            let direct_kloosterman_max = (0..(1_u64 << ell))
                .map(|frequency| {
                    (0..(1_u64 << ell))
                        .map(|tail| {
                            let unit = 1 | (tail << 1);
                            let phase = (unit_inverse(unit, ell)
                                ^ unit_multiply(frequency, unit, ell))
                                >> ell
                                & 1;
                            if phase == 0 { 1_i64 } else { -1_i64 }
                        })
                        .sum::<i64>()
                        .unsigned_abs()
                })
                .max()
                .unwrap();
            assert!(BigUint::from(direct_kloosterman_max) <= report.max_abs_kloosterman_sum);

            let mut products = BTreeMap::<u64, u64>::new();
            for left_tail in 0..(1_u64 << (ell - 1)) {
                let left = 1 | (left_tail << 1);
                for right_tail in 0..(1_u64 << (ell - 1)) {
                    let right = 1 | (right_tail << 1);
                    *products.entry(unit_multiply(left, right, ell)).or_default() += 1;
                }
            }
            let mean = 1_u64 << (ell - 2);
            let direct_deviation_max = (0..(1_u64 << ell))
                .map(|tail| {
                    products
                        .get(&(1 | (tail << 1)))
                        .copied()
                        .unwrap_or(0)
                        .abs_diff(mean)
                })
                .max()
                .unwrap();
            assert!(BigUint::from(direct_deviation_max) <= report.max_abs_top_product_deviation);
        }

        let level_three = principal_unit_kloosterman_bound(3, limits).unwrap();
        assert_eq!(level_three.max_abs_kloosterman_sum, BigUint::from(8_u8));
        assert_eq!(level_three.max_contributing_cosets, BigUint::from(2_u8));
        assert_eq!(
            level_three.max_abs_top_product_deviation,
            BigUint::from(2_u8)
        );
        let modulus_x_four_frequency_one_plus_x_squared = (0..8_u64)
            .map(|tail| {
                let unit = 1 | (tail << 1);
                let phase = (unit_inverse(unit, 3) ^ unit_multiply(0b0101, unit, 3)) >> 3 & 1;
                if phase == 0 { 1_i64 } else { -1_i64 }
            })
            .sum::<i64>();
        assert_eq!(modulus_x_four_frequency_one_plus_x_squared, 8);
    }

    #[test]
    fn principal_unit_kloosterman_bound_declines_invalid_or_limited_inputs() {
        let limits = HayesLimits::default();
        assert!(matches!(
            principal_unit_kloosterman_bound(1, limits),
            Err(HayesError::InvalidParameter(_))
        ));
        let limited = HayesLimits {
            max_ell: 4,
            ..limits
        };
        assert!(matches!(
            principal_unit_kloosterman_bound(5, limited),
            Err(HayesError::ResourceLimit {
                resource: "ell",
                requested: 5,
                limit: 4
            })
        ));
    }

    #[test]
    fn principal_unit_mixed_product_energy_matches_direct_collisions() {
        let limits = HayesLimits::default();
        for ell in 2..=8 {
            for left_degree in 1..ell {
                for right_degree in 1..ell {
                    let report =
                        principal_unit_mixed_product_energy(ell, left_degree, right_degree, limits)
                            .unwrap();
                    let mut products = BTreeMap::<u64, u128>::new();
                    for left_tail in 0..(1_u64 << left_degree) {
                        let left = 1 | (left_tail << 1);
                        for right_tail in 0..(1_u64 << right_degree) {
                            let right = 1 | (right_tail << 1);
                            *products.entry(unit_multiply(left, right, ell)).or_default() += 1;
                        }
                    }
                    let direct = products
                        .values()
                        .map(|multiplicity| multiplicity * multiplicity)
                        .sum::<u128>();
                    assert_eq!(report.pair_product_energy, BigUint::from(direct));
                    assert_eq!(report.left_set_size, BigUint::from(1_u8) << left_degree);
                    assert_eq!(report.right_set_size, BigUint::from(1_u8) << right_degree);
                    assert_eq!(
                        report.ordered_pair_count,
                        BigUint::from(1_u8) << (left_degree + right_degree)
                    );
                    assert_eq!(
                        report.ordinary_product_regime,
                        left_degree + right_degree <= ell
                    );
                }
            }
        }

        let ordinary = principal_unit_mixed_product_energy(14, 4, 7, limits).unwrap();
        assert_eq!(ordinary.pair_product_energy, BigUint::from(6_144_u32));
        let projected = principal_unit_mixed_product_energy(14, 6, 9, limits).unwrap();
        assert_eq!(projected.pair_product_energy, BigUint::from(147_456_u32));
        assert_eq!(
            projected.centered_fourier_mixed_moment_numerator,
            BigUint::from(1_342_177_280_u64)
        );
        assert_eq!(
            projected,
            principal_unit_mixed_product_energy(14, 9, 6, limits)
                .map(|mut swapped| {
                    std::mem::swap(&mut swapped.left_degree, &mut swapped.right_degree);
                    std::mem::swap(&mut swapped.left_set_size, &mut swapped.right_set_size);
                    swapped
                })
                .unwrap()
        );
    }

    #[test]
    fn principal_unit_inverse_additive_energy_matches_direct_collisions() {
        let limits = HayesLimits::default();
        for ell in 2_usize..=9 {
            for degree in 1_usize..ell {
                let report = principal_unit_inverse_additive_energy(ell, degree, limits).unwrap();
                let inverses = (0..1_u64 << degree)
                    .map(|tail| principal_unit_inverse(1 | (tail << 1), ell) >> 1)
                    .collect::<Vec<_>>();
                let mut pair_sums = vec![0_u128; 1_usize << ell];
                for left in &inverses {
                    for right in &inverses {
                        pair_sums[usize::try_from(left ^ right).unwrap()] += 1;
                    }
                }
                let direct = pair_sums
                    .into_iter()
                    .map(|multiplicity| multiplicity * multiplicity)
                    .sum::<u128>();
                assert_eq!(report.additive_energy, BigUint::from(direct));
                assert_eq!(report.polynomial_degree_cutoff, degree + 1);
                assert_eq!(
                    report.fourth_walsh_moment,
                    (BigUint::from(1_u8) << ell) * &report.additive_energy
                );
            }
        }

        let row = (1_usize..8)
            .map(|degree| {
                principal_unit_inverse_additive_energy(8, degree, limits)
                    .unwrap()
                    .additive_energy
            })
            .collect::<Vec<_>>();
        assert_eq!(
            row,
            [8_u64, 40, 176, 928, 7_424, 77_824, 1_114_112]
                .into_iter()
                .map(BigUint::from)
                .collect::<Vec<_>>()
        );
        assert_ne!(
            principal_unit_inverse_additive_energy(8, 4, limits)
                .unwrap()
                .additive_energy,
            principal_unit_product_energy(8, 4, limits)
                .unwrap()
                .pair_product_energy
        );
    }

    #[test]
    fn inverse_additive_energy_stabilizes_when_the_modulus_cannot_wrap() {
        let limits = HayesLimits::default();
        let expected = [8_u64, 40, 176, 760, 3_128, 12_520];
        for (offset, expected_energy) in expected.into_iter().enumerate() {
            let degree = offset + 1;
            let stable = principal_unit_inverse_additive_energy_no_wrap(degree, limits).unwrap();
            assert_eq!(stable.minimum_stable_ell, 3 * degree);
            assert_eq!(
                stable.ordered_pair_count,
                BigUint::from(1_u8) << (2 * degree)
            );
            assert_eq!(stable.additive_energy, BigUint::from(expected_energy));
            for ell in [3 * degree, 3 * degree + 1] {
                let modular = principal_unit_inverse_additive_energy(ell, degree, limits).unwrap();
                assert_eq!(modular.additive_energy, stable.additive_energy);
            }
        }

        // Below the proved threshold the congruence can identify fractions
        // whose cross-products differ by a nonzero multiple of x^(ell+1).
        let wrapped = principal_unit_inverse_additive_energy(8, 4, limits).unwrap();
        let stable = principal_unit_inverse_additive_energy_no_wrap(4, limits).unwrap();
        assert_eq!(wrapped.additive_energy, BigUint::from(928_u16));
        assert_eq!(stable.additive_energy, BigUint::from(760_u16));
    }

    #[test]
    fn no_wrap_fraction_reduction_is_canonical_and_bounded() {
        let limits = HayesLimits::default();
        let report = principal_unit_inverse_additive_energy_no_wrap(3, limits).unwrap();
        assert_eq!(report.reduced_fraction_count, 29);
        assert_eq!(report.maximum_fraction_multiplicity, 8);
        assert!(matches!(
            principal_unit_inverse_additive_energy_no_wrap(0, limits),
            Err(HayesError::InvalidParameter(_))
        ));
        assert_eq!(
            principal_unit_inverse_additive_energy_no_wrap(
                4,
                HayesLimits {
                    max_table_cells: 255,
                    ..limits
                }
            ),
            Err(HayesError::ResourceLimit {
                resource: "table_cells",
                requested: 256,
                limit: 255,
            })
        );
    }

    #[test]
    fn no_wrap_divisor_bound_dominates_exact_collision_classes() {
        let limits = HayesLimits::default();
        for degree in 1..=7 {
            let exact = principal_unit_inverse_additive_energy_no_wrap(degree, limits).unwrap();
            let bound =
                principal_unit_inverse_additive_energy_no_wrap_bound(degree, limits).unwrap();
            assert_eq!(bound.minimum_stable_ell, 3 * degree);
            assert!(
                BigUint::from(exact.maximum_fraction_multiplicity)
                    <= bound.maximum_multiplicity_bound
            );
            assert!(exact.additive_energy <= bound.additive_energy_bound);
        }
        assert!(matches!(
            principal_unit_inverse_additive_energy_no_wrap_bound(0, limits),
            Err(HayesError::InvalidParameter(_))
        ));
        assert_eq!(
            principal_unit_inverse_additive_energy_no_wrap_bound(
                4,
                HayesLimits {
                    max_degree: 3,
                    ..limits
                }
            ),
            Err(HayesError::ResourceLimit {
                resource: "degree",
                requested: 4,
                limit: 3,
            })
        );
    }

    #[test]
    fn wrapped_binary_inverse_energy_envelope_dominates_exact_tables() {
        let limits = HayesLimits::default();
        for modulus_degree in 3..=9 {
            for cutoff in 2..modulus_degree {
                let bound = binary_prime_power_inverse_additive_energy_bound(
                    modulus_degree,
                    cutoff,
                    limits,
                )
                .unwrap();
                let exact =
                    principal_unit_inverse_additive_energy(modulus_degree - 1, cutoff - 1, limits)
                        .unwrap();
                assert!(exact.additive_energy <= bound.additive_energy_bound);
                let non_diagonal_pairs = &bound.set_size * (&bound.set_size - 1_u8);
                let stratified_pairs = bound
                    .strata
                    .iter()
                    .fold(BigUint::from(0_u8), |sum, stratum| {
                        sum + &stratum.ordered_pair_count
                    });
                assert_eq!(stratified_pairs, non_diagonal_pairs);
            }
        }

        // The wrapped theorem includes the exact boundary excluded by the
        // no-wrap condition: 3m=r in modulus-degree notation.
        let boundary = binary_prime_power_inverse_additive_energy_bound(9, 3, limits).unwrap();
        let boundary_exact = principal_unit_inverse_additive_energy(8, 2, limits).unwrap();
        assert!(boundary_exact.additive_energy <= boundary.additive_energy_bound);

        let full_units = binary_prime_power_inverse_additive_energy_bound(6, 6, limits).unwrap();
        assert_eq!(full_units.strata.len(), 5);
        assert!(matches!(
            binary_prime_power_inverse_additive_energy_bound(5, 6, limits),
            Err(HayesError::InvalidParameter(_))
        ));
        assert!(matches!(
            binary_prime_power_inverse_additive_energy_bound(
                5,
                5,
                HayesLimits {
                    max_table_cells: 1,
                    ..limits
                }
            ),
            Err(HayesError::ResourceLimit {
                resource: "table_cells",
                ..
            })
        ));
    }

    #[test]
    fn exact_binary_divisor_envelope_matches_direct_factorization() {
        let mut direct_maximum = BigUint::from(1_u8);
        assert_eq!(
            binary_polynomial_divisor_envelope(0).unwrap(),
            direct_maximum
        );
        for degree in 1_usize..=10 {
            for lower in 0_u64..1_u64 << degree {
                let polynomial = (1_u64 << degree) | lower;
                let coefficients = (0..=degree)
                    .map(|index| i128::from((polynomial >> index) & 1))
                    .collect::<Vec<_>>();
                let factors = crate::gfp::factor_berlekamp(&coefficients, 2).unwrap();
                let divisors = factors.iter().fold(BigUint::from(1_u8), |product, term| {
                    product * BigUint::from(term.1 + 1)
                });
                direct_maximum = direct_maximum.max(divisors);
            }
            assert_eq!(
                binary_polynomial_divisor_envelope(degree).unwrap(),
                direct_maximum,
                "degree={degree}"
            );
        }
    }

    #[test]
    fn bilinear_energy_ledger_exposes_the_exact_type_two_margin() {
        // This first report deliberately checks a caller-supplied idealized
        // energy exponent.  The strict no-wrap modulus condition is r>3d,
        // so r=301 is the first valid modulus degree for d=100.
        let saving = binary_bilinear_energy_exponent(100, 100, 301, 200, 200, 1, 200).unwrap();
        assert_eq!(saving.bound_exponent_numerator, 1_501);
        assert_eq!(saving.target_exponent_numerator, 1_600);
        assert_eq!(saving.deficit_numerator, 99);
        assert!(saving.strict_saving);

        // At total interval size r/2, the same energy scale merely reaches
        // the trivial exponent and supplies no strict saving.
        let boundary = binary_bilinear_energy_exponent(100, 100, 400, 200, 200, 1, 200).unwrap();
        assert_eq!(boundary.bound_exponent_numerator, 1_600);
        assert_eq!(boundary.deficit_numerator, 0);
        assert!(!boundary.strict_saving);

        assert!(matches!(
            binary_bilinear_energy_exponent(1, 1, 3, 2, 2, 0, 2),
            Err(HayesError::InvalidParameter(_))
        ));
    }

    #[test]
    fn explicit_bilinear_ledger_carries_divisor_envelope_and_loss_reserve() {
        let limits = HayesLimits::default();
        let explicit =
            binary_bilinear_explicit_prime_power_energy_exponent(2, 2, 9, 0, 1, 4, limits).unwrap();
        let energy = binary_prime_power_inverse_additive_energy_bound(9, 3, limits).unwrap();
        assert_eq!(
            explicit.left_energy_ceiling_exponent,
            energy.ceiling_energy_exponent().unwrap()
        );
        assert_eq!(
            explicit.right_energy_ceiling_exponent,
            energy.ceiling_energy_exponent().unwrap()
        );
        assert!(!explicit.strict_saving);

        let reserved =
            binary_bilinear_explicit_prime_power_energy_exponent(2, 2, 9, 1, 2, 4, limits).unwrap();
        assert_eq!(
            reserved.bound_exponent_numerator,
            2 * explicit.bound_exponent_numerator + 8
        );
        assert_eq!(
            reserved.target_exponent_numerator,
            2 * explicit.target_exponent_numerator
        );
        assert!(reserved.deficit_numerator < explicit.deficit_numerator);
        assert!(matches!(
            binary_bilinear_explicit_prime_power_energy_exponent(2, 2, 9, 0, 0, 4, limits),
            Err(HayesError::InvalidParameter(_))
        ));
    }

    #[test]
    fn principal_unit_inverse_additive_energy_declines_invalid_inputs() {
        let limits = HayesLimits::default();
        for degree in [0, 4] {
            assert!(matches!(
                principal_unit_inverse_additive_energy(4, degree, limits),
                Err(HayesError::InvalidParameter(_))
            ));
        }
        assert_eq!(
            principal_unit_inverse_additive_energy(
                8,
                4,
                HayesLimits {
                    max_group_order: 128,
                    ..limits
                }
            ),
            Err(HayesError::ResourceLimit {
                resource: "group_order",
                requested: 256,
                limit: 128,
            })
        );
    }

    #[test]
    fn binary_type_one_case_one_ledger_replays_range_and_saving() {
        let report = binary_type_one_case_one_exponent(601, 301).unwrap();
        assert_eq!(report.maximum_admissible_u, 200);
        assert_eq!(report.complete_kloosterman_exponent, 201);
        assert_eq!(report.bound_exponent, 501);
        assert_eq!(report.trivial_exponent, 601);
        assert_eq!(report.deficit, 100);
        assert!(report.strict_saving);

        let one = binary_type_one_case_one_exponent(1, 1).unwrap();
        assert_eq!(one.maximum_admissible_u, 0);
        assert_eq!(one.deficit, 0);
        assert!(!one.strict_saving);
        assert!(matches!(
            binary_type_one_case_one_exponent(300, 301),
            Err(HayesError::InvalidParameter(_))
        ));
    }

    #[test]
    fn binary_type_one_case_two_ledger_optimizes_every_integer_endpoint() {
        let balanced = binary_type_one_case_two_exponent(300, 300).unwrap();
        assert_eq!(balanced.minimum_admissible_u, 0);
        assert_eq!(balanced.maximum_admissible_u, 100);
        assert_eq!(balanced.worst_admissible_u, 80);
        assert_eq!(balanced.complete_kloosterman_exponent, 200);
        assert_eq!(balanced.energy_bound_quarters, 1_120);
        assert_eq!(balanced.completion_bound_quarters, 1_120);
        assert_eq!(balanced.bound_exponent_quarters, 1_120);
        assert_eq!(balanced.deficit_quarters, 80);
        assert!(balanced.strict_saving);

        // Here the two formal lines meet beyond the Case-2 interval, so the
        // exact maximum is attained at its upper endpoint.
        let clipped = binary_type_one_case_two_exponent(350, 300).unwrap();
        assert_eq!(clipped.minimum_admissible_u, 50);
        assert_eq!(clipped.maximum_admissible_u, 100);
        assert_eq!(clipped.worst_admissible_u, 100);
        assert_eq!(clipped.energy_bound_quarters, 1_250);
        assert_eq!(clipped.completion_bound_quarters, 1_200);
        assert_eq!(clipped.bound_exponent_quarters, 1_200);
        assert_eq!(clipped.deficit_quarters, 200);

        // Independently enumerate all small integer ranges.  This pins the
        // floor/ceiling choices around the intersection and both endpoints.
        for r0 in 1..=40 {
            let kappa = binary_complete_kloosterman_exponent(r0).unwrap();
            for cutoff in 1..=2 * r0 {
                let lower = cutoff.saturating_sub(r0);
                let upper_from_y = cutoff.checked_sub(r0.div_ceil(3));
                let upper = upper_from_y.map(|value| (r0 / 3).min(value));
                let expected = upper.filter(|value| lower <= *value).map(|upper| {
                    (lower..=upper)
                        .map(|u| {
                            let energy = 3 * cutoff + r0 - u;
                            let completion = 4 * (u + kappa);
                            (u, energy.min(completion))
                        })
                        .max_by(|left, right| {
                            left.1.cmp(&right.1).then_with(|| right.0.cmp(&left.0))
                        })
                        .unwrap()
                });
                match (binary_type_one_case_two_exponent(cutoff, r0), expected) {
                    (Ok(report), Some((u, bound))) => {
                        assert_eq!(report.worst_admissible_u, u);
                        assert_eq!(report.bound_exponent_quarters, bound as u128);
                    }
                    (Err(HayesError::InvalidParameter(_)), None) => {}
                    (actual, expected) => panic!(
                        "Case-2 domain mismatch at N={cutoff}, r0={r0}: {actual:?} versus {expected:?}"
                    ),
                }
            }
        }

        assert!(matches!(
            binary_type_one_case_two_exponent(601, 301),
            Err(HayesError::InvalidParameter(_))
        ));
    }

    #[test]
    fn binary_type_one_case_five_ledger_exposes_the_missing_saving() {
        let equal = binary_type_one_case_five_exponent(300, 300).unwrap();
        assert_eq!(equal.complete_kloosterman_exponent, 200);
        assert_eq!(equal.bound_exponent_sixths, 1_800);
        assert_eq!(equal.trivial_exponent_sixths, 1_800);
        assert_eq!(equal.deficit_sixths, 0);
        assert!(!equal.strict_saving);

        let worse = binary_type_one_case_five_exponent(300, 320).unwrap();
        assert_eq!(worse.complete_kloosterman_exponent, 213);
        assert_eq!(worse.deficit_sixths, -39);
        assert!(!worse.strict_saving);

        // A residue-class rounding accident can save one sixth at n=302,
        // r0=302, but it is not a uniform power saving.
        let rounded = binary_type_one_case_five_exponent(302, 302).unwrap();
        assert_eq!(rounded.deficit_sixths, 1);
        assert!(rounded.strict_saving);
        assert!(matches!(
            binary_type_one_case_five_exponent(0, 1),
            Err(HayesError::InvalidParameter(_))
        ));
        assert!(matches!(
            binary_type_one_case_five_exponent(3, 2),
            Err(HayesError::InvalidParameter(_))
        ));
    }

    #[test]
    fn endpoint_inverse_mobius_calibration_pins_the_uncovered_interval() {
        let ell = 300;
        let odd = 2 * ell + 1;
        let even = odd + 1;
        let first_odd = (1..ell)
            .find(|degree| {
                endpoint_inverse_mobius_exponent_calibration(ell, odd, *degree)
                    .unwrap()
                    .strict_pointwise_closure
            })
            .unwrap();
        let first_even = (1..ell)
            .find(|degree| {
                endpoint_inverse_mobius_exponent_calibration(ell, even, *degree)
                    .unwrap()
                    .strict_pointwise_closure
            })
            .unwrap();
        assert_eq!(first_odd, 283);
        assert_eq!(first_even, 284);

        let odd_boundary =
            endpoint_inverse_mobius_exponent_calibration(ell, odd, first_odd - 1).unwrap();
        assert!(odd_boundary.cumulative_cutoff_exceeds_modulus);
        assert_eq!(odd_boundary.cumulative_cutoff, 320);
        assert_eq!(odd_boundary.fifteen_sixteenths_exponent_48ths, 14_400);
        assert_eq!(odd_boundary.deficit_48ths, 0);
        assert!(!odd_boundary.strict_pointwise_closure);
        let odd_first = endpoint_inverse_mobius_exponent_calibration(ell, odd, first_odd).unwrap();
        assert_eq!(odd_first.cumulative_cutoff, 319);
        assert_eq!(odd_first.deficit_48ths, 45);
        assert!(odd_first.strict_pointwise_closure);

        for endpoint in [odd, even] {
            for degree in 1..ell {
                assert!(
                    endpoint_inverse_mobius_exponent_calibration(ell, endpoint, degree)
                        .unwrap()
                        .cumulative_cutoff_exceeds_modulus
                );
            }
        }

        assert!(matches!(
            endpoint_inverse_mobius_exponent_calibration(ell, odd - 1, 1),
            Err(HayesError::InvalidParameter(_))
        ));
    }

    fn assert_explicit_endpoint_energy_columns(
        boundary: &EndpointVaughanRangeReport,
        odd_first: &EndpointVaughanRangeReport,
        even_first: &EndpointVaughanRangeReport,
        odd_table: &EndpointVaughanTableReport,
        even_table: &EndpointVaughanTableReport,
    ) {
        assert_eq!(boundary.worst_explicit_energy_bound_sixteenths, 5_176);
        assert_eq!(boundary.explicit_energy_deficit_sixteenths, -376);
        for report in [odd_first, even_first] {
            assert_eq!(report.worst_explicit_energy_bound_sixteenths, 5_160);
            assert_eq!(report.explicit_energy_deficit_sixteenths, -360);
        }
        assert_eq!(odd_table.first_strict_explicit_energy_degree, None);
        assert_eq!(even_table.first_strict_explicit_energy_degree, None);
        let odd_last = odd_table.convolution_orders.last().unwrap();
        assert_eq!(odd_last.interval_degree, 299);
        assert_eq!(odd_last.worst_explicit_energy_bound_sixteenths, 4_906);
        assert_eq!(odd_last.explicit_energy_deficit_sixteenths, -106);
        let row = odd_last
            .rows
            .iter()
            .max_by_key(|row| row.worst_explicit_energy_bound_sixteenths)
            .unwrap();
        assert_eq!(row.case, EndpointVaughanCase::TypeTwoCaseOne);
        assert_eq!(
            row.worst_explicit_energy_effective_modulus_degree,
            Some(152)
        );
        assert_eq!(row.worst_explicit_energy_split_degree, Some(151));
    }

    #[test]
    fn endpoint_vaughan_table_covers_every_split_and_pins_the_same_transition() {
        let limits = HayesLimits {
            max_degree: 400,
            ..HayesLimits::default()
        };
        let ell = 300;
        let odd = 2 * ell + 1;
        let even = odd + 1;
        let odd_boundary = endpoint_vaughan_range_report(ell, odd, 282, limits).unwrap();
        assert!(odd_boundary.all_ranges_covered());
        assert!(odd_boundary.short_inner_type_one_cases_empty());
        assert_eq!(odd_boundary.cumulative_cutoff, 320);
        assert_eq!(odd_boundary.worst_bound_sixteenths, 4_800);
        assert_eq!(odd_boundary.deficit_sixteenths, 0);
        assert!(!odd_boundary.strict_pointwise_main_term_closure());

        let odd_first = endpoint_vaughan_range_report(ell, odd, 283, limits).unwrap();
        let even_first = endpoint_vaughan_range_report(ell, even, 284, limits).unwrap();
        for report in [&odd_first, &even_first] {
            assert!(report.all_ranges_covered());
            assert!(report.short_inner_type_one_cases_empty());
            assert_eq!(report.cumulative_cutoff, 319);
            assert_eq!(report.worst_case, EndpointVaughanCase::TypeOneCaseThree);
            assert_eq!(report.worst_bound_sixteenths, 4_785);
            assert_eq!(report.deficit_sixteenths, 15);
            assert!(report.strict_pointwise_main_term_closure());
            assert!(report.suppressed_losses_remain());
            for required in [
                EndpointVaughanCase::SmallEffectiveModulus,
                EndpointVaughanCase::TypeOneCaseOne,
                EndpointVaughanCase::TypeOneCaseTwo,
                EndpointVaughanCase::TypeOneCaseThree,
                EndpointVaughanCase::TypeTwoCaseOne,
                EndpointVaughanCase::TypeTwoCaseTwo,
                EndpointVaughanCase::TypeTwoCaseThree,
            ] {
                assert!(
                    report
                        .rows
                        .iter()
                        .find(|row| row.case == required)
                        .unwrap()
                        .sample_count
                        > 0
                );
            }
            for empty in [
                EndpointVaughanCase::TypeOneCaseFour,
                EndpointVaughanCase::TypeOneCaseFive,
            ] {
                assert_eq!(
                    report
                        .rows
                        .iter()
                        .find(|row| row.case == empty)
                        .unwrap()
                        .sample_count,
                    0
                );
            }
        }

        let odd_table = endpoint_vaughan_range_table(ell, odd, limits).unwrap();
        let even_table = endpoint_vaughan_range_table(ell, even, limits).unwrap();
        assert!(odd_table.all_convolution_orders_present());
        assert!(even_table.all_convolution_orders_present());
        assert_eq!(odd_table.first_strict_pointwise_degree, Some(283));
        assert_eq!(even_table.first_strict_pointwise_degree, Some(284));
        assert_explicit_endpoint_energy_columns(
            &odd_boundary,
            &odd_first,
            &even_first,
            &odd_table,
            &even_table,
        );
        assert!(odd_table.suppressed_losses_remain());
        assert!(even_table.suppressed_losses_remain());

        let unbuffered = odd_endpoint_vaughan_tail_budget(ell, 292, 0, limits).unwrap();
        assert_eq!(unbuffered.tail_absolute_bound, BigUint::from(1_u8) << 301);
        assert!(!unbuffered.tail_fits_endpoint_budget());
        assert!(!unbuffered.explicit_energy_tail_fits_endpoint_budget());
        let buffered = odd_endpoint_vaughan_tail_budget(ell, 293, 0, limits).unwrap();
        assert_eq!(buffered.tail_absolute_bound, BigUint::from(1_u8) << 300);
        assert!(buffered.tail_fits_endpoint_budget());
        assert!(!buffered.explicit_energy_tail_fits_endpoint_budget());
        assert!(buffered.explicit_energy_tail_absolute_bound > buffered.endpoint_absolute_budget);
        assert_eq!(
            buffered.residual_low_block_budget,
            Some((BigUint::from(1_u8) << 301) - (BigUint::from(1_u8) << 300) - 2_u8)
        );
    }

    #[test]
    fn principal_unit_product_energy_matches_direct_collisions() {
        let limits = HayesLimits::default();
        for ell in 2..=8 {
            for degree in 1..ell {
                let report = principal_unit_product_energy(ell, degree, limits).unwrap();
                let mut products = BTreeMap::<u64, u128>::new();
                for left_tail in 0..(1_u64 << degree) {
                    let left = 1 | (left_tail << 1);
                    for right_tail in 0..(1_u64 << degree) {
                        let right = 1 | (right_tail << 1);
                        *products.entry(unit_multiply(left, right, ell)).or_default() += 1;
                    }
                }
                let direct = products
                    .values()
                    .map(|multiplicity| multiplicity * multiplicity)
                    .sum::<u128>();
                assert_eq!(report.pair_product_energy, BigUint::from(direct));
                assert_eq!(report.set_size, BigUint::from(1_u8) << degree);
                assert_eq!(
                    report.ordered_pair_count,
                    BigUint::from(1_u8) << (2 * degree)
                );
                assert_eq!(report.ordinary_product_regime, 2 * degree <= ell);
            }
        }

        let ordinary = principal_unit_product_energy(14, 6, limits).unwrap();
        assert_eq!(ordinary.pair_product_energy, BigUint::from(16_384_u32));
        let projected = principal_unit_product_energy(14, 8, limits).unwrap();
        assert_eq!(projected.pair_product_energy, BigUint::from(458_752_u32));
    }

    #[test]
    fn principal_unit_product_energy_declines_invalid_or_limited_inputs() {
        let limits = HayesLimits::default();
        assert!(matches!(
            principal_unit_mixed_product_energy(4, 0, 1, limits),
            Err(HayesError::InvalidParameter(_))
        ));
        assert!(matches!(
            principal_unit_mixed_product_energy(4, 1, 4, limits),
            Err(HayesError::InvalidParameter(_))
        ));
        assert!(matches!(
            principal_unit_product_energy(0, 1, limits),
            Err(HayesError::InvalidParameter(_))
        ));
        assert!(matches!(
            principal_unit_product_energy(4, 0, limits),
            Err(HayesError::InvalidParameter(_))
        ));
        assert!(matches!(
            principal_unit_product_energy(4, 4, limits),
            Err(HayesError::InvalidParameter(_))
        ));
        let ell_limited = HayesLimits {
            max_ell: 5,
            ..limits
        };
        assert!(matches!(
            principal_unit_product_energy(6, 3, ell_limited),
            Err(HayesError::ResourceLimit {
                resource: "ell",
                requested: 6,
                limit: 5,
            })
        ));
        let degree_limited = HayesLimits {
            max_degree: 2,
            ..limits
        };
        assert!(matches!(
            principal_unit_product_energy(6, 3, degree_limited),
            Err(HayesError::ResourceLimit {
                resource: "degree",
                requested: 3,
                limit: 2,
            })
        ));
    }

    #[test]
    fn sufficient_bound_implication_is_exact() {
        let report =
            check_conductor_bound_sufficiency(ConductorBoundAssumption::default()).unwrap();
        assert_eq!(report.first_odd_degree, 389);
        assert_eq!(report.first_even_degree, 390);
        let weak_threshold = ConductorBoundAssumption {
            threshold: 10,
            ..ConductorBoundAssumption::default()
        };
        assert!(check_conductor_bound_sufficiency(weak_threshold).is_err());
        let unchecked_remainder = ConductorBoundAssumption {
            threshold: 201,
            ..ConductorBoundAssumption::default()
        };
        assert!(check_conductor_bound_sufficiency(unchecked_remainder).is_err());
    }

    #[test]
    fn fourth_moment_bound_implication_is_exact() {
        let report =
            check_fourth_moment_bound_sufficiency(FourthMomentBoundAssumption::default()).unwrap();
        assert_eq!(report.first_odd_degree, 401);
        assert_eq!(report.first_even_degree, 402);

        let weak_threshold = FourthMomentBoundAssumption {
            threshold: 13,
            ..FourthMomentBoundAssumption::default()
        };
        assert!(check_fourth_moment_bound_sufficiency(weak_threshold).is_err());
        let unchecked_remainder = FourthMomentBoundAssumption {
            threshold: 201,
            ..FourthMomentBoundAssumption::default()
        };
        assert!(check_fourth_moment_bound_sufficiency(unchecked_remainder).is_err());
    }

    #[test]
    fn weak_fourth_moment_ledger_retains_the_proper_power_margin() {
        let odd = weak_fourth_moment_endpoint_ledger(200, 401).unwrap();
        assert_eq!(odd.main_mangoldt_term, BigUint::from(1_u8) << 201);
        assert_eq!(odd.proper_prime_power_upper_bound, BigUint::from(1_u8));
        assert_eq!(
            odd.irreducible_margin,
            (BigUint::from(1_u8) << 201) - BigUint::from(1_u8)
        );
        assert!(
            odd.strict_irreducible_fourth_moment_threshold
                < odd.positivity_only_fourth_moment_threshold
        );
        assert_eq!(
            odd.second_moment_weil_factor,
            (BigUint::from(1_u8) << 200) * BigUint::from(39_206_u32) - BigUint::from(6_u8)
        );
        assert!(odd.strong_connected_target_has_strict_reserve);
        assert!(
            BigUint::from(4_u8) * &odd.sufficient_root_ratio_denominator
                < odd.sufficient_root_ratio_numerator
        );
        assert_eq!(
            odd.wild_fourth_moment_unit_scale,
            (BigUint::from(1_u8) << 200) * (BigUint::from(1_u8) << 603)
        );
        assert_eq!(
            odd.sufficient_wild_constant_numerator,
            odd.strict_irreducible_fourth_moment_threshold
        );
        assert_eq!(
            odd.sufficient_wild_constant_denominator,
            odd.wild_fourth_moment_unit_scale
        );
        assert!(
            odd.sufficient_wild_constant_numerator
                < BigUint::from(2_u8) * &odd.sufficient_wild_constant_denominator
        );

        let even = weak_fourth_moment_endpoint_ledger(200, 402).unwrap();
        assert!(even.proper_prime_power_upper_bound > BigUint::from(1_u8));
        assert!(even.strong_connected_target_has_strict_reserve);
        assert!(
            even.sufficient_wild_constant_numerator
                < BigUint::from(4_u8) * &even.sufficient_wild_constant_denominator
        );
        assert_eq!(
            weak_fourth_moment_endpoint_ledger(8, 16),
            Err(HayesError::InvalidParameter(
                "weak fourth-moment ledger is endpoint-only: ell=8, degree=16".to_owned()
            ))
        );
    }

    #[test]
    fn even_endpoint_proper_power_bound_uses_only_even_exponent_layers() {
        let ell_11 = weak_fourth_moment_endpoint_ledger(11, 24).unwrap();
        assert_eq!(
            ell_11.proper_prime_power_upper_bound,
            BigUint::from(2_304_u32)
        );
        let ell_13 = weak_fourth_moment_endpoint_ledger(13, 28).unwrap();
        assert_eq!(
            ell_13.proper_prime_power_upper_bound,
            BigUint::from(5_376_u32)
        );

        assert!(
            !weak_fourth_moment_endpoint_ledger(12, 26)
                .unwrap()
                .strong_connected_target_has_strict_reserve
        );
        for ell in 13..=100 {
            let degree = 2 * ell + 2;
            assert!(
                weak_fourth_moment_endpoint_ledger(ell, degree)
                    .unwrap()
                    .strong_connected_target_has_strict_reserve,
                "even strong-target crossover failed at ell={ell}"
            );
        }
    }

    #[test]
    fn square_root_layer_bound_implication_is_exact() {
        let report =
            check_square_root_layer_bound_sufficiency(SquareRootLayerBoundAssumption::default())
                .unwrap();
        assert_eq!(report.first_odd_degree, 45);
        assert_eq!(report.first_even_degree, 46);

        for malformed in [
            SquareRootLayerBoundAssumption {
                threshold: 21,
                ..SquareRootLayerBoundAssumption::default()
            },
            SquareRootLayerBoundAssumption {
                finite_max_degree: 43,
                ..SquareRootLayerBoundAssumption::default()
            },
            SquareRootLayerBoundAssumption {
                sqrt_two_upper_numerator: 7,
                sqrt_two_upper_denominator: 5,
                ..SquareRootLayerBoundAssumption::default()
            },
            SquareRootLayerBoundAssumption {
                sqrt_two_upper_numerator: 2,
                sqrt_two_upper_denominator: 1,
                ..SquareRootLayerBoundAssumption::default()
            },
        ] {
            assert!(check_square_root_layer_bound_sufficiency(malformed).is_err());
        }
    }

    #[test]
    fn conductor_layers_telescope() {
        let limits = HayesLimits::default();
        let layers = conductor_layers(8, 17, limits).unwrap();
        assert_eq!(
            layers.iter().map(|layer| layer.value).collect::<Vec<_>>(),
            vec![0, 512, 1024, 960, 832, 3840, 3328, 2304]
        );
        let discrepancy = endpoint_discrepancies(8, limits).unwrap().odd;
        assert_eq!(
            layers.iter().map(|layer| layer.value).sum::<i128>(),
            256 * discrepancy
        );
        assert!(
            layers
                .iter()
                .all(|layer| layer.satisfies_square_root_bound(17))
        );
        assert!(!ConductorLayer { level: 0, value: 0 }.satisfies_square_root_bound(17));
    }

    #[test]
    fn translation_pairs_the_lowest_binary_conductor_level() {
        assert_eq!(translation_paired_conductor_level(0), None);
        assert_eq!(translation_paired_conductor_level(25), Some(1));
        assert_eq!(translation_paired_conductor_level(26), Some(2));
        assert_eq!(translation_paired_conductor_level(12), Some(4));
        assert_eq!(translation_paired_conductor_level(24), Some(8));

        let limits = HayesLimits::default();
        for degree in 3_usize..=20 {
            let ell = degree.div_ceil(2) - 1;
            let paired_level = translation_paired_conductor_level(degree).unwrap();
            if paired_level <= ell {
                let layers = conductor_layers(ell, degree, limits).unwrap();
                assert_eq!(layers[paired_level - 1].value, 0, "degree={degree}");
            }
        }
    }

    #[test]
    fn ordinary_weil_leaves_only_logarithmically_many_top_levels() {
        assert!(low_conductor_weil_split(1).is_err());
        let control = low_conductor_weil_split(199).unwrap();
        assert_eq!(control.cutoff, 189);
        assert_eq!(control.unresolved_top_levels, 10);
        assert_eq!(
            control.scaled_discrepancy_bound,
            BigUint::from(2_u8) * ((BigUint::from(187_u16) << 189) + BigUint::from(2_u8))
        );
        assert!(control.scaled_discrepancy_bound <= control.half_candidate_budget);

        for ell in 2..=4_000 {
            let split = low_conductor_weil_split(ell).unwrap();
            assert!(split.unresolved_top_levels <= ell);
            assert_eq!(split.cutoff + split.unresolved_top_levels, ell);
            assert!(split.scaled_discrepancy_bound <= split.half_candidate_budget);
        }
    }

    #[test]
    fn exact_conductor_second_moment_is_reconstructed() {
        let limits = HayesLimits::default();
        let moment = exact_conductor_second_moment(8, 17, limits).unwrap();
        assert_eq!(moment.level, 8);
        assert_eq!(moment.degree, 17);
        assert_eq!(moment.value, 86_200_320);
        assert!(!moment.proves_square_root_layer_bound());
        assert_eq!(
            exact_conductor_second_moment(17, 36, limits),
            Err(HayesError::InvalidParameter(
                "exact conductor second moment at level 17, degree 36 exceeds the CRT uniqueness range"
                    .to_owned()
            ))
        );
    }

    #[test]
    fn full_family_parseval_diagnostic_is_exact_and_fail_closed() {
        let limits = HayesLimits::default();
        let odd = identity_class_fourier_variance(8, 17, limits).unwrap();
        assert_eq!(odd.uniform_mean, 512);
        assert_eq!(odd.total_squared_deviation, 693_360);
        assert!(!odd.proves_identity_class_positive());

        let even = identity_class_fourier_variance(8, 18, limits).unwrap();
        assert_eq!(even.uniform_mean, 1_024);
        assert_eq!(even.total_squared_deviation, 1_861_136);
        assert!(!even.proves_identity_class_positive());
    }

    #[test]
    fn full_class_distribution_recovers_l_infinity_controls() {
        let limits = HayesLimits::default();
        let low_even = class_population_distribution(5, 12, limits).unwrap();
        assert_eq!(
            low_even.central_absolute_power_sum(4).unwrap(),
            BigUint::from(73_638_400_u32)
        );
        assert!(!low_even.satisfies_fourth_moment_candidate().unwrap());

        let odd = class_population_distribution(8, 17, limits).unwrap();
        assert_eq!(odd.counts.len(), 256);
        assert_eq!(odd.counts[0], identity_class_count(8, 17, limits).unwrap());
        assert_eq!(odd.uniform_mean(), Some(512));
        assert_eq!(odd.maximum_absolute_deviation(), Some(155));
        assert!(odd.all_classes_positive());
        let odd_squared_deviation = odd
            .counts
            .iter()
            .map(|count| count.abs_diff(512).pow(2))
            .sum::<u128>();
        assert_eq!(odd_squared_deviation, 693_360);
        assert_eq!(
            odd.central_absolute_power_sum(2).unwrap(),
            BigUint::from(693_360_u32)
        );
        assert_eq!(
            odd.central_absolute_power_sum(4).unwrap(),
            BigUint::from(5_447_397_264_u64)
        );
        assert_eq!(
            odd.fourth_cumulant_numerator().unwrap(),
            BigInt::from(-47_710_569_216_i64)
        );
        assert_eq!(
            odd.central_absolute_power_sum(0),
            Err(HayesError::InvalidParameter(
                "central absolute power must be in 1..=64, got 0".to_owned()
            ))
        );
        assert_eq!(
            odd.central_absolute_power_sum(65),
            Err(HayesError::InvalidParameter(
                "central absolute power must be in 1..=64, got 65".to_owned()
            ))
        );
        assert!(odd.satisfies_fourth_moment_candidate().unwrap());
        assert!(
            odd.fourth_moment_proves_identity_class_irreducible()
                .unwrap()
        );
        assert!(
            !odd.fourth_moment_proves_candidate_discrepancy_bound()
                .unwrap()
        );
        let mut non_endpoint = odd.clone();
        non_endpoint.degree = 16;
        assert_eq!(
            non_endpoint.fourth_moment_candidate_bound(),
            Err(HayesError::InvalidParameter(
                "fourth-moment candidate is endpoint-only: ell=8, degree=16".to_owned()
            ))
        );

        let even = class_population_distribution(8, 18, limits).unwrap();
        assert_eq!(even.counts[0], identity_class_count(8, 18, limits).unwrap());
        assert_eq!(even.uniform_mean(), Some(1_024));
        assert_eq!(even.maximum_absolute_deviation(), Some(290));
        assert!(even.all_classes_positive());
        assert!(even.satisfies_fourth_moment_candidate().unwrap());
        assert_eq!(
            even.fourth_moment_proves_identity_class_irreducible(),
            Ok(false)
        );
        assert_eq!(
            even.central_absolute_power_sum(4).unwrap(),
            BigUint::from(54_144_813_200_u64)
        );
        assert_eq!(
            even.fourth_cumulant_numerator().unwrap(),
            BigInt::from(3_469_590_547_712_i64)
        );
        assert!(
            !even
                .fourth_moment_proves_candidate_discrepancy_bound()
                .unwrap()
        );
        let even_squared_deviation = even
            .counts
            .iter()
            .map(|count| count.abs_diff(1_024).pow(2))
            .sum::<u128>();
        assert_eq!(even_squared_deviation, 1_861_136);
    }

    #[test]
    fn efron_stein_spectral_weights_reconstruct_parseval() {
        let distribution = class_population_distribution(8, 17, HayesLimits::default()).unwrap();
        let report = distribution
            .efron_stein_spectral_weight_report(16 * 256)
            .unwrap();
        assert_eq!(report.factor_weights, vec![4, 2, 1, 1]);
        assert_eq!(
            report.total_spectral_second_moment,
            BigUint::from(256_u16) * BigUint::from(693_360_u32)
        );
        assert_eq!(
            report
                .weights
                .iter()
                .map(|row| row.character_count)
                .sum::<usize>(),
            256
        );
        assert_eq!(report.weights[0].weight, 0);
        assert_eq!(report.weights[0].character_count, 1);
        assert_eq!(
            report.weights[0].spectral_second_moment,
            BigUint::from(0_u8)
        );
        assert!(
            report
                .conditional_hypercontractive_root_ratio_proxy(3.0)
                .is_some_and(|value| value > 0.0)
        );
        assert!(
            report
                .conditional_hypercontractive_root_ratio_proxy(0.0)
                .is_none()
        );
        assert_eq!(
            distribution.efron_stein_spectral_weight_report(16 * 256 - 1),
            Err(HayesError::ResourceLimit {
                resource: "efron_stein_projection_cells",
                requested: 16 * 256,
                limit: 16 * 256 - 1,
            })
        );
    }

    #[test]
    #[ignore = "extended finite diagnostic; select one row with AXEYUM_EFRON_STEIN_ELL/OFFSET"]
    fn efron_stein_spectral_weight_extended_probe() {
        let parse = |name: &str| {
            std::env::var(name)
                .unwrap_or_else(|_| panic!("missing {name}"))
                .parse::<usize>()
                .unwrap_or_else(|_| panic!("invalid {name}"))
        };
        let ell = parse("AXEYUM_EFRON_STEIN_ELL");
        let offset = parse("AXEYUM_EFRON_STEIN_OFFSET");
        assert!(matches!(offset, 1 | 2));
        let degree = 2 * ell + offset;
        let distribution =
            class_population_distribution(ell, degree, HayesLimits::default()).unwrap();
        let factor_count = principal_unit_factors(ell).len();
        let max_projection_cells = (1_usize << factor_count) * (1_usize << ell);
        let report = distribution
            .efron_stein_spectral_weight_report(max_projection_cells)
            .unwrap();
        let weak = weak_fourth_moment_endpoint_ledger(ell, degree).ok();
        let allowance = weak.as_ref().and_then(|ledger| {
            Some(
                ledger.sufficient_root_ratio_numerator.to_f64()?
                    / ledger.sufficient_root_ratio_denominator.to_f64()?,
            )
        });
        eprintln!(
            "ell={ell} degree={degree} factors={:?} masses={:?} proxy_c2={:?} proxy_c3={:?} proxy_c4={:?} proxy_c9={:?} weak_root_allowance={allowance:?}",
            report.factor_weights,
            report.weights,
            report.conditional_hypercontractive_root_ratio_proxy(2.0),
            report.conditional_hypercontractive_root_ratio_proxy(3.0),
            report.conditional_hypercontractive_root_ratio_proxy(4.0),
            report.conditional_hypercontractive_root_ratio_proxy(9.0),
        );
    }

    #[test]
    fn class_mobius_distribution_matches_independent_factorization() {
        let limits = HayesLimits::default();
        for ell in 1_usize..=5 {
            for degree in 1_usize..=8 {
                let report = class_mobius_distribution(ell, degree, limits).unwrap();
                let direct = direct_class_mobius_distribution(ell, degree);
                assert_eq!(report.values, direct, "ell={ell}, degree={degree}");
                assert_eq!(
                    report.values.iter().sum::<i128>(),
                    if degree == 1 { -2 } else { 0 }
                );
            }
        }

        let odd_endpoint = class_mobius_distribution(8, 17, limits).unwrap();
        assert_eq!(odd_endpoint.values[0], -22);
        assert_eq!(
            odd_endpoint
                .values
                .iter()
                .map(|value| value.unsigned_abs())
                .max(),
            Some(48)
        );
        assert_eq!(
            odd_endpoint
                .values
                .iter()
                .map(|value| value * value)
                .sum::<i128>(),
            85_072
        );
    }

    #[test]
    fn class_mobius_distribution_declines_invalid_or_ambiguous_inputs() {
        let limits = HayesLimits::default();
        assert!(matches!(
            class_mobius_distribution(0, 3, limits),
            Err(HayesError::InvalidParameter(_))
        ));
        assert!(matches!(
            class_mobius_distribution(3, 0, limits),
            Err(HayesError::InvalidParameter(_))
        ));
        let degree_limited = HayesLimits {
            max_degree: 7,
            ..limits
        };
        assert_eq!(
            class_mobius_distribution(3, 8, degree_limited),
            Err(HayesError::ResourceLimit {
                resource: "degree",
                requested: 8,
                limit: 7,
            })
        );
        assert!(matches!(
            class_mobius_distribution(
                3,
                60,
                HayesLimits {
                    max_degree: 60,
                    ..limits
                }
            ),
            Err(HayesError::InvalidParameter(_))
        ));
    }

    #[test]
    fn inverse_additive_mobius_spectrum_matches_direct_factorization() {
        let limits = HayesLimits::default();
        for ell in 2_usize..=5 {
            let unit_to_index = principal_unit_index_map(ell);
            for degree in ell + 2..=2 * ell + 1 {
                let report = inverse_additive_mobius_spectrum(ell, degree, limits).unwrap();
                let direct_mobius = direct_class_mobius_distribution(ell, degree);
                let mut direct_spectrum = vec![0_i128; 1_usize << ell];
                for (frequency, coefficient) in direct_spectrum.iter_mut().enumerate() {
                    for (&unit, &class_index) in &unit_to_index {
                        let packed_inverse = unit_inverse(unit, ell) >> 1;
                        let parity = (packed_inverse & frequency as u64).count_ones() % 2;
                        let sign = if parity == 0 { 1 } else { -1 };
                        *coefficient += sign * direct_mobius[class_index];
                    }
                }
                assert_eq!(report.values, direct_spectrum, "ell={ell}, degree={degree}");

                let current = direct_unit_polynomial_inverse_spectrum(ell, degree);
                let previous = direct_unit_polynomial_inverse_spectrum(ell, degree - 1);
                let reciprocal_difference = current
                    .into_iter()
                    .zip(previous)
                    .map(|(left, right)| left - right)
                    .collect::<Vec<_>>();
                assert_eq!(
                    report.values, reciprocal_difference,
                    "reciprocal/T split: ell={ell}, degree={degree}"
                );
            }
        }
    }

    #[test]
    fn berlekamp_inverse_phase_reports_exact_shift_fibres() {
        let limits = HayesLimits::default();
        let ell = 4;
        let degree = 9;
        let frequency = 12;
        let no_shift =
            binary_berlekamp_inverse_phase_report(ell, degree, frequency, 0, limits).unwrap();
        let middle_shift =
            binary_berlekamp_inverse_phase_report(ell, degree, frequency, 4, limits).unwrap();
        let full_shift =
            binary_berlekamp_inverse_phase_report(ell, degree, frequency, degree - 1, limits)
                .unwrap();
        assert_eq!(no_shift.input_count, 256);
        assert_eq!(no_shift.squarefree_count, 171);
        assert_eq!(no_shift.phase_sum, -19);
        assert_eq!(no_shift.shift_subspace_energy, 171);
        assert_eq!(no_shift.cauchy_square_bound, 43_776);
        assert_eq!(middle_shift.stationary_same_sign_pairs, 1_041);
        assert_eq!(middle_shift.oscillating_opposite_sign_pairs, 796);
        assert_eq!(middle_shift.shift_subspace_energy, 245);
        assert_eq!(middle_shift.cauchy_square_bound, 3_920);
        assert_eq!(full_shift.shift_subspace_energy, 361);
        assert_eq!(full_shift.cauchy_square_bound, 361);
        assert_eq!(full_shift.phase_sum.unsigned_abs().pow(2), 361);
        assert!(!no_shift.improves_trivial_bound());
        assert!(middle_shift.improves_trivial_bound());
        assert!(full_shift.improves_trivial_bound());
        for candidate_frequency in 0..1 << ell {
            assert!(
                binary_berlekamp_inverse_phase_report(ell, degree, candidate_frequency, 4, limits,)
                    .unwrap()
                    .improves_trivial_bound(),
                "frequency={candidate_frequency}"
            );
        }

        let current =
            binary_berlekamp_inverse_phase_report(ell, degree, frequency, degree - 1, limits)
                .unwrap();
        let previous =
            binary_berlekamp_inverse_phase_report(ell, degree - 1, frequency, degree - 2, limits)
                .unwrap();
        let spectrum = inverse_additive_mobius_spectrum(ell, degree, limits).unwrap();
        assert_eq!(
            current.phase_sum - previous.phase_sum,
            spectrum.values[frequency]
        );

        assert!(matches!(
            binary_berlekamp_inverse_phase_report(ell, degree, 1 << ell, 1, limits),
            Err(HayesError::InvalidParameter(_))
        ));
        assert!(matches!(
            binary_berlekamp_inverse_phase_report(ell, degree, 0, degree, limits),
            Err(HayesError::InvalidParameter(_))
        ));
        let starved = HayesLimits {
            max_table_cells: 100,
            ..limits
        };
        assert_eq!(
            binary_berlekamp_inverse_phase_report(ell, degree, frequency, 4, starved),
            Err(HayesError::ResourceLimit {
                resource: "table_cells",
                requested: 224,
                limit: 100,
            })
        );
    }

    #[test]
    fn berlekamp_annihilator_energy_is_the_exact_frequency_average() {
        let limits = HayesLimits::default();
        let ell = 4;
        let degree = 9;
        let interval_degree = 3;
        let shift_dimension = 3;
        let report = binary_berlekamp_annihilator_energy_report(
            ell,
            degree,
            interval_degree,
            shift_dimension,
            limits,
        )
        .unwrap();
        assert_eq!(report.input_count, 256);
        assert_eq!(report.annihilator_frequency_count, 2);
        assert_eq!(report.occupied_coset_count, 62);
        assert_eq!(report.inverse_interval_phase_sum, 0);
        assert_eq!(report.signed_coset_energy, BigUint::from(179_u16));
        assert_eq!(report.unsigned_collision_count, BigUint::from(599_u16));
        assert_eq!(report.diagonal_squarefree_count, 171);
        assert_eq!(report.off_diagonal_signed_correlation, 8);
        assert_eq!(report.averaged_shift_energy, BigUint::from(358_u16));
        assert_eq!(report.fibre_cauchy_square_bound, BigUint::from(5_728_u16));
        let mut direct_phase_sum = 0_i128;
        let mut direct_energy = BigUint::from(0_u8);
        for frequency in (0..1 << ell).step_by(1 << interval_degree) {
            let phase = binary_berlekamp_inverse_phase_report(
                ell,
                degree,
                frequency,
                shift_dimension,
                limits,
            )
            .unwrap();
            direct_phase_sum += phase.phase_sum;
            direct_energy += BigUint::from(phase.shift_subspace_energy);
        }
        assert_eq!(
            direct_phase_sum,
            i128::try_from(report.annihilator_frequency_count).unwrap()
                * report.inverse_interval_phase_sum
        );
        assert_eq!(direct_energy, report.averaged_shift_energy);
        assert!(report.has_signed_collision_cancellation());
    }

    #[test]
    fn connected_off_diagonal_candidate_has_exact_endpoint_ledger() {
        let limits = HayesLimits::default();
        // Keep the ordinary gate bounded.  The extended ell<=9 research
        // sweep is replayed by the ignored environment-selected probe below.
        for probe_ell in 2_usize..=7 {
            for endpoint in [2 * probe_ell + 1, 2 * probe_ell + 2] {
                for d in 1..probe_ell {
                    let k = endpoint - d;
                    let candidate =
                        binary_berlekamp_annihilator_energy_report(probe_ell, k, d, d, limits)
                            .unwrap();
                    let random_scale = BigUint::from(1_u8) << k;
                    assert!(
                        candidate.signed_coset_energy <= random_scale,
                        "ell={probe_ell}, endpoint={endpoint}, d={d}, energy={}",
                        candidate.signed_coset_energy
                    );
                    assert!(
                        candidate.worst_bucket_signed_square
                            <= BigUint::from(2 * d) * candidate.worst_bucket_population,
                        "local ell={probe_ell}, endpoint={endpoint}, d={d}, square={}, population={}",
                        candidate.worst_bucket_signed_square,
                        candidate.worst_bucket_population
                    );
                    assert!(
                        candidate
                            .satisfies_connected_off_diagonal_candidate()
                            .unwrap(),
                        "connected ell={probe_ell}, endpoint={endpoint}, d={d}, offdiag={}",
                        candidate.off_diagonal_signed_correlation
                    );
                    assert!(
                        candidate
                            .connected_candidate_implies_degree_scale_energy()
                            .unwrap()
                    );
                }
            }
        }
        let constant_one_failure =
            binary_berlekamp_annihilator_energy_report(6, 9, 5, 5, limits).unwrap();
        assert_eq!(
            constant_one_failure.signed_coset_energy,
            BigUint::from(309_u16)
        );
        assert_eq!(
            constant_one_failure.shift_correlations[0],
            BinaryBerlekampShiftCorrelation {
                shift: 0,
                valuation: None,
                supported_pairs: 171,
                signed_correlation: 171,
                artin_schreier_modulus_degree: None,
                artin_schreier_kernel_dimension: None,
                support_upper_bound: 171,
            }
        );
        assert_eq!(constant_one_failure.off_diagonal_signed_correlation, 138);
        let constant_one_magnitude = BigUint::from(138_u16);
        assert!(
            constant_one_magnitude.pow(2)
                > BigUint::from(1_u8)
                    << (constant_one_failure.degree + constant_one_failure.shift_dimension)
        );
        assert!(
            constant_one_failure
                .satisfies_connected_off_diagonal_candidate()
                .unwrap()
        );
        assert!(
            constant_one_failure
                .connected_candidate_implies_degree_scale_energy()
                .unwrap()
        );
        assert!(constant_one_failure.signed_coset_energy > BigUint::from(1_u8) << 8);
        assert!(constant_one_failure.signed_coset_energy <= BigUint::from(1_u8) << 9);
    }

    #[test]
    fn binary_witt_coordinate_roundtrip_is_exact() {
        let limits = HayesLimits::default();
        assert!(binary_principal_unit_witt_report(1, 0, limits).is_err());
        assert!(binary_principal_unit_witt_report(2, 3, limits).is_err());
        assert!(binary_principal_unit_witt_report(1 << 5 | 1, 3, limits).is_err());
        for ell in 1_usize..=5 {
            for unit_tail in 0_u64..1_u64 << ell {
                let unit = 1 | (unit_tail << 1);
                let report = binary_principal_unit_witt_report(unit, ell, limits).unwrap();
                assert_eq!(report.unit, unit);
                assert_eq!(report.blocks.len(), ell.div_ceil(2));
                for block in &report.blocks {
                    assert_eq!(
                        block.active_slot_degrees.len(),
                        block.coordinate.count_ones() as usize
                    );
                    assert_eq!(
                        block.highest_active_slot,
                        block.active_slot_degrees.last().copied()
                    );
                    assert!(block.active_slot_degrees.iter().all(|&slot| slot <= ell));
                }
            }
        }
        let frobenius_slot = binary_principal_unit_witt_report(1 | (1 << 4), 5, limits).unwrap();
        assert_eq!(frobenius_slot.blocks[0].coordinate, 4);
        assert_eq!(frobenius_slot.blocks[0].active_slot_degrees, vec![4]);
        assert_eq!(frobenius_slot.blocks[0].highest_active_slot, Some(4));
    }

    #[test]
    fn witt_first_slot_projection_has_the_exact_growing_kernel() {
        let limits = HayesLimits::default();
        assert!(binary_witt_first_slot_projection_report(0, limits).is_err());
        for ell in 1_usize..=8 {
            let report = binary_witt_first_slot_projection_report(ell, limits).unwrap();
            assert_eq!(
                report.first_slot_degrees,
                (1..=ell).step_by(2).collect::<Vec<_>>()
            );
            assert_eq!(report.source_order, 1 << ell);
            assert_eq!(report.image_order, 1 << ell.div_ceil(2));
            assert_eq!(report.maximal_elementary_quotient_rank, ell.div_ceil(2));
            assert_eq!(report.kernel_order, 1 << (ell / 2));
            assert_eq!(report.kernel_dimension, ell / 2);
            assert_eq!(report.minimum_elementary_kernel_dimension, ell / 2);
            assert_eq!(report.block_lengths.iter().sum::<usize>(), ell);

            let factors = principal_unit_factors(ell);
            let project = |mut index: usize| {
                let mut mask = 0_usize;
                for (block, factor) in factors.iter().enumerate() {
                    let coordinate = index % factor.order;
                    index /= factor.order;
                    mask |= (coordinate & 1) << block;
                }
                assert_eq!(index, 0);
                mask
            };
            let mut fibre_sizes = vec![0_usize; report.image_order];
            for index in 0..report.source_order {
                fibre_sizes[project(index)] += 1;
            }
            assert!(fibre_sizes.iter().all(|&size| size == report.kernel_order));
            for left in 0..report.source_order {
                for right in 0..report.source_order {
                    let sum = add_mixed_radix_indices(left, right, &factors).unwrap();
                    assert_eq!(project(sum), project(left) ^ project(right));
                }
            }
        }
    }

    #[test]
    fn population_refinement_triangle_reconstructs_and_has_failure_control() {
        let projection_limit = 2 * 12 * (1 << 12);
        let low_failure = class_population_distribution(4, 9, HayesLimits::default())
            .unwrap()
            .population_refinement_triangle(projection_limit)
            .unwrap();
        assert_eq!(low_failure.triangle_numerator, BigUint::from(272_u16));
        assert_eq!(
            low_failure.candidate_target_numerator,
            BigUint::from(256_u16)
        );
        assert!(!low_failure.proves_candidate_discrepancy_bound());

        let expected = [
            (25_usize, 8_213_504_u128, 2_168_832_u128, 1_400_832_i128),
            (26_usize, 14_542_848_u128, 2_653_184_u128, 1_339_392_i128),
        ];
        for (degree, triangle, identity_triangle, connected_top) in expected {
            let distribution =
                class_population_distribution(12, degree, HayesLimits::default()).unwrap();
            let report = distribution
                .population_refinement_triangle(projection_limit)
                .unwrap();
            assert_eq!(report.levels.len(), 12);
            assert_eq!(report.triangle_numerator, BigUint::from(triangle));
            assert_eq!(
                report.identity_path_triangle_numerator,
                BigUint::from(identity_triangle)
            );
            assert_eq!(report.connected_top_first_level, 7);
            assert_eq!(
                report.connected_top_signed_numerator,
                BigInt::from(connected_top)
            );
            assert!(report.satisfies_connected_top_candidate());
            assert_eq!(
                report.candidate_target_numerator,
                BigUint::from(16_777_216_u128)
            );
            assert!(report.proves_candidate_discrepancy_bound());
            assert_eq!(
                report.levels.last().unwrap().maximum_sibling_difference,
                if degree == 25 { 1_575 } else { 3_016 }
            );
            assert!(report.satisfies_square_root_fibre_envelope());
        }
        for ell in 1_usize..=30 {
            let odd = population_refinement_envelope_implication(ell, 2 * ell + 1).unwrap();
            let even = population_refinement_envelope_implication(ell, 2 * ell + 2).unwrap();
            assert_eq!(odd.proves_candidate_discrepancy_bound(), ell >= 13);
            assert_eq!(even.proves_candidate_discrepancy_bound(), ell >= 15);
        }
        let odd_hybrid = population_refinement_hybrid_implication(200, 401).unwrap();
        let even_hybrid = population_refinement_hybrid_implication(200, 402).unwrap();
        for report in [&odd_hybrid, &even_hybrid] {
            assert_eq!(report.first_square_root_fibre_level, 192);
            assert_eq!(report.square_root_fibre_level_count, 9);
            assert!(report.proves_candidate_discrepancy_bound());
            assert!(report.weil_triangle_numerator > BigUint::from(0_u8));
            assert!(report.square_root_fibre_triangle_numerator > BigUint::from(0_u8));
        }
        for ell in 200_usize..=512 {
            let first = ell - ell.ilog2() as usize - usize::from(!ell.is_power_of_two());
            for degree in [2 * ell + 1, 2 * ell + 2] {
                let report = population_refinement_hybrid_implication(ell, degree).unwrap();
                assert!(report.first_square_root_fibre_level >= first);
                assert!(report.square_root_fibre_level_count <= ell + 1 - first);
                let connected =
                    population_refinement_connected_top_implication(ell, degree).unwrap();
                assert_eq!(connected.first_top_level, first - 1);
                assert_eq!(connected.top_level_count, ell + 2 - first);
                assert!(connected.proves_candidate_discrepancy_bound());
            }
        }
        assert!(population_refinement_envelope_implication(12, 24).is_err());
        assert!(population_refinement_hybrid_implication(12, 24).is_err());
        assert!(population_refinement_connected_top_implication(12, 24).is_err());
        assert!(matches!(
            class_population_distribution(12, 25, HayesLimits::default())
                .unwrap()
                .population_refinement_triangle(1),
            Err(HayesError::ResourceLimit {
                resource: "population_refinement_projection_cells",
                ..
            })
        ));
    }

    #[test]
    fn connected_top_refinement_quantifies_required_weil_saving() {
        for degree in [401_usize, 402] {
            let connected = population_refinement_connected_top_implication(200, degree).unwrap();
            assert_eq!(connected.first_top_level, 191);
            assert_eq!(connected.top_level_count, 10);
            assert_eq!(
                connected.connected_top_required_saving_ceiling,
                BigUint::from(1_583_u16)
            );
            assert_eq!(
                &connected.connected_top_individual_weil_numerator * BigUint::from(32_u8),
                &connected.connected_top_assumption_numerator * BigUint::from(50_641_u16)
            );
        }
    }

    #[test]
    fn one_sided_connected_refinement_spends_the_exact_remaining_allowance() {
        let first_odd = population_refinement_one_sided_connected_implication(200, 401).unwrap();
        let first_even = population_refinement_one_sided_connected_implication(200, 402).unwrap();
        assert_eq!(first_odd.required_saving_ceiling, BigUint::from(626_u16));
        assert_eq!(first_even.required_saving_ceiling, BigUint::from(626_u16));
        let scaled_allowance = &first_odd.negative_allowance_numerator * BigUint::from(128_u8);
        assert!(scaled_allowance < &first_odd.candidate_target_numerator * BigUint::from(81_u8));
        assert!(scaled_allowance > &first_odd.candidate_target_numerator * BigUint::from(80_u8));
        for ell in 200_usize..=1_024 {
            for degree in [2 * ell + 1, 2 * ell + 2] {
                let one_sided =
                    population_refinement_one_sided_connected_implication(ell, degree).unwrap();
                let symmetric =
                    population_refinement_connected_top_implication(ell, degree).unwrap();
                assert!(one_sided.has_exact_allowance_partition());
                assert_eq!(one_sided.first_top_level, symmetric.first_top_level);
                assert_eq!(one_sided.top_level_count, symmetric.top_level_count);
                assert!(
                    one_sided.negative_allowance_numerator
                        > symmetric.connected_top_assumption_numerator
                );
                assert!(
                    one_sided.required_saving_ceiling
                        < symmetric.connected_top_required_saving_ceiling
                );
                let boundary = -BigInt::from(one_sided.negative_allowance_numerator.clone());
                assert!(!one_sided.trace_closes_candidate(&boundary));
                assert!(one_sided.trace_closes_candidate(&(boundary + BigInt::from(1_u8))));
            }
        }
        assert!(population_refinement_one_sided_connected_implication(3, 7).is_err());
        assert!(population_refinement_one_sided_connected_implication(200, 400).is_err());
    }

    #[test]
    fn top_polynomial_refinement_closes_the_finite_handoff() {
        let odd = population_refinement_top_polynomial_implication(200, 401).unwrap();
        let even = population_refinement_top_polynomial_implication(200, 402).unwrap();
        for report in [&odd, &even] {
            assert_eq!(report.first_top_level, 168);
            assert_eq!(report.top_level_count, 33);
            assert!(report.low_weil_scaled_numerator > BigUint::from(0_u8));
            assert!(report.top_polynomial_scaled_numerator > BigUint::from(0_u8));
            assert!(report.proves_candidate_discrepancy_bound());
        }
        assert_eq!(odd.common_denominator, 1_600);
        assert_eq!(even.common_denominator, 2_400);

        for ell in 200_usize..=1_024 {
            let ceil_log = ell.ilog2() as usize + usize::from(!ell.is_power_of_two());
            for degree in [2 * ell + 1, 2 * ell + 2] {
                let report = population_refinement_top_polynomial_implication(ell, degree).unwrap();
                assert_eq!(report.first_top_level, ell - 4 * ceil_log);
                assert_eq!(report.top_level_count, 4 * ceil_log + 1);
                assert!(report.proves_candidate_discrepancy_bound());
            }
        }
        assert!(population_refinement_top_polynomial_implication(199, 399).is_err());
        assert!(population_refinement_top_polynomial_implication(200, 400).is_err());
    }

    #[test]
    fn connected_top_mobius_orders_reconstruct_the_selected_trace() {
        let limits = HayesLimits::default();
        let expected = [
            (
                17_usize,
                11_264_i128,
                vec![-768_i128, 8_192, -2_304, 2_048, 10_240, 15_360, -21_504],
            ),
            (
                18,
                18_176,
                vec![-4_096_i128, 7_168, 9_984, 0, -5_120, 13_824, -3_584],
            ),
        ];
        for (degree, expected_trace, expected_terms) in expected {
            let report = connected_top_mobius_convolution(8, degree, limits).unwrap();
            assert_eq!(report.first_top_level, 4);
            assert_eq!(report.coarse_level, 3);
            assert_eq!(report.first_nonzero_interval_degree, Some(1));
            assert_eq!(
                report.nonzero_order_count,
                expected_terms.iter().filter(|value| **value != 0).count()
            );
            assert_eq!(report.signed_connected_trace, BigInt::from(expected_trace));
            assert!(&report.orderwise_absolute_trace > report.signed_connected_trace.magnitude());
            assert_eq!(
                report
                    .terms
                    .iter()
                    .map(|term| term.connected_value.clone())
                    .collect::<Vec<_>>(),
                expected_terms
                    .into_iter()
                    .map(BigInt::from)
                    .collect::<Vec<_>>()
            );
        }
        assert!(connected_top_mobius_convolution(4, 9, limits).is_err());
    }

    #[test]
    fn carlitz_geometry_reconstructs_the_connected_top_weil_envelope() {
        let geometry = carlitz_connected_top_geometry(12, 25).unwrap();
        assert_eq!(geometry.fine_conductor_exponent, 13);
        assert_eq!(geometry.coarse_conductor_exponent, 7);
        assert_eq!(geometry.artin_schreier_step_count, 6);
        assert_eq!(geometry.fine_galois_degree, BigUint::from(4_096_u16));
        assert_eq!(geometry.coarse_galois_degree, BigUint::from(64_u8));
        assert_eq!(geometry.relative_extension_degree, BigUint::from(64_u8));
        assert_eq!(geometry.fine_twice_genus, BigUint::from(40_962_u16));
        assert_eq!(geometry.coarse_twice_genus, BigUint::from(258_u16));
        assert_eq!(
            geometry.relative_first_cohomology_dimension,
            BigUint::from(40_704_u16)
        );
        assert_eq!(
            geometry.relative_abelian_dimension,
            BigUint::from(20_352_u16)
        );
        assert_eq!(geometry.p_zero_trace_divisibility_exponent, 1);
        assert_eq!(geometry.p_zero_trace_divisor, BigUint::from(2_u8));
        assert_eq!(
            geometry.integer_relative_weil_numerator,
            BigUint::from(333_447_168_u32)
        );
        assert_eq!(
            geometry.connected_top_allowance_numerator,
            BigUint::from(4_194_304_u32)
        );
        assert_eq!(geometry.required_saving_ceiling, BigUint::from(80_u8));
        assert!(
            geometry.one_sided_negative_allowance_numerator
                > geometry.connected_top_allowance_numerator
        );
        assert!(geometry.one_sided_required_saving_ceiling < geometry.required_saving_ceiling);
        assert!(carlitz_connected_top_geometry(12, 24).is_err());
    }

    #[test]
    fn p_zero_trace_divisibility_is_trivial_on_every_lemire_endpoint() {
        for ell in 200..=1_024 {
            for degree in [2 * ell + 1, 2 * ell + 2] {
                let geometry = carlitz_connected_top_geometry(ell, degree).unwrap();
                assert!(geometry.relative_abelian_dimension > BigUint::from(degree));
                assert_eq!(geometry.p_zero_trace_divisibility_exponent, 1);
                assert_eq!(geometry.p_zero_trace_divisor, BigUint::from(2_u8));
                assert!(geometry.one_sided_required_saving_ceiling > BigUint::from(1_u8));
            }
        }
    }

    #[test]
    fn binary_hayes_l_degrees_follow_exact_conductors() {
        let limits = HayesLimits {
            max_ell: 8,
            ..HayesLimits::default()
        };
        let level_five = binary_hayes_l_degree_distribution(5, limits).unwrap();
        assert_eq!(
            level_five.positive_degree_counts,
            vec![
                (1, BigUint::from(2_u8)),
                (2, BigUint::from(4_u8)),
                (3, BigUint::from(8_u8)),
                (4, BigUint::from(16_u8)),
            ]
        );
        assert_eq!(level_five.nontrivial_character_count, BigUint::from(31_u8));
        assert_eq!(level_five.aggregate_degree, BigUint::from(98_u8));

        let level_eight = binary_hayes_l_degree_distribution(8, limits).unwrap();
        assert_eq!(
            level_eight.positive_degree_counts,
            (1_usize..8)
                .map(|degree| (degree, BigUint::from(1_u8) << degree))
                .collect::<Vec<_>>()
        );
        assert_eq!(level_eight.aggregate_degree, BigUint::from(1_538_u16));

        for ell in 1_usize..=6 {
            let report = binary_hayes_l_degree_distribution(ell, limits).unwrap();
            let factors = principal_unit_factors(ell);
            let mut direct = BTreeMap::<usize, BigUint>::new();
            for character in 1..(1_usize << ell) {
                let level = mixed_radix_character_conductor(character, &factors)
                    .unwrap()
                    .unwrap();
                if level > 1 {
                    *direct.entry(level - 1).or_default() += BigUint::from(1_u8);
                }
            }
            assert_eq!(
                report
                    .positive_degree_counts
                    .into_iter()
                    .collect::<BTreeMap<_, _>>(),
                direct
            );
        }

        assert!(binary_hayes_l_degree_distribution(0, limits).is_err());
        assert!(matches!(
            binary_hayes_l_degree_distribution(9, limits),
            Err(HayesError::ResourceLimit {
                resource: "ell",
                requested: 9,
                limit: 8
            })
        ));
    }

    #[test]
    fn exact_conductor_trace_obstructs_a_supersingular_heisenberg_decomposition() {
        let limits = HayesLimits::default();
        let witness = exact_conductor_supersingularity_divisibility(10, 22, limits).unwrap();
        assert_eq!(witness.trace, -5_120);
        assert_eq!(witness.necessary_divisor, BigUint::from(2_048_u16));
        assert_eq!(witness.magnitude_remainder, BigUint::from(1_024_u16));
        assert!(witness.obstructs_supersingularity());

        let inconclusive = exact_conductor_supersingularity_divisibility(4, 4, limits).unwrap();
        assert!(!inconclusive.obstructs_supersingularity());
        assert!(exact_conductor_supersingularity_divisibility(4, 5, limits).is_err());
    }

    #[test]
    fn root_number_fibres_do_not_determine_endpoint_power_sums() {
        let report = hayes_root_number_fibre_report(5, 11, HayesLimits::default()).unwrap();
        assert_eq!(report.primitive_character_count, 16);
        assert_eq!(report.leading_coefficient_fibre_count, 6);
        assert_eq!(report.varying_power_sum_fibre_count, 6);
        let witness = report.witness.unwrap();
        assert_eq!(witness.level, 5);
        assert_eq!(witness.degree, 11);
        assert_eq!(witness.cyclotomic_order, 8);
        assert_eq!((witness.left_character, witness.right_character), (26, 30));
        assert_eq!(witness.common_leading_coefficient, [-4, 0, 0, 0]);
        assert_eq!(witness.left_power_sum, [-32, 0, 32, 0]);
        assert_eq!(witness.right_power_sum, [-32, 0, -32, 0]);

        let declined = hayes_root_number_fibre_report(15, 31, HayesLimits::default());
        assert_eq!(
            declined,
            Err(HayesError::ResourceLimit {
                resource: "root_number_fibre_cells",
                requested: 1 << 30,
                limit: HayesLimits::default().max_table_cells,
            })
        );
    }

    #[test]
    fn cyclotomic_uniformizer_and_hayes_newton_polygons_are_exact() {
        for order in [2_usize, 4, 8, 16] {
            let mut uniformizer = PowerTwoCyclotomicInteger::root_power(order, 0);
            uniformizer
                .subtract_assign(&PowerTwoCyclotomicInteger::root_power(order, 1))
                .unwrap();
            assert_eq!(uniformizer.uniformizer_valuation().unwrap(), Some(1));
            let two = PowerTwoCyclotomicInteger::root_power(order, 0)
                .scale(2)
                .unwrap();
            assert_eq!(two.uniformizer_valuation().unwrap(), Some(order / 2));
            let mut power = PowerTwoCyclotomicInteger::root_power(order, 0);
            for valuation in 1..=order {
                power = power.multiply(&uniformizer).unwrap();
                assert_eq!(power.uniformizer_valuation().unwrap(), Some(valuation));
            }
            assert_eq!(
                PowerTwoCyclotomicInteger::zero(order)
                    .uniformizer_valuation()
                    .unwrap(),
                None
            );
        }

        for order in [2_usize, 4, 8] {
            let dimension = order / 2;
            let exhaustive_size = 5_usize.pow(u32::try_from(dimension).unwrap());
            for seed in 1..exhaustive_size.min(512) {
                let mut quotient = seed;
                let mut coefficients = Vec::with_capacity(dimension);
                for _ in 0..dimension {
                    coefficients.push(i128::try_from(quotient % 5).unwrap() - 2);
                    quotient /= 5;
                }
                let value = PowerTwoCyclotomicInteger(coefficients);
                if value.0.iter().all(|coefficient| *coefficient == 0) {
                    continue;
                }
                let mut norm = value.field_norm().unwrap();
                assert_ne!(norm, BigInt::from(0_u8));
                let mut norm_valuation = 0_usize;
                while &norm % BigInt::from(2_u8) == BigInt::from(0_u8) {
                    norm /= 2;
                    norm_valuation += 1;
                }
                assert_eq!(value.uniformizer_valuation().unwrap(), Some(norm_valuation));
            }
        }

        let expected = [
            (2_usize, 2_usize, -8_i128, 3_u32),
            (2, 8, 32, 5),
            (4, 8, 80, 4),
            (4, 8, -160, 5),
            (4, 64, -2_048, 11),
            (4, 80, 2_944, 7),
            (8, 128, 2_304, 8),
            (8, 128, -9_472, 8),
            (8, 256, 108_032, 9),
        ];
        for (level, (expected_denominator, expected_multiplicity, expected_trace, expected_v2)) in
            (2..=10).zip(expected)
        {
            let degree = 2 * level + 1;
            let group_order = 1 << level;
            let max_table_cells =
                (level * (1 << (2 * level - 1))).max((level + degree + 1) * group_order);
            let report = hayes_conductor_two_adic_newton_report(
                level,
                degree,
                HayesLimits {
                    max_ell: level,
                    max_degree: degree,
                    max_group_order: group_order,
                    max_table_cells,
                },
            )
            .unwrap();
            assert_eq!(report.primitive_character_count, 1 << (level - 1));
            assert_eq!(report.characters.len(), report.primitive_character_count);
            assert_eq!(report.minimum_slope_numerator, 1);
            assert_eq!(report.minimum_slope_denominator, expected_denominator);
            assert_eq!(report.minimum_slope_multiplicity, expected_multiplicity);
            assert_eq!(report.direct_conductor_trace, expected_trace);
            assert_eq!(
                report.direct_conductor_trace_two_adic_valuation,
                Some(expected_v2)
            );
            assert!(report.characters.iter().all(|row| {
                row.coefficient_uniformizer_valuations.len() == level
                    && row
                        .slopes
                        .iter()
                        .map(|slope| slope.multiplicity)
                        .sum::<usize>()
                        == level - 1
            }));
        }
    }

    #[test]
    fn galois_orbit_traces_reconstruct_exact_conductor_layers() {
        let mut worst = (0_u128, None);
        for level in 2..=12 {
            for degree in [2 * level + 1, 2 * level + 2] {
                let report =
                    hayes_galois_orbit_trace_report(level, degree, HayesLimits::default()).unwrap();
                assert_eq!(report.primitive_character_count, 1 << (level - 1));
                assert_eq!(
                    report.reconstructed_conductor_trace,
                    report.direct_conductor_trace
                );
                if report.required_order_layer_coefficient > worst.0 {
                    worst = (
                        report.required_order_layer_coefficient,
                        Some(report.clone()),
                    );
                }
                if (level, degree) == (6, 14) {
                    assert_eq!(report.maximum_absolute_order_layer_trace, 1_920);
                    assert_eq!(report.required_order_layer_coefficient, 3);
                }
                assert_eq!(
                    report
                        .orders
                        .iter()
                        .map(|row| row.orbit_count)
                        .sum::<usize>(),
                    report.orbit_count
                );
                assert_eq!(
                    report
                        .orders
                        .iter()
                        .map(|row| row.signed_trace_sum)
                        .sum::<i128>(),
                    report.direct_conductor_trace
                );
                if (level, degree) == (7, 15) {
                    assert_eq!(report.candidate_orbit_allowance, 256);
                    assert_eq!(report.maximum_absolute_orbit_trace, 1_696);
                    assert_eq!(report.candidate_violation_count, 18);
                    assert_eq!(report.order_layer_candidate_allowance, 6_144);
                    assert_eq!(report.maximum_absolute_order_layer_trace, 1_472);
                    assert_eq!(report.order_layer_candidate_violation_count, 0);
                    assert_eq!(report.required_order_layer_coefficient, 1);
                    assert_eq!(
                        report
                            .orders
                            .iter()
                            .map(|row| (row.character_order, row.signed_trace_sum))
                            .collect::<Vec<_>>(),
                        [(2, 128), (4, 1_344), (8, 1_472)]
                    );
                }
            }
        }
        assert_eq!(worst.0, 17, "{:?}", worst.1);
        let worst = worst.1.unwrap();
        assert_eq!((worst.level, worst.degree), (11, 24));
        assert_eq!(worst.maximum_absolute_order_layer_trace, 663_552);
        assert_eq!(worst.order_layer_candidate_violation_count, 2);
    }

    #[test]
    fn fomenko_restriction_packets_reconstruct_exact_conductor_layers() {
        let mut worst_one_coordinate = (0_u128, None);
        let mut worst_logarithmic = (0_u128, None);
        for level in 2..=12 {
            for degree in [2 * level + 1, 2 * level + 2] {
                let report = hayes_fomenko_restriction_packet_report(
                    level,
                    1,
                    degree,
                    HayesLimits::default(),
                )
                .unwrap();
                assert_eq!(report.restriction_kernel_size, 2);
                assert_eq!(report.primitive_character_count, 1 << (level - 1));
                assert!(report.packet_count <= 1 << (level - 2));
                assert!(report.maximum_packet_size >= 2);
                assert_eq!(
                    report.reconstructed_conductor_trace,
                    report.direct_conductor_trace
                );
                if report.required_square_root_coefficient > worst_one_coordinate.0 {
                    worst_one_coordinate = (
                        report.required_square_root_coefficient,
                        Some(report.clone()),
                    );
                }

                let restriction_level =
                    (level.ilog2() as usize + usize::from(!level.is_power_of_two()) + 1)
                        .min(level - 1);
                let logarithmic = hayes_fomenko_restriction_packet_report(
                    level,
                    restriction_level,
                    degree,
                    HayesLimits::default(),
                )
                .unwrap();
                assert_eq!(logarithmic.restriction_kernel_size, 1 << restriction_level);
                assert_eq!(
                    logarithmic.reconstructed_conductor_trace,
                    logarithmic.direct_conductor_trace
                );
                if logarithmic.required_square_root_coefficient > worst_logarithmic.0 {
                    worst_logarithmic = (
                        logarithmic.required_square_root_coefficient,
                        Some(logarithmic),
                    );
                }
            }
        }
        let worst_one_coordinate = worst_one_coordinate.1.unwrap();
        let worst_logarithmic = worst_logarithmic.1.unwrap();
        assert_eq!(
            (worst_one_coordinate.level, worst_one_coordinate.degree),
            (12, 26)
        );
        assert_eq!(worst_one_coordinate.packet_count, 256);
        assert_eq!(worst_one_coordinate.maximum_packet_size, 8);
        assert_eq!(worst_one_coordinate.maximum_absolute_packet_trace, 226_816);
        assert_eq!(worst_one_coordinate.packetwise_absolute_trace, 15_422_336);
        assert_eq!(worst_one_coordinate.square_root_violation_count, 233);
        assert_eq!(worst_one_coordinate.required_square_root_coefficient, 28);
        assert_eq!(
            (worst_logarithmic.level, worst_logarithmic.degree),
            (12, 26)
        );
        assert_eq!(worst_logarithmic.restriction_level, 5);
        assert_eq!(worst_logarithmic.packet_count, 32);
        assert_eq!(worst_logarithmic.maximum_packet_size, 64);
        assert_eq!(worst_logarithmic.maximum_absolute_packet_trace, 525_056);
        assert_eq!(worst_logarithmic.packetwise_absolute_trace, 6_433_280);
        assert_eq!(worst_logarithmic.square_root_violation_count, 29);
        assert_eq!(worst_logarithmic.required_square_root_coefficient, 65);

        assert!(hayes_fomenko_restriction_packet_report(1, 1, 3, HayesLimits::default()).is_err());
        assert_eq!(
            hayes_fomenko_restriction_packet_report(
                12,
                5,
                26,
                HayesLimits {
                    max_table_cells: 2_097_151,
                    ..HayesLimits::default()
                }
            ),
            Err(HayesError::ResourceLimit {
                resource: "fomenko_restriction_packet_cells",
                requested: 2_097_152,
                limit: 2_097_151,
            })
        );
    }

    #[test]
    fn binary_power_sum_characters_cover_only_a_thin_quadratic_sector() {
        let limits = HayesLimits {
            max_ell: 16,
            ..HayesLimits::default()
        };
        for level in 1..=16 {
            let report = hayes_power_sum_character_coverage(level, limits).unwrap();
            assert_eq!(report.primitive_character_count, 1 << (level - 1));
            assert_eq!(
                report.primitive_quadratic_character_count,
                if level % 2 == 1 {
                    1 << ((level - 1) / 2)
                } else {
                    0
                }
            );
            assert_eq!(report.primitive_single_monomial_character_count, level % 2);
            assert_eq!(
                report.maximum_power_sum_span_coverage,
                report.primitive_quadratic_character_count
            );
            assert_eq!(
                report.primitive_higher_order_character_count
                    + report.primitive_quadratic_character_count,
                report.primitive_character_count
            );
        }
        let level_eleven = hayes_power_sum_character_coverage(11, limits).unwrap();
        assert_eq!(level_eleven.primitive_character_count, 1_024);
        assert_eq!(level_eleven.primitive_quadratic_character_count, 32);
        assert_eq!(level_eleven.primitive_higher_order_character_count, 992);
        let level_twelve = hayes_power_sum_character_coverage(12, limits).unwrap();
        assert_eq!(level_twelve.primitive_quadratic_character_count, 0);
        assert_eq!(level_twelve.primitive_higher_order_character_count, 2_048);

        assert!(hayes_power_sum_character_coverage(0, limits).is_err());
        assert!(matches!(
            hayes_power_sum_character_coverage(17, limits),
            Err(HayesError::ResourceLimit {
                resource: "ell",
                requested: 17,
                limit: 16
            })
        ));
    }

    #[test]
    fn connected_fibre_product_is_a_signed_virtual_count() {
        let distribution = class_population_distribution(9, 19, HayesLimits::default()).unwrap();
        let report = distribution.connected_fibre_product_report().unwrap();
        assert_eq!((report.ell, report.degree), (9, 19));
        assert_eq!(
            report.centered_second_moment,
            distribution.central_absolute_power_sum(2).unwrap()
        );
        assert_eq!(
            report.centered_fourth_moment,
            distribution.central_absolute_power_sum(4).unwrap()
        );
        assert_eq!(
            report.connected_fourth_cumulant,
            BigInt::from(-2_086_965_956_608_i64)
        );
        assert!(report.raw_quadruple_fibre_count > report.raw_triple_fibre_count);
        assert!(report.raw_triple_fibre_count > report.raw_pair_fibre_count);
    }

    #[test]
    fn pointwise_character_fourth_moment_is_not_the_constrained_cumulant() {
        let distribution = class_population_distribution(7, 15, HayesLimits::default()).unwrap();
        let report = distribution
            .character_fourth_moment_comparison(1 << 14)
            .unwrap();
        assert_eq!((report.ell, report.degree), (7, 15));
        assert_ne!(
            report.pointwise_character_fourth_moment,
            report.product_constrained_fourth_moment
        );
        assert_eq!(
            report.character_second_moment,
            BigUint::from(1_u16 << 7) * distribution.central_absolute_power_sum(2).unwrap()
        );
        assert_eq!(
            report.single_wick_pairing,
            report.character_second_moment.pow(2)
        );
        assert_eq!(
            report.three_wick_pairings,
            BigUint::from(3_u8) * &report.single_wick_pairing
        );
        assert_eq!(
            BigInt::from(report.product_constrained_fourth_moment.clone())
                - BigInt::from(report.three_wick_pairings.clone()),
            report.connected_product_constrained_numerator
        );
        assert_eq!(
            report.connected_product_constrained_numerator,
            BigInt::from(1_u16 << 14) * distribution.fourth_cumulant_numerator().unwrap()
        );
        assert!(matches!(
            distribution.character_fourth_moment_comparison((1 << 14) - 1),
            Err(HayesError::ResourceLimit {
                resource: "character_fourth_moment_autocorrelation_cells",
                requested,
                limit
            }) if requested == 1 << 14 && limit == (1 << 14) - 1
        ));
    }

    #[test]
    fn connected_top_second_moment_cauchy_is_an_exact_finite_ledger() {
        let limits = HayesLimits::default();
        for degree in [25_usize, 26] {
            let report = connected_top_second_moment_cauchy(12, degree, limits).unwrap();
            assert_eq!(report.first_top_level, 7);
            assert_eq!(report.character_count, BigUint::from(4_032_u16));
            assert!(!report.proves_connected_top_candidate());
            assert_eq!(
                report.maximum_second_moment_for_candidate,
                BigUint::from(4_363_141_380_u64)
            );
            assert_eq!(
                report.required_second_moment_saving_ceiling,
                BigUint::from(if degree == 25 { 304_u16 } else { 633_u16 })
            );
        }
        assert!(connected_top_second_moment_cauchy(12, 24, limits).is_err());
    }

    #[test]
    fn blockwise_verschiebung_embedding_is_an_injective_homomorphism() {
        for target_ell in 1_usize..=6 {
            let target_factors = principal_unit_factors(target_ell);
            let target_order = 1_usize << target_ell;
            let mut conductor_counts = BTreeMap::<Option<usize>, usize>::new();
            for character in 0..target_order {
                *conductor_counts
                    .entry(mixed_radix_character_conductor(character, &target_factors).unwrap())
                    .or_default() += 1;
            }
            assert_eq!(conductor_counts[&None], 1);
            for level in 1..=target_ell {
                assert_eq!(conductor_counts[&Some(level)], 1 << (level - 1));
            }
            for source_ell in 0..=target_ell {
                let source_factors = principal_unit_factors(source_ell);
                let source_order = 1_usize << source_ell;
                let embedded = (0..source_order)
                    .map(|index| {
                        verschiebung_embed_mixed_radix_index(
                            index,
                            &source_factors,
                            &target_factors,
                        )
                        .unwrap()
                    })
                    .collect::<Vec<_>>();
                let mut seen = BTreeMap::new();
                for (source, target) in embedded.iter().copied().enumerate() {
                    assert!(seen.insert(target, source).is_none());
                }
                for left in 0..source_order {
                    for right in 0..source_order {
                        let source_sum =
                            add_mixed_radix_indices(left, right, &source_factors).unwrap();
                        let target_sum = add_mixed_radix_indices(
                            embedded[left],
                            embedded[right],
                            &target_factors,
                        )
                        .unwrap();
                        assert_eq!(embedded[source_sum], target_sum);
                    }
                }
            }
        }
    }

    #[test]
    fn binary_order_two_projection_parseval_is_exact() {
        let limits = HayesLimits::default();
        let failing_translation_bucket =
            binary_berlekamp_order_two_projection_report(9, 11, 8, 8, limits).unwrap();
        assert_eq!(
            failing_translation_bucket.odd_block_degrees,
            vec![1, 3, 5, 7, 9]
        );
        assert_eq!(failing_translation_bucket.character_count, 32);
        assert_eq!(failing_translation_bucket.occupied_bucket_count, 8);
        assert_eq!(
            failing_translation_bucket.projections[0].exact_conductor,
            None
        );
        assert_eq!(
            failing_translation_bucket.projections[0].signed_coset_energy,
            BigUint::from(615_u16)
        );
        let largest = failing_translation_bucket
            .projections
            .iter()
            .max_by_key(|row| &row.signed_coset_energy)
            .unwrap();
        assert_eq!(largest.character_mask, 16);
        assert_eq!(largest.exact_conductor, Some(9));
        assert_eq!(largest.signed_coset_energy, BigUint::from(1_719_u16));
        assert_eq!(
            failing_translation_bucket.conductor_energies,
            vec![
                BinaryOrderTwoConductorEnergy {
                    exact_conductor: None,
                    character_count: 1,
                    projected_energy: BigUint::from(615_u16),
                },
                BinaryOrderTwoConductorEnergy {
                    exact_conductor: Some(1),
                    character_count: 1,
                    projected_energy: BigUint::from(475_u16),
                },
                BinaryOrderTwoConductorEnergy {
                    exact_conductor: Some(3),
                    character_count: 2,
                    projected_energy: BigUint::from(1_106_u16),
                },
                BinaryOrderTwoConductorEnergy {
                    exact_conductor: Some(5),
                    character_count: 4,
                    projected_energy: BigUint::from(2_020_u16),
                },
                BinaryOrderTwoConductorEnergy {
                    exact_conductor: Some(7),
                    character_count: 8,
                    projected_energy: BigUint::from(5_528_u16),
                },
                BinaryOrderTwoConductorEnergy {
                    exact_conductor: Some(9),
                    character_count: 16,
                    projected_energy: BigUint::from(11_088_u16),
                },
            ]
        );
        assert_eq!(
            failing_translation_bucket.total_projected_energy,
            BigUint::from(20_832_u16)
        );
        assert_eq!(
            failing_translation_bucket.witt_parity_fibre_energy,
            BigUint::from(651_u16)
        );
        assert!(matches!(
            binary_berlekamp_order_two_projection_report(9, 11, 0, 8, limits),
            Err(HayesError::InvalidParameter(_))
        ));
        assert!(matches!(
            binary_berlekamp_order_two_projection_report(
                9,
                11,
                8,
                8,
                HayesLimits {
                    max_table_cells: 12_000,
                    ..limits
                },
            ),
            Err(HayesError::ResourceLimit { .. })
        ));
    }

    #[test]
    #[ignore = "extended finite diagnostic; select one row with AXEYUM_BERLEKAMP_PROBE_ELL/D/OFFSET"]
    fn berlekamp_annihilator_energy_extended_probe() {
        let parse = |name: &str| {
            std::env::var(name)
                .unwrap_or_else(|_| panic!("missing {name}"))
                .parse::<usize>()
                .unwrap_or_else(|_| panic!("invalid {name}"))
        };
        let ell = parse("AXEYUM_BERLEKAMP_PROBE_ELL");
        let d = parse("AXEYUM_BERLEKAMP_PROBE_D");
        let endpoint_offset = parse("AXEYUM_BERLEKAMP_PROBE_OFFSET");
        assert!(matches!(endpoint_offset, 1 | 2));
        let endpoint = 2 * ell + endpoint_offset;
        let k = endpoint - d;
        let report =
            binary_berlekamp_annihilator_energy_report(ell, k, d, d, HayesLimits::default())
                .unwrap();
        let involution =
            binary_berlekamp_involution_defect_report(ell, k, d, HayesLimits::default()).unwrap();
        let global_bound = BigUint::from(1_u8) << k;
        let local_bound = BigUint::from(2 * d) * report.worst_bucket_population;
        eprintln!(
            "ell={ell} endpoint={endpoint} d={d} k={k} energy={} global_bound={} worst_square={} worst_population={} local_bound={} exact_involutions={}/{} exact_triangles={} defect_candidate={} defect_signed={} worst_defect={} defect_population={} defect_translation={}",
            report.signed_coset_energy,
            global_bound,
            report.worst_bucket_signed_square,
            report.worst_bucket_population,
            local_bound,
            involution.exactly_sign_reversed_bucket_count,
            involution.occupied_bucket_count,
            involution.exact_triangle_bucket_count,
            involution.finite_defect_candidate_holds,
            involution.worst_bucket_signed_magnitude,
            involution.worst_bucket_minimum_defect,
            involution.worst_bucket_population,
            involution.worst_bucket_translation
        );
        assert!(report.signed_coset_energy <= global_bound);
        assert!(report.worst_bucket_signed_square <= local_bound);
    }

    #[test]
    fn berlekamp_bucket_translations_give_checked_triangle_bounds() {
        let report =
            binary_berlekamp_involution_defect_report(8, 12, 5, HayesLimits::default()).unwrap();
        assert_eq!(report.ell, 8);
        assert_eq!(report.degree, 12);
        assert_eq!(report.interval_degree, 5);
        assert_eq!(report.occupied_bucket_count, 471);
        assert_eq!(report.zero_signed_bucket_count, 95);
        assert_eq!(report.exactly_sign_reversed_bucket_count, 62);
        assert_eq!(report.exact_triangle_bucket_count, 393);
        assert_eq!(report.worst_input_coset, 62);
        assert_eq!(report.worst_inverse_coset, 3);
        assert_eq!(report.worst_bucket_translation, 1);
        assert_eq!(report.worst_bucket_signed_magnitude, 6);
        assert_eq!(report.worst_bucket_minimum_defect, 6);
        assert_eq!(report.worst_bucket_population, 6);
        assert!(report.finite_defect_candidate_holds);

        let failure =
            binary_berlekamp_involution_defect_report(9, 11, 8, HayesLimits::default()).unwrap();
        assert_eq!(failure.occupied_bucket_count, 8);
        assert_eq!(failure.exactly_sign_reversed_bucket_count, 0);
        assert_eq!(failure.exact_triangle_bucket_count, 0);
        assert_eq!(failure.worst_bucket_translation, 104);
        assert_eq!(failure.worst_bucket_signed_magnitude, 6);
        assert_eq!(failure.worst_bucket_minimum_defect, 54);
        assert_eq!(failure.worst_bucket_population, 88);
        assert!(!failure.finite_defect_candidate_holds);
    }

    #[test]
    fn dyadic_auxiliary_projector_has_the_exact_quadratic_radicals() {
        let auxiliary = dyadic_auxiliary_quadratic_projector_report().unwrap();
        assert_eq!(auxiliary.residues.len(), 8);
        for row in &auxiliary.residues {
            assert_eq!(
                row.projector_cyclotomic_basis,
                row.expected_projector_cyclotomic_basis
            );
            if row.discriminant_residue.is_multiple_of(2) {
                assert_eq!(row.radical_size, 4);
                assert!(!row.phase_trivial_on_radical);
                assert_eq!(row.normalized_gauss_cyclotomic_basis, [0; 4]);
            } else {
                assert_eq!(row.radical_size, 2);
                assert!(row.phase_trivial_on_radical);
                assert_ne!(row.normalized_gauss_cyclotomic_basis, [0; 4]);
            }
        }
        assert_eq!(
            auxiliary.residues[1].normalized_gauss_cyclotomic_basis,
            [2, 0, -2, 0]
        );
    }

    #[test]
    fn pinned_dyadic_fibre_rejects_projection_preserving_extensions() {
        let report = pinned_dyadic_fibre_projection_obstruction_report().unwrap();
        assert_eq!(report.polynomial_degree, 11);
        assert_eq!(report.fibre_dimension, 7);
        assert_eq!(report.paired_coordinate_shift, 48);
        assert_eq!(report.full_support_coefficient_mod_eight, 6);
        assert_eq!(
            report.witness,
            DyadicFibreModFourAdditivityWitness {
                left: 1,
                right: 1,
                left_phase_mod_four: 1,
                right_phase_mod_four: 1,
                xor_phase_mod_four: 0,
                expected_xor_phase_mod_four: 2,
            }
        );
    }

    #[test]
    fn second_trace_arf_and_swan_signs_match_binary_factorization() {
        for residue in 0_u8..8 {
            let fourier = binary_dyadic_character_fourier_report(residue).unwrap();
            assert_eq!(fourier.residue, residue);
            assert_eq!(fourier.gauss_sum_basis, fourier.expected_basis);
            assert_eq!(
                fourier.kronecker_two,
                match residue {
                    1 | 7 => 1,
                    3 | 5 => -1,
                    _ => 0,
                }
            );
        }
        assert!(binary_second_trace_arf_report(1, 0).is_err());
        assert!(binary_second_trace_arf_report(0b10, 1).is_err());
        let quadratic = binary_second_trace_arf_report(0b111, 2).unwrap();
        assert_eq!(quadratic.mobius, -1);
        assert_eq!(quadratic.integral_discriminant_mod_eight, Some(5));
        assert_eq!(quadratic.integral_discriminant_residue_mod_eight, 5);
        assert!(quadratic.integral_discriminant_is_odd);
        assert_eq!(quadratic.kronecker_two_discriminant, -1);
        assert_eq!(quadratic.arf_invariant, Some(1));
        assert_eq!(quadratic.arf_degree_correction, 0);
        assert_eq!(quadratic.sign_phase, Some(1));
        let irreducible_cubic = binary_second_trace_arf_report(0b1011, 3).unwrap();
        assert_eq!(irreducible_cubic.mobius, -1);
        assert_eq!(irreducible_cubic.integral_discriminant_mod_eight, Some(1));
        assert_eq!(irreducible_cubic.integral_discriminant_residue_mod_eight, 1);
        assert!(irreducible_cubic.integral_discriminant_is_odd);
        assert_eq!(irreducible_cubic.kronecker_two_discriminant, 1);
        assert_eq!(irreducible_cubic.arf_invariant, Some(1));
        assert_eq!(irreducible_cubic.arf_degree_correction, 1);
        assert_eq!(irreducible_cubic.sign_phase, Some(0));
        let reducible_cubic = binary_second_trace_arf_report(0b1001, 3).unwrap();
        assert_eq!(reducible_cubic.mobius, 1);
        assert_eq!(reducible_cubic.integral_discriminant_mod_eight, Some(5));
        assert_eq!(reducible_cubic.integral_discriminant_residue_mod_eight, 5);
        assert!(reducible_cubic.integral_discriminant_is_odd);
        assert_eq!(reducible_cubic.kronecker_two_discriminant, -1);
        assert_eq!(reducible_cubic.arf_invariant, Some(0));
        assert_eq!(reducible_cubic.arf_degree_correction, 1);
        assert_eq!(reducible_cubic.sign_phase, Some(1));
        let squareful = binary_second_trace_arf_report(0b101, 2).unwrap();
        assert_eq!(squareful.mobius, 0);
        assert_eq!(squareful.integral_discriminant_mod_eight, None);
        assert_eq!(squareful.integral_discriminant_residue_mod_eight, 4);
        assert!(!squareful.integral_discriminant_is_odd);
        assert_eq!(squareful.kronecker_two_discriminant, 0);
        assert_eq!(squareful.arf_invariant, None);
        assert_eq!(squareful.sign_phase, None);
        for degree in 1..=10 {
            for middle in 0..1_u64 << (degree - 1) {
                let polynomial = (1_u64 << degree) | (middle << 1) | 1;
                let report = binary_second_trace_arf_report(polynomial, degree).unwrap();
                assert_eq!(report.polynomial, polynomial);
                assert_eq!(report.degree, degree);
                assert_eq!(
                    report.trace_form_dimension,
                    if degree.is_multiple_of(2) {
                        degree
                    } else {
                        degree - 1
                    }
                );
                if report.mobius == 0 {
                    assert!(
                        report
                            .integral_discriminant_residue_mod_eight
                            .is_multiple_of(2)
                    );
                    assert!(!report.integral_discriminant_is_odd);
                    assert_eq!(report.kronecker_two_discriminant, 0);
                    assert_eq!(report.integral_discriminant_mod_eight, None);
                    assert_eq!(report.arf_invariant, None);
                    assert_eq!(report.sign_phase, None);
                } else {
                    assert_eq!(
                        report.integral_discriminant_mod_eight,
                        Some(report.integral_discriminant_residue_mod_eight)
                    );
                    assert!(report.integral_discriminant_is_odd);
                    assert_eq!(report.kronecker_two_discriminant.unsigned_abs(), 1);
                    assert!(matches!(
                        report.integral_discriminant_mod_eight,
                        Some(1 | 5)
                    ));
                    assert_eq!(report.polar_rank, report.trace_form_dimension);
                    assert_eq!(report.radical_dimension, 0);
                    assert_eq!(
                        report.arf_invariant.unwrap() ^ report.arf_degree_correction,
                        report.sign_phase.unwrap()
                    );
                }
            }
        }
    }

    #[test]
    fn second_trace_difference_types_are_exact_in_pinned_buckets() {
        for (
            ell,
            degree,
            interval_degree,
            expected_squarefree,
            expected_pairs,
            expected_types,
            expected_minimum_rank,
            expected_witnesses,
        ) in [
            (6, 8, 5, 85, 410, 9, 0, 1),
            (7, 9, 6, 171, 1_856, 9, 0, 2),
            (8, 10, 7, 341, 7_100, 10, 2, 1),
        ] {
            let row = binary_second_trace_bucket_difference_report(
                ell,
                degree,
                interval_degree,
                HayesLimits::default(),
            )
            .unwrap();
            assert_eq!(row.occupied_bucket_count, 8);
            assert_eq!(row.squarefree_count, expected_squarefree);
            assert_eq!(row.unordered_pair_count, expected_pairs);
            assert_eq!(row.types.len(), expected_types);
            assert_eq!(row.minimum_nonzero_gauss_rank, Some(expected_minimum_rank));
            assert_eq!(row.minimum_rank_witnesses.len(), expected_witnesses);
        }
        let report =
            binary_second_trace_bucket_difference_report(9, 11, 8, HayesLimits::default()).unwrap();
        assert_eq!(report.occupied_bucket_count, 8);
        assert_eq!(report.squarefree_count, 683);
        assert_eq!(report.unordered_pair_count, 28_830);
        assert_eq!(report.types.len(), 10);
        assert_eq!(report.minimum_nonzero_gauss_rank, Some(2));
        assert_eq!(report.minimum_rank_witnesses.len(), 5);
        assert_eq!(
            report
                .minimum_rank_witnesses
                .iter()
                .map(|row| row.polynomial_difference)
                .collect::<Vec<_>>(),
            vec![8, 8, 10, 364, 10]
        );
        assert_eq!(
            report.types.iter().map(|row| row.pair_count).sum::<u128>(),
            report.unordered_pair_count
        );
        assert!(
            binary_second_trace_bucket_difference_report(9, 11, 0, HayesLimits::default()).is_err()
        );
    }

    #[test]
    fn connected_witt_gauss_reconstruction_detects_a_phase_mutation() {
        for modulus in [PRIME_ONE, PRIME_TWO] {
            let root = mod_pow(PRIMITIVE_ROOT, (modulus - 1) / 8, modulus);
            let mut phases = [1_u64, 3, 5, 7]
                .into_iter()
                .map(|exponent| vec![mod_pow(root, exponent, modulus)])
                .collect::<Vec<_>>();
            assert!(check_connected_witt_gauss_identity(&[1], &phases, modulus).is_ok());
            phases[0][0] = add_mod(phases[0][0], 1, modulus);
            assert!(check_connected_witt_gauss_identity(&[1], &phases, modulus).is_err());
        }
    }

    #[test]
    fn discriminant_mod_eight_anf_reconstructs_every_coefficient_cube() {
        let limits = HayesLimits::default();
        assert!(binary_discriminant_anf_report(0, limits).is_err());
        for degree in 1..=10 {
            let report = binary_discriminant_anf_report(degree, limits).unwrap();
            assert_eq!(report.polynomial_degree, degree);
            assert_eq!(report.variable_count, degree - 1);
            assert_eq!(report.coefficient_count, 1 << (degree - 1));
            assert!(!report.full_support_coefficient_mod_eight.is_multiple_of(2));
            assert_eq!(report.max_odd_support_degree, Some(degree - 1));
        }
        assert!(matches!(
            binary_discriminant_anf_report(
                10,
                HayesLimits {
                    max_table_cells: 100,
                    ..limits
                }
            ),
            Err(HayesError::ResourceLimit {
                resource: "discriminant_anf_cells",
                requested: 512,
                limit: 100,
            })
        ));
    }

    fn assert_pinned_connected_witt_spectrum(report: &BinaryDyadicAutocorrelationFibreReport) {
        let spectrum = &report.connected_witt_spectrum;
        assert_eq!(spectrum.ell, 9);
        assert_eq!(spectrum.normalized_parameter_count, 214);
        assert_eq!(spectrum.embedded_support_count, 184);
        assert_eq!(spectrum.signed_total, -68);
        assert_eq!(spectrum.embedded_absolute_sum, 3_776);
        assert_eq!(spectrum.spatial_second_moment, BigUint::from(126_568_u32));
        assert_eq!(
            spectrum.spectral_second_moment,
            BigUint::from(64_802_816_u32)
        );
        assert_eq!(
            spectrum.spectral_fourth_moment,
            BigUint::from(20_409_844_301_824_u64)
        );
        assert_eq!(
            spectrum.phase_residue_totals,
            [52_596, 28_796, 0, 0, 19_792, 28_864, 0, 0]
        );
        assert_eq!(
            spectrum.phase_complementarity_identity,
            BigUint::from(13_942_624_u32)
        );
        assert_eq!(
            spectrum.phase_complementarity_max_off_identity,
            BigUint::from(10_785_296_u32)
        );
        assert_eq!(
            spectrum.phase_complementarity_square_sum,
            BigUint::from(5_227_607_974_543_488_u64)
        );
        assert_ne!(
            spectrum.phase_complementarity_square_sum,
            spectrum.phase_complementarity_identity.pow(2)
        );
        assert_eq!(
            spectrum
                .additive_phase_spectra
                .iter()
                .map(|row| (
                    row.multiplier,
                    row.prime_one_nonzero_count,
                    row.prime_two_nonzero_count,
                    row.zero_status_disagreement_count,
                ))
                .collect::<Vec<_>>(),
            vec![
                (1, 512, 512, 0),
                (3, 512, 512, 0),
                (5, 512, 512, 0),
                (7, 512, 512, 0)
            ]
        );
        assert_eq!(spectrum.conductor_spectra.len(), 10);
        for (level, row) in spectrum.conductor_spectra.iter().enumerate() {
            assert_eq!(row.exact_conductor, (level != 0).then_some(level));
            assert_eq!(row.character_count, 1_usize << level.saturating_sub(1));
            assert_eq!(row.prime_one_nonzero_count, row.character_count);
            assert_eq!(row.prime_two_nonzero_count, row.character_count);
            assert_eq!(row.jointly_nonzero_count, row.character_count);
            assert_eq!(row.zero_status_disagreement_count, 0);
        }
    }

    #[test]
    fn connected_witt_phase_complementarity_detects_off_identity_mass() {
        let target = principal_unit_structure(2, HayesLimits::default()).unwrap();
        let mut phases = vec![[0_u128; 8]; target.group_order];
        phases[0][0] = 1;
        let (identity, max_off, square_sum) =
            connected_witt_phase_complementarity(&phases, &target).unwrap();
        assert_eq!(identity, BigUint::from(1_u8));
        assert_eq!(max_off, BigUint::from(0_u8));
        assert_eq!(square_sum, identity.pow(2));

        phases[1][0] = 1;
        let (identity, max_off, square_sum) =
            connected_witt_phase_complementarity(&phases, &target).unwrap();
        assert!(max_off > BigUint::from(0_u8));
        assert!(square_sum > identity.pow(2));
    }

    #[test]
    fn generalized_bent_test_detects_a_phase_mutation() {
        let mut phase = [0_u8, 0, 0, 4];
        assert!(mod_eight_phase_is_generalized_bent(&phase));
        phase[3] = 0;
        assert!(!mod_eight_phase_is_generalized_bent(&phase));
    }

    #[test]
    fn dyadic_product_discriminants_reconstruct_affine_shift_fibres() {
        let report =
            binary_dyadic_autocorrelation_fibre_report(9, 11, 8, HayesLimits::default()).unwrap();
        assert_eq!(report.nonzero_shift_count, 255);
        assert_eq!(report.fibre_count, 18_884);
        assert_eq!(report.total_fibre_points, 130_048);
        assert_eq!(report.max_fibre_dimension, 8);
        assert_eq!(report.at_most_quadratic_fibre_count, 16_587);
        assert_eq!(
            report.at_most_quadratic_fibre_points + report.nonquadratic_fibre_points,
            report.total_fibre_points
        );
        assert_eq!(report.generalized_bent_fibre_count, 0);
        assert_eq!(report.generalized_bent_fibre_points, 0);
        assert_eq!(report.nonquadratic_fibre_points, 61_264);
        assert_eq!(report.nonquadratic_signed_correlation, -202);
        assert_eq!(report.nonquadratic_absolute_correlation, 8_622);
        assert_eq!(
            &report.at_most_quadratic_correlation_square_sum
                + &report.nonquadratic_correlation_square_sum,
            report.fibre_correlation_square_sum
        );
        assert_eq!(report.fibrewise_absolute_correlation, 33_680);
        assert_eq!(
            report.fibre_correlation_square_sum,
            BigUint::from(120_680_u32)
        );
        assert_eq!(report.nonzero_fibre_correlation_count, 12_915);
        assert_eq!(report.power_of_two_magnitude_fibre_count, 12_456);
        assert_eq!(
            report.within_fibre_off_diagonal_correlation(),
            BigInt::from(-9_368)
        );
        assert!(report.satisfies_nonpositive_within_fibre_correlation());
        assert_eq!(report.shift_inverse_pair_count, 4_721);
        assert_eq!(report.shift_inverse_pairwise_absolute_correlation, 16_972);
        assert_eq!(report.normalized_parameter_count, 214);
        assert_eq!(report.normalized_parameterwise_absolute_correlation, 3_956);
        assert_eq!(report.valuationwise_absolute_correlation, 388);
        assert_pinned_connected_witt_spectrum(&report);
        assert_eq!(
            report
                .valuation_correlations
                .iter()
                .map(|row| (
                    row.valuation,
                    row.normalized_parameter_count,
                    row.parameterwise_absolute_correlation,
                    row.signed_correlation,
                ))
                .collect::<Vec<_>>(),
            vec![
                (1, 128, 2_286, 70),
                (2, 60, 998, 90),
                (3, 12, 330, -30),
                (4, 7, 258, -138),
                (5, 3, 30, -6),
                (6, 2, 38, -38),
                (7, 1, 16, -16),
                (8, 1, 0, 0),
            ]
        );
        assert_eq!(report.full_degree_fibre_count, 5_540);
        assert_eq!(report.max_phase_support_degree, 7);
        assert_eq!(report.off_diagonal_signed_correlation, -68);
        assert_eq!(
            report.worst_fibre,
            Some(BinaryDyadicAutocorrelationFibreWitness {
                shift: 96,
                input_coset: 0,
                inverse_difference: 192,
                fibre_dimension: 7,
                max_odd_support_degree: Some(6),
                max_twice_odd_support_degree: Some(7),
                max_four_support_degree: Some(6),
                signed_correlation: -10,
            })
        );
        assert!(
            binary_dyadic_autocorrelation_fibre_report(9, 11, 0, HayesLimits::default()).is_err()
        );
    }

    #[test]
    #[ignore = "extended finite diagnostic; select one row with AXEYUM_DYADIC_PROBE_ELL/D/OFFSET"]
    fn dyadic_parameter_aggregation_extended_probe() {
        let parse = |name: &str| {
            std::env::var(name)
                .unwrap_or_else(|_| panic!("missing {name}"))
                .parse::<usize>()
                .unwrap_or_else(|_| panic!("invalid {name}"))
        };
        let ell = parse("AXEYUM_DYADIC_PROBE_ELL");
        let d = parse("AXEYUM_DYADIC_PROBE_D");
        let offset = parse("AXEYUM_DYADIC_PROBE_OFFSET");
        assert!(matches!(offset, 1 | 2));
        let degree = 2 * ell + offset - d;
        let max_table_cells = std::env::var("AXEYUM_DYADIC_PROBE_MAX_CELLS")
            .map_or(Ok(HayesLimits::default().max_table_cells), |value| {
                value
                    .parse::<usize>()
                    .map_err(|_| "invalid AXEYUM_DYADIC_PROBE_MAX_CELLS")
            })
            .unwrap();
        let report = binary_dyadic_autocorrelation_fibre_report(
            ell,
            degree,
            d,
            HayesLimits {
                max_table_cells,
                ..HayesLimits::default()
            },
        )
        .unwrap();
        eprintln!(
            "ell={ell} d={d} offset={offset} k={degree} offdiag={} fibre_abs={} fibre_l2_square={} fibre_points={} within_fibre_offdiag={} nonzero_fibres={} power_two_fibres={} counting_candidate={} quadratic_l2_square={} quadratic_points={} nonquadratic_l2_square={} nonquadratic_points={} pair_abs={} normalized_abs={} valuation_abs={} gbent_fibres={} gbent_points={} witt_support={} witt_abs={} witt_m2={} witt_fourier_m2={} witt_fourier_m4={} phase_residues={:?} phase_comp_identity={} phase_comp_max_off={} phase_comp_square_sum={} additive_phases={:?} witt_conductors={:?} layers={:?}",
            report.off_diagonal_signed_correlation,
            report.fibrewise_absolute_correlation,
            report.fibre_correlation_square_sum,
            report.total_fibre_points,
            report.within_fibre_off_diagonal_correlation(),
            report.nonzero_fibre_correlation_count,
            report.power_of_two_magnitude_fibre_count,
            report.satisfies_nonpositive_within_fibre_correlation(),
            report.at_most_quadratic_correlation_square_sum,
            report.at_most_quadratic_fibre_points,
            report.nonquadratic_correlation_square_sum,
            report.nonquadratic_fibre_points,
            report.shift_inverse_pairwise_absolute_correlation,
            report.normalized_parameterwise_absolute_correlation,
            report.valuationwise_absolute_correlation,
            report.generalized_bent_fibre_count,
            report.generalized_bent_fibre_points,
            report.connected_witt_spectrum.embedded_support_count,
            report.connected_witt_spectrum.embedded_absolute_sum,
            report.connected_witt_spectrum.spatial_second_moment,
            report.connected_witt_spectrum.spectral_second_moment,
            report.connected_witt_spectrum.spectral_fourth_moment,
            report.connected_witt_spectrum.phase_residue_totals,
            report
                .connected_witt_spectrum
                .phase_complementarity_identity,
            report
                .connected_witt_spectrum
                .phase_complementarity_max_off_identity,
            report
                .connected_witt_spectrum
                .phase_complementarity_square_sum,
            report.connected_witt_spectrum.additive_phase_spectra,
            report.connected_witt_spectrum.conductor_spectra,
            report.valuation_correlations,
        );
    }

    #[test]
    #[ignore = "extended finite diagnostic; select one row with AXEYUM_DYADIC_PROBE_ELL/D/OFFSET"]
    fn valuation_layer_square_root_probe() {
        let parse = |name: &str| {
            std::env::var(name)
                .unwrap_or_else(|_| panic!("missing {name}"))
                .parse::<usize>()
                .unwrap_or_else(|_| panic!("invalid {name}"))
        };
        let ell = parse("AXEYUM_DYADIC_PROBE_ELL");
        let d = parse("AXEYUM_DYADIC_PROBE_D");
        let offset = parse("AXEYUM_DYADIC_PROBE_OFFSET");
        assert!(matches!(offset, 1 | 2));
        let degree = 2 * ell + offset - d;
        let report =
            binary_berlekamp_annihilator_energy_report(ell, degree, d, d, HayesLimits::default())
                .unwrap();
        let mut layers = BTreeMap::<usize, i128>::new();
        for row in &report.shift_correlations {
            if let Some(valuation) = row.valuation {
                *layers.entry(valuation).or_default() += row.signed_correlation;
            }
        }
        let valuation_absolute = layers
            .values()
            .map(|value| value.unsigned_abs())
            .sum::<u128>();
        eprintln!(
            "ell={ell} d={d} offset={offset} k={degree} offdiag={} valuation_abs={valuation_absolute} layers={layers:?}",
            report.off_diagonal_signed_correlation,
        );
    }

    #[test]
    fn constant_one_squarefree_count_satisfies_its_exact_recurrence() {
        assert!(binary_constant_one_squarefree_count(0).is_err());
        assert_eq!(binary_constant_one_squarefree_count(1).unwrap(), 1);
        for degree in 2..=63 {
            let current = binary_constant_one_squarefree_count(degree).unwrap();
            let previous = binary_constant_one_squarefree_count(degree - 1).unwrap();
            assert_eq!(current + previous, 1_u128 << (degree - 1));
        }
    }

    #[test]
    fn truncated_artin_schreier_kernel_formula_is_exact() {
        assert!(binary_artin_schreier_kernel_report(0, None).is_err());
        for modulus_degree in 1_usize..=12 {
            let mask = (1_u64 << modulus_degree) - 1;
            for shift in 0_u64..=mask {
                let valuation = (shift != 0).then(|| shift.trailing_zeros() as usize);
                let report =
                    binary_artin_schreier_kernel_report(modulus_degree, valuation).unwrap();
                let direct = (0_u64..=mask)
                    .filter(|&value| polynomial_multiply_packed(value, value ^ shift) & mask == 0)
                    .count() as u128;
                assert_eq!(
                    direct, report.kernel_size,
                    "r={modulus_degree}, h={shift:#b}, v={valuation:?}"
                );
            }
        }
    }

    #[test]
    fn inverse_difference_fibres_are_shift_only_parallelograms() {
        assert!(binary_inverse_difference_parallelogram_report(0, 1, 0, 0).is_err());
        assert!(binary_inverse_difference_parallelogram_report(3, 0, 0, 0).is_err());
        assert!(binary_inverse_difference_parallelogram_report(3, 1, 1, 0).is_err());
        for ell in 1_usize..=6 {
            let group_order = 1_usize << ell;
            for middle in 0..group_order {
                let input = 1_u64 | ((middle as u64) << 1);
                for first in 0..group_order {
                    for second in 0..group_order {
                        let report = binary_inverse_difference_parallelogram_report(
                            ell,
                            input,
                            (first as u64) << 1,
                            (second as u64) << 1,
                        )
                        .unwrap();
                        assert_eq!(
                            report.inverse_differences_equal,
                            report.annihilator_product_vanishes
                        );
                    }
                }
            }
        }

        let ramified = binary_inverse_difference_parallelogram_report(3, 1, 0b100, 0b010).unwrap();
        assert!(ramified.inverse_differences_equal);
        let mask = (1_u64 << 4) - 1;
        assert_ne!(
            polynomial_multiply_packed(0b010, 0b010 ^ 0b100) & mask,
            0,
            "dropping the ramified factor h must change the criterion"
        );
    }

    #[test]
    fn berlekamp_random_scale_energy_would_move_the_endpoint_tail() {
        let ell = 300;
        let odd = 2 * ell + 1;
        let even = odd + 1;
        let first = |endpoint| {
            (1..ell).find(|&d| {
                let k = endpoint - d;
                binary_berlekamp_aggregate_exponent_ledger(
                    ell,
                    endpoint,
                    d,
                    d,
                    u128::try_from(16 * k).unwrap(),
                    u128::try_from(16 * (k - 1)).unwrap(),
                )
                .unwrap()
                .closes_strictly()
            })
        };
        assert_eq!(first(odd), Some(207));
        assert_eq!(first(even), Some(208));

        let boundary = binary_berlekamp_aggregate_exponent_ledger(
            ell,
            odd,
            206,
            206,
            16 * (odd - 206) as u128,
            16 * (odd - 207) as u128,
        )
        .unwrap();
        assert_eq!(boundary.deficit_thirty_seconds, -16);
        let first_strict = binary_berlekamp_aggregate_exponent_ledger(
            ell,
            odd,
            207,
            207,
            16 * (odd - 207) as u128,
            16 * (odd - 208) as u128,
        )
        .unwrap();
        assert_eq!(first_strict.deficit_thirty_seconds, 32);

        // The more local target b_(C,D)^2 <= 2d * #bucket implies
        // E(k) <= 2d Q_k < d 2^k.  Its polynomial loss moves the same
        // pointwise tail only slightly, and is a plausible character-sum
        // lemma rather than a bare global-energy conjecture.
        let first_from_local_square_root = |endpoint| {
            (1..ell).find(|&d| {
                let k = endpoint - d;
                let loss_bits = if d == 1 {
                    0
                } else {
                    usize::BITS as usize - (d - 1).leading_zeros() as usize
                };
                binary_berlekamp_aggregate_exponent_ledger(
                    ell,
                    endpoint,
                    d,
                    d,
                    16 * (k + loss_bits) as u128,
                    16 * (k - 1 + loss_bits) as u128,
                )
                .unwrap()
                .closes_strictly()
            })
        };
        assert_eq!(first_from_local_square_root(odd), Some(210));
        assert_eq!(first_from_local_square_root(even), Some(210));
    }

    #[test]
    fn inverse_additive_orthogonality_recovers_convolution_fibres() {
        let limits = HayesLimits::default();
        for ell in 2_usize..=9 {
            for degree in [2 * ell + 1, 2 * ell + 2] {
                let convolution = identity_class_mobius_convolution(ell, degree, limits).unwrap();
                for term in convolution.terms {
                    let spectrum = inverse_additive_mobius_spectrum(
                        ell,
                        degree - term.interval_degree,
                        limits,
                    )
                    .unwrap();
                    let fibre = spectrum
                        .inverse_interval_fibre_sum(term.interval_degree)
                        .unwrap();
                    assert_eq!(
                        i128::try_from(term.interval_degree).unwrap() * fibre,
                        term.value
                    );
                }
            }
        }

        let report = inverse_additive_mobius_spectrum(4, 9, limits).unwrap();
        assert!(matches!(
            report.inverse_interval_fibre_sum(0),
            Err(HayesError::InvalidParameter(_))
        ));
        assert!(matches!(
            report.inverse_interval_fibre_sum(4),
            Err(HayesError::InvalidParameter(_))
        ));
    }

    #[test]
    fn inverse_mobius_fourier_regroup_preserves_cross_order_cancellation() {
        let limits = HayesLimits::default();
        for ell in 2_usize..=8 {
            for degree in [2 * ell + 1, 2 * ell + 2] {
                let report = inverse_mobius_fourier_regroup(ell, degree, limits).unwrap();
                let denominator = 1_u128 << ell;
                assert_eq!(report.denominator, denominator);
                assert_eq!(report.layers.len(), ell + 1);
                assert_eq!(
                    report
                        .layers
                        .iter()
                        .map(|layer| layer.frequency_count)
                        .sum::<u128>(),
                    denominator
                );
                for layer in &report.layers[..ell] {
                    assert_eq!(
                        layer.frequency_count,
                        1_u128 << (ell - layer.annihilator_depth - 1)
                    );
                }
                assert_eq!(report.layers[ell].frequency_count, 1);
                assert_eq!(
                    report.regrouped_numerator,
                    report.discrepancy * i128::try_from(denominator).unwrap()
                );
                assert!(report.cellwise_absolute_numerator >= report.orderwise_absolute_numerator);
                assert!(report.cellwise_absolute_numerator >= report.layerwise_absolute_numerator);
            }
        }
    }

    #[test]
    fn connected_top_fourier_regroup_combines_conductors_and_orders() {
        let limits = HayesLimits::default();
        let expected = [
            (
                17_usize,
                11_264_i128,
                313_952_u128,
                60_416_u128,
                162_672_u128,
                71_280_u128,
                1_541_548_032_u128,
                1_425_u128,
                vec![0_i128, -2_560, 5_952, 896, -944, 13_904, 20_520, -26_504, 0],
            ),
            (
                18,
                18_176,
                415_264,
                43_776,
                205_856,
                70_208,
                1_604_489_216,
                1_483,
                vec![
                    0_i128, 2_560, 256, 10_624, -14_112, 23_008, 7_744, -11_904, 0,
                ],
            ),
        ];
        for (
            degree,
            expected_trace,
            expected_cellwise,
            expected_orderwise,
            expected_frequencywise,
            expected_layerwise,
            expected_square_sum,
            expected_saving,
            expected_layers,
        ) in expected
        {
            let report = connected_top_inverse_mobius_fourier_regroup(8, degree, limits).unwrap();
            assert_eq!(report.first_top_level, 4);
            assert_eq!(report.coarse_level, 3);
            assert_eq!(report.cancelled_coarse_frequency_count, 8);
            assert_eq!(report.high_frequency_support_bound, 248);
            assert_eq!(report.connected_trace, expected_trace);
            assert_eq!(report.cellwise_absolute_numerator, expected_cellwise);
            assert_eq!(report.orderwise_absolute_numerator, expected_orderwise);
            assert_eq!(
                report.frequencywise_absolute_numerator,
                expected_frequencywise
            );
            assert_eq!(report.layerwise_absolute_numerator, expected_layerwise);
            assert_eq!(
                report
                    .layers
                    .iter()
                    .map(|layer| layer.weighted_numerator)
                    .collect::<Vec<_>>(),
                expected_layers
            );
            assert!(report.cellwise_absolute_numerator >= report.orderwise_absolute_numerator);
            assert!(report.cellwise_absolute_numerator >= report.frequencywise_absolute_numerator);
            assert!(report.frequencywise_absolute_numerator >= report.layerwise_absolute_numerator);
            assert_eq!(
                report.frequency_square_sum,
                BigUint::from(expected_square_sum)
            );
            assert_eq!(
                report.frequency_cauchy_bound_square,
                BigUint::from(expected_square_sum) * BigUint::from(248_u16)
            );
            assert_eq!(
                report.connected_allowance_square,
                BigUint::from(268_435_456_u32)
            );
            assert_eq!(
                report.maximum_frequency_square_sum_for_candidate,
                BigUint::from(1_082_401_u32)
            );
            assert_eq!(
                report.required_frequency_square_sum_saving_ceiling,
                BigUint::from(expected_saving)
            );
            assert!(!report.frequency_cauchy_proves_candidate());
        }
        for ell in 6_usize..=8 {
            for degree in [2 * ell + 1, 2 * ell + 2] {
                connected_top_inverse_mobius_fourier_regroup(ell, degree, limits).unwrap();
            }
        }
        assert!(connected_top_inverse_mobius_fourier_regroup(4, 9, limits).is_err());
    }

    #[test]
    fn identity_class_mobius_convolution_reconstructs_endpoints() {
        let limits = HayesLimits::default();
        for ell in 2_usize..=9 {
            let exact = endpoint_discrepancies(ell, limits).unwrap();
            for (degree, expected) in [(2 * ell + 1, exact.odd), (2 * ell + 2, exact.even)] {
                let report = identity_class_mobius_convolution(ell, degree, limits).unwrap();
                assert_eq!(report.discrepancy, expected);
                assert_eq!(report.terms.len(), ell - 1);
                assert_eq!(
                    report.terms.iter().map(|term| term.value).sum::<i128>(),
                    expected
                );
            }
        }

        let odd = identity_class_mobius_convolution(8, 17, limits).unwrap();
        assert_eq!(odd.uniform_mean, 512);
        assert_eq!(odd.mangoldt_population, 562);
        assert_eq!(odd.discrepancy, 50);
        assert_eq!(
            odd.terms.iter().map(|term| term.value).collect::<Vec<_>>(),
            vec![-1, 36, -9, 8, 40, 60, -84]
        );
        let even = identity_class_mobius_convolution(8, 18, limits).unwrap();
        assert_eq!(even.discrepancy, 75);
        assert_eq!(
            even.terms.iter().map(|term| term.value).collect::<Vec<_>>(),
            vec![-20, 36, 39, 0, -20, 54, -14]
        );
    }

    #[test]
    fn identity_class_mobius_convolution_terms_match_direct_factorization() {
        let limits = HayesLimits::default();
        let mut inverse_mutation_detected = false;
        let mut weight_mutation_detected = false;
        for ell in 2_usize..=5 {
            let unit_to_index = principal_unit_index_map(ell);
            let mut direct_rows = BTreeMap::new();
            for degree in ell + 2..=2 * ell + 1 {
                direct_rows.insert(degree, direct_class_mobius_distribution(ell, degree));
            }
            for degree in [2 * ell + 1, 2 * ell + 2] {
                let report = identity_class_mobius_convolution(ell, degree, limits).unwrap();
                for term in &report.terms {
                    let mobius = &direct_rows[&(degree - term.interval_degree)];
                    let mut inverse_fibre = 0_i128;
                    let mut uninverted_fibre = 0_i128;
                    for tail in 0..1_u64 << term.interval_degree {
                        let unit = 1 | (tail << 1);
                        inverse_fibre += mobius[unit_to_index[&unit_inverse(unit, ell)]];
                        uninverted_fibre += mobius[unit_to_index[&unit]];
                    }
                    let weight = i128::try_from(term.interval_degree).unwrap();
                    assert_eq!(term.value, weight * inverse_fibre);
                    inverse_mutation_detected |= weight * uninverted_fibre != term.value;
                    weight_mutation_detected |= inverse_fibre != term.value;
                }
            }
        }
        assert!(inverse_mutation_detected);
        assert!(weight_mutation_detected);
    }

    #[test]
    fn identity_class_mobius_convolution_declines_invalid_inputs() {
        let limits = HayesLimits::default();
        assert!(matches!(
            identity_class_mobius_convolution(0, 3, limits),
            Err(HayesError::InvalidParameter(_))
        ));
        assert_eq!(
            identity_class_mobius_convolution(3, 3, limits),
            Err(HayesError::InvalidParameter(
                "Mobius convolution decomposition requires degree>=ell+1".to_owned()
            ))
        );
        assert!(matches!(
            identity_class_mobius_convolution(
                3,
                60,
                HayesLimits {
                    max_degree: 60,
                    ..limits
                }
            ),
            Err(HayesError::InvalidParameter(_))
        ));
    }

    #[test]
    fn connected_order_cumulant_reconstructs_both_endpoints() {
        let limits = HayesLimits::default();
        for degree in [9, 10] {
            let report = connected_order_cumulant_report(4, degree, limits).unwrap();
            assert_eq!(report.order_count, 3);
            assert_eq!(report.cells.len(), 15);
            assert_eq!(
                report.reconstructed_fourth_cumulant_numerator,
                report.direct_fourth_cumulant_numerator
            );
            assert!(report.cells.iter().all(|cell| {
                cell.interval_degrees
                    .windows(2)
                    .all(|pair| pair[0] <= pair[1])
                    && matches!(cell.permutation_multiplicity, 1 | 4 | 6 | 12 | 24)
            }));
        }
        assert!(connected_order_cumulant_report(4, 8, limits).is_err());
        assert!(matches!(
            connected_order_cumulant_report(
                4,
                9,
                HayesLimits {
                    max_table_cells: 463,
                    ..limits
                }
            ),
            Err(HayesError::ResourceLimit {
                resource: "connected_order_cumulant_cells",
                requested: 464,
                limit: 463,
            })
        ));
    }

    #[test]
    #[ignore = "extended finite diagnostic; select ell/offset with AXEYUM_ORDER_CUMULANT_ELL/OFFSET"]
    fn connected_order_cumulant_extended_probe() {
        let ell = std::env::var("AXEYUM_ORDER_CUMULANT_ELL")
            .expect("missing AXEYUM_ORDER_CUMULANT_ELL")
            .parse::<usize>()
            .expect("invalid AXEYUM_ORDER_CUMULANT_ELL");
        let offset = std::env::var("AXEYUM_ORDER_CUMULANT_OFFSET")
            .expect("missing AXEYUM_ORDER_CUMULANT_OFFSET")
            .parse::<usize>()
            .expect("invalid AXEYUM_ORDER_CUMULANT_OFFSET");
        assert!(matches!(offset, 1 | 2));
        let degree = 2 * ell + offset;
        let report = connected_order_cumulant_report(ell, degree, HayesLimits::default()).unwrap();
        let mut ranked = report.cells.iter().collect::<Vec<_>>();
        ranked.sort_by(|left, right| {
            right
                .connected_numerator
                .magnitude()
                .cmp(left.connected_numerator.magnitude())
        });
        eprintln!(
            "ell={ell} degree={degree} cells={} K4={} top={:?}",
            report.cells.len(),
            report.direct_fourth_cumulant_numerator,
            ranked
                .into_iter()
                .take(12)
                .map(|cell| (
                    cell.interval_degrees,
                    cell.permutation_multiplicity,
                    cell.connected_numerator.clone(),
                ))
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn identity_class_irreducible_count_removes_prime_powers_exactly() {
        let expected = [
            1_u128, 1, 1, 2, 3, 2, 4, 7, 4, 12, 6, 19, 20, 28, 33, 59, 49, 101,
        ];
        for (degree, expected_count) in (3..=20).zip(expected) {
            let ell = (degree - 1) / 2;
            let report =
                identity_class_irreducible_count(ell, degree, HayesLimits::default()).unwrap();
            assert_eq!(report.ell, ell);
            assert_eq!(report.degree, degree);
            assert_eq!(report.irreducible_count, expected_count);
            assert!(report.proves_irreducible_exists());
            assert_eq!(
                report.mangoldt_population,
                report.proper_prime_power_population + degree as u128 * expected_count
            );
        }

        let even = identity_class_irreducible_count(5, 12, HayesLimits::default()).unwrap();
        assert!(even.proper_prime_power_population != 0);
        assert_eq!(even.irreducible_count, 12);
    }

    #[test]
    fn odd_endpoint_single_ntt_matches_two_prime_reconstruction() {
        for ell in 1..=12 {
            let single =
                odd_endpoint_irreducible_count_single_ntt(ell, HayesLimits::default()).unwrap();
            let full =
                identity_class_irreducible_count(ell, 2 * ell + 1, HayesLimits::default()).unwrap();
            assert_eq!(single, full);
        }
    }

    #[test]
    fn odd_endpoint_two_adic_report_replays_residue_and_precision() {
        let expected_mod_8 = [1_u8, 1, 3, 4, 4, 6, 4, 1, 1, 4, 3, 6];
        let expected_valuations = [0_u32, 0, 0, 2, 2, 1, 2, 0, 0, 2, 0, 1];
        for (ell, (expected_residue, expected_valuation)) in
            (1..=12).zip(expected_mod_8.into_iter().zip(expected_valuations))
        {
            let report = odd_endpoint_two_adic_report(ell, HayesLimits::default()).unwrap();
            assert_eq!(report.irreducible_residue_mod_8, expected_residue);
            assert_eq!(
                report.irreducible_two_adic_valuation,
                Some(expected_valuation)
            );
            assert!(report.proves_odd_endpoint_by_modulo_eight());
            assert_eq!(report.carlitz_galois_group_order, 1_u128 << ell);
            assert_eq!(
                report.ramified_place_stabilizer_order,
                report.carlitz_galois_group_order
            );
            assert_eq!(report.carlitz_two_rank, 0);
            assert_eq!(report.required_curve_point_modulus_bits, ell + 3);
            assert_eq!(
                report.curve_point_count,
                1 + report.carlitz_galois_group_order * report.mangoldt_population
            );
            let population_mod_8 =
                ((report.curve_point_residue_at_required_precision - 1) >> ell) % 8;
            let inverse_degree_mod_8 = (report.degree % 8) as u128;
            assert_eq!(
                ((population_mod_8 + 7) * inverse_degree_mod_8) % 8,
                u128::from(report.irreducible_residue_mod_8)
            );
        }
    }

    #[test]
    fn odd_endpoint_single_ntt_modulus_has_the_admitted_root_order() {
        assert!(crate::ntheory::is_prime(i128::from(
            ODD_ENDPOINT_SINGLE_PRIME
        )));
        assert_eq!(ODD_ENDPOINT_SINGLE_PRIME - 1, 70_u64 * (1_u64 << 30));
        for prime_factor in [2_u64, 5, 7] {
            assert_ne!(
                mod_pow(
                    PRIMITIVE_ROOT,
                    (ODD_ENDPOINT_SINGLE_PRIME - 1) / prime_factor,
                    ODD_ENDPOINT_SINGLE_PRIME,
                ),
                1
            );
        }
        assert_eq!(
            mod_pow(
                PRIMITIVE_ROOT,
                ODD_ENDPOINT_SINGLE_PRIME - 1,
                ODD_ENDPOINT_SINGLE_PRIME,
            ),
            1
        );
    }

    #[test]
    fn odd_endpoint_single_ntt_crosses_the_character_block_boundary() {
        let ell = 16;
        let degree = 2 * ell + 1;
        let group_order = 1 << ell;
        let report = odd_endpoint_irreducible_count_single_ntt(
            ell,
            HayesLimits {
                max_ell: ell,
                max_degree: degree,
                max_group_order: group_order,
                max_table_cells: (ell + degree + 1) * group_order,
            },
        )
        .unwrap();
        assert_eq!(report.mangoldt_population, 133_816);
        assert_eq!(report.proper_prime_power_population, 1);
        assert_eq!(report.irreducible_count, 4_055);
    }

    #[test]
    fn odd_endpoint_single_ntt_fails_closed_outside_its_uniqueness_range() {
        assert!(matches!(
            odd_endpoint_irreducible_count_single_ntt(0, HayesLimits::default()),
            Err(HayesError::InvalidParameter(_))
        ));
        let limits = HayesLimits {
            max_ell: 31,
            max_degree: 63,
            max_group_order: 1_usize << 31,
            max_table_cells: usize::MAX,
        };
        assert!(matches!(
            odd_endpoint_irreducible_count_single_ntt(31, limits),
            Err(HayesError::ResourceLimit {
                resource: "odd-endpoint single-prime uniqueness bound",
                ..
            })
        ));
    }

    #[test]
    fn odd_endpoint_reduction_leaves_only_the_ramified_x_power() {
        for ell in 1..=8 {
            let reduction =
                odd_endpoint_prime_power_reduction(ell, HayesLimits::default()).unwrap();
            assert_eq!(reduction.degree, 2 * ell + 1);
            assert_eq!(reduction.group_order, 1 << ell);
            assert_eq!(reduction.proper_prime_power_population, 1);
            assert!(reduction.proper_divisors.iter().all(|term| {
                term.prime_degree <= ell
                    && term.exponent >= 3
                    && term.exponent % 2 == 1
                    && reduction.degree == term.prime_degree * term.exponent
            }));

            let exact =
                identity_class_irreducible_count(ell, reduction.degree, HayesLimits::default())
                    .unwrap();
            assert_eq!(exact.proper_prime_power_population, 1);
            assert_eq!(
                reduction.population_proves_irreducible_exists(exact.mangoldt_population),
                exact.proves_irreducible_exists()
            );
        }

        let composite = odd_endpoint_prime_power_reduction(7, HayesLimits::default()).unwrap();
        assert_eq!(
            composite.proper_divisors,
            vec![
                OddEndpointProperDivisor {
                    prime_degree: 1,
                    exponent: 15,
                },
                OddEndpointProperDivisor {
                    prime_degree: 3,
                    exponent: 5,
                },
                OddEndpointProperDivisor {
                    prime_degree: 5,
                    exponent: 3,
                },
            ]
        );
    }

    #[test]
    fn odd_endpoint_reduction_enforces_structural_limits() {
        assert!(matches!(
            odd_endpoint_prime_power_reduction(0, HayesLimits::default()),
            Err(HayesError::InvalidParameter(_))
        ));
        let degree_limited = HayesLimits {
            max_degree: 16,
            ..HayesLimits::default()
        };
        assert_eq!(
            odd_endpoint_prime_power_reduction(8, degree_limited),
            Err(HayesError::ResourceLimit {
                resource: "degree",
                requested: 17,
                limit: 16,
            })
        );
        let group_limited = HayesLimits {
            max_group_order: 127,
            ..HayesLimits::default()
        };
        assert_eq!(
            odd_endpoint_prime_power_reduction(7, group_limited),
            Err(HayesError::ResourceLimit {
                resource: "group_order",
                requested: 128,
                limit: 127,
            })
        );
    }

    #[test]
    fn half_interval_mobius_sieve_exposes_the_parity_barrier() {
        let limits = HayesLimits {
            max_ell: 24,
            ..HayesLimits::default()
        };
        for degree in 2..=48 {
            let report = half_interval_mobius_sieve_report(degree, &[], limits).unwrap();
            assert_eq!(report.cutoff, degree / 2);
            assert_eq!(report.interval_size, BigInt::from(1_u8) << (degree / 2));
            assert_eq!(report.total_weight, BigInt::from(1_u8));
        }

        // x^10+x^5+x^3+x^2+x+1 has distinct irreducible factors of degrees
        // 1, 2, and 3 (with multiplicities supplying the remaining degree).
        // Its truncated weight is +1, so aggregate weight one is not a
        // pointwise lower bound for the prime indicator.
        let bits = 0x42f_u16;
        let coefficients = (0..=10)
            .map(|exponent| i128::from(u8::from(bits & (1 << exponent) != 0)))
            .collect::<Vec<_>>();
        let factors = crate::gfp::factor_berlekamp(&coefficients, 2).unwrap();
        assert_eq!(
            factors
                .iter()
                .map(|(factor, _multiplicity)| factor.len() - 1)
                .collect::<Vec<_>>(),
            vec![1, 2, 3]
        );
        assert!(
            factors
                .iter()
                .any(|(_factor, multiplicity)| *multiplicity > 1)
        );
        let counterexample = half_interval_mobius_sieve_report(10, &[1, 2, 3], limits).unwrap();
        assert_eq!(counterexample.candidate_weight, BigInt::from(1_u8));
    }

    #[test]
    fn half_interval_mobius_sieve_declines_malformed_inputs() {
        let limits = HayesLimits::default();
        assert!(matches!(
            half_interval_mobius_sieve_report(1, &[], limits),
            Err(HayesError::InvalidParameter(_))
        ));
        assert!(matches!(
            half_interval_mobius_sieve_report(10, &[0], limits),
            Err(HayesError::InvalidParameter(_))
        ));
        assert!(matches!(
            half_interval_mobius_sieve_report(10, &[6, 5], limits),
            Err(HayesError::InvalidParameter(_))
        ));
        let degree_limited = HayesLimits {
            max_degree: 9,
            ..limits
        };
        assert_eq!(
            half_interval_mobius_sieve_report(10, &[], degree_limited),
            Err(HayesError::ResourceLimit {
                resource: "degree",
                requested: 10,
                limit: 9,
            })
        );
    }

    #[test]
    fn identity_class_irreducible_count_declines_before_work() {
        assert!(matches!(
            identity_class_irreducible_count(0, 9, HayesLimits::default()),
            Err(HayesError::InvalidParameter(_))
        ));
        assert!(matches!(
            identity_class_irreducible_count(4, 0, HayesLimits::default()),
            Err(HayesError::InvalidParameter(_))
        ));
        let limits = HayesLimits {
            max_table_cells: 100,
            ..HayesLimits::default()
        };
        assert_eq!(
            identity_class_irreducible_count(4, 9, limits),
            Err(HayesError::ResourceLimit {
                resource: "table_cells",
                requested: 224,
                limit: 100,
            })
        );
    }

    #[test]
    fn squared_discrepancy_fourier_energy_filters_by_exact_conductor() {
        let distribution = class_population_distribution(8, 17, HayesLimits::default()).unwrap();
        let decomposition = distribution
            .fourth_moment_conductor_decomposition(8 * 256)
            .unwrap();
        assert_eq!(decomposition.second_moment, BigUint::from(693_360_u32));
        assert_eq!(
            decomposition.fourth_moment,
            BigUint::from(5_447_397_264_u64)
        );
        assert_eq!(decomposition.levels.len(), 8);
        assert_eq!(
            decomposition
                .levels
                .iter()
                .map(|level| level.exact_fourier_energy.clone())
                .collect::<Vec<_>>(),
            [
                0_u64,
                15_904_236_544,
                39_316_443_392,
                9_589_782_016,
                27_393_511_424,
                134_382_961_664,
                280_918_622_208,
                406_280_052_736,
            ]
            .into_iter()
            .map(BigUint::from)
            .collect::<Vec<_>>()
        );
        assert!(decomposition.levels.iter().all(|level| {
            (&level.haar_difference_square_sum << (level.level - 1)) == level.exact_fourier_energy
        }));
        assert_eq!(
            decomposition
                .levels
                .last()
                .unwrap()
                .cumulative_fourier_energy,
            (BigUint::from(1_u8) << 8) * &decomposition.fourth_moment
        );
        assert_eq!(
            decomposition
                .levels
                .iter()
                .map(|level| level.exact_fourier_energy.clone())
                .sum::<BigUint>()
                + decomposition.second_moment.pow(2),
            (BigUint::from(1_u8) << 8) * &decomposition.fourth_moment
        );
        let product = decomposition.kurtosis_product().unwrap();
        assert_eq!(product.factors.len(), 8);
        assert_eq!(
            product.root_ratio_denominator,
            decomposition.second_moment.pow(2)
        );
        assert_eq!(
            product.root_ratio_numerator,
            (BigUint::from(1_u8) << 8) * &decomposition.fourth_moment
        );
        for (index, factor) in product.factors.iter().enumerate() {
            assert_eq!(factor.level, index + 1);
            assert_eq!(
                &factor.factor_denominator + &factor.imbalance_numerator,
                factor.factor_numerator
            );
            assert_eq!(factor.imbalance_denominator, factor.factor_denominator);
            assert!(factor.factor_numerator <= (&factor.factor_denominator << 1_usize));
            if index > 0 {
                assert_eq!(
                    factor.factor_denominator,
                    product.factors[index - 1].factor_numerator
                );
            }
        }
        assert!(!decomposition.satisfies_connected_geometric_split());

        let positive_distribution =
            class_population_distribution(12, 25, HayesLimits::default()).unwrap();
        let positive = positive_distribution
            .fourth_moment_conductor_decomposition(12 * (1 << 12))
            .unwrap();
        assert!(positive.satisfies_connected_geometric_split());
        let mut falsified = positive.clone();
        falsified.levels[7].exact_fourier_energy =
            BigUint::from(3_u8) * falsified.second_moment.pow(2);
        assert!(!falsified.satisfies_connected_geometric_split());
    }

    #[test]
    fn mixed_radix_projection_agrees_with_fresh_lower_distributions() {
        let limits = HayesLimits::default();
        let full = class_population_distribution(8, 17, limits).unwrap();
        let full_factors = principal_unit_factors(8);
        for level in 1..8 {
            let quotient_factors = principal_unit_factors(level);
            let mut projected = vec![0_u128; 1 << level];
            for (index, count) in full.counts.iter().enumerate() {
                let quotient_index =
                    project_mixed_radix_index(index, &full_factors, &quotient_factors).unwrap();
                projected[quotient_index] += count;
            }
            assert_eq!(
                projected,
                class_population_distribution(level, 17, limits)
                    .unwrap()
                    .counts,
                "projection to E_{level} disagrees with a fresh transform"
            );
        }
    }

    #[test]
    fn fourth_moment_filtration_declines_before_projection() {
        let distribution = class_population_distribution(8, 17, HayesLimits::default()).unwrap();
        assert_eq!(
            distribution.fourth_moment_conductor_decomposition(8 * 256 - 1),
            Err(HayesError::ResourceLimit {
                resource: "fourth_moment_projection_cells",
                requested: 8 * 256,
                limit: 8 * 256 - 1,
            })
        );
    }

    #[test]
    fn conductor_layer_sup_norm_is_exact_and_non_credit_bearing() {
        for degree in [17, 18] {
            let distribution =
                class_population_distribution(8, degree, HayesLimits::default()).unwrap();
            let report = distribution
                .conductor_layer_sup_norm_diagnostic(2 * 8 * 256)
                .unwrap();
            assert_eq!(report.ell, 8);
            assert_eq!(report.degree, degree);
            assert_eq!(report.levels.len(), 7);
            assert!((2..=8).eq(report.levels.iter().map(|level| level.level)));
            assert!(report.satisfies_squared_constant(4));
            assert!(!report.satisfies_squared_constant(0));
            let witness = report
                .levels
                .iter()
                .find(|level| level.level == report.witness_level)
                .unwrap();
            assert_eq!(
                &witness.squared_constant_numerator * &report.maximum_squared_constant_denominator,
                &report.maximum_squared_constant_numerator * &witness.squared_constant_denominator
            );
            for level in &report.levels {
                assert_eq!(
                    level.squared_constant_numerator,
                    (BigUint::from(level.maximum_sibling_difference).pow(2) << (level.level - 1))
                );
                assert_eq!(
                    level.squared_constant_denominator,
                    BigUint::from(level.level - 1).pow(2) << degree
                );
            }
        }
    }

    #[test]
    fn conductor_layer_sup_bound_implication_is_exact() {
        let report = check_conductor_layer_sup_bound_sufficiency(
            ConductorLayerSupBoundAssumption::default(),
        )
        .unwrap();
        assert_eq!(report.derived_fourth_moment_constant, 2_500);
        assert_eq!(report.derived_fourth_moment_power, 8);
        assert_eq!(report.individual_weil_proved_through_level_at_threshold, 31);
        assert_eq!(report.derived_fourth_moment.first_odd_degree, 401);
        assert_eq!(report.derived_fourth_moment.first_even_degree, 402);

        assert!(
            check_conductor_layer_sup_bound_sufficiency(ConductorLayerSupBoundAssumption {
                squared_constant: 0,
                ..ConductorLayerSupBoundAssumption::default()
            })
            .is_err()
        );
        assert!(
            check_conductor_layer_sup_bound_sufficiency(ConductorLayerSupBoundAssumption {
                threshold: 20,
                ..ConductorLayerSupBoundAssumption::default()
            })
            .is_err()
        );
    }

    #[test]
    fn absolute_conductor_delocalization_has_exact_counterexample() {
        // Degree 56 is the even endpoint for ell=27.  The level-four sibling
        // difference is independent of the ambient endpoint level, so the
        // E_4 transform gives the exact counterexample without allocating
        // the much larger E_27 table.
        let distribution = class_population_distribution(
            4,
            56,
            HayesLimits {
                max_degree: 56,
                ..HayesLimits::default()
            },
        )
        .unwrap();
        let report = distribution
            .conductor_layer_sup_norm_diagnostic(2 * 4 * 16)
            .unwrap();
        let level = report.levels.iter().find(|level| level.level == 4).unwrap();
        assert_eq!(level.maximum_sibling_difference, 670_285_824);
        assert_eq!(
            level.squared_constant_numerator,
            BigUint::from(3_594_264_686_842_871_808_u128)
        );
        assert_eq!(
            level.squared_constant_denominator,
            BigUint::from(648_518_346_341_351_424_u128)
        );
        assert!(!report.satisfies_squared_constant(4));

        let recurrence = fixed_conductor_sibling_recurrence(
            4,
            56,
            HayesLimits {
                max_degree: 56,
                ..HayesLimits::default()
            },
        )
        .unwrap();
        assert_eq!(
            recurrence.maximum_sibling_difference,
            BigUint::from(level.maximum_sibling_difference)
        );
        assert_eq!(
            recurrence.squared_constant_numerator,
            level.squared_constant_numerator
        );
        assert_eq!(
            recurrence.squared_constant_denominator,
            level.squared_constant_denominator
        );
    }

    #[test]
    fn absolute_conductor_delocalization_fails_after_finite_handoff() {
        // Degree 688 is the even endpoint for ell=343, beyond the separately
        // certified degree-400 range.  The exact BigInt recurrence proves
        // that the absolute C=4 target still fails there.
        let limits = HayesLimits {
            max_degree: 688,
            max_table_cells: 688 * 16 * 16,
            ..HayesLimits::default()
        };
        let report = fixed_conductor_sibling_recurrence(4, 688, limits).unwrap();
        assert_eq!(report.level, 4);
        assert_eq!(report.degree, 688);
        assert_eq!(report.group_order, 16);
        assert_eq!(report.seed_count, 3);
        assert_eq!(report.independently_checked_degree, 7);
        assert!(report.violates_squared_constant(4));
        assert!(!report.violates_squared_constant(4 * 343_usize.pow(4)));

        assert!(matches!(
            fixed_conductor_sibling_recurrence(
                4,
                688,
                HayesLimits {
                    max_degree: 688,
                    max_table_cells: 688 * 16 * 16 - 1,
                    ..HayesLimits::default()
                }
            ),
            Err(HayesError::ResourceLimit {
                resource: "fixed_conductor_recurrence_cells",
                ..
            })
        ));
    }

    #[test]
    fn witt_cylinder_concentration_matches_global_moments() {
        let distribution = class_population_distribution(8, 17, HayesLimits::default()).unwrap();
        let report = distribution.witt_cylinder_concentration(9 * 256).unwrap();
        assert_eq!(report.levels.len(), 9);
        let second = distribution.central_absolute_power_sum(2).unwrap();
        let fourth = distribution.central_absolute_power_sum(4).unwrap();
        assert_eq!(
            report.levels[0].maximum_ratio_numerator,
            BigUint::from(256_u16) * fourth
        );
        assert_eq!(report.levels[0].maximum_ratio_denominator, second.pow(2));
        let last = &report.levels[8];
        assert_eq!(last.descendant_count, 1);
        assert_eq!(last.maximum_ratio_numerator, last.maximum_ratio_denominator);
        assert!(report.satisfies_linear_ceiling());
        assert!(report.root_ratio_at_most_four());
        assert!(
            distribution
                .connected_cumulant_at_most_second_moment_square()
                .unwrap()
        );
        assert!(!report.satisfies_linear_dominance_ceiling());
        assert_eq!(
            report.levels[0].maximum_dominance_numerator,
            6_150_400_u32.into()
        );
        assert_eq!(
            report.levels[0].maximum_dominance_denominator,
            693_360_u32.into()
        );
        let mut falsified = report.clone();
        falsified.levels[0].maximum_ratio_numerator =
            BigUint::from(falsified.ell) * &falsified.levels[0].maximum_ratio_denominator + 1_u8;
        assert!(!falsified.satisfies_linear_ceiling());
        falsified.levels[0].maximum_ratio_numerator =
            BigUint::from(4_u8) * &falsified.levels[0].maximum_ratio_denominator + 1_u8;
        assert!(!falsified.root_ratio_at_most_four());
        assert!(matches!(
            distribution.witt_cylinder_concentration(9 * 256 - 1),
            Err(HayesError::ResourceLimit {
                resource: "witt_cylinder_projection_cells",
                requested: 2304,
                limit: 2303,
            })
        ));
    }

    #[test]
    #[ignore = "extended finite diagnostic; select ell/offset with AXEYUM_CYLINDER_ELL/OFFSET"]
    fn witt_cylinder_concentration_extended_probe() {
        let ell = std::env::var("AXEYUM_CYLINDER_ELL")
            .expect("missing AXEYUM_CYLINDER_ELL")
            .parse::<usize>()
            .expect("invalid AXEYUM_CYLINDER_ELL");
        let offset = std::env::var("AXEYUM_CYLINDER_OFFSET")
            .expect("missing AXEYUM_CYLINDER_OFFSET")
            .parse::<usize>()
            .expect("invalid AXEYUM_CYLINDER_OFFSET");
        assert!(matches!(offset, 1 | 2));
        let degree = 2 * ell + offset;
        let distribution =
            class_population_distribution(ell, degree, HayesLimits::default()).unwrap();
        let report = distribution
            .witt_cylinder_concentration((ell + 1) * (1_usize << ell))
            .unwrap();
        eprintln!(
            "ell={ell} degree={degree} root4={} linear={} dominance={} levels={:?}",
            report.root_ratio_at_most_four(),
            report.satisfies_linear_ceiling(),
            report.satisfies_linear_dominance_ceiling(),
            report
                .levels
                .iter()
                .map(|row| (
                    row.level,
                    row.witness_cylinder,
                    row.maximum_ratio_numerator.clone(),
                    row.maximum_ratio_denominator.clone(),
                    row.dominance_witness_cylinder,
                    row.maximum_dominance_numerator.clone(),
                    row.maximum_dominance_denominator.clone(),
                ))
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn linear_witt_cylinder_target_closes_the_symbolic_endpoint_ledger() {
        let report = check_witt_cylinder_linear_bound_sufficiency(
            WittCylinderLinearBoundAssumption::default(),
        )
        .unwrap();
        assert_eq!(report.derived_fourth_moment.assumption.constant, 16);
        assert_eq!(report.derived_fourth_moment.assumption.power, 5);
        assert_eq!(report.derived_fourth_moment.first_odd_degree, 401);
        assert_eq!(report.derived_fourth_moment.first_even_degree, 402);

        let unchecked_remainder = WittCylinderLinearBoundAssumption {
            finite_max_degree: 399,
            ..WittCylinderLinearBoundAssumption::default()
        };
        assert!(check_witt_cylinder_linear_bound_sufficiency(unchecked_remainder).is_err());
    }

    #[test]
    fn connected_cumulant_target_closes_the_symbolic_endpoint_ledger() {
        let report =
            check_connected_cumulant_bound_sufficiency(ConnectedCumulantBoundAssumption::default())
                .unwrap();
        assert_eq!(report.derived_fourth_moment.assumption.constant, 64);
        assert_eq!(report.derived_fourth_moment.assumption.power, 4);
        assert_eq!(report.derived_fourth_moment.first_odd_degree, 401);
        assert_eq!(report.derived_fourth_moment.first_even_degree, 402);

        let unchecked_remainder = ConnectedCumulantBoundAssumption {
            finite_max_degree: 399,
            ..ConnectedCumulantBoundAssumption::default()
        };
        assert!(check_connected_cumulant_bound_sufficiency(unchecked_remainder).is_err());
    }

    #[test]
    fn adams_identity_fibre_budget_matches_the_connected_endpoint_envelope() {
        for degree in [401_usize, 402] {
            let report = hayes_adams_identity_fibre_requirement(200, degree).unwrap();
            assert_eq!(report.identity_fibre_dimension, 600);
            assert_eq!(report.ambient_max_cohomology_degree, 1_200);
            assert_eq!(report.wick_pairing_dimension, 400);
            assert_eq!(report.required_max_cohomology_degree, 800);
            assert_eq!(report.required_cohomology_degree_drop, 400);
            assert_eq!(
                report.normalized_betti_budget,
                BigUint::from(1_600_000_000_u64)
            );
            assert_eq!(
                report.normalized_connected_trace_allowance,
                &report.normalized_betti_budget << 400
            );
            assert_eq!(
                report.connected_trace_allowance,
                &report.normalized_connected_trace_allowance << (2 * degree)
            );
            assert_eq!(
                &report.connected_trace_allowance >> 400,
                &report.normalized_betti_budget << (2 * degree)
            );
        }
        assert!(hayes_adams_identity_fibre_requirement(0, 1).is_err());
        assert!(hayes_adams_identity_fibre_requirement(12, 24).is_err());
    }

    #[test]
    fn foulkes_ramanujan_compression_reconstructs_only_the_long_cycle() {
        let report =
            sawin_foulkes_endpoint_ledger(12, BigUint::from(1_u8), SawinFoulkesLimits::default())
                .unwrap();
        assert_eq!(report.ell, 5);
        assert_eq!(report.interval_dimension, 7);
        assert_eq!(report.fixed_leading_coefficient_count, 5);
        assert_eq!(report.sawin_weight_exponent_numerator, 12);
        assert_eq!(report.squared_exponential_margin_exponent, 2);
        assert_eq!(report.coefficient_denominator, BigUint::from(4_u8));
        assert_eq!(report.distinct_prime_factor_count, 2);
        assert_eq!(report.coefficient_l1_numerator, BigUint::from(16_u8));
        assert_eq!(report.coefficient_l1_mass, BigUint::from(4_u8));
        assert_eq!(
            report
                .coefficients
                .iter()
                .map(|row| row.numerator.clone())
                .collect::<Vec<_>>(),
            [4, 0, 2, 0, -2, 0, -4, 0, -2, 0, 2, 0]
                .into_iter()
                .map(BigInt::from)
                .collect::<Vec<_>>()
        );
        assert_eq!(
            report
                .reconstructed_power_sum_coefficients
                .iter()
                .map(|row| (row.divisor, row.numerator.clone()))
                .collect::<Vec<_>>(),
            [
                (1, BigInt::from(0_u8)),
                (2, BigInt::from(0_u8)),
                (3, BigInt::from(0_u8)),
                (4, BigInt::from(0_u8)),
                (6, BigInt::from(0_u8)),
                (12, BigInt::from(48_u8)),
            ]
        );
        assert_eq!(
            report
                .distinct_coefficients
                .iter()
                .map(|row| (
                    row.divisor,
                    row.cyclic_character_residue,
                    row.coefficient.clone()
                ))
                .collect::<Vec<_>>(),
            [
                (1, 12, BigInt::from(1_i8)),
                (2, 6, BigInt::from(-1_i8)),
                (3, 4, BigInt::from(-1_i8)),
                (4, 3, BigInt::from(0_i8)),
                (6, 2, BigInt::from(1_i8)),
                (12, 1, BigInt::from(0_i8)),
            ]
        );
        assert_eq!(report.assumed_squared_total_cost, BigUint::from(16_u8));
        assert_eq!(report.squared_exponential_margin, BigUint::from(4_u8));
        assert_eq!(report.main_mangoldt_term, BigUint::from(128_u8));
        assert_eq!(
            report.proper_prime_power_upper_bound,
            BigUint::from(144_u16)
        );
        assert_eq!(report.irreducible_margin, BigUint::from(0_u8));
        assert_eq!(
            report.assumed_squared_absolute_error,
            BigUint::from(65_536_u32)
        );
        assert_eq!(report.squared_irreducible_margin, BigUint::from(0_u8));
        assert!(!report.conditional_endpoint_closure);
        assert!(!report.published_generic_endpoint_closure);
        assert_eq!(
            report.wan_zhang_complete_intersection_betti_bound,
            BigUint::from(330_u16) * BigUint::from(6_u8).pow(12)
        );
        assert!(!report.wan_zhang_endpoint_closure);
    }

    #[test]
    fn long_cycle_cone_cancels_non_top_euler_trace_including_wild_row() {
        for (degree, first_odd, full_fixed_dimension, point_reduction) in [
            (401_usize, 1_usize, 0_usize, true),
            (402, 2, 0, true),
            (12, 4, 0, true),
            (512, 512, 1, false),
        ] {
            let report =
                sawin_long_cycle_euler_report(degree, SawinFoulkesLimits::default()).unwrap();
            assert_eq!(report.ell, degree.div_ceil(2) - 1);
            assert_eq!(report.interval_dimension, degree - report.ell);
            assert_eq!(report.first_odd_binomial_index, first_odd);
            assert_eq!(
                report.full_cycle_fixed_locus_dimension,
                full_fixed_dimension
            );
            assert_eq!(
                report.has_active_odd_binomial_constraint,
                full_fixed_dimension == 0
            );
            assert_eq!(report.fixed_locus_compact_euler_characteristic, 1);
            assert_eq!(report.wild_cycle_order, first_odd);
            assert_eq!(report.tame_cycle_order, degree / first_odd);
            assert_eq!(report.cycle_trace_reduced_to_point, point_reduction);
            assert_eq!(
                report.tame_fixed_locus_dimension,
                if point_reduction {
                    0
                } else {
                    report.interval_dimension
                }
            );
            assert_eq!(report.cone_vertex_cycle_trace, 1);
            assert_eq!(report.punctured_cone_alternating_cycle_trace, 0);
            assert_eq!(report.power_sum_value_on_long_cycle, degree);
            assert_eq!(report.long_cycle_centralizer_order, degree);
            assert_eq!(report.power_sum_projection_scalar, 1);
            assert_eq!(
                report.top_compact_cohomology_degree,
                2 * report.interval_dimension
            );
            assert_eq!(report.top_cycle_trace, 1);
            assert_eq!(report.total_alternating_cycle_trace, 1);
            assert_eq!(report.non_top_alternating_cycle_trace, 0);
            assert_eq!(report.binary_frobenius_projective_trace_factor, 1);
            assert!(!report.frobenius_weighted_cancellation_certified);
        }
    }

    #[test]
    fn long_cycle_lowest_odd_binomial_index_matches_pascal_recurrence() {
        let mut pascal_row = vec![true];
        for degree in 1_usize..=128 {
            let mut next = vec![false; degree + 1];
            for (index, &odd) in pascal_row.iter().enumerate() {
                next[index] ^= odd;
                next[index + 1] ^= odd;
            }
            pascal_row = next;
            if degree < 5 {
                continue;
            }
            let independently_enumerated_first = pascal_row
                .iter()
                .enumerate()
                .skip(1)
                .find_map(|(index, &odd)| odd.then_some(index))
                .unwrap();
            let report =
                sawin_long_cycle_euler_report(degree, SawinFoulkesLimits::default()).unwrap();
            assert_eq!(
                report.first_odd_binomial_index,
                independently_enumerated_first
            );
        }
    }

    #[test]
    fn projective_eigenlines_reject_a_free_long_cycle_quotient() {
        for (degree, wild, tame, fixed_points, reduced, tame_trace) in [
            (
                401_usize,
                1_usize,
                401_usize,
                400_usize,
                true,
                Some(400_usize),
            ),
            (402, 2, 201, 132, false, None),
            (12, 4, 3, 2, false, None),
            (512, 512, 1, 1, false, None),
        ] {
            let report =
                sawin_projective_eigenline_report(degree, SawinFoulkesLimits::default()).unwrap();
            assert_eq!(report.degree, degree);
            assert_eq!(report.ell, degree.div_ceil(2) - 1);
            assert_eq!(report.wild_cycle_order, wild);
            assert_eq!(report.tame_cycle_order, tame);
            assert_eq!(report.primitive_tame_eigenvalue_count, fixed_points);
            assert_eq!(report.reduced_projective_fixed_point_count, fixed_points);
            assert_eq!(report.projective_fixed_scheme_reduced_certified, reduced);
            assert_eq!(report.tame_projective_euler_trace, tame_trace);
            if reduced {
                let affine_dimension = degree - report.ell;
                assert_eq!(report.tame_eigenline_jacobian_rank, Some(report.ell));
                assert_eq!(report.tame_affine_tangent_dimension, Some(affine_dimension));
                assert_eq!(
                    report.tame_projective_tangent_dimension,
                    Some(affine_dimension - 1)
                );
                assert_eq!(
                    report.tame_projective_tangent_weight_exponents,
                    (1..affine_dimension).collect::<Vec<_>>()
                );
                assert_eq!(
                    report.tame_projective_normal_weight_exponents,
                    (affine_dimension..degree).collect::<Vec<_>>()
                );
                assert_eq!(
                    report.tame_eigenline_local_status,
                    SawinTameEigenlineLocalStatus::SmoothTransverse
                );
            } else {
                assert_eq!(report.tame_eigenline_jacobian_rank, None);
                assert_eq!(report.tame_affine_tangent_dimension, None);
                assert_eq!(report.tame_projective_tangent_dimension, None);
                assert!(report.tame_projective_tangent_weight_exponents.is_empty());
                assert!(report.tame_projective_normal_weight_exponents.is_empty());
                assert_eq!(
                    report.tame_eigenline_local_status,
                    SawinTameEigenlineLocalStatus::NotCertifiedWild
                );
            }
            assert!(!report.projective_long_cycle_action_free);
            assert!(!report.frobenius_weighted_trace_bound_certified);
        }
    }

    #[test]
    fn tame_eigenline_jacobian_rank_matches_extension_field_elimination() {
        fn field_inverse(mut value: u64, modulus: u64, field_degree: usize) -> u64 {
            assert_ne!(value, 0);
            let mut result = 1_u64;
            let mut exponent = (1_u64 << field_degree) - 2;
            while exponent != 0 {
                if exponent & 1 != 0 {
                    result = binary_quotient_multiply(result, value, modulus, field_degree);
                }
                exponent >>= 1;
                if exponent != 0 {
                    value = binary_quotient_multiply(value, value, modulus, field_degree);
                }
            }
            result
        }

        fn extension_rank(mut matrix: Vec<Vec<u64>>, modulus: u64, field_degree: usize) -> usize {
            let row_count = matrix.len();
            let column_count = matrix.first().map_or(0, Vec::len);
            let mut pivot_row = 0_usize;
            for column in 0..column_count {
                let Some(pivot) = (pivot_row..row_count).find(|&row| matrix[row][column] != 0)
                else {
                    continue;
                };
                matrix.swap(pivot_row, pivot);
                let inverse = field_inverse(matrix[pivot_row][column], modulus, field_degree);
                for entry in &mut matrix[pivot_row][column..] {
                    *entry = binary_quotient_multiply(*entry, inverse, modulus, field_degree);
                }
                let pivot_tail = matrix[pivot_row][column..].to_vec();
                for (row, entries) in matrix.iter_mut().enumerate() {
                    if row == pivot_row || entries[column] == 0 {
                        continue;
                    }
                    let scale = entries[column];
                    for (entry, &pivot_entry) in entries[column..].iter_mut().zip(&pivot_tail) {
                        *entry ^=
                            binary_quotient_multiply(scale, pivot_entry, modulus, field_degree);
                    }
                }
                pivot_row += 1;
                if pivot_row == row_count {
                    break;
                }
            }
            pivot_row
        }

        // Each listed modulus is primitive.  Raising its root `x` to
        // `(2^m-1)/n` produces a primitive nth root `lambda`.  The matrix is
        // built from the literal partial derivatives
        // `d e_j / d a_i = a_i^(j-1)` at `(1,lambda,...,lambda^(n-1))`.
        for (degree, field_degree, modulus) in [
            (5_usize, 4_usize, 0b1_0011_u64),
            (7, 3, 0b1_011),
            (9, 6, 0b100_0011),
        ] {
            let ell = degree.div_ceil(2) - 1;
            let root_exponent = ((1_usize << field_degree) - 1) / degree;
            let mut lambda = 1_u64;
            for _ in 0..root_exponent {
                lambda = binary_quotient_multiply(lambda, 2, modulus, field_degree);
            }
            let mut coordinates = Vec::with_capacity(degree);
            let mut coordinate = 1_u64;
            for _ in 0..degree {
                coordinates.push(coordinate);
                coordinate = binary_quotient_multiply(coordinate, lambda, modulus, field_degree);
            }
            assert_eq!(coordinate, 1);
            assert_eq!(
                coordinates.iter().copied().collect::<BTreeSet<_>>().len(),
                degree
            );

            let mut jacobian = Vec::with_capacity(ell);
            let mut row = vec![1_u64; degree];
            for _ in 0..ell {
                jacobian.push(row.clone());
                for (entry, &coordinate) in row.iter_mut().zip(&coordinates) {
                    *entry = binary_quotient_multiply(*entry, coordinate, modulus, field_degree);
                }
            }
            assert_eq!(extension_rank(jacobian, modulus, field_degree), ell);
            assert_eq!(
                sawin_projective_eigenline_report(degree, SawinFoulkesLimits::default())
                    .unwrap()
                    .tame_eigenline_jacobian_rank,
                Some(ell)
            );
        }
    }

    #[test]
    fn odd_frobenius_cycle_fixed_locus_has_only_vertex_repetitions() {
        for degree in (5_usize..=401).step_by(2) {
            let report =
                sawin_odd_frobenius_cycle_fixed_locus_report(degree, SawinFoulkesLimits::default())
                    .unwrap();
            assert_eq!(report.degree, degree);
            assert_eq!(report.ell, (degree - 1) / 2);
            assert!(report.proper_orbit_degrees.iter().all(|&e| {
                e < degree
                    && degree.is_multiple_of(e)
                    && !(degree / e).is_multiple_of(2)
                    && e < report.ell
            }));
            assert_eq!(
                report.largest_proper_orbit_degree,
                report.proper_orbit_degrees.last().copied().unwrap_or(0)
            );
            assert!(report.proper_orbit_strata_collapse_to_vertex_certified);
            assert!(report.nonvertex_exact_orbit_degree_certified);
            assert_eq!(report.nonvertex_jacobian_rank, report.ell);
            assert_eq!(
                report.projective_local_status,
                SawinOddFrobeniusCycleLocalStatus::SmoothTransverseUnitTerms
            );
            assert!(!report.frobenius_weighted_trace_bound_certified);
        }
        for degree in [0_usize, 1, 3, 4, 6, 402] {
            assert!(
                sawin_odd_frobenius_cycle_fixed_locus_report(degree, SawinFoulkesLimits::default())
                    .is_err()
            );
        }
    }

    #[test]
    fn odd_fixed_locus_collapse_matches_literal_extension_field_orbits() {
        fn orbit_degree(value: u64, modulus: u64, degree: usize) -> usize {
            let mut conjugate = value;
            for orbit_degree in 1..=degree {
                conjugate = binary_quotient_multiply(conjugate, conjugate, modulus, degree);
                if conjugate == value {
                    return orbit_degree;
                }
            }
            panic!("binary Frobenius orbit failed to close");
        }

        fn characteristic_coefficients(value: u64, modulus: u64, degree: usize) -> Vec<u64> {
            let mut polynomial = vec![1_u64];
            let mut root = value;
            for _ in 0..degree {
                let mut product = vec![0_u64; polynomial.len() + 1];
                for (index, &coefficient) in polynomial.iter().enumerate() {
                    product[index] ^= coefficient;
                    product[index + 1] ^=
                        binary_quotient_multiply(coefficient, root, modulus, degree);
                }
                polynomial = product;
                root = binary_quotient_multiply(root, root, modulus, degree);
            }
            assert!(polynomial.iter().all(|&coefficient| coefficient <= 1));
            polynomial
        }

        // The moduli x^5+x^2+1 and x^7+x+1 are irreducible over GF(2).
        // Literal enumeration is independent of the divisor/triangular proof:
        // build every Frobenius-root polynomial and inspect its zero prefix.
        for (degree, modulus) in [(5_usize, 0b10_0101_u64), (7, 0b1000_0011)] {
            let ell = (degree - 1) / 2;
            let mut shaped_nonzero = 0_usize;
            for value in 0_u64..(1_u64 << degree) {
                let coefficients = characteristic_coefficients(value, modulus, degree);
                let shaped = coefficients[1..=ell]
                    .iter()
                    .all(|&coefficient| coefficient == 0);
                if shaped && value != 0 {
                    shaped_nonzero += 1;
                    assert_eq!(orbit_degree(value, modulus, degree), degree);
                }
                if value == 0 {
                    assert!(shaped);
                    assert_eq!(orbit_degree(value, modulus, degree), 1);
                }
            }
            assert!(shaped_nonzero > 0);
        }
    }

    #[test]
    fn hast_matei_endpoint_hooks_expose_the_second_moment_deficit() {
        for (degree, tail, denominator) in
            [(401_usize, 200_usize, 2_u8), (402_usize, 201_usize, 4_u8)]
        {
            let report =
                hast_matei_long_cycle_endpoint_report(degree, SawinFoulkesLimits::default())
                    .unwrap();
            assert_eq!(report.ell, 200);
            assert_eq!(report.short_interval_tail_degree, tail);
            assert_eq!(report.coefficient_equation_count, 200);
            assert_eq!(report.repeated_root_threshold, 199);
            assert_eq!(report.top_weight_long_cycle_hook_count, 199);
            assert_eq!(report.top_weight_frobenius_exponent, degree - 1);
            assert_eq!(
                report.top_weight_global_second_moment,
                BigUint::from(199_u8) << degree
            );
            assert_eq!(
                report.squared_identity_class_mean,
                BigUint::from(1_u8) << (2 * (degree - 200))
            );
            assert_eq!(report.pointwise_deficit_numerator, 199);
            assert_eq!(
                report.pointwise_deficit_denominator,
                BigUint::from(denominator)
            );
            assert!(!report.top_weight_second_moment_alone_closes_endpoint);
            assert!(report.repeated_root_strata.iter().all(|row| {
                row.triangular_base_recovery_certified || row.frobenius_square_stratum
            }));
            assert!(!report.connected_frobenius_trace_bound_certified);
        }

        let first_admitted =
            hast_matei_long_cycle_endpoint_report(9, SawinFoulkesLimits::default()).unwrap();
        assert!(!first_admitted.top_weight_second_moment_alone_closes_endpoint);
    }

    #[test]
    fn hast_matei_long_cycle_strata_separate_odd_powers_from_squares() {
        let report =
            hast_matei_long_cycle_endpoint_report(12, SawinFoulkesLimits::default()).unwrap();
        assert_eq!(report.ell, 5);
        assert_eq!(report.short_interval_tail_degree, 6);
        assert_eq!(report.repeated_root_threshold, 4);
        assert_eq!(
            report
                .repeated_root_strata
                .iter()
                .map(|row| (
                    row.base_degree,
                    row.multiplicity,
                    row.frobenius_coefficient_stride,
                    row.triangular_base_recovery_certified,
                    row.frobenius_square_stratum,
                ))
                .collect::<Vec<_>>(),
            [
                (1, 12, 4, false, true),
                (2, 6, 2, false, true),
                (3, 4, 4, false, true),
                (4, 3, 1, true, false),
            ]
        );

        for degree in 9_usize..=128 {
            let report =
                hast_matei_long_cycle_endpoint_report(degree, SawinFoulkesLimits::default())
                    .unwrap();
            assert!(report.repeated_root_strata.iter().all(|row| {
                degree == row.base_degree * row.multiplicity
                    && row.base_degree <= report.repeated_root_threshold
                    && row.odd_multiplicity == (row.multiplicity % 2 == 1)
                    && row.triangular_base_recovery_certified == row.odd_multiplicity
                    && row.frobenius_square_stratum != row.odd_multiplicity
                    && row.frobenius_coefficient_stride
                        == (1_usize << row.multiplicity.trailing_zeros())
            }));
        }

        // Independent packed-polynomial control of the symbolic argument:
        // odd powers are injective on the first e leading coefficients, while
        // even powers have the asserted Frobenius coefficient stride.
        for base_degree in 1_usize..=6 {
            for multiplicity in 1_usize..=7 {
                let output_degree = base_degree * multiplicity;
                let stride = 1_usize << multiplicity.trailing_zeros();
                let mut prefixes = BTreeSet::new();
                for tail in 0_u64..(1_u64 << base_degree) {
                    let base = (1_u64 << base_degree) | tail;
                    let mut power = 1_u64;
                    for _ in 0..multiplicity {
                        power = polynomial_multiply_packed(power, base);
                    }
                    let mut prefix = 0_u64;
                    for index in 1..=base_degree {
                        let coefficient = (power >> (output_degree - index)) & 1;
                        prefix |= coefficient << (index - 1);
                    }
                    if multiplicity % 2 == 1 {
                        assert!(prefixes.insert(prefix));
                    } else {
                        for index in 1..=output_degree {
                            if index % stride != 0 {
                                assert_eq!((power >> (output_degree - index)) & 1, 0);
                            }
                        }
                    }
                }
                if multiplicity % 2 == 1 {
                    assert_eq!(prefixes.len(), 1_usize << base_degree);
                }
            }
        }
    }

    #[test]
    fn hast_matei_endpoint_report_declines_invalid_or_excessive_degree() {
        for degree in 0..=8 {
            assert!(
                hast_matei_long_cycle_endpoint_report(degree, SawinFoulkesLimits::default())
                    .is_err()
            );
        }
        assert_eq!(
            hast_matei_long_cycle_endpoint_report(
                13,
                SawinFoulkesLimits {
                    max_degree: 12,
                    max_orthogonality_cells: 100,
                }
            ),
            Err(HayesError::ResourceLimit {
                resource: "hast_matei_endpoint_degree",
                requested: 13,
                limit: 12,
            })
        );
    }

    #[test]
    fn tuxanidy_lemire_convolution_has_maximum_period_through_degree_twelve() {
        let expected_support_sizes = [
            (3_usize, 4_usize),
            (4, 5),
            (5, 16),
            (6, 30),
            (7, 64),
            (8, 133),
            (9, 240),
            (10, 536),
            (11, 968),
            (12, 2_094),
        ];
        for (degree, expected_support_size) in expected_support_sizes {
            let report = tuxanidy_lemire_period_report(
                degree,
                TuxanidyPeriodLimits {
                    max_degree: 12,
                    max_cyclic_order: (1 << 12) - 1,
                    max_convolution_cells: 20_000_000,
                },
            )
            .unwrap();
            assert_eq!(report.degree, degree);
            assert_eq!(report.ell, degree.div_ceil(2) - 1);
            assert_eq!(report.cyclic_order, (1 << degree) - 1);
            assert_eq!(report.convolution_support_size, expected_support_size);
            assert_eq!(report.least_period, report.cyclic_order);
            assert!(report.maximum_least_period);
            assert!(report.period_criterion_holds);
            assert!(report.exact_degree_support_criterion_holds());
            assert!(report.exact_degree_difference_support_size > 0);
            assert!(report.first_exact_degree_difference_witness.is_some());
            assert_eq!(
                report.period_criterion_relation,
                if factor_usize(degree).len() == 1 {
                    TuxanidyPeriodCriterionRelation::ExactPrimePowerDegree
                } else {
                    TuxanidyPeriodCriterionRelation::SufficientOnlyMixedDivisorDegree
                }
            );
            assert_eq!(
                report.maximal_proper_subfield_periods,
                factor_usize(degree)
                    .iter()
                    .map(|(prime, _)| (1_usize << (degree / prime)) - 1)
                    .collect::<Vec<_>>()
            );
            assert_eq!(
                report.theorem_boundary,
                TuxanidyPeriodTheoremBoundary::ExactDegreeDifferenceCertifiedUniversalNonvanishingOpen
            );
            assert!(report.proper_subfield_exponent_lcm < report.cyclic_order);
        }
    }

    #[test]
    fn tuxanidy_characteristic_delta_factors_have_binomial_support() {
        for degree in 3_usize..=10 {
            let report = tuxanidy_lemire_period_report(
                degree,
                TuxanidyPeriodLimits {
                    max_degree: 10,
                    max_cyclic_order: (1 << 10) - 1,
                    max_convolution_cells: 2_000_000,
                },
            )
            .unwrap();
            for (weight, actual) in report.factor_support_sizes.iter().copied().enumerate() {
                let weight = weight + 1;
                let mut binomial = 1_usize;
                for index in 0..weight {
                    binomial = binomial * (degree - index) / (index + 1);
                }
                assert_eq!(actual, binomial + 1);
            }
        }
    }

    #[test]
    fn tuxanidy_distinct_maximum_period_factors_need_not_preserve_period() {
        // Tuxanidy--Wang prove maximum period for each individual binary
        // delta_0+delta_j with j<=n/2.  That theorem cannot be multiplied:
        // at n=8 the convolution through the middle weight has period 15,
        // while the Lemire convolution stops one factor earlier and has the
        // maximum period 255.
        let degree = 8_usize;
        let cyclic_order = (1_usize << degree) - 1;
        let convolution =
            characteristic_delta_convolution(degree, degree / 2, cyclic_order, 1_000_000).unwrap();
        let least_period = positive_divisors(cyclic_order)
            .into_iter()
            .find(|period| {
                convolution
                    .coefficients
                    .iter()
                    .copied()
                    .enumerate()
                    .all(|(index, value)| {
                        value == convolution.coefficients[(index + period) % cyclic_order]
                    })
            })
            .unwrap();
        assert_eq!(least_period, 15);
        assert_eq!(
            tuxanidy_lemire_period_report(degree, TuxanidyPeriodLimits::default())
                .unwrap()
                .least_period,
            cyclic_order
        );
    }

    #[test]
    fn tuxanidy_period_matches_direct_extension_field_support_gcd() {
        // Primitive packed moduli for degrees three through eight.  This
        // oracle never constructs the characteristic-delta convolution: it
        // enumerates powers of x in GF(2^n), multiplies the Frobenius-root
        // characteristic polynomial directly, and applies the independent
        // support-gcd formula for the DFT period.
        for (degree, modulus) in [
            (3_usize, 0b1_011_u64),
            (4, 0b1_0011),
            (5, 0b10_0101),
            (6, 0b100_0011),
            (7, 0b1000_0011),
            (8, 0b1_0001_1101),
        ] {
            let report = tuxanidy_lemire_period_report(
                degree,
                TuxanidyPeriodLimits {
                    max_degree: 8,
                    max_cyclic_order: 255,
                    max_convolution_cells: 200_000,
                },
            )
            .unwrap();
            let mut element = 1_u64;
            let mut support_gcd = report.cyclic_order;
            let mut exact_degree_support = false;
            let mut seen = BTreeSet::new();
            for exponent in 0..report.cyclic_order {
                assert!(seen.insert(element), "listed modulus is not primitive");
                let mut characteristic = vec![1_u64];
                let mut root = element;
                for _ in 0..degree {
                    let mut next = vec![0_u64; characteristic.len() + 1];
                    for (index, coefficient) in characteristic.iter().copied().enumerate() {
                        next[index] ^= binary_quotient_multiply(coefficient, root, modulus, degree);
                        next[index + 1] ^= coefficient;
                    }
                    characteristic = next;
                    root = binary_quotient_multiply(root, root, modulus, degree);
                }
                assert_eq!(root, element);
                assert_eq!(characteristic[degree], 1);
                assert!(characteristic.iter().all(|coefficient| *coefficient <= 1));
                let in_lemire_class =
                    (1..=report.ell).all(|index| characteristic[degree - index] == 0);
                if in_lemire_class {
                    support_gcd = gcd_usize(support_gcd, exponent);
                    let lies_in_maximal_proper_subfield =
                        factor_usize(degree).iter().any(|(prime, _)| {
                            let mut conjugate = element;
                            for _ in 0..(degree / prime) {
                                conjugate =
                                    binary_quotient_multiply(conjugate, conjugate, modulus, degree);
                            }
                            conjugate == element
                        });
                    exact_degree_support |= !lies_in_maximal_proper_subfield;
                }
                element = binary_quotient_multiply(element, 2, modulus, degree);
            }
            assert_eq!(seen.len(), report.cyclic_order);
            assert_eq!(report.least_period, report.cyclic_order / support_gcd);
            assert_eq!(
                report.exact_degree_support_criterion_holds(),
                exact_degree_support
            );
        }
    }

    #[test]
    fn tuxanidy_period_report_declines_invalid_or_excessive_work() {
        for degree in 0..=2 {
            assert!(
                tuxanidy_lemire_period_report(degree, TuxanidyPeriodLimits::default()).is_err()
            );
        }
        assert_eq!(
            tuxanidy_lemire_period_report(
                7,
                TuxanidyPeriodLimits {
                    max_degree: 6,
                    max_cyclic_order: 127,
                    max_convolution_cells: 1_000_000,
                }
            ),
            Err(HayesError::ResourceLimit {
                resource: "tuxanidy_period_degree",
                requested: 7,
                limit: 6,
            })
        );
        assert!(matches!(
            tuxanidy_lemire_period_report(
                8,
                TuxanidyPeriodLimits {
                    max_degree: 8,
                    max_cyclic_order: 255,
                    max_convolution_cells: 10,
                }
            ),
            Err(HayesError::ResourceLimit {
                resource: "tuxanidy_period_convolution_cells",
                ..
            })
        ));
    }

    #[test]
    fn long_cycle_euler_report_declines_invalid_or_excessive_degree() {
        for degree in 0..=4 {
            assert!(sawin_long_cycle_euler_report(degree, SawinFoulkesLimits::default()).is_err());
        }
        assert_eq!(
            sawin_long_cycle_euler_report(
                13,
                SawinFoulkesLimits {
                    max_degree: 12,
                    max_orthogonality_cells: 1,
                }
            ),
            Err(HayesError::ResourceLimit {
                resource: "sawin_long_cycle_fixed_locus_degree",
                requested: 13,
                limit: 12,
            })
        );
    }

    #[test]
    fn foulkes_endpoint_ledger_preserves_strictness_at_degree_400_handoff() {
        let below_boundary = BigUint::from(1_u8) << 46_usize;
        for (degree, phi, mass) in [(401_usize, 400_u16, 2_u8), (402, 132, 8)] {
            let report = sawin_foulkes_endpoint_ledger(
                degree,
                below_boundary.clone(),
                SawinFoulkesLimits::default(),
            )
            .unwrap();
            assert_eq!(report.ell, 200);
            assert_eq!(report.squared_exponential_margin_exponent, 100);
            assert_eq!(
                report.squared_exponential_margin,
                BigUint::from(1_u8) << 100
            );
            assert_eq!(report.coefficient_denominator, BigUint::from(phi));
            assert_eq!(report.coefficient_l1_mass, BigUint::from(mass));
            assert!(report.proper_prime_power_upper_bound < (&report.main_mangoldt_term >> 1));
            assert!(report.assumed_squared_absolute_error < report.squared_irreducible_margin);
            assert!(report.conditional_endpoint_closure);
            assert!(!report.published_generic_endpoint_closure);
            assert!(
                report.wan_zhang_complete_intersection_betti_bound
                    < report.published_generic_single_betti_bound
            );
            assert!(!report.wan_zhang_endpoint_closure);
        }

        let exact_even_boundary = BigUint::from(1_u8) << 47_usize;
        let report =
            sawin_foulkes_endpoint_ledger(402, exact_even_boundary, SawinFoulkesLimits::default())
                .unwrap();
        assert_eq!(
            report.assumed_squared_total_cost,
            report.squared_exponential_margin
        );
        assert!(!report.conditional_endpoint_closure);
        assert!(!report.wan_zhang_endpoint_closure);
    }

    #[test]
    fn quartic_cyclic_betti_target_closes_every_degree_after_400() {
        let report = check_sawin_foulkes_polynomial_betti_sufficiency(
            SawinFoulkesPolynomialBettiAssumption::default(),
        )
        .unwrap();
        assert_eq!(report.squared_polynomial_power, 10);
        assert_eq!(
            report
                .base_rows
                .iter()
                .map(|row| row.degree)
                .collect::<Vec<_>>(),
            (401..=412).collect::<Vec<_>>()
        );
        assert!(report.base_rows.iter().all(|row| {
            row.squared_polynomial_cost < row.squared_half_main_margin
                && row.proper_prime_power_upper_bound < row.half_main_mangoldt_term
        }));
        assert_eq!(
            report.base_rows[0].squared_half_main_margin,
            BigUint::from(1_u8) << 98
        );
        assert_eq!(
            report.base_rows[4].squared_half_main_margin,
            BigUint::from(1_u8) << 99
        );
        assert_eq!(
            report.base_rows[8].squared_half_main_margin,
            BigUint::from(1_u8) << 100
        );
        assert!(report.step_left < report.step_right);

        assert!(
            check_sawin_foulkes_polynomial_betti_sufficiency(
                SawinFoulkesPolynomialBettiAssumption {
                    threshold: 401,
                    polynomial_power: 5,
                }
            )
            .is_err()
        );
        assert!(
            check_sawin_foulkes_polynomial_betti_sufficiency(
                SawinFoulkesPolynomialBettiAssumption {
                    threshold: 2,
                    polynomial_power: 4,
                }
            )
            .is_err()
        );
    }

    #[test]
    fn foulkes_endpoint_ledger_declines_bad_parameters_and_work() {
        assert!(
            sawin_foulkes_endpoint_ledger(2, BigUint::from(1_u8), SawinFoulkesLimits::default())
                .is_err()
        );
        assert!(
            sawin_foulkes_endpoint_ledger(12, BigUint::from(0_u8), SawinFoulkesLimits::default())
                .is_err()
        );
        assert_eq!(
            sawin_foulkes_endpoint_ledger(
                12,
                BigUint::from(1_u8),
                SawinFoulkesLimits {
                    max_degree: 11,
                    max_orthogonality_cells: 100,
                }
            ),
            Err(HayesError::ResourceLimit {
                resource: "sawin_foulkes_degree",
                requested: 12,
                limit: 11,
            })
        );
        assert_eq!(
            sawin_foulkes_endpoint_ledger(
                12,
                BigUint::from(1_u8),
                SawinFoulkesLimits {
                    max_degree: 12,
                    max_orthogonality_cells: 71,
                }
            ),
            Err(HayesError::ResourceLimit {
                resource: "sawin_foulkes_orthogonality_cells",
                requested: 72,
                limit: 71,
            })
        );
    }

    #[test]
    fn constant_one_layer_target_is_refuted_at_first_symbolic_endpoint() {
        let layers = conductor_layers(5, 45, HayesLimits::default()).unwrap();
        let layer = layers.last().copied().unwrap();
        assert_eq!(layer.level, 5);
        assert_eq!(layer.value, 113_287_168);
        assert_eq!(layer.value / 16, 7_080_448);
        assert!(!layer.satisfies_square_root_bound(45));
    }

    #[test]
    fn resource_limits_decline_before_allocation() {
        let limits = HayesLimits {
            max_table_cells: 100,
            ..HayesLimits::default()
        };
        assert_eq!(
            identity_class_count(4, 9, limits),
            Err(HayesError::ResourceLimit {
                resource: "table_cells",
                requested: 224,
                limit: 100,
            })
        );
    }

    #[test]
    fn malformed_parameters_decline() {
        let limits = HayesLimits::default();
        assert!(matches!(
            identity_class_count(0, 3, limits),
            Err(HayesError::InvalidParameter(_))
        ));
        assert!(matches!(
            identity_class_count(4, 3, limits),
            Err(HayesError::InvalidParameter(_))
        ));
    }
}
