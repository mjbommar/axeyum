//! Bounded exact short-interval traces over binary extension fields.
//!
//! This module evaluates the fixed-polynomial-degree, varying-base-field
//! Frobenius traces used by the long-cycle diagnostic.  It is deliberately
//! separate from the base-field Hayes route: a degree-`n` interval over
//! `GF(2^r)` is not the degree-`rn` identity population over `GF(2)`.

use core::fmt;

use num_bigint::{BigInt, BigUint, Sign};
use serde::{Deserialize, Serialize};

use crate::gf2::{
    Gf2Error, Gf2Limits, Gf2Poly, certify_irreducible, check_irreducible_certificate,
};

/// Deterministic limits for one extension-field interval trace.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct BinaryExtensionTraceLimits {
    /// Largest admitted extension degree `r` in `GF(2^r)`.
    pub max_field_degree: usize,
    /// Largest admitted polynomial degree.
    pub max_polynomial_degree: usize,
    /// Largest admitted interval population `(2^r)^h`.
    pub max_candidates: u64,
}

impl Default for BinaryExtensionTraceLimits {
    fn default() -> Self {
        Self {
            max_field_degree: 8,
            max_polynomial_degree: 16,
            max_candidates: 1_000_000,
        }
    }
}

/// Exact fixed-degree long-cycle trace over one binary extension field.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct BinaryExtensionLongCycleTraceReport {
    /// Packed monic irreducible modulus defining `GF(2^r)`.
    pub field_modulus: u64,
    /// Extension degree `r`.
    pub field_degree: usize,
    /// Field order `2^r`.
    pub field_order: u64,
    /// Degree of every monic polynomial in the interval.
    pub polynomial_degree: usize,
    /// Number of prescribed zero next-to-leading coefficients.
    pub fixed_leading_coefficients: usize,
    /// Number of free low coefficients.
    pub free_coefficients: usize,
    /// Exact number `(2^r)^free_coefficients` of interval polynomials.
    pub candidate_count: u64,
    /// Exact sum of the polynomial von Mangoldt function on the interval.
    pub mangoldt_sum: u128,
    /// Signed long-cycle error `mangoldt_sum-candidate_count`.
    pub error: i128,
}

/// Exact connected fourth-cumulant trace over one binary extension field.
///
/// This is the extension-field analogue of the base-field Hayes class
/// distribution.  It retains every leading-coefficient class before forming
/// the second moment, fourth moment, and connected Wick subtraction.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BinaryExtensionConnectedAdamsTraceReport {
    /// Packed monic irreducible modulus defining `GF(2^r)`.
    pub field_modulus: u64,
    /// Extension degree `r`.
    pub field_degree: usize,
    /// Field order `q=2^r`.
    pub field_order: u64,
    /// Leading-coefficient prefix length.
    pub ell: usize,
    /// Degree of every monic polynomial.
    pub polynomial_degree: usize,
    /// Number `q^ell` of coefficient classes.
    pub class_count: u64,
    /// Number `q^degree` of enumerated monic polynomials.
    pub candidate_count: u64,
    /// Exact uniform Mangoldt mean `q^(degree-ell)` in every class.
    pub uniform_mean: u64,
    /// Mangoldt population of the all-zero leading-coefficient class.
    pub identity_class_mangoldt_sum: u128,
    /// `M_2=sum_e (N_e-uniform_mean)^2`.
    pub centered_second_moment: BigUint,
    /// `M_4=sum_e (N_e-uniform_mean)^4`.
    pub centered_fourth_moment: BigUint,
    /// Connected cumulant numerator `q^ell M_4-3M_2^2`.
    pub fourth_cumulant_numerator: BigInt,
    /// Product-constrained connected trace `q^(2ell)` times the cumulant.
    pub connected_adams_trace: BigInt,
    /// Candidate geometric allowance `ell^4 q^(2ell+2degree)`.
    pub candidate_absolute_bound: BigUint,
    /// Least integral coefficient `B` with `abs(trace)<=B q^(2ell+2degree)`.
    pub minimum_normalized_betti_ceiling: BigUint,
    /// Whether this bounded row satisfies the candidate allowance.
    pub satisfies_candidate_bound: bool,
}

/// One exact-conductor layer in the extension-field Witt shifted trace.
///
/// This is the varying-base-field analogue of one row of the aggregate
/// identity-energy path of the base-field Hayes route.  It combines every high
/// conductor before taking a sign, and it combines every low twist of exact
/// conductor `layer` before taking an absolute value.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BinaryExtensionWittShiftedLayerTrace {
    /// Exact low-twist conductor layer.
    pub layer: usize,
    /// Aggregate conditional-covariance mass above the identity child.
    pub identity_aggregate_mass: BigUint,
    /// Aggregate mass above its parent cylinder.
    pub parent_aggregate_mass: BigUint,
    /// Spatial/Fourier layer `q^i A_i-q^(i-1) A_(i-1)`.
    pub signed_spatial_layer: BigInt,
    /// Unnormalised high-character trace `q^coarse_level signed_spatial_layer`.
    pub signed_high_character_trace: BigInt,
    /// Whether this exact row contracts by at least the q-ary average:
    /// `q A_i<=A_(i-1)`.
    pub average_contraction_holds: bool,
}

/// Exact joint `(high character, low twist)` trace over `GF(2^r)`.
///
/// If `D` is the centered degree-`n` Mangoldt population on the `q^ell`
/// leading-coefficient classes, `c` is the coarse level, and
/// `R=q^(ell-c)`, put
///
/// ```text
/// w(a)=R sum_(g above a) D(g)^2-(sum_(g above a)D(g))^2,
/// A_i=sum_(a whose first i coordinates vanish) w(a).
/// ```
///
/// The layer trace is exactly
///
/// ```text
/// q^c (q^i A_i-q^(i-1)A_(i-1)),
/// ```
///
/// the sum of the shifted high-character correlation over every twist of
/// exact conductor `i`.  Varying `r` therefore gives a Frobenius-trace
/// sequence for the connected `(WITT-LOW)` family.  Bounded rows are
/// diagnostics only; they do not certify a cohomological bound.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BinaryExtensionWittShiftedTraceReport {
    /// Packed monic irreducible modulus defining `GF(2^r)`.
    pub field_modulus: u64,
    /// Extension degree `r`.
    pub field_degree: usize,
    /// Field order `q=2^r`.
    pub field_order: u64,
    /// Leading-coefficient prefix length.
    pub ell: usize,
    /// Degree of every monic polynomial.
    pub polynomial_degree: usize,
    /// Coarse high-character cutoff `c`.
    pub coarse_level: usize,
    /// Number `q^(ell-c)` of fine classes above each coarse class.
    pub descendant_count: u64,
    /// Aggregate mass `A_0` before identity-path localization.
    pub aggregate_global_mass: BigUint,
    /// Exact layers `1..=c` in increasing order.
    pub layers: Vec<BinaryExtensionWittShiftedLayerTrace>,
}

/// One deterministic shard of the connected extension-field class vector.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct BinaryExtensionConnectedAdamsTraceShardReport {
    /// Packed monic irreducible modulus defining `GF(2^r)`.
    pub field_modulus: u64,
    /// Extension degree `r`.
    pub field_degree: usize,
    /// Field order `q=2^r`.
    pub field_order: u64,
    /// Leading-coefficient prefix length.
    pub ell: usize,
    /// Degree of every monic polynomial.
    pub polynomial_degree: usize,
    /// Number `q^ell` of coefficient classes.
    pub class_count: u64,
    /// Number `q^degree` of monic polynomials before sharding.
    pub candidate_count: u64,
    /// Exact uniform population `q^(degree-ell)` in every class.
    pub uniform_mean: u64,
    /// Zero-based shard index.
    pub shard_index: u64,
    /// Total number of deterministic contiguous shards.
    pub shard_count: u64,
    /// Inclusive start in the canonical coefficient encoding.
    pub candidate_start: u64,
    /// Exclusive end in the canonical coefficient encoding.
    pub candidate_end: u64,
    /// Partial Mangoldt population in every leading-coefficient class.
    pub class_mangoldt_populations: Vec<u128>,
}

/// Closed-form connected trace at the first nontrivial endpoint `(ell,n)=(2,5)`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BinaryExtensionEllTwoDegreeFiveClosedForm {
    /// Extension degree `r` in `q=2^r`.
    pub field_degree: usize,
    /// Field order `q`.
    pub field_order: BigUint,
    /// Population of each of the `q` classes with subtrace zero.
    pub zero_subtrace_population: BigInt,
    /// Population of each of the `q(q-1)` classes with nonzero subtrace.
    pub nonzero_subtrace_population: BigInt,
    /// Exact second central moment `q^4(q-1)`.
    pub centered_second_moment: BigUint,
    /// Exact fourth central moment `q^5((q-1)^4+(q-1))`.
    pub centered_fourth_moment: BigUint,
    /// Exact cumulant numerator `q^8(q-1)(q^2-6q+6)`.
    pub fourth_cumulant_numerator: BigInt,
    /// Exact connected trace `q^12(q-1)(q^2-6q+6)`.
    pub connected_adams_trace: BigInt,
    /// Leading degree 15 in `q` of the connected trace polynomial.
    pub connected_trace_q_degree: usize,
    /// Adams weight degree `2n=10` in `q`.
    pub adams_weight_q_degree: usize,
    /// Leading degree 5 after removing the Adams weight.
    pub normalized_connected_q_degree: usize,
    /// Degree `2ell=4` permitted by the proposed cutoff.
    pub proposed_normalized_q_degree: usize,
    /// One-degree excess over the proposed cutoff.
    pub normalized_q_degree_excess: usize,
}

/// Closed-form connected trace at `(ell,n)=(3,7)`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BinaryExtensionEllThreeDegreeSevenClosedForm {
    /// Extension degree `r` in `q=2^r`.
    pub field_degree: usize,
    /// Field order `q`.
    pub field_order: BigUint,
    /// Number `q` of classes satisfying `t_2=t_1^2, t_3=t_1^3`.
    pub special_class_count: BigUint,
    /// Number `q^3-q` of remaining classes.
    pub ordinary_class_count: BigUint,
    /// Population `q^4-q+q^3` of every special class.
    pub special_class_population: BigUint,
    /// Population `q^4-q` of every ordinary class.
    pub ordinary_class_population: BigUint,
    /// Exact second central moment `q^5(q^2-1)`.
    pub centered_second_moment: BigUint,
    /// Exact fourth central moment `q^5((q^2-1)^4+(q^2-1))`.
    pub centered_fourth_moment: BigUint,
    /// Exact cumulant numerator `q^10(q^2-1)(q^4-6q^2+6)`.
    pub fourth_cumulant_numerator: BigInt,
    /// Exact connected trace `q^16(q^2-1)(q^4-6q^2+6)`.
    pub connected_adams_trace: BigInt,
    /// Leading degree 22 in `q` of the connected trace polynomial.
    pub connected_trace_q_degree: usize,
    /// Adams weight degree `2n=14` in `q`.
    pub adams_weight_q_degree: usize,
    /// Leading degree 8 after removing the Adams weight.
    pub normalized_connected_q_degree: usize,
    /// Degree `2ell=6` permitted by the original proposed cutoff.
    pub proposed_normalized_q_degree: usize,
    /// Degree 7 permitted after adding one factor of `q`.
    pub one_extra_q_normalized_degree: usize,
    /// Two-degree excess over the original proposed cutoff.
    pub normalized_q_degree_excess: usize,
}

/// Closed form for the joint Witt shifted trace at `(ell,n,c)=(3,7,2)`.
///
/// The exact-conductor-one layer vanishes.  The conductor-two layer is
/// `q^9(q-1)^2`, of q-degree 11 after restoring the high-character
/// normalisation.  The formal top degree is `n+ell+layer=12`, so joint
/// low-twist summation removes only one full q-degree in this family.  This
/// rules out obtaining an arbitrary number of weight drops merely from the
/// dimension of the low-twist affine shell.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BinaryExtensionEllThreeDegreeSevenWittShiftedClosedForm {
    /// Extension degree `r` in `q=2^r`.
    pub field_degree: usize,
    /// Field order `q`.
    pub field_order: BigUint,
    /// The common nonzero coarse covariance mass `q^6(q-1)`.
    pub supported_coarse_mass: BigUint,
    /// Exact vanishing conductor-one high-character trace.
    pub conductor_one_high_character_trace: BigInt,
    /// Conductor-two high-character trace `q^9(q-1)^2`.
    pub conductor_two_high_character_trace: BigInt,
    /// Leading q-degree 11 of the conductor-two trace.
    pub conductor_two_trace_q_degree: usize,
    /// Formal top q-degree `n+ell+layer=12` before monodromy cancellation.
    pub formal_top_q_degree: usize,
    /// Exactly one full q-degree removed in the closed form.
    pub q_degree_drop: usize,
}

/// One deterministic interval of an extension-field long-cycle trace.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct BinaryExtensionLongCycleTraceShardReport {
    /// Packed monic irreducible modulus defining `GF(2^r)`.
    pub field_modulus: u64,
    /// Extension degree `r`.
    pub field_degree: usize,
    /// Field order `2^r`.
    pub field_order: u64,
    /// Degree of every monic polynomial in the interval.
    pub polynomial_degree: usize,
    /// Number of prescribed zero next-to-leading coefficients.
    pub fixed_leading_coefficients: usize,
    /// Number of free low coefficients.
    pub free_coefficients: usize,
    /// Exact total interval population before sharding.
    pub candidate_count: u64,
    /// Zero-based shard index.
    pub shard_index: u64,
    /// Total number of deterministic contiguous shards.
    pub shard_count: u64,
    /// Inclusive start for canonical Frobenius-orbit representatives.
    pub candidate_start: u64,
    /// Exclusive end for canonical Frobenius-orbit representatives.
    pub candidate_end: u64,
    /// Exact orbit-weighted Mangoldt sum owned by this shard.
    pub mangoldt_sum: u128,
}

/// Exact Hankel obstruction to a short constant-coefficient trace recurrence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExtensionTraceHankelMinor {
    /// Frobenius power represented by `traces[0]`.
    pub first_power: usize,
    /// Recurrence order ruled out when the determinant is nonzero.
    pub tested_maximum_recurrence_order: usize,
    /// Exact determinant of the `(order+1)`-square Hankel minor.
    pub determinant: BigInt,
}

impl ExtensionTraceHankelMinor {
    /// Whether this minor proves that no recurrence of the tested order (or
    /// smaller) can generate the supplied consecutive trace sequence.
    #[must_use]
    pub fn excludes_tested_order(&self) -> bool {
        self.determinant != BigInt::from(0_u8)
    }
}

/// Typed failure from bounded binary-extension trace work.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BinaryExtensionTraceError {
    /// A parameter lies outside the mathematical domain.
    InvalidParameter(String),
    /// The packed field modulus is reducible.
    ReducibleFieldModulus,
    /// A configured deterministic limit was exceeded.
    ResourceLimit(String),
    /// An exact arithmetic invariant failed.
    Invariant(String),
    /// The underlying certified `GF(2)[x]` checker declined.
    Gf2(Gf2Error),
}

impl fmt::Display for BinaryExtensionTraceError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidParameter(message) => write!(formatter, "invalid parameter: {message}"),
            Self::ReducibleFieldModulus => {
                write!(formatter, "field modulus is reducible over GF(2)")
            }
            Self::ResourceLimit(message) => write!(formatter, "resource limit: {message}"),
            Self::Invariant(message) => write!(formatter, "invariant failed: {message}"),
            Self::Gf2(error) => write!(formatter, "GF(2) certificate error: {error}"),
        }
    }
}

impl std::error::Error for BinaryExtensionTraceError {}

impl From<Gf2Error> for BinaryExtensionTraceError {
    fn from(error: Gf2Error) -> Self {
        Self::Gf2(error)
    }
}

#[derive(Clone, Copy, Debug)]
struct BinaryExtensionField {
    modulus: u64,
    degree: usize,
    order: u64,
    mask: u64,
}

impl BinaryExtensionField {
    fn new(
        modulus: u64,
        limits: BinaryExtensionTraceLimits,
    ) -> Result<Self, BinaryExtensionTraceError> {
        let degree = packed_degree(modulus).ok_or_else(|| {
            BinaryExtensionTraceError::InvalidParameter(
                "field modulus must have positive degree".to_owned(),
            )
        })?;
        if degree == 0 {
            return Err(BinaryExtensionTraceError::InvalidParameter(
                "field modulus must have positive degree".to_owned(),
            ));
        }
        if degree > limits.max_field_degree || degree >= 63 {
            return Err(BinaryExtensionTraceError::ResourceLimit(format!(
                "field degree {degree} exceeds limit {}",
                limits.max_field_degree
            )));
        }
        let polynomial = Gf2Poly::from_words(vec![modulus]);
        let gf2_limits = Gf2Limits {
            max_input_degree: limits.max_field_degree,
            max_intermediate_degree: limits.max_field_degree.saturating_mul(2),
            max_frobenius_steps: limits.max_field_degree,
            max_word_ops: 1_000_000,
        };
        let Some(certificate) = certify_irreducible(&polynomial, gf2_limits)? else {
            return Err(BinaryExtensionTraceError::ReducibleFieldModulus);
        };
        check_irreducible_certificate(&certificate, gf2_limits)?;
        let order = 1_u64 << degree;
        Ok(Self {
            modulus,
            degree,
            order,
            mask: order - 1,
        })
    }

    fn multiply(self, mut left: u64, mut right: u64) -> u64 {
        let reduction = self.modulus & self.mask;
        let high_bit = 1_u64 << (self.degree - 1);
        let mut result = 0_u64;
        while right != 0 {
            if right & 1 != 0 {
                result ^= left;
            }
            right >>= 1;
            let carry = left & high_bit != 0;
            left = (left << 1) & self.mask;
            if carry {
                left ^= reduction;
            }
        }
        result & self.mask
    }

    fn power(self, mut base: u64, mut exponent: u64) -> u64 {
        let mut result = 1_u64;
        while exponent != 0 {
            if exponent & 1 != 0 {
                result = self.multiply(result, base);
            }
            exponent >>= 1;
            if exponent != 0 {
                base = self.multiply(base, base);
            }
        }
        result
    }

    fn inverse(self, value: u64) -> Option<u64> {
        (value != 0).then(|| self.power(value, self.order - 2))
    }

    fn inverse_frobenius(self, mut value: u64, steps: usize) -> u64 {
        let inverse_steps = (self.degree - (steps % self.degree)) % self.degree;
        for _ in 0..inverse_steps {
            value = self.multiply(value, value);
        }
        value
    }
}

type ExtensionPoly = Vec<u64>;

/// Compute an exact fixed-degree short-interval Mangoldt trace over
/// `GF(2^r)`.
///
/// The interval consists of
///
/// ```text
/// T^n + a_(h-1) T^(h-1) + ... + a_0,
/// h = n-fixed_leading_coefficients.
/// ```
///
/// Its signed error is the Frobenius-power/long-cycle diagnostic `A_r(n)`.
/// Search contributes no theorem credit: the result is an exact bounded
/// enumeration with a certified irreducible binary field modulus.
///
/// # Errors
///
/// Rejects a reducible field modulus, an empty or malformed interval, a
/// configured degree/population excess, or a failed exact invariant.
pub fn binary_extension_long_cycle_trace(
    field_modulus: u64,
    polynomial_degree: usize,
    fixed_leading_coefficients: usize,
    limits: BinaryExtensionTraceLimits,
) -> Result<BinaryExtensionLongCycleTraceReport, BinaryExtensionTraceError> {
    let shard = binary_extension_long_cycle_trace_shard(
        field_modulus,
        polynomial_degree,
        fixed_leading_coefficients,
        0,
        1,
        limits,
    )?;
    combine_binary_extension_long_cycle_trace_shards(&[shard])
}

/// Compute the exact connected endpoint trace over `GF(2^r)`.
///
/// All `q^degree` monic polynomials are partitioned by their first `ell`
/// next-to-leading coefficients.  Their polynomial Mangoldt weights give
/// populations `N_e`; the operation then computes
///
/// ```text
/// M_2 = sum_e (N_e-q^(degree-ell))^2,
/// M_4 = sum_e (N_e-q^(degree-ell))^4,
/// T_r = q^(2ell) (q^ell M_4-3M_2^2).
/// ```
///
/// Thus `T_r` is the extension-field point-count sequence attached to the
/// connected product-constrained contraction, rather than the one-class
/// long-cycle trace returned by [`binary_extension_long_cycle_trace`].  The
/// candidate bound is a stopping test only and receives no theorem credit.
///
/// # Errors
///
/// Rejects non-endpoint degrees, inadmissible fields or populations, host-size
/// overflow, and failures of the exact Mangoldt conservation identity.
pub fn binary_extension_connected_adams_trace(
    field_modulus: u64,
    ell: usize,
    polynomial_degree: usize,
    limits: BinaryExtensionTraceLimits,
) -> Result<BinaryExtensionConnectedAdamsTraceReport, BinaryExtensionTraceError> {
    let shard = binary_extension_connected_adams_trace_shard(
        field_modulus,
        ell,
        polynomial_degree,
        0,
        1,
        limits,
    )?;
    combine_binary_extension_connected_adams_trace_shards(&[shard])
}

/// Compute the complete signed low-twist layer sequence over one extension
/// field.
///
/// This operation deliberately works from coefficient cylinders, not from a
/// numerical character table.  The q-ary finite-group Fourier identities are
/// therefore reconstructed with exact integer arithmetic and remain valid for
/// every binary extension field admitted by the resource limits.
///
/// # Errors
///
/// Rejects a non-endpoint degree, `c` outside `1..ell`, an inadmissible field
/// or population, checked-arithmetic overflow, and any negative conditional
/// covariance or failed population invariant.
pub fn binary_extension_witt_shifted_trace(
    field_modulus: u64,
    ell: usize,
    polynomial_degree: usize,
    coarse_level: usize,
    limits: BinaryExtensionTraceLimits,
) -> Result<BinaryExtensionWittShiftedTraceReport, BinaryExtensionTraceError> {
    if coarse_level == 0 || coarse_level >= ell {
        return Err(BinaryExtensionTraceError::InvalidParameter(
            "Witt shifted trace requires 1 <= coarse level < ell".to_owned(),
        ));
    }
    let shard = binary_extension_connected_adams_trace_shard(
        field_modulus,
        ell,
        polynomial_degree,
        0,
        1,
        limits,
    )?;
    // Reuse the independently maintained moment constructor as a fail-closed
    // conservation check before interpreting the vector geometrically.
    let _ = connected_adams_report_from_populations(&shard, &shard.class_mangoldt_populations)?;
    witt_shifted_report_from_populations(&shard, coarse_level)
}

fn witt_shifted_report_from_populations(
    metadata: &BinaryExtensionConnectedAdamsTraceShardReport,
    coarse_level: usize,
) -> Result<BinaryExtensionWittShiftedTraceReport, BinaryExtensionTraceError> {
    if coarse_level == 0 || coarse_level >= metadata.ell {
        return Err(BinaryExtensionTraceError::InvalidParameter(
            "Witt shifted trace requires 1 <= coarse level < ell".to_owned(),
        ));
    }
    let q = metadata.field_order;
    let descendant_exponent = u32::try_from(metadata.ell - coarse_level).map_err(|_| {
        BinaryExtensionTraceError::ResourceLimit("Witt descendant exponent exceeds u32".to_owned())
    })?;
    let descendant_count = q.checked_pow(descendant_exponent).ok_or_else(|| {
        BinaryExtensionTraceError::ResourceLimit("Witt descendant count overflow".to_owned())
    })?;
    let coarse_exponent = u32::try_from(coarse_level).map_err(|_| {
        BinaryExtensionTraceError::ResourceLimit("Witt coarse exponent exceeds u32".to_owned())
    })?;
    let coarse_count = q.checked_pow(coarse_exponent).ok_or_else(|| {
        BinaryExtensionTraceError::ResourceLimit("Witt coarse count overflow".to_owned())
    })?;
    let coarse_len = usize::try_from(coarse_count).map_err(|_| {
        BinaryExtensionTraceError::ResourceLimit("Witt coarse count exceeds host size".to_owned())
    })?;
    let descendant_len = usize::try_from(descendant_count).map_err(|_| {
        BinaryExtensionTraceError::ResourceLimit(
            "Witt descendant count exceeds host size".to_owned(),
        )
    })?;
    if coarse_len.checked_mul(descendant_len) != Some(metadata.class_mangoldt_populations.len()) {
        return Err(BinaryExtensionTraceError::Invariant(
            "Witt coarse blocks do not partition the class vector".to_owned(),
        ));
    }
    let coarse_masses = witt_conditional_coarse_masses(metadata, descendant_len, coarse_len)?;
    let aggregate_global_mass = coarse_masses.iter().cloned().sum::<BigUint>();
    let layers = witt_shifted_layers(q, coarse_level, &coarse_masses, &aggregate_global_mass)?;

    Ok(BinaryExtensionWittShiftedTraceReport {
        field_modulus: metadata.field_modulus,
        field_degree: metadata.field_degree,
        field_order: q,
        ell: metadata.ell,
        polynomial_degree: metadata.polynomial_degree,
        coarse_level,
        descendant_count,
        aggregate_global_mass,
        layers,
    })
}

fn witt_conditional_coarse_masses(
    metadata: &BinaryExtensionConnectedAdamsTraceShardReport,
    descendant_len: usize,
    coarse_len: usize,
) -> Result<Vec<BigUint>, BinaryExtensionTraceError> {
    let mean = BigInt::from(metadata.uniform_mean);
    let descendant_scale = BigUint::from(descendant_len);
    let mut coarse_masses = Vec::with_capacity(coarse_len);
    for block in metadata
        .class_mangoldt_populations
        .chunks_exact(descendant_len)
    {
        let mut sum = BigInt::from(0_u8);
        let mut square_sum = BigUint::from(0_u8);
        for population in block {
            let delta = BigInt::from(*population) - &mean;
            square_sum += delta.magnitude().pow(2);
            sum += delta;
        }
        let covariance = BigInt::from(&descendant_scale * square_sum) - sum.pow(2);
        if covariance.sign() == Sign::Minus {
            return Err(BinaryExtensionTraceError::Invariant(
                "Witt conditional covariance became negative".to_owned(),
            ));
        }
        coarse_masses.push(covariance.magnitude().clone());
    }
    Ok(coarse_masses)
}

fn witt_shifted_layers(
    q: u64,
    coarse_level: usize,
    coarse_masses: &[BigUint],
    aggregate_global_mass: &BigUint,
) -> Result<Vec<BinaryExtensionWittShiftedLayerTrace>, BinaryExtensionTraceError> {
    let q_big = BigUint::from(q);
    let coarse_exponent = u32::try_from(coarse_level).map_err(|_| {
        BinaryExtensionTraceError::ResourceLimit("Witt coarse exponent exceeds u32".to_owned())
    })?;
    let coarse_character_scale = q_big.pow(coarse_exponent);
    let mut parent_mass = aggregate_global_mass.clone();
    let mut layers = Vec::with_capacity(coarse_level);
    for layer in 1..=coarse_level {
        let identity_exponent = u32::try_from(coarse_level - layer).map_err(|_| {
            BinaryExtensionTraceError::ResourceLimit(
                "Witt identity-cylinder exponent exceeds u32".to_owned(),
            )
        })?;
        let identity_count = q.checked_pow(identity_exponent).ok_or_else(|| {
            BinaryExtensionTraceError::ResourceLimit(
                "Witt identity-cylinder count overflow".to_owned(),
            )
        })?;
        let identity_len = usize::try_from(identity_count).map_err(|_| {
            BinaryExtensionTraceError::ResourceLimit(
                "Witt identity-cylinder count exceeds host size".to_owned(),
            )
        })?;
        let identity_aggregate_mass = coarse_masses
            .iter()
            .take(identity_len)
            .cloned()
            .sum::<BigUint>();
        if identity_aggregate_mass > parent_mass {
            return Err(BinaryExtensionTraceError::Invariant(
                "Witt identity aggregate mass grew under localization".to_owned(),
            ));
        }
        let layer_exponent = u32::try_from(layer).map_err(|_| {
            BinaryExtensionTraceError::ResourceLimit("Witt layer exceeds u32".to_owned())
        })?;
        let parent_exponent = layer_exponent - 1;
        let signed_spatial_layer =
            BigInt::from(q_big.pow(layer_exponent) * &identity_aggregate_mass)
                - BigInt::from(q_big.pow(parent_exponent) * &parent_mass);
        let signed_high_character_trace =
            BigInt::from(coarse_character_scale.clone()) * &signed_spatial_layer;
        let average_contraction_holds = &q_big * &identity_aggregate_mass <= parent_mass;
        layers.push(BinaryExtensionWittShiftedLayerTrace {
            layer,
            identity_aggregate_mass: identity_aggregate_mass.clone(),
            parent_aggregate_mass: parent_mass,
            signed_spatial_layer,
            signed_high_character_trace,
            average_contraction_holds,
        });
        parent_mass = identity_aggregate_mass;
    }
    Ok(layers)
}

fn connected_adams_domain(
    field_modulus: u64,
    ell: usize,
    polynomial_degree: usize,
    limits: BinaryExtensionTraceLimits,
) -> Result<(BinaryExtensionField, u64, u64, usize), BinaryExtensionTraceError> {
    let twice_ell = ell.checked_mul(2).ok_or_else(|| {
        BinaryExtensionTraceError::InvalidParameter("connected ell overflow".to_owned())
    })?;
    if ell == 0 || !matches!(polynomial_degree.checked_sub(twice_ell), Some(1 | 2)) {
        return Err(BinaryExtensionTraceError::InvalidParameter(
            "connected Adams trace requires degree in {2*ell+1,2*ell+2}".to_owned(),
        ));
    }
    let (field, free_coefficients, candidate_count) =
        extension_trace_domain(field_modulus, polynomial_degree, 0, limits)?;
    if free_coefficients != polynomial_degree {
        return Err(BinaryExtensionTraceError::Invariant(
            "full connected trace did not admit every coefficient".to_owned(),
        ));
    }
    let ell_exponent = u32::try_from(ell).map_err(|_| {
        BinaryExtensionTraceError::ResourceLimit("class exponent exceeds u32".to_owned())
    })?;
    let class_count = field.order.checked_pow(ell_exponent).ok_or_else(|| {
        BinaryExtensionTraceError::ResourceLimit("class count overflow".to_owned())
    })?;
    let class_len = usize::try_from(class_count).map_err(|_| {
        BinaryExtensionTraceError::ResourceLimit("class count exceeds host size".to_owned())
    })?;
    let low_exponent = u32::try_from(polynomial_degree - ell).map_err(|_| {
        BinaryExtensionTraceError::ResourceLimit("class-block exponent exceeds u32".to_owned())
    })?;
    let uniform_mean = field.order.checked_pow(low_exponent).ok_or_else(|| {
        BinaryExtensionTraceError::ResourceLimit("uniform class mean overflow".to_owned())
    })?;
    Ok((field, candidate_count, uniform_mean, class_len))
}

/// Compute one deterministic contiguous shard of the connected class vector.
///
/// Unlike the long-cycle shard, this report retains one partial population
/// for every leading-coefficient class.  Shards may split a class; exact
/// componentwise addition during merge restores the full population vector.
///
/// # Errors
///
/// Rejects invalid shard coordinates, non-endpoint parameters, inadmissible
/// fields/populations, and checked arithmetic or class-index failures.
pub fn binary_extension_connected_adams_trace_shard(
    field_modulus: u64,
    ell: usize,
    polynomial_degree: usize,
    shard_index: u64,
    shard_count: u64,
    limits: BinaryExtensionTraceLimits,
) -> Result<BinaryExtensionConnectedAdamsTraceShardReport, BinaryExtensionTraceError> {
    if shard_count == 0 || shard_index >= shard_count {
        return Err(BinaryExtensionTraceError::InvalidParameter(
            "require 0 <= shard index < positive shard count".to_owned(),
        ));
    }
    let (field, candidate_count, uniform_mean, class_len) =
        connected_adams_domain(field_modulus, ell, polynomial_degree, limits)?;
    let candidate_start = shard_endpoint(candidate_count, shard_index, shard_count)?;
    let candidate_end = shard_endpoint(candidate_count, shard_index + 1, shard_count)?;
    let class_mangoldt_populations = extension_class_mangoldt_population_range(
        field,
        polynomial_degree,
        class_len,
        uniform_mean,
        candidate_start,
        candidate_end,
    )?;
    Ok(BinaryExtensionConnectedAdamsTraceShardReport {
        field_modulus,
        field_degree: field.degree,
        field_order: field.order,
        ell,
        polynomial_degree,
        class_count: u64::try_from(class_len).map_err(|_| {
            BinaryExtensionTraceError::ResourceLimit("class count exceeds u64".to_owned())
        })?,
        candidate_count,
        uniform_mean,
        shard_index,
        shard_count,
        candidate_start,
        candidate_end,
        class_mangoldt_populations,
    })
}

/// Merge a complete deterministic shard set and form the connected moments.
///
/// # Errors
///
/// Rejects empty, duplicated, missing, noncontiguous, differently
/// parameterized, or malformed class vectors.  The merged vector must recover
/// the exact global Mangoldt population before any moment is returned.
pub fn combine_binary_extension_connected_adams_trace_shards(
    shards: &[BinaryExtensionConnectedAdamsTraceShardReport],
) -> Result<BinaryExtensionConnectedAdamsTraceReport, BinaryExtensionTraceError> {
    let first = shards.first().ok_or_else(|| {
        BinaryExtensionTraceError::InvalidParameter(
            "cannot combine zero connected shards".to_owned(),
        )
    })?;
    let expected_len = usize::try_from(first.shard_count).map_err(|_| {
        BinaryExtensionTraceError::ResourceLimit("shard count exceeds host size".to_owned())
    })?;
    if shards.len() != expected_len {
        return Err(BinaryExtensionTraceError::Invariant(format!(
            "received {} connected shards but expected {expected_len}",
            shards.len()
        )));
    }
    let class_len = usize::try_from(first.class_count).map_err(|_| {
        BinaryExtensionTraceError::ResourceLimit("class count exceeds host size".to_owned())
    })?;
    let mut populations = vec![0_u128; class_len];
    let mut ordered = shards.iter().collect::<Vec<_>>();
    ordered.sort_by_key(|shard| shard.shard_index);
    let mut expected_start = 0_u64;
    for (expected_index, shard) in ordered.into_iter().enumerate() {
        let expected_index = u64::try_from(expected_index).map_err(|_| {
            BinaryExtensionTraceError::ResourceLimit("shard index exceeds u64".to_owned())
        })?;
        if shard.field_modulus != first.field_modulus
            || shard.field_degree != first.field_degree
            || shard.field_order != first.field_order
            || shard.ell != first.ell
            || shard.polynomial_degree != first.polynomial_degree
            || shard.class_count != first.class_count
            || shard.candidate_count != first.candidate_count
            || shard.uniform_mean != first.uniform_mean
            || shard.shard_count != first.shard_count
        {
            return Err(BinaryExtensionTraceError::Invariant(
                "connected shard parameters disagree".to_owned(),
            ));
        }
        if shard.shard_index != expected_index || shard.candidate_start != expected_start {
            return Err(BinaryExtensionTraceError::Invariant(
                "connected shards are duplicated, missing, or noncontiguous".to_owned(),
            ));
        }
        if shard.candidate_end < shard.candidate_start
            || shard.class_mangoldt_populations.len() != class_len
        {
            return Err(BinaryExtensionTraceError::Invariant(
                "connected shard has a reversed range or malformed class vector".to_owned(),
            ));
        }
        expected_start = shard.candidate_end;
        for (total, partial) in populations
            .iter_mut()
            .zip(&shard.class_mangoldt_populations)
        {
            *total = total.checked_add(*partial).ok_or_else(|| {
                BinaryExtensionTraceError::ResourceLimit(
                    "connected class population overflow".to_owned(),
                )
            })?;
        }
    }
    if expected_start != first.candidate_count {
        return Err(BinaryExtensionTraceError::Invariant(
            "connected shards do not cover the full population".to_owned(),
        ));
    }
    connected_adams_report_from_populations(first, &populations)
}

fn connected_adams_report_from_populations(
    metadata: &BinaryExtensionConnectedAdamsTraceShardReport,
    populations: &[u128],
) -> Result<BinaryExtensionConnectedAdamsTraceReport, BinaryExtensionTraceError> {
    let class_count = metadata
        .field_order
        .checked_pow(u32::try_from(metadata.ell).map_err(|_| {
            BinaryExtensionTraceError::ResourceLimit("class exponent exceeds u32".to_owned())
        })?)
        .ok_or_else(|| {
            BinaryExtensionTraceError::ResourceLimit("class count overflow".to_owned())
        })?;
    if populations.len()
        != usize::try_from(class_count).map_err(|_| {
            BinaryExtensionTraceError::ResourceLimit("class count exceeds host size".to_owned())
        })?
    {
        return Err(BinaryExtensionTraceError::Invariant(
            "connected class population vector has the wrong length".to_owned(),
        ));
    }
    let recovered_total = populations.iter().try_fold(0_u128, |sum, value| {
        sum.checked_add(*value).ok_or_else(|| {
            BinaryExtensionTraceError::ResourceLimit(
                "connected class population total overflow".to_owned(),
            )
        })
    })?;
    if recovered_total != u128::from(metadata.candidate_count) {
        return Err(BinaryExtensionTraceError::Invariant(format!(
            "Mangoldt populations sum to {recovered_total}, expected {}",
            metadata.candidate_count
        )));
    }
    let mean = u128::from(metadata.uniform_mean);
    let centered_second_moment = populations
        .iter()
        .map(|population| BigUint::from(population.abs_diff(mean)).pow(2))
        .sum::<BigUint>();
    let centered_fourth_moment = populations
        .iter()
        .map(|population| BigUint::from(population.abs_diff(mean)).pow(4))
        .sum::<BigUint>();
    let class_count_big = BigUint::from(class_count);
    let fourth_cumulant_numerator = BigInt::from(&class_count_big * &centered_fourth_moment)
        - BigInt::from(BigUint::from(3_u8) * centered_second_moment.pow(2));
    let connected_adams_trace = BigInt::from(class_count_big.pow(2)) * &fourth_cumulant_numerator;
    let allowance_exponent = metadata
        .ell
        .checked_mul(2)
        .and_then(|value| {
            metadata
                .polynomial_degree
                .checked_mul(2)
                .and_then(|n| value.checked_add(n))
        })
        .and_then(|value| u32::try_from(value).ok())
        .ok_or_else(|| {
            BinaryExtensionTraceError::ResourceLimit(
                "connected allowance exponent overflow".to_owned(),
            )
        })?;
    let geometric_scale = BigUint::from(metadata.field_order).pow(allowance_exponent);
    let candidate_absolute_bound = BigUint::from(metadata.ell).pow(4) * &geometric_scale;
    let minimum_normalized_betti_ceiling = (connected_adams_trace.magnitude() + &geometric_scale
        - BigUint::from(1_u8))
        / &geometric_scale;
    let satisfies_candidate_bound = connected_adams_trace.magnitude() <= &candidate_absolute_bound;
    Ok(BinaryExtensionConnectedAdamsTraceReport {
        field_modulus: metadata.field_modulus,
        field_degree: metadata.field_degree,
        field_order: metadata.field_order,
        ell: metadata.ell,
        polynomial_degree: metadata.polynomial_degree,
        class_count,
        candidate_count: metadata.candidate_count,
        uniform_mean: metadata.uniform_mean,
        identity_class_mangoldt_sum: populations[0],
        centered_second_moment,
        centered_fourth_moment,
        fourth_cumulant_numerator,
        connected_adams_trace,
        candidate_absolute_bound,
        minimum_normalized_betti_ceiling,
        satisfies_candidate_bound,
    })
}

/// Evaluate the exact trace/subtrace closed form for `(ell,n)=(2,5)`.
///
/// For `q=2^r`, the characteristic-two trace/subtrace quadratic-form count is
///
/// ```text
/// N_(t,0) = q^3 + (-1)^r (q-1)q,
/// N_(t,s) = q^3 - (-1)^r q       for s != 0.
/// ```
///
/// There are `q` classes of the first kind and `q(q-1)` of the second.  Exact
/// algebra then gives
///
/// ```text
/// T_r = q^12 (q-1)(q^2-6q+6).
/// ```
///
/// Its leading `q`-degree is 15.  Removing the degree-10 Adams weight leaves
/// degree 5, refuting a universal normalized degree-`2ell=4` cutoff.  This is
/// a fixed-`ell` obstruction and says nothing by itself about `ell>=200`.
///
/// # Errors
///
/// Rejects zero extension degree or a degree above the configured bound.
pub fn binary_extension_ell_two_degree_five_closed_form(
    field_degree: usize,
    limits: BinaryExtensionTraceLimits,
) -> Result<BinaryExtensionEllTwoDegreeFiveClosedForm, BinaryExtensionTraceError> {
    if field_degree == 0 {
        return Err(BinaryExtensionTraceError::InvalidParameter(
            "extension degree must be positive".to_owned(),
        ));
    }
    if field_degree > limits.max_field_degree {
        return Err(BinaryExtensionTraceError::ResourceLimit(format!(
            "field degree {field_degree} exceeds limit {}",
            limits.max_field_degree
        )));
    }
    let q = BigUint::from(1_u8) << field_degree;
    let q_minus_one = &q - BigUint::from(1_u8);
    let q_cubed = q.pow(3);
    let correction = &q * &q_minus_one;
    let single_correction = q.clone();
    let (zero_subtrace_population, nonzero_subtrace_population) = if field_degree.is_multiple_of(2)
    {
        (
            BigInt::from(&q_cubed + correction),
            BigInt::from(&q_cubed - single_correction),
        )
    } else {
        (
            BigInt::from(&q_cubed - correction),
            BigInt::from(&q_cubed + single_correction),
        )
    };
    let centered_second_moment = q.pow(4) * &q_minus_one;
    let centered_fourth_moment = q.pow(5) * (q_minus_one.pow(4) + &q_minus_one);
    let quadratic_factor =
        BigInt::from(q.pow(2)) - BigInt::from(6_u8) * BigInt::from(q.clone()) + BigInt::from(6_u8);
    let fourth_cumulant_numerator = BigInt::from(q.pow(8) * &q_minus_one) * &quadratic_factor;
    let connected_adams_trace = BigInt::from(q.pow(12) * &q_minus_one) * quadratic_factor;
    Ok(BinaryExtensionEllTwoDegreeFiveClosedForm {
        field_degree,
        field_order: q,
        zero_subtrace_population,
        nonzero_subtrace_population,
        centered_second_moment,
        centered_fourth_moment,
        fourth_cumulant_numerator,
        connected_adams_trace,
        connected_trace_q_degree: 15,
        adams_weight_q_degree: 10,
        normalized_connected_q_degree: 5,
        proposed_normalized_q_degree: 4,
        normalized_q_degree_excess: 1,
    })
}

/// Evaluate the exact three-leading-coefficient form for `(ell,n)=(3,7)`.
///
/// Gorodetsky's characteristic-two period-24 symmetry reduces normalized
/// degree-seven Mangoldt populations to degree one.  Since `7^-1=7 mod 24`,
/// the transformed degree-one class is nonempty exactly when
///
/// ```text
/// t_2=t_1^2 and t_3=t_1^3.
/// ```
///
/// Therefore the `q^3` class populations take only the two values
///
/// ```text
/// N(t_1,t_2,t_3) = q^4-q+q^3  on the q special classes,
///                   q^4-q      otherwise.
/// ```
///
/// Exact central-moment algebra gives
///
/// ```text
/// T_r = q^16 (q^2-1)(q^4-6q^2+6).
/// ```
///
/// Its leading `q`-degree is 22.  Removing the degree-14 Adams weight leaves
/// degree 8, exceeding both the proposed normalized degree `2ell=6` and its
/// one-extra-`q` repair.  This fixed-level obstruction does not decide the
/// growing binary endpoint.
///
/// # Errors
///
/// Rejects zero extension degree or a degree above the configured bound.
pub fn binary_extension_ell_three_degree_seven_closed_form(
    field_degree: usize,
    limits: BinaryExtensionTraceLimits,
) -> Result<BinaryExtensionEllThreeDegreeSevenClosedForm, BinaryExtensionTraceError> {
    if field_degree == 0 {
        return Err(BinaryExtensionTraceError::InvalidParameter(
            "extension degree must be positive".to_owned(),
        ));
    }
    if field_degree > limits.max_field_degree {
        return Err(BinaryExtensionTraceError::ResourceLimit(format!(
            "field degree {field_degree} exceeds limit {}",
            limits.max_field_degree
        )));
    }
    let q = BigUint::from(1_u8) << field_degree;
    let q_squared_minus_one = q.pow(2) - BigUint::from(1_u8);
    let ordinary_class_count = q.pow(3) - &q;
    let ordinary_class_population = q.pow(4) - &q;
    let special_class_population = &ordinary_class_population + q.pow(3);
    let centered_second_moment = q.pow(5) * &q_squared_minus_one;
    let centered_fourth_moment = q.pow(5) * (q_squared_minus_one.pow(4) + &q_squared_minus_one);
    let quartic_factor =
        BigInt::from(q.pow(4)) - BigInt::from(6_u8) * BigInt::from(q.pow(2)) + BigInt::from(6_u8);
    let fourth_cumulant_numerator =
        BigInt::from(q.pow(10) * &q_squared_minus_one) * &quartic_factor;
    let connected_adams_trace = BigInt::from(q.pow(16) * &q_squared_minus_one) * quartic_factor;
    Ok(BinaryExtensionEllThreeDegreeSevenClosedForm {
        field_degree,
        field_order: q.clone(),
        special_class_count: q,
        ordinary_class_count,
        special_class_population,
        ordinary_class_population,
        centered_second_moment,
        centered_fourth_moment,
        fourth_cumulant_numerator,
        connected_adams_trace,
        connected_trace_q_degree: 22,
        adams_weight_q_degree: 14,
        normalized_connected_q_degree: 8,
        proposed_normalized_q_degree: 6,
        one_extra_q_normalized_degree: 7,
        normalized_q_degree_excess: 2,
    })
}

/// Evaluate the joint low-twist layer closed form at `(ell,n,c)=(3,7,2)`.
///
/// The degree-seven population formula has centered value `-q` off the curve
///
/// ```text
/// t_2=t_1^2,  t_3=t_1^3,
/// ```
///
/// and `q(q^2-1)` on it.  In each coarse `(t_1,t_2)` fibre, conditional
/// covariance is consequently zero off `t_2=t_1^2` and `q^6(q-1)` on it.
/// The two identity-path layers then follow by counting this graph.
///
/// # Errors
///
/// Rejects zero extension degree or a degree above the configured bound.
pub fn binary_extension_ell_three_degree_seven_witt_shifted_closed_form(
    field_degree: usize,
    limits: BinaryExtensionTraceLimits,
) -> Result<BinaryExtensionEllThreeDegreeSevenWittShiftedClosedForm, BinaryExtensionTraceError> {
    if field_degree == 0 {
        return Err(BinaryExtensionTraceError::InvalidParameter(
            "extension degree must be positive".to_owned(),
        ));
    }
    if field_degree > limits.max_field_degree {
        return Err(BinaryExtensionTraceError::ResourceLimit(format!(
            "field degree {field_degree} exceeds limit {}",
            limits.max_field_degree
        )));
    }
    let q = BigUint::from(1_u8) << field_degree;
    let q_minus_one = &q - BigUint::from(1_u8);
    let supported_coarse_mass = q.pow(6) * &q_minus_one;
    let conductor_two_high_character_trace = BigInt::from(q.pow(9) * q_minus_one.pow(2));
    Ok(BinaryExtensionEllThreeDegreeSevenWittShiftedClosedForm {
        field_degree,
        field_order: q,
        supported_coarse_mass,
        conductor_one_high_character_trace: BigInt::from(0_u8),
        conductor_two_high_character_trace,
        conductor_two_trace_q_degree: 11,
        formal_top_q_degree: 12,
        q_degree_drop: 1,
    })
}

/// Compute one deterministic contiguous shard of an extension-field trace.
///
/// A coefficientwise-Frobenius orbit belongs to shard `s` of `k` exactly when
/// its least encoded representative lies in
///
/// ```text
/// floor(N*s/k) <= encoded < floor(N*(s+1)/k),
/// ```
///
/// where `N` is the full interval population.  The Mangoldt weight is constant
/// on each orbit, so the representative contributes its weight times the
/// exact orbit size.  The endpoints are evaluated in `u128`, so the partition
/// itself cannot overflow its admitted `u64` population.
///
/// # Errors
///
/// In addition to the full-trace errors, rejects zero shard counts and shard
/// indices outside `0..shard_count`.
pub fn binary_extension_long_cycle_trace_shard(
    field_modulus: u64,
    polynomial_degree: usize,
    fixed_leading_coefficients: usize,
    shard_index: u64,
    shard_count: u64,
    limits: BinaryExtensionTraceLimits,
) -> Result<BinaryExtensionLongCycleTraceShardReport, BinaryExtensionTraceError> {
    if shard_count == 0 || shard_index >= shard_count {
        return Err(BinaryExtensionTraceError::InvalidParameter(
            "require 0 <= shard index < positive shard count".to_owned(),
        ));
    }
    let (field, free_coefficients, candidate_count) = extension_trace_domain(
        field_modulus,
        polynomial_degree,
        fixed_leading_coefficients,
        limits,
    )?;
    let candidate_start = shard_endpoint(candidate_count, shard_index, shard_count)?;
    let candidate_end = shard_endpoint(candidate_count, shard_index + 1, shard_count)?;
    let mangoldt_sum = extension_trace_range(
        field,
        polynomial_degree,
        free_coefficients,
        candidate_start,
        candidate_end,
    )?;

    Ok(BinaryExtensionLongCycleTraceShardReport {
        field_modulus,
        field_degree: field.degree,
        field_order: field.order,
        polynomial_degree,
        fixed_leading_coefficients,
        free_coefficients,
        candidate_count,
        shard_index,
        shard_count,
        candidate_start,
        candidate_end,
        mangoldt_sum,
    })
}

/// Merge a complete set of deterministic extension-trace shards.
///
/// # Errors
///
/// Rejects empty, duplicated, missing, differently parameterized, or
/// noncontiguous shard sets, and any exact-total overflow.
pub fn combine_binary_extension_long_cycle_trace_shards(
    shards: &[BinaryExtensionLongCycleTraceShardReport],
) -> Result<BinaryExtensionLongCycleTraceReport, BinaryExtensionTraceError> {
    let first = shards.first().ok_or_else(|| {
        BinaryExtensionTraceError::InvalidParameter("cannot combine zero shards".to_owned())
    })?;
    let expected_len = usize::try_from(first.shard_count).map_err(|_| {
        BinaryExtensionTraceError::ResourceLimit("shard count exceeds host size".to_owned())
    })?;
    if shards.len() != expected_len {
        return Err(BinaryExtensionTraceError::Invariant(format!(
            "received {} shards but expected {expected_len}",
            shards.len()
        )));
    }
    let mut ordered = shards.iter().collect::<Vec<_>>();
    ordered.sort_by_key(|shard| shard.shard_index);
    let mut expected_start = 0_u64;
    let mut mangoldt_sum = 0_u128;
    for (expected_index, shard) in ordered.into_iter().enumerate() {
        let expected_index = u64::try_from(expected_index).map_err(|_| {
            BinaryExtensionTraceError::ResourceLimit("shard index exceeds u64".to_owned())
        })?;
        if shard.field_modulus != first.field_modulus
            || shard.field_degree != first.field_degree
            || shard.field_order != first.field_order
            || shard.polynomial_degree != first.polynomial_degree
            || shard.fixed_leading_coefficients != first.fixed_leading_coefficients
            || shard.free_coefficients != first.free_coefficients
            || shard.candidate_count != first.candidate_count
            || shard.shard_count != first.shard_count
        {
            return Err(BinaryExtensionTraceError::Invariant(
                "extension-trace shard parameters disagree".to_owned(),
            ));
        }
        if shard.shard_index != expected_index || shard.candidate_start != expected_start {
            return Err(BinaryExtensionTraceError::Invariant(
                "extension-trace shards are duplicated, missing, or noncontiguous".to_owned(),
            ));
        }
        if shard.candidate_end < shard.candidate_start {
            return Err(BinaryExtensionTraceError::Invariant(
                "extension-trace shard has a reversed range".to_owned(),
            ));
        }
        expected_start = shard.candidate_end;
        mangoldt_sum = mangoldt_sum
            .checked_add(shard.mangoldt_sum)
            .ok_or_else(|| {
                BinaryExtensionTraceError::ResourceLimit("Mangoldt sum overflow".to_owned())
            })?;
    }
    if expected_start != first.candidate_count {
        return Err(BinaryExtensionTraceError::Invariant(
            "extension-trace shards do not cover the full population".to_owned(),
        ));
    }
    let signed_sum = i128::try_from(mangoldt_sum).map_err(|_| {
        BinaryExtensionTraceError::ResourceLimit("Mangoldt sum exceeds i128".to_owned())
    })?;

    Ok(BinaryExtensionLongCycleTraceReport {
        field_modulus: first.field_modulus,
        field_degree: first.field_degree,
        field_order: first.field_order,
        polynomial_degree: first.polynomial_degree,
        fixed_leading_coefficients: first.fixed_leading_coefficients,
        free_coefficients: first.free_coefficients,
        candidate_count: first.candidate_count,
        mangoldt_sum,
        error: signed_sum - i128::from(first.candidate_count),
    })
}

/// Collapse a complete contiguous block of fine shards into one coarser shard.
///
/// The child shard count must be an exact multiple of `parent_shard_count`.
/// The function checks every parameter, child index, and range endpoint before
/// summing, so hierarchical fleet execution has the same exact partition
/// contract as a direct coarse shard.
///
/// # Errors
///
/// Rejects an invalid parent index/count, an incommensurable child partition,
/// missing or duplicated children, parameter disagreement, endpoint drift, or
/// an exact-total overflow.
pub fn collapse_binary_extension_long_cycle_trace_subshards(
    subshards: &[BinaryExtensionLongCycleTraceShardReport],
    parent_shard_index: u64,
    parent_shard_count: u64,
) -> Result<BinaryExtensionLongCycleTraceShardReport, BinaryExtensionTraceError> {
    if parent_shard_count == 0 || parent_shard_index >= parent_shard_count {
        return Err(BinaryExtensionTraceError::InvalidParameter(
            "require 0 <= parent shard index < positive parent shard count".to_owned(),
        ));
    }
    let first = subshards.first().ok_or_else(|| {
        BinaryExtensionTraceError::InvalidParameter("cannot collapse zero subshards".to_owned())
    })?;
    if !first.shard_count.is_multiple_of(parent_shard_count) {
        return Err(BinaryExtensionTraceError::Invariant(
            "child shard count is not a multiple of parent shard count".to_owned(),
        ));
    }
    let children_per_parent = first.shard_count / parent_shard_count;
    let expected_len = usize::try_from(children_per_parent).map_err(|_| {
        BinaryExtensionTraceError::ResourceLimit("child block exceeds host size".to_owned())
    })?;
    if subshards.len() != expected_len {
        return Err(BinaryExtensionTraceError::Invariant(format!(
            "received {} subshards but expected {expected_len}",
            subshards.len()
        )));
    }
    let first_child = parent_shard_index
        .checked_mul(children_per_parent)
        .ok_or_else(|| {
            BinaryExtensionTraceError::ResourceLimit("first child index overflow".to_owned())
        })?;
    let expected_parent_start = shard_endpoint(
        first.candidate_count,
        parent_shard_index,
        parent_shard_count,
    )?;
    let expected_parent_end = shard_endpoint(
        first.candidate_count,
        parent_shard_index + 1,
        parent_shard_count,
    )?;

    let mut ordered = subshards.iter().collect::<Vec<_>>();
    ordered.sort_by_key(|shard| shard.shard_index);
    let mut expected_start = expected_parent_start;
    let mut mangoldt_sum = 0_u128;
    for (offset, shard) in ordered.into_iter().enumerate() {
        let expected_index = first_child
            .checked_add(u64::try_from(offset).map_err(|_| {
                BinaryExtensionTraceError::ResourceLimit("child offset exceeds u64".to_owned())
            })?)
            .ok_or_else(|| {
                BinaryExtensionTraceError::ResourceLimit("child index overflow".to_owned())
            })?;
        if shard.field_modulus != first.field_modulus
            || shard.field_degree != first.field_degree
            || shard.field_order != first.field_order
            || shard.polynomial_degree != first.polynomial_degree
            || shard.fixed_leading_coefficients != first.fixed_leading_coefficients
            || shard.free_coefficients != first.free_coefficients
            || shard.candidate_count != first.candidate_count
            || shard.shard_count != first.shard_count
        {
            return Err(BinaryExtensionTraceError::Invariant(
                "extension-trace subshard parameters disagree".to_owned(),
            ));
        }
        if shard.shard_index != expected_index || shard.candidate_start != expected_start {
            return Err(BinaryExtensionTraceError::Invariant(
                "extension-trace subshards are duplicated, missing, or noncontiguous".to_owned(),
            ));
        }
        if shard.candidate_end < shard.candidate_start {
            return Err(BinaryExtensionTraceError::Invariant(
                "extension-trace subshard has a reversed range".to_owned(),
            ));
        }
        expected_start = shard.candidate_end;
        mangoldt_sum = mangoldt_sum
            .checked_add(shard.mangoldt_sum)
            .ok_or_else(|| {
                BinaryExtensionTraceError::ResourceLimit("Mangoldt sum overflow".to_owned())
            })?;
    }
    if expected_start != expected_parent_end {
        return Err(BinaryExtensionTraceError::Invariant(
            "extension-trace subshards do not cover the parent range".to_owned(),
        ));
    }

    Ok(BinaryExtensionLongCycleTraceShardReport {
        field_modulus: first.field_modulus,
        field_degree: first.field_degree,
        field_order: first.field_order,
        polynomial_degree: first.polynomial_degree,
        fixed_leading_coefficients: first.fixed_leading_coefficients,
        free_coefficients: first.free_coefficients,
        candidate_count: first.candidate_count,
        shard_index: parent_shard_index,
        shard_count: parent_shard_count,
        candidate_start: expected_parent_start,
        candidate_end: expected_parent_end,
        mangoldt_sum,
    })
}

fn shard_endpoint(
    candidate_count: u64,
    shard_index: u64,
    shard_count: u64,
) -> Result<u64, BinaryExtensionTraceError> {
    u64::try_from(u128::from(candidate_count) * u128::from(shard_index) / u128::from(shard_count))
        .map_err(|_| BinaryExtensionTraceError::Invariant("shard endpoint exceeds u64".to_owned()))
}

/// Compute an exact Hankel minor from consecutive Frobenius traces.
///
/// If `A_r` is a power-sum sequence with a constant-coefficient recurrence of
/// order at most `d`, every `(d+1)`-square Hankel minor vanishes.  A nonzero
/// result therefore proves that the reduced virtual zeta factor needs more
/// than `d` recurrence modes.  It does not infer a recurrence from finite
/// data or promote the bounded traces into a uniform theorem.
///
/// # Errors
///
/// Rejects order zero, a power-label overflow, too few traces, or a failed
/// exact Bareiss-division invariant.
pub fn extension_trace_hankel_minor(
    traces: &[i128],
    first_power: usize,
    tested_maximum_recurrence_order: usize,
) -> Result<ExtensionTraceHankelMinor, BinaryExtensionTraceError> {
    if tested_maximum_recurrence_order == 0 {
        return Err(BinaryExtensionTraceError::InvalidParameter(
            "Hankel recurrence order must be positive".to_owned(),
        ));
    }
    let dimension = tested_maximum_recurrence_order
        .checked_add(1)
        .ok_or_else(|| {
            BinaryExtensionTraceError::ResourceLimit("Hankel dimension overflow".to_owned())
        })?;
    let required = dimension
        .checked_mul(2)
        .and_then(|value| value.checked_sub(1))
        .ok_or_else(|| {
            BinaryExtensionTraceError::ResourceLimit("Hankel trace count overflow".to_owned())
        })?;
    if traces.len() < required {
        return Err(BinaryExtensionTraceError::InvalidParameter(format!(
            "Hankel order {tested_maximum_recurrence_order} requires {required} traces"
        )));
    }
    first_power.checked_add(required - 1).ok_or_else(|| {
        BinaryExtensionTraceError::ResourceLimit("Frobenius power overflow".to_owned())
    })?;
    let matrix = (0..dimension)
        .map(|row| {
            (0..dimension)
                .map(|column| BigInt::from(traces[row + column]))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let determinant = bareiss_determinant(matrix)?;
    Ok(ExtensionTraceHankelMinor {
        first_power,
        tested_maximum_recurrence_order,
        determinant,
    })
}

fn bareiss_determinant(mut matrix: Vec<Vec<BigInt>>) -> Result<BigInt, BinaryExtensionTraceError> {
    let dimension = matrix.len();
    if dimension == 0 || matrix.iter().any(|row| row.len() != dimension) {
        return Err(BinaryExtensionTraceError::InvalidParameter(
            "Bareiss determinant requires a nonempty square matrix".to_owned(),
        ));
    }
    if dimension == 1 {
        return Ok(matrix[0][0].clone());
    }
    let mut previous_pivot = BigInt::from(1_u8);
    let mut sign = BigInt::from(1_u8);
    for pivot_index in 0..dimension - 1 {
        let Some(pivot_row) =
            (pivot_index..dimension).find(|&row| matrix[row][pivot_index] != BigInt::from(0_u8))
        else {
            return Ok(BigInt::from(0_u8));
        };
        if pivot_row != pivot_index {
            matrix.swap(pivot_row, pivot_index);
            sign = -sign;
        }
        let pivot = matrix[pivot_index][pivot_index].clone();
        for row in pivot_index + 1..dimension {
            for column in pivot_index + 1..dimension {
                let numerator = &matrix[row][column] * &pivot
                    - &matrix[row][pivot_index] * &matrix[pivot_index][column];
                let quotient = &numerator / &previous_pivot;
                if &quotient * &previous_pivot != numerator {
                    return Err(BinaryExtensionTraceError::Invariant(
                        "Bareiss determinant division was not exact".to_owned(),
                    ));
                }
                matrix[row][column] = quotient;
            }
            matrix[row][pivot_index] = BigInt::from(0_u8);
        }
        previous_pivot = pivot;
    }
    Ok(sign * matrix[dimension - 1][dimension - 1].clone())
}

fn extension_trace_domain(
    field_modulus: u64,
    polynomial_degree: usize,
    fixed_leading_coefficients: usize,
    limits: BinaryExtensionTraceLimits,
) -> Result<(BinaryExtensionField, usize, u64), BinaryExtensionTraceError> {
    let field = BinaryExtensionField::new(field_modulus, limits)?;
    if polynomial_degree == 0 || fixed_leading_coefficients >= polynomial_degree {
        return Err(BinaryExtensionTraceError::InvalidParameter(
            "require 0 <= fixed leading coefficients < polynomial degree".to_owned(),
        ));
    }
    if polynomial_degree > limits.max_polynomial_degree {
        return Err(BinaryExtensionTraceError::ResourceLimit(format!(
            "polynomial degree {polynomial_degree} exceeds limit {}",
            limits.max_polynomial_degree
        )));
    }
    let free_coefficients = polynomial_degree - fixed_leading_coefficients;
    let exponent = u32::try_from(free_coefficients).map_err(|_| {
        BinaryExtensionTraceError::ResourceLimit(
            "free-coefficient count does not fit exponent domain".to_owned(),
        )
    })?;
    let candidate_count = field.order.checked_pow(exponent).ok_or_else(|| {
        BinaryExtensionTraceError::ResourceLimit("candidate count overflow".to_owned())
    })?;
    if candidate_count > limits.max_candidates {
        return Err(BinaryExtensionTraceError::ResourceLimit(format!(
            "candidate count {candidate_count} exceeds limit {}",
            limits.max_candidates
        )));
    }

    Ok((field, free_coefficients, candidate_count))
}

fn extension_trace_range(
    field: BinaryExtensionField,
    polynomial_degree: usize,
    free_coefficients: usize,
    candidate_start: u64,
    candidate_end: u64,
) -> Result<u128, BinaryExtensionTraceError> {
    let mut mangoldt_sum = 0_u128;
    for encoded in candidate_start..candidate_end {
        let mut digits = encoded;
        let mut polynomial = vec![0_u64; polynomial_degree + 1];
        for coefficient in polynomial.iter_mut().take(free_coefficients) {
            *coefficient = digits % field.order;
            digits /= field.order;
        }
        polynomial[polynomial_degree] = 1;
        let Some(orbit_size) =
            canonical_frobenius_orbit_size(encoded, &polynomial[..free_coefficients], field)?
        else {
            continue;
        };
        let lambda = polynomial_mangoldt(&polynomial, field)?;
        let orbit_contribution = (lambda as u128)
            .checked_mul(orbit_size as u128)
            .ok_or_else(|| {
                BinaryExtensionTraceError::ResourceLimit(
                    "Frobenius-orbit Mangoldt contribution overflow".to_owned(),
                )
            })?;
        mangoldt_sum = mangoldt_sum
            .checked_add(orbit_contribution)
            .ok_or_else(|| {
                BinaryExtensionTraceError::ResourceLimit("Mangoldt sum overflow".to_owned())
            })?;
    }
    Ok(mangoldt_sum)
}

fn extension_class_mangoldt_population_range(
    field: BinaryExtensionField,
    polynomial_degree: usize,
    class_len: usize,
    uniform_mean: u64,
    candidate_start: u64,
    candidate_end: u64,
) -> Result<Vec<u128>, BinaryExtensionTraceError> {
    let mut populations = vec![0_u128; class_len];
    for encoded in candidate_start..candidate_end {
        let mut digits = encoded;
        let mut polynomial = vec![0_u64; polynomial_degree + 1];
        for coefficient in polynomial.iter_mut().take(polynomial_degree) {
            *coefficient = digits % field.order;
            digits /= field.order;
        }
        polynomial[polynomial_degree] = 1;
        let class_index = usize::try_from(encoded / uniform_mean).map_err(|_| {
            BinaryExtensionTraceError::Invariant("class index exceeds host size".to_owned())
        })?;
        let lambda = polynomial_mangoldt(&polynomial, field)? as u128;
        populations[class_index] =
            populations[class_index]
                .checked_add(lambda)
                .ok_or_else(|| {
                    BinaryExtensionTraceError::ResourceLimit(
                        "class Mangoldt population overflow".to_owned(),
                    )
                })?;
    }
    Ok(populations)
}

/// Return the orbit size when `encoded` is the least element of its
/// coefficientwise-Frobenius orbit, and `None` otherwise.
fn canonical_frobenius_orbit_size(
    encoded: u64,
    coefficients: &[u64],
    field: BinaryExtensionField,
) -> Result<Option<usize>, BinaryExtensionTraceError> {
    let mut orbit = coefficients.to_vec();
    for orbit_size in 1..=field.degree {
        let mut transformed = 0_u64;
        let mut place = 1_u64;
        for coefficient in &mut orbit {
            *coefficient = field.multiply(*coefficient, *coefficient);
            transformed = transformed
                .checked_add(coefficient.checked_mul(place).ok_or_else(|| {
                    BinaryExtensionTraceError::Invariant(
                        "Frobenius-orbit encoding multiplication overflow".to_owned(),
                    )
                })?)
                .ok_or_else(|| {
                    BinaryExtensionTraceError::Invariant(
                        "Frobenius-orbit encoding addition overflow".to_owned(),
                    )
                })?;
            place = place.checked_mul(field.order).ok_or_else(|| {
                BinaryExtensionTraceError::Invariant(
                    "Frobenius-orbit encoding place overflow".to_owned(),
                )
            })?;
        }
        if transformed < encoded {
            return Ok(None);
        }
        if transformed == encoded {
            return Ok(Some(orbit_size));
        }
    }
    Err(BinaryExtensionTraceError::Invariant(
        "coefficientwise Frobenius orbit did not close".to_owned(),
    ))
}

fn polynomial_mangoldt(
    polynomial: &[u64],
    field: BinaryExtensionField,
) -> Result<usize, BinaryExtensionTraceError> {
    let degree = poly_degree(polynomial).ok_or_else(|| {
        BinaryExtensionTraceError::Invariant("enumerated polynomial is zero".to_owned())
    })?;
    for exponent in (1..=degree).rev() {
        if !degree.is_multiple_of(exponent) {
            continue;
        }
        let Some(root) = polynomial_power_root(polynomial, exponent, field) else {
            continue;
        };
        if polynomial_is_irreducible(&root, field)? {
            return Ok(degree / exponent);
        }
    }
    Ok(0)
}

fn polynomial_power_root(
    polynomial: &[u64],
    exponent: usize,
    field: BinaryExtensionField,
) -> Option<ExtensionPoly> {
    let two_power_exponent = exponent.trailing_zeros() as usize;
    let two_power = 1_usize.checked_shl(u32::try_from(two_power_exponent).ok()?)?;
    let odd_exponent = exponent / two_power;
    let degree = poly_degree(polynomial)?;
    if !degree.is_multiple_of(exponent) {
        return None;
    }

    let mut stripped = vec![0_u64; degree / two_power + 1];
    for (index, &coefficient) in polynomial.iter().enumerate() {
        if coefficient == 0 {
            continue;
        }
        if !index.is_multiple_of(two_power) {
            return None;
        }
        stripped[index / two_power] = field.inverse_frobenius(coefficient, two_power_exponent);
    }
    trim_poly(&mut stripped);

    let root_degree = degree / exponent;
    let mut root = vec![0_u64; root_degree + 1];
    root[root_degree] = 1;
    for offset in 1..=root_degree {
        let current = poly_power(&root, odd_exponent, field);
        let target_degree = odd_exponent * root_degree - offset;
        let current_value = current.get(target_degree).copied().unwrap_or(0);
        let target_value = stripped.get(target_degree).copied().unwrap_or(0);
        root[root_degree - offset] = current_value ^ target_value;
    }
    (poly_power(&root, odd_exponent, field) == stripped).then_some(root)
}

fn polynomial_is_irreducible(
    polynomial: &[u64],
    field: BinaryExtensionField,
) -> Result<bool, BinaryExtensionTraceError> {
    let Some(degree) = poly_degree(polynomial) else {
        return Ok(false);
    };
    if degree == 0 {
        return Ok(false);
    }
    if degree == 1 {
        return Ok(true);
    }
    if polynomial[degree] != 1 {
        return Err(BinaryExtensionTraceError::Invariant(
            "irreducibility input is not monic".to_owned(),
        ));
    }

    let x = vec![0, 1];
    let prime_divisors = distinct_prime_factors(degree);
    let mut current = x.clone();
    for step in 1..=degree {
        for _ in 0..field.degree {
            current = poly_square_mod(&current, polynomial, field)?;
        }
        for &prime in &prime_divisors {
            if step == degree / prime {
                let difference = poly_add(&current, &x);
                if poly_degree(&poly_gcd(polynomial, &difference, field)?) != Some(0) {
                    return Ok(false);
                }
            }
        }
    }
    Ok(current == x)
}

fn poly_add(left: &[u64], right: &[u64]) -> ExtensionPoly {
    let mut result = vec![0_u64; left.len().max(right.len())];
    for (index, value) in result.iter_mut().enumerate() {
        *value = left.get(index).copied().unwrap_or(0) ^ right.get(index).copied().unwrap_or(0);
    }
    trim_poly(&mut result);
    result
}

fn poly_multiply(left: &[u64], right: &[u64], field: BinaryExtensionField) -> ExtensionPoly {
    if left.is_empty() || right.is_empty() {
        return Vec::new();
    }
    let mut result = vec![0_u64; left.len() + right.len() - 1];
    for (left_index, &left_value) in left.iter().enumerate() {
        for (right_index, &right_value) in right.iter().enumerate() {
            result[left_index + right_index] ^= field.multiply(left_value, right_value);
        }
    }
    trim_poly(&mut result);
    result
}

fn poly_power(
    polynomial: &[u64],
    mut exponent: usize,
    field: BinaryExtensionField,
) -> ExtensionPoly {
    let mut base = polynomial.to_vec();
    let mut result = vec![1_u64];
    while exponent != 0 {
        if exponent & 1 != 0 {
            result = poly_multiply(&result, &base, field);
        }
        exponent >>= 1;
        if exponent != 0 {
            base = poly_multiply(&base, &base, field);
        }
    }
    result
}

fn poly_div_rem(
    dividend: &[u64],
    divisor: &[u64],
    field: BinaryExtensionField,
) -> Result<(ExtensionPoly, ExtensionPoly), BinaryExtensionTraceError> {
    let divisor_degree = poly_degree(divisor).ok_or_else(|| {
        BinaryExtensionTraceError::Invariant("polynomial division by zero".to_owned())
    })?;
    let inverse_lead = field.inverse(divisor[divisor_degree]).ok_or_else(|| {
        BinaryExtensionTraceError::Invariant("polynomial divisor has zero lead".to_owned())
    })?;
    let mut remainder = dividend.to_vec();
    trim_poly(&mut remainder);
    let mut quotient = vec![0_u64; remainder.len().saturating_sub(divisor_degree)];
    while let Some(remainder_degree) = poly_degree(&remainder) {
        if remainder_degree < divisor_degree {
            break;
        }
        let shift = remainder_degree - divisor_degree;
        let factor = field.multiply(remainder[remainder_degree], inverse_lead);
        quotient[shift] ^= factor;
        for (index, &coefficient) in divisor.iter().enumerate() {
            remainder[index + shift] ^= field.multiply(factor, coefficient);
        }
        trim_poly(&mut remainder);
    }
    trim_poly(&mut quotient);
    Ok((quotient, remainder))
}

fn poly_mod(
    polynomial: &[u64],
    modulus: &[u64],
    field: BinaryExtensionField,
) -> Result<ExtensionPoly, BinaryExtensionTraceError> {
    Ok(poly_div_rem(polynomial, modulus, field)?.1)
}

fn poly_square_mod(
    polynomial: &[u64],
    modulus: &[u64],
    field: BinaryExtensionField,
) -> Result<ExtensionPoly, BinaryExtensionTraceError> {
    let mut square = vec![0_u64; polynomial.len().saturating_mul(2).saturating_sub(1)];
    for (index, &coefficient) in polynomial.iter().enumerate() {
        square[2 * index] = field.multiply(coefficient, coefficient);
    }
    poly_mod(&square, modulus, field)
}

fn poly_gcd(
    left: &[u64],
    right: &[u64],
    field: BinaryExtensionField,
) -> Result<ExtensionPoly, BinaryExtensionTraceError> {
    let mut first = left.to_vec();
    let mut second = right.to_vec();
    trim_poly(&mut first);
    trim_poly(&mut second);
    while !second.is_empty() {
        let remainder = poly_div_rem(&first, &second, field)?.1;
        first = second;
        second = remainder;
    }
    let Some(degree) = poly_degree(&first) else {
        return Ok(first);
    };
    let inverse_lead = field.inverse(first[degree]).ok_or_else(|| {
        BinaryExtensionTraceError::Invariant("gcd has zero leading coefficient".to_owned())
    })?;
    for coefficient in &mut first {
        *coefficient = field.multiply(*coefficient, inverse_lead);
    }
    Ok(first)
}

fn packed_degree(polynomial: u64) -> Option<usize> {
    (polynomial != 0).then(|| (u64::BITS - 1 - polynomial.leading_zeros()) as usize)
}

fn poly_degree(polynomial: &[u64]) -> Option<usize> {
    polynomial.iter().rposition(|&coefficient| coefficient != 0)
}

fn trim_poly(polynomial: &mut ExtensionPoly) {
    while polynomial.last() == Some(&0) {
        polynomial.pop();
    }
}

fn distinct_prime_factors(mut value: usize) -> Vec<usize> {
    let mut factors = Vec::new();
    let mut divisor = 2_usize;
    while divisor <= value / divisor {
        if value.is_multiple_of(divisor) {
            factors.push(divisor);
            while value.is_multiple_of(divisor) {
                value /= divisor;
            }
        }
        divisor += 1;
    }
    if value > 1 {
        factors.push(value);
    }
    factors
}

#[cfg(test)]
mod tests {
    use super::*;

    // Two cross-checks against the base-field Hayes route
    // (`unweighted_cone_cancellation_does_not_imply_frobenius_cancellation`
    // and `connected_adams_trace_matches_base_field_hayes_moments`) live on
    // the `agent/gf2/lemire-proof` branch, which carries `gf2_hayes`. They
    // return here when `class_population_distribution` and the Sawin Euler
    // report are lifted out of that module.

    fn naive_extension_trace_sum(
        field_modulus: u64,
        polynomial_degree: usize,
        fixed_leading_coefficients: usize,
        limits: BinaryExtensionTraceLimits,
    ) -> u128 {
        let (field, free_coefficients, candidate_count) = extension_trace_domain(
            field_modulus,
            polynomial_degree,
            fixed_leading_coefficients,
            limits,
        )
        .unwrap();
        (0..candidate_count)
            .map(|encoded| {
                let mut digits = encoded;
                let mut polynomial = vec![0_u64; polynomial_degree + 1];
                for coefficient in polynomial.iter_mut().take(free_coefficients) {
                    *coefficient = digits % field.order;
                    digits /= field.order;
                }
                polynomial[polynomial_degree] = 1;
                polynomial_mangoldt(&polynomial, field).unwrap() as u128
            })
            .sum()
    }

    #[test]
    fn extension_field_long_cycle_traces_match_small_exact_formulas() {
        let limits = BinaryExtensionTraceLimits::default();
        let rows = [
            (0b11_u64, 1_usize, -2_i128),
            (0b111, 2, 12),
            (0b1011, 3, -56),
        ];
        for (modulus, extension_degree, expected_error) in rows {
            let report = binary_extension_long_cycle_trace(modulus, 5, 2, limits).unwrap();
            let power = u32::try_from(extension_degree).unwrap();
            assert_eq!(report.field_degree, extension_degree);
            assert_eq!(report.error, expected_error);
            assert_eq!(report.error, (-4_i128).pow(power) - (-2_i128).pow(power));
        }

        let degree_nine = binary_extension_long_cycle_trace(0b11, 9, 4, limits).unwrap();
        assert_eq!(degree_nine.candidate_count, 32);
        assert_eq!(degree_nine.mangoldt_sum, 37);
        assert_eq!(degree_nine.error, 5);

        for (modulus, expected_error) in [(0b111_u64, 129_i128), (0b1011, -1_771)] {
            let report = binary_extension_long_cycle_trace(modulus, 9, 4, limits).unwrap();
            assert_eq!(report.error, expected_error);
        }
    }

    #[test]
    fn ell_three_degree_seven_closed_form_matches_exact_populations() {
        let limits = BinaryExtensionTraceLimits::default();
        for (modulus, expected_trace) in
            [(0b11_u64, -393_216_i128), (0b111, 10_694_468_567_040_i128)]
        {
            let row = binary_extension_connected_adams_trace(modulus, 3, 7, limits).unwrap();
            let closed =
                binary_extension_ell_three_degree_seven_closed_form(row.field_degree, limits)
                    .unwrap();
            assert_eq!(row.connected_adams_trace, BigInt::from(expected_trace));
            assert_eq!(closed.field_order, BigUint::from(row.field_order));
            assert_eq!(
                closed.special_class_population,
                BigUint::from(row.identity_class_mangoldt_sum)
            );
            assert_eq!(closed.centered_second_moment, row.centered_second_moment);
            assert_eq!(closed.centered_fourth_moment, row.centered_fourth_moment);
            assert_eq!(
                closed.fourth_cumulant_numerator,
                row.fourth_cumulant_numerator
            );
            assert_eq!(closed.connected_adams_trace, row.connected_adams_trace);
        }

        let q16 = binary_extension_ell_three_degree_seven_closed_form(4, limits).unwrap();
        assert_eq!(q16.special_class_count, BigUint::from(16_u8));
        assert_eq!(q16.ordinary_class_count, BigUint::from(4_080_u16));
        assert_eq!(q16.centered_second_moment, BigUint::from(267_386_880_u32));
        assert_eq!(
            q16.centered_fourth_moment,
            BigUint::from(4_433_642_394_746_880_u64)
        );
        assert_eq!(
            q16.fourth_cumulant_numerator,
            BigInt::from(17_945_712_018_094_817_280_i128)
        );
        assert_eq!(
            q16.connected_adams_trace,
            BigInt::from(301_079_086_801_372_657_987_092_480_i128)
        );
        assert_eq!(q16.normalized_connected_q_degree, 8);
        assert_eq!(q16.proposed_normalized_q_degree, 6);
        assert_eq!(q16.one_extra_q_normalized_degree, 7);
        assert_eq!(q16.normalized_q_degree_excess, 2);

        for (field_degree, expected_failure) in [(6_usize, false), (7, true)] {
            let closed =
                binary_extension_ell_three_degree_seven_closed_form(field_degree, limits).unwrap();
            let geometric_scale = closed.field_order.pow(20);
            let one_extra_q_allowance =
                BigUint::from(81_u8) * &closed.field_order * geometric_scale;
            assert_eq!(
                closed.connected_adams_trace.magnitude() > &one_extra_q_allowance,
                expected_failure
            );
        }

        assert!(binary_extension_ell_three_degree_seven_closed_form(0, limits).is_err());
        let field_tight = BinaryExtensionTraceLimits {
            max_field_degree: 3,
            ..limits
        };
        assert!(matches!(
            binary_extension_ell_three_degree_seven_closed_form(4, field_tight),
            Err(BinaryExtensionTraceError::ResourceLimit(_))
        ));
    }

    #[test]
    fn witt_shifted_trace_matches_degree_seven_closed_form() {
        let limits = BinaryExtensionTraceLimits::default();
        for (modulus, field_degree) in [(0b11_u64, 1_usize), (0b111, 2)] {
            let report = binary_extension_witt_shifted_trace(modulus, 3, 7, 2, limits).unwrap();
            let closed = binary_extension_ell_three_degree_seven_witt_shifted_closed_form(
                field_degree,
                limits,
            )
            .unwrap();
            let q = &closed.field_order;
            assert_eq!(report.field_degree, field_degree);
            assert_eq!(report.layers.len(), 2);
            assert_eq!(
                report.aggregate_global_mass,
                q * &closed.supported_coarse_mass
            );
            assert_eq!(
                report.layers[0].identity_aggregate_mass,
                closed.supported_coarse_mass
            );
            assert_eq!(
                report.layers[0].signed_high_character_trace,
                closed.conductor_one_high_character_trace
            );
            assert!(report.layers[0].average_contraction_holds);
            assert_eq!(
                report.layers[1].identity_aggregate_mass,
                closed.supported_coarse_mass
            );
            assert_eq!(
                report.layers[1].signed_high_character_trace,
                closed.conductor_two_high_character_trace
            );
            assert!(!report.layers[1].average_contraction_holds);
            assert_eq!(closed.conductor_two_trace_q_degree, 11);
            assert_eq!(closed.formal_top_q_degree, 12);
            assert_eq!(closed.q_degree_drop, 1);
        }
    }

    #[test]
    fn witt_shifted_trace_declines_outside_its_exact_domain() {
        let limits = BinaryExtensionTraceLimits::default();
        assert!(binary_extension_witt_shifted_trace(0b11, 3, 7, 0, limits).is_err());
        assert!(binary_extension_witt_shifted_trace(0b11, 3, 7, 3, limits).is_err());
        assert!(binary_extension_witt_shifted_trace(0b11, 3, 6, 2, limits).is_err());
        assert!(
            binary_extension_ell_three_degree_seven_witt_shifted_closed_form(0, limits).is_err()
        );
    }

    #[test]
    fn connected_adams_shards_merge_exact_class_vectors() {
        let limits = BinaryExtensionTraceLimits::default();
        for (modulus, ell, degree) in [(0b11_u64, 2_usize, 5_usize), (0b111, 2, 5)] {
            let direct =
                binary_extension_connected_adams_trace(modulus, ell, degree, limits).unwrap();
            for shard_count in [2_u64, 3, 7] {
                let shards = (0..shard_count)
                    .map(|shard_index| {
                        binary_extension_connected_adams_trace_shard(
                            modulus,
                            ell,
                            degree,
                            shard_index,
                            shard_count,
                            limits,
                        )
                        .unwrap()
                    })
                    .collect::<Vec<_>>();
                let merged =
                    combine_binary_extension_connected_adams_trace_shards(&shards).unwrap();
                assert_eq!(merged, direct);
                assert_eq!(shards.first().unwrap().candidate_start, 0);
                assert_eq!(shards.last().unwrap().candidate_end, direct.candidate_count);

                let encoded = serde_json::to_string(&shards[0]).unwrap();
                assert_eq!(
                    serde_json::from_str::<BinaryExtensionConnectedAdamsTraceShardReport>(&encoded)
                        .unwrap(),
                    shards[0]
                );
            }
        }

        let shards = (0..2_u64)
            .map(|index| {
                binary_extension_connected_adams_trace_shard(0b11, 2, 5, index, 2, limits).unwrap()
            })
            .collect::<Vec<_>>();
        assert!(combine_binary_extension_connected_adams_trace_shards(&shards[..1]).is_err());
        assert!(
            combine_binary_extension_connected_adams_trace_shards(&[
                shards[0].clone(),
                shards[0].clone(),
            ])
            .is_err()
        );

        let mut bad_parameter = shards.clone();
        bad_parameter[1].ell = 3;
        assert!(combine_binary_extension_connected_adams_trace_shards(&bad_parameter).is_err());
        let mut bad_vector = shards.clone();
        bad_vector[1].class_mangoldt_populations.pop();
        assert!(combine_binary_extension_connected_adams_trace_shards(&bad_vector).is_err());
        let mut bad_population = shards;
        bad_population[0].class_mangoldt_populations[0] += 1;
        assert!(combine_binary_extension_connected_adams_trace_shards(&bad_population).is_err());

        assert!(binary_extension_connected_adams_trace_shard(0b11, 2, 5, 0, 0, limits).is_err());
        assert!(binary_extension_connected_adams_trace_shard(0b11, 2, 5, 2, 2, limits).is_err());
    }

    #[test]
    #[ignore = "33,554,432 exact extension-field candidates in the r=5 stopping row"]
    fn connected_adams_trace_extension_stopping_probe() {
        let limits = BinaryExtensionTraceLimits {
            max_field_degree: 5,
            max_polynomial_degree: 5,
            max_candidates: 34_000_000,
        };
        for (modulus, expected_trace, expected_ceiling, expected_passes) in [
            (
                0b10011_u64,
                BigInt::from(700_872_692_009_533_440_i128),
                BigUint::from(10_u8),
                true,
            ),
            (
                0b10_0101,
                BigInt::from(29_950_594_846_676_670_742_528_i128),
                BigUint::from(26_u8),
                false,
            ),
        ] {
            let row = binary_extension_connected_adams_trace(modulus, 2, 5, limits).unwrap();
            let closed =
                binary_extension_ell_two_degree_five_closed_form(row.field_degree, limits).unwrap();
            assert_eq!(row.connected_adams_trace, expected_trace);
            assert_eq!(row.connected_adams_trace, closed.connected_adams_trace);
            assert_eq!(row.minimum_normalized_betti_ceiling, expected_ceiling);
            assert_eq!(row.satisfies_candidate_bound, expected_passes);
            println!(
                "ell=2 r={} trace={} bound={} minimum_betti={} passes={}",
                row.field_degree,
                row.connected_adams_trace,
                row.candidate_absolute_bound,
                row.minimum_normalized_betti_ceiling,
                row.satisfies_candidate_bound
            );
        }
    }

    #[test]
    fn extension_field_trace_rejects_bad_moduli_and_candidate_excess() {
        let limits = BinaryExtensionTraceLimits::default();
        assert_eq!(
            binary_extension_long_cycle_trace(0b101, 5, 2, limits),
            Err(BinaryExtensionTraceError::ReducibleFieldModulus)
        );
        let tight = BinaryExtensionTraceLimits {
            max_candidates: 31,
            ..limits
        };
        assert!(matches!(
            binary_extension_long_cycle_trace(0b11, 9, 4, tight),
            Err(BinaryExtensionTraceError::ResourceLimit(_))
        ));
    }

    #[test]
    fn extension_field_trace_shards_merge_exactly_and_fail_closed() {
        let limits = BinaryExtensionTraceLimits::default();
        let direct = binary_extension_long_cycle_trace(0b111, 9, 4, limits).unwrap();
        let shards = (0_u64..7)
            .map(|shard_index| {
                binary_extension_long_cycle_trace_shard(0b111, 9, 4, shard_index, 7, limits)
                    .unwrap()
            })
            .collect::<Vec<_>>();
        assert_eq!(shards.first().unwrap().candidate_start, 0);
        assert_eq!(shards.last().unwrap().candidate_end, direct.candidate_count);
        assert_eq!(
            shards
                .windows(2)
                .map(|pair| (pair[0].candidate_end, pair[1].candidate_start))
                .collect::<Vec<_>>(),
            vec![
                (146, 146),
                (292, 292),
                (438, 438),
                (585, 585),
                (731, 731),
                (877, 877)
            ]
        );
        assert_eq!(
            combine_binary_extension_long_cycle_trace_shards(&shards).unwrap(),
            direct
        );
        let fine = (0_u64..35)
            .map(|shard_index| {
                binary_extension_long_cycle_trace_shard(0b111, 9, 4, shard_index, 35, limits)
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let collapsed = (0_u64..7)
            .map(|parent_index| {
                let start = usize::try_from(parent_index * 5).unwrap();
                collapse_binary_extension_long_cycle_trace_subshards(
                    &fine[start..start + 5],
                    parent_index,
                    7,
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        assert_eq!(collapsed, shards);
        assert_eq!(
            combine_binary_extension_long_cycle_trace_shards(&collapsed).unwrap(),
            direct
        );
        assert!(collapse_binary_extension_long_cycle_trace_subshards(&fine[..4], 0, 7).is_err());
        assert!(collapse_binary_extension_long_cycle_trace_subshards(&fine[..5], 0, 6).is_err());
        let encoded = serde_json::to_string(&shards[3]).unwrap();
        assert_eq!(
            serde_json::from_str::<BinaryExtensionLongCycleTraceShardReport>(&encoded).unwrap(),
            shards[3]
        );

        let mut missing = shards.clone();
        missing.pop();
        assert!(combine_binary_extension_long_cycle_trace_shards(&missing).is_err());
        let mut duplicated = shards.clone();
        duplicated[4] = duplicated[3].clone();
        assert!(combine_binary_extension_long_cycle_trace_shards(&duplicated).is_err());
        let mut mismatched = shards.clone();
        mismatched[6].polynomial_degree = 8;
        assert!(combine_binary_extension_long_cycle_trace_shards(&mismatched).is_err());
        assert!(binary_extension_long_cycle_trace_shard(0b111, 9, 4, 0, 0, limits).is_err());
        assert!(binary_extension_long_cycle_trace_shard(0b111, 9, 4, 7, 7, limits).is_err());
    }

    #[test]
    fn frobenius_orbit_compression_matches_naive_enumeration() {
        let limits = BinaryExtensionTraceLimits::default();
        for (field_modulus, polynomial_degree, fixed_leading_coefficients) in
            [(0b111_u64, 5_usize, 2_usize), (0b1011, 5, 2)]
        {
            let report = binary_extension_long_cycle_trace(
                field_modulus,
                polynomial_degree,
                fixed_leading_coefficients,
                limits,
            )
            .unwrap();
            assert_eq!(
                report.mangoldt_sum,
                naive_extension_trace_sum(
                    field_modulus,
                    polynomial_degree,
                    fixed_leading_coefficients,
                    limits,
                )
            );
        }

        let (field, _, candidate_count) = extension_trace_domain(0b1011, 5, 2, limits).unwrap();
        let mut owned_population = 0_usize;
        for encoded in 0..candidate_count {
            let mut digits = encoded;
            let coefficients = (0..3)
                .map(|_| {
                    let coefficient = digits % field.order;
                    digits /= field.order;
                    coefficient
                })
                .collect::<Vec<_>>();
            if let Some(orbit_size) =
                canonical_frobenius_orbit_size(encoded, &coefficients, field).unwrap()
            {
                owned_population += orbit_size;
            }
        }
        assert_eq!(owned_population, usize::try_from(candidate_count).unwrap());
    }

    #[test]
    fn extension_trace_hankel_minor_rules_out_two_modes_exactly() {
        let degree_nine_traces = [5_i128, 129, -1_771, -3_855, -28_675];
        let witness = extension_trace_hankel_minor(&degree_nine_traces, 1, 2).unwrap();
        assert_eq!(witness.determinant, BigInt::from(7_972_848_576_u64));
        assert!(witness.excludes_tested_order());

        let shifted_degree_nine_traces = [129_i128, -1_771, -3_855, -28_675, -277_767];
        let shifted = extension_trace_hankel_minor(&shifted_degree_nine_traces, 2, 2).unwrap();
        assert_eq!(shifted.determinant, BigInt::from(569_010_016_512_u64));
        assert!(shifted.excludes_tested_order());

        let seven_degree_nine_traces = [5_i128, 129, -1_771, -3_855, -28_675, -277_767, -2_479_675];
        let order_three = extension_trace_hankel_minor(&seven_degree_nine_traces, 1, 3).unwrap();
        assert_eq!(
            order_three.determinant,
            BigInt::from(-6_852_895_898_075_136_i64)
        );
        assert!(order_three.excludes_tested_order());

        let two_mode = (1_u32..=5)
            .map(|power| 3_i128.pow(power) - 2_i128.pow(power))
            .collect::<Vec<_>>();
        let zero = extension_trace_hankel_minor(&two_mode, 1, 2).unwrap();
        assert_eq!(zero.determinant, BigInt::from(0_u8));
        assert!(!zero.excludes_tested_order());

        let row_swap = extension_trace_hankel_minor(&[0, 1, 0], 1, 1).unwrap();
        assert_eq!(row_swap.determinant, BigInt::from(-1_i8));
        assert!(row_swap.excludes_tested_order());
        assert!(extension_trace_hankel_minor(&degree_nine_traces[..4], 1, 2).is_err());
        assert!(extension_trace_hankel_minor(&degree_nine_traces, 1, 0).is_err());
    }

    #[test]
    fn extension_field_mangoldt_recognizes_separable_and_inseparable_powers() {
        let field =
            BinaryExtensionField::new(0b111, BinaryExtensionTraceLimits::default()).unwrap();
        let irreducible_quadratic = vec![2, 1, 1];
        assert!(polynomial_is_irreducible(&irreducible_quadratic, field).unwrap());
        for exponent in [2_usize, 3, 6] {
            let power = poly_power(&irreducible_quadratic, exponent, field);
            assert_eq!(polynomial_mangoldt(&power, field).unwrap(), 2);
        }

        let first_linear = vec![1, 1];
        let second_linear = vec![2, 1];
        let mixed = poly_multiply(&first_linear, &second_linear, field);
        assert_eq!(polynomial_mangoldt(&mixed, field).unwrap(), 0);
    }

    #[test]
    #[ignore = "33,554,432-candidate long-cycle research probe"]
    fn extension_field_degree_nine_four_coefficient_probe() {
        let limits = BinaryExtensionTraceLimits {
            max_field_degree: 5,
            max_polynomial_degree: 9,
            max_candidates: 33_554_432,
        };
        let report = binary_extension_long_cycle_trace(0b10_0101, 9, 4, limits).unwrap();
        assert_eq!(report.field_order, 32);
        assert_eq!(report.candidate_count, 33_554_432);
        assert_eq!(report.mangoldt_sum, 33_525_757);
        assert_eq!(report.error, -28_675);
    }
}
