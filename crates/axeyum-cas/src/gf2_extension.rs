//! Bounded exact short-interval traces over binary extension fields.
//!
//! This module evaluates the fixed-polynomial-degree, varying-base-field
//! Frobenius traces used by the long-cycle diagnostic.  It is deliberately
//! separate from [`crate::gf2_hayes`]: a degree-`n` interval over
//! `GF(2^r)` is not the degree-`rn` identity population over `GF(2)`.

use core::fmt;

use num_bigint::BigInt;
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
