//! Exact bounded Hayes type-II class computations over `GF(2)`.
//!
//! This module supplies the reusable algebra behind the Lemire endpoint
//! experiment. Search and asymptotic conjectures remain untrusted: the public
//! operations compute exact integral class counts using two modular transforms
//! and CRT, with explicit admission limits and residue checks.

use std::collections::BTreeMap;
use std::fmt;

use num_bigint::BigUint;
use serde::{Deserialize, Serialize};

const PRIME_ONE: u64 = 998_244_353;
const PRIME_TWO: u64 = 1_004_535_809;
const PRIMITIVE_ROOT: u64 = 3;

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
    Ok(layers)
}

fn admit(ell: usize, degree: usize, limits: HayesLimits) -> Result<(), HayesError> {
    if ell == 0 {
        return Err(HayesError::InvalidParameter(
            "ell must be positive".to_owned(),
        ));
    }
    if degree < ell {
        return Err(HayesError::InvalidParameter(format!(
            "degree {degree} is smaller than ell {ell}"
        )));
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

fn identity_class_residue(ell: usize, target: usize, modulus: u64) -> Result<u64, HayesError> {
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

    let mut mangoldt = vec![vec![0_u64; size]; target + 1];
    for degree in 1..=target {
        for character in 0..size {
            let class_sum = |class_degree: usize| {
                if class_degree < ell {
                    class_sums[class_degree][character]
                } else if character == 0 {
                    powers_of_two[class_degree]
                } else {
                    0
                }
            };
            let mut value = multiply_mod(degree as u64 % modulus, class_sum(degree), modulus);
            for (earlier, earlier_values) in mangoldt.iter().enumerate().take(degree).skip(1) {
                let correction = multiply_mod(
                    earlier_values[character],
                    class_sum(degree - earlier),
                    modulus,
                );
                value = subtract_mod(value, correction, modulus);
            }
            mangoldt[degree][character] = value;
        }
    }
    let sum = mangoldt[target].iter().fold(0_u64, |accumulator, value| {
        add_mod(accumulator, *value, modulus)
    });
    Ok(multiply_mod(
        sum,
        mod_pow(size as u64, modulus - 2, modulus),
        modulus,
    ))
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
