//! Exact bounded Hayes type-II class computations over `GF(2)`.
//!
//! This module supplies the reusable algebra behind the Lemire endpoint
//! experiment. Search and asymptotic conjectures remain untrusted: the public
//! operations compute exact integral class counts using two modular transforms
//! and CRT, with explicit admission limits and residue checks.

use std::collections::BTreeMap;
use std::fmt;

use num_bigint::{BigInt, BigUint};
use serde::{Deserialize, Serialize};

const PRIME_ONE: u64 = 998_244_353;
const PRIME_TWO: u64 = 1_004_535_809;
const PRIMITIVE_ROOT: u64 = 3;

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
                * buckets
                    .into_iter()
                    .map(|bucket| bucket.pow(2))
                    .sum::<BigUint>();
            if cumulative < previous {
                return Err(HayesError::Invariant(format!(
                    "squared-discrepancy Fourier energy decreases at level {level}"
                )));
            }
            let exact = &cumulative - &previous;
            levels.push(SquaredDeviationConductorLevel {
                level,
                cumulative_fourier_energy: cumulative.clone(),
                exact_fourier_energy: exact,
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
    Ok((mangoldt.swap_remove(target), dimensions))
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
    fn class_mobius_distribution_matches_independent_factorization() {
        let limits = HayesLimits::default();
        for ell in 1_usize..=5 {
            let unit_to_index = principal_unit_index_map(ell);
            for degree in 1_usize..=8 {
                let report = class_mobius_distribution(ell, degree, limits).unwrap();
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
            (BigUint::from(1_u8) << 8) * decomposition.fourth_moment
        );
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
