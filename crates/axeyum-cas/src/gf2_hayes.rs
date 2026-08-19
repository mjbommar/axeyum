//! Exact bounded Hayes type-II class computations over `GF(2)`.
//!
//! This module supplies the reusable algebra behind the Lemire endpoint
//! experiment. Search and asymptotic conjectures remain untrusted: the public
//! operations compute exact integral class counts using two modular transforms
//! and CRT, with explicit admission limits and residue checks.

use std::collections::BTreeMap;
use std::fmt;
use std::sync::{Mutex, OnceLock};

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
    let derivative = binary_formal_derivative(polynomial, degree);
    let integral_discriminant_is_odd = polynomial_gcd_packed(polynomial, derivative) == 1;
    if integral_discriminant_is_odd != (mobius != 0) {
        return Err(HayesError::Invariant(
            "discriminant parity and factorization disagree on squarefreeness".to_owned(),
        ));
    }
    let discriminant = integral_discriminant_is_odd
        .then(|| binary_integral_discriminant_mod_eight(polynomial, degree))
        .transpose()?;
    let kronecker_two_discriminant = discriminant.map_or(0, kronecker_two_mod_eight);
    let degree_sign = if degree.is_multiple_of(2) { 1 } else { -1 };
    if degree_sign * kronecker_two_discriminant != mobius {
        return Err(HayesError::Invariant(
            "dyadic discriminant character and polynomial Mobius value disagree".to_owned(),
        ));
    }
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
        let discriminant = discriminant.ok_or_else(|| {
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
        integral_discriminant_mod_eight: discriminant,
        integral_discriminant_is_odd,
        kronecker_two_discriminant,
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
        assert!(quadratic.integral_discriminant_is_odd);
        assert_eq!(quadratic.kronecker_two_discriminant, -1);
        assert_eq!(quadratic.arf_invariant, Some(1));
        assert_eq!(quadratic.arf_degree_correction, 0);
        assert_eq!(quadratic.sign_phase, Some(1));
        let irreducible_cubic = binary_second_trace_arf_report(0b1011, 3).unwrap();
        assert_eq!(irreducible_cubic.mobius, -1);
        assert_eq!(irreducible_cubic.integral_discriminant_mod_eight, Some(1));
        assert!(irreducible_cubic.integral_discriminant_is_odd);
        assert_eq!(irreducible_cubic.kronecker_two_discriminant, 1);
        assert_eq!(irreducible_cubic.arf_invariant, Some(1));
        assert_eq!(irreducible_cubic.arf_degree_correction, 1);
        assert_eq!(irreducible_cubic.sign_phase, Some(0));
        let reducible_cubic = binary_second_trace_arf_report(0b1001, 3).unwrap();
        assert_eq!(reducible_cubic.mobius, 1);
        assert_eq!(reducible_cubic.integral_discriminant_mod_eight, Some(5));
        assert!(reducible_cubic.integral_discriminant_is_odd);
        assert_eq!(reducible_cubic.kronecker_two_discriminant, -1);
        assert_eq!(reducible_cubic.arf_invariant, Some(0));
        assert_eq!(reducible_cubic.arf_degree_correction, 1);
        assert_eq!(reducible_cubic.sign_phase, Some(1));
        let squareful = binary_second_trace_arf_report(0b101, 2).unwrap();
        assert_eq!(squareful.mobius, 0);
        assert_eq!(squareful.integral_discriminant_mod_eight, None);
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
                    assert!(!report.integral_discriminant_is_odd);
                    assert_eq!(report.kronecker_two_discriminant, 0);
                    assert_eq!(report.integral_discriminant_mod_eight, None);
                    assert_eq!(report.arf_invariant, None);
                    assert_eq!(report.sign_phase, None);
                } else {
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
