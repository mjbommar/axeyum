//! AC-Bridge phase-3 workstream 22 ((CDL) assault): the exact low-conductor
//! twisted spectrum of the squared endpoint discrepancy.
//!
//! Notation follows `docs/research/10-cas/ac-bridge-2026-08/00-charter.md` and
//! the residual lemma `(CDL)` of `13-angle-dichotomy.md`.  With
//! `D_e = N_n(e) - mu` on `G_ell`, `f_e = D_e^2` and
//! `fhat(chi) = sum_e D_e^2 chi(e)`, the target is
//!
//! ```text
//! (CDL)   sum_(cond(chi) = j) |fhat(chi)|^2  <=  M_2^2 / ell    for j <= c log2 ell.
//! ```
//!
//! This example computes `fhat(chi)` EXACTLY, as an element of the cyclotomic
//! ring `Z[zeta_N]`, `N = 2^K` the smallest power of two above the level cap,
//! for every character of conductor level `j <= jmax`, and asserts on every row
//!
//! * `fhat(1) = M_2`;
//! * `sum_(cond chi = j) |fhat(chi)|^2 = E_j` exactly -- the irrational part of
//!   the layer sum cancels and the rational part is the library's
//!   `exact_fourier_energy` (a genuine check of the character convention);
//! * the polynomial-pair identity, for every nontrivial `chi`,
//!   `fhat(chi) = sum_e N_n(e)^2 chi(e) - 2 mu S_chi`  (identity (PP)), whose
//!   left-hand double sum is the Mangoldt pair correlation
//!   `sum_(F,G monic deg n, <F> = <G>) Lambda(F) Lambda(G) chi(<F>)`;
//! * the proved coarse (pushforward) Weil bound `A_j <= 2^(n-j) Sigma_j` with
//!   `Sigma_j = sum_(i=2)^j 2^(i-1)(i-1)^2`, which is the bound that DOES hold
//!   for the index-`2^j` pair correlation, i.e. the object `(CDL)` is not.
//!
//! Emitted per level: `E_j`, `q_j = E_j/C_(j-1)`, the `(CDL)` budget
//! `M_2^2/ell` and the exact margin, the proved trivial bound `C_(j-1)`, and
//! the extreme per-character magnitudes against the pointwise sufficient form
//! `|fhat(chi)| <= M_2 ell^(-(c+2)/2)`.

// Printed diagnostics convert exact integers to f64 for ratios only; every
// retained quantity is an exact integer or an exact cyclotomic integer.
#![allow(clippy::cast_precision_loss)]

use axeyum_cas::gf2_hayes::{
    ClassPopulationDistribution, HayesLimits, PrincipalUnitFactor, class_population_distribution,
    principal_unit_structure,
};
use num_bigint::{BigInt, BigUint};
use num_traits::{Signed, ToPrimitive, Zero};

/// Exact element of `Z[zeta_N]`, `N = 2^K >= 2`, in the basis
/// `1, zeta, ..., zeta^(N/2 - 1)` (reduction `zeta^(N/2) = -1`).
#[derive(Clone, Debug, PartialEq, Eq)]
struct Cyc {
    order: usize,
    coefficients: Vec<BigInt>,
}

impl Cyc {
    fn zero(order: usize) -> Self {
        Self {
            order,
            coefficients: vec![BigInt::from(0_u8); order / 2],
        }
    }

    /// Add `value * zeta^exponent`.
    fn add_term(&mut self, exponent: usize, value: &BigInt) {
        let half = self.order / 2;
        let reduced = exponent % self.order;
        if reduced < half {
            self.coefficients[reduced] += value;
        } else {
            self.coefficients[reduced - half] -= value;
        }
    }

    fn add_assign(&mut self, other: &Self) {
        for (slot, value) in self.coefficients.iter_mut().zip(other.coefficients.iter()) {
            *slot += value;
        }
    }

    fn conjugate(&self) -> Self {
        let mut result = Self::zero(self.order);
        for (exponent, value) in self.coefficients.iter().enumerate() {
            result.add_term((self.order - exponent) % self.order, value);
        }
        result
    }

    fn multiply(&self, other: &Self) -> Self {
        let mut result = Self::zero(self.order);
        for (left_exponent, left) in self.coefficients.iter().enumerate() {
            if left.is_zero() {
                continue;
            }
            for (right_exponent, right) in other.coefficients.iter().enumerate() {
                if right.is_zero() {
                    continue;
                }
                result.add_term(left_exponent + right_exponent, &(left * right));
            }
        }
        result
    }

    /// `|z|^2 = z * conj(z)`, an exact element of the real subring.
    fn norm_square(&self) -> Self {
        self.multiply(&self.conjugate())
    }

    fn is_rational_integer(&self) -> Option<BigInt> {
        if self
            .coefficients
            .iter()
            .skip(1)
            .all(num_traits::Zero::is_zero)
        {
            Some(self.coefficients[0].clone())
        } else {
            None
        }
    }

    /// Numerical magnitude, for printed ratios only.
    fn magnitude(&self) -> f64 {
        let mut real = 0.0_f64;
        let mut imaginary = 0.0_f64;
        for (exponent, value) in self.coefficients.iter().enumerate() {
            let angle = 2.0 * std::f64::consts::PI * (exponent as f64) / (self.order as f64);
            let scaled = big_to_f64(value);
            real += scaled * angle.cos();
            imaginary += scaled * angle.sin();
        }
        real.hypot(imaginary)
    }
}

fn big_to_f64(value: &BigInt) -> f64 {
    value.to_f64().unwrap_or_else(|| {
        let bits = value.magnitude().bits();
        let shift = bits.saturating_sub(800);
        let head = value.magnitude() >> shift;
        let scaled = head.to_f64().unwrap_or(f64::NAN) * (shift as f64).exp2();
        if value.is_negative() { -scaled } else { scaled }
    })
}

fn log2_f64(value: &BigUint) -> f64 {
    if value.is_zero() {
        return f64::NEG_INFINITY;
    }
    let bits = value.bits();
    if bits <= 900 {
        value.to_f64().map_or(f64::NAN, f64::log2)
    } else {
        let shift = bits - 800;
        let head = value >> shift;
        head.to_f64()
            .map_or(f64::NAN, |head| head.log2() + (shift as f64))
    }
}

fn ratio(numerator: &BigUint, denominator: &BigUint) -> f64 {
    (log2_f64(numerator) - log2_f64(denominator)).exp2()
}

/// The factor list of `E_level`, rebuilt independently of the library helper.
fn factors_of(level: usize) -> Vec<PrincipalUnitFactor> {
    (1..=level)
        .step_by(2)
        .map(|odd_degree| {
            let mut order = 1_usize;
            while odd_degree <= level / order {
                order *= 2;
            }
            PrincipalUnitFactor { odd_degree, order }
        })
        .collect()
}

/// Mixed-radix coordinates of `index` in `E_ell`, reduced into `E_level`.
fn project_coordinates(index: usize, full: &[PrincipalUnitFactor], level: usize) -> Vec<usize> {
    let quotient = factors_of(level);
    let mut remainder = index;
    let mut coordinates = Vec::with_capacity(quotient.len());
    let mut cursor = 0_usize;
    for factor in full {
        let coordinate = remainder % factor.order;
        remainder /= factor.order;
        if let Some(target) = quotient.get(cursor)
            && target.odd_degree == factor.odd_degree
        {
            coordinates.push(coordinate % target.order);
            cursor += 1;
        }
    }
    coordinates
}

fn cylinder_index(coordinates: &[usize], quotient: &[PrincipalUnitFactor]) -> usize {
    let mut index = 0_usize;
    let mut stride = 1_usize;
    for (coordinate, factor) in coordinates.iter().zip(quotient.iter()) {
        index += coordinate * stride;
        stride *= factor.order;
    }
    index
}

/// `Sigma_j = sum_(i=2)^j 2^(i-1) (i-1)^2`; `Sigma_ell` is the charter's `Sigma(ell)`.
fn sigma_upto(level: usize) -> BigUint {
    (2..=level).fold(BigUint::from(0_u8), |total, i| {
        total + (BigUint::from(i - 1).pow(2) << (i - 1))
    })
}

/// Conductor level of a character of `E_level` given by dual coordinates.
///
/// `chi` is trivial on `ker(E_level -> E_j)` iff every coordinate above `j`
/// vanishes and, for `i <= j`, `order_j(i)` divides `c_i * order_j(i) mod order_level(i)`,
/// i.e. `order_level(i)/order_j(i)` divides `c_i`.
fn conductor_level(duals: &[usize], level: usize) -> usize {
    let full = factors_of(level);
    for candidate in 0..=level {
        let quotient = factors_of(candidate);
        let mut trivial = true;
        for (position, factor) in full.iter().enumerate() {
            let dual = duals[position];
            match quotient.get(position) {
                Some(target) if target.odd_degree == factor.odd_degree => {
                    let step = factor.order / target.order;
                    if !(dual % step == 0) {
                        trivial = false;
                    }
                }
                _ => {
                    if dual != 0 {
                        trivial = false;
                    }
                }
            }
            if !trivial {
                break;
            }
        }
        if trivial {
            return candidate;
        }
    }
    level
}

struct LevelData {
    masses: Vec<BigUint>,
    signed: Vec<BigInt>,
    population: Vec<BigUint>,
    population_square: Vec<BigUint>,
}

#[allow(clippy::too_many_lines)]
fn emit_row(
    ell: usize,
    degree: usize,
    level_cap: usize,
    limits: HayesLimits,
) -> Result<(), String> {
    let distribution: ClassPopulationDistribution =
        class_population_distribution(ell, degree, limits).map_err(|error| error.to_string())?;
    let classes = distribution.counts.len();
    if classes != 1_usize << ell {
        return Err(format!("class count {classes} is not 2^{ell}"));
    }
    let mean = u128::from(1_u8) << (degree - ell);
    let _mean_big = BigUint::from(mean);
    let structure = principal_unit_structure(ell, limits).map_err(|error| error.to_string())?;
    let full = structure.factors.clone();
    if factors_of(ell) != full {
        return Err("independent factor list disagrees with the library".to_owned());
    }

    let signed_all = distribution
        .counts
        .iter()
        .map(|count| BigInt::from(*count) - BigInt::from(mean))
        .collect::<Vec<_>>();
    if signed_all.iter().sum::<BigInt>() != BigInt::from(0_u8) {
        return Err("class discrepancies are not mean zero".to_owned());
    }
    let squared_all = signed_all
        .iter()
        .map(|value| value.magnitude().pow(2))
        .collect::<Vec<_>>();
    let m2 = squared_all.iter().sum::<BigUint>();
    let m4 = squared_all
        .iter()
        .map(|value| value.pow(2))
        .sum::<BigUint>();
    let m2_square = m2.pow(2);

    let library = distribution
        .fourth_moment_conductor_decomposition(limits.max_table_cells)
        .map_err(|error| error.to_string())?;
    if library.second_moment != m2 || library.fourth_moment != m4 {
        return Err("library conductor decomposition disagrees on the moments".to_owned());
    }

    let cap = level_cap.min(ell);
    // Cyclotomic order: every character of conductor <= cap takes values in
    // mu_N with N the smallest power of two exceeding cap (the order of the
    // coordinate of the generator 1 + x in E_cap).
    let mut cyclotomic_order = 2_usize;
    while cyclotomic_order <= cap {
        cyclotomic_order *= 2;
    }

    let mut level_data = Vec::with_capacity(cap + 1);
    for level in 0..=cap {
        let quotient = factors_of(level);
        let cylinders = 1_usize << level;
        let mut masses = vec![BigUint::from(0_u8); cylinders];
        let mut signed = vec![BigInt::from(0_u8); cylinders];
        let mut population = vec![BigUint::from(0_u8); cylinders];
        let mut population_square = vec![BigUint::from(0_u8); cylinders];
        for index in 0..classes {
            let cylinder = if level == 0 {
                0
            } else {
                cylinder_index(&project_coordinates(index, &full, level), &quotient)
            };
            masses[cylinder] += &squared_all[index];
            signed[cylinder] += &signed_all[index];
            let count = BigUint::from(distribution.counts[index]);
            population_square[cylinder] += &count * &count;
            population[cylinder] += count;
        }
        if masses.iter().sum::<BigUint>() != m2 {
            return Err(format!("cylinder masses miss M_2 at level {level}"));
        }
        level_data.push(LevelData {
            masses,
            signed,
            population,
            population_square,
        });
    }

    let mut previous_energy = m2_square.clone();
    let mut level_rows = Vec::with_capacity(cap + 1);
    let mut character_rows = Vec::new();
    for level in 1..=cap {
        let data = &level_data[level];
        let quotient = factors_of(level);
        let cylinders = 1_usize << level;
        let energy =
            BigUint::from(cylinders) * data.masses.iter().map(|mass| mass.pow(2)).sum::<BigUint>();
        if energy < previous_energy || energy > BigUint::from(2_u8) * &previous_energy {
            return Err(format!("Lemma D1 violated at level {level}"));
        }
        let exact_energy = &energy - &previous_energy;
        let library_row = &library.levels[level - 1];
        if library_row.level != level
            || library_row.cumulative_fourier_energy != energy
            || library_row.exact_fourier_energy != exact_energy
        {
            return Err(format!(
                "library conductor energy disagrees at level {level}"
            ));
        }

        // Enumerate every character of E_level; keep those of exact conductor.
        let mut layer_sum = Cyc::zero(cyclotomic_order);
        let mut layer_count = 0_usize;
        let mut max_magnitude = 0.0_f64;
        let mut min_magnitude = f64::INFINITY;
        let mut duals = vec![0_usize; quotient.len()];
        for _ in 0..cylinders {
            if conductor_level(&duals, level) == level {
                layer_count += 1;
                let mut transform = Cyc::zero(cyclotomic_order);
                let mut population_transform = Cyc::zero(cyclotomic_order);
                let mut population_square_transform = Cyc::zero(cyclotomic_order);
                let mut cylinder_duals = vec![0_usize; quotient.len()];
                for cylinder in 0..cylinders {
                    let mut exponent = 0_usize;
                    for (position, factor) in quotient.iter().enumerate() {
                        exponent += duals[position]
                            * cylinder_duals[position]
                            * (cyclotomic_order / factor.order);
                    }
                    transform.add_term(exponent, &BigInt::from(data.masses[cylinder].clone()));
                    population_transform
                        .add_term(exponent, &BigInt::from(data.population[cylinder].clone()));
                    population_square_transform.add_term(
                        exponent,
                        &BigInt::from(data.population_square[cylinder].clone()),
                    );
                    // odometer over cylinder coordinates
                    for (position, factor) in quotient.iter().enumerate() {
                        cylinder_duals[position] += 1;
                        if cylinder_duals[position] < factor.order {
                            break;
                        }
                        cylinder_duals[position] = 0;
                    }
                }
                // (PP): fhat(chi) = sum_e N_e^2 chi(e) - 2 mu S_chi.
                let mut pair_form = population_square_transform.clone();
                let mut correction = Cyc::zero(cyclotomic_order);
                for (exponent, value) in population_transform.coefficients.iter().enumerate() {
                    correction.add_term(
                        exponent,
                        &(-BigInt::from(2_u8) * BigInt::from(mean) * value),
                    );
                }
                pair_form.add_assign(&correction);
                if pair_form != transform {
                    return Err(format!(
                        "polynomial-pair identity (PP) fails at level {level}"
                    ));
                }
                let magnitude = transform.magnitude();
                max_magnitude = max_magnitude.max(magnitude);
                min_magnitude = min_magnitude.min(magnitude);
                let norm = transform.norm_square();
                layer_sum.add_assign(&norm);
                if level <= 3 {
                    character_rows.push(format!(
                        "ACB_CDL_CHAR|ell={ell}|degree={degree}|j={level}|\
duals={duals:?}|abs_fhat_over_M2={share:.12e}",
                        share = magnitude / big_to_f64(&BigInt::from(m2.clone())),
                    ));
                }
            }
            for (position, factor) in quotient.iter().enumerate() {
                duals[position] += 1;
                if duals[position] < factor.order {
                    break;
                }
                duals[position] = 0;
            }
        }
        if layer_count != cylinders / 2 {
            return Err(format!(
                "exact-conductor character count {layer_count} is not 2^(j-1) at level {level}"
            ));
        }
        let layer_total = layer_sum
            .is_rational_integer()
            .ok_or_else(|| format!("layer sum is irrational at level {level}"))?;
        if layer_total != BigInt::from(exact_energy.clone()) {
            return Err(format!(
                "layer sum of |fhat|^2 disagrees with E_j at level {level}"
            ));
        }

        // Proved coarse (pushforward) Weil bound: A_j <= 2^(n-j) Sigma_j.
        let pushforward = data
            .signed
            .iter()
            .map(|value| value.magnitude().pow(2))
            .sum::<BigUint>();
        let coarse_allowance = sigma_upto(level) << (degree - level);
        let coarse_holds = pushforward <= coarse_allowance;
        if !coarse_holds {
            return Err(format!(
                "proved coarse Weil bound A_j fails at level {level}"
            ));
        }

        let budget = &m2_square / BigUint::from(ell);
        let cdl_holds = exact_energy <= budget;
        let imbalance = ratio(&exact_energy, &previous_energy);
        level_rows.push(format!(
            "ACB_CDL_LEVEL|ell={ell}|degree={degree}|j={level}|characters={layer_count}|\
E_j={exact_energy}|q_j={imbalance:.12e}|ell_q_j={scaled:.9}|cdl_holds={cdl_holds}|\
cdl_margin={margin:.6e}|max_abs_fhat_over_M2={max_share:.9e}|\
min_abs_fhat_over_M2={min_share:.9e}|pointwise_requirement={requirement:.9e}|\
A_j={pushforward}|coarse_weil_allowance={coarse_allowance}|coarse_ratio={coarse_ratio:.6e}",
            scaled = imbalance * (ell as f64),
            margin = ratio(&budget, &exact_energy),
            max_share = max_magnitude / big_to_f64(&BigInt::from(m2.clone())),
            min_share = min_magnitude / big_to_f64(&BigInt::from(m2.clone())),
            requirement = (ell as f64).powf(-(4.1 + 2.0) / 2.0),
            coarse_ratio = ratio(&pushforward, &coarse_allowance),
        ));
        previous_energy = energy;
    }

    // fhat(1) = M_2, exactly.
    let root_transform = level_data[0].masses[0].clone();
    if root_transform != m2 {
        return Err("fhat(1) is not M_2".to_owned());
    }

    let root_ratio = ratio(&(BigUint::from(classes) * &m4), &m2_square);
    println!(
        "ACB_CDL_TWIST|status=PASS|ell={ell}|degree={degree}|parity={parity}|\
M_2={m2}|M_4={m4}|R_0={root_ratio:.9}|level_cap={cap}|cyclotomic_order={cyclotomic_order}|\
cdl_budget={budget}|m2_over_ell_2n={normalized:.6}",
        parity = if degree % 2 == 0 { "even" } else { "odd" },
        budget = &m2_square / BigUint::from(ell),
        normalized = ratio(&m2, &(BigUint::from(ell) << degree)),
    );
    for row in level_rows {
        println!("{row}");
    }
    for row in character_rows {
        println!("{row}");
    }
    Ok(())
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args().skip(1);
    let first = arguments
        .next()
        .map_or(Ok(2), |value| value.parse::<usize>())
        .map_err(|_| "ell bounds must be integers".to_owned())?;
    let last = arguments
        .next()
        .map_or(Ok(first), |value| value.parse::<usize>())
        .map_err(|_| "ell bounds must be integers".to_owned())?;
    let cap = arguments
        .next()
        .map_or(Ok(6), |value| value.parse::<usize>())
        .map_err(|_| "level cap must be an integer".to_owned())?;
    if arguments.next().is_some() || first < 2 || last < first {
        return Err("usage: acb_cdl_twist [ell_min] [ell_max] [level_cap]".to_owned());
    }
    let limits = HayesLimits {
        max_ell: 24,
        max_degree: 50,
        max_group_order: 1 << 24,
        max_table_cells: 900_000_000,
    };
    for ell in first..=last {
        for degree in [2 * ell + 1, 2 * ell + 2] {
            emit_row(ell, degree, cap, limits)?;
        }
    }
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("ACB_CDL_TWIST|status=FAIL|error={error}");
        std::process::exit(1);
    }
}
