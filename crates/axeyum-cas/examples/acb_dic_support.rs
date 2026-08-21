//! AC-Bridge workstream C: the support-set-resolved spectral mass profile of
//! the endpoint discrepancy (diary 01's open item `(L2-3)`).
//!
//! `G_ell = prod_(i odd, i<=ell) Z/2^(k_i)` is an exact product group, so its
//! Efron--Stein decomposition is exact and its layers are indexed by coordinate
//! support sets `S`.  For each `S` this example computes, by subgroup Parseval
//! plus Boolean-lattice Mobius inversion and in exact integer arithmetic,
//!
//! ```text
//! mass(S) = sum_(chi : supp chi = S) |S_chi|^2 ,      sum_S mass(S) = 2^ell M_2
//! f_S     = mass(S) / (2^ell M_2)
//! ```
//!
//! and then evaluates the sharp tensorized hypercontractive functional of
//! diary 01 `(L2-3)`
//!
//! ```text
//! R_0 <= ( sum_S A_S sqrt(f_S) )^4 ,   A_S = prod_(i in S) rho_c(2^(k_i))^(-1)
//! rho_c(m) = sqrt( sinh(u/4) / sinh(3u/4) ),   u = log(m-1)
//! ```
//!
//! against the same functional evaluated on diary 01's uniform-mass model
//! `f_S^unif = prod_(i in S) (2^(k_i)-1) / 2^ell`.  Diary 01 predicts the true
//! profile is WORSE than the uniform-mass model because the `k_i = 1`
//! coordinates carry the top conductor levels; this example decides it.
//!
//! The weight-grouped totals are cross-checked against the library's own
//! `efron_stein_spectral_weight_report`.

// Printed diagnostics convert exact integers to f64 for ratios only; the
// retained quantities are exact.
#![allow(clippy::cast_precision_loss)]

use axeyum_cas::gf2_hayes::{
    HayesLimits, PrincipalUnitFactor, class_population_distribution, principal_unit_structure,
};
use num_bigint::BigUint;

fn main() {
    if let Err(error) = run() {
        eprintln!("ACB_DIC_SUPPORT|status=FAIL|error={error}");
        std::process::exit(1);
    }
}

/// Sharp Latala--Oleszkiewicz/Wolff `(2,4)` threshold for a uniform `m`-point
/// alphabet, `rho_c(m) = sqrt(sinh(u/4)/sinh(3u/4))`, `u = log(m-1)`.
fn rho_critical(m: usize) -> f64 {
    if m == 2 {
        // u -> 0, sinh(u/4)/sinh(3u/4) -> 1/3: the sharp two-point value.
        return (1.0_f64 / 3.0).sqrt();
    }
    let u = ((m - 1) as f64).ln();
    (((u / 4.0).sinh()) / ((3.0 * u / 4.0).sinh())).sqrt()
}

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

#[allow(clippy::too_many_lines)]
fn emit_row(ell: usize, degree: usize, limits: HayesLimits) -> Result<(), String> {
    let distribution =
        class_population_distribution(ell, degree, limits).map_err(|error| error.to_string())?;
    let classes = distribution.counts.len();
    let mean = u128::from(1_u8) << (degree - ell);
    let structure = principal_unit_structure(ell, limits).map_err(|error| error.to_string())?;
    let factors = structure.factors.clone();
    if factors_of(ell) != factors {
        return Err("independent factor list disagrees with the library".to_owned());
    }
    let coordinates = factors.len();
    let subsets = 1_usize << coordinates;
    let weights = factors
        .iter()
        .map(|factor| factor.order.trailing_zeros() as usize)
        .collect::<Vec<_>>();
    if weights.iter().sum::<usize>() != ell {
        return Err("Witt weights do not sum to ell".to_owned());
    }

    let signed = distribution
        .counts
        .iter()
        .map(|count| {
            i128::try_from(*count).unwrap_or(i128::MAX) - i128::try_from(mean).unwrap_or(i128::MAX)
        })
        .collect::<Vec<_>>();
    let m2 = signed.iter().map(|value| value * value).sum::<i128>();
    let total_mass = (classes as i128)
        .checked_mul(m2)
        .ok_or_else(|| "spectral mass overflows i128".to_owned())?;

    // Precompute the mixed-radix coordinates of every class once.
    let mut digits = vec![0_usize; classes * coordinates];
    for index in 0..classes {
        let mut remainder = index;
        for (slot, factor) in factors.iter().enumerate() {
            digits[index * coordinates + slot] = remainder % factor.order;
            remainder /= factor.order;
        }
    }

    let mut exact = vec![0_i128; subsets];
    for subset in 0..subsets {
        let mut order = 1_usize;
        let mut strides = vec![0_usize; coordinates];
        for slot in 0..coordinates {
            if subset & (1 << slot) != 0 {
                strides[slot] = order;
                order *= factors[slot].order;
            }
        }
        let mut buckets = vec![0_i128; order];
        for index in 0..classes {
            let mut projected = 0_usize;
            for slot in 0..coordinates {
                if subset & (1 << slot) != 0 {
                    projected += digits[index * coordinates + slot] * strides[slot];
                }
            }
            buckets[projected] += signed[index];
        }
        let cumulative = (order as i128)
            .checked_mul(buckets.iter().map(|value| value * value).sum::<i128>())
            .ok_or_else(|| "cumulative subgroup mass overflows i128".to_owned())?;
        let mut value = cumulative;
        if subset != 0 {
            let mut proper = (subset - 1) & subset;
            loop {
                value -= exact[proper];
                if proper == 0 {
                    break;
                }
                proper = (proper - 1) & subset;
            }
        }
        if value < 0 {
            return Err(format!("exact support mass is negative at subset {subset}"));
        }
        exact[subset] = value;
    }
    if exact.iter().sum::<i128>() != total_mass {
        return Err("support masses miss Parseval".to_owned());
    }

    // Library cross-check on the weight-grouped totals.
    let library = distribution
        .efron_stein_spectral_weight_report(limits.max_table_cells)
        .map_err(|error| error.to_string())?;
    let mut grouped = vec![0_i128; ell + 1];
    for (subset, mass) in exact.iter().enumerate() {
        let weight = (0..coordinates)
            .filter(|slot| subset & (1 << slot) != 0)
            .map(|slot| weights[slot])
            .sum::<usize>();
        grouped[weight] += mass;
    }
    for row in &library.weights {
        let mine = BigUint::from(u128::try_from(grouped[row.weight]).unwrap_or(0));
        if mine != row.spectral_second_moment {
            return Err(format!(
                "weight-{} mass disagrees with the library",
                row.weight
            ));
        }
    }

    // The sharp per-coordinate costs and the two functionals.
    let costs = factors
        .iter()
        .map(|factor| 1.0 / rho_critical(factor.order))
        .collect::<Vec<_>>();
    let total = total_mass as f64;
    let mut measured = 0.0_f64;
    let mut uniform = 0.0_f64;
    let mut top_weight_mass = 0.0_f64;
    let mut full_support_mass = 0.0_f64;
    for (subset, mass) in exact.iter().enumerate() {
        let mut cost = 1.0_f64;
        let mut characters = 1.0_f64;
        for slot in 0..coordinates {
            if subset & (1 << slot) != 0 {
                cost *= costs[slot];
                characters *= (factors[slot].order - 1) as f64;
            }
        }
        let share = *mass as f64 / total;
        measured += cost * share.sqrt();
        uniform += cost * (characters / (classes as f64)).sqrt();
        if subset == subsets - 1 {
            full_support_mass = share;
        }
        if subset != 0 {
            top_weight_mass += share;
        }
    }
    // The coarser weight grading, with the worst support pattern per weight.
    let mut weight_cost = vec![0.0_f64; ell + 1];
    let mut weight_characters = vec![0.0_f64; ell + 1];
    for subset in 0..exact.len() {
        let mut cost = 1.0_f64;
        let mut characters = 1.0_f64;
        let mut weight = 0_usize;
        for slot in 0..coordinates {
            if subset & (1 << slot) != 0 {
                cost *= costs[slot];
                characters *= (factors[slot].order - 1) as f64;
                weight += weights[slot];
            }
        }
        if cost > weight_cost[weight] {
            weight_cost[weight] = cost;
        }
        weight_characters[weight] += characters;
    }
    let mut weight_measured = 0.0_f64;
    let mut weight_uniform = 0.0_f64;
    for weight in 0..=ell {
        if weight_cost[weight] == 0.0 {
            continue;
        }
        let share = grouped[weight] as f64 / total;
        weight_measured += weight_cost[weight] * share.sqrt();
        weight_uniform +=
            weight_cost[weight] * (weight_characters[weight] / (classes as f64)).sqrt();
    }

    let measured_bound = 4.0 * measured.log2();
    let uniform_bound = 4.0 * uniform.log2();
    let uniform_full = factors
        .iter()
        .map(|factor| (factor.order - 1) as f64)
        .product::<f64>()
        / (classes as f64);

    // Sufficiency reference: the route must reach R_0 <= 2^ell (mu-1)^4/(mu Sigma)^2.
    let sigma = (2..=ell).fold(0.0_f64, |total, j| {
        total + ((j - 1) as f64).powi(2) * (2.0_f64).powi(i32::try_from(j - 1).unwrap_or(0))
    });
    let mean_log2 = (degree - ell) as f64;
    let sufficient = ell as f64 + 4.0 * mean_log2 - 2.0 * (mean_log2 + sigma.log2());

    println!(
        "ACB_DIC_SUPPORT|status=PASS|ell={ell}|degree={degree}|parity={parity}|\
coordinates={coordinates}|subsets={subsets}|k_list={klist}|\
M_2={m2}|total_spectral_mass={total_mass}|\
full_support_mass_fraction={full_support_mass:.9}|uniform_full_support_fraction={uniform_full:.9}|\
nontrivial_mass_fraction={top_weight_mass:.9}|\
measured_functional={measured:.6}|log2_measured_R0_bound={measured_bound:.6}|\
uniform_functional={uniform:.6}|log2_uniform_R0_bound={uniform_bound:.6}|\
measured_minus_uniform={delta:.6}|measured_worse_than_uniform={worse}|\
log2_sufficient_R0={sufficient:.6}|route_closes={closes}|\
weight_measured_functional={weight_measured:.6}|log2_weight_measured_R0_bound={weight_bound:.6}|\
log2_weight_uniform_R0_bound={weight_uniform_bound:.6}|\
weight_measured_worse={weight_worse}",
        parity = if degree.is_multiple_of(2) {
            "even"
        } else {
            "odd"
        },
        klist = weights
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(","),
        delta = measured_bound - uniform_bound,
        worse = measured_bound > uniform_bound,
        closes = measured_bound < sufficient,
        weight_bound = 4.0 * weight_measured.log2(),
        weight_uniform_bound = 4.0 * weight_uniform.log2(),
        weight_worse = weight_measured > weight_uniform,
    );
    Ok(())
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args().skip(1);
    let first = arguments
        .next()
        .map_or(Ok(4), |value| value.parse::<usize>())
        .map_err(|_| "ell bounds must be integers".to_owned())?;
    let last = arguments
        .next()
        .map_or(Ok(first), |value| value.parse::<usize>())
        .map_err(|_| "ell bounds must be integers".to_owned())?;
    if arguments.next().is_some() || first < 2 || last < first {
        return Err("usage: acb_dic_support [ell_min] [ell_max]".to_owned());
    }
    let limits = HayesLimits {
        max_ell: 24,
        max_degree: 50,
        max_group_order: 1 << 24,
        max_table_cells: 900_000_000,
    };
    for ell in first..=last {
        for degree in [2 * ell + 1, 2 * ell + 2] {
            emit_row(ell, degree, limits)?;
        }
    }
    Ok(())
}
