//! AC-Bridge phase-3 workstream 22 ((CDL) assault): the (CDL) SUPPLY/DEMAND
//! ledger over the whole conductor filtration.
//!
//! Lemma D5 of `13-angle-dichotomy.md` needs a SET `J` of conductor levels with
//! `q_j <= Q` -- not an initial segment.  Writing
//!
//! ```text
//! demand(ell) = ell - log2 G,   G = 2^ell (mu - P_n)^4 / (mu Sigma(ell))^2
//! supply(Q)   = #{ j : q_j <= Q } * (1 - log2(1 + Q))
//! ```
//!
//! the endpoint follows at that parity as soon as `supply(Q) > demand(ell)`,
//! because `R_0 = prod_j (1+q_j) <= 2^(ell - |J|) (1+Q)^|J|` and each level off
//! `J` costs at most one bit (`q_j <= 1`, Lemma D1).  Since a level supplies at
//! most one bit, `#J >= demand(ell)` is a HARD FLOOR independent of `Q`.
//!
//! This example emits, exactly, per row: every `q_j`; the demand; the supply at
//! `Q = 1/ell`, `Q = 1/2` and `Q = 0`; the largest initial segment on which
//! `q_j <= 1/ell` holds; and the `(CDL)` level requirement `ceil(4.1 log2 ell)`
//! it is meant to be compared against.  Only the energies are needed, so every
//! level of the filtration is affordable.
//!
//! It also emits `demand_sharp`, the same demand computed with the MEASURED
//! `M_2` in place of the proved Weil envelope `mu Sigma(ell)`: the difference
//! is exactly the `2 log2 ell` bits the envelope's `ell^2` costs, and it is what
//! sets the constant `4.1` versus `2.1`.

#![allow(clippy::cast_precision_loss)]

use axeyum_cas::gf2_hayes::{
    ClassPopulationDistribution, HayesLimits, PrincipalUnitFactor, class_population_distribution,
    principal_unit_structure,
};
use num_bigint::{BigInt, BigUint};
use num_traits::{ToPrimitive, Zero};

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

fn project(index: usize, full: &[PrincipalUnitFactor], quotient: &[PrincipalUnitFactor]) -> usize {
    let mut remainder = index;
    let mut projected = 0_usize;
    let mut stride = 1_usize;
    let mut cursor = 0_usize;
    for factor in full {
        let coordinate = remainder % factor.order;
        remainder /= factor.order;
        if let Some(target) = quotient.get(cursor)
            && target.odd_degree == factor.odd_degree
        {
            projected += (coordinate % target.order) * stride;
            stride *= target.order;
            cursor += 1;
        }
    }
    projected
}

fn sigma(ell: usize) -> BigUint {
    (2..=ell).fold(BigUint::from(0_u8), |total, j| {
        total + (BigUint::from(j - 1).pow(2) << (j - 1))
    })
}

#[allow(clippy::too_many_lines)]
fn emit_row(ell: usize, degree: usize, limits: HayesLimits) -> Result<(), String> {
    let distribution: ClassPopulationDistribution =
        class_population_distribution(ell, degree, limits).map_err(|error| error.to_string())?;
    let classes = distribution.counts.len();
    let mean = u128::from(1_u8) << (degree - ell);
    let structure = principal_unit_structure(ell, limits).map_err(|error| error.to_string())?;
    let full = structure.factors.clone();
    if factors_of(ell) != full {
        return Err("independent factor list disagrees with the library".to_owned());
    }
    let squared = distribution
        .counts
        .iter()
        .map(|count| {
            (BigInt::from(*count) - BigInt::from(mean))
                .magnitude()
                .pow(2)
        })
        .collect::<Vec<_>>();
    let m2 = squared.iter().sum::<BigUint>();
    let m4 = squared.iter().map(|value| value.pow(2)).sum::<BigUint>();

    let library = distribution
        .fourth_moment_conductor_decomposition(limits.max_table_cells)
        .map_err(|error| error.to_string())?;
    if library.second_moment != m2 || library.fourth_moment != m4 {
        return Err("library disagrees on the moments".to_owned());
    }

    let mut previous = m2.pow(2);
    let mut imbalances = Vec::with_capacity(ell + 1);
    let mut level_rows = Vec::with_capacity(ell + 1);
    for level in 1..=ell {
        let quotient = factors_of(level);
        let cylinders = 1_usize << level;
        let mut masses = vec![BigUint::from(0_u8); cylinders];
        for (index, value) in squared.iter().enumerate() {
            masses[project(index, &full, &quotient)] += value;
        }
        if masses.iter().sum::<BigUint>() != m2 {
            return Err(format!("cylinder masses miss M_2 at level {level}"));
        }
        let energy =
            BigUint::from(cylinders) * masses.iter().map(|mass| mass.pow(2)).sum::<BigUint>();
        if energy < previous || energy > BigUint::from(2_u8) * &previous {
            return Err(format!("Lemma D1 violated at level {level}"));
        }
        let row = &library.levels[level - 1];
        if row.level != level || row.cumulative_fourier_energy != energy {
            return Err(format!(
                "library cumulative energy disagrees at level {level}"
            ));
        }
        let exact = &energy - &previous;
        let imbalance = ratio(&exact, &previous);
        imbalances.push(imbalance);
        level_rows.push(format!(
            "ACB_CDL_WINDOW_LEVEL|ell={ell}|degree={degree}|j={level}|q_j={imbalance:.12e}|\
ell_q_j={scaled:.9}|E_j={exact}",
            scaled = imbalance * (ell as f64),
        ));
        previous = energy;
    }
    if previous != BigUint::from(classes) * &m4 {
        return Err("full conductor energy is not 2^ell M_4".to_owned());
    }

    // Demand: ell - log2 G, with G the proved threshold of (WR).
    let mean_big = BigUint::from(mean);
    let proper = if degree == 2 * ell + 1 {
        BigUint::from(1_u8)
    } else {
        (BigUint::from(ell + 1) << ell.div_ceil(2))
            + (BigUint::from(degree) << (ell + 1).div_ceil(2))
    };
    if mean_big <= proper {
        return Err("proper-power bound exceeds the mean; row below the crossover".to_owned());
    }
    let numerator = (&mean_big - &proper).pow(4) << ell;
    let envelope = &mean_big * sigma(ell);
    if m2 > envelope {
        return Err("proved Weil envelope fails".to_owned());
    }
    let log2_threshold = log2_f64(&numerator) - log2_f64(&envelope.pow(2));
    let demand = (ell as f64) - log2_threshold;
    // The same demand with the measured M_2 in place of the envelope.
    let log2_threshold_sharp = log2_f64(&numerator) - log2_f64(&m2.pow(2));
    let demand_sharp = (ell as f64) - log2_threshold_sharp;

    let inverse = 1.0 / (ell as f64);
    let count_inverse = imbalances.iter().filter(|q| **q <= inverse).count();
    let count_half = imbalances.iter().filter(|q| **q <= 0.5).count();
    let count_zero = imbalances.iter().filter(|q| **q == 0.0).count();
    let supply_inverse = (count_inverse as f64) * (1.0 - (1.0 + inverse).log2());
    let supply_half = (count_half as f64) * (1.0 - 1.5_f64.log2());
    let mut initial = 0_usize;
    for imbalance in &imbalances {
        if *imbalance <= inverse {
            initial += 1;
        } else {
            break;
        }
    }
    let requirement = (4.1 * (ell as f64).log2()).ceil();
    let requirement_half = (9.7 * (ell as f64).log2()).ceil();

    println!(
        "ACB_CDL_WINDOW|status=PASS|ell={ell}|degree={degree}|parity={parity}|\
M_2={m2}|R_0={root:.9}|demand_bits={demand:.6}|demand_bits_sharp={demand_sharp:.6}|\
levels_q_le_inv_ell={count_inverse}|initial_segment_q_le_inv_ell={initial}|\
supply_bits_inv_ell={supply_inverse:.6}|sufficient_inv_ell={ok_inverse}|\
levels_q_le_half={count_half}|supply_bits_half={supply_half:.6}|sufficient_half={ok_half}|\
levels_q_zero={count_zero}|cdl_level_requirement={requirement}|\
cdl_level_requirement_half={requirement_half}|floor_met={floor_met}",
        parity = if degree % 2 == 0 { "even" } else { "odd" },
        root = ratio(&(BigUint::from(classes) * &m4), &m2.pow(2)),
        ok_inverse = supply_inverse > demand,
        ok_half = supply_half > demand,
        floor_met = (count_inverse as f64) >= demand,
    );
    for row in level_rows {
        println!("{row}");
    }
    Ok(())
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args().skip(1);
    let first = arguments
        .next()
        .map_or(Ok(8), |value| value.parse::<usize>())
        .map_err(|_| "ell bounds must be integers".to_owned())?;
    let last = arguments
        .next()
        .map_or(Ok(first), |value| value.parse::<usize>())
        .map_err(|_| "ell bounds must be integers".to_owned())?;
    if arguments.next().is_some() || first < 2 || last < first {
        return Err("usage: acb_cdl_window [ell_min] [ell_max]".to_owned());
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

fn main() {
    if let Err(error) = run() {
        eprintln!("ACB_CDL_WINDOW|status=FAIL|error={error}");
        std::process::exit(1);
    }
}
