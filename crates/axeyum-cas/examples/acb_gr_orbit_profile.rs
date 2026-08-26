// Research example (AC-Bridge workstream D).  The casts below are all inside
// explicitly bounded ranges (`degree < 30`, `input_count = 2^(degree-1)`), and
// the classification struct is deliberately a flat record of independent
// boolean predicates, so the pedantic cast/bool lints are allowed here.
#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::struct_excessive_bools,
    clippy::too_many_lines,
    clippy::needless_range_loop
)]

//! AC-Bridge workstream D (rank/Arf split), task 3: the twist-orbit structure
//! of the inverse-coset fibre family, and the exact completion identity that
//! replaces a Burgess-style amplification.
//!
//! The lane's proved parallelogram identity says
//! `delta_h(f) = delta_h(f+t) <=> h t (t+h) = 0` in `GF(2)[x]/x^(ell+1)`, and
//! `t -> h t (t+h) = h(t^2 + h t)` is `F_2`-linear.  So for a fixed shift `h`
//! the inverse difference `delta_h` is constant exactly on the cosets of the
//! group
//!
//! ```text
//! T_h = { t : deg t <= d, t^2 + h t = 0 mod x^(ell+1-v(h)) }
//! ```
//!
//! and every exact affine fibre is a **complete** `T_h`-orbit.  The family is
//! incomplete only in *which* orbits are selected, and the selection
//! `deg delta_h <= d` is an `F_2`-subspace condition of index `2^(ell-d)`.
//! With the lane's pinned `d = ell - 1` the index is two, so the indicator
//! expands into exactly two additive characters and the completion is an
//! identity with no error term:
//!
//! ```text
//! 2 Delta = A + B,
//! A = sum_h sum_m mu(f_m) mu(f_(m+h))                     (complete orbits)
//! B = sum_h sum_m (-1)^(coefficient of x^ell in delta_h) mu(f_m) mu(f_(m+h)).
//! ```
//!
//! This example verifies that identity, measures the orbit-completeness
//! profile, and prints the boundary mass a Burgess-style argument would pay.
//!
//! Usage: `acb_gr_orbit_profile <ell_min> [ell_max]`.

use axeyum_cas::gf2_hayes::{HayesLimits, binary_dyadic_autocorrelation_fibre_report};

fn main() {
    if let Err(error) = run() {
        eprintln!("ACB_GR_ORBIT|status=FAIL|error={error}");
        std::process::exit(1);
    }
}

fn poly_degree(value: u64) -> usize {
    (u64::BITS - 1 - value.leading_zeros()) as usize
}

fn poly_div(mut left: u64, right: u64) -> u64 {
    let right_degree = poly_degree(right);
    let mut quotient = 0_u64;
    while left != 0 && poly_degree(left) >= right_degree {
        let shift = poly_degree(left) - right_degree;
        quotient |= 1_u64 << shift;
        left ^= right << shift;
    }
    quotient
}

fn gf2_mul(left: u64, right: u64) -> u64 {
    let mut product = 0_u64;
    let mut shift = 0_u32;
    let mut remaining = right;
    while remaining != 0 {
        if remaining & 1 != 0 {
            product ^= left << shift;
        }
        remaining >>= 1;
        shift += 1;
    }
    product
}

fn smallest_factor_sieve(degree: usize) -> Vec<u32> {
    let bound = 1_usize << (degree + 1);
    let mut smallest = vec![0_u32; bound];
    for candidate in 2..bound {
        if smallest[candidate] != 0 {
            continue;
        }
        let candidate_u64 = candidate as u64;
        let candidate_degree = poly_degree(candidate_u64);
        let mut multiplier = 1_u64;
        while ((multiplier as usize) << candidate_degree) < bound {
            let product = gf2_mul(candidate_u64, multiplier) as usize;
            if product < bound && smallest[product] == 0 {
                smallest[product] = candidate as u32;
            }
            multiplier += 1;
        }
    }
    smallest
}

fn moebius(mut value: u64, smallest: &[u32]) -> i8 {
    let mut sign = 1_i8;
    let mut previous = 0_u64;
    while value != 1 {
        let factor = u64::from(smallest[value as usize]);
        if factor == previous {
            return 0;
        }
        previous = factor;
        value = poly_div(value, factor);
        sign = -sign;
    }
    sign
}

fn principal_unit_inverse(unit: u64, ell: usize) -> u64 {
    let mut inverse = 1_u64;
    for degree in 1..=ell {
        let mut coefficient = 0_u64;
        for left in 1..=degree {
            coefficient ^= ((unit >> left) & 1) & ((inverse >> (degree - left)) & 1);
        }
        inverse |= coefficient << degree;
    }
    inverse
}

/// Truncated Artin--Schreier kernel dimension proved in the lane ledger:
/// `dim ker(z -> z^2 + h z)` in `GF(2)[x]/x^r` is `v+1` when `2v < r` and
/// `floor(r/2)` otherwise, with `v` the valuation of `h`.
fn artin_schreier_kernel_dimension(valuation: usize, modulus_degree: usize) -> usize {
    if 2 * valuation < modulus_degree {
        valuation + 1
    } else {
        modulus_degree / 2
    }
}

/// Closed-form orbit dimension.
///
/// The parallelogram identity gives `T_h = { tau : v(tau) + v(tau+h) >= c }`
/// with `c = ell + 1 - v`, i.e. `tau^2 + h tau = 0` in `GF(2)[x]/x^c`.  The
/// direction space is `span{x, ..., x^d}`, every element of the kernel already
/// has positive valuation, and the directions of valuation at least `c` are
/// automatically in the kernel, so
///
/// ```text
/// dim T_h = dim ker(z -> z^2 + hz mod x^c) + max(0, d - c + 1).
/// ```
fn closed_form_orbit_dimension(valuation: usize, ell: usize, interval: usize) -> usize {
    let truncation = ell + 1 - valuation;
    artin_schreier_kernel_dimension(valuation, truncation)
        + (interval + 1).saturating_sub(truncation)
}

struct ShiftRow {
    shift: usize,
    valuation: usize,
    orbit_dimension: usize,
    predicted_dimension: usize,
    orbit_count: usize,
    admissible_orbits: usize,
    complete_sum: i64,
    twisted_sum: i64,
    restricted_sum: i64,
    boundary_absolute: u64,
    admissible_points: u64,
    admissible_squarefree_pairs: u64,
    square_divides_shift: bool,
}

#[allow(clippy::too_many_lines)]
fn profile(ell: usize, degree: usize, interval: usize) -> Result<Vec<ShiftRow>, String> {
    let smallest = smallest_factor_sieve(degree);
    let input_count = 1_usize << (degree - 1);
    let shift_count = 1_usize << interval;
    let residue_mask = (1_u64 << (ell + 1)) - 1;
    let mut moebius_values = vec![0_i8; input_count];
    let mut inverses = vec![0_u64; input_count];
    for middle in 0..input_count {
        let polynomial = (1_u64 << degree) | ((middle as u64) << 1) | 1;
        moebius_values[middle] = moebius(polynomial, &smallest);
        inverses[middle] = principal_unit_inverse(polynomial & residue_mask, ell);
    }
    let mut rows = Vec::with_capacity(shift_count - 1);
    let mut orbit_sums = std::collections::BTreeMap::<u64, i64>::new();
    for shift in 1..shift_count {
        // Shift polynomial and its valuation.
        let shift_polynomial = (shift as u64) << 1;
        let valuation = shift_polynomial.trailing_zeros() as usize;
        // The orbit group: directions that fix the inverse difference.  By the
        // proved parallelogram identity this stabiliser is independent of the
        // base point, so one base point determines it.
        let base_difference = inverses[0] ^ inverses[shift];
        let mut stabiliser = Vec::new();
        for translation in 0..(1_usize << interval) {
            if inverses[translation] ^ inverses[translation ^ shift] == base_difference {
                stabiliser.push(translation);
            }
        }
        let orbit_dimension = stabiliser.len().trailing_zeros() as usize;
        if !stabiliser.len().is_power_of_two() {
            return Err("orbit stabiliser is not a power of two".to_owned());
        }
        // Independence of the base point, checked on three probes.
        for &translation in &stabiliser {
            for probe in [0_usize, 1, input_count / 3] {
                let base = probe % input_count;
                let moved = base ^ translation;
                if inverses[base] ^ inverses[base ^ shift]
                    != inverses[moved] ^ inverses[moved ^ shift]
                {
                    return Err("inverse difference is not constant on the orbit".to_owned());
                }
            }
        }
        let predicted = closed_form_orbit_dimension(valuation, ell, interval);
        // Accumulate the complete, twisted and restricted sums.
        orbit_sums.clear();
        let mut complete_sum = 0_i64;
        let mut twisted_sum = 0_i64;
        let mut restricted_sum = 0_i64;
        let mut admissible_points = 0_u64;
        let mut admissible_squarefree_pairs = 0_u64;
        // Is the shift polynomial divisible by `(x+1)^2 = x^2 + 1`?  Over `F_2`
        // this is `h(1) = 0` and `h'(1) = 0`.
        let odd_mask: u64 = (0..=degree)
            .filter(|index| !index.is_multiple_of(2))
            .fold(0_u64, |mask, index| mask | (1_u64 << index));
        let square_divides_shift = shift_polynomial.count_ones().is_multiple_of(2)
            && (shift_polynomial & odd_mask).count_ones().is_multiple_of(2);
        for middle in 0..input_count {
            let value =
                i64::from(moebius_values[middle]) * i64::from(moebius_values[middle ^ shift]);
            let difference = inverses[middle] ^ inverses[middle ^ shift];
            let admissible = difference >> (interval + 1) == 0;
            complete_sum += value;
            if admissible {
                twisted_sum += value;
                restricted_sum += value;
                admissible_points += 1;
                if value != 0 {
                    admissible_squarefree_pairs += 1;
                }
            } else {
                twisted_sum -= value;
            }
            let key = (difference << (degree as u64)) | ((middle >> interval) as u64);
            *orbit_sums.entry(key).or_default() += value;
        }
        let orbit_count = orbit_sums.len();
        let mut admissible_orbits = 0_usize;
        let mut boundary_absolute = 0_u64;
        for (&key, &sum) in &orbit_sums {
            let difference = key >> (degree as u64);
            if difference >> (interval + 1) == 0 {
                admissible_orbits += 1;
            } else {
                boundary_absolute += sum.unsigned_abs();
            }
        }
        rows.push(ShiftRow {
            shift,
            valuation,
            orbit_dimension,
            predicted_dimension: predicted,
            orbit_count,
            admissible_orbits,
            complete_sum,
            twisted_sum,
            restricted_sum,
            boundary_absolute,
            admissible_points,
            admissible_squarefree_pairs,
            square_divides_shift,
        });
    }
    Ok(rows)
}

fn run() -> Result<(), String> {
    let arguments = std::env::args().skip(1).collect::<Vec<_>>();
    let verbose = arguments.iter().any(|value| value == "--verbose");
    let numeric = arguments
        .iter()
        .filter(|value| !value.starts_with("--"))
        .map(|value| {
            value
                .parse::<usize>()
                .map_err(|_| "ell bounds must be integers".to_owned())
        })
        .collect::<Result<Vec<_>, String>>()?;
    let first = numeric.first().copied().unwrap_or(4);
    let last = numeric.get(1).copied().unwrap_or(first);
    let limits = HayesLimits {
        max_ell: 24,
        max_degree: 50,
        max_group_order: 1 << 24,
        max_table_cells: 1_600_000_000,
    };
    for ell in first..=last {
        for degree in [ell + 2, ell + 3] {
            let interval = ell - 1;
            let rows = profile(ell, degree, interval)?;
            let report = binary_dyadic_autocorrelation_fibre_report(ell, degree, interval, limits)
                .map_err(|error| error.to_string())?;
            let complete = rows
                .iter()
                .map(|row| i128::from(row.complete_sum))
                .sum::<i128>();
            let twisted = rows
                .iter()
                .map(|row| i128::from(row.twisted_sum))
                .sum::<i128>();
            let restricted = rows
                .iter()
                .map(|row| i128::from(row.restricted_sum))
                .sum::<i128>();
            let boundary = rows
                .iter()
                .map(|row| u128::from(row.boundary_absolute))
                .sum::<u128>();
            let mut clean_points = 0_u128;
            let mut clean_pairs = 0_u128;
            let mut dirty_points = 0_u128;
            let mut dirty_pairs = 0_u128;
            for row in &rows {
                if row.square_divides_shift {
                    dirty_points += u128::from(row.admissible_points);
                    dirty_pairs += u128::from(row.admissible_squarefree_pairs);
                } else {
                    clean_points += u128::from(row.admissible_points);
                    clean_pairs += u128::from(row.admissible_squarefree_pairs);
                }
            }
            #[allow(clippy::cast_precision_loss)]
            let clean_density = clean_pairs as f64 / clean_points as f64;
            #[allow(clippy::cast_precision_loss)]
            let dirty_density = dirty_pairs as f64 / dirty_points as f64;
            let complete_absolute = rows
                .iter()
                .map(|row| u128::from(row.complete_sum.unsigned_abs()))
                .sum::<u128>();
            let twisted_absolute = rows
                .iter()
                .map(|row| u128::from(row.twisted_sum.unsigned_abs()))
                .sum::<u128>();
            let restricted_absolute = rows
                .iter()
                .map(|row| u128::from(row.restricted_sum.unsigned_abs()))
                .sum::<u128>();
            let orbit_total = rows.iter().map(|row| row.orbit_count).sum::<usize>();
            let admissible_total = rows.iter().map(|row| row.admissible_orbits).sum::<usize>();
            if restricted != report.off_diagonal_signed_correlation {
                return Err(format!(
                    "restricted orbit sum {restricted} misses the report Delta {}",
                    report.off_diagonal_signed_correlation
                ));
            }
            if admissible_total != report.fibre_count {
                return Err(format!(
                    "admissible orbit count {admissible_total} misses the report fibre count {}",
                    report.fibre_count
                ));
            }
            if 2 * restricted != complete + twisted {
                return Err(format!(
                    "completion identity failed: 2*{restricted} != {complete} + {twisted}"
                ));
            }
            let mismatched_dimensions = rows
                .iter()
                .filter(|row| row.orbit_dimension != row.predicted_dimension)
                .count();
            if mismatched_dimensions != 0 {
                let sample = rows
                    .iter()
                    .find(|row| row.orbit_dimension != row.predicted_dimension)
                    .map_or_else(String::new, |row| {
                        format!(
                            "shift={} v={} measured={} predicted={}",
                            row.shift, row.valuation, row.orbit_dimension, row.predicted_dimension
                        )
                    });
                return Err(format!(
                    "closed-form orbit dimension fails on {mismatched_dimensions} shifts ({sample})"
                ));
            }
            let dimension_histogram = {
                let mut counts = std::collections::BTreeMap::<usize, usize>::new();
                for row in &rows {
                    *counts.entry(row.orbit_dimension).or_default() += 1;
                }
                counts
                    .into_iter()
                    .map(|(dimension, count)| format!("{dimension}:{count}"))
                    .collect::<Vec<_>>()
                    .join(",")
            };
            #[allow(clippy::cast_precision_loss)]
            let completeness = admissible_total as f64 / orbit_total as f64;
            println!(
                "ACB_GR_ORBIT|status=PASS|ell={ell}|k={degree}|d={interval}|\
shifts={shifts}|orbits={orbit_total}|admissible_orbits={admissible_total}|\
orbit_completeness={completeness:.6}|\
complete_sum_A={complete}|twisted_sum_B={twisted}|delta={restricted}|\
boundary_absolute={boundary}|\
shiftwise_absolute_A={complete_absolute}|shiftwise_absolute_B={twisted_absolute}|\
shiftwise_absolute_R={restricted_absolute}|\
clean_points={clean_points}|clean_pairs={clean_pairs}|\
dirty_points={dirty_points}|dirty_pairs={dirty_pairs}|\
clean_density={clean_density:.6}|dirty_density={dirty_density:.6}|\
dimension_mismatch_vs_artin_schreier={mismatched_dimensions}|\
orbit_dimensions={dimension_histogram}",
                shifts = rows.len(),
                clean_density = clean_density,
                dirty_density = dirty_density,
            );
            if verbose {
                for row in &rows {
                    println!(
                        "ACB_GR_ORBIT|shift|ell={ell}|k={degree}|s={s}|v={v}|dim={dim}|\
predicted={pred}|orbits={orbits}|admissible={adm}|A_s={a}|B_s={b}|R_s={r}|boundary={bd}",
                        s = row.shift,
                        v = row.valuation,
                        dim = row.orbit_dimension,
                        pred = row.predicted_dimension,
                        orbits = row.orbit_count,
                        adm = row.admissible_orbits,
                        a = row.complete_sum,
                        b = row.twisted_sum,
                        r = row.restricted_sum,
                        bd = row.boundary_absolute,
                    );
                }
            }
        }
    }
    Ok(())
}
