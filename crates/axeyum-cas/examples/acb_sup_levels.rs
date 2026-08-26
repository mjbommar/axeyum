//! AC-Bridge workstream phase-3 (assignment 21): the sup-norm of one
//! conductor layer, `(SUP-L)`.
//!
//! `(SUP-L)` (diary 11, Result 6) asks for an absolute `K` with
//!
//! ```text
//!   max_e |D_[j](e)|  <=  K (j-1) 2^((j-1)/2) 2^(n/2) / 2^ell
//! ```
//!
//! for every conductor level `j <= ell` and both endpoint degrees.
//!
//! This example rests on the identity (proved in the diary, controlled by the
//! `identity` mode here) that the level-`j` layer is the LEVEL-`j` SIBLING
//! DIFFERENCE and carries no `ell` at all:
//!
//! ```text
//!   D_[j](e) = Delta_j(pi_j e) / 2^(ell-j+1),
//!   Delta_j(b) = N_j(b) - N_j(b (1+x^j)),
//! ```
//!
//! with `N_j(b)` the von-Mangoldt-weighted count of monic degree-`n`
//! polynomials whose reciprocal class truncates to `b` mod `x^(j+1)`.  Hence
//!
//! ```text
//!   kappa_j(n) := max_e |D_[j](e)| 2^ell / ((j-1) 2^((j-1)/2) 2^(n/2))
//!               = max_b |Delta_j(b)| 2^((j-1)/2) / ((j-1) 2^(n/2))
//! ```
//! depends only on `(j, n)`.  Everything retained is an exact integer; the
//! printed `kappa` is the decimal image of the exact rational `kappa^2`.
//!
//! Usage:
//!   `acb_sup_levels identity <ell> <n>`         control: ell-freeness
//!   `acb_sup_levels grid <jlo> <jhi> <nlo> <nhi>`
//!   `acb_sup_levels endpoints <elllo> <ellhi>`  the (SUP-L) pairs
//!   `acb_sup_levels layer <j> <n>`              one layer, full vector stats
#![allow(
    clippy::cast_precision_loss,
    clippy::cast_possible_wrap,
    clippy::cast_possible_truncation,
    clippy::needless_range_loop,
    clippy::too_many_lines,
    clippy::many_single_char_names
)]
use axeyum_cas::gf2_hayes::{
    HayesLimits, class_population_distribution, exact_conductor_second_moment,
};
use num_bigint::BigInt;
use num_traits::{One, Zero};

#[derive(Debug, Clone, Copy)]
struct Factor {
    odd_degree: usize,
    order: usize,
}

fn factors(ell: usize) -> Vec<Factor> {
    (1..=ell)
        .step_by(2)
        .map(|odd_degree| {
            let mut order = 1_usize;
            while odd_degree <= ell / order {
                order *= 2;
            }
            Factor { odd_degree, order }
        })
        .collect()
}

fn unit_multiply(mut left: u64, right: u64, ell: usize) -> u64 {
    let mut product = 0_u64;
    while left != 0 {
        let degree = left.trailing_zeros() as usize;
        left &= left - 1;
        product ^= right << degree;
    }
    product & ((1_u64 << (ell + 1)) - 1)
}

fn unit_from_index(mut index: usize, fs: &[Factor], ell: usize) -> u64 {
    let mut unit = 1_u64;
    for factor in fs {
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
    assert_eq!(index, 0, "mixed-radix index out of range");
    unit
}

/// Packed mixed-radix model of `E_ell` with SWAR group addition.
pub struct Group {
    ell: usize,
    order: usize,
    high: u64,
    low: u64,
    unit_of: Vec<u64>,
    index_of: Vec<u32>,
}

impl Group {
    fn new(ell: usize) -> Self {
        let fs = factors(ell);
        let order = 1_usize << ell;
        let mut high = 0_u64;
        let mut offset = 0_u32;
        for factor in &fs {
            offset += factor.order.trailing_zeros();
            high |= 1_u64 << (offset - 1);
        }
        assert_eq!(offset as usize, ell, "coordinate widths must sum to ell");
        let full = (1_u64 << ell) - 1;
        let mut unit_of = vec![0_u64; order];
        let mut index_of = vec![u32::MAX; order];
        for index in 0..order {
            let unit = unit_from_index(index, &fs, ell);
            unit_of[index] = unit;
            let slot = (unit >> 1) as usize;
            assert_eq!(index_of[slot], u32::MAX, "Witt coordinates not injective");
            index_of[slot] = u32::try_from(index).expect("index fits u32");
        }
        Self {
            ell,
            order,
            high,
            low: full & !high,
            unit_of,
            index_of,
        }
    }

    #[inline]
    fn add(&self, x: usize, y: usize) -> usize {
        let (x, y) = (x as u64, y as u64);
        let sum = (x & self.low) + (y & self.low);
        ((sum ^ ((x ^ y) & self.high)) & ((1_u64 << self.ell) - 1)) as usize
    }

    fn index(&self, unit: u64) -> usize {
        self.index_of[(unit >> 1) as usize] as usize
    }

    /// Truncation `pi_j : E_ell -> E_j`, as a map of mixed-radix indices.
    fn truncate_to(&self, coarse: &Group, index: usize) -> usize {
        let mask = (1_u64 << (coarse.ell + 1)) - 1;
        coarse.index(self.unit_of[index] & mask)
    }

    fn check_add(&self) {
        let stride = if self.order <= 512 { 1 } else { 37 };
        let mut checked = 0_usize;
        let mut a = 0_usize;
        while a < self.order {
            let mut b = 0_usize;
            while b < self.order {
                let via = self.index(unit_multiply(self.unit_of[a], self.unit_of[b], self.ell));
                assert_eq!(self.add(a, b), via, "SWAR add disagrees at ({a},{b})");
                checked += 1;
                b += stride;
            }
            a += stride;
        }
        assert!(checked > 0);
    }
}

fn limits(ell: usize, degree: usize) -> HayesLimits {
    HayesLimits {
        max_ell: ell.max(24),
        max_degree: degree.max(128),
        max_group_order: 1 << 24,
        max_table_cells: 1 << 62,
    }
}

/// Exact class populations `N_j(b)` at level `j` and degree `n`.
fn populations(group: &Group, j: usize, n: usize) -> Result<Vec<i128>, String> {
    assert_eq!(group.ell, j);
    let distribution = class_population_distribution(j, n, limits(j, n))
        .map_err(|error| format!("population declined: {error:?}"))?;
    let counts: Vec<i128> = distribution
        .counts
        .iter()
        .map(|value| i128::try_from(*value).expect("count fits i128"))
        .collect();
    let total: i128 = counts.iter().sum();
    let expected = 1_i128 << u32::try_from(n).expect("degree shift");
    if total != expected {
        return Err(format!(
            "sum_b N_j(b) = {total}, expected 2^{n} = {expected}"
        ));
    }
    Ok(counts)
}

/// `Delta_j(b) = N_j(b) - N_j(b (1+x^j))`, the level-`j` sibling difference.
fn sibling_difference(group: &Group, counts: &[i128]) -> Vec<i128> {
    let j = group.ell;
    let generator = group.index(1 | (1_u64 << j));
    assert_ne!(generator, 0, "1+x^j must be a nonidentity class");
    (0..group.order)
        .map(|b| counts[b] - counts[group.add(b, generator)])
        .collect()
}

struct LayerStats {
    peak: i128,
    sum_squares: BigInt,
    /// `kappa_j^2` as an exact rational `num/den`.
    kappa2: (BigInt, BigInt),
    /// flatness `F_j^2 = max^2 2^j / sum_b Delta^2`, exact rational.
    flat2: (BigInt, BigInt),
    /// Weil fill `V_j / envelope = sum_b Delta^2 / (2 (j-1)^2 2^n)`, exact.
    fill: (BigInt, BigInt),
}

fn stats(delta: &[i128], j: usize, n: usize) -> LayerStats {
    let peak = delta.iter().map(num_traits::Signed::abs).max().unwrap_or(0);
    let mut sum_squares = BigInt::zero();
    for value in delta {
        sum_squares += BigInt::from(*value) * BigInt::from(*value);
    }
    let peak_squared = BigInt::from(peak) * BigInt::from(peak);
    let two_n = BigInt::one() << u32::try_from(n).expect("degree shift");
    let level = BigInt::from(j as i64 - 1);
    let kappa2 = if j >= 2 {
        (
            &peak_squared << u32::try_from(j - 1).expect("shift"),
            &level * &level * &two_n,
        )
    } else {
        (BigInt::zero(), BigInt::one())
    };
    let flat2 = if sum_squares.is_zero() {
        (BigInt::zero(), BigInt::one())
    } else {
        (
            &peak_squared << u32::try_from(j).expect("shift"),
            sum_squares.clone(),
        )
    };
    let fill = if j >= 2 {
        (
            sum_squares.clone(),
            BigInt::from(2) * &level * &level * &two_n,
        )
    } else {
        (BigInt::zero(), BigInt::one())
    };
    LayerStats {
        peak,
        sum_squares,
        kappa2,
        flat2,
        fill,
    }
}

fn ratio(pair: &(BigInt, BigInt)) -> f64 {
    if pair.1.is_zero() {
        return 0.0;
    }
    let scale = BigInt::one() << 40;
    let quotient: BigInt = (&pair.0 * &scale) / &pair.1;
    let (sign, digits) = quotient.to_u64_digits();
    let magnitude = digits.iter().rev().fold(0.0_f64, |acc, digit| {
        acc * 18_446_744_073_709_551_616.0 + *digit as f64
    });
    let value = magnitude / (1_u64 << 40) as f64;
    if sign == num_bigint::Sign::Minus {
        -value
    } else {
        value
    }
}

/// Exact test `kappa_j^2 <= (num/den)^2`, i.e. `(SUP-L)` at constant `num/den`.
fn kappa_at_most(kappa2: &(BigInt, BigInt), num: i64, den: i64) -> bool {
    &kappa2.0 * BigInt::from(den) * BigInt::from(den)
        <= &kappa2.1 * BigInt::from(num) * BigInt::from(num)
}

fn layer_line(j: usize, n: usize, delta: &[i128]) -> LayerStats {
    let s = stats(delta, j, n);
    println!(
        "ACB_SUP|probe=layer|j={j}|n={n}|peak={}|kappa={:.6}|flat={:.6}|fill={:.6}|le_2={}|le_3_2={}|le_sqrt2={}",
        s.peak,
        ratio(&s.kappa2).sqrt(),
        ratio(&s.flat2).sqrt(),
        ratio(&s.fill),
        kappa_at_most(&s.kappa2, 2, 1),
        kappa_at_most(&s.kappa2, 3, 2),
        kappa_at_most(&s.kappa2, 1_414_213_562, 1_000_000_000),
    );
    s
}

fn main() -> Result<(), String> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        return Err("usage: acb_sup_levels <identity|grid|endpoints|layer> ...".to_owned());
    }
    match args[0].as_str() {
        // Control: the full-ell conductor layer equals the level-j sibling
        // difference, rescaled.  This is the ell-freeness of (SUP-L).
        "identity" => {
            let ell: usize = args[1].parse().map_err(|_| "bad ell".to_owned())?;
            let n: usize = args[2].parse().map_err(|_| "bad n".to_owned())?;
            let fine = Group::new(ell);
            fine.check_add();
            let fine_counts = populations(&fine, ell, n)?;
            let mean = (1_i128 << u32::try_from(n - ell).expect("shift")) as i128;
            let discrepancy: Vec<i128> = fine_counts.iter().map(|c| c - mean).collect();
            // Sibling recursion at level ell, exactly as diary 11.
            let mut r = discrepancy.clone();
            let mut a = vec![Vec::new(); ell + 1];
            for level in (1..=ell).rev() {
                let generator = fine.index(1 | (1_u64 << level));
                let shifted: Vec<i128> =
                    (0..fine.order).map(|e| r[fine.add(e, generator)]).collect();
                a[level] = (0..fine.order).map(|e| r[e] - shifted[e]).collect();
                for e in 0..fine.order {
                    r[e] += shifted[e];
                }
            }
            assert!(r.iter().all(|v| *v == 0), "R_0 must vanish");
            for j in 1..=ell {
                let coarse = Group::new(j);
                let coarse_counts = populations(&coarse, j, n)?;
                let delta = sibling_difference(&coarse, &coarse_counts);
                // A_j(e) = 2^(ell-j) * Delta_j(pi_j e):
                //   D_[j] = A_j / 2^(ell-j+1) = Delta_j / 2^(ell-j+1) * 2^(ell-j)
                // is the claim; check the integer form A_j(e) = Delta_j(pi_j e).
                let mut agree = true;
                for e in 0..fine.order {
                    let b = fine.truncate_to(&coarse, e);
                    if a[j][e] != delta[b] {
                        agree = false;
                        println!(
                            "ACB_SUP|control=ell_free|ell={ell}|n={n}|j={j}|MISMATCH|e={e}|fine={}|coarse={}",
                            a[j][e], delta[b]
                        );
                        break;
                    }
                }
                let peak_fine = a[j].iter().map(num_traits::Signed::abs).max().unwrap_or(0);
                let peak_coarse = delta.iter().map(num_traits::Signed::abs).max().unwrap_or(0);
                println!(
                    "ACB_SUP|control=ell_free|ell={ell}|n={n}|j={j}|agree={agree}|peak_fine={peak_fine}|peak_coarse={peak_coarse}"
                );
                assert!(agree, "ell-freeness identity failed at j={j}");
                // Independent control on the layer energy against the CAS.
                let s = stats(&delta, j, n);
                let family = (&s.sum_squares) << u32::try_from(j.saturating_sub(2)).expect("shift");
                match exact_conductor_second_moment(j, n, limits(ell, n)) {
                    Ok(report) => {
                        let theirs = BigInt::from(report.value);
                        let ok = if j >= 2 {
                            family == theirs
                        } else {
                            theirs.is_zero()
                        };
                        println!(
                            "ACB_SUP|control=conductor_second_moment|j={j}|n={n}|mine={family}|cas={theirs}|agree={ok}"
                        );
                        assert!(ok, "level energy disagrees with the CAS at j={j}");
                    }
                    Err(error) => println!(
                        "ACB_SUP|control=conductor_second_moment|j={j}|n={n}|declined={error:?}"
                    ),
                }
            }
        }
        "layer" => {
            let j: usize = args[1].parse().map_err(|_| "bad j".to_owned())?;
            let n: usize = args[2].parse().map_err(|_| "bad n".to_owned())?;
            let group = Group::new(j);
            group.check_add();
            let counts = populations(&group, j, n)?;
            let delta = sibling_difference(&group, &counts);
            let s = layer_line(j, n, &delta);
            let _ = s;
            for b in 0..group.order {
                println!(
                    "ACB_SUP|probe=class|j={j}|n={n}|b={b}|unit={:#x}|delta={}",
                    group.unit_of[b], delta[b]
                );
            }
        }
        "grid" => {
            let jlo: usize = args[1].parse().map_err(|_| "bad jlo".to_owned())?;
            let jhi: usize = args[2].parse().map_err(|_| "bad jhi".to_owned())?;
            let nlo: usize = args[3].parse().map_err(|_| "bad nlo".to_owned())?;
            let nhi: usize = args[4].parse().map_err(|_| "bad nhi".to_owned())?;
            for j in jlo..=jhi {
                let group = Group::new(j);
                if j <= 10 {
                    group.check_add();
                }
                for n in nlo.max(j)..=nhi {
                    match populations(&group, j, n) {
                        Ok(counts) => {
                            let delta = sibling_difference(&group, &counts);
                            layer_line(j, n, &delta);
                        }
                        Err(error) => println!("ACB_SUP|probe=layer|j={j}|n={n}|declined={error}"),
                    }
                }
            }
        }
        "endpoints" => {
            let lo: usize = args[1].parse().map_err(|_| "bad ell lo".to_owned())?;
            let hi: usize = args[2].parse().map_err(|_| "bad ell hi".to_owned())?;
            // Cache by level: the layer depends only on (j, n).
            for ell in lo..=hi {
                for n in [2 * ell + 1, 2 * ell + 2] {
                    let mut worst = (0.0_f64, 0_usize);
                    let mut worst4 = (0.0_f64, 0_usize);
                    for j in 2..=ell {
                        let group = Group::new(j);
                        let counts = match populations(&group, j, n) {
                            Ok(counts) => counts,
                            Err(error) => {
                                println!(
                                    "ACB_SUP|probe=endpoint|ell={ell}|n={n}|j={j}|declined={error}"
                                );
                                continue;
                            }
                        };
                        let delta = sibling_difference(&group, &counts);
                        let s = stats(&delta, j, n);
                        let value = ratio(&s.kappa2).sqrt();
                        if value > worst.0 {
                            worst = (value, j);
                        }
                        if j >= 4 && value > worst4.0 {
                            worst4 = (value, j);
                        }
                        println!(
                            "ACB_SUP|probe=endpoint|ell={ell}|n={n}|j={j}|peak={}|kappa={value:.6}|flat={:.6}|fill={:.6}|le_2={}",
                            s.peak,
                            ratio(&s.flat2).sqrt(),
                            ratio(&s.fill),
                            kappa_at_most(&s.kappa2, 2, 1)
                        );
                    }
                    println!(
                        "ACB_SUP|probe=endpoint_max|ell={ell}|n={n}|max_kappa={:.6}|at_j={}|max_kappa_j_ge_4={:.6}|at_j={}",
                        worst.0, worst.1, worst4.0, worst4.1
                    );
                }
            }
        }
        other => return Err(format!("unknown mode {other}")),
    }
    Ok(())
}
