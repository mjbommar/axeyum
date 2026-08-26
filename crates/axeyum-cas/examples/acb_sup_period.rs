//! AC-Bridge phase-3 (assignment 21): the exact level-`j` recursion in the
//! DEGREE, and the periodicity (supersingularity) test.
//!
//! On the exact-conductor-level-`j` isotypic component every character has
//! `a_d(chi) = 0` for `d >= j` (diary 11, Lemma 2), so `L(chi, z)` has degree
//! `j-1` and the Mangoldt power sums obey
//!
//! ```text
//!   S_m(chi) = - sum_(d=1)^(j-1) a_d(chi) S_(m-d)(chi),   m >= j.
//! ```
//!
//! In the group ring of `E_j` the same recursion holds for the level-`j`
//! sibling difference `Delta_j(.; m) = N_j(.; m) - N_j(. (1+x^j); m)`, whose
//! Fourier support is exactly the level-`j` family:
//!
//! ```text
//!   Delta(m) = - sum_(d=1)^(j-1) A_d * Delta(m-d),   m >= j,
//!   A_d = sum_(u in V_d) u,  V_d = { 1 + a_1 x + ... + a_d x^d }.
//! ```
//!
//! This is an INDEPENDENT algorithm from `class_population_distribution`
//! (which the `verify` mode checks it against), it is exact in `BigInt`, and
//! it removes the `n <= 59` ceiling of the CRT-bounded population route.
//!
//! Periodicity test.  If every inverse root satisfies `alpha^P = 2^(P/2)`
//! (the level is "supersingular"), then `Delta(m+P) = 2^(P/2) Delta(m)` for
//! all `m`.  Conversely, if that identity holds for `j-1` CONSECUTIVE values
//! `m >= j`, the linear recursion PROPAGATES it to every larger `m`; the
//! finite check is then a proof of periodicity of `kappa_j` on the whole
//! endpoint range `m >= 2j+1`.
//!
//! Usage:
//!   `acb_sup_period verify <j> <nmax>`     recursion vs the CAS populations
//!   `acb_sup_period scan <j> <nmax>`       `kappa_j(n)` to large n
//!   `acb_sup_period period <j> <pmax>`     smallest propagating period
#![allow(
    clippy::cast_precision_loss,
    clippy::cast_possible_wrap,
    clippy::cast_possible_truncation,
    clippy::needless_range_loop,
    clippy::too_many_lines,
    clippy::many_single_char_names
)]
use axeyum_cas::gf2_hayes::{HayesLimits, class_population_distribution};
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

/// Packed mixed-radix model of `E_j` with SWAR group addition.
struct Group {
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

    fn check_add(&self) {
        let stride = if self.order <= 512 { 1 } else { 37 };
        let mut a = 0_usize;
        while a < self.order {
            let mut b = 0_usize;
            while b < self.order {
                let via = self.index(unit_multiply(self.unit_of[a], self.unit_of[b], self.ell));
                assert_eq!(self.add(a, b), via, "SWAR add disagrees at ({a},{b})");
                b += stride;
            }
            a += stride;
        }
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

/// `V_d = { 1 + a_1 x + ... + a_d x^d }` as mixed-radix indices.
fn coefficient_block(group: &Group, d: usize) -> Vec<usize> {
    (0..(1_usize << d))
        .map(|mask| {
            let unit = 1_u64 | ((mask as u64) << 1);
            assert!(unit < (1_u64 << (d + 1)));
            group.index(unit)
        })
        .collect()
}

/// `Delta_j(.; n)` from the CAS population route (`n >= j`).
fn cas_delta(group: &Group, j: usize, n: usize) -> Result<Vec<BigInt>, String> {
    let distribution = class_population_distribution(j, n, limits(j, n))
        .map_err(|error| format!("population declined: {error:?}"))?;
    let generator = group.index(1 | (1_u64 << j));
    Ok((0..group.order)
        .map(|b| {
            BigInt::from(distribution.counts[b])
                - BigInt::from(distribution.counts[group.add(b, generator)])
        })
        .collect())
}

/// One step of `Delta(m) = - sum_(d=1)^(j-1) A_d * Delta(m-d)`.
fn step(group: &Group, blocks: &[Vec<usize>], history: &[Vec<BigInt>]) -> Vec<BigInt> {
    // `history[k]` is `Delta(m-1-k)`.
    let mut out = vec![BigInt::zero(); group.order];
    for (k, previous) in history.iter().enumerate() {
        let d = k + 1;
        for &shift in &blocks[d] {
            for c in 0..group.order {
                if previous[c].is_zero() {
                    continue;
                }
                out[group.add(c, shift)] -= &previous[c];
            }
        }
    }
    out
}

fn kappa_squared(delta: &[BigInt], j: usize, n: usize) -> (BigInt, BigInt) {
    let peak = delta
        .iter()
        .map(num_traits::Signed::abs)
        .max()
        .unwrap_or_else(BigInt::zero);
    let level = BigInt::from(j as i64 - 1);
    (
        (&peak * &peak) << u32::try_from(j - 1).expect("shift"),
        &level * &level * (BigInt::one() << u32::try_from(n).expect("shift")),
    )
}

fn ratio(pair: &(BigInt, BigInt)) -> f64 {
    if pair.1.is_zero() {
        return 0.0;
    }
    let scale = BigInt::one() << 40;
    let quotient: BigInt = (&pair.0 * &scale) / &pair.1;
    let (_, digits) = quotient.to_u64_digits();
    let magnitude = digits.iter().rev().fold(0.0_f64, |acc, digit| {
        acc * 18_446_744_073_709_551_616.0 + *digit as f64
    });
    magnitude / (1_u64 << 40) as f64
}

/// Seeds `Delta(j) .. Delta(2j-2)` from the CAS, then iterates the recursion.
struct Sequence {
    j: usize,
    /// `values[m]` is `Delta(.; m)` for `m >= j` (index `m - j`).
    values: Vec<Vec<BigInt>>,
}

fn build(group: &Group, j: usize, upto: usize, verify_to: usize) -> Result<Sequence, String> {
    assert!(j >= 2);
    let blocks: Vec<Vec<usize>> = (0..j).map(|d| coefficient_block(group, d)).collect();
    let seeds = j - 1; // order of the recursion
    let mut values: Vec<Vec<BigInt>> = Vec::new();
    for m in j..(j + seeds) {
        values.push(cas_delta(group, j, m)?);
    }
    let mut mismatch = 0_usize;
    let mut verified = 0_usize;
    for m in (j + seeds)..=upto {
        let history: Vec<Vec<BigInt>> = (1..=seeds).map(|d| values[m - d - j].clone()).collect();
        let next = step(group, &blocks, &history);
        if m <= verify_to
            && let Ok(reference) = cas_delta(group, j, m)
        {
            if reference == next {
                verified += 1;
            } else {
                mismatch += 1;
                println!("ACB_SUP|control=recursion|j={j}|n={m}|MISMATCH");
            }
        }
        values.push(next);
    }
    println!(
        "ACB_SUP|control=recursion|j={j}|seeds={seeds}|verified_against_cas={verified}|mismatches={mismatch}"
    );
    assert_eq!(mismatch, 0, "the degree recursion disagrees with the CAS");
    assert!(verified > 0, "no CAS cross-check was performed");
    Ok(Sequence { j, values })
}

impl Sequence {
    fn at(&self, m: usize) -> &Vec<BigInt> {
        &self.values[m - self.j]
    }
}

fn main() -> Result<(), String> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() < 3 {
        return Err("usage: acb_sup_period <verify|scan|period> <j> <bound>".to_owned());
    }
    let j: usize = args[1].parse().map_err(|_| "bad j".to_owned())?;
    let bound: usize = args[2].parse().map_err(|_| "bad bound".to_owned())?;
    let group = Group::new(j);
    group.check_add();
    match args[0].as_str() {
        "verify" => {
            let _ = build(&group, j, bound, bound)?;
        }
        "scan" => {
            let sequence = build(&group, j, bound, 59.min(bound))?;
            let mut best = (0.0_f64, 0_usize);
            for m in (2 * j + 1)..=bound {
                let k2 = kappa_squared(sequence.at(m), j, m);
                let value = ratio(&k2).sqrt();
                if value > best.0 {
                    best = (value, m);
                    let peak = sequence
                        .at(m)
                        .iter()
                        .map(num_traits::Signed::abs)
                        .max()
                        .unwrap_or_else(BigInt::zero);
                    println!(
                        "ACB_SUP|probe=record|j={j}|n={m}|kappa={value:.6}|exceeds_K2={}|peak={peak}",
                        k2.0 > (&k2.1 * BigInt::from(4))
                    );
                }
            }
            println!(
                "ACB_SUP|probe=scan_max|j={j}|nmax={bound}|max_kappa={:.6}|at_n={}|triangle_ceiling={:.6}",
                best.0,
                best.1,
                (2.0_f64).powf((j as f64 - 1.0) / 2.0)
            );
        }
        "period" => {
            // Look for P with Delta(m+P) = 2^(P/2) Delta(m) on j-1 consecutive m.
            let need = j - 1;
            let start = 2 * j + 1;
            let sequence = build(
                &group,
                j,
                start + bound + need,
                59.min(start + bound + need),
            )?;
            let mut found = 0_usize;
            for p in (2..=bound).step_by(2) {
                let scale = BigInt::one() << u32::try_from(p / 2).expect("shift");
                let mut ok = true;
                for m in start..(start + need) {
                    let lhs = sequence.at(m + p);
                    let rhs: Vec<BigInt> = sequence.at(m).iter().map(|v| v * &scale).collect();
                    if *lhs != rhs {
                        ok = false;
                        break;
                    }
                }
                if ok {
                    println!(
                        "ACB_SUP|probe=period|j={j}|P={p}|propagating=true|proved_for_all_n_ge={start}"
                    );
                    found = p;
                    break;
                }
            }
            if found == 0 {
                println!("ACB_SUP|probe=period|j={j}|P=none|searched_to={bound}|propagating=false");
            } else {
                // Exact sup over one period, hence over every n >= 2j+1.
                let mut best = (BigInt::zero(), BigInt::one(), 0_usize);
                for m in start..(start + found) {
                    let k2 = kappa_squared(sequence.at(m), j, m);
                    if &k2.0 * &best.1 > &best.0 * &k2.1 {
                        best = (k2.0, k2.1, m);
                    }
                }
                let value = ratio(&(best.0.clone(), best.1.clone())).sqrt();
                println!(
                    "ACB_SUP|probe=period_sup|j={j}|P={found}|sup_kappa={value:.9}|attained_at_n={}|kappa2_num={}|kappa2_den={}",
                    best.2, best.0, best.1
                );
            }
        }
        other => return Err(format!("unknown mode {other}")),
    }
    Ok(())
}
