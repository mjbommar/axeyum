//! AC-Bridge workstream A: the CONDUCTOR-graded connected cumulant cells.
//!
//! The resurrected candidate `(CAB)` grades the fourth cumulant by
//! CONVOLUTION ORDER (`T_d`, `d=1..ell-1`).  This example builds the
//! alternative grading by exact CONDUCTOR LEVEL,
//!
//! ```text
//! D = sum_(j=1)^ell D_[j],   D_[j] = P_j D - P_(j-1) D,
//! P_j D(e) = 2^-(ell-j) sum_(h in H_j) D(e h),  H_j = 1 + x^(j+1) F_2[x],
//! ```
//! computed by the integer sibling recursion
//! `R_ell = D`, `R_(j-1)(e) = R_j(e) + R_j(e g_j)`, `g_j = 1 + x^j`,
//! `A_j(e) = R_j(e) - R_j(e g_j)`, `D_[j] = A_j / 2^(ell-j+1)`.
//!
//! Two structural facts make this grading different from the order grading:
//! the level components are pairwise ORTHOGONAL, so the covariance matrix is
//! diagonal and every Wick pairing is nonnegative; and each level energy
//! `V_j = ||D_[j]||^2` is bounded by the lane's PROVED Weil envelope
//! `V_j <= 2^(n-ell) 2^(j-1) (j-1)^2`.
//!
//! Read-only diagnostic.  Exact integers throughout (cells are integers after
//! the common scaling by `2^(4 ell)`); the only floating point is in printed
//! ratios.  Finite computation is evidence, never a theorem.
//!
//! Usage:
//!   `acb_cab_levels sweep <lo> <hi>`    -- (CAB-L) closure, both parities
//!   `acb_cab_levels row <ell> <n>`      -- one row with the level profile
//!   `acb_cab_levels top <ell> <n> <k>`  -- heaviest level cells

// Lint policy for this diagnostic example.  Every RETAINED quantity is an
// exact integer (`i128`/`u128`/`BigInt`); the allowed casts occur only where a
// ratio is converted for PRINTING, and a printed ratio is never a certificate.
// The range loops index the packed mixed-radix group coordinate, where the
// index IS the group element, so iterating the slice instead would lose the
// meaning.
#![allow(
    clippy::cast_precision_loss,
    clippy::cast_possible_wrap,
    clippy::cast_possible_truncation,
    clippy::needless_range_loop,
    clippy::too_many_lines,
    clippy::many_single_char_names,
    clippy::unreadable_literal
)]
use axeyum_cas::gf2_hayes::{
    HayesLimits, class_population_distribution, exact_conductor_second_moment,
};
use num_bigint::BigInt;
use num_traits::Signed;

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
        max_degree: degree.max(60),
        max_group_order: 1 << 24,
        max_table_cells: 1 << 62,
    }
}

struct Levels {
    /// `A_j` for `j = 1..=ell`, indexed from zero.
    a: Vec<Vec<i128>>,
    /// `S_j = sum_e A_j(e)^2`.
    s: Vec<i128>,
    discrepancy: Vec<i128>,
    ell: usize,
    #[allow(dead_code)]
    degree: usize,
    order: usize,
}

fn build_levels(group: &Group, ell: usize, degree: usize) -> Result<Levels, String> {
    let distribution = class_population_distribution(ell, degree, limits(ell, degree))
        .map_err(|error| format!("population declined: {error:?}"))?;
    let mean = i128::try_from(
        distribution
            .uniform_mean()
            .ok_or_else(|| "no uniform mean".to_owned())?,
    )
    .map_err(|_| "mean exceeds i128".to_owned())?;
    let discrepancy: Vec<i128> = (0..group.order)
        .map(|class| i128::try_from(distribution.counts[class]).expect("count") - mean)
        .collect();
    let total: i128 = discrepancy.iter().sum();
    if total != 0 {
        return Err(format!("sum_e D_e = {total}, expected 0"));
    }
    // Sibling recursion downward in the conductor level.
    let mut r = discrepancy.clone();
    let mut a = vec![Vec::new(); ell + 1];
    for j in (1..=ell).rev() {
        let generator = group.index(1 | (1_u64 << j));
        let shifted: Vec<i128> = (0..group.order)
            .map(|class| r[group.add(class, generator)])
            .collect();
        a[j] = (0..group.order)
            .map(|class| r[class] - shifted[class])
            .collect();
        for class in 0..group.order {
            r[class] += shifted[class];
        }
    }
    // R_0 must be the (zero) total in every class.
    if r.iter().any(|value| *value != 0) {
        return Err("R_0 is not identically zero".to_owned());
    }
    // Reconstruction control: sum_j A_j / 2^(ell-j+1) = D, tested after
    // clearing denominators by 2^ell.
    for class in 0..group.order {
        let mut accumulated = 0_i128;
        for j in 1..=ell {
            let shift = u32::try_from(j - 1).expect("shift");
            accumulated += a[j][class] << shift;
        }
        let expected = discrepancy[class] << u32::try_from(ell).expect("shift");
        if accumulated != expected {
            return Err(format!(
                "level reconstruction failed at class {class}: {accumulated} != {expected}"
            ));
        }
    }
    let s: Vec<i128> = (0..=ell)
        .map(|j| {
            if j == 0 {
                0
            } else {
                a[j].iter().map(|value| value * value).sum()
            }
        })
        .collect();
    Ok(Levels {
        a,
        s,
        discrepancy,
        ell,
        degree,
        order: group.order,
    })
}

fn moments(levels: &Levels) -> (u128, u128, BigInt) {
    let mut m2 = 0_u128;
    let mut m4 = 0_u128;
    for value in &levels.discrepancy {
        let square = value.unsigned_abs() * value.unsigned_abs();
        m2 += square;
        m4 += square * square;
    }
    let k4 = BigInt::from(levels.order) * BigInt::from(m4)
        - BigInt::from(3_u32) * BigInt::from(m2) * BigInt::from(m2);
    (m2, m4, k4)
}

struct LevelCell {
    levels: [usize; 4],
    multiplicity: u128,
    /// `K_lev * 2^(4 ell)`, an exact integer.
    scaled: BigInt,
}

fn multiplicity(indices: [usize; 4]) -> u128 {
    let mut runs: Vec<usize> = Vec::new();
    let mut last = usize::MAX;
    for value in indices {
        if value == last {
            *runs.last_mut().expect("run") += 1;
        } else {
            runs.push(1);
            last = value;
        }
    }
    let mut result = 24_u128;
    for run in runs {
        result /= (1..=run as u128).product::<u128>();
    }
    result
}

/// `sum_e Uhat(e)^4` with `Uhat(e) = sum_j |A_j(e)| 2^(j-1) = 2^ell U_L(e)`,
/// the pointwise level-absolute envelope.  Signed, this is exactly `2^ell D`.
fn level_absolute_envelope(levels: &Levels) -> (BigInt, BigInt) {
    let ell = levels.ell;
    let mut fourth = BigInt::from(0);
    let mut second = BigInt::from(0);
    for e in 0..levels.order {
        let mut envelope = 0_u128;
        for j in 1..=ell {
            if levels.s[j] == 0 {
                continue;
            }
            envelope += levels.a[j][e].unsigned_abs() << u32::try_from(j - 1).expect("shift");
        }
        let square = BigInt::from(envelope) * BigInt::from(envelope);
        second += &square;
        fourth += &square * &square;
    }
    (second, fourth)
}

fn build_level_cells(levels: &Levels) -> (Vec<LevelCell>, BigInt, BigInt, BigInt) {
    let ell = levels.ell;
    let active: Vec<usize> = (1..=ell).filter(|j| levels.s[*j] != 0).collect();
    let k = active.len();
    // Magnitude guard for the i128 raw accumulator.
    let peak = active
        .iter()
        .map(|j| {
            levels.a[*j]
                .iter()
                .map(|v| v.unsigned_abs())
                .max()
                .unwrap_or(0)
        })
        .max()
        .unwrap_or(0);
    let mass = active
        .iter()
        .map(|j| levels.a[*j].iter().map(|v| v.unsigned_abs()).sum::<u128>())
        .max()
        .unwrap_or(0);
    let ceiling = peak
        .checked_mul(peak)
        .and_then(|v| v.checked_mul(peak))
        .and_then(|v| v.checked_mul(mass))
        .expect("guard overflow");
    assert!(ceiling < (1_u128 << 126), "i128 level tensor would wrap");
    let mut index: Vec<[usize; 4]> = Vec::new();
    for a in 0..k {
        for b in a..k {
            for c in b..k {
                for d in c..k {
                    index.push([a, b, c, d]);
                }
            }
        }
    }
    let mut raw = vec![0_i128; index.len()];
    for e in 0..levels.order {
        let mut slot = 0_usize;
        for a in 0..k {
            let ta = levels.a[active[a]][e];
            if ta == 0 {
                for b in a..k {
                    for c in b..k {
                        slot += k - c;
                    }
                }
                continue;
            }
            for b in a..k {
                let tab = ta * levels.a[active[b]][e];
                if tab == 0 {
                    for c in b..k {
                        slot += k - c;
                    }
                    continue;
                }
                for c in b..k {
                    let tabc = tab * levels.a[active[c]][e];
                    if tabc == 0 {
                        slot += k - c;
                        continue;
                    }
                    for d in c..k {
                        raw[slot] += tabc * levels.a[active[d]][e];
                        slot += 1;
                    }
                }
            }
        }
        debug_assert_eq!(slot, index.len());
    }
    let mut cells = Vec::with_capacity(index.len());
    let mut signed = BigInt::from(0);
    let mut absolute = BigInt::from(0);
    let mut raw_absolute = BigInt::from(0);
    for (slot, quad) in index.iter().enumerate() {
        let js = [
            active[quad[0]],
            active[quad[1]],
            active[quad[2]],
            active[quad[3]],
        ];
        let exponent = ell + js.iter().sum::<usize>() - 4;
        let mut scaled = (BigInt::from(1) << exponent) * BigInt::from(raw[slot]);
        let mult_raw = multiplicity(js);
        raw_absolute += BigInt::from(mult_raw) * scaled.abs();
        // Wick part: only matchings of equal levels survive orthogonality.
        for matching in [[0_usize, 1, 2, 3], [0, 2, 1, 3], [0, 3, 1, 2]] {
            let (p, q, r, t) = (
                js[matching[0]],
                js[matching[1]],
                js[matching[2]],
                js[matching[3]],
            );
            if p == q && r == t {
                let shift = 2 * p + 2 * r - 4;
                scaled -= (BigInt::from(1) << shift)
                    * BigInt::from(levels.s[p])
                    * BigInt::from(levels.s[r]);
            }
        }
        let mult = multiplicity(js);
        signed += BigInt::from(mult) * &scaled;
        absolute += BigInt::from(mult) * scaled.abs();
        cells.push(LevelCell {
            levels: js,
            multiplicity: mult,
            scaled,
        });
    }
    (cells, signed, absolute, raw_absolute)
}

fn endpoints(ell: usize) -> [usize; 2] {
    [2 * ell + 1, 2 * ell + 2]
}

fn report(
    group: &Group,
    ell: usize,
    degree: usize,
    verbose: bool,
    top: usize,
) -> Result<(), String> {
    let levels = build_levels(group, ell, degree)?;
    // Orthogonality control on a deterministic subset of level pairs.
    for j in 1..=ell {
        for k in (j + 1)..=ell {
            let cross: i128 = (0..group.order)
                .map(|e| levels.a[j][e] * levels.a[k][e])
                .sum();
            if cross != 0 {
                return Err(format!("levels {j},{k} are not orthogonal: {cross}"));
            }
        }
    }
    let (m2, _m4, k4) = moments(&levels);
    let (cells, signed, absolute, raw_absolute) = build_level_cells(&levels);
    let (_envelope_second, envelope_fourth) = level_absolute_envelope(&levels);
    let scale = BigInt::from(1) << (4 * ell);
    if signed != &k4 * &scale {
        return Err(format!(
            "level cells reconstruct {signed}, expected {}",
            &k4 * &scale
        ));
    }
    let budget_exponent = ell + 4 * (degree - ell);
    let affordable = ((BigInt::from(1) << budget_exponent)
        - BigInt::from(3_u32) * BigInt::from(m2) * BigInt::from(m2))
        * &scale;
    let closure = bigint_ratio(&absolute, &affordable);
    // Strict budget: 2^ell (mu - P_n)^4 - 3 M_2^2 with P_n from diary 04
    // Lemma A (odd, exact) / Lemma B (even, proved upper bound).
    let mu = BigInt::from(1) << (degree - ell);
    let proper = if degree % 2 == 1 {
        BigInt::from(1)
    } else {
        BigInt::from(ell + 1) * (BigInt::from(1) << ell.div_ceil(2))
            + BigInt::from(degree) * (BigInt::from(1) << (ell + 1).div_ceil(2))
    };
    let head = &mu - &proper;
    let strict = if head.sign() == num_bigint::Sign::Plus {
        (BigInt::from(1) << ell) * (&head * &head) * (&head * &head)
            - BigInt::from(3_u32) * BigInt::from(m2) * BigInt::from(m2)
    } else {
        BigInt::from(-1)
    };
    let strict_scaled = &strict * &scale;
    let strict_closure = if strict.sign() == num_bigint::Sign::Plus {
        bigint_ratio(&absolute, &strict_scaled)
    } else {
        f64::INFINITY
    };
    let zero_cells = cells
        .iter()
        .filter(|cell| cell.scaled.sign() == num_bigint::Sign::NoSign)
        .count();
    let odd_max_cells = cells
        .iter()
        .filter(|cell| {
            let top = cell.levels[3];
            cell.levels.iter().filter(|j| **j == top).count() % 2 == 1
        })
        .count();
    let odd_max_nonzero = cells
        .iter()
        .filter(|cell| {
            let top = cell.levels[3];
            cell.levels.iter().filter(|j| **j == top).count() % 2 == 1
                && cell.scaled.sign() != num_bigint::Sign::NoSign
        })
        .count();
    // Split bound: A_L <= R_L + 3 M_2^2 (Wick part is exactly 3 M_2^2).
    let wick_scaled = BigInt::from(3_u32) * BigInt::from(m2) * BigInt::from(m2) * &scale;
    let split_closure = bigint_ratio(&(&raw_absolute + &wick_scaled), &affordable);
    // Pointwise envelope bound: sum_e Uhat^4 < 2^(4 ell)(mu-P_n)^4 - 3 2^(3 ell) M_2^2.
    let envelope_budget = if head.sign() == num_bigint::Sign::Plus {
        (BigInt::from(1) << (4 * ell)) * (&head * &head) * (&head * &head)
            - BigInt::from(3_u32)
                * BigInt::from(m2)
                * BigInt::from(m2)
                * (BigInt::from(1) << (3 * ell))
    } else {
        BigInt::from(-1)
    };
    let envelope_closure = if envelope_budget.sign() == num_bigint::Sign::Plus {
        bigint_ratio(&envelope_fourth, &envelope_budget)
    } else {
        f64::INFINITY
    };
    println!(
        "ACB_CABL|probe=row|ell={ell}|n={degree}|cells={}|active_levels={}|m2={m2}|k4={k4}|abs_scaled={absolute}|affordable_scaled={affordable}|closure={closure:.6}|strict_closure={strict_closure:.6}|zero_cells={zero_cells}|odd_max_cells={odd_max_cells}|odd_max_nonzero={odd_max_nonzero}|raw_abs_scaled={raw_absolute}|split_closure={split_closure:.6}|envelope_fourth={envelope_fourth}|envelope_closure={envelope_closure:.6}",
        cells.len(),
        levels.s.iter().filter(|v| **v != 0).count()
    );
    if verbose {
        let mu = 1_u128 << (degree - ell);
        for j in 1..=ell {
            if levels.s[j] == 0 {
                continue;
            }
            // V_j = S_j / 2^(2(ell-j+1)); Weil envelope 2^(n-ell) 2^(j-1) (j-1)^2.
            let denominator = 1_u128 << (2 * (ell - j + 1));
            let energy = levels.s[j] as f64 / denominator as f64;
            let weil = (mu as f64) * ((1_u128 << (j - 1)) as f64) * ((j - 1) * (j - 1)) as f64;
            println!(
                "ACB_CABL|probe=level|ell={ell}|n={degree}|j={j}|energy={energy:.1}|weil={weil:.1}|fill={:.4}|share={:.6}",
                if weil > 0.0 { energy / weil } else { 0.0 },
                energy / m2 as f64
            );
        }
        // Mass split by how many indices sit at the TOP level ell.
        let mut by_top: Vec<BigInt> = (0..5).map(|_| BigInt::from(0)).collect();
        for cell in &cells {
            let count = cell.levels.iter().filter(|j| **j == ell).count();
            by_top[count] += BigInt::from(cell.multiplicity) * cell.scaled.abs();
        }
        for (count, mass) in by_top.iter().enumerate() {
            println!(
                "ACB_CABL|probe=toplevel|ell={ell}|n={degree}|top_indices={count}|mass={mass}|share={:.6}",
                bigint_ratio(mass, &absolute)
            );
        }
    }
    if top > 0 {
        let mut ranked: Vec<&LevelCell> = cells.iter().collect();
        ranked.sort_by_key(|cell| {
            std::cmp::Reverse(BigInt::from(cell.multiplicity) * cell.scaled.abs())
        });
        for cell in ranked.into_iter().take(top) {
            let weighted = BigInt::from(cell.multiplicity) * cell.scaled.abs();
            println!(
                "ACB_CABL|probe=top|ell={ell}|n={degree}|levels={:?}|mult={}|share={:.6}",
                cell.levels,
                cell.multiplicity,
                bigint_ratio(&weighted, &absolute)
            );
        }
    }
    Ok(())
}

fn bigint_ratio(numerator: &BigInt, denominator: &BigInt) -> f64 {
    let scale = BigInt::from(1_u64 << 40);
    let quotient = (numerator * &scale) / denominator;
    let (sign, digits) = quotient.to_u64_digits();
    let magnitude = digits.iter().rev().fold(0.0_f64, |acc, digit| {
        acc * 18446744073709551616.0 + *digit as f64
    });
    let value = magnitude / (1_u64 << 40) as f64;
    if sign == num_bigint::Sign::Minus {
        -value
    } else {
        value
    }
}

fn main() -> Result<(), String> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() < 3 {
        return Err("usage: acb_cab_levels <sweep|row|top> <a> <b> [k]".to_owned());
    }
    let mode = args[0].clone();
    let lo: usize = args[1]
        .parse()
        .map_err(|_| "bad first argument".to_owned())?;
    match mode.as_str() {
        "sweep" => {
            let hi: usize = args[2].parse().map_err(|_| "bad hi".to_owned())?;
            for ell in lo..=hi {
                let group = Group::new(ell);
                if ell <= 10 {
                    group.check_add();
                }
                for degree in endpoints(ell) {
                    if let Err(error) = report(&group, ell, degree, false, 0) {
                        println!("ACB_CABL|ell={ell}|n={degree}|declined={error}");
                    }
                }
            }
        }
        "layers" => {
            let degree: usize = args[2].parse().map_err(|_| "bad n".to_owned())?;
            let group = Group::new(lo);
            let levels = build_levels(&group, lo, degree)?;
            let ell = lo;
            let mu = (1_u128 << (degree - ell)) as f64;
            let proper: f64 = if degree % 2 == 1 {
                1.0
            } else {
                ((ell + 1) as f64) * ((1_u128 << ell.div_ceil(2)) as f64)
                    + (degree as f64) * ((1_u128 << (ell + 1).div_ceil(2)) as f64)
            };
            let head = mu - proper;
            let mut l4_sum = 0.0_f64;
            for j in 1..=ell {
                if levels.s[j] == 0 {
                    continue;
                }
                let mut fourth = 0_u128;
                let mut peak = 0_u128;
                for value in &levels.a[j] {
                    let square = value.unsigned_abs() * value.unsigned_abs();
                    fourth += square * square;
                    peak = peak.max(value.unsigned_abs());
                }
                let denominator = (1_u128 << (ell - j + 1)) as f64;
                let l4 = (fourth as f64).powf(0.25) / denominator;
                let sup = peak as f64 / denominator;
                // Trivial per-layer triangle bound on the sup norm:
                // max_e |D_[j]| <= 2^(j-1) (j-1) 2^(n/2) / 2^ell.
                let triangle = ((1_u128 << (j - 1)) as f64)
                    * ((j - 1) as f64)
                    * (2.0_f64).powf(degree as f64 / 2.0)
                    / ((1_u128 << ell) as f64);
                l4_sum += l4;
                println!(
                    "ACB_CABL|probe=layer|ell={ell}|n={degree}|j={j}|l4={l4:.4e}|sup={sup:.4e}|triangle_sup={triangle:.4e}|sup_over_triangle={:.6}|l4_over_mu={:.6}",
                    sup / triangle,
                    l4 / mu
                );
            }
            println!(
                "ACB_CABL|probe=layer_total|ell={ell}|n={degree}|sum_l4={l4_sum:.6e}|head={head:.6e}|minkowski_closure={:.6}",
                l4_sum / head
            );
        }
        "control" => {
            let degree: usize = args[2].parse().map_err(|_| "bad n".to_owned())?;
            let group = Group::new(lo);
            group.check_add();
            let levels = build_levels(&group, lo, degree)?;
            for j in 1..=lo {
                // 2^ell V_j must equal the CAS exact conductor second moment.
                let mine = BigInt::from(levels.s[j]) << u32::try_from(lo).expect("shift");
                let mine = mine >> u32::try_from(2 * (lo - j + 1)).expect("shift");
                let residual = (BigInt::from(levels.s[j]) << u32::try_from(lo).expect("shift"))
                    - (&mine << u32::try_from(2 * (lo - j + 1)).expect("shift"));
                match exact_conductor_second_moment(j, degree, limits(lo, degree)) {
                    Ok(report) => {
                        let theirs = BigInt::from(report.value);
                        println!(
                            "ACB_CABL|control=conductor_second_moment|ell={lo}|n={degree}|j={j}|mine={mine}|cas={theirs}|agree={}|exact_division={}",
                            mine == theirs,
                            residual.sign() == num_bigint::Sign::NoSign
                        );
                        assert_eq!(mine, theirs, "level energy disagrees with the CAS at j={j}");
                    }
                    Err(error) => println!(
                        "ACB_CABL|control=conductor_second_moment|ell={lo}|n={degree}|j={j}|declined={error:?}"
                    ),
                }
            }
        }
        "row" | "top" => {
            let degree: usize = args[2].parse().map_err(|_| "bad n".to_owned())?;
            let top: usize = if mode == "top" {
                args[3].parse().map_err(|_| "bad k".to_owned())?
            } else {
                0
            };
            let group = Group::new(lo);
            group.check_add();
            report(&group, lo, degree, mode == "row", top)?;
        }
        other => return Err(format!("unknown mode {other}")),
    }
    Ok(())
}
