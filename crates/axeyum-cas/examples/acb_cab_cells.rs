//! AC-Bridge workstream A: structure of the connected order-cumulant cells
//! `K_(a,b,c,d)` behind the resurrected cellwise-absolute candidate
//!
//! ```text
//! (CAB)  sum_(a<=b<=c<=d) mult |K_(a,b,c,d)| < 2^(ell+4(n-ell)) - 3 M_2^2 .
//! ```
//!
//! This is an INDEPENDENT reimplementation of the interval-order vectors
//! `T_d` and of the symmetric cell tensor, sharing no code path with
//! `connected_order_cumulant_report` beyond the public
//! `class_mobius_distribution` / `class_population_distribution` inputs.  It
//! is verified against that report cell-by-cell wherever the report admits,
//! and against `sum_d T_d = D` on every class of every row.
//!
//! Read-only diagnostic.  Every retained quantity is an exact integer; the
//! only floating point is in printed ratios, which are diagnostics and never
//! a certificate.  Finite computation is evidence, never a theorem.
//!
//! Usage:
//!   `acb_cab_cells verify <ell> <n>`  -- cross-check against the CAS report
//!   `acb_cab_cells row <ell> <n>`     -- full per-row structure dump
//!   `acb_cab_cells sweep <lo> <hi>`   -- (CAB) closure table, both parities
//!   `acb_cab_cells top <ell> <n> <k>` -- the `k` heaviest cells
//!   `acb_cab_cells orders <ell> <n>`  -- per-order energies and covariances

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
    HayesLimits, class_mobius_distribution, class_population_distribution,
    connected_order_cumulant_report,
};

/// Cyclic factor of `E_ell`: generator `1+x^odd_degree` of the given order.
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

/// Packed mixed-radix group: field `i` occupies `log2(order_i)` bits, low
/// field first, so the mixed-radix index IS the packed bitfield word and
/// group addition is a carry-masked SWAR add.
struct Group {
    ell: usize,
    order: usize,
    /// Top bit of every field.
    high: u64,
    /// All bits except the top bit of every field.
    low: u64,
    /// `unit_of[index]`, and `index_of[(unit>>1)]`.
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
            let width = factor.order.trailing_zeros();
            offset += width;
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

    /// Independent control: the packed SWAR add must agree with the group
    /// multiplication of the corresponding units, on every pair when the
    /// group is small and on a deterministic stride otherwise.
    fn check_add(&self) {
        let stride = if self.order <= 512 { 1 } else { 37 };
        let mut checked = 0_usize;
        let mut a = 0_usize;
        while a < self.order {
            let mut b = 0_usize;
            while b < self.order {
                let via_group =
                    self.index(unit_multiply(self.unit_of[a], self.unit_of[b], self.ell));
                assert_eq!(self.add(a, b), via_group, "SWAR add disagrees at ({a},{b})");
                checked += 1;
                b += stride;
            }
            a += stride;
        }
        assert!(checked > 0, "SWAR control examined nothing");
        println!(
            "ACB_CAB|control=swar_add|ell={}|pairs_checked={checked}",
            self.ell
        );
    }
}

fn interval_units(group: &Group, d: usize) -> Vec<usize> {
    // V_d = {1 + a_1 x + ... + a_d x^d}; store the index of each inverse.
    (0..1_u64 << d)
        .map(|tail| {
            let unit = 1 | (tail << 1);
            let index = group.index(unit);
            // inverse index = per-field negation
            let mut inverse = 0_usize;
            let fs = factors(group.ell);
            let mut rest = index;
            let mut stride = 1_usize;
            for factor in &fs {
                let coordinate = rest % factor.order;
                rest /= factor.order;
                let negated = if coordinate == 0 {
                    0
                } else {
                    factor.order - coordinate
                };
                inverse += negated * stride;
                stride *= factor.order;
            }
            inverse
        })
        .collect()
}

fn limits(ell: usize, degree: usize) -> HayesLimits {
    HayesLimits {
        max_ell: ell.max(24),
        max_degree: degree.max(60),
        max_group_order: 1 << 24,
        max_table_cells: 1 << 62,
    }
}

/// Exact interval-order vectors `T_d`, `d = 1..ell-1`, and the class
/// discrepancy they reconstruct.
struct Orders {
    #[allow(dead_code)]
    ell: usize,
    #[allow(dead_code)]
    degree: usize,
    group_order: usize,
    t: Vec<Vec<i128>>,
    discrepancy: Vec<i128>,
    #[allow(dead_code)]
    mean: i128,
}

fn build_orders(group: &Group, ell: usize, degree: usize) -> Result<Orders, String> {
    let lim = limits(ell, degree);
    let mut t = Vec::with_capacity(ell - 1);
    for d in 1..ell {
        let mobius = class_mobius_distribution(ell, degree - d, lim)
            .map_err(|error| format!("mobius declined: {error:?}"))?;
        let inverses = interval_units(group, d);
        let weight = i128::try_from(d).expect("degree fits i128");
        let mut values = vec![0_i128; group.order];
        for &inverse in &inverses {
            for (class, slot) in values.iter_mut().enumerate() {
                *slot += mobius.values[group.add(class, inverse)];
            }
        }
        for slot in &mut values {
            *slot *= weight;
        }
        t.push(values);
    }
    let distribution = class_population_distribution(ell, degree, lim)
        .map_err(|error| format!("population declined: {error:?}"))?;
    let mean = i128::try_from(
        distribution
            .uniform_mean()
            .ok_or_else(|| "no uniform mean".to_owned())?,
    )
    .map_err(|_| "uniform mean exceeds i128".to_owned())?;
    let mut discrepancy = Vec::with_capacity(group.order);
    for class in 0..group.order {
        let expected = i128::try_from(distribution.counts[class]).expect("count fits i128") - mean;
        let got: i128 = t.iter().map(|values| values[class]).sum();
        if got != expected {
            return Err(format!(
                "order reconstruction failed at class {class}: {got} != {expected}"
            ));
        }
        discrepancy.push(expected);
    }
    Ok(Orders {
        ell,
        degree,
        group_order: group.order,
        t,
        discrepancy,
        mean,
    })
}

#[derive(Debug, Clone)]
struct Cell {
    orders: [usize; 4],
    multiplicity: u128,
    raw: i128,
    pairing: i128,
    connected: i128,
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

struct Tensor {
    covariance: Vec<Vec<i128>>,
    cells: Vec<Cell>,
    signed: i128,
    absolute: u128,
    pairing_absolute: u128,
    raw_absolute: u128,
}

/// Fail-closed magnitude guard: every `i128` product formed below is bounded
/// by `2^ell (max|T|)^3 (sum_e |T|)`, so checking that bound once rules out
/// silent wrapping in the release profile.
fn guard_magnitudes(orders: &Orders) {
    let peak = orders
        .t
        .iter()
        .map(|values| values.iter().map(|v| v.unsigned_abs()).max().unwrap_or(0))
        .max()
        .unwrap_or(0);
    let mass = orders
        .t
        .iter()
        .map(|values| values.iter().map(|v| v.unsigned_abs()).sum::<u128>())
        .max()
        .unwrap_or(0);
    let ceiling = (orders.group_order as u128)
        .checked_mul(peak)
        .and_then(|v| v.checked_mul(peak))
        .and_then(|v| v.checked_mul(peak))
        .and_then(|v| v.checked_mul(mass))
        .expect("magnitude guard overflows u128");
    assert!(
        ceiling < (1_u128 << 126),
        "i128 tensor arithmetic would wrap: ceiling 2^{}",
        (ceiling as f64).log2()
    );
}

fn build_tensor(orders: &Orders) -> Tensor {
    guard_magnitudes(orders);
    let k = orders.t.len();
    let n = orders.group_order;
    let mut covariance = vec![vec![0_i128; k]; k];
    for a in 0..k {
        for b in a..k {
            let value: i128 = (0..n).map(|e| orders.t[a][e] * orders.t[b][e]).sum();
            covariance[a][b] = value;
            covariance[b][a] = value;
        }
    }
    let scale = i128::try_from(n).expect("group order fits i128");
    // raw[a][b][c][d] accumulated with a<=b<=c<=d in one pass over classes.
    let mut index = vec![[0_usize; 4]; 0];
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
    for e in 0..n {
        let mut slot = 0_usize;
        for a in 0..k {
            let ta = orders.t[a][e];
            if ta == 0 {
                // still must advance the slot counter
                for b in a..k {
                    for c in b..k {
                        slot += k - c;
                    }
                }
                continue;
            }
            for b in a..k {
                let tab = ta * orders.t[b][e];
                if tab == 0 {
                    for c in b..k {
                        slot += k - c;
                    }
                    continue;
                }
                for c in b..k {
                    let tabc = tab * orders.t[c][e];
                    if tabc == 0 {
                        slot += k - c;
                        continue;
                    }
                    for d in c..k {
                        raw[slot] += tabc * orders.t[d][e];
                        slot += 1;
                    }
                }
            }
        }
        debug_assert_eq!(slot, index.len());
    }
    let mut cells = Vec::with_capacity(index.len());
    let mut signed = 0_i128;
    let mut absolute = 0_u128;
    let mut pairing_absolute = 0_u128;
    let mut raw_absolute = 0_u128;
    for (slot, orders_index) in index.iter().enumerate() {
        let [a, b, c, d] = *orders_index;
        let pairing = covariance[a][b] * covariance[c][d]
            + covariance[a][c] * covariance[b][d]
            + covariance[a][d] * covariance[b][c];
        let connected = scale * raw[slot] - pairing;
        let mult = multiplicity([a, b, c, d]);
        signed += i128::try_from(mult).expect("multiplicity fits i128") * connected;
        absolute += mult * connected.unsigned_abs();
        pairing_absolute += mult * pairing.unsigned_abs();
        raw_absolute += mult * (scale * raw[slot]).unsigned_abs();
        cells.push(Cell {
            orders: [a + 1, b + 1, c + 1, d + 1],
            multiplicity: mult,
            raw: raw[slot],
            pairing,
            connected,
        });
    }
    Tensor {
        covariance,
        cells,
        signed,
        absolute,
        pairing_absolute,
        raw_absolute,
    }
}

fn moments(orders: &Orders) -> (u128, u128, i128) {
    let mut m2 = 0_u128;
    let mut m4 = 0_u128;
    for value in &orders.discrepancy {
        let square = value
            .unsigned_abs()
            .checked_mul(value.unsigned_abs())
            .expect("D^2");
        m2 = m2.checked_add(square).expect("M_2 overflow");
        m4 = m4
            .checked_add(square.checked_mul(square).expect("D^4"))
            .expect("M_4 overflow");
    }
    let scale = orders.group_order as u128;
    let total = i128::try_from(scale.checked_mul(m4).expect("2^ell M_4 overflow"))
        .expect("2^ell M_4 fits i128");
    let wick = i128::try_from(
        m2.checked_mul(m2)
            .and_then(|v| v.checked_mul(3))
            .expect("3 M_2^2 overflow"),
    )
    .expect("3 M_2^2 fits i128");
    (m2, m4, total - wick)
}

fn log2(value: f64) -> f64 {
    value.log2()
}

fn budget(ell: usize, degree: usize, m2: u128) -> (u128, i128) {
    // 2^(ell + 4(n-ell)) - 3 M_2^2
    let exponent = ell + 4 * (degree - ell);
    assert!(exponent < 127, "budget exponent overflows i128");
    let total = 1_u128 << exponent;
    let wick = 3 * m2 * m2;
    (total, total as i128 - wick as i128)
}

fn print_row(ell: usize, degree: usize, orders: &Orders, tensor: &Tensor) {
    let (m2, m4, k4) = moments(orders);
    let (total, affordable) = budget(ell, degree, m2);
    let closure = tensor.absolute as f64 / affordable as f64;
    let ratio = (3.0 * (m2 as f64) * (m2 as f64) + tensor.absolute as f64) / total as f64;
    println!(
        "ACB_CAB|probe=row|ell={ell}|n={degree}|cells={}|m2={m2}|m4={m4}|k4={k4}|signed={}|abs_total={}|pairing_abs={}|raw_abs={}|budget=2^{}|affordable={affordable}|closure={closure:.6}|audit_ratio={ratio:.6}",
        tensor.cells.len(),
        tensor.signed,
        tensor.absolute,
        tensor.pairing_absolute,
        tensor.raw_absolute,
        ell + 4 * (degree - ell),
    );
    assert_eq!(tensor.signed, k4, "cell reconstruction disagrees with K_4");
}

fn verify(ell: usize, degree: usize, tensor: &Tensor) -> Result<(), String> {
    let report = connected_order_cumulant_report(ell, degree, limits(ell, degree))
        .map_err(|error| format!("report declined: {error:?}"))?;
    if report.cells.len() != tensor.cells.len() {
        return Err(format!(
            "cell count {} != {}",
            report.cells.len(),
            tensor.cells.len()
        ));
    }
    for (mine, theirs) in tensor.cells.iter().zip(report.cells.iter()) {
        if mine.orders != theirs.interval_degrees {
            return Err(format!("cell order mismatch {:?}", mine.orders));
        }
        if mine.multiplicity != theirs.permutation_multiplicity as u128 {
            return Err(format!("multiplicity mismatch at {:?}", mine.orders));
        }
        let raw = theirs.raw_fourth_sum.to_string();
        let pairing = theirs.pairing_sum.to_string();
        let connected = theirs.connected_numerator.to_string();
        if mine.raw.to_string() != raw
            || mine.pairing.to_string() != pairing
            || mine.connected.to_string() != connected
        {
            return Err(format!(
                "cell value mismatch at {:?}: mine ({},{},{}) theirs ({raw},{pairing},{connected})",
                mine.orders, mine.raw, mine.pairing, mine.connected
            ));
        }
    }
    println!(
        "ACB_CAB|control=cas_report|ell={ell}|n={degree}|cells_agree={}|direct={}",
        report.cells.len(),
        report.direct_fourth_cumulant_numerator
    );
    Ok(())
}

fn endpoints(ell: usize) -> [usize; 2] {
    [2 * ell + 1, 2 * ell + 2]
}

#[allow(clippy::too_many_lines)]
fn main() -> Result<(), String> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() < 2 {
        return Err("usage: acb_cab_cells <mode> <args...>".to_owned());
    }
    match args[0].as_str() {
        "verify" => {
            let ell: usize = args[1].parse().map_err(|_| "bad ell".to_owned())?;
            let degree: usize = args[2].parse().map_err(|_| "bad n".to_owned())?;
            let group = Group::new(ell);
            group.check_add();
            let orders = build_orders(&group, ell, degree)?;
            let tensor = build_tensor(&orders);
            verify(ell, degree, &tensor)?;
            print_row(ell, degree, &orders, &tensor);
        }
        "row" | "sweep" | "orders" | "top" | "profile" => {
            let lo: usize = args[1].parse().map_err(|_| "bad ell".to_owned())?;
            let hi: usize = if args[0] == "sweep" {
                args[2].parse().map_err(|_| "bad hi".to_owned())?
            } else {
                lo
            };
            for ell in lo..=hi {
                let group = Group::new(ell);
                let degrees: Vec<usize> = if args[0] == "sweep" {
                    endpoints(ell).to_vec()
                } else {
                    vec![args[2].parse().map_err(|_| "bad n".to_owned())?]
                };
                for degree in degrees {
                    let orders = match build_orders(&group, ell, degree) {
                        Ok(orders) => orders,
                        Err(error) => {
                            println!("ACB_CAB|ell={ell}|n={degree}|declined={error}");
                            continue;
                        }
                    };
                    let tensor = build_tensor(&orders);
                    print_row(ell, degree, &orders, &tensor);
                    if args[0] == "orders" {
                        let k = orders.t.len();
                        for d in 0..k {
                            let energy = tensor.covariance[d][d];
                            let peak = orders.t[d].iter().map(|v| v.abs()).max().unwrap_or(0);
                            let l1: i128 = orders.t[d].iter().map(|v| v.abs()).sum();
                            println!(
                                "ACB_CAB|probe=order|ell={ell}|n={degree}|d={}|energy={energy}|max={peak}|l1={l1}|log2_energy={:.4}",
                                d + 1,
                                log2(energy as f64)
                            );
                        }
                        let mut covariance_l1 = 0_i128;
                        for row in &tensor.covariance {
                            for value in row {
                                covariance_l1 += value.abs();
                            }
                        }
                        let (m2, _, _) = moments(&orders);
                        println!(
                            "ACB_CAB|probe=cov|ell={ell}|n={degree}|cov_l1={covariance_l1}|m2={m2}|ratio={:.4}",
                            covariance_l1 as f64 / m2 as f64
                        );
                    }
                    if args[0] == "profile" {
                        let k = orders.t.len();
                        // (i) mass by number of distinct orders in the cell
                        let mut by_distinct = [0_u128; 5];
                        // (ii) mass by max order
                        let mut by_max = vec![0_u128; k + 1];
                        // (iii) mass by min order
                        let mut by_min = vec![0_u128; k + 1];
                        // (iv) mass by order-sum
                        let mut by_sum = vec![0_u128; 4 * k + 1];
                        for cell in &tensor.cells {
                            let weighted = cell.multiplicity * cell.connected.unsigned_abs();
                            let mut distinct = 1_usize;
                            for i in 1..4 {
                                if cell.orders[i] != cell.orders[i - 1] {
                                    distinct += 1;
                                }
                            }
                            by_distinct[distinct] += weighted;
                            by_max[cell.orders[3]] += weighted;
                            by_min[cell.orders[0]] += weighted;
                            by_sum[cell.orders.iter().sum::<usize>()] += weighted;
                        }
                        for (distinct, mass) in by_distinct.iter().enumerate().skip(1) {
                            println!(
                                "ACB_CAB|probe=profile_distinct|ell={ell}|n={degree}|distinct={distinct}|mass={mass}|share={:.6}",
                                *mass as f64 / tensor.absolute as f64
                            );
                        }
                        for (order, mass) in by_max.iter().enumerate().skip(1) {
                            println!(
                                "ACB_CAB|probe=profile_max|ell={ell}|n={degree}|max_order={order}|mass={mass}|share={:.6}",
                                *mass as f64 / tensor.absolute as f64
                            );
                        }
                        for (order, mass) in by_min.iter().enumerate().skip(1) {
                            println!(
                                "ACB_CAB|probe=profile_min|ell={ell}|n={degree}|min_order={order}|mass={mass}|share={:.6}",
                                *mass as f64 / tensor.absolute as f64
                            );
                        }
                        for (total, mass) in by_sum.iter().enumerate() {
                            if *mass > 0 {
                                println!(
                                    "ACB_CAB|probe=profile_sum|ell={ell}|n={degree}|order_sum={total}|mass={mass}|share={:.6}",
                                    *mass as f64 / tensor.absolute as f64
                                );
                            }
                        }
                    }
                    if args[0] == "top" {
                        let count: usize = args[3].parse().map_err(|_| "bad k".to_owned())?;
                        let mut ranked: Vec<&Cell> = tensor.cells.iter().collect();
                        ranked.sort_by_key(|cell| {
                            std::cmp::Reverse(cell.multiplicity * cell.connected.unsigned_abs())
                        });
                        for cell in ranked.into_iter().take(count) {
                            let weighted = cell.multiplicity * cell.connected.unsigned_abs();
                            println!(
                                "ACB_CAB|probe=top|ell={ell}|n={degree}|orders={:?}|mult={}|weighted={weighted}|share={:.6}|connected={}|pairing={}",
                                cell.orders,
                                cell.multiplicity,
                                weighted as f64 / tensor.absolute as f64,
                                cell.connected,
                                cell.pairing
                            );
                        }
                    }
                }
            }
        }
        other => return Err(format!("unknown mode {other}")),
    }
    Ok(())
}
