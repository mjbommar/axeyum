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

//! AC-Bridge workstream D (rank/Arf split), task 1: an independent from-scratch
//! census of the inverse-coset fibres, built to falsify the structural
//! hypothesis `(GR-2)` of `docs/research/10-cas/ac-bridge-2026-08/03-lit-galois-ring-fourier.md`.
//!
//! `(GR-2)` asserts that every fibre whose correlation magnitude is a power of
//! two lies in the alternating stratum, i.e. that
//!
//! ```text
//! c_F = (-1)^(Arf(q_F)) 2^(n_F - r_F/2)
//! ```
//!
//! with `q_F` an ordinary `F_2`-valued quadratic function on the fibre and
//! `r_F` the rank of its alternating bilinear form.  For that statement to have
//! any content the fibre sign `eps(x) = mu(f_x) mu(f_(x+h))` must be nowhere
//! zero on `F`, since a Moebius zero (a squareful input) cannot be written as
//! `(-1)^(anything)`.
//!
//! This example shares no code with `gf2_hayes`: the Moebius sign is computed
//! by `GF(2)` factorization through a smallest-irreducible-factor sieve, the
//! principal-unit inverse by its own recursion, and the fibres by their own
//! grouping.  It then cross-checks its aggregate row against the in-tree
//! `binary_dyadic_autocorrelation_fibre_report`, and exits nonzero on any
//! disagreement or on a failed structural invariant.
//!
//! Usage: `acb_gr_fibre_census <ell_min> [ell_max] [--light]`.

use axeyum_cas::gf2_hayes::{HayesLimits, binary_dyadic_autocorrelation_fibre_report};
use num_bigint::BigUint;

fn main() {
    if let Err(error) = run() {
        eprintln!("ACB_GR_CENSUS|status=FAIL|error={error}");
        std::process::exit(1);
    }
}

/// Degree of a nonzero `GF(2)` polynomial held as a bit mask.
fn poly_degree(value: u64) -> usize {
    debug_assert!(value != 0);
    (u64::BITS - 1 - value.leading_zeros()) as usize
}

/// Quotient of `left` by `right` in `GF(2)[x]`.
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

/// Smallest irreducible factor of every monic `GF(2)` polynomial of degree at
/// most `degree`, indexed by bit mask.  Entry `0` and `1` are unused.
fn smallest_factor_sieve(degree: usize) -> Vec<u32> {
    let bound = 1_usize << (degree + 1);
    let mut smallest = vec![0_u32; bound];
    for candidate in 2..bound {
        if smallest[candidate] != 0 {
            continue;
        }
        let candidate_u64 = candidate as u64;
        let candidate_degree = poly_degree(candidate_u64);
        // `candidate` has no smaller irreducible factor, hence is irreducible.
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

/// Carry-less product in `GF(2)[x]`.
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

/// Binary Moebius value: `0` when squareful, `(-1)^(factor count)` otherwise.
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

/// Inverse of a principal unit in `GF(2)[x]/x^(ell+1)`, by its own recursion.
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

/// Row-reduce `vectors` over `F_2`, returning an echelon basis.
fn echelon_basis(vectors: &[u64]) -> Vec<u64> {
    let mut basis: Vec<u64> = Vec::new();
    for &vector in vectors {
        let mut current = vector;
        for &pivot in &basis {
            let candidate = current ^ pivot;
            if candidate < current {
                current = candidate;
            }
        }
        if current != 0 {
            basis.push(current);
            basis.sort_unstable_by(|a, b| b.cmp(a));
        }
    }
    basis
}

/// Coordinate of `vector` in the echelon `basis`, or `None` when outside.
fn coordinate_of(mut vector: u64, basis: &[u64]) -> Option<usize> {
    let mut coordinate = 0_usize;
    for (index, &pivot) in basis.iter().enumerate() {
        let candidate = vector ^ pivot;
        if candidate < vector {
            vector = candidate;
            coordinate |= 1 << index;
        }
    }
    if vector == 0 { Some(coordinate) } else { None }
}

/// Structural classification of one fibre's sign function.
#[derive(Default, Clone, Copy)]
struct FibreClass {
    dimension: usize,
    population: usize,
    nonzero_points: usize,
    correlation: i64,
    zero_free: bool,
    support_is_affine: bool,
    quadratic: bool,
    anf_degree: usize,
    rank: usize,
    gauss_magnitude_matches: bool,
    arf_sign_matches: bool,
    square_divisible_members: usize,
}

/// `F_2` algebraic normal form degree of a truth table of dimension `n`.
fn anf_degree(table: &[u8], dimension: usize) -> usize {
    let mut coefficients = table.to_vec();
    for bit in 0..dimension {
        let step = 1_usize << bit;
        for index in 0..coefficients.len() {
            if index & step != 0 {
                coefficients[index] ^= coefficients[index ^ step];
            }
        }
    }
    coefficients
        .iter()
        .enumerate()
        .filter(|&(_, &value)| value & 1 != 0)
        .map(|(index, _)| index.count_ones() as usize)
        .max()
        .unwrap_or(0)
}

/// Arf invariant and rank of an `F_2` quadratic function given by `q`, with
/// `q[0] = 0`.  Returns `(rank, tame, arf)`; `tame` false means the Gauss sum
/// vanishes because the radical carries a nontrivial linear character.
fn rank_and_arf(q: &[u8], dimension: usize) -> (usize, bool, u8) {
    let bilinear = |u: usize, v: usize| -> u8 { q[u ^ v] ^ q[u] ^ q[v] };
    // Matrix rows over the standard basis.
    let mut rows = vec![0_u64; dimension];
    for i in 0..dimension {
        for j in 0..dimension {
            if bilinear(1 << i, 1 << j) & 1 != 0 {
                rows[i] |= 1 << j;
            }
        }
    }
    // Track the change of basis so the radical is expressed in coordinates.
    let mut transform = (0..dimension).map(|i| 1_u64 << i).collect::<Vec<_>>();
    let mut rank = 0_usize;
    let mut pivot_column = 0_usize;
    let mut row = 0_usize;
    while row < dimension && pivot_column < dimension {
        let Some(found) = (row..dimension).find(|&index| rows[index] >> pivot_column & 1 != 0)
        else {
            pivot_column += 1;
            continue;
        };
        rows.swap(row, found);
        transform.swap(row, found);
        for other in 0..dimension {
            if other != row && rows[other] >> pivot_column & 1 != 0 {
                rows[other] ^= rows[row];
                transform[other] ^= transform[row];
            }
        }
        rank += 1;
        row += 1;
        pivot_column += 1;
    }
    // Rows `rank..` of `transform` span the radical.
    let mut tame = true;
    for entry in transform.iter().skip(rank) {
        let vector = usize::try_from(*entry).unwrap_or(0);
        if q[vector] & 1 != 0 {
            tame = false;
        }
    }
    // Arf invariant on a symplectic complement, computed by elimination on the
    // full space (radical vectors never pair, so they drop out harmlessly).
    let mut vectors: Vec<usize> = (0..dimension).map(|i| 1_usize << i).collect();
    let mut arf = 0_u8;
    while let Some((first, second)) = pick_symplectic_pair(&vectors, &bilinear) {
        let u = vectors[first];
        let v = vectors[second];
        arf ^= (q[u] & 1) & (q[v] & 1);
        let mut next = Vec::with_capacity(vectors.len());
        for (index, &w) in vectors.iter().enumerate() {
            if index == first || index == second {
                continue;
            }
            let mut adjusted = w;
            if bilinear(w, v) & 1 != 0 {
                adjusted ^= u;
            }
            if bilinear(w, u) & 1 != 0 {
                adjusted ^= v;
            }
            next.push(adjusted);
        }
        vectors = next;
    }
    (rank, tame, arf)
}

fn pick_symplectic_pair(
    vectors: &[usize],
    bilinear: &dyn Fn(usize, usize) -> u8,
) -> Option<(usize, usize)> {
    for i in 0..vectors.len() {
        for j in (i + 1)..vectors.len() {
            if bilinear(vectors[i], vectors[j]) & 1 != 0 {
                return Some((i, j));
            }
        }
    }
    None
}

struct RowTotals {
    fibre_count: usize,
    points: u128,
    nonzero_points: u128,
    square_sum: BigUint,
    absolute_sum: u128,
    signed_total: i128,
    nonzero_fibres: usize,
    power_of_two_fibres: usize,
    magnitude_histogram: Vec<(u64, usize)>,
    zero_free_fibres: usize,
    zero_free_points: u128,
    zero_free_quadratic: usize,
    zero_free_nonquadratic: usize,
    gauss_matches: usize,
    arf_matches: usize,
    support_affine_fibres: usize,
    dimension_histogram: Vec<usize>,
    rank_histogram: Vec<usize>,
    pow2_not_zero_free: usize,
    pow2_zero_free_nonquadratic: usize,
    square_forced_violations: usize,
    square_divisible_total: u128,
    large_pow2: usize,
    large_nonzero: usize,
    witness: Option<String>,
    tame_defect_mass: BigUint,
    nontame_point_mass: BigUint,
    stratum: Vec<DimensionStratum>,
}

/// Per-affine-dimension totals.
#[derive(Default, Clone)]
struct DimensionStratum {
    fibres: usize,
    points: u128,
    nonzero_points: u128,
    square_sum: BigUint,
    zero_free_fibres: usize,
    signed_total: i128,
    max_nonzero_points: usize,
    deficit_histogram: std::collections::BTreeMap<usize, usize>,
}

#[allow(clippy::too_many_lines)]
fn census(ell: usize, degree: usize, interval: usize, light: bool) -> Result<RowTotals, String> {
    if degree >= 30 {
        return Err("degree bound exceeded".to_owned());
    }
    let smallest = smallest_factor_sieve(degree);
    let input_count = 1_usize << (degree - 1);
    let coset_size = 1_usize << interval;
    let shift_count = 1_usize << interval;
    let mut moebius_values = vec![0_i8; input_count];
    let mut inverses = vec![0_u64; input_count];
    let residue_mask = (1_u64 << (ell + 1)) - 1;
    for middle in 0..input_count {
        let polynomial = (1_u64 << degree) | ((middle as u64) << 1) | 1;
        moebius_values[middle] = moebius(polynomial, &smallest);
        inverses[middle] = principal_unit_inverse(polynomial & residue_mask, ell);
    }
    let bucket_bits = (degree - 1 - interval) + (interval + 1);
    let bucket_count = 1_usize << bucket_bits;
    let mut head = vec![-1_i32; bucket_count];
    let mut next = vec![-1_i32; input_count];
    let mut touched: Vec<usize> = Vec::new();
    let mut totals = RowTotals {
        fibre_count: 0,
        points: 0,
        nonzero_points: 0,
        square_sum: BigUint::from(0_u8),
        absolute_sum: 0,
        signed_total: 0,
        nonzero_fibres: 0,
        power_of_two_fibres: 0,
        magnitude_histogram: Vec::new(),
        zero_free_fibres: 0,
        zero_free_points: 0,
        zero_free_quadratic: 0,
        zero_free_nonquadratic: 0,
        gauss_matches: 0,
        arf_matches: 0,
        support_affine_fibres: 0,
        dimension_histogram: vec![0; degree + 2],
        rank_histogram: vec![0; degree + 2],
        pow2_not_zero_free: 0,
        pow2_zero_free_nonquadratic: 0,
        square_forced_violations: 0,
        square_divisible_total: 0,
        large_pow2: 0,
        large_nonzero: 0,
        witness: None,
        tame_defect_mass: BigUint::from(0_u8),
        nontame_point_mass: BigUint::from(0_u8),
        stratum: vec![DimensionStratum::default(); degree + 2],
    };
    let mut histogram = std::collections::BTreeMap::<u64, usize>::new();
    let mut members: Vec<usize> = Vec::new();
    for shift in 1..shift_count {
        touched.clear();
        for middle in 0..input_count {
            let difference = inverses[middle] ^ inverses[middle ^ shift];
            if difference >> (interval + 1) != 0 {
                continue;
            }
            let key = ((middle / coset_size) << (interval + 1)) | (difference as usize);
            if head[key] == -1 {
                touched.push(key);
            }
            next[middle] = head[key];
            head[key] = middle as i32;
        }
        for &key in &touched {
            members.clear();
            let mut cursor = head[key];
            while cursor != -1 {
                members.push(cursor as usize);
                cursor = next[cursor as usize];
            }
            head[key] = -1;
            members.sort_unstable();
            let class = classify_fibre(&members, shift, &moebius_values, degree, light)?;
            accumulate(
                &mut totals,
                &mut histogram,
                &class,
                ell,
                degree,
                interval,
                shift,
                &members,
            );
        }
    }
    totals.magnitude_histogram = histogram.into_iter().collect();
    Ok(totals)
}

/// Members of the fibre divisible by `(x+1)^2`.  Over `F_2` this is the pair
/// of linear conditions `f(1) = 0` and `f'(1) = 0`, i.e. an even number of
/// nonzero coefficients and an even number of odd-index nonzero coefficients.
fn square_divisible_count(members: &[usize], degree: usize) -> usize {
    let odd_mask: u64 = (0..=degree)
        .filter(|index| !index.is_multiple_of(2))
        .fold(0_u64, |mask, index| mask | (1_u64 << index));
    members
        .iter()
        .filter(|&&member| {
            let polynomial = (1_u64 << degree) | ((member as u64) << 1) | 1;
            polynomial.count_ones().is_multiple_of(2)
                && (polynomial & odd_mask).count_ones().is_multiple_of(2)
        })
        .count()
}

fn classify_fibre(
    members: &[usize],
    shift: usize,
    moebius_values: &[i8],
    degree: usize,
    light: bool,
) -> Result<FibreClass, String> {
    let origin = members[0];
    let differences = members
        .iter()
        .map(|&m| (m ^ origin) as u64)
        .collect::<Vec<_>>();
    let basis = echelon_basis(&differences);
    let dimension = basis.len();
    if members.len() != 1 << dimension {
        return Err("fibre is not an affine subspace".to_owned());
    }
    let mut table = vec![0_i8; members.len()];
    let mut correlation = 0_i64;
    let mut nonzero_points = 0_usize;
    for &member in members {
        let coordinate = coordinate_of((member ^ origin) as u64, &basis)
            .ok_or_else(|| "fibre member outside its own span".to_owned())?;
        let value = i64::from(moebius_values[member]) * i64::from(moebius_values[member ^ shift]);
        table[coordinate] = value as i8;
        correlation += value;
        if value != 0 {
            nonzero_points += 1;
        }
    }
    let mut class = FibreClass {
        dimension,
        population: members.len(),
        nonzero_points,
        correlation,
        zero_free: nonzero_points == members.len(),
        square_divisible_members: square_divisible_count(members, degree),
        ..FibreClass::default()
    };
    if light {
        return Ok(class);
    }
    // Support affinity: is the nonzero locus an affine subspace?
    let support = table
        .iter()
        .enumerate()
        .filter(|&(_, &value)| value != 0)
        .map(|(index, _)| index as u64)
        .collect::<Vec<_>>();
    if !support.is_empty() {
        let support_origin = support[0];
        let shifted = support
            .iter()
            .map(|&s| s ^ support_origin)
            .collect::<Vec<_>>();
        let support_basis = echelon_basis(&shifted);
        class.support_is_affine = support.len() == 1 << support_basis.len();
    }
    if class.zero_free {
        let bits = table
            .iter()
            .map(|&value| u8::from(value < 0))
            .collect::<Vec<_>>();
        class.anf_degree = anf_degree(&bits, dimension);
        class.quadratic = class.anf_degree <= 2;
        if class.quadratic {
            let base = bits[0];
            let normalized = bits.iter().map(|&b| b ^ base).collect::<Vec<_>>();
            let (rank, tame, arf) = rank_and_arf(&normalized, dimension);
            class.rank = rank;
            let magnitude = if tame {
                1_i64 << (dimension - rank / 2)
            } else {
                0
            };
            let sign = if (arf ^ base) & 1 == 0 { 1_i64 } else { -1 };
            class.gauss_magnitude_matches = class.correlation.abs() == magnitude;
            class.arf_sign_matches = class.correlation == sign * magnitude;
        }
    }
    Ok(class)
}

#[allow(clippy::too_many_arguments)]
fn accumulate(
    totals: &mut RowTotals,
    histogram: &mut std::collections::BTreeMap<u64, usize>,
    class: &FibreClass,
    ell: usize,
    degree: usize,
    interval: usize,
    shift: usize,
    members: &[usize],
) {
    totals.fibre_count += 1;
    totals.square_divisible_total += class.square_divisible_members as u128;
    // Lemma D3: a fibre of dimension at least four (equivalently, a shift of
    // valuation at least two) must contain exactly `2^(n-2)` members divisible
    // by `(x+1)^2`, hence at least that many Moebius zeros.
    if class.dimension >= 4 && class.square_divisible_members != 1 << (class.dimension - 2) {
        totals.square_forced_violations += 1;
    }
    totals.points += class.population as u128;
    totals.nonzero_points += class.nonzero_points as u128;
    totals.signed_total += i128::from(class.correlation);
    totals.absolute_sum += u128::from(class.correlation.unsigned_abs());
    totals.square_sum += BigUint::from(class.correlation.unsigned_abs()).pow(2);
    if class.dimension < totals.dimension_histogram.len() {
        totals.dimension_histogram[class.dimension] += 1;
        let stratum = &mut totals.stratum[class.dimension];
        stratum.fibres += 1;
        stratum.points += class.population as u128;
        stratum.nonzero_points += class.nonzero_points as u128;
        stratum.square_sum += BigUint::from(class.correlation.unsigned_abs()).pow(2);
        stratum.signed_total += i128::from(class.correlation);
        if class.zero_free {
            stratum.zero_free_fibres += 1;
        }
        stratum.max_nonzero_points = stratum.max_nonzero_points.max(class.nonzero_points);
        if class.dimension <= 6 {
            *stratum
                .deficit_histogram
                .entry(class.population - class.nonzero_points)
                .or_default() += 1;
        }
    }
    let magnitude = class.correlation.unsigned_abs();
    if magnitude != 0 {
        totals.nonzero_fibres += 1;
        *histogram.entry(magnitude).or_default() += 1;
        let is_power_of_two = magnitude.is_power_of_two();
        if is_power_of_two {
            totals.power_of_two_fibres += 1;
        }
        if magnitude >= 6 {
            totals.large_nonzero += 1;
            if is_power_of_two {
                totals.large_pow2 += 1;
            }
        }
        if is_power_of_two {
            if !class.zero_free {
                totals.pow2_not_zero_free += 1;
                if totals.witness.is_none() && magnitude >= 4 {
                    totals.witness = Some(format!(
                        "ell={ell},k={degree},d={interval},shift={shift},origin={origin},\
dim={dim},points={points},nonzero_points={nz},c_F={c}",
                        origin = members[0],
                        dim = class.dimension,
                        points = class.population,
                        nz = class.nonzero_points,
                        c = class.correlation,
                    ));
                }
            } else if !class.quadratic {
                totals.pow2_zero_free_nonquadratic += 1;
            }
        }
    }
    if class.support_is_affine {
        totals.support_affine_fibres += 1;
    }
    if class.zero_free {
        totals.zero_free_fibres += 1;
        totals.zero_free_points += class.population as u128;
        if class.quadratic {
            totals.zero_free_quadratic += 1;
            if class.rank < totals.rank_histogram.len() {
                totals.rank_histogram[class.rank] += 1;
            }
            if class.gauss_magnitude_matches {
                totals.gauss_matches += 1;
            }
            if class.arf_sign_matches {
                totals.arf_matches += 1;
            }
            // The rank-count form of (E2') on the stratum where it is defined.
            if class.correlation != 0 {
                let defect = (BigUint::from(1_u8) << class.dimension)
                    * ((BigUint::from(1_u8) << (class.dimension - class.rank))
                        - BigUint::from(1_u8));
                totals.tame_defect_mass += defect;
            } else {
                totals.nontame_point_mass += BigUint::from(1_u8) << class.dimension;
            }
        } else {
            totals.zero_free_nonquadratic += 1;
        }
    }
}

fn run() -> Result<(), String> {
    let arguments = std::env::args().skip(1).collect::<Vec<_>>();
    let light = arguments.iter().any(|value| value == "--light");
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
    if first < 2 || last < first {
        return Err("usage: acb_gr_fibre_census <ell_min> [ell_max] [--light]".to_owned());
    }
    let limits = HayesLimits {
        max_ell: 24,
        max_degree: 50,
        max_group_order: 1 << 24,
        max_table_cells: 1_600_000_000,
    };
    for ell in first..=last {
        for degree in [ell + 2, ell + 3] {
            let interval = ell - 1;
            let totals = census(ell, degree, interval, light)?;
            // Cross-check against the in-tree report, which shares no code with
            // the enumeration above.
            let report = binary_dyadic_autocorrelation_fibre_report(ell, degree, interval, limits)
                .map_err(|error| error.to_string())?;
            let mut mismatches = Vec::new();
            if report.fibre_count != totals.fibre_count {
                mismatches.push("fibre_count");
            }
            if report.total_fibre_points != totals.points {
                mismatches.push("points");
            }
            if report.fibre_correlation_square_sum != totals.square_sum {
                mismatches.push("square_sum");
            }
            if report.off_diagonal_signed_correlation != totals.signed_total {
                mismatches.push("delta");
            }
            if report.fibrewise_absolute_correlation != totals.absolute_sum {
                mismatches.push("absolute_sum");
            }
            if report.nonzero_fibre_correlation_count != totals.nonzero_fibres {
                mismatches.push("nonzero_fibres");
            }
            if report.power_of_two_magnitude_fibre_count != totals.power_of_two_fibres {
                mismatches.push("power_of_two_fibres");
            }
            if !mismatches.is_empty() {
                return Err(format!(
                    "independent census disagrees with the in-tree report on {mismatches:?} at \
(ell,k,d)=({ell},{degree},{interval})"
                ));
            }
            let doubled_nonzero = 2 * totals.nonzero_points;
            let true_off_diagonal = num_bigint::BigInt::from(totals.square_sum.clone())
                - num_bigint::BigInt::from(doubled_nonzero);
            let histogram = totals
                .magnitude_histogram
                .iter()
                .map(|(magnitude, count)| format!("{magnitude}:{count}"))
                .collect::<Vec<_>>()
                .join(",");
            let dimensions = totals
                .dimension_histogram
                .iter()
                .enumerate()
                .filter(|&(_, &count)| count != 0)
                .map(|(dimension, count)| format!("{dimension}:{count}"))
                .collect::<Vec<_>>()
                .join(",");
            let ranks = totals
                .rank_histogram
                .iter()
                .enumerate()
                .filter(|&(_, &count)| count != 0)
                .map(|(rank, count)| format!("{rank}:{count}"))
                .collect::<Vec<_>>()
                .join(",");
            #[allow(clippy::cast_precision_loss)]
            let points_f = totals.points as f64;
            let square_sum_f: f64 = totals
                .square_sum
                .to_string()
                .parse()
                .map_err(|_| "square sum does not parse".to_owned())?;
            #[allow(clippy::cast_precision_loss)]
            let nonzero_f = totals.nonzero_points as f64;
            println!(
                "ACB_GR_CENSUS|status=PASS|ell={ell}|k={degree}|d={interval}|\
fibres={fibres}|points={points}|nonzero_points={nonzero}|\
sq_sum={sq}|delta={delta}|abs={abs}|\
nonzero_fibres={nzf}|pow2_fibres={pow2}|\
pow2_not_zero_free={pnz}|pow2_zero_free_nonquadratic={pzn}|\
square_divisible_total={sdt}|square_forced_violations={sfv}|\
large_nonzero={ln}|large_pow2={lp}|\
zero_free_fibres={zf}|zero_free_points={zfp}|\
zero_free_quadratic={zfq}|zero_free_nonquadratic={zfn}|\
gauss_magnitude_matches={gm}|arf_sign_matches={am}|\
support_affine_fibres={saf}|\
tame_defect_mass={tdm}|nontame_point_mass={npm}|\
doubled_nonzero={dn}|true_off_diagonal={tod}|\
nonzero_fraction={nf:.6}|doubled_nonzero_over_points={dnp:.6}|\
sq_over_points={sop:.6}|dims={dims}|ranks={ranks}|hist={hist}",
                fibres = totals.fibre_count,
                points = totals.points,
                nonzero = totals.nonzero_points,
                sq = totals.square_sum,
                delta = totals.signed_total,
                abs = totals.absolute_sum,
                nzf = totals.nonzero_fibres,
                pow2 = totals.power_of_two_fibres,
                pnz = totals.pow2_not_zero_free,
                pzn = totals.pow2_zero_free_nonquadratic,
                sdt = totals.square_divisible_total,
                sfv = totals.square_forced_violations,
                ln = totals.large_nonzero,
                lp = totals.large_pow2,
                zf = totals.zero_free_fibres,
                zfp = totals.zero_free_points,
                zfq = totals.zero_free_quadratic,
                zfn = totals.zero_free_nonquadratic,
                gm = totals.gauss_matches,
                am = totals.arf_matches,
                saf = totals.support_affine_fibres,
                tdm = totals.tame_defect_mass,
                npm = totals.nontame_point_mass,
                dn = doubled_nonzero,
                tod = true_off_diagonal,
                nf = nonzero_f / points_f,
                dnp = 2.0 * nonzero_f / points_f,
                sop = square_sum_f / points_f,
                dims = dimensions,
                ranks = ranks,
                hist = histogram,
            );
            for (dimension, stratum) in totals.stratum.iter().enumerate() {
                if stratum.fibres == 0 {
                    continue;
                }
                println!(
                    "ACB_GR_CENSUS|stratum|ell={ell}|k={degree}|d={interval}|dim={dimension}|\
fibres={fibres}|points={points}|nonzero_points={nonzero}|sq_sum={sq}|\
zero_free_fibres={zf}|signed={signed}|max_nonzero={mx}|deficits={deficits}",
                    fibres = stratum.fibres,
                    points = stratum.points,
                    nonzero = stratum.nonzero_points,
                    sq = stratum.square_sum,
                    zf = stratum.zero_free_fibres,
                    signed = stratum.signed_total,
                    mx = stratum.max_nonzero_points,
                    deficits = stratum
                        .deficit_histogram
                        .iter()
                        .map(|(deficit, count)| format!("{deficit}:{count}"))
                        .collect::<Vec<_>>()
                        .join(","),
                );
            }
            if let Some(witness) = &totals.witness {
                println!("ACB_GR_CENSUS|witness|{witness}");
            }
        }
    }
    Ok(())
}
