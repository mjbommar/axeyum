//! AC-Bridge phase-3 workstream 22 ((CDL) assault): the translation involution
//! and the characters it kills at the bottom of the conductor filtration.
//!
//! Result C4 of `13-angle-dichotomy.md` proves `fhat(chi_1) = 0` at the odd
//! endpoint from the Mangoldt-preserving bijection `F(x) -> F(x+1)`.  The same
//! bijection kills MORE than the level-1 character.  Writing `sigma` for the
//! induced map of `G_ell`,
//!
//! ```text
//! a_i(sigma e) = sum_(m=0)^i a_m binom(n-m, i-m)   (a_0 = 1),  i = 1..ell,
//! ```
//!
//! `sigma` is an involution with `D_(sigma e) = D_e`, so `fhat(chi) = 0` for
//! EVERY character with `chi(sigma e) = -chi(e)`, and those characters form a
//! coset of `{chi : chi o sigma = chi}` inside `H = {chi : chi o sigma = +-chi}`
//! -- exactly half of `H` when the sign map is onto, which `chi_1` witnesses at
//! odd `n`.
//!
//! This example builds `sigma` from the binomial formula, checks that it is an
//! involution and that it preserves the class populations (an independent
//! structural check of the Result C4 argument), enumerates the anti-invariant
//! characters of conductor level `<= cap`, and asserts `fhat(chi) = 0` EXACTLY
//! for each of them in `Z[zeta_N]`.  It emits the per-level counts, i.e. how
//! many of the `2^(j-1)` characters of level `j` are free.

#![allow(clippy::cast_precision_loss)]

use axeyum_cas::gf2_hayes::{
    ClassPopulationDistribution, HayesLimits, PrincipalUnitFactor, class_population_distribution,
    principal_unit_structure,
};
use num_bigint::{BigInt, BigUint};

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
    fn add_term(&mut self, exponent: usize, value: &BigInt) {
        let half = self.order / 2;
        let reduced = exponent % self.order;
        if reduced < half {
            self.coefficients[reduced] += value;
        } else {
            self.coefficients[reduced - half] -= value;
        }
    }
    fn is_zero_element(&self) -> bool {
        self.coefficients.iter().all(num_traits::Zero::is_zero)
    }
}

/// Product of two truncated power series `mod t^(ell+1)`, bit `i` = coefficient of `t^i`.
fn series_multiply(left: usize, right: usize, ell: usize) -> usize {
    let mut result = 0_usize;
    for i in 0..=ell {
        if (left >> i) & 1 == 0 {
            continue;
        }
        for j in 0..=(ell - i) {
            if (right >> j) & 1 == 1 {
                result ^= 1 << (i + j);
            }
        }
    }
    result
}

/// `u^(-1)` for a principal unit `u = 1 + A`, by `u^(-1) = 1 + A u^(-1)`.
fn series_inverse(unit: usize, ell: usize) -> usize {
    let tail = unit & !1_usize;
    let mut inverse = 1_usize;
    for _ in 0..=ell {
        inverse = 1 ^ series_multiply(tail, inverse, ell);
    }
    inverse
}

/// `u(t / (1+t)) mod t^(ell+1)`: the involutive automorphism `tau` of `G_ell`.
fn substitution_tau(unit: usize, ell: usize) -> usize {
    // s = t/(1+t) = t + t^2 + ... + t^ell
    let mut s = 0_usize;
    for i in 1..=ell {
        s |= 1 << i;
    }
    let mut power = 1_usize; // s^0
    let mut image = 0_usize;
    for i in 0..=ell {
        if (unit >> i) & 1 == 1 {
            image ^= power;
        }
        power = series_multiply(power, s, ell);
    }
    image
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

/// `(1 + A(t)) (1 + B(t)) mod t^(ell+1)`, masks holding `a_1..a_ell`.
fn unit_multiply(left: usize, right: usize, ell: usize) -> usize {
    let mut result = left ^ right;
    for i in 1..=ell {
        if (left >> (i - 1)) & 1 == 0 {
            continue;
        }
        for j in 1..=ell {
            if i + j > ell {
                break;
            }
            if (right >> (j - 1)) & 1 == 1 {
                result ^= 1 << (i + j - 1);
            }
        }
    }
    result
}

/// `binom(a, b) mod 2` by Lucas' theorem.
fn binomial_parity(upper: usize, lower: usize) -> bool {
    lower & !upper == 0
}

fn conductor_level(duals: &[usize], level: usize) -> usize {
    let full = factors_of(level);
    for candidate in 0..=level {
        let quotient = factors_of(candidate);
        let mut trivial = true;
        for (position, factor) in full.iter().enumerate() {
            match quotient.get(position) {
                Some(target) if target.odd_degree == factor.odd_degree => {
                    if duals[position] % (factor.order / target.order) != 0 {
                        trivial = false;
                    }
                }
                _ => {
                    if duals[position] != 0 {
                        trivial = false;
                    }
                }
            }
        }
        if trivial {
            return candidate;
        }
    }
    level
}

#[allow(clippy::too_many_lines)]
fn emit_row(ell: usize, degree: usize, cap: usize, limits: HayesLimits) -> Result<(), String> {
    let distribution: ClassPopulationDistribution =
        class_population_distribution(ell, degree, limits).map_err(|error| error.to_string())?;
    let classes = distribution.counts.len();
    let mean = u128::from(1_u8) << (degree - ell);
    let structure = principal_unit_structure(ell, limits).map_err(|error| error.to_string())?;
    let full = structure.factors.clone();
    if factors_of(ell) != full {
        return Err("independent factor list disagrees with the library".to_owned());
    }

    // index (mixed radix over the cyclic factors) <-> mask (a_1..a_ell)
    let mut mask_of_index = vec![0_usize; classes];
    let mut index_of_mask = vec![usize::MAX; classes];
    let mut coordinates = vec![0_usize; full.len()];
    for index in 0..classes {
        let mut element = 0_usize;
        for (position, factor) in full.iter().enumerate() {
            let generator = 1_usize << (factor.odd_degree - 1);
            for _ in 0..coordinates[position] {
                element = unit_multiply(element, generator, ell);
            }
        }
        if index_of_mask[element] != usize::MAX {
            return Err("coordinate map is not injective".to_owned());
        }
        mask_of_index[index] = element;
        index_of_mask[element] = index;
        for (position, factor) in full.iter().enumerate() {
            coordinates[position] += 1;
            if coordinates[position] < factor.order {
                break;
            }
            coordinates[position] = 0;
        }
    }

    // sigma on masks: a_i -> sum_(m<=i) a_m binom(n-m, i-m), a_0 = 1.
    let mut sigma = vec![0_usize; classes];
    for mask in 0..classes {
        let mut image = 0_usize;
        for i in 1..=ell {
            let mut bit = binomial_parity(degree, i); // m = 0 term, a_0 = 1
            for m in 1..=i {
                if (mask >> (m - 1)) & 1 == 1 && binomial_parity(degree - m, i - m) {
                    bit = !bit;
                }
            }
            if bit {
                image |= 1 << (i - 1);
            }
        }
        sigma[mask] = image;
    }
    for mask in 0..classes {
        if sigma[sigma[mask]] != mask {
            return Err("sigma is not an involution".to_owned());
        }
    }
    // Theorem C22-6: sigma(u) = c * tau(u) with c = (1+t)^n and tau(u)(t) =
    // u(t/(1+t)) an involutive automorphism of G_ell satisfying tau(c) = c^(-1).
    let one_plus_t = 0b11_usize;
    let mut translation = 1_usize;
    for _ in 0..degree {
        translation = series_multiply(translation, one_plus_t, ell);
    }
    let translation_inverse = series_inverse(translation, ell);
    if series_multiply(translation, translation_inverse, ell) != 1 {
        return Err("inverse of (1+t)^n is wrong".to_owned());
    }
    if substitution_tau(translation, ell) != translation_inverse {
        return Err("tau((1+t)^n) is not (1+t)^(-n)".to_owned());
    }
    let mut tau = vec![0_usize; classes];
    for mask in 0..classes {
        let unit = (mask << 1) | 1;
        let image = substitution_tau(unit, ell);
        if image & 1 != 1 {
            return Err("tau leaves the principal units".to_owned());
        }
        tau[mask] = image >> 1;
        // closed form: sigma(u) = c * tau(u)
        if series_multiply(translation, image, ell) != ((sigma[mask] << 1) | 1) {
            return Err("sigma(u) = c * tau(u) fails".to_owned());
        }
        if substitution_tau(image, ell) != unit {
            return Err("tau is not an involution".to_owned());
        }
    }
    // tau is a group automorphism: check against every generator and every element.
    for factor in &full {
        let generator = 1_usize << (factor.odd_degree - 1);
        for mask in 0..classes {
            let product = unit_multiply(generator, mask, ell);
            if tau[product] != unit_multiply(tau[generator], tau[mask], ell) {
                return Err("tau is not multiplicative".to_owned());
            }
        }
    }

    // Is the commutator group K = <tau(g) g^(-1)> equal to the squares G^2?
    // (That is the identification Fix(tau) = {chi : chi^2 = 1} in the dual.)
    let mut squares = vec![false; classes];
    let mut square_count = 0_usize;
    for mask in 0..classes {
        let value = unit_multiply(mask, mask, ell);
        if !squares[value] {
            squares[value] = true;
            square_count += 1;
        }
    }
    let mut generated = vec![false; classes];
    generated[0] = true;
    let mut frontier = vec![0_usize];
    let mut seeds = Vec::new();
    for mask in 0..classes {
        let image = tau[mask];
        let inverse = series_inverse((mask << 1) | 1, ell) >> 1;
        seeds.push(unit_multiply(image, inverse, ell));
    }
    while let Some(current) = frontier.pop() {
        for seed in &seeds {
            let next = unit_multiply(current, *seed, ell);
            if !generated[next] {
                generated[next] = true;
                frontier.push(next);
            }
        }
    }
    let generated_count = generated.iter().filter(|flag| **flag).count();
    let commutator_is_squares = (0..classes).all(|mask| generated[mask] == squares[mask]);

    // The structural fact: sigma permutes classes with equal Mangoldt mass.
    for index in 0..classes {
        let image = index_of_mask[sigma[mask_of_index[index]]];
        if distribution.counts[index] != distribution.counts[image] {
            return Err("sigma does not preserve the class populations".to_owned());
        }
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

    let level_cap = cap.min(ell);
    let mut cyclotomic_order = 2_usize;
    while cyclotomic_order <= level_cap {
        cyclotomic_order *= 2;
    }

    // Enumerate characters of E_(level_cap) and test anti-invariance.
    let quotient = factors_of(level_cap);
    let mut level_free = vec![0_usize; level_cap + 1];
    let mut level_fixed = vec![0_usize; level_cap + 1];
    let mut level_total = vec![0_usize; level_cap + 1];
    let mut duals = vec![0_usize; quotient.len()];
    // exponent of chi at each class index, as a residue mod cyclotomic_order
    for _ in 0..(1_usize << level_cap) {
        let level = conductor_level(&duals, level_cap);
        if level >= 1 {
            level_total[level] += 1;
            // chi(e) for every class: reduce the E_ell coordinates into E_cap.
            let mut exponent_of_index = vec![0_usize; classes];
            let mut coordinates = vec![0_usize; full.len()];
            for index in 0..classes {
                let mut exponent = 0_usize;
                let mut cursor = 0_usize;
                for (position, factor) in full.iter().enumerate() {
                    if let Some(target) = quotient.get(cursor)
                        && target.odd_degree == factor.odd_degree
                    {
                        exponent += duals[cursor]
                            * (coordinates[position] % target.order)
                            * (cyclotomic_order / target.order);
                        cursor += 1;
                    }
                }
                exponent_of_index[index] = exponent % cyclotomic_order;
                for (position, factor) in full.iter().enumerate() {
                    coordinates[position] += 1;
                    if coordinates[position] < factor.order {
                        break;
                    }
                    coordinates[position] = 0;
                }
            }
            // anti-invariance: chi(sigma e) = -chi(e) for every e.
            let half = cyclotomic_order / 2;
            let mut anti = true;
            let mut fixed = true;
            for index in 0..classes {
                let image = index_of_mask[sigma[mask_of_index[index]]];
                let shift = (exponent_of_index[image] + cyclotomic_order
                    - exponent_of_index[index])
                    % cyclotomic_order;
                if shift != half {
                    anti = false;
                }
                let tau_image = index_of_mask[tau[mask_of_index[index]]];
                if exponent_of_index[tau_image] != exponent_of_index[index] {
                    fixed = false;
                }
                if !anti && !fixed {
                    break;
                }
            }
            // Functional equation fhat(chi) = chi(c) fhat(chi o tau), PROVED by
            // Theorem C22-6; verified here as an exact identity in Z[zeta_N].
            let mut transform_direct = Cyc::zero(cyclotomic_order);
            let mut transform_tau = Cyc::zero(cyclotomic_order);
            for index in 0..classes {
                let value = BigInt::from(squared[index].clone());
                transform_direct.add_term(exponent_of_index[index], &value);
                let image = index_of_mask[tau[mask_of_index[index]]];
                transform_tau.add_term(exponent_of_index[image], &value);
            }
            let translation_index = index_of_mask[translation >> 1];
            let translation_exponent = exponent_of_index[translation_index];
            let mut scaled = Cyc::zero(cyclotomic_order);
            for (exponent, value) in transform_tau.coefficients.iter().enumerate() {
                scaled.add_term(exponent + translation_exponent, value);
            }
            if scaled != transform_direct {
                return Err(format!(
                    "functional equation fhat(chi) = chi(c) fhat(chi o tau) fails at level {level}"
                ));
            }
            if fixed {
                level_fixed[level] += 1;
            }
            if anti {
                if !transform_direct.is_zero_element() {
                    return Err("anti-invariant character has nonzero fhat".to_owned());
                }
                level_free[level] += 1;
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

    let total_free: usize = level_free.iter().sum();
    let total_characters: usize = level_total.iter().sum();
    println!(
        "ACB_CDL_INVOLUTION|status=PASS|ell={ell}|degree={degree}|parity={parity}|M_2={m2}|\
level_cap={level_cap}|characters={total_characters}|vanishing={total_free}|\
per_level={detail}|tau_fixed={total_fixed}|tau_fixed_per_level={fixed_detail}|\
two_torsion_of_dual={two_torsion}|squares={square_count}|commutator_subgroup={generated_count}|\
commutator_is_squares={commutator_is_squares}|fixed_translation_class={translation_index}",
        parity = if degree % 2 == 0 { "even" } else { "odd" },
        translation_index = index_of_mask[translation >> 1],
        total_fixed = level_fixed.iter().sum::<usize>() + 1,
        two_torsion = 1_usize << level_cap.div_ceil(2),
        fixed_detail = (1..=level_cap)
            .map(|j| format!("j{j}:{}", level_fixed[j]))
            .collect::<Vec<_>>()
            .join(","),
        detail = (1..=level_cap)
            .map(|j| format!("j{j}:{}/{}", level_free[j], level_total[j]))
            .collect::<Vec<_>>()
            .join(","),
    );
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
        .map_err(|_| "cap must be an integer".to_owned())?;
    if arguments.next().is_some() || first < 2 || last < first {
        return Err("usage: acb_cdl_involution [ell_min] [ell_max] [level_cap]".to_owned());
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
        eprintln!("ACB_CDL_INVOLUTION|status=FAIL|error={error}");
        std::process::exit(1);
    }
}
