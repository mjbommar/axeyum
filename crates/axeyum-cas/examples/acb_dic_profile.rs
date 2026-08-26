//! AC-Bridge workstream C (dichotomy / delocalization): the exact conductor
//! filtration localization profile of the endpoint discrepancy.
//!
//! Notation follows `docs/research/10-cas/ac-bridge-2026-08/00-charter.md`.
//! With `D_e = N_n(e) - mu` on `G_ell` and `f_e = D_e^2`, let `B_j(b)` be the
//! level-`j` conductor cylinder (a coset of `H_j = ker(G_ell -> E_j)`, of size
//! `2^(ell-j)`) and
//!
//! ```text
//! m_j(b) = sum_(e in B_j(b)) D_e^2         (D^2 mass of the cylinder)
//! s_j(b) = sum_(e in B_j(b)) D_e           (signed cylinder discrepancy)
//! C_j    = 2^j sum_b m_j(b)^2              (cumulative conductor energy)
//! A_j    = sum_b s_j(b)^2                  (pushforward L2 mass of D)
//! ```
//!
//! Then `C_0 = M_2^2`, `C_ell = 2^ell M_4`, `A_0 = 0`, `A_ell = M_2`, and this
//! example emits, exactly:
//!
//! ```text
//! q_j    = (C_j - C_(j-1)) / C_(j-1)       weighted mean-square Haar imbalance
//! PR_j   = 2^j C_0 / C_j                   Renyi-2 cylinder participation ratio
//! dom_j  = 2^j max_b m_j(b) / M_2          max-to-average cylinder mass
//! a_j    = A_j / (2^(ell-j) M_2)           fraction of D's L2 mass at codim <= j
//! ```
//!
//! `q_j` is the exact per-level object of the delocalization dichotomy: the
//! identity `R_0 = prod_(j=1..ell) (1 + q_j)` holds with `0 <= q_j <= 1`, so a
//! failure of the weak target forces `q_j ~ 1` at all but `O(log ell)` levels.
//!
//! It also emits the machine-checked spike witness: whether the proved
//! low-conductor Weil cylinder bound
//! `|s_j(b)| <= 2^(-j) ((j-2) 2^j + 2) 2^(n/2)` excludes a single-class spike
//! of the critical height `mu = 2^(n-ell)` at level `j`.
//!
//! Every retained quantity is an exact integer; floats appear only in printed
//! ratios.  The conductor energies are cross-checked against the library's own
//! `fourth_moment_conductor_decomposition`.

// Printed diagnostics convert exact integers to f64 for ratios only; the
// retained quantities are exact.
#![allow(clippy::cast_precision_loss)]

use axeyum_cas::gf2_hayes::{
    ClassPopulationDistribution, HayesLimits, PrincipalUnitFactor, class_population_distribution,
    principal_unit_structure,
};
use num_bigint::{BigInt, BigUint};
use num_traits::ToPrimitive;

fn main() {
    if let Err(error) = run() {
        eprintln!("ACB_DIC_PROFILE|status=FAIL|error={error}");
        std::process::exit(1);
    }
}

/// Independent mixed-radix projection onto the level-`level` quotient `E_level`.
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

fn log2_f64(value: &BigUint) -> f64 {
    if *value == BigUint::from(0_u8) {
        return f64::NEG_INFINITY;
    }
    let bits = value.bits();
    if bits <= 900 {
        value.to_f64().map_or(f64::NAN, f64::log2)
    } else {
        let shift = bits - 800;
        let head = value >> shift;
        head.to_f64().map_or(f64::NAN, |head| {
            head.log2() + shift.to_f64().unwrap_or(f64::NAN)
        })
    }
}

fn ratio(numerator: &BigUint, denominator: &BigUint) -> f64 {
    (log2_f64(numerator) - log2_f64(denominator)).exp2()
}

/// `Sigma(ell) = sum_(j=2)^ell 2^(j-1) (j-1)^2`.
fn sigma(ell: usize) -> BigUint {
    (2..=ell).fold(BigUint::from(0_u8), |total, j| {
        total + (BigUint::from(j - 1).pow(2) << (j - 1))
    })
}

/// `W_j = sum_(i=2)^j (i-1) 2^i = 2((j-2)2^j + 2)`, the proved level sum used by
/// `low_conductor_weil_split`, kept as an exact integer.
fn weil_level_sum(j: usize) -> BigUint {
    (2..=j).fold(BigUint::from(0_u8), |total, i| {
        total + (BigUint::from(i - 1) << (i - 1))
    })
}

#[allow(clippy::too_many_lines)]
fn emit_row(ell: usize, degree: usize, limits: HayesLimits) -> Result<(), String> {
    let distribution: ClassPopulationDistribution =
        class_population_distribution(ell, degree, limits).map_err(|error| error.to_string())?;
    let classes = distribution.counts.len();
    if classes != 1_usize << ell {
        return Err(format!("class count {classes} is not 2^{ell}"));
    }
    let mean = u128::from(1_u8) << (degree - ell);
    let structure = principal_unit_structure(ell, limits).map_err(|error| error.to_string())?;
    let full = structure.factors.clone();
    if factors_of(ell) != full {
        return Err("independent factor list disagrees with the library".to_owned());
    }

    let signed = distribution
        .counts
        .iter()
        .map(|count| BigInt::from(*count) - BigInt::from(mean))
        .collect::<Vec<_>>();
    let squared = signed
        .iter()
        .map(|value| value.magnitude().pow(2))
        .collect::<Vec<_>>();
    let m2 = squared.iter().sum::<BigUint>();
    let m4 = squared.iter().map(|value| value.pow(2)).sum::<BigUint>();
    if signed.iter().sum::<BigInt>() != BigInt::from(0_u8) {
        return Err("class discrepancies are not mean zero".to_owned());
    }

    // Library cross-check of the conductor energies.
    let library = distribution
        .fourth_moment_conductor_decomposition(limits.max_table_cells)
        .map_err(|error| error.to_string())?;
    if library.second_moment != m2 || library.fourth_moment != m4 {
        return Err("library conductor decomposition disagrees on the moments".to_owned());
    }

    let mut previous_energy = m2.pow(2);
    let root_energy = previous_energy.clone();
    let mut level_rows = Vec::with_capacity(ell + 1);
    let mut imbalance_sum = 0.0_f64;
    let mut log2_growth = 0.0_f64;
    for level in 0..=ell {
        let quotient = factors_of(level);
        let cylinders = 1_usize << level;
        let mut masses = vec![BigUint::from(0_u8); cylinders];
        let mut signed_masses = vec![BigInt::from(0_u8); cylinders];
        for (index, value) in squared.iter().enumerate() {
            let cylinder = if level == 0 {
                0
            } else {
                project(index, &full, &quotient)
            };
            masses[cylinder] += value;
            signed_masses[cylinder] += &signed[index];
        }
        if masses.iter().sum::<BigUint>() != m2 {
            return Err(format!("cylinder masses miss M_2 at level {level}"));
        }
        let energy =
            BigUint::from(cylinders) * masses.iter().map(|mass| mass.pow(2)).sum::<BigUint>();
        let pushforward = signed_masses
            .iter()
            .map(|value| value.magnitude().pow(2))
            .sum::<BigUint>();
        let dominant = masses
            .iter()
            .max()
            .cloned()
            .unwrap_or_else(|| BigUint::from(0_u8));
        let max_signed_square = signed_masses
            .iter()
            .map(|value| value.magnitude().pow(2))
            .max()
            .unwrap_or_else(|| BigUint::from(0_u8));

        if level == 0 {
            if energy != root_energy {
                return Err("level 0 conductor energy is not M_2^2".to_owned());
            }
            if pushforward != BigUint::from(0_u8) {
                return Err("level 0 pushforward mass is nonzero".to_owned());
            }
        } else {
            if energy < previous_energy {
                return Err(format!("conductor energy decreases at level {level}"));
            }
            if energy > BigUint::from(2_u8) * &previous_energy {
                return Err(format!(
                    "conductor energy more than doubles at level {level}"
                ));
            }
            let row = &library.levels[level - 1];
            if row.level != level || row.cumulative_fourier_energy != energy {
                return Err(format!(
                    "library cumulative conductor energy disagrees at level {level}"
                ));
            }
            if row.exact_fourier_energy != &energy - &previous_energy {
                return Err(format!(
                    "library exact conductor energy disagrees at level {level}"
                ));
            }
        }
        if level == ell {
            if energy != BigUint::from(classes) * &m4 {
                return Err("full conductor energy is not 2^ell M_4".to_owned());
            }
            if pushforward != m2 {
                return Err("full pushforward mass is not M_2".to_owned());
            }
        }

        // The proved Weil cylinder allowance, compared by exact squares:
        //   |s_j(b)| <= 2^(-j) W_j 2^(n/2)   <=>   s^2 2^(2j) <= W_j^2 2^n.
        let weil = weil_level_sum(level);
        let weil_square = weil.pow(2) << degree;
        let observed_square = &max_signed_square << (2 * level);
        let weil_bound_holds = level == 0 || observed_square <= weil_square;
        // Would that same bound exclude a single-class spike of height mu?
        let spike_square = BigUint::from(mean).pow(2) << (2 * level);
        let spike_excluded = level > 0 && spike_square > weil_square;

        let imbalance = if level == 0 {
            0.0
        } else {
            ratio(&(&energy - &previous_energy), &previous_energy)
        };
        if level > 0 {
            imbalance_sum += imbalance;
            log2_growth += (1.0 + imbalance).log2();
        }
        let participation = ratio(&(BigUint::from(cylinders) * &root_energy), &energy);
        let dominance = ratio(&(BigUint::from(cylinders) * &dominant), &m2);
        // ||E[D | F_j]||_2^2 / ||D||_2^2 = A_j / (2^(ell-j) M_2): the exact
        // fraction of D's L2 mass measurable at codimension <= j.  A_j itself
        // is NOT a fraction of M_2 and is not monotone in j.
        let codim_share = ratio(&pushforward, &(&m2 << (ell - level)));

        level_rows.push(format!(
            "ACB_DIC_LEVEL|ell={ell}|degree={degree}|j={level}|cylinders={cylinders}|\
q_j={imbalance:.9}|PR_j={participation:.6}|PR_j_over_cylinders={pr_frac:.9}|\
dominance_j={dominance:.6}|l2_fraction_j={codim_share:.12}|\
max_cylinder_mass={dominant}|C_j={energy}|A_j={pushforward}|\
weil_cylinder_bound_holds={weil_bound_holds}|critical_spike_excluded={spike_excluded}",
            pr_frac = participation / (cylinders as f64),
        ));
        previous_energy = energy;
    }

    // Sufficiency arithmetic: the failure hypothesis forces the multiplicative
    // conductor growth to reach `G = 2^ell (mu - P_n)^4 / (mu Sigma)^2`.
    let mean_big = BigUint::from(mean);
    let proper = if degree == 2 * ell + 1 {
        BigUint::from(1_u8)
    } else {
        // Lemma B (diary 04): (ell+1) 2^ceil(ell/2) + n 2^ceil((ell+1)/2).
        (BigUint::from(ell + 1) << ell.div_ceil(2))
            + (BigUint::from(degree) << (ell + 1).div_ceil(2))
    };
    let sigma_ell = sigma(ell);
    let envelope = &mean_big * &sigma_ell;
    let weil_envelope_holds = m2 <= envelope;
    let (failure_growth_log2, failure_growth_defined) = if mean_big > proper {
        let numerator = (&mean_big - &proper).pow(4) << ell;
        let denominator = envelope.pow(2);
        (log2_f64(&numerator) - log2_f64(&denominator), true)
    } else {
        (f64::NAN, false)
    };
    let root_ratio = ratio(&(BigUint::from(classes) * &m4), &m2.pow(2));
    let deficit_budget = if failure_growth_defined {
        (ell as f64) - failure_growth_log2
    } else {
        f64::NAN
    };

    println!(
        "ACB_DIC_PROFILE|status=PASS|ell={ell}|degree={degree}|parity={parity}|\
M_2={m2}|M_4={m4}|R_0={root_ratio:.9}|log2_R_0={log2_r0:.6}|\
sum_q_j={imbalance_sum:.6}|log2_prod_one_plus_q={log2_growth:.6}|mean_q_j={mean_q:.9}|\
weil_envelope_holds={weil_envelope_holds}|\
failure_growth_log2={failure_growth_log2:.6}|failure_defined={failure_growth_defined}|\
failure_deficit_budget={deficit_budget:.6}|\
weil_cutoff={cutoff}|top_window={window}",
        parity = if degree.is_multiple_of(2) {
            "even"
        } else {
            "odd"
        },
        log2_r0 = root_ratio.log2(),
        mean_q = imbalance_sum / (ell as f64),
        cutoff = weil_cutoff(ell).0,
        window = weil_cutoff(ell).1,
    );
    for row in level_rows {
        println!("{row}");
    }
    Ok(())
}

/// The in-tree low-conductor split: cutoff level and unresolved top width.
fn weil_cutoff(ell: usize) -> (usize, usize) {
    if ell < 2 {
        return (0, ell);
    }
    let ceil_log_two = usize::BITS as usize - (ell - 1).leading_zeros() as usize;
    let window = (ceil_log_two + 2).min(ell);
    (ell - window, window)
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
    if arguments.next().is_some() || first < 2 || last < first {
        return Err("usage: acb_dic_profile [ell_min] [ell_max]".to_owned());
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
