//! AC-Bridge workstream 04: the symbolic side of the weak endpoint target.
//!
//! Pure exact integer arithmetic (no transform).  For each `ell` it prints the
//! two proper-prime-power upper bounds
//!
//! ```text
//! P_lib(n)   = (n/2) 2^(n/2 - floor(ell/2)) + n 2^ceil(n/3)      (in-tree)
//! P_sharp(n) = (ell+1) 2^ceil(ell/2) + n 2^ceil((ell+1)/2)       (this file)
//! ```
//!
//! at the even endpoint (`P = 1` exactly at the odd endpoint), the resulting
//! strict weak thresholds `(mu - P)^4`, the sufficient root-ratio allowance
//!
//! ```text
//! R_0 < 2^ell (mu - P)^4 / (mu Sigma(ell))^2,   Sigma(ell)=sum_(j=2)^ell 2^(j-1)(j-1)^2,
//! ```
//!
//! and the two crossovers that matter: the first `ell` at which the allowance
//! exceeds the old strong target `R_0 <= 4`, and the first `ell` at which the
//! PROVED Weil envelope alone discharges the whole Wick part, i.e.
//! `3 (mu Sigma)^2 < 2^ell (mu - P)^4`, after which `K_4 <= 0` would suffice.

use num_bigint::BigUint;
use num_traits::ToPrimitive;

fn main() {
    if let Err(error) = run() {
        eprintln!("ACB_WT_SYMBOLIC|status=FAIL|error={error}");
        std::process::exit(1);
    }
}

fn sigma(ell: usize) -> BigUint {
    let mut total = BigUint::from(0_u8);
    for j in 2..=ell {
        total += BigUint::from(j - 1).pow(2) << (j - 1);
    }
    total
}

fn library_even_bound(ell: usize, degree: usize) -> BigUint {
    let half = degree / 2;
    (BigUint::from(half) << (half - ell / 2)) + (BigUint::from(degree) << degree.div_ceil(3))
}

fn sharp_even_bound(ell: usize, degree: usize) -> BigUint {
    (BigUint::from(ell + 1) << ell.div_ceil(2)) + (BigUint::from(degree) << (ell + 1).div_ceil(2))
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
        (value >> shift).to_f64().map_or(f64::NAN, |head| {
            head.log2() + shift.to_f64().unwrap_or(f64::NAN)
        })
    }
}

fn emit(ell: usize, degree: usize) {
    let mean = BigUint::from(1_u8) << (degree - ell);
    let (library, sharp) = if degree.is_multiple_of(2) {
        (
            library_even_bound(ell, degree),
            sharp_even_bound(ell, degree),
        )
    } else {
        (BigUint::from(1_u8), BigUint::from(1_u8))
    };
    let sigma_value = sigma(ell);
    let envelope = &mean * &sigma_value;
    let mut fields = Vec::new();
    for (name, bound) in [("library", &library), ("sharp", &sharp)] {
        let positive = *bound < mean;
        let threshold = if positive {
            (&mean - bound).pow(4)
        } else {
            BigUint::from(0_u8)
        };
        let allowance = (BigUint::from(1_u8) << ell) * &threshold;
        let wick = BigUint::from(3_u8) * envelope.pow(2);
        let log2_allowance = log2_f64(&allowance) - 2.0 * log2_f64(&envelope);
        fields.push(format!(
            "{name}_bound={bound}|{name}_margin_positive={positive}|\
{name}_log2_threshold={:.6}|{name}_log2_sufficient_R_0={log2_allowance:.6}|\
{name}_beats_strong_target={}|{name}_wick_discharged={}",
            log2_f64(&threshold),
            allowance > BigUint::from(4_u8) * envelope.pow(2),
            positive && wick < allowance,
        ));
    }
    println!(
        "ACB_WT_SYMBOLIC|status=PASS|ell={ell}|degree={degree}|parity={}|\
log2_mean={}|log2_sigma={:.6}|{}",
        if degree.is_multiple_of(2) {
            "even"
        } else {
            "odd"
        },
        degree - ell,
        log2_f64(&sigma_value),
        fields.join("|"),
    );
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
    let step = arguments
        .next()
        .map_or(Ok(1), |value| value.parse::<usize>())
        .map_err(|_| "step must be an integer".to_owned())?;
    if arguments.next().is_some() || first < 2 || last < first || step == 0 {
        return Err("usage: acb_wt_symbolic [ell_min] [ell_max] [step]".to_owned());
    }
    let mut ell = first;
    while ell <= last {
        for degree in [2 * ell + 1, 2 * ell + 2] {
            emit(ell, degree);
        }
        ell += step;
    }
    Ok(())
}
