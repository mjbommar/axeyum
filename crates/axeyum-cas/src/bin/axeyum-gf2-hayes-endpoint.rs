//! Compute one exact Hayes endpoint pair with an explicit high-memory admission.
//!
//! Unlike the small regression CLI, this program evaluates only the requested
//! level.  Level 24 retains roughly 1.2 billion modular table cells and used
//! about 10 GiB in the recorded release run, so it is never part of a default
//! gate and requests above the independently replayed boundary are rejected.

use axeyum_cas::gf2_hayes::{HayesLimits, endpoint_discrepancies};

const MAX_ELL: usize = 24;

fn main() {
    if let Err(error) = run() {
        eprintln!("GF2_HAYES_ENDPOINT_SINGLE|status=FAIL|error={error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let mut arguments = std::env::args().skip(1);
    let ell = arguments
        .next()
        .ok_or("usage: axeyum-gf2-hayes-endpoint <ell: 1..=24>")?
        .parse::<usize>()?;
    if arguments.next().is_some() || !(1..=MAX_ELL).contains(&ell) {
        return Err("usage: axeyum-gf2-hayes-endpoint <ell: 1..=24>".into());
    }

    let group_order = 1_usize
        .checked_shl(u32::try_from(ell)?)
        .ok_or("group-order overflow")?;
    let max_degree = ell
        .checked_mul(2)
        .and_then(|value| value.checked_add(2))
        .ok_or("degree overflow")?;
    let retained_rows = ell
        .checked_add(max_degree)
        .and_then(|value| value.checked_add(1))
        .ok_or("row-count overflow")?;
    let max_table_cells = retained_rows
        .checked_mul(group_order)
        .ok_or("table-cell overflow")?;
    let limits = HayesLimits {
        max_ell: ell,
        max_degree,
        max_group_order: group_order,
        max_table_cells,
    };

    let started = std::time::Instant::now();
    let result = endpoint_discrepancies(ell, limits)?;
    println!(
        "GF2_HAYES_ENDPOINT_SINGLE|status=PASS|ell={ell}|odd={}|even={}|candidate_abs_discrepancy_le_2powell={}|elapsed_seconds={:.3}",
        result.odd,
        result.even,
        result.satisfies_candidate_bound(),
        started.elapsed().as_secs_f64(),
    );
    Ok(())
}
