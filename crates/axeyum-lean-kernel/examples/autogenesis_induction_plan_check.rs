//! Interpret catalog-only Nat induction proposals in a fresh kernel process.

#[path = "autogenesis_support/mod.rs"]
mod autogenesis_support;

use std::path::PathBuf;
use std::process::ExitCode;

use autogenesis_support::{parse_induction_plans, search_induction};
use axeyum_lean_kernel::{Kernel, build_nat_prelude};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Expected {
    Proved,
    NoProof,
}

impl Expected {
    fn parse(raw: &str) -> Result<Self, String> {
        match raw {
            "proved" => Ok(Self::Proved),
            "no-proof" => Ok(Self::NoProof),
            _ => Err(format!("invalid expected outcome {raw:?}")),
        }
    }
}

struct Args {
    plans: PathBuf,
    candidate: String,
    budget: usize,
    expected: Expected,
    bundle_sha256: String,
    catalog_sha256: String,
}

fn take_value(arguments: &mut impl Iterator<Item = String>, flag: &str) -> Result<String, String> {
    arguments
        .next()
        .ok_or_else(|| format!("{flag} requires a value"))
}

fn parse_args() -> Result<Args, String> {
    let mut plans = None;
    let mut candidate = None;
    let mut budget = None;
    let mut expected = None;
    let mut bundle_sha256 = None;
    let mut catalog_sha256 = None;
    let mut arguments = std::env::args().skip(1);
    while let Some(flag) = arguments.next() {
        match flag.as_str() {
            "--plans" => plans = Some(PathBuf::from(take_value(&mut arguments, &flag)?)),
            "--candidate" => candidate = Some(take_value(&mut arguments, &flag)?),
            "--budget" => {
                let raw = take_value(&mut arguments, &flag)?;
                budget = Some(
                    raw.parse::<usize>()
                        .map_err(|_| format!("invalid budget {raw:?}"))?,
                );
            }
            "--expect" => expected = Some(Expected::parse(&take_value(&mut arguments, &flag)?)?),
            "--bundle-sha256" => bundle_sha256 = Some(take_value(&mut arguments, &flag)?),
            "--catalog-sha256" => catalog_sha256 = Some(take_value(&mut arguments, &flag)?),
            _ => return Err(format!("unknown flag {flag:?}")),
        }
    }
    let parsed = Args {
        plans: plans.ok_or("--plans is required")?,
        candidate: candidate.ok_or("--candidate is required")?,
        budget: budget.ok_or("--budget is required")?,
        expected: expected.ok_or("--expect is required")?,
        bundle_sha256: bundle_sha256.ok_or("--bundle-sha256 is required")?,
        catalog_sha256: catalog_sha256.ok_or("--catalog-sha256 is required")?,
    };
    if parsed.budget == 0 {
        return Err("--budget must be positive".to_owned());
    }
    Ok(parsed)
}

fn run(args: &Args) -> Result<String, String> {
    let plans = parse_induction_plans(
        &args.plans,
        &args.bundle_sha256,
        &args.catalog_sha256,
        "pre_b",
    )?;
    let mut kernel = Kernel::new();
    let prelude = build_nat_prelude(&mut kernel).map_err(|error| format!("{error:?}"))?;
    let search = search_induction(
        kernel,
        &prelude,
        prelude.zero_add,
        &args.candidate,
        &plans,
        args.budget,
    )?;
    let observed = if search.candidate.is_some() {
        Expected::Proved
    } else {
        Expected::NoProof
    };
    if let Some(candidate) = search.candidate
        && search.kernel.environment().get(candidate).is_none()
    {
        return Err("accepted induction candidate is absent from the returned kernel".to_owned());
    }
    if observed != args.expected {
        return Err("observed outcome differs from --expect".to_owned());
    }
    let outcome = if observed == Expected::Proved {
        "proved"
    } else {
        "no-proof"
    };
    let rank = search
        .accepted_rank
        .map_or_else(|| "-".to_owned(), |rank| rank.to_string());
    Ok(format!(
        "AUTOGENESIS_INDUCTION_RESULT|phase=pre_b|attempted={}|budget={}|outcome={outcome}|plan_rank={rank}",
        search.attempted, args.budget
    ))
}

fn main() -> ExitCode {
    match parse_args().and_then(|args| run(&args)) {
        Ok(result) => {
            println!("{result}");
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("AUTOGENESIS_INDUCTION_ERROR|{error}");
            ExitCode::FAILURE
        }
    }
}
