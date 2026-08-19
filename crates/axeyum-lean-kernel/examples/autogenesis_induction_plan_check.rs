//! Interpret catalog-only Nat induction proposals in a fresh kernel process.

#[path = "autogenesis_support/mod.rs"]
mod autogenesis_support;

use std::collections::BTreeSet;
use std::fs::OpenOptions;
use std::io::Write;
use std::path::{Path, PathBuf};
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
    evidence_output: Option<PathBuf>,
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
    let mut evidence_output = None;
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
            "--evidence-output" => {
                evidence_output = Some(PathBuf::from(take_value(&mut arguments, &flag)?));
            }
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
        evidence_output,
    };
    if parsed.budget == 0 {
        return Err("--budget must be positive".to_owned());
    }
    if parsed.evidence_output.is_some() && parsed.expected != Expected::Proved {
        return Err("--evidence-output requires --expect proved".to_owned());
    }
    Ok(parsed)
}

fn write_evidence(
    path: &Path,
    args: &Args,
    search: &autogenesis_support::InductionSearch,
    candidate: axeyum_lean_kernel::NameId,
) -> Result<(), String> {
    let declaration = search
        .kernel
        .environment()
        .get(candidate)
        .ok_or("accepted candidate is absent while writing evidence")?;
    let canonical_type = search.kernel.render_lean(declaration.ty());
    if canonical_type.contains(['\t', '\n', '\r']) || args.candidate.contains(['\t', '\n', '\r']) {
        return Err("kernel evidence fields are not TSV-safe".to_owned());
    }
    let footprint: BTreeSet<String> = search
        .kernel
        .axiom_footprint(candidate)
        .into_iter()
        .map(|name| search.kernel.display_name(name).to_string())
        .collect();
    let closure: BTreeSet<String> = search
        .kernel
        .declaration_dependency_closure(candidate)
        .into_iter()
        .map(|name| search.kernel.display_name(name).to_string())
        .collect();
    let retained: Vec<&str> = ["Nat.mul_one", "Nat.zero_add"]
        .into_iter()
        .filter(|name| closure.contains(*name))
        .collect();
    let rank = search
        .accepted_rank
        .ok_or("proved result has no accepted plan rank")?;
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|error| format!("cannot create {}: {error}", path.display()))?;
    writeln!(file, "AXEYUM_AUTOGENESIS_KERNEL_EVIDENCE_V1")
        .and_then(|()| writeln!(file, "candidate\t{}", args.candidate))
        .and_then(|()| writeln!(file, "canonical_type\t{canonical_type}"))
        .and_then(|()| writeln!(file, "bundle_sha256\t{}", args.bundle_sha256))
        .and_then(|()| writeln!(file, "catalog_sha256\t{}", args.catalog_sha256))
        .and_then(|()| writeln!(file, "attempted\t{}", search.attempted))
        .and_then(|()| writeln!(file, "budget\t{}", args.budget))
        .and_then(|()| writeln!(file, "accepted_plan_rank\t{rank}"))
        .and_then(|()| {
            writeln!(
                file,
                "axiom_footprint\t{}",
                footprint.into_iter().collect::<Vec<_>>().join(",")
            )
        })
        .and_then(|()| writeln!(file, "retained_answer_dependencies\t{}", retained.join(",")))
        .map_err(|error| format!("cannot write {}: {error}", path.display()))
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
    if let (Some(path), Some(candidate)) = (&args.evidence_output, search.candidate) {
        write_evidence(path, args, &search, candidate)?;
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
