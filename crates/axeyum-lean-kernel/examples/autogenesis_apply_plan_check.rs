//! Check catalog-only `apply-visible-theorem` proposals against fresh Nat goals.
//!
//! The proposer runs outside this process and never sees proof bodies. This
//! checker receives its deterministic TSV projection, rebuilds the full kernel
//! environment, and gives each proposed theorem application a real admission
//! attempt. `--expect` is mandatory: completing the search without a proof is
//! not success when the caller expected one, and finding a proof is not success
//! for the registered pre-A negative control.

#[path = "autogenesis_support/mod.rs"]
mod autogenesis_support;

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::fs::OpenOptions;
use std::io::Write;
use std::path::Path;
use std::path::PathBuf;
use std::process::ExitCode;

use autogenesis_support::{parse_induction_plans, search_induction};
use axeyum_lean_kernel::{Kernel, NameId, NatDev, NatOps, NatPrelude, build_nat_prelude};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Phase {
    PreB,
    PreA,
    PostB,
}

impl Phase {
    fn parse(raw: &str) -> Result<Self, String> {
        match raw {
            "pre_b" => Ok(Self::PreB),
            "pre_a" => Ok(Self::PreA),
            "post_b" => Ok(Self::PostB),
            _ => Err(format!("invalid phase {raw:?}")),
        }
    }

    const fn rendered(self) -> &'static str {
        match self {
            Self::PreB => "pre_b",
            Self::PreA => "pre_a",
            Self::PostB => "post_b",
        }
    }
}

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

#[derive(Debug)]
struct Args {
    plans: PathBuf,
    phase: Phase,
    candidate: String,
    premise_candidate: Option<String>,
    premise_plans: Option<PathBuf>,
    premise_budget: Option<usize>,
    premise_bundle_sha256: Option<String>,
    premise_catalog_sha256: Option<String>,
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
    let mut phase = None;
    let mut candidate = None;
    let mut premise_candidate = None;
    let mut premise_plans = None;
    let mut premise_budget = None;
    let mut premise_bundle_sha256 = None;
    let mut premise_catalog_sha256 = None;
    let mut budget = None;
    let mut expected = None;
    let mut bundle_sha256 = None;
    let mut catalog_sha256 = None;
    let mut evidence_output = None;
    let mut arguments = std::env::args().skip(1);
    while let Some(flag) = arguments.next() {
        match flag.as_str() {
            "--plans" => plans = Some(PathBuf::from(take_value(&mut arguments, &flag)?)),
            "--phase" => phase = Some(Phase::parse(&take_value(&mut arguments, &flag)?)?),
            "--candidate" => candidate = Some(take_value(&mut arguments, &flag)?),
            "--premise-candidate" => premise_candidate = Some(take_value(&mut arguments, &flag)?),
            "--premise-plans" => {
                premise_plans = Some(PathBuf::from(take_value(&mut arguments, &flag)?));
            }
            "--premise-budget" => {
                let raw = take_value(&mut arguments, &flag)?;
                premise_budget = Some(
                    raw.parse::<usize>()
                        .map_err(|_| format!("invalid premise budget {raw:?}"))?,
                );
            }
            "--premise-bundle-sha256" => {
                premise_bundle_sha256 = Some(take_value(&mut arguments, &flag)?);
            }
            "--premise-catalog-sha256" => {
                premise_catalog_sha256 = Some(take_value(&mut arguments, &flag)?);
            }
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
        phase: phase.ok_or("--phase is required")?,
        candidate: candidate.ok_or("--candidate is required")?,
        premise_candidate,
        premise_plans,
        premise_budget,
        premise_bundle_sha256,
        premise_catalog_sha256,
        budget: budget.ok_or("--budget is required")?,
        expected: expected.ok_or("--expect is required")?,
        bundle_sha256: bundle_sha256.ok_or("--bundle-sha256 is required")?,
        catalog_sha256: catalog_sha256.ok_or("--catalog-sha256 is required")?,
        evidence_output,
    };
    if parsed.budget == 0 {
        return Err("--budget must be positive".to_owned());
    }
    let premise_fields = [
        parsed.premise_candidate.is_some(),
        parsed.premise_plans.is_some(),
        parsed.premise_budget.is_some(),
        parsed.premise_bundle_sha256.is_some(),
        parsed.premise_catalog_sha256.is_some(),
    ];
    if parsed.phase == Phase::PostB && premise_fields.iter().any(|present| !present) {
        return Err("post_b requires the complete premise plan identity and budget".to_owned());
    }
    if parsed.phase != Phase::PostB && premise_fields.iter().any(|present| *present) {
        return Err("pre phases must not receive premise plan arguments".to_owned());
    }
    if parsed.premise_budget == Some(0) {
        return Err("--premise-budget must be positive".to_owned());
    }
    if parsed.evidence_output.is_some()
        && (parsed.phase != Phase::PostB || parsed.expected != Expected::Proved)
    {
        return Err("--evidence-output requires --phase post_b --expect proved".to_owned());
    }
    Ok(parsed)
}

#[derive(Debug)]
struct Plan {
    rank: usize,
    theorem: String,
    arity: usize,
}

fn parse_plans(args: &Args) -> Result<Vec<Plan>, String> {
    let text = fs::read_to_string(&args.plans)
        .map_err(|error| format!("cannot read {}: {error}", args.plans.display()))?;
    let mut lines = text.lines();
    let header = lines.next().ok_or("plan file is empty")?;
    let header_fields: Vec<&str> = header.split('\t').collect();
    if header_fields
        != [
            "AXEYUM_APPLY_PLANS_V1",
            args.bundle_sha256.as_str(),
            args.catalog_sha256.as_str(),
            args.phase.rendered(),
        ]
    {
        return Err("plan header does not match the registered bundle/catalog/phase".to_owned());
    }
    let mut plans = Vec::new();
    let mut names = BTreeSet::new();
    for (index, line) in lines.enumerate() {
        let fields: Vec<&str> = line.split('\t').collect();
        if fields.len() != 3 {
            return Err(format!(
                "plan row {} has {} fields",
                index + 1,
                fields.len()
            ));
        }
        let rank = fields[0]
            .parse::<usize>()
            .map_err(|_| format!("plan row {} has invalid rank", index + 1))?;
        if rank != index + 1 {
            return Err(format!(
                "plan rank {rank} is not the expected {}",
                index + 1
            ));
        }
        let theorem = fields[1].to_owned();
        if theorem.is_empty() || !names.insert(theorem.clone()) {
            return Err(format!(
                "plan rank {rank} has an empty or duplicate theorem"
            ));
        }
        let arity = fields[2]
            .parse::<usize>()
            .map_err(|_| format!("plan rank {rank} has invalid arity"))?;
        plans.push(Plan {
            rank,
            theorem,
            arity,
        });
    }
    if plans.is_empty() {
        return Err("plan file contains no proposals".to_owned());
    }
    Ok(plans)
}

fn intern_dotted(kernel: &mut Kernel, rendered: &str) -> Result<NameId, String> {
    if rendered.is_empty() || rendered.split('.').any(str::is_empty) {
        return Err(format!("invalid dotted declaration name {rendered:?}"));
    }
    let mut name = kernel.anon();
    for component in rendered.split('.') {
        name = kernel.name_str(name, component);
    }
    Ok(name)
}

fn names(kernel: &Kernel) -> BTreeMap<String, NameId> {
    kernel
        .environment()
        .iter()
        .map(|(name, _)| (kernel.display_name(*name).to_string(), *name))
        .collect()
}

fn try_plan(
    kernel: &mut Kernel,
    prelude: &NatPrelude,
    phase: Phase,
    candidate: NameId,
    theorem: NameId,
) -> Result<(), String> {
    let mut development = NatDev::new(kernel, *prelude);
    development
        .theorem(candidate, 1, &|d, variables| {
            let value = variables[0];
            let statement = match phase {
                Phase::PreB => {
                    let zero = d.zero();
                    let sum = d.add(zero, value);
                    d.eq(sum, value)
                }
                Phase::PreA | Phase::PostB => {
                    let one = d.num(1);
                    let product = d.mul(value, one);
                    d.eq(product, value)
                }
            };
            let proof = d.lemma(theorem, &[value]);
            (statement, proof)
        })
        .map(|_| ())
        .map_err(|error| development.explain(&error))
}

struct SearchBase {
    kernel: Kernel,
    prelude: NatPrelude,
    premise: Option<NameId>,
    premise_attempted: usize,
    premise_plan_rank: Option<usize>,
    target: NameId,
    denied: BTreeSet<String>,
}

fn build_base(args: &Args) -> Result<SearchBase, String> {
    let mut kernel = Kernel::new();
    let prelude = build_nat_prelude(&mut kernel).map_err(|error| format!("{error:?}"))?;
    let target = match args.phase {
        Phase::PreB => prelude.zero_add,
        Phase::PreA | Phase::PostB => prelude.mul_one,
    };
    let (kernel, premise, premise_attempted, premise_plan_rank) =
        if let Some(rendered) = &args.premise_candidate {
            let plans = parse_induction_plans(
                args.premise_plans
                    .as_deref()
                    .ok_or("post_b premise plan path disappeared")?,
                args.premise_bundle_sha256
                    .as_deref()
                    .ok_or("post_b premise bundle identity disappeared")?,
                args.premise_catalog_sha256
                    .as_deref()
                    .ok_or("post_b premise catalog identity disappeared")?,
                "pre_b",
            )?;
            let search = search_induction(
                kernel,
                &prelude,
                prelude.zero_add,
                rendered,
                &plans,
                args.premise_budget
                    .ok_or("post_b premise budget disappeared")?,
            )?;
            let candidate = search
                .candidate
                .ok_or("premise induction search completed without a creditable proof")?;
            (
                search.kernel,
                Some(candidate),
                search.attempted,
                search.accepted_rank,
            )
        } else {
            (kernel, None, 0, None)
        };
    Ok(SearchBase {
        kernel,
        prelude,
        premise,
        premise_attempted,
        premise_plan_rank,
        target,
        denied: BTreeSet::from(["Nat.mul_one".to_owned(), "Nat.zero_add".to_owned()]),
    })
}

fn candidate_is_creditable(
    kernel: &mut Kernel,
    candidate: NameId,
    base: &SearchBase,
) -> Result<bool, String> {
    let closure: BTreeSet<String> = kernel
        .declaration_dependency_closure(candidate)
        .into_iter()
        .map(|name| kernel.display_name(name).to_string())
        .collect();
    if !base.denied.is_disjoint(&closure) || !kernel.axiom_footprint(candidate).is_empty() {
        return Ok(false);
    }
    if let Some(premise) = base.premise
        && !closure.contains(&kernel.display_name(premise).to_string())
    {
        return Ok(false);
    }
    let candidate_type = kernel
        .environment()
        .get(candidate)
        .ok_or("candidate disappeared after admission")?
        .ty();
    let target_type = kernel
        .environment()
        .get(base.target)
        .ok_or("target disappeared during admission")?
        .ty();
    Ok(kernel.def_eq(candidate_type, target_type)
        && kernel.render_lean(candidate_type) == kernel.render_lean(target_type))
}

struct ApplySearch {
    kernel: Kernel,
    candidate: Option<NameId>,
    premise: Option<NameId>,
    premise_attempted: usize,
    premise_plan_rank: Option<usize>,
    attempted: usize,
    accepted_plan_rank: Option<usize>,
    theorem: Option<String>,
}

fn search(args: &Args, plans: &[Plan]) -> Result<ApplySearch, String> {
    let base = build_base(args)?;
    let limited = plans.iter().take(args.budget);
    let mut attempted = 0;
    for plan in limited {
        attempted += 1;
        if plan.arity != 1 {
            continue;
        }
        let mut trial = base.kernel.clone();
        let available = names(&trial);
        let Some(&theorem) = available.get(&plan.theorem) else {
            return Err(format!(
                "plan rank {} names unavailable theorem {:?}",
                plan.rank, plan.theorem
            ));
        };
        let trial_name = intern_dotted(
            &mut trial,
            &format!("{}.trial{}", args.candidate, plan.rank),
        )?;
        if try_plan(&mut trial, &base.prelude, args.phase, trial_name, theorem).is_err()
            || !candidate_is_creditable(&mut trial, trial_name, &base)?
        {
            continue;
        }

        let mut accepted = base.kernel.clone();
        let theorem = names(&accepted)
            .get(&plan.theorem)
            .copied()
            .ok_or_else(|| format!("accepted theorem {:?} disappeared", plan.theorem))?;
        let candidate = intern_dotted(&mut accepted, &args.candidate)?;
        try_plan(&mut accepted, &base.prelude, args.phase, candidate, theorem)?;
        if !candidate_is_creditable(&mut accepted, candidate, &base)? {
            return Err("trial passed but exact candidate failed the same audit".to_owned());
        }
        return Ok(ApplySearch {
            kernel: accepted,
            candidate: Some(candidate),
            premise: base.premise,
            premise_attempted: base.premise_attempted,
            premise_plan_rank: base.premise_plan_rank,
            attempted,
            accepted_plan_rank: Some(plan.rank),
            theorem: Some(plan.theorem.clone()),
        });
    }
    Ok(ApplySearch {
        kernel: base.kernel,
        candidate: None,
        premise: base.premise,
        premise_attempted: base.premise_attempted,
        premise_plan_rank: base.premise_plan_rank,
        attempted,
        accepted_plan_rank: None,
        theorem: None,
    })
}

fn write_evidence(path: &Path, args: &Args, search: &ApplySearch) -> Result<(), String> {
    let candidate = search
        .candidate
        .ok_or("proved apply result has no candidate")?;
    let premise = search
        .premise
        .ok_or("proved post-B result has no premise")?;
    let declaration = search
        .kernel
        .environment()
        .get(candidate)
        .ok_or("accepted apply candidate is absent while writing evidence")?;
    let canonical_type = search.kernel.render_lean(declaration.ty());
    let premise_name = search.kernel.display_name(premise).to_string();
    let applied = search
        .theorem
        .as_deref()
        .ok_or("proved apply result has no applied theorem")?;
    let accepted_rank = search
        .accepted_plan_rank
        .ok_or("proved apply result has no accepted plan rank")?;
    let premise_rank = search
        .premise_plan_rank
        .ok_or("proved post-B result has no premise plan rank")?;
    if canonical_type.contains(['\t', '\n', '\r'])
        || args.candidate.contains(['\t', '\n', '\r'])
        || premise_name.contains(['\t', '\n', '\r'])
        || applied.contains(['\t', '\n', '\r'])
    {
        return Err("kernel apply evidence fields are not TSV-safe".to_owned());
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
    if !closure.contains(&premise_name) || applied != premise_name {
        return Err("accepted apply proof does not use exactly the episode premise".to_owned());
    }
    let retained: Vec<&str> = ["Nat.mul_one", "Nat.zero_add"]
        .into_iter()
        .filter(|name| closure.contains(*name))
        .collect();
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|error| format!("cannot create {}: {error}", path.display()))?;
    writeln!(file, "AXEYUM_AUTOGENESIS_APPLY_EVIDENCE_V1")
        .and_then(|()| writeln!(file, "candidate\t{}", args.candidate))
        .and_then(|()| writeln!(file, "canonical_type\t{canonical_type}"))
        .and_then(|()| writeln!(file, "bundle_sha256\t{}", args.bundle_sha256))
        .and_then(|()| writeln!(file, "catalog_sha256\t{}", args.catalog_sha256))
        .and_then(|()| writeln!(file, "attempted\t{}", search.attempted))
        .and_then(|()| writeln!(file, "budget\t{}", args.budget))
        .and_then(|()| writeln!(file, "accepted_plan_rank\t{accepted_rank}"))
        .and_then(|()| writeln!(file, "applied_theorem\t{applied}"))
        .and_then(|()| writeln!(file, "premise_candidate\t{premise_name}"))
        .and_then(|()| writeln!(file, "premise_attempted\t{}", search.premise_attempted))
        .and_then(|()| writeln!(file, "premise_plan_rank\t{premise_rank}"))
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

fn run() -> Result<bool, String> {
    let args = parse_args()?;
    let plans = parse_plans(&args)?;
    let search = search(&args, &plans)?;
    let outcome = if search.theorem.is_some() {
        "proved"
    } else {
        "no-proof"
    };
    println!(
        "AUTOGENESIS_APPLY_RESULT|phase={}|premise_attempted={}|premise_plan_rank={}|attempted={}|budget={}|outcome={outcome}|theorem={}",
        args.phase.rendered(),
        search.premise_attempted,
        search
            .premise_plan_rank
            .map_or_else(|| "-".to_owned(), |rank| rank.to_string()),
        search.attempted,
        args.budget,
        search.theorem.as_deref().unwrap_or("-")
    );
    if let Some(path) = &args.evidence_output {
        write_evidence(path, &args, &search)?;
    }
    Ok(matches!(
        (args.expected, search.theorem.is_some()),
        (Expected::Proved, true) | (Expected::NoProof, false)
    ))
}

fn main() -> ExitCode {
    match run() {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => {
            eprintln!("AUTOGENESIS_APPLY_ERROR|observed outcome differs from --expect");
            ExitCode::FAILURE
        }
        Err(error) => {
            eprintln!("AUTOGENESIS_APPLY_ERROR|{error}");
            ExitCode::FAILURE
        }
    }
}
