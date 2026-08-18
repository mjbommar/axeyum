//! Check catalog-only `apply-visible-theorem` proposals against fresh Nat goals.
//!
//! The proposer runs outside this process and never sees proof bodies. This
//! checker receives its deterministic TSV projection, rebuilds the full kernel
//! environment, and gives each proposed theorem application a real admission
//! attempt. `--expect` is mandatory: completing the search without a proof is
//! not success when the caller expected one, and finding a proof is not success
//! for the registered pre-A negative control.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;

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
    let mut phase = None;
    let mut candidate = None;
    let mut premise_candidate = None;
    let mut budget = None;
    let mut expected = None;
    let mut bundle_sha256 = None;
    let mut catalog_sha256 = None;
    let mut arguments = std::env::args().skip(1);
    while let Some(flag) = arguments.next() {
        match flag.as_str() {
            "--plans" => plans = Some(PathBuf::from(take_value(&mut arguments, &flag)?)),
            "--phase" => phase = Some(Phase::parse(&take_value(&mut arguments, &flag)?)?),
            "--candidate" => candidate = Some(take_value(&mut arguments, &flag)?),
            "--premise-candidate" => premise_candidate = Some(take_value(&mut arguments, &flag)?),
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
        phase: phase.ok_or("--phase is required")?,
        candidate: candidate.ok_or("--candidate is required")?,
        premise_candidate,
        budget: budget.ok_or("--budget is required")?,
        expected: expected.ok_or("--expect is required")?,
        bundle_sha256: bundle_sha256.ok_or("--bundle-sha256 is required")?,
        catalog_sha256: catalog_sha256.ok_or("--catalog-sha256 is required")?,
    };
    if parsed.budget == 0 {
        return Err("--budget must be positive".to_owned());
    }
    if parsed.phase == Phase::PostB && parsed.premise_candidate.is_none() {
        return Err("post_b requires --premise-candidate".to_owned());
    }
    if parsed.phase != Phase::PostB && parsed.premise_candidate.is_some() {
        return Err("pre phases must not receive --premise-candidate".to_owned());
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

fn add_fresh_zero_add(
    kernel: &mut Kernel,
    prelude: &NatPrelude,
    name: NameId,
) -> Result<(), String> {
    let mut development = NatDev::new(kernel, *prelude);
    development
        .theorem(name, 1, &|d, variables| {
            let value = variables[0];
            let motive = |d: &mut NatDev<'_>, item| {
                let zero = d.zero();
                let sum = d.add(zero, item);
                d.eq(sum, item)
            };
            let statement = motive(d, value);
            let proof = d.induct(
                &motive,
                &|d| {
                    let zero = d.zero();
                    d.refl(zero)
                },
                &|d, item, hypothesis| {
                    let zero = d.zero();
                    let sum = d.add(zero, item);
                    d.congr(sum, item, hypothesis, &|d, expression| d.succ(expression))
                },
                value,
            );
            (statement, proof)
        })
        .map(|_| ())
        .map_err(|error| development.explain(&error))
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
    let premise = if let Some(rendered) = &args.premise_candidate {
        let name = intern_dotted(&mut kernel, rendered)?;
        add_fresh_zero_add(&mut kernel, &prelude, name)?;
        Some(name)
    } else {
        None
    };
    Ok(SearchBase {
        kernel,
        prelude,
        premise,
        target,
        denied: BTreeSet::from(["Nat.mul_one".to_owned(), "Nat.zero_add".to_owned()]),
    })
}

fn candidate_is_creditable(kernel: &mut Kernel, candidate: NameId, base: &SearchBase) -> bool {
    let closure: BTreeSet<String> = kernel
        .declaration_dependency_closure(candidate)
        .into_iter()
        .map(|name| kernel.display_name(name).to_string())
        .collect();
    if !base.denied.is_disjoint(&closure) || !kernel.axiom_footprint(candidate).is_empty() {
        return false;
    }
    if let Some(premise) = base.premise
        && !closure.contains(&kernel.display_name(premise).to_string())
    {
        return false;
    }
    let candidate_type = kernel
        .environment()
        .get(candidate)
        .expect("candidate exists")
        .ty();
    let target_type = kernel
        .environment()
        .get(base.target)
        .expect("target exists")
        .ty();
    kernel.def_eq(candidate_type, target_type)
        && kernel.render_lean(candidate_type) == kernel.render_lean(target_type)
}

fn search(args: &Args, plans: &[Plan]) -> Result<(usize, Option<String>), String> {
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
            || !candidate_is_creditable(&mut trial, trial_name, &base)
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
        if !candidate_is_creditable(&mut accepted, candidate, &base) {
            return Err("trial passed but exact candidate failed the same audit".to_owned());
        }
        return Ok((attempted, Some(plan.theorem.clone())));
    }
    Ok((attempted, None))
}

fn run() -> Result<bool, String> {
    let args = parse_args()?;
    let plans = parse_plans(&args)?;
    let (attempted, theorem) = search(&args, &plans)?;
    let outcome = if theorem.is_some() {
        "proved"
    } else {
        "no-proof"
    };
    println!(
        "AUTOGENESIS_APPLY_RESULT|phase={}|attempted={attempted}|budget={}|outcome={outcome}|theorem={}",
        args.phase.rendered(),
        args.budget,
        theorem.as_deref().unwrap_or("-")
    );
    Ok(matches!(
        (args.expected, theorem.is_some()),
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
