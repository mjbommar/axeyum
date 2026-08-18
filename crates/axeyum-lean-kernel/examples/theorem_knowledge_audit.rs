//! Fail-closed proof-dependency audit for a Nat theorem.
//!
//! A counterfactual Autogenesis run may keep the complete checked prelude in
//! the kernel while hiding selected theorems from proof search.  Keeping the
//! environment avoids invalidating later declarations, but it creates a proof
//! leakage risk: a proposed proof could still name a withheld theorem directly
//! or through an allowed helper.  This command audits the kernel-derived,
//! transitive declaration closure after admission.
//!
//! ```sh
//! cargo run -q -p axeyum-lean-kernel --example theorem_knowledge_audit -- \
//!   Nat.mul_one --require Nat.zero_add --deny Nat.add_comm --expect-axiom-free
//! ```
//!
//! Unknown roots, unknown policy names, missing requirements, forbidden
//! dependencies, and a non-empty trusted footprint all exit non-zero.  A
//! proposed theorem should be admitted under a fresh name, while the original
//! target theorem is supplied with `--deny`; that makes reuse of the retained
//! answer visible without requiring a physically truncated kernel environment.

use std::collections::{BTreeMap, BTreeSet};
use std::process::ExitCode;

use axeyum_lean_kernel::{Declaration, Kernel, NameId, build_nat_prelude};

#[derive(Debug, Default)]
struct Args {
    root: Option<String>,
    denied: BTreeSet<String>,
    required: BTreeSet<String>,
    expect_axiom_free: bool,
}

fn parse_args() -> Result<Args, String> {
    let mut parsed = Args::default();
    let mut args = std::env::args().skip(1);
    while let Some(argument) = args.next() {
        match argument.as_str() {
            "--deny" => {
                let name = args.next().ok_or("--deny requires a declaration name")?;
                parsed.denied.insert(name);
            }
            "--require" => {
                let name = args.next().ok_or("--require requires a declaration name")?;
                parsed.required.insert(name);
            }
            "--expect-axiom-free" => parsed.expect_axiom_free = true,
            flag if flag.starts_with("--") => return Err(format!("unknown flag {flag:?}")),
            root if parsed.root.is_none() => parsed.root = Some(root.to_owned()),
            extra => return Err(format!("unexpected positional argument {extra:?}")),
        }
    }
    if parsed
        .denied
        .intersection(&parsed.required)
        .next()
        .is_some()
    {
        return Err("a declaration cannot be both required and denied".to_owned());
    }
    if parsed.root.is_none() {
        return Err("usage: theorem_knowledge_audit ROOT [--require NAME] [--deny NAME] [--expect-axiom-free]".to_owned());
    }
    Ok(parsed)
}

fn names(kernel: &Kernel) -> BTreeMap<String, NameId> {
    kernel
        .environment()
        .iter()
        .map(|(name, _)| (kernel.display_name(*name).to_string(), *name))
        .collect()
}

fn main() -> ExitCode {
    let args = match parse_args() {
        Ok(args) => args,
        Err(error) => {
            eprintln!("KNOWLEDGE_AUDIT_ERROR|{error}");
            return ExitCode::FAILURE;
        }
    };

    let mut kernel = Kernel::new();
    build_nat_prelude(&mut kernel).expect("Nat prelude must build");
    let by_name = names(&kernel);
    let root_name = args.root.as_deref().expect("parser requires a root");
    let Some(&root) = by_name.get(root_name) else {
        eprintln!("KNOWLEDGE_AUDIT_ERROR|unknown root {root_name:?}");
        return ExitCode::FAILURE;
    };
    if !matches!(
        kernel.environment().get(root),
        Some(Declaration::Theorem { .. })
    ) {
        eprintln!("KNOWLEDGE_AUDIT_ERROR|root {root_name:?} is not a theorem");
        return ExitCode::FAILURE;
    }

    let policy_names: BTreeSet<&String> = args.denied.union(&args.required).collect();
    let unknown: Vec<&str> = policy_names
        .into_iter()
        .filter(|name| !by_name.contains_key(name.as_str()))
        .map(String::as_str)
        .collect();
    if !unknown.is_empty() {
        eprintln!(
            "KNOWLEDGE_AUDIT_ERROR|unknown policy declarations: {}",
            unknown.join(",")
        );
        return ExitCode::FAILURE;
    }

    let closure: BTreeSet<String> = kernel
        .declaration_dependency_closure(root)
        .into_iter()
        .map(|name| kernel.display_name(name).to_string())
        .collect();
    let forbidden: Vec<&str> = args
        .denied
        .intersection(&closure)
        .map(String::as_str)
        .collect();
    let missing: Vec<&str> = args
        .required
        .difference(&closure)
        .map(String::as_str)
        .collect();
    let footprint = kernel.axiom_footprint(root);

    println!(
        "KNOWLEDGE_AUDIT|root={root_name}|closure={}|required={}|denied={}|trusted={}",
        closure.len(),
        args.required.len(),
        args.denied.len(),
        footprint.len()
    );
    if !forbidden.is_empty() {
        eprintln!(
            "KNOWLEDGE_AUDIT_ERROR|forbidden dependencies reached transitively: {}",
            forbidden.join(",")
        );
    }
    if !missing.is_empty() {
        eprintln!(
            "KNOWLEDGE_AUDIT_ERROR|required dependencies not reached: {}",
            missing.join(",")
        );
    }
    if args.expect_axiom_free && !footprint.is_empty() {
        let rendered: Vec<String> = footprint
            .into_iter()
            .map(|name| kernel.display_name(name).to_string())
            .collect();
        eprintln!(
            "KNOWLEDGE_AUDIT_ERROR|trusted footprint is not empty: {}",
            rendered.join(",")
        );
    }

    if forbidden.is_empty()
        && missing.is_empty()
        && (!args.expect_axiom_free || kernel.axiom_footprint(root).is_empty())
    {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
