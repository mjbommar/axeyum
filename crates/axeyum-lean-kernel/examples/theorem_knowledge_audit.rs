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
//!   Autogenesis.Candidate.consequent --fixture chain-clean \
//!   --same-type-as Nat.mul_one --require Autogenesis.Candidate.premise \
//!   --deny Nat.zero_add --deny Nat.mul_one --expect-axiom-free
//! ```
//!
//! Unknown roots, unknown policy names, missing requirements, forbidden
//! dependencies, and a non-empty trusted footprint all exit non-zero.  A
//! proposed theorem should be admitted under a fresh name, while the original
//! target theorem is supplied with `--deny`; that makes reuse of the retained
//! answer visible without requiring a physically truncated kernel environment.

use std::collections::{BTreeMap, BTreeSet};
use std::process::ExitCode;

use axeyum_lean_kernel::{
    Declaration, Kernel, NameId, NatDev, NatOps, NatPrelude, build_nat_prelude,
};

#[derive(Debug, Default)]
struct Args {
    root: Option<String>,
    denied: BTreeSet<String>,
    required: BTreeSet<String>,
    same_type_as: Option<String>,
    fixture: Option<String>,
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
            "--same-type-as" => {
                if parsed.same_type_as.is_some() {
                    return Err("--same-type-as may be supplied only once".to_owned());
                }
                parsed.same_type_as = Some(
                    args.next()
                        .ok_or("--same-type-as requires a theorem name")?,
                );
            }
            "--fixture" => {
                if parsed.fixture.is_some() {
                    return Err("--fixture may be supplied only once".to_owned());
                }
                parsed.fixture = Some(args.next().ok_or("--fixture requires a mode")?);
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
        return Err("usage: theorem_knowledge_audit ROOT [--fixture chain-clean|chain-premise-leak|chain-direct-leak|chain-indirect-leak] [--same-type-as NAME] [--require NAME] [--deny NAME] [--expect-axiom-free]".to_owned());
    }
    Ok(parsed)
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

fn require_same_canonical_type(
    development: &mut NatDev<'_>,
    candidate: NameId,
    target: NameId,
) -> Result<(), String> {
    let (candidate_type, target_type) = {
        let kernel = development.kernel();
        let candidate_type = kernel
            .environment()
            .get(candidate)
            .ok_or("candidate declaration disappeared")?
            .ty();
        let target_type = kernel
            .environment()
            .get(target)
            .ok_or("target declaration disappeared")?
            .ty();
        (candidate_type, target_type)
    };
    let kernel = development.kernel();
    if kernel.def_eq(candidate_type, target_type)
        && kernel.render_lean(candidate_type) == kernel.render_lean(target_type)
    {
        Ok(())
    } else {
        Err("fixture premise does not have the retained premise's canonical type".to_owned())
    }
}

fn build_fixture(
    kernel: &mut Kernel,
    prelude: &NatPrelude,
    root: &str,
    fixture: &str,
) -> Result<(), String> {
    let candidate = intern_dotted(kernel, root)?;
    let premise_rendered = root.strip_suffix(".consequent").map_or_else(
        || format!("{root}.premise"),
        |prefix| format!("{prefix}.premise"),
    );
    let premise = intern_dotted(kernel, &premise_rendered)?;
    let helper = intern_dotted(kernel, &format!("{root}.helper"))?;
    let mut development = NatDev::new(kernel, *prelude);
    let premise_leaks = fixture == "chain-premise-leak";
    development
        .theorem(premise, 1, &|d, variables| {
            let value = variables[0];
            let motive = |d: &mut NatDev<'_>, item| {
                let zero = d.zero();
                let sum = d.add(zero, item);
                d.eq(sum, item)
            };
            let statement = motive(d, value);
            let proof = if premise_leaks {
                d.lemma(prelude.zero_add, &[value])
            } else {
                d.induct(
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
                )
            };
            (statement, proof)
        })
        .map_err(|error| development.explain(&error))?;
    require_same_canonical_type(&mut development, premise, prelude.zero_add)?;

    match fixture {
        "chain-clean" | "chain-premise-leak" => development
            .theorem(candidate, 1, &|d, variables| {
                let value = variables[0];
                let one = d.num(1);
                let product = d.mul(value, one);
                let statement = d.eq(product, value);
                let proof = d.lemma(premise, &[value]);
                (statement, proof)
            })
            .map(|_| ())
            .map_err(|error| development.explain(&error)),
        "chain-direct-leak" => development
            .theorem(candidate, 1, &|d, variables| {
                let value = variables[0];
                let one = d.num(1);
                let product = d.mul(value, one);
                let statement = d.eq(product, value);
                let proof = d.lemma(prelude.mul_one, &[value]);
                (statement, proof)
            })
            .map(|_| ())
            .map_err(|error| development.explain(&error)),
        "chain-indirect-leak" => {
            development
                .theorem(helper, 1, &|d, variables| {
                    let value = variables[0];
                    let one = d.num(1);
                    let product = d.mul(value, one);
                    let statement = d.eq(product, value);
                    let proof = d.lemma(prelude.mul_one, &[value]);
                    (statement, proof)
                })
                .map_err(|error| development.explain(&error))?;
            development
                .theorem(candidate, 1, &|d, variables| {
                    let value = variables[0];
                    let one = d.num(1);
                    let product = d.mul(value, one);
                    let statement = d.eq(product, value);
                    let proof = d.lemma(helper, &[value]);
                    (statement, proof)
                })
                .map(|_| ())
                .map_err(|error| development.explain(&error))
        }
        other => Err(format!("unknown fixture mode {other:?}")),
    }
}

fn names(kernel: &Kernel) -> BTreeMap<String, NameId> {
    kernel
        .environment()
        .iter()
        .map(|(name, _)| (kernel.display_name(*name).to_string(), *name))
        .collect()
}

struct AuditResult {
    closure_len: usize,
    forbidden: Vec<String>,
    missing: Vec<String>,
    footprint: Vec<String>,
    same_type: bool,
    canonical_type: bool,
}

fn resolve_root_and_policy(
    kernel: &Kernel,
    args: &Args,
    by_name: &BTreeMap<String, NameId>,
) -> Result<NameId, String> {
    let root_name = args.root.as_deref().expect("parser requires a root");
    let root = by_name
        .get(root_name)
        .copied()
        .ok_or_else(|| format!("unknown root {root_name:?}"))?;
    if !matches!(
        kernel.environment().get(root),
        Some(Declaration::Theorem { .. })
    ) {
        return Err(format!("root {root_name:?} is not a theorem"));
    }
    if args.same_type_as.as_deref() == Some(root_name) {
        return Err("candidate root must differ from --same-type-as target".to_owned());
    }
    let mut policy_names: BTreeSet<&String> = args.denied.union(&args.required).collect();
    if let Some(target) = &args.same_type_as {
        policy_names.insert(target);
    }
    let unknown: Vec<&str> = policy_names
        .into_iter()
        .filter(|name| !by_name.contains_key(name.as_str()))
        .map(String::as_str)
        .collect();
    if !unknown.is_empty() {
        return Err(format!(
            "unknown policy declarations: {}",
            unknown.join(",")
        ));
    }
    Ok(root)
}

fn evaluate(
    kernel: &mut Kernel,
    args: &Args,
    by_name: &BTreeMap<String, NameId>,
    root: NameId,
) -> AuditResult {
    let closure: BTreeSet<String> = kernel
        .declaration_dependency_closure(root)
        .into_iter()
        .map(|name| kernel.display_name(name).to_string())
        .collect();
    let forbidden: Vec<String> = args.denied.intersection(&closure).cloned().collect();
    let missing: Vec<String> = args.required.difference(&closure).cloned().collect();
    let footprint: Vec<String> = kernel
        .axiom_footprint(root)
        .into_iter()
        .map(|name| kernel.display_name(name).to_string())
        .collect();
    let (same_type, canonical_type) =
        args.same_type_as
            .as_ref()
            .map_or((true, true), |target_name| {
                let target = by_name[target_name];
                let root_ty = kernel
                    .environment()
                    .get(root)
                    .expect("resolved root exists")
                    .ty();
                let target_ty = kernel
                    .environment()
                    .get(target)
                    .expect("resolved target exists")
                    .ty();
                (
                    kernel.def_eq(root_ty, target_ty),
                    kernel.render_lean(root_ty) == kernel.render_lean(target_ty),
                )
            });

    AuditResult {
        closure_len: closure.len(),
        forbidden,
        missing,
        footprint,
        same_type,
        canonical_type,
    }
}

fn report(root_name: &str, args: &Args, result: &AuditResult) -> bool {
    println!(
        "KNOWLEDGE_AUDIT|root={root_name}|closure={}|required={}|denied={}|trusted={}|same_type={same_type}|canonical_type={canonical_type}",
        result.closure_len,
        args.required.len(),
        args.denied.len(),
        result.footprint.len(),
        same_type = result.same_type,
        canonical_type = result.canonical_type,
    );
    if !result.forbidden.is_empty() {
        eprintln!(
            "KNOWLEDGE_AUDIT_ERROR|forbidden dependencies reached transitively: {}",
            result.forbidden.join(",")
        );
    }
    if !result.missing.is_empty() {
        eprintln!(
            "KNOWLEDGE_AUDIT_ERROR|required dependencies not reached: {}",
            result.missing.join(",")
        );
    }
    if args.expect_axiom_free && !result.footprint.is_empty() {
        eprintln!(
            "KNOWLEDGE_AUDIT_ERROR|trusted footprint is not empty: {}",
            result.footprint.join(",")
        );
    }
    if !result.same_type {
        eprintln!(
            "KNOWLEDGE_AUDIT_ERROR|root type differs from {:?}",
            args.same_type_as
                .as_deref()
                .expect("comparison target exists")
        );
    }
    if !result.canonical_type {
        eprintln!(
            "KNOWLEDGE_AUDIT_ERROR|root canonical type differs from {:?}",
            args.same_type_as
                .as_deref()
                .expect("comparison target exists")
        );
    }

    result.forbidden.is_empty()
        && result.missing.is_empty()
        && result.same_type
        && result.canonical_type
        && (!args.expect_axiom_free || result.footprint.is_empty())
}

fn main() -> ExitCode {
    let args = match parse_args() {
        Ok(args) => args,
        Err(error) => {
            eprintln!("KNOWLEDGE_AUDIT_ERROR|{error}");
            return ExitCode::FAILURE;
        }
    };
    let root_name = args.root.as_deref().expect("parser requires a root");
    let mut kernel = Kernel::new();
    let prelude = build_nat_prelude(&mut kernel).expect("Nat prelude must build");
    if let Some(fixture) = &args.fixture
        && let Err(error) = build_fixture(&mut kernel, &prelude, root_name, fixture)
    {
        eprintln!("KNOWLEDGE_AUDIT_ERROR|fixture construction failed: {error}");
        return ExitCode::FAILURE;
    }
    let by_name = names(&kernel);
    let root = match resolve_root_and_policy(&kernel, &args, &by_name) {
        Ok(root) => root,
        Err(error) => {
            eprintln!("KNOWLEDGE_AUDIT_ERROR|{error}");
            return ExitCode::FAILURE;
        }
    };
    let result = evaluate(&mut kernel, &args, &by_name, root);
    if report(root_name, &args, &result) {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
