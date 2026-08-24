//! Produce and independently check one bounded structural-induction candidate
//! for a proof-isolated statement import: `Eq.refl`, and where that is stuck,
//! a bounded induction over a discovered zero/succ-shaped binder plus one
//! congruence rewrite driven by the induction hypothesis. See
//! `axeyum_lean_import::producers::bounded_induction` for the full contract.

use std::fmt::Write;
use std::fs::File;
use std::io::BufReader;
use std::path::PathBuf;

use axeyum_lean_import::producers::bounded_induction;
use axeyum_lean_import::{ImportLimits, import_statement_ndjson};
use axeyum_lean_kernel::{Declaration, Kernel, NameId};
use sha2::{Digest, Sha256};

use bounded_induction::propose_bounded_induction;

fn sha256(text: &str) -> String {
    Sha256::digest(text.as_bytes())
        .iter()
        .fold(String::with_capacity(64), |mut output, byte| {
            write!(output, "{byte:02x}").expect("writing to a String cannot fail");
            output
        })
}

fn candidate_name(kernel: &mut Kernel, goal_sha256: &str) -> NameId {
    let root = kernel.anon();
    let axeyum = kernel.name_str(root, "Axeyum");
    let autogenesis = kernel.name_str(axeyum, "Autogenesis");
    let candidate = kernel.name_str(autogenesis, "BoundedInduction");
    kernel.name_str(candidate, format!("I{}", &goal_sha256[..16]))
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args_os().skip(1);
    let path = args
        .next()
        .map(PathBuf::from)
        .ok_or("usage: bounded_induction_operation <export.ndjson> <target-definition>")?;
    let target = args
        .next()
        .ok_or("usage: bounded_induction_operation <export.ndjson> <target-definition>")?
        .into_string()
        .map_err(|_| "target definition must be UTF-8")?;
    if args.next().is_some() {
        return Err(
            "usage: bounded_induction_operation <export.ndjson> <target-definition>".into(),
        );
    }

    let completed = import_statement_ndjson(
        BufReader::new(File::open(path)?),
        ImportLimits::default(),
        &target,
    )?;
    let (mut kernel, report, target_name, goal) = completed.into_parts();
    let rendered_goal = kernel.render_lean(goal);
    let goal_sha256 = sha256(&rendered_goal);
    let candidate = propose_bounded_induction(&mut kernel, goal)
        .map_err(|reason| format!("producer declined: {reason}"))?;
    let rendered_proof = kernel.render_lean(candidate.proof);
    let proof_sha256 = sha256(&rendered_proof);
    let candidate_name = candidate_name(&mut kernel, &goal_sha256);

    if std::env::var("BIS_DEBUG").is_ok() {
        eprintln!("PROOF (pre-check)|{rendered_proof}");
    }
    kernel
        .add_declaration(Declaration::Theorem {
            name: candidate_name,
            uparams: vec![],
            ty: goal,
            value: candidate.proof,
        })
        .map_err(|error| {
            if std::env::var("BIS_DEBUG").is_ok()
                && let axeyum_lean_kernel::KernelError::TypeMismatch { expected, got } = error
            {
                eprintln!("TypeMismatch expected={}", kernel.render_lean(expected));
                eprintln!("TypeMismatch got={}", kernel.render_lean(got));
            }
            format!("independent kernel rejected bounded-induction candidate: {error:?}")
        })?;
    let closure = kernel.declaration_dependency_closure(candidate_name);
    let target_dependency = closure.contains(&target_name);
    let footprint = kernel.axiom_footprint(candidate_name);
    let theorem_dependencies = kernel.theorem_dependencies(candidate_name);
    if target_dependency || !footprint.is_empty() || !theorem_dependencies.is_empty() {
        return Err(format!(
            "candidate dependency audit failed: target={target_dependency} axioms={} theorems={}",
            footprint.len(),
            theorem_dependencies.len()
        )
        .into());
    }
    let target_identity = report
        .declaration_identities
        .iter()
        .find(|identity| identity.name == target)
        .ok_or("target declaration identity disappeared")?;
    println!(
        "BOUNDED_INDUCTION_OK|target={target}|goal_sha256={goal_sha256}|proof_sha256={proof_sha256}|target_content_sha256={}|binders_used={}|inductions_used={}|max_binders={}|max_inductions={}|declarations={}|axioms={}|theorem_dependencies={}|target_dependency={target_dependency}|ledger_writes=0",
        target_identity.content_sha256,
        candidate.binders_used,
        candidate.inductions_used,
        bounded_induction::MAX_BINDERS,
        bounded_induction::MAX_INDUCTIONS,
        report.declaration_identities.len(),
        footprint.len(),
        theorem_dependencies.len(),
    );
    println!("GOAL|{rendered_goal}");
    println!("PROOF|{rendered_proof}");
    Ok(())
}
