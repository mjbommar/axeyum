//! Produce and independently check one bounded Eq/Iff-combinator candidate
//! (see `modeq_family_support`) for a proof-isolated statement import, then
//! mechanically audit that the candidate does not cite the target theorem
//! itself or any named sibling — never by doc comment, never by head symbol,
//! only over `Kernel::declaration_dependency_closure`.

use std::fmt::Write;
use std::fs::File;
use std::io::BufReader;
use std::path::PathBuf;

use axeyum_lean_import::{ImportLimits, import_statement_ndjson};
use axeyum_lean_kernel::{Declaration, Kernel, NameId};
use sha2::{Digest, Sha256};

#[path = "modeq_family_support/mod.rs"]
mod modeq_family_support;

use modeq_family_support::propose_modeq_family;

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
    let candidate = kernel.name_str(autogenesis, "ModEqFamily");
    kernel.name_str(candidate, format!("M{}", &goal_sha256[..16]))
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args_os().skip(1);
    let path = args
        .next()
        .map(PathBuf::from)
        .ok_or("usage: modeq_family_operation <export.ndjson> <target-definition>")?;
    let target = args
        .next()
        .ok_or("usage: modeq_family_operation <export.ndjson> <target-definition>")?
        .into_string()
        .map_err(|_| "target definition must be UTF-8")?;
    if args.next().is_some() {
        return Err("usage: modeq_family_operation <export.ndjson> <target-definition>".into());
    }

    let completed = import_statement_ndjson(
        BufReader::new(File::open(path)?),
        ImportLimits::default(),
        &target,
    )?;
    let (mut kernel, report, target_name, goal) = completed.into_parts();
    let rendered_goal = kernel.render_lean(goal);
    let goal_sha256 = sha256(&rendered_goal);
    let candidate = propose_modeq_family(&mut kernel, goal)
        .map_err(|reason| format!("producer declined: {reason}"))?;
    let rendered_proof = kernel.render_lean(candidate.proof);
    let proof_sha256 = sha256(&rendered_proof);
    let candidate_name = candidate_name(&mut kernel, &goal_sha256);

    if std::env::var("MFS_DEBUG").is_ok() {
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
            format!("independent kernel rejected modeq-family candidate: {error:?}")
        })?;

    // Mechanical circularity guard — `modeq_family_support::audit_circularity`,
    // computed only from `Kernel::declaration_dependency_closure` /
    // `Kernel::axiom_footprint` / `Kernel::theorem_dependencies`, never a doc
    // comment, never a head-symbol text match. `crates/axeyum-lean-import/
    // tests/modeq_family_operation.rs` carries the adversarial fixture
    // proving this exact function actually rejects a candidate built to cite
    // its own target, and a positive control proving it does not
    // false-positive on a genuine derivation.
    let audit = modeq_family_support::audit_circularity(&kernel, candidate_name, target_name);
    if !audit.passes() {
        return Err(format!("candidate dependency audit failed: {audit:?}").into());
    }
    let target_identity = report
        .declaration_identities
        .iter()
        .find(|identity| identity.name == target)
        .ok_or("target declaration identity disappeared")?;
    println!(
        "MODEQ_FAMILY_OK|target={target}|goal_sha256={goal_sha256}|proof_sha256={proof_sha256}|target_content_sha256={}|binders_used={}|max_binders={}|declarations={}|axioms={}|theorem_dependencies={}|target_dependency={}|ledger_writes=0",
        target_identity.content_sha256,
        candidate.binders_used,
        modeq_family_support::MAX_BINDERS,
        report.declaration_identities.len(),
        audit.axiom_footprint,
        audit.theorem_dependencies,
        audit.target_dependency,
    );
    println!("GOAL|{rendered_goal}");
    println!("PROOF|{rendered_proof}");
    Ok(())
}
