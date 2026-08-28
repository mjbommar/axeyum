//! Transport explicit theorem roots from one imported source capsule into an
//! independently proof-isolated imported target, then run bounded application.
//!
//! This is the source-to-source counterpart of `native_candidate_transport_probe`.
//! Exact declaration reuse or checked closure composition still has to succeed,
//! each transported theorem must have an empty axiom footprint, and the target
//! theorem is absent from both inputs.

use std::fs::File;
use std::io::{BufReader, Read};
use std::path::PathBuf;

use axeyum_lean_import::{
    CandidateTransportReceipt, ImportLimits, canonical_declaration_sha256,
    canonical_expression_sha256, import_candidate_statement_ndjson, import_ndjson,
    producers::propose_bounded_application, transport_checked_theorem_candidate,
};
use axeyum_lean_kernel::Declaration;

const USAGE: &str = "usage: imported_candidate_transport_probe <target-stream.ndjson> <target-definition> <source-stream.ndjson> <source-theorem>...";

const TARGET_CAPSULE_CANDIDATES: [&str; 13] = [
    "Eq.refl",
    "Eq.symm",
    "Eq.trans",
    "congrArg",
    "Nat.zero_add",
    "Nat.add_zero",
    "Nat.mul_one",
    "Nat.one_mul",
    "Nat.le_refl",
    "Nat.le_trans",
    "Nat.succ_le_succ",
    "Nat.zero_le",
    "Nat.not_succ_le_zero",
];

fn main() {
    if let Err(error) = run() {
        eprintln!("IMPORTED_CANDIDATE_TRANSPORT|result=declined|reason={error}");
        std::process::exit(1);
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "a linear CLI driver: parse args, run the probe, print the record. Splitting it would scatter one readable sequence across helpers that each have exactly one caller."
)]
fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let target_path = arguments.next().map(PathBuf::from).ok_or(USAGE)?;
    let target = utf8_argument(arguments.next())?;
    let source_path = arguments.next().map(PathBuf::from).ok_or(USAGE)?;
    let roots = arguments
        .map(|argument| {
            argument
                .into_string()
                .map_err(|_| "source theorem is not valid UTF-8".to_owned())
        })
        .collect::<Result<Vec<_>, _>>()?;
    if roots.is_empty() {
        return Err(USAGE.to_owned());
    }

    let imported = import_candidate_statement_ndjson(
        BufReader::new(
            File::open(&target_path)
                .map_err(|error| format!("cannot read {}: {error}", target_path.display()))?,
        ),
        ImportLimits::default(),
        &target,
        &TARGET_CAPSULE_CANDIDATES.map(str::to_owned),
    )
    .map_err(|error| format!("target-import:{error}"))?;
    let (mut kernel, report, target_name, goal) = imported.into_parts();

    let mut source_bytes = Vec::new();
    File::open(&source_path)
        .and_then(|mut file| file.read_to_end(&mut source_bytes))
        .map_err(|error| format!("cannot read {}: {error}", source_path.display()))?;
    let source = import_ndjson(std::io::Cursor::new(source_bytes), ImportLimits::default())
        .map_err(|error| format!("source-import:{error:?}"))?;

    let mut candidates = Vec::new();
    let mut added = 0;
    let mut reused = 0;
    let mut declined = Vec::new();
    for root in &roots {
        match transport_checked_theorem_candidate(source.kernel(), &kernel, root) {
            Ok(completed) => {
                match completed.receipt() {
                    CandidateTransportReceipt::Added(_) => added += 1,
                    CandidateTransportReceipt::Reused(_) => reused += 1,
                }
                let (completed_kernel, candidate, _) = completed.into_parts();
                kernel = completed_kernel;
                candidates.push(candidate);
            }
            Err(error) => declined.push(format!("{root}:{error:?}")),
        }
    }
    if candidates.is_empty() {
        return Err(format!(
            "candidate-transport:none-available;transport_declines={}",
            declined.join(";")
        ));
    }

    let candidate = propose_bounded_application(&mut kernel, goal, &candidates).map_err(|error| {
        format!(
            "bounded-application:{error:?};transported={};added={added};reused={reused};transport_declines={}:{}",
            candidates.len(),
            declined.len(),
            declined.join(";")
        )
    })?;
    let root = kernel.anon();
    let axeyum = kernel.name_str(root, "Axeyum");
    let transport = kernel.name_str(axeyum, "ImportedCandidateTransport");
    let name = kernel.name_str(transport, "Verified");
    let goal_sha256 = canonical_expression_sha256(&kernel, goal)
        .map_err(|error| format!("candidate-audit:goal-identity:{error}"))?;
    let proof_sha256 = canonical_expression_sha256(&kernel, candidate.proof)
        .map_err(|error| format!("candidate-audit:proof-identity:{error}"))?;
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: goal,
            value: candidate.proof,
        })
        .map_err(|error| format!("candidate-admission:{error:?}"))?;
    let closure = kernel.declaration_dependency_closure(name);
    let target_dependency = closure.contains(&target_name);
    let footprint = kernel.axiom_footprint(name);
    let theorem_dependencies = kernel.theorem_dependencies(name);
    let theorem_dependency_names = theorem_dependencies
        .iter()
        .map(|dependency| kernel.display_name(*dependency).to_string())
        .collect::<Vec<_>>()
        .join(",");
    let target_content_sha256 = canonical_declaration_sha256(&kernel, name)
        .map_err(|error| format!("candidate-audit:declaration-identity:{error}"))?;
    if target_dependency || !footprint.is_empty() {
        return Err(format!(
            "candidate-audit:target_dependency={target_dependency};axioms={}",
            footprint.len()
        ));
    }
    println!(
        "IMPORTED_CANDIDATE_TRANSPORT|result=accepted|target={target}|roots={}|transported={}|added={added}|reused={reused}|transport_declines={}|binders_used={}|application_depth={}|terms_considered={}|declarations={}|axioms={}|theorem_dependencies={}|theorem_dependency_names={theorem_dependency_names}|target_dependency={target_dependency}|goal_sha256={goal_sha256}|proof_sha256={proof_sha256}|target_content_sha256={target_content_sha256}",
        roots.len(),
        candidates.len(),
        declined.len(),
        candidate.binders_used,
        candidate.application_depth,
        candidate.terms_considered,
        report.admitted_declarations + added,
        footprint.len(),
        theorem_dependencies.len(),
    );
    Ok(())
}

fn utf8_argument(argument: Option<std::ffi::OsString>) -> Result<String, String> {
    argument
        .ok_or_else(|| USAGE.to_owned())?
        .into_string()
        .map_err(|_| "target definition is not valid UTF-8".to_owned())
}
