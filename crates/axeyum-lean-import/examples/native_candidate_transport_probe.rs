//! Compose native theorem roots into a proof-isolated imported goal, then run
//! the bounded application producer over exactly those transported roots.
//!
//! This is a diagnostic boundary: success checks one candidate theorem in the
//! private composed kernel, while failure reports the existing typed import,
//! composition, or producer error. It grants no fact or operation authority.

use std::fs::File;
use std::io::BufReader;
use std::path::PathBuf;

use axeyum_lean_import::{
    CandidateTransportReceipt, ImportLimits, import_candidate_statement_ndjson,
    producers::propose_bounded_application, transport_checked_theorem_candidate,
};
use axeyum_lean_kernel::{Declaration, Kernel, build_int_prelude};

const USAGE: &str = "usage: native_candidate_transport_probe <stream.ndjson> <target-definition> <native-theorem>...";

const CAPSULE_CANDIDATES: [&str; 13] = [
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
        eprintln!("NATIVE_CANDIDATE_TRANSPORT|result=declined|reason={error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let path = arguments.next().map(PathBuf::from).ok_or(USAGE)?;
    let target = utf8_argument(arguments.next())?;
    let roots = arguments
        .map(|argument| {
            argument
                .into_string()
                .map_err(|_| "native theorem is not valid UTF-8".to_owned())
        })
        .collect::<Result<Vec<_>, _>>()?;
    if roots.is_empty() {
        return Err(USAGE.to_owned());
    }

    let imported = import_candidate_statement_ndjson(
        BufReader::new(
            File::open(&path)
                .map_err(|error| format!("cannot read {}: {error}", path.display()))?,
        ),
        ImportLimits::default(),
        &target,
        &CAPSULE_CANDIDATES.map(str::to_owned),
    )
    .map_err(|error| format!("statement-import:{error}"))?;
    let (mut kernel, _report, _target_name, goal) = imported.into_parts();

    let mut source = Kernel::new();
    build_int_prelude(&mut source).map_err(|error| format!("native-prelude:{error:?}"))?;
    let mut candidates = Vec::new();
    let mut added = 0;
    let mut reused = 0;
    let mut declined = Vec::new();
    for root in &roots {
        match transport_checked_theorem_candidate(&source, &kernel, root) {
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
            "candidate-transport:none-available;declines={}",
            declined.join(";")
        ));
    }
    let candidate = propose_bounded_application(&mut kernel, goal, &candidates)
        .map_err(|error| {
            format!(
                "bounded-application:{error:?};transported={};added={added};reused={reused};transport_declines={}",
                candidates.len(),
                declined.len()
            )
        })?;
    let root = kernel.anon();
    let axeyum = kernel.name_str(root, "Axeyum");
    let transport = kernel.name_str(axeyum, "NativeCandidateTransport");
    let name = kernel.name_str(transport, "Verified");
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: goal,
            value: candidate.proof,
        })
        .map_err(|error| format!("candidate-admission:{error:?}"))?;
    let footprint = kernel
        .axiom_footprint(name)
        .into_iter()
        .map(|dependency| kernel.display_name(dependency).to_string())
        .collect::<Vec<_>>();
    println!(
        "NATIVE_CANDIDATE_TRANSPORT|result=accepted|roots={}|transported={}|added={added}|reused={reused}|transport_declines={}|binders_used={}|application_depth={}|terms_considered={}|axioms={}",
        roots.len(),
        candidates.len(),
        declined.len(),
        candidate.binders_used,
        candidate.application_depth,
        candidate.terms_considered,
        footprint.len(),
    );
    Ok(())
}

fn utf8_argument(argument: Option<std::ffi::OsString>) -> Result<String, String> {
    argument
        .ok_or_else(|| USAGE.to_owned())?
        .into_string()
        .map_err(|_| "target definition is not valid UTF-8".to_owned())
}
