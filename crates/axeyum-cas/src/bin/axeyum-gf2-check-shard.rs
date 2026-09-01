//! Standalone admission checker for deterministic sparse-search shards.
//!
//! Every `exhausted` row is re-derived by re-running the producer's own
//! enumeration under the manifest's own declared policy; a fabricated
//! exhaustion is refused by the default invocation, with no opt-in flag.
//! `rederived_candidates` in the PASS line is how much of that work actually
//! ran, so a run that re-derived nothing cannot be mistaken for one that did.

use std::path::PathBuf;

use axeyum_cas::gf2_artifact::ArtifactLimits;
use axeyum_cas::gf2_shard::check_shard_directory;

fn main() {
    if let Err(error) = run() {
        eprintln!("GF2_SHARD_CHECK|status=FAIL|error={error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os();
    let _program = arguments.next();
    let directory = PathBuf::from(arguments.next().ok_or_else(usage)?);
    let require_all_found = match arguments.next() {
        None => false,
        Some(flag) if flag == "--require-all-found" => true,
        Some(_) => return Err(usage()),
    };
    if arguments.next().is_some() {
        return Err(usage());
    }
    let summary = check_shard_directory(&directory, ArtifactLimits::default())
        .map_err(|error| error.to_string())?;
    if require_all_found && summary.found != summary.rows {
        return Err(format!(
            "only {} of {} degree rows have checked witnesses",
            summary.found, summary.rows
        ));
    }
    println!(
        "GF2_SHARD_CHECK|status=PASS|rows={}|found={}|exhausted={}|candidate_limit={}|rederived_candidates={}|require_all_found={require_all_found}",
        summary.rows,
        summary.found,
        summary.exhausted,
        summary.candidate_limit,
        summary.rederived_candidates
    );
    Ok(())
}

fn usage() -> String {
    "usage: axeyum-gf2-check-shard <shard-dir> [--require-all-found]".to_owned()
}
