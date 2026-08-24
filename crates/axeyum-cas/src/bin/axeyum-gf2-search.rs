//! Produce one deterministic sparse-search shard and its content-bound manifest.

use std::fs;
use std::path::{Path, PathBuf};

use axeyum_cas::gf2_artifact::{ArtifactLimits, HalfDegreeArtifact, to_canonical_json};
use axeyum_cas::gf2_search::{SparseSearchLimits, SparseSearchOutcome, search_sparse_half_degree};
use axeyum_cas::gf2_shard::{
    MANIFEST_FILE, ManifestArithmeticLimits, SHARD_FORMAT, SHARD_VERSION, ShardManifest, ShardRow,
    ShardStatus, sha256_hex, to_canonical_manifest_json,
};

fn main() {
    if let Err(error) = run() {
        eprintln!("GF2_SEARCH|status=FAIL|error={error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os();
    let _program = arguments.next();
    let output = PathBuf::from(arguments.next().ok_or_else(usage)?);
    let producer = utf8_argument(arguments.next(), "producer", usage)?;
    let start_degree = parse_argument(arguments.next(), "start degree", usage)?;
    let end_degree = parse_argument(arguments.next(), "end degree", usage)?;
    let max_tail_terms = parse_argument(arguments.next(), "max tail terms", usage)?;
    let max_candidates = parse_argument(arguments.next(), "max candidates", usage)?;
    if arguments.next().is_some() {
        return Err(usage());
    }
    if output.exists() {
        return Err(format!("{} already exists", output.display()));
    }
    let parent = output
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    if !parent.is_dir() {
        return Err(format!(
            "parent directory {} does not exist",
            parent.display()
        ));
    }
    let name = output
        .file_name()
        .ok_or_else(|| "output directory has no file name".to_owned())?
        .to_string_lossy();
    let temporary = parent.join(format!(".{name}.tmp-{}", std::process::id()));
    fs::create_dir(&temporary).map_err(|error| format!("{}: {error}", temporary.display()))?;
    let result = produce_shard(
        &temporary,
        producer,
        start_degree,
        end_degree,
        max_tail_terms,
        max_candidates,
    );
    let (rows, found, exhausted, candidate_limit) = match result {
        Ok(summary) => summary,
        Err(error) => {
            let _ = fs::remove_dir_all(&temporary);
            return Err(error);
        }
    };
    if let Err(error) = fs::rename(&temporary, &output) {
        let _ = fs::remove_dir_all(&temporary);
        return Err(format!(
            "{} -> {}: {error}",
            temporary.display(),
            output.display()
        ));
    }
    println!(
        "GF2_SEARCH|status=PASS|path={}|rows={rows}|found={found}|exhausted={exhausted}|candidate_limit={candidate_limit}",
        output.display()
    );
    Ok(())
}

fn produce_shard(
    directory: &Path,
    producer: String,
    start_degree: usize,
    end_degree: usize,
    max_tail_terms: usize,
    max_candidates: u64,
) -> Result<(usize, usize, usize, usize), String> {
    if start_degree == 0 || start_degree > end_degree {
        return Err("invalid inclusive degree range".to_owned());
    }
    let limits = SparseSearchLimits {
        max_tail_terms,
        max_candidates,
        ..SparseSearchLimits::default()
    };
    let artifact_limits = ArtifactLimits {
        primary: limits.arithmetic,
        ..ArtifactLimits::default()
    };
    let mut rows = Vec::with_capacity(end_degree - start_degree + 1);
    let mut found = 0;
    let mut exhausted = 0;
    let mut candidate_limit = 0;
    for degree in start_degree..=end_degree {
        let outcome =
            search_sparse_half_degree(degree, limits).map_err(|error| error.to_string())?;
        let row = match outcome {
            SparseSearchOutcome::Found {
                certificate,
                candidates_tested,
                tail_terms,
            } => {
                let artifact_name = format!("degree-{degree}.json");
                let artifact = HalfDegreeArtifact {
                    id: format!("lemire-degree-{degree}"),
                    producer: producer.clone(),
                    certificate,
                };
                let bytes = to_canonical_json(&artifact, artifact_limits)
                    .map_err(|error| error.to_string())?;
                fs::write(directory.join(&artifact_name), &bytes)
                    .map_err(|error| format!("{artifact_name}: {error}"))?;
                found += 1;
                ShardRow {
                    degree,
                    status: ShardStatus::Found,
                    candidates_tested,
                    tail_terms: Some(tail_terms),
                    artifact: Some(artifact_name),
                    artifact_sha256: Some(sha256_hex(bytes.as_bytes())),
                }
            }
            SparseSearchOutcome::Exhausted { candidates_tested } => {
                exhausted += 1;
                ShardRow {
                    degree,
                    status: ShardStatus::Exhausted,
                    candidates_tested,
                    tail_terms: None,
                    artifact: None,
                    artifact_sha256: None,
                }
            }
            SparseSearchOutcome::CandidateLimit {
                candidates_tested, ..
            } => {
                candidate_limit += 1;
                ShardRow {
                    degree,
                    status: ShardStatus::CandidateLimit,
                    candidates_tested,
                    tail_terms: None,
                    artifact: None,
                    artifact_sha256: None,
                }
            }
        };
        rows.push(row);
    }
    let manifest = ShardManifest {
        format: SHARD_FORMAT.to_owned(),
        version: SHARD_VERSION,
        producer,
        start_degree,
        end_degree,
        max_tail_terms,
        max_candidates_per_degree: max_candidates,
        arithmetic_limits: ManifestArithmeticLimits::from(limits.arithmetic),
        rows,
    };
    let manifest_json = to_canonical_manifest_json(&manifest).map_err(|error| error.to_string())?;
    fs::write(directory.join(MANIFEST_FILE), manifest_json)
        .map_err(|error| format!("{MANIFEST_FILE}: {error}"))?;
    Ok((manifest.rows.len(), found, exhausted, candidate_limit))
}

fn usage() -> String {
    "usage: axeyum-gf2-search <new-output-dir> <producer> <start> <end> <max-tail-terms> <max-candidates-per-degree>".to_owned()
}

fn utf8_argument(
    argument: Option<std::ffi::OsString>,
    name: &str,
    usage: fn() -> String,
) -> Result<String, String> {
    argument
        .ok_or_else(usage)?
        .into_string()
        .map_err(|_| format!("{name} is not UTF-8"))
}

fn parse_argument<T: std::str::FromStr>(
    argument: Option<std::ffi::OsString>,
    name: &str,
    usage: fn() -> String,
) -> Result<T, String> {
    utf8_argument(argument, name, usage)?
        .parse()
        .map_err(|_| format!("invalid {name}"))
}
