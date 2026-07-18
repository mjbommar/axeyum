//! Run a hash-bound `QF_BV` manifest through fresh cvc5 processes at fixed timeouts.
//!
//! Usage: `cvc5_qfbv_timeout_sweep CORPUS_ROOT MANIFEST CVC5 OUT.json
//! [REPETITIONS] [TIMEOUTS_CSV]`.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Component, Path, PathBuf};
use std::process::Command;
use std::time::Instant;

use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const SCHEMA: &str = "axeyum-qfbv-cvc5-timeout-sweep-v1";

#[derive(Clone, Debug)]
struct ManifestEntry {
    path: PathBuf,
    content_hash: String,
    expected: String,
    family: String,
    tiers: Vec<String>,
}

#[derive(Debug)]
struct Manifest {
    raw_sha256: String,
    name: String,
    logic: String,
    source: String,
    entries: Vec<ManifestEntry>,
}

#[derive(Debug)]
struct RunRow {
    timeout_ms: u32,
    repetition: usize,
    path: PathBuf,
    content_hash: String,
    expected: String,
    outcome: String,
    elapsed_nanos: u64,
    stdout_bytes: usize,
    stdout_sha256: String,
}

fn sha256_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let digest = Sha256::digest(bytes);
    let mut encoded = String::with_capacity(64);
    for byte in digest {
        encoded.push(char::from(HEX[usize::from(byte >> 4)]));
        encoded.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    encoded
}

fn required_str<'a>(value: &'a Value, key: &str) -> Result<&'a str, String> {
    value[key]
        .as_str()
        .ok_or_else(|| format!("missing string field {key}"))
}

fn checked_relative_path(value: &str) -> Result<PathBuf, String> {
    let path = Path::new(value);
    if value.is_empty()
        || path.is_absolute()
        || path.components().any(|component| {
            matches!(
                component,
                Component::ParentDir | Component::RootDir | Component::Prefix(_)
            )
        })
    {
        return Err(format!(
            "manifest path is not a safe relative path: {value:?}"
        ));
    }
    Ok(path.to_path_buf())
}

fn load_manifest(root: &Path, path: &Path) -> Result<Manifest, String> {
    let bytes = fs::read(path).map_err(|error| format!("read {}: {error}", path.display()))?;
    let value: Value = serde_json::from_slice(&bytes)
        .map_err(|error| format!("parse {}: {error}", path.display()))?;
    if value["version"].as_u64() != Some(1) {
        return Err("manifest version must be 1".to_string());
    }
    let logic = required_str(&value, "logic")?.to_string();
    if logic != "QF_BV" {
        return Err(format!("manifest logic must be QF_BV, got {logic:?}"));
    }
    let files = value["files"]
        .as_array()
        .ok_or_else(|| "manifest files must be an array".to_string())?;
    if files.is_empty() {
        return Err("manifest files must not be empty".to_string());
    }
    let mut seen = BTreeSet::new();
    let mut entries = Vec::with_capacity(files.len());
    for (index, file) in files.iter().enumerate() {
        let relative = checked_relative_path(required_str(file, "path")?)?;
        if !seen.insert(relative.clone()) {
            return Err(format!("duplicate manifest path {}", relative.display()));
        }
        let content_hash = required_str(file, "content_hash")?.to_string();
        let Some(expected_hex) = content_hash.strip_prefix("sha256:") else {
            return Err(format!(
                "{}: content_hash must use sha256:",
                relative.display()
            ));
        };
        if expected_hex.len() != 64 || !expected_hex.bytes().all(|byte| byte.is_ascii_hexdigit()) {
            return Err(format!(
                "{}: invalid sha256 content_hash",
                relative.display()
            ));
        }
        let expected = required_str(file, "expected")?.to_string();
        if !matches!(expected.as_str(), "sat" | "unsat") {
            return Err(format!(
                "{}: expected must be sat or unsat, got {expected:?}",
                relative.display()
            ));
        }
        let full_path = root.join(&relative);
        let script = fs::read(&full_path)
            .map_err(|error| format!("read {}: {error}", full_path.display()))?;
        let actual_hash = sha256_hex(&script);
        if actual_hash != expected_hex {
            return Err(format!(
                "{}: content hash mismatch: expected {expected_hex}, got {actual_hash}",
                relative.display()
            ));
        }
        let tiers = file["tiers"]
            .as_array()
            .ok_or_else(|| format!("files[{index}].tiers must be an array"))?
            .iter()
            .map(|tier| {
                tier.as_str()
                    .map(str::to_string)
                    .ok_or_else(|| format!("files[{index}].tiers must contain strings"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        entries.push(ManifestEntry {
            path: relative,
            content_hash,
            expected,
            family: required_str(file, "family")?.to_string(),
            tiers,
        });
    }
    let disk_files = fs::read_dir(root)
        .map_err(|error| format!("read {}: {error}", root.display()))?
        .filter_map(Result::ok)
        .filter_map(|entry| {
            let path = entry.path();
            (path.extension().and_then(|value| value.to_str()) == Some("smt2"))
                .then(|| PathBuf::from(entry.file_name()))
        })
        .collect::<BTreeSet<_>>();
    if disk_files != seen {
        return Err(format!(
            "manifest membership mismatch: {} manifested, {} on disk",
            seen.len(),
            disk_files.len()
        ));
    }
    Ok(Manifest {
        raw_sha256: format!("sha256:{}", sha256_hex(&bytes)),
        name: required_str(&value, "name")?.to_string(),
        logic,
        source: required_str(&value, "source")?.to_string(),
        entries,
    })
}

fn cvc5_version(binary: &Path) -> Result<String, String> {
    let output = Command::new(binary)
        .arg("--version")
        .output()
        .map_err(|error| format!("run {} --version: {error}", binary.display()))?;
    if !output.status.success() || !output.stderr.is_empty() {
        return Err(format!("{} --version failed cleanly", binary.display()));
    }
    let stdout = std::str::from_utf8(&output.stdout)
        .map_err(|error| format!("cvc5 version output is not UTF-8: {error}"))?;
    let version = stdout.lines().next().unwrap_or("").trim();
    if !version.starts_with("cvc5 ") {
        return Err(format!("unexpected cvc5 version output: {version:?}"));
    }
    Ok(version.to_string())
}

fn parse_cvc5_outcome(stdout: &[u8]) -> Result<&'static str, String> {
    let text = std::str::from_utf8(stdout)
        .map_err(|error| format!("cvc5 stdout is not UTF-8: {error}"))?;
    let mut nonempty = text.lines().map(str::trim).filter(|line| !line.is_empty());
    let outcome = match nonempty.next() {
        Some("sat") => "sat",
        Some("unsat") => "unsat",
        Some("unknown") => "unknown",
        other => return Err(format!("cvc5 stdout has no leading verdict: {other:?}")),
    };
    if nonempty.any(|line| matches!(line, "sat" | "unsat" | "unknown")) {
        return Err("cvc5 stdout contains more than one verdict".to_string());
    }
    Ok(outcome)
}

fn run_one(
    binary: &Path,
    root: &Path,
    entry: &ManifestEntry,
    timeout_ms: u32,
    repetition: usize,
) -> Result<RunRow, String> {
    let script = root.join(&entry.path);
    let started = Instant::now();
    let output = Command::new(binary)
        .arg("--lang=smt2")
        .arg("--produce-models")
        .arg(format!("--tlimit-per={timeout_ms}"))
        .arg(&script)
        .output()
        .map_err(|error| format!("run {} on {}: {error}", binary.display(), script.display()))?;
    let elapsed_nanos = u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX);
    if !output.status.success() {
        return Err(format!(
            "cvc5 timeout {timeout_ms} repetition {repetition} {} exited {}: {}",
            entry.path.display(),
            output.status,
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    if !output.stderr.is_empty() {
        return Err(format!(
            "cvc5 timeout {timeout_ms} repetition {repetition} {} wrote stderr: {}",
            entry.path.display(),
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    let outcome = parse_cvc5_outcome(&output.stdout)?.to_string();
    if outcome != "unknown" && outcome != entry.expected {
        return Err(format!(
            "cvc5 timeout {timeout_ms} repetition {repetition} {} disagrees with manifest: expected {}, got {outcome}",
            entry.path.display(),
            entry.expected
        ));
    }
    Ok(RunRow {
        timeout_ms,
        repetition,
        path: entry.path.clone(),
        content_hash: entry.content_hash.clone(),
        expected: entry.expected.clone(),
        outcome,
        elapsed_nanos,
        stdout_bytes: output.stdout.len(),
        stdout_sha256: format!("sha256:{}", sha256_hex(&output.stdout)),
    })
}

fn parse_timeouts(value: &str) -> Result<Vec<u32>, String> {
    let mut timeouts = value
        .split(',')
        .map(|part| {
            part.parse::<u32>()
                .map_err(|error| format!("invalid timeout {part:?}: {error}"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    if timeouts.is_empty() || timeouts.contains(&0) {
        return Err("timeouts must be a non-empty list of positive integers".to_string());
    }
    let original_len = timeouts.len();
    timeouts.sort_unstable();
    timeouts.dedup();
    if timeouts.len() != original_len {
        return Err("timeouts must be unique".to_string());
    }
    Ok(timeouts)
}

#[allow(clippy::too_many_lines)]
fn main() -> Result<(), String> {
    let usage = "usage: cvc5_qfbv_timeout_sweep CORPUS_ROOT MANIFEST CVC5 OUT.json \
                 [REPETITIONS] [TIMEOUTS_CSV]";
    let mut args = std::env::args_os().skip(1);
    let root = PathBuf::from(args.next().ok_or(usage)?);
    let manifest_path = PathBuf::from(args.next().ok_or(usage)?);
    let cvc5 = PathBuf::from(args.next().ok_or(usage)?);
    let output = PathBuf::from(args.next().ok_or(usage)?);
    let repetitions = args
        .next()
        .map(|value| value.to_string_lossy().parse::<usize>())
        .transpose()
        .map_err(|error| format!("invalid repetitions: {error}"))?
        .unwrap_or(5);
    let timeouts = args
        .next()
        .map(|value| parse_timeouts(&value.to_string_lossy()))
        .transpose()?
        .unwrap_or_else(|| vec![50, 100, 250, 1_000]);
    if repetitions < 5 || args.next().is_some() {
        return Err(format!("{usage}; repetitions must be at least 5"));
    }

    let canonical_root =
        fs::canonicalize(&root).map_err(|error| format!("resolve {}: {error}", root.display()))?;
    let canonical_manifest = fs::canonicalize(&manifest_path)
        .map_err(|error| format!("resolve {}: {error}", manifest_path.display()))?;
    let canonical_cvc5 =
        fs::canonicalize(&cvc5).map_err(|error| format!("resolve {}: {error}", cvc5.display()))?;
    let binary_bytes = fs::read(&canonical_cvc5)
        .map_err(|error| format!("read {}: {error}", canonical_cvc5.display()))?;
    let version = cvc5_version(&canonical_cvc5)?;
    let manifest = load_manifest(&canonical_root, &canonical_manifest)?;

    let mut rows = Vec::with_capacity(manifest.entries.len() * repetitions * timeouts.len());
    for repetition in 0..repetitions {
        for &timeout_ms in &timeouts {
            for entry in &manifest.entries {
                rows.push(run_one(
                    &canonical_cvc5,
                    &canonical_root,
                    entry,
                    timeout_ms,
                    repetition,
                )?);
            }
        }
    }

    let mut summaries = Vec::new();
    for &timeout_ms in &timeouts {
        for repetition in 0..repetitions {
            let selected = rows
                .iter()
                .filter(|row| row.timeout_ms == timeout_ms && row.repetition == repetition)
                .collect::<Vec<_>>();
            summaries.push(json!({
                "timeout_ms": timeout_ms,
                "repetition": repetition,
                "files": selected.len(),
                "sat": selected.iter().filter(|row| row.outcome == "sat").count(),
                "unsat": selected.iter().filter(|row| row.outcome == "unsat").count(),
                "unknown": selected.iter().filter(|row| row.outcome == "unknown").count(),
                "elapsed_nanos": selected.iter().map(|row| row.elapsed_nanos).sum::<u64>(),
            }));
        }
    }
    let families =
        manifest
            .entries
            .iter()
            .fold(BTreeMap::<String, usize>::new(), |mut counts, entry| {
                *counts.entry(entry.family.clone()).or_default() += 1;
                counts
            });
    let tiers = manifest
        .entries
        .iter()
        .flat_map(|entry| entry.tiers.iter())
        .fold(BTreeMap::<String, usize>::new(), |mut counts, tier| {
            *counts.entry(tier.clone()).or_default() += 1;
            counts
        });
    let report_rows = rows
        .iter()
        .map(|row| {
            json!({
                "timeout_ms": row.timeout_ms,
                "repetition": row.repetition,
                "path": row.path,
                "content_hash": row.content_hash,
                "expected": row.expected,
                "outcome": row.outcome,
                "elapsed_nanos": row.elapsed_nanos,
                "stdout_bytes": row.stdout_bytes,
                "stdout_sha256": row.stdout_sha256,
            })
        })
        .collect::<Vec<_>>();
    let report = json!({
        "schema": SCHEMA,
        "corpus_root": canonical_root,
        "manifest": {
            "path": canonical_manifest,
            "content_hash": manifest.raw_sha256,
            "name": manifest.name,
            "logic": manifest.logic,
            "source": manifest.source,
            "files": manifest.entries.len(),
            "family_counts": families,
            "tier_counts": tiers,
        },
        "cvc5": {
            "path": canonical_cvc5,
            "binary_sha256": format!("sha256:{}", sha256_hex(&binary_bytes)),
            "version": version,
            "arguments": ["--lang=smt2", "--produce-models", "--tlimit-per=<timeout_ms>", "<exact-manifest-file>"],
            "process_boundary": "fresh cvc5 process per exact SMT-LIB file",
            "timing_boundary": "wall time includes process startup, SMT-LIB parsing, solving, and model output",
        },
        "measured_repetitions": repetitions,
        "timeouts_ms": timeouts,
        "summaries": summaries,
        "rows": report_rows,
    });
    fs::write(
        &output,
        serde_json::to_vec_pretty(&report).map_err(|error| error.to_string())?,
    )
    .map_err(|error| format!("write {}: {error}", output.display()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_one_verdict_and_rejects_ambiguous_output() {
        assert_eq!(parse_cvc5_outcome(b"sat\n((x #b0))\n").unwrap(), "sat");
        assert_eq!(
            parse_cvc5_outcome(b"unknown\n((x #b0))\n").unwrap(),
            "unknown"
        );
        assert!(parse_cvc5_outcome(b"success\nsat\n").is_err());
        assert!(parse_cvc5_outcome(b"sat\nunsat\n").is_err());
    }

    #[test]
    fn timeout_list_is_positive_unique_and_sorted() {
        assert_eq!(
            parse_timeouts("250,50,1000,100").unwrap(),
            [50, 100, 250, 1000]
        );
        assert!(parse_timeouts("50,50").is_err());
        assert!(parse_timeouts("0").is_err());
        assert!(parse_timeouts("").is_err());
    }

    #[test]
    fn rejects_parent_and_absolute_manifest_paths() {
        assert!(checked_relative_path("one.smt2").is_ok());
        assert!(checked_relative_path("../one.smt2").is_err());
        assert!(checked_relative_path("/one.smt2").is_err());
    }
}
