//! Replay a hash-bound ordered Glaurung SMT stream through one cvc5 process.
//!
//! Usage: `cvc5_smt_stream_bench TRACE_DIR CVC5 OUT.json [REPETITIONS]
//! [TIMEOUT_MS]`.

use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, OpenOptions};
use std::io::Write as _;
use std::path::{Component, Path, PathBuf};
use std::process::Command;
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const TRACE_SCHEMA: &str = "glaurung-ordered-trace-v1";

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Occurrence {
    check_id: String,
    event_seq: u64,
    path_id: String,
}

struct QueryRecord {
    path: PathBuf,
    occurrences: BTreeSet<Occurrence>,
    outcomes: BTreeSet<String>,
}

struct Check {
    id: String,
    event_seq: u64,
    path_id: String,
    query_sha256: String,
    outcome: String,
    z3_cold_nanos: u64,
    z3_warm_nanos: u64,
    axeyum_cold_nanos: u64,
    axeyum_warm_nanos: u64,
}

struct OrderedStream {
    batch: Vec<u8>,
    checks: Vec<Check>,
    unique_queries: usize,
    expected_sat_models: usize,
    expected_unsat_model_errors: usize,
    events_sha256: String,
    query_index_sha256: String,
    driver_path: String,
    driver_sha256: String,
    source_revision: String,
}

struct RunRow {
    repetition: usize,
    total_nanos: u64,
    stdout_bytes: usize,
    stdout_sha256: String,
    sat: usize,
    unsat: usize,
    unknown: usize,
    model_lines: usize,
    expected_model_errors: usize,
}

struct TempBatch {
    path: PathBuf,
}

impl Drop for TempBatch {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

fn required_str<'a>(value: &'a Value, key: &str) -> Result<&'a str, String> {
    value[key]
        .as_str()
        .ok_or_else(|| format!("missing string field {key}"))
}

fn required_u64(value: &Value, key: &str) -> Result<u64, String> {
    value[key]
        .as_u64()
        .ok_or_else(|| format!("missing integer field {key}"))
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

fn checked_relative_path(value: &str) -> Result<PathBuf, String> {
    let path = Path::new(value);
    if path.is_absolute()
        || path.components().any(|component| {
            matches!(
                component,
                Component::ParentDir | Component::RootDir | Component::Prefix(_)
            )
        })
    {
        return Err(format!("query path is not a safe relative path: {value}"));
    }
    Ok(path.to_path_buf())
}

fn load_manifest(trace_dir: &Path) -> Result<Value, String> {
    let path = trace_dir.join("trace-manifest-v1.json");
    let bytes = fs::read(&path).map_err(|error| format!("read {}: {error}", path.display()))?;
    let value: Value = serde_json::from_slice(&bytes)
        .map_err(|error| format!("parse {}: {error}", path.display()))?;
    if required_str(&value, "schema")? != TRACE_SCHEMA || required_u64(&value, "version")? != 1 {
        return Err(format!("unsupported trace manifest {}", path.display()));
    }
    if value["source"]["dirty"].as_bool() != Some(false)
        || required_str(&value["source"], "status_sha256")?
            != "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    {
        return Err("source trace is not from a clean Glaurung worktree".to_string());
    }
    Ok(value)
}

fn load_query_index(
    trace_dir: &Path,
    expected_sha256: &str,
) -> Result<(BTreeMap<String, QueryRecord>, String), String> {
    let path = trace_dir.join("query-index-v1.json");
    let bytes = fs::read(&path).map_err(|error| format!("read {}: {error}", path.display()))?;
    let actual_sha256 = sha256_hex(&bytes);
    if actual_sha256 != expected_sha256 {
        return Err(format!("query-index hash mismatch at {}", path.display()));
    }
    let value: Value = serde_json::from_slice(&bytes)
        .map_err(|error| format!("parse {}: {error}", path.display()))?;
    if required_u64(&value, "version")? != 1 {
        return Err("unsupported query-index version".to_string());
    }
    let rows = value["queries"]
        .as_array()
        .ok_or_else(|| "query index has no queries array".to_string())?;
    let mut records = BTreeMap::new();
    for row in rows {
        let hash = required_str(row, "content_hash")?.to_string();
        let path = checked_relative_path(required_str(row, "path")?)?;
        let occurrences = row["occurrences"]
            .as_array()
            .ok_or_else(|| format!("query {hash} has no occurrences"))?
            .iter()
            .map(|value| {
                Ok(Occurrence {
                    check_id: required_str(value, "check_id")?.to_string(),
                    event_seq: required_u64(value, "event_seq")?,
                    path_id: required_str(value, "path_id")?.to_string(),
                })
            })
            .collect::<Result<BTreeSet<_>, String>>()?;
        let outcomes = row["outcomes"]
            .as_array()
            .ok_or_else(|| format!("query {hash} has no outcomes"))?
            .iter()
            .map(|value| {
                value
                    .as_str()
                    .map(str::to_string)
                    .ok_or_else(|| format!("query {hash} has a non-string outcome"))
            })
            .collect::<Result<BTreeSet<_>, String>>()?;
        if occurrences.is_empty() || outcomes.is_empty() || records.contains_key(&hash) {
            return Err(format!("invalid or duplicate query-index row {hash}"));
        }
        records.insert(
            hash,
            QueryRecord {
                path,
                occurrences,
                outcomes,
            },
        );
    }
    Ok((records, actual_sha256))
}

fn load_checks(trace_dir: &Path, expected_sha256: &str) -> Result<(Vec<Check>, String), String> {
    let path = trace_dir.join("events-v1.ndjson");
    let bytes = fs::read(&path).map_err(|error| format!("read {}: {error}", path.display()))?;
    let actual_sha256 = sha256_hex(&bytes);
    if actual_sha256 != expected_sha256 {
        return Err(format!("events hash mismatch at {}", path.display()));
    }
    let text = std::str::from_utf8(&bytes)
        .map_err(|error| format!("{} is not UTF-8: {error}", path.display()))?;
    let mut checks = Vec::new();
    for (line_index, line) in text.lines().enumerate() {
        let value: Value = serde_json::from_str(line)
            .map_err(|error| format!("{} line {}: {error}", path.display(), line_index + 1))?;
        if value["event"] != "check" {
            continue;
        }
        let outcome = required_str(&value, "outcome")?.to_string();
        if outcome != "sat" && outcome != "unsat" {
            return Err(format!(
                "nondecided source check at line {}",
                line_index + 1
            ));
        }
        for key in [
            "z3_cold_outcome",
            "z3_warm_outcome",
            "axeyum_cold_outcome",
            "axeyum_warm_outcome",
        ] {
            if required_str(&value, key)? != outcome {
                return Err(format!(
                    "source four-cell disagreement at line {}",
                    line_index + 1
                ));
            }
        }
        checks.push(Check {
            id: required_str(&value, "check_id")?.to_string(),
            event_seq: required_u64(&value, "event_seq")?,
            path_id: required_str(&value, "path_id")?.to_string(),
            query_sha256: required_str(&value, "query_sha256")?.to_string(),
            outcome,
            z3_cold_nanos: required_u64(&value, "z3_cold_nanos")?,
            z3_warm_nanos: required_u64(&value, "z3_warm_nanos")?,
            axeyum_cold_nanos: required_u64(&value, "axeyum_cold_nanos")?,
            axeyum_warm_nanos: required_u64(&value, "axeyum_warm_nanos")?,
        });
    }
    if checks.is_empty()
        || !checks
            .windows(2)
            .all(|pair| pair[0].event_seq < pair[1].event_seq)
    {
        return Err("trace has no checks or non-monotone check order".to_string());
    }
    Ok((checks, actual_sha256))
}

fn validate_script(bytes: &[u8], hash: &str) -> Result<bool, String> {
    if sha256_hex(bytes) != hash {
        return Err(format!("query content hash mismatch for {hash}"));
    }
    let text = std::str::from_utf8(bytes)
        .map_err(|error| format!("query {hash} is not UTF-8: {error}"))?;
    let set_logic = text
        .lines()
        .filter(|line| line.starts_with("(set-logic "))
        .count();
    let checks = text.lines().filter(|line| *line == "(check-sat)").count();
    let get_values = text
        .lines()
        .filter(|line| line.starts_with("(get-value "))
        .count();
    if set_logic != 1
        || checks != 1
        || get_values > 1
        || text
            .lines()
            .any(|line| line == "(reset)" || line == "(exit)")
    {
        return Err(format!(
            "query {hash} violates the single-check script contract"
        ));
    }
    Ok(get_values == 1)
}

fn load_ordered_stream(trace_dir: &Path) -> Result<OrderedStream, String> {
    let manifest = load_manifest(trace_dir)?;
    let expected_index_sha = required_str(&manifest, "query_index_sha256")?;
    let expected_events_sha = required_str(&manifest, "events_sha256")?;
    let (queries, query_index_sha256) = load_query_index(trace_dir, expected_index_sha)?;
    let (checks, events_sha256) = load_checks(trace_dir, expected_events_sha)?;
    if usize::try_from(required_u64(&manifest, "query_count")?)
        .map_err(|_| "query count exceeds usize".to_string())?
        != queries.len()
        || usize::try_from(required_u64(
            &manifest["native_replay"],
            "warm_check_count",
        )?)
        .map_err(|_| "check count exceeds usize".to_string())?
            != checks.len()
    {
        return Err("manifest/query/check cardinality mismatch".to_string());
    }

    let mut cached_scripts = BTreeMap::<String, (Vec<u8>, bool)>::new();
    let mut batch = Vec::new();
    let mut expected_sat_models = 0_usize;
    let mut expected_unsat_model_errors = 0_usize;
    for check in &checks {
        let query = queries
            .get(&check.query_sha256)
            .ok_or_else(|| format!("check {} missing from query index", check.id))?;
        let occurrence = Occurrence {
            check_id: check.id.clone(),
            event_seq: check.event_seq,
            path_id: check.path_id.clone(),
        };
        if !query.occurrences.contains(&occurrence) || !query.outcomes.contains(&check.outcome) {
            return Err(format!("query-index identity mismatch at {}", check.id));
        }
        if !cached_scripts.contains_key(&check.query_sha256) {
            let path = trace_dir.join(&query.path);
            let bytes =
                fs::read(&path).map_err(|error| format!("read {}: {error}", path.display()))?;
            let has_get_value = validate_script(&bytes, &check.query_sha256)?;
            cached_scripts.insert(check.query_sha256.clone(), (bytes, has_get_value));
        }
        let (script, has_get_value) = cached_scripts
            .get(&check.query_sha256)
            .expect("script was cached above");
        batch.extend_from_slice(script);
        if !script.ends_with(b"\n") {
            batch.push(b'\n');
        }
        batch.extend_from_slice(b"(reset)\n");
        if *has_get_value {
            if check.outcome == "sat" {
                expected_sat_models += 1;
            } else {
                expected_unsat_model_errors += 1;
            }
        }
    }
    batch.extend_from_slice(b"(exit)\n");

    Ok(OrderedStream {
        batch,
        checks,
        unique_queries: queries.len(),
        expected_sat_models,
        expected_unsat_model_errors,
        events_sha256,
        query_index_sha256,
        driver_path: required_str(&manifest["driver"], "path")?.to_string(),
        driver_sha256: required_str(&manifest["driver"], "sha256")?.to_string(),
        source_revision: required_str(&manifest["source"], "revision")?.to_string(),
    })
}

fn create_temp_batch(bytes: &[u8]) -> Result<TempBatch, String> {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|error| error.to_string())?
        .as_nanos();
    let path = std::env::temp_dir().join(format!(
        "axeyum-cvc5-smt-stream-{}-{nonce}.smt2",
        std::process::id()
    ));
    let mut file = OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(&path)
        .map_err(|error| format!("create {}: {error}", path.display()))?;
    file.write_all(bytes)
        .map_err(|error| format!("write {}: {error}", path.display()))?;
    Ok(TempBatch { path })
}

fn cvc5_version(binary: &Path) -> Result<String, String> {
    let output = Command::new(binary)
        .arg("--version")
        .output()
        .map_err(|error| format!("run {} --version: {error}", binary.display()))?;
    if !output.status.success() {
        return Err(format!("{} --version failed", binary.display()));
    }
    let stdout = String::from_utf8(output.stdout)
        .map_err(|error| format!("cvc5 version output is not UTF-8: {error}"))?;
    let version = stdout.lines().next().unwrap_or("").trim();
    if !version.starts_with("cvc5 ") {
        return Err(format!("unexpected cvc5 version output: {version:?}"));
    }
    Ok(version.to_string())
}

fn run_cvc5(
    binary: &Path,
    batch: &Path,
    stream: &OrderedStream,
    timeout_ms: u32,
    repetition: usize,
) -> Result<RunRow, String> {
    let started = Instant::now();
    let output = Command::new(binary)
        .arg("--lang=smt2")
        .arg("--incremental")
        .arg("--produce-models")
        .arg(format!("--tlimit-per={timeout_ms}"))
        .arg(batch)
        .output()
        .map_err(|error| format!("run {}: {error}", binary.display()))?;
    let total_nanos = u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX);
    if !output.status.success() {
        return Err(format!(
            "cvc5 repetition {repetition} exited {}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    if !output.stderr.is_empty() {
        return Err(format!(
            "cvc5 repetition {repetition} wrote stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    let stdout = std::str::from_utf8(&output.stdout)
        .map_err(|error| format!("cvc5 stdout is not UTF-8: {error}"))?;
    let mut outcomes = Vec::new();
    let mut model_lines = 0_usize;
    let mut expected_model_errors = 0_usize;
    for line in stdout.lines() {
        match line.trim() {
            "sat" | "unsat" | "unknown" => outcomes.push(line.trim()),
            value if value.starts_with("((") => model_lines += 1,
            "(error \"cannot get value unless after a SAT or UNKNOWN response.\")" => {
                expected_model_errors += 1;
            }
            "" => {}
            other => {
                return Err(format!(
                    "unexpected cvc5 stdout at repetition {repetition}: {other:?}"
                ));
            }
        }
    }
    if outcomes.len() != stream.checks.len() {
        return Err(format!(
            "cvc5 repetition {repetition} produced {} outcomes for {} checks",
            outcomes.len(),
            stream.checks.len()
        ));
    }
    for (check, actual) in stream.checks.iter().zip(&outcomes) {
        if check.outcome != *actual {
            return Err(format!(
                "cvc5 verdict mismatch at repetition {repetition}, {}: expected {}, got {actual}",
                check.id, check.outcome
            ));
        }
    }
    if model_lines != stream.expected_sat_models
        || expected_model_errors != stream.expected_unsat_model_errors
    {
        return Err(format!(
            "cvc5 model-output mismatch at repetition {repetition}: models {model_lines}/{}, expected errors {expected_model_errors}/{}",
            stream.expected_sat_models, stream.expected_unsat_model_errors
        ));
    }
    Ok(RunRow {
        repetition,
        total_nanos,
        stdout_bytes: output.stdout.len(),
        stdout_sha256: sha256_hex(&output.stdout),
        sat: outcomes.iter().filter(|&&value| value == "sat").count(),
        unsat: outcomes.iter().filter(|&&value| value == "unsat").count(),
        unknown: outcomes.iter().filter(|&&value| value == "unknown").count(),
        model_lines,
        expected_model_errors,
    })
}

fn source_cell_sums(checks: &[Check]) -> Value {
    json!({
        "z3_cold_nanos": checks.iter().map(|check| check.z3_cold_nanos).sum::<u64>(),
        "z3_warm_nanos": checks.iter().map(|check| check.z3_warm_nanos).sum::<u64>(),
        "axeyum_cold_nanos": checks.iter().map(|check| check.axeyum_cold_nanos).sum::<u64>(),
        "axeyum_warm_nanos": checks.iter().map(|check| check.axeyum_warm_nanos).sum::<u64>(),
    })
}

// Keeping argument validation, provenance capture, execution, and report
// assembly together makes this one-purpose artifact runner easier to audit.
#[allow(clippy::too_many_lines)]
fn main() -> Result<(), String> {
    let usage = "usage: cvc5_smt_stream_bench TRACE_DIR CVC5 OUT.json [REPETITIONS] [TIMEOUT_MS]";
    let mut args = std::env::args_os().skip(1);
    let trace_dir = PathBuf::from(args.next().ok_or(usage)?);
    let cvc5 = PathBuf::from(args.next().ok_or(usage)?);
    let output = PathBuf::from(args.next().ok_or(usage)?);
    let repetitions = args
        .next()
        .map(|value| value.to_string_lossy().parse::<usize>())
        .transpose()
        .map_err(|error| format!("invalid repetitions: {error}"))?
        .unwrap_or(5);
    let timeout_ms = args
        .next()
        .map(|value| value.to_string_lossy().parse::<u32>())
        .transpose()
        .map_err(|error| format!("invalid timeout: {error}"))?
        .unwrap_or(250);
    if repetitions == 0 || timeout_ms == 0 || args.next().is_some() {
        return Err(usage.to_string());
    }

    let canonical_cvc5 =
        fs::canonicalize(&cvc5).map_err(|error| format!("resolve {}: {error}", cvc5.display()))?;
    let binary_bytes = fs::read(&canonical_cvc5)
        .map_err(|error| format!("read {}: {error}", canonical_cvc5.display()))?;
    let version = cvc5_version(&canonical_cvc5)?;
    let stream = load_ordered_stream(&trace_dir)?;
    let batch_sha256 = sha256_hex(&stream.batch);
    let batch = create_temp_batch(&stream.batch)?;

    // One unreported warm-up faults in the binary and validates the complete
    // stream before the fixed measured repetition schedule.
    run_cvc5(
        &canonical_cvc5,
        &batch.path,
        &stream,
        timeout_ms,
        usize::MAX,
    )?;
    let mut rows = Vec::with_capacity(repetitions);
    for repetition in 0..repetitions {
        rows.push(run_cvc5(
            &canonical_cvc5,
            &batch.path,
            &stream,
            timeout_ms,
            repetition,
        )?);
    }
    let mut totals = rows.iter().map(|row| row.total_nanos).collect::<Vec<_>>();
    totals.sort_unstable();
    let median_total_nanos = totals[totals.len() / 2];
    let report_rows = rows
        .iter()
        .map(|row| {
            json!({
                "repetition": row.repetition,
                "total_nanos": row.total_nanos,
                "stdout_bytes": row.stdout_bytes,
                "stdout_sha256": row.stdout_sha256,
                "sat": row.sat,
                "unsat": row.unsat,
                "unknown": row.unknown,
                "model_lines": row.model_lines,
                "expected_unsat_model_errors": row.expected_model_errors,
            })
        })
        .collect::<Vec<_>>();
    let report = json!({
        "schema": "axeyum-ordered-smt-stream-cvc5-benchmark-v1",
        "trace_directory": trace_dir,
        "trace": {
            "schema": TRACE_SCHEMA,
            "events_sha256": stream.events_sha256,
            "query_index_sha256": stream.query_index_sha256,
            "source_revision": stream.source_revision,
            "driver_path": stream.driver_path,
            "driver_sha256": stream.driver_sha256,
            "checks": stream.checks.len(),
            "unique_queries": stream.unique_queries,
            "sat": stream.checks.iter().filter(|check| check.outcome == "sat").count(),
            "unsat": stream.checks.iter().filter(|check| check.outcome == "unsat").count(),
            "expected_sat_models": stream.expected_sat_models,
            "expected_unsat_model_errors": stream.expected_unsat_model_errors,
            "source_cell_sums": source_cell_sums(&stream.checks),
        },
        "batch": {
            "sha256": batch_sha256,
            "bytes": stream.batch.len(),
            "policy": "exact ordered standalone scripts; full reset after every check; one process per repetition",
        },
        "cvc5": {
            "path": canonical_cvc5,
            "binary_sha256": sha256_hex(&binary_bytes),
            "version": version,
            "arguments": ["--lang=smt2", "--incremental", "--produce-models", format!("--tlimit-per={timeout_ms}")],
        },
        "warmup_repetitions": 1,
        "measured_repetitions": repetitions,
        "median_total_nanos": median_total_nanos,
        "rows": report_rows,
    });
    fs::write(
        &output,
        serde_json::to_vec_pretty(&report).map_err(|error| error.to_string())?,
    )
    .map_err(|error| format!("write {}: {error}", output.display()))
}
