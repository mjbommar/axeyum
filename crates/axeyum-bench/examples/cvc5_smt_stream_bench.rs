//! Replay a hash-bound ordered Glaurung SMT stream through one cvc5 process.
//!
//! Usage: `cvc5_smt_stream_bench TRACE_DIR CVC5 OUT.json [REPETITIONS]
//! [TIMEOUT_MS] [cold-reset|retained-lcp]`.

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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum StreamPolicy {
    ColdReset,
    RetainedLcp,
}

impl StreamPolicy {
    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "cold-reset" => Ok(Self::ColdReset),
            "retained-lcp" => Ok(Self::RetainedLcp),
            _ => Err(format!("unknown stream policy {value:?}")),
        }
    }

    const fn name(self) -> &'static str {
        match self {
            Self::ColdReset => "cold-reset",
            Self::RetainedLcp => "retained-lcp",
        }
    }
}

#[derive(Clone, Debug)]
struct ParsedScript {
    bytes: Vec<u8>,
    declarations: Vec<(String, Vec<u8>)>,
    assertions: Vec<Vec<u8>>,
    get_value: Option<Vec<u8>>,
}

#[derive(Clone, Debug, Default)]
struct TransitionStats {
    declaration_count: usize,
    declaration_emissions: usize,
    owner_sessions: usize,
    owner_resets: usize,
    assertion_occurrences: usize,
    retained_assertion_occurrences: usize,
    requested_retained_assertion_occurrences: usize,
    temporary_assumption_occurrences: usize,
    pushed_assertions: usize,
    popped_assertions: usize,
    checks_with_retained_prefix: usize,
    checks_rewound_below_requested: usize,
    assertions_rewound_below_requested: usize,
    max_requested_minus_actual: usize,
    checks_retained_above_requested: usize,
    assertions_retained_above_requested: usize,
    max_actual_minus_requested: usize,
    unchanged_snapshots: usize,
    peak_assertion_depth: usize,
}

#[derive(Clone, Copy, Debug)]
struct RetentionBoundary {
    owner_id: u64,
    active: usize,
    requested: usize,
    persistent: usize,
    temporary: usize,
}

#[derive(Default)]
struct OwnerSessionState {
    current: Option<u64>,
    closed: BTreeSet<u64>,
    active: Vec<Vec<u8>>,
}

impl OwnerSessionState {
    fn enter(
        &mut self,
        owner_id: u64,
        batch: &mut Vec<u8>,
        declarations: &BTreeMap<String, Vec<u8>>,
        stats: &mut TransitionStats,
    ) -> Result<(), String> {
        if self.current == Some(owner_id) {
            return Ok(());
        }
        if self.closed.contains(&owner_id) {
            return Err(format!(
                "warm owner {owner_id} reappears after its solver session was reset"
            ));
        }
        if let Some(prior) = self.current.replace(owner_id) {
            self.closed.insert(prior);
            batch.extend_from_slice(b"(reset)\n");
            stats.owner_resets += 1;
        }
        append_declaration_prelude(batch, declarations);
        stats.owner_sessions += 1;
        stats.declaration_emissions = stats
            .declaration_emissions
            .saturating_add(declarations.len());
        self.active.clear();
        Ok(())
    }
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
    active_constraint_count: usize,
    requested_retain_assertions: usize,
    persistent_assertions: usize,
    temporary_assertions: usize,
    owner_id: u64,
}

struct OrderedStream {
    batch: Vec<u8>,
    policy: StreamPolicy,
    transition_stats: TransitionStats,
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

fn required_usize(value: &Value, key: &str) -> Result<usize, String> {
    usize::try_from(required_u64(value, key)?)
        .map_err(|_| format!("integer field {key} exceeds usize"))
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
        if value["warm_replay"]["synchronized"].as_bool() != Some(true) {
            return Err(format!(
                "source warm replay is not synchronized at line {}",
                line_index + 1
            ));
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
            active_constraint_count: required_usize(&value, "active_constraint_count")?,
            requested_retain_assertions: required_usize(
                &value["warm_replay"],
                "requested_retain_assertions",
            )?,
            persistent_assertions: required_usize(&value["warm_replay"], "persistent_assertions")?,
            temporary_assertions: required_usize(&value["warm_replay"], "temporary_assertions")?,
            owner_id: required_u64(&value["warm_replay"], "owner_id")?,
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

fn parse_declaration_name(line: &str, hash: &str) -> Result<String, String> {
    let rest = line
        .strip_prefix("(declare-const ")
        .ok_or_else(|| format!("query {hash} has an unsupported declaration"))?;
    let name = rest
        .split_whitespace()
        .next()
        .ok_or_else(|| format!("query {hash} has an empty declaration"))?;
    if name.is_empty() || name.contains(['(', ')']) {
        return Err(format!("query {hash} has an invalid declaration name"));
    }
    Ok(name.to_string())
}

fn parse_script(bytes: &[u8], hash: &str) -> Result<ParsedScript, String> {
    if sha256_hex(bytes) != hash {
        return Err(format!("query content hash mismatch for {hash}"));
    }
    let text = std::str::from_utf8(bytes)
        .map_err(|error| format!("query {hash} is not UTF-8: {error}"))?;
    let mut set_logic = 0_usize;
    let mut checks = 0_usize;
    let mut declarations = Vec::new();
    let mut assertions = Vec::new();
    let mut get_value = None;
    for line in text.lines() {
        if line == "(set-logic QF_BV)"
            && set_logic == 0
            && declarations.is_empty()
            && assertions.is_empty()
            && checks == 0
        {
            set_logic += 1;
        } else if line.starts_with("(declare-const ")
            && set_logic == 1
            && assertions.is_empty()
            && checks == 0
        {
            declarations.push((
                parse_declaration_name(line, hash)?,
                line.as_bytes().to_vec(),
            ));
        } else if line.starts_with("(assert ") && set_logic == 1 && checks == 0 {
            assertions.push(line.as_bytes().to_vec());
        } else if line == "(check-sat)" && set_logic == 1 && checks == 0 {
            checks += 1;
        } else if line.starts_with("(get-value ") && checks == 1 && get_value.is_none() {
            get_value = Some(line.as_bytes().to_vec());
        } else if !line.is_empty() {
            return Err(format!(
                "query {hash} has an unsupported or duplicate command: {line:?}"
            ));
        }
    }
    if set_logic != 1 || checks != 1 {
        return Err(format!(
            "query {hash} violates the single-check script contract"
        ));
    }
    Ok(ParsedScript {
        bytes: bytes.to_vec(),
        declarations,
        assertions,
        get_value,
    })
}

fn append_line(batch: &mut Vec<u8>, line: &[u8]) {
    batch.extend_from_slice(line);
    batch.push(b'\n');
}

fn assertion_term(assertion: &[u8]) -> Result<&[u8], String> {
    assertion
        .strip_prefix(b"(assert ")
        .and_then(|rest| rest.strip_suffix(b")"))
        .ok_or_else(|| "captured assertion does not have one outer assert command".to_string())
}

fn append_check_command(batch: &mut Vec<u8>, temporary: &[Vec<u8>]) -> Result<(), String> {
    if temporary.is_empty() {
        batch.extend_from_slice(b"(check-sat)\n");
        return Ok(());
    }
    batch.extend_from_slice(b"(check-sat-assuming (");
    for (index, assertion) in temporary.iter().enumerate() {
        if index > 0 {
            batch.push(b' ');
        }
        batch.extend_from_slice(assertion_term(assertion)?);
    }
    batch.extend_from_slice(b"))\n");
    Ok(())
}

fn collect_declarations(scripts: &[&ParsedScript]) -> Result<BTreeMap<String, Vec<u8>>, String> {
    let mut declarations = BTreeMap::<String, Vec<u8>>::new();
    for script in scripts {
        for (name, declaration) in &script.declarations {
            if declarations
                .insert(name.clone(), declaration.clone())
                .is_some_and(|prior| prior != *declaration)
            {
                return Err(format!(
                    "symbol {name} has inconsistent declarations in the ordered stream"
                ));
            }
        }
    }
    Ok(declarations)
}

fn append_declaration_prelude(batch: &mut Vec<u8>, declarations: &BTreeMap<String, Vec<u8>>) {
    batch.extend_from_slice(b"(set-logic QF_BV)\n");
    for declaration in declarations.values() {
        append_line(batch, declaration);
    }
}

fn build_cold_reset_batch(scripts: &[&ParsedScript]) -> Vec<u8> {
    let mut batch = Vec::new();
    for script in scripts {
        batch.extend_from_slice(&script.bytes);
        if !script.bytes.ends_with(b"\n") {
            batch.push(b'\n');
        }
        batch.extend_from_slice(b"(reset)\n");
    }
    batch.extend_from_slice(b"(exit)\n");
    batch
}

fn build_retained_lcp_batch(
    scripts: &[&ParsedScript],
    boundaries: &[RetentionBoundary],
) -> Result<(Vec<u8>, TransitionStats), String> {
    if scripts.len() != boundaries.len() {
        return Err("ordered script/retention-boundary cardinality mismatch".to_string());
    }
    let declarations = collect_declarations(scripts)?;

    let mut batch = Vec::new();
    let mut stats = TransitionStats {
        declaration_count: declarations.len(),
        ..TransitionStats::default()
    };
    let mut owner = OwnerSessionState::default();
    for (script, boundary) in scripts.iter().zip(boundaries) {
        owner.enter(boundary.owner_id, &mut batch, &declarations, &mut stats)?;
        let partition = boundary
            .persistent
            .checked_add(boundary.temporary)
            .ok_or_else(|| "source retention partition overflows usize".to_string())?;
        if script.assertions.len() != boundary.active
            || partition != boundary.active
            || boundary.requested > boundary.persistent
        {
            return Err(format!(
                "source retention boundary mismatch: query {}, active {}, persistent {} + \
                 temporary {}, requested {}",
                script.assertions.len(),
                boundary.active,
                boundary.persistent,
                boundary.temporary,
                boundary.requested,
            ));
        }
        let (persistent, temporary) = script.assertions.split_at(boundary.persistent);
        let prefix = owner
            .active
            .iter()
            .zip(persistent)
            .take_while(|(left, right)| left == right)
            .count();
        stats.assertion_occurrences = stats
            .assertion_occurrences
            .saturating_add(script.assertions.len());
        stats.retained_assertion_occurrences =
            stats.retained_assertion_occurrences.saturating_add(prefix);
        stats.requested_retained_assertion_occurrences = stats
            .requested_retained_assertion_occurrences
            .saturating_add(boundary.requested);
        stats.temporary_assumption_occurrences = stats
            .temporary_assumption_occurrences
            .saturating_add(boundary.temporary);
        let rewind = boundary.requested.saturating_sub(prefix);
        if rewind > 0 {
            stats.checks_rewound_below_requested += 1;
            stats.assertions_rewound_below_requested = stats
                .assertions_rewound_below_requested
                .saturating_add(rewind);
            stats.max_requested_minus_actual = stats.max_requested_minus_actual.max(rewind);
        }
        let advance = prefix.saturating_sub(boundary.requested);
        if advance > 0 {
            stats.checks_retained_above_requested += 1;
            stats.assertions_retained_above_requested = stats
                .assertions_retained_above_requested
                .saturating_add(advance);
            stats.max_actual_minus_requested = stats.max_actual_minus_requested.max(advance);
        }
        if prefix > 0 {
            stats.checks_with_retained_prefix += 1;
        }
        if prefix == owner.active.len() && prefix == persistent.len() && temporary.is_empty() {
            stats.unchanged_snapshots += 1;
        }

        let pops = owner.active.len().saturating_sub(prefix);
        for _ in 0..pops {
            batch.extend_from_slice(b"(pop 1)\n");
        }
        stats.popped_assertions = stats.popped_assertions.saturating_add(pops);
        owner.active.truncate(prefix);

        for assertion in &persistent[prefix..] {
            batch.extend_from_slice(b"(push 1)\n");
            append_line(&mut batch, assertion);
            owner.active.push(assertion.clone());
            stats.pushed_assertions += 1;
        }
        stats.peak_assertion_depth = stats.peak_assertion_depth.max(owner.active.len());
        append_check_command(&mut batch, temporary)?;
        if let Some(get_value) = &script.get_value {
            append_line(&mut batch, get_value);
        }
    }
    batch.extend_from_slice(b"(exit)\n");
    Ok((batch, stats))
}

fn load_ordered_stream(trace_dir: &Path, policy: StreamPolicy) -> Result<OrderedStream, String> {
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

    let mut cached_scripts = BTreeMap::<String, ParsedScript>::new();
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
            let script = parse_script(&bytes, &check.query_sha256)?;
            cached_scripts.insert(check.query_sha256.clone(), script);
        }
        let script = cached_scripts
            .get(&check.query_sha256)
            .expect("script was cached above");
        if script.get_value.is_some() {
            if check.outcome == "sat" {
                expected_sat_models += 1;
            } else {
                expected_unsat_model_errors += 1;
            }
        }
    }

    let ordered_scripts = checks
        .iter()
        .map(|check| {
            cached_scripts
                .get(&check.query_sha256)
                .expect("every check script was cached above")
        })
        .collect::<Vec<_>>();
    let retention_boundaries = checks
        .iter()
        .map(|check| RetentionBoundary {
            owner_id: check.owner_id,
            active: check.active_constraint_count,
            requested: check.requested_retain_assertions,
            persistent: check.persistent_assertions,
            temporary: check.temporary_assertions,
        })
        .collect::<Vec<_>>();
    let (batch, transition_stats) = match policy {
        StreamPolicy::ColdReset => (
            build_cold_reset_batch(&ordered_scripts),
            TransitionStats::default(),
        ),
        StreamPolicy::RetainedLcp => {
            build_retained_lcp_batch(&ordered_scripts, &retention_boundaries)?
        }
    };

    Ok(OrderedStream {
        batch,
        policy,
        transition_stats,
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
    let usage = "usage: cvc5_smt_stream_bench TRACE_DIR CVC5 OUT.json [REPETITIONS] \
                 [TIMEOUT_MS] [cold-reset|retained-lcp]";
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
    let policy = args
        .next()
        .map(|value| StreamPolicy::parse(&value.to_string_lossy()))
        .transpose()?
        .unwrap_or(StreamPolicy::ColdReset);
    if repetitions == 0 || timeout_ms == 0 || args.next().is_some() {
        return Err(usage.to_string());
    }

    let canonical_cvc5 =
        fs::canonicalize(&cvc5).map_err(|error| format!("resolve {}: {error}", cvc5.display()))?;
    let binary_bytes = fs::read(&canonical_cvc5)
        .map_err(|error| format!("read {}: {error}", canonical_cvc5.display()))?;
    let version = cvc5_version(&canonical_cvc5)?;
    let stream = load_ordered_stream(&trace_dir, policy)?;
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
    let transition_stats = &stream.transition_stats;
    let report = json!({
        "schema": if stream.policy == StreamPolicy::ColdReset {
            "axeyum-ordered-smt-stream-cvc5-benchmark-v1"
        } else {
            "axeyum-ordered-smt-stream-cvc5-benchmark-v2"
        },
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
            "policy": stream.policy.name(),
            "process_boundary": "one cvc5 process per repetition",
            "state_boundary": match stream.policy {
                StreamPolicy::ColdReset => "full reset after every exact standalone script",
                StreamPolicy::RetainedLcp => "one solver session/declaration prelude per contiguous source owner; persistent-prefix LCP push/pop transitions; temporary suffix via check-sat-assuming",
            },
            "transition_stats": if stream.policy == StreamPolicy::RetainedLcp {
                Some(json!({
                    "declaration_count": transition_stats.declaration_count,
                    "declaration_emissions": transition_stats.declaration_emissions,
                    "owner_sessions": transition_stats.owner_sessions,
                    "owner_resets": transition_stats.owner_resets,
                    "assertion_occurrences": transition_stats.assertion_occurrences,
                    "retained_assertion_occurrences": transition_stats.retained_assertion_occurrences,
                    "requested_retained_assertion_occurrences": transition_stats.requested_retained_assertion_occurrences,
                    "temporary_assumption_occurrences": transition_stats.temporary_assumption_occurrences,
                    "pushed_assertions": transition_stats.pushed_assertions,
                    "popped_assertions": transition_stats.popped_assertions,
                    "checks_with_retained_prefix": transition_stats.checks_with_retained_prefix,
                    "checks_rewound_below_requested": transition_stats.checks_rewound_below_requested,
                    "assertions_rewound_below_requested": transition_stats.assertions_rewound_below_requested,
                    "max_requested_minus_actual": transition_stats.max_requested_minus_actual,
                    "checks_retained_above_requested": transition_stats.checks_retained_above_requested,
                    "assertions_retained_above_requested": transition_stats.assertions_retained_above_requested,
                    "max_actual_minus_requested": transition_stats.max_actual_minus_requested,
                    "unchanged_snapshots": transition_stats.unchanged_snapshots,
                    "peak_assertion_depth": transition_stats.peak_assertion_depth,
                }))
            } else {
                None
            },
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

#[cfg(test)]
mod tests {
    use super::*;

    fn script(declaration: &[u8], assertions: &[&[u8]], get_value: bool) -> ParsedScript {
        ParsedScript {
            bytes: Vec::new(),
            declarations: vec![("x".to_string(), declaration.to_vec())],
            assertions: assertions.iter().map(|value| value.to_vec()).collect(),
            get_value: get_value.then(|| b"(get-value (x))".to_vec()),
        }
    }

    #[test]
    fn parses_empty_assertion_snapshot_in_command_order() {
        let bytes =
            b"(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n(check-sat)\n(get-value (x))\n";
        let parsed = parse_script(bytes, &sha256_hex(bytes)).expect("valid script");
        assert!(parsed.assertions.is_empty());
        assert_eq!(parsed.declarations.len(), 1);
        assert_eq!(parsed.get_value.as_deref(), Some(&b"(get-value (x))"[..]));

        let out_of_order = b"(set-logic QF_BV)\n(check-sat)\n(assert true)\n";
        assert!(parse_script(out_of_order, &sha256_hex(out_of_order)).is_err());
    }

    #[test]
    fn retained_lcp_batch_scopes_only_the_changed_suffix() {
        let declaration = b"(declare-const x (_ BitVec 8))";
        let first = script(declaration, &[b"(assert a)", b"(assert b)"], false);
        let second = script(declaration, &[b"(assert a)", b"(assert c)"], true);
        let third = script(declaration, &[b"(assert a)", b"(assert c)"], true);
        let scripts = [&first, &second, &third];
        let boundaries = [
            RetentionBoundary {
                owner_id: 7,
                active: 2,
                requested: 0,
                persistent: 1,
                temporary: 1,
            },
            RetentionBoundary {
                owner_id: 7,
                active: 2,
                requested: 1,
                persistent: 2,
                temporary: 0,
            },
            RetentionBoundary {
                owner_id: 7,
                active: 2,
                requested: 2,
                persistent: 2,
                temporary: 0,
            },
        ];
        let (batch, stats) =
            build_retained_lcp_batch(&scripts, &boundaries).expect("consistent stream");
        let text = String::from_utf8(batch).expect("ASCII batch");

        assert_eq!(text.matches("(push 1)\n").count(), 2);
        assert_eq!(text.matches("(pop 1)\n").count(), 0);
        assert_eq!(text.matches("(check-sat)\n").count(), 2);
        assert!(text.contains("(check-sat-assuming (b))\n"));
        assert_eq!(text.matches("(declare-const x ").count(), 1);
        assert_eq!(stats.declaration_count, 1);
        assert_eq!(stats.declaration_emissions, 1);
        assert_eq!(stats.owner_sessions, 1);
        assert_eq!(stats.owner_resets, 0);
        assert_eq!(stats.assertion_occurrences, 6);
        assert_eq!(stats.retained_assertion_occurrences, 3);
        assert_eq!(stats.requested_retained_assertion_occurrences, 3);
        assert_eq!(stats.temporary_assumption_occurrences, 1);
        assert_eq!(stats.pushed_assertions, 2);
        assert_eq!(stats.popped_assertions, 0);
        assert_eq!(stats.checks_with_retained_prefix, 2);
        assert_eq!(stats.unchanged_snapshots, 1);
        assert_eq!(stats.peak_assertion_depth, 2);
    }

    #[test]
    fn retained_lcp_batch_rejects_conflicting_symbol_sorts() {
        let left = script(b"(declare-const x (_ BitVec 8))", &[], false);
        let right = script(b"(declare-const x (_ BitVec 16))", &[], false);
        let boundaries = [RetentionBoundary {
            owner_id: 7,
            active: 0,
            requested: 0,
            persistent: 0,
            temporary: 0,
        }; 2];
        assert!(build_retained_lcp_batch(&[&left, &right], &boundaries).is_err());
    }

    #[test]
    fn retained_lcp_batch_rejects_owner_reentry_after_reset() {
        let declaration = b"(declare-const x (_ BitVec 8))";
        let script = script(declaration, &[], false);
        let boundary = |owner_id| RetentionBoundary {
            owner_id,
            active: 0,
            requested: 0,
            persistent: 0,
            temporary: 0,
        };
        assert!(
            build_retained_lcp_batch(
                &[&script, &script, &script],
                &[boundary(7), boundary(8), boundary(7)],
            )
            .is_err()
        );
    }
}
