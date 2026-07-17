//! Independent Axeyum validator/replayer for Glaurung ordered trace v1.
//!
//! The producer artifact is untrusted input. This tool reconstructs its path
//! scopes, verifies exact query bytes, parses every unique script through
//! Axeyum's typed SMT-LIB front end, re-solves every recorded decided outcome,
//! and proves each exploration-driving model choice remains satisfiable when
//! asserted against the exact query that produced it.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::time::{Duration, Instant};

use axeyum_ir::{TermArena, TermId, Value as IrValue, eval};
use axeyum_smtlib::{ScriptCommand, parse_script};
use axeyum_solver::{CheckResult, IncrementalBvSolver, Model, SolverConfig, solve_smtlib};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const TRACE_SCHEMA: &str = "glaurung-ordered-trace-v1";
const REPLAY_SCHEMA: &str = "axeyum-glaurung-ordered-trace-replay-v1";
const VALIDATION_WORKER_SCHEMA: &str = "axeyum-glaurung-query-validation-worker-v1";

fn main() -> ExitCode {
    match run() {
        Ok(summary) => {
            if summary["schema"] == VALIDATION_WORKER_SCHEMA {
                println!(
                    "{}",
                    serde_json::to_string(&summary)
                        .expect("validation worker summary is serializable")
                );
                return ExitCode::SUCCESS;
            }
            println!(
                "ordered trace replay valid: events={} paths={} checks={} unique_queries={} \
                 duplicate_occurrences={} choices={}",
                summary["events"],
                summary["paths"],
                summary["checks"],
                summary["unique_queries"],
                summary["exact_duplicate_occurrences"],
                summary["model_choices"],
            );
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("ordered trace replay INVALID: {error}");
            ExitCode::FAILURE
        }
    }
}

// Keeping the three independently checked replay phases together makes it hard
// to accidentally publish a warm result without the cold-query/choice checks.
#[allow(clippy::too_many_lines)]
fn run() -> Result<Value, String> {
    let options = Options::parse(env::args().skip(1))?;
    let executable = env::current_exe()
        .map_err(|error| format!("resolve current replay executable: {error}"))?;
    let executable_sha256 = sha256(read(&executable)?);
    let started = Instant::now();
    let config = SolverConfig::new()
        .with_preprocess(false)
        .with_timeout(Duration::from_millis(options.timeout_ms));
    if let Some((start, end)) = options.validation_worker {
        return run_query_validation_worker(&options.trace, &config, start, end);
    }
    let validated = validate_queries_with_workers(&options.trace, options.timeout_ms, &executable)?;
    let trace = Trace::load(&options.trace, &validated)?;

    let choice_started = Instant::now();
    let mut unique_choices = BTreeSet::new();
    for read in trace.model_reads.values() {
        let check = trace
            .checks
            .get(&read.check_id)
            .ok_or_else(|| format!("model read {} references missing check", read.read_id))?;
        if check.outcome != "sat" {
            return Err(format!(
                "model read {} references non-SAT check {}",
                read.read_id, read.check_id
            ));
        }
        let key = (
            check.query_hash.clone(),
            read.expression_id.clone(),
            read.returned_value,
        );
        if !unique_choices.insert(key) {
            continue;
        }
        let query = trace
            .queries
            .get(&check.query_hash)
            .ok_or_else(|| format!("check {} query is missing", check.check_id))?;
        let query_bytes = query.read_bytes()?;
        let constrained = append_choice_assertion(&query_bytes, read)?;
        validate_qf_bv_script(&format!("choice:{}", read.read_id), constrained.as_bytes())?;
        let outcome = solve_text(constrained.as_bytes(), &config)
            .map_err(|error| format!("model choice {}: {error}", read.read_id))?;
        if outcome != "sat" {
            return Err(format!(
                "model choice {} is not satisfiable under check {}: Axeyum {outcome}",
                read.read_id, read.check_id
            ));
        }
    }
    let choice_replay_nanos = nanos(choice_started.elapsed());
    let policy_config = options.policy_timeout_ms.map_or_else(
        || config.clone(),
        |timeout_ms| {
            SolverConfig::new()
                .with_preprocess(false)
                .with_timeout(Duration::from_millis(timeout_ms))
        },
    );
    let allow_policy_nondecisions = options.policy_timeout_ms.is_some();
    let cold_occurrence_replay = options
        .cold_occurrences
        .then(|| replay_cold_occurrences(&trace, &config))
        .transpose()?;
    let snapshot_replay = options
        .snapshot
        .then(|| {
            replay_snapshot_trace(
                &trace,
                &policy_config,
                allow_policy_nondecisions,
                options.unknown_policy.enabled(),
            )
        })
        .transpose()?;
    let warm_replay = options
        .lineage
        .then(|| {
            replay_warm_trace(
                &trace,
                &policy_config,
                allow_policy_nondecisions,
                options.unknown_policy.enabled(),
            )
        })
        .transpose()?;

    let summary = json!({
        "schema": REPLAY_SCHEMA,
        "version": 1,
        "trace_analysis_id": trace.analysis_id,
        "trace_process_id": trace.process_id,
        "trace_events_sha256": trace.events_hash,
        "events": trace.event_count,
        "paths": trace.path_count,
        "checks": trace.checks.len(),
        "unique_queries": trace.queries.len(),
        "exact_duplicate_occurrences": trace.checks.len().saturating_sub(trace.queries.len()),
        "exact_duplicate_rate_ppm": fraction_ppm(
            trace.checks.len().saturating_sub(trace.queries.len()),
            trace.checks.len(),
        ),
        "same_lineage_repeated_checks": trace.reuse.same_lineage_repeats,
        "prefix_extensions": trace.reuse.prefix_extensions,
        "prefix_delta_assertions": trace.reuse.prefix_delta_assertions,
        "divergent_lineage_checks": trace.reuse.divergent_checks,
        "maximum_scope_depth": trace.reuse.maximum_scope_depth,
        "model_reads": trace.model_reads.len(),
        "model_choices": trace.model_choice_count,
        "unique_model_choices_replayed": unique_choices.len(),
        "recorded_outcomes": trace.recorded_outcomes,
        "recorded_backend_timing": {
            "total_nanos": trace.backend_timing.total_nanos,
            "z3_nanos": trace.backend_timing.z3_nanos,
            "z3_timed_checks": trace.backend_timing.z3_timed_checks,
            "axeyum_nanos": trace.backend_timing.axeyum_nanos,
            "axeyum_timed_checks": trace.backend_timing.axeyum_timed_checks,
        },
        "axeyum_unique_query_outcomes": trace.unique_query_outcomes,
        "solver_policy": {
            "preprocess": false,
            "timeout_ms_per_check": options.timeout_ms,
            "sat_model_replay": "solve_smtlib original-assertion replay",
        },
        "query_replay_nanos": trace.query_replay_nanos,
        "query_validation_workers": {
            "batches": trace.query_validation_worker_batches,
            "maximum_peak_rss_bytes": trace.query_validation_worker_peak_rss_bytes,
        },
        "choice_replay_nanos": choice_replay_nanos,
        "resource_identity": {
            "trace_manifest_sha256": trace.manifest_hash,
            "axeyum_package_version": env!("CARGO_PKG_VERSION"),
            "replay_executable_sha256": executable_sha256,
            "target_arch": env::consts::ARCH,
            "target_os": env::consts::OS,
            "validation_timeout_ms_per_check": options.timeout_ms,
            "policy_timeout_ms_per_check": options.policy_timeout_ms,
            "continue_once_on_unknown": options.unknown_policy.enabled(),
            "preprocess": false,
        },
        "cold_occurrence_replay": cold_occurrence_replay,
        "snapshot_replay": snapshot_replay,
        "warm_replay": warm_replay,
        "total_nanos": nanos(started.elapsed()),
    });
    if let Some(output) = options.output {
        write_json_atomic(&output, &summary)?;
    }
    Ok(summary)
}

#[derive(Debug)]
struct Options {
    trace: PathBuf,
    timeout_ms: u64,
    policy_timeout_ms: Option<u64>,
    unknown_policy: UnknownPolicy,
    cold_occurrences: bool,
    snapshot: bool,
    lineage: bool,
    output: Option<PathBuf>,
    validation_worker: Option<(usize, usize)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum UnknownPolicy {
    Preserve,
    ContinueOnce,
}

impl UnknownPolicy {
    fn enabled(self) -> bool {
        self == Self::ContinueOnce
    }
}

impl Options {
    #[allow(clippy::too_many_lines)]
    fn parse(args: impl Iterator<Item = String>) -> Result<Self, String> {
        let mut trace = None;
        let mut timeout_ms = 1_000;
        let mut policy_timeout_ms = None;
        let mut unknown_policy = UnknownPolicy::Preserve;
        let mut cold_occurrences = false;
        let mut snapshot = false;
        let mut lineage = false;
        let mut output = None;
        let mut validation_worker_start = None;
        let mut validation_worker_end = None;
        let mut args = args.peekable();
        while let Some(argument) = args.next() {
            match argument.as_str() {
                "--timeout-ms" => {
                    let value = args
                        .next()
                        .ok_or_else(|| "--timeout-ms requires a value".to_string())?;
                    timeout_ms = value
                        .parse::<u64>()
                        .map_err(|_| format!("invalid --timeout-ms value: {value}"))?;
                    if timeout_ms == 0 {
                        return Err("--timeout-ms must be positive".into());
                    }
                }
                "--policy-timeout-ms" => {
                    let value = args
                        .next()
                        .ok_or_else(|| "--policy-timeout-ms requires a value".to_string())?;
                    let value = value
                        .parse::<u64>()
                        .map_err(|_| format!("invalid --policy-timeout-ms value: {value}"))?;
                    if value == 0 {
                        return Err("--policy-timeout-ms must be positive".into());
                    }
                    policy_timeout_ms = Some(value);
                }
                "--out" => {
                    output = Some(PathBuf::from(
                        args.next()
                            .ok_or_else(|| "--out requires a path".to_string())?,
                    ));
                }
                "--validation-worker-start" => {
                    validation_worker_start =
                        Some(parse_usize_option(&mut args, "--validation-worker-start")?);
                }
                "--validation-worker-end" => {
                    validation_worker_end =
                        Some(parse_usize_option(&mut args, "--validation-worker-end")?);
                }
                "--cold-occurrences" => cold_occurrences = true,
                "--snapshot" => snapshot = true,
                "--warm" | "--lineage" => lineage = true,
                "--continue-on-unknown" => unknown_policy = UnknownPolicy::ContinueOnce,
                "-h" | "--help" => {
                    return Err("usage: glaurung-ordered-trace TRACE_DIR [--timeout-ms N] \
                         [--cold-occurrences] [--snapshot] [--lineage] \
                         [--policy-timeout-ms N] [--continue-on-unknown] [--out FILE]"
                        .into());
                }
                value if value.starts_with('-') => return Err(format!("unknown option: {value}")),
                value => {
                    if trace.replace(PathBuf::from(value)).is_some() {
                        return Err("only one TRACE_DIR may be supplied".into());
                    }
                }
            }
        }
        if policy_timeout_ms.is_some() && !snapshot && !lineage {
            return Err("--policy-timeout-ms requires --snapshot or --lineage".into());
        }
        if unknown_policy.enabled() && policy_timeout_ms.is_none() {
            return Err("--continue-on-unknown requires --policy-timeout-ms".into());
        }
        if unknown_policy.enabled() && !snapshot && !lineage {
            return Err("--continue-on-unknown requires --snapshot or --lineage".into());
        }
        let validation_worker = match (validation_worker_start, validation_worker_end) {
            (Some(start), Some(end)) if start < end => Some((start, end)),
            (None, None) => None,
            _ => {
                return Err(
                    "validation worker bounds must both be present with start < end".into(),
                );
            }
        };
        Ok(Self {
            trace: trace.ok_or_else(|| {
                "usage: glaurung-ordered-trace TRACE_DIR [--timeout-ms N] \
                 [--cold-occurrences] [--snapshot] [--lineage] \
                 [--policy-timeout-ms N] [--continue-on-unknown] [--out FILE]"
                    .to_string()
            })?,
            timeout_ms,
            policy_timeout_ms,
            unknown_policy,
            cold_occurrences,
            snapshot,
            lineage,
            output,
            validation_worker,
        })
    }
}

fn parse_usize_option(
    args: &mut impl Iterator<Item = String>,
    option: &str,
) -> Result<usize, String> {
    let value = args
        .next()
        .ok_or_else(|| format!("{option} requires a value"))?;
    value
        .parse::<usize>()
        .map_err(|_| format!("invalid {option} value: {value}"))
}

struct Trace {
    analysis_id: String,
    process_id: String,
    manifest_hash: String,
    events_hash: String,
    event_count: usize,
    path_count: usize,
    queries: BTreeMap<String, QueryRecord>,
    assertions: BTreeMap<String, Vec<u8>>,
    assertion_symbols: BTreeMap<String, Vec<(String, u64)>>,
    checks: BTreeMap<String, CheckRecord>,
    model_reads: BTreeMap<String, ModelRead>,
    model_choice_count: usize,
    recorded_outcomes: BTreeMap<String, u64>,
    unique_query_outcomes: BTreeMap<String, u64>,
    query_replay_nanos: u64,
    query_validation_worker_batches: u64,
    query_validation_worker_peak_rss_bytes: u64,
    backend_timing: BackendTimingStats,
    reuse: ReuseStats,
    warm_events: Vec<WarmEvent>,
}

struct QueryRecord {
    content_hash: String,
    path: Option<PathBuf>,
    inline_bytes: Option<Vec<u8>>,
    assertion_count: usize,
    assertion_sequence_digest: String,
    outcomes: BTreeSet<String>,
    occurrences: OccurrenceIdentity,
}

struct ValidatedQuery {
    assertion_count: usize,
    assertion_sequence_digest: String,
    outcome: String,
}

struct ValidatedQueries {
    records: BTreeMap<String, ValidatedQuery>,
    outcomes: BTreeMap<String, u64>,
    replay_nanos: u64,
    worker_batches: u64,
    worker_peak_rss_bytes: u64,
}

impl QueryRecord {
    fn read_bytes(&self) -> Result<Vec<u8>, String> {
        let bytes = if let Some(bytes) = &self.inline_bytes {
            bytes.clone()
        } else {
            read(
                self.path
                    .as_deref()
                    .ok_or_else(|| format!("query {} has no payload source", self.content_hash))?,
            )?
        };
        if sha256(&bytes) != self.content_hash {
            return Err(format!(
                "query content hash changed after indexing: {}",
                self.content_hash
            ));
        }
        Ok(bytes)
    }

    #[cfg(test)]
    fn is_file_backed(&self) -> bool {
        self.path.is_some() && self.inline_bytes.is_none()
    }

    #[cfg(test)]
    fn inline(bytes: Vec<u8>, outcomes: BTreeSet<String>) -> Self {
        let (assertion_count, assertion_sequence_digest) = assertion_sequence_identity(&bytes);
        Self {
            content_hash: sha256(&bytes),
            assertion_count,
            assertion_sequence_digest,
            path: None,
            inline_bytes: Some(bytes),
            outcomes,
            occurrences: OccurrenceAccumulator::default().identity(),
        }
    }
}

struct CheckRecord {
    check_id: String,
    path_id: String,
    query_hash: String,
    outcome: String,
    z3_nanos: Option<u64>,
}

struct ModelRead {
    read_id: String,
    check_id: String,
    path_id: String,
    expression_id: String,
    expression: String,
    symbols: Vec<(String, u64)>,
    width: u64,
    returned_value: u128,
}

#[derive(Default)]
struct BackendTimingStats {
    total_nanos: u64,
    z3_nanos: u64,
    z3_timed_checks: u64,
    axeyum_nanos: u64,
    axeyum_timed_checks: u64,
}

#[derive(Default)]
struct ReuseStats {
    same_lineage_repeats: usize,
    prefix_extensions: usize,
    prefix_delta_assertions: usize,
    divergent_checks: usize,
    maximum_scope_depth: usize,
}

#[derive(Clone, Default)]
struct PathState {
    scopes: Vec<ScopeState>,
    last_checked_constraints: Vec<String>,
    next_seq: u64,
    pending_sat_check: Option<String>,
    ended: bool,
}

#[derive(Clone)]
struct ScopeState {
    scope_id: String,
    constraint_id: Option<String>,
}

fn validate_native_warm_metadata(
    warm: &serde_json::Map<String, Value>,
    scopes: &[ScopeState],
    check_id: &str,
) -> Result<(), String> {
    let owner = warm
        .get("owner_id")
        .and_then(Value::as_u64)
        .ok_or_else(|| format!("check {check_id} has invalid warm owner"))?;
    let requested = warm
        .get("requested_retain_assertions")
        .and_then(Value::as_u64)
        .and_then(|value| usize::try_from(value).ok())
        .ok_or_else(|| format!("check {check_id} has invalid requested retain depth"))?;
    let persistent = warm
        .get("persistent_assertions")
        .and_then(Value::as_u64)
        .and_then(|value| usize::try_from(value).ok())
        .ok_or_else(|| format!("check {check_id} has invalid persistent depth"))?;
    let temporary = warm
        .get("temporary_assertions")
        .and_then(Value::as_u64)
        .and_then(|value| usize::try_from(value).ok())
        .ok_or_else(|| format!("check {check_id} has invalid temporary depth"))?;
    if owner == 0
        || requested > persistent
        || persistent > scopes.len()
        || temporary != scopes.len() - persistent
        || !warm.get("synchronized").is_some_and(Value::is_boolean)
        || warm.get("source_prefix_digest").and_then(Value::as_str)
            != Some(&scope_digest(&scopes[..persistent])?)
    {
        return Err(format!(
            "check {check_id} has inconsistent native warm replay metadata"
        ));
    }
    Ok(())
}

#[derive(Clone)]
enum WarmEvent {
    PathStart {
        path_id: String,
        parent_path_id: Option<String>,
    },
    Push {
        path_id: String,
    },
    Assert {
        path_id: String,
        constraint_id: String,
    },
    Pop {
        path_id: String,
    },
    Check {
        path_id: String,
        check_id: String,
    },
    ModelRead {
        path_id: String,
        read_id: String,
    },
    ModelChoice {
        path_id: String,
    },
    PathEnd {
        path_id: String,
    },
}

#[derive(Clone)]
struct OccurrenceIdentity {
    count: u64,
    digest: String,
}

struct OccurrenceAccumulator {
    count: u64,
    hasher: Sha256,
}

impl Default for OccurrenceAccumulator {
    fn default() -> Self {
        let mut hasher = Sha256::new();
        hasher.update(b"axeyum-ordered-query-occurrences-v1\0");
        Self { count: 0, hasher }
    }
}

impl OccurrenceAccumulator {
    fn record(&mut self, check_id: &str, path_id: &str, event_seq: u64) {
        hash_framed(&mut self.hasher, check_id.as_bytes());
        hash_framed(&mut self.hasher, path_id.as_bytes());
        hash_framed(&mut self.hasher, &event_seq.to_le_bytes());
        self.count = self.count.saturating_add(1);
    }

    fn identity(&self) -> OccurrenceIdentity {
        OccurrenceIdentity {
            count: self.count,
            digest: hex_digest(&self.hasher.clone().finalize()),
        }
    }
}

impl Trace {
    // Keeping the ordered validation state in one pass makes sequence, lineage,
    // scope, check, and model-choice ownership invariants directly auditable.
    #[allow(clippy::too_many_lines)]
    fn load(root: &Path, validated: &ValidatedQueries) -> Result<Self, String> {
        let manifest_bytes = read(&root.join("trace-manifest-v1.json"))?;
        let manifest_hash = sha256(&manifest_bytes);
        let manifest: Value = serde_json::from_slice(&manifest_bytes)
            .map_err(|error| format!("parse trace-manifest-v1.json: {error}"))?;
        if string(&manifest, "schema")? != TRACE_SCHEMA || integer(&manifest, "version")? != 1 {
            return Err("unsupported trace manifest schema/version".into());
        }
        let analysis_id = string(&manifest, "analysis_id")?.to_string();
        let process_id = string(&manifest, "process_id")?.to_string();
        let events_bytes = read(&root.join("events-v1.ndjson"))?;
        let index_bytes = read(&root.join("query-index-v1.json"))?;
        let events_hash = sha256(&events_bytes);
        if events_hash != string(&manifest, "events_sha256")? {
            return Err("events SHA-256 does not match manifest".into());
        }
        if sha256(&index_bytes) != string(&manifest, "query_index_sha256")? {
            return Err("query-index SHA-256 does not match manifest".into());
        }
        let index: Value = serde_json::from_slice(&index_bytes)
            .map_err(|error| format!("parse query-index-v1.json: {error}"))?;
        let queries = load_queries(root, &index, &validated.records)?;
        let unique_query_outcomes = validated.outcomes.clone();
        let query_replay_nanos = validated.replay_nanos;
        let query_validation_worker_batches = validated.worker_batches;
        let query_validation_worker_peak_rss_bytes = validated.worker_peak_rss_bytes;
        let assertions = load_assertions(root, &manifest)?;
        let native_replay = manifest.get("native_replay");
        if let Some(native) = native_replay
            && (string(native, "schema")? != "glaurung-native-ordered-replay-v1"
                || string(native, "topology")? != "source-owner-serial-lease-v1")
        {
            return Err("unsupported native ordered-replay extension".into());
        }

        let mut paths = BTreeMap::from([("analysis".to_string(), PathState::default())]);
        let mut checks = BTreeMap::new();
        let mut model_reads = BTreeMap::new();
        let mut recorded_outcomes = BTreeMap::<String, u64>::new();
        let mut backend_timing = BackendTimingStats::default();
        let mut observed_assertions = BTreeSet::new();
        let mut assertion_symbols = BTreeMap::new();
        let mut observed_occurrences = BTreeMap::<String, OccurrenceAccumulator>::new();
        let mut observed_query_outcomes = BTreeMap::<String, BTreeSet<String>>::new();
        let mut reuse = ReuseStats::default();
        let mut expected_event_seq = 0_u64;
        let mut expected_process_seq = 0_u64;
        let mut expected_worker_seq = BTreeMap::<String, u64>::new();
        let mut event_kinds = Vec::new();
        let mut choice_ids = BTreeSet::new();
        let mut choice_reads = BTreeSet::new();
        let mut warm_events = Vec::new();
        let mut native_warm_checks = 0_u64;
        let mut warm_owner_shares = 0_u64;
        let mut warm_owner_releases = 0_u64;
        let mut warm_owner_references = BTreeMap::<u64, u64>::new();

        for (line_index, line) in events_bytes.split(|byte| *byte == b'\n').enumerate() {
            if line.is_empty() {
                continue;
            }
            let event: Value = serde_json::from_slice(line)
                .map_err(|error| format!("event line {}: {error}", line_index + 1))?;
            if integer(&event, "version")? != 1 {
                return Err(format!("event line {} has wrong version", line_index + 1));
            }
            require_sequence(&event, "event_seq", &mut expected_event_seq)?;
            require_sequence(&event, "process_seq", &mut expected_process_seq)?;
            let worker_id = string(&event, "worker_id")?.to_string();
            require_sequence(
                &event,
                "worker_seq",
                expected_worker_seq.entry(worker_id).or_default(),
            )?;
            if string(&event, "analysis_id")? != analysis_id
                || string(&event, "process_id")? != process_id
            {
                return Err(format!(
                    "event line {} changes analysis/process ID",
                    line_index + 1
                ));
            }
            let kind = string(&event, "event")?.to_string();
            let path_id = string(&event, "path_id")?.to_string();
            event_kinds.push(kind.clone());
            if kind == "path_start" {
                if paths.contains_key(&path_id) {
                    return Err(format!("duplicate path start: {path_id}"));
                }
                let parent_path_id = event
                    .get("parent_path_id")
                    .filter(|value| !value.is_null())
                    .map(|value| {
                        value
                            .as_str()
                            .map(str::to_string)
                            .ok_or_else(|| "parent_path_id is not a string".to_string())
                    })
                    .transpose()?;
                let state = if let Some(parent_id) = &parent_path_id {
                    let parent = paths
                        .get(parent_id)
                        .ok_or_else(|| format!("path {path_id} has missing parent {parent_id}"))?;
                    if parent.ended {
                        return Err(format!("path {path_id} has ended parent {parent_id}"));
                    }
                    parent.clone()
                } else {
                    PathState::default()
                };
                if usize_integer(&event, "inherited_scope_depth")? != state.scopes.len()
                    || string(&event, "scope_digest")? != scope_digest(&state.scopes)?
                {
                    return Err(format!("path {path_id} inherited scope mismatch"));
                }
                paths.insert(
                    path_id.clone(),
                    PathState {
                        next_seq: 0,
                        pending_sat_check: None,
                        ended: false,
                        ..state
                    },
                );
                warm_events.push(WarmEvent::PathStart {
                    path_id: path_id.clone(),
                    parent_path_id,
                });
            }
            let state = paths
                .get_mut(&path_id)
                .ok_or_else(|| format!("{kind} references unknown path {path_id}"))?;
            if integer(&event, "path_seq")? != state.next_seq {
                return Err(format!("non-contiguous path_seq on {path_id}"));
            }
            state.next_seq += 1;
            if state.ended {
                return Err(format!("event {kind} follows path_end on {path_id}"));
            }

            match kind.as_str() {
                "push" => {
                    state.pending_sat_check = None;
                    if usize_integer(&event, "prior_depth")? != state.scopes.len() {
                        return Err(format!("push depth mismatch on {path_id}"));
                    }
                    state.scopes.push(ScopeState {
                        scope_id: string(&event, "scope_id")?.to_string(),
                        constraint_id: None,
                    });
                    if usize_integer(&event, "resulting_depth")? != state.scopes.len() {
                        return Err(format!("push resulting depth mismatch on {path_id}"));
                    }
                    warm_events.push(WarmEvent::Push {
                        path_id: path_id.clone(),
                    });
                }
                "assert" => {
                    state.pending_sat_check = None;
                    let scope = state
                        .scopes
                        .last_mut()
                        .ok_or_else(|| format!("assert without push on {path_id}"))?;
                    if scope.scope_id != string(&event, "scope_id")?
                        || scope.constraint_id.is_some()
                    {
                        return Err(format!("assert does not fill top scope on {path_id}"));
                    }
                    if event.get("sort_validated") != Some(&Value::Bool(true)) {
                        return Err(format!("unvalidated assertion on {path_id}"));
                    }
                    let constraint = string(&event, "constraint_id")?.to_string();
                    if string(&event, "assertion_sha256")? != constraint {
                        return Err(format!("assertion hash mismatch on {path_id}"));
                    }
                    if manifest.get("assertion_count").is_some() {
                        let relative = string(&event, "assertion_path")?;
                        if relative != format!("assertions/{constraint}.smt2")
                            || !assertions.contains_key(&constraint)
                        {
                            return Err(format!("assertion store mismatch on {path_id}"));
                        }
                        let symbols = parse_symbol_declarations(
                            &event,
                            "assertion_symbols",
                            &format!("assertion {constraint}"),
                        )?;
                        if let Some(previous) =
                            assertion_symbols.insert(constraint.clone(), symbols.clone())
                            && previous != symbols
                        {
                            return Err(format!(
                                "assertion {constraint} has inconsistent symbol declarations"
                            ));
                        }
                    }
                    observed_assertions.insert(constraint.clone());
                    scope.constraint_id = Some(constraint.clone());
                    if string(&event, "scope_digest")? != scope_digest(&state.scopes)? {
                        return Err(format!("assert scope digest mismatch on {path_id}"));
                    }
                    warm_events.push(WarmEvent::Assert {
                        path_id: path_id.clone(),
                        constraint_id: constraint,
                    });
                }
                "pop" => {
                    state.pending_sat_check = None;
                    if usize_integer(&event, "prior_depth")? != state.scopes.len() {
                        return Err(format!("pop prior depth mismatch on {path_id}"));
                    }
                    let top = state
                        .scopes
                        .pop()
                        .ok_or_else(|| format!("scope underflow on {path_id}"))?;
                    if top.scope_id != string(&event, "scope_id")? {
                        return Err(format!("scope pop mismatch on {path_id}"));
                    }
                    if usize_integer(&event, "resulting_depth")? != state.scopes.len()
                        || string(&event, "scope_digest")? != scope_digest(&state.scopes)?
                    {
                        return Err(format!("pop resulting scope mismatch on {path_id}"));
                    }
                    warm_events.push(WarmEvent::Pop {
                        path_id: path_id.clone(),
                    });
                }
                "check" => {
                    let constraints = complete_constraints(state, &path_id)?;
                    if usize_integer(&event, "scope_depth")? != constraints.len()
                        || usize_integer(&event, "active_constraint_count")? != constraints.len()
                    {
                        return Err(format!("check count/depth mismatch on {path_id}"));
                    }
                    if string(&event, "scope_digest")? != scope_digest(&state.scopes)? {
                        return Err(format!("check scope digest mismatch on {path_id}"));
                    }
                    let query_hash = string(&event, "query_sha256")?.to_string();
                    let query = queries
                        .get(&query_hash)
                        .ok_or_else(|| format!("check references missing query {query_hash}"))?;
                    let (assertion_count, assertion_sequence_digest) =
                        constraint_sequence_identity(&constraints);
                    if query.assertion_count != assertion_count
                        || query.assertion_sequence_digest != assertion_sequence_digest
                    {
                        return Err(format!(
                            "check query does not reconstruct scopes on {path_id}"
                        ));
                    }
                    let check_id = string(&event, "check_id")?.to_string();
                    let outcome = string(&event, "outcome")?.to_string();
                    if !matches!(outcome.as_str(), "sat" | "unsat" | "unknown" | "error") {
                        return Err(format!("invalid outcome on {check_id}: {outcome}"));
                    }
                    let total_nanos = integer(&event, "backend_nanos")?;
                    let z3_nanos = optional_integer(&event, "z3_nanos")?;
                    let axeyum_nanos = optional_integer(&event, "axeyum_nanos")?;
                    if z3_nanos
                        .unwrap_or_default()
                        .saturating_add(axeyum_nanos.unwrap_or_default())
                        > total_nanos
                    {
                        return Err(format!(
                            "per-backend timing exceeds total on check {check_id}"
                        ));
                    }
                    backend_timing.total_nanos =
                        backend_timing.total_nanos.saturating_add(total_nanos);
                    if let Some(nanos) = z3_nanos {
                        backend_timing.z3_nanos = backend_timing.z3_nanos.saturating_add(nanos);
                        backend_timing.z3_timed_checks =
                            backend_timing.z3_timed_checks.saturating_add(1);
                    }
                    if let Some(nanos) = axeyum_nanos {
                        backend_timing.axeyum_nanos =
                            backend_timing.axeyum_nanos.saturating_add(nanos);
                        backend_timing.axeyum_timed_checks =
                            backend_timing.axeyum_timed_checks.saturating_add(1);
                    }
                    if checks
                        .insert(
                            check_id.clone(),
                            CheckRecord {
                                check_id: check_id.clone(),
                                path_id: path_id.clone(),
                                query_hash: query_hash.clone(),
                                outcome: outcome.clone(),
                                z3_nanos,
                            },
                        )
                        .is_some()
                    {
                        return Err(format!("duplicate check ID {check_id}"));
                    }
                    *recorded_outcomes.entry(outcome.clone()).or_default() += 1;
                    observed_query_outcomes
                        .entry(query_hash.clone())
                        .or_default()
                        .insert(outcome);
                    observed_occurrences.entry(query_hash).or_default().record(
                        &check_id,
                        &path_id,
                        integer(&event, "event_seq")?,
                    );
                    classify_reuse(&mut reuse, &state.last_checked_constraints, &constraints);
                    reuse.maximum_scope_depth = reuse.maximum_scope_depth.max(constraints.len());
                    state.last_checked_constraints = constraints;
                    state.pending_sat_check =
                        (checks[&check_id].outcome == "sat").then_some(check_id.clone());
                    if native_replay.is_some() {
                        let warm = event
                            .get("warm_replay")
                            .and_then(Value::as_object)
                            .ok_or_else(|| {
                                format!("check {check_id} omits native warm replay metadata")
                            })?;
                        validate_native_warm_metadata(warm, &state.scopes, &check_id)?;
                        native_warm_checks = native_warm_checks.saturating_add(1);
                    }
                    warm_events.push(WarmEvent::Check {
                        path_id: path_id.clone(),
                        check_id,
                    });
                }
                "model_read" => {
                    let read = parse_model_read(&event, &path_id)?;
                    let read_id = read.read_id.clone();
                    let check = checks.get(&read.check_id).ok_or_else(|| {
                        format!("model read {} references missing check", read.read_id)
                    })?;
                    if check.path_id != path_id
                        || check.outcome != "sat"
                        || state.pending_sat_check.as_deref() != Some(&read.check_id)
                    {
                        return Err(format!(
                            "model read {} does not follow a same-path SAT check",
                            read.read_id
                        ));
                    }
                    if model_reads.insert(read.read_id.clone(), read).is_some() {
                        return Err("duplicate model-read ID".into());
                    }
                    warm_events.push(WarmEvent::ModelRead {
                        path_id: path_id.clone(),
                        read_id,
                    });
                }
                "model_choice" => {
                    let choice_id = string(&event, "model_choice_id")?.to_string();
                    if !choice_ids.insert(choice_id.clone()) {
                        return Err(format!("duplicate model-choice ID {choice_id}"));
                    }
                    let check_id = string(&event, "check_id")?;
                    if state.pending_sat_check.as_deref() != Some(check_id) {
                        return Err(format!(
                            "model choice {choice_id} does not consume the pending SAT check"
                        ));
                    }
                    let reads = array(&event, "model_read_ids")?;
                    let values = array(&event, "chosen_values")?;
                    if reads.is_empty() || reads.len() != values.len() {
                        return Err(format!("model choice for {check_id} has no reads"));
                    }
                    if string(&event, "policy_id")?.is_empty()
                        || integer(&event, "policy_version")? == 0
                    {
                        return Err(format!("model choice {choice_id} has invalid policy"));
                    }
                    let downstream = array(&event, "downstream_path_ids")?;
                    if downstream.is_empty()
                        || !downstream
                            .iter()
                            .all(|value| value.as_str() == Some(&path_id))
                    {
                        return Err(format!(
                            "model choice {choice_id} has invalid downstream path"
                        ));
                    }
                    for (read, value) in reads.iter().zip(values) {
                        let read_id = read
                            .as_str()
                            .ok_or_else(|| "model_read_ids entry is not a string".to_string())?;
                        let model_read = model_reads
                            .get(read_id)
                            .ok_or_else(|| format!("model choice references missing {read_id}"))?;
                        if model_read.check_id != check_id {
                            return Err(format!("model choice/read check mismatch for {read_id}"));
                        }
                        if model_read.path_id != path_id {
                            return Err(format!("model choice/read path mismatch for {read_id}"));
                        }
                        let chosen = value.as_str().ok_or_else(|| {
                            format!("model choice {choice_id} has non-string value")
                        })?;
                        if parse_hex(chosen)? != model_read.returned_value {
                            return Err(format!("model choice/read value mismatch for {read_id}"));
                        }
                        if !choice_reads.insert(read_id.to_string()) {
                            return Err(format!("model read {read_id} is consumed more than once"));
                        }
                    }
                    state.pending_sat_check = None;
                    warm_events.push(WarmEvent::ModelChoice {
                        path_id: path_id.clone(),
                    });
                }
                "path_end" => {
                    state.pending_sat_check = None;
                    if usize_integer(&event, "terminal_scope_depth")? != state.scopes.len()
                        || string(&event, "scope_digest")? != scope_digest(&state.scopes)?
                    {
                        return Err(format!("path_end scope digest mismatch on {path_id}"));
                    }
                    warm_events.push(WarmEvent::PathEnd {
                        path_id: path_id.clone(),
                    });
                    state.ended = true;
                }
                "warm_owner_share" => {
                    let owner = integer(&event, "owner_id")?;
                    let children = integer(&event, "children")?;
                    if path_id != "analysis" || owner == 0 || children == 0 {
                        return Err("invalid native warm-owner share event".into());
                    }
                    let references = warm_owner_references.entry(owner).or_insert(1);
                    *references = references.saturating_add(children);
                    warm_owner_shares = warm_owner_shares.saturating_add(1);
                }
                "warm_owner_release" => {
                    let owner = integer(&event, "owner_id")?;
                    if path_id != "analysis" || owner == 0 {
                        return Err("invalid native warm-owner release event".into());
                    }
                    if let Some(references) = warm_owner_references.get_mut(&owner) {
                        *references = references.saturating_sub(1);
                        if *references == 0 {
                            warm_owner_references.remove(&owner);
                        }
                    }
                    warm_owner_releases = warm_owner_releases.saturating_add(1);
                }
                "analysis_start" | "analysis_end" | "path_start" => {}
                other => return Err(format!("unsupported trace event: {other}")),
            }
        }

        if let Some(native) = native_replay
            && (integer(native, "warm_check_count")? != native_warm_checks
                || integer(native, "warm_owner_share_count")? != warm_owner_shares
                || integer(native, "warm_owner_release_count")? != warm_owner_releases
                || !warm_owner_references.is_empty())
        {
            return Err("native warm replay manifest/lifecycle mismatch".into());
        }

        if event_kinds.first().map(String::as_str) != Some("analysis_start")
            || event_kinds.last().map(String::as_str) != Some("analysis_end")
            || event_kinds
                .iter()
                .filter(|kind| kind.as_str() == "analysis_start")
                .count()
                != 1
            || event_kinds
                .iter()
                .filter(|kind| kind.as_str() == "analysis_end")
                .count()
                != 1
        {
            return Err("analysis boundary events do not enclose trace".into());
        }
        for (path_id, state) in &paths {
            if path_id != "analysis" && !state.ended {
                return Err(format!("unterminated path {path_id}"));
            }
        }
        let event_count = usize::try_from(expected_event_seq)
            .map_err(|_| "event count does not fit usize".to_string())?;
        if event_count != usize_integer(&manifest, "event_count")? {
            return Err("manifest event count mismatch".into());
        }
        let path_count = paths.len() - 1;
        if path_count != usize_integer(&manifest, "path_count")? {
            return Err("manifest path count mismatch".into());
        }
        if queries.len() != usize_integer(&manifest, "query_count")? {
            return Err("manifest query count mismatch".into());
        }
        if expected_worker_seq.len() != usize_integer(&manifest, "worker_count")? {
            return Err("manifest worker count mismatch".into());
        }
        for (hash, query) in &queries {
            let observed = observed_occurrences
                .get(hash)
                .map(OccurrenceAccumulator::identity);
            if observed.as_ref().is_none_or(|observed| {
                observed.count != query.occurrences.count
                    || observed.digest != query.occurrences.digest
            }) {
                return Err(format!("query occurrence index mismatch for {hash}"));
            }
            if observed_query_outcomes.get(hash) != Some(&query.outcomes) {
                return Err(format!("query outcome index mismatch for {hash}"));
            }
        }
        let recorded_reads = model_reads.keys().cloned().collect::<BTreeSet<_>>();
        if choice_reads != recorded_reads {
            return Err("model reads and model-choice consumption differ".into());
        }
        if let Some(expected) = manifest.get("assertion_count").and_then(Value::as_u64)
            && (usize_to_u64(assertions.len()) != expected
                || observed_assertions != assertions.keys().cloned().collect()
                || assertion_symbols.keys().ne(assertions.keys()))
        {
            return Err("assertion store membership/count differs from events".into());
        }

        Ok(Self {
            analysis_id,
            process_id,
            manifest_hash,
            events_hash,
            event_count,
            path_count,
            queries,
            assertions,
            assertion_symbols,
            checks,
            model_reads,
            model_choice_count: choice_ids.len(),
            recorded_outcomes,
            unique_query_outcomes,
            query_replay_nanos,
            query_validation_worker_batches,
            query_validation_worker_peak_rss_bytes,
            backend_timing,
            reuse,
            warm_events,
        })
    }
}

fn load_validated_query_index(root: &Path) -> Result<Value, String> {
    let manifest_bytes = read(&root.join("trace-manifest-v1.json"))?;
    let manifest: Value = serde_json::from_slice(&manifest_bytes)
        .map_err(|error| format!("parse trace-manifest-v1.json: {error}"))?;
    if string(&manifest, "schema")? != TRACE_SCHEMA || integer(&manifest, "version")? != 1 {
        return Err("unsupported trace manifest schema/version".into());
    }
    let index_bytes = read(&root.join("query-index-v1.json"))?;
    if sha256(&index_bytes) != string(&manifest, "query_index_sha256")? {
        return Err("query-index SHA-256 does not match manifest".into());
    }
    serde_json::from_slice(&index_bytes)
        .map_err(|error| format!("parse query-index-v1.json: {error}"))
}

fn run_query_validation_worker(
    root: &Path,
    config: &SolverConfig,
    start: usize,
    end: usize,
) -> Result<Value, String> {
    let index = load_validated_query_index(root)?;
    let rows = array(&index, "queries")?;
    if end > rows.len() {
        return Err(format!(
            "validation worker range {start}..{end} exceeds {} queries",
            rows.len()
        ));
    }
    let mut records = Vec::with_capacity(end - start);
    for row in &rows[start..end] {
        let hash = string(row, "content_hash")?;
        let relative = string(row, "path")?;
        if relative != format!("queries/{hash}.smt2") {
            return Err(format!("non-canonical query path for {hash}"));
        }
        let outcomes = array(row, "outcomes")?
            .iter()
            .map(|outcome| {
                outcome
                    .as_str()
                    .ok_or_else(|| format!("non-string query outcome for {hash}"))
            })
            .collect::<Result<BTreeSet<_>, _>>()?;
        let sat = outcomes.contains("sat");
        let unsat = outcomes.contains("unsat");
        if outcomes.is_empty() || (sat && unsat) {
            return Err(format!("query {hash} has invalid recorded outcomes"));
        }
        let expected = sat.then_some("sat").or_else(|| unsat.then_some("unsat"));
        let bytes = read(&root.join(relative))?;
        if sha256(&bytes) != hash {
            return Err(format!("query content hash mismatch for {hash}"));
        }
        validate_qf_bv_script(hash, &bytes)?;
        let outcome =
            solve_text(&bytes, config).map_err(|error| format!("query {hash}: {error}"))?;
        if let Some(expected) = expected
            && outcome != expected
        {
            return Err(format!(
                "query {hash} verdict disagreement: recorded {expected}, Axeyum {outcome}"
            ));
        }
        let (assertion_count, assertion_sequence_digest) = assertion_sequence_identity(&bytes);
        records.push(json!({
            "content_hash": hash,
            "assertion_count": assertion_count,
            "assertion_sequence_digest": assertion_sequence_digest,
            "outcome": outcome,
        }));
    }
    Ok(json!({
        "schema": VALIDATION_WORKER_SCHEMA,
        "version": 1,
        "start": start,
        "end": end,
        "records": records,
        "process_peak_rss_bytes": process_peak_rss_bytes(),
    }))
}

fn validate_queries_with_workers(
    root: &Path,
    timeout_ms: u64,
    executable: &Path,
) -> Result<ValidatedQueries, String> {
    const BATCH_SIZE: usize = 128;

    let started = Instant::now();
    let index = load_validated_query_index(root)?;
    let query_count = array(&index, "queries")?.len();
    let mut records = BTreeMap::new();
    let mut outcomes = BTreeMap::<String, u64>::new();
    let mut worker_batches = 0_u64;
    let mut worker_peak_rss_bytes = 0_u64;
    for start in (0..query_count).step_by(BATCH_SIZE) {
        let end = start.saturating_add(BATCH_SIZE).min(query_count);
        let output = Command::new(executable)
            .arg(root)
            .arg("--timeout-ms")
            .arg(timeout_ms.to_string())
            .arg("--validation-worker-start")
            .arg(start.to_string())
            .arg("--validation-worker-end")
            .arg(end.to_string())
            .output()
            .map_err(|error| format!("start query validation worker {start}..{end}: {error}"))?;
        if !output.status.success() {
            return Err(format!(
                "query validation worker {start}..{end} failed with {}: {}",
                output.status,
                String::from_utf8_lossy(&output.stderr).trim()
            ));
        }
        let summary: Value = serde_json::from_slice(&output.stdout).map_err(|error| {
            format!("parse query validation worker {start}..{end} output: {error}")
        })?;
        if string(&summary, "schema")? != VALIDATION_WORKER_SCHEMA
            || usize_integer(&summary, "start")? != start
            || usize_integer(&summary, "end")? != end
        {
            return Err(format!(
                "query validation worker {start}..{end} identity mismatch"
            ));
        }
        worker_batches = worker_batches.saturating_add(1);
        worker_peak_rss_bytes =
            worker_peak_rss_bytes.max(integer(&summary, "process_peak_rss_bytes")?);
        let batch = array(&summary, "records")?;
        if batch.len() != end - start {
            return Err(format!(
                "query validation worker {start}..{end} count mismatch"
            ));
        }
        for record in batch {
            let hash = string(record, "content_hash")?.to_string();
            let digest = string(record, "assertion_sequence_digest")?.to_string();
            let outcome = string(record, "outcome")?.to_string();
            if hash.len() != 64
                || digest.len() != 64
                || !matches!(outcome.as_str(), "sat" | "unsat" | "unknown")
            {
                return Err(format!("invalid validation-worker record for {hash}"));
            }
            *outcomes.entry(outcome.clone()).or_default() += 1;
            if records
                .insert(
                    hash.clone(),
                    ValidatedQuery {
                        assertion_count: usize_integer(record, "assertion_count")?,
                        assertion_sequence_digest: digest,
                        outcome,
                    },
                )
                .is_some()
            {
                return Err(format!("duplicate validation-worker result for {hash}"));
            }
        }
    }
    if records.len() != query_count {
        return Err("validation-worker results do not cover the query index".into());
    }
    Ok(ValidatedQueries {
        records,
        outcomes,
        replay_nanos: nanos(started.elapsed()),
        worker_batches,
        worker_peak_rss_bytes,
    })
}

fn load_queries(
    root: &Path,
    index: &Value,
    validated: &BTreeMap<String, ValidatedQuery>,
) -> Result<BTreeMap<String, QueryRecord>, String> {
    if integer(index, "version")? != 1 {
        return Err("query-index version is not 1".into());
    }
    let mut queries = BTreeMap::new();
    for row in array(index, "queries")? {
        let hash = string(row, "content_hash")?.to_string();
        if hash.len() != 64 || !hash.bytes().all(|byte| byte.is_ascii_hexdigit()) {
            return Err(format!("invalid query hash {hash:?}"));
        }
        let relative = string(row, "path")?;
        if relative != format!("queries/{hash}.smt2") {
            return Err(format!("non-canonical query path for {hash}"));
        }
        let outcomes = array(row, "outcomes")?
            .iter()
            .map(|outcome| {
                outcome
                    .as_str()
                    .map(str::to_string)
                    .ok_or_else(|| format!("non-string query outcome for {hash}"))
            })
            .collect::<Result<BTreeSet<_>, _>>()?;
        if outcomes.is_empty() {
            return Err(format!("query {hash} has no outcomes"));
        }
        let sat = outcomes.contains("sat");
        let unsat = outcomes.contains("unsat");
        if sat && unsat {
            return Err(format!("query {hash} contains both sat and unsat"));
        }
        let expected = sat.then_some("sat").or_else(|| unsat.then_some("unsat"));
        let validated_query = validated
            .get(&hash)
            .ok_or_else(|| format!("query {hash} has no validation-worker result"))?;
        if let Some(expected) = expected
            && validated_query.outcome != expected
        {
            return Err(format!(
                "query {hash} verdict disagreement: recorded {expected}, Axeyum {}",
                validated_query.outcome
            ));
        }
        let path = root.join(relative);
        let mut occurrences = OccurrenceAccumulator::default();
        for occurrence in array(row, "occurrences")? {
            occurrences.record(
                string(occurrence, "check_id")?,
                string(occurrence, "path_id")?,
                integer(occurrence, "event_seq")?,
            );
        }
        if queries
            .insert(
                hash,
                QueryRecord {
                    content_hash: string(row, "content_hash")?.to_string(),
                    path: Some(path),
                    inline_bytes: None,
                    assertion_count: validated_query.assertion_count,
                    assertion_sequence_digest: validated_query.assertion_sequence_digest.clone(),
                    outcomes,
                    occurrences: occurrences.identity(),
                },
            )
            .is_some()
        {
            return Err("duplicate query-index hash".into());
        }
    }
    let stored = fs::read_dir(root.join("queries"))
        .map_err(|error| format!("read query store: {error}"))?
        .filter_map(Result::ok)
        .filter_map(|entry| {
            entry
                .path()
                .extension()
                .is_some_and(|extension| extension == "smt2")
                .then(|| entry.path().file_stem()?.to_str().map(str::to_string))
                .flatten()
        })
        .collect::<BTreeSet<_>>();
    let indexed = queries.keys().cloned().collect::<BTreeSet<_>>();
    if stored != indexed {
        return Err("query store membership differs from query index".into());
    }
    if validated.len() != queries.len() {
        return Err("validation-worker query membership differs from query index".into());
    }
    Ok(queries)
}

fn load_assertions(root: &Path, manifest: &Value) -> Result<BTreeMap<String, Vec<u8>>, String> {
    let Some(expected_count) = manifest.get("assertion_count").and_then(Value::as_u64) else {
        if root.join("assertions").exists() {
            return Err("assertion store exists without manifest assertion_count".into());
        }
        return Ok(BTreeMap::new());
    };
    let mut assertions = BTreeMap::new();
    for entry in fs::read_dir(root.join("assertions"))
        .map_err(|error| format!("read assertion store: {error}"))?
    {
        let entry = entry.map_err(|error| format!("read assertion-store entry: {error}"))?;
        let path = entry.path();
        if path.extension().is_none_or(|extension| extension != "smt2") {
            return Err(format!(
                "non-SMT2 file in assertion store: {}",
                path.display()
            ));
        }
        let constraint_id = path
            .file_stem()
            .and_then(|stem| stem.to_str())
            .ok_or_else(|| format!("invalid assertion filename: {}", path.display()))?
            .to_string();
        if constraint_id.len() != 64 || !constraint_id.bytes().all(|byte| byte.is_ascii_hexdigit())
        {
            return Err(format!("invalid assertion content hash: {constraint_id}"));
        }
        let bytes = read(&path)?;
        if sha256(&bytes) != constraint_id || !bytes.starts_with(b"(assert ") {
            return Err(format!("assertion bytes do not match {constraint_id}"));
        }
        if assertions.insert(constraint_id.clone(), bytes).is_some() {
            return Err(format!("duplicate assertion content hash: {constraint_id}"));
        }
    }
    if usize_to_u64(assertions.len()) != expected_count {
        return Err("manifest assertion count differs from assertion store".into());
    }
    Ok(assertions)
}

fn replay_cold_occurrences(trace: &Trace, config: &SolverConfig) -> Result<Value, String> {
    let replay_started = Instant::now();
    let peak_rss_before = process_peak_rss_bytes();
    let mut latencies = Vec::with_capacity(trace.checks.len());
    let mut outcomes = BTreeMap::<String, u64>::new();
    let mut checks = 0_u64;
    for event in &trace.warm_events {
        let WarmEvent::Check { check_id, .. } = event else {
            continue;
        };
        let check = trace
            .checks
            .get(check_id)
            .ok_or_else(|| format!("cold occurrence references missing check {check_id}"))?;
        let query = trace
            .queries
            .get(&check.query_hash)
            .ok_or_else(|| format!("cold occurrence {check_id} references a missing query"))?;
        let bytes = query.read_bytes()?;
        let started = Instant::now();
        let result = solve_smtlib(
            std::str::from_utf8(&bytes)
                .map_err(|error| format!("cold occurrence {check_id}: non-UTF-8: {error}"))?,
            config,
        )
        .map_err(|error| format!("cold occurrence {check_id}: {error}"))?;
        latencies.push(nanos(started.elapsed()));
        let outcome = result_name(&result.result);
        *outcomes.entry(outcome.to_string()).or_default() += 1;
        checks = checks.saturating_add(1);
        if check.outcome != outcome {
            return Err(format!(
                "cold occurrence {check_id} verdict disagreement: recorded {}, Axeyum {outcome}",
                check.outcome
            ));
        }
    }
    latencies.sort_unstable();
    let replay_nanos = nanos(replay_started.elapsed());
    Ok(json!({
        "policy": {
            "entry": "exact occurrence SMT-LIB bytes",
            "arena": "fresh parse and arena per occurrence",
            "solver": "fresh one-shot solver per occurrence",
            "preprocess": config.preprocess,
            "timeout_ms_per_check": config.timeout.map(|timeout| timeout.as_millis()),
            "sat_model_replay": "solve_smtlib original-assertion replay",
        },
        "checks": checks,
        "outcomes": outcomes,
        "occurrence_latency_p50_nanos": percentile(&latencies, 50),
        "occurrence_latency_p95_nanos": percentile(&latencies, 95),
        "replay_nanos": replay_nanos,
        "ratio_to_recorded_z3_ppm": same_stream_z3_ratio_ppm(trace, replay_nanos),
        "process_peak_rss_bytes_before": peak_rss_before,
        "process_peak_rss_bytes_after": process_peak_rss_bytes(),
    }))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ContinuationOutcome {
    NotAttempted,
    RecoveredSat,
    RecoveredUnsat,
    RepeatedUnknown,
    Error,
}

struct CheckAttempt {
    result: CheckResult,
    initial_nanos: u64,
    continuation_nanos: u64,
    total_nanos: u64,
    continuation: ContinuationOutcome,
}

fn check_with_optional_continuation<E>(
    continue_on_unknown: bool,
    mut check: impl FnMut() -> Result<CheckResult, E>,
) -> Result<CheckAttempt, String>
where
    E: core::fmt::Display,
{
    let total_started = Instant::now();
    let initial_started = Instant::now();
    let initial = check().map_err(|error| format!("initial check failed: {error}"))?;
    let initial_nanos = nanos(initial_started.elapsed());
    if !continue_on_unknown || !matches!(initial, CheckResult::Unknown(_)) {
        return Ok(CheckAttempt {
            result: initial,
            initial_nanos,
            continuation_nanos: 0,
            total_nanos: nanos(total_started.elapsed()),
            continuation: ContinuationOutcome::NotAttempted,
        });
    }

    let continuation_started = Instant::now();
    let continuation = check();
    let continuation_nanos = nanos(continuation_started.elapsed());
    let (result, continuation) = match continuation {
        Ok(result @ CheckResult::Sat(_)) => (result, ContinuationOutcome::RecoveredSat),
        Ok(CheckResult::Unsat) => (CheckResult::Unsat, ContinuationOutcome::RecoveredUnsat),
        Ok(CheckResult::Unknown(_)) => (initial, ContinuationOutcome::RepeatedUnknown),
        Err(_) => (initial, ContinuationOutcome::Error),
    };
    Ok(CheckAttempt {
        result,
        initial_nanos,
        continuation_nanos,
        total_nanos: nanos(total_started.elapsed()),
        continuation,
    })
}

#[derive(Default)]
struct TimeoutContinuationStats {
    attempts: u64,
    recovered_sat: u64,
    recovered_unsat: u64,
    repeated_unknowns: u64,
    errors: u64,
    initial_check_nanos: u64,
    continuation_check_nanos: u64,
}

impl TimeoutContinuationStats {
    fn record(&mut self, attempt: &CheckAttempt) {
        self.initial_check_nanos = self
            .initial_check_nanos
            .saturating_add(attempt.initial_nanos);
        self.continuation_check_nanos = self
            .continuation_check_nanos
            .saturating_add(attempt.continuation_nanos);
        match attempt.continuation {
            ContinuationOutcome::NotAttempted => {}
            ContinuationOutcome::RecoveredSat => {
                self.attempts = self.attempts.saturating_add(1);
                self.recovered_sat = self.recovered_sat.saturating_add(1);
            }
            ContinuationOutcome::RecoveredUnsat => {
                self.attempts = self.attempts.saturating_add(1);
                self.recovered_unsat = self.recovered_unsat.saturating_add(1);
            }
            ContinuationOutcome::RepeatedUnknown => {
                self.attempts = self.attempts.saturating_add(1);
                self.repeated_unknowns = self.repeated_unknowns.saturating_add(1);
            }
            ContinuationOutcome::Error => {
                self.attempts = self.attempts.saturating_add(1);
                self.errors = self.errors.saturating_add(1);
            }
        }
    }

    fn json(&self, enabled: bool) -> Value {
        debug_assert_eq!(
            self.attempts,
            self.recovered_sat
                .saturating_add(self.recovered_unsat)
                .saturating_add(self.repeated_unknowns)
                .saturating_add(self.errors)
        );
        json!({
            "enabled": enabled,
            "attempts": self.attempts,
            "recoveries": self.recovered_sat.saturating_add(self.recovered_unsat),
            "recovered_sat": self.recovered_sat,
            "recovered_unsat": self.recovered_unsat,
            "repeated_unknowns": self.repeated_unknowns,
            "errors": self.errors,
            "initial_check_nanos": self.initial_check_nanos,
            "continuation_check_nanos": self.continuation_check_nanos,
        })
    }
}

#[derive(Default)]
struct OutcomeComparisonStats {
    exact: u64,
    recorded_decided_observed_nondecided: u64,
    recorded_nondecided_observed_decided: u64,
    nondecided_class_changes: u64,
}

impl OutcomeComparisonStats {
    fn compare(
        &mut self,
        check_id: &str,
        recorded: &str,
        observed: &str,
        allow_nondecisions: bool,
    ) -> Result<(), String> {
        if recorded == "error" || observed == "error" {
            return Err(format!(
                "check {check_id} contains an operational error outcome: recorded {recorded}, \
                 Axeyum {observed}"
            ));
        }
        if recorded == observed {
            self.exact = self.exact.saturating_add(1);
            return Ok(());
        }
        let recorded_decided = is_decided_outcome(recorded);
        let observed_decided = is_decided_outcome(observed);
        if recorded_decided && observed_decided {
            return Err(format!(
                "check {check_id} decided verdict disagreement: recorded {recorded}, Axeyum \
                 {observed}"
            ));
        }
        if !allow_nondecisions {
            return Err(format!(
                "check {check_id} verdict disagreement: recorded {recorded}, Axeyum {observed}"
            ));
        }
        match (recorded_decided, observed_decided) {
            (true, false) => {
                self.recorded_decided_observed_nondecided =
                    self.recorded_decided_observed_nondecided.saturating_add(1);
            }
            (false, true) => {
                self.recorded_nondecided_observed_decided =
                    self.recorded_nondecided_observed_decided.saturating_add(1);
            }
            (false, false) => {
                self.nondecided_class_changes = self.nondecided_class_changes.saturating_add(1);
            }
            (true, true) => unreachable!("decided disagreement returned above"),
        }
        Ok(())
    }

    fn json(&self) -> Value {
        json!({
            "exact": self.exact,
            "recorded_decided_observed_nondecided":
                self.recorded_decided_observed_nondecided,
            "recorded_nondecided_observed_decided":
                self.recorded_nondecided_observed_decided,
            "nondecided_class_changes": self.nondecided_class_changes,
            "decided_disagreements": 0,
        })
    }
}

fn is_decided_outcome(outcome: &str) -> bool {
    matches!(outcome, "sat" | "unsat")
}

#[derive(Default)]
struct SnapshotReplayStats {
    checks: u64,
    unchanged_snapshots: u64,
    roots_retained: u64,
    roots_added: u64,
    roots_popped: u64,
    model_read_matches: u64,
    model_read_divergences: u64,
    model_reads_not_evaluable: u64,
    peak_aig_nodes: u64,
    peak_cnf_variables: u64,
    peak_cnf_clauses: u64,
    occurrence_latencies_nanos: Vec<u64>,
    check_latencies_nanos: Vec<u64>,
    outcomes: BTreeMap<String, u64>,
    depth: BTreeMap<usize, DepthReplayStats>,
    comparisons: OutcomeComparisonStats,
    continuations: TimeoutContinuationStats,
}

#[derive(Default)]
struct DepthReplayStats {
    checks: u64,
    occurrence_nanos: u64,
    recorded_z3_nanos: u64,
    recorded_z3_checks: u64,
}

// Snapshot replay is deliberately one ordered state machine: the consecutive
// LCP policy, pending model, and exact occurrence verdict stay visibly coupled.
#[allow(clippy::too_many_lines)]
fn replay_snapshot_trace(
    trace: &Trace,
    config: &SolverConfig,
    allow_nondecisions: bool,
    continue_on_unknown: bool,
) -> Result<Value, String> {
    let build_started = Instant::now();
    let program = build_warm_program(trace)?;
    let build_nanos = nanos(build_started.elapsed());
    let peak_rss_before = process_peak_rss_bytes();
    let replay_started = Instant::now();
    let mut solver = IncrementalBvSolver::with_config_and_profiling(config.clone());
    let mut active = Vec::<String>::new();
    let mut paths = BTreeMap::<String, Vec<Option<String>>>::new();
    let mut pending_model = None::<(String, Model)>;
    let mut stats = SnapshotReplayStats::default();

    for event in &trace.warm_events {
        match event {
            WarmEvent::PathStart {
                path_id,
                parent_path_id,
            } => {
                let scopes = parent_path_id.as_ref().map_or_else(
                    || Ok(Vec::new()),
                    |parent| {
                        paths.get(parent).cloned().ok_or_else(|| {
                            format!("snapshot fork {path_id} has no parent {parent}")
                        })
                    },
                )?;
                if paths.insert(path_id.clone(), scopes).is_some() {
                    return Err(format!("snapshot replay duplicates path {path_id}"));
                }
            }
            WarmEvent::Push { path_id } => {
                paths
                    .get_mut(path_id)
                    .ok_or_else(|| format!("snapshot push has no path {path_id}"))?
                    .push(None);
            }
            WarmEvent::Assert {
                path_id,
                constraint_id,
            } => {
                let scope = paths
                    .get_mut(path_id)
                    .and_then(|scopes| scopes.last_mut())
                    .ok_or_else(|| format!("snapshot assert has no scope on {path_id}"))?;
                if scope.replace(constraint_id.clone()).is_some() {
                    return Err(format!(
                        "snapshot path {path_id} asserts twice in one scope"
                    ));
                }
            }
            WarmEvent::Pop { path_id } => {
                let scopes = paths
                    .get_mut(path_id)
                    .ok_or_else(|| format!("snapshot pop has no path {path_id}"))?;
                if scopes.pop().is_none() {
                    return Err(format!("snapshot scope underflow on {path_id}"));
                }
            }
            WarmEvent::Check { path_id, check_id } => {
                let constraints = paths
                    .get(path_id)
                    .ok_or_else(|| format!("snapshot check {check_id} has no path {path_id}"))?
                    .iter()
                    .map(|constraint| {
                        constraint.as_deref().ok_or_else(|| {
                            format!("snapshot check {check_id} reaches an unasserted scope")
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let occurrence_started = Instant::now();
                let lcp = active
                    .iter()
                    .map(String::as_str)
                    .zip(&constraints)
                    .take_while(|(left, right)| left == *right)
                    .count();
                stats.roots_retained = stats.roots_retained.saturating_add(usize_to_u64(lcp));
                if active
                    .iter()
                    .map(String::as_str)
                    .eq(constraints.iter().copied())
                {
                    stats.unchanged_snapshots = stats.unchanged_snapshots.saturating_add(1);
                }
                for _ in lcp..active.len() {
                    if !solver.pop() {
                        return Err(format!("snapshot scope underflow on check {check_id}"));
                    }
                    stats.roots_popped = stats.roots_popped.saturating_add(1);
                }
                active.truncate(lcp);
                for &constraint_id in &constraints[lcp..] {
                    let term = program.constraints.get(constraint_id).ok_or_else(|| {
                        format!(
                            "snapshot check {check_id} reaches assertion {constraint_id} absent \
                             from the query store"
                        )
                    })?;
                    solver
                        .push()
                        .map_err(|error| format!("snapshot check {check_id} push: {error}"))?;
                    solver.assert(&program.arena, *term).map_err(|error| {
                        format!("snapshot check {check_id} assert {constraint_id}: {error}")
                    })?;
                    active.push(constraint_id.to_owned());
                    stats.roots_added = stats.roots_added.saturating_add(1);
                }
                if solver.scope_depth() != constraints.len()
                    || !active
                        .iter()
                        .map(String::as_str)
                        .eq(constraints.iter().copied())
                {
                    return Err(format!("snapshot scope differs on check {check_id}"));
                }
                let check = trace.checks.get(check_id).ok_or_else(|| {
                    format!("snapshot replay references missing check {check_id}")
                })?;
                let attempt = check_with_optional_continuation(continue_on_unknown, || {
                    solver.check(&program.arena)
                })
                .map_err(|error| format!("snapshot check {check_id}: {error}"))?;
                stats.check_latencies_nanos.push(attempt.total_nanos);
                stats.continuations.record(&attempt);
                let occurrence_nanos = nanos(occurrence_started.elapsed());
                stats.occurrence_latencies_nanos.push(occurrence_nanos);
                stats.checks = stats.checks.saturating_add(1);
                let (outcome, model) = split_result(attempt.result);
                *stats.outcomes.entry(outcome.to_string()).or_default() += 1;
                stats
                    .comparisons
                    .compare(check_id, &check.outcome, outcome, allow_nondecisions)?;
                let depth = stats.depth.entry(constraints.len()).or_default();
                depth.checks = depth.checks.saturating_add(1);
                depth.occurrence_nanos = depth.occurrence_nanos.saturating_add(occurrence_nanos);
                if let Some(z3_nanos) = check.z3_nanos {
                    depth.recorded_z3_nanos = depth.recorded_z3_nanos.saturating_add(z3_nanos);
                    depth.recorded_z3_checks = depth.recorded_z3_checks.saturating_add(1);
                }
                pending_model = model.map(|model| (check_id.clone(), model));
                let retained = solver.stats();
                stats.peak_aig_nodes = stats.peak_aig_nodes.max(retained.aig_nodes);
                stats.peak_cnf_variables = stats.peak_cnf_variables.max(retained.cnf_variables);
                stats.peak_cnf_clauses = stats.peak_cnf_clauses.max(retained.cnf_clauses);
            }
            WarmEvent::ModelRead { read_id, .. } => {
                let read = trace
                    .model_reads
                    .get(read_id)
                    .ok_or_else(|| format!("snapshot replay has no model read {read_id}"))?;
                let term = program.model_read_equalities.get(read_id).ok_or_else(|| {
                    format!("snapshot replay has no expression equality for read {read_id}")
                })?;
                let (check_id, model) = pending_model.as_ref().ok_or_else(|| {
                    format!("snapshot model read {read_id} has no pending SAT model")
                })?;
                if check_id != &read.check_id {
                    return Err(format!("snapshot model read {read_id} follows wrong check"));
                }
                match eval(&program.arena, *term, &model.to_assignment()) {
                    Ok(IrValue::Bool(true)) => {
                        stats.model_read_matches = stats.model_read_matches.saturating_add(1);
                    }
                    Ok(IrValue::Bool(false)) => {
                        stats.model_read_divergences =
                            stats.model_read_divergences.saturating_add(1);
                    }
                    Ok(_) | Err(_) => {
                        stats.model_reads_not_evaluable =
                            stats.model_reads_not_evaluable.saturating_add(1);
                    }
                }
            }
            WarmEvent::ModelChoice { .. } => pending_model = None,
            WarmEvent::PathEnd { path_id } => {
                if paths.remove(path_id).is_none() {
                    return Err(format!("snapshot replay ends missing path {path_id}"));
                }
            }
        }
    }
    if !paths.is_empty() {
        return Err("snapshot replay retains unterminated paths".into());
    }

    stats.occurrence_latencies_nanos.sort_unstable();
    stats.check_latencies_nanos.sort_unstable();
    let solver_stats = solver.stats();
    let replay_nanos = nanos(replay_started.elapsed());
    let measured_nanos = build_nanos.saturating_add(replay_nanos);
    let depth_buckets = depth_json(&stats.depth);
    let first_observed_faster_depth = stats.depth.iter().find_map(|(depth, stats)| {
        (stats.recorded_z3_checks == stats.checks
            && stats.occurrence_nanos < stats.recorded_z3_nanos)
            .then_some(*depth)
    });
    let observed_faster_depths = stats
        .depth
        .values()
        .filter(|stats| {
            stats.recorded_z3_checks == stats.checks
                && stats.occurrence_nanos < stats.recorded_z3_nanos
        })
        .count();
    let observed_slower_depths = stats
        .depth
        .values()
        .filter(|stats| {
            stats.recorded_z3_checks == stats.checks
                && stats.occurrence_nanos >= stats.recorded_z3_nanos
        })
        .count();
    let observed_unavailable_depths = stats
        .depth
        .values()
        .filter(|stats| stats.recorded_z3_checks != stats.checks)
        .count();
    let monotone_observed_break_even_depth = stats.depth.keys().find(|candidate| {
        stats.depth.range(**candidate..).all(|(_, stats)| {
            stats.recorded_z3_checks == stats.checks
                && stats.occurrence_nanos < stats.recorded_z3_nanos
        })
    });
    Ok(json!({
        "policy": {
            "entry": "consecutive complete snapshots reconstructed from ordered checks",
            "arena": "one shared parsed arena",
            "solver": "one retained solver with longest-common-prefix pop/push",
            "lineage_used": false,
            "preprocess": config.preprocess,
            "timeout_ms_per_check": config.timeout.map(|timeout| timeout.as_millis()),
            "allow_classified_nondecisions": allow_nondecisions,
            "continue_once_on_unknown": continue_on_unknown,
            "sat_model_replay": "IncrementalBvSolver original-assertion replay",
        },
        "shared_arena_build_nanos": build_nanos,
        "replay_nanos": replay_nanos,
        "ratio_to_recorded_z3_ppm_including_arena_build":
            same_stream_z3_ratio_ppm(trace, measured_nanos),
        "checks": stats.checks,
        "outcomes": stats.outcomes,
        "outcome_comparison": stats.comparisons.json(),
        "timeout_continuation": stats.continuations.json(continue_on_unknown),
        "unchanged_snapshots": stats.unchanged_snapshots,
        "roots_retained": stats.roots_retained,
        "roots_added": stats.roots_added,
        "roots_popped": stats.roots_popped,
        "occurrence_latency_p50_nanos": percentile(&stats.occurrence_latencies_nanos, 50),
        "occurrence_latency_p95_nanos": percentile(&stats.occurrence_latencies_nanos, 95),
        "check_latency_p50_nanos": percentile(&stats.check_latencies_nanos, 50),
        "check_latency_p95_nanos": percentile(&stats.check_latencies_nanos, 95),
        "model_read_matches": stats.model_read_matches,
        "model_read_divergences": stats.model_read_divergences,
        "model_reads_not_evaluable": stats.model_reads_not_evaluable,
        "scope_depth_buckets": depth_buckets,
        "first_observed_scope_depth_faster_than_recorded_z3": first_observed_faster_depth,
        "observed_scope_depths_faster_than_recorded_z3": observed_faster_depths,
        "observed_scope_depths_slower_than_recorded_z3": observed_slower_depths,
        "observed_scope_depths_without_recorded_z3": observed_unavailable_depths,
        "monotone_observed_break_even_scope_depth": monotone_observed_break_even_depth,
        "peak_retained_structure": {
            "aig_nodes": stats.peak_aig_nodes,
            "cnf_variables": stats.peak_cnf_variables,
            "cnf_clauses": stats.peak_cnf_clauses,
        },
        "phase_nanos": phase_json(&solver_stats),
        "process_peak_rss_bytes_before": peak_rss_before,
        "process_peak_rss_bytes_after": process_peak_rss_bytes(),
    }))
}

struct WarmProgram {
    arena: TermArena,
    constraints: BTreeMap<String, TermId>,
    model_read_equalities: BTreeMap<String, TermId>,
}

struct WarmPath {
    solver: IncrementalBvSolver,
    scopes: Vec<Option<String>>,
    materialized: Vec<bool>,
    pending_model: Option<(String, Model)>,
}

#[derive(Default)]
struct WarmReplayStats {
    path_states_created: u64,
    fork_states_created: u64,
    fork_prefix_roots_replayed: u64,
    fork_prefix_replay_nanos: u64,
    pushes: u64,
    assertions: u64,
    unmaterialized_assertions: u64,
    unmaterialized_fork_prefix_roots: u64,
    pops: u64,
    checks: u64,
    model_read_matches: u64,
    model_read_divergences: u64,
    model_reads_not_evaluable: u64,
    peak_live_paths: usize,
    peak_live_aig_nodes: u64,
    peak_live_cnf_variables: u64,
    peak_live_cnf_clauses: u64,
    total_word_rewrite_nanos: u64,
    total_bit_blast_nanos: u64,
    total_cnf_encode_nanos: u64,
    total_sat_nanos: u64,
    total_model_lift_nanos: u64,
    total_model_replay_nanos: u64,
    total_aig_nodes_by_path: u64,
    total_cnf_variables_by_path: u64,
    total_cnf_clauses_by_path: u64,
    check_latencies_nanos: Vec<u64>,
    outcomes: BTreeMap<String, u64>,
    comparisons: OutcomeComparisonStats,
    continuations: TimeoutContinuationStats,
}

// One ordered state machine owns the fork/scope/model invariants. Splitting the
// event handlers across independent passes would weaken their auditable order.
#[allow(clippy::too_many_lines)]
fn replay_warm_trace(
    trace: &Trace,
    config: &SolverConfig,
    allow_nondecisions: bool,
    continue_on_unknown: bool,
) -> Result<Value, String> {
    let build_started = Instant::now();
    let program = build_warm_program(trace)?;
    let build_nanos = nanos(build_started.elapsed());
    let peak_rss_before = process_peak_rss_bytes();
    let mut paths = BTreeMap::<String, WarmPath>::new();
    let mut stats = WarmReplayStats::default();
    let replay_started = Instant::now();

    for event in &trace.warm_events {
        match event {
            WarmEvent::PathStart {
                path_id,
                parent_path_id,
            } => {
                if paths.contains_key(path_id) {
                    return Err(format!("warm replay duplicates path {path_id}"));
                }
                let inherited_constraints = if let Some(parent_path_id) = parent_path_id {
                    let parent = paths.get(parent_path_id).ok_or_else(|| {
                        format!("warm fork {path_id} has no live parent {parent_path_id}")
                    })?;
                    stats.fork_states_created = stats.fork_states_created.saturating_add(1);
                    warm_constraints(parent, parent_path_id)?
                } else {
                    Vec::new()
                };

                let fork_started = Instant::now();
                let mut solver = IncrementalBvSolver::with_config_and_profiling(config.clone());
                let mut scopes = Vec::with_capacity(inherited_constraints.len());
                let mut materialized = Vec::with_capacity(inherited_constraints.len());
                for constraint_id in &inherited_constraints {
                    solver
                        .push()
                        .map_err(|error| format!("warm fork {path_id} push: {error}"))?;
                    let available = if let Some(term) = program.constraints.get(constraint_id) {
                        solver.assert(&program.arena, *term).map_err(|error| {
                            format!("warm fork {path_id} assert {constraint_id}: {error}")
                        })?;
                        true
                    } else {
                        stats.unmaterialized_fork_prefix_roots =
                            stats.unmaterialized_fork_prefix_roots.saturating_add(1);
                        false
                    };
                    scopes.push(Some(constraint_id.clone()));
                    materialized.push(available);
                }
                if parent_path_id.is_some() {
                    stats.fork_prefix_roots_replayed = stats
                        .fork_prefix_roots_replayed
                        .saturating_add(usize_to_u64(inherited_constraints.len()));
                    stats.fork_prefix_replay_nanos = stats
                        .fork_prefix_replay_nanos
                        .saturating_add(nanos(fork_started.elapsed()));
                }
                paths.insert(
                    path_id.clone(),
                    WarmPath {
                        solver,
                        scopes,
                        materialized,
                        pending_model: None,
                    },
                );
                stats.path_states_created = stats.path_states_created.saturating_add(1);
                refresh_warm_peaks(&paths, &mut stats);
            }
            WarmEvent::Push { path_id } => {
                let path = warm_path_mut(&mut paths, path_id)?;
                path.pending_model = None;
                path.solver
                    .push()
                    .map_err(|error| format!("warm path {path_id} push: {error}"))?;
                path.scopes.push(None);
                path.materialized.push(false);
                stats.pushes = stats.pushes.saturating_add(1);
                refresh_warm_peaks(&paths, &mut stats);
            }
            WarmEvent::Assert {
                path_id,
                constraint_id,
            } => {
                let path = warm_path_mut(&mut paths, path_id)?;
                path.pending_model = None;
                if path.scopes.last().is_none() {
                    return Err(format!("warm assert without push on {path_id}"));
                }
                if path.scopes.last().is_some_and(Option::is_some) {
                    return Err(format!("warm path {path_id} asserts twice in one scope"));
                }
                if let Some(term) = program.constraints.get(constraint_id) {
                    path.solver.assert(&program.arena, *term).map_err(|error| {
                        format!("warm path {path_id} assert {constraint_id}: {error}")
                    })?;
                    *path
                        .materialized
                        .last_mut()
                        .expect("scope and materialization stacks are parallel") = true;
                } else {
                    stats.unmaterialized_assertions =
                        stats.unmaterialized_assertions.saturating_add(1);
                }
                *path
                    .scopes
                    .last_mut()
                    .expect("scope presence checked above") = Some(constraint_id.clone());
                stats.assertions = stats.assertions.saturating_add(1);
                refresh_warm_peaks(&paths, &mut stats);
            }
            WarmEvent::Pop { path_id } => {
                let path = warm_path_mut(&mut paths, path_id)?;
                path.pending_model = None;
                if path.scopes.pop().is_none()
                    || path.materialized.pop().is_none()
                    || !path.solver.pop()
                {
                    return Err(format!("warm scope underflow on {path_id}"));
                }
                stats.pops = stats.pops.saturating_add(1);
            }
            WarmEvent::Check { path_id, check_id } => {
                let check = trace
                    .checks
                    .get(check_id)
                    .ok_or_else(|| format!("warm replay references missing check {check_id}"))?;
                let path = warm_path_mut(&mut paths, path_id)?;
                let constraints = warm_constraints(path, path_id)?;
                if path.solver.scope_depth() != constraints.len() {
                    return Err(format!("warm solver depth differs on check {check_id}"));
                }
                if path.materialized.iter().any(|available| !available) {
                    return Err(format!(
                        "warm check {check_id} reaches an assertion absent from the query store"
                    ));
                }
                let attempt = check_with_optional_continuation(continue_on_unknown, || {
                    path.solver.check(&program.arena)
                })
                .map_err(|error| format!("warm check {check_id}: {error}"))?;
                stats.check_latencies_nanos.push(attempt.total_nanos);
                stats.continuations.record(&attempt);
                stats.checks = stats.checks.saturating_add(1);
                let (outcome, model) = split_result(attempt.result);
                *stats.outcomes.entry(outcome.to_string()).or_default() += 1;
                stats
                    .comparisons
                    .compare(check_id, &check.outcome, outcome, allow_nondecisions)?;
                path.pending_model = model.map(|model| (check_id.clone(), model));
            }
            WarmEvent::ModelRead { path_id, read_id } => {
                let term = program.model_read_equalities.get(read_id).ok_or_else(|| {
                    format!("warm replay has no expression equality for model read {read_id}")
                })?;
                let read = trace
                    .model_reads
                    .get(read_id)
                    .ok_or_else(|| format!("warm replay has no model read {read_id}"))?;
                let path = warm_path_mut(&mut paths, path_id)?;
                let (check_id, model) = path
                    .pending_model
                    .as_ref()
                    .ok_or_else(|| format!("warm model read {read_id} has no pending SAT model"))?;
                if check_id != &read.check_id {
                    return Err(format!("warm model read {read_id} follows the wrong check"));
                }
                match eval(&program.arena, *term, &model.to_assignment()) {
                    Ok(IrValue::Bool(true)) => {
                        stats.model_read_matches = stats.model_read_matches.saturating_add(1);
                    }
                    Ok(IrValue::Bool(false)) => {
                        stats.model_read_divergences =
                            stats.model_read_divergences.saturating_add(1);
                    }
                    Ok(_) | Err(_) => {
                        stats.model_reads_not_evaluable =
                            stats.model_reads_not_evaluable.saturating_add(1);
                    }
                }
            }
            WarmEvent::ModelChoice { path_id } => {
                warm_path_mut(&mut paths, path_id)?.pending_model = None;
            }
            WarmEvent::PathEnd { path_id } => {
                let path = paths
                    .remove(path_id)
                    .ok_or_else(|| format!("warm replay ends missing path {path_id}"))?;
                let _ = warm_constraints(&path, path_id)?;
                accumulate_warm_path_stats(&path.solver.stats(), &mut stats);
            }
        }
    }
    if !paths.is_empty() {
        return Err("warm replay retains unterminated paths".into());
    }

    stats.check_latencies_nanos.sort_unstable();
    let replay_nanos = nanos(replay_started.elapsed());
    let measured_nanos = build_nanos.saturating_add(replay_nanos);
    Ok(json!({
        "policy": {
            "preprocess": config.preprocess,
            "timeout_ms_per_check": config.timeout.map(|timeout| timeout.as_millis()),
            "allow_classified_nondecisions": allow_nondecisions,
            "continue_once_on_unknown": continue_on_unknown,
            "fork_behavior": "fresh child solver plus validated inherited-prefix replay",
            "mutable_solver_state_shared_across_paths": false,
            "sat_model_replay": "IncrementalBvSolver original-assertion replay",
        },
        "shared_arena_build_nanos": build_nanos,
        "replay_nanos": replay_nanos,
        "ratio_to_recorded_z3_ppm_including_arena_build":
            same_stream_z3_ratio_ppm(trace, measured_nanos),
        "path_states_created": stats.path_states_created,
        "fork_states_created": stats.fork_states_created,
        "fork_prefix_roots_replayed": stats.fork_prefix_roots_replayed,
        "fork_prefix_replay_nanos": stats.fork_prefix_replay_nanos,
        "pushes": stats.pushes,
        "assertions": stats.assertions,
        "unmaterialized_assertions": stats.unmaterialized_assertions,
        "unmaterialized_fork_prefix_roots": stats.unmaterialized_fork_prefix_roots,
        "pops": stats.pops,
        "checks": stats.checks,
        "outcomes": stats.outcomes,
        "outcome_comparison": stats.comparisons.json(),
        "timeout_continuation": stats.continuations.json(continue_on_unknown),
        "check_latency_p50_nanos": percentile(&stats.check_latencies_nanos, 50),
        "check_latency_p95_nanos": percentile(&stats.check_latencies_nanos, 95),
        "model_read_matches": stats.model_read_matches,
        "model_read_divergences": stats.model_read_divergences,
        "model_reads_not_evaluable": stats.model_reads_not_evaluable,
        "peak_live_paths": stats.peak_live_paths,
        "peak_live_aig_nodes": stats.peak_live_aig_nodes,
        "peak_live_cnf_variables": stats.peak_live_cnf_variables,
        "peak_live_cnf_clauses": stats.peak_live_cnf_clauses,
        "phase_nanos": {
            "word_rewrite": stats.total_word_rewrite_nanos,
            "bit_blast": stats.total_bit_blast_nanos,
            "cnf_encode": stats.total_cnf_encode_nanos,
            "sat": stats.total_sat_nanos,
            "model_lift": stats.total_model_lift_nanos,
            "model_replay": stats.total_model_replay_nanos,
        },
        "total_retained_structure_by_path": {
            "aig_nodes": stats.total_aig_nodes_by_path,
            "cnf_variables": stats.total_cnf_variables_by_path,
            "cnf_clauses": stats.total_cnf_clauses_by_path,
        },
        "process_peak_rss_bytes_before": peak_rss_before,
        "process_peak_rss_bytes_after": process_peak_rss_bytes(),
    }))
}

fn build_warm_program(trace: &Trace) -> Result<WarmProgram, String> {
    let mut declarations = BTreeSet::<String>::new();
    let mut constraint_text = BTreeMap::<String, String>::new();
    for (constraint_id, bytes) in &trace.assertions {
        let assertion = std::str::from_utf8(bytes)
            .map_err(|error| format!("assertion {constraint_id} is non-UTF-8: {error}"))?;
        constraint_text.insert(constraint_id.clone(), assertion.to_string());
        let symbols = trace
            .assertion_symbols
            .get(constraint_id)
            .ok_or_else(|| format!("assertion {constraint_id} has no free-symbol declarations"))?;
        for (name, width) in symbols {
            declarations.insert(format!("(declare-const {name} (_ BitVec {width}))\n"));
        }
    }
    if trace.assertions.is_empty() {
        for (query_hash, query) in &trace.queries {
            let bytes = query.read_bytes()?;
            let text = std::str::from_utf8(&bytes)
                .map_err(|error| format!("query {query_hash} is non-UTF-8: {error}"))?;
            for line in text.split_inclusive('\n') {
                if line.starts_with("(declare-const ") || line.starts_with("(declare-fun ") {
                    declarations.insert(line.to_string());
                } else if line.starts_with("(assert ") {
                    let constraint_id = sha256(line.as_bytes());
                    if let Some(previous) =
                        constraint_text.insert(constraint_id.clone(), line.into())
                        && previous != line
                    {
                        return Err(format!("constraint SHA-256 collision at {constraint_id}"));
                    }
                }
            }
        }
    }
    for read in trace.model_reads.values() {
        for (name, width) in &read.symbols {
            declarations.insert(format!("(declare-const {name} (_ BitVec {width}))\n"));
        }
    }

    let mut source = String::from("(set-logic QF_BV)\n");
    for declaration in declarations {
        source.push_str(&declaration);
        if !declaration.ends_with('\n') {
            source.push('\n');
        }
    }
    let constraint_ids = constraint_text.keys().cloned().collect::<Vec<_>>();
    for assertion in constraint_text.values() {
        source.push_str(assertion);
        if !assertion.ends_with('\n') {
            source.push('\n');
        }
    }
    let read_ids = trace.model_reads.keys().cloned().collect::<Vec<_>>();
    for read in trace.model_reads.values() {
        writeln!(
            source,
            "(assert (= {} (_ bv{} {})))",
            read.expression, read.returned_value, read.width
        )
        .map_err(|error| format!("render warm model-read equality: {error}"))?;
    }
    source.push_str("(check-sat)\n");
    let script = parse_script(&source).map_err(|error| format!("warm shared parse: {error}"))?;
    if script.logic.as_deref() != Some("QF_BV") || script.solvable_flat_view().is_none() {
        return Err("warm shared script is not a flat QF_BV problem".into());
    }
    if script.assertions.len() != constraint_ids.len() + read_ids.len() {
        return Err("warm shared parse changed the assertion count".into());
    }
    let constraints = constraint_ids
        .into_iter()
        .zip(script.assertions.iter().copied())
        .collect();
    let model_read_equalities = read_ids
        .into_iter()
        .zip(script.assertions[constraint_text.len()..].iter().copied())
        .collect();
    Ok(WarmProgram {
        arena: script.arena,
        constraints,
        model_read_equalities,
    })
}

fn warm_path_mut<'a>(
    paths: &'a mut BTreeMap<String, WarmPath>,
    path_id: &str,
) -> Result<&'a mut WarmPath, String> {
    paths
        .get_mut(path_id)
        .ok_or_else(|| format!("warm event references missing path {path_id}"))
}

fn warm_constraints(path: &WarmPath, path_id: &str) -> Result<Vec<String>, String> {
    path.scopes
        .iter()
        .map(|constraint| {
            constraint
                .clone()
                .ok_or_else(|| format!("warm path {path_id} has an unasserted scope"))
        })
        .collect()
}

fn refresh_warm_peaks(paths: &BTreeMap<String, WarmPath>, stats: &mut WarmReplayStats) {
    stats.peak_live_paths = stats.peak_live_paths.max(paths.len());
    let (aig_nodes, cnf_variables, cnf_clauses) = paths.values().fold(
        (0_u64, 0_u64, 0_u64),
        |(aig_nodes, cnf_variables, cnf_clauses), path| {
            let path_stats = path.solver.stats();
            (
                aig_nodes.saturating_add(path_stats.aig_nodes),
                cnf_variables.saturating_add(path_stats.cnf_variables),
                cnf_clauses.saturating_add(path_stats.cnf_clauses),
            )
        },
    );
    stats.peak_live_aig_nodes = stats.peak_live_aig_nodes.max(aig_nodes);
    stats.peak_live_cnf_variables = stats.peak_live_cnf_variables.max(cnf_variables);
    stats.peak_live_cnf_clauses = stats.peak_live_cnf_clauses.max(cnf_clauses);
}

fn accumulate_warm_path_stats(
    path: &axeyum_solver::IncrementalBvStats,
    stats: &mut WarmReplayStats,
) {
    stats.total_word_rewrite_nanos = stats
        .total_word_rewrite_nanos
        .saturating_add(nanos(path.word_rewrite));
    stats.total_bit_blast_nanos = stats
        .total_bit_blast_nanos
        .saturating_add(nanos(path.bit_blast));
    stats.total_cnf_encode_nanos = stats
        .total_cnf_encode_nanos
        .saturating_add(nanos(path.cnf_encode));
    stats.total_sat_nanos = stats.total_sat_nanos.saturating_add(nanos(path.solve));
    stats.total_model_lift_nanos = stats
        .total_model_lift_nanos
        .saturating_add(nanos(path.model_lift));
    stats.total_model_replay_nanos = stats
        .total_model_replay_nanos
        .saturating_add(nanos(path.replay));
    stats.total_aig_nodes_by_path = stats.total_aig_nodes_by_path.saturating_add(path.aig_nodes);
    stats.total_cnf_variables_by_path = stats
        .total_cnf_variables_by_path
        .saturating_add(path.cnf_variables);
    stats.total_cnf_clauses_by_path = stats
        .total_cnf_clauses_by_path
        .saturating_add(path.cnf_clauses);
}

fn percentile(sorted: &[u64], percent: usize) -> u64 {
    if sorted.is_empty() {
        return 0;
    }
    let index = (sorted.len() - 1).saturating_mul(percent).div_ceil(100);
    sorted[index.min(sorted.len() - 1)]
}

fn same_stream_z3_ratio_ppm(trace: &Trace, axeyum_nanos: u64) -> Option<u64> {
    (trace.backend_timing.z3_timed_checks == usize_to_u64(trace.checks.len())
        && trace.backend_timing.z3_nanos > 0)
        .then(|| ratio_ppm(axeyum_nanos, trace.backend_timing.z3_nanos))
}

fn depth_json(depth: &BTreeMap<usize, DepthReplayStats>) -> Vec<Value> {
    depth
        .iter()
        .map(|(scope_depth, stats)| {
            let ratio = (stats.recorded_z3_checks == stats.checks && stats.recorded_z3_nanos > 0)
                .then(|| ratio_ppm(stats.occurrence_nanos, stats.recorded_z3_nanos));
            json!({
                "scope_depth": scope_depth,
                "checks": stats.checks,
                "snapshot_occurrence_nanos": stats.occurrence_nanos,
                "recorded_z3_nanos": stats.recorded_z3_nanos,
                "recorded_z3_checks": stats.recorded_z3_checks,
                "ratio_to_recorded_z3_ppm": ratio,
            })
        })
        .collect()
}

fn ratio_ppm(numerator: u64, denominator: u64) -> u64 {
    if denominator == 0 {
        return 0;
    }
    let scaled = u128::from(numerator).saturating_mul(1_000_000) / u128::from(denominator);
    u64::try_from(scaled).unwrap_or(u64::MAX)
}

fn usize_to_u64(value: usize) -> u64 {
    u64::try_from(value).unwrap_or(u64::MAX)
}

fn parse_model_read(event: &Value, path_id: &str) -> Result<ModelRead, String> {
    let read_id = string(event, "model_read_id")?.to_string();
    let check_id = string(event, "check_id")?.to_string();
    let expression_id = string(event, "expression_id")?.to_string();
    let expression = string(event, "expression_smtlib")?.to_string();
    if event
        .get("affected_exploration")
        .and_then(Value::as_bool)
        .is_none()
    {
        return Err(format!(
            "model read {read_id} has no Boolean affected_exploration"
        ));
    }
    let width = integer(event, "width")?;
    if width == 0 || string(event, "sort")? != format!("(_ BitVec {width})") {
        return Err(format!("invalid model-read sort for {read_id}"));
    }
    if sha256(format!("{width}\0{expression}").as_bytes()) != expression_id {
        return Err(format!("model-read expression hash mismatch for {read_id}"));
    }
    let symbols = parse_symbol_declarations(
        event,
        "expression_symbols",
        &format!("model read {read_id}"),
    )?;
    let returned_value = parse_hex(string(event, "returned_value")?)?;
    if width < 128 && returned_value >= (1_u128 << width) {
        return Err(format!("model-read value is out of range for {read_id}"));
    }
    Ok(ModelRead {
        read_id,
        check_id,
        path_id: path_id.to_string(),
        expression_id,
        expression,
        symbols,
        width,
        returned_value,
    })
}

fn parse_symbol_declarations(
    event: &Value,
    field: &str,
    label: &str,
) -> Result<Vec<(String, u64)>, String> {
    let mut symbols = Vec::new();
    let mut previous_id = None;
    for symbol in array(event, field)? {
        let name = string(symbol, "name")?.to_string();
        let symbol_width = integer(symbol, "width")?;
        let (symbol_id, encoded_width) = parse_symbol_name(&name)?;
        if encoded_width != symbol_width || previous_id.is_some_and(|prior| prior >= symbol_id) {
            return Err(format!("invalid/unsorted symbol {name} for {label}"));
        }
        previous_id = Some(symbol_id);
        symbols.push((name, symbol_width));
    }
    Ok(symbols)
}

fn validate_qf_bv_script(label: &str, bytes: &[u8]) -> Result<(), String> {
    let text =
        std::str::from_utf8(bytes).map_err(|error| format!("{label}: non-UTF-8: {error}"))?;
    let script = parse_script(text).map_err(|error| format!("{label}: strict parse: {error}"))?;
    if script.logic.as_deref() != Some("QF_BV") {
        return Err(format!(
            "{label}: logic is {:?}, expected QF_BV",
            script.logic
        ));
    }
    if script.solvable_flat_view().is_none() {
        return Err(format!("{label}: unexpected word-only fallback"));
    }
    let checks = script
        .commands
        .iter()
        .filter(|command| {
            matches!(
                command,
                ScriptCommand::CheckSat | ScriptCommand::CheckSatAssuming(_)
            )
        })
        .count();
    if checks != 1 {
        return Err(format!("{label}: expected one check-sat, found {checks}"));
    }
    Ok(())
}

fn solve_text(bytes: &[u8], config: &SolverConfig) -> Result<String, String> {
    let text = std::str::from_utf8(bytes).map_err(|error| format!("non-UTF-8 query: {error}"))?;
    let outcome = solve_smtlib(text, config).map_err(|error| error.to_string())?;
    Ok(match outcome.result {
        CheckResult::Sat(_) => "sat".to_string(),
        CheckResult::Unsat => "unsat".to_string(),
        CheckResult::Unknown(reason) => format!("unknown:{:?}:{}", reason.kind, reason.detail),
    })
}

fn result_name(result: &CheckResult) -> &'static str {
    match result {
        CheckResult::Sat(_) => "sat",
        CheckResult::Unsat => "unsat",
        CheckResult::Unknown(_) => "unknown",
    }
}

fn split_result(result: CheckResult) -> (&'static str, Option<Model>) {
    match result {
        CheckResult::Sat(model) => ("sat", Some(model)),
        CheckResult::Unsat => ("unsat", None),
        CheckResult::Unknown(_) => ("unknown", None),
    }
}

fn phase_json(stats: &axeyum_solver::IncrementalBvStats) -> Value {
    json!({
        "word_rewrite": nanos(stats.word_rewrite),
        "bit_blast": nanos(stats.bit_blast),
        "cnf_encode": nanos(stats.cnf_encode),
        "sat": nanos(stats.solve),
        "model_lift": nanos(stats.model_lift),
        "model_replay": nanos(stats.replay),
    })
}

fn append_choice_assertion(query: &[u8], read: &ModelRead) -> Result<String, String> {
    let text = std::str::from_utf8(query).map_err(|error| format!("non-UTF-8 query: {error}"))?;
    let marker = "(check-sat)";
    let position = text
        .find(marker)
        .ok_or_else(|| "choice query has no (check-sat)".to_string())?;
    if text[position + marker.len()..].contains(marker) {
        return Err("choice query has multiple (check-sat) commands".into());
    }
    let mut constrained = String::with_capacity(text.len() + read.expression.len() + 128);
    constrained.push_str(&text[..position]);
    if !constrained.ends_with('\n') {
        constrained.push('\n');
    }
    for (name, width) in &read.symbols {
        let declaration_prefix = format!("(declare-const {name} ");
        if !text.contains(&declaration_prefix) {
            writeln!(constrained, "(declare-const {name} (_ BitVec {width}))")
                .map_err(|error| format!("render model-choice declaration: {error}"))?;
        }
    }
    writeln!(
        constrained,
        "(assert (= {} (_ bv{} {})))",
        read.expression, read.returned_value, read.width
    )
    .map_err(|error| format!("render model-choice assertion: {error}"))?;
    constrained.push_str(&text[position..]);
    Ok(constrained)
}

fn complete_constraints(state: &PathState, path_id: &str) -> Result<Vec<String>, String> {
    state
        .scopes
        .iter()
        .map(|scope| {
            scope
                .constraint_id
                .clone()
                .ok_or_else(|| format!("unasserted scope on {path_id}"))
        })
        .collect()
}

fn classify_reuse(stats: &mut ReuseStats, previous: &[String], current: &[String]) {
    if previous.is_empty() {
        return;
    }
    let lcp = previous
        .iter()
        .zip(current)
        .take_while(|(left, right)| left == right)
        .count();
    if previous == current {
        stats.same_lineage_repeats += 1;
    } else if lcp == previous.len() {
        stats.prefix_extensions += 1;
        stats.prefix_delta_assertions += current.len() - previous.len();
    } else {
        stats.divergent_checks += 1;
    }
}

fn assertion_sequence_identity(bytes: &[u8]) -> (usize, String) {
    let mut hasher = Sha256::new();
    hasher.update(b"axeyum-ordered-query-assertions-v1\0");
    let mut count = 0;
    for line in bytes
        .split_inclusive(|byte| *byte == b'\n')
        .filter(|line| line.starts_with(b"(assert "))
    {
        let constraint_id = sha256(line);
        hash_framed(&mut hasher, constraint_id.as_bytes());
        count += 1;
    }
    (count, hex_digest(&hasher.finalize()))
}

fn constraint_sequence_identity(constraints: &[String]) -> (usize, String) {
    let mut hasher = Sha256::new();
    hasher.update(b"axeyum-ordered-query-assertions-v1\0");
    for constraint in constraints {
        hash_framed(&mut hasher, constraint.as_bytes());
    }
    (constraints.len(), hex_digest(&hasher.finalize()))
}

fn scope_digest(scopes: &[ScopeState]) -> Result<String, String> {
    let mut hasher = Sha256::new();
    hasher.update(b"glaurung-scope-digest-v1\0");
    for scope in scopes {
        hash_framed(&mut hasher, scope.scope_id.as_bytes());
        let constraint = scope
            .constraint_id
            .as_ref()
            .ok_or_else(|| format!("scope {} has no assertion", scope.scope_id))?;
        hash_framed(&mut hasher, constraint.as_bytes());
    }
    Ok(hex_digest(&hasher.finalize()))
}

fn hash_framed(hasher: &mut Sha256, bytes: &[u8]) {
    hasher.update((bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
}

fn sha256(bytes: impl AsRef<[u8]>) -> String {
    hex_digest(&Sha256::digest(bytes.as_ref()))
}

fn hex_digest(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        output.push(char::from(HEX[usize::from(byte >> 4)]));
        output.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    output
}

fn parse_symbol_name(name: &str) -> Result<(u64, u64), String> {
    let body = name
        .strip_prefix("sym")
        .ok_or_else(|| format!("invalid symbol name {name}"))?;
    let (id, width) = body
        .split_once('_')
        .ok_or_else(|| format!("invalid symbol name {name}"))?;
    Ok((
        id.parse()
            .map_err(|_| format!("invalid symbol ID {name}"))?,
        width
            .parse()
            .map_err(|_| format!("invalid symbol width {name}"))?,
    ))
}

fn parse_hex(value: &str) -> Result<u128, String> {
    let digits = value
        .strip_prefix("0x")
        .ok_or_else(|| format!("model value is not hexadecimal: {value}"))?;
    u128::from_str_radix(digits, 16).map_err(|_| format!("invalid model value: {value}"))
}

fn require_sequence(event: &Value, field: &str, expected: &mut u64) -> Result<(), String> {
    let actual = integer(event, field)?;
    if actual != *expected {
        return Err(format!("non-contiguous {field}: {actual} != {expected}"));
    }
    *expected += 1;
    Ok(())
}

fn read(path: &Path) -> Result<Vec<u8>, String> {
    fs::read(path).map_err(|error| format!("read {}: {error}", path.display()))
}

fn string<'a>(value: &'a Value, field: &str) -> Result<&'a str, String> {
    value
        .get(field)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("missing/non-string field {field}"))
}

fn integer(value: &Value, field: &str) -> Result<u64, String> {
    value
        .get(field)
        .and_then(Value::as_u64)
        .ok_or_else(|| format!("missing/non-integer field {field}"))
}

fn optional_integer(value: &Value, field: &str) -> Result<Option<u64>, String> {
    match value.get(field) {
        None | Some(Value::Null) => Ok(None),
        Some(value) => value
            .as_u64()
            .map(Some)
            .ok_or_else(|| format!("non-integer field {field}")),
    }
}

fn usize_integer(value: &Value, field: &str) -> Result<usize, String> {
    usize::try_from(integer(value, field)?).map_err(|_| format!("field {field} does not fit usize"))
}

fn array<'a>(value: &'a Value, field: &str) -> Result<&'a [Value], String> {
    value
        .get(field)
        .and_then(Value::as_array)
        .map(Vec::as_slice)
        .ok_or_else(|| format!("missing/non-array field {field}"))
}

fn fraction_ppm(numerator: usize, denominator: usize) -> u64 {
    if denominator == 0 {
        0
    } else {
        let scaled = (numerator as u128) * 1_000_000 / (denominator as u128);
        u64::try_from(scaled).unwrap_or(u64::MAX)
    }
}

fn nanos(duration: Duration) -> u64 {
    u64::try_from(duration.as_nanos()).unwrap_or(u64::MAX)
}

fn process_peak_rss_bytes() -> Option<u64> {
    let status = fs::read_to_string("/proc/self/status").ok()?;
    let kibibytes = status.lines().find_map(|line| {
        let value = line.strip_prefix("VmHWM:")?;
        value.split_whitespace().next()?.parse::<u64>().ok()
    })?;
    kibibytes.checked_mul(1024)
}

fn write_json_atomic(path: &Path, value: &Value) -> Result<(), String> {
    let mut bytes = serde_json::to_vec_pretty(value)
        .map_err(|error| format!("serialize replay summary: {error}"))?;
    bytes.push(b'\n');
    let temp = path.with_extension(format!("tmp-{}", std::process::id()));
    fs::write(&temp, bytes).map_err(|error| format!("write {}: {error}", temp.display()))?;
    fs::rename(&temp, path).map_err(|error| {
        format!(
            "publish replay summary {} as {}: {error}",
            temp.display(),
            path.display()
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn timeout_experiment_requires_a_retained_replay_policy() {
        let error = Options::parse(
            [
                "trace".to_string(),
                "--policy-timeout-ms".to_string(),
                "250".to_string(),
            ]
            .into_iter(),
        )
        .expect_err("a policy timeout without snapshot/lineage must fail");
        assert!(error.contains("--snapshot or --lineage"));

        let error = Options::parse(
            [
                "trace".to_string(),
                "--snapshot".to_string(),
                "--continue-on-unknown".to_string(),
            ]
            .into_iter(),
        )
        .expect_err("continuation without an explicit policy timeout must fail");
        assert!(error.contains("--policy-timeout-ms"));
    }

    #[test]
    fn same_instance_continuation_preserves_or_recovers_unknown() {
        let unknown = || {
            let mut solver =
                IncrementalBvSolver::with_config(SolverConfig::new().with_timeout(Duration::ZERO));
            let arena = TermArena::new();
            solver
                .check(&arena)
                .expect("an empty incremental query is well formed")
        };
        assert!(matches!(unknown(), CheckResult::Unknown(_)));

        let mut repeated = [Ok::<_, &str>(unknown()), Ok(unknown())].into_iter();
        let attempt = check_with_optional_continuation(true, || {
            repeated.next().expect("two scripted checks")
        })
        .expect("scripted checks do not error");
        assert!(matches!(attempt.result, CheckResult::Unknown(_)));
        assert_eq!(attempt.continuation, ContinuationOutcome::RepeatedUnknown);

        let mut recovered = [Ok::<_, &str>(unknown()), Ok(CheckResult::Unsat)].into_iter();
        let attempt = check_with_optional_continuation(true, || {
            recovered.next().expect("two scripted checks")
        })
        .expect("scripted checks do not error");
        assert!(matches!(attempt.result, CheckResult::Unsat));
        assert_eq!(attempt.continuation, ContinuationOutcome::RecoveredUnsat);

        let mut errored = [Ok(unknown()), Err("second-check failure")].into_iter();
        let attempt =
            check_with_optional_continuation(true, || errored.next().expect("two scripted checks"))
                .expect("a continuation error preserves the original unknown");
        assert!(matches!(attempt.result, CheckResult::Unknown(_)));
        assert_eq!(attempt.continuation, ContinuationOutcome::Error);
    }

    #[test]
    fn bounded_policy_never_accepts_a_decided_disagreement_or_hidden_timeout() {
        let mut comparisons = OutcomeComparisonStats::default();
        let error = comparisons
            .compare("check-0", "sat", "unsat", true)
            .expect_err("opposite decided verdicts are always fatal");
        assert!(error.contains("decided verdict disagreement"));

        let error = comparisons
            .compare("check-1", "sat", "unknown", false)
            .expect_err("default replay remains strict on nondecisions");
        assert!(error.contains("verdict disagreement"));

        comparisons
            .compare("check-2", "sat", "unknown", true)
            .expect("an explicit bounded policy reports rather than hides a timeout");
        assert_eq!(comparisons.recorded_decided_observed_nondecided, 1);
        assert_eq!(comparisons.json()["decided_disagreements"], 0);

        let error = comparisons
            .compare("check-3", "error", "error", true)
            .expect_err("an operational error is never an exact successful outcome");
        assert!(error.contains("operational error outcome"));
    }

    fn warm_test_trace(
        queries: BTreeMap<String, QueryRecord>,
        checks: BTreeMap<String, CheckRecord>,
        warm_events: Vec<WarmEvent>,
    ) -> Trace {
        Trace {
            analysis_id: "analysis-test".into(),
            process_id: "process-test".into(),
            manifest_hash: "manifest-test".into(),
            events_hash: "events-test".into(),
            event_count: warm_events.len(),
            path_count: 2,
            queries,
            assertions: BTreeMap::new(),
            assertion_symbols: BTreeMap::new(),
            checks,
            model_reads: BTreeMap::new(),
            model_choice_count: 0,
            recorded_outcomes: BTreeMap::new(),
            unique_query_outcomes: BTreeMap::new(),
            query_replay_nanos: 0,
            query_validation_worker_batches: 0,
            query_validation_worker_peak_rss_bytes: 0,
            backend_timing: BackendTimingStats::default(),
            reuse: ReuseStats::default(),
            warm_events,
        }
    }

    #[test]
    fn choice_assertion_declares_missing_symbols_before_check() {
        let read = ModelRead {
            read_id: "read-0".into(),
            check_id: "check-0".into(),
            path_id: "path-0".into(),
            expression_id: String::new(),
            expression: "(bvadd sym0_8 sym1_8)".into(),
            symbols: vec![("sym0_8".into(), 8), ("sym1_8".into(), 8)],
            width: 8,
            returned_value: 3,
        };
        let query = b"(set-logic QF_BV)\n(declare-const sym0_8 (_ BitVec 8))\n(check-sat)\n";
        let constrained = append_choice_assertion(query, &read).unwrap();
        assert_eq!(constrained.matches("declare-const sym0_8").count(), 1);
        assert!(constrained.contains("(declare-const sym1_8 (_ BitVec 8))"));
        assert!(constrained.contains("(assert (= (bvadd sym0_8 sym1_8) (_ bv3 8)))"));
        assert!(constrained.find("(assert").unwrap() < constrained.find("(check-sat)").unwrap());
    }

    #[test]
    fn scope_digest_is_order_and_identity_sensitive() {
        let scopes = vec![ScopeState {
            scope_id: "scope-1".into(),
            constraint_id: Some("constraint-1".into()),
        }];
        let digest = scope_digest(&scopes).unwrap();
        assert_eq!(digest.len(), 64);
        let changed = vec![ScopeState {
            scope_id: "scope-2".into(),
            constraint_id: Some("constraint-1".into()),
        }];
        assert_ne!(digest, scope_digest(&changed).unwrap());
    }

    #[test]
    fn native_warm_metadata_binds_partition_prefix_and_sync_result() {
        let scopes = vec![
            ScopeState {
                scope_id: "scope-0".into(),
                constraint_id: Some("constraint-0".into()),
            },
            ScopeState {
                scope_id: "scope-1".into(),
                constraint_id: Some("constraint-1".into()),
            },
        ];
        let mut warm = json!({
            "owner_id": 7,
            "requested_retain_assertions": 1,
            "persistent_assertions": 1,
            "temporary_assertions": 1,
            "synchronized": true,
            "source_prefix_digest": scope_digest(&scopes[..1]).unwrap(),
        })
        .as_object()
        .cloned()
        .unwrap();
        validate_native_warm_metadata(&warm, &scopes, "check-0").unwrap();

        warm.insert("synchronized".into(), Value::Null);
        assert!(
            validate_native_warm_metadata(&warm, &scopes, "check-0")
                .unwrap_err()
                .contains("inconsistent native warm replay metadata")
        );
        warm.insert("synchronized".into(), Value::Bool(true));
        warm.insert("source_prefix_digest".into(), Value::String("bad".into()));
        assert!(validate_native_warm_metadata(&warm, &scopes, "check-0").is_err());
    }

    #[test]
    fn assertion_store_is_content_addressed_and_manifest_complete() {
        let root = env::temp_dir().join(format!(
            "axeyum-ordered-assertion-test-{}-{}",
            std::process::id(),
            nanos(Instant::now().elapsed())
        ));
        fs::create_dir_all(root.join("assertions")).unwrap();
        let bytes = b"(assert true)\n";
        let constraint_id = sha256(bytes);
        fs::write(
            root.join("assertions")
                .join(format!("{constraint_id}.smt2")),
            bytes,
        )
        .unwrap();
        let loaded = load_assertions(&root, &json!({"assertion_count": 1})).unwrap();
        assert_eq!(
            loaded.get(&constraint_id).map(Vec::as_slice),
            Some(&bytes[..])
        );
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn validation_worker_checks_query_before_parent_retains_only_compact_identity() {
        let root = env::temp_dir().join(format!(
            "axeyum-ordered-query-test-{}-{}",
            std::process::id(),
            nanos(Instant::now().elapsed())
        ));
        fs::create_dir_all(root.join("queries")).unwrap();
        let bytes = b"(set-logic QF_BV)\n(assert true)\n(check-sat)\n";
        let hash = sha256(bytes);
        fs::write(root.join("queries").join(format!("{hash}.smt2")), bytes).unwrap();
        let index = json!({
            "version": 1,
            "queries": [{
                "content_hash": hash,
                "path": format!("queries/{hash}.smt2"),
                "outcomes": ["sat"],
                "occurrences": [],
            }],
        });
        let index_bytes = serde_json::to_vec(&index).unwrap();
        fs::write(root.join("query-index-v1.json"), &index_bytes).unwrap();
        let manifest = json!({
            "schema": TRACE_SCHEMA,
            "version": 1,
            "query_index_sha256": sha256(&index_bytes),
        });
        fs::write(
            root.join("trace-manifest-v1.json"),
            serde_json::to_vec(&manifest).unwrap(),
        )
        .unwrap();
        let worker = run_query_validation_worker(&root, &SolverConfig::new(), 0, 1).unwrap();
        assert_eq!(worker["schema"], VALIDATION_WORKER_SCHEMA);
        assert_eq!(worker["records"][0]["outcome"], "sat");
        assert!(worker["process_peak_rss_bytes"].as_u64().unwrap() > 0);
        let assertion_count = usize_integer(&worker["records"][0], "assertion_count").unwrap();
        let assertion_sequence_digest = string(&worker["records"][0], "assertion_sequence_digest")
            .unwrap()
            .to_string();
        let validated = BTreeMap::from([(
            hash.clone(),
            ValidatedQuery {
                assertion_count,
                assertion_sequence_digest: assertion_sequence_digest.clone(),
                outcome: "sat".into(),
            },
        )]);
        let queries = load_queries(&root, &index, &validated).unwrap();
        let query = queries.get(&hash).unwrap();
        assert!(query.is_file_backed());
        assert_eq!(query.read_bytes().unwrap(), bytes);
        assert_eq!(query.assertion_count, assertion_count);
        assert_eq!(query.assertion_sequence_digest, assertion_sequence_digest);
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn compact_assertion_identity_preserves_exact_order_and_count() {
        let first = sha256(b"(assert (= x (_ bv1 8)))\n");
        let second = sha256(b"(assert (= y (_ bv2 8)))\n");
        let bytes = b"(set-logic QF_BV)\n(assert (= x (_ bv1 8)))\n\
                      (assert (= y (_ bv2 8)))\n(check-sat)\n";
        let query_identity = assertion_sequence_identity(bytes);
        assert_eq!(
            query_identity,
            constraint_sequence_identity(&[first.clone(), second.clone()])
        );
        assert_ne!(
            query_identity,
            constraint_sequence_identity(&[second, first.clone()])
        );
        assert_ne!(query_identity, constraint_sequence_identity(&[first]));
    }

    #[test]
    fn compact_occurrence_identity_preserves_exact_order_and_fields() {
        let mut expected = OccurrenceAccumulator::default();
        expected.record("check-1", "path-2", 3);
        expected.record("check-4", "path-5", 6);
        let expected = expected.identity();

        let mut reordered = OccurrenceAccumulator::default();
        reordered.record("check-4", "path-5", 6);
        reordered.record("check-1", "path-2", 3);
        let reordered = reordered.identity();
        assert_eq!(expected.count, reordered.count);
        assert_ne!(expected.digest, reordered.digest);

        let mut changed = OccurrenceAccumulator::default();
        changed.record("check-1", "path-2", 7);
        let changed = changed.identity();
        assert_ne!(expected.count, changed.count);
        assert_ne!(expected.digest, changed.digest);
    }

    #[test]
    fn warm_fork_replays_a_validated_parent_prefix_without_sharing_solver_state() {
        let assertion = "(assert (= x (_ bv1 8)))\n";
        let constraint_id = sha256(assertion);
        let query =
            format!("(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n{assertion}(check-sat)\n");
        let query_hash = sha256(query.as_bytes());
        let queries = BTreeMap::from([(
            query_hash.clone(),
            QueryRecord::inline(query.into_bytes(), BTreeSet::from(["sat".into()])),
        )]);
        let checks = BTreeMap::from([
            (
                "check-parent".into(),
                CheckRecord {
                    check_id: "check-parent".into(),
                    path_id: "parent".into(),
                    query_hash: query_hash.clone(),
                    outcome: "sat".into(),
                    z3_nanos: None,
                },
            ),
            (
                "check-child".into(),
                CheckRecord {
                    check_id: "check-child".into(),
                    path_id: "child".into(),
                    query_hash,
                    outcome: "sat".into(),
                    z3_nanos: None,
                },
            ),
        ]);
        let events = vec![
            WarmEvent::PathStart {
                path_id: "parent".into(),
                parent_path_id: None,
            },
            WarmEvent::Push {
                path_id: "parent".into(),
            },
            WarmEvent::Assert {
                path_id: "parent".into(),
                constraint_id: constraint_id.clone(),
            },
            WarmEvent::Check {
                path_id: "parent".into(),
                check_id: "check-parent".into(),
            },
            WarmEvent::PathStart {
                path_id: "child".into(),
                parent_path_id: Some("parent".into()),
            },
            WarmEvent::Check {
                path_id: "child".into(),
                check_id: "check-child".into(),
            },
            WarmEvent::PathEnd {
                path_id: "child".into(),
            },
            WarmEvent::PathEnd {
                path_id: "parent".into(),
            },
        ];
        let trace = warm_test_trace(queries, checks, events);
        let summary = replay_warm_trace(&trace, &SolverConfig::new(), false, false).unwrap();
        assert_eq!(summary["checks"], 2);
        assert_eq!(summary["fork_states_created"], 1);
        assert_eq!(summary["fork_prefix_roots_replayed"], 1);
        assert_eq!(summary["outcomes"]["sat"], 2);
        assert_eq!(
            summary["policy"]["mutable_solver_state_shared_across_paths"],
            false
        );

        let cold = replay_cold_occurrences(&trace, &SolverConfig::new()).unwrap();
        assert_eq!(cold["checks"], 2);
        assert_eq!(cold["outcomes"]["sat"], 2);
        let snapshot = replay_snapshot_trace(&trace, &SolverConfig::new(), false, false).unwrap();
        assert_eq!(snapshot["checks"], 2);
        assert_eq!(snapshot["roots_added"], 1);
        assert_eq!(snapshot["unchanged_snapshots"], 1);
        assert_eq!(snapshot["outcomes"]["sat"], 2);
    }

    #[test]
    fn warm_check_rejects_an_active_constraint_missing_from_the_query_store() {
        let query = b"(set-logic QF_BV)\n(check-sat)\n".to_vec();
        let query_hash = sha256(&query);
        let queries = BTreeMap::from([(
            query_hash.clone(),
            QueryRecord::inline(query, BTreeSet::from(["sat".into()])),
        )]);
        let checks = BTreeMap::from([(
            "check-missing".into(),
            CheckRecord {
                check_id: "check-missing".into(),
                path_id: "path".into(),
                query_hash,
                outcome: "sat".into(),
                z3_nanos: None,
            },
        )]);
        let missing = "missing-constraint".to_string();
        let events = vec![
            WarmEvent::PathStart {
                path_id: "path".into(),
                parent_path_id: None,
            },
            WarmEvent::Push {
                path_id: "path".into(),
            },
            WarmEvent::Assert {
                path_id: "path".into(),
                constraint_id: missing.clone(),
            },
            WarmEvent::Check {
                path_id: "path".into(),
                check_id: "check-missing".into(),
            },
        ];
        let trace = warm_test_trace(queries, checks, events);
        let error = replay_warm_trace(&trace, &SolverConfig::new(), false, false).unwrap_err();
        assert!(error.contains("absent from the query store"));
        let error = replay_snapshot_trace(&trace, &SolverConfig::new(), false, false).unwrap_err();
        assert!(error.contains("absent from the query store"));
    }
}
