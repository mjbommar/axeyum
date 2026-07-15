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
use std::process::ExitCode;
use std::time::{Duration, Instant};

use axeyum_ir::{TermArena, TermId, Value as IrValue, eval};
use axeyum_smtlib::{ScriptCommand, parse_script};
use axeyum_solver::{CheckResult, IncrementalBvSolver, Model, SolverConfig, solve_smtlib};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const TRACE_SCHEMA: &str = "glaurung-ordered-trace-v1";
const REPLAY_SCHEMA: &str = "axeyum-glaurung-ordered-trace-replay-v1";

fn main() -> ExitCode {
    match run() {
        Ok(summary) => {
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
    let started = Instant::now();
    let trace = Trace::load(&options.trace)?;
    let config = SolverConfig::new()
        .with_preprocess(false)
        .with_timeout(Duration::from_millis(options.timeout_ms));

    let query_started = Instant::now();
    let mut outcome_counts = BTreeMap::<String, u64>::new();
    for (hash, query) in &trace.queries {
        validate_qf_bv_script(hash, &query.bytes)?;
        let outcome =
            solve_text(&query.bytes, &config).map_err(|error| format!("query {hash}: {error}"))?;
        if let Some(expected) = query.decided_outcome()?
            && outcome != expected
        {
            return Err(format!(
                "query {hash} verdict disagreement: recorded {expected}, Axeyum {outcome}"
            ));
        }
        *outcome_counts.entry(outcome).or_default() += 1;
    }
    let query_replay_nanos = nanos(query_started.elapsed());

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
        let constrained = append_choice_assertion(&query.bytes, read)?;
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
    let cold_occurrence_replay = options
        .cold_occurrences
        .then(|| replay_cold_occurrences(&trace, &config))
        .transpose()?;
    let snapshot_replay = options
        .snapshot
        .then(|| replay_snapshot_trace(&trace, &config))
        .transpose()?;
    let warm_replay = options
        .lineage
        .then(|| replay_warm_trace(&trace, &config))
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
        "axeyum_unique_query_outcomes": outcome_counts,
        "solver_policy": {
            "preprocess": false,
            "timeout_ms_per_check": options.timeout_ms,
            "sat_model_replay": "solve_smtlib original-assertion replay",
        },
        "query_replay_nanos": query_replay_nanos,
        "choice_replay_nanos": choice_replay_nanos,
        "resource_identity": {
            "trace_manifest_sha256": trace.manifest_hash,
            "axeyum_package_version": env!("CARGO_PKG_VERSION"),
            "target_arch": env::consts::ARCH,
            "target_os": env::consts::OS,
            "timeout_ms_per_check": options.timeout_ms,
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

struct Options {
    trace: PathBuf,
    timeout_ms: u64,
    cold_occurrences: bool,
    snapshot: bool,
    lineage: bool,
    output: Option<PathBuf>,
}

impl Options {
    fn parse(args: impl Iterator<Item = String>) -> Result<Self, String> {
        let mut trace = None;
        let mut timeout_ms = 1_000;
        let mut cold_occurrences = false;
        let mut snapshot = false;
        let mut lineage = false;
        let mut output = None;
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
                "--out" => {
                    output = Some(PathBuf::from(
                        args.next()
                            .ok_or_else(|| "--out requires a path".to_string())?,
                    ));
                }
                "--cold-occurrences" => cold_occurrences = true,
                "--snapshot" => snapshot = true,
                "--warm" | "--lineage" => lineage = true,
                "-h" | "--help" => {
                    return Err("usage: glaurung-ordered-trace TRACE_DIR [--timeout-ms N] \
                         [--cold-occurrences] [--snapshot] [--lineage] [--out FILE]"
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
        Ok(Self {
            trace: trace.ok_or_else(|| {
                "usage: glaurung-ordered-trace TRACE_DIR [--timeout-ms N] \
                 [--cold-occurrences] [--snapshot] [--lineage] [--out FILE]"
                    .to_string()
            })?,
            timeout_ms,
            cold_occurrences,
            snapshot,
            lineage,
            output,
        })
    }
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
    checks: BTreeMap<String, CheckRecord>,
    model_reads: BTreeMap<String, ModelRead>,
    model_choice_count: usize,
    recorded_outcomes: BTreeMap<String, u64>,
    backend_timing: BackendTimingStats,
    reuse: ReuseStats,
    warm_events: Vec<WarmEvent>,
}

struct QueryRecord {
    bytes: Vec<u8>,
    outcomes: BTreeSet<String>,
    occurrences: Vec<(String, String, u64)>,
}

impl QueryRecord {
    fn decided_outcome(&self) -> Result<Option<&str>, String> {
        let sat = self.outcomes.contains("sat");
        let unsat = self.outcomes.contains("unsat");
        match (sat, unsat) {
            (true, true) => Err("query index contains both sat and unsat".into()),
            (true, false) => Ok(Some("sat")),
            (false, true) => Ok(Some("unsat")),
            (false, false) => Ok(None),
        }
    }
}

struct CheckRecord {
    check_id: String,
    path_id: String,
    query_hash: String,
    outcome: String,
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

#[derive(Clone)]
enum WarmEvent {
    PathStart {
        path_id: String,
        parent_path_id: Option<String>,
        inherited_constraints: Vec<String>,
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
        constraints: Vec<String>,
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
        constraints: Vec<String>,
    },
}

impl Trace {
    // Keeping the ordered validation state in one pass makes sequence, lineage,
    // scope, check, and model-choice ownership invariants directly auditable.
    #[allow(clippy::too_many_lines)]
    fn load(root: &Path) -> Result<Self, String> {
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
        let queries = load_queries(root, &index)?;
        let assertions = load_assertions(root, &manifest)?;

        let mut paths = BTreeMap::from([("analysis".to_string(), PathState::default())]);
        let mut checks = BTreeMap::new();
        let mut model_reads = BTreeMap::new();
        let mut recorded_outcomes = BTreeMap::<String, u64>::new();
        let mut backend_timing = BackendTimingStats::default();
        let mut observed_assertions = BTreeSet::new();
        let mut observed_occurrences = BTreeMap::<String, Vec<(String, String, u64)>>::new();
        let mut reuse = ReuseStats::default();
        let mut expected_event_seq = 0_u64;
        let mut expected_process_seq = 0_u64;
        let mut expected_worker_seq = BTreeMap::<String, u64>::new();
        let mut event_kinds = Vec::new();
        let mut choice_ids = BTreeSet::new();
        let mut choice_reads = BTreeSet::new();
        let mut warm_events = Vec::new();

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
                let inherited_constraints = complete_constraints(
                    paths
                        .get(&path_id)
                        .expect("path was inserted immediately above"),
                    &path_id,
                )?;
                warm_events.push(WarmEvent::PathStart {
                    path_id: path_id.clone(),
                    parent_path_id,
                    inherited_constraints,
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
                    if assertion_hashes(&query.bytes) != constraints {
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
                            },
                        )
                        .is_some()
                    {
                        return Err(format!("duplicate check ID {check_id}"));
                    }
                    *recorded_outcomes.entry(outcome).or_default() += 1;
                    observed_occurrences.entry(query_hash).or_default().push((
                        check_id.clone(),
                        path_id.clone(),
                        integer(&event, "event_seq")?,
                    ));
                    classify_reuse(&mut reuse, &state.last_checked_constraints, &constraints);
                    reuse.maximum_scope_depth = reuse.maximum_scope_depth.max(constraints.len());
                    state.last_checked_constraints = constraints;
                    state.pending_sat_check =
                        (checks[&check_id].outcome == "sat").then_some(check_id.clone());
                    warm_events.push(WarmEvent::Check {
                        path_id: path_id.clone(),
                        check_id,
                        constraints: state.last_checked_constraints.clone(),
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
                        constraints: complete_constraints(state, &path_id)?,
                    });
                    state.ended = true;
                }
                "analysis_start" | "analysis_end" | "path_start" => {}
                other => return Err(format!("unsupported trace event: {other}")),
            }
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
            if observed_occurrences.get(hash) != Some(&query.occurrences) {
                return Err(format!("query occurrence index mismatch for {hash}"));
            }
            let observed: BTreeSet<String> = query
                .occurrences
                .iter()
                .filter_map(|(check_id, _, _)| {
                    checks.get(check_id).map(|check| check.outcome.clone())
                })
                .collect();
            if observed != query.outcomes {
                return Err(format!("query outcome index mismatch for {hash}"));
            }
        }
        let recorded_reads = model_reads.keys().cloned().collect::<BTreeSet<_>>();
        if choice_reads != recorded_reads {
            return Err("model reads and model-choice consumption differ".into());
        }
        if let Some(expected) = manifest.get("assertion_count").and_then(Value::as_u64)
            && (usize_to_u64(assertions.len()) != expected
                || observed_assertions != assertions.keys().cloned().collect())
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
            checks,
            model_reads,
            model_choice_count: choice_ids.len(),
            recorded_outcomes,
            backend_timing,
            reuse,
            warm_events,
        })
    }
}

fn load_queries(root: &Path, index: &Value) -> Result<BTreeMap<String, QueryRecord>, String> {
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
        let bytes = read(&root.join(relative))?;
        if sha256(&bytes) != hash {
            return Err(format!("query content hash mismatch for {hash}"));
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
        let occurrences = array(row, "occurrences")?
            .iter()
            .map(|occurrence| {
                Ok((
                    string(occurrence, "check_id")?.to_string(),
                    string(occurrence, "path_id")?.to_string(),
                    integer(occurrence, "event_seq")?,
                ))
            })
            .collect::<Result<Vec<_>, String>>()?;
        if queries
            .insert(
                hash,
                QueryRecord {
                    bytes,
                    outcomes,
                    occurrences,
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
        let started = Instant::now();
        let result = solve_smtlib(
            std::str::from_utf8(&query.bytes)
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
        "replay_nanos": nanos(replay_started.elapsed()),
        "process_peak_rss_bytes_before": peak_rss_before,
        "process_peak_rss_bytes_after": process_peak_rss_bytes(),
    }))
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
}

// Snapshot replay is deliberately one ordered state machine: the consecutive
// LCP policy, pending model, and exact occurrence verdict stay visibly coupled.
#[allow(clippy::too_many_lines)]
fn replay_snapshot_trace(trace: &Trace, config: &SolverConfig) -> Result<Value, String> {
    let build_started = Instant::now();
    let program = build_warm_program(trace)?;
    let build_nanos = nanos(build_started.elapsed());
    let peak_rss_before = process_peak_rss_bytes();
    let replay_started = Instant::now();
    let mut solver = IncrementalBvSolver::with_config_and_profiling(config.clone());
    let mut active = Vec::<String>::new();
    let mut pending_model = None::<(String, Model)>;
    let mut stats = SnapshotReplayStats::default();

    for event in &trace.warm_events {
        match event {
            WarmEvent::Check {
                check_id,
                constraints,
                ..
            } => {
                let occurrence_started = Instant::now();
                let lcp = active
                    .iter()
                    .zip(constraints)
                    .take_while(|(left, right)| left == right)
                    .count();
                stats.roots_retained = stats.roots_retained.saturating_add(usize_to_u64(lcp));
                if active == *constraints {
                    stats.unchanged_snapshots = stats.unchanged_snapshots.saturating_add(1);
                }
                for _ in lcp..active.len() {
                    if !solver.pop() {
                        return Err(format!("snapshot scope underflow on check {check_id}"));
                    }
                    stats.roots_popped = stats.roots_popped.saturating_add(1);
                }
                active.truncate(lcp);
                for constraint_id in &constraints[lcp..] {
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
                    active.push(constraint_id.clone());
                    stats.roots_added = stats.roots_added.saturating_add(1);
                }
                if solver.scope_depth() != constraints.len() || active != *constraints {
                    return Err(format!("snapshot scope differs on check {check_id}"));
                }
                let check = trace.checks.get(check_id).ok_or_else(|| {
                    format!("snapshot replay references missing check {check_id}")
                })?;
                let check_started = Instant::now();
                let result = solver
                    .check(&program.arena)
                    .map_err(|error| format!("snapshot check {check_id}: {error}"))?;
                stats
                    .check_latencies_nanos
                    .push(nanos(check_started.elapsed()));
                stats
                    .occurrence_latencies_nanos
                    .push(nanos(occurrence_started.elapsed()));
                stats.checks = stats.checks.saturating_add(1);
                let (outcome, model) = split_result(result);
                *stats.outcomes.entry(outcome.to_string()).or_default() += 1;
                if check.outcome != outcome {
                    return Err(format!(
                        "snapshot check {check_id} verdict disagreement: recorded {}, Axeyum \
                         {outcome}",
                        check.outcome
                    ));
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
            WarmEvent::PathStart { .. }
            | WarmEvent::Push { .. }
            | WarmEvent::Assert { .. }
            | WarmEvent::Pop { .. }
            | WarmEvent::PathEnd { .. } => {}
        }
    }

    stats.occurrence_latencies_nanos.sort_unstable();
    stats.check_latencies_nanos.sort_unstable();
    let solver_stats = solver.stats();
    Ok(json!({
        "policy": {
            "entry": "consecutive complete snapshots reconstructed from ordered checks",
            "arena": "one shared parsed arena",
            "solver": "one retained solver with longest-common-prefix pop/push",
            "lineage_used": false,
            "preprocess": config.preprocess,
            "timeout_ms_per_check": config.timeout.map(|timeout| timeout.as_millis()),
            "sat_model_replay": "IncrementalBvSolver original-assertion replay",
        },
        "shared_arena_build_nanos": build_nanos,
        "replay_nanos": nanos(replay_started.elapsed()),
        "checks": stats.checks,
        "outcomes": stats.outcomes,
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
}

// One ordered state machine owns the fork/scope/model invariants. Splitting the
// event handlers across independent passes would weaken their auditable order.
#[allow(clippy::too_many_lines)]
fn replay_warm_trace(trace: &Trace, config: &SolverConfig) -> Result<Value, String> {
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
                inherited_constraints,
            } => {
                if paths.contains_key(path_id) {
                    return Err(format!("warm replay duplicates path {path_id}"));
                }
                if let Some(parent_path_id) = parent_path_id {
                    let parent = paths.get(parent_path_id).ok_or_else(|| {
                        format!("warm fork {path_id} has no live parent {parent_path_id}")
                    })?;
                    let parent_constraints = warm_constraints(parent, parent_path_id)?;
                    if &parent_constraints != inherited_constraints {
                        return Err(format!(
                            "warm fork {path_id} inherited a different prefix from {parent_path_id}"
                        ));
                    }
                    stats.fork_states_created = stats.fork_states_created.saturating_add(1);
                } else if !inherited_constraints.is_empty() {
                    return Err(format!("warm root path {path_id} inherits constraints"));
                }

                let fork_started = Instant::now();
                let mut solver = IncrementalBvSolver::with_config_and_profiling(config.clone());
                let mut scopes = Vec::with_capacity(inherited_constraints.len());
                let mut materialized = Vec::with_capacity(inherited_constraints.len());
                for constraint_id in inherited_constraints {
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
            WarmEvent::Check {
                path_id,
                check_id,
                constraints,
            } => {
                let check = trace
                    .checks
                    .get(check_id)
                    .ok_or_else(|| format!("warm replay references missing check {check_id}"))?;
                let path = warm_path_mut(&mut paths, path_id)?;
                if warm_constraints(path, path_id)? != *constraints {
                    return Err(format!("warm active scopes differ on check {check_id}"));
                }
                if path.solver.scope_depth() != constraints.len() {
                    return Err(format!("warm solver depth differs on check {check_id}"));
                }
                if path.materialized.iter().any(|available| !available) {
                    return Err(format!(
                        "warm check {check_id} reaches an assertion absent from the query store"
                    ));
                }
                let check_started = Instant::now();
                let result = path
                    .solver
                    .check(&program.arena)
                    .map_err(|error| format!("warm check {check_id}: {error}"))?;
                stats
                    .check_latencies_nanos
                    .push(nanos(check_started.elapsed()));
                stats.checks = stats.checks.saturating_add(1);
                let (outcome, model) = match result {
                    CheckResult::Sat(model) => ("sat", Some(model)),
                    CheckResult::Unsat => ("unsat", None),
                    CheckResult::Unknown(_) => ("unknown", None),
                };
                *stats.outcomes.entry(outcome.to_string()).or_default() += 1;
                if check.outcome != outcome {
                    return Err(format!(
                        "warm check {check_id} verdict disagreement: recorded {}, Axeyum {outcome}",
                        check.outcome
                    ));
                }
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
            WarmEvent::PathEnd {
                path_id,
                constraints,
            } => {
                let path = paths
                    .remove(path_id)
                    .ok_or_else(|| format!("warm replay ends missing path {path_id}"))?;
                if warm_constraints(&path, path_id)? != *constraints {
                    return Err(format!("warm terminal scopes differ on path {path_id}"));
                }
                accumulate_warm_path_stats(&path.solver.stats(), &mut stats);
            }
        }
    }
    if !paths.is_empty() {
        return Err("warm replay retains unterminated paths".into());
    }

    stats.check_latencies_nanos.sort_unstable();
    Ok(json!({
        "policy": {
            "preprocess": config.preprocess,
            "timeout_ms_per_check": config.timeout.map(|timeout| timeout.as_millis()),
            "fork_behavior": "fresh child solver plus validated inherited-prefix replay",
            "mutable_solver_state_shared_across_paths": false,
            "sat_model_replay": "IncrementalBvSolver original-assertion replay",
        },
        "shared_arena_build_nanos": build_nanos,
        "replay_nanos": nanos(replay_started.elapsed()),
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
    }
    for (query_hash, query) in &trace.queries {
        let text = std::str::from_utf8(&query.bytes)
            .map_err(|error| format!("query {query_hash} is non-UTF-8: {error}"))?;
        for line in text.split_inclusive('\n') {
            if line.starts_with("(declare-const ") || line.starts_with("(declare-fun ") {
                declarations.insert(line.to_string());
            } else if line.starts_with("(assert ") {
                let constraint_id = sha256(line.as_bytes());
                if let Some(previous) = constraint_text.insert(constraint_id.clone(), line.into())
                    && previous != line
                {
                    return Err(format!("constraint SHA-256 collision at {constraint_id}"));
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
    let mut symbols = Vec::new();
    let mut previous_id = None;
    for symbol in array(event, "expression_symbols")? {
        let name = string(symbol, "name")?.to_string();
        let symbol_width = integer(symbol, "width")?;
        let (symbol_id, encoded_width) = parse_symbol_name(&name)?;
        if encoded_width != symbol_width || previous_id.is_some_and(|prior| prior >= symbol_id) {
            return Err(format!("invalid/unsorted model-read symbol {name}"));
        }
        previous_id = Some(symbol_id);
        symbols.push((name, symbol_width));
    }
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

fn assertion_hashes(bytes: &[u8]) -> Vec<String> {
    bytes
        .split_inclusive(|byte| *byte == b'\n')
        .filter(|line| line.starts_with(b"(assert "))
        .map(sha256)
        .collect()
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
            checks,
            model_reads: BTreeMap::new(),
            model_choice_count: 0,
            recorded_outcomes: BTreeMap::new(),
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
    fn warm_fork_replays_a_validated_parent_prefix_without_sharing_solver_state() {
        let assertion = "(assert (= x (_ bv1 8)))\n";
        let constraint_id = sha256(assertion);
        let query =
            format!("(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n{assertion}(check-sat)\n");
        let query_hash = sha256(query.as_bytes());
        let queries = BTreeMap::from([(
            query_hash.clone(),
            QueryRecord {
                bytes: query.into_bytes(),
                outcomes: BTreeSet::from(["sat".into()]),
                occurrences: Vec::new(),
            },
        )]);
        let checks = BTreeMap::from([
            (
                "check-parent".into(),
                CheckRecord {
                    check_id: "check-parent".into(),
                    path_id: "parent".into(),
                    query_hash: query_hash.clone(),
                    outcome: "sat".into(),
                },
            ),
            (
                "check-child".into(),
                CheckRecord {
                    check_id: "check-child".into(),
                    path_id: "child".into(),
                    query_hash,
                    outcome: "sat".into(),
                },
            ),
        ]);
        let events = vec![
            WarmEvent::PathStart {
                path_id: "parent".into(),
                parent_path_id: None,
                inherited_constraints: Vec::new(),
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
                constraints: vec![constraint_id.clone()],
            },
            WarmEvent::PathStart {
                path_id: "child".into(),
                parent_path_id: Some("parent".into()),
                inherited_constraints: vec![constraint_id.clone()],
            },
            WarmEvent::Check {
                path_id: "child".into(),
                check_id: "check-child".into(),
                constraints: vec![constraint_id.clone()],
            },
            WarmEvent::PathEnd {
                path_id: "child".into(),
                constraints: vec![constraint_id.clone()],
            },
            WarmEvent::PathEnd {
                path_id: "parent".into(),
                constraints: vec![constraint_id],
            },
        ];
        let trace = warm_test_trace(queries, checks, events);
        let summary = replay_warm_trace(&trace, &SolverConfig::new()).unwrap();
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
        let snapshot = replay_snapshot_trace(&trace, &SolverConfig::new()).unwrap();
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
            QueryRecord {
                bytes: query,
                outcomes: BTreeSet::from(["sat".into()]),
                occurrences: Vec::new(),
            },
        )]);
        let checks = BTreeMap::from([(
            "check-missing".into(),
            CheckRecord {
                check_id: "check-missing".into(),
                path_id: "path".into(),
                query_hash,
                outcome: "sat".into(),
            },
        )]);
        let missing = "missing-constraint".to_string();
        let events = vec![
            WarmEvent::PathStart {
                path_id: "path".into(),
                parent_path_id: None,
                inherited_constraints: Vec::new(),
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
                constraints: vec![missing],
            },
        ];
        let trace = warm_test_trace(queries, checks, events);
        let error = replay_warm_trace(&trace, &SolverConfig::new()).unwrap_err();
        assert!(error.contains("absent from the query store"));
        let error = replay_snapshot_trace(&trace, &SolverConfig::new()).unwrap_err();
        assert!(error.contains("absent from the query store"));
    }
}
