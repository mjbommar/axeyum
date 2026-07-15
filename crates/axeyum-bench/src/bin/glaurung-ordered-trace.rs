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

use axeyum_smtlib::{ScriptCommand, parse_script};
use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};
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
        "axeyum_unique_query_outcomes": outcome_counts,
        "solver_policy": {
            "preprocess": false,
            "timeout_ms_per_check": options.timeout_ms,
            "sat_model_replay": "solve_smtlib original-assertion replay",
        },
        "query_replay_nanos": query_replay_nanos,
        "choice_replay_nanos": choice_replay_nanos,
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
    output: Option<PathBuf>,
}

impl Options {
    fn parse(args: impl Iterator<Item = String>) -> Result<Self, String> {
        let mut trace = None;
        let mut timeout_ms = 1_000;
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
                "-h" | "--help" => {
                    return Err(
                        "usage: glaurung-ordered-trace TRACE_DIR [--timeout-ms N] [--out FILE]"
                            .into(),
                    );
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
                "usage: glaurung-ordered-trace TRACE_DIR [--timeout-ms N] [--out FILE]".to_string()
            })?,
            timeout_ms,
            output,
        })
    }
}

struct Trace {
    analysis_id: String,
    process_id: String,
    events_hash: String,
    event_count: usize,
    path_count: usize,
    queries: BTreeMap<String, QueryRecord>,
    checks: BTreeMap<String, CheckRecord>,
    model_reads: BTreeMap<String, ModelRead>,
    model_choice_count: usize,
    recorded_outcomes: BTreeMap<String, u64>,
    reuse: ReuseStats,
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

impl Trace {
    // Keeping the ordered validation state in one pass makes sequence, lineage,
    // scope, check, and model-choice ownership invariants directly auditable.
    #[allow(clippy::too_many_lines)]
    fn load(root: &Path) -> Result<Self, String> {
        let manifest = read_json(&root.join("trace-manifest-v1.json"))?;
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

        let mut paths = BTreeMap::from([("analysis".to_string(), PathState::default())]);
        let mut checks = BTreeMap::new();
        let mut model_reads = BTreeMap::new();
        let mut recorded_outcomes = BTreeMap::<String, u64>::new();
        let mut observed_occurrences = BTreeMap::<String, Vec<(String, String, u64)>>::new();
        let mut reuse = ReuseStats::default();
        let mut expected_event_seq = 0_u64;
        let mut expected_process_seq = 0_u64;
        let mut expected_worker_seq = BTreeMap::<String, u64>::new();
        let mut event_kinds = Vec::new();
        let mut choice_ids = BTreeSet::new();
        let mut choice_reads = BTreeSet::new();

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
                let state = if event.get("parent_path_id").is_none_or(Value::is_null) {
                    PathState::default()
                } else {
                    let parent_id = string(&event, "parent_path_id")?;
                    let parent = paths
                        .get(parent_id)
                        .ok_or_else(|| format!("path {path_id} has missing parent {parent_id}"))?;
                    if parent.ended {
                        return Err(format!("path {path_id} has ended parent {parent_id}"));
                    }
                    parent.clone()
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
                    scope.constraint_id = Some(constraint);
                    if string(&event, "scope_digest")? != scope_digest(&state.scopes)? {
                        return Err(format!("assert scope digest mismatch on {path_id}"));
                    }
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
                        (checks[&check_id].outcome == "sat").then_some(check_id);
                }
                "model_read" => {
                    let read = parse_model_read(&event, &path_id)?;
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
                }
                "path_end" => {
                    state.pending_sat_check = None;
                    if usize_integer(&event, "terminal_scope_depth")? != state.scopes.len()
                        || string(&event, "scope_digest")? != scope_digest(&state.scopes)?
                    {
                        return Err(format!("path_end scope digest mismatch on {path_id}"));
                    }
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

        Ok(Self {
            analysis_id,
            process_id,
            events_hash,
            event_count,
            path_count,
            queries,
            checks,
            model_reads,
            model_choice_count: choice_ids.len(),
            recorded_outcomes,
            reuse,
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

fn read_json(path: &Path) -> Result<Value, String> {
    serde_json::from_slice(&read(path)?)
        .map_err(|error| format!("parse {}: {error}", path.display()))
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
}
