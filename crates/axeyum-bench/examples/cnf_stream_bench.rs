//! Replay captured append-only CNF streams through persistent `BatSat` and Z3.
//!
//! Usage: `cnf_stream_bench PROFILE.jsonl SNAPSHOT_DIR OUT.json [REPETITIONS]
//! [TIMEOUT_MS]`.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use axeyum_cnf::{CnfClause, CnfLit, IncrementalSat, SatResult, parse_dimacs};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use z3::{Params, SatResult as Z3SatResult, Solver, ast::Bool};

const WARM_SCHEMA: &str = "glaurung-axeyum-warm-profile-v7";
const SNAPSHOT_SCHEMA: &str = "glaurung-axeyum-retained-cnf-snapshot-v1";

struct ProfileCheck {
    query_hash: String,
    path_id: u64,
    outcome: String,
    persistent_clauses: usize,
}

struct ProfileStream {
    checks: Vec<ProfileCheck>,
    decided_records: usize,
    replay_cache_hits: usize,
}

struct Snapshot {
    sequence: u64,
    path_id: u64,
    query_hash: String,
    outcome: String,
    variable_count: usize,
    persistent: Vec<CnfClause>,
    assumptions: Vec<CnfLit>,
}

struct BatState {
    solver: IncrementalSat,
    persistent: Vec<CnfClause>,
}

struct Z3State {
    solver: Solver,
    vars: Vec<Bool>,
    persistent: Vec<CnfClause>,
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

fn usize_from(value: u64, label: &str) -> Result<usize, String> {
    usize::try_from(value).map_err(|_| format!("{label} exceeds usize"))
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

fn load_profile(path: &Path) -> Result<ProfileStream, String> {
    let text =
        fs::read_to_string(path).map_err(|error| format!("read {}: {error}", path.display()))?;
    let mut result = Vec::new();
    let mut decided_records = 0_usize;
    let mut replay_cache_hits = 0_usize;
    for (index, line) in text.lines().enumerate() {
        let value: Value = serde_json::from_str(line)
            .map_err(|error| format!("{} line {}: {error}", path.display(), index + 1))?;
        if value["schema"] == WARM_SCHEMA
            && matches!(value["outcome"].as_str(), Some("sat" | "unsat"))
        {
            decided_records += 1;
            let cache_hits = required_u64(&value["replay_sat_cache"], "hits")?;
            if cache_hits > 0 {
                replay_cache_hits = replay_cache_hits
                    .saturating_add(usize_from(cache_hits, "replay cache hit count")?);
                continue;
            }
            result.push(ProfileCheck {
                query_hash: required_str(&value, "query_hash")?.to_string(),
                path_id: required_u64(&value, "path_id")?,
                outcome: required_str(&value, "outcome")?.to_string(),
                persistent_clauses: usize_from(
                    required_u64(&value, "cnf_clauses")?,
                    "persistent clause count",
                )?,
            });
        }
    }
    if result.is_empty() {
        return Err("profile has no decided warm records".to_string());
    }
    Ok(ProfileStream {
        checks: result,
        decided_records,
        replay_cache_hits,
    })
}

fn load_snapshots(directory: &Path, profile: &[ProfileCheck]) -> Result<Vec<Snapshot>, String> {
    let mut metadata = fs::read_dir(directory)
        .map_err(|error| format!("read {}: {error}", directory.display()))?
        .map(|entry| entry.map(|entry| entry.path()))
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| format!("read {}: {error}", directory.display()))?;
    metadata.retain(|path| {
        path.extension()
            .is_some_and(|extension| extension == "json")
    });
    let mut decoded = metadata
        .into_iter()
        .map(|path| {
            let value: Value = serde_json::from_slice(
                &fs::read(&path).map_err(|error| format!("read {}: {error}", path.display()))?,
            )
            .map_err(|error| format!("parse {}: {error}", path.display()))?;
            Ok::<_, String>((required_u64(&value, "sequence")?, path, value))
        })
        .collect::<Result<Vec<_>, _>>()?;
    decoded.sort_by_key(|(sequence, _, _)| *sequence);
    if decoded.len() != profile.len() {
        return Err(format!(
            "snapshot/profile cardinality mismatch: {} versus {}",
            decoded.len(),
            profile.len()
        ));
    }

    let mut snapshots = Vec::with_capacity(profile.len());
    for ((sequence, metadata_path, value), expected) in decoded.into_iter().zip(profile) {
        if value["schema"] != SNAPSHOT_SCHEMA {
            return Err(format!("unexpected schema in {}", metadata_path.display()));
        }
        let query_hash = required_str(&value, "query_hash")?;
        let path_id = required_u64(&value, "path_id")?;
        let outcome = required_str(&value, "outcome")?;
        if query_hash != expected.query_hash
            || path_id != expected.path_id
            || outcome != expected.outcome
        {
            return Err(format!(
                "profile/snapshot identity mismatch at {}",
                metadata_path.display()
            ));
        }
        let cnf_path = metadata_path.with_extension("cnf");
        let bytes =
            fs::read(&cnf_path).map_err(|error| format!("read {}: {error}", cnf_path.display()))?;
        if sha256_hex(&bytes) != required_str(&value, "dimacs_sha256")? {
            return Err(format!("DIMACS hash mismatch at {}", cnf_path.display()));
        }
        let formula = parse_dimacs(
            std::str::from_utf8(&bytes)
                .map_err(|error| format!("{} is not UTF-8: {error}", cnf_path.display()))?,
        )
        .map_err(|error| format!("{}: {error}", cnf_path.display()))?;
        if formula.variable_count()
            != usize_from(required_u64(&value, "variable_count")?, "variable count")?
            || formula.clauses().len()
                != usize_from(required_u64(&value, "clause_count")?, "clause count")?
            || expected.persistent_clauses > formula.clauses().len()
        {
            return Err(format!("DIMACS shape mismatch at {}", cnf_path.display()));
        }
        let assumptions = formula.clauses()[expected.persistent_clauses..]
            .iter()
            .map(|clause| match clause.lits() {
                [lit] if !lit.is_negated() => Ok(*lit),
                _ => Err(format!(
                    "non-positive-unit selector at {}",
                    cnf_path.display()
                )),
            })
            .collect::<Result<Vec<_>, _>>()?;
        snapshots.push(Snapshot {
            sequence,
            path_id,
            query_hash: query_hash.to_string(),
            outcome: outcome.to_string(),
            variable_count: formula.variable_count(),
            persistent: formula.clauses()[..expected.persistent_clauses].to_vec(),
            assumptions,
        });
    }
    Ok(snapshots)
}

fn verify_prefix(previous: &[CnfClause], next: &[CnfClause], path_id: u64) -> Result<(), String> {
    if next.len() < previous.len() || next[..previous.len()] != previous[..] {
        return Err(format!(
            "persistent clause prefix changed for path {path_id}"
        ));
    }
    Ok(())
}

fn z3_lit(vars: &[Bool], lit: CnfLit) -> Bool {
    let atom = vars[lit.var().index()].clone();
    if lit.is_negated() { atom.not() } else { atom }
}

fn new_z3_state(timeout_ms: u32) -> Z3State {
    let solver = Solver::new();
    let mut params = Params::new();
    params.set_u32("random_seed", 0);
    params.set_u32("timeout", timeout_ms);
    solver.set_params(&params);
    Z3State {
        solver,
        vars: Vec::new(),
        persistent: Vec::new(),
    }
}

fn nanos(started: Instant) -> u64 {
    u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX)
}

// Keeping the paired core operations adjacent makes the measured boundaries
// auditable; splitting this diagnostic loop would obscure their symmetry.
#[allow(clippy::too_many_lines)]
fn main() -> Result<(), String> {
    let usage =
        "usage: cnf_stream_bench PROFILE.jsonl SNAPSHOT_DIR OUT.json [REPETITIONS] [TIMEOUT_MS]";
    let mut args = std::env::args_os().skip(1);
    let profile_path = PathBuf::from(args.next().ok_or(usage)?);
    let snapshot_dir = PathBuf::from(args.next().ok_or(usage)?);
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
    let timeout = Duration::from_millis(u64::from(timeout_ms));

    let profile = load_profile(&profile_path)?;
    let snapshots = load_snapshots(&snapshot_dir, &profile.checks)?;
    let mut rows = Vec::with_capacity(repetitions * snapshots.len());
    for repetition in 0..repetitions {
        let mut batsat: BTreeMap<u64, BatState> = BTreeMap::new();
        let mut z3: BTreeMap<u64, Z3State> = BTreeMap::new();
        for snapshot in &snapshots {
            let bat = batsat.entry(snapshot.path_id).or_insert_with(|| BatState {
                solver: IncrementalSat::new(),
                persistent: Vec::new(),
            });
            verify_prefix(&bat.persistent, &snapshot.persistent, snapshot.path_id)?;
            let bat_add_started = Instant::now();
            for clause in &snapshot.persistent[bat.persistent.len()..] {
                bat.solver
                    .add_clause(clause.clone())
                    .map_err(|error| error.to_string())?;
            }
            // Match the producer's gradual clause stream: let each clause
            // introduce its variables in encounter order, then reserve any
            // allocated-but-unused tail variables recorded by the snapshot.
            bat.solver
                .reserve(snapshot.variable_count)
                .map_err(|error| error.to_string())?;
            let bat_add_nanos = nanos(bat_add_started);
            bat.persistent.clone_from(&snapshot.persistent);
            let bat_solve_started = Instant::now();
            let bat_outcome = match bat
                .solver
                .solve_assuming(&snapshot.assumptions, Some(timeout))
                .map_err(|error| error.to_string())?
            {
                SatResult::Sat(_) => "sat",
                SatResult::Unsat(_) => "unsat",
                SatResult::Unknown(_) => "unknown",
            };
            let bat_solve_nanos = nanos(bat_solve_started);

            let z3_state = z3
                .entry(snapshot.path_id)
                .or_insert_with(|| new_z3_state(timeout_ms));
            verify_prefix(&z3_state.persistent, &snapshot.persistent, snapshot.path_id)?;
            let z3_add_started = Instant::now();
            while z3_state.vars.len() < snapshot.variable_count {
                let index = z3_state.vars.len();
                z3_state
                    .vars
                    .push(Bool::new_const(format!("p{}_v{index}", snapshot.path_id)));
            }
            for clause in &snapshot.persistent[z3_state.persistent.len()..] {
                let lits = clause
                    .lits()
                    .iter()
                    .map(|&lit| z3_lit(&z3_state.vars, lit))
                    .collect::<Vec<_>>();
                z3_state.solver.assert(Bool::or(&lits));
            }
            let z3_add_nanos = nanos(z3_add_started);
            z3_state.persistent.clone_from(&snapshot.persistent);
            let assumptions = snapshot
                .assumptions
                .iter()
                .map(|&lit| z3_lit(&z3_state.vars, lit))
                .collect::<Vec<_>>();
            let z3_solve_started = Instant::now();
            let z3_outcome = match z3_state.solver.check_assumptions(&assumptions) {
                Z3SatResult::Sat => "sat",
                Z3SatResult::Unsat => "unsat",
                Z3SatResult::Unknown => "unknown",
            };
            let z3_solve_nanos = nanos(z3_solve_started);
            if bat_outcome != snapshot.outcome || z3_outcome != snapshot.outcome {
                return Err(format!(
                    "verdict mismatch at repetition {repetition}, snapshot {}: BatSat={bat_outcome}, Z3={z3_outcome}",
                    snapshot.sequence
                ));
            }
            rows.push(json!({
                "repetition": repetition,
                "sequence": snapshot.sequence,
                "path_id": snapshot.path_id,
                "query_hash": snapshot.query_hash,
                "expected_outcome": snapshot.outcome,
                "variables": snapshot.variable_count,
                "persistent_clauses": snapshot.persistent.len(),
                "active_assumptions": snapshot.assumptions.len(),
                "batsat": {"outcome": bat_outcome, "add_nanos": bat_add_nanos, "solve_nanos": bat_solve_nanos},
                "z3": {"outcome": z3_outcome, "add_nanos": z3_add_nanos, "solve_nanos": z3_solve_nanos},
            }));
        }
    }
    let report = json!({
        "schema": "axeyum-persistent-cnf-stream-benchmark-v1",
        "profile": profile_path,
        "snapshot_directory": snapshot_dir,
        "repetitions": repetitions,
        "per_check_timeout_ms": timeout_ms,
        "profile_decided_records": profile.decided_records,
        "profile_replay_cache_hits_skipped": profile.replay_cache_hits,
        "snapshots_per_repetition": snapshots.len(),
        "paths": snapshots.iter().map(|snapshot| snapshot.path_id).collect::<BTreeSet<_>>(),
        "rows": rows,
    });
    fs::write(
        &output,
        serde_json::to_vec_pretty(&report).map_err(|error| error.to_string())?,
    )
    .map_err(|error| format!("write {}: {error}", output.display()))
}
