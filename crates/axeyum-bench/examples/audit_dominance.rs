//! Per-instance Pareto-dominance evidence audit for an existing baseline JSON.
//!
//! This is the measurement bridge called out by `bench-results/DOMINANCE.md`.
//! The decide-rate baselines already record per-instance files and outcomes; this
//! example re-runs the baseline-decided instances through `produce_evidence` and,
//! for `unsat`, `prove_unsat_to_lean_module`, then emits the missing proof fields:
//! `evidence_certified`, `evidence_checked`, `lean_fragment`, `lean_checked`, and
//! `trust_holes`.
//!
//! Usage:
//! ```text
//! cargo run --release -p axeyum-bench --example audit_dominance -- \
//!   bench-results/baselines/qf-lra-cvc5-regress-clean-solver-vs-z3-10s.json \
//!   [timeout_ms] [limit] [out.json]
//! ```
//!
//! The first slice is deliberately a harness, not a benchmark-speed trophy: it is
//! sequential and conservative so the JSON is easy to review and diff.

#![allow(
    clippy::cast_precision_loss,
    clippy::struct_excessive_bools,
    clippy::too_many_lines
)]

use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, mpsc};
use std::thread;
use std::time::{Duration, Instant};

use axeyum_ir::{TermArena, TermId};
use axeyum_smtlib::parse_script;
use axeyum_solver::{
    Evidence, SolverConfig, produce_evidence, produce_evidence_smtlib, prove_unsat_to_lean_module,
};
use serde_json::{Value as JsonValue, json};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

impl Verdict {
    fn from_label(label: &str) -> Self {
        match label {
            "sat" => Self::Sat,
            "unsat" => Self::Unsat,
            _ => Self::Unknown,
        }
    }

    fn label(self) -> &'static str {
        match self {
            Self::Sat => "sat",
            Self::Unsat => "unsat",
            Self::Unknown => "unknown",
        }
    }

    fn decided(self) -> bool {
        matches!(self, Self::Sat | Self::Unsat)
    }
}

#[derive(Debug)]
struct AuditResult {
    record: JsonValue,
    dominant_candidate: bool,
    evidence_certified: bool,
    evidence_checked: bool,
    lean_checked: bool,
    unsat: bool,
    timed_out: bool,
    audit_error: bool,
}

#[derive(Debug)]
struct AuditProgress {
    phase: &'static str,
    phase_started: Instant,
}

fn mark_phase(progress: &Arc<Mutex<AuditProgress>>, phase: &'static str) {
    if let Ok(mut state) = progress.lock() {
        state.phase = phase;
        state.phase_started = Instant::now();
    }
}

fn progress_snapshot(progress: &Arc<Mutex<AuditProgress>>) -> (&'static str, f64) {
    match progress.lock() {
        Ok(state) => (
            state.phase,
            state.phase_started.elapsed().as_secs_f64() * 1000.0,
        ),
        Err(_) => ("poisoned-progress", 0.0),
    }
}

fn ms(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1000.0
}

fn evidence_kind(evidence: &Evidence) -> &'static str {
    match evidence {
        Evidence::Sat(model)
            if model
                .quantified_bv_model_sat_certificates()
                .next()
                .is_some() =>
        {
            "quantified-bv-model-sat"
        }
        Evidence::Sat(model) if model.quantified_guard_sat_certificates().next().is_some() => {
            "quantified-guard-sat"
        }
        Evidence::Sat(model) if model.quantified_sat_certificates().next().is_some() => {
            "quantified-skolem-sat"
        }
        Evidence::Sat(model)
            if model
                .quantified_bool_model_sat_certificates()
                .next()
                .is_some() =>
        {
            "quantified-bool-model-sat"
        }
        Evidence::Sat(_) => "sat-model",
        Evidence::Unsat(Some(_)) => "drat-unsat",
        Evidence::Unsat(None) => "bare-unsat",
        Evidence::UnsatAletheProof(_) => "alethe-unsat",
        Evidence::UnsatArithAletheProof(_) => "arith-alethe-unsat",
        Evidence::UnsatGuardedQuantAletheProof { .. } => "guarded-quant-alethe-unsat",
        Evidence::UnsatIntEuclideanResidue(_) => "int-euclidean-residue-unsat",
        Evidence::UnsatIntAffineGrowth(_) => "int-affine-growth-unsat",
        Evidence::UnsatIntNestedXor(_) => "int-nested-xor-unsat",
        Evidence::UnsatClosedUniversalCounterexample(_) => "closed-universal-counterexample-unsat",
        Evidence::UnsatVacuousExistsUniversalCounterexample(_) => {
            "vacuous-exists-universal-counterexample-unsat"
        }
        Evidence::UnsatNegatedExistentialWitness(_) => "negated-existential-witness-unsat",
        Evidence::UnsatBvAlternationCounterexample(_) => "bv-alternation-counterexample-unsat",
        Evidence::UnsatBvConjunctiveUniversalInstance(_) => {
            "bv-conjunctive-universal-instance-unsat"
        }
        Evidence::UnsatBvPositiveUniversalInstanceSet(_) => {
            "bv-positive-universal-instance-set-unsat"
        }
        Evidence::UnsatBvPairedExistentialTransfer(_) => "bv-paired-existential-transfer-unsat",
        Evidence::UnsatEqualityPartition(_) => "equality-partition-unsat",
        Evidence::UnsatQuantifiedCounterexampleCover(_) => "quantified-counterexample-cover-unsat",
        Evidence::UnsatTermLevel { .. } => "term-level-unsat",
        Evidence::UnsatFiniteDomainEnum { .. } => "finite-domain-enum-unsat",
        Evidence::UnsatBvDefinedEnum(_) => "bv-defined-enum-unsat",
        Evidence::UnsatBvForallNonconstant(_) => "bv-forall-nonconstant-unsat",
        Evidence::UnsatBvUfLocal(_) => "bv-uf-local-unsat",
        Evidence::UnsatSetCardinality(_) => "set-cardinality-unsat",
        Evidence::UnsatFarkas(_) => "farkas-unsat",
        Evidence::UnsatLraDpll(_) => "lra-dpll-unsat",
        Evidence::UnsatArithDpll(_) => "arith-dpll-unsat",
        Evidence::UnsatSos { .. } => "sos-unsat",
        Evidence::UnsatNraEvenPower(_) => "nra-even-power-unsat",
        Evidence::UnsatDiophantine { .. } => "diophantine-unsat",
        Evidence::UnsatBoundedIntBlast(_) => "bounded-int-blast-unsat",
        Evidence::UnsatFiniteDomainPigeonhole(_) => "finite-domain-pigeonhole-unsat",
        Evidence::UnsatBoolUfExhaustive(_) => "bool-uf-exhaustive-unsat",
        Evidence::UnsatBoolEufExhaustive(_) => "bool-euf-exhaustive-unsat",
        Evidence::UnsatBoolEufOnline(_) => "bool-euf-online-unsat",
        Evidence::UnsatUfArithCongruence(_) => "uf-arith-congruence-unsat",
        Evidence::UnsatDatatypeStructural(_) => "datatype-structural-unsat",
        Evidence::UnsatFiniteArrayExtensionality(_) => "finite-array-extensionality-unsat",
        Evidence::UnsatBoolArrayReadCollapse(_) => "bool-array-read-collapse-unsat",
        Evidence::UnsatArrayAxiom(_) => "array-axiom-unsat",
        Evidence::UnsatConstArrayDefaultMismatch(_) => "const-array-default-mismatch-unsat",
        Evidence::UnsatStoreChainReadback(_) => "store-chain-readback-unsat",
        Evidence::UnsatCrossStoreArrayDisequality(_) => "cross-store-array-disequality-unsat",
        Evidence::UnsatTermIdentity(_) => "term-identity-unsat",
        Evidence::UnsatBoolSimplification(_) => "bool-simplification-unsat",
        Evidence::UnsatBvAbstraction(_) => "bv-abstraction-unsat",
        Evidence::UnsatAlignedWriteChainCommutation(_) => "aligned-write-chain-unsat",
        Evidence::UnsatTwoByteMemcpy(_) => "two-byte-memcpy-unsat",
        Evidence::UnsatTwoElementBubbleSort(_) => "two-element-bubble-sort-unsat",
        Evidence::UnsatTwoElementSelectionSort(_) => "two-element-selection-sort-unsat",
        Evidence::UnsatTwoCellXorSwap(_) => "two-cell-xor-swap-unsat",
        Evidence::UnsatTwoByteXorSwapRoundtrip(_) => "two-byte-xor-swap-roundtrip-unsat",
        Evidence::UnsatBinarySearch16(_) => "binary-search16-unsat",
        Evidence::UnsatFifoBc04(_) => "fifo-bc04-unsat",
        Evidence::UnsatRegexEmptiness { .. } => "regex-emptiness-unsat",
        Evidence::UnsatWordClash(_) => "word-clash-unsat",
        Evidence::Unknown(_) => "unknown",
    }
}

/// Run only a *real* independent evidence check.
///
/// `Evidence::check` deliberately treats `Unsat(None)` and `Unknown` as
/// structurally well-formed (`Ok(true)`), but neither carries a certificate to
/// recheck. The dominance audit must therefore gate on `is_certified()` before
/// calling it. String SAT has a separate limitation: its faithful replay happened
/// inside the text front door and cannot be repeated against the bounded/empty
/// arena view available here.
fn independently_check_evidence(
    evidence: &Evidence,
    arena: &TermArena,
    assertions: &[TermId],
    is_string_script: bool,
) -> bool {
    if !evidence.is_certified() {
        return false;
    }
    if is_string_script && matches!(evidence, Evidence::Sat(_)) {
        return false;
    }
    let assertions = if is_string_script { &[] } else { assertions };
    evidence.check(arena, assertions).unwrap_or(false)
}

fn check_result_label(evidence: &Evidence) -> Verdict {
    match evidence {
        Evidence::Sat(_) => Verdict::Sat,
        Evidence::Unknown(_) => Verdict::Unknown,
        _ => Verdict::Unsat,
    }
}

fn record_verdict(record: &JsonValue, key: &str) -> Verdict {
    record
        .get(key)
        .and_then(JsonValue::as_str)
        .map_or(Verdict::Unknown, Verdict::from_label)
}

fn record_has_decided_mismatch(record: &JsonValue) -> bool {
    let baseline = record_verdict(record, "baseline_outcome");
    let audit = record_verdict(record, "audit_outcome");
    baseline.decided() && audit.decided() && baseline != audit
}

fn audit_instance(
    path: &Path,
    baseline_outcome: Verdict,
    cap: Duration,
    progress: &Arc<Mutex<AuditProgress>>,
) -> AuditResult {
    let start = Instant::now();
    mark_phase(progress, "read");
    let text = match std::fs::read_to_string(path) {
        Ok(text) => text,
        Err(error) => {
            return AuditResult {
                record: json!({
                    "file": path.display().to_string(),
                    "baseline_outcome": baseline_outcome.label(),
                    "audit_outcome": "read-error",
                    "baseline_matches_audit": JsonValue::Null,
                    "elapsed_ms": ms(start.elapsed()),
                    "audit_phase": "read",
                    "phase_timings_ms": {
                        "read": ms(start.elapsed()),
                    },
                    "evidence_kind": JsonValue::Null,
                    "evidence_certified": false,
                    "evidence_checked": false,
                    "lean_fragment": JsonValue::Null,
                    "lean_checked": false,
                    "lean_module_bytes": JsonValue::Null,
                    "lean_error": JsonValue::Null,
                    "trust_steps": [],
                    "trust_holes": [],
                    "dominant_candidate": false,
                    "error": format!("read failed: {error}"),
                }),
                dominant_candidate: false,
                evidence_certified: false,
                evidence_checked: false,
                lean_checked: false,
                unsat: baseline_outcome == Verdict::Unsat,
                timed_out: false,
                audit_error: true,
            };
        }
    };
    let read_ms = ms(start.elapsed());

    let config = SolverConfig::default().with_timeout(cap);
    mark_phase(progress, "parse-evidence");
    let parse_start = Instant::now();
    let mut evidence_script = match parse_script(&text) {
        Ok(script) => script,
        Err(error) => {
            return AuditResult {
                record: json!({
                    "file": path.display().to_string(),
                    "baseline_outcome": baseline_outcome.label(),
                    "audit_outcome": "parse-error",
                    "baseline_matches_audit": JsonValue::Null,
                    "elapsed_ms": ms(start.elapsed()),
                    "audit_phase": "parse-evidence",
                    "phase_timings_ms": {
                        "read": read_ms,
                        "parse_evidence": ms(parse_start.elapsed()),
                    },
                    "evidence_kind": JsonValue::Null,
                    "evidence_certified": false,
                    "evidence_checked": false,
                    "lean_fragment": JsonValue::Null,
                    "lean_checked": false,
                    "lean_module_bytes": JsonValue::Null,
                    "lean_error": JsonValue::Null,
                    "trust_steps": [],
                    "trust_holes": [],
                    "dominant_candidate": false,
                    "error": error.to_string(),
                }),
                dominant_candidate: false,
                evidence_certified: false,
                evidence_checked: false,
                lean_checked: false,
                unsat: baseline_outcome == Verdict::Unsat,
                timed_out: false,
                audit_error: true,
            };
        }
    };
    let parse_evidence_ms = ms(parse_start.elapsed());

    let assertions = evidence_script.assertions.clone();
    // A string script (bounded string/sequence encoding, or one the bounded encoder
    // declined wholesale into a word-first fallback) carries its decidable content in
    // the parser side channels, NOT in the flat arena assertions — for a word-only
    // fallback `assertions` is even EMPTY. Feeding that flat/empty view to the arena
    // front door `produce_evidence` returns a vacuous (wrong) `sat`. The string-capable
    // text front door `produce_evidence_smtlib` (soundness fix f719c27d) decides such a
    // script through `solve_smtlib` and wraps the already-sound verdict. Non-string
    // scripts keep the arena path byte-for-byte, preserving the full certificate ladder.
    let is_string_script =
        evidence_script.uses_bounded_strings || evidence_script.word_only_fallback.is_some();
    mark_phase(progress, "produce-evidence");
    let produce_start = Instant::now();
    let produced = if is_string_script {
        produce_evidence_smtlib(&text, &config)
    } else {
        produce_evidence(&mut evidence_script.arena, &assertions, &config)
    };
    let report = match produced {
        Ok(report) => report,
        Err(error) => {
            return AuditResult {
                record: json!({
                    "file": path.display().to_string(),
                    "baseline_outcome": baseline_outcome.label(),
                    "audit_outcome": "solver-error",
                    "baseline_matches_audit": JsonValue::Null,
                    "elapsed_ms": ms(start.elapsed()),
                    "audit_phase": "produce-evidence",
                    "phase_timings_ms": {
                        "read": read_ms,
                        "parse_evidence": parse_evidence_ms,
                        "produce_evidence": ms(produce_start.elapsed()),
                    },
                    "evidence_kind": JsonValue::Null,
                    "evidence_certified": false,
                    "evidence_checked": false,
                    "lean_fragment": JsonValue::Null,
                    "lean_checked": false,
                    "lean_module_bytes": JsonValue::Null,
                    "lean_error": JsonValue::Null,
                    "trust_steps": [],
                    "trust_holes": [],
                    "dominant_candidate": false,
                    "error": error.to_string(),
                }),
                dominant_candidate: false,
                evidence_certified: false,
                evidence_checked: false,
                lean_checked: false,
                unsat: baseline_outcome == Verdict::Unsat,
                timed_out: false,
                audit_error: true,
            };
        }
    };
    let produce_evidence_ms = ms(produce_start.elapsed());

    let audit_outcome = check_result_label(&report.evidence);
    let evidence_certified = report.evidence.is_certified();
    mark_phase(progress, "check-evidence");
    let check_start = Instant::now();
    // A true independent check requires a certificate on every route. In particular,
    // bare `Evidence::Unsat(None)` returns structural `Ok(true)` but has nothing to
    // replay; v1 accidentally credited 28 non-string cases on that basis. String SAT
    // adds a separate limitation: its faithful Seq replay happened inside the text
    // route, while the bounded/empty arena view here cannot repeat it. Certified string
    // UNSAT variants are self-contained and can be independently rechecked here.
    let evidence_checked = independently_check_evidence(
        &report.evidence,
        &evidence_script.arena,
        &assertions,
        is_string_script,
    );
    let evidence_check_mode = if !evidence_certified {
        "not-applicable-uncertified"
    } else if is_string_script && matches!(report.evidence, Evidence::Sat(_)) {
        "internal-route-replay-only"
    } else {
        "independent-recheck-attempted"
    };
    let check_evidence_ms = ms(check_start.elapsed());
    let trust_steps: Vec<JsonValue> = report
        .trusted_steps
        .iter()
        .map(|step| {
            json!({
                "id": step.id.label(),
                "certified": step.certified,
            })
        })
        .collect();
    let trust_holes: Vec<&'static str> = report
        .trusted_steps
        .iter()
        .filter(|step| !step.certified)
        .map(|step| step.id.label())
        .collect();

    let mut lean_fragment = JsonValue::Null;
    let mut lean_checked = false;
    let mut lean_error = JsonValue::Null;
    let mut lean_module_bytes = JsonValue::Null;
    let mut parse_lean_ms = JsonValue::Null;
    let mut lean_reconstruction_ms = JsonValue::Null;
    // A string-script `unsat` that is the certified regex derivative-emptiness class carries a
    // kernel-checked Lean `False` module that `check` re-derives from first principles; credit
    // `lean_checked` only for that variant (and only when `evidence_checked` — the honest
    // re-derivation — passed). Bare `Evidence::Unsat(None)` string unsats (word clash,
    // concat/length) have no arena refutation and no Lean module, so they stay honestly false.
    if is_string_script {
        if let Evidence::UnsatRegexEmptiness { lean_module, .. } = &report.evidence
            && evidence_checked
        {
            lean_fragment = json!("RegexEmptiness");
            lean_module_bytes = json!(lean_module.len());
            lean_checked = true;
        }
    } else if audit_outcome == Verdict::Unsat {
        mark_phase(progress, "parse-lean");
        let parse_lean_start = Instant::now();
        match parse_script(&text) {
            Ok(mut lean_script) => {
                parse_lean_ms = json!(ms(parse_lean_start.elapsed()));
                let lean_assertions = lean_script.assertions.clone();
                mark_phase(progress, "lean-reconstruction");
                let lean_start = Instant::now();
                match prove_unsat_to_lean_module(&mut lean_script.arena, &lean_assertions) {
                    Ok((fragment, module)) => {
                        lean_reconstruction_ms = json!(ms(lean_start.elapsed()));
                        lean_fragment = json!(format!("{fragment:?}"));
                        lean_module_bytes = json!(module.len());
                        lean_checked = true;
                    }
                    Err(error) => {
                        lean_reconstruction_ms = json!(ms(lean_start.elapsed()));
                        lean_error = json!(error.to_string());
                    }
                }
            }
            Err(error) => {
                parse_lean_ms = json!(ms(parse_lean_start.elapsed()));
                lean_error = json!(format!("parse failed before Lean reconstruction: {error}"));
            }
        }
    }
    mark_phase(progress, "complete");

    let dominant_candidate = match audit_outcome {
        Verdict::Sat => evidence_certified && evidence_checked,
        Verdict::Unsat => {
            evidence_certified && evidence_checked && lean_checked && trust_holes.is_empty()
        }
        Verdict::Unknown => false,
    };

    AuditResult {
        record: json!({
            "file": path.display().to_string(),
            "baseline_outcome": baseline_outcome.label(),
            "audit_outcome": audit_outcome.label(),
            "baseline_matches_audit": baseline_outcome == audit_outcome,
            "elapsed_ms": ms(start.elapsed()),
            "audit_phase": "complete",
            "phase_timings_ms": {
                "read": read_ms,
                "parse_evidence": parse_evidence_ms,
                "produce_evidence": produce_evidence_ms,
                "check_evidence": check_evidence_ms,
                "parse_lean": parse_lean_ms,
                "lean_reconstruction": lean_reconstruction_ms,
            },
            "evidence_kind": evidence_kind(&report.evidence),
            "decision_backend": report.provenance.backend,
            "evidence_certified": evidence_certified,
            "evidence_checked": evidence_checked,
            "evidence_check_mode": evidence_check_mode,
            "lean_fragment": lean_fragment,
            "lean_checked": lean_checked,
            "lean_module_bytes": lean_module_bytes,
            "lean_error": lean_error,
            "trust_steps": trust_steps,
            "trust_holes": trust_holes,
            "dominant_candidate": dominant_candidate,
        }),
        dominant_candidate,
        evidence_certified,
        evidence_checked,
        lean_checked,
        unsat: audit_outcome == Verdict::Unsat,
        timed_out: false,
        audit_error: false,
    }
}

fn audit_instance_capped(path: PathBuf, baseline_outcome: Verdict, cap: Duration) -> AuditResult {
    let (tx, rx) = mpsc::channel();
    let display = path.display().to_string();
    let wall_cap = cap.checked_add(Duration::from_secs(5)).unwrap_or(cap);
    let wall_start = Instant::now();
    let progress = Arc::new(Mutex::new(AuditProgress {
        phase: "queued",
        phase_started: Instant::now(),
    }));
    let worker_progress = Arc::clone(&progress);
    thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let _ = tx.send(audit_instance(
                &path,
                baseline_outcome,
                cap,
                &worker_progress,
            ));
        })
        .expect("spawn dominance audit thread");
    rx.recv_timeout(wall_cap).unwrap_or_else(|_| {
        let (phase, phase_elapsed_ms) = progress_snapshot(&progress);
        AuditResult {
            record: json!({
                "file": display,
                "baseline_outcome": baseline_outcome.label(),
                "audit_outcome": "timeout",
                "baseline_matches_audit": JsonValue::Null,
                "elapsed_ms": ms(wall_start.elapsed()),
                "audit_phase": phase,
                "timeout_phase": phase,
                "timeout_phase_elapsed_ms": phase_elapsed_ms,
                "evidence_kind": JsonValue::Null,
                "evidence_certified": false,
                "evidence_checked": false,
                "lean_fragment": JsonValue::Null,
                "lean_checked": false,
                "lean_module_bytes": JsonValue::Null,
                "lean_error": JsonValue::Null,
                "trust_steps": [],
                "trust_holes": ["timeout"],
                "dominant_candidate": false,
            }),
            dominant_candidate: false,
            evidence_certified: false,
            evidence_checked: false,
            lean_checked: false,
            unsat: baseline_outcome == Verdict::Unsat,
            timed_out: true,
            audit_error: false,
        }
    })
}

fn repo_rel(path: &Path) -> String {
    path.to_string_lossy().replace('\\', "/")
}

fn collect_smt2(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    let mut paths: Vec<PathBuf> = entries.filter_map(|e| e.ok().map(|e| e.path())).collect();
    paths.sort();
    for path in paths {
        if path.is_dir() {
            collect_smt2(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "smt2") {
            out.push(path);
        }
    }
}

fn logic_component_from_path(path: &str) -> Option<String> {
    let mut after_logic_root = false;
    for component in path.split('/') {
        if after_logic_root {
            return Some(component.to_owned());
        }
        after_logic_root = component == "non-incremental" || component == "synthetic";
    }
    None
}

fn status_of_text(text: &str) -> Verdict {
    for line in text.lines() {
        if let Some(rest) = line.trim().strip_prefix("(set-info :status ") {
            return Verdict::from_label(rest.trim_end_matches(')').trim());
        }
    }
    Verdict::Unknown
}

fn baseline_logic(baseline_json: &JsonValue, instances: Option<&[JsonValue]>) -> String {
    if let Some(logic) = baseline_json
        .pointer("/config/logic")
        .and_then(JsonValue::as_str)
        .filter(|logic| !logic.is_empty())
    {
        return logic.to_owned();
    }
    if let Some(logic) = baseline_json
        .pointer("/config/corpus")
        .and_then(JsonValue::as_str)
        .and_then(logic_component_from_path)
    {
        return logic;
    }
    if let Some(logic) = baseline_json
        .get("dir")
        .and_then(JsonValue::as_str)
        .and_then(logic_component_from_path)
    {
        return logic;
    }
    instances
        .and_then(|items| {
            items
                .iter()
                .filter_map(|instance| instance.get("file").and_then(JsonValue::as_str))
                .find_map(logic_component_from_path)
        })
        .unwrap_or_else(|| "unknown".to_owned())
}

fn json_usize(value: Option<u64>, default: usize) -> usize {
    value
        .and_then(|n| usize::try_from(n).ok())
        .unwrap_or(default)
}

fn usage() -> ! {
    eprintln!("usage: audit_dominance <baseline.json> [timeout_ms] [limit] [out.json]");
    std::process::exit(2);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let baseline = args.get(1).map_or_else(|| usage(), PathBuf::from);
    let timeout_ms = args
        .get(2)
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(10_000);
    let limit = args
        .get(3)
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(usize::MAX);
    let out_json = args.get(4).map(PathBuf::from);
    let cap = Duration::from_millis(timeout_ms);

    let baseline_text = std::fs::read_to_string(&baseline).expect("read baseline JSON");
    let baseline_json: JsonValue =
        serde_json::from_str(&baseline_text).expect("parse baseline JSON");
    let corpus_instances = baseline_json.get("instances").and_then(JsonValue::as_array);
    let logic = baseline_logic(&baseline_json, corpus_instances.map(Vec::as_slice));
    let slice = baseline
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or("baseline");

    let mut records = Vec::new();
    let mut audited_decided = 0usize;
    let mut baseline_decided = 0usize;
    let mut baseline_mismatches = 0usize;
    let mut dominant_candidates = 0usize;
    let mut evidence_certified = 0usize;
    let mut evidence_checked = 0usize;
    let mut lean_checked_unsat = 0usize;
    let mut audited_unsat = 0usize;
    let mut timed_out = 0usize;
    let mut audit_errors = 0usize;

    let instances_len: usize;

    if let Some(instances) = corpus_instances {
        instances_len = instances.len();
        for instance in instances {
            let outcome = instance
                .get("outcome")
                .and_then(JsonValue::as_str)
                .map_or(Verdict::Unknown, Verdict::from_label);
            if !outcome.decided() {
                continue;
            }
            baseline_decided += 1;
            if audited_decided >= limit {
                continue;
            }
            let Some(file) = instance.get("file").and_then(JsonValue::as_str) else {
                continue;
            };
            let result = audit_instance_capped(PathBuf::from(file), outcome, cap);
            if record_has_decided_mismatch(&result.record) {
                baseline_mismatches += 1;
            }
            if result.dominant_candidate {
                dominant_candidates += 1;
            }
            if result.evidence_certified {
                evidence_certified += 1;
            }
            if result.evidence_checked {
                evidence_checked += 1;
            }
            if result.unsat {
                audited_unsat += 1;
            }
            if result.lean_checked {
                lean_checked_unsat += 1;
            }
            if result.timed_out {
                timed_out += 1;
            }
            if result.audit_error {
                audit_errors += 1;
            }
            audited_decided += 1;
            records.push(result.record);
        }
    } else {
        let dir = baseline_json
            .get("dir")
            .and_then(JsonValue::as_str)
            .unwrap_or_else(|| panic!("{} has neither instances nor dir", baseline.display()));
        baseline_decided = json_usize(
            baseline_json
                .get("axeyum_decided")
                .and_then(JsonValue::as_u64),
            0,
        );
        let mut files = Vec::new();
        collect_smt2(Path::new(dir), &mut files);
        instances_len = json_usize(
            baseline_json.get("considered").and_then(JsonValue::as_u64),
            files.len(),
        );
        let baseline_decided_all_considered = baseline_decided == instances_len;

        for file in files {
            if audited_decided >= limit {
                break;
            }
            let Ok(text) = std::fs::read_to_string(&file) else {
                continue;
            };
            if parse_script(&text).is_err() {
                continue;
            }
            let baseline_outcome = status_of_text(&text);
            if !baseline_outcome.decided() {
                continue;
            }
            let result = audit_instance_capped(file, baseline_outcome, cap);
            let audit_outcome = result
                .record
                .get("audit_outcome")
                .and_then(JsonValue::as_str)
                .map_or(Verdict::Unknown, Verdict::from_label);
            if !baseline_decided_all_considered && !audit_outcome.decided() {
                continue;
            }
            if record_has_decided_mismatch(&result.record) {
                baseline_mismatches += 1;
            }
            if result.dominant_candidate {
                dominant_candidates += 1;
            }
            if result.evidence_certified {
                evidence_certified += 1;
            }
            if result.evidence_checked {
                evidence_checked += 1;
            }
            if result.unsat {
                audited_unsat += 1;
            }
            if result.lean_checked {
                lean_checked_unsat += 1;
            }
            if result.timed_out {
                timed_out += 1;
            }
            if result.audit_error {
                audit_errors += 1;
            }
            audited_decided += 1;
            records.push(result.record);
        }
    }

    let complete = audited_decided == baseline_decided;
    let dominant_pct_audited = if audited_decided == 0 {
        0.0
    } else {
        100.0 * dominant_candidates as f64 / audited_decided as f64
    };
    let lean_unsat_pct = if audited_unsat == 0 {
        100.0
    } else {
        100.0 * lean_checked_unsat as f64 / audited_unsat as f64
    };

    let artifact = json!({
        "version": 2,
        "baseline": repo_rel(&baseline),
        "logic": logic,
        "slice": slice,
        "timeout_ms": timeout_ms,
        "limit": if limit == usize::MAX { JsonValue::Null } else { json!(limit) },
        "complete_audit": complete,
        "summary": {
            "instances": instances_len,
            "baseline_decided": baseline_decided,
            "audited_decided": audited_decided,
            "audited_unsat": audited_unsat,
            "evidence_certified": evidence_certified,
            "evidence_checked": evidence_checked,
            "lean_checked_unsat": lean_checked_unsat,
            "lean_unsat_pct": lean_unsat_pct,
            "dominant_candidates": dominant_candidates,
            "dominant_pct_audited": dominant_pct_audited,
            "baseline_mismatches": baseline_mismatches,
            "audit_errors": audit_errors,
            "timeouts": timed_out,
        },
        "instances": records,
    });

    let rendered = serde_json::to_string_pretty(&artifact).expect("render dominance audit JSON");
    if let Some(out) = out_json {
        std::fs::write(&out, rendered).expect("write dominance audit JSON");
        println!("wrote {}", out.display());
    } else {
        println!("{rendered}");
    }

    eprintln!(
        "dominance audit {logic}: {dominant_candidates}/{audited_decided} audited decided ({dominant_pct_audited:.1}%), Lean unsat {lean_checked_unsat}/{audited_unsat} ({lean_unsat_pct:.1}%), mismatches {baseline_mismatches}, audit errors {audit_errors}, timeouts {timed_out}"
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bare_unsat_structural_ok_is_not_an_independent_check() {
        let arena = TermArena::new();
        let evidence = Evidence::Unsat(None);
        assert!(evidence.check(&arena, &[]).unwrap());
        assert!(!evidence.is_certified());
        assert!(!independently_check_evidence(
            &evidence,
            &arena,
            &[],
            false
        ));
    }
}
