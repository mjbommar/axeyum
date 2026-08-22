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
    Evidence, LeanModuleContent, LraReconstructCtx, SolverConfig, produce_evidence,
    produce_evidence_smtlib, prove_unsat_to_lean_module, scan_proof_fragment,
};
#[cfg(test)]
use axeyum_solver::{EvidenceCheck, NoCheckReason};
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
    /// What the current phase is working ON, when the phase name alone does not
    /// say. Today: the `ProofFragment` a lean reconstruction is attempting.
    ///
    /// Without it, a timeout in `lean-reconstruction` is unreadable. Measured
    /// 2026-08-20, NINE of ten timing-out rows landed in that one phase, and
    /// they were three unrelated failures: an exponential blowup, a CORRECT
    /// decline arriving 35s late because `lra_ctx()` builds a `CReal` prelude
    /// before the route knows it will decline, and a SUCCESS emitting a 2.4 GB
    /// module. The fragment name separates all three at a glance and costs
    /// microseconds -- `scan_proof_fragment` is the same classification the
    /// reconstruction is about to do anyway.
    detail: Option<String>,
}

fn mark_phase(progress: &Arc<Mutex<AuditProgress>>, phase: &'static str) {
    if let Ok(mut state) = progress.lock() {
        state.phase = phase;
        state.phase_started = Instant::now();
        state.detail = None;
    }
}

/// Annotate the CURRENT phase without restarting its clock.
fn mark_detail(progress: &Arc<Mutex<AuditProgress>>, detail: String) {
    if let Ok(mut state) = progress.lock() {
        state.detail = Some(detail);
    }
}

fn progress_snapshot(progress: &Arc<Mutex<AuditProgress>>) -> (&'static str, f64, Option<String>) {
    match progress.lock() {
        Ok(state) => (
            state.phase,
            state.phase_started.elapsed().as_secs_f64() * 1000.0,
            state.detail.clone(),
        ),
        Err(_) => ("poisoned-progress", 0.0, None),
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
        Evidence::UnsatIntQuadraticNegativeDiscriminant(_) => {
            "int-quadratic-negative-discriminant-unsat"
        }
        Evidence::UnsatIntUnivariatePoly(_) => "int-univariate-poly-unsat",
        Evidence::UnsatNraEvenPower(_) => "nra-even-power-unsat",
        Evidence::UnsatRealZeroProduct(_) => "real-zero-product-unsat",
        Evidence::UnsatRealProduct(_) => "real-product-unsat",
        Evidence::UnsatRealHandelman(_) => "real-handelman-unsat",
        Evidence::UnsatMonomialBound(_) => "monomial-bound-unsat",
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
        Evidence::UnsatStringLength { .. } => "string-length-unsat",
        Evidence::UnsatQuantInstanceSet(_) => "quant-instance-set-unsat",
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
/// Re-derive the certificate, **in the arena that produced it**.
///
/// "Independently" is relative to the BASELINE run — this re-parses the file and
/// re-runs `produce_evidence` — but the check below is handed
/// `evidence_script.arena`, the same arena the evidence was just produced on. It
/// is therefore an in-process re-derivation, not a re-check against a fresh
/// parse.
///
/// For most certificate families that distinction does not matter, because they
/// are self-contained: `bv2nat_bound_certificate` says outright that its check
/// "reads only the carried Alethe commands, not the arena", and DRAT objects are
/// the same. For a certificate that carries `TermId`s, it matters a great deal —
/// those ids name slots in the producing arena and mean nothing in another.
///
/// Measured 2026-08-17, at this repository's expense: a quantifier certificate
/// that stored instance ids passed this check and FAILED when
/// `smtcomp_cli --evidence` re-validated it against a fresh parse, reporting
/// `certified=1` alongside `arena=FAIL`. One instance passed by allocation-order
/// coincidence; two did not. `crates/axeyum-solver/tests/certified_implies_revalidatable.rs`
/// is the guard for the stronger property, and it currently exercises 3 of the
/// 49 certified evidence kinds these audits actually observe.
///
/// So read `evidence_checked` as "the certificate re-derives", not as "the
/// certificate is portable". They are different claims and only one of them is
/// measured here.
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
    let mut lean_content = JsonValue::Null;
    let mut lean_error = JsonValue::Null;
    let mut lean_module_bytes = JsonValue::Null;
    let mut parse_lean_ms = JsonValue::Null;
    let mut lean_reconstruction_ms = JsonValue::Null;
    // A string script has no faithful arena view, so `prove_unsat_to_lean_module`
    // is not the route: the two string classes that reconstruct carry (or
    // re-derive) their own kernel-checked `False` module, and `check` re-derives
    // it from first principles rather than reading the stored string back. Credit
    // `lean_checked` only for those, and only when `evidence_checked` — the
    // honest re-derivation — passed. Everything else stays honestly false: a
    // word clash, a case-split length refutation, and a bare
    // `Evidence::Unsat(None)` have no Lean module and do not pretend to.
    if is_string_script {
        match &report.evidence {
            Evidence::UnsatRegexEmptiness { lean_module, .. } if evidence_checked => {
                lean_fragment = json!("RegexEmptiness");
                lean_module_bytes = json!(lean_module.len());
                lean_checked = true;
                // CLASSIFY THE STRING ROUTE TOO. These two labels are not
                // `ProofFragment` variants, so `lean_module_content()` never
                // sees them and this branch used to leave `lean_content` null.
                // Measured 2026-08-21: that silently left 13 of 269
                // Lean-reconstructed `unsat` unclassified (11 `RegexEmptiness`,
                // 2 `StringLength`), so `lean_theory_unsat` read 129 where the
                // reasoning half is 142 -- an undercount of the REASONING side,
                // i.e. in the direction that makes the claim look weaker.
                //
                // Read the module rather than a table: `of_module_source` keys
                // on `STRUCTURAL_ATTESTATION_MARKER`, which only the shared
                // structural emitter in `reconstruct/direct.rs` writes. The
                // string reconstructors do not use it, so this is a measurement
                // of the artifact and not an assumption about the route.
                lean_content = match LeanModuleContent::of_module_source(lean_module) {
                    LeanModuleContent::TheoryReconstruction => json!("theory"),
                    LeanModuleContent::StructuralAttestation => json!("attestation"),
                };
            }
            Evidence::UnsatStringLength {
                lean_module: Some(module),
                ..
            } if evidence_checked => {
                lean_fragment = json!("StringLength");
                lean_module_bytes = json!(module.len());
                lean_checked = true;
                lean_content = match LeanModuleContent::of_module_source(module) {
                    LeanModuleContent::TheoryReconstruction => json!("theory"),
                    LeanModuleContent::StructuralAttestation => json!("attestation"),
                };
            }
            _ => {}
        }
    } else if audit_outcome == Verdict::Unsat {
        mark_phase(progress, "parse-lean");
        let parse_lean_start = Instant::now();
        match parse_script(&text) {
            Ok(mut lean_script) => {
                parse_lean_ms = json!(ms(parse_lean_start.elapsed()));
                let lean_assertions = lean_script.assertions.clone();
                mark_phase(progress, "lean-reconstruction");
                // Classify FIRST and record it, so a timeout row says which
                // route was being attempted rather than only that one was.
                mark_detail(
                    progress,
                    format!(
                        "{:?}",
                        scan_proof_fragment(&lean_script.arena, &lean_assertions)
                    ),
                );
                let lean_start = Instant::now();
                match prove_unsat_to_lean_module(&mut lean_script.arena, &lean_assertions) {
                    Ok((fragment, module)) => {
                        lean_reconstruction_ms = json!(ms(lean_start.elapsed()));
                        lean_fragment = json!(format!("{fragment:?}"));
                        lean_module_bytes = json!(module.len());
                        lean_checked = true;
                        // WHAT KIND of Lean module this is, not just that one
                        // exists. `lean_checked` alone reads as "Lean proved
                        // something about the query" and for roughly half of
                        // these it does not: 29 fragments emit a structural
                        // ATTESTATION — `axiom P`, `axiom Not P`,
                        // `theorem _ : False` — which kernel-checks, is
                        // sorry-free, and contains none of the reasoning. The
                        // checking that mattered happened in Rust.
                        //
                        // Measured 2026-08-21 over the 269 Lean-reconstructed
                        // `unsat` in the committed audits: 142 reason, 127
                        // attest. `check-lean-gate.sh` already reports and
                        // floors this split for the crosscheck families; the
                        // dominance denominator did not, so the headline read
                        // stronger than it was by a factor of nearly two.
                        //
                        // The 142 counts the 13 string-route modules classified
                        // in the `is_string_script` branch above. Before that
                        // branch classified them this field recorded only 129,
                        // so a reader summing `lean_theory_unsat` got a
                        // different number from the one written here.
                        lean_content = match fragment.lean_module_content() {
                            Some(LeanModuleContent::TheoryReconstruction) => {
                                json!("theory")
                            }
                            Some(LeanModuleContent::StructuralAttestation) => json!("attestation"),
                            // A fragment outside the `ProofFragment` table —
                            // the string and regex routes reconstruct through
                            // their own emitters. Recorded as unclassified
                            // rather than silently counted either way.
                            None => json!("unclassified"),
                        };
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
            "lean_module_content": lean_content,
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
        detail: None,
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
        let (phase, phase_elapsed_ms, phase_detail) = progress_snapshot(&progress);
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
                "timeout_phase_detail": phase_detail
                    .map_or(JsonValue::Null, JsonValue::from),
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

/// Mark a record the directory-backed sweep KEPT but did not count in
/// `audited_decided`, and say why.
///
/// THE ROW THAT SHRANK ITS NUMERATOR AND DENOMINATOR TOGETHER. The
/// directory-backed path used to `continue` at each of the sites that call
/// this, so an instance the audit could not decide left **no trace at all**:
/// not in `audited_decided`, not in `timeouts`, not in `instances`. The
/// artifact then reported `timeouts: 0`, which was true and meant nothing — a
/// row that timed out on ten instances and a row that timed out on none emitted
/// byte-identical summaries, and only the two synthetic rows take this path, so
/// `newly_decided` covered 33 of 35 rows by construction while a `0` on the
/// other two was not evidence of anything.
///
/// Keeping them OUT of `audited_decided` is still right, and is a different
/// thing from dropping them. A directory-backed baseline records counts
/// (`considered`, `axeyum_decided`) and not files, so the sweep cannot tell
/// which instances its baseline decided; an instance neither side decided must
/// therefore not enter a percentage whose denominator is meant to be the
/// baseline's population. Excluded is reportable. Vanished is not.
fn mark_excluded(record: &mut JsonValue, reason: &str) {
    if let Some(map) = record.as_object_mut() {
        map.insert("excluded_from_audited".to_owned(), json!(true));
        map.insert("excluded_reason".to_owned(), json!(reason));
    }
}

/// A record for a file the sweep never got as far as running.
fn unaudited_record(file: &Path, reason: &str) -> JsonValue {
    let mut record = json!({
        "file": file.display().to_string(),
        "baseline_outcome": Verdict::Unknown.label(),
        "audit_outcome": Verdict::Unknown.label(),
        "baseline_matches_audit": JsonValue::Null,
        "evidence_kind": JsonValue::Null,
        "evidence_certified": false,
        "evidence_checked": false,
        "lean_fragment": JsonValue::Null,
        "lean_checked": false,
        "trust_steps": [],
        "trust_holes": [reason],
        "dominant_candidate": false,
    });
    mark_excluded(&mut record, reason);
    record
}

/// What a DIRECTORY-backed row can honestly say about the instances its
/// baseline left undecided.
///
/// The JSON-backed path re-probes per instance, because its baseline names its
/// files. A directory-backed baseline records only counts, so nothing here can
/// name the undecided ones. What it CAN do is bound them. This sweep runs every
/// `.smt2` under the directory, so when the directory is the population the
/// baseline considered:
///
/// * all `considered - axeyum_decided` instances the baseline left undecided
///   were re-run, and
/// * at least `audited_decided - axeyum_decided` of this audit's decisions land
///   on files the baseline did not decide (pigeonhole: both sides decided out
///   of the same `considered` files).
///
/// Both are counts, not attributions, which is why the artifact stamps
/// `newly_decided_attribution` — a lower bound derived from two totals must not
/// be read as the per-instance measurement the JSON path produces.
///
/// Returns `None` when the populations cannot be reconciled — the directory has
/// grown or shrunk since the baseline ran, `limit` cut the sweep short, or the
/// baseline claims more decisions than it considered — because then the bound
/// is not derivable and the artifact must say so rather than print a number it
/// cannot defend.
/// Does a directory-backed instance belong in `audited_decided`?
///
/// `true` keeps it in the denominator. `false` means EXCLUDED, which is not the
/// same as dropped — see `mark_excluded`.
///
/// When the baseline decided everything it considered, its population is the
/// whole directory and every instance is comparable, including ones this audit
/// fails to decide (that is a regression, and it must be visible in the
/// percentage). When the baseline decided only some of what it considered, the
/// audit cannot tell which, so an instance neither side decided is not
/// attributable to either population.
fn counts_toward_audited(baseline_decided_all_considered: bool, audit_outcome: Verdict) -> bool {
    baseline_decided_all_considered || audit_outcome.decided()
}

fn dir_undecided_bound(
    files_len: usize,
    instances_len: usize,
    baseline_decided: usize,
    audited_decided: usize,
    swept_every_file: bool,
) -> Option<(usize, usize)> {
    if !swept_every_file || files_len != instances_len || baseline_decided > instances_len {
        return None;
    }
    Some((
        instances_len - baseline_decided,
        audited_decided.saturating_sub(baseline_decided),
    ))
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

    // Warm the constructed-real prelude BEFORE the per-instance timer starts.
    //
    // Building it costs **31.9 s the first time in a process and 0.4 s every
    // time after** — an 80x difference, measured by
    // `axeyum-lean-kernel --example prelude_build_timing`. It is shared
    // infrastructure, not per-instance work, but the audit made whichever
    // instance happened to reach an LRA reconstruction FIRST pay all of it,
    // inside a 15 s per-instance cap it cannot survive.
    //
    // That produced four rows recorded as `timeout` whose emitter had in fact
    // returned the CORRECT decline — `cli__regress0__arith__div.01` reports the
    // same `malformed la_generic step` message it always did, 35 s later, of
    // which `build_creal_prelude` is 35.23 s. They were then scored as
    // proof-production errors.
    //
    // Warming here does not make anything faster; it stops one instance being
    // billed for the process. The cost is reported separately so it stays
    // visible rather than disappearing into setup.
    let warm_start = Instant::now();
    let warmed = LraReconstructCtx::try_new_over_constructed_reals().is_ok();
    let prelude_warm_ms = ms(warm_start.elapsed());
    eprintln!(
        "dominance audit: constructed-real prelude warmed in {prelude_warm_ms:.0} ms (ok={warmed})"
    );

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
    // How many baseline-UNDECIDED instances were re-probed, and how many of
    // those the solver decides today. See the long comment at the skip site.
    let mut newly_audited = 0usize;
    let mut newly_decided = 0usize;
    // How `newly_audited` / `newly_decided` were obtained. The JSON path names
    // its baseline's files and re-probes each one; the directory path can only
    // bound the same quantity from two totals (`dir_undecided_bound`). Reading
    // a bound as a measurement is exactly the mistake this artifact exists to
    // stop, so the artifact says which it is.
    let mut newly_decided_attribution = "per-instance";
    // Instances the DIRECTORY-backed sweep keeps out of `audited_decided`.
    // Every one of these used to be dropped without a record; see
    // `mark_excluded` for what that cost.
    let mut excluded_audit_undecided = 0usize;
    let mut excluded_audit_undecided_timeouts = 0usize;
    let mut excluded_audit_undecided_errors = 0usize;
    let mut excluded_status_unknown = 0usize;
    let mut status_unknown_reprobed = 0usize;
    let mut status_unknown_decided = 0usize;
    let mut excluded_unparsed = 0usize;
    let mut excluded_unreadable = 0usize;
    // Of the Lean-reconstructed unsat, how many carry REASONING rather than a
    // structural attestation. See the producer for why the distinction matters.
    let mut lean_theory_unsat = 0usize;
    // Re-probing the undecided set is pure added cost on rows where nothing has
    // changed, so it is capped independently of `limit`. A row with a zero
    // baseline is exactly the case this must cover, and those rows are small.
    let undecided_cap: usize = std::env::var("AXEYUM_AUDIT_UNDECIDED_CAP")
        .ok()
        .and_then(|raw| raw.parse().ok())
        .unwrap_or(64);

    let instances_len: usize;

    if let Some(instances) = corpus_instances {
        instances_len = instances.len();
        for instance in instances {
            let outcome = instance
                .get("outcome")
                .and_then(JsonValue::as_str)
                .map_or(Verdict::Unknown, Verdict::from_label);
            if !outcome.decided() {
                // THE ZERO THAT COULD NOT MOVE. This branch used to `continue`,
                // so an instance the baseline recorded as undecided was never
                // re-run — and a row whose baseline decided NOTHING reported
                // `audited_decided: 0` forever, no matter what the solver
                // learned to do afterwards.
                //
                // That is not hypothetical. `quantified LIA` was recorded 0/12
                // on 2026-06-24; measured through the shipped front door on
                // 2026-08-21 it is **12/12**. The audit re-ran on 2026-08-21 and
                // still emitted `instances: []`, because every instance was
                // filtered out here. Three months of a capability the project
                // had, published as a hole it did not, and the 2026-07-07 gap
                // analysis named it "the biggest categorical hole" on the
                // strength of this number.
                //
                // So the undecided ones are re-audited too, capped separately so
                // this cannot blow up a large row's runtime, and counted as
                // `newly_decided` — a gain the artifact can show rather than a
                // zero it can only repeat.
                if newly_audited < undecided_cap {
                    newly_audited += 1;
                    if let Some(file) = instance.get("file").and_then(JsonValue::as_str) {
                        let probe = audit_instance_capped(PathBuf::from(file), outcome, cap);
                        let probe_outcome = probe
                            .record
                            .get("audit_outcome")
                            .and_then(JsonValue::as_str)
                            .map_or(Verdict::Unknown, Verdict::from_label);
                        if probe_outcome.decided() {
                            newly_decided += 1;
                            records.push(probe.record);
                        }
                    }
                }
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
                if result
                    .record
                    .get("lean_module_content")
                    .and_then(JsonValue::as_str)
                    == Some("theory")
                {
                    lean_theory_unsat += 1;
                }
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
        let files_len = files.len();
        let mut swept_every_file = true;

        for file in files {
            if audited_decided >= limit {
                swept_every_file = false;
                break;
            }
            let Ok(text) = std::fs::read_to_string(&file) else {
                excluded_unreadable += 1;
                records.push(unaudited_record(&file, "unreadable"));
                continue;
            };
            if parse_script(&text).is_err() {
                excluded_unparsed += 1;
                records.push(unaudited_record(&file, "unparsed"));
                continue;
            }
            let baseline_outcome = status_of_text(&text);
            if !baseline_outcome.decided() {
                // No declared `:status`, so there is no baseline verdict to be
                // dominant over and the instance cannot enter the denominator.
                // It can still be RUN, and running it is the only way a
                // capability on this shape becomes visible at all — the JSON
                // path learned that the expensive way (quantified LIA read 0/12
                // for three months while the solver decided 12/12).
                excluded_status_unknown += 1;
                if status_unknown_reprobed < undecided_cap {
                    status_unknown_reprobed += 1;
                    let probe = audit_instance_capped(file, baseline_outcome, cap);
                    let probe_outcome = probe
                        .record
                        .get("audit_outcome")
                        .and_then(JsonValue::as_str)
                        .map_or(Verdict::Unknown, Verdict::from_label);
                    if probe_outcome.decided() {
                        status_unknown_decided += 1;
                    }
                    let mut record = probe.record;
                    mark_excluded(&mut record, "benchmark-status-unknown");
                    records.push(record);
                } else {
                    records.push(unaudited_record(
                        &file,
                        "benchmark-status-unknown-over-reprobe-cap",
                    ));
                }
                continue;
            }
            let result = audit_instance_capped(file, baseline_outcome, cap);
            let audit_outcome = result
                .record
                .get("audit_outcome")
                .and_then(JsonValue::as_str)
                .map_or(Verdict::Unknown, Verdict::from_label);
            if !counts_toward_audited(baseline_decided_all_considered, audit_outcome) {
                excluded_audit_undecided += 1;
                if result.timed_out {
                    excluded_audit_undecided_timeouts += 1;
                }
                if result.audit_error {
                    excluded_audit_undecided_errors += 1;
                }
                let mut record = result.record;
                mark_excluded(&mut record, "audit-undecided-baseline-population-unknown");
                records.push(record);
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
                if result
                    .record
                    .get("lean_module_content")
                    .and_then(JsonValue::as_str)
                    == Some("theory")
                {
                    lean_theory_unsat += 1;
                }
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

        match dir_undecided_bound(
            files_len,
            instances_len,
            baseline_decided,
            audited_decided,
            swept_every_file,
        ) {
            Some((undecided, gained)) => {
                newly_audited = undecided;
                newly_decided = gained;
                newly_decided_attribution = "count-inferred";
            }
            None => newly_decided_attribution = "unavailable",
        }
    }

    // `>=`, not `==`. **Beating the baseline used to delete the logic from the
    // report.**
    //
    // `complete_audit` means "this audit re-ran every instance the baseline
    // decided", and `gen-proof-gap-matrix.py` skips any audit where it is false.
    // With `==`, an audit that decides MORE than its baseline — an improvement —
    // was scored incomplete and dropped entirely.
    //
    // Measured 2026-08-20: `qf-nra-synthetic-graduated` decided 31 against a
    // baseline of 30 and vanished from the matrix. That single drop was the
    // ENTIRE apparent decline in the day's numbers; counting it, dominance was
    // flat at 261. A metric that punishes improvement by making it invisible is
    // worse than one that merely lags.
    //
    // Deciding FEWER is still incomplete, which is the property the flag exists
    // to carry: the audit could not reproduce the baseline's population, so its
    // percentages are over a different denominator and must not be published as
    // comparable.
    let complete = audited_decided >= baseline_decided;
    let excluded_total = excluded_audit_undecided
        + excluded_status_unknown
        + excluded_unparsed
        + excluded_unreadable;
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
        "version": 4,
        "source_revision": source_revision(),
        "baseline": repo_rel(&baseline),
        "logic": logic,
        "slice": slice,
        "timeout_ms": timeout_ms,
        "prelude_warm_ms": prelude_warm_ms,
        "prelude_warmed": warmed,
        "limit": if limit == usize::MAX { JsonValue::Null } else { json!(limit) },
        "complete_audit": complete,
        "summary": {
            "instances": instances_len,
            "baseline_decided": baseline_decided,
            "audited_decided": audited_decided,
            "baseline_undecided_reprobed": newly_audited,
            "newly_decided": newly_decided,
            "newly_decided_attribution": newly_decided_attribution,
            "audited_unsat": audited_unsat,
            "evidence_certified": evidence_certified,
            "evidence_checked": evidence_checked,
            "lean_checked_unsat": lean_checked_unsat,
            "lean_theory_unsat": lean_theory_unsat,
            "lean_unsat_pct": lean_unsat_pct,
            "dominant_candidates": dominant_candidates,
            "dominant_pct_audited": dominant_pct_audited,
            "baseline_mismatches": baseline_mismatches,
            "audit_errors": audit_errors,
            "timeouts": timed_out,
            // Instances this audit ran (or could not run) that are NOT in
            // `audited_decided`. `timeouts` above counts only the audited
            // population, so before these existed a directory-backed row could
            // time out repeatedly and still publish `timeouts: 0`.
            "excluded_from_audited": {
                "total": excluded_total,
                "audit_undecided": excluded_audit_undecided,
                "audit_undecided_timeouts": excluded_audit_undecided_timeouts,
                "audit_undecided_errors": excluded_audit_undecided_errors,
                "benchmark_status_unknown": excluded_status_unknown,
                "benchmark_status_unknown_reprobed": status_unknown_reprobed,
                "benchmark_status_unknown_decided": status_unknown_decided,
                "unparsed": excluded_unparsed,
                "unreadable": excluded_unreadable,
            },
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

    // A row whose baseline decided nothing prints `0/0 audited decided (0.0%)`,
    // which reads as "there is nothing here" — and that is precisely how a
    // frozen zero stayed invisible for three months while the solver could
    // decide 12 of those 12. If the re-probe found capability the baseline never
    // recorded, say so on the line a human actually reads.
    // Split the Lean figure on the line a human reads. `Lean unsat 85/85` invites
    // "Lean proved 85 things about these queries"; for a structural attestation it
    // proved a tautology, and the reader cannot tell without this.
    let attesting = lean_checked_unsat.saturating_sub(lean_theory_unsat);
    let newly = if newly_decided > 0 {
        format!(
            ", NEWLY DECIDED {newly_decided}/{newly_audited} the baseline recorded as undecided ({newly_decided_attribution}; the baseline is stale)"
        )
    } else {
        String::new()
    };
    // `timeouts {timed_out}` is over the AUDITED population only. A
    // directory-backed row excludes what it cannot decide, so without this
    // clause a row that timed out on every excluded instance still printed
    // `timeouts 0` — true, and worthless.
    let excluded = if excluded_total > 0 {
        format!(
            ", EXCLUDED {excluded_total} not in the audited population (audit-undecided {excluded_audit_undecided} of which timeouts {excluded_audit_undecided_timeouts} errors {excluded_audit_undecided_errors}, status-unknown {excluded_status_unknown} of which decided {status_unknown_decided}, unparsed {excluded_unparsed}, unreadable {excluded_unreadable})"
        )
    } else {
        String::new()
    };
    eprintln!(
        "dominance audit {logic}: {dominant_candidates}/{audited_decided} audited decided ({dominant_pct_audited:.1}%), Lean unsat {lean_checked_unsat}/{audited_unsat} ({lean_unsat_pct:.1}%, of which {lean_theory_unsat} reason and {attesting} attest), mismatches {baseline_mismatches}, audit errors {audit_errors}, timeouts {timed_out}{newly}{excluded}"
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    // --- the directory-backed sweep's exclusion accounting ---------------
    //
    // Each guard below was deleted in turn and the suite re-run; the mutation
    // results are recorded in the commit that introduced these tests. A guard
    // whose deletion kills nothing is worse than no guard.

    #[test]
    fn a_baseline_that_decided_everything_keeps_its_undecided_instances() {
        // The audit failing where the baseline succeeded is a REGRESSION and
        // must stay in the denominator. Positive control for the exclusion
        // tests below: same undecided verdict, opposite disposition.
        assert!(counts_toward_audited(true, Verdict::Unknown));
        assert!(counts_toward_audited(true, Verdict::Sat));
    }

    #[test]
    fn an_unattributable_undecided_instance_is_excluded_not_counted() {
        assert!(!counts_toward_audited(false, Verdict::Unknown));
        // ...but a DECIDED one is still counted even then.
        assert!(counts_toward_audited(false, Verdict::Unsat));
    }

    #[test]
    fn dir_bound_is_the_pigeonhole_gain_over_the_baseline() {
        // `qf-nra-synthetic-graduated`: 33 considered, baseline decided 30,
        // this audit decides 33. Three of those decisions cannot be on files
        // the baseline decided.
        assert_eq!(dir_undecided_bound(33, 33, 30, 33, true), Some((3, 3)));
        // A row whose baseline decided everything has nothing to re-probe.
        assert_eq!(dir_undecided_bound(32, 32, 32, 32, true), Some((0, 0)));
    }

    #[test]
    fn dir_bound_never_reports_a_negative_gain() {
        // Deciding FEWER than the baseline is a regression, not a gain of
        // `-1`. `complete_audit` is what carries that; this must clamp.
        assert_eq!(dir_undecided_bound(33, 33, 30, 29, true), Some((3, 0)));
    }

    #[test]
    fn dir_bound_declines_when_limit_cut_the_sweep_short() {
        // `audited_decided` is then over a prefix of the directory, so the
        // pigeonhole argument does not hold.
        assert_eq!(dir_undecided_bound(33, 33, 30, 33, false), None);
    }

    #[test]
    fn dir_bound_declines_when_the_directory_is_not_the_baseline_population() {
        // A file added or removed since the baseline ran breaks the shared
        // denominator the argument needs.
        assert_eq!(dir_undecided_bound(34, 33, 30, 33, true), None);
        assert_eq!(dir_undecided_bound(32, 33, 30, 32, true), None);
    }

    #[test]
    fn dir_bound_declines_on_an_incoherent_baseline() {
        // `axeyum_decided > considered` cannot be true; subtracting would
        // underflow, and `saturating_sub` would hide it as a confident zero.
        assert_eq!(dir_undecided_bound(33, 33, 40, 33, true), None);
    }

    #[test]
    fn mark_excluded_flags_the_record() {
        let mut record = json!({"file": "x.smt2"});
        mark_excluded(&mut record, "unparsed");
        assert_eq!(record.get("excluded_from_audited"), Some(&json!(true)));
    }

    #[test]
    fn an_unaudited_file_still_produces_a_record_that_says_why() {
        // The whole defect in one assertion: this used to be `continue`.
        let record = unaudited_record(Path::new("corpus/x.smt2"), "unreadable");
        assert_eq!(record.get("file"), Some(&json!("corpus/x.smt2")));
        assert_eq!(record.get("excluded_reason"), Some(&json!("unreadable")));
        assert_eq!(record.get("trust_holes"), Some(&json!(["unreadable"])));
    }

    #[test]
    fn bare_unsat_structural_ok_is_not_an_independent_check() {
        // THIS TEST HAD BEEN FAILING SINCE ADR-0384 AND NOTHING RAN IT.
        // `Evidence::check` used to return `true` for a bare `unsat`, meaning
        // "no objection"; ADR-0384 made it three-valued, so `Unsat(None)` is
        // `NothingToCheck(UncertifiedUnsat)` and `check` -- which is
        // `is_verified()` -- is now `false`. The assertion above was the old
        // `true`. No gate compiled this suite (`cargo test -p axeyum-bench
        // --example audit_dominance` appeared in no script), so the audit
        // harness for this project's dominance numbers shipped a red test
        // invisibly. `scripts/check.sh` now runs it.
        let arena = TermArena::new();
        let evidence = Evidence::Unsat(None);
        assert_eq!(
            evidence.check_outcome(&arena, &[]).unwrap(),
            EvidenceCheck::NothingToCheck(NoCheckReason::UncertifiedUnsat),
        );
        assert!(!evidence.check(&arena, &[]).unwrap());
        assert!(!evidence.is_certified());
        assert!(!independently_check_evidence(&evidence, &arena, &[], false));
    }
}

/// The source revision this audit actually ran against, and whether the tree was
/// clean when it did.
///
/// A dominance audit recorded `logic`, `slice`, `timeout_ms` and a `version`
/// integer — and nothing about the code that produced it. That is not a
/// cosmetic omission. Measured 2026-08-20: `r0_QF_SLIA_replace-find-base` is
/// recorded in a committed audit as `audit_outcome=unsat,
/// baseline_matches_audit=true`, and building `8aff8d507` — the commit that
/// last touched that audit — and running the byte-identical corpus file returns
/// **`sat`**, a wrong answer on a query z3 decides unsat. The row disagrees
/// with the tree it appears to belong to, because the file's commit date is the
/// date of a SCHEMA MIGRATION ("refresh bare-route audits to v2"), not of the
/// measurement. Nothing in the artifact let anyone notice, and the proof-gap
/// matrix replays these rows into planning documents as current.
///
/// So every audit now carries the sha it ran against. `dirty` matters as much as
/// the sha: an audit produced from a modified worktree describes a tree that has
/// no name and cannot be rebuilt, and saying so is more useful than a sha that
/// silently means something else.
fn source_revision() -> JsonValue {
    let rev = std::process::Command::new("git")
        .args(["rev-parse", "HEAD"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_owned())
        .filter(|s| !s.is_empty());
    let dirty = std::process::Command::new("git")
        .args(["status", "--porcelain", "--untracked-files=no"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| !String::from_utf8_lossy(&o.stdout).trim().is_empty());
    if let Some(sha) = rev {
        return json!({
            "sha": sha,
            "dirty": dirty.map_or(JsonValue::Null, JsonValue::from),
            "source": "git",
        });
    }

    // No git. That is the NORMAL case for the clean tree this audit most wants
    // to run in: `scripts/lane-snapshot.sh` extracts `git archive <ref>`, which
    // has no `.git` at all — so the recommended way to get an unmodified tree was
    // also the only way to lose the sha. Measured here: a snapshot run stamped
    // `sha: "unknown"` while the shared worktree, which DID have git, stamped
    // `dirty: true` because other lanes had uncommitted files. Neither is the
    // artifact anyone wants.
    //
    // `lane-snapshot.sh` already writes the ref it extracted to `.lane-ref`, so
    // read that. A `git archive` of a commit is clean by construction — there is
    // nowhere for a modification to have come from — which is why `dirty` is
    // `false` here and not `null`.
    if let Ok(text) = std::fs::read_to_string(".lane-ref") {
        let sha = text.trim();
        if !sha.is_empty() {
            return json!({ "sha": sha, "dirty": false, "source": "lane-snapshot" });
        }
    }

    // `unknown` rather than an omitted field: a missing key reads as an old
    // schema, which is exactly the ambiguity this exists to remove.
    json!({ "sha": "unknown", "dirty": JsonValue::Null, "source": "none" })
}
