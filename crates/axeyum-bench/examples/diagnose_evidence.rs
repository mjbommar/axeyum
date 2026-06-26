//! Single-file evidence-production stage timing.
//!
//! This is a diagnostic companion to `audit_dominance`: the audit tells us that a
//! row timed out inside `produce_evidence`; this tool splits that opaque phase
//! into the decision route and the post-decision certificate attempts.
//!
//! Usage:
//! ```text
//! cargo run -p axeyum-bench --example diagnose_evidence -- <file.smt2> [timeout_ms]
//! ```

#![allow(clippy::too_many_lines)]

use std::path::PathBuf;
use std::time::{Duration, Instant};

use axeyum_cnf::check_alethe;
use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CheckResult, Evidence, SolverConfig, UnsatProofOutcome, check_auto_explained,
    export_qf_aufbv_unsat_proof_within, produce_evidence, prove_qf_abv_unsat_alethe,
    prove_qf_abv_unsat_alethe_via_elimination, solve,
};

fn elapsed_ms(start: Instant) -> f64 {
    start.elapsed().as_secs_f64() * 1000.0
}

fn verdict(result: &CheckResult) -> &'static str {
    match result {
        CheckResult::Sat(_) => "sat",
        CheckResult::Unsat => "unsat",
        CheckResult::Unknown(_) => "unknown",
    }
}

fn proof_outcome_label(outcome: &UnsatProofOutcome) -> &'static str {
    match outcome {
        UnsatProofOutcome::Proved(_) => "proved",
        UnsatProofOutcome::Satisfiable => "satisfiable",
        UnsatProofOutcome::Inconclusive => "inconclusive",
    }
}

fn evidence_kind(evidence: &Evidence) -> &'static str {
    match evidence {
        Evidence::Sat(_) => "sat-model",
        Evidence::Unsat(Some(_)) => "drat-unsat",
        Evidence::Unsat(None) => "bare-unsat",
        Evidence::UnsatAletheProof(_) => "alethe-unsat",
        Evidence::UnsatArithAletheProof(_) => "arith-alethe-unsat",
        Evidence::UnsatGuardedQuantAletheProof { .. } => "guarded-quant-alethe-unsat",
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
        Evidence::UnsatArrayAxiom(_) => "array-axiom-unsat",
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
        Evidence::Unknown(_) => "unknown",
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let file = args.get(1).map_or_else(
        || {
            eprintln!("usage: diagnose_evidence <file.smt2> [timeout_ms]");
            std::process::exit(2);
        },
        PathBuf::from,
    );
    let timeout_ms = args
        .get(2)
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(10_000);
    let config = SolverConfig::default().with_timeout(Duration::from_millis(timeout_ms));

    let text = std::fs::read_to_string(&file).expect("read SMT-LIB file");
    println!("file: {}", file.display());
    println!("timeout_ms: {timeout_ms}");

    if std::env::var_os("AXEYUM_DIAGNOSE_ONLY_EVIDENCE").is_none() {
        let mut script = parse_script(&text).expect("parse SMT-LIB file");
        let assertions = script.assertions.clone();
        let start = Instant::now();
        match check_auto_explained(&mut script.arena, &assertions, &config) {
            Ok((result, trace)) => {
                println!(
                    "check_auto_explained: {} {:.3}ms",
                    verdict(&result),
                    elapsed_ms(start)
                );
                for attempt in trace.attempts() {
                    println!("  {attempt}");
                }
            }
            Err(error) => println!(
                "check_auto_explained: error {error} {:.3}ms",
                elapsed_ms(start)
            ),
        }

        let mut script = parse_script(&text).expect("parse SMT-LIB file");
        let assertions = script.assertions.clone();
        let start = Instant::now();
        match solve(&mut script.arena, &assertions, &config) {
            Ok(result) => println!("solve: {} {:.3}ms", verdict(&result), elapsed_ms(start)),
            Err(error) => println!("solve: error {error} {:.3}ms", elapsed_ms(start)),
        }

        let script = parse_script(&text).expect("parse SMT-LIB file");
        let assertions = script.assertions.clone();
        let start = Instant::now();
        match prove_qf_abv_unsat_alethe(&script.arena, &assertions) {
            Some(proof) => println!(
                "abv-direct-alethe: some steps={} checked={} {:.3}ms",
                proof.len(),
                matches!(check_alethe(&proof), Ok(true)),
                elapsed_ms(start)
            ),
            None => println!("abv-direct-alethe: none {:.3}ms", elapsed_ms(start)),
        }

        let mut script = parse_script(&text).expect("parse SMT-LIB file");
        let assertions = script.assertions.clone();
        let start = Instant::now();
        match prove_qf_abv_unsat_alethe_via_elimination(&mut script.arena, &assertions) {
            Some(proof) => println!(
                "abv-elim-alethe: some steps={} checked={} {:.3}ms",
                proof.len(),
                matches!(check_alethe(&proof), Ok(true)),
                elapsed_ms(start)
            ),
            None => println!("abv-elim-alethe: none {:.3}ms", elapsed_ms(start)),
        }

        if std::env::var_os("AXEYUM_DIAGNOSE_EXPENSIVE_EXPORT").is_some() {
            let mut script = parse_script(&text).expect("parse SMT-LIB file");
            let assertions = script.assertions.clone();
            let start = Instant::now();
            let deadline = Instant::now().checked_add(Duration::from_millis(timeout_ms));
            match export_qf_aufbv_unsat_proof_within(&mut script.arena, &assertions, deadline) {
                Ok(outcome) => println!(
                    "aufbv-reduction-proof: {} {:.3}ms",
                    proof_outcome_label(&outcome),
                    elapsed_ms(start)
                ),
                Err(error) => {
                    println!(
                        "aufbv-reduction-proof: error {error} {:.3}ms",
                        elapsed_ms(start)
                    );
                }
            }
        } else {
            println!("aufbv-reduction-proof: skipped (set AXEYUM_DIAGNOSE_EXPENSIVE_EXPORT=1)");
        }
    } else {
        println!("diagnostic prepasses: skipped (AXEYUM_DIAGNOSE_ONLY_EVIDENCE=1)");
    }

    let mut script = parse_script(&text).expect("parse SMT-LIB file");
    let assertions = script.assertions.clone();
    let start = Instant::now();
    match produce_evidence(&mut script.arena, &assertions, &config) {
        Ok(report) => println!(
            "produce_evidence: {} certified={} checked={} trust_steps=[{}] {:.3}ms",
            evidence_kind(&report.evidence),
            report.evidence.is_certified(),
            report
                .evidence
                .check(&script.arena, &assertions)
                .unwrap_or(false),
            report
                .trusted_steps
                .iter()
                .map(|step| format!("{}:{}", step.id.label(), step.certified))
                .collect::<Vec<_>>()
                .join(","),
            elapsed_ms(start)
        ),
        Err(error) => println!("produce_evidence: error {error} {:.3}ms", elapsed_ms(start)),
    }
}
