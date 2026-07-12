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

use std::collections::BTreeSet;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use axeyum_cnf::check_alethe;
use axeyum_ir::{TermArena, TermId, TermNode, render};
use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CheckResult, DeclineReason, Evidence, RouteOutcome, RouteTrace, SolverConfig,
    UnsatProofOutcome, check_auto_explained, export_qf_aufbv_unsat_proof_within, produce_evidence,
    prove_qf_abv_unsat_alethe, prove_qf_abv_unsat_alethe_via_elimination, solve,
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

fn decline_detail(reason: &DeclineReason) -> Option<&str> {
    match reason {
        DeclineReason::Budget(detail) | DeclineReason::VerifierRejected(detail) => Some(detail),
        DeclineReason::Incomplete(reason) => Some(&reason.detail),
        DeclineReason::Unsupported | DeclineReason::NotApplicable => None,
    }
}

fn extract_named_usize(text: &str, name: &str) -> Option<usize> {
    let needle = format!("{name}=");
    let after = text.split_once(&needle)?.1;
    let digits = after
        .chars()
        .take_while(char::is_ascii_digit)
        .collect::<String>();
    digits.parse().ok()
}

fn find_term_by_index(
    arena: &TermArena,
    roots: &[TermId],
    index: usize,
) -> Option<(TermId, &'static str)> {
    let mut visited = BTreeSet::new();
    let mut stack = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        if term.index() == index {
            return Some((term, "reachable"));
        }
        if let TermNode::App { args, .. } = arena.node(term) {
            stack.extend(args.iter().copied());
        }
    }
    arena.term_by_index(index).map(|term| (term, "arena"))
}

fn node_label(node: &TermNode) -> String {
    match node {
        TermNode::BoolConst(value) => format!("BoolConst({value})"),
        TermNode::BvConst { width, value } => format!("BvConst(width={width}, value={value})"),
        TermNode::WideBvConst(value) => format!("WideBvConst(width={})", value.width()),
        TermNode::IntConst(value) => format!("IntConst({value})"),
        TermNode::RealConst(value) => format!("RealConst({value})"),
        TermNode::Symbol(symbol) => format!("Symbol({})", symbol.index()),
        TermNode::App { op, args } => format!("App({op:?}, arity={})", args.len()),
    }
}

fn compact_render(arena: &TermArena, term: TermId) -> String {
    let limit = std::env::var("AXEYUM_DIAGNOSE_RENDER_LIMIT")
        .ok()
        .and_then(|raw| raw.parse::<usize>().ok())
        .unwrap_or(480);
    let rendered = render(arena, term);
    if rendered.chars().count() <= limit {
        rendered
    } else {
        let prefix = rendered.chars().take(limit).collect::<String>();
        format!("{prefix}...")
    }
}

fn print_lazy_replay_terms(arena: &TermArena, assertions: &[TermId], trace: &RouteTrace) {
    let mut emitted = BTreeSet::new();
    for attempt in trace.attempts() {
        let RouteOutcome::Declined(reason) = &attempt.outcome else {
            continue;
        };
        let Some(detail) = decline_detail(reason) else {
            continue;
        };
        if !detail.contains("last_candidate_replay=false(") {
            continue;
        }

        if let (Some(assertion_ordinal), Some(conjunct_ordinal)) = (
            extract_named_usize(detail, "assertion_ordinal"),
            extract_named_usize(detail, "failed_conjunct_ordinal"),
        ) {
            println!(
                "  lazy-ext-replay: route={} assertion_ordinal={} failed_conjunct_ordinal={}",
                attempt.route, assertion_ordinal, conjunct_ordinal
            );
        }

        for (label, key) in [
            ("replay_assertion", "term"),
            ("failed_conjunct", "failed_conjunct_term"),
            ("best_branch", "failed_or_best_branch_term"),
            ("followup_branch", "followup_branch_term"),
            ("followup_next_branch", "followup_next_branch_term"),
            (
                "followup_global_false_branch",
                "followup_global_false_or_best_branch_term",
            ),
            (
                "followup_global_false_branch_first_false",
                "followup_global_false_or_best_branch_first_false_term",
            ),
            (
                "followup_closure_global_false_branch",
                "followup_closure_global_false_or_best_branch_term",
            ),
            (
                "followup_closure_global_false_branch_first_false",
                "followup_closure_global_false_or_best_branch_first_false_term",
            ),
            (
                "followup_next_global_false_branch",
                "followup_next_global_false_or_best_branch_term",
            ),
            (
                "followup_next_global_false_branch_first_false",
                "followup_next_global_false_or_best_branch_first_false_term",
            ),
            (
                "followup_next_closure_global_false_branch",
                "followup_next_closure_global_false_or_best_branch_term",
            ),
            (
                "followup_next_closure_global_false_branch_first_false",
                "followup_next_closure_global_false_or_best_branch_first_false_term",
            ),
            (
                "returned_or_stabilization_branch",
                "returned_or_stabilization_branch_term",
            ),
            (
                "returned_or_stabilization_false_literal",
                "returned_or_stabilization_false_literal_term",
            ),
            (
                "returned_or_stabilization_global_false_branch",
                "returned_or_stabilization_global_false_or_best_branch_term",
            ),
            (
                "returned_or_stabilization_global_false_branch_first_false",
                "returned_or_stabilization_global_false_or_best_branch_first_false_term",
            ),
            (
                "best_branch_first_false",
                "failed_or_best_branch_first_false_term",
            ),
            (
                "global_false_best_branch",
                "global_false_or_best_branch_term",
            ),
        ] {
            let Some(index) = extract_named_usize(detail, key) else {
                continue;
            };
            if !emitted.insert((label, index)) {
                continue;
            }
            if let Some((term, source)) = find_term_by_index(arena, assertions, index) {
                println!(
                    "  {label}: #{} source={} sort={:?} node={}",
                    term.index(),
                    source,
                    arena.sort_of(term),
                    node_label(arena.node(term))
                );
                println!("    {}", compact_render(arena, term));
            } else {
                println!("  {label}: #{index} not reachable from original assertions");
            }
        }
    }
}

fn requested_term_indices() -> Vec<usize> {
    let Some(raw) = std::env::var_os("AXEYUM_DIAGNOSE_TERMS") else {
        return Vec::new();
    };
    raw.to_string_lossy()
        .split(',')
        .filter_map(|part| part.trim().parse::<usize>().ok())
        .collect()
}

fn print_requested_terms(arena: &TermArena, assertions: &[TermId], indices: &[usize]) {
    let mut emitted = BTreeSet::new();
    for &index in indices {
        if !emitted.insert(index) {
            continue;
        }
        if let Some((term, source)) = find_term_by_index(arena, assertions, index) {
            println!(
                "  requested_term: #{} source={} sort={:?} node={}",
                term.index(),
                source,
                arena.sort_of(term),
                node_label(arena.node(term))
            );
            println!("    {}", compact_render(arena, term));
        } else {
            println!("  requested_term: #{index} not present in arena");
        }
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
    let requested_terms = requested_term_indices();

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
                print_lazy_replay_terms(&script.arena, &assertions, &trace);
                print_requested_terms(&script.arena, &assertions, &requested_terms);
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
