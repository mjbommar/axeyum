//! ADR-0335 authenticated Tock integer-log proof and replay scoreboard.

use std::env;
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use axeyum_ir::{Assignment, Sort, SymbolId, TermArena, TermId, Value, eval};
use axeyum_solver::{BitLoweringMode, Evidence, EvidenceReport, ProofOutcome, SolverConfig, prove};
use axeyum_verify::reflect::llvm::checked::{DefinedValue, reflect_scalar_into_checked};
use sha2::{Digest, Sha256};

const CANONICAL_32: &str = "log_base_two.ll";
const CANONICAL_64: &str = "log_base_two_u64.ll";
const CANONICAL_32_BYTES: usize = 331;
const CANONICAL_64_BYTES: usize = 374;
const CANONICAL_32_SHA256: &str =
    "5063d99b01d07bf04ab25567ba1be2fe563983d3d4344e2265b66b6a70e4d51c";
const CANONICAL_64_SHA256: &str =
    "f8e23452acf6d8112d653e9d0d8cd56b7f9972129646d0bc5bb373311206a4e3";

const TIMEOUT_SECS: u64 = 30;
const RESOURCE_LIMIT: u64 = 5_000_000;
const MEMORY_LIMIT_MB: u64 = 2_048;
const NODE_BUDGET: u64 = 250_000;
const CNF_VARIABLE_BUDGET: u64 = 1_000_000;
const CNF_CLAUSE_BUDGET: u64 = 5_000_000;

#[derive(Clone, Copy)]
struct Target {
    name: &'static str,
    width: u32,
    file: &'static str,
    bytes: usize,
    sha256: &'static str,
}

const TARGETS: [Target; 2] = [
    Target {
        name: "log_base_two",
        width: 32,
        file: CANONICAL_32,
        bytes: CANONICAL_32_BYTES,
        sha256: CANONICAL_32_SHA256,
    },
    Target {
        name: "log_base_two_u64",
        width: 64,
        file: CANONICAL_64,
        bytes: CANONICAL_64_BYTES,
        sha256: CANONICAL_64_SHA256,
    },
];

fn solver_config() -> SolverConfig {
    SolverConfig::default()
        .with_timeout(Duration::from_secs(TIMEOUT_SECS))
        .with_resource_limit(RESOURCE_LIMIT)
        .with_memory_limit_mb(MEMORY_LIMIT_MB)
        .with_node_budget(NODE_BUDGET)
        .with_cnf_variable_budget(CNF_VARIABLE_BUDGET)
        .with_cnf_clause_budget(CNF_CLAUSE_BUDGET)
        .with_prove_unsat(true)
        .with_preprocess(false)
        .with_cnf_inprocessing(false)
        .with_cnf_vivify(false)
        .with_xor_cdcl_fallback(false)
        .with_lazy_bv(false)
        .with_lazy_bv_abstract_ite(false)
        .with_native_cdcl(false)
        .with_bit_lowering_mode(BitLoweringMode::Eager)
}

fn sha256(bytes: &[u8]) -> String {
    let mut output = String::with_capacity(64);
    for byte in Sha256::digest(bytes) {
        write!(&mut output, "{byte:02x}").unwrap();
    }
    output
}

fn load_target(root: &Path, target: Target) -> String {
    let path = root.join(target.file);
    let bytes = fs::read(&path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
    assert_eq!(bytes.len(), target.bytes, "{} byte count", target.name);
    assert_eq!(sha256(&bytes), target.sha256, "{} SHA-256", target.name);
    String::from_utf8(bytes).unwrap_or_else(|error| panic!("{} UTF-8: {error}", target.name))
}

fn bv_const(arena: &mut TermArena, width: u32, value: u128) -> TermId {
    arena.bv_const(width, value).unwrap()
}

/// Independent threshold partition for floor(log2(x)), with `0 -> 0`.
fn floor_log2_spec(
    arena: &mut TermArena,
    input: TermId,
    width: u32,
    corrupt_top_partition: bool,
) -> TermId {
    let mut result = bv_const(arena, 32, 0);
    for bit in 0..width {
        let threshold_value = 1_u128 << bit;
        let threshold = bv_const(arena, width, threshold_value);
        let at_least = arena.bv_uge(input, threshold).unwrap();
        let encoded = if corrupt_top_partition && bit == width - 1 {
            1
        } else {
            u128::from(bit)
        };
        let encoded = bv_const(arena, 32, encoded);
        result = arena.ite(at_least, encoded, result).unwrap();
    }
    result
}

fn msb_characterization(
    arena: &mut TermArena,
    input: TermId,
    result: TermId,
    width: u32,
) -> TermId {
    let zero = bv_const(arena, width, 0);
    let is_zero = arena.eq(input, zero).unwrap();
    let mut valid = arena.bool_const(false);
    for bit in 0..width {
        let encoded = bv_const(arena, 32, u128::from(bit));
        let selected = arena.eq(result, encoded).unwrap();
        let extracted = arena.extract(bit, bit, input).unwrap();
        let one = bv_const(arena, 1, 1);
        let selected_bit_is_one = arena.eq(extracted, one).unwrap();
        let higher_bits_are_zero = if bit + 1 == width {
            arena.bool_const(true)
        } else {
            let higher = arena.extract(width - 1, bit + 1, input).unwrap();
            let higher_zero = bv_const(arena, width - bit - 1, 0);
            arena.eq(higher, higher_zero).unwrap()
        };
        let case = arena.and(selected, selected_bit_is_one).unwrap();
        let case = arena.and(case, higher_bits_are_zero).unwrap();
        valid = arena.or(valid, case).unwrap();
    }
    arena.or(is_zero, valid).unwrap()
}

fn native_tock_oracle(width: u32, input: u128) -> u128 {
    if input == 0 {
        return 0;
    }
    match width {
        32 => u128::from(u32::try_from(input).unwrap().ilog2()),
        64 => u128::from(u64::try_from(input).unwrap().ilog2()),
        other => panic!("unsupported native oracle width {other}"),
    }
}

fn assignment(symbol: SymbolId, width: u32, input: u128) -> Assignment {
    let mut assignment = Assignment::new();
    assignment.set(
        symbol,
        Value::Bv {
            width,
            value: input,
        },
    );
    assignment
}

fn eval_bv(arena: &TermArena, term: TermId, symbol: SymbolId, width: u32, input: u128) -> u128 {
    match eval(arena, term, &assignment(symbol, width, input)).unwrap() {
        Value::Bv { value, .. } => value,
        other => panic!("expected BV replay value, got {other:?}"),
    }
}

fn eval_bool(arena: &TermArena, term: TermId, symbol: SymbolId, width: u32, input: u128) -> bool {
    match eval(arena, term, &assignment(symbol, width, input)).unwrap() {
        Value::Bool(value) => value,
        other => panic!("expected Boolean replay value, got {other:?}"),
    }
}

fn evidence_family(report: &EvidenceReport) -> &'static str {
    match &report.evidence {
        Evidence::UnsatAletheProof(_) => "alethe_bitblast_resolution",
        Evidence::Unsat(Some(_)) => "drat",
        other => panic!("proof lacks an accepted checked evidence family: {other:?}"),
    }
}

fn check_provenance(report: &EvidenceReport) {
    let provenance = &report.provenance;
    assert_eq!(provenance.timeout, Some(Duration::from_secs(TIMEOUT_SECS)));
    assert_eq!(provenance.resource_limit, Some(RESOURCE_LIMIT));
    assert_eq!(provenance.node_budget, Some(NODE_BUDGET));
    assert_eq!(provenance.cnf_variable_budget, Some(CNF_VARIABLE_BUDGET));
    assert_eq!(provenance.cnf_clause_budget, Some(CNF_CLAUSE_BUDGET));
    assert!(provenance.prove_unsat, "DRAT re-check must be enabled");
    assert!(
        !report.trusted_steps.is_empty(),
        "wide target proof must report its trust steps"
    );
    assert!(
        report.trusted_steps.iter().all(|step| step.certified),
        "every target proof trust step must be certified: {:?}",
        report.trusted_steps
    );
}

fn prove_row(arena: &mut TermArena, target: Target, property: &str, goal: TermId) -> u128 {
    let started = Instant::now();
    let outcome = prove(arena, &[], goal, &solver_config()).unwrap();
    let wall_us = started.elapsed().as_micros();
    let ProofOutcome::Proved(report) = outcome else {
        panic!(
            "{} {property} expected Proved, got {outcome:?}",
            target.name
        );
    };
    check_provenance(&report);
    let evidence = evidence_family(&report);
    let trust = report
        .trusted_steps
        .iter()
        .map(|step| format!("{}:certified", step.id.label()))
        .collect::<Vec<_>>()
        .join(",");
    println!(
        "TOCK_PROOF|target={}|width={}|property={property}|outcome=proved|evidence={evidence}|backend={}|trust={trust}|terms={}|wall_us={wall_us}",
        target.name,
        target.width,
        report.provenance.backend,
        arena.len(),
    );
    wall_us
}

fn model_input(model: &axeyum_solver::Model, symbol: SymbolId, width: u32) -> u128 {
    match model.get(symbol) {
        Some(Value::Bv {
            width: actual,
            value,
        }) => {
            assert_eq!(actual, width, "countermodel input width");
            value
        }
        other => panic!("countermodel has no width-{width} input: {other:?}"),
    }
}

#[derive(Clone, Copy)]
struct ControlTerms {
    correct: DefinedValue,
    mutated: TermId,
    mutated_defined: Option<TermId>,
}

fn control_row(
    arena: &mut TermArena,
    symbol: SymbolId,
    target: Target,
    mutation: &str,
    terms: ControlTerms,
) -> u128 {
    let equal = arena.eq(terms.correct.value, terms.mutated).unwrap();
    let hypotheses = if let Some(mutated_defined) = terms.mutated_defined {
        vec![terms.correct.defined, mutated_defined]
    } else {
        vec![terms.correct.defined]
    };
    let started = Instant::now();
    let outcome = prove(arena, &hypotheses, equal, &solver_config()).unwrap();
    let wall_us = started.elapsed().as_micros();
    let ProofOutcome::Disproved(model) = outcome else {
        panic!(
            "{} {mutation} expected Disproved, got {outcome:?}",
            target.name
        );
    };
    let input = model_input(&model, symbol, target.width);
    assert!(eval_bool(
        arena,
        terms.correct.defined,
        symbol,
        target.width,
        input
    ));
    if let Some(mutated_defined) = terms.mutated_defined {
        assert!(eval_bool(
            arena,
            mutated_defined,
            symbol,
            target.width,
            input
        ));
    }
    let reflected = eval_bv(arena, terms.correct.value, symbol, target.width, input);
    let mutated = eval_bv(arena, terms.mutated, symbol, target.width, input);
    let native = native_tock_oracle(target.width, input);
    assert_eq!(reflected, native, "correct reflection/native disagreement");
    assert_ne!(mutated, native, "mutation did not discriminate at witness");
    println!(
        "TOCK_CONTROL|target={}|width={}|mutation={mutation}|outcome=disproved|witness={input}|reflected={reflected}|native={native}|mutated={mutated}|replay=pass|wall_us={wall_us}",
        target.name, target.width,
    );
    wall_us
}

fn reflected_terms(source: &str, width: u32) -> (TermArena, SymbolId, TermId, DefinedValue) {
    let mut arena = TermArena::new();
    let symbol = arena.declare("tock_input", Sort::BitVec(width)).unwrap();
    let input = arena.var(symbol);
    let reflected = reflect_scalar_into_checked(&mut arena, &[input], source).unwrap();
    assert_eq!(reflected.width, 32);
    (arena, symbol, input, reflected)
}

fn textual_mutation(source: &str, target: Target, mutation: &str) -> String {
    let (needle, replacement) = match (target.width, mutation) {
        (32, "wrong_index") => ("xor i32 %\"0\", 31", "xor i32 %\"0\", 30"),
        (64, "wrong_index") => ("xor i32 %\"1\", 63", "xor i32 %\"1\", 62"),
        (_, "inverted_zero") => (
            "select i1 %\".not.i.not\", i32 0, i32 %\"_5.i\"",
            "select i1 %\".not.i.not\", i32 %\"_5.i\", i32 0",
        ),
        _ => panic!("unsupported textual mutation {mutation}"),
    };
    assert_eq!(source.matches(needle).count(), 1, "mutation source shape");
    source.replacen(needle, replacement, 1)
}

fn prove_target(target: Target, source: &str) -> (usize, usize, u128) {
    let mut proof_rows = 0;
    let mut control_rows = 0;
    let mut query_wall_us = 0;

    let (mut arena, _symbol, input, reflected) = reflected_terms(source, target.width);
    query_wall_us += prove_row(&mut arena, target, "defined", reflected.defined);
    proof_rows += 1;

    let zero = bv_const(&mut arena, target.width, 0);
    let is_zero = arena.eq(input, zero).unwrap();
    let zero_result = bv_const(&mut arena, 32, 0);
    let result_is_zero = arena.eq(reflected.value, zero_result).unwrap();
    let zero_property = arena.implies(is_zero, result_is_zero).unwrap();
    let zero_goal = arena.and(reflected.defined, zero_property).unwrap();
    query_wall_us += prove_row(&mut arena, target, "zero", zero_goal);
    proof_rows += 1;

    let expected = floor_log2_spec(&mut arena, input, target.width, false);
    let equal = arena.eq(reflected.value, expected).unwrap();
    let equivalence = arena.and(reflected.defined, equal).unwrap();
    query_wall_us += prove_row(&mut arena, target, "floor_log2", equivalence);
    proof_rows += 1;

    let msb = msb_characterization(&mut arena, input, reflected.value, target.width);
    let msb_goal = arena.and(reflected.defined, msb).unwrap();
    query_wall_us += prove_row(&mut arena, target, "msb", msb_goal);
    proof_rows += 1;

    for mutation in ["wrong_index", "inverted_zero"] {
        let mutated_source = textual_mutation(source, target, mutation);
        let (mut arena, symbol, input, correct) = reflected_terms(source, target.width);
        let mutated = reflect_scalar_into_checked(&mut arena, &[input], &mutated_source).unwrap();
        query_wall_us += control_row(
            &mut arena,
            symbol,
            target,
            mutation,
            ControlTerms {
                correct,
                mutated: mutated.value,
                mutated_defined: Some(mutated.defined),
            },
        );
        control_rows += 1;
    }

    let (mut arena, symbol, input, correct) = reflected_terms(source, target.width);
    let corrupted = floor_log2_spec(&mut arena, input, target.width, true);
    query_wall_us += control_row(
        &mut arena,
        symbol,
        target,
        "high_partition",
        ControlTerms {
            correct,
            mutated: corrupted,
            mutated_defined: None,
        },
    );
    control_rows += 1;

    (proof_rows, control_rows, query_wall_us)
}

#[test]
fn independent_floor_log_spec_matches_native_small_rows() {
    for width in [32, 64] {
        let mut arena = TermArena::new();
        let symbol = arena.declare("x", Sort::BitVec(width)).unwrap();
        let input = arena.var(symbol);
        let spec = floor_log2_spec(&mut arena, input, width, false);
        for value in [0, 1, 2, 3, 4, 7, 8, 15, 16, 31, 32] {
            assert_eq!(
                eval_bv(&arena, spec, symbol, width, value),
                native_tock_oracle(width, value)
            );
        }
    }
}

#[test]
#[ignore = "requires ADR-0334 authenticated local Tock canonical LLVM"]
fn authenticated_tock_log2_scoreboard() {
    let root = PathBuf::from(
        env::var_os("AXEYUM_TOCK_CANONICAL_DIR")
            .expect("AXEYUM_TOCK_CANONICAL_DIR must name authenticated canonicals"),
    );
    assert!(root.is_absolute(), "canonical directory must be absolute");
    let started = Instant::now();
    let mut proofs = 0;
    let mut controls = 0;
    let mut query_wall_us = 0;
    for target in TARGETS {
        let source = load_target(&root, target);
        let (target_proofs, target_controls, target_wall_us) = prove_target(target, &source);
        proofs += target_proofs;
        controls += target_controls;
        query_wall_us += target_wall_us;
    }
    assert_eq!(proofs, 8);
    assert_eq!(controls, 6);
    println!(
        "TOCK_SCOREBOARD|functions=2|proved={proofs}|refuted_replayed={controls}|unknown=0|disagree=0|query_wall_us={query_wall_us}|runner_wall_us={}",
        started.elapsed().as_micros(),
    );
}
