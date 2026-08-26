//! Replay a circuit through the portable ANF system and its exact CNF lowering.

use std::path::PathBuf;

use axeyum_cas::boolean_circuit::BooleanCircuitArtifact;
use axeyum_cnf::ProofSolveOutcome;
use axeyum_search::boolean_anf_cnf::{BooleanAnfCnfLimits, encode_boolean_anf_cnf};
use axeyum_search::multiplicative_circuit::{
    MultiplicativeEncodingOptions, MultiplicativeSynthesisLimits, MultiplicativeSynthesisProblem,
    encode_multiplicative_anf_system, normalize_multiplicative_witness,
};

fn main() {
    let path = std::env::args_os()
        .nth(1)
        .map(PathBuf::from)
        .expect("usage: replay_multiplicative_anf_cnf_witness ARTIFACT.json");
    let artifact: BooleanCircuitArtifact =
        serde_json::from_slice(&std::fs::read(&path).expect("read circuit artifact"))
            .expect("parse artifact");
    let and_gates = artifact
        .gates
        .iter()
        .filter(|gate| gate.op == axeyum_cas::boolean_circuit::BooleanGateOp::And)
        .count();
    let witness =
        normalize_multiplicative_witness(&artifact, and_gates).expect("normalize witness");
    let problem = MultiplicativeSynthesisProblem {
        input_bits: artifact.inputs.len(),
        output_bits: artifact.outputs.len(),
        truth_table: artifact.truth_table.clone(),
        and_gates,
    };
    let source = encode_multiplicative_anf_system(
        &problem,
        MultiplicativeSynthesisLimits::default(),
        MultiplicativeEncodingOptions {
            eliminate_internal_constants: false,
            partial_operand_order: false,
            lexicographic_operand_order: true,
        },
    )
    .expect("encode portable ANF system");
    let encoding = encode_boolean_anf_cnf(source.system(), BooleanAnfCnfLimits::default())
        .expect("lower ANF system to CNF");
    let units = source
        .source_units_with_witness(&witness)
        .expect("bind witness selectors");
    let pinned = encoding
        .formula_with_source_units(&units)
        .expect("pin source selector units");
    println!("schema=axeyum.mc-anf-cnf-witness-replay.v1");
    println!("and-gates={and_gates}");
    println!("anf-variables={}", source.system().variable_count());
    println!("anf-equations={}", source.system().equations().len());
    println!("selector-units={}", units.len());
    println!("cnf-variables={}", encoding.formula().variable_count());
    println!("cnf-base-clauses={}", encoding.formula().clauses().len());
    println!("cnf-pinned-clauses={}", pinned.clauses().len());
    match axeyum_cnf::solve_with_drat_proof(&pinned) {
        ProofSolveOutcome::Sat(model) => {
            let assignment = encoding
                .lift_source_assignment(source.system(), &model)
                .expect("project and replay source ANF system");
            source
                .lift_assignment(&assignment)
                .expect("lift and replay portable circuit");
            println!("verdict=sat-replayed");
        }
        other => panic!("published witness must inhabit the ANF-to-CNF route: {other:?}"),
    }
}
