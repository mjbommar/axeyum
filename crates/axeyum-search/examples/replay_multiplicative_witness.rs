//! Bind a portable Boolean circuit to the generic synthesis CNF and replay it.

use std::path::PathBuf;

use axeyum_cas::boolean_circuit::BooleanCircuitArtifact;
use axeyum_cnf::ProofSolveOutcome;
use axeyum_search::multiplicative_circuit::{
    MultiplicativeSynthesisLimits, MultiplicativeSynthesisProblem, encode_multiplicative_circuit,
    normalize_multiplicative_witness,
};

fn main() {
    let path = std::env::args_os()
        .nth(1)
        .map(PathBuf::from)
        .expect("usage: replay_multiplicative_witness ARTIFACT.json");
    let bytes = std::fs::read(&path).expect("read circuit artifact");
    let artifact: BooleanCircuitArtifact = serde_json::from_slice(&bytes).expect("parse artifact");
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
    let encoding =
        encode_multiplicative_circuit(&problem, MultiplicativeSynthesisLimits::default())
            .expect("encode synthesis problem");
    let pinned = encoding
        .formula_with_witness(&witness)
        .expect("pin witness selectors");
    println!("schema=axeyum.mc-witness-replay.v1");
    println!("and-gates={and_gates}");
    println!("variables={}", encoding.formula().variable_count());
    println!("base-clauses={}", encoding.formula().clauses().len());
    println!("pinned-clauses={}", pinned.clauses().len());
    match axeyum_cnf::solve_with_drat_proof(&pinned) {
        ProofSolveOutcome::Sat(model) => {
            encoding.lift_model(&model).expect("lift and replay model");
            println!("verdict=sat-replayed");
        }
        other => panic!("published witness must satisfy the synthesis CNF: {other:?}"),
    }
}
