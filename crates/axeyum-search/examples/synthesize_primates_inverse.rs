//! Run the generic multiplicative-complexity encoder on PRIMATEs inverse.

use std::time::{Duration, Instant};

use axeyum_search::multiplicative_circuit::{
    MultiplicativeSynthesisLimits, MultiplicativeSynthesisOutcome, MultiplicativeSynthesisProblem,
    encode_multiplicative_circuit, synthesize_multiplicative_circuit,
};

const TABLE: [u64; 32] = [
    1, 0, 14, 19, 10, 9, 18, 21, 17, 25, 27, 30, 29, 20, 12, 16, 23, 4, 13, 31, 8, 6, 28, 11, 22,
    2, 3, 7, 15, 5, 24, 26,
];

fn main() {
    let budget = std::env::args()
        .nth(1)
        .and_then(|text| text.parse::<usize>().ok())
        .unwrap_or(8);
    let seconds = std::env::args()
        .nth(2)
        .and_then(|text| text.parse::<u64>().ok())
        .unwrap_or(30);
    let problem = MultiplicativeSynthesisProblem {
        input_bits: 5,
        output_bits: 5,
        truth_table: TABLE.to_vec(),
        and_gates: budget,
    };
    let limits = MultiplicativeSynthesisLimits {
        max_conflicts: 10_000_000,
        ..MultiplicativeSynthesisLimits::default()
    };
    let encoding = encode_multiplicative_circuit(&problem, limits).expect("encoding must fit");
    println!("schema=axeyum.mc-synthesis-run.v1");
    println!("problem=primates-inverse");
    println!("and-budget={budget}");
    println!("variables={}", encoding.formula().variable_count());
    println!("clauses={}", encoding.formula().clauses().len());
    let started = Instant::now();
    let outcome = synthesize_multiplicative_circuit(
        &problem,
        limits,
        Some(started + Duration::from_secs(seconds)),
    )
    .expect("checked synthesis handoff");
    println!("elapsed-ms={}", started.elapsed().as_millis());
    match outcome {
        MultiplicativeSynthesisOutcome::Sat(artifact) => {
            let ands = artifact
                .gates
                .iter()
                .filter(|gate| gate.op == axeyum_cas::boolean_circuit::BooleanGateOp::And)
                .count();
            println!("verdict=sat-replayed");
            println!("lifted-and-gates={ands}");
        }
        MultiplicativeSynthesisOutcome::Unsat { proof, .. } => {
            println!("verdict=unsat-checked");
            println!("drat-steps={}", proof.len());
        }
        MultiplicativeSynthesisOutcome::ResourceOut => println!("verdict=resource-out"),
        MultiplicativeSynthesisOutcome::Interrupted => println!("verdict=interrupted"),
    }
}
