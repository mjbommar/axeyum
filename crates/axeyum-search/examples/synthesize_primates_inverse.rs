//! Run the generic multiplicative-complexity encoder on PRIMATEs inverse.

use std::path::PathBuf;
use std::time::{Duration, Instant};

use axeyum_cnf::{
    ProofSolveOutcome, VivifyOptions, check_drat_backward, parse_drat, vivify_within,
};
use axeyum_search::multiplicative_circuit::{
    MultiplicativeEncodingOptions, MultiplicativeSynthesisLimits, MultiplicativeSynthesisOutcome,
    MultiplicativeSynthesisProblem, encode_multiplicative_anf_system,
    encode_multiplicative_circuit_anf, encode_multiplicative_circuit_with_options,
};

const TABLE: [u64; 32] = [
    1, 0, 14, 19, 10, 9, 18, 21, 17, 25, 27, 30, 29, 20, 12, 16, 23, 4, 13, 31, 8, 6, 28, 11, 22,
    2, 3, 7, 15, 5, 24, 26,
];

struct Arguments {
    budget: usize,
    seconds: u64,
    encoding: String,
    dimacs_path: Option<PathBuf>,
    anf_path: Option<PathBuf>,
    drat_path: Option<PathBuf>,
}

fn arguments() -> Arguments {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let budget = args
        .first()
        .and_then(|text| text.parse::<usize>().ok())
        .unwrap_or(8);
    let seconds = args
        .get(1)
        .and_then(|text| text.parse::<u64>().ok())
        .unwrap_or(30);
    let mut encoding = "anf".to_string();
    let mut dimacs_path: Option<PathBuf> = None;
    let mut anf_path: Option<PathBuf> = None;
    let mut drat_path: Option<PathBuf> = None;
    let mut index = 2;
    while index < args.len() {
        match args[index].as_str() {
            "--encoding" => {
                encoding.clone_from(args.get(index + 1).expect("--encoding needs anf or truth"));
                assert!(matches!(encoding.as_str(), "anf" | "truth"));
                index += 2;
            }
            "--dimacs" => {
                dimacs_path = Some(PathBuf::from(
                    args.get(index + 1).expect("--dimacs needs a path"),
                ));
                index += 2;
            }
            "--anf-file" => {
                anf_path = Some(PathBuf::from(
                    args.get(index + 1).expect("--anf-file needs a path"),
                ));
                index += 2;
            }
            "--check-drat" => {
                drat_path = Some(PathBuf::from(
                    args.get(index + 1).expect("--check-drat needs a path"),
                ));
                index += 2;
            }
            other => panic!("unknown argument: {other}"),
        }
    }
    Arguments {
        budget,
        seconds,
        encoding,
        dimacs_path,
        anf_path,
        drat_path,
    }
}

fn export_anf(
    problem: &MultiplicativeSynthesisProblem,
    limits: MultiplicativeSynthesisLimits,
    options: MultiplicativeEncodingOptions,
    path: &PathBuf,
    budget: usize,
) {
    let encoding =
        encode_multiplicative_anf_system(problem, limits, options).expect("ANF encoding must fit");
    std::fs::write(path, encoding.system().to_bosphorus_anf()).expect("write ANF");
    println!("schema=axeyum.mc-anf-system.v1");
    println!("problem=primates-inverse");
    println!("and-budget={budget}");
    println!("variables={}", encoding.system().variable_count());
    println!("equations={}", encoding.system().equations().len());
    println!(
        "monomials={}",
        encoding
            .system()
            .equations()
            .iter()
            .map(axeyum_cas::boolean_anf::BooleanAnfPolynomial::monomial_count)
            .sum::<usize>()
    );
    println!("anf={}", path.display());
    println!("verdict=encoded");
}

fn main() {
    let args = arguments();
    let budget = args.budget;
    let seconds = args.seconds;
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
    let options = MultiplicativeEncodingOptions {
        eliminate_internal_constants: true,
        partial_operand_order: true,
    };
    if let Some(path) = args.anf_path {
        export_anf(&problem, limits, options, &path, budget);
        return;
    }
    let encoding = match args.encoding.as_str() {
        "anf" => encode_multiplicative_circuit_anf(&problem, limits, options),
        "truth" => encode_multiplicative_circuit_with_options(&problem, limits, options),
        _ => unreachable!("validated above"),
    }
    .expect("encoding must fit");
    println!("schema=axeyum.mc-synthesis-run.v1");
    println!("problem=primates-inverse");
    println!("and-budget={budget}");
    println!("internal-constants=eliminated");
    println!("operand-order=first-coefficient");
    println!("semantics={}", args.encoding);
    println!("variables={}", encoding.formula().variable_count());
    println!("clauses={}", encoding.formula().clauses().len());
    if let Some(path) = args.dimacs_path {
        std::fs::write(&path, encoding.formula().to_dimacs()).expect("write DIMACS");
        println!("dimacs={}", path.display());
        println!("verdict=encoded");
        return;
    }
    if let Some(path) = args.drat_path {
        let text = std::fs::read_to_string(&path).expect("read textual DRAT");
        let proof = parse_drat(&text).expect("parse textual DRAT");
        assert_eq!(check_drat_backward(encoding.formula(), &proof), Ok(true));
        println!("drat={}", path.display());
        println!("drat-steps={}", proof.len());
        println!("verdict=unsat-checked");
        return;
    }
    let started = Instant::now();
    let deadline = started + Duration::from_secs(seconds);
    let vivified = vivify_within(
        encoding.formula(),
        VivifyOptions::default(),
        Some((started + Duration::from_secs(10)).min(deadline)),
    );
    println!("vivified-clauses={}", vivified.formula.clauses().len());
    println!(
        "vivified-literals-removed={}",
        vivified.stats.literals_removed
    );
    let outcome = match axeyum_cnf::solve_with_drat_proof_with_limits(
        &vivified.formula,
        Some(deadline),
        limits.max_conflicts,
    ) {
        ProofSolveOutcome::Sat(model) => MultiplicativeSynthesisOutcome::Sat(
            encoding.lift_model(&model).expect("lift and replay model"),
        ),
        ProofSolveOutcome::Unsat(proof) => {
            let mut combined = vivified.proof;
            combined.extend(proof);
            assert_eq!(check_drat_backward(encoding.formula(), &combined), Ok(true));
            MultiplicativeSynthesisOutcome::Unsat {
                formula: encoding.formula().clone(),
                proof: combined,
            }
        }
        ProofSolveOutcome::ResourceOut => MultiplicativeSynthesisOutcome::ResourceOut,
        ProofSolveOutcome::Interrupted => MultiplicativeSynthesisOutcome::Interrupted,
    };
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
