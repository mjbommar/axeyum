//! Encode, search, and independently replay bounded-rank full polynomial multiplication over GF(2).

use std::path::PathBuf;
use std::time::{Duration, Instant};
use std::{fs::File, io::BufReader};

use axeyum_cas::gf2_tensor::{Gf2Tensor, Gf2TensorDecomposition};
use axeyum_cnf::{
    CnfAssignment, ProofSolveOutcome, check_drat_backward, check_drat_backward_reader,
};
use axeyum_search::harness::parse_sat_competition_model;
use axeyum_search::tensor_decomposition::{
    TensorRankEncodingLimits, encode_full_polynomial_rank_with_group_minimal_first,
    encode_tensor_rank, encode_tensor_rank_with_ordered_terms,
};

struct Arguments {
    terms: usize,
    rank: usize,
    seconds: u64,
    dimacs: Option<PathBuf>,
    pinned_witness: Option<PathBuf>,
    model: Option<PathBuf>,
    output_witness: Option<PathBuf>,
    drat: Option<PathBuf>,
    ordered_terms: bool,
    polynomial_group_min_first: bool,
}

fn arguments() -> Arguments {
    let args: Vec<String> = std::env::args().skip(1).collect();
    assert!(
        args.len() >= 2,
        "usage: synthesize_gf2_polynomial_tensor TERMS RANK [SECONDS] [--ordered-terms | --polynomial-group-min-first] [--dimacs PATH] [--witness PATH] [--check-model PATH --output-witness PATH] [--check-drat PATH]"
    );
    let parse = |index: usize, name: &str| {
        args[index]
            .parse::<usize>()
            .unwrap_or_else(|_| panic!("{name} must be a nonnegative integer"))
    };
    let terms = parse(0, "TERMS");
    let rank = parse(1, "RANK");
    let mut seconds = 30_u64;
    let mut index = 2;
    if let Some(value) = args.get(index).and_then(|text| text.parse::<u64>().ok()) {
        seconds = value;
        index += 1;
    }
    let mut dimacs = None;
    let mut pinned_witness = None;
    let mut model = None;
    let mut output_witness = None;
    let mut drat = None;
    let mut ordered_terms = false;
    let mut polynomial_group_min_first = false;
    while index < args.len() {
        if args[index] == "--ordered-terms" {
            ordered_terms = true;
            index += 1;
            continue;
        }
        if args[index] == "--polynomial-group-min-first" {
            polynomial_group_min_first = true;
            index += 1;
            continue;
        }
        let destination = match args[index].as_str() {
            "--dimacs" => &mut dimacs,
            "--witness" => &mut pinned_witness,
            "--check-model" => &mut model,
            "--output-witness" => &mut output_witness,
            "--check-drat" => &mut drat,
            other => panic!("unknown argument: {other}"),
        };
        *destination = Some(PathBuf::from(
            args.get(index + 1).expect("option needs a path"),
        ));
        index += 2;
    }
    assert_eq!(
        model.is_some(),
        output_witness.is_some(),
        "--check-model and --output-witness must be supplied together"
    );
    let terminal_modes =
        usize::from(dimacs.is_some()) + usize::from(model.is_some()) + usize::from(drat.is_some());
    assert!(terminal_modes <= 1, "choose at most one terminal file mode");
    assert!(
        !(ordered_terms && polynomial_group_min_first),
        "choose at most one symmetry mode"
    );
    Arguments {
        terms,
        rank,
        seconds,
        dimacs,
        pinned_witness,
        model,
        output_witness,
        drat,
        ordered_terms,
        polynomial_group_min_first,
    }
}

fn write_witness(path: &PathBuf, witness: &Gf2TensorDecomposition) {
    let mut bytes = serde_json::to_vec_pretty(witness).expect("serialize witness JSON");
    bytes.push(b'\n');
    std::fs::write(path, bytes).expect("write witness JSON");
}

fn main() {
    let args = arguments();
    let target =
        Gf2Tensor::full_polynomial_multiplication(args.terms).expect("valid polynomial term count");
    let encoding = if args.polynomial_group_min_first {
        encode_full_polynomial_rank_with_group_minimal_first(
            args.terms,
            args.rank,
            TensorRankEncodingLimits::default(),
        )
    } else if args.ordered_terms {
        encode_tensor_rank_with_ordered_terms(
            &target,
            args.rank,
            TensorRankEncodingLimits::default(),
        )
    } else {
        encode_tensor_rank(&target, args.rank, TensorRankEncodingLimits::default())
    }
    .expect("encoding must fit explicit defaults");
    println!("schema=axeyum.gf2-tensor-rank-run.v1");
    println!("full-polynomial-terms={}", args.terms);
    println!("tensor-dimensions={:?}", target.dimensions);
    println!("rank-budget={}", args.rank);
    println!("ordered-terms={}", args.ordered_terms);
    println!(
        "polynomial-group-min-first={}",
        args.polynomial_group_min_first
    );
    println!("variables={}", encoding.formula().variable_count());
    println!("clauses={}", encoding.formula().clauses().len());

    let formula = if let Some(path) = &args.pinned_witness {
        let witness: Gf2TensorDecomposition =
            serde_json::from_slice(&std::fs::read(path).expect("read witness JSON"))
                .expect("parse witness JSON");
        let pinned = encoding
            .formula_with_witness(&witness)
            .expect("witness must replay and fit budget");
        println!("witness={}", path.display());
        println!("witness-rank={}", witness.terms.len());
        pinned
    } else {
        encoding.formula().clone()
    };

    if let Some(path) = args.dimacs {
        std::fs::write(&path, formula.to_dimacs()).expect("write DIMACS");
        println!("dimacs={}", path.display());
        println!("verdict=encoded");
        return;
    }
    if let Some(path) = args.model {
        let output = std::fs::read_to_string(&path).expect("read SAT Competition output");
        let values = parse_sat_competition_model(&output, formula.variable_count())
            .expect("strict SAT model import");
        let witness = encoding
            .lift_model(&CnfAssignment::new(values))
            .expect("model must satisfy CNF, lift, and independently replay");
        let output_path = args.output_witness.expect("paired output path");
        write_witness(&output_path, &witness);
        println!("model={}", path.display());
        println!("output-witness={}", output_path.display());
        println!("lifted-rank={}", witness.terms.len());
        println!("verdict=sat-replayed");
        return;
    }
    if let Some(path) = args.drat {
        let proof_bytes = std::fs::metadata(&path).expect("stat textual DRAT").len();
        let reader = BufReader::new(File::open(&path).expect("open textual DRAT"));
        assert_eq!(check_drat_backward_reader(&formula, reader), Ok(true));
        println!("drat={}", path.display());
        println!("drat-bytes={proof_bytes}");
        println!("verdict=unsat-checked");
        return;
    }

    let started = Instant::now();
    let outcome = axeyum_cnf::solve_with_drat_proof_with_limits(
        &formula,
        Some(started + Duration::from_secs(args.seconds)),
        100_000_000,
    );
    println!("elapsed-ms={}", started.elapsed().as_millis());
    match outcome {
        ProofSolveOutcome::Sat(model) => {
            let witness = encoding
                .lift_model(&model)
                .expect("SAT model must lift and independently replay");
            println!("lifted-rank={}", witness.terms.len());
            println!("verdict=sat-replayed");
        }
        ProofSolveOutcome::Unsat(proof) => {
            assert_eq!(check_drat_backward(&formula, &proof), Ok(true));
            println!("drat-steps={}", proof.len());
            println!("verdict=unsat-checked");
        }
        ProofSolveOutcome::ResourceOut => println!("verdict=resource-out"),
        ProofSolveOutcome::Interrupted => println!("verdict=interrupted"),
    }
}
