//! Encode, search, and independently replay bounded-rank matrix tensors over GF(2).

use std::path::PathBuf;
use std::time::{Duration, Instant};
use std::{fs::File, io::BufReader};

use axeyum_cas::gf2_tensor::{Gf2Tensor, Gf2TensorDecomposition};
use axeyum_cnf::{ProofSolveOutcome, check_drat_backward, check_drat_backward_reader};
use axeyum_search::tensor_decomposition::{
    TensorRankEncodingLimits, encode_matrix_tensor_rank_with_normalized_first_factor,
    encode_tensor_rank, encode_tensor_rank_with_ordered_terms,
};

struct Arguments {
    m: usize,
    n: usize,
    p: usize,
    rank: usize,
    seconds: u64,
    dimacs: Option<PathBuf>,
    witness: Option<PathBuf>,
    drat: Option<PathBuf>,
    ordered_terms: bool,
    normalized_first_factor: bool,
}

fn arguments() -> Arguments {
    let args: Vec<String> = std::env::args().skip(1).collect();
    assert!(
        args.len() >= 4,
        "usage: synthesize_gf2_matrix_tensor M N P RANK [SECONDS] [--ordered-terms | --normalize-first-factor] [--dimacs PATH] [--witness PATH] [--check-drat PATH]"
    );
    let parse = |index: usize, name: &str| {
        args[index]
            .parse::<usize>()
            .unwrap_or_else(|_| panic!("{name} must be a nonnegative integer"))
    };
    let m = parse(0, "M");
    let n = parse(1, "N");
    let p = parse(2, "P");
    let rank = parse(3, "RANK");
    let mut seconds = 30_u64;
    let mut index = 4;
    if let Some(value) = args.get(index).and_then(|text| text.parse::<u64>().ok()) {
        seconds = value;
        index += 1;
    }
    let mut dimacs = None;
    let mut witness = None;
    let mut drat = None;
    let mut ordered_terms = false;
    let mut normalized_first_factor = false;
    while index < args.len() {
        if args[index] == "--ordered-terms" {
            ordered_terms = true;
            index += 1;
            continue;
        }
        if args[index] == "--normalize-first-factor" {
            normalized_first_factor = true;
            index += 1;
            continue;
        }
        let destination = match args[index].as_str() {
            "--dimacs" => &mut dimacs,
            "--witness" => &mut witness,
            "--check-drat" => &mut drat,
            other => panic!("unknown argument: {other}"),
        };
        *destination = Some(PathBuf::from(
            args.get(index + 1).expect("option needs a path"),
        ));
        index += 2;
    }
    Arguments {
        m,
        n,
        p,
        rank,
        seconds,
        dimacs,
        witness,
        drat,
        ordered_terms,
        normalized_first_factor,
    }
}

fn main() {
    let args = arguments();
    let target =
        Gf2Tensor::matrix_multiplication(args.m, args.n, args.p).expect("valid matrix dimensions");
    assert!(
        !(args.ordered_terms && args.normalized_first_factor),
        "choose at most one symmetry mode"
    );
    let encoding = if args.normalized_first_factor {
        encode_matrix_tensor_rank_with_normalized_first_factor(
            args.m,
            args.n,
            args.p,
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
    println!("matrix={}x{}x{}", args.m, args.n, args.p);
    println!("tensor-dimensions={:?}", target.dimensions);
    println!("rank-budget={}", args.rank);
    println!("ordered-terms={}", args.ordered_terms);
    println!("normalized-first-factor={}", args.normalized_first_factor);
    println!("variables={}", encoding.formula().variable_count());
    println!("clauses={}", encoding.formula().clauses().len());

    let formula = if let Some(path) = &args.witness {
        let bytes = std::fs::read(path).expect("read witness JSON");
        let witness: Gf2TensorDecomposition =
            serde_json::from_slice(&bytes).expect("parse witness JSON");
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
            let decomposition = encoding
                .lift_model(&model)
                .expect("SAT model must lift and independently replay");
            println!("lifted-rank={}", decomposition.terms.len());
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
