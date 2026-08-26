//! Synthesize and certify weighted-cost unary AVX2 byte permutations.

use std::fs::File;
use std::io::BufReader;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use axeyum_cnf::{ProofSolveOutcome, check_drat_backward, check_drat_backward_reader};
use axeyum_search::simd::ByteTags;
use axeyum_search::simd_synthesis::{
    UnaryAvx2InstructionCosts, UnaryAvx2SynthesisLimits, encode_weighted_unary_avx2_sequence,
};

struct Arguments {
    bound: u64,
    seconds: u64,
    dimacs: Option<PathBuf>,
    drat: Option<PathBuf>,
}

fn arguments() -> Arguments {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let bound = args
        .first()
        .expect("usage: synthesize_weighted_unary_avx2 BOUND [SECONDS] [--dimacs PATH] [--check-drat PATH]")
        .parse::<u64>()
        .expect("BOUND must be a nonnegative integer");
    let mut seconds = 30_u64;
    let mut index = 1;
    if let Some(value) = args.get(index).and_then(|text| text.parse::<u64>().ok()) {
        seconds = value;
        index += 1;
    }
    let mut dimacs = None;
    let mut drat = None;
    while index < args.len() {
        let destination = match args[index].as_str() {
            "--dimacs" => &mut dimacs,
            "--check-drat" => &mut drat,
            other => panic!("unknown argument: {other}"),
        };
        *destination = Some(PathBuf::from(
            args.get(index + 1).expect("option needs a path"),
        ));
        index += 2;
    }
    Arguments {
        bound,
        seconds,
        dimacs,
        drat,
    }
}

fn main() {
    let args = arguments();
    // Register-to-register dependent latency on Intel Haswell, in cycles.
    let costs = UnaryAvx2InstructionCosts {
        pshufb: 1,
        permute_dwords: 3,
        permute_qwords: 3,
        align_right: 1,
        permute_2x128: 3,
    };
    let encoding = encode_weighted_unary_avx2_sequence(
        &ByteTags::reversed(),
        costs,
        args.bound,
        UnaryAvx2SynthesisLimits::default(),
    )
    .expect("weighted encoding must fit explicit defaults");
    println!("schema=axeyum.unary-avx2-weighted-synthesis-run.v1");
    println!("target=reverse");
    println!("cost-model=intel-haswell-dependent-latency-cycles");
    println!("family-costs=pshufb:1,vpermd:3,vpermq:3,vpalignr:1,vperm2i128:3");
    println!("cost-bound={}", args.bound);
    println!("variables={}", encoding.formula().variable_count());
    println!("clauses={}", encoding.formula().clauses().len());
    if let Some(path) = args.dimacs {
        std::fs::write(&path, encoding.formula().to_dimacs()).expect("write DIMACS");
        println!("dimacs={}", path.display());
        println!("verdict=encoded");
        return;
    }
    if let Some(path) = args.drat {
        let bytes = std::fs::metadata(&path).expect("stat textual DRAT").len();
        let reader = BufReader::new(File::open(&path).expect("open textual DRAT"));
        assert_eq!(
            check_drat_backward_reader(encoding.formula(), reader),
            Ok(true)
        );
        println!("drat={}", path.display());
        println!("drat-bytes={bytes}");
        println!("verdict=unsat-checked");
        return;
    }
    let started = Instant::now();
    let outcome = axeyum_cnf::solve_with_drat_proof_with_limits(
        encoding.formula(),
        Some(started + Duration::from_secs(args.seconds)),
        100_000_000,
    );
    println!("elapsed-ms={}", started.elapsed().as_millis());
    match outcome {
        ProofSolveOutcome::Sat(model) => {
            let sequence = encoding
                .lift_model(&model)
                .expect("model must lift and replay");
            println!("sequence={sequence:?}");
            println!("sequence-cost={}", costs.sequence_cost(&sequence));
            println!("verdict=sat-replayed");
        }
        ProofSolveOutcome::Unsat(proof) => {
            assert_eq!(check_drat_backward(encoding.formula(), &proof), Ok(true));
            println!("drat-steps={}", proof.len());
            println!("verdict=unsat-checked");
        }
        ProofSolveOutcome::ResourceOut => println!("verdict=resource-out"),
        ProofSolveOutcome::Interrupted => println!("verdict=interrupted"),
    }
}
