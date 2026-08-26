//! Synthesize and certify bounded unary AVX2 byte permutations.

use std::fs::File;
use std::io::BufReader;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use axeyum_cnf::{ProofSolveOutcome, check_drat_backward, check_drat_backward_reader};
use axeyum_search::simd::ByteTags;
use axeyum_search::simd_synthesis::{UnaryAvx2SynthesisLimits, encode_unary_avx2_sequence};

struct Arguments {
    target: ByteTags,
    target_name: String,
    steps: usize,
    seconds: u64,
    dimacs: Option<PathBuf>,
    drat: Option<PathBuf>,
}

fn target(text: &str) -> ByteTags {
    if text == "reverse" {
        return ByteTags::reversed();
    }
    let values = text
        .split(',')
        .map(|word| word.parse::<u8>().expect("target tags must be u8"))
        .collect::<Vec<_>>();
    let values: [u8; 32] = values.try_into().expect("target must contain 32 tags");
    ByteTags::new(values.map(Some)).expect("target tags must be in range")
}

fn arguments() -> Arguments {
    let args: Vec<String> = std::env::args().skip(1).collect();
    assert!(
        args.len() >= 2,
        "usage: synthesize_unary_avx2 TARGET STEPS [SECONDS] [--dimacs PATH] [--check-drat PATH]"
    );
    let target_name = args[0].clone();
    let target = target(&target_name);
    let steps = args[1]
        .parse::<usize>()
        .expect("STEPS must be a nonnegative integer");
    let mut seconds = 30_u64;
    let mut index = 2;
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
        target,
        target_name,
        steps,
        seconds,
        dimacs,
        drat,
    }
}

fn main() {
    let args = arguments();
    let encoding = encode_unary_avx2_sequence(
        &args.target,
        args.steps,
        UnaryAvx2SynthesisLimits::default(),
    )
    .expect("encoding must fit explicit defaults");
    println!("schema=axeyum.unary-avx2-synthesis-run.v1");
    println!("target={}", args.target_name);
    println!("steps={}", args.steps);
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
