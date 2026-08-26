//! Encode, solve, and independently certify classical job-shop bounds.

use std::fmt::Write as _;
use std::fs::File;
use std::io::BufReader;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use axeyum_cnf::{
    CnfAssignment, ProofSolveOutcome, check_drat_backward, check_drat_backward_reader,
};
use axeyum_search::job_shop::{
    JobShopEncoding, JobShopEncodingLimits, JobShopProblem, JobShopSchedule, encode_job_shop,
    encode_job_shop_with_job_windows,
};

struct Arguments {
    instance: PathBuf,
    bound: usize,
    seconds: u64,
    dimacs: Option<PathBuf>,
    witness: Option<PathBuf>,
    model: Option<PathBuf>,
    schedule_out: Option<PathBuf>,
    drat: Option<PathBuf>,
    machine_orders: Option<PathBuf>,
    job_windows: bool,
}

fn arguments() -> Arguments {
    let args: Vec<String> = std::env::args().skip(1).collect();
    assert!(
        args.len() >= 2,
        "usage: certify_job_shop INSTANCE BOUND [SECONDS] [--job-windows] [--dimacs PATH] [--witness JSON] [--model SAT-SOLUTION] [--schedule-out JSON] [--check-drat PATH] [--machine-orders PATH]"
    );
    let instance = PathBuf::from(&args[0]);
    let bound = args[1]
        .parse::<usize>()
        .expect("BOUND must be a nonnegative integer");
    let mut seconds = 30_u64;
    let mut index = 2;
    if let Some(value) = args.get(index).and_then(|text| text.parse::<u64>().ok()) {
        seconds = value;
        index += 1;
    }
    let mut dimacs = None;
    let mut witness = None;
    let mut model = None;
    let mut schedule_out = None;
    let mut drat = None;
    let mut machine_orders = None;
    let mut job_windows = false;
    while index < args.len() {
        if args[index] == "--job-windows" {
            job_windows = true;
            index += 1;
            continue;
        }
        let destination = match args[index].as_str() {
            "--dimacs" => &mut dimacs,
            "--witness" => &mut witness,
            "--model" => &mut model,
            "--schedule-out" => &mut schedule_out,
            "--check-drat" => &mut drat,
            "--machine-orders" => &mut machine_orders,
            other => panic!("unknown argument: {other}"),
        };
        *destination = Some(PathBuf::from(
            args.get(index + 1).expect("option needs a path"),
        ));
        index += 2;
    }
    Arguments {
        instance,
        bound,
        seconds,
        dimacs,
        witness,
        model,
        schedule_out,
        drat,
        machine_orders,
        job_windows,
    }
}

fn parse_competition_model(text: &str, variables: usize) -> CnfAssignment {
    assert!(
        text.lines().any(|line| line.trim() == "s SATISFIABLE"),
        "model file lacks SATISFIABLE status"
    );
    let mut values = vec![None; variables];
    for line in text.lines().map(str::trim) {
        let Some(rest) = line.strip_prefix("v ") else {
            continue;
        };
        for word in rest.split_whitespace() {
            let literal = word.parse::<i64>().expect("model literal is an integer");
            if literal == 0 {
                continue;
            }
            let index =
                usize::try_from(literal.unsigned_abs() - 1).expect("model variable fits usize");
            assert!(index < variables, "model variable is out of range");
            let value = literal > 0;
            assert!(
                values[index].is_none_or(|previous| previous == value),
                "model assigns a variable inconsistently"
            );
            values[index] = Some(value);
        }
    }
    CnfAssignment::new(
        values
            .into_iter()
            .map(|value| value.expect("model must assign every formula variable"))
            .collect(),
    )
}

fn write_machine_order_manifest(path: &PathBuf, encoding: &JobShopEncoding) {
    let mut text = String::from(
        "schema=axeyum.job-shop-machine-orders.v1\nindex\tmachine\tleft-job\tleft-operation\tright-job\tright-operation\tselector\n",
    );
    for (index, order) in encoding.machine_orders().iter().enumerate() {
        writeln!(
            text,
            "{index}\t{}\t{}\t{}\t{}\t{}\t{}",
            order.machine,
            order.left_job,
            order.left_operation,
            order.right_job,
            order.right_operation,
            order.selector.dimacs()
        )
        .expect("write to String");
    }
    std::fs::write(path, text).expect("write machine-order manifest");
}

fn main() {
    let args = arguments();
    let text = std::fs::read_to_string(&args.instance).expect("read instance");
    let problem = JobShopProblem::parse_orlib(&text).expect("parse OR-Library instance");
    let encoding = if args.job_windows {
        encode_job_shop_with_job_windows(&problem, args.bound, JobShopEncodingLimits::default())
    } else {
        encode_job_shop(&problem, args.bound, JobShopEncodingLimits::default())
    }
    .expect("encoding must fit explicit defaults");
    println!("schema=axeyum.job-shop-bound-run.v1");
    println!("instance={}", args.instance.display());
    println!("jobs={}", problem.jobs.len());
    println!("machines={}", problem.machines);
    println!("bound={}", args.bound);
    println!("job-windows={}", args.job_windows);
    println!("variables={}", encoding.formula().variable_count());
    println!("clauses={}", encoding.formula().clauses().len());
    println!("machine-orders={}", encoding.machine_orders().len());
    if let Some(path) = &args.machine_orders {
        write_machine_order_manifest(path, &encoding);
        println!("machine-order-manifest={}", path.display());
    }

    let formula = if let Some(path) = &args.witness {
        let bytes = std::fs::read(path).expect("read schedule JSON");
        let schedule: JobShopSchedule =
            serde_json::from_slice(&bytes).expect("parse schedule JSON");
        let pinned = encoding
            .formula_with_schedule(&schedule)
            .expect("schedule must replay and fit bound");
        println!("witness={}", path.display());
        println!("witness-makespan={}", schedule.makespan);
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
    if let Some(path) = args.model {
        let text = std::fs::read_to_string(&path).expect("read SAT competition model");
        let model = parse_competition_model(&text, formula.variable_count());
        let schedule = encoding
            .lift_model(&model)
            .expect("external SAT model must satisfy, lift, and replay");
        if let Some(path) = args.schedule_out {
            let bytes = serde_json::to_vec_pretty(&schedule).expect("serialize schedule");
            std::fs::write(&path, bytes).expect("write schedule JSON");
            println!("schedule={}", path.display());
        }
        println!("model={}", path.display());
        println!("makespan={}", schedule.makespan);
        println!("verdict=sat-replayed");
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
            let schedule = encoding
                .lift_model(&model)
                .expect("SAT model must lift and independently replay");
            if let Some(path) = args.schedule_out {
                let bytes = serde_json::to_vec_pretty(&schedule).expect("serialize schedule");
                std::fs::write(&path, bytes).expect("write schedule JSON");
                println!("schedule={}", path.display());
            }
            println!("makespan={}", schedule.makespan);
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
