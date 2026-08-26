//! Exhaustively derive checked standalone energetic unit clauses.

use std::path::PathBuf;

use axeyum_search::job_shop::{
    JobShopConditionalEnergeticUnitLimits, JobShopEncodingLimits, JobShopEnergeticDomain,
    JobShopProblem, encode_job_shop_with_job_windows, encode_job_shop_with_precedence_closure,
    scan_job_shop_conditional_energetic_unit_conflicts,
};

fn main() {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    assert!(
        args.len() >= 2,
        "usage: job_shop_conditional_energetic_scan INSTANCE BOUND [--precedence-closure] [--conflicts-out JSON] [--dimacs PATH]"
    );
    let instance = PathBuf::from(&args[0]);
    let bound = args[1]
        .parse::<usize>()
        .expect("BOUND must be a nonnegative integer");
    let mut precedence_closure = false;
    let mut conflicts_out = None;
    let mut dimacs = None;
    let mut index = 2;
    while index < args.len() {
        match args[index].as_str() {
            "--precedence-closure" => {
                precedence_closure = true;
                index += 1;
            }
            "--conflicts-out" => {
                conflicts_out = Some(PathBuf::from(
                    args.get(index + 1).expect("missing JSON path"),
                ));
                index += 2;
            }
            "--dimacs" => {
                dimacs = Some(PathBuf::from(
                    args.get(index + 1).expect("missing DIMACS path"),
                ));
                index += 2;
            }
            other => panic!("unknown argument: {other}"),
        }
    }
    let text = std::fs::read_to_string(&instance).expect("read instance");
    let problem = JobShopProblem::parse_orlib(&text).expect("parse OR-Library instance");
    let domain = if precedence_closure {
        JobShopEnergeticDomain::PrecedenceClosure
    } else {
        JobShopEnergeticDomain::JobChains
    };
    let scan = scan_job_shop_conditional_energetic_unit_conflicts(
        &problem,
        bound,
        domain,
        JobShopConditionalEnergeticUnitLimits::default(),
    )
    .expect("conditional energetic unit scan");
    println!("schema=axeyum.job-shop-conditional-energetic-unit-scan.v1");
    println!("instance={}", instance.display());
    println!("bound={bound}");
    println!("intervals-checked={}", scan.intervals_checked);
    println!("candidates-checked={}", scan.candidates_checked);
    println!("task-checks={}", scan.task_checks);
    println!("conflicts={}", scan.conflicts.len());
    if let Some(path) = conflicts_out {
        let bytes = serde_json::to_vec_pretty(&scan.conflicts).expect("serialize conflicts");
        std::fs::write(&path, bytes).expect("write conflicts");
        println!("conflicts-out={}", path.display());
    }
    if let Some(path) = dimacs {
        let encoding = if precedence_closure {
            encode_job_shop_with_precedence_closure(
                &problem,
                bound,
                JobShopEncodingLimits::default(),
            )
        } else {
            encode_job_shop_with_job_windows(&problem, bound, JobShopEncodingLimits::default())
        }
        .expect("encode exact job-shop question");
        let formula = encoding
            .formula_with_conditional_energetic_conflicts(&scan.conflicts)
            .expect("insert checked conditional energetic units");
        std::fs::write(&path, formula.to_dimacs()).expect("write strengthened DIMACS");
        println!("dimacs={}", path.display());
        println!("variables={}", formula.variable_count());
        println!("clauses={}", formula.clauses().len());
    }
    println!("verdict=conditional-energetic-units-checked");
}
