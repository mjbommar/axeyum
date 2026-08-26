//! Produce, replay, and optionally encode one conditional energetic lemma.

use std::path::PathBuf;

use axeyum_search::job_shop::{
    JobShopEncodingLimits, JobShopEnergeticDomain, JobShopProblem,
    check_job_shop_conditional_energetic_conflict, encode_job_shop_with_job_windows,
    encode_job_shop_with_precedence_closure, find_job_shop_conditional_energetic_conflict,
};

fn number(args: &[String], index: usize, name: &str) -> usize {
    args.get(index)
        .unwrap_or_else(|| panic!("missing {name}"))
        .parse()
        .unwrap_or_else(|_| panic!("{name} must be a nonnegative integer"))
}

fn main() {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    assert!(
        args.len() >= 6,
        "usage: job_shop_conditional_energetic INSTANCE BOUND MACHINE START END MAX_ASSUMPTIONS [--precedence-closure] [--conflict-out JSON] [--dimacs PATH]"
    );
    let instance = PathBuf::from(&args[0]);
    let bound = number(&args, 1, "BOUND");
    let machine = number(&args, 2, "MACHINE");
    let interval_start = number(&args, 3, "START");
    let interval_end = number(&args, 4, "END");
    let max_assumptions = number(&args, 5, "MAX_ASSUMPTIONS");
    let mut precedence_closure = false;
    let mut conflict_out = None;
    let mut dimacs = None;
    let mut index = 6;
    while index < args.len() {
        match args[index].as_str() {
            "--precedence-closure" => {
                precedence_closure = true;
                index += 1;
            }
            "--conflict-out" => {
                conflict_out = Some(PathBuf::from(
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
    let search = find_job_shop_conditional_energetic_conflict(
        &problem,
        bound,
        domain,
        machine,
        interval_start,
        interval_end,
        max_assumptions,
    )
    .expect("bounded conditional energetic search");
    println!("schema=axeyum.job-shop-conditional-energetic-search.v1");
    println!("instance={}", instance.display());
    println!("bound={bound}");
    println!("machine={machine}");
    println!("interval={interval_start}..{interval_end}");
    println!("base-required-energy={}", search.base.required_energy);
    println!("capacity-energy={}", search.base.capacity_energy);
    println!("candidates-checked={}", search.candidates_checked);
    let Some(conflict) = search.conflict else {
        assert!(conflict_out.is_none() && dimacs.is_none());
        println!("verdict=no-conditional-energetic-conflict");
        return;
    };
    let check = check_job_shop_conditional_energetic_conflict(&problem, bound, &conflict)
        .expect("producer output must independently replay");
    println!("assumptions={}", check.assumptions_applied);
    println!("required-energy={}", check.energetic.required_energy);
    if let Some(path) = conflict_out {
        let bytes = serde_json::to_vec_pretty(&conflict).expect("serialize conflict");
        std::fs::write(&path, bytes).expect("write conflict");
        println!("conflict={}", path.display());
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
            .formula_with_conditional_energetic_conflict(&conflict)
            .expect("insert independently checked lemma");
        std::fs::write(&path, formula.to_dimacs()).expect("write strengthened DIMACS");
        println!("dimacs={}", path.display());
        println!("variables={}", formula.variable_count());
        println!("clauses={}", formula.clauses().len());
    }
    println!("verdict=conditional-energetic-conflict-checked");
}
