//! Close checked energetic units and emit the strengthened job-shop CNF.

use std::path::PathBuf;

use axeyum_search::job_shop::{
    JobShopConditionalEnergeticConflict, JobShopConditionalEnergeticFixpointLimits,
    JobShopEncodingLimits, JobShopProblem, close_job_shop_conditional_energetic_units,
    encode_job_shop_with_precedence_closure, propagate_job_shop_precedences_with_start_bounds,
};
use serde::Serialize;

#[derive(Serialize)]
#[serde(deny_unknown_fields)]
struct FixpointReceipt<'a> {
    schema: &'static str,
    instance: String,
    bound: usize,
    premise_conflicts: &'a [JobShopConditionalEnergeticConflict],
    fixpoint: &'a axeyum_search::job_shop::JobShopConditionalEnergeticFixpoint,
    base_clauses: usize,
    strengthened_clauses: usize,
}

fn main() {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    assert!(
        args.len() == 4 || args.len() == 5,
        "usage: job_shop_start_bound_propagation INSTANCE BOUND PREMISE_CONFLICTS_JSON FIXPOINT_JSON [STRENGTHENED_DIMACS]"
    );
    let instance = PathBuf::from(&args[0]);
    let bound = args[1]
        .parse::<usize>()
        .expect("BOUND must be a nonnegative integer");
    let premises_path = PathBuf::from(&args[2]);
    let receipt_path = PathBuf::from(&args[3]);
    let problem =
        JobShopProblem::parse_orlib(&std::fs::read_to_string(&instance).expect("read instance"))
            .expect("parse OR-Library instance");
    let premises: Vec<JobShopConditionalEnergeticConflict> =
        serde_json::from_slice(&std::fs::read(&premises_path).expect("read premise-conflict JSON"))
            .expect("parse premise-conflict JSON");
    let fixpoint = close_job_shop_conditional_energetic_units(
        &problem,
        bound,
        &premises,
        JobShopConditionalEnergeticFixpointLimits::default(),
    )
    .expect("close checked energetic units");
    let propagation =
        propagate_job_shop_precedences_with_start_bounds(&problem, bound, &fixpoint.assumptions)
            .expect("propagate derived start bounds");
    let encoding =
        encode_job_shop_with_precedence_closure(&problem, bound, JobShopEncodingLimits::default())
            .expect("encode precedence-closed job shop");
    let mut conflicts = premises.clone();
    conflicts.extend(fixpoint.conflicts.iter().cloned());
    let strengthened = encoding
        .formula_with_conditional_energetic_conflicts(&conflicts)
        .expect("insert checked energetic clauses");
    let receipt = FixpointReceipt {
        schema: "axeyum.job-shop-conditional-energetic-fixpoint.v1",
        instance: instance.display().to_string(),
        bound,
        premise_conflicts: &premises,
        fixpoint: &fixpoint,
        base_clauses: encoding.formula().clauses().len(),
        strengthened_clauses: strengthened.clauses().len(),
    };
    std::fs::write(
        &receipt_path,
        serde_json::to_vec_pretty(&receipt).expect("serialize fixpoint receipt"),
    )
    .expect("write fixpoint receipt");
    if let Some(path) = args.get(4) {
        std::fs::write(path, strengthened.to_dimacs()).expect("write strengthened DIMACS");
        println!("strengthened-dimacs={path}");
    }

    println!("schema=axeyum.job-shop-conditional-energetic-fixpoint.v1");
    println!("instance={}", instance.display());
    println!("bound={bound}");
    println!("premise-conflicts={}", premises.len());
    println!("fixpoint-rounds={}", fixpoint.rounds.len());
    println!("contextual-conflicts={}", fixpoint.conflicts.len());
    println!("derived-bounds={}", fixpoint.assumptions.len());
    println!("stabilized={}", fixpoint.stabilized);
    println!("propagation-rounds={}", propagation.rounds);
    println!(
        "forced-orders={}",
        propagation
            .machine_orders
            .iter()
            .filter(|status| {
                !matches!(
                    status,
                    axeyum_search::job_shop::JobShopMachineOrderStatus::Free
                )
            })
            .count()
    );
    println!("infeasible={}", propagation.infeasible);
    println!("base-clauses={}", encoding.formula().clauses().len());
    println!("strengthened-clauses={}", strengthened.clauses().len());
    println!("fixpoint-receipt={}", receipt_path.display());
    println!("verdict=checked-fixpoint");
}
