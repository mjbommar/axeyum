//! Emit a deterministic, independently checkable Boolean-product cube cover.

use std::fmt::Write as _;
use std::path::PathBuf;

use axeyum_cnf::cube::{augmented_formula, boolean_product_cubes, covering_formula};
use axeyum_cnf::{
    CnfVar, ProofSolveOutcome, check_drat, parse_dimacs, solve_with_drat_proof, write_drat,
};

fn main() {
    let mut args = std::env::args().skip(1);
    let base_path = PathBuf::from(args.next().expect("usage: BASE.cnf OUT-DIR SELECTOR..."));
    let output_dir = PathBuf::from(args.next().expect("usage: BASE.cnf OUT-DIR SELECTOR..."));
    let selector_numbers: Vec<usize> = args
        .map(|text| {
            text.parse::<usize>()
                .expect("selector must be a DIMACS variable")
        })
        .collect();
    assert!(
        !selector_numbers.is_empty(),
        "at least one selector is required"
    );

    let base_text = std::fs::read_to_string(&base_path).expect("read base DIMACS");
    let base = parse_dimacs(&base_text).expect("parse base DIMACS");
    let selectors: Vec<CnfVar> = selector_numbers
        .iter()
        .map(|number| {
            assert!(*number > 0, "DIMACS selectors are one-based");
            let variable = CnfVar::new(number - 1).expect("selector fits");
            assert!(
                variable.index() < base.variable_count(),
                "selector is in range"
            );
            variable
        })
        .collect();
    let cubes = boolean_product_cubes(&selectors).expect("product cover admitted");

    std::fs::create_dir(&output_dir).expect("create new output directory");
    let mut manifest = String::from("schema=axeyum.cnf-boolean-product-cover.v1\n");
    writeln!(manifest, "base={}", base_path.display()).unwrap();
    writeln!(manifest, "variables={}", base.variable_count()).unwrap();
    writeln!(manifest, "clauses={}", base.clauses().len()).unwrap();
    writeln!(
        manifest,
        "selectors={}",
        selector_numbers
            .iter()
            .map(usize::to_string)
            .collect::<Vec<_>>()
            .join(",")
    )
    .unwrap();
    writeln!(manifest, "cubes={}", cubes.len()).unwrap();
    for (index, cube) in cubes.iter().enumerate() {
        let name = format!("cube-{index:06}.cnf");
        let formula = augmented_formula(&base, cube).expect("cube is in range");
        std::fs::write(output_dir.join(&name), formula.to_dimacs()).expect("write cube DIMACS");
        writeln!(
            manifest,
            "cube={index}\tliterals={}\tformula={name}",
            cube.iter()
                .map(|literal| literal.dimacs().to_string())
                .collect::<Vec<_>>()
                .join(",")
        )
        .unwrap();
    }

    let covering = covering_formula(&base, &cubes).expect("cover is in range");
    let ProofSolveOutcome::Unsat(proof) = solve_with_drat_proof(&covering) else {
        panic!("Boolean product must cover every assignment");
    };
    assert_eq!(check_drat(&covering, &proof), Ok(true));
    std::fs::write(output_dir.join("covering.cnf"), covering.to_dimacs())
        .expect("write covering CNF");
    std::fs::write(output_dir.join("covering.drat"), write_drat(&proof))
        .expect("write covering DRAT");
    std::fs::write(output_dir.join("manifest.txt"), &manifest).expect("write manifest");
    print!("{manifest}");
    println!("covering-variables={}", covering.variable_count());
    println!("covering-clauses={}", covering.clauses().len());
    println!("covering-drat-steps={}", proof.len());
    println!("verdict=cover-emitted-and-checked");
}
