//! Rebuild and check one retained Boolean-product cube leaf.
//!
//! This is deliberately a *leaf* verdict, not an UNSAT verdict for the base
//! formula.  A complete result still requires every leaf plus the independently
//! checked covering proof; use `check_boolean_product_cover` for that step.

use std::fs::File;
use std::io::BufReader;
use std::path::PathBuf;

use axeyum_cnf::cube::{augmented_formula, boolean_product_cubes};
use axeyum_cnf::{CnfVar, check_drat_backward_reader, parse_dimacs};

fn main() {
    let mut args = std::env::args().skip(1);
    let base_path = PathBuf::from(
        args.next()
            .expect("usage: BASE.cnf LEAF.drat CUBE-INDEX SELECTOR..."),
    );
    let proof_path = PathBuf::from(
        args.next()
            .expect("usage: BASE.cnf LEAF.drat CUBE-INDEX SELECTOR..."),
    );
    let cube_index = args
        .next()
        .expect("usage: BASE.cnf LEAF.drat CUBE-INDEX SELECTOR...")
        .parse::<usize>()
        .expect("cube index must be a non-negative integer");
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

    let base = parse_dimacs(&std::fs::read_to_string(&base_path).expect("read base DIMACS"))
        .expect("parse base DIMACS");
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
    let cube = cubes.get(cube_index).expect("cube index is in range");
    let augmented = augmented_formula(&base, cube).expect("cube literals are in range");
    let reader = BufReader::new(File::open(&proof_path).expect("open leaf DRAT"));
    assert_eq!(
        check_drat_backward_reader(&augmented, reader),
        Ok(true),
        "leaf proof must refute the regenerated base-and-cube formula"
    );

    println!("schema=axeyum.cnf-cube-leaf-check.v1");
    println!("base={}", base_path.display());
    println!("variables={}", base.variable_count());
    println!("clauses={}", base.clauses().len());
    println!("cube-index={cube_index}");
    println!(
        "cube-literals={}",
        cube.iter()
            .map(|literal| literal.dimacs().to_string())
            .collect::<Vec<_>>()
            .join(",")
    );
    println!("proof={}", proof_path.display());
    println!("checker=file-backed-backward");
    println!("verdict=leaf-unsat-checked");
}
