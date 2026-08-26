//! Rebuild and check a Boolean-product cube refutation from retained proofs.

use std::fs::File;
use std::io::BufReader;
use std::path::PathBuf;

use axeyum_cnf::cube::{boolean_product_cubes, check_cube_refutation_backward_readers};
use axeyum_cnf::{CnfVar, parse_dimacs};

fn main() {
    let mut args = std::env::args().skip(1);
    let base_path = PathBuf::from(args.next().expect("usage: BASE.cnf COVER-DIR SELECTOR..."));
    let cover_dir = PathBuf::from(args.next().expect("usage: BASE.cnf COVER-DIR SELECTOR..."));
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
    let readers: Vec<_> = (0..cubes.len())
        .map(|index| {
            let path = cover_dir.join(format!("cube-{index:06}.drat"));
            BufReader::new(File::open(path).expect("open cube DRAT"))
        })
        .collect();
    let covering =
        BufReader::new(File::open(cover_dir.join("covering.drat")).expect("open covering DRAT"));
    check_cube_refutation_backward_readers(&base, &cubes, readers, covering)
        .expect("check composite cube refutation");
    println!("schema=axeyum.cnf-cube-refutation-check.v1");
    println!("base={}", base_path.display());
    println!("variables={}", base.variable_count());
    println!("clauses={}", base.clauses().len());
    println!("cubes={}", cubes.len());
    println!("checker=file-backed-backward-plus-covering-drat");
    println!("verdict=unsat-checked");
}
