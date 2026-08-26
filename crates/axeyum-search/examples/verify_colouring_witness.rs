//! Independently replay a colouring witness and bind it to Axeyum's CNF.
//!
//! The family implementation checks the defining relation by brute force,
//! without consulting the encoder. The witness is then converted to a complete
//! one-hot assignment and evaluated against the freshly generated formula.
//!
//! For a uniform family, `canonicalize=true` may rename freely permutable
//! colours by first occurrence so an externally named palette satisfies the
//! encoding's symmetry clauses. It is refused for off-diagonal families.
//!
//! usage: `verify_colouring_witness family=rado:a=3,b=1,k=5 witness=path.txt \
//!         [canonicalize=true]`

use std::collections::BTreeMap;
use std::fs;
use std::process::ExitCode;

use axeyum_search::{Witness, parse_family};

fn main() -> ExitCode {
    let args: BTreeMap<String, String> = std::env::args()
        .skip(1)
        .filter_map(|arg| {
            arg.split_once('=')
                .map(|(key, value)| (key.to_owned(), value.to_owned()))
        })
        .collect();
    let Some(specification) = args.get("family") else {
        eprintln!("missing family=<specification>");
        return ExitCode::from(2);
    };
    let Some(path) = args.get("witness") else {
        eprintln!("missing witness=<path>");
        return ExitCode::from(2);
    };
    let family = match parse_family(specification) {
        Ok(family) => family,
        Err(error) => {
            eprintln!("invalid family: {error}");
            return ExitCode::from(2);
        }
    };
    let text = match fs::read_to_string(path) {
        Ok(text) => text,
        Err(error) => {
            eprintln!("cannot read witness: {error}");
            return ExitCode::from(2);
        }
    };
    let mut witness = match Witness::parse(family.colours(), &text) {
        Ok(witness) => witness,
        Err(error) => {
            eprintln!("invalid witness: {error}");
            return ExitCode::from(1);
        }
    };
    let canonicalize = args
        .get("canonicalize")
        .is_some_and(|value| value == "true");
    if canonicalize {
        if family.colour_dependent() {
            eprintln!("palette canonicalization is unsound for an off-diagonal family");
            return ExitCode::from(2);
        }
        witness = witness.canonicalize_palette();
    }

    if let Err(error) = family.verify_witness(&witness) {
        eprintln!("relation replay failed: {error}");
        return ExitCode::from(1);
    }
    let problem = match family.problem(witness.points()) {
        Ok(problem) => problem,
        Err(error) => {
            eprintln!("problem construction failed: {error}");
            return ExitCode::from(2);
        }
    };
    let formula = match problem.encode() {
        Ok(formula) => formula,
        Err(error) => {
            eprintln!("encoding failed: {error}");
            return ExitCode::from(2);
        }
    };
    let assignment = match problem.witness_assignment(&witness) {
        Ok(assignment) => assignment,
        Err(error) => {
            eprintln!("assignment construction failed: {error}");
            return ExitCode::from(1);
        }
    };
    if formula.evaluate(&assignment) != Ok(true) {
        eprintln!("witness does not satisfy the freshly generated formula");
        return ExitCode::from(1);
    }

    println!(
        "{{\"schema\":\"axeyum.colouring-witness-check.v1\",\"status\":\"verified\",\
         \"family\":{:?},\"points\":{},\"colours\":{},\"variables\":{},\
         \"clauses\":{},\"canonicalized\":{canonicalize}}}",
        family.label(),
        witness.points(),
        witness.colours(),
        formula.variable_count(),
        formula.clauses().len(),
    );
    ExitCode::SUCCESS
}
