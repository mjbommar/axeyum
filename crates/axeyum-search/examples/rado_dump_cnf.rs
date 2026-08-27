//! Write the deciding CNF **from the encoder the cover actually used**.
//!
//! A cover ledger records `unsat` for a list of cubes. That is a verdict about
//! a formula, and it is worth nothing unless the formula is identified — the
//! 313 upper bound shipped for a while with five cover ledgers and no pinned
//! instance. The pin is checked by *regeneration*, so the bytes have to come
//! from somewhere, and the only honest somewhere is the encoder the search ran
//! against: `ColouringProblem::encode`, reached through the same
//! `Rado::problem` the cover drivers call.
//!
//! Compare the output against `scripts/gen-rado-instance.py a b k n` and the
//! independent encoder inside `scripts/check-claim-certificates.py`. Three
//! implementations agreeing byte for byte is what makes the pin mean "this is
//! the formula those parameters denote" rather than "this is a file someone
//! stored".
//!
//! usage: `rado_dump_cnf a=5 b=4 k=4 n=741 out=F_741.cnf \
//!         [prefix_witness=previous.txt prefix_points=100]`
//! or: `rado_dump_cnf a=3 b=2 k=5 n=405 out=repair.cnf \
//!      hamming_witness=witness-404.txt hamming_points=404 max_changes=10`
//! Add `hamming_mod_palette=true` to minimize distance over all colour
//! permutations in one checked bijection encoding.
//! Or add `hamming_permutation=2,1,3,4,5` to generate one explicit labelled
//! representative for finite proof-set composition.
//!
//! exit: 0 written, 2 usage.

use std::collections::BTreeMap;
use std::fs;
use std::process::ExitCode;

use axeyum_cnf::WeightedAtMostLimits;
use axeyum_search::{ColouringFamily, Rado, Witness};

fn apply_hamming_permutation(args: &BTreeMap<String, String>, witness: Witness) -> Witness {
    let Some(permutation) = args.get("hamming_permutation") else {
        return witness;
    };
    let permutation = permutation
        .split(',')
        .map(|value| value.parse::<usize>().expect("palette image number"))
        .collect::<Vec<_>>();
    witness
        .permute_palette(&permutation)
        .expect("permute Hamming witness palette")
}

fn usage() {
    eprintln!(
        "usage: rado_dump_cnf a=5 b=4 k=4 n=741 out=<file.cnf> \
         [prefix_witness=<path> prefix_points=<count>]"
    );
}

fn main() -> ExitCode {
    let args: BTreeMap<String, String> = std::env::args()
        .skip(1)
        .filter_map(|arg| {
            arg.split_once('=')
                .map(|(key, value)| (key.to_string(), value.to_string()))
        })
        .collect();
    let number = |key: &str, fallback: usize| -> usize {
        args.get(key)
            .map_or(fallback, |value| value.parse().expect("number"))
    };
    let Some(out) = args.get("out") else {
        usage();
        return ExitCode::from(2);
    };
    let (a, b, k, n) = (
        number("a", 5),
        number("b", 4),
        number("k", 4),
        number("n", 741),
    );
    let family = Rado::new(a, b, k).expect("family");
    let problem = family.problem(n).expect("problem");
    let prefix = (args.get("prefix_witness"), args.get("prefix_points"));
    let hamming = (
        args.get("hamming_witness"),
        args.get("hamming_points"),
        args.get("max_changes"),
    );
    let (formula, restriction) = match (prefix, hamming) {
        ((None, None), (None, None, None)) => {
            (problem.encode().expect("encode"), "canonical".to_owned())
        }
        ((Some(path), Some(points)), (None, None, None)) => {
            let text = fs::read_to_string(path).expect("read prefix witness");
            let witness = Witness::parse(k, &text).expect("parse prefix witness");
            let points = points.parse::<usize>().expect("prefix_points number");
            (
                problem
                    .encode_with_witness_prefix(&witness, points)
                    .expect("encode with witness prefix"),
                format!("fixed-prefix:{points}"),
            )
        }
        ((None, None), (Some(path), Some(points), Some(changes))) => {
            let text = fs::read_to_string(path).expect("read Hamming witness");
            let witness = apply_hamming_permutation(
                &args,
                Witness::parse(k, &text).expect("parse Hamming witness"),
            );
            let points = points.parse::<usize>().expect("hamming_points number");
            let changes = changes.parse::<u64>().expect("max_changes number");
            if args.get("hamming_mod_palette").map(String::as_str) == Some("true") {
                let encoding = problem
                    .encode_with_witness_hamming_ball_up_to_palette_permutation(
                        &witness,
                        points,
                        changes,
                        WeightedAtMostLimits::default(),
                    )
                    .expect("encode palette-orbit Hamming ball");
                (
                    encoding.formula().clone(),
                    format!("hamming-mod-palette:{points}:at-most:{changes}"),
                )
            } else {
                let encoding = problem
                    .encode_with_witness_hamming_ball(
                        &witness,
                        points,
                        changes,
                        WeightedAtMostLimits::default(),
                    )
                    .expect("encode Hamming ball");
                (
                    encoding.formula().clone(),
                    format!("hamming:{points}:at-most:{changes}"),
                )
            }
        }
        _ => {
            eprintln!(
                "supply either the complete prefix pair, the complete Hamming triple, or neither"
            );
            return ExitCode::from(2);
        }
    };
    let dimacs = formula.to_dimacs();
    fs::write(out, &dimacs).expect("write cnf");
    println!(
        "{{\"status\":\"written\",\"a\":{a},\"b\":{b},\"k\":{k},\"n\":{n},\
         \"restriction\":{restriction:?},\"vars\":{},\"clauses\":{},\"bytes\":{},\
         \"out\":{out:?}}}",
        formula.variable_count(),
        formula.clauses().len(),
        dimacs.len(),
    );
    ExitCode::SUCCESS
}
