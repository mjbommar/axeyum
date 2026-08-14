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
//! usage: `rado_dump_cnf a=5 b=4 k=4 n=741 out=F_741.cnf`
//!
//! exit: 0 written, 2 usage.

use std::collections::BTreeMap;
use std::fs;
use std::process::ExitCode;

use axeyum_search::{ColouringFamily, Rado};

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
        eprintln!("usage: rado_dump_cnf a=5 b=4 k=4 n=741 out=<file.cnf>");
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
    let formula = problem.encode().expect("encode");
    let dimacs = formula.to_dimacs();
    fs::write(out, &dimacs).expect("write cnf");
    println!(
        "{{\"status\":\"written\",\"a\":{a},\"b\":{b},\"k\":{k},\"n\":{n},\
         \"vars\":{},\"clauses\":{},\"bytes\":{},\"out\":{out:?}}}",
        formula.variable_count(),
        formula.clauses().len(),
        dimacs.len(),
    );
    ExitCode::SUCCESS
}
