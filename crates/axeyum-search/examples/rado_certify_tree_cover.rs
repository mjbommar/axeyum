//! Offline certification of a dumped adaptive (tree) cover of a Rado instance.
//!
//! The search run dumps proofs and records `deferred`; this pass reads every
//! ledger it is given, re-checks every deferred proof from disk against a
//! formula it regenerates itself, and discharges all four cover obligations
//! through `certify_dumped_tree_cover`. Separating the two is what turned one
//! cover from 42% complete after 5.5 hours into complete in 152.9 seconds.
//!
//! Nothing from the search run is trusted here:
//!
//! * the **instance** is rebuilt from `(a, b, k, n)`, not read from the run;
//! * each cube's **augmenting units** come from the plan and the row's own
//!   recorded choices, not from the proof file;
//! * the **completeness** of the cover is re-derived from the union of the
//!   ledgers, so a missing cube is `MissingCell` rather than a smaller cover.
//!
//! Several ledgers may be passed: an adaptive cover that resumed after a stop
//! is spread over one ledger per run, and the union is the cover. Cube codes do
//! not depend on the tree's shape, so the union is well defined, and a cube
//! that two runs both refuted is a `DuplicateCell` rather than a silent
//! preference for one of them.
//!
//! usage: `rado_certify_tree_cover a=5 b=4 k=4 n=741 proofs=<dir> prefix=f741 \
//!         points=2,4,6,8,10,12 ledger=<a.tsv> [ledger2=<b.tsv> ...]`
//!
//! exit: 0 certified, 3 rejected (the message names the obligation and the
//! cube), 2 usage.

// `main` is one long linear script by design: parse the arguments, run, and
// report. Splitting it would scatter a driver that is meant to be read top to
// bottom next to the log it produces.
#![allow(clippy::too_many_lines)]

use std::collections::BTreeMap;
use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Instant;

use axeyum_search::certify::certify_dumped_tree_cover;
use axeyum_search::cover::colour_branch_plan;
use axeyum_search::ledger::parse_ledger;
use axeyum_search::{CellRecord, CheckMode, ColouringFamily, Rado};

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
    let Some(proofs) = args.get("proofs") else {
        eprintln!(
            "usage: rado_certify_tree_cover a=5 b=4 k=4 n=741 proofs=<dir> prefix=f741 \
             points=2,4,… ledger=<tsv> [ledger2=<tsv> …]"
        );
        return ExitCode::from(2);
    };
    let proofs = PathBuf::from(proofs);
    let (a, b, k, n) = (
        number("a", 5),
        number("b", 4),
        number("k", 4),
        number("n", 741),
    );
    let prefix = args
        .get("prefix")
        .cloned()
        .unwrap_or_else(|| format!("f{n}"));

    let family = Rado::new(a, b, k).expect("family");
    let problem = family.problem(n).expect("problem");
    let formula = problem.encode().expect("encode");
    let points: Vec<usize> = match args.get("points") {
        Some(list) => list
            .split(',')
            .map(|token| token.parse().expect("branch point"))
            .collect(),
        None => family.branch_points(number("depth", 12)),
    };
    let plan = colour_branch_plan(&problem, &points).expect("plan");

    let mut ledgers: Vec<&String> = args
        .iter()
        .filter(|(key, _)| key.starts_with("ledger"))
        .map(|(_, value)| value)
        .collect();
    ledgers.sort();
    if ledgers.is_empty() {
        eprintln!("no ledger= argument: nothing to certify");
        return ExitCode::from(2);
    }
    let mut records: Vec<CellRecord> = Vec::new();
    for path in &ledgers {
        let text = fs::read_to_string(path).expect("read ledger");
        match parse_ledger(&text) {
            Ok(rows) => {
                println!("ledger {path}: {} rows", rows.len());
                records.extend(rows);
            }
            Err(error) => {
                println!("{{\"status\":\"bad-ledger\",\"path\":{path:?},\"error\":\"{error}\"}}");
                return ExitCode::from(3);
            }
        }
    }
    // Concatenating ledgers can reintroduce exactly the duplicate row finding
    // B2 produced, so re-run that check over the union rather than per file.
    let mut codes: Vec<usize> = records.iter().map(|record| record.index).collect();
    codes.sort_unstable();
    let total = codes.len();
    codes.dedup();
    if codes.len() != total {
        println!(
            "{{\"status\":\"duplicate-rows\",\"rows\":{total},\"distinct\":{}}}",
            codes.len()
        );
        return ExitCode::from(3);
    }

    let started = Instant::now();
    let verdict = certify_dumped_tree_cover(
        &formula,
        &plan,
        &records,
        &proofs,
        &prefix,
        CheckMode::Backward,
    );
    let wall = started.elapsed().as_secs_f64();
    match verdict {
        Ok(certificate) => {
            println!("{}", certificate.summary());
            println!(
                "{{\"status\":\"certified\",\"a\":{a},\"b\":{b},\"k\":{k},\"n\":{n},\
                 \"cubes\":{},\"steps\":{},\"branch_clauses\":{:?},\"wall_s\":{wall:.1}}}",
                certificate.cells, certificate.steps, certificate.branch_clauses,
            );
            ExitCode::SUCCESS
        }
        Err(error) => {
            println!(
                "{{\"status\":\"rejected\",\"a\":{a},\"b\":{b},\"k\":{k},\"n\":{n},\
                 \"error\":\"{error}\",\"wall_s\":{wall:.1}}}"
            );
            ExitCode::from(3)
        }
    }
}
