//! Independent re-validation of a tree cover from its ledger alone.
//!
//! A cover run that checks inline and keeps no DRAT bytes leaves one artifact:
//! the list of cubes it refuted. That list is the interesting part — every
//! proof regenerates from it deterministically — but only if something actually
//! regenerates them. This driver is that something, and it is meant to run on a
//! **different host, with a different worker count, from a different
//! checkout** than the search did.
//!
//! For each ledger row it rebuilds `F` from `(a, b, k, n)`, rebuilds the cube's
//! augmenting units from the row's own recorded choices through the branch
//! plan, re-refutes it with axeyum's proof-producing CDCL core, re-checks the
//! proof with `check_drat_backward`, and then compares against the row:
//!
//! * the **verdict** must still be `unsat` — a `sat` here is a soundness alarm
//!   and would mean the recorded cover is worthless;
//! * the **step count** must match exactly. Determinism is a public API
//!   promise, so a differing count is a defect somewhere, not noise, and this
//!   is the only check that would notice.
//!
//! Only when every row survives does it run `certify_tree_cover` over the
//! re-derived records, so the certificate it prints is built from what this
//! process checked, never from what the ledger asserted.
//!
//! usage: `rado_replay_tree_cover a=5 b=4 k=4 n=741 points=5,10,… \
//!         ledger=<tsv> [workers=16] [strict_steps=1]`
//!
//! exit: 0 every row re-validated and the cover certified, 3 a mismatch or a
//! rejected cover (the message names the cube), 10 a cube came back SAT, 2
//! usage.

// `main` is one long linear script by design: parse, replay, compare, certify.
#![allow(clippy::too_many_lines)]

use std::collections::BTreeMap;
use std::fs;
use std::process::ExitCode;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, PoisonError};
use std::time::{Duration, Instant};

use axeyum_cnf::{
    CnfClause, DratStep, ProofSolveOutcome, check_drat_backward, solve_with_drat_proof,
};
use axeyum_search::cover::{certify_tree_cover, colour_branch_plan};
use axeyum_search::ledger::parse_ledger;
use axeyum_search::{CellCheck, CellRecord, CellVerdict, ColouringFamily, Rado};

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
    let Some(ledger) = args.get("ledger") else {
        eprintln!("usage: rado_replay_tree_cover a=5 b=4 k=4 n=741 points=5,10,… ledger=<tsv>");
        return ExitCode::from(2);
    };
    let (a, b, k, n) = (
        number("a", 5),
        number("b", 4),
        number("k", 4),
        number("n", 741),
    );
    let workers = number("workers", 8).max(1);
    let strict_steps = number("strict_steps", 1) != 0;

    let family = Rado::new(a, b, k).expect("family");
    let problem = family.problem(n).expect("problem");
    let formula = problem.encode().expect("encode");
    let points: Vec<usize> = match args.get("points") {
        Some(list) => list
            .split(',')
            .map(|token| token.parse().expect("branch point"))
            .collect(),
        None => family.branch_points(number("depth", 16)),
    };
    let plan = colour_branch_plan(&problem, &points).expect("plan");

    let recorded = match parse_ledger(&fs::read_to_string(ledger).expect("read ledger")) {
        Ok(rows) => rows,
        Err(error) => {
            println!("{{\"status\":\"bad-ledger\",\"error\":\"{error}\"}}");
            return ExitCode::from(3);
        }
    };
    println!(
        "replaying {} cubes of R_{k}({a}(x-y)={b}z) n={n} ({} vars, {} clauses) on {workers} workers",
        recorded.len(),
        formula.variable_count(),
        formula.clauses().len(),
    );

    let next = AtomicUsize::new(0);
    let done = AtomicUsize::new(0);
    let replayed: Mutex<Vec<CellRecord>> = Mutex::new(Vec::new());
    let alarms: Mutex<Vec<String>> = Mutex::new(Vec::new());
    let started = Instant::now();

    std::thread::scope(|scope| {
        for _ in 0..workers {
            scope.spawn(|| {
                loop {
                    if !alarms
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .is_empty()
                    {
                        return;
                    }
                    let index = next.fetch_add(1, Ordering::SeqCst);
                    let Some(row) = recorded.get(index) else {
                        return;
                    };
                    let mut augmented = formula.clone();
                    for literal in plan
                        .literals_for_prefix(&row.choices)
                        .expect("cube literals")
                    {
                        augmented
                            .add_clause(CnfClause::new(vec![literal]))
                            .expect("unit clause");
                    }
                    let solve_started = Instant::now();
                    let outcome = solve_with_drat_proof(&augmented);
                    let solve = solve_started.elapsed();
                    let proof =
                        match outcome {
                            ProofSolveOutcome::Unsat(proof) => proof,
                            ProofSolveOutcome::Sat(_) => {
                                alarms.lock().unwrap_or_else(PoisonError::into_inner).push(
                                    format!("cube {} came back SATISFIABLE on replay", row.index),
                                );
                                return;
                            }
                            other => {
                                alarms.lock().unwrap_or_else(PoisonError::into_inner).push(
                                    format!(
                                        "cube {} replay gave {other:?}, not a refutation",
                                        row.index
                                    ),
                                );
                                return;
                            }
                        };
                    let steps = proof.len();
                    // Count clause ADDITIONS separately. The 313 cover shipped
                    // with an `adds` column that duplicated `steps` in all 4096
                    // rows and carried no information; do not repeat it.
                    let adds = proof
                        .iter()
                        .filter(|step| matches!(step, DratStep::Add(_)))
                        .count();
                    if strict_steps && steps != row.steps {
                        alarms
                            .lock()
                            .unwrap_or_else(PoisonError::into_inner)
                            .push(format!(
                                "cube {} replayed to {steps} proof steps, the ledger records {}; \
                             determinism is a public API promise, so this is a defect",
                                row.index, row.steps
                            ));
                        return;
                    }
                    let check_started = Instant::now();
                    let verdict = check_drat_backward(&augmented, &proof);
                    let check_time = check_started.elapsed();
                    let check = match verdict {
                        Ok(true) => CellCheck::Passed,
                        Ok(false) => CellCheck::Failed("no empty clause derived".to_string()),
                        Err(error) => CellCheck::Failed(error.to_string()),
                    };
                    if let CellCheck::Failed(reason) = &check {
                        alarms
                            .lock()
                            .unwrap_or_else(PoisonError::into_inner)
                            .push(format!(
                                "cube {} proof REJECTED on replay: {reason}",
                                row.index
                            ));
                        return;
                    }
                    replayed
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .push(CellRecord {
                            run: row.run.clone(),
                            index: row.index,
                            choices: row.choices.clone(),
                            verdict: CellVerdict::Unsat,
                            solve,
                            steps,
                            adds,
                            check,
                            check_time,
                        });
                    let finished = done.fetch_add(1, Ordering::Relaxed) + 1;
                    if finished.is_multiple_of(250) {
                        println!(
                            "[{:8.1}s] replayed {finished}/{} cubes",
                            started.elapsed().as_secs_f64(),
                            recorded.len()
                        );
                    }
                }
            });
        }
    });
    let wall = started.elapsed();

    let alarms = alarms.into_inner().unwrap_or_else(PoisonError::into_inner);
    if !alarms.is_empty() {
        for alarm in &alarms {
            println!("ALARM {alarm}");
        }
        let sat = alarms.iter().any(|alarm| alarm.contains("SATISFIABLE"));
        println!(
            "{{\"status\":\"{}\",\"alarms\":{}}}",
            if sat { "SAT-ON-REPLAY" } else { "mismatch" },
            alarms.len()
        );
        return ExitCode::from(if sat { 10 } else { 3 });
    }

    let mut records = replayed
        .into_inner()
        .unwrap_or_else(PoisonError::into_inner);
    records.sort_by_key(|record| record.index);
    let steps: usize = records.iter().map(|record| record.steps).sum();
    let check_time: Duration = records.iter().map(|record| record.check_time).sum();
    match certify_tree_cover(&formula, &plan, &records) {
        Ok(certificate) => {
            println!("{}", certificate.summary());
            println!(
                "{{\"status\":\"revalidated\",\"a\":{a},\"b\":{b},\"k\":{k},\"n\":{n},\
                 \"cubes\":{},\"steps\":{steps},\"check_s\":{:.1},\"wall_s\":{:.1},\
                 \"strict_steps\":{strict_steps}}}",
                certificate.cells,
                check_time.as_secs_f64(),
                wall.as_secs_f64(),
            );
            ExitCode::SUCCESS
        }
        Err(error) => {
            println!(
                "{{\"status\":\"rejected\",\"cubes\":{},\"steps\":{steps},\
                 \"error\":\"{error}\",\"wall_s\":{:.1}}}",
                records.len(),
                wall.as_secs_f64(),
            );
            ExitCode::from(3)
        }
    }
}
