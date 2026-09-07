//! Does the inprocessed proof still check **at corpus scale**, and what does it
//! cost?
//!
//! ```sh
//! cargo run --release -p axeyum-cnf --example inprocess_proof_check -- \
//!     <file.cnf> [max_conflicts] [off|subsume|vivify|bve|preprocess|preprocess-full]
//! ```
//!
//! `tests/inprocess_proof_path.rs` establishes that every `unsat` the
//! inprocessed path produces carries a proof [`check_drat`] accepts against the
//! **original** formula, over a 19-instance corpus of small fixtures. This is
//! the same obligation asked of one real `p4dfa` instance, where the numbers are
//! four to six orders of magnitude larger and a checker that is fine on a
//! 30-clause pigeonhole may not finish at all.
//!
//! It reports the two checking routes separately because they are not
//! interchangeable here: forward [`check_drat`] re-derives every step against a
//! growing active set, while [`check_drat_backward`] only re-derives the steps
//! the refutation actually needs. On the committed pigeonhole fixture the
//! boolean-core lane measured backward at 26x forward; whether that ratio
//! survives a preprocessing prefix — which is *front-loaded* and may be almost
//! entirely unnecessary to the refutation — is exactly what this prints.
//!
//! One JSON object on stdout. `verdict` other than `unsat` means there was no
//! proof to check, which the driver must not read as a passing check.

use std::time::Instant;

use axeyum_cnf::{
    InprocessOptions, ProofSolveOutcome, check_drat, check_drat_backward, parse_dimacs,
    solve_with_drat_proof_inprocessed,
};

fn arm_options(name: &str) -> InprocessOptions {
    match name {
        "off" => InprocessOptions::OFF,
        "subsume" => InprocessOptions {
            subsume: true,
            ..InprocessOptions::OFF
        },
        "vivify" => InprocessOptions {
            vivify: true,
            ..InprocessOptions::OFF
        },
        "bve" => InprocessOptions {
            bve: true,
            ..InprocessOptions::OFF
        },
        "preprocess" => InprocessOptions::preprocess(),
        "preprocess-full" => InprocessOptions::preprocess_full(),
        other => panic!("unknown arm `{other}`"),
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let path = args
        .next()
        .expect("usage: inprocess_proof_check <file.cnf> [max_conflicts] [arm]");
    let max_conflicts: usize = args.next().map_or(20_000, |a| {
        a.parse().expect("max_conflicts must be a number")
    });
    let arm = args.next().unwrap_or_else(|| "preprocess".to_owned());
    let options = arm_options(&arm);

    let text = std::fs::read_to_string(&path).expect("read cnf");
    let formula = parse_dimacs(&text).expect("parse dimacs");
    drop(text);

    let solve_started = Instant::now();
    let outcome = solve_with_drat_proof_inprocessed(&formula, None, max_conflicts, options);
    let solve_seconds = solve_started.elapsed().as_secs_f64();

    let ProofSolveOutcome::Unsat(proof) = outcome else {
        let verdict = match outcome {
            ProofSolveOutcome::Sat(_) => "sat",
            ProofSolveOutcome::ResourceOut => "resource_out",
            ProofSolveOutcome::Interrupted => "interrupted",
            ProofSolveOutcome::Unsat(_) => unreachable!("matched above"),
        };
        println!(
            "{{\"file\":\"{path}\",\"arm\":\"{arm}\",\"verdict\":\"{verdict}\",\
             \"solve_seconds\":{solve_seconds:.3},\"checked\":false}}"
        );
        return;
    };

    let steps = proof.len();

    let backward_started = Instant::now();
    let backward = check_drat_backward(&formula, &proof);
    let backward_seconds = backward_started.elapsed().as_secs_f64();

    let forward_started = Instant::now();
    let forward = check_drat(&formula, &proof);
    let forward_seconds = forward_started.elapsed().as_secs_f64();

    println!(
        "{{\"file\":\"{path}\",\"arm\":\"{arm}\",\"verdict\":\"unsat\",\
         \"solve_seconds\":{solve_seconds:.3},\"proof_steps\":{steps},\
         \"backward\":\"{backward:?}\",\"backward_seconds\":{backward_seconds:.3},\
         \"forward\":\"{forward:?}\",\"forward_seconds\":{forward_seconds:.3},\
         \"checked\":{}}}",
        forward == Ok(true)
    );
}
