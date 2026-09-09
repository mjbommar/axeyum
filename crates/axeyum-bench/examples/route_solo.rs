//! Run **one named route, alone**, on one benchmark file.
//!
//! # Why this exists
//!
//! The 2026-09-07 route-attribution sweep wanted a virtual best — each route run
//! alone on each file — and could not have one: *"`SolverConfig` has no
//! route-selection knob, so that is not measurable and is not claimed"*
//! (`docs/research/12-performance/route-attribution-2026-09-07.md`). That is
//! still true of the dispatcher, and this example does not change it. What it
//! does instead is call the route entry points **directly**, one per process,
//! so the question "would this route have decided this file inside the budget,
//! had it been given the budget?" becomes a measurement rather than an
//! inference from a truncated trail.
//!
//! A sequential trail is three-valued per file: every route before the winner
//! is a measured NO, the winner is a measured YES, and **every route after it is
//! UNKNOWN**. A portfolio's whole prize lives in that third class, and no amount
//! of re-reading the same trails recovers it.
//!
//! # What this is NOT
//!
//! **It is not the shipped front door, and its answers are not parity verdicts.**
//! Three gaps, each of which makes this a LOWER bound on what a route can do:
//!
//! 1. It decides the **flat assertion view** (`parse_script` +
//!    `solvable_flat_view`), the same view `explain_corpus` uses — which
//!    disagrees with the shipped front door on 134 of 397 benchmarks. Thirteen
//!    front-door stages can decide a file before `check_auto` is ever reached.
//! 2. It applies **no preprocessing, no coercion normalization, and no admission
//!    test**. `check_auto` runs the canonicalizer and the `to_real`/`to_int`
//!    normalization before dispatch; a route called cold may decline on a shape
//!    the dispatcher would have handed it in normal form.
//! 3. `array-fast-path` in a route trail is **one label over four distinct
//!    sub-routes**, so the names here are finer than the trail's and do not map
//!    one-to-one onto it.
//!
//! A route that decides a file here would decide it in a portfolio arm. A route
//! that declines here may still decide under the dispatcher. Read every negative
//! as "not shown", never as "cannot".
//!
//! # Isolation
//!
//! One route per process, by construction: there is no `--routes a,b,c`. Two
//! routes in one process share an allocator, a warm page cache and this
//! workspace's thread-local instrument state, so the second one measured would
//! not be measuring the same thing as the first. The caller loops over
//! `--list`'s output under its own `timeout`, which is also what makes a route
//! that ignores its budget a killable process rather than a leaked thread.
//!
//! # Usage
//!
//! ```text
//! route_solo --list
//! route_solo <benchmark.smt2> --route <name> [--timeout-ms N]
//! ```
//!
//! Prints one TSV line: `route`, `verdict`, `wall_ms`, `detail`.

use std::fs;
use std::process::ExitCode;
use std::time::{Duration, Instant};

use axeyum_ir::{TermArena, TermId};
use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SatBvBackend, SolverConfig, SolverError};

/// Worker stack, sized like `smtcomp_cli`'s: a deeply nested input must not turn
/// a decline into a stack-overflow abort.
const WORKER_STACK_BYTES: usize = 512 * 1024 * 1024;

/// One route the solo prober can run.
///
/// `run` takes the arena by value-of-mutable-borrow and the assertions, so a
/// route that mutates the arena (most of them introduce fresh symbols) cannot
/// leak that mutation into another route's measurement: the caller hands each
/// invocation its own parse.
struct Route {
    name: &'static str,
    run: fn(&mut TermArena, &[TermId], &SolverConfig) -> Result<CheckResult, SolverError>,
}

/// The routes with a public entry point of the shape this prober can drive.
///
/// This list is deliberately NOT derived from the dispatcher: `auto.rs` is a
/// hard-coded `if let Some(..)` cascade whose route names are `&'static str`
/// literals at ~85 recording sites, with no registry to read. So the coverage
/// claim here is exactly "these routes", never "every route", and a name absent
/// from this table is untested rather than shown irrelevant.
fn routes() -> Vec<Route> {
    vec![
        Route {
            name: "lia-dpll",
            run: axeyum_solver::check_with_lia_dpll,
        },
        Route {
            name: "lra-dpll",
            run: axeyum_solver::check_with_lra_dpll,
        },
        Route {
            name: "nra",
            run: axeyum_solver::check_with_nra,
        },
        Route {
            name: "uf-arithmetic",
            run: axeyum_solver::check_with_uf_arithmetic,
        },
        Route {
            name: "uf-arith-lazy",
            run: axeyum_solver::check_with_uf_arithmetic_lazy,
        },
        Route {
            name: "uflia-online",
            run: axeyum_solver::check_qf_uflia_online,
        },
        Route {
            name: "uflra-online",
            run: axeyum_solver::check_qf_uflra_online,
        },
        Route {
            name: "ufbv-online-cdclt",
            run: axeyum_solver::check_qf_ufbv_online_cdclt,
        },
        Route {
            name: "abv-online-cdclt",
            run: axeyum_solver::check_qf_aufbv_online_cdclt,
        },
        Route {
            name: "datatype-elim",
            run: axeyum_solver::check_with_datatype_elimination,
        },
        Route {
            name: "datatype-native",
            run: axeyum_solver::check_with_datatype_native,
        },
        Route {
            name: "euf-online",
            run: |arena, assertions, config| {
                Ok(axeyum_solver::check_qf_uf_online_cdclt(
                    arena, assertions, config,
                ))
            },
        },
        Route {
            name: "lia-online-cdclt",
            run: |arena, assertions, config| {
                axeyum_solver::check_qf_lia_online_cdclt(arena, assertions, config)
            },
        },
        Route {
            name: "lra-online-cdclt",
            run: |arena, assertions, config| {
                axeyum_solver::check_qf_lra_online_cdclt(arena, assertions, config)
            },
        },
        Route {
            name: "abv-lazy-row",
            run: |arena, assertions, config| {
                let mut backend = SatBvBackend::default();
                axeyum_solver::check_qf_abv_lazy_row(&mut backend, arena, assertions, config)
            },
        },
        Route {
            name: "array-elim",
            run: |arena, assertions, config| {
                let mut backend = SatBvBackend::default();
                axeyum_solver::check_with_array_elimination(&mut backend, arena, assertions, config)
            },
        },
        Route {
            name: "aufbv",
            run: |arena, assertions, config| {
                let mut backend = SatBvBackend::default();
                axeyum_solver::check_with_arrays_and_functions(
                    &mut backend,
                    arena,
                    assertions,
                    config,
                )
            },
        },
    ]
}

fn verdict_of(result: &CheckResult) -> (&'static str, String) {
    match result {
        CheckResult::Sat(_) => ("sat", String::new()),
        CheckResult::Unsat => ("unsat", String::new()),
        CheckResult::Unknown(reason) => ("unknown", format!("{reason:?}")),
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.iter().any(|a| a == "--list") {
        for route in routes() {
            println!("{}", route.name);
        }
        return ExitCode::SUCCESS;
    }

    let mut path = None;
    let mut want = None;
    let mut timeout_ms: u64 = 24_000;
    let mut it = args.iter();
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--route" => want = it.next().cloned(),
            "--timeout-ms" => {
                timeout_ms = it.next().and_then(|v| v.parse().ok()).unwrap_or(timeout_ms);
            }
            other if other.starts_with("--") => {
                eprintln!("route_solo: unknown flag {other}");
                return ExitCode::FAILURE;
            }
            other => path = Some(other.to_string()),
        }
    }

    let (Some(path), Some(want)) = (path, want) else {
        eprintln!("usage: route_solo <benchmark.smt2> --route <name> [--timeout-ms N]");
        eprintln!("       route_solo --list");
        return ExitCode::FAILURE;
    };

    let all = routes();
    let Some(route) = all.into_iter().find(|r| r.name == want) else {
        // An unknown name must fail loudly. A prober that silently ran nothing
        // and exited 0 would report every route as "did not decide".
        eprintln!("route_solo: no route named {want}; try --list");
        return ExitCode::FAILURE;
    };

    let text = match fs::read_to_string(&path) {
        Ok(text) => text,
        Err(error) => {
            println!("{want}\tread-error\t0\t{error}");
            return ExitCode::FAILURE;
        }
    };

    let config = SolverConfig {
        timeout: Some(Duration::from_millis(timeout_ms)),
        ..SolverConfig::default()
    };

    let name = route.name;
    let run = route.run;
    let worker = std::thread::Builder::new()
        .stack_size(WORKER_STACK_BYTES)
        .spawn(move || {
            let mut script = match parse_script(&text) {
                Ok(script) => script,
                Err(error) => return (String::from("parse-error"), 0u128, format!("{error}")),
            };
            let Some(assertions) = script.solvable_flat_view() else {
                // A word-first-fallback parse has an EMPTY flat view whose
                // content lives in the parser side channels; solving it would be
                // a vacuous `sat`, which is worse than reporting no coverage.
                return (String::from("no-flat-view"), 0, String::new());
            };
            let assertions = assertions.to_vec();
            let started = Instant::now();
            let outcome = run(&mut script.arena, &assertions, &config);
            let wall = started.elapsed().as_millis();
            match outcome {
                Ok(result) => {
                    let (verdict, detail) = verdict_of(&result);
                    (verdict.to_string(), wall, detail)
                }
                Err(error) => (String::from("error"), wall, format!("{error}")),
            }
        });

    let worker = match worker {
        Ok(worker) => worker,
        Err(error) => {
            println!("{name}\tspawn-failed\t0\t{error}");
            return ExitCode::FAILURE;
        }
    };
    match worker.join() {
        Ok((verdict, wall_ms, detail)) => {
            println!("{name}\t{verdict}\t{wall_ms}\t{detail}");
            ExitCode::SUCCESS
        }
        Err(_) => {
            // A panic is a real answer about this route on this file, and one a
            // portfolio arm would have to survive; it is never silence.
            println!("{name}\tpanic\t0\t");
            ExitCode::FAILURE
        }
    }
}
