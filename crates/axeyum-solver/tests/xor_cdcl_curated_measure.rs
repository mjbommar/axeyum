//! MEASUREMENT harness (not production wiring): does CDCL(XOR) decide the
//! curated `QF_BV` multiplier-equivalence instances that plain batsat times out
//! on?
//!
//! This is an `#[ignore]`-by-default integration test. It changes no library
//! code, no dispatch, no trust ledger. It reproduces `sat_bv_backend`'s
//! lowering→encoding path (parse SMT-LIB → `lower_terms` → `tseitin_encode` →
//! `CnfFormula`) for a small SELECTED SUBSET of curated files and runs BOTH
//! `solve_with_xor_cdcl` (the new search-only CDCL(XOR) core; CONFLICT-budgeted,
//! not time-budgeted) and `solve_with_rustsat_batsat_timeout` (the production
//! adapter) on the same `CnfFormula`, recording verdict, wall-clock time, and
//! CNF size. Where both reach a definite verdict it asserts they agree (a
//! disagreement is a soundness bug to surface loudly).
//!
//! Run it explicitly:
//! ```sh
//! cargo test -p axeyum-solver --test xor_cdcl_curated_measure -- --ignored --nocapture
//! ```
#![cfg(feature = "full")]

use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use axeyum_bv::lower_terms;
use axeyum_cnf::{
    CnfFormula, SatResult, XorCdclResult, solve_with_rustsat_batsat_timeout, solve_with_xor_cdcl,
    tseitin_encode,
};

/// Per-instance batsat wall-clock cap. The `xor_cdcl` core has no time budget
/// (its `2M`-conflict budget bounds it), so only batsat gets a clock cap here.
const BATSAT_TIMEOUT: Duration = Duration::from_secs(2);

/// A curated file plus the role it plays in the measurement.
struct Pick {
    /// File stem under `corpus/qfbv-curated/` (without `.smt2`).
    stem: &'static str,
    /// Human-readable role for the table.
    role: &'static str,
}

/// The selected subset: the smaller multiplier unknowns first, then SAT and
/// easy-UNSAT controls. (Multiplier unknowns are the question; controls confirm
/// both solvers agree on instances they both decide.)
const PICKS: &[Pick] = &[
    // --- multiplier-equivalence unknowns (batsat times out at 2 s) ----------
    Pick {
        stem: "brummayerbiere3__mulhs08",
        role: "mul-unknown (exp unsat)",
    },
    Pick {
        stem: "calypto__problem_9",
        role: "mul-unknown (exp sat)",
    },
    Pick {
        stem: "stp_samples__22930-0601-11",
        role: "mul-unknown (exp unsat)",
    },
    Pick {
        stem: "brummayerbiere3__mulhs16",
        role: "mul-unknown (exp unsat)",
    },
    Pick {
        stem: "stp_samples__22930-0426-195",
        role: "mul-unknown (exp unsat)",
    },
    // --- SAT controls (both should agree: sat) ------------------------------
    Pick {
        stem: "bmc-bv__ex13",
        role: "control sat",
    },
    Pick {
        stem: "bench_ab__a100test0001",
        role: "control sat",
    },
    Pick {
        stem: "bench_ab__a115test0002",
        role: "control sat",
    },
    // --- easy-UNSAT controls (both should agree: unsat) ---------------------
    Pick {
        stem: "crafted__bitops0",
        role: "control unsat",
    },
    Pick {
        stem: "bruttomesso__ext_con_004_001_0016",
        role: "control unsat",
    },
    Pick {
        stem: "wienand-cav2008__distrib04.sf",
        role: "control unsat",
    },
];

fn curated_dir() -> PathBuf {
    // CARGO_MANIFEST_DIR is crates/axeyum-solver; the corpus is at the repo root.
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("corpus")
        .join("qfbv-curated")
}

/// Reproduces `sat_bv_backend::check_with_replay`'s lowering→encoding path:
/// parse SMT-LIB, lower the assertions to AIG, Tseitin-encode the root bits.
/// No inprocessing (we measure on the un-inprocessed Tseitin CNF, the baseline
/// both solvers see identically).
fn encode_to_cnf(path: &Path) -> CnfFormula {
    let text =
        std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let script = axeyum_smtlib::parse_script(&text)
        .unwrap_or_else(|e| panic!("parse {}: {e:?}", path.display()));
    let lowering = lower_terms(&script.arena, &script.assertions)
        .unwrap_or_else(|e| panic!("lower {}: {e:?}", path.display()));
    let roots: Vec<_> = lowering.roots().iter().map(|r| r.bits()[0]).collect();
    let encoding = tseitin_encode(lowering.aig(), &roots)
        .unwrap_or_else(|e| panic!("tseitin {}: {e:?}", path.display()));
    encoding.formula().clone()
}

/// Compact verdict label for either solver.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

impl Verdict {
    fn label(self) -> &'static str {
        match self {
            Verdict::Sat => "sat",
            Verdict::Unsat => "unsat",
            Verdict::Unknown => "unknown",
        }
    }
}

fn xor_verdict(r: &XorCdclResult) -> Verdict {
    match r {
        XorCdclResult::Sat(_) => Verdict::Sat,
        XorCdclResult::Unsat => Verdict::Unsat,
        XorCdclResult::Unknown => Verdict::Unknown,
    }
}

fn batsat_verdict(r: &SatResult) -> Verdict {
    match r {
        SatResult::Sat(_) => Verdict::Sat,
        SatResult::Unsat(_) => Verdict::Unsat,
        SatResult::Unknown(_) => Verdict::Unknown,
    }
}

#[test]
#[ignore = "measurement harness; run explicitly with --ignored --nocapture"]
fn xor_cdcl_vs_batsat_on_curated_multipliers() {
    let dir = curated_dir();

    println!();
    println!(
        "CDCL(XOR) vs batsat on curated QF_BV (xor_cdcl: 2M-CONFLICT budget, NOT time; \
         batsat: {BATSAT_TIMEOUT:?} wall cap)"
    );
    println!("Tseitin CNF reproduced from sat_bv_backend's lowering path; no inprocessing.");
    println!();
    println!(
        "{:<34} {:<24} {:>7} {:>8}  {:>9} {:>9}  {:>9} {:>9}  new?",
        "file", "role", "vars", "clauses", "batsat", "bat_ms", "xorcdcl", "xor_ms"
    );
    println!("{}", "-".repeat(140));

    let mut decided_by_xor_not_batsat: Vec<&str> = Vec::new();
    let mut disagreements: Vec<String> = Vec::new();

    for pick in PICKS {
        let path = dir.join(format!("{}.smt2", pick.stem));
        if !path.exists() {
            println!("{:<34} MISSING ({})", pick.stem, path.display());
            continue;
        }

        let formula = encode_to_cnf(&path);
        let vars = formula.variable_count();
        let clauses = formula.clauses().len();

        // batsat (time-budgeted)
        let t0 = Instant::now();
        let bat = solve_with_rustsat_batsat_timeout(&formula, Some(BATSAT_TIMEOUT))
            .expect("batsat adapter should not error");
        let bat_ms = t0.elapsed().as_secs_f64() * 1000.0;
        let bat_v = batsat_verdict(&bat);

        // xor_cdcl (conflict-budgeted; its "time" is whatever 2M conflicts or a
        // decision takes — reported honestly, it is NOT a wall-clock budget)
        let t1 = Instant::now();
        let xor = solve_with_xor_cdcl(&formula);
        let xor_ms = t1.elapsed().as_secs_f64() * 1000.0;
        let xor_v = xor_verdict(&xor);

        // Soundness cross-check: where both are definite, they MUST agree.
        if bat_v != Verdict::Unknown && xor_v != Verdict::Unknown && bat_v != xor_v {
            disagreements.push(format!(
                "{}: batsat={} xor_cdcl={}",
                pick.stem,
                bat_v.label(),
                xor_v.label()
            ));
        }

        // Did xor_cdcl decide something batsat did not (within these budgets)?
        let new = xor_v != Verdict::Unknown && bat_v == Verdict::Unknown;
        if new {
            decided_by_xor_not_batsat.push(pick.stem);
        }

        println!(
            "{:<34} {:<24} {:>7} {:>8}  {:>9} {:>9.1}  {:>9} {:>9.1}  {}",
            pick.stem,
            pick.role,
            vars,
            clauses,
            bat_v.label(),
            bat_ms,
            xor_v.label(),
            xor_ms,
            if new { "YES <-- xor only" } else { "" }
        );
    }

    println!("{}", "-".repeat(140));
    println!();
    println!("ANSWER:");
    if decided_by_xor_not_batsat.is_empty() {
        println!(
            "  CDCL(XOR) decided NO curated multiplier unknown that batsat could not \
             (within these budgets)."
        );
    } else {
        println!(
            "  CDCL(XOR) decided {} instance(s) batsat did not: {}",
            decided_by_xor_not_batsat.len(),
            decided_by_xor_not_batsat.join(", ")
        );
    }
    println!();
    println!(
        "  (xor_cdcl heuristics, from xor_cdcl.rs: lowest-index branching, false-first \
         phase, NO restarts, NO VSIDS.)"
    );

    // A soundness disagreement is a bug; fail loudly.
    assert!(
        disagreements.is_empty(),
        "SOUNDNESS DISAGREEMENT(s): {}",
        disagreements.join("; ")
    );
}
