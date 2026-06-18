//! MEASUREMENT harness (destination-2 / P2.1): does the EXISTING lazy
//! bit-blasting abstraction (`solve_lazy_bv_abstraction`, ADR-0019) — built but
//! NOT wired into the default `solve`/bench path — decide problems the eager
//! mountain-builder drowns on?
//!
//! Two cohorts (the lever's payoff is conditional):
//! - **Essential-multiplier** (the curated multiplier-equivalence unknowns): the
//!   heavy op IS the crux, so lazy must refine (bit-blast) it and collapses to the
//!   eager strategy — expected NO shortcut. Measured to confirm/quantify.
//! - **Incidental-heavy-op** (the contradiction is in non-multiplier
//!   constraints): lazy decides with **zero** ops refined — the multiplier never
//!   materializes. The broad real-world pattern Z3's word-level reasoning sweeps
//!   and our default eager path chokes on.
//!
//! `#[ignore]` by default; run with `--ignored --nocapture`.

use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, solve, solve_lazy_bv_abstraction};

fn curated_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("corpus")
        .join("qfbv-curated")
}

fn cfg() -> SolverConfig {
    SolverConfig::default().with_timeout(Duration::from_secs(4))
}

fn verdict(r: &CheckResult) -> &'static str {
    match r {
        CheckResult::Sat(_) => "sat",
        CheckResult::Unsat => "unsat",
        CheckResult::Unknown(_) => "unknown",
    }
}

#[test]
#[ignore = "measurement; run with --ignored --nocapture"]
fn lazy_on_curated_multipliers() {
    let dir = curated_dir();
    let picks = [
        "brummayerbiere3__mulhs08",
        "calypto__problem_9",
        "stp_samples__22930-0601-11",
    ];
    println!();
    println!("LAZY abstraction-refinement on curated multiplier unknowns (eager: all unknown@2s):");
    println!(
        "{:<34} {:>9} {:>6} {:>8} {:>7} {:>9}",
        "file", "lazy", "ops", "refined", "rounds", "lazy_ms"
    );
    println!("{}", "-".repeat(80));
    for stem in picks {
        let path = dir.join(format!("{stem}.smt2"));
        if !path.exists() {
            println!("{stem:<34} MISSING");
            continue;
        }
        let text = std::fs::read_to_string(&path).unwrap();
        let mut script = match axeyum_smtlib::parse_script(&text) {
            Ok(s) => s,
            Err(e) => {
                println!("{stem:<34} parse-error {e:?}");
                continue;
            }
        };
        let t = Instant::now();
        let lazy =
            solve_lazy_bv_abstraction(&mut script.arena, &script.assertions, &cfg()).unwrap();
        let ms = t.elapsed().as_secs_f64() * 1000.0;
        println!(
            "{stem:<34} {:>9} {:>6} {:>8} {:>7} {ms:>9.0}",
            verdict(&lazy.result),
            lazy.ops_total,
            lazy.ops_refined,
            lazy.rounds
        );
    }
    println!("(essential-multiplier: lazy refines the gadget — no shortcut vs eager)");
}

/// `x = 1 ∧ x = 2` (the real contradiction) ∧ `r = p*q` (incidental 64-bit mul).
fn build_incidental(a: &mut TermArena, width: u32) -> Vec<TermId> {
    let xs = a.declare("x", Sort::BitVec(width)).unwrap();
    let ps = a.declare("p", Sort::BitVec(width)).unwrap();
    let qs = a.declare("q", Sort::BitVec(width)).unwrap();
    let rs = a.declare("r", Sort::BitVec(width)).unwrap();
    let x = a.var(xs);
    let p = a.var(ps);
    let q = a.var(qs);
    let r = a.var(rs);
    let one = a.bv_const(width, 1).unwrap();
    let two = a.bv_const(width, 2).unwrap();
    let mul = a.bv_mul(p, q).unwrap();
    let c1 = a.eq(x, one).unwrap();
    let c2 = a.eq(x, two).unwrap();
    let c3 = a.eq(r, mul).unwrap();
    vec![c1, c2, c3]
}

#[test]
#[ignore = "measurement; run with --ignored --nocapture"]
fn lazy_decides_incidental_heavy_op_eager_chokes() {
    let w = 64u32;

    // eager — bit-blasts the 64-bit multiplier (the mountain).
    let mut a1 = TermArena::new();
    let asserts1 = build_incidental(&mut a1, w);
    let t0 = Instant::now();
    let eager = solve(&mut a1, &asserts1, &cfg()).unwrap();
    let eager_ms = t0.elapsed().as_secs_f64() * 1000.0;

    // lazy — should be UNSAT with 0 ops refined, far faster.
    let mut a2 = TermArena::new();
    let asserts2 = build_incidental(&mut a2, w);
    let t1 = Instant::now();
    let lazy = solve_lazy_bv_abstraction(&mut a2, &asserts2, &cfg()).unwrap();
    let lazy_ms = t1.elapsed().as_secs_f64() * 1000.0;

    println!();
    println!("INCIDENTAL 64-bit multiplier (real contradiction is x=1 ∧ x=2):");
    println!("  eager:  {} in {eager_ms:.0} ms", verdict(&eager));
    println!(
        "  lazy:   {} in {lazy_ms:.0} ms  (ops_total={}, ops_refined={}, rounds={})",
        verdict(&lazy.result),
        lazy.ops_total,
        lazy.ops_refined,
        lazy.rounds
    );

    // The lever working as intended: UNSAT decided WITHOUT blasting the multiplier.
    assert!(
        matches!(lazy.result, CheckResult::Unsat),
        "lazy must decide UNSAT, got {:?}",
        lazy.result
    );
    assert_eq!(
        lazy.ops_refined, 0,
        "lazy must decide WITHOUT materializing the multiplier (0 refined)"
    );
    assert_eq!(lazy.ops_total, 1, "exactly one heavy op present");
}
