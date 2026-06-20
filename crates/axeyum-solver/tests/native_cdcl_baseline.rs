//! MEASUREMENT harness (slice 1, not production wiring): how far off batsat is
//! the in-tree native CDCL core (`solve_with_drat_proof_within`) as a primary
//! SAT search?
//!
//! This is an `#[ignore]`-by-default integration test. It reproduces
//! `sat_bv_backend`'s lowering→encoding path (parse SMT-LIB → `lower_terms` →
//! `tseitin_encode` → `CnfFormula`, no inprocessing) on a handful of instances
//! spanning small SAT, small UNSAT, and a couple from the p4dfa small-CNF band,
//! then runs BOTH the native core and `solve_with_rustsat_batsat_timeout` on the
//! same formula. It records each engine's verdict + wall-clock and the per-instance
//! gap factor, and ASSERTS the two engines agree wherever both decide (a
//! disagreement would be a soundness bug to surface loudly).
//!
//! Run it explicitly (release for honest timings):
//! ```sh
//! cargo test -p axeyum-solver --release --test native_cdcl_baseline \
//!     -- --ignored --nocapture
//! ```

use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use axeyum_bv::lower_terms;
use axeyum_cnf::{
    CnfFormula, ProofSolveOutcome, SatResult, solve_with_drat_proof_within,
    solve_with_rustsat_batsat_timeout, tseitin_encode,
};

/// Per-instance wall-clock cap for both engines, so a single hard instance can
/// never hang the measurement. Both engines get the same deadline.
const ENGINE_TIMEOUT: Duration = Duration::from_secs(10);

/// A measured instance: a corpus path relative to `corpus/` and a role label.
struct Pick {
    /// Path under `corpus/` (without the leading `corpus/`).
    rel: &'static str,
    /// Human-readable role for the table.
    role: &'static str,
}

const PICKS: &[Pick] = &[
    // --- small controls from the curated set --------------------------------
    Pick {
        rel: "qfbv-curated/bench_ab__a100test0001.smt2",
        role: "small sat",
    },
    Pick {
        rel: "qfbv-curated/bmc-bv__ex13.smt2",
        role: "small sat",
    },
    Pick {
        rel: "qfbv-curated/crafted__bitops0.smt2",
        role: "small unsat",
    },
    Pick {
        rel: "qfbv-curated/bruttomesso__ext_con_004_001_0016.smt2",
        role: "small unsat",
    },
    Pick {
        rel: "qfbv-curated/wienand-cav2008__distrib04.sf.smt2",
        role: "small unsat",
    },
    // --- p4dfa small-CNF band ----------------------------------------------
    Pick {
        rel: "public/non-incremental/QF_BV/20221214-p4dfa-XiaoqiChen/Composition/\
              simple_bit8_na1_nr1_twocond.smt2",
        role: "p4dfa small",
    },
    Pick {
        rel: "public/non-incremental/QF_BV/20221214-p4dfa-XiaoqiChen/MobileDevice/\
              mobiledevice_bit8_na1_nr1_twocond.smt2",
        role: "p4dfa small",
    },
];

fn corpus_dir() -> PathBuf {
    // CARGO_MANIFEST_DIR is crates/axeyum-solver; the corpus is at the repo root.
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("corpus")
}

/// Reproduces `sat_bv_backend::check_with_replay`'s lowering→encoding path on the
/// un-inprocessed Tseitin CNF (the baseline both engines see identically).
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

fn native_verdict(r: &ProofSolveOutcome) -> Verdict {
    match r {
        ProofSolveOutcome::Sat(_) => Verdict::Sat,
        ProofSolveOutcome::Unsat(_) => Verdict::Unsat,
        ProofSolveOutcome::ResourceOut | ProofSolveOutcome::Interrupted => Verdict::Unknown,
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
#[ignore = "measurement harness; run explicitly with --release --ignored --nocapture"]
fn native_cdcl_vs_batsat_baseline() {
    let dir = corpus_dir();

    println!();
    println!("native CDCL vs batsat baseline (per-instance wall-clock, same Tseitin CNF)");
    println!(
        "{:<26} {:>9} {:>8} | {:>10} {:>8} | {:>10} {:>8} | {:>8}",
        "instance", "vars", "clauses", "native", "verdict", "batsat", "verdict", "gap x"
    );

    let mut gaps: Vec<f64> = Vec::new();
    for pick in PICKS {
        let path = dir.join(pick.rel);
        let formula = encode_to_cnf(&path);
        let vars = formula.variable_count();
        let clauses = formula.clauses().len();

        let native_deadline = Instant::now().checked_add(ENGINE_TIMEOUT);
        let t0 = Instant::now();
        let native = solve_with_drat_proof_within(&formula, native_deadline);
        let native_time = t0.elapsed();

        let t1 = Instant::now();
        let batsat = solve_with_rustsat_batsat_timeout(&formula, Some(ENGINE_TIMEOUT))
            .expect("batsat solve");
        let batsat_time = t1.elapsed();

        let nv = native_verdict(&native);
        let bv = batsat_verdict(&batsat);

        // Soundness gate: where both decide, they MUST agree.
        if nv != Verdict::Unknown && bv != Verdict::Unknown {
            assert_eq!(
                nv.label(),
                bv.label(),
                "DISAGREE on {}: native={} batsat={}",
                pick.rel,
                nv.label(),
                bv.label()
            );
        }

        let stem = Path::new(pick.rel)
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or(pick.rel);
        let stem: String = stem.chars().take(26).collect();

        let native_ms = native_time.as_secs_f64() * 1000.0;
        let batsat_ms = batsat_time.as_secs_f64() * 1000.0;
        let gap = if batsat_ms > 0.0 {
            native_ms / batsat_ms
        } else {
            f64::INFINITY
        };
        // Only fold a gap into the geomean where both engines decided (an
        // `unknown` timeout is a floor, not a true time).
        if nv != Verdict::Unknown && bv != Verdict::Unknown && gap.is_finite() {
            gaps.push(gap);
        }

        println!(
            "{:<26} {:>9} {:>8} | {:>8.2}ms {:>8} | {:>8.2}ms {:>8} | {:>7.1}x [{}]",
            stem,
            vars,
            clauses,
            native_ms,
            nv.label(),
            batsat_ms,
            bv.label(),
            gap,
            pick.role
        );
    }

    if !gaps.is_empty() {
        // Geometric mean of the per-instance gap factors (robust to outliers).
        let log_sum: f64 = gaps.iter().map(|g| g.ln()).sum();
        let count = u32::try_from(gaps.len()).unwrap_or(u32::MAX);
        let geomean = (log_sum / f64::from(count)).exp();
        let max = gaps.iter().copied().fold(f64::MIN, f64::max);
        let min = gaps.iter().copied().fold(f64::MAX, f64::min);
        println!();
        println!(
            "gap factor (native/batsat) over {} both-decided instances: \
             geomean {geomean:.1}x  (min {min:.1}x, max {max:.1}x)",
            gaps.len()
        );
    }
}
