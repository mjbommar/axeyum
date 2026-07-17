//! Regression: the NIA/NRA relaxation honors config.timeout instead of running
//! many seconds past it (task #84 — a hang/OOM risk on large lazy-SMT cubes).
//! The deadline poll is soundness-neutral (only slow → Unknown), so this asserts
//! a *timely* Unknown, never a specific verdict.
#![cfg(feature = "full")]
use std::time::{Duration, Instant};

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

fn nia_file(name: &str) -> Option<String> {
    let dir = "corpus/public-curated/non-incremental/QF_NIA/cvc5-regress-clean";
    let p = std::fs::read_dir(dir)
        .ok()?
        .filter_map(std::result::Result::ok)
        .map(|e| e.path())
        .find(|p| {
            p.file_name()
                .is_some_and(|n| n.to_string_lossy().contains(name))
        })?;
    std::fs::read_to_string(p).ok()
}

#[test]
fn nia_relaxation_honors_timeout() {
    // mod.03 overran a 15s budget by ~14s before the deadline was threaded into
    // the decide_system loops + sort_roots. With a 2s budget it must return a
    // sound Unknown well under the old overrun (allow generous slack for poll
    // granularity + machine load). Skipped if the corpus symlink is absent.
    let Some(text) = nia_file("mod.03") else {
        eprintln!("corpus absent — skipping");
        return;
    };
    let cfg = SolverConfig::new().with_timeout(Duration::from_secs(2));
    let start = Instant::now();
    let result = solve_smtlib(&text, &cfg)
        .expect("decides without error")
        .result;
    let elapsed = start.elapsed();
    assert!(
        matches!(result, CheckResult::Unknown(_)),
        "a 2s budget cannot decide mod.03 — expected a sound Unknown, got {result:?}"
    );
    assert!(
        elapsed < Duration::from_secs(8),
        "the NIA relaxation must honor the 2s budget (returned in {elapsed:?}, not run many seconds past it)"
    );
}
