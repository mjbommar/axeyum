//! TEMPORARY exploration harness.
#![cfg(feature = "full")]

use std::path::{Path, PathBuf};
use std::time::Duration;

use axeyum_solver::{RouteAttributionGuard, SolverConfig, last_route_attribution, solve_smtlib};

fn files() -> Vec<PathBuf> {
    let root =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/regression/uflia_induction");
    let mut v: Vec<PathBuf> = std::fs::read_dir(&root)
        .unwrap()
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|e| e == "smt2"))
        .collect();
    v.sort();
    v
}

#[test]
fn dump() {
    let cfg = SolverConfig {
        timeout: Some(Duration::from_millis(10_000)),
        ..SolverConfig::default()
    };
    for f in files() {
        let text = std::fs::read_to_string(&f).unwrap();
        let guard = RouteAttributionGuard::enable();
        let r = solve_smtlib(&text, &cfg);
        drop(guard);
        let trace = last_route_attribution();
        let verdict = match &r {
            Ok(o) => format!("{:?}", std::mem::discriminant(&o.result)),
            Err(e) => format!("err {e}"),
        };
        let decided = trace
            .decided_by()
            .map(|(_, a, _)| a.route.to_string())
            .unwrap_or_else(|| "<none>".to_owned());
        eprintln!(
            "--- {} verdict={verdict} decided_by={decided}",
            f.file_name().unwrap().to_string_lossy()
        );
        for a in trace.attempts() {
            eprintln!("      {a}");
        }
    }
}
