//! Print what the cell-covering checker EXAMINED on an `unsat` from the
//! single-cell route, for one SMT-LIB file (ADR-2126).
//!
//! # Why this exists
//!
//! ADR-2126 replaced a sampling delineability check with an exact one, and the
//! route's two `unsat` verdicts on the QF_NRA A/B survive the change. "Survive"
//! is only interesting if the exact check RAN on them: check 6a is skipped on a
//! POINT cell, which needs no generalisation, so a refutation whose every
//! `Deeper` cell is a point cell would pass the exact checker without exercising
//! a single exact test. That would make "the exact check accepts it" a true
//! statement about a check that did nothing.
//!
//! This prints `open_deeper_cells` and `delineability_exact_tests` beside the
//! verdict, so the claim can be read instead of assumed.
//!
//! ```text
//! cargo run --release -p axeyum-solver --features full \
//!     --example nra_cell_check_stats -- FILE.smt2
//! ```

fn main() {
    let path = match std::env::args().nth(1) {
        Some(p) => p,
        None => {
            eprintln!("usage: nra_cell_check_stats FILE.smt2");
            std::process::exit(2);
        }
    };
    let text = match std::fs::read_to_string(&path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("read {path}: {e}");
            std::process::exit(2);
        }
    };
    let parsed = match axeyum_smtlib::parse_script(&text) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("parse {path}: {e:?}");
            std::process::exit(2);
        }
    };

    let out = axeyum_solver::single_cell_decide_for_testing(&parsed.arena, &parsed.assertions);
    let verdict = match &out {
        None => format!("declined:{}", axeyum_solver::single_cell_decline_cause()),
        Some(axeyum_solver::CheckResult::Sat(_)) => "sat".to_owned(),
        Some(axeyum_solver::CheckResult::Unsat) => "unsat".to_owned(),
        Some(axeyum_solver::CheckResult::Unknown(_)) => "unknown".to_owned(),
    };
    match axeyum_solver::single_cell_last_check() {
        Some(s) => println!(
            "{verdict}\tcoverings={}\tcells={}\tatom_cells={}\tdeeper={}\t\
             open_deeper={}\tpoint_deeper={}\texact_tests={}\tprobes={}\tmax_level={}\t{path}",
            s.coverings,
            s.cells,
            s.atom_cells,
            s.deeper_cells,
            s.open_deeper_cells,
            s.point_deeper_cells,
            s.delineability_exact_tests,
            s.delineability_probes,
            s.max_level,
        ),
        None => println!("{verdict}\t(no certificate check recorded)\t{path}"),
    }
}
