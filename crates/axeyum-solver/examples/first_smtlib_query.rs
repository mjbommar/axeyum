//! Minimal command-faithful SMT-LIB model example used by the user guide.
//!
//! It solves ONE fixed query and takes no arguments. That is deliberate — it is a
//! doc example, not a driver — but until 2026-08-22 it also *ignored* any it was
//! given, and that combination is a trap rather than a limitation.
//!
//! Measured that day: an agent looking for a way to run a `.smt2` file passed one
//! here, got `sat` with a model in about a second, compared it against z3's
//! `unsat` on that file, and reported a P0 wrong-`sat` in axeyum's
//! floating-point route. There is no such defect. The example never opened the
//! file; `sat` and `x = (_ bv255 8)` are this query's own answer and it prints
//! them for any argument, including a path that does not exist.
//!
//! This is the repository's own recurring failure with the sign flipped: a tool
//! that was never pointed at your subject usually returns an empty answer
//! indistinguishable from a strong negative result, and here it returned a
//! CONFIDENT one. So the example now refuses arguments instead of ignoring them,
//! and names the drivers that do read a file.
//!
//! To actually solve a file: `axeyum_cli` or `smtcomp_cli` in `axeyum-bench`.

use std::time::Duration;

use axeyum_ir::Value;
use axeyum_solver::{SolverConfig, solve_smtlib_get_model};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Fail closed on arguments. Ignoring them let a fabricated soundness report
    // be written up and committed; refusing them costs four lines.
    let extra: Vec<String> = std::env::args().skip(1).collect();
    if !extra.is_empty() {
        return Err(format!(
            "first_smtlib_query takes no arguments and solves one fixed query; it \
             cannot read {extra:?}. Its output describes the built-in query ONLY, \
             so comparing it against another solver's answer on a file compares \
             two different problems. To solve a file, use `cargo run -p \
             axeyum-bench --example axeyum_cli -- <file.smt2>` or the SMT-COMP \
             driver `smtcomp_cli`."
        )
        .into());
    }

    let query = r"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= (bvadd x #x01) #x00))
        (check-sat)
        (get-model)
    ";

    let config = SolverConfig::new().with_timeout(Duration::from_secs(5));
    let model = solve_smtlib_get_model(query, &config)?
        .ok_or("the example query did not produce a satisfiable model")?;

    println!("sat");
    for (name, value) in model.constants {
        match value {
            Value::Bv { width, value } => println!("{name} = (_ bv{value} {width})"),
            other => println!("{name} = {other}"),
        }
    }

    Ok(())
}
