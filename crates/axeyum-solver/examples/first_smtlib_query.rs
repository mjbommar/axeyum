//! Minimal command-faithful SMT-LIB model example used by the user guide.

use std::time::Duration;

use axeyum_ir::Value;
use axeyum_solver::{SolverConfig, solve_smtlib_get_model};

fn main() -> Result<(), Box<dyn std::error::Error>> {
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
