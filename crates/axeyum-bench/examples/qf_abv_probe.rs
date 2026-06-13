//! Eager array-elimination blow-up probe over real `QF_ABV` files (ADR-0010).
//!
//! For each SMT-LIB file argument, this parses it, eagerly eliminates arrays to
//! `QF_BV`, and reports the DAG-node count before and after elimination — the
//! measurement the roadmap calls for to decide whether the eager read-over-write
//! + Ackermann reduction blows up enough to justify a lazy array procedure.
//!
//! Run with:
//!
//! ```sh
//! cargo run -p axeyum-bench --example qf_abv_probe -- file1.smt2 file2.smt2 ...
//! ```

use std::env;
use std::fs;

use axeyum_ir::TermStats;
use axeyum_rewrite::eliminate_arrays;
use axeyum_smtlib::parse_script;

fn main() {
    let files: Vec<String> = env::args().skip(1).collect();
    if files.is_empty() {
        eprintln!("usage: qf_abv_probe <file.smt2> ...");
        return;
    }

    println!(
        "{:<44} {:>8} {:>10} {:>10} {:>7} status",
        "file", "asserts", "dag_in", "dag_out", "ratio"
    );
    println!("{}", "-".repeat(96));

    let mut parsed = 0usize;
    let mut eliminated_ok = 0usize;
    for path in &files {
        let short = short_name(path);
        let Ok(text) = fs::read_to_string(path) else {
            println!("{short:<44}   read-error");
            continue;
        };
        let mut script = match parse_script(&text) {
            Ok(script) => script,
            Err(error) => {
                println!("{short:<44}   parse: {error}");
                continue;
            }
        };
        parsed += 1;
        let asserts = script.assertions.len();
        let dag_in = TermStats::compute(&script.arena, &script.assertions).dag_nodes;

        match eliminate_arrays(&mut script.arena, &script.assertions) {
            Ok(elimination) => {
                eliminated_ok += 1;
                let out = elimination.assertions().to_vec();
                let dag_out = TermStats::compute(&script.arena, &out).dag_nodes;
                let ratio = ratio(dag_in, dag_out);
                let status = if elimination.had_arrays() {
                    "eliminated"
                } else {
                    "no-arrays"
                };
                println!(
                    "{short:<44} {asserts:>8} {dag_in:>10} {dag_out:>10} {ratio:>7.2} {status}"
                );
            }
            Err(error) => {
                println!("{short:<44} {asserts:>8} {dag_in:>10}   unsupported: {error}");
            }
        }
    }

    println!();
    println!(
        "parsed {parsed}/{} files; eliminated {eliminated_ok}/{parsed}",
        files.len()
    );
}

fn short_name(path: &str) -> String {
    let name = path.rsplit('/').next().unwrap_or(path);
    if name.len() <= 44 {
        name.to_owned()
    } else {
        format!("{}…", &name[..43])
    }
}

#[allow(clippy::cast_precision_loss)]
fn ratio(dag_in: u64, dag_out: u64) -> f64 {
    if dag_in == 0 {
        0.0
    } else {
        dag_out as f64 / dag_in as f64
    }
}
