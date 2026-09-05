//! Emit every theorem `Metric.prod`'s prelude (`metric_prod.rs`) admits, with
//! its canonical `render_lean` type -- the same shape as `nat_theorem_inventory`,
//! for a prelude `kernel_declaration_projection` does not build (it stops at
//! `build_metric_prelude`; `Metric.prod`/`Metric.prod_complete`/... are a
//! separate lane's file on top of it).
//!
//! ```sh
//! cargo run -q --release -p axeyum-lean-kernel --example metric_prod_theorem_inventory -- prod_complete
//! ```
//!
//! Filter with the first argument, which matches as a substring; a filter
//! that matches nothing exits non-zero (asking for a theorem and finding none
//! is a failure, not an empty report), matching every other `*_theorem_inventory`
//! example.

use std::process::ExitCode;

use axeyum_lean_kernel::{Declaration, Kernel, build_metric_prod_prelude, on_a_deep_stack};

fn main() -> ExitCode {
    on_a_deep_stack(run)
}

fn run() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let filter = args.first().cloned().unwrap_or_default();

    let mut kernel = Kernel::new();
    let _ = build_metric_prod_prelude(&mut kernel).expect("Metric.prod prelude must build");

    let mut rows: Vec<(String, usize, String)> = kernel
        .environment()
        .iter()
        .filter_map(|(_, declaration)| match declaration {
            Declaration::Theorem { name, ty, .. } => {
                let name = kernel.display_name(*name).to_string();
                (filter.is_empty() || name.contains(&filter))
                    .then(|| (name, 0usize, kernel.render_lean(*ty)))
            }
            _ => None,
        })
        .collect();
    rows.sort();

    for (name, _, ty) in &rows {
        let binders = ty.matches("->").count();
        println!("{name}\t{binders}\t{ty}");
    }
    eprintln!("{} theorems", rows.len());

    if !filter.is_empty() && rows.is_empty() {
        eprintln!(
            "error: no Metric.prod theorem matches {filter:?} -- an absent theorem is a \
             failed check, not an empty report"
        );
        return ExitCode::FAILURE;
    }
    ExitCode::SUCCESS
}
