//! Emit every declaration `Top.*`'s prelude (`top_frame.rs`) admits, with its
//! canonical `render_lean` type and the SIZE OF ITS AXIOM FOOTPRINT — the same
//! shape as `metric_prod_theorem_inventory`, for a prelude
//! `kernel_declaration_projection` does not build.
//!
//! ```sh
//! cargo run -q --release -p axeyum-lean-kernel --example top_frame_theorem_inventory -- frame_law
//! cargo run -q --release -p axeyum-lean-kernel --example top_frame_theorem_inventory -- --defs Opens
//! ```
//!
//! Columns are TAB-separated: `kind`, `name`, `binders`, `footprint`,
//! `rendered type`. `kind` is `theorem` or `def`; `--defs` adds the `def` rows,
//! which are omitted by default because every other `*_theorem_inventory`
//! example lists theorems only and a caller who forgets that reads a false
//! ABSENT for `Nat.add`-shaped names.
//!
//! **The exit status depends on the finding.** A filter that matches nothing
//! exits non-zero — asking for a declaration and finding none is a failure, not
//! an empty report — and so does a nonempty axiom footprint on any row that was
//! printed, because the headline claim about this prelude is that it has none.
//!
//! `--release` is MANDATORY: this binary builds `creal` underneath `Top`, which
//! overflows the default debug thread stack.

use std::process::ExitCode;

use axeyum_lean_kernel::{Declaration, Kernel, build_top_frame_prelude, on_a_deep_stack};

fn main() -> ExitCode {
    on_a_deep_stack(run)
}

fn run() -> ExitCode {
    let mut with_defs = false;
    let mut filter = String::new();
    for arg in std::env::args().skip(1) {
        if arg == "--defs" {
            with_defs = true;
        } else if filter.is_empty() {
            filter = arg;
        } else {
            eprintln!("error: at most one filter argument (got a second: {arg:?})");
            return ExitCode::FAILURE;
        }
    }

    let mut kernel = Kernel::new();
    let _ = build_top_frame_prelude(&mut kernel).expect("Top.Frame prelude must build");

    let mut rows: Vec<(String, String, usize, usize, String)> = Vec::new();
    for (_, declaration) in kernel.environment().iter() {
        let (kind, name, ty) = match declaration {
            Declaration::Theorem { name, ty, .. } => ("theorem", *name, *ty),
            Declaration::Definition { name, ty, .. } if with_defs => ("def", *name, *ty),
            _ => continue,
        };
        let rendered_name = kernel.display_name(name).to_string();
        if rendered_name != "Top" && !rendered_name.starts_with("Top.") {
            continue;
        }
        if !filter.is_empty() && !rendered_name.contains(&filter) {
            continue;
        }
        let rendered_ty = kernel.render_lean(ty);
        let binders = rendered_ty.matches("->").count();
        let footprint = kernel.axiom_footprint(name).len();
        rows.push((
            rendered_name,
            kind.to_owned(),
            binders,
            footprint,
            rendered_ty,
        ));
    }
    rows.sort();

    let mut dirty = 0usize;
    for (name, kind, binders, footprint, ty) in &rows {
        println!("{kind}\t{name}\t{binders}\t{footprint}\t{ty}");
        if *footprint != 0 {
            dirty += 1;
        }
    }
    eprintln!(
        "{} row(s), {} with a nonempty axiom footprint",
        rows.len(),
        dirty
    );

    if rows.is_empty() {
        eprintln!(
            "error: no Top declaration matches {filter:?} -- an absent declaration is a \
             failed check, not an empty report"
        );
        return ExitCode::FAILURE;
    }
    if dirty != 0 {
        eprintln!("error: {dirty} printed row(s) carry an axiom footprint");
        return ExitCode::FAILURE;
    }
    ExitCode::SUCCESS
}
