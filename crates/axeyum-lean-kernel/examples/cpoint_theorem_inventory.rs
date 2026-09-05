//! Emit every declaration the `CPoint` prelude (`creal_point.rs` and its
//! submodules `angle.rs`, `isometry.rs`, `conic.rs`) admits, with its
//! canonical `render_lean` type -- the same shape as `nat_theorem_inventory`,
//! for a prelude no existing `*_theorem_inventory` example renders types for.
//!
//! `nat_theorem_inventory` builds only `Nat`; `prelude_theorem_inventory`
//! builds `cpoint` but prints the axiom footprint rather than the type; and
//! `kernel_declaration_projection` builds `cpoint` but its
//! `--require-declaration` is a presence check, not a renderer. A fact whose
//! `formal.statement` must be "the rendered type, verbatim" therefore had no
//! in-tree source for a `CPoint` theorem before this file.
//!
//! ```sh
//! cargo run -q --release -p axeyum-lean-kernel --example cpoint_theorem_inventory -- discriminant_rotate
//! ```
//!
//! Filter with the first argument, which matches as a substring; a filter
//! that matches nothing exits non-zero (asking for a declaration and finding
//! none is a failure, not an empty report), matching every other
//! `*_theorem_inventory` example.
//!
//! `--definitions` additionally emits `Definition`s. Every other inventory
//! example in this tree filters to `Declaration::Theorem` and says so; a
//! `CPoint.Conic.*` construction (`Conic.circle`, `Conic.rotate`, …) is a
//! `Definition`, so a fact whose evidence is a construction rather than a
//! theorem needs this flag. It is opt-in so the default output means the same
//! thing here as everywhere else.
//!
//! `--release` is MANDATORY: this builds `creal` and `cpoint`, which recurse
//! deep enough that the debug kernel is measured up to 32x slower on proof
//! terms of this size.

use std::process::ExitCode;

use axeyum_lean_kernel::{Declaration, Kernel, build_cpoint_prelude, on_a_deep_stack};

fn main() -> ExitCode {
    on_a_deep_stack(run)
}

fn run() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut filter = String::new();
    let mut definitions = false;
    for arg in &args {
        match arg.as_str() {
            "--definitions" => definitions = true,
            other if other.starts_with("--") => {
                eprintln!("error: unknown flag {other:?}");
                return ExitCode::FAILURE;
            }
            other => other.clone_into(&mut filter),
        }
    }

    let mut kernel = Kernel::new();
    let _ = build_cpoint_prelude(&mut kernel).expect("CPoint prelude must build");

    let mut rows: Vec<(String, &'static str, String)> = kernel
        .environment()
        .iter()
        .filter_map(|(_, declaration)| {
            let (name, ty, kind) = match declaration {
                Declaration::Theorem { name, ty, .. } => (*name, *ty, "theorem"),
                Declaration::Definition { name, ty, .. } if definitions => {
                    (*name, *ty, "definition")
                }
                _ => return None,
            };
            let name = kernel.display_name(name).to_string();
            (filter.is_empty() || name.contains(&filter))
                .then(|| (name, kind, kernel.render_lean(ty)))
        })
        .collect();
    rows.sort();

    for (name, kind, ty) in &rows {
        println!("{name}\t{kind}\t{ty}");
    }
    eprintln!("{} declarations", rows.len());

    if !filter.is_empty() && rows.is_empty() {
        eprintln!(
            "error: no CPoint declaration matches {filter:?} -- an absent \
             declaration is a failed check, not an empty report"
        );
        return ExitCode::FAILURE;
    }
    ExitCode::SUCCESS
}
