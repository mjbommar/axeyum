//! Emit every theorem the `List`/`List`-`Nat`-bridge/`List.Perm` preludes
//! admit, with its canonical type — the `List` twin of `nat_theorem_
//! inventory` (see that file's own doc for why this exists: a fact ledger
//! entry needs the proposition *as the kernel admitted it*, not a
//! transcription from a doc comment).
//!
//! Builds `build_list_nat_bridge` (which also builds `build_list_prelude`
//! and `build_nat_prelude`) and then `build_list_perm` on top, so the
//! reported theorems include everything from `list_prelude.rs`/`theorems.rs`
//! /`bridge.rs`/`perm.rs` — `List.count_toMultiset` through `List.Perm`'s
//! four theorems, added 2026-09-03 (`list-carrier-2`). Filter with the first
//! argument (substring match); an unfiltered run lists everything.
//!
//! ```sh
//! cargo run -q -p axeyum-lean-kernel --example list_theorem_inventory -- append_assoc
//! ```
//!
//! Asking for a theorem and finding none is a FAILURE (a named filter that
//! matches nothing exits non-zero), matching `nat_theorem_inventory`'s own
//! rule: a tool never pointed at its subject must not look like a negative
//! result.

use std::process::ExitCode;

use axeyum_lean_kernel::{Declaration, Kernel, build_list_nat_bridge, build_list_perm};

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut filter = String::new();
    let mut expect_count: Option<usize> = None;
    let mut iter = args.iter();
    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--expect-count" => {
                let Some(raw) = iter.next() else {
                    eprintln!("error: --expect-count needs a number");
                    return ExitCode::FAILURE;
                };
                let Ok(value) = raw.parse() else {
                    eprintln!("error: --expect-count expects a number, got {raw:?}");
                    return ExitCode::FAILURE;
                };
                expect_count = Some(value);
            }
            other if other.starts_with("--") => {
                eprintln!("error: unknown flag {other:?}");
                return ExitCode::FAILURE;
            }
            other => other.clone_into(&mut filter),
        }
    }

    let mut kernel = Kernel::new();
    let (list_prelude, nat_prelude, bridge) =
        build_list_nat_bridge(&mut kernel).expect("List/Nat bridge must build");
    let _ = build_list_perm(&mut kernel, &list_prelude, &nat_prelude, &bridge)
        .expect("List.Perm must build");

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

    let mut failed = false;
    if !filter.is_empty() && rows.is_empty() {
        eprintln!(
            "error: no List theorem matches {filter:?} -- an absent theorem is a \
             failed check, not an empty report"
        );
        failed = true;
    }
    if let Some(expected) = expect_count
        && rows.len() != expected
    {
        eprintln!(
            "error: expected {expected} theorems, found {} (drift in either \
             direction is a failure: a shrink means something previously proved \
             is gone, a growth means the expectation is stale)",
            rows.len()
        );
        failed = true;
    }
    if failed {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}
