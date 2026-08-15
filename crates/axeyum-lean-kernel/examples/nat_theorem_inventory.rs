//! Emit every theorem the Nat prelude admits, with its canonical type.
//!
//! There was no way to read this without building the environment.  The
//! declarations go through a `.theorem(name, ..)` helper taking an interned
//! `NameId` field (`p.add_comm`), not a string literal, so grepping the source
//! for `.theorem("...")` returns **zero matches** and grepping for
//! `Declaration::Theorem` returns 1 — the helper — against 119 real theorems.
//! Two separate lanes miscounted this repository's theorems from source text
//! before anyone built the environment to look.
//!
//! The cost of that gap was not just miscounting.  A fact ledger entry has to
//! carry the proposition *as the kernel admitted it*, and with no inventory the
//! only route was transcribing from doc comments — which produced three seed
//! facts with statements the kernel would reject, two of them unparseable, and
//! sent one extraction lane off to build an out-of-tree probe crate.  Dumping
//! `render_lean` of the admitted type removes the transcription step entirely.
//!
//! Output: `name<TAB>arity<TAB>canonical-type`, sorted by name, rendered as
//! Lean-ish text rather than hex — this one is meant to be read and pasted into
//! a `formal.statement`, not hashed.  For the hash-bound trusted-surface
//! inventory see `nat_axiom_inventory`.
//!
//! Filter with the first argument, which matches as a substring:
//!
//! ```sh
//! cargo run -q -p axeyum-lean-kernel --example nat_theorem_inventory -- add_comm
//! ```
//!
//! # Asking for a theorem and finding none is a FAILURE
//!
//! This example is the `checker_command` of a large family of fact-ledger
//! entries (`F:nat-add-comm` is backed by `-- add_comm`). Until 2026-08-15 it
//! printed `0 theorems` and exited **0** for a name that does not exist, so
//! deleting a theorem from the kernel would have left
//! `scripts/check-fact-evidence-replay.sh` reporting the fact re-derived. A
//! named filter that matches nothing now exits non-zero; a bare run that lists
//! everything still exits 0, because an unfiltered inventory has no expectation
//! to violate.
//!
//! `--expect-count <n>` pins the total (119 as measured 2026-08-15) and fails on
//! drift in **either** direction: a shrink means something previously proved is
//! gone, a growth means the pinned number is stale.

use std::process::ExitCode;

use axeyum_lean_kernel::{Declaration, Kernel, build_nat_prelude};

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
    let _ = build_nat_prelude(&mut kernel).expect("Nat prelude must build");

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
        // The binder count is read off the rendered telescope rather than the
        // expression, so it describes exactly what a consumer pasting this
        // string will see.
        let binders = ty.matches("->").count();
        println!("{name}\t{binders}\t{ty}");
    }
    eprintln!("{} theorems", rows.len());

    let mut failed = false;
    if !filter.is_empty() && rows.is_empty() {
        eprintln!(
            "error: no Nat theorem matches {filter:?} -- an absent theorem is a \
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
