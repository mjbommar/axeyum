//! Emit the integer prelude's `Int.*` declarations — what is **derived** and
//! what is still **asserted** — with canonical types and per-declaration axiom
//! footprints.
//!
//! The sibling `nat_theorem_inventory` exists because the theorem population
//! cannot be read from source text: declarations go through helpers taking
//! interned `NameId` fields, so grepping returns zero. The integer development
//! has the same problem plus a second one this example is really about — the
//! `Int` prelude now holds *both* kinds of declaration, so "what does ℤ still
//! assume" is no longer answerable by naming the file. A row here is a theorem
//! exactly when its `kind` says `theorem`, and its footprint column is
//! `Kernel::axiom_footprint`, this kernel's `#print axioms`.
//!
//! An empty footprint on a `theorem` row is the ledger-grade claim: that law is
//! derived from the axiom-free `Nat` development and rests on nothing. On an
//! `axiom` row the footprint is the declaration itself, which is what Lean's
//! `#print axioms` reports for an assumption and is why a fact citing one may
//! not write `axiom_footprint: []`.
//!
//! Output: `kind<TAB>name<TAB>footprint<TAB>canonical-type`, sorted by name,
//! rendered as Lean-ish text meant to be pasted into a `formal.statement`.
//!
//! Filter with the first argument, which matches as a substring:
//!
//! ```sh
//! cargo run -q -p axeyum-lean-kernel --example int_theorem_inventory -- add_neg
//! ```
//!
//! # Asking for a declaration and finding none is a FAILURE
//!
//! Like `nat_theorem_inventory`, this backs fact-ledger `checker_command`s and
//! until 2026-08-15 exited **0** for a name that does not exist, so a deleted
//! theorem would have read as a re-derived fact. A named filter matching nothing
//! now exits non-zero.
//!
//! `--expect-derived <n>` / `--expect-asserted <n>` pin the split (51 derived,
//! 1 asserted as measured 2026-08-15) and fail on drift in either direction —
//! a *growth* in the asserted count is the one that matters most, since it means
//! something previously proved is now assumed.

use std::process::ExitCode;

use axeyum_lean_kernel::{Declaration, Kernel, build_int_prelude};

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut filter = String::new();
    let mut expect_derived: Option<usize> = None;
    let mut expect_asserted: Option<usize> = None;
    let mut iter = args.iter();
    while let Some(arg) = iter.next() {
        let mut number = |flag: &str| -> Option<usize> {
            let raw = iter.next()?;
            let Ok(value) = raw.parse() else {
                eprintln!("error: {flag} expects a number, got {raw:?}");
                return None;
            };
            Some(value)
        };
        match arg.as_str() {
            "--expect-derived" => match number("--expect-derived") {
                Some(value) => expect_derived = Some(value),
                None => return ExitCode::FAILURE,
            },
            "--expect-asserted" => match number("--expect-asserted") {
                Some(value) => expect_asserted = Some(value),
                None => return ExitCode::FAILURE,
            },
            other if other.starts_with("--") => {
                eprintln!("error: unknown flag {other:?}");
                return ExitCode::FAILURE;
            }
            other => other.clone_into(&mut filter),
        }
    }

    let mut kernel = Kernel::new();
    let _ = build_int_prelude(&mut kernel).expect("Int prelude must build");

    let mut rows: Vec<(String, &'static str, String, String)> = kernel
        .environment()
        .iter()
        .filter_map(|(_, declaration)| {
            let (kind, name, ty) = match declaration {
                Declaration::Theorem { name, ty, .. } => ("theorem", name, ty),
                Declaration::Axiom { name, ty, .. } => ("axiom", name, ty),
                _ => return None,
            };
            let rendered = kernel.display_name(*name).to_string();
            // `Int.` only: the environment also carries the whole `Nat`
            // development the construction rests on, which its own inventory
            // already covers.
            if !rendered.starts_with("Int.") && rendered != "Int" {
                return None;
            }
            if !filter.is_empty() && !rendered.contains(&filter) {
                return None;
            }
            let footprint = kernel
                .axiom_footprint(*name)
                .into_iter()
                .map(|a| kernel.display_name(a).to_string())
                .collect::<Vec<_>>()
                .join(",");
            Some((rendered, kind, footprint, kernel.render_lean(*ty)))
        })
        .collect();
    rows.sort();

    for (name, kind, footprint, ty) in &rows {
        println!("{kind}\t{name}\t{footprint}\t{ty}");
    }

    let derived = rows.iter().filter(|(_, k, _, _)| *k == "theorem").count();
    let asserted = rows.len() - derived;
    let axiom_free = rows
        .iter()
        .filter(|(_, k, f, _)| *k == "theorem" && f.is_empty())
        .count();
    eprintln!(
        "Int: {derived} derived ({axiom_free} with an EMPTY axiom footprint), {asserted} still \
         asserted"
    );

    let mut failed = false;
    if !filter.is_empty() && rows.is_empty() {
        eprintln!(
            "error: no Int declaration matches {filter:?} -- an absent \
             declaration is a failed check, not an empty report"
        );
        failed = true;
    }
    for (label, expected, found) in [
        ("--expect-derived", expect_derived, derived),
        ("--expect-asserted", expect_asserted, asserted),
    ] {
        if let Some(expected) = expected
            && expected != found
        {
            eprintln!("error: {label} {expected}, found {found}");
            failed = true;
        }
    }
    if failed {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}
