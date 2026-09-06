//! Emit the rational prelude's `Rat.*` declarations — what is **derived** and
//! what is still **asserted** — with canonical types and per-declaration axiom
//! footprints.
//!
//! The ℚ member of the family `nat_theorem_inventory` and `int_theorem_inventory`
//! already cover for ℕ and ℤ. It exists because ℚ did not have one: measured
//! 2026-09-05, `prelude_theorem_inventory` counts `rat` but prints no types,
//! `theorem_dependency_inventory` prints dependency edges but no types, and
//! `shape_search --name` prints a hypothesis-head summary, not a canonical type.
//! So the only route to a `formal.statement` for a `Rat` theorem was an
//! out-of-tree probe crate — which is exactly what the provenance block of the
//! existing `F:rat-*` facts records having been built, used and deleted, leaving
//! their `checker_command` unable to re-derive the field it filled in.
//!
//! Output: `kind<TAB>name<TAB>footprint<TAB>canonical-type`, sorted by name,
//! rendered as Lean-ish text meant to be pasted into a `formal.statement`.
//!
//! Filter with the first non-flag argument, which matches as a substring:
//!
//! ```sh
//! cargo run -q --release -p axeyum-lean-kernel --example rat_theorem_inventory \
//!   -- two_mul_le_sq_add_sq
//! ```
//!
//! `--release` is recommended rather than mandatory here: this binary builds
//! `logic`/`nat`/`int`/`rat` and no constructed prelude, so it does not hit the
//! deep-recursion ceiling `prelude_theorem_inventory --include-constructed`
//! does. It is still several minutes slower in a debug build.
//!
//! # Asking for a declaration and finding none is a FAILURE
//!
//! Like both siblings, a named filter matching nothing exits **non-zero**. A
//! deleted or renamed theorem must not read as a re-derived one — that regression
//! is the reason both siblings were changed on 2026-08-15, and it is designed in
//! here rather than discovered later.
//!
//! `--expect-derived <n>` / `--expect-asserted <n>` pin the split. The asserted
//! count is the one worth watching: ℚ is measured at **0** asserted, and a
//! growth there means something previously proved is now assumed.

use std::process::ExitCode;

use axeyum_lean_kernel::{Declaration, Kernel, build_rat_prelude, on_a_deep_stack};

fn main() -> ExitCode {
    on_a_deep_stack(run)
}

fn run() -> ExitCode {
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
    let _ = build_rat_prelude(&mut kernel).expect("Rat prelude must build");

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
            // `Rat.` only: the environment also carries the whole `Nat` and
            // `Int` development ℚ is constructed over, and both have their own
            // inventory.
            if !rendered.starts_with("Rat.") && rendered != "Rat" {
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
        "Rat: {derived} derived ({axiom_free} with an EMPTY axiom footprint), {asserted} still \
         asserted"
    );

    let mut failed = false;
    if !filter.is_empty() && rows.is_empty() {
        eprintln!(
            "error: no Rat declaration matches {filter:?} -- an absent \
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
