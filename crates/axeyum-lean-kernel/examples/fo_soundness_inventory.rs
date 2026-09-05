//! Emit every declaration the first-order model theory package (`fo_*.rs`,
//! ADR-1636) adds on top of the `Nat` prelude, with its kind, axiom footprint,
//! and canonical type.
//!
//! This is the `checker_command` for the `F:fo-*` facts, and — like
//! `ipc_soundness_inventory`, which it is modelled on — it is built to **fail
//! on absence** rather than report an empty set. A named filter matching
//! nothing exits non-zero, so deleting `FO.soundness` from the kernel turns the
//! fact's evidence red instead of leaving it green with nothing to say.
//!
//! # Why it does not filter to `Declaration::Theorem`
//!
//! `prelude_theorem_inventory` lists theorems only, so it returns **zero rows**
//! for `Nat.add` and would return zero for `FO.sat`, `FO.Term.eval` and
//! `FO.natStructure` — all `Definition`s that certainly exist. Asking a theorem
//! inventory whether a definition exists gets a confident wrong answer in both
//! directions. This one lists every kind and prints the kind in its own column.
//!
//! # Why the row set is derived rather than listed
//!
//! A hand-maintained list measures the maintainer's memory, not the
//! environment. The rows here are exactly the names present after
//! `build_fo_soundness_prelude` and absent after `build_nat_prelude` alone — a
//! set difference against the authority, recomputed on every run, so a
//! declaration nobody remembered to list still appears and one that disappears
//! still vanishes from the report.
//!
//! ```sh
//! # everything the package declares
//! cargo run -q --release -p axeyum-lean-kernel --example fo_soundness_inventory
//!
//! # a fact's own check: the named theorem must exist AND rest on no axiom
//! cargo run -q --release -p axeyum-lean-kernel --example fo_soundness_inventory \
//!   -- FO.soundness --exact --require-axiom-free
//! ```
//!
//! `--exact` matches the whole name rather than a substring. Without it,
//! `FO.sat` also matches `FO.sat_congr`, `FO.sat_subst`, `FO.sat_shift` and
//! `FO.sat_inst`, which is the right behaviour when checking a family and the
//! wrong one when checking a single declaration.
//!
//! Output is `name<TAB>kind<TAB>axioms=<n><TAB>canonical-type`, sorted by name.

use std::collections::BTreeSet;
use std::process::ExitCode;

use axeyum_lean_kernel::{Declaration, Kernel, build_fo_soundness_prelude, build_nat_prelude};

fn kind_of(declaration: &Declaration) -> &'static str {
    match declaration {
        Declaration::Definition { .. } => "definition",
        Declaration::Theorem { .. } => "theorem",
        Declaration::Axiom { .. } => "axiom",
        Declaration::Opaque { .. } => "opaque",
        Declaration::Inductive { .. } => "inductive",
        Declaration::Constructor { .. } => "constructor",
        Declaration::Recursor { .. } => "recursor",
        // Named rather than left to a wildcard on purpose: `Axiom` alone is not
        // the trusted surface -- `Opaque` has no proof body and `Quotient`
        // admits `Quot.sound`, so all three have to be visible in the kind
        // column for a reader to check the axiom-freedom claim themselves.
        Declaration::Quotient { .. } => "quotient",
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut filter = String::new();
    let mut exact = false;
    let mut require_axiom_free = false;
    let mut expect_count: Option<usize> = None;
    let mut iter = args.iter();
    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--require-axiom-free" => require_axiom_free = true,
            "--exact" => exact = true,
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

    // The baseline the package is measured against. Everything below is a set
    // difference against this, so nothing has to be listed by hand.
    let baseline: BTreeSet<String> = {
        let mut kernel = Kernel::new();
        let _ = build_nat_prelude(&mut kernel).expect("Nat prelude must build");
        kernel
            .environment()
            .iter()
            .map(|(_, declaration)| kernel.display_name(declaration.name()).to_string())
            .collect()
    };

    let mut kernel = Kernel::new();
    let _ = build_fo_soundness_prelude(&mut kernel).expect("FO soundness prelude must build");

    let mut rows: Vec<(String, &'static str, usize, String)> = kernel
        .environment()
        .iter()
        .map(|(_, declaration)| {
            let name_id = declaration.name();
            let name = kernel.display_name(name_id).to_string();
            (name, kind_of(declaration), name_id, declaration.ty())
        })
        .filter(|(name, _, _, _)| !baseline.contains(name))
        .filter(|(name, _, _, _)| {
            filter.is_empty()
                || if exact {
                    *name == filter
                } else {
                    name.contains(&filter)
                }
        })
        .map(|(name, kind, name_id, ty)| {
            let axioms = kernel.axiom_footprint(name_id).len();
            let rendered = kernel.render_lean(ty);
            (name, kind, axioms, rendered)
        })
        .collect();
    rows.sort();

    for (name, kind, axioms, ty) in &rows {
        println!("{name}\t{kind}\taxioms={axioms}\t{ty}");
    }
    eprintln!("{} FO declarations", rows.len());

    let mut failed = false;
    if !filter.is_empty() && rows.is_empty() {
        eprintln!(
            "error: no FO declaration matches {filter:?} -- an absent \
             declaration is a failed check, not an empty report"
        );
        failed = true;
    }
    if require_axiom_free {
        let assuming: Vec<&String> = rows
            .iter()
            .filter(|(_, _, axioms, _)| *axioms != 0)
            .map(|(name, _, _, _)| name)
            .collect();
        if assuming.is_empty() {
            eprintln!("axiom-free: yes ({} declarations checked)", rows.len());
        } else {
            eprintln!("error: these declarations rest on axioms: {assuming:?}");
            failed = true;
        }
    }
    if let Some(expected) = expect_count
        && rows.len() != expected
    {
        eprintln!(
            "error: expected {expected} declarations, found {} (drift in \
             either direction is a failure)",
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
