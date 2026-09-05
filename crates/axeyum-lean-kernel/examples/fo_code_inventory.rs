//! Emit every declaration the arithmetization package (`fo_code.rs`,
//! `fo_numbering.rs`, ADR-1640) adds on top of the `Nat` prelude, with its
//! kind, axiom footprint, and canonical type.
//!
//! This is the `checker_command` for the `F:fo-code-*` facts. It is a sibling
//! of `fo_soundness_inventory` rather than an extension of it, because the two
//! packages are two chains off the same `fo_syntax.rs` root and neither
//! `build_fo_syntax_prelude` nor `build_fo_semantics_prelude` is cached — so
//! building both in ONE kernel would re-admit `FO.Term` and be rejected as a
//! duplicate name. Reported separately, each package's set difference is still
//! taken against the same `build_nat_prelude` baseline, so the two reports
//! partition cleanly on their shared `FO.Term`/`FO.Formula` rows.
//!
//! Like its sibling it is built to **fail on absence** rather than report an
//! empty set: a named filter matching nothing exits non-zero, so deleting
//! `FO.Formula.code_injective` from the kernel turns the fact's evidence red
//! instead of leaving it green with nothing to say.
//!
//! It does not filter to `Declaration::Theorem`, for the reason
//! `fo_soundness_inventory` gives: `prelude_theorem_inventory` returns zero
//! rows for a `Definition`, and `FO.Code.pair`, `FO.Code.unpair`,
//! `FO.Term.code` and `FO.Formula.code` are all definitions. Every kind is
//! listed and the kind is printed in its own column.
//!
//! The row set is **derived**, not listed: the rows are exactly the names
//! present after `build_fo_numbering_prelude` and absent after
//! `build_nat_prelude` alone. A declaration nobody remembered to list still
//! appears, and one that disappears still vanishes.
//!
//! ```sh
//! # everything the package declares
//! cargo run -q --release -p axeyum-lean-kernel --example fo_code_inventory
//!
//! # a fact's own check: the named theorem must exist AND rest on no axiom
//! cargo run -q --release -p axeyum-lean-kernel --example fo_code_inventory \
//!   -- FO.Formula.code_injective --exact --require-axiom-free
//! ```
//!
//! `--exact` matches the whole name rather than a substring. Without it,
//! `FO.Code.pair` also matches `FO.Code.pair_succ`, `FO.Code.pair_zero_succ`,
//! `FO.Code.pair_inj_left` and `FO.Code.pair_inj_right`, which is right when
//! checking a family and wrong when checking one declaration.
//!
//! Output is `name<TAB>kind<TAB>axioms=<n><TAB>canonical-type`, sorted by name.

use std::collections::BTreeSet;
use std::process::ExitCode;

use axeyum_lean_kernel::{Declaration, Kernel, build_fo_numbering_prelude, build_nat_prelude};

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

// The argument parsing, the set difference, the three exit conditions and the
// row rendering are one linear pipeline; splitting it into helpers to satisfy
// `too_many_lines` would spread the exit conditions across functions, which is
// the opposite of what a checker whose whole contract is "fails on absence"
// wants.
#[allow(clippy::too_many_lines)]
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
    let _ = build_fo_numbering_prelude(&mut kernel).expect("FO numbering prelude must build");

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
    eprintln!("{} FO arithmetization declarations", rows.len());

    let mut failed = false;
    if !filter.is_empty() && rows.is_empty() {
        eprintln!(
            "error: no FO arithmetization declaration matches {filter:?} -- an \
             absent declaration is a failed check, not an empty report"
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
