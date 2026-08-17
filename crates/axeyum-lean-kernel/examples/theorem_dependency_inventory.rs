//! Emit, per admitted theorem, the theorems its statement and proof directly use.
//!
//! This exists to make the fact ledger's `depends_on` **derivable** rather than
//! transcribed — the position ADR-0465 already settled for the axiom ledger.
//!
//! # Why it is needed
//!
//! CLAUDE.md's flywheel ends with *"the concept DAG and the fact ledger say what
//! to prove next"*, and that arrow is `depends_on`. Measured 2026-08-17 by
//! `scripts/check-fact-dag.py`: of 109 facts, **65 declare no dependency and have
//! no dependent**, so proving one usually unlocks nothing. Some of that isolation
//! is honest — an SMT-LIB propositional refutation genuinely does not rest on a
//! Nat lemma — but 13 of the isolated facts are `kernel-lean`, and a kernel-route
//! proposition whose proof cites prelude theorems while declaring none is simply
//! unrecorded. Nothing could tell the two cases apart, because the information
//! lived only in the proof term.
//!
//! It was already being computed and discarded. `Kernel::axiom_footprint` walks
//! the whole constant closure and then keeps only `Axiom` / `Opaque` / `Quotient`;
//! `Kernel::theorem_dependencies` keeps the other half.
//!
//! # What it prints
//!
//! `name<TAB>dep,dep,dep` — DIRECT theorem references only, sorted, one line per
//! theorem, with the dependency list empty for a base theorem. Direct rather than
//! transitive because `depends_on` means what a proposition immediately rests on;
//! the transitive set of a late theorem is most of the prelude.
//!
//! Definitions, inductives and axioms are excluded: a proof of `Nat.add_comm`
//! references `Nat` and `Nat.add`, and recording those would say nothing about
//! which *propositions* it needs.
//!
//! ```sh
//! cargo run -q -p axeyum-lean-kernel --example theorem_dependency_inventory
//! cargo run -q -p axeyum-lean-kernel --example theorem_dependency_inventory -- euclid
//! ```
//!
//! # A filter that matches nothing is a FAILURE
//!
//! The same trap `nat_theorem_inventory` had until 2026-08-15: if this is ever a
//! fact's `checker_command`, a name that no longer exists must not print an empty
//! list and exit 0. A named filter matching nothing exits non-zero; an unfiltered
//! run has no expectation to violate and exits 0.

use std::process::ExitCode;

use axeyum_lean_kernel::{Declaration, Kernel, build_nat_prelude};

fn main() -> ExitCode {
    let filter: Option<String> = std::env::args().nth(1);

    let mut kernel = Kernel::new();
    let _ = build_nat_prelude(&mut kernel).expect("Nat prelude must build");

    // Collect first, then sort by rendered name: environment iteration order is
    // an interning artifact and this output is meant to be diffable.
    let mut theorems: Vec<(String, Vec<String>)> = kernel
        .environment()
        .iter()
        .filter(|(_, decl)| matches!(decl, Declaration::Theorem { .. }))
        .map(|(name, _)| {
            let rendered = kernel.display_name(*name).to_string();
            let deps = kernel
                .theorem_dependencies(*name)
                .into_iter()
                .map(|d| kernel.display_name(d).to_string())
                .collect();
            (rendered, deps)
        })
        .collect();
    theorems.sort();

    let shown: Vec<&(String, Vec<String>)> = theorems
        .iter()
        .filter(|(name, _)| filter.as_ref().is_none_or(|f| name.contains(f)))
        .collect();

    for (name, deps) in &shown {
        println!("{name}\t{}", deps.join(","));
    }

    let with_deps = shown.iter().filter(|(_, d)| !d.is_empty()).count();
    let edges: usize = shown.iter().map(|(_, d)| d.len()).sum();
    eprintln!(
        "{} theorems, {with_deps} with dependencies, {edges} edges",
        shown.len()
    );

    if shown.is_empty() {
        if let Some(f) = filter {
            eprintln!(
                "error: no theorem matches {f:?}. Asking for a theorem and finding \
                 none is a failure, not an empty answer -- a deleted theorem must \
                 not read as a re-derived one."
            );
            return ExitCode::FAILURE;
        }
        eprintln!("error: the Nat prelude admitted no theorems at all");
        return ExitCode::FAILURE;
    }
    ExitCode::SUCCESS
}
