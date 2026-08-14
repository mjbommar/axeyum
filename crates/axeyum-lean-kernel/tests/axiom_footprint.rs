//! `Kernel::axiom_footprint` — the per-theorem trusted-dependency closure.
//!
//! The property under test is **discrimination**. A footprint that returns the
//! whole environment for every declaration is trivially sound and completely
//! useless: it is exactly the bound we already had by enumerating the
//! environment, and it is the bound that led an extraction lane to decline to
//! record any integer or real fact rather than assert a footprint it could not
//! justify. So "is it correct" here means "does it separate declarations that
//! rest on different axioms", not merely "does it over-approximate".

use axeyum_lean_kernel::{Declaration, Kernel, build_int_prelude, build_nat_prelude};

/// Resolve by rendered name, since prelude names are interned `NameId`s and the
/// declaration helpers take struct fields rather than string literals — there is
/// no way to name one from outside without walking the environment.
fn named(kernel: &Kernel, want: &str) -> axeyum_lean_kernel::NameId {
    kernel
        .environment()
        .iter()
        .find_map(|(_, d)| {
            let name = match d {
                Declaration::Axiom { name, .. }
                | Declaration::Definition { name, .. }
                | Declaration::Theorem { name, .. }
                | Declaration::Opaque { name, .. } => *name,
                _ => return None,
            };
            (kernel.display_name(name).to_string() == want).then_some(name)
        })
        .unwrap_or_else(|| panic!("{want} is not declared in this environment"))
}

fn footprint_names(kernel: &Kernel, want: &str) -> Vec<String> {
    kernel
        .axiom_footprint(named(kernel, want))
        .into_iter()
        .map(|n| kernel.display_name(n).to_string())
        .collect()
}

#[test]
fn every_nat_theorem_is_axiom_free() {
    let mut kernel = Kernel::new();
    let _ = build_nat_prelude(&mut kernel).expect("Nat prelude must build");

    let theorems: Vec<_> = kernel
        .environment()
        .iter()
        .filter_map(|(_, d)| match d {
            Declaration::Theorem { name, .. } => Some(*name),
            _ => None,
        })
        .collect();

    // Guards the measurement itself: an empty or tiny set would make the
    // assertion below vacuously true, which is how a gate comes to check
    // nothing while exiting 0.
    assert!(
        theorems.len() >= 119,
        "expected at least the 119 known Nat theorems, found {}",
        theorems.len()
    );

    for name in theorems {
        let footprint = kernel.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{} is not axiom-free: {:?}",
            kernel.display_name(name),
            footprint
                .iter()
                .map(|n| kernel.display_name(*n).to_string())
                .collect::<Vec<_>>()
        );
    }
}

#[test]
fn int_footprints_name_only_what_a_declaration_actually_uses() {
    let mut kernel = Kernel::new();
    let _ = build_int_prelude(&mut kernel).expect("Int prelude must build");

    let trusted = kernel
        .environment()
        .iter()
        .filter(|(_, d)| matches!(d, Declaration::Axiom { .. }))
        .count();
    assert_eq!(trusted, 34, "Int prelude axiom population changed");

    // Exact, not a subset check: an over-approximation that happened to contain
    // these would pass a subset assertion while being worthless.
    assert_eq!(
        footprint_names(&kernel, "Int.add_neg"),
        vec!["Int", "Int.add", "Int.add_neg", "Int.neg", "Int.zero"],
    );
    assert_eq!(
        footprint_names(&kernel, "Int.add_comm"),
        vec!["Int", "Int.add", "Int.add_comm"],
    );

    // The discrimination property, stated directly: two declarations in one
    // environment must be able to have different footprints.
    assert_ne!(
        footprint_names(&kernel, "Int.add_neg"),
        footprint_names(&kernel, "Int.add_comm"),
    );

    // ...and no declaration may drag in the whole environment.
    for name in ["Int.add_neg", "Int.add_comm", "Int.mul_one"] {
        let size = footprint_names(&kernel, name).len();
        assert!(
            size < trusted,
            "{name} rests on {size} of {trusted} axioms -- a footprint that is the \
             whole environment is the useless bound this method exists to replace"
        );
    }
}

#[test]
fn an_axiom_rests_on_itself() {
    let mut kernel = Kernel::new();
    let _ = build_int_prelude(&mut kernel).expect("Int prelude must build");

    // Matches Lean's `#print axioms` on an axiom. Omitting the root would let a
    // fact cite an axiom as its own axiom-free evidence.
    assert!(footprint_names(&kernel, "Int.add_comm").contains(&"Int.add_comm".to_owned()));
}
