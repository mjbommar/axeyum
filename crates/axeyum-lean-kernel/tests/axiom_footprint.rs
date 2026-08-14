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
                | Declaration::Opaque { name, .. }
                | Declaration::Inductive { name, .. }
                | Declaration::Constructor { name, .. } => *name,
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

/// Build `theorem combined : And (0+1)+1 = 0+(1+1) ∧ (0*1)*1 = 0*(1*1)` from
/// the two associativity assumptions, so the environment contains one
/// declaration whose footprint is genuinely *composite*.
///
/// Every remaining `Int` assumption now has a one-element footprint (itself) —
/// the operations became definitions — so without a composite witness this
/// suite could no longer tell an exact closure from "return the root and stop".
fn declare_composite_witness(kernel: &mut Kernel) {
    let int_ty = {
        let name = named(kernel, "Int");
        kernel.const_(name, vec![])
    };
    let apply = |kernel: &mut Kernel, head: &str, args: &[axeyum_lean_kernel::ExprId]| {
        let name = named(kernel, head);
        let mut term = kernel.const_(name, vec![]);
        for &argument in args {
            term = kernel.app(term, argument);
        }
        term
    };
    let zero = apply(kernel, "Int.zero", &[]);
    let one = apply(kernel, "Int.one", &[]);
    let equation = |kernel: &mut Kernel, operation: &str| {
        let inner_left = apply(kernel, operation, &[zero, one]);
        let left = apply(kernel, operation, &[inner_left, one]);
        let inner_right = apply(kernel, operation, &[one, one]);
        let right = apply(kernel, operation, &[zero, inner_right]);
        let level_zero = kernel.level_zero();
        let level_one = kernel.level_succ(level_zero);
        let name = named(kernel, "Eq");
        let eq = kernel.const_(name, vec![level_one]);
        let term = kernel.app(eq, int_ty);
        let term = kernel.app(term, left);
        kernel.app(term, right)
    };
    let additive = equation(kernel, "Int.add");
    let multiplicative = equation(kernel, "Int.mul");
    let ty = apply(kernel, "And", &[additive, multiplicative]);
    let additive_proof = apply(kernel, "Int.add_assoc", &[zero, one, one]);
    let multiplicative_proof = apply(kernel, "Int.mul_assoc", &[zero, one, one]);
    let value = apply(
        kernel,
        "And.intro",
        &[
            additive,
            multiplicative,
            additive_proof,
            multiplicative_proof,
        ],
    );
    let anon = kernel.anon();
    let name = kernel.name_str(anon, "combined");
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .expect("the composite witness must type-check");
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
    assert_eq!(
        trusted, 6,
        "Int prelude axiom population changed -- 28 of the original 34 are now \
         constructed or derived; a change here is a real result either way"
    );

    declare_composite_witness(&mut kernel);

    // Exact, not a subset check: an over-approximation that happened to contain
    // these would pass a subset assertion while being worthless.
    assert_eq!(
        footprint_names(&kernel, "combined"),
        vec!["Int.add_assoc", "Int.mul_assoc"],
    );
    assert_eq!(
        footprint_names(&kernel, "Int.add_assoc"),
        vec!["Int.add_assoc"],
    );
    // Derived from the axiom-free `Nat` development: nothing at all.
    assert!(footprint_names(&kernel, "Int.add_comm").is_empty());
    assert!(footprint_names(&kernel, "Int.add_neg").is_empty());

    // The discrimination property, stated directly: declarations in one
    // environment must be able to have different footprints.
    assert_ne!(
        footprint_names(&kernel, "combined"),
        footprint_names(&kernel, "Int.add_assoc"),
    );
    assert_ne!(
        footprint_names(&kernel, "Int.add_assoc"),
        footprint_names(&kernel, "Int.mul_assoc"),
    );

    // ...and no declaration may drag in the whole environment.
    for name in [
        "combined",
        "Int.add_assoc",
        "Int.mul_one",
        "Int.euclidean_decomposition",
    ] {
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
    assert!(footprint_names(&kernel, "Int.add_assoc").contains(&"Int.add_assoc".to_owned()));
}
