//! `Kernel::axiom_footprint` — the per-theorem trusted-dependency closure.
//!
//! The property under test is **discrimination**. A footprint that returns the
//! whole environment for every declaration is trivially sound and completely
//! useless: it is exactly the bound we already had by enumerating the
//! environment, and it is the bound that led an extraction lane to decline to
//! record any integer or real fact rather than assert a footprint it could not
//! justify. So "is it correct" here means "does it separate declarations that
//! rest on different axioms", not merely "does it over-approximate".

use axeyum_lean_kernel::{
    Declaration, Kernel, build_arith_prelude, build_int_prelude, build_nat_prelude,
};

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

/// Build one theorem whose footprint is genuinely **composite** and spans two
/// preludes: the real half is a ring step over the still-assumed `R`, the
/// integer half is the one integer law that is still asserted.
///
/// It used to combine `Int.add_assoc` with `Int.mul_assoc`. Both are theorems
/// now, and so is every other integer law except `Int.euclidean_decomposition`
/// — so an integer-only composite is no longer constructible, and the suite
/// reaches into `arith` to keep testing an exact closure rather than "return
/// the root and stop".
fn declare_composite_witness(kernel: &mut Kernel) {
    let apply = |kernel: &mut Kernel, head: &str, args: &[axeyum_lean_kernel::ExprId]| {
        let name = named(kernel, head);
        let mut term = kernel.const_(name, vec![]);
        for &argument in args {
            term = kernel.app(term, argument);
        }
        term
    };
    let real_ty = apply(kernel, "Real", &[]);
    let real_zero = apply(kernel, "Real.zero", &[]);
    let real_one = apply(kernel, "Real.one", &[]);
    let additive = {
        let inner_left = apply(kernel, "Real.add", &[real_zero, real_one]);
        let left = apply(kernel, "Real.add", &[inner_left, real_one]);
        let inner_right = apply(kernel, "Real.add", &[real_one, real_one]);
        let right = apply(kernel, "Real.add", &[real_zero, inner_right]);
        let level_zero = kernel.level_zero();
        let level_one = kernel.level_succ(level_zero);
        let name = named(kernel, "Eq");
        let eq = kernel.const_(name, vec![level_one]);
        let term = kernel.app(eq, real_ty);
        let term = kernel.app(term, left);
        kernel.app(term, right)
    };
    let additive_proof = apply(kernel, "Real.add_assoc", &[real_zero, real_one, real_one]);
    let int_one = apply(kernel, "Int.one", &[]);
    let positive = apply(kernel, "Int.zero_lt_one", &[]);
    let euclidean_proof = apply(
        kernel,
        "Int.euclidean_decomposition",
        &[int_one, int_one, positive],
    );
    // The Euclidean statement is two nested existentials over a conjunction;
    // inferring it is both shorter and less error-prone than rebuilding it.
    let euclidean = kernel
        .infer(euclidean_proof)
        .expect("the Euclidean instance must type-check");
    let ty = apply(kernel, "And", &[additive, euclidean]);
    let value = apply(
        kernel,
        "And.intro",
        &[additive, euclidean, additive_proof, euclidean_proof],
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
    let _ = build_arith_prelude(&mut kernel).expect("Real prelude must build");

    let trusted = kernel
        .environment()
        .iter()
        .filter(|(_, d)| matches!(d, Declaration::Axiom { .. }))
        .count();
    // 1 integer (`euclidean_decomposition`) + 30 real. 33 of the integer
    // prelude's original 34 are now constructed or derived; a change to either
    // number is a real result either way.
    assert_eq!(trusted, 31, "trusted population changed");

    declare_composite_witness(&mut kernel);

    // Exact, not a subset check: an over-approximation that happened to contain
    // these would pass a subset assertion while being worthless. The real half
    // drags in the carrier and the operations it is stated over, because those
    // are assumptions too; the integer half drags in exactly one law.
    let mut composite = footprint_names(&kernel, "combined");
    composite.sort();
    assert_eq!(
        composite,
        vec![
            "Int.euclidean_decomposition",
            "Real",
            "Real.add",
            "Real.add_assoc",
            "Real.one",
            "Real.zero",
        ],
    );
    assert_eq!(
        footprint_names(&kernel, "Int.euclidean_decomposition"),
        vec!["Int.euclidean_decomposition"],
    );
    // Derived from the axiom-free `Nat` development: nothing at all — including
    // the four laws that were assumptions until the `subNatNat` borrow lemmas
    // landed.
    for derived in [
        "Int.add_comm",
        "Int.add_neg",
        "Int.add_assoc",
        "Int.mul_assoc",
        "Int.left_distrib",
        "Int.add_le_add",
        "Int.add_lt_add_of_le_of_lt",
        "Int.subNatNat_elim",
    ] {
        assert!(
            footprint_names(&kernel, derived).is_empty(),
            "{derived} should rest on nothing"
        );
    }

    // The discrimination property, stated directly: declarations in one
    // environment must be able to have different footprints.
    assert_ne!(
        footprint_names(&kernel, "combined"),
        footprint_names(&kernel, "Int.euclidean_decomposition"),
    );
    assert_ne!(
        footprint_names(&kernel, "Int.euclidean_decomposition"),
        footprint_names(&kernel, "Real.add_assoc"),
    );

    // ...and no declaration may drag in the whole environment.
    for name in [
        "combined",
        "Int.mul_one",
        "Int.euclidean_decomposition",
        "Real.add_assoc",
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
    assert!(
        footprint_names(&kernel, "Int.euclidean_decomposition")
            .contains(&"Int.euclidean_decomposition".to_owned())
    );
}
