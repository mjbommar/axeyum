//! Tests for the rational prelude.

use super::{RatPrelude, build_rat_prelude};
use crate::{Declaration, Kernel};

fn built() -> (Kernel, RatPrelude) {
    let mut kernel = Kernel::new();
    let prelude = build_rat_prelude(&mut kernel).expect("Rat prelude must build");
    (kernel, prelude)
}

#[test]
fn rat_prelude_is_axiom_free() {
    let (kernel, _) = built();
    let trusted: Vec<String> = kernel
        .environment()
        .iter()
        .filter_map(|(_, declaration)| match declaration {
            Declaration::Axiom { name, .. }
            | Declaration::Opaque { name, .. }
            | Declaration::Quotient { name, .. } => Some(kernel.display_name(*name).to_string()),
            _ => None,
        })
        .collect();
    assert!(
        trusted.is_empty(),
        "the rational prelude must assume nothing, found: {trusted:?}"
    );
}

#[test]
fn every_named_declaration_exists() {
    let (kernel, p) = built();
    let expected = [
        ("zero", p.zero),
        ("one", p.one),
        ("le", p.le),
        ("lt", p.lt),
        ("inv", p.inv),
        ("sub", p.sub),
        ("div", p.div),
        ("mk_congr", p.mk_congr),
        ("eta", p.eta),
        ("ext", p.ext),
        ("le_total", p.le_total),
        ("lt_of_not_le", p.lt_of_not_le),
        ("normalize_add_normalize", p.normalize_add_normalize),
        ("normalize_mul_normalize", p.normalize_mul_normalize),
    ];
    for (label, name) in expected {
        assert!(
            kernel.environment().get(name).is_some(),
            "Rat.{label} was interned but never declared"
        );
    }
}

/// The build itself, with the kernel's rejection **rendered** rather than
/// printed as opaque `ExprId`s. A `Debug` of `KernelError` says nothing about
/// what was refused; this says which two types failed to match.
#[test]
fn rat_prelude_builds() {
    let mut kernel = Kernel::new();
    match build_rat_prelude(&mut kernel) {
        Ok(_) => {}
        Err(error) => {
            let nat = crate::build_nat_prelude(&mut kernel).expect("Nat prelude must build");
            let mut dev = crate::NatDev::new(&mut kernel, nat);
            let explained = crate::NatOps::explain(&mut dev, &error);
            panic!("the kernel refused a rational proof: {explained}");
        }
    }
}

/// Every one of the 22 ordered-commutative-ring laws is a **checked theorem**
/// with an empty axiom footprint — not an axiom, not an opaque, not missing.
///
/// This fails if a law is dropped, demoted to an axiom, or quietly loses its
/// proof: it reads the kernel's own environment and footprint rather than
/// trusting that `build_rat_prelude` returned `Ok`.
#[test]
fn every_ordered_ring_law_is_a_checked_theorem() {
    let (kernel, p) = built();
    for (index, law) in p.ring_laws().into_iter().enumerate() {
        let rendered = kernel.display_name(law).to_string();
        let declaration = kernel
            .environment()
            .get(law)
            .unwrap_or_else(|| panic!("ring law #{index} ({rendered}) is not declared at all"));
        assert!(
            matches!(declaration, Declaration::Theorem { .. }),
            "ring law #{index} ({rendered}) must be a checked Theorem, found a different kind"
        );
        let footprint: Vec<String> = kernel
            .axiom_footprint(law)
            .into_iter()
            .map(|name| kernel.display_name(name).to_string())
            .collect();
        assert!(
            footprint.is_empty(),
            "ring law #{index} ({rendered}) rests on {footprint:?}"
        );
    }
}

/// Dropping any single law is caught: the list this asserts against is
/// `RatPrelude::ring_laws`, which `build_rat_model_of_arith` pairs positionally
/// with the `Real` package, so a shortened or reordered list is a build failure
/// there rather than a silently weaker claim here.
#[test]
fn the_ring_law_list_has_exactly_twenty_two_distinct_entries() {
    let (kernel, p) = built();
    let mut names: Vec<String> = p
        .ring_laws()
        .into_iter()
        .map(|law| kernel.display_name(law).to_string())
        .collect();
    assert_eq!(names.len(), 22);
    names.sort();
    names.dedup();
    assert_eq!(names.len(), 22, "the ring-law list repeats an entry");
}

/// ℚ is a model of the whole `Real` axiom package: every one of the 30
/// declarations is either an interpreted symbol or a law with a
/// kernel-checked, axiom-free witness.
#[test]
fn rationals_model_the_real_axioms() {
    let mut kernel = Kernel::new();
    let model = crate::build_rat_model_of_arith(&mut kernel).expect("ℚ must model the Real axioms");
    assert_eq!(model.laws.len(), 22);
    assert_eq!(model.symbols.len(), 8);
    for law in &model.laws {
        let footprint: Vec<String> = kernel
            .axiom_footprint(law.witness)
            .into_iter()
            .map(|name| kernel.display_name(name).to_string())
            .collect();
        let rendered = kernel.display_name(law.real).to_string();
        assert!(
            footprint.is_empty(),
            "the ℚ witness for {rendered} rests on {footprint:?}"
        );
    }
    // Completeness: no `Real` declaration escapes the interpretation.
    let interpreted: std::collections::HashSet<_> = model
        .symbols
        .iter()
        .map(|(real, _)| *real)
        .chain(model.laws.iter().map(|law| law.real))
        .collect();
    let missed: Vec<String> = kernel
        .environment()
        .iter()
        .filter_map(|(_, declaration)| match declaration {
            Declaration::Axiom { name, .. } => Some(*name),
            _ => None,
        })
        .filter(|name| !interpreted.contains(name))
        .map(|name| kernel.display_name(name).to_string())
        .collect();
    assert!(
        missed.is_empty(),
        "these Real declarations have no ℚ interpretation: {missed:?}"
    );
}
