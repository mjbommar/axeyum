//! Tests for the `Int` model of the `Real` axiom package.
//!
//! Three properties, and the second is the one that keeps the first honest:
//!
//! - [`every_law_is_witnessed_and_axiom_free`] — the interpretation of each
//!   `Real` law is admitted with an `Int` theorem as its proof, and the witness
//!   rests on nothing.
//! - [`the_interpretation_covers_every_real_declaration`] — no `Real`
//!   declaration is left out. A count of "22 laws modelled" means nothing
//!   unless the package really has 22 laws; this test derives the population
//!   from the environment instead of from this file.
//! - [`the_real_package_has_no_inverse_completeness_or_archimedean_axiom`] —
//!   the measurement the whole decision rests on, pinned so that adding one
//!   breaks a test rather than quietly invalidating the model.

use std::collections::BTreeSet;

use super::build_int_model_of_arith;
use crate::env::Declaration;
use crate::{Kernel, build_int_prelude};

/// Every `Real` law is modelled by an `Int` theorem the kernel accepted, and
/// every witness has an empty axiom footprint.
///
/// The empty footprint is the whole point. A witness whose closure reached a
/// `Real` axiom would type-check trivially (`Real.add_comm` proves
/// `Real.add_comm`) and would establish nothing; only the footprint separates a
/// model from a restatement.
#[test]
fn every_law_is_witnessed_and_axiom_free() {
    let mut k = Kernel::new();
    let model = build_int_model_of_arith(&mut k).expect("the Int model must build");
    assert_eq!(model.laws.len(), 22, "the Real package has 22 laws");
    for law in &model.laws {
        let footprint = k.axiom_footprint(law.witness);
        assert!(
            footprint.is_empty(),
            "{} must rest on nothing, but rests on {:?}",
            k.display_name(law.witness),
            footprint
                .iter()
                .map(|a| k.display_name(*a).to_string())
                .collect::<Vec<_>>()
        );
        assert!(
            matches!(
                k.environment().get(law.witness),
                Some(Declaration::Theorem { .. })
            ),
            "{} must be a checked theorem",
            k.display_name(law.witness)
        );
    }
}

/// Interpreting a `Real` axiom lands on exactly the `Int` law's own statement,
/// not merely on something definitionally equal to it.
///
/// This is stronger than admission and is what lets the two developments share
/// a reading: the `Real` axiom and the `Int` theorem say the same thing about
/// their respective carriers, symbol for symbol. If a law ever fails here the
/// two statements have drifted apart in shape and the difference should be
/// examined rather than absorbed by the definitional-equality checker.
#[test]
fn interpretation_is_syntactic_identity_on_every_law() {
    let mut k = Kernel::new();
    let model = build_int_model_of_arith(&mut k).expect("the Int model must build");
    let drifted: Vec<String> = model
        .laws
        .iter()
        .filter(|law| !law.identical)
        .map(|law| k.display_name(law.real).to_string())
        .collect();
    assert!(
        drifted.is_empty(),
        "interpreted Real axioms that are not syntactically the Int law: {drifted:?}"
    );
}

/// Every `Real.*` declaration is accounted for: either an interpreted symbol or
/// a modelled law. Nothing in the package is silently skipped.
#[test]
fn the_interpretation_covers_every_real_declaration() {
    let mut k = Kernel::new();
    let model = build_int_model_of_arith(&mut k).expect("the Int model must build");

    let mut accounted: BTreeSet<_> = model.symbols.iter().map(|&(real, _)| real).collect();
    accounted.extend(model.laws.iter().map(|law| law.real));

    let mut declared = BTreeSet::new();
    for (_, declaration) in k.environment().iter() {
        if let Declaration::Axiom { name, .. } = declaration {
            let rendered = k.display_name(*name).to_string();
            if rendered == "Real" || rendered.starts_with("Real.") {
                declared.insert(*name);
            }
        }
    }
    assert_eq!(
        declared.len(),
        30,
        "the Real package is 30 trusted declarations"
    );
    let missed: Vec<_> = declared
        .difference(&accounted)
        .map(|n| k.display_name(*n).to_string())
        .collect();
    assert!(
        missed.is_empty(),
        "Real declarations with no interpretation: {missed:?}"
    );
}

/// The `Real` package contains no multiplicative inverse, no division, no
/// supremum/completeness axiom, no Archimedean axiom and no density axiom.
///
/// This is the measurement the decision to model `Real` in `ℤ` rests on, and it
/// is exactly the kind of claim that rots silently. Adding any of these names
/// makes `ℤ` stop being a model, and this test fails before the model does.
#[test]
fn the_real_package_has_no_inverse_completeness_or_archimedean_axiom() {
    let mut k = Kernel::new();
    let model = build_int_model_of_arith(&mut k).expect("the Int model must build");
    let _ = model;
    let forbidden = [
        "inv",
        "div",
        "sup",
        "lub",
        "complete",
        "cauchy",
        "archimedean",
        "dense",
        "sqrt",
    ];
    let mut offenders = Vec::new();
    for (_, declaration) in k.environment().iter() {
        if let Declaration::Axiom { name, .. } = declaration {
            let rendered = k.display_name(*name).to_string();
            let Some(leaf) = rendered.strip_prefix("Real.") else {
                continue;
            };
            let lowered = leaf.to_ascii_lowercase();
            if forbidden.iter().any(|needle| lowered.contains(needle)) {
                offenders.push(rendered);
            }
        }
    }
    assert!(
        offenders.is_empty(),
        "the Real package grew a field/completeness axiom the Int model cannot satisfy: \
         {offenders:?}"
    );
}

/// `Int.sq_nonneg` — the one `Real` law that had no `Int` counterpart before
/// this model existed — is derived and axiom-free.
#[test]
fn int_square_nonnegativity_is_derived() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    assert!(
        matches!(
            k.environment().get(p.sq_nonneg),
            Some(Declaration::Theorem { .. })
        ),
        "Int.sq_nonneg must be a theorem, not an assumption"
    );
    assert!(
        k.axiom_footprint(p.sq_nonneg).is_empty(),
        "Int.sq_nonneg must rest on nothing"
    );
}

/// The kernel's quotient package is `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`
/// — and **not** `Quot.sound`.
///
/// This is the load-bearing negative measurement behind the whole `ℝ` decision,
/// and it contradicts what three places in this repository asserted in prose
/// (that a setoid construction would "put `Quot.sound` in every footprint").
/// It would not: without `Quot.sound` there is no way to prove two `Quot.mk`s
/// equal, so a Cauchy-sequence quotient cannot be built here at all. Pinned as
/// a test so that adding `Quot.sound` — which is a deliberate extension of the
/// trusted surface — cannot happen without this failing first.
#[test]
fn the_quotient_package_has_no_soundness_primitive() {
    let mut k = Kernel::new();
    let _ = build_int_model_of_arith(&mut k).expect("the Int model must build");
    let anon = k.anon();
    let quot = k.name_str(anon, "Quot");
    let sound = k.name_str(quot, "sound");
    assert!(
        !k.environment().contains(sound),
        "Quot.sound is now declared; the ADR-0456 accounting of what ℝ costs must be redone"
    );
}
