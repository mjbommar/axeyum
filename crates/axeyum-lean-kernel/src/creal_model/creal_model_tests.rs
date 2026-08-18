//! Tests for the `CReal` model of the `Real` axiom package (ADR-0483 phase R4).
//!
//! The first test is the claim; the rest are the ones that stop the claim being
//! vacuous, and each of them fails for a *different* reason:
//!
//! - [`every_law_is_witnessed_and_axiom_free`] — the interpretation of each
//!   `Real` law is admitted with a `CReal` theorem as its proof, and rests on
//!   nothing.
//! - [`the_pairing_is_by_leaf_name`] — the two 22-element lists really do
//!   correspond entry by entry. **This one is belt-and-braces today, and the
//!   measurement says so**: every mis-pairing that could be constructed is
//!   already fatal at admission — a swapped entry is a `TypeMismatch`, and a
//!   consistently *duplicated* entry (the case a type check cannot see, since
//!   every type still matches) is refused as a repeated declaration name, which
//!   was verified by mutating both lists and watching all seven tests die on
//!   `build_creal_model_of_arith` itself rather than on this assertion. It is
//!   kept because it states the correspondence at the level of *names*, which
//!   is what would still hold if two law types ever coincided, and because it
//!   costs one pass over a list already in hand.
//! - [`exactly_nine_laws_are_restated_over_equiv`] — ADR-0483's Measurement 2,
//!   read out of the kernel. Thirteen laws are the `Real` package's statements
//!   verbatim and nine are not, and it is the nine that make the setoid route
//!   cost anything at all.
//! - [`the_interpretation_covers_every_real_declaration`] — no `Real`
//!   declaration is left out; the population comes from the environment.
//! - [`the_model_is_worthless_without_the_discrimination_witnesses`] — the
//!   seven witnesses that keep `CReal`'s laws from being true of an empty
//!   carrier, a total relation, an empty relation, or a constant-zero product.
//!   **Presence is asserted before any footprint is read**, because
//!   `axiom_footprint` of an interned-but-undeclared name is the empty vector
//!   and a footprint-only test passes with the witness deleted.
//! - [`the_equality_slot_is_not_eq`] — `Eq CReal` is not what any witness
//!   states, so nothing here quietly re-acquires Leibniz equality.

use std::collections::BTreeSet;

use super::build_creal_model_of_arith;
use crate::arith_model::leaf_name;
use crate::env::Declaration;
use crate::{Kernel, build_creal_prelude};

/// Every `Real` law is modelled by a `CReal` theorem the kernel accepted, and
/// every witness has an empty axiom footprint.
///
/// The empty footprint is the whole point. A witness whose closure reached a
/// `Real` axiom would type-check trivially (`Real.add_comm` proves
/// `Real.add_comm`) and would establish nothing; only the footprint separates a
/// model from a restatement.
#[test]
fn every_law_is_witnessed_and_axiom_free() {
    let mut k = Kernel::new();
    let model = build_creal_model_of_arith(&mut k).expect("the CReal model must build");
    assert_eq!(model.laws.len(), 22, "the Real package has 22 laws");
    for law in &model.laws {
        assert!(
            matches!(
                k.environment().get(law.witness),
                Some(Declaration::Theorem { .. })
            ),
            "{} must be a checked theorem",
            k.display_name(law.witness)
        );
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
    }
}

/// The `Real` law and the `CReal` theorem paired with it have the same leaf
/// name, for all 22.
///
/// `build_creal_model_of_arith` zips two hand-written orderings, and this says
/// the two orderings agree.
///
/// Measured rather than assumed: **no mutation reaches this assertion.**
/// Swapping one entry makes the kernel reject the proof (`TypeMismatch`), and
/// duplicating an entry consistently in *both* lists — the shape a type check
/// structurally cannot see, since all 22 types still match — is refused as a
/// repeated declaration name. Both mutations kill all seven tests at
/// `build_creal_model_of_arith`, not here.
///
/// Kept anyway, for one reason that is not sentiment: it is the only statement
/// of the correspondence that does not go through the kernel's conversion
/// checker, so it is the one that would still fire if two of the 22 law types
/// ever coincided under the interpretation. Read it as documentation with an
/// exit status, not as the load-bearing guard.
#[test]
fn the_pairing_is_by_leaf_name() {
    let mut k = Kernel::new();
    let model = build_creal_model_of_arith(&mut k).expect("the CReal model must build");
    let mismatched: Vec<(String, String)> = model
        .laws
        .iter()
        .map(|law| (leaf_name(&k, law.real), leaf_name(&k, law.creal)))
        .filter(|(real, creal)| real != creal)
        .collect();
    assert!(
        mismatched.is_empty(),
        "Real/CReal laws paired across different names: {mismatched:?}"
    );
    let distinct: BTreeSet<String> = model
        .laws
        .iter()
        .map(|law| leaf_name(&k, law.real))
        .collect();
    assert_eq!(distinct.len(), 22, "the 22 laws must be 22 distinct names");
}

/// Exactly nine of the 22 laws mention the carrier's `Eq` and are therefore
/// modelled in `CReal.Equiv`-restated form; the other thirteen are the `Real`
/// package's statements verbatim.
///
/// This is ADR-0483's Measurement 2 and it is the entire price of the setoid
/// route. It is pinned here because both directions are interesting: a tenth
/// restated law means the `Real` package grew an `Eq`-statement the order
/// fragment did not have, and an eighth means one was dropped.
#[test]
fn exactly_nine_laws_are_restated_over_equiv() {
    let mut k = Kernel::new();
    let model = build_creal_model_of_arith(&mut k).expect("the CReal model must build");
    let mut restated: Vec<String> = model
        .laws
        .iter()
        .filter(|law| law.restated_over_equiv)
        .map(|law| leaf_name(&k, law.real))
        .collect();
    restated.sort();
    assert_eq!(
        restated,
        vec![
            "add_assoc",
            "add_comm",
            "add_neg",
            "add_zero",
            "left_distrib",
            "mul_assoc",
            "mul_comm",
            "mul_one",
            "mul_zero",
        ],
        "the nine Eq-laws of ADR-0483 Measurement 2"
    );
    assert_eq!(model.restated_count(), 9);
    assert_eq!(model.laws.len() - model.restated_count(), 13);
}

/// Every `Real.*` declaration is accounted for: either an interpreted symbol or
/// a modelled law. Nothing in the package is silently skipped, so a 31st axiom
/// cannot slip past this model while the count still reads "all covered".
#[test]
fn the_interpretation_covers_every_real_declaration() {
    let mut k = Kernel::new();
    let model = build_creal_model_of_arith(&mut k).expect("the CReal model must build");

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

/// The model's 22 empty footprints mean nothing without the seven witnesses
/// that say `CReal` is not degenerate.
///
/// Each of these closes a hole an axiom footprint structurally cannot see:
/// an empty carrier makes every ∀-law true; the total relation is an
/// equivalence relation and satisfies `le_refl`/`le_trans`/`add_le_add`; the
/// empty relation satisfies six of the seven strict-order laws; and
/// `fun _ _ => zero` satisfies `mul_zero`, `mul_comm` and `sq_nonneg`.
///
/// **Presence first.** `Kernel::axiom_footprint` of a name that was interned
/// but never declared returns the empty vector, so a test that reads the
/// footprint without checking the declaration exists passes with the witness
/// deleted — which is how a presence test in this development once did.
#[test]
fn the_model_is_worthless_without_the_discrimination_witnesses() {
    let mut k = Kernel::new();
    let model = build_creal_model_of_arith(&mut k).expect("the CReal model must build");
    let p = model.creal;
    let guards = [
        ("carrier inhabited", p.of_rat),
        ("Equiv discriminates", p.not_zero_one),
        ("le discriminates", p.not_le_one_zero),
        ("lt inhabited", p.zero_lt_one),
        ("lt irreflexive", p.lt_irrefl),
        ("mul agrees with Rat.mul on ℚ", p.of_rat_mul),
        ("mul discriminates", p.not_equiv_mul_one_one_zero),
    ];
    for (what, name) in guards {
        let declaration = k.environment().get(name);
        assert!(
            matches!(
                declaration,
                Some(Declaration::Theorem { .. } | Declaration::Definition { .. })
            ),
            "{what}: {} is not a checked declaration, so the 22 witnesses above \
             may all be vacuously true with empty footprints",
            k.display_name(name)
        );
        assert!(
            k.axiom_footprint(name).is_empty(),
            "{what}: {} does not rest on nothing",
            k.display_name(name)
        );
    }
}

/// The nine restated laws are stated over `CReal.Equiv` and **not** over
/// `Eq CReal`.
///
/// Building the model must not quietly hand back Leibniz equality: that is what
/// would cost `Quot.sound`, and the whole construction is worth zero trusted
/// declarations only because it does not. Checked by rebuilding the model's
/// equality slot from the `CReal` prelude and confirming it is `CReal.Equiv`,
/// and by confirming `Quot.sound` is still absent from the environment the
/// model was built in.
#[test]
fn the_equality_slot_is_not_eq() {
    let mut k = Kernel::new();
    let model = build_creal_model_of_arith(&mut k).expect("the CReal model must build");
    let mut k2 = Kernel::new();
    let p = build_creal_prelude(&mut k2).expect("the CReal development must build");
    assert_eq!(
        k.display_name(model.equality.1).to_string(),
        k2.display_name(p.equiv).to_string(),
        "the equality slot must be CReal.Equiv"
    );
    assert_ne!(
        model.equality.0, model.equality.1,
        "the equality slot must not be the kernel's Eq"
    );
    let anon = k.anon();
    let quot = k.name_str(anon, "Quot");
    let sound = k.name_str(quot, "sound");
    assert!(
        !k.environment().contains(sound),
        "Quot.sound is now declared; ADR-0483's zero-cost accounting must be redone"
    );
}

/// The whole trusted surface of the environment the model was built in is the
/// `Real` package and nothing else — in particular the constructed `CReal` and
/// everything under it adds **zero**.
///
/// This is the measurement that says what deleting `build_arith_prelude` would
/// buy: 30, and exactly 30.
#[test]
fn the_only_trusted_declarations_left_are_the_real_package() {
    let mut k = Kernel::new();
    let _ = build_creal_model_of_arith(&mut k).expect("the CReal model must build");
    let trusted: Vec<String> = k
        .environment()
        .iter()
        .filter_map(|(_, declaration)| match declaration {
            Declaration::Axiom { name, .. }
            | Declaration::Opaque { name, .. }
            | Declaration::Quotient { name, .. } => Some(k.display_name(*name).to_string()),
            _ => None,
        })
        .collect();
    let non_real: Vec<&String> = trusted
        .iter()
        .filter(|n| *n != "Real" && !n.starts_with("Real."))
        .collect();
    assert!(
        non_real.is_empty(),
        "trusted declarations outside the Real package: {non_real:?}"
    );
    assert_eq!(
        trusted.len(),
        30,
        "the Real package is the whole remaining trusted surface"
    );
}
