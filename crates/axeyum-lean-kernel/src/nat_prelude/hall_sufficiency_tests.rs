//! Checks for `nat_prelude::hall_sufficiency` (ADR-1630).
//!
//! Nothing here is a `Definition`, so there is no value to evaluate; what
//! these tests guard is that each declaration is PRESENT, is a checked
//! `Theorem` rather than an `Axiom` or `Opaque`, and rests on zero axioms —
//! with the `Environment::contains` assertion first, because
//! `Kernel::axiom_footprint` of a name that was never declared is also empty.
//!
//! The rendered type of each is printed so a reviewer can read the statement
//! off the kernel rather than off this file's prose.

use crate::env::Declaration;
use crate::{Kernel, NameId, NatPrelude, build_nat_prelude};

fn fixture() -> (Kernel, NatPrelude) {
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
    (k, p)
}

/// Every declaration this module lands is a checked, axiom-free `Theorem`.
#[test]
fn hall_sufficiency_shelf_is_admitted_and_axiom_free() {
    let (k, p) = fixture();
    let names: [NameId; 3] = [
        p.hall_is_matching_congr,
        p.hall_exists_is_matching_of_card_le_zero,
        p.hall_exists_is_matching_singleton,
    ];
    for name in names {
        let shown = k.display_name(name).to_string();
        assert!(
            k.environment().contains(name),
            "{shown} must be declared before its footprint means anything"
        );
        let decl = k.environment().get(name).expect("just checked");
        assert!(
            matches!(decl, Declaration::Theorem { .. }),
            "{shown} must be a checked Theorem"
        );
        let ty = decl.ty();
        println!("theorem {shown} : {}", k.render_lean(ty));
        assert!(
            k.axiom_footprint(name).is_empty(),
            "{shown} must rest on zero axioms"
        );
    }
}

/// The base case is stated over the SAME vocabulary as necessity, so the two
/// compose.
///
/// `Nat.Hall.hallCondition_of_isMatching` takes `IsMatching s nb f` and
/// returns `HallCondition s nb`; the base case takes `HallCondition` at
/// `s := singleton a` and returns an `Exists` over `IsMatching`. This test
/// asserts the two rendered types mention the same three constants, which is
/// what makes an eventual `Iff` a composition rather than a restatement. A
/// mismatch here — a base case phrased over `Nat.Finset.range 1`, say — would
/// be invisible to the footprint test above.
#[test]
fn the_base_case_speaks_necessitys_vocabulary() {
    let (k, p) = fixture();

    let necessity = k
        .environment()
        .get(p.hall_condition_of_is_matching)
        .expect("necessity must be admitted")
        .ty();
    let necessity_shown = k.render_lean(necessity);

    let base = k
        .environment()
        .get(p.hall_exists_is_matching_singleton)
        .expect("the base case must be admitted")
        .ty();
    let base_shown = k.render_lean(base);

    for needle in ["Nat.Hall.IsMatching", "Nat.Hall.HallCondition"] {
        assert!(
            necessity_shown.contains(needle),
            "necessity must mention {needle}; got {necessity_shown}"
        );
        assert!(
            base_shown.contains(needle),
            "the base case must mention {needle}; got {base_shown}"
        );
    }
    assert!(
        base_shown.contains("Nat.Finset.singleton"),
        "the base case must be stated at a singleton index set; got {base_shown}"
    );
    // The control: the base case is NOT stated over `Nat.Finset.range`, which
    // is the other one-element spelling and would not compose with a `card`
    // induction on an arbitrary `Nat.Finset`.
    assert!(
        !base_shown.contains("Nat.Finset.range"),
        "the base case must not be phrased over `range`; got {base_shown}"
    );
}
