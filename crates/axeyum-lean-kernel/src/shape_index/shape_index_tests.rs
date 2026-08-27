//! Controls for the shape index.
//!
//! Every test here is written so that deleting the guard it names — and only
//! that guard — turns it red. The mutation table is recorded in
//! `docs/research/11-design-review/2026-08-27-retrieval-is-the-bottleneck.md`.
//!
//! The synthetic cases below build [`Entry`] rows directly rather than a
//! prelude, so the query and answerability logic is tested at zero kernel cost.
//! Two tests at the end run against a real built environment, because a
//! synthetic index cannot show that EXTRACTION works.

use std::collections::BTreeSet;

use super::{DeclKind, Entry, Outcome, Query, ShapeIndex, index_kernel, namespace_root, run};
use crate::{Kernel, build_nat_prelude};

fn entry(name: &str, kind: DeclKind, hyps: &[&str], concl: &str) -> Entry {
    let hyp_heads: Vec<Option<String>> = hyps
        .iter()
        .map(|head| Some((*head).to_owned()))
        .collect();
    let mut type_consts: BTreeSet<String> =
        hyps.iter().map(|head| (*head).to_owned()).collect();
    type_consts.insert(concl.to_owned());
    Entry {
        name: name.to_owned(),
        kind,
        arity: hyps.len(),
        hyp_heads,
        concl_head: Some(concl.to_owned()),
        type_consts,
        value_consts: None,
        shape: format!("{}|={concl}", hyps.join(",")),
        groups: ["synthetic".to_owned()].into_iter().collect(),
    }
}

/// An index whose declared vocabulary covers every name the tests query with,
/// so a test that expects `Absent` cannot accidentally be measuring
/// `Unanswerable`.
fn fixture() -> ShapeIndex {
    let mut index = ShapeIndex::new(vec!["synthetic".to_owned()], false);
    index.insert(entry("CReal.le", DeclKind::Definition, &["CReal"], "Prop"));
    index.insert(entry("CReal.Equiv", DeclKind::Definition, &["CReal"], "Prop"));
    index.insert(entry("CReal", DeclKind::Inductive, &[], "Sort"));
    index.insert(entry("Prop", DeclKind::Inductive, &[], "Sort"));
    index.insert(entry("Sort", DeclKind::Inductive, &[], "Sort"));
    index.insert(entry(
        "CReal.equiv_of_le_le",
        DeclKind::Theorem,
        &["CReal.le", "CReal.le"],
        "CReal.Equiv",
    ));
    index.insert(entry(
        "CReal.le_refl",
        DeclKind::Theorem,
        &["CReal"],
        "CReal.le",
    ));
    index.insert(entry(
        "Rat.polyEval",
        DeclKind::Definition,
        &["Rat"],
        "Rat",
    ));
    index.insert(entry("Rat", DeclKind::Inductive, &[], "Sort"));
    index.insert(entry(
        "Rat.polyEval_add",
        DeclKind::Theorem,
        &["Rat"],
        "Eq",
    ));
    index.insert(entry("Eq", DeclKind::Inductive, &[], "Sort"));
    index.finish();
    index
}

fn names(outcome: &Outcome) -> Vec<String> {
    match outcome {
        Outcome::Found(rows) => rows.clone(),
        other => panic!("expected Found, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// The retrieval question itself
// ---------------------------------------------------------------------------

/// GUARD: shape retrieval by conclusion head plus hypothesis heads. This is
/// the whole point — `equiv_of_le_le` is found without knowing its name.
#[test]
fn shape_query_finds_a_lemma_whose_name_is_unknown() {
    let index = fixture();
    let query = Query {
        concl: Some("CReal.Equiv".to_owned()),
        hyps: vec!["CReal.le".to_owned(), "CReal.le".to_owned()],
        ..Query::default()
    };
    assert_eq!(names(&run(&index, &query)), vec!["CReal.equiv_of_le_le"]);
}

/// GUARD: `--hyp X --hyp X` demands two DISTINCT binders headed by `X`.
/// Without it, `le_refl` (one `CReal` binder) would answer a two-hypothesis
/// query and the tool would report a lemma that cannot be applied.
#[test]
fn repeated_hypothesis_needs_distinct_binders() {
    let index = fixture();
    let one = Query {
        concl: Some("CReal.le".to_owned()),
        hyps: vec!["CReal".to_owned()],
        ..Query::default()
    };
    assert_eq!(names(&run(&index, &one)), vec!["CReal.le_refl"]);
    let two = Query {
        concl: Some("CReal.le".to_owned()),
        hyps: vec!["CReal".to_owned(), "CReal".to_owned()],
        ..Query::default()
    };
    assert_eq!(run(&index, &two), Outcome::Absent);
}

/// GUARD: every declaration KIND is indexed, and a definition is retrievable
/// as a definition. `prelude_theorem_inventory` filters to `Theorem`, so
/// `Rat.polyEval` returns zero rows from it while sixteen lemmas ABOUT it
/// return hits — the careless query confirms presence and the careful one
/// reports absence, and both are wrong about the definition.
#[test]
fn the_definition_is_retrievable_and_its_lemmas_do_not_stand_in_for_it() {
    let index = fixture();
    let definition = Query {
        name: Some("Rat.polyEval".to_owned()),
        kinds: vec![DeclKind::Definition],
        ..Query::default()
    };
    assert_eq!(names(&run(&index, &definition)), vec!["Rat.polyEval"]);

    // The lemmas are a different kind and must not satisfy the query.
    let as_theorem = Query {
        name: Some("Rat.polyEval".to_owned()),
        kinds: vec![DeclKind::Theorem],
        ..Query::default()
    };
    assert_eq!(run(&index, &as_theorem), Outcome::Absent);
}

/// GUARD: `--like` is order-insensitive over hypothesis heads, because
/// argument order is what a lane guessing at an unseen lemma gets wrong.
#[test]
fn like_key_ignores_hypothesis_order() {
    let forward = entry("A", DeclKind::Theorem, &["P", "Q"], "R");
    let reversed = entry("B", DeclKind::Theorem, &["Q", "P"], "R");
    assert_eq!(forward.like_key(), reversed.like_key());
    let different = entry("C", DeclKind::Theorem, &["P", "Q"], "S");
    assert_ne!(forward.like_key(), different.like_key());
}

/// GUARD: identical statements under different names are reported together.
/// A duplicate is worse than a delay — two proofs of one fact that must stay
/// in sync while the kernel happily verifies both.
#[test]
fn duplicate_shapes_are_grouped() {
    let mut index = ShapeIndex::new(vec!["synthetic".to_owned()], false);
    let mut first = entry("Pkg.alpha", DeclKind::Theorem, &["P"], "Q");
    let mut second = entry("Pkg.beta", DeclKind::Theorem, &["P"], "Q");
    first.shape = "SAME".to_owned();
    second.shape = "SAME".to_owned();
    index.insert(first);
    index.insert(second);
    index.insert(entry("Pkg.gamma", DeclKind::Theorem, &["P"], "R"));
    index.finish();
    let duplicates = index.duplicate_shapes();
    assert_eq!(duplicates.len(), 1);
    assert_eq!(duplicates[0].len(), 2);
}

// ---------------------------------------------------------------------------
// Absence must be a finding, and must be distinct from unanswerable
// ---------------------------------------------------------------------------

/// GUARD: a well-formed query over covered vocabulary that matches nothing is
/// `Absent` (status 1), NOT `Unanswerable`. Without this the tool could report
/// every zero as "I could not tell", which is as useless as reporting every
/// zero as absence.
#[test]
fn a_genuine_zero_is_absent_not_unanswerable() {
    let index = fixture();
    let query = Query {
        concl: Some("CReal.Equiv".to_owned()),
        hyps: vec!["CReal.le".to_owned()],
        arity: Some(9),
        ..Query::default()
    };
    assert_eq!(run(&index, &query), Outcome::Absent);
    assert_eq!(run(&index, &query).status(), 1);
}

/// GUARD: a constant the index does not declare makes the run unanswerable.
/// This is the structural positive control — you cannot receive "0 rows" for
/// vocabulary the index never carried, which is exactly how an empty grep gets
/// reported as a strong negative result.
#[test]
fn an_undeclared_constant_is_unanswerable() {
    let index = fixture();
    let query = Query {
        concl: Some("CReal.Equivv".to_owned()),
        ..Query::default()
    };
    let outcome = run(&index, &query);
    assert_eq!(outcome.status(), 3);
    match outcome {
        Outcome::Unanswerable(reasons) => {
            assert!(
                reasons.iter().any(|reason| reason.contains("CReal.Equivv")),
                "the reason must name the unresolved constant: {reasons:?}"
            );
        }
        other => panic!("expected Unanswerable, got {other:?}"),
    }
}

/// GUARD: the `AxNat` / `AxReal` trap. `AxNat.add` is a `lean_pp` EXPORT name;
/// no such kernel declaration exists, so querying it must be unanswerable
/// rather than a confident zero — and the "nearest declared" hint must point
/// at the real name.
#[test]
fn an_export_name_is_unanswerable_with_a_pointer_to_the_kernel_name() {
    let mut index = fixture();
    index.insert(entry("Nat.add", DeclKind::Definition, &["Nat"], "Nat"));
    index.insert(entry("Nat", DeclKind::Inductive, &[], "Sort"));
    index.finish();
    let query = Query {
        concl: Some("AxNat.add".to_owned()),
        ..Query::default()
    };
    match run(&index, &query) {
        Outcome::Unanswerable(reasons) => assert!(
            reasons.iter().any(|reason| reason.contains("Nat.add")),
            "the hint must name the kernel spelling: {reasons:?}"
        ),
        other => panic!("expected Unanswerable, got {other:?}"),
    }
}

/// GUARD: a query constraining nothing is unanswerable. An unconstrained query
/// matches the whole index, so it answers "yes" to every question and can
/// never report an absence.
#[test]
fn an_unconstrained_query_is_unanswerable() {
    let index = fixture();
    assert_eq!(run(&index, &Query::default()).status(), 3);
}

/// GUARD: `--value-const` without value indexing is unanswerable, not a zero.
/// Values are unread in that mode, so every answer would be vacuous.
#[test]
fn value_const_without_value_indexing_is_unanswerable() {
    let index = fixture();
    let query = Query {
        value_consts: vec!["CReal.le".to_owned()],
        ..Query::default()
    };
    assert_eq!(run(&index, &query).status(), 3);

    // …and with values indexed the same query is answerable.
    let mut with_values = ShapeIndex::new(vec!["synthetic".to_owned()], true);
    let mut row = entry("Pkg.thm", DeclKind::Theorem, &["P"], "Q");
    row.value_consts = Some(["CReal.le".to_owned()].into_iter().collect());
    with_values.insert(row);
    with_values.insert(entry("CReal.le", DeclKind::Definition, &["CReal"], "Prop"));
    with_values.finish();
    assert_eq!(names(&run(&with_values, &query)), vec!["Pkg.thm"]);
}

/// GUARD: a kind with zero indexed rows cannot report an absence. This is the
/// same-kind positive control made structural: asking a theorem-only index
/// about a definition is refused rather than answered.
#[test]
fn a_kind_the_index_does_not_carry_is_unanswerable() {
    let mut index = ShapeIndex::new(vec!["synthetic".to_owned()], false);
    index.insert(entry("Pkg.thm", DeclKind::Theorem, &["P"], "Q"));
    index.finish();
    let query = Query {
        name_contains: Some("thm".to_owned()),
        kinds: vec![DeclKind::Definition],
        ..Query::default()
    };
    assert_eq!(run(&index, &query).status(), 3);
}

/// GUARD: a namespace with zero indexed rows is unanswerable. This is the
/// "you did not build the package" case — asking about `CReal` without
/// `--include-constructed` must not answer "absent".
#[test]
fn an_unbuilt_namespace_is_unanswerable() {
    let mut index = ShapeIndex::new(vec!["nat".to_owned()], false);
    index.insert(entry("Nat.add", DeclKind::Definition, &["Nat"], "Nat"));
    index.finish();
    let query = Query {
        namespace: Some("CReal".to_owned()),
        name_contains: Some("integral".to_owned()),
        ..Query::default()
    };
    assert_eq!(run(&index, &query).status(), 3);

    // An exact `--name` carries its own namespace root, so the same guard
    // fires without `--namespace`.
    let by_name = Query {
        name: Some("CReal.integral".to_owned()),
        ..Query::default()
    };
    assert_eq!(run(&index, &by_name).status(), 3);
}

/// GUARD: an empty index is unanswerable rather than a universal absence.
#[test]
fn an_empty_index_is_unanswerable() {
    let index = ShapeIndex::new(Vec::new(), false);
    let query = Query {
        name_contains: Some("anything".to_owned()),
        ..Query::default()
    };
    assert_eq!(run(&index, &query).status(), 3);
}

/// GUARD: the namespace root is the FIRST dotted component, so `CReal` and
/// `AxReal` are distinct roots and neither is a prefix match of the other.
#[test]
fn namespace_root_is_the_first_component() {
    assert_eq!(namespace_root("CReal.integral_const"), "CReal");
    assert_eq!(namespace_root("AxReal.add_comm"), "AxReal");
    assert_eq!(namespace_root("Nat"), "Nat");
    assert_ne!(namespace_root("CReal.le"), namespace_root("AxReal.le"));
}

// ---------------------------------------------------------------------------
// Extraction from a real environment
// ---------------------------------------------------------------------------

/// GUARD: extraction indexes DEFINITIONS from a real kernel. `Nat.add` is the
/// canonical row that `prelude_theorem_inventory` returns zero of, and the
/// paired assertion is the same-kind control: the definition and a theorem
/// about it are both present and are distinguished by kind.
#[test]
fn the_nat_prelude_yields_definitions_and_theorems() {
    let mut kernel = Kernel::new();
    let _ = build_nat_prelude(&mut kernel).expect("Nat prelude must build");
    let mut index = ShapeIndex::new(vec!["nat".to_owned()], false);
    index_kernel(&kernel, "nat", &mut index, false);
    index.finish();

    let census = index.kind_census();
    assert!(
        census.get(&DeclKind::Definition).copied().unwrap_or(0) > 0,
        "the Nat prelude must contribute definitions: {census:?}"
    );
    assert!(
        census.get(&DeclKind::Theorem).copied().unwrap_or(0) > 0,
        "the Nat prelude must contribute theorems: {census:?}"
    );

    let definition = Query {
        name: Some("Nat.add".to_owned()),
        kinds: vec![DeclKind::Definition],
        ..Query::default()
    };
    assert_eq!(names(&run(&index, &definition)), vec!["Nat.add"]);

    let theorem = Query {
        name: Some("Nat.add_comm".to_owned()),
        kinds: vec![DeclKind::Theorem],
        ..Query::default()
    };
    assert_eq!(names(&run(&index, &theorem)), vec!["Nat.add_comm"]);

    // Kernel names, not export names: `AxNat.add` is not a declaration here.
    assert!(index.declares("Nat.add"));
    assert!(!index.declares("AxNat.add"));
}

/// GUARD: shape extraction is real — a hypothesis/conclusion query over the
/// built Nat environment retrieves `Nat.add_comm` without naming it.
#[test]
fn a_shape_query_over_the_nat_prelude_retrieves_by_structure() {
    let mut kernel = Kernel::new();
    let _ = build_nat_prelude(&mut kernel).expect("Nat prelude must build");
    let mut index = ShapeIndex::new(vec!["nat".to_owned()], false);
    index_kernel(&kernel, "nat", &mut index, false);
    index.finish();

    let query = Query {
        concl: Some("Eq".to_owned()),
        consts: vec!["Nat.add".to_owned()],
        kinds: vec![DeclKind::Theorem],
        namespace: Some("Nat".to_owned()),
        ..Query::default()
    };
    let found = names(&run(&index, &query));
    assert!(
        found.iter().any(|name| name == "Nat.add_comm"),
        "an equation about Nat.add must be retrievable by shape: {found:?}"
    );
}
