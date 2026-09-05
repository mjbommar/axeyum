//! Unit tests for the `by axeyum` bridge.
//!
//! These are the checks that do **not** need Lean: decoding, the fragment
//! boundary, and the correspondence gate. The checks that need Lean — does the
//! printed term actually close the goal — are in
//! `lean/axeyum-tactic/Tests/`, run by `scripts/check-lean-tactic.sh`, because
//! only Lean can answer them.
//!
//! Every negative here is paired with a positive control, because a decline is
//! also what a translator that recognizes nothing returns.

use serde_json::json;

use super::{Decline, Dev, Hypothesis, LeanExpr, NAME_MAP, Translator, decode, prove_to_lean_term};

/// `@HAdd.hAdd Nat Nat Nat inst a b`, the shape Lean elaborates `a + b` into.
fn nat_add(left: LeanExpr, right: LeanExpr) -> LeanExpr {
    app(vec![
        LeanExpr::Const("HAdd.hAdd".to_owned()),
        LeanExpr::Const("Nat".to_owned()),
        LeanExpr::Const("Nat".to_owned()),
        LeanExpr::Const("Nat".to_owned()),
        app(vec![
            LeanExpr::Const("instHAdd".to_owned()),
            LeanExpr::Const("Nat".to_owned()),
            LeanExpr::Const("instAddNat".to_owned()),
        ]),
        left,
        right,
    ])
}

/// `@Eq Nat lhs rhs`.
fn nat_eq(lhs: LeanExpr, rhs: LeanExpr) -> LeanExpr {
    app(vec![
        LeanExpr::Const("Eq".to_owned()),
        LeanExpr::Const("Nat".to_owned()),
        lhs,
        rhs,
    ])
}

/// `@LE.le Nat instLENat lhs rhs`.
fn nat_le(lhs: LeanExpr, rhs: LeanExpr) -> LeanExpr {
    app(vec![
        LeanExpr::Const("LE.le".to_owned()),
        LeanExpr::Const("Nat".to_owned()),
        LeanExpr::Const("instLENat".to_owned()),
        lhs,
        rhs,
    ])
}

fn app(parts: Vec<LeanExpr>) -> LeanExpr {
    let mut iter = parts.into_iter();
    let mut head = iter.next().expect("an application needs a head");
    for arg in iter {
        head = LeanExpr::App(Box::new(head), Box::new(arg));
    }
    head
}

fn fvar(name: &str) -> LeanExpr {
    LeanExpr::FVar(name.to_owned())
}

#[test]
fn decode_reads_the_shapes_the_tactic_emits() {
    let value = json!({
        "k": "app",
        "fn": {"k": "const", "name": "Nat.succ"},
        "arg": {"k": "fvar", "name": "n"}
    });
    let decoded = decode(&value).expect("this is the encoder's own shape");
    assert_eq!(
        decoded,
        LeanExpr::App(
            Box::new(LeanExpr::Const("Nat.succ".to_owned())),
            Box::new(LeanExpr::FVar("n".to_owned()))
        )
    );
}

#[test]
fn decode_refuses_an_unrecognized_node_kind() {
    // The positive control is the test above: the same decoder reads a
    // well-formed node. So this really is the node kind being refused.
    let value = json!({"k": "sort", "level": 1});
    let error = decode(&value).expect_err("`sort` is not one of the five encoded kinds");
    assert!(
        error.contains("sort"),
        "the error must name the offending kind, got {error}"
    );
}

#[test]
fn a_plus_b_equals_b_plus_a_prints_a_lean_term() {
    let mut dev = Dev::new().expect("the ℕ prelude must build");
    let goal = nat_eq(nat_add(fvar("a"), fvar("b")), nat_add(fvar("b"), fvar("a")));
    let term = prove_to_lean_term(&mut dev, &[], &goal).expect("ring closes commutativity");
    assert!(
        term.contains("Axeyum.Shim.natAddComm"),
        "the term must route commutativity through the proved shim, got {term}"
    );
    assert!(
        !term.contains("AxNat"),
        "no axeyum-side spelling may survive into the Lean term, got {term}"
    );
}

#[test]
fn a_is_at_most_a_plus_b_prints_a_lean_term() {
    let mut dev = Dev::new().expect("the ℕ prelude must build");
    let goal = nat_le(fvar("a"), nat_add(fvar("a"), fvar("b")));
    let term = prove_to_lean_term(&mut dev, &[], &goal).expect("linarith closes this");
    assert!(
        !term.contains("AxNat"),
        "no axeyum-side spelling may survive into the Lean term, got {term}"
    );
    assert!(
        term.contains("Axeyum.Shim."),
        "an order goal must reach at least one shim lemma, got {term}"
    );
}

#[test]
fn a_hypothesis_is_used_and_named_by_its_lean_name() {
    let mut dev = Dev::new().expect("the ℕ prelude must build");
    let hypothesis = Hypothesis {
        name: "hab".to_owned(),
        ty: nat_le(fvar("a"), fvar("b")),
    };
    let goal = nat_le(fvar("a"), nat_add(fvar("b"), fvar("c")));
    let term = prove_to_lean_term(&mut dev, &[hypothesis], &goal)
        .expect("linarith closes a ≤ b ⊢ a ≤ b + c");
    assert!(
        term.contains("hab"),
        "the term must refer to the hypothesis by its Lean name, got {term}"
    );
}

#[test]
fn the_same_goal_without_the_hypothesis_declines() {
    // The negative control for the test above: `a ≤ b + c` is not provable
    // without `a ≤ b`, so a bridge that ignored hypotheses entirely would fail
    // that test rather than passing it vacuously.
    let mut dev = Dev::new().expect("the ℕ prelude must build");
    let goal = nat_le(fvar("a"), nat_add(fvar("b"), fvar("c")));
    let declined = prove_to_lean_term(&mut dev, &[], &goal)
        .expect_err("a ≤ b + c is not provable with no hypothesis");
    assert_eq!(declined.reason(), "unknown");
}

#[test]
fn a_goal_at_the_wrong_type_is_unsupported() {
    let mut dev = Dev::new().expect("the ℕ prelude must build");
    // `@Eq Int a b` — the same shape, one constant different.
    let goal = app(vec![
        LeanExpr::Const("Eq".to_owned()),
        LeanExpr::Const("Int".to_owned()),
        fvar("a"),
        fvar("b"),
    ]);
    let declined = prove_to_lean_term(&mut dev, &[], &goal).expect_err("ℤ is not the ℕ fragment");
    assert_eq!(declined.reason(), "unsupported");
    assert!(
        declined.detail().contains("ℕ"),
        "the decline must say the fragment is ℕ, got {}",
        declined.detail()
    );
}

#[test]
fn addition_with_a_foreign_instance_is_refused() {
    // The type arguments say ℕ but the instance is not ℕ's. Nothing here is a
    // soundness boundary — Lean would refuse the resulting term — but reading
    // a different operation as `+` would produce a confusing far-end error
    // instead of a local one.
    let mut dev = Dev::new().expect("the ℕ prelude must build");
    let bogus = app(vec![
        LeanExpr::Const("HAdd.hAdd".to_owned()),
        LeanExpr::Const("Nat".to_owned()),
        LeanExpr::Const("Nat".to_owned()),
        LeanExpr::Const("Nat".to_owned()),
        LeanExpr::Const("myWeirdAddInstance".to_owned()),
        fvar("a"),
        fvar("b"),
    ]);
    let goal = nat_eq(bogus.clone(), bogus);
    let declined =
        prove_to_lean_term(&mut dev, &[], &goal).expect_err("a foreign `+` instance is refused");
    assert_eq!(declined.reason(), "unsupported");
    assert!(
        declined.detail().contains("instAddNat"),
        "the decline must name the instance it expected, got {}",
        declined.detail()
    );
}

#[test]
fn the_name_map_has_no_duplicate_left_hand_sides() {
    // A duplicate would make `mapped` silently prefer the first row, which is
    // exactly the kind of table defect no downstream test can see.
    let mut ours: Vec<&str> = NAME_MAP.iter().map(|(o, _, _)| *o).collect();
    let before = ours.len();
    ours.sort_unstable();
    ours.dedup();
    assert_eq!(before, ours.len(), "NAME_MAP has a duplicate kernel name");
    assert!(
        before >= 20,
        "the measured inventory is 20 constants; NAME_MAP has {before}"
    );
}

#[test]
fn every_shim_row_names_a_theorem_in_the_shim_file() {
    // The authority is the Lean file, not this list: a row that names a shim
    // theorem the file does not declare would print a term Lean cannot parse.
    let shim = include_str!("../../../../lean/axeyum-tactic/Axeyum/Shim.lean");
    let mut checked = 0_usize;
    for (ours, theirs, _) in NAME_MAP {
        let Some(short) = theirs.strip_prefix("Axeyum.Shim.") else {
            continue;
        };
        assert!(
            shim.contains(&format!("theorem {short} ")),
            "NAME_MAP maps `{ours}` to `{theirs}`, but Shim.lean declares no `theorem {short}`"
        );
        checked += 1;
    }
    assert!(
        checked >= 13,
        "the shim has 13 theorems; this test only checked {checked}, so it is not covering them"
    );
}

#[test]
fn a_constant_outside_the_name_map_is_the_gate_that_declines() {
    // The correspondence gate, exercised directly: `Translator` is fine with
    // `Nat.sub`-free goals, but a producer reaching a lemma with no shim row
    // must decline rather than print a name Lean does not have. The cheapest
    // honest way to see the gate fire is to ask for a goal whose proof needs a
    // prelude lemma outside the table.
    let mut dev = Dev::new().expect("the ℕ prelude must build");
    let mut translator = Translator::new();
    // `Nat.sub` is outside the term fragment, so the goal never reaches a
    // producer -- this asserts the FRAGMENT boundary. The name-map boundary
    // itself is asserted by `every_shim_row_names_a_theorem_in_the_shim_file`
    // (a row that vanished) and by the Lean-side battery (a term that cannot
    // parse).
    let goal = app(vec![
        LeanExpr::Const("Eq".to_owned()),
        LeanExpr::Const("Nat".to_owned()),
        app(vec![
            LeanExpr::Const("Nat.sub".to_owned()),
            fvar("a"),
            fvar("b"),
        ]),
        fvar("c"),
    ]);
    let declined = translator
        .prop(&mut dev, &goal)
        .expect_err("`Nat.sub` is not in the ℕ term fragment");
    assert_eq!(declined.reason(), "unsupported");
    assert!(
        matches!(declined, Decline::Unsupported(ref d) if d.contains("Nat.sub")),
        "the decline must name the head it did not recognize"
    );
}
