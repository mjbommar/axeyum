//! Hand-built cases for the T-B.3 inference slice: cycle ε-inference (self-loop
//! and a two-class cycle), `INFER_UNIFY` (equal-length units) plus
//! `INFER_ENDPOINT_EQ`, `INFER_ENDPOINT_EMP`, a constant-clash `Conflict` with
//! exact premises, the fixpoint using a derived ε to reconcile a class T-B.2
//! alone declined, and a determinism check.
#![allow(clippy::many_single_char_names)] // deliberately mirrors x, y, z, a, … word-equation vars

mod common;

use std::collections::BTreeSet;

use axeyum_ir::{Assignment, TermArena, TermId, Value, eval};
use axeyum_strings::{Classes, Declined, Inference, Rule, infer};
use common::{cat, ch, empty, seq_sort, unit};

/// A `Seq(BitVec 8)` variable term.
fn svar(arena: &mut TermArena, name: &str) -> TermId {
    let s = arena.declare(name, seq_sort()).expect("declare seq var");
    arena.var(s)
}

/// A `seq.unit` over a *variable* 8-bit element (a length-1 but non-constant
/// sequence — the genuine `INFER_UNIFY` trigger).
fn unit_var(arena: &mut TermArena, name: &str) -> TermId {
    let e = arena.bv_var(name, 8).expect("bv var");
    unit(arena, e)
}

/// Whether the inference list contains a `Fact` with the given rule and
/// (unordered) equality.
fn has_fact(inf: &axeyum_strings::Inferences, rule: Rule, a: TermId, b: TermId) -> bool {
    let want = if a <= b { (a, b) } else { (b, a) };
    inf.facts().any(|f| f.rule == rule && f.equality == want)
}

/// The premises of the first `Fact` matching `(rule, equality)`.
fn fact_premises(
    inf: &axeyum_strings::Inferences,
    rule: Rule,
    a: TermId,
    b: TermId,
) -> BTreeSet<usize> {
    let want = if a <= b { (a, b) } else { (b, a) };
    inf.facts()
        .find(|f| f.rule == rule && f.equality == want)
        .map(|f| f.premises.clone())
        .expect("fact present")
}

/// The empty sequence term (built once) for equality lookups.
fn eps(arena: &mut TermArena) -> TermId {
    empty(arena)
}

// ----- rule a: cycle ε-inference ---------------------------------------------

#[test]
fn self_cycle_infers_epsilon() {
    // x ≈ y ++ x  forces  y ≈ ε.
    let mut arena = TermArena::new();
    let x = svar(&mut arena, "x");
    let y = svar(&mut arena, "y");
    let yx = cat(&mut arena, y, x);

    let eqs = [(x, yx)];
    let inf = infer(&mut arena, &eqs);
    let e = eps(&mut arena);

    assert!(!inf.is_conflict(), "no conflict on a satisfiable loop");
    assert!(!inf.hit_budget, "fixpoint converges");
    assert!(
        has_fact(&inf, Rule::CycleEpsilon, y, e),
        "x ≈ y ++ x must infer y ≈ ε, got {:?}",
        inf.items
    );
    // The only premise is the single asserted equality.
    assert_eq!(
        fact_premises(&inf, Rule::CycleEpsilon, y, e),
        BTreeSet::from([0]),
        "cites exactly the loop equality"
    );
}

#[test]
fn two_class_cycle_infers_epsilon_on_both_arms() {
    // x ≈ y ++ a, a ≈ z ++ x : a mutual containment cycle ⇒ y ≈ ε and z ≈ ε.
    let mut arena = TermArena::new();
    let x = svar(&mut arena, "x");
    let a = svar(&mut arena, "a");
    let y = svar(&mut arena, "y");
    let z = svar(&mut arena, "z");
    let ya = cat(&mut arena, y, a);
    let zx = cat(&mut arena, z, x);

    let eqs = [(x, ya), (a, zx)];
    let inf = infer(&mut arena, &eqs);
    let e = eps(&mut arena);

    assert!(!inf.is_conflict());
    assert!(!inf.hit_budget);
    assert!(has_fact(&inf, Rule::CycleEpsilon, y, e), "y ≈ ε");
    assert!(has_fact(&inf, Rule::CycleEpsilon, z, e), "z ≈ ε");
    // The cycle spans both asserted equalities.
    assert_eq!(
        fact_premises(&inf, Rule::CycleEpsilon, y, e),
        BTreeSet::from([0, 1])
    );
    assert_eq!(
        fact_premises(&inf, Rule::CycleEpsilon, z, e),
        BTreeSet::from([0, 1])
    );
}

// ----- rule b: INFER_UNIFY (+ endpoint eq for the tail) -----------------------

#[test]
fn unify_equal_length_units_then_endpoint_eq() {
    // unit(p) ++ x ≈ unit(q) ++ y : the length-1 units unify, then the single
    // remaining tails are equal.
    let mut arena = TermArena::new();
    let up = unit_var(&mut arena, "p");
    let uq = unit_var(&mut arena, "q");
    let x = svar(&mut arena, "x");
    let y = svar(&mut arena, "y");
    let m1 = cat(&mut arena, up, x);
    let m2 = cat(&mut arena, uq, y);

    let eqs = [(m1, m2)];
    let inf = infer(&mut arena, &eqs);

    assert!(!inf.is_conflict());
    assert!(
        has_fact(&inf, Rule::InferUnify, up, uq),
        "unit(p) ≈ unit(q) by equal structural length, got {:?}",
        inf.items
    );
    assert!(
        has_fact(&inf, Rule::InferEndpointEq, x, y),
        "x ≈ y as the aligned single tails"
    );
    // Both cite only the asserted equality.
    assert_eq!(
        fact_premises(&inf, Rule::InferUnify, up, uq),
        BTreeSet::from([0])
    );
}

#[test]
fn constant_prefix_then_endpoint_eq() {
    // "a" ++ x ≈ "a" ++ y : the shared constant advances, then x ≈ y.
    let mut arena = TermArena::new();
    let ca = ch(&mut arena, b'a'.into());
    let ua = unit(&mut arena, ca);
    let x = svar(&mut arena, "x");
    let y = svar(&mut arena, "y");
    let m1 = cat(&mut arena, ua, x);
    let ua2 = unit(&mut arena, ca);
    let m2 = cat(&mut arena, ua2, y);

    let eqs = [(m1, m2)];
    let inf = infer(&mut arena, &eqs);

    assert!(!inf.is_conflict());
    assert!(
        has_fact(&inf, Rule::InferEndpointEq, x, y),
        "shared 'a' prefix ⇒ x ≈ y, got {:?}",
        inf.items
    );
}

// ----- rule c: INFER_ENDPOINT_EMP --------------------------------------------

#[test]
fn endpoint_empty_forces_tail_epsilon() {
    // x ++ y ≈ x ++ y ++ z : the extra tail component must be ε (no cycle here —
    // x, y, z are independent).
    let mut arena = TermArena::new();
    let x = svar(&mut arena, "x");
    let y = svar(&mut arena, "y");
    let z = svar(&mut arena, "z");
    let m1 = cat(&mut arena, x, y);
    let xy = cat(&mut arena, x, y);
    let m2 = cat(&mut arena, xy, z);

    let eqs = [(m1, m2)];
    let inf = infer(&mut arena, &eqs);
    let e = eps(&mut arena);

    assert!(!inf.is_conflict());
    assert!(
        has_fact(&inf, Rule::InferEndpointEmp, z, e),
        "x++y ≈ x++y++z ⇒ z ≈ ε, got {:?}",
        inf.items
    );
}

#[test]
fn endpoint_empty_via_cycle_shape() {
    // x ++ y ≈ x : the task's ENDPOINT_EMP shape; mechanically a self-loop, so
    // the ε fact is derived (as a cycle inference). Either way y ≈ ε.
    let mut arena = TermArena::new();
    let x = svar(&mut arena, "x");
    let y = svar(&mut arena, "y");
    let xy = cat(&mut arena, x, y);

    let eqs = [(xy, x)];
    let inf = infer(&mut arena, &eqs);
    let e = eps(&mut arena);

    assert!(!inf.is_conflict());
    assert!(
        inf.facts()
            .any(|f| f.equality == (y.min(e), y.max(e)) || f.equality == (e.min(y), e.max(y))),
        "x++y ≈ x ⇒ y ≈ ε, got {:?}",
        inf.items
    );
}

// ----- constant-clash Conflict with exact premises ---------------------------

#[test]
fn constant_clash_is_a_conflict_with_exact_premises() {
    // x ≈ "a" (0), x ≈ "b" (1): x is forced to two distinct constants.
    let mut arena = TermArena::new();
    let x = svar(&mut arena, "x");
    let ca = ch(&mut arena, b'a'.into());
    let cb = ch(&mut arena, b'b'.into());
    let ua = unit(&mut arena, ca);
    let ub = unit(&mut arena, cb);

    let eqs = [(x, ua), (x, ub)];
    let inf = infer(&mut arena, &eqs);

    let conflict = inf.conflict().expect("distinct constants are a conflict");
    assert_eq!(
        conflict.premises,
        BTreeSet::from([0, 1]),
        "cites exactly the two asserted equalities"
    );
    assert_eq!(conflict.reason.rule, "const-clash");
    // The clashing constants are the two unit blocks (in some aligned order).
    let clash = {
        let mut v = [conflict.reason.const_a, conflict.reason.const_b];
        v.sort_unstable();
        v
    };
    let want = {
        let mut v = [ua, ub];
        v.sort_unstable();
        v
    };
    assert_eq!(clash, want, "reason records the clashing constant blocks");
}

#[test]
fn constant_clash_through_a_chain() {
    // x ≈ y (0), y ≈ "a" (1), x ≈ "b" (2): the clash needs the whole chain.
    let mut arena = TermArena::new();
    let x = svar(&mut arena, "x");
    let y = svar(&mut arena, "y");
    let ca = ch(&mut arena, b'a'.into());
    let ua = unit(&mut arena, ca);
    let cb = ch(&mut arena, b'b'.into());
    let ub = unit(&mut arena, cb);

    let eqs = [(x, y), (y, ua), (x, ub)];
    let inf = infer(&mut arena, &eqs);

    let conflict = inf.conflict().expect("chain forces a clash");
    assert_eq!(
        conflict.premises,
        BTreeSet::from([0, 1, 2]),
        "the whole chain is cited"
    );
}

// ----- fixpoint: a derived ε reconciles what T-B.2 declined -------------------

#[test]
fn derived_epsilon_reconciles_a_declined_class() {
    // y ++ w ≈ w : T-B.2 alone declines (Declined::Cycle); T-B.3 derives w's
    // loop component w ≈ ... no — derives y ≈ ε, which breaks the loop, and the
    // fixpoint then reaches a clean state with no further inference.
    let mut arena = TermArena::new();
    let y = svar(&mut arena, "y");
    let w = svar(&mut arena, "w");
    let yw = cat(&mut arena, y, w);
    let eqs = [(yw, w)];

    // T-B.2 substrate declines on the containment cycle.
    let classes = Classes::new(&eqs);
    assert!(
        matches!(
            classes.normal_forms(&mut arena),
            Err(Declined::Cycle { .. })
        ),
        "T-B.2 declines the loop"
    );

    // T-B.3 derives y ≈ ε and converges.
    let inf = infer(&mut arena, &eqs);
    let e = eps(&mut arena);
    assert!(!inf.is_conflict());
    assert!(
        !inf.hit_budget,
        "the ε breaks the loop, so the fixpoint converges"
    );
    assert!(has_fact(&inf, Rule::CycleEpsilon, y, e), "y ≈ ε");

    // Feeding the derived ε back reaches a fixpoint: no new inference.
    let augmented = [(yw, w), (y, e)];
    let inf2 = infer(&mut arena, &augmented);
    assert!(!inf2.is_conflict());
    // Every derived fact of the augmented run is already implied ε-collapse; the
    // loop no longer re-derives (idempotent w.r.t. the ε we added).
    assert!(
        !inf2.facts().any(|f| f.rule == Rule::CycleEpsilon
            && f.equality == (y.min(e), y.max(e))
            && f.premises == BTreeSet::from([0])),
        "the ε already present is not re-derived from the loop premise alone"
    );
}

// ----- soundness spot-check: derived facts evaluate true ---------------------

#[test]
fn derived_facts_hold_under_a_witness_model() {
    // A model where x++y ≈ x++y++z with z = ε: the derived z ≈ ε must hold.
    let mut arena = TermArena::new();
    let x = svar(&mut arena, "x");
    let y = svar(&mut arena, "y");
    let z = svar(&mut arena, "z");
    let m1 = cat(&mut arena, x, y);
    let xy = cat(&mut arena, x, y);
    let m2 = cat(&mut arena, xy, z);

    let eqs = [(m1, m2)];
    let inf = infer(&mut arena, &eqs);

    for f in inf.facts() {
        let (a, b) = f.equality;
        let va = eval(&arena, a, &Assignment::new());
        let vb = eval(&arena, b, &Assignment::new());
        // Only the ε target is closed here; check the closed side is empty.
        if let (Ok(Value::Seq(sa)), Ok(Value::Seq(sb))) = (&va, &vb) {
            assert_eq!(sa, sb, "closed fact sides must be equal");
        }
    }
    // z ≈ ε specifically.
    assert!(inf.facts().any(|f| {
        let (a, b) = f.equality;
        (a == z || b == z) && f.rule == Rule::InferEndpointEmp
    }));
}

// ----- determinism ------------------------------------------------------------

#[test]
fn inference_is_byte_identical_across_runs() {
    fn run() -> Vec<Inference> {
        let mut arena = TermArena::new();
        let x = svar(&mut arena, "x");
        let a = svar(&mut arena, "a");
        let y = svar(&mut arena, "y");
        let z = svar(&mut arena, "z");
        let ya = cat(&mut arena, y, a);
        let zx = cat(&mut arena, z, x);
        let up = unit_var(&mut arena, "p");
        let uq = unit_var(&mut arena, "q");
        let m1 = cat(&mut arena, up, x);
        let m2 = cat(&mut arena, uq, a);
        let eqs = [(x, ya), (a, zx), (m1, m2)];
        infer(&mut arena, &eqs).items
    }
    assert_eq!(run(), run(), "inference output must be deterministic");
}
