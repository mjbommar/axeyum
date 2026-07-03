//! Independent-checker tests for the T-B.7 derivation re-checker
//! ([`check_conflict`]).
//!
//! Two halves:
//!
//! - **acceptance** — every genuinely-refutable constant-clash shape produces a
//!   T-B.3 [`Conflict`] the re-checker confirms; and the shapes that are unsat but
//!   *not* an aligned constant clash (loops, parity) are **not** confirmed (they
//!   stay `unknown`);
//! - **rejection** — a valid conflict, then corrupted three ways (wrong premise
//!   set, wrong position, matching constants), must be rejected. The re-checker
//!   trusts nothing in the record: each corruption breaks re-derivation.

#![allow(clippy::many_single_char_names, clippy::similar_names)]

mod common;

use std::collections::BTreeSet;

use axeyum_ir::{TermArena, TermId};
use axeyum_strings::{
    Conflict, Fact, Rule, check_conflict, check_cycle_constant_conflict, check_fact, infer,
};
use common::{cat, ch, empty, seq_var, unit};

/// `"a"` and `"b"` as length-1 constant sequence terms.
fn ab(arena: &mut TermArena) -> (TermId, TermId) {
    let a = {
        let e = ch(arena, u128::from(b'a'));
        unit(arena, e)
    };
    let b = {
        let e = ch(arena, u128::from(b'b'));
        unit(arena, e)
    };
    (a, b)
}

/// The first conflict `infer` reports on `eqs`, or `None`.
fn conflict_of(arena: &mut TermArena, eqs: &[(TermId, TermId)]) -> Option<Conflict> {
    infer(arena, eqs).conflict().cloned()
}

// ----- acceptance ------------------------------------------------------------

#[test]
fn accepts_direct_constant_clash() {
    let mut arena = TermArena::new();
    let (a, b) = ab(&mut arena);
    let eqs = [(a, b)];
    let c = conflict_of(&mut arena, &eqs).expect("\"a\" = \"b\" conflicts");
    assert!(
        check_conflict(&mut arena, &eqs, &c),
        "the equal-length constant clash \"a\"=\"b\" must re-check"
    );
}

#[test]
fn accepts_suffix_clash_after_shared_variable_prefix() {
    // x ++ "a"  =  x ++ "b": the shared variable x aligns (same class), then the
    // trailing constants clash.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let (a, b) = ab(&mut arena);
    let lhs = cat(&mut arena, x, a);
    let rhs = cat(&mut arena, x, b);
    let eqs = [(lhs, rhs)];
    let c = conflict_of(&mut arena, &eqs).expect("x++\"a\" = x++\"b\" conflicts");
    assert!(
        check_conflict(&mut arena, &eqs, &c),
        "the suffix clash after a shared variable prefix must re-check"
    );
}

#[test]
fn accepts_prefix_clash_through_shared_class() {
    // x = "ab" ++ y  and  x = "ba" ++ y: via x, "ab"++y and "ba"++y are one class,
    // and the leading equal-length constant blocks clash.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let (unit_a, unit_b) = ab(&mut arena);
    let ab_block = cat(&mut arena, unit_a, unit_b); // "ab"
    let ba_block = cat(&mut arena, unit_b, unit_a); // "ba"
    let lhs = cat(&mut arena, ab_block, y);
    let rhs = cat(&mut arena, ba_block, y);
    let eqs = [(x, lhs), (x, rhs)];
    let conflict = conflict_of(&mut arena, &eqs).expect("\"ab\"++y = \"ba\"++y (via x) conflicts");
    assert!(
        check_conflict(&mut arena, &eqs, &conflict),
        "the prefix clash through a shared class must re-check"
    );
    // Its cited premises must both be in range and non-trivial.
    assert!(!conflict.premises.is_empty());
    assert!(conflict.premises.iter().all(|&p| p < eqs.len()));
}

#[test]
fn does_not_confirm_a_length_loop() {
    // x = "a" ++ x is unsat (|x| = 1 + |x|) but by a LENGTH argument, not an
    // aligned constant clash. Whatever `infer` does, the re-checker must not
    // certify it (it stays `unknown`).
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let a = {
        let e = ch(&mut arena, u128::from(b'a'));
        unit(&mut arena, e)
    };
    let rhs = cat(&mut arena, a, x);
    let eqs = [(x, rhs)];
    if let Some(c) = conflict_of(&mut arena, &eqs) {
        assert!(
            !check_conflict(&mut arena, &eqs, &c),
            "a length loop is not an aligned constant clash; it must NOT re-check"
        );
    }
}

#[test]
fn does_not_confirm_a_parity_contradiction() {
    // x = x ++ x with x != "" is unsat by parity/length, not a constant clash.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let rhs = cat(&mut arena, x, x);
    let eqs = [(x, rhs)];
    if let Some(c) = conflict_of(&mut arena, &eqs) {
        assert!(
            !check_conflict(&mut arena, &eqs, &c),
            "a parity contradiction must NOT re-check as a constant clash"
        );
    }
}

// ----- rejection of corrupted records ----------------------------------------

/// A known-good conflict over `x++"a" = x++"b"` plus its equalities, for the
/// corruption tests.
fn good_conflict() -> (TermArena, Vec<(TermId, TermId)>, Conflict) {
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let (a, b) = ab(&mut arena);
    let lhs = cat(&mut arena, x, a);
    let rhs = cat(&mut arena, x, b);
    let eqs = vec![(lhs, rhs)];
    let c = conflict_of(&mut arena, &eqs).expect("conflict");
    assert!(
        check_conflict(&mut arena, &eqs, &c),
        "the baseline conflict must re-check before we corrupt it"
    );
    (arena, eqs, c)
}

#[test]
fn rejects_empty_premise_set() {
    let (mut arena, eqs, c) = good_conflict();
    let corrupt = Conflict {
        premises: BTreeSet::new(), // no premises ⇒ members are not provably equal
        reason: c.reason,
    };
    assert!(
        !check_conflict(&mut arena, &eqs, &corrupt),
        "an empty premise set cannot entail member_a ≈ member_b"
    );
}

#[test]
fn rejects_out_of_range_premise() {
    let (mut arena, eqs, c) = good_conflict();
    let corrupt = Conflict {
        premises: BTreeSet::from([99]), // out of range
        reason: c.reason,
    };
    assert!(
        !check_conflict(&mut arena, &eqs, &corrupt),
        "an out-of-range premise index must be rejected"
    );
}

#[test]
fn rejects_wrong_position() {
    let (mut arena, eqs, c) = good_conflict();
    let mut reason = c.reason;
    reason.position_a += 3; // the clash is not at this position
    reason.position_b += 3;
    let corrupt = Conflict {
        premises: c.premises.clone(),
        reason,
    };
    assert!(
        !check_conflict(&mut arena, &eqs, &corrupt),
        "a position that does not match the independent walk must be rejected"
    );
}

#[test]
fn rejects_matching_constants() {
    // Corrupt the record so both clashing constants are the SAME term: no clash,
    // so nothing to certify.
    let (mut arena, eqs, c) = good_conflict();
    let mut reason = c.reason;
    reason.const_b = reason.const_a; // now they "match"
    let corrupt = Conflict {
        premises: c.premises.clone(),
        reason,
    };
    assert!(
        !check_conflict(&mut arena, &eqs, &corrupt),
        "a record whose two constants coincide describes no clash and must be rejected"
    );
}

#[test]
fn rejects_swapped_members_to_unrelated_terms() {
    // Point member_b at an unrelated fresh variable not connected by the premises.
    let (mut arena, eqs, c) = good_conflict();
    let z = seq_var(&mut arena, "z_unrelated");
    let mut reason = c.reason;
    reason.member_b = z;
    let corrupt = Conflict {
        premises: c.premises.clone(),
        reason,
    };
    assert!(
        !check_conflict(&mut arena, &eqs, &corrupt),
        "an unrelated member is not in the class the premises build; reject"
    );
}

// ----- check_fact: acceptance (slice 2) --------------------------------------

/// `"a"` as a length-1 constant sequence.
fn a_unit(arena: &mut TermArena) -> TermId {
    let e = ch(arena, u128::from(b'a'));
    unit(arena, e)
}

/// The first derived fact of `rule` in `infer(eqs)`, or `None`.
fn fact_of(arena: &mut TermArena, eqs: &[(TermId, TermId)], rule: Rule) -> Option<Fact> {
    infer(arena, eqs).facts().find(|f| f.rule == rule).cloned()
}

#[test]
fn accepts_cycle_epsilon_variable_target() {
    // x = y ++ x forces y ≈ ε (|x| = |y| + |x|). The derived CycleEpsilon fact must
    // re-check from its cited premise alone.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let rhs = cat(&mut arena, y, x);
    let eqs = [(x, rhs)];
    let fact = fact_of(&mut arena, &eqs, Rule::CycleEpsilon).expect("cycle forces y ≈ ε");
    assert!(
        check_fact(&mut arena, &eqs, &fact),
        "the self-loop ε fact y ≈ ε must re-check"
    );
    // It is a variable ε fact, NOT the nonempty-constant contradiction shape.
    assert!(!check_cycle_constant_conflict(&mut arena, &eqs, &fact));
}

#[test]
fn accepts_endpoint_emp_fact() {
    // x = "a" ++ z and x = "a"  ⇒  z ≈ ε (the exhausted-prefix tail). A CONSTANT
    // prefix, so this is an endpoint-emp alignment, not a containment cycle.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let z = seq_var(&mut arena, "z");
    let a = a_unit(&mut arena);
    let az = cat(&mut arena, a, z);
    let eqs = [(x, az), (x, a)];
    let fact = fact_of(&mut arena, &eqs, Rule::InferEndpointEmp).expect("endpoint-emp z ≈ ε");
    assert!(
        check_fact(&mut arena, &eqs, &fact),
        "the endpoint-emp fact z ≈ ε must re-check"
    );
}

#[test]
fn accepts_endpoint_eq_fact() {
    // x = "a" ++ z and x = "a" ++ w  ⇒  z ≈ w (single remainder each side).
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let z = seq_var(&mut arena, "z");
    let w = seq_var(&mut arena, "w");
    let a = a_unit(&mut arena);
    let az = cat(&mut arena, a, z);
    let aw = cat(&mut arena, a, w);
    let eqs = [(x, az), (x, aw)];
    let fact = fact_of(&mut arena, &eqs, Rule::InferEndpointEq).expect("endpoint-eq z ≈ w");
    assert!(
        check_fact(&mut arena, &eqs, &fact),
        "the endpoint-eq fact z ≈ w must re-check"
    );
}

#[test]
fn certifies_self_loop_nonempty_constant_as_conflict() {
    // x = "a" ++ x is unsat; infer emits a CycleEpsilon fact "a" ≈ ε whose honest
    // re-check FAILS as an ε fact (it is false) but certifies as a CONFLICT.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let a = a_unit(&mut arena);
    let rhs = cat(&mut arena, a, x);
    let eqs = [(x, rhs)];
    let fact = fact_of(&mut arena, &eqs, Rule::CycleEpsilon).expect("cycle forces \"a\" ≈ ε");
    assert!(
        !check_fact(&mut arena, &eqs, &fact),
        "\"a\" ≈ ε is not a valid ε fact — check_fact must decline it"
    );
    assert!(
        check_cycle_constant_conflict(&mut arena, &eqs, &fact),
        "the self-loop forcing a nonempty constant to ε is a certified contradiction"
    );
}

// ----- check_fact: rejection (slice 2) ---------------------------------------

#[test]
fn rejects_cycle_epsilon_fact_with_empty_premises() {
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let rhs = cat(&mut arena, y, x);
    let eqs = [(x, rhs)];
    let mut fact = fact_of(&mut arena, &eqs, Rule::CycleEpsilon).expect("cycle fact");
    fact.premises = BTreeSet::new(); // no premise ⇒ no witnessing endpoint
    assert!(
        !check_fact(&mut arena, &eqs, &fact),
        "an empty premise set cannot re-derive the cycle ε fact"
    );
}

#[test]
fn rejects_cycle_epsilon_fact_with_out_of_range_premise() {
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let rhs = cat(&mut arena, y, x);
    let eqs = [(x, rhs)];
    let mut fact = fact_of(&mut arena, &eqs, Rule::CycleEpsilon).expect("cycle fact");
    fact.premises = BTreeSet::from([99]);
    assert!(!check_fact(&mut arena, &eqs, &fact));
}

#[test]
fn rejects_cycle_epsilon_fact_with_wrong_target() {
    // Corrupt y ≈ ε into z ≈ ε where z is unrelated to the cycle: not re-derivable.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let z = seq_var(&mut arena, "z_unrelated");
    let rhs = cat(&mut arena, y, x);
    let eqs = [(x, rhs)];
    let fact = fact_of(&mut arena, &eqs, Rule::CycleEpsilon).expect("cycle fact");
    let eps = empty(&mut arena);
    let corrupt = Fact {
        rule: Rule::CycleEpsilon,
        equality: if z <= eps { (z, eps) } else { (eps, z) },
        premises: fact.premises.clone(),
    };
    assert!(
        !check_fact(&mut arena, &eqs, &corrupt),
        "an unrelated ε target is not forced by the cited cycle premise"
    );
}

#[test]
fn rejects_endpoint_eq_fact_pointed_at_unrelated_terms() {
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let z = seq_var(&mut arena, "z");
    let w = seq_var(&mut arena, "w");
    let u = seq_var(&mut arena, "u_unrelated");
    let a = a_unit(&mut arena);
    let az = cat(&mut arena, a, z);
    let aw = cat(&mut arena, a, w);
    let eqs = [(x, az), (x, aw)];
    let fact = fact_of(&mut arena, &eqs, Rule::InferEndpointEq).expect("endpoint-eq fact");
    let corrupt = Fact {
        rule: Rule::InferEndpointEq,
        equality: if z <= u { (z, u) } else { (u, z) }, // z ≈ u_unrelated, not z ≈ w
        premises: fact.premises.clone(),
    };
    assert!(
        !check_fact(&mut arena, &eqs, &corrupt),
        "the aligned remainders are z and w, not an unrelated u"
    );
}
