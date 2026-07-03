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

mod common;

use std::collections::BTreeSet;

use axeyum_ir::{TermArena, TermId};
use axeyum_strings::{Conflict, check_conflict, infer};
use common::{cat, ch, seq_var, unit};

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
