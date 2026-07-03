//! **Mutation-hardening tests for the T-B.7 derivation re-checker.**
//!
//! These tests were written to kill mutants surfaced by `cargo mutants` over
//! `src/check_derivation.rs`. Each targets the *accept path* of
//! [`check_conflict`](axeyum_strings::check_conflict),
//! [`check_fact`](axeyum_strings::check_fact),
//! [`check_equality`](axeyum_strings::check_equality), and
//! [`check_cycle_constant_conflict`](axeyum_strings::check_cycle_constant_conflict)
//! — the logic whose corruption could let a bogus derivation certify an unsound
//! `unsat`.
//!
//! The guiding principle: a mutation is **dangerous** iff it makes a checker
//! return `true` (certify) on an input the real checker rejects, or crashes on a
//! reachable input. Every such mutation is killed here by a hand-built record that
//! drives the exact branch. Mutations that only make a checker *decline more*
//! (return `false` where the real one certifies) are soundness-preserving and are
//! documented in the commit body, not killed here — though several are killed as a
//! side effect of the acceptance cases below.
//!
//! Records are hand-built (the `pub` fields of [`Conflict`]/[`Fact`]) so a test can
//! aim a specific member/premise/position at a specific walk branch, exactly as a
//! *corrupted* record from a buggy search would.

#![allow(clippy::many_single_char_names, clippy::similar_names)]

mod common;

use std::collections::BTreeSet;

use axeyum_ir::{TermArena, TermId};
use axeyum_strings::{
    Conflict, ConflictReason, Fact, Rule, check_conflict, check_cycle_constant_conflict,
    check_equality, check_fact, concat_components, infer, normalize,
};
use common::{bv_var, cat, ch, empty, seq_var, unit};

// ----- shared builders --------------------------------------------------------

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

/// A constant unit for an arbitrary char.
fn cunit(arena: &mut TermArena, c: u8) -> TermId {
    let e = ch(arena, u128::from(c));
    unit(arena, e)
}

/// A `seq.unit` over a fresh 8-bit *element variable* (an opaque, non-constant
/// unit of known length 1).
fn var_unit(arena: &mut TermArena, name: &str) -> TermId {
    let e = bv_var(arena, name);
    unit(arena, e)
}

/// The normalized, ε-dropped component vector of `t` — the same view the checker
/// walks.
fn comps(arena: &mut TermArena, t: TermId) -> Vec<TermId> {
    let n = normalize(arena, t);
    concat_components(arena, n)
}

/// An ordered (min, max) [`TermId`] pair (facts store equalities that way).
fn opair(a: TermId, b: TermId) -> (TermId, TermId) {
    if a <= b { (a, b) } else { (b, a) }
}

/// A hand-built [`Conflict`] over two members, citing `prem`, whose recorded clash
/// is at aligned component positions `(i, j)` — the constants are read from the
/// members' own normalized vectors, so a *valid* record is trivial to build and a
/// *corrupt* one is built by passing mismatched `(i, j)`.
fn conflict_at(
    arena: &mut TermArena,
    ma: TermId,
    mb: TermId,
    prem: &[usize],
    i: usize,
    j: usize,
) -> Conflict {
    let a = comps(arena, ma);
    let b = comps(arena, mb);
    Conflict {
        premises: prem.iter().copied().collect(),
        reason: ConflictReason {
            rule: "test",
            member_a: ma,
            member_b: mb,
            position_a: i,
            position_b: j,
            const_a: a[i],
            const_b: b[j],
        },
    }
}

// ===== check_conflict: the record cross-check (line 140) ======================

/// 140:31 `|| -> &&` — the position cross-check must reject when **either** aligned
/// position disagrees with the independent walk, not only when *both* do.
#[test]
fn conflict_rejects_single_wrong_position() {
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let (a, b) = ab(&mut arena);
    let lhs = cat(&mut arena, x, a); // x ++ "a"  -> [x, "a"]
    let rhs = cat(&mut arena, x, b); // x ++ "b"  -> [x, "b"]
    let eqs = [(lhs, rhs)];
    // Genuine clash is at (1, 1). Corrupt ONLY position_a.
    let mut c = conflict_at(&mut arena, lhs, rhs, &[0], 1, 1);
    c.reason.position_a = 0; // now position_a is wrong, position_b still right
    assert!(
        !check_conflict(&mut arena, &eqs, &c),
        "a record whose position_a disagrees with the walk must be rejected"
    );
}

// ===== check_equality (lines 162-177) — no direct test existed ================

#[test]
fn equality_certifies_only_when_premises_connect() {
    let mut arena = TermArena::new();
    let a = seq_var(&mut arena, "a");
    let b = seq_var(&mut arena, "b");
    let c = seq_var(&mut arena, "c_unrelated");
    let eqs = [(a, b)];

    // Connected: premise 0 places a, b in one class.
    assert!(
        check_equality(&eqs, &BTreeSet::from([0]), a, b),
        "premise a=b entails a ≈ b"
    );
    // Unconnected: c is not reachable from the cited premise.
    assert!(
        !check_equality(&eqs, &BTreeSet::from([0]), a, c),
        "an unrelated term is not entailed equal"
    );
    // Out-of-range premise index must be rejected (never panic / index oob).
    assert!(
        !check_equality(&eqs, &BTreeSet::from([99]), a, b),
        "an out-of-range premise index must be rejected"
    );
}

// ===== check_cycle_constant_conflict guard (line 220) =========================

/// 220:40 `|| -> &&` — the function must fire **only** for a `CycleEpsilon`-labeled
/// fact; a fact of another rule (even one with a genuine self-loop witness) is
/// declined by the rule guard.
#[test]
fn cycle_constant_conflict_requires_cycle_epsilon_rule() {
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let a = cunit(&mut arena, b'a');
    let rhs = cat(&mut arena, a, x); // x = "a" ++ x
    let eqs = [(x, rhs)];
    let good = infer(&mut arena, &eqs)
        .facts()
        .find(|f| f.rule == Rule::CycleEpsilon)
        .cloned()
        .expect("self-loop CycleEpsilon fact");
    assert!(
        check_cycle_constant_conflict(&mut arena, &eqs, &good),
        "baseline: the labeled cycle-constant fact certifies"
    );
    // Relabel the rule; the guard must now decline.
    let relabeled = Fact {
        rule: Rule::InferUnify,
        equality: good.equality,
        premises: good.premises.clone(),
    };
    assert!(
        !check_cycle_constant_conflict(&mut arena, &eqs, &relabeled),
        "a non-CycleEpsilon rule must be declined by the rule guard"
    );
}

// ===== check_endpoint_emp_fact (lines 293-326) ================================

/// 298:5 `-> true`, 316:17 / 317:17 `&& -> ||` — an endpoint-emp fact for a target
/// that is **not** forced to ε (the prefix does not exhaust the shorter member)
/// must be declined.
#[test]
fn endpoint_emp_declines_unforced_target() {
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let z = seq_var(&mut arena, "z");
    let w = seq_var(&mut arena, "w");
    let a = cunit(&mut arena, b'a');
    let az = cat(&mut arena, a, z); // "a" ++ z
    let aw = cat(&mut arena, a, w); // "a" ++ w
    let eqs = [(x, az), (x, aw)];
    // z ≈ ε is NOT entailed (x = "a"++z = "a"++w only gives z ≈ w).
    let eps = empty(&mut arena);
    let fact = Fact {
        rule: Rule::InferEndpointEmp,
        equality: opair(z, eps),
        premises: BTreeSet::from([0, 1]),
    };
    assert!(
        !check_fact(&mut arena, &eqs, &fact),
        "z is not forced to ε here; endpoint-emp must decline"
    );
}

/// 308:23 `|| -> &&` — endpoint-emp must only consider **provably-equal** (same
/// class) endpoints; a cross-class pair must never witness a fact.
#[test]
fn endpoint_emp_rejects_cross_class_witness() {
    let mut arena = TermArena::new();
    // Two disjoint classes: (L, L2) and (R, R2).
    let l2 = seq_var(&mut arena, "l2");
    let r2 = seq_var(&mut arena, "r2");
    let t = seq_var(&mut arena, "t"); // the ε-target
    let a = cunit(&mut arena, b'a');
    let l = cat(&mut arena, a, t); // "a" ++ t   -> [ "a", t ]
    let r = a; // "a"                -> [ "a" ]
    let eqs = [(l, l2), (r, r2)];
    let eps = empty(&mut arena);
    let fact = Fact {
        rule: Rule::InferEndpointEmp,
        equality: opair(t, eps),
        premises: BTreeSet::from([0, 1]),
    };
    // Under the real code L and R are in different classes → no witness → false.
    // A mutant that drops the same-class guard would pair (L, R) and certify t ≈ ε.
    assert!(
        !check_fact(&mut arena, &eqs, &fact),
        "endpoint-emp must not witness across unequal (cross-class) endpoints"
    );
}

/// 319:33 / 319:57 `== -> !=` — the tail must actually **contain the target**; a
/// tail cell that is neither the target nor in its class must not satisfy the
/// occurrence test.
#[test]
fn endpoint_emp_requires_target_in_tail() {
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let p = seq_var(&mut arena, "p");
    let q = seq_var(&mut arena, "q_absent");
    let a = cunit(&mut arena, b'a');
    let ap = cat(&mut arena, a, p); // "a" ++ p
    let eqs = [(x, ap), (x, a)]; // x = "a"++p and x = "a"  ⇒ p ≈ ε, but NOT q ≈ ε
    let eps = empty(&mut arena);
    // Claim q ≈ ε; q is absent from the tail (the tail is [p]).
    let fact = Fact {
        rule: Rule::InferEndpointEmp,
        equality: opair(q, eps),
        premises: BTreeSet::from([0, 1]),
    };
    assert!(
        !check_fact(&mut arena, &eqs, &fact),
        "the tail contains p, not q; q ≈ ε must not certify"
    );
}

/// 460:5 `consume_equal_prefix -> 1` — the prefix length must be *computed*, not
/// assumed to be 1. Here the two members share **no** aligned prefix, so a forced
/// length of 1 would falsely satisfy the exhaustion check.
#[test]
fn endpoint_emp_uses_real_prefix_length() {
    let mut arena = TermArena::new();
    let p = seq_var(&mut arena, "p");
    let tgt = seq_var(&mut arena, "tgt");
    let q = seq_var(&mut arena, "q");
    let ptgt = cat(&mut arena, p, tgt); // p ++ tgt   -> [p, tgt]
    let eqs = [(ptgt, q)]; // (p ++ tgt) ≈ q ; no shared prefix cell
    let eps = empty(&mut arena);
    let fact = Fact {
        rule: Rule::InferEndpointEmp,
        equality: opair(tgt, eps),
        premises: BTreeSet::from([0]),
    };
    // Real consume_equal_prefix([p,tgt],[q]) = 0 (p and q don't align) → false.
    // A forced length of 1 would make it look like q was exhausted → certify.
    assert!(
        !check_fact(&mut arena, &eqs, &fact),
        "no aligned prefix exists; a computed prefix length of 0 must decline"
    );
}

// ===== check_endpoint_eq_fact (lines 331-356) =================================

/// 341:23 `|| -> &&` — endpoint-eq must only align **same-class** endpoints; a
/// cross-class pair must not certify c ≈ d.
#[test]
fn endpoint_eq_rejects_cross_class_witness() {
    let mut arena = TermArena::new();
    let l2 = seq_var(&mut arena, "l2");
    let r2 = seq_var(&mut arena, "r2");
    let c1 = seq_var(&mut arena, "c1");
    let d1 = seq_var(&mut arena, "d1");
    let a = cunit(&mut arena, b'a');
    let l = cat(&mut arena, a, c1); // "a" ++ c1
    let r = cat(&mut arena, a, d1); // "a" ++ d1
    let eqs = [(l, l2), (r, r2)]; // L and R are in DIFFERENT classes
    let fact = Fact {
        rule: Rule::InferEndpointEq,
        equality: opair(c1, d1),
        premises: BTreeSet::from([0, 1]),
    };
    assert!(
        !check_fact(&mut arena, &eqs, &fact),
        "c1 ≈ d1 is not entailed across unequal endpoints"
    );
}

/// 346:30 `|| -> &&` — the empty-side skip must trigger when **either** member
/// normalizes to the empty vector; otherwise `na.len() - 1` underflows (panic).
#[test]
fn endpoint_eq_handles_empty_member() {
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let p = seq_var(&mut arena, "p_unmatched");
    let q = seq_var(&mut arena, "q_unmatched");
    let eps = empty(&mut arena);
    // x ≈ ε and x ≈ y put ε (empty component vector) and y in one class; the class
    // therefore contains an endpoint (ε) whose component vector is empty.
    let eqs = [(x, eps), (x, y)];
    // The claimed equality is unmatched, so the *real* checker returns false — but
    // it must still visit (and skip) the empty-normalizing ε endpoint. A mutant
    // that processes the empty side computes `0 - 1` and panics.
    let fact = Fact {
        rule: Rule::InferEndpointEq,
        equality: opair(p, q),
        premises: BTreeSet::from([0, 1]),
    };
    assert!(
        !check_fact(&mut arena, &eqs, &fact),
        "an empty-normalizing member must be skipped, not indexed"
    );
}

/// 450:36 `== -> !=` in `pair_equal_length` — two cells of **different** known
/// length must not be treated as equal-length (which would misalign the prefix).
#[test]
fn endpoint_eq_rejects_unequal_length_alignment() {
    let mut arena = TermArena::new();
    let u = var_unit(&mut arena, "u_elem"); // known length 1
    let c1 = seq_var(&mut arena, "c1");
    let xy = {
        let x = cunit(&mut arena, b'x');
        let y = cunit(&mut arena, b'y');
        cat(&mut arena, x, y) // "xy" — known length 2
    };
    let d1 = seq_var(&mut arena, "d1");
    let l = cat(&mut arena, u, c1); // unit(e) ++ c1   -> [unit(e), c1]
    let r = cat(&mut arena, xy, d1); // "xy" ++ d1      -> ["xy", d1]
    let eqs = [(l, r)];
    let fact = Fact {
        rule: Rule::InferEndpointEq,
        equality: opair(c1, d1),
        premises: BTreeSet::from([0]),
    };
    // Cell 0 lengths are 1 vs 2 → not equal-length → no aligned prefix → the
    // single-remainder shape is not reached → decline. A mutant treating unequal
    // lengths as equal would align and certify c1 ≈ d1.
    assert!(
        !check_fact(&mut arena, &eqs, &fact),
        "unequal-length lead cells must not align"
    );
}

// ===== check_unify_fact (lines 358-385) — no acceptance test existed ==========

/// `InferUnify` acceptance at an **interior** aligned position (kills the
/// whole-function replacements, the loop-bound mutants, and the `i += 1` mutants,
/// since the match lands only after advancing past cell 0).
#[test]
fn unify_certifies_interior_equal_length_match() {
    let mut arena = TermArena::new();
    let a = cunit(&mut arena, b'a');
    let ua = var_unit(&mut arena, "e0"); // unit(e0), length 1
    let ub = var_unit(&mut arena, "e1"); // unit(e1), length 1
    let l = cat(&mut arena, a, ua); // "a" ++ unit(e0)  -> ["a", unit(e0)]
    let r = cat(&mut arena, a, ub); // "a" ++ unit(e1)  -> ["a", unit(e1)]
    let eqs = [(l, r)];
    // At position 0 "a"="a" (equal length, but not the claimed pair); at position 1
    // unit(e0), unit(e1) are equal-length and — the members being equal — must be
    // equal.
    let fact = Fact {
        rule: Rule::InferUnify,
        equality: opair(ua, ub),
        premises: BTreeSet::from([0]),
    };
    assert!(
        check_fact(&mut arena, &eqs, &fact),
        "aligned equal-length interior components of equal members must unify"
    );
}

/// 361:5 `-> true`, 374:20 `delete !` — `InferUnify` must not certify a pair at a
/// position whose cells are **not** provably equal length (unknown-length seq
/// vars): the aligned-offset invariant fails, so the checker must break, not match.
#[test]
fn unify_declines_unequal_length_position() {
    let mut arena = TermArena::new();
    let s0 = seq_var(&mut arena, "s0"); // unknown length
    let t0 = seq_var(&mut arena, "t0"); // unknown length
    let z = cunit(&mut arena, b'z');
    let l = cat(&mut arena, s0, z); // s0 ++ "z"  -> [s0, "z"]
    let r = cat(&mut arena, t0, z); // t0 ++ "z"  -> [t0, "z"]
    let eqs = [(l, r)];
    let fact = Fact {
        rule: Rule::InferUnify,
        equality: opair(s0, t0),
        premises: BTreeSet::from([0]),
    };
    // s0, t0 have unknown (and not provably equal) length → position 0 is not
    // offset-aligned → the walk must break before matching.
    assert!(
        !check_fact(&mut arena, &eqs, &fact),
        "unify must not match across cells of unknown/unequal length"
    );
}

/// 372:21 / 372:32 / 372:37 (loop-bound mutants) — the unify walk must stop at the
/// **shorter** of the two component vectors. A same-class pair of unequal vector
/// lengths whose lead cells are equal-length (so the walk advances) but never
/// matches the claimed pair drives the walk to the short vector's end; a loosened
/// bound (`<=`, or `&& -> ||`) indexes out of bounds. Both orientations are covered
/// by the checker's own `(l, r)` / `(r, l)` double loop.
#[test]
fn unify_walk_stays_in_bounds() {
    let mut arena = TermArena::new();
    let u0 = var_unit(&mut arena, "e0"); // length 1
    let u1 = var_unit(&mut arena, "e1");
    let u2 = var_unit(&mut arena, "e2");
    let short = u0; // components: [unit(e0)]          (length 1)
    let long = cat(&mut arena, u1, u2); // [unit(e1), unit(e2)]  (length 2)
    let eqs = [(short, long)]; // same class, unequal vector lengths
    // A claimed pair that never matches, so the real walk advances to the short
    // vector's end and stops there (returns false); a bad bound overruns and panics.
    let p = seq_var(&mut arena, "p_unmatched");
    let q = seq_var(&mut arena, "q_unmatched");
    let fact = Fact {
        rule: Rule::InferUnify,
        equality: opair(p, q),
        premises: BTreeSet::from([0]),
    };
    assert!(
        !check_fact(&mut arena, &eqs, &fact),
        "the unify walk must stop at the shorter vector without overrunning"
    );
}

/// 366:23 `|| -> &&` (and 366:37 `!= -> ==`) — unify must only walk **same-class**
/// endpoint pairs; a cross-class pair must not certify.
#[test]
fn unify_rejects_cross_class_witness() {
    let mut arena = TermArena::new();
    let l2 = seq_var(&mut arena, "l2");
    let r2 = seq_var(&mut arena, "r2");
    let ua = var_unit(&mut arena, "e0");
    let ub = var_unit(&mut arena, "e1");
    let z = cunit(&mut arena, b'z');
    let l = cat(&mut arena, ua, z); // unit(e0) ++ "z"
    let r = cat(&mut arena, ub, z); // unit(e1) ++ "z"
    let eqs = [(l, l2), (r, r2)]; // L and R in different classes
    let fact = Fact {
        rule: Rule::InferUnify,
        equality: opair(ua, ub),
        premises: BTreeSet::from([0, 1]),
    };
    assert!(
        !check_fact(&mut arena, &eqs, &fact),
        "unify must not certify across unequal (cross-class) members"
    );
}

// ===== check_conflict walk: first_divergence (lines 481-530) ==================

/// Multi-cell accept: the walk must consume an equal **constant** block (497-501)
/// and a same-class **variable** cell (510-512) before the clash — exercising both
/// consume branches' `i += 1 / j += 1` (a corrupted increment underflows or loops).
#[test]
fn conflict_walks_constant_then_variable_prefix() {
    let mut arena = TermArena::new();
    let u = seq_var(&mut arena, "u");
    let v = seq_var(&mut arena, "v");
    let a = cunit(&mut arena, b'a');
    let b = cunit(&mut arena, b'b');
    let d = cunit(&mut arena, b'd');
    let ma = {
        let au = cat(&mut arena, a, u);
        cat(&mut arena, au, b) // "a" ++ u ++ "b"  -> ["a", u, "b"]
    };
    let mb = {
        let av = cat(&mut arena, a, v);
        cat(&mut arena, av, d) // "a" ++ v ++ "d"  -> ["a", v, "d"]
    };
    // premise 0: ma ≈ mb ; premise 1: u ≈ v (so the variable cells align).
    let eqs = [(ma, mb), (u, v)];
    let c = conflict_at(&mut arena, ma, mb, &[0, 1], 2, 2);
    assert!(
        check_conflict(&mut arena, &eqs, &c),
        "a clash after a constant block and an aligned variable must certify"
    );
}

/// Multi-cell accept via the **known-equal-length** advance branch (521-527): two
/// `seq.unit`s over element variables (each length 1) align, then the constants
/// clash. Exercises `known_len`'s `SeqUnit` arm and the branch's `i += 1 / j += 1`.
#[test]
fn conflict_walks_known_length_units_then_clash() {
    let mut arena = TermArena::new();
    let u0 = var_unit(&mut arena, "e0"); // length 1
    let u1 = var_unit(&mut arena, "e1"); // length 1
    let b = cunit(&mut arena, b'b');
    let d = cunit(&mut arena, b'd');
    let ma = cat(&mut arena, u0, b); // unit(e0) ++ "b"  -> [unit(e0), "b"]
    let mb = cat(&mut arena, u1, d); // unit(e1) ++ "d"  -> [unit(e1), "d"]
    let eqs = [(ma, mb)];
    let c = conflict_at(&mut arena, ma, mb, &[0], 1, 1);
    assert!(
        check_conflict(&mut arena, &eqs, &c),
        "equal-length unit prefixes must be skipped before the clash certifies"
    );
}

/// 488:13 / 488:34 `< -> <=`, 488:29 `&& -> ||` — the walk's bounds must stop at
/// the shorter vector's end; overrunning it indexes out of bounds. Here `member_b` is
/// a strict, fully-aligned extension of `member_a`, so the real walk exhausts without
/// a clash (returns `false`); a bad bound would index past the end and panic.
#[test]
fn conflict_walk_stays_in_bounds_on_exhaustion() {
    // member_b longer (exercises the `i < atoms_a.len()` bound).
    {
        let mut arena = TermArena::new();
        let x = seq_var(&mut arena, "x");
        let y = seq_var(&mut arena, "y");
        let a = cunit(&mut arena, b'a');
        let ma = cat(&mut arena, a, x); // "a" ++ x       -> ["a", x]
        let mb = {
            let ax = cat(&mut arena, a, x);
            cat(&mut arena, ax, y) // "a" ++ x ++ y  -> ["a", x, y]
        };
        let eqs = [(ma, mb)];
        let dummy = conflict_at(&mut arena, ma, mb, &[0], 0, 0);
        assert!(
            !check_conflict(&mut arena, &eqs, &dummy),
            "member_a exhausted first: decline without overrunning atoms_a"
        );
    }
    // member_a longer (exercises the `j < atoms_b.len()` bound and `&& -> ||`).
    {
        let mut arena = TermArena::new();
        let x = seq_var(&mut arena, "x");
        let y = seq_var(&mut arena, "y");
        let a = cunit(&mut arena, b'a');
        let ma = {
            let ax = cat(&mut arena, a, x);
            cat(&mut arena, ax, y) // "a" ++ x ++ y  -> ["a", x, y]
        };
        let mb = cat(&mut arena, a, x); // "a" ++ x   -> ["a", x]
        let eqs = [(ma, mb)];
        let dummy = conflict_at(&mut arena, ma, mb, &[0], 0, 0);
        assert!(
            !check_conflict(&mut arena, &eqs, &dummy),
            "member_b exhausted first: decline without overrunning atoms_b"
        );
    }
}

/// 510:15 `== -> !=`, 510:36 `== -> !=` — the same-class consume must fire only for
/// cells that are the same handle **or** provably one class. Two unrelated
/// variables must NOT be consumed (which would misalign the walk onto a spurious
/// clash). The record points at the clash a misaligning mutant would reach.
#[test]
fn conflict_walk_declines_unrelated_variable_cells() {
    let mut arena = TermArena::new();
    let u = seq_var(&mut arena, "u");
    let w = seq_var(&mut arena, "w_unrelated");
    let a = cunit(&mut arena, b'a');
    let b = cunit(&mut arena, b'b');
    let d = cunit(&mut arena, b'd');
    let ma = {
        let au = cat(&mut arena, a, u);
        cat(&mut arena, au, b) // "a" ++ u ++ "b"
    };
    let mb = {
        let aw = cat(&mut arena, a, w);
        cat(&mut arena, aw, d) // "a" ++ w ++ "d"
    };
    // premise 0 unions the MEMBERS but NOT u and w.
    let eqs = [(ma, mb)];
    let c = conflict_at(&mut arena, ma, mb, &[0], 2, 2);
    assert!(
        !check_conflict(&mut arena, &eqs, &c),
        "unrelated variable cells must halt the walk, not be consumed"
    );
}

// (The known-length advance branch's `la == lb` guard is covered by
// `conflict_walks_known_length_units_then_clash`: the `== -> !=` and guard-`false`
// mutants there turn the equal-length advance into a decline, breaking that accept
// case. The guard-`true` mutant only differs on *unequal* known lengths, a shape
// that cannot be built as an aligned constant clash because adjacent constant
// components always fuse — it is documented as an equivalent mutant.)

// ===== constants_clash (lines 537-551) ========================================

/// 538:5 `-> true`, 550:5 `delete !`, 550:51 `== -> !=` — a shorter constant that is
/// a genuine **prefix** of the longer one is NOT a clash (it is a length argument,
/// which this checker declines). The clash decision must return `false`.
#[test]
fn conflict_declines_prefix_not_clash() {
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let a = cunit(&mut arena, b'a');
    let ab_block = {
        let a2 = cunit(&mut arena, b'a');
        let b2 = cunit(&mut arena, b'b');
        cat(&mut arena, a2, b2) // "ab"
    };
    let ma = cat(&mut arena, x, a); // x ++ "a"   -> [x, "a"]
    let mb = cat(&mut arena, x, ab_block); // x ++ "ab" -> [x, "ab"]
    let eqs = [(ma, mb)];
    let c = conflict_at(&mut arena, ma, mb, &[0], 1, 1);
    // "a" is a prefix of "ab": not a self-evident aligned-constant clash → decline.
    assert!(
        !check_conflict(&mut arena, &eqs, &c),
        "a prefix (not a clash) must not certify a conflict"
    );
}

// ===== epsilon_fact_target / is_epsilon_term (lines 422-440) ==================

/// 425:9 (delete `(true, false)` arm) — an ε-fact whose ε side is stored **first**
/// (smaller `TermId`) must still be recognized, so the fact certifies.
#[test]
fn cycle_epsilon_fact_certifies_with_epsilon_stored_first() {
    let mut arena = TermArena::new();
    // Create ε FIRST so its TermId is small and sorts ahead of the target var.
    let eps = empty(&mut arena);
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let yx = cat(&mut arena, y, x); // x = y ++ x forces y ≈ ε
    let eqs = [(x, yx)];
    let base = infer(&mut arena, &eqs)
        .facts()
        .find(|f| f.rule == Rule::CycleEpsilon)
        .cloned()
        .expect("cycle forces y ≈ ε");
    // Force the equality to (ε, y) order regardless of TermId ordering.
    let fact = Fact {
        rule: Rule::CycleEpsilon,
        equality: (eps, y),
        premises: base.premises.clone(),
    };
    assert!(
        eps < y,
        "test setup: ε must have the smaller TermId to exercise the (true,false) arm"
    );
    assert!(
        check_fact(&mut arena, &eqs, &fact),
        "an ε-first ε-fact must still be recognized and certified"
    );
}

/// 439:7 `|| -> &&` — a value-empty-but-not-structural-ε term (`ε ++ ε`) must be
/// recognized as the empty sequence so the fact's ε side is detected.
#[test]
fn cycle_epsilon_fact_recognizes_value_empty_side() {
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let yx = cat(&mut arena, y, x); // x = y ++ x forces y ≈ ε
    let eqs = [(x, yx)];
    let base = infer(&mut arena, &eqs)
        .facts()
        .find(|f| f.rule == Rule::CycleEpsilon)
        .cloned()
        .expect("cycle forces y ≈ ε");
    // A concatenation of two ε's: value-empty, but NOT a structural seq.empty node.
    let eps = empty(&mut arena);
    let eps2 = empty(&mut arena);
    let eps_concat = cat(&mut arena, eps, eps2);
    let fact = Fact {
        rule: Rule::CycleEpsilon,
        equality: opair(y, eps_concat),
        premises: base.premises.clone(),
    };
    assert!(
        check_fact(&mut arena, &eqs, &fact),
        "a value-empty (non-structural) ε side must be recognized"
    );
}
