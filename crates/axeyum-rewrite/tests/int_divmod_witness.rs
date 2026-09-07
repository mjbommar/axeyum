//! The `eliminate_int_divmod` faithfulness witness and its congruence mode
//! (ADR-1730, the second slice of ADR-1721).
//!
//! `eliminate_int_divmod` does two things and they owe different evidence. It
//! **replaces** each `div`/`mod`-by-constant and `abs` term with a fresh
//! variable, which can break both directions; and it **appends** the defining
//! linear constraints, which can only break `unsat`. Until this suite it carried
//! no artifact of any kind — not even the re-derivation ADR-1721 §2 measures as
//! insufficient — so a wrong constraint or a wrong substitution was accepted by
//! construction.
//!
//! [`witness_int_divmod`] does not re-run the transform. For each sampled
//! assignment it binds every fresh symbol to the GROUND EVALUATOR'S value of the
//! original term that symbol replaced, then interprets both sides. The reference
//! never enters the rewriting code.
//!
//! Two halves are checked because neither subsumes the other, and both controls
//! below make that concrete: a consistently-swapped quotient/remainder pair is
//! invisible to the replacement half and caught by the constraint half.
//!
//! The suite also pins the congruence mode the pass reports. Crossing
//! `MAX_CONGRUENCE_GROUPS` is a RELAXATION — it drops added conjuncts — so
//! `unsat` transfers at every group count and it is `sat` that degrades. That is
//! the direction, and `ZeroDivisorCongruence::sat_transfers` is where a caller
//! reads it.

use axeyum_ir::{TermArena, TermId, Value};
use axeyum_rewrite::{
    INT_DIVMOD_WITNESS_SAMPLES, IntDivModFinding, MAX_CONGRUENCE_GROUPS, ZeroDivisorCongruence,
    eliminate_int_divmod, witness_int_divmod,
};

/// `mod(x, 3) = 2 ∧ div(x, 3) = y ∧ abs(x) < 20` — one of each eliminated shape,
/// with a nonzero divisor so the appended Euclidean constraints are real.
fn divmod_query(arena: &mut TermArena) -> Vec<TermId> {
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let three = arena.int_const(3);
    let m = arena.int_mod(x, three).unwrap();
    let two = arena.int_const(2);
    let a0 = arena.eq(m, two).unwrap();

    let q = arena.int_div(x, three).unwrap();
    let a1 = arena.eq(q, y).unwrap();

    let ab = arena.int_abs(x).unwrap();
    let twenty = arena.int_const(20);
    let a2 = arena.int_lt(ab, twenty).unwrap();

    vec![a0, a1, a2]
}

/// POSITIVE CONTROL. The shipped elimination is faithful, and the witness says so
/// having actually examined something — both counts are pinned to the full grid
/// rather than accepting a run that quietly examined nothing.
#[test]
fn witness_accepts_the_shipped_elimination() {
    let mut arena = TermArena::new();
    let assertions = divmod_query(&mut arena);
    let elim = eliminate_int_divmod(&mut arena, &assertions).unwrap();
    assert!(elim.eliminated_any());

    let witness = witness_int_divmod(&arena, &assertions, &elim, INT_DIVMOD_WITNESS_SAMPLES);

    assert_eq!(
        witness.finding, None,
        "the shipped elimination must be faithful"
    );
    assert_eq!(
        witness.compared,
        INT_DIVMOD_WITNESS_SAMPLES * assertions.len(),
        "every (sample, assertion) pair must be compared, not skipped"
    );
    assert_eq!(
        witness.constraints_checked,
        INT_DIVMOD_WITNESS_SAMPLES * elim.added_constraints().len(),
        "every (sample, constraint) pair must be evaluated, not skipped"
    );
    assert_eq!(witness.unavailable, 0);
    assert!(witness.is_faithful());
}

/// NEGATIVE CONTROL (replacement half) — the witness can reach a `Replacement`
/// finding.
///
/// A witness that structurally cannot report a disagreement would pass the test
/// above forever, so this hands it an "original" whose meaning is the *negation*
/// of what the elimination rewrote. Both sides evaluate; they must differ.
#[test]
fn witness_rejects_an_original_that_is_not_what_was_rewritten() {
    let mut arena = TermArena::new();
    let assertions = divmod_query(&mut arena);
    // A second "original" of the same length whose first assertion is the negation
    // of the real one. Built before elimination so its `TermId`s are valid in the
    // same arena.
    let negated = arena.not(assertions[0]).unwrap();
    let mismatched = vec![negated, assertions[1], assertions[2]];

    let elim = eliminate_int_divmod(&mut arena, &assertions).unwrap();
    let witness = witness_int_divmod(&arena, &mismatched, &elim, INT_DIVMOD_WITNESS_SAMPLES);

    match witness.finding.as_ref() {
        Some(IntDivModFinding::Replacement {
            assertion,
            original,
            rewritten,
            ..
        }) => {
            assert_eq!(
                *assertion, 0,
                "the finding must name the assertion that was negated"
            );
            assert_ne!(original, rewritten);
        }
        other => panic!("a negated original must disagree with the rewrite, got {other:?}"),
    }
    assert!(!witness.is_faithful());
}

/// NEGATIVE CONTROL (strengthening half) — the witness can reach a `Constraint`
/// finding, and it is a *distinct* reachable outcome from the one above.
///
/// A constraint that is not a consequence of the original is what turns a
/// satisfiable query `unsat`, so this half must be shown to fire on its own. The
/// fixture takes an honest elimination apart with
/// `IntDivModElimination::from_parts` and appends one constraint that is false
/// under the canonical extension (`mod(x, 3) = 5`, impossible for a Euclidean
/// remainder mod 3) — the exact shape of a spurious strengthening.
#[test]
fn witness_rejects_an_added_constraint_that_is_not_a_consequence() {
    let mut arena = TermArena::new();
    let assertions = divmod_query(&mut arena);
    let honest = eliminate_int_divmod(&mut arena, &assertions).unwrap();

    // `mod(x, 3) = 5` — false for every x, hence a consequence of nothing. Appended
    // to the tail, it occupies exactly the position a spurious strengthening would.
    let x = arena.int_var("x").unwrap();
    let three = arena.int_const(3);
    let m = arena.int_mod(x, three).unwrap();
    let five = arena.int_const(5);
    let bogus = arena.eq(m, five).unwrap();

    let mut forged_assertions = honest.assertions().to_vec();
    forged_assertions.push(bogus);
    let forged = axeyum_rewrite::IntDivModElimination::from_parts(
        forged_assertions,
        honest.original_count(),
        honest.replacements().to_vec(),
        honest.congruence(),
    )
    .expect("original_count is within the forged assertion list");

    let witness = witness_int_divmod(&arena, &assertions, &forged, INT_DIVMOD_WITNESS_SAMPLES);

    match witness.finding.as_ref() {
        Some(IntDivModFinding::Constraint {
            constraint, value, ..
        }) => {
            assert_eq!(
                *constraint,
                forged.added_constraints().len() - 1,
                "the finding must name the appended constraint, not an honest one"
            );
            assert_ne!(
                *value,
                Value::Bool(true),
                "a reported constraint finding must not be a true constraint"
            );
        }
        other => panic!("a false appended constraint must be rejected, got {other:?}"),
    }
    assert!(!witness.is_faithful());
}

/// VACUITY CONTROL. A query with nothing to eliminate gives the witness nothing
/// to examine, and `compared == 0` must NOT read as a pass — otherwise every
/// query outside the fragment would silently "witness" faithfulness.
#[test]
fn an_empty_witness_is_not_a_pass() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let one = arena.int_const(1);
    let assertions = vec![arena.int_lt(x, one).unwrap()];
    let elim = eliminate_int_divmod(&mut arena, &assertions).unwrap();
    assert!(!elim.eliminated_any());

    let witness = witness_int_divmod(&arena, &assertions, &elim, INT_DIVMOD_WITNESS_SAMPLES);

    assert_eq!(witness.compared, 0);
    assert_eq!(witness.constraints_checked, 0);
    assert_eq!(witness.finding, None);
    assert!(
        !witness.is_faithful(),
        "a witness that examined nothing has not witnessed anything"
    );
}

/// The sample sequence is a public API promise (determinism), so two runs over
/// the same query must produce identical witnesses — and the elimination itself
/// must produce identical output, which it did not while it iterated hash maps.
#[test]
fn the_witness_and_the_elimination_are_deterministic() {
    let run = || {
        let mut arena = TermArena::new();
        let assertions = divmod_query(&mut arena);
        let elim = eliminate_int_divmod(&mut arena, &assertions).unwrap();
        let witness = witness_int_divmod(&arena, &assertions, &elim, INT_DIVMOD_WITNESS_SAMPLES);
        (elim, witness)
    };
    let (first_elim, first_witness) = run();
    let (second_elim, second_witness) = run();
    assert_eq!(first_elim, second_elim);
    assert_eq!(first_witness, second_witness);
}

/// A query with a negative constant divisor. The Euclidean remainder bound is
/// `0 ≤ r ≤ |c| − 1`, and getting the absolute value wrong there is a
/// *strengthening* — it can refute a satisfiable query. The default gate has no
/// negative-divisor coverage (the only fuzz that emits one needs `--features z3`),
/// so the witness carries it.
#[test]
fn witness_covers_a_negative_constant_divisor() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let minus_three = arena.int_const(-3);
    let m = arena.int_mod(x, minus_three).unwrap();
    let two = arena.int_const(2);
    let assertions = vec![arena.eq(m, two).unwrap()];

    let elim = eliminate_int_divmod(&mut arena, &assertions).unwrap();
    assert!(elim.eliminated_any());
    let witness = witness_int_divmod(&arena, &assertions, &elim, INT_DIVMOD_WITNESS_SAMPLES);

    assert_eq!(witness.finding, None);
    assert!(witness.is_faithful());
    assert!(
        witness.constraints_checked > 0,
        "the negative-divisor Euclidean constraints must actually be evaluated"
    );
}

/// The split index is the ADR-1721 §5 subtraction: the rewritten originals are a
/// prefix positionally aligned with the caller's input and the added constraints
/// are the tail, so their count never needs a separate counter that can drift.
#[test]
fn the_split_index_partitions_the_output() {
    let mut arena = TermArena::new();
    let assertions = divmod_query(&mut arena);
    let elim = eliminate_int_divmod(&mut arena, &assertions).unwrap();

    assert_eq!(elim.original_count(), assertions.len());
    assert_eq!(elim.rewritten().len(), assertions.len());
    assert_eq!(
        elim.rewritten().len() + elim.added_constraints().len(),
        elim.assertions().len()
    );
    assert!(
        !elim.added_constraints().is_empty(),
        "a div/mod/abs query must append its defining constraints"
    );
    // Every replaced term is one the caller's query actually contained.
    assert!(!elim.replacements().is_empty());
}

/// Below the cap the zero-divisor relaxation is congruence-closed, so a caller
/// may trust a `sat` of the output. This is the mode nobody could see before.
#[test]
fn zero_divisor_congruence_below_the_cap_is_closed_and_sat_transfers() {
    let mut arena = TermArena::new();
    let assertions = zero_divisor_query(&mut arena, 4);
    let elim = eliminate_int_divmod(&mut arena, &assertions).unwrap();

    match elim.congruence() {
        ZeroDivisorCongruence::Closed { groups, lemmas } => {
            assert_eq!(groups, 4);
            // One `mod _ 0` per group and every unordered pair gets one lemma.
            assert_eq!(lemmas, 4 * 3 / 2);
        }
        other => panic!("expected a closed congruence below the cap, got {other:?}"),
    }
    assert!(elim.congruence().sat_transfers());
}

/// Above the cap the lemmas are dropped. That is a RELAXATION — added conjuncts
/// are removed — so `unsat` still transfers and `sat` does not, which is exactly
/// what `sat_transfers()` reports. Before this slice the crossing was silent.
#[test]
fn zero_divisor_congruence_above_the_cap_is_omitted_and_sat_does_not_transfer() {
    let groups = MAX_CONGRUENCE_GROUPS + 1;
    let mut arena = TermArena::new();
    let assertions = zero_divisor_query(&mut arena, groups);
    let elim = eliminate_int_divmod(&mut arena, &assertions).unwrap();

    match elim.congruence() {
        ZeroDivisorCongruence::Omitted {
            groups: reported,
            limit,
        } => {
            assert_eq!(reported, groups);
            assert_eq!(limit, MAX_CONGRUENCE_GROUPS);
        }
        other => panic!("expected an omitted congruence above the cap, got {other:?}"),
    }
    assert!(!elim.congruence().sat_transfers());
    assert_eq!(elim.congruence().lemmas(), 0);
    // The mode change is a DELETION of conjuncts, not an addition: at the cap the
    // same query shape carries lemmas and one group further it carries none.
    let mut at_cap_arena = TermArena::new();
    let at_cap = zero_divisor_query(&mut at_cap_arena, MAX_CONGRUENCE_GROUPS);
    let at_cap_elim = eliminate_int_divmod(&mut at_cap_arena, &at_cap).unwrap();
    assert!(at_cap_elim.congruence().sat_transfers());
    assert!(at_cap_elim.congruence().lemmas() > 0);
    assert!(
        elim.added_constraints().len() < at_cap_elim.added_constraints().len(),
        "dropping the lemmas must shrink the added set, i.e. weaken the output"
    );
}

/// A query with no zero divisor reports `NotApplicable`, which is not a weaker
/// mode — the elimination is exact there — and must still say `sat` transfers.
#[test]
fn no_zero_divisor_reports_not_applicable() {
    let mut arena = TermArena::new();
    let assertions = divmod_query(&mut arena);
    let elim = eliminate_int_divmod(&mut arena, &assertions).unwrap();
    assert_eq!(elim.congruence(), ZeroDivisorCongruence::NotApplicable);
    assert!(elim.congruence().sat_transfers());
    assert_eq!(elim.congruence().groups(), 0);
}

/// `n` assertions, each mentioning `mod(xᵢ, 0)` for a distinct variable, so the
/// pass sees exactly `n` distinct syntactic zero-divisor dividends.
fn zero_divisor_query(arena: &mut TermArena, n: usize) -> Vec<TermId> {
    let zero = arena.int_const(0);
    let bound = arena.int_const(7);
    (0..n)
        .map(|i| {
            let v = arena.int_var(&format!("x{i}")).unwrap();
            let m = arena.int_mod(v, zero).unwrap();
            arena.int_lt(m, bound).unwrap()
        })
        .collect()
}
