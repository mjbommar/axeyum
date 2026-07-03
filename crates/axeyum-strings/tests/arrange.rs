//! Hand-built decided-SAT and `unknown` cases for the T-B.4a arrangement search.
//!
//! Every `Sat` case additionally re-verifies the returned model by evaluating
//! the original assertions through the ground evaluator (the trust anchor),
//! mirroring the search's own internal replay.

mod common;

use axeyum_ir::{Assignment, TermArena, TermId, Value, eval};
use axeyum_strings::{SearchBudget, SearchOutcome, UnknownReason, solve_word_equations};
use common::{cat, ch, empty, seq_var, unit};

/// A generous default budget for the decidable hand cases.
fn budget() -> SearchBudget {
    SearchBudget::new(100_000)
}

/// Builds the constant string `s` (ASCII) as a right-nested `str.++` of units.
fn string(arena: &mut TermArena, s: &str) -> TermId {
    let mut term: Option<TermId> = None;
    for byte in s.bytes() {
        let u = {
            let c = ch(arena, u128::from(byte));
            unit(arena, c)
        };
        term = Some(match term {
            None => u,
            Some(acc) => cat(arena, acc, u),
        });
    }
    term.unwrap_or_else(|| empty(arena))
}

/// Asserts every equality holds and every disequality holds under `asg`.
fn replay_ok(
    arena: &TermArena,
    asg: &Assignment,
    eqs: &[(TermId, TermId)],
    diseqs: &[(TermId, TermId)],
) -> bool {
    eqs.iter().all(|&(a, b)| {
        eval(arena, a, asg).ok() == eval(arena, b, asg).ok() && eval(arena, a, asg).is_ok()
    }) && diseqs.iter().all(|&(a, b)| {
        matches!((eval(arena, a, asg), eval(arena, b, asg)), (Ok(va), Ok(vb)) if va != vb)
    })
}

/// Runs the search and asserts a replay-checked `Sat`.
#[track_caller]
fn assert_sat(
    arena: &mut TermArena,
    eqs: &[(TermId, TermId)],
    diseqs: &[(TermId, TermId)],
) -> Assignment {
    match solve_word_equations(arena, eqs, diseqs, &budget()) {
        SearchOutcome::Sat(asg) => {
            assert!(
                replay_ok(arena, &asg, eqs, diseqs),
                "returned model does not replay against the original assertions"
            );
            asg
        }
        SearchOutcome::Unknown { reason } => panic!("expected Sat, got Unknown({reason})"),
    }
}

// ----- decided-SAT cases ------------------------------------------------------

#[test]
fn concat_equals_two_char_constant() {
    // x ++ y ≈ "ab" — the three splits (ε|ab, a|b, ab|ε); the search finds one.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let xy = cat(&mut arena, x, y);
    let ab = string(&mut arena, "ab");
    assert_sat(&mut arena, &[(xy, ab)], &[]);
}

#[test]
fn split_across_constant_boundary() {
    // x ++ "b" ≈ "a" ++ y  (needs constant-boundary alignment).
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let b = string(&mut arena, "b");
    let a = string(&mut arena, "a");
    let lhs = cat(&mut arena, x, b);
    let rhs = cat(&mut arena, a, y);
    let asg = assert_sat(&mut arena, &[(lhs, rhs)], &[]);
    // Spot-check: the model makes both sides evaluate to the same sequence.
    let lv = eval(&arena, lhs, &asg).expect("lhs");
    let rv = eval(&arena, rhs, &asg).expect("rhs");
    assert_eq!(lv, rv);
}

#[test]
fn chain_variable_to_constant() {
    // x ≈ y ++ z  ∧  z ≈ "c".  A straight-line chain; y is free.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let z = seq_var(&mut arena, "z");
    let yz = cat(&mut arena, y, z);
    let c = string(&mut arena, "c");
    assert_sat(&mut arena, &[(x, yz), (z, c)], &[]);
}

#[test]
fn f_split_with_skolem() {
    // x ++ "ab" ≈ "a" ++ y  — requires an F-Split / character split with a Skolem.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let ab = string(&mut arena, "ab");
    let a = string(&mut arena, "a");
    let lhs = cat(&mut arena, x, ab);
    let rhs = cat(&mut arena, a, y);
    let asg = assert_sat(&mut arena, &[(lhs, rhs)], &[]);
    let lv = eval(&arena, lhs, &asg).expect("lhs");
    let rv = eval(&arena, rhs, &asg).expect("rhs");
    assert_eq!(lv, rv);
}

#[test]
fn len_split_epsilon_case() {
    // "a" ++ x ≈ "a"  forces x ≈ ε (the Len-Split ε branch).
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let a1 = string(&mut arena, "a");
    let ax = cat(&mut arena, a1, x);
    let a2 = string(&mut arena, "a");
    let asg = assert_sat(&mut arena, &[(ax, a2)], &[]);
    // x must be ε.
    let sym = match arena.node(x) {
        axeyum_ir::TermNode::Symbol(s) => *s,
        _ => unreachable!(),
    };
    assert_eq!(asg.get(sym), Some(Value::Seq(Vec::new())));
}

#[test]
fn disequality_forces_distinct_instantiation() {
    // x ≠ y with no equalities — must find distinct instantiations.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    assert_sat(&mut arena, &[], &[(x, y)]);
}

#[test]
fn equalities_and_disequality_together() {
    // x ≈ "a", y ≈ z, x ≠ y — sat: x="a", y=z=ε.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let z = seq_var(&mut arena, "z");
    let a = string(&mut arena, "a");
    assert_sat(&mut arena, &[(x, a), (y, z)], &[(x, y)]);
}

#[test]
fn empty_instance_is_trivially_sat() {
    let mut arena = TermArena::new();
    match solve_word_equations(&mut arena, &[], &[], &budget()) {
        SearchOutcome::Sat(_) => {}
        SearchOutcome::Unknown { reason } => panic!("empty instance should be Sat, got {reason}"),
    }
}

// ----- unknown cases ----------------------------------------------------------

#[test]
fn self_loop_yields_unknown_not_unsat() {
    // x ≈ "a" ++ x — an F-Loop (T-B.5). The cycle rule forces "a" ≈ ε (false),
    // so every branch conflicts and the search exhausts to Unknown — NEVER unsat.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let a = string(&mut arena, "a");
    let ax = cat(&mut arena, a, x);
    match solve_word_equations(&mut arena, &[(x, ax)], &[], &budget()) {
        SearchOutcome::Unknown { .. } => {}
        SearchOutcome::Sat(_) => panic!("a self-loop must not produce a (spurious) model"),
    }
}

#[test]
fn contradictory_constants_is_unknown_not_unsat() {
    // x ≈ "a" ∧ x ≈ "b": genuinely unsat, but the search returns Unknown
    // (word-level unsat is deferred to T-B.7).
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let a = string(&mut arena, "a");
    let b = string(&mut arena, "b");
    match solve_word_equations(&mut arena, &[(x, a), (x, b)], &[], &budget()) {
        SearchOutcome::Unknown { .. } => {}
        SearchOutcome::Sat(_) => panic!("must never return a model for x=a ∧ x=b"),
    }
}

#[test]
fn equal_and_distinct_is_unknown() {
    // x ≈ y ∧ x ≠ y — unsat; must be Unknown, never Sat.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    match solve_word_equations(&mut arena, &[(x, y)], &[(x, y)], &budget()) {
        SearchOutcome::Unknown { .. } => {}
        SearchOutcome::Sat(_) => panic!("x=y ∧ x≠y must not be Sat"),
    }
}

#[test]
fn node_budget_exhaustion_is_unknown() {
    // A tiny node budget on a branching instance yields NodeBudget.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let xy = cat(&mut arena, x, y);
    let abc = string(&mut arena, "abcabc");
    let tiny = SearchBudget::new(1);
    // With a 1-node budget the very first branch already trips the cap.
    match solve_word_equations(&mut arena, &[(xy, abc)], &[], &tiny) {
        SearchOutcome::Unknown { reason } => {
            assert_eq!(reason, UnknownReason::NodeBudget);
        }
        SearchOutcome::Sat(_) => panic!("a 1-node budget should not decide this"),
    }
}

#[test]
fn past_deadline_is_immediate_unknown() {
    // A deadline already in the past must return Unknown(Deadline) immediately —
    // the deadline regression guard.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let xy = cat(&mut arena, x, y);
    let ab = string(&mut arena, "ab");
    let past = std::time::Instant::now()
        .checked_sub(std::time::Duration::from_secs(1))
        .expect("past instant");
    let b = SearchBudget::with_deadline(100_000, past);
    match solve_word_equations(&mut arena, &[(xy, ab)], &[], &b) {
        SearchOutcome::Unknown { reason } => assert_eq!(reason, UnknownReason::Deadline),
        SearchOutcome::Sat(_) => panic!("a past deadline must return Unknown immediately"),
    }
}

#[test]
fn non_sequence_endpoint_is_unknown() {
    let mut arena = TermArena::new();
    let a = arena.bv_var("a", 8).expect("bv");
    let b = arena.bv_var("b", 8).expect("bv");
    match solve_word_equations(&mut arena, &[(a, b)], &[], &budget()) {
        SearchOutcome::Unknown { reason } => assert_eq!(reason, UnknownReason::NonSequence),
        SearchOutcome::Sat(_) => panic!("non-sequence endpoints are not word equations"),
    }
}

// ----- determinism ------------------------------------------------------------

#[test]
fn identical_runs_give_identical_outcomes() {
    let build = |arena: &mut TermArena| {
        let x = seq_var(arena, "x");
        let y = seq_var(arena, "y");
        let xy = cat(arena, x, y);
        let ab = string(arena, "ab");
        (vec![(xy, ab)], Vec::<(TermId, TermId)>::new())
    };

    let mut a1 = TermArena::new();
    let (e1, d1) = build(&mut a1);
    let o1 = solve_word_equations(&mut a1, &e1, &d1, &budget());

    let mut a2 = TermArena::new();
    let (e2, d2) = build(&mut a2);
    let o2 = solve_word_equations(&mut a2, &e2, &d2, &budget());

    match (o1, o2) {
        (SearchOutcome::Sat(m1), SearchOutcome::Sat(m2)) => {
            // The two arenas are built identically, so symbol ids line up.
            for (arena, x_name) in [(&a1, "x"), (&a1, "y")] {
                if let Some(s) = arena.find_symbol(x_name) {
                    assert_eq!(m1.get(s), m2.get(s), "model differs for {x_name}");
                }
            }
        }
        (SearchOutcome::Unknown { reason: r1 }, SearchOutcome::Unknown { reason: r2 }) => {
            assert_eq!(r1, r2);
        }
        _ => panic!("nondeterministic outcome"),
    }
}
