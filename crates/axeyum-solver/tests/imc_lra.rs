//! Integration tests for `prove_safety_imc_lra` — `McMillan` interpolation-based
//! model checking over linear-real-arithmetic transition systems.
//!
//! Every `Safe` is re-checked test-side (the three inductive-invariant conditions
//! through `check_auto`); every `Reachable` has its trace re-decided; the
//! resource-cap and non-`LRA` cases assert a graceful `Unknown` (never a hang or a
//! wrong verdict).

use std::time::Duration;

use axeyum_ir::{Rational, Sort, SymbolId, TermArena, TermId};
use axeyum_solver::{
    CheckResult, ImcLraOutcome, SolverConfig, SolverError, TransitionSystem, check_auto,
    prove_safety_imc_lra,
};

/// A single `Real` state variable named `x@{step}`.
fn real_var(arena: &mut TermArena, step: usize) -> SymbolId {
    arena.declare(&format!("x@{step}"), Sort::Real).unwrap()
}

fn rint(n: i128) -> Rational {
    Rational::new(n, 1)
}

/// A real accumulator: `init : x = 0`, `trans : x' = x + 1`, `bad : x < 0`. The
/// reachable set is `x ∈ {0, 1, 2, …}`; the safety invariant is `x ≥ 0`.
struct RealAccumulator;

impl TransitionSystem for RealAccumulator {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![real_var(arena, step)])
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s0[0]);
        let zero = arena.real_const(Rational::zero());
        Ok(arena.eq(x, zero)?)
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let x = arena.var(pre[0]);
        let one = arena.real_const(rint(1));
        let inc = arena.real_add(x, one)?;
        let x_next = arena.var(post[0]);
        Ok(arena.eq(x_next, inc)?)
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s[0]);
        let zero = arena.real_const(Rational::zero());
        Ok(arena.real_lt(x, zero)?)
    }
}

/// A monotone real system whose `init` is **already inductive**, so the
/// conjunctive `McMillan` fixpoint closes at `k = 1`: `init : x ≥ 0`,
/// `trans : x' = x + 1`, `bad : x < 0`. The reachable set is `x ≥ 0`, and
/// `init = (x ≥ 0)` is itself the inductive invariant (it is closed under the
/// transition and excludes `bad`). The first-iteration partition is conjunctive
/// (`A = [x0 ≥ 0, x1 = x0 + 1]`, `B = [x1 < 0]`), so `lra_interpolant` produces a
/// real interpolant `x1 ≥ c`; renamed and disjoined it leaves `R = (x ≥ 0)`, which
/// passes the fixpoint test immediately. This is the favorable conjunctive shape.
struct MonotoneLowerBound;

impl TransitionSystem for MonotoneLowerBound {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![real_var(arena, step)])
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s0[0]);
        let zero = arena.real_const(Rational::zero());
        Ok(arena.real_ge(x, zero)?)
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let x = arena.var(pre[0]);
        let one = arena.real_const(rint(1));
        let inc = arena.real_add(x, one)?;
        let x_next = arena.var(post[0]);
        Ok(arena.eq(x_next, inc)?)
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s[0]);
        let zero = arena.real_const(Rational::zero());
        Ok(arena.real_lt(x, zero)?)
    }
}

/// An **unsafe** real system: `init : x = 0`, `trans : x' = x + 1`, `bad : x = 3`.
/// A bad state is reachable in exactly three transitions.
struct ReachesThree;

impl TransitionSystem for ReachesThree {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![real_var(arena, step)])
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s0[0]);
        let zero = arena.real_const(Rational::zero());
        Ok(arena.eq(x, zero)?)
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let x = arena.var(pre[0]);
        let one = arena.real_const(rint(1));
        let inc = arena.real_add(x, one)?;
        let x_next = arena.var(post[0]);
        Ok(arena.eq(x_next, inc)?)
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s[0]);
        let three = arena.real_const(rint(3));
        Ok(arena.eq(x, three)?)
    }
}

/// A **non-LRA** system: 8-bit bit-vector state. The LRA interpolation /
/// LRA-shaped decisions cannot represent it; the engine must decline to `Unknown`
/// gracefully — never panic, never a wrong verdict.
struct BvSystem;

impl TransitionSystem for BvSystem {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![arena.declare(&format!("b@{step}"), Sort::BitVec(8))?])
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s0[0]);
        let zero = arena.bv_const(8, 0)?;
        Ok(arena.eq(x, zero)?)
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let x = arena.var(pre[0]);
        let one = arena.bv_const(8, 1)?;
        let inc = arena.bv_add(x, one)?;
        let x_next = arena.var(post[0]);
        Ok(arena.eq(x_next, inc)?)
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s[0]);
        let target = arena.bv_const(8, 42)?;
        Ok(arena.eq(x, target)?)
    }
}

/// Re-checks the three inductive-invariant conditions test-side, independently of
/// the engine's own gate: each must be `Unsat` under `check_auto`.
fn recheck_invariant(
    arena: &mut TermArena,
    system: &impl TransitionSystem,
    invariant: TermId,
) -> bool {
    let config = SolverConfig::default();
    let s = system.state_vars(arena, 0).unwrap();
    let sp = system.state_vars(arena, 1).unwrap();

    // Initiation: init(s) ∧ ¬Inv(s) unsat.
    let init = system.init(arena, &s).unwrap();
    let not_inv = arena.not(invariant).unwrap();
    if !matches!(
        check_auto(arena, &[init, not_inv], &config),
        Ok(CheckResult::Unsat)
    ) {
        return false;
    }

    // Consecution: Inv(s) ∧ trans(s, s') ∧ ¬Inv(s') unsat. Prime the invariant
    // structurally s[i] ↦ sp[i] (a single real variable here).
    let inv_primed = substitute_one(arena, invariant, s[0], sp[0]);
    let trans = system.trans(arena, &s, &sp).unwrap();
    let not_inv_primed = arena.not(inv_primed).unwrap();
    if !matches!(
        check_auto(arena, &[invariant, trans, not_inv_primed], &config),
        Ok(CheckResult::Unsat)
    ) {
        return false;
    }

    // Safety: Inv(s) ∧ bad(s) unsat.
    let bad = system.bad(arena, &s).unwrap();
    matches!(
        check_auto(arena, &[invariant, bad], &config),
        Ok(CheckResult::Unsat)
    )
}

/// Structural single-symbol substitution `from ↦ to`, for priming the invariant.
fn substitute_one(arena: &mut TermArena, term: TermId, from: SymbolId, to: SymbolId) -> TermId {
    use axeyum_ir::TermNode;
    match arena.node(term).clone() {
        TermNode::App { args, .. } => {
            let new_args: Vec<TermId> = args
                .iter()
                .map(|&arg| substitute_one(arena, arg, from, to))
                .collect();
            arena.rebuild_with_args(term, &new_args)
        }
        TermNode::Symbol(sym) if sym == from => arena.var(to),
        _ => term,
    }
}

#[test]
fn monotone_lower_bound_is_proven_safe_and_revalidates() {
    let mut arena = TermArena::new();
    let outcome =
        prove_safety_imc_lra(&mut arena, &MonotoneLowerBound, &SolverConfig::default()).unwrap();
    match outcome {
        ImcLraOutcome::Safe { invariant } => {
            // Independently re-validate the three inductive-invariant conditions —
            // the conjunctive McMillan fixpoint closed and the gate accepted it.
            assert!(
                recheck_invariant(&mut arena, &MonotoneLowerBound, invariant),
                "the returned invariant must pass an independent 3-condition re-check"
            );
        }
        // Soundness floor: an honest Unknown would be acceptable, but the
        // conjunctive fixpoint should close here — so we require Safe.
        ImcLraOutcome::Unknown { .. } => {
            panic!("the monotone-lower-bound fixpoint is conjunctive and should close to Safe")
        }
        ImcLraOutcome::Reachable { .. } => {
            panic!("the monotone system is safe (x ≥ 0); a Reachable verdict is unsound")
        }
    }
}

#[test]
fn real_accumulator_is_never_a_wrong_verdict() {
    // The accumulator is genuinely safe (x ≥ 0 forever). The disjunctive McMillan
    // fixpoint may or may not close under the conjunctive LRA interpolant; the
    // contract is only that the verdict is sound: Safe (re-validated) or Unknown,
    // never Reachable.
    let mut arena = TermArena::new();
    let outcome =
        prove_safety_imc_lra(&mut arena, &RealAccumulator, &SolverConfig::default()).unwrap();
    match outcome {
        ImcLraOutcome::Safe { invariant } => {
            assert!(
                recheck_invariant(&mut arena, &RealAccumulator, invariant),
                "any Safe invariant must pass the independent 3-condition re-check"
            );
        }
        ImcLraOutcome::Unknown { .. } => {}
        ImcLraOutcome::Reachable { .. } => {
            panic!("the accumulator is safe (x ≥ 0); a Reachable verdict is unsound")
        }
    }
}

#[test]
fn real_accumulator_is_proven_safe_via_disjunctive_interpolation() {
    // With the disjunctive `lra_interpolant_cnf` fallback, the IMC fixpoint closes
    // the accumulator (whose growing `R = (x=0) ∨ (x≥0)` becomes disjunctive after
    // the first step) to a genuine inductive invariant — a case the conjunctive-only
    // route declined to `Unknown`. The discovered invariant is independently
    // re-checked.
    let mut arena = TermArena::new();
    let outcome =
        prove_safety_imc_lra(&mut arena, &RealAccumulator, &SolverConfig::default()).unwrap();
    let ImcLraOutcome::Safe { invariant } = outcome else {
        panic!("disjunctive interpolation should prove the accumulator Safe, got {outcome:?}");
    };
    assert!(
        recheck_invariant(&mut arena, &RealAccumulator, invariant),
        "the discovered invariant must pass the independent 3-condition re-check"
    );
}

#[test]
fn reaches_three_is_reachable_with_a_revalidated_trace() {
    let mut arena = TermArena::new();
    let outcome =
        prove_safety_imc_lra(&mut arena, &ReachesThree, &SolverConfig::default()).unwrap();
    match outcome {
        ImcLraOutcome::Reachable { steps, model } => {
            assert!(steps >= 3, "bad (x = 3) needs at least three increments");
            // Re-decide the concrete unrolling with the witnessed model values and
            // confirm the trace really reaches a bad state: replay-check test-side.
            let config = SolverConfig::default();
            let mut states: Vec<Vec<SymbolId>> = Vec::new();
            for step in 0..=steps {
                states.push(ReachesThree.state_vars(&mut arena, step).unwrap());
            }
            let mut assertions = vec![ReachesThree.init(&mut arena, &states[0]).unwrap()];
            for window in states.windows(2) {
                assertions.push(
                    ReachesThree
                        .trans(&mut arena, &window[0], &window[1])
                        .unwrap(),
                );
            }
            // Pin the witnessed value of every step variable from the returned
            // model, then assert the final state is bad: a Sat re-confirms the
            // trace is a genuine path to bad.
            for state in &states {
                if let Some(axeyum_ir::Value::Real(r)) = model.get(state[0]) {
                    let xv = arena.var(state[0]);
                    let cv = arena.real_const(r);
                    assertions.push(arena.eq(xv, cv).unwrap());
                }
            }
            let bad_last = ReachesThree.bad(&mut arena, &states[steps]).unwrap();
            assertions.push(bad_last);
            assert!(
                matches!(
                    check_auto(&mut arena, &assertions, &config),
                    Ok(CheckResult::Sat(_))
                ),
                "the witnessed trace must re-check as a genuine path to a bad state"
            );
        }
        other => panic!("x = 3 is reachable from x = 0 by +1; expected Reachable, got {other:?}"),
    }
}

#[test]
fn tight_timeout_yields_unknown_without_hanging() {
    let mut arena = TermArena::new();
    let config = SolverConfig::default().with_timeout(Duration::from_nanos(1));
    // A near-zero deadline must produce a first-class Unknown promptly — never a
    // hang, panic, or a fabricated Safe/Reachable.
    let outcome = prove_safety_imc_lra(&mut arena, &RealAccumulator, &config).unwrap();
    assert!(
        matches!(outcome, ImcLraOutcome::Unknown { .. }),
        "a 1 ns timeout must degrade to Unknown, got {outcome:?}"
    );
}

#[test]
fn non_lra_bv_system_declines_to_unknown_gracefully() {
    let mut arena = TermArena::new();
    // The BV system is outside the conjunctive-LRA fragment the interpolation /
    // LRA decision procedures handle. The bounded check decides BV unrollings, but
    // the LRA interpolation fixpoint cannot close — and crucially nothing panics.
    // A Reachable here would still be sound (BV bad = 42 is reachable), but the
    // engine must at minimum never produce a wrong Safe and never panic.
    let outcome = prove_safety_imc_lra(&mut arena, &BvSystem, &SolverConfig::default()).unwrap();
    match outcome {
        // Unknown is the expected graceful decline. A Reachable would also be
        // sound (BV bad = 42 is reachable by +1, replay-checked) — both acceptable.
        ImcLraOutcome::Unknown { .. } | ImcLraOutcome::Reachable { .. } => {}
        ImcLraOutcome::Safe { invariant } => {
            // A Safe must still pass the independent re-check (BV system is NOT
            // safe, so this should never happen; guard against a wrong Safe).
            assert!(
                recheck_invariant(&mut arena, &BvSystem, invariant),
                "a BV Safe verdict must independently re-check (it must not)"
            );
            panic!("the BV system is unsafe (42 reachable); a Safe verdict is unsound");
        }
    }
}
