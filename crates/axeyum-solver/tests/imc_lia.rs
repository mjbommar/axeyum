//! Integration tests for `prove_safety_imc_lia` — `McMillan` interpolation-based
//! model checking over linear-INTEGER-arithmetic transition systems (the integer
//! mirror of the `imc_lra` tests).
//!
//! Every `Safe` is re-checked test-side (the three inductive-invariant conditions
//! through `check_auto` over ℤ); every `Reachable` has its trace re-decided; the
//! `lia_interpolant`-declines, resource-cap, and non-`LIA` cases assert a graceful
//! `Unknown` (never a hang, never a wrong verdict). A soundness-negative case
//! requires an actually-unsafe system to never be reported `Safe`.

use std::time::Duration;

use axeyum_ir::{Sort, SymbolId, TermArena, TermId};
use axeyum_solver::{
    CheckResult, ImcLiaOutcome, SolverConfig, SolverError, TransitionSystem, check_auto,
    prove_safety_imc_lia,
};

/// A single `Int` state variable named `x@{step}`.
fn int_var(arena: &mut TermArena, step: usize) -> SymbolId {
    arena.declare(&format!("x@{step}"), Sort::Int).unwrap()
}

/// A monotone integer system whose `init` is **already inductive**, so the
/// conjunctive `McMillan` fixpoint closes at `k = 1`: `init : x ≥ 0`,
/// `trans : x' = x + 1`, `bad : x < 0`. The reachable set is `x ≥ 0`, and
/// `init = (x ≥ 0)` is itself the inductive invariant (closed under the transition,
/// excludes `bad`). The first-iteration partition is conjunctive
/// (`A = [x0 ≥ 0, x1 = x0 + 1]`, `B = [x1 < 0]`), the rational relaxation is unsat,
/// so `lia_interpolant` returns a verified integer interpolant `x1 ≥ c`; renamed and
/// disjoined it leaves `R = (x ≥ 0)`, which passes the fixpoint test immediately.
/// This is the favorable conjunctive shape.
struct MonotoneLowerBound;

impl TransitionSystem for MonotoneLowerBound {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![int_var(arena, step)])
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s0[0]);
        let zero = arena.int_const(0);
        Ok(arena.int_ge(x, zero)?)
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let x = arena.var(pre[0]);
        let one = arena.int_const(1);
        let inc = arena.int_add(x, one)?;
        let x_next = arena.var(post[0]);
        Ok(arena.eq(x_next, inc)?)
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s[0]);
        let zero = arena.int_const(0);
        Ok(arena.int_lt(x, zero)?)
    }
}

/// A genuinely safe integer accumulator: `init : x = 0`, `trans : x' = x + 1`,
/// `bad : x < 0`. The reachable set is `x ∈ {0, 1, 2, …}`; the safety invariant is
/// `x ≥ 0`. Because `init` is the singleton `x = 0`, the growing `R` becomes a
/// disjunction after the first step, which the conjunctive-only `lia_interpolant`
/// declines — there is no disjunctive integer fallback, so the engine deepens and
/// ultimately declines to `Unknown` (sound partiality). Used to assert that an
/// `Unknown` is acceptable but a `Reachable` is never produced for a safe system.
struct IntAccumulator;

impl TransitionSystem for IntAccumulator {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![int_var(arena, step)])
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s0[0]);
        let zero = arena.int_const(0);
        Ok(arena.eq(x, zero)?)
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let x = arena.var(pre[0]);
        let one = arena.int_const(1);
        let inc = arena.int_add(x, one)?;
        let x_next = arena.var(post[0]);
        Ok(arena.eq(x_next, inc)?)
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s[0]);
        let zero = arena.int_const(0);
        Ok(arena.int_lt(x, zero)?)
    }
}

/// A genuinely safe integer system whose **inductive invariant is DISJUNCTIVE**
/// (not conjunctively interpolatable): `init : x = 0 ∨ x = 10`,
/// `trans : x' = x` (stutter), `bad : 1 ≤ x ≤ 9`. The reachable set is `{0, 10}`,
/// and the natural inductive invariant is `x ≤ 0 ∨ x ≥ 10` — it contains `{0, 10}`,
/// is closed under the stutter transition, and excludes the bad band `1..=9`. No
/// single conjunction of linear-integer atoms separates `{0, 10}` from `1..=9`, so
/// the conjunctive-only `lia_interpolant` declines (the A side `init` is itself a
/// disjunction). The disjunctive `lia_interpolant_cnf` route, now wired into the
/// fixpoint, closes it — and the engine reports `Safe`, re-checked test-side.
struct DisjunctiveTwoRegion;

impl TransitionSystem for DisjunctiveTwoRegion {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![int_var(arena, step)])
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s0[0]);
        let zero = arena.int_const(0);
        let ten = arena.int_const(10);
        let at_zero = arena.eq(x, zero)?;
        let at_ten = arena.eq(x, ten)?;
        Ok(arena.or(at_zero, at_ten)?)
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        // Stutter: x' = x. The reachable set is exactly the (disjunctive) init set.
        let x = arena.var(pre[0]);
        let x_next = arena.var(post[0]);
        Ok(arena.eq(x_next, x)?)
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        // The band 1 ≤ x ≤ 9 — separated from {0, 10} only by a disjunction.
        let x = arena.var(s[0]);
        let one = arena.int_const(1);
        let nine = arena.int_const(9);
        let lower = arena.int_ge(x, one)?;
        let upper = arena.int_le(x, nine)?;
        Ok(arena.and(lower, upper)?)
    }
}

/// An **unsafe** integer system: `init : x = 0`, `trans : x' = x + 1`,
/// `bad : x = 3`. A bad state is reachable in exactly three transitions.
struct ReachesThree;

impl TransitionSystem for ReachesThree {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![int_var(arena, step)])
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s0[0]);
        let zero = arena.int_const(0);
        Ok(arena.eq(x, zero)?)
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let x = arena.var(pre[0]);
        let one = arena.int_const(1);
        let inc = arena.int_add(x, one)?;
        let x_next = arena.var(post[0]);
        Ok(arena.eq(x_next, inc)?)
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s[0]);
        let three = arena.int_const(3);
        Ok(arena.eq(x, three)?)
    }
}

/// A **non-LIA** system: 8-bit bit-vector state. The integer interpolation /
/// integer-shaped decisions cannot represent it; the engine must decline to
/// `Unknown` gracefully (or report a sound `Reachable`) — never panic, never a
/// wrong `Safe`.
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

/// Re-checks the three inductive-invariant conditions test-side over ℤ,
/// independently of the engine's own gate: each must be `Unsat` under `check_auto`.
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
    // structurally s[i] ↦ sp[i] (a single integer variable here).
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
        prove_safety_imc_lia(&mut arena, &MonotoneLowerBound, &SolverConfig::default()).unwrap();
    match outcome {
        ImcLiaOutcome::Safe { invariant } => {
            // Independently re-validate the three inductive-invariant conditions over
            // ℤ — the conjunctive McMillan fixpoint closed and the gate accepted it.
            assert!(
                recheck_invariant(&mut arena, &MonotoneLowerBound, invariant),
                "the returned invariant must pass an independent 3-condition re-check over ℤ"
            );
        }
        // Soundness floor: an honest Unknown would be acceptable, but the
        // conjunctive integer fixpoint should close here — so we require Safe.
        ImcLiaOutcome::Unknown { .. } => {
            panic!("the monotone-lower-bound fixpoint is conjunctive and should close to Safe")
        }
        ImcLiaOutcome::Reachable { .. } => {
            panic!("the monotone system is safe (x ≥ 0); a Reachable verdict is unsound")
        }
    }
}

#[test]
fn disjunctive_two_region_is_proven_safe_via_disjunctive_interpolant() {
    // A safe system whose ONLY inductive invariant is disjunctive (x ≤ 0 ∨ x ≥ 10):
    // the reachable set {0, 10} cannot be separated from the bad band 1..=9 by any
    // single conjunction of linear-integer atoms. The conjunctive `lia_interpolant`
    // alone could not close this fixpoint (it declines on the disjunctive A side);
    // the newly-wired disjunctive `lia_interpolant_cnf` route does. We require Safe
    // and independently re-check the three inductive-invariant conditions over ℤ.
    let mut arena = TermArena::new();
    let outcome =
        prove_safety_imc_lia(&mut arena, &DisjunctiveTwoRegion, &SolverConfig::default()).unwrap();
    match outcome {
        ImcLiaOutcome::Safe { invariant } => {
            assert!(
                recheck_invariant(&mut arena, &DisjunctiveTwoRegion, invariant),
                "the disjunctive invariant must pass an independent 3-condition re-check over ℤ"
            );
        }
        ImcLiaOutcome::Unknown { reason } => panic!(
            "the disjunctive interpolant should close this fixpoint to Safe, got Unknown: {reason}"
        ),
        ImcLiaOutcome::Reachable { .. } => {
            panic!("the two-region system is safe (reachable set {{0, 10}}); Reachable is unsound")
        }
    }
}

#[test]
fn reaches_three_is_reachable_with_a_revalidated_trace() {
    let mut arena = TermArena::new();
    let outcome =
        prove_safety_imc_lia(&mut arena, &ReachesThree, &SolverConfig::default()).unwrap();
    match outcome {
        ImcLiaOutcome::Reachable { steps, model } => {
            assert!(steps >= 3, "bad (x = 3) needs at least three increments");
            // Replay-check test-side: re-decide the concrete unrolling pinned to the
            // witnessed model values and confirm the final state is bad.
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
            for state in &states {
                if let Some(axeyum_ir::Value::Int(v)) = model.get(state[0]) {
                    let xv = arena.var(state[0]);
                    let cv = arena.int_const(v);
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
fn int_accumulator_declines_to_unknown_but_is_never_reachable() {
    // The accumulator is genuinely safe (x ≥ 0 forever), but its `init = (x = 0)`
    // grows `R` into a disjunction the conjunctive-only `lia_interpolant` cannot
    // interpolate (no disjunctive integer fallback exists yet). The engine therefore
    // deepens and declines to `Unknown` — sound partiality. The contract is only that
    // the verdict is sound: Unknown (the expected partial-coverage outcome) or, if a
    // conjunctive interpolant happens to close it, a re-validated Safe; NEVER a wrong
    // Reachable for a safe system.
    let mut arena = TermArena::new();
    let outcome =
        prove_safety_imc_lia(&mut arena, &IntAccumulator, &SolverConfig::default()).unwrap();
    match outcome {
        ImcLiaOutcome::Unknown { .. } => {}
        ImcLiaOutcome::Safe { invariant } => {
            assert!(
                recheck_invariant(&mut arena, &IntAccumulator, invariant),
                "any Safe invariant must pass the independent 3-condition re-check over ℤ"
            );
        }
        ImcLiaOutcome::Reachable { .. } => {
            panic!("the accumulator is safe (x ≥ 0); a Reachable verdict is unsound")
        }
    }
}

#[test]
fn unsafe_system_is_never_reported_safe() {
    // Soundness-negative: an actually-unsafe system (bad x = 3 reachable in 3 steps)
    // must NEVER be reported Safe. The only sound verdicts are Reachable (a real
    // counterexample) or Unknown (a decline) — both acceptable; Safe is unsound.
    let mut arena = TermArena::new();
    let outcome =
        prove_safety_imc_lia(&mut arena, &ReachesThree, &SolverConfig::default()).unwrap();
    assert!(
        !matches!(outcome, ImcLiaOutcome::Safe { .. }),
        "an unsafe system must never be reported Safe, got {outcome:?}"
    );
}

#[test]
fn tight_timeout_yields_unknown_without_hanging() {
    let mut arena = TermArena::new();
    let config = SolverConfig::default().with_timeout(Duration::from_nanos(1));
    // A near-zero deadline must produce a first-class Unknown promptly — never a
    // hang, panic, or a fabricated Safe/Reachable.
    let outcome = prove_safety_imc_lia(&mut arena, &MonotoneLowerBound, &config).unwrap();
    assert!(
        matches!(outcome, ImcLiaOutcome::Unknown { .. }),
        "a 1 ns timeout must degrade to Unknown, got {outcome:?}"
    );
}

#[test]
fn non_lia_bv_system_declines_to_unknown_gracefully() {
    let mut arena = TermArena::new();
    // The BV system is outside the conjunctive-LIA fragment the interpolation /
    // integer decision procedures handle. The bounded check decides BV unrollings,
    // but the integer interpolation fixpoint cannot close — and crucially nothing
    // panics. A Reachable here would still be sound (BV bad = 42 is reachable), but
    // the engine must at minimum never produce a wrong Safe and never panic.
    let outcome = prove_safety_imc_lia(&mut arena, &BvSystem, &SolverConfig::default()).unwrap();
    match outcome {
        // Unknown is the expected graceful decline. A Reachable would also be sound
        // (BV bad = 42 is reachable by +1, replay-checked) — both acceptable.
        ImcLiaOutcome::Unknown { .. } | ImcLiaOutcome::Reachable { .. } => {}
        ImcLiaOutcome::Safe { invariant } => {
            // The BV system is NOT safe, so this should never happen; guard against a
            // wrong Safe with the independent re-check.
            assert!(
                recheck_invariant(&mut arena, &BvSystem, invariant),
                "a BV Safe verdict must independently re-check (it must not)"
            );
            panic!("the BV system is unsafe (42 reachable); a Safe verdict is unsound");
        }
    }
}
