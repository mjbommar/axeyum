//! Bounded model checking — reachability over a symbolic transition system.
//!
//! This is the reachability-analysis consumer the symbolic-execution primitives
//! were built for. A [`TransitionSystem`] describes a state machine symbolically
//! (state variables, an initial-state predicate, a transition relation, and a
//! "bad"/property-violation predicate). [`bounded_model_check`] unrolls it up to
//! a bound `k` and asks, at each depth, *can a bad state be reached in exactly
//! this many transitions?*
//!
//! It rides the warm [`IncrementalBvSolver`]: `init` and each `trans` step are
//! asserted once into the persistent CNF (shared subterms encode once, learned
//! clauses are kept across depths), and each depth's `bad` query is a
//! `push`/`check`/`pop` over that warm state.
//!
//! Soundness follows the project invariant exactly:
//!
//! * [`BmcOutcome::Reachable`] carries a **replay-checked** counterexample trace
//!   — the incremental solver already evaluated the model against every active
//!   assertion (`init`, the `trans` chain, and `bad`) with the ground evaluator
//!   before returning it. It is a genuine witnessed path to a bad state.
//! * [`BmcOutcome::UnreachableWithinBound`] is a **bounded** statement only: no
//!   bad state is reachable in `≤ bound` transitions. It is deliberately *not* a
//!   proof of unreachability — that needs k-induction or interpolation (a
//!   future-work lever toward unbounded safety, see PLAN.md Track C1).
//! * [`BmcOutcome::Unknown`] is first-class: a resource limit or an unsupported
//!   construct at some depth is reported honestly, never as a safe result.
//!
//! [`bounded_model_check`] rides the array-free warm path (BV/Bool transition
//! systems); [`bounded_model_check_with_memory`] adds array/symbolic-memory state
//! (`select`/`store`) via the validated eager elimination, one-shot per depth
//! (warm lazy arrays are the ADR-0030 follow-up).

use axeyum_ir::{SymbolId, TermArena, TermId};

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::incremental::IncrementalBvSolver;
use crate::model::Model;
use crate::proof::{UnsatProof, UnsatProofOutcome, export_qf_bv_unsat_proof};

/// A symbolic transition system: the input to [`bounded_model_check`].
///
/// All formulas are built over **state variable symbols**, freshly declared per
/// time step via [`state_vars`](TransitionSystem::state_vars) so that distinct
/// steps get distinct variables (the unrolling). Every step must declare the
/// same number of variables with the same sorts, in the same order.
pub trait TransitionSystem {
    /// Declares (or returns) the state variable symbols for time `step`.
    ///
    /// Implementations typically `arena.declare(&format!("{name}@{step}"), sort)`
    /// one symbol per state component. The returned arity/sorts must not vary
    /// with `step`.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if a declaration fails.
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError>;

    /// The initial-state constraint, over the step-0 variables `s0`.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if the predicate cannot be built.
    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError>;

    /// The transition relation from `pre` (step `k`) to `post` (step `k+1`).
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if the relation cannot be built.
    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError>;

    /// The "bad"/property-violation predicate over a state `s`. A bad state is
    /// the target of the reachability query.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if the predicate cannot be built.
    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError>;
}

/// The result of [`bounded_model_check`].
#[derive(Debug, Clone)]
pub enum BmcOutcome {
    /// A bad state is reachable in exactly `steps` transitions (`steps == 0`
    /// means the initial state itself is bad). `model` is the replay-checked
    /// counterexample: it assigns every step variable along the witnessing path.
    Reachable {
        /// The number of transitions to the bad state.
        steps: usize,
        /// The witnessed trace (assignments to all unrolled state variables).
        model: Model,
    },
    /// No bad state is reachable within `bound` transitions. A **bounded**
    /// guarantee, not a proof of unreachability.
    UnreachableWithinBound {
        /// The depth searched (inclusive).
        bound: usize,
    },
    /// The reachability query at depth `steps` could not be decided.
    Unknown {
        /// The depth whose query was undecided.
        steps: usize,
        /// The classified reason.
        reason: UnknownReason,
    },
}

/// Bounded model checking: is a bad state of `system` reachable within `bound`
/// transitions?
///
/// Unrolls `system` depth by depth over a warm [`IncrementalBvSolver`]. At depth
/// `k` the active assertions are `init(s0) ∧ trans(s0,s1) ∧ … ∧ trans(s_{k-1},s_k)`
/// and the query (under a temporary scope) is `bad(s_k)`; a `sat` there is a
/// length-`k` counterexample. The base assertions are warm — each `trans` step is
/// added once, so depth `k+1` reuses everything depth `k` already encoded.
///
/// Returns at the **shallowest** depth a bad state is reachable, or
/// [`BmcOutcome::UnreachableWithinBound`] if none is found through `bound`.
///
/// # Errors
///
/// Returns [`SolverError`] if building the system's terms or driving the warm
/// solver fails. A solver *timeout/unsupported* at some depth is not an error —
/// it is reported as [`BmcOutcome::Unknown`].
pub fn bounded_model_check(
    arena: &mut TermArena,
    system: &impl TransitionSystem,
    bound: usize,
    config: &SolverConfig,
) -> Result<BmcOutcome, SolverError> {
    run_bounded_model_check(arena, system, bound, config, false)
}

/// Like [`bounded_model_check`], but for transition systems whose state includes
/// **arrays / symbolic memory** (`select`/`store`) — the representation symbolic
/// execution uses for program heaps and register files.
///
/// Each depth's query is decided by the incremental engine's
/// [`check_with_memory`](IncrementalBvSolver::check_with_memory), which discharges
/// array constraints by the validated eager read-over-write + Ackermann
/// elimination (ADR-0010). Soundness is unchanged: a `sat` is replay-checked
/// against the original `select`/`store` assertions before becoming a
/// [`BmcOutcome::Reachable`] counterexample.
///
/// This first slice re-solves each depth one-shot (eager elimination does not yet
/// reuse the warm CNF across depths — warm lazy arrays are ADR-0030 follow-up), so
/// it trades the warm-solver speedup for memory support. For array-free systems it
/// agrees with [`bounded_model_check`]; prefer that one there (it stays warm).
///
/// # Errors
///
/// As [`bounded_model_check`], plus array-elimination errors from
/// [`check_with_memory`](IncrementalBvSolver::check_with_memory).
pub fn bounded_model_check_with_memory(
    arena: &mut TermArena,
    system: &impl TransitionSystem,
    bound: usize,
    config: &SolverConfig,
) -> Result<BmcOutcome, SolverError> {
    run_bounded_model_check(arena, system, bound, config, true)
}

/// Shared BMC unrolling for [`bounded_model_check`] and
/// [`bounded_model_check_with_memory`]; `use_memory` selects the array-aware
/// `check_with_memory` decision procedure for memory-bearing systems.
/// Maps a backend `Unsupported` (the warm BV solver cannot represent an operator
/// in the unrolling — e.g. an uninterpreted `Apply` in the transition relation) to
/// a first-class [`BmcOutcome::Unknown`] at depth `steps`, honoring this module's
/// contract that an unsupported query "is not an error". Any other [`SolverError`]
/// (a genuine internal failure) still propagates.
fn unsupported_to_unknown(err: SolverError, steps: usize) -> Result<BmcOutcome, SolverError> {
    match err {
        SolverError::Unsupported(detail) => Ok(BmcOutcome::Unknown {
            steps,
            reason: UnknownReason {
                kind: UnknownKind::Incomplete,
                detail,
            },
        }),
        other => Err(other),
    }
}

fn run_bounded_model_check(
    arena: &mut TermArena,
    system: &impl TransitionSystem,
    bound: usize,
    config: &SolverConfig,
    use_memory: bool,
) -> Result<BmcOutcome, SolverError> {
    let mut solver = IncrementalBvSolver::with_config(config.clone());

    // Step 0: declare s0 and pin the initial-state constraint permanently.
    let s0 = system.state_vars(arena, 0)?;
    let init = system.init(arena, &s0)?;
    if let Err(e) = solver.assert(arena, init) {
        return unsupported_to_unknown(e, 0);
    }

    let mut states: Vec<Vec<SymbolId>> = vec![s0];

    for k in 0..=bound {
        // Query: is bad(s_k) reachable given init and the trans chain so far?
        // Push a temporary scope so the bad assertion is dropped after the check.
        let bad = system.bad(arena, &states[k])?;
        solver.push()?;
        // A backend `Unsupported` from asserting/checking this depth (e.g. an
        // uninterpreted `Apply` in `bad`/the unrolling) is reported as `Unknown`,
        // not propagated as an error — pop the scope first to keep the solver warm.
        let checked = match solver.assert(arena, bad) {
            Ok(()) => {
                if use_memory {
                    solver.check_with_memory(arena)
                } else {
                    solver.check(arena)
                }
            }
            Err(e) => Err(e),
        };
        solver.pop();
        let result = match checked {
            Ok(result) => result,
            Err(e) => return unsupported_to_unknown(e, k),
        };

        match result {
            CheckResult::Sat(model) => {
                return Ok(BmcOutcome::Reachable { steps: k, model });
            }
            CheckResult::Unknown(reason) => {
                return Ok(BmcOutcome::Unknown { steps: k, reason });
            }
            CheckResult::Unsat => {}
        }

        // Extend the unrolling by one transition (unless this was the last depth).
        if k < bound {
            let next = system.state_vars(arena, k + 1)?;
            let trans = system.trans(arena, &states[k], &next)?;
            if let Err(e) = solver.assert(arena, trans) {
                return unsupported_to_unknown(e, k);
            }
            states.push(next);
        }
    }

    Ok(BmcOutcome::UnreachableWithinBound { bound })
}

/// The result of [`prove_safety_k_induction`].
#[derive(Debug, Clone)]
pub enum SafetyOutcome {
    /// The property `¬bad` holds in **every reachable state** (an unbounded
    /// guarantee), proven by `k`-induction at this `k`: no bad state is reachable
    /// within `k` transitions of an initial state (base case), and any path of
    /// `k+1` consecutive good states cannot transition into a bad state
    /// (inductive step).
    Safe {
        /// The induction depth at which both obligations discharged.
        k: usize,
    },
    /// A bad state **is** reachable: `model` is a replay-checked counterexample
    /// at `steps` transitions. The property is false.
    Reachable {
        /// The number of transitions to the bad state.
        steps: usize,
        /// The witnessed trace.
        model: Model,
    },
    /// `k`-induction was inconclusive through depth `max_k`: no counterexample was
    /// found within the base bound, but the inductive step never closed. The
    /// property may still be true — try a larger `max_k`, strengthen it with an
    /// inductive invariant, or use interpolation (future work). Reported honestly
    /// rather than as a (possibly wrong) `Safe`.
    Inconclusive {
        /// The deepest induction depth attempted.
        max_k: usize,
    },
    /// Undecided: a resource limit or unsupported construct prevented a decision.
    Unknown {
        /// The classified reason.
        reason: UnknownReason,
    },
}

/// Proves a safety property (`bad` is *never* reachable) by **k-induction** — the
/// standard lifting of bounded model checking to an *unbounded* guarantee.
///
/// For increasing `k` up to `max_k`:
///
/// * **Base case** — no bad state is reachable within `k` transitions of an
///   initial state. This is exactly [`bounded_model_check`] to depth `max_k`; a
///   `sat` here is a real counterexample ([`SafetyOutcome::Reachable`]).
/// * **Inductive step** — over *arbitrary* (not necessarily initial) states, a
///   path of `k+1` consecutive states each satisfying `¬bad`, followed by one
///   transition, cannot land in a bad state. Encoded as the unsatisfiability of
///   `¬bad(t₀) ∧ trans(t₀,t₁) ∧ … ∧ ¬bad(t_k) ∧ trans(t_k,t_{k+1}) ∧ bad(t_{k+1})`.
///
/// When both discharge at some `k`, the property holds in every reachable state
/// ([`SafetyOutcome::Safe`]). This is a genuine unbounded result, not a bounded
/// one — the step quantifies over all states, so it covers depths beyond `max_k`.
///
/// Soundness: a `Safe` verdict rests on the inductive step's `unsat` (a sound
/// CDCL result over the bit-blasted encoding) plus the base case; the technique
/// itself is sound. Incompleteness is first-class: a true-but-not-k-inductive
/// property returns [`SafetyOutcome::Inconclusive`], never a wrong `Safe`.
///
/// The inductive step reuses the per-step state-variable symbols in its own
/// independent solver (it asserts no `init`), so the two obligations do not
/// interfere.
///
/// # Errors
///
/// Returns [`SolverError`] if building the system's terms or driving the warm
/// solver fails.
pub fn prove_safety_k_induction(
    arena: &mut TermArena,
    system: &impl TransitionSystem,
    max_k: usize,
    config: &SolverConfig,
) -> Result<SafetyOutcome, SolverError> {
    // Base case: a counterexample within max_k transitions refutes safety
    // outright; otherwise the base obligation holds for every k ≤ max_k.
    match bounded_model_check(arena, system, max_k, config)? {
        BmcOutcome::Reachable { steps, model } => {
            return Ok(SafetyOutcome::Reachable { steps, model });
        }
        BmcOutcome::Unknown { reason, .. } => return Ok(SafetyOutcome::Unknown { reason }),
        BmcOutcome::UnreachableWithinBound { .. } => {}
    }

    // Inductive step, warm: assert ¬bad on the hypothesis chain and the trans
    // links once, and probe bad(t_{k+1}) under a temporary scope at each depth.
    let mut step = IncrementalBvSolver::with_config(config.clone());
    let mut t: Vec<Vec<SymbolId>> = vec![system.state_vars(arena, 0)?];
    let not_bad0 = negate_bad(arena, system, &t[0])?;
    step.assert(arena, not_bad0)?;

    for k in 0..=max_k {
        let next = system.state_vars(arena, k + 1)?;
        let trans = system.trans(arena, &t[k], &next)?;
        step.assert(arena, trans)?;
        t.push(next);

        let bad_next = system.bad(arena, &t[k + 1])?;
        step.push()?;
        step.assert(arena, bad_next)?;
        let result = step.check(arena)?;
        step.pop();

        match result {
            // No P-chain of length k+1 can reach a bad state ⇒ inductive ⇒ safe.
            CheckResult::Unsat => return Ok(SafetyOutcome::Safe { k }),
            CheckResult::Unknown(reason) => return Ok(SafetyOutcome::Unknown { reason }),
            // Step failed at this depth: extend the good-state hypothesis to
            // t_{k+1} (it becomes part of the chain for the next, deeper attempt).
            CheckResult::Sat(_) => {
                let not_bad_next = negate_bad(arena, system, &t[k + 1])?;
                step.assert(arena, not_bad_next)?;
            }
        }
    }

    Ok(SafetyOutcome::Inconclusive { max_k })
}

/// `¬bad(s)` — the per-state safety predicate `P`.
fn negate_bad(
    arena: &mut TermArena,
    system: &impl TransitionSystem,
    s: &[SymbolId],
) -> Result<TermId, SolverError> {
    let bad = system.bad(arena, s)?;
    Ok(arena.not(bad)?)
}

/// Two externally-checkable `unsat` certificates that together establish a
/// `k`-induction safety proof: the base case and the inductive step.
#[derive(Debug, Clone)]
pub struct SafetyCertificate {
    /// The induction depth the proof closed at.
    pub k: usize,
    /// DRAT-checked `unsat` of `init ∧ trans₀…ₖ ∧ (bad(s₀) ∨ … ∨ bad(s_k))` — no
    /// counterexample of length `≤ k` exists.
    pub base_case: UnsatProof,
    /// DRAT-checked `unsat` of `¬bad(t₀) ∧ trans … ∧ ¬bad(t_k) ∧ trans ∧
    /// bad(t_{k+1})` — a path of `k+1` consecutive good states cannot reach a bad
    /// one (over arbitrary, non-initial states).
    pub inductive_step: UnsatProof,
}

impl SafetyCertificate {
    /// Independently re-checks **both** induction obligations from their stored
    /// DRAT text (see [`UnsatProof::recheck`](crate::UnsatProof::recheck)). Returns
    /// `true` only if each certificate re-derives the empty clause — the
    /// consumer-side validation of the whole k-induction safety proof.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::Backend`] if either certificate is unparseable.
    pub fn recheck(&self) -> Result<bool, SolverError> {
        Ok(self.base_case.recheck()? && self.inductive_step.recheck()?)
    }
}

/// The outcome of [`certify_safety_k_induction`].
#[derive(Debug, Clone)]
pub enum CertifiedSafetyOutcome {
    /// Proven safe in every reachable state, with both `k`-induction obligations
    /// as `drat-trim`-checkable certificates (machine-checked at the clausal
    /// layer, modulo the trusted term→CNF reduction — the same caveat as every
    /// `export_qf_*_unsat_proof`).
    Safe(SafetyCertificate),
    /// A counterexample exists: `model` is a replay-checked trace at `steps`.
    Reachable {
        /// The number of transitions to the bad state.
        steps: usize,
        /// The witnessed trace.
        model: Model,
    },
    /// No `k ≤ max_k` closed the inductive step (and no counterexample within the
    /// base bound). The property may still hold — honest, not `Safe`.
    Inconclusive {
        /// The deepest depth attempted.
        max_k: usize,
    },
    /// A proof core exhausted its conflict budget on an obligation at depth `k`.
    ProofInconclusive {
        /// The depth whose obligation could not be proven within budget.
        k: usize,
    },
}

/// Like [`prove_safety_k_induction`], but a `Safe` verdict comes with **two
/// externally-checkable DRAT certificates** — one per `k`-induction obligation.
///
/// For increasing `k` up to `max_k`, both the base case and the inductive step
/// are exported through [`export_qf_bv_unsat_proof`](crate::export_qf_bv_unsat_proof),
/// which bit-blasts the obligation, runs the proof-producing CDCL core, and
/// self-verifies the DRAT before returning it. A `Safe` result therefore carries
/// proof a consumer (or `drat-trim`, or eventually a Lean checker) can re-check
/// offline — the reachability track meeting the trusted-checking north star.
///
/// Outcomes mirror [`SafetyOutcome`] but with certificates on `Safe`; a base case
/// that turns out *satisfiable* means a counterexample exists, recovered (with its
/// model) via [`bounded_model_check`] and returned as
/// [`CertifiedSafetyOutcome::Reachable`].
///
/// Array-free `QF_BV`/Bool transition systems only (the proof exporter does not
/// take arrays; certified memory safety would ride `export_qf_abv_unsat_proof`).
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for non-QF_BV constructs (e.g. arrays),
/// or [`SolverError::Backend`] on an encoding failure, a proof that fails to
/// check (a soundness alarm), or a base/BMC disagreement.
pub fn certify_safety_k_induction(
    arena: &mut TermArena,
    system: &impl TransitionSystem,
    max_k: usize,
    config: &SolverConfig,
) -> Result<CertifiedSafetyOutcome, SolverError> {
    for k in 0..=max_k {
        // Base case: is there a counterexample of length ≤ k?
        let base = base_case_assertions(arena, system, k)?;
        match export_qf_bv_unsat_proof(arena, &base)? {
            UnsatProofOutcome::Satisfiable => {
                // A counterexample exists within k; recover its model and depth.
                return match bounded_model_check(arena, system, k, config)? {
                    BmcOutcome::Reachable { steps, model } => {
                        Ok(CertifiedSafetyOutcome::Reachable { steps, model })
                    }
                    other => Err(SolverError::Backend(format!(
                        "base case at k={k} is satisfiable but BMC returned {other:?}"
                    ))),
                };
            }
            UnsatProofOutcome::Inconclusive => {
                return Ok(CertifiedSafetyOutcome::ProofInconclusive { k });
            }
            UnsatProofOutcome::Proved(base_case) => {
                // Base holds at k; try to close the inductive step at the same k.
                let step = inductive_step_assertions(arena, system, k)?;
                match export_qf_bv_unsat_proof(arena, &step)? {
                    UnsatProofOutcome::Proved(inductive_step) => {
                        return Ok(CertifiedSafetyOutcome::Safe(SafetyCertificate {
                            k,
                            base_case,
                            inductive_step,
                        }));
                    }
                    // Step failed at this k: deepen the induction.
                    UnsatProofOutcome::Satisfiable => {}
                    UnsatProofOutcome::Inconclusive => {
                        return Ok(CertifiedSafetyOutcome::ProofInconclusive { k });
                    }
                }
            }
        }
    }

    Ok(CertifiedSafetyOutcome::Inconclusive { max_k })
}

/// The base-case obligation at depth `k`: `init(s₀) ∧ trans(s₀,s₁) ∧ … ∧
/// trans(s_{k-1},s_k) ∧ (bad(s₀) ∨ … ∨ bad(s_k))`. Unsatisfiable iff no bad state
/// is reachable within `k` transitions.
fn base_case_assertions(
    arena: &mut TermArena,
    system: &impl TransitionSystem,
    k: usize,
) -> Result<Vec<TermId>, SolverError> {
    let mut states = vec![system.state_vars(arena, 0)?];
    let mut assertions = vec![system.init(arena, &states[0])?];
    for i in 0..k {
        let next = system.state_vars(arena, i + 1)?;
        let trans = system.trans(arena, &states[i], &next)?;
        assertions.push(trans);
        states.push(next);
    }
    let mut bad_any = system.bad(arena, &states[0])?;
    for state in states.iter().skip(1) {
        let bad_i = system.bad(arena, state)?;
        bad_any = arena.or(bad_any, bad_i)?;
    }
    assertions.push(bad_any);
    Ok(assertions)
}

/// The inductive-step obligation at depth `k`: `¬bad(t₀) ∧ trans(t₀,t₁) ∧ … ∧
/// ¬bad(t_k) ∧ trans(t_k,t_{k+1}) ∧ bad(t_{k+1})` over arbitrary (non-initial)
/// states. Unsatisfiable iff `k+1` consecutive good states cannot transition into
/// a bad one.
fn inductive_step_assertions(
    arena: &mut TermArena,
    system: &impl TransitionSystem,
    k: usize,
) -> Result<Vec<TermId>, SolverError> {
    let mut t = vec![system.state_vars(arena, 0)?];
    let mut assertions = vec![negate_bad(arena, system, &t[0])?];
    for i in 0..=k {
        let next = system.state_vars(arena, i + 1)?;
        let trans = system.trans(arena, &t[i], &next)?;
        assertions.push(trans);
        t.push(next);
        let tail = if i < k {
            negate_bad(arena, system, &t[i + 1])?
        } else {
            system.bad(arena, &t[i + 1])?
        };
        assertions.push(tail);
    }
    Ok(assertions)
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::{ArraySortKey, Sort, Value};

    /// An 8-bit counter: `x@0 = start`, `x@{k+1} = x@k + 1`, bad when `x = target`.
    struct Counter {
        start: u128,
        target: u128,
    }

    fn counter_var(arena: &mut TermArena, step: usize) -> SymbolId {
        arena
            .declare(&format!("x@{step}"), Sort::BitVec(8))
            .unwrap()
    }

    impl TransitionSystem for Counter {
        fn state_vars(
            &self,
            arena: &mut TermArena,
            step: usize,
        ) -> Result<Vec<SymbolId>, SolverError> {
            Ok(vec![counter_var(arena, step)])
        }

        fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
            let x = arena.var(s0[0]);
            let c = arena.bv_const(8, self.start)?;
            Ok(arena.eq(x, c)?)
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
            let c = arena.bv_const(8, self.target)?;
            Ok(arena.eq(x, c)?)
        }
    }

    /// An 8-bit system whose step function is an **uninterpreted** `f`:
    /// `x@0 = 0`, `x@{k+1} = f(x@k)`, bad when `x = 42`. The warm BV backend
    /// cannot represent `Apply`, so per the module contract the run must report
    /// `Unknown` (a graceful first-class result), never an `Err`.
    struct UfStepper;

    impl TransitionSystem for UfStepper {
        fn state_vars(
            &self,
            arena: &mut TermArena,
            step: usize,
        ) -> Result<Vec<SymbolId>, SolverError> {
            Ok(vec![counter_var(arena, step)])
        }

        fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
            let x = arena.var(s0[0]);
            let c = arena.bv_const(8, 0)?;
            Ok(arena.eq(x, c)?)
        }

        fn trans(
            &self,
            arena: &mut TermArena,
            pre: &[SymbolId],
            post: &[SymbolId],
        ) -> Result<TermId, SolverError> {
            let f = arena
                .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
                .unwrap();
            let x = arena.var(pre[0]);
            let fx = arena.apply(f, &[x])?;
            let x_next = arena.var(post[0]);
            Ok(arena.eq(x_next, fx)?)
        }

        fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
            let x = arena.var(s[0]);
            let c = arena.bv_const(8, 42)?;
            Ok(arena.eq(x, c)?)
        }
    }

    #[test]
    fn unsupported_uf_transition_is_unknown_not_error() {
        let mut arena = TermArena::new();
        // The transition relation uses an uninterpreted `Apply`, which the warm BV
        // solver rejects. The run must surface that as a first-class `Unknown`,
        // honoring the documented "unsupported is not an error" contract — NOT a
        // hard `Err` (the prior behavior that violated the hard rule).
        let outcome = bounded_model_check(&mut arena, &UfStepper, 3, &SolverConfig::default());
        match outcome {
            Ok(BmcOutcome::Unknown { .. }) => {}
            other => panic!("expected Ok(Unknown) for a UF transition, got {other:?}"),
        }
    }

    #[test]
    fn reachable_counter_finds_shallowest_depth() {
        let mut arena = TermArena::new();
        let system = Counter {
            start: 0,
            target: 5,
        };
        let outcome =
            bounded_model_check(&mut arena, &system, 10, &SolverConfig::default()).unwrap();
        match outcome {
            BmcOutcome::Reachable { steps, model } => {
                assert_eq!(steps, 5, "0 → 5 takes exactly five increments");
                // The counterexample trace is a genuine, replay-checked path.
                for k in 0..=5u128 {
                    let sym = arena.find_symbol(&format!("x@{k}")).unwrap();
                    assert_eq!(
                        model.get(sym),
                        Some(Value::Bv { width: 8, value: k }),
                        "trace value at step {k}"
                    );
                }
            }
            other => panic!("expected Reachable, got {other:?}"),
        }
    }

    #[test]
    fn reachable_at_step_zero_when_init_is_bad() {
        let mut arena = TermArena::new();
        let system = Counter {
            start: 7,
            target: 7,
        };
        let outcome =
            bounded_model_check(&mut arena, &system, 4, &SolverConfig::default()).unwrap();
        assert!(
            matches!(outcome, BmcOutcome::Reachable { steps: 0, .. }),
            "init state already bad ⇒ reachable in 0 transitions, got {outcome:?}"
        );
    }

    #[test]
    fn unreachable_within_bound_is_honest_and_bounded() {
        let mut arena = TermArena::new();
        // 0,1,2,3 in four steps never reaches 200.
        let system = Counter {
            start: 0,
            target: 200,
        };
        let outcome =
            bounded_model_check(&mut arena, &system, 3, &SolverConfig::default()).unwrap();
        assert!(
            matches!(outcome, BmcOutcome::UnreachableWithinBound { bound: 3 }),
            "200 is unreachable within 3 increments from 0, got {outcome:?}"
        );
    }

    #[test]
    fn deeper_bound_eventually_reaches_a_wrapping_target() {
        // The counter wraps mod 256; target 250 is reachable from 248 in 2 steps.
        let mut arena = TermArena::new();
        let system = Counter {
            start: 248,
            target: 250,
        };
        let outcome =
            bounded_model_check(&mut arena, &system, 8, &SolverConfig::default()).unwrap();
        assert!(
            matches!(outcome, BmcOutcome::Reachable { steps: 2, .. }),
            "248 → 250 is two increments, got {outcome:?}"
        );
    }

    /// An 8-bit register stepping by +2 from 0; "bad" = the value is odd. The
    /// invariant "x is even" is genuinely *inductive* (even + 2 is even), so
    /// k-induction proves unbounded safety already at k = 0 (plain induction).
    struct EvenStepper;

    impl EvenStepper {
        fn is_odd(arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
            let x = arena.var(s[0]);
            let one = arena.bv_const(8, 1)?;
            let lsb = arena.bv_and(x, one)?;
            Ok(arena.eq(lsb, one)?)
        }
    }

    impl TransitionSystem for EvenStepper {
        fn state_vars(
            &self,
            arena: &mut TermArena,
            step: usize,
        ) -> Result<Vec<SymbolId>, SolverError> {
            Ok(vec![counter_var(arena, step)])
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
            let two = arena.bv_const(8, 2)?;
            let inc = arena.bv_add(x, two)?;
            let x_next = arena.var(post[0]);
            Ok(arena.eq(x_next, inc)?)
        }

        fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
            Self::is_odd(arena, s)
        }
    }

    #[test]
    fn k_induction_proves_unbounded_safety() {
        let mut arena = TermArena::new();
        let outcome =
            prove_safety_k_induction(&mut arena, &EvenStepper, 4, &SolverConfig::default())
                .unwrap();
        assert!(
            matches!(outcome, SafetyOutcome::Safe { k: 0 }),
            "‘x even’ is 0-inductive ⇒ unbounded Safe at k=0, got {outcome:?}"
        );
    }

    #[test]
    fn k_induction_returns_counterexample_for_unsafe_property() {
        let mut arena = TermArena::new();
        // Counter from 0 reaches 5; "bad = x == 5" is genuinely violated.
        let system = Counter {
            start: 0,
            target: 5,
        };
        let outcome =
            prove_safety_k_induction(&mut arena, &system, 8, &SolverConfig::default()).unwrap();
        assert!(
            matches!(outcome, SafetyOutcome::Reachable { steps: 5, .. }),
            "k-induction base case must surface the real counterexample, got {outcome:?}"
        );
    }

    #[test]
    fn k_induction_is_honestly_inconclusive_not_wrongly_safe() {
        let mut arena = TermArena::new();
        // "x != 100" holds for the first few steps but is NOT k-inductive for any
        // small k (the 99 → 100 transition always breaks the step), and the base
        // bound (3) is too shallow to find the real counterexample at step 100.
        // The only sound answer is Inconclusive — never Safe.
        let system = Counter {
            start: 0,
            target: 100,
        };
        let outcome =
            prove_safety_k_induction(&mut arena, &system, 3, &SolverConfig::default()).unwrap();
        assert!(
            matches!(outcome, SafetyOutcome::Inconclusive { max_k: 3 }),
            "must not over-claim Safe for a non-inductive property, got {outcome:?}"
        );
    }

    /// A memory-bearing system: a 4-cell array `mem` (2-bit index → 8-bit value)
    /// and a 2-bit write pointer `i`. `init`: all cells 0, `i = 0`. `trans`:
    /// `mem' = store(mem, i, 7)`, `i' = i + 1`. `bad`: `mem[3] == 7`. Cell 3 is
    /// first written when the pointer reaches 3 — i.e. the `3 → 4` transition —
    /// so a bad state is reachable in exactly four steps. Exercises the
    /// symbolic-memory (`select`/`store`) reachability path.
    struct MemWriter;

    impl MemWriter {
        fn mem(arena: &mut TermArena, step: usize) -> SymbolId {
            arena
                .declare(
                    &format!("mem@{step}"),
                    Sort::Array {
                        index: ArraySortKey::BitVec(2),
                        element: ArraySortKey::BitVec(8),
                    },
                )
                .unwrap()
        }
        fn ptr(arena: &mut TermArena, step: usize) -> SymbolId {
            arena
                .declare(&format!("i@{step}"), Sort::BitVec(2))
                .unwrap()
        }
    }

    impl TransitionSystem for MemWriter {
        fn state_vars(
            &self,
            arena: &mut TermArena,
            step: usize,
        ) -> Result<Vec<SymbolId>, SolverError> {
            Ok(vec![Self::mem(arena, step), Self::ptr(arena, step)])
        }

        fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
            let mem = arena.var(s0[0]);
            let zero8 = arena.bv_const(8, 0)?;
            let all_zero = arena.const_array(2, zero8)?;
            let mem_init = arena.eq(mem, all_zero)?;
            let ptr = arena.var(s0[1]);
            let zero2 = arena.bv_const(2, 0)?;
            let ptr_init = arena.eq(ptr, zero2)?;
            Ok(arena.and(mem_init, ptr_init)?)
        }

        fn trans(
            &self,
            arena: &mut TermArena,
            pre: &[SymbolId],
            post: &[SymbolId],
        ) -> Result<TermId, SolverError> {
            let mem = arena.var(pre[0]);
            let i = arena.var(pre[1]);
            let seven = arena.bv_const(8, 7)?;
            let written = arena.store(mem, i, seven)?;
            let mem_next = arena.var(post[0]);
            let mem_step = arena.eq(mem_next, written)?;

            let one = arena.bv_const(2, 1)?;
            let inc = arena.bv_add(i, one)?;
            let ptr_next = arena.var(post[1]);
            let ptr_step = arena.eq(ptr_next, inc)?;
            Ok(arena.and(mem_step, ptr_step)?)
        }

        fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
            let mem = arena.var(s[0]);
            let three = arena.bv_const(2, 3)?;
            let cell3 = arena.select(mem, three)?;
            let seven = arena.bv_const(8, 7)?;
            Ok(arena.eq(cell3, seven)?)
        }
    }

    #[test]
    fn memory_bmc_reaches_a_written_cell() {
        let mut arena = TermArena::new();
        let outcome =
            bounded_model_check_with_memory(&mut arena, &MemWriter, 6, &SolverConfig::default())
                .unwrap();
        assert!(
            matches!(outcome, BmcOutcome::Reachable { steps: 4, .. }),
            "mem[3] is first written on the 3→4 transition, got {outcome:?}"
        );
    }

    #[test]
    fn memory_bmc_is_bounded_before_the_write() {
        let mut arena = TermArena::new();
        // Through step 3 the pointer has only visited cells 0,1,2; mem[3] is still 0.
        let outcome =
            bounded_model_check_with_memory(&mut arena, &MemWriter, 3, &SolverConfig::default())
                .unwrap();
        assert!(
            matches!(outcome, BmcOutcome::UnreachableWithinBound { bound: 3 }),
            "mem[3] is untouched within three steps, got {outcome:?}"
        );
    }

    #[test]
    fn certified_k_induction_emits_checkable_proofs() {
        let mut arena = TermArena::new();
        let outcome =
            certify_safety_k_induction(&mut arena, &EvenStepper, 4, &SolverConfig::default())
                .unwrap();
        let CertifiedSafetyOutcome::Safe(cert) = outcome else {
            panic!("expected a certified Safe verdict, got {outcome:?}");
        };
        assert_eq!(cert.k, 0, "‘x even’ is 0-inductive");
        // Each obligation carries non-empty certificate text, and the whole proof
        // re-checks independently through the consumer-side entry point.
        for proof in [&cert.base_case, &cert.inductive_step] {
            assert!(!proof.dimacs.is_empty() && !proof.drat.is_empty());
            assert!(proof.recheck().unwrap(), "each obligation must re-check");
        }
        assert!(
            cert.recheck().unwrap(),
            "the whole k-induction certificate must re-check independently"
        );
    }

    #[test]
    fn certified_k_induction_surfaces_counterexample_for_unsafe() {
        let mut arena = TermArena::new();
        let system = Counter {
            start: 0,
            target: 5,
        };
        let outcome =
            certify_safety_k_induction(&mut arena, &system, 8, &SolverConfig::default()).unwrap();
        assert!(
            matches!(outcome, CertifiedSafetyOutcome::Reachable { steps: 5, .. }),
            "an unsafe property has no safety certificate; expected Reachable, got {outcome:?}"
        );
    }

    #[test]
    fn certified_k_induction_is_honestly_inconclusive() {
        let mut arena = TermArena::new();
        let system = Counter {
            start: 0,
            target: 100,
        };
        let outcome =
            certify_safety_k_induction(&mut arena, &system, 3, &SolverConfig::default()).unwrap();
        assert!(
            matches!(outcome, CertifiedSafetyOutcome::Inconclusive { max_k: 3 }),
            "never fabricate a certificate for a non-inductive property, got {outcome:?}"
        );
    }
}
