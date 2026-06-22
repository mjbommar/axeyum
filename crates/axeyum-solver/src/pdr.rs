//! IC3/PDR — inductive-invariant discovery over a symbolic transition system.
//!
//! Bounded model checking ([`bounded_model_check`](crate::bounded_model_check))
//! refutes safety; k-induction
//! ([`prove_safety_k_induction`](crate::prove_safety_k_induction)) proves it when
//! the property is *k*-inductive. Many true safety properties are **not**
//! k-inductive for any small `k` — they need an auxiliary inductive *invariant*
//! that is not the property itself. `IC3`/`PDR` (property-directed reachability)
//! *discovers* such an invariant by incrementally learning relatively-inductive
//! blocking clauses ("lemmas") organized into a sequence of frames.
//!
//! # The soundness contract (the whole point)
//!
//! The `IC3` search in this module is **untrusted**. Its frames, proof
//! obligations, cube extraction, and generalization are all best-effort: a bug in
//! any of them can only ever cause an over-eager [`PdrOutcome::Unknown`], never a
//! wrong [`PdrOutcome::Safe`]. That guarantee is enforced by a *single* trusted
//! gate, [`verify_invariant`], run before any `Safe` is returned: the candidate
//! invariant `Inv` (the conjunction of a converged frame's lemma clauses) must
//! pass all three classical inductive-invariant checks, each decided independently
//! by the trusted decider [`check_auto`](crate::check_auto):
//!
//! 1. **Initiation** — `init(s) ∧ ¬Inv(s)` is `unsat` (every initial state
//!    satisfies `Inv`).
//! 2. **Consecution** — `Inv(s) ∧ trans(s, s') ∧ ¬Inv(s')` is `unsat` (`Inv` is
//!    closed under the transition relation).
//! 3. **Safety** — `Inv(s) ∧ bad(s)` is `unsat` (`Inv` excludes every bad state).
//!
//! Only if all three are `Unsat` is `Safe { invariant }` returned; otherwise the
//! engine declines to [`PdrOutcome::Unknown`]. A [`PdrOutcome::Reachable`] verdict
//! is likewise gated: the `IC3` search may *believe* it found a counterexample,
//! but the result is confirmed only by
//! [`bounded_model_check`](crate::bounded_model_check) returning a replay-checked
//! [`BmcOutcome::Reachable`](crate::BmcOutcome::Reachable) trace.
//!
//! Every resource cap (frames, obligations, iterations, `config.timeout`) degrades
//! to `Unknown`; the engine never hangs and never panics on adversarial input.

use std::time::Instant;

use axeyum_ir::{SymbolId, TermArena, TermId, Value};

use crate::auto::check_auto;
use crate::backend::{CheckResult, SolverConfig, SolverError};
use crate::bmc::{BmcOutcome, TransitionSystem, bounded_model_check};
use crate::incremental::IncrementalBvSolver;
use crate::model::Model;
use crate::proof::{UnsatProof, UnsatProofOutcome, export_qf_bv_unsat_proof};

/// Resource caps for the `IC3`/`PDR` search. All degrade to
/// [`PdrOutcome::Unknown`]; none can cause a wrong verdict.
#[derive(Debug, Clone)]
#[allow(clippy::struct_field_names)]
struct PdrLimits {
    /// Maximum number of frames `F[0..=max_frames]` before declining.
    max_frames: usize,
    /// Maximum proof obligations processed per `block` call.
    max_obligations: usize,
    /// Maximum top-level outer iterations (one per new frame attempt).
    max_iterations: usize,
}

impl Default for PdrLimits {
    fn default() -> Self {
        Self {
            max_frames: 64,
            max_obligations: 100_000,
            max_iterations: 4096,
        }
    }
}

/// The result of [`prove_safety_pdr`].
#[derive(Debug, Clone)]
pub enum PdrOutcome {
    /// The property holds in every reachable state, proven by the discovered
    /// inductive invariant `invariant` — a [`TermId`] (a conjunction of the
    /// converged frame's lemma clauses) that **passed all three** independent
    /// implication checks (initiation, consecution, safety) under the trusted
    /// [`check_auto`](crate::check_auto) decider. This is an unbounded guarantee.
    Safe {
        /// The discovered inductive invariant `Inv(s)`, as a Boolean term over the
        /// step-0 state variables. Re-checkable: assert `init ∧ ¬Inv`,
        /// `Inv ∧ trans ∧ ¬Inv'`, and `Inv ∧ bad`; each must be `unsat`.
        invariant: TermId,
    },
    /// A bad state **is** reachable: `model` is a replay-checked counterexample at
    /// `steps` transitions, confirmed by
    /// [`bounded_model_check`](crate::bounded_model_check). The property is false.
    Reachable {
        /// The number of transitions to the bad state.
        steps: usize,
        /// The witnessed trace.
        model: Model,
    },
    /// Undecided: a resource cap, an unsupported construct, or a candidate
    /// invariant that failed its inductive verification. First-class and honest —
    /// never a (possibly wrong) `Safe`.
    Unknown {
        /// A human-readable reason for declining.
        reason: String,
    },
}

/// A literal of a state cube: a single state variable constrained to a concrete
/// value (`var == value`), or its negation (`var != value`). A *cube* is a
/// conjunction of such literals (a partial state); a *clause* is the negation of a
/// cube (a disjunction of negated literals — a blocking lemma).
#[derive(Debug, Clone, PartialEq, Eq)]
struct CubeLit {
    /// The state variable.
    sym: SymbolId,
    /// Its pinned value.
    value: Value,
}

/// A cube: a conjunction of [`CubeLit`]s, deterministically ordered. Represents a
/// (partial) state to be blocked.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Cube {
    lits: Vec<CubeLit>,
}

impl Cube {
    /// Builds the cube describing `model`'s assignment to `state_vars` (skipping
    /// any unassigned symbol). Deterministic: literals follow `state_vars` order.
    fn from_model(model: &Model, state_vars: &[SymbolId]) -> Self {
        let mut lits = Vec::new();
        for &sym in state_vars {
            if let Some(value) = model.get(sym) {
                lits.push(CubeLit { sym, value });
            }
        }
        Cube { lits }
    }

    /// The cube as a Boolean term over `vars` (a primed/unprimed copy): the
    /// conjunction `⋀ vars[i] == lits[i].value`. The literal at position `j` uses
    /// `vars[index_of(lits[j].sym in base)]`; here cubes are always built from a
    /// known `base` ordering, so we pass an explicit `(base → vars)` remap.
    fn to_term(
        &self,
        arena: &mut TermArena,
        base: &[SymbolId],
        vars: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let mut acc: Option<TermId> = None;
        for lit in &self.lits {
            let Some(pos) = base.iter().position(|&s| s == lit.sym) else {
                continue;
            };
            let var = arena.var(vars[pos]);
            let constant = value_const(arena, &lit.value)?;
            let equal = arena.eq(var, constant)?;
            acc = Some(match acc {
                None => equal,
                Some(prev) => arena.and(prev, equal)?,
            });
        }
        match acc {
            Some(term) => Ok(term),
            None => Ok(arena.bool_const(true)),
        }
    }

    /// The blocking clause `¬cube` over `vars`: `⋁ vars[i] != lits[i].value`.
    fn to_clause_term(
        &self,
        arena: &mut TermArena,
        base: &[SymbolId],
        vars: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let cube = self.to_term(arena, base, vars)?;
        Ok(arena.not(cube)?)
    }
}

/// A learned lemma: a blocking clause, stored as the cube it negates (so literal
/// dropping during generalization is just cube-literal removal).
type Lemma = Cube;

/// The discovered invariant bundled with its three re-checkable `unsat`
/// certificates — the certified analogue of
/// [`SafetyCertificate`](crate::SafetyCertificate) for the `IC3`/`PDR` route.
///
/// A `Safe` verdict here is backed by three `drat`-checkable proofs, one per
/// inductive-invariant obligation. [`recheck`](ChcSafetyCertificate::recheck)
/// re-derives the empty clause from each, the consumer-side validation of the
/// whole safety argument (modulo the trusted term→CNF reduction — the same caveat
/// as every `export_qf_*_unsat_proof`).
#[derive(Debug, Clone)]
pub struct ChcSafetyCertificate {
    /// The discovered inductive invariant `Inv(s)` over the step-0 state variables.
    pub invariant: TermId,
    /// `unsat` of `init(s) ∧ ¬Inv(s)` — every initial state satisfies `Inv`.
    pub initiation: UnsatProof,
    /// `unsat` of `Inv(s) ∧ trans(s, s') ∧ ¬Inv(s')` — `Inv` is transition-closed.
    pub consecution: UnsatProof,
    /// `unsat` of `Inv(s) ∧ bad(s)` — `Inv` excludes every bad state.
    pub safety: UnsatProof,
}

impl ChcSafetyCertificate {
    /// Independently re-checks **all three** invariant obligations from their
    /// stored `DRAT` text. Returns `true` only if each re-derives the empty clause
    /// — the consumer-side validation of the whole `IC3`/`PDR` safety proof.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::Backend`] if any certificate is unparseable.
    pub fn recheck(&self) -> Result<bool, SolverError> {
        Ok(self.initiation.recheck()? && self.consecution.recheck()? && self.safety.recheck()?)
    }
}

/// The outcome of [`prove_safety_pdr_certified`].
#[derive(Debug, Clone)]
pub enum CertifiedPdrOutcome {
    /// Proven safe by a discovered inductive invariant, with all three obligations
    /// as `drat`-checkable certificates.
    Safe(ChcSafetyCertificate),
    /// A counterexample exists: `model` is a replay-checked trace at `steps`.
    Reachable {
        /// The number of transitions to the bad state.
        steps: usize,
        /// The witnessed trace.
        model: Model,
    },
    /// Undecided (resource cap, unsupported construct, or a discovered invariant
    /// whose certificate did not check). Honest, never `Safe`.
    Unknown {
        /// A human-readable reason.
        reason: String,
    },
}

/// Proves a safety property (`bad` is *never* reachable) by **`IC3`/`PDR`
/// inductive-invariant discovery** — succeeding on true properties that are not
/// k-inductive (where [`prove_safety_k_induction`](crate::prove_safety_k_induction)
/// returns `Inconclusive`).
///
/// The untrusted `IC3` search learns relatively-inductive blocking clauses across
/// a growing frame sequence until a frame converges (a fixpoint), then bundles
/// that frame's lemmas into a candidate invariant. **No `Safe` is returned until
/// that candidate passes all three independent implication checks** (initiation,
/// consecution, safety) under the trusted [`check_auto`](crate::check_auto)
/// decider; otherwise the engine declines to [`PdrOutcome::Unknown`]. A
/// [`PdrOutcome::Reachable`] is confirmed by
/// [`bounded_model_check`](crate::bounded_model_check). Array-free `QF_BV`/Bool
/// transition systems only.
///
/// # Errors
///
/// Returns [`SolverError`] only for a genuine internal failure while building the
/// system's terms; a solver `timeout`/`unsupported`/unsupported-construct or a
/// failed invariant verification is reported as [`PdrOutcome::Unknown`], never an
/// error.
pub fn prove_safety_pdr(
    arena: &mut TermArena,
    system: &impl TransitionSystem,
    config: &SolverConfig,
) -> Result<PdrOutcome, SolverError> {
    let limits = PdrLimits::default();
    let mut engine = match Ic3Engine::new(arena, system, config, limits) {
        Ok(engine) => engine,
        Err(EngineSetup::Unsupported(reason)) => return Ok(PdrOutcome::Unknown { reason }),
        Err(EngineSetup::Error(error)) => return Err(error),
    };
    engine.run(arena)
}

/// Like [`prove_safety_pdr`], but a `Safe` verdict comes bundled with **three
/// externally-checkable `DRAT` certificates** — one per inductive-invariant
/// obligation ([`ChcSafetyCertificate`]).
///
/// The invariant is discovered and verified exactly as in [`prove_safety_pdr`];
/// then each of the three obligations is re-exported through
/// [`export_qf_bv_unsat_proof`](crate::export_qf_bv_unsat_proof), which bit-blasts
/// it, runs the proof-producing CDCL core, and self-verifies the `DRAT`. If any
/// export does not prove `unsat` (it should, since the same query was just decided
/// `unsat` by [`check_auto`](crate::check_auto)), the engine declines to
/// [`CertifiedPdrOutcome::Unknown`] rather than emit an unbacked `Safe`.
///
/// # Errors
///
/// As [`prove_safety_pdr`].
pub fn prove_safety_pdr_certified(
    arena: &mut TermArena,
    system: &impl TransitionSystem,
    config: &SolverConfig,
) -> Result<CertifiedPdrOutcome, SolverError> {
    match prove_safety_pdr(arena, system, config)? {
        PdrOutcome::Reachable { steps, model } => {
            Ok(CertifiedPdrOutcome::Reachable { steps, model })
        }
        PdrOutcome::Unknown { reason } => Ok(CertifiedPdrOutcome::Unknown { reason }),
        PdrOutcome::Safe { invariant } => certify_discovered_invariant(arena, system, invariant),
    }
}

/// Re-exports the three invariant obligations as `DRAT` certificates for an
/// already-verified `invariant`. Declines (`Unknown`) if any export fails to prove
/// `unsat` — never emits an unbacked certificate.
fn certify_discovered_invariant(
    arena: &mut TermArena,
    system: &impl TransitionSystem,
    invariant: TermId,
) -> Result<CertifiedPdrOutcome, SolverError> {
    let s = system.state_vars(arena, 0)?;
    let sp = system.state_vars(arena, 1)?;

    // Initiation: init(s) ∧ ¬Inv(s).
    let init = system.init(arena, &s)?;
    let not_inv = arena.not(invariant)?;
    let UnsatProofOutcome::Proved(initiation) = export_qf_bv_unsat_proof(arena, &[init, not_inv])?
    else {
        return Ok(decline_certificate("initiation"));
    };

    // Consecution: Inv(s) ∧ trans(s, s') ∧ ¬Inv(s').
    let inv_primed = prime_invariant(arena, invariant, &s, &sp)?;
    let trans = system.trans(arena, &s, &sp)?;
    let not_inv_primed = arena.not(inv_primed)?;
    let UnsatProofOutcome::Proved(consecution) =
        export_qf_bv_unsat_proof(arena, &[invariant, trans, not_inv_primed])?
    else {
        return Ok(decline_certificate("consecution"));
    };

    // Safety: Inv(s) ∧ bad(s).
    let bad = system.bad(arena, &s)?;
    let UnsatProofOutcome::Proved(safety) = export_qf_bv_unsat_proof(arena, &[invariant, bad])?
    else {
        return Ok(decline_certificate("safety"));
    };

    Ok(CertifiedPdrOutcome::Safe(ChcSafetyCertificate {
        invariant,
        initiation,
        consecution,
        safety,
    }))
}

fn decline_certificate(which: &str) -> CertifiedPdrOutcome {
    CertifiedPdrOutcome::Unknown {
        reason: format!(
            "{which} obligation did not export a checkable unsat proof (declining rather than \
             emitting an unbacked certificate)"
        ),
    }
}

/// Setup failures for [`Ic3Engine::new`]: an unsupported construct degrades to
/// `Unknown` at the caller; a genuine error propagates.
enum EngineSetup {
    Unsupported(String),
    Error(SolverError),
}

impl From<SolverError> for EngineSetup {
    fn from(error: SolverError) -> Self {
        EngineSetup::Error(error)
    }
}

/// The `IC3`/`PDR` engine over a fixed transition system. Frames are sets of
/// lemmas (blocking clauses, stored as the cubes they negate); `F[0]` is `init`.
struct Ic3Engine<'sys, S: TransitionSystem> {
    system: &'sys S,
    config: SolverConfig,
    limits: PdrLimits,
    deadline: Option<Instant>,
    /// The step-0 state-variable symbols (the canonical "unprimed" copy).
    s: Vec<SymbolId>,
    /// The step-1 state-variable symbols (the "primed" copy).
    sp: Vec<SymbolId>,
    /// `F[i]` for `i >= 1` is the set of lemmas at frame `i`; `F[0]` is `init`,
    /// handled specially. Index 0 of this vector corresponds to `F[1]`.
    frames: Vec<Vec<Lemma>>,
}

impl<'sys, S: TransitionSystem> Ic3Engine<'sys, S> {
    fn new(
        arena: &mut TermArena,
        system: &'sys S,
        config: &SolverConfig,
        limits: PdrLimits,
    ) -> Result<Self, EngineSetup> {
        let s = system.state_vars(arena, 0)?;
        let sp = system.state_vars(arena, 1)?;
        if s.len() != sp.len() {
            return Err(EngineSetup::Unsupported(
                "transition system declared a different number of state variables per step"
                    .to_owned(),
            ));
        }
        let deadline = config.timeout.map(|d| Instant::now() + d);
        Ok(Self {
            system,
            config: config.clone(),
            limits,
            deadline,
            s,
            sp,
            frames: Vec::new(),
        })
    }

    /// `true` if the configured timeout has elapsed.
    fn timed_out(&self) -> bool {
        self.deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
    }

    /// The current top frame index `k` (`F[k]` is the deepest frame). `F[0]=init`
    /// plus `frames.len()` learned frames ⇒ `k == frames.len()`.
    fn k(&self) -> usize {
        self.frames.len()
    }

    /// Drives the `IC3` loop. See the module docs for the soundness gate.
    fn run(&mut self, arena: &mut TermArena) -> Result<PdrOutcome, SolverError> {
        // F[0] = init. Quick check: is init itself bad? (BMC at depth 0 confirms.)
        // Start with one empty learned frame F[1].
        self.frames.push(Vec::new());

        for _iteration in 0..self.limits.max_iterations {
            if self.timed_out() {
                return Ok(unknown("PDR timed out"));
            }
            if self.k() > self.limits.max_frames {
                return Ok(unknown("PDR exceeded the maximum frame count"));
            }

            // 1. Block all bad states at the top frame F[k].
            match self.block_bad_states(arena)? {
                BlockResult::Blocked => {}
                BlockResult::Cex => {
                    // The search believes a counterexample exists. Confirm with BMC
                    // (the only trusted source of a Reachable verdict).
                    return self.confirm_cex(arena);
                }
                BlockResult::Decline(reason) => return Ok(unknown(&reason)),
            }

            // 2. Push a new frame and propagate lemmas forward.
            self.frames.push(Vec::new());
            match self.propagate(arena)? {
                PropagateResult::Fixpoint(frame_index) => {
                    return self.finish_with_invariant(arena, frame_index);
                }
                PropagateResult::Continue => {}
                PropagateResult::Decline(reason) => return Ok(unknown(&reason)),
            }
        }

        Ok(unknown("PDR exceeded the maximum iteration count"))
    }

    /// Repeatedly blocks bad cubes at the top frame `F[k]` until `F[k] ∧ bad` is
    /// `unsat` (all blocked) or a real predecessor chain reaches `F[0]`.
    fn block_bad_states(&mut self, arena: &mut TermArena) -> Result<BlockResult, SolverError> {
        let mut obligations_processed = 0usize;
        loop {
            if self.timed_out() {
                return Ok(BlockResult::Decline("PDR timed out in block".to_owned()));
            }
            // Is there a bad state in F[k]?
            let k = self.k();
            let Some(bad_cube) = self.bad_cube_in_frame(arena, k)? else {
                return Ok(BlockResult::Blocked);
            };
            // Recursively block (bad_cube, k).
            match self.block_obligation(arena, bad_cube, k, &mut obligations_processed)? {
                BlockResult::Blocked => {}
                other => return Ok(other),
            }
        }
    }

    /// Tries to block proof obligation `(cube, level)`: ensure `cube` is
    /// unreachable in `≤ level` steps. Recurses on predecessors. A simple explicit
    /// work-stack (rather than recursion) keeps the depth bounded and panic-free.
    fn block_obligation(
        &mut self,
        arena: &mut TermArena,
        cube: Cube,
        level: usize,
        processed: &mut usize,
    ) -> Result<BlockResult, SolverError> {
        // Work stack of (cube, level) obligations, lowest-level-first by repeated
        // push of predecessors.
        let mut stack = vec![(cube, level)];
        while let Some((cube, level)) = stack.pop() {
            *processed += 1;
            if *processed > self.limits.max_obligations {
                return Ok(BlockResult::Decline(
                    "PDR exceeded the proof-obligation budget".to_owned(),
                ));
            }
            if self.timed_out() {
                return Ok(BlockResult::Decline("PDR timed out in block".to_owned()));
            }

            if level == 0 {
                // A cube at level 0 that intersects init is a genuine cex seed.
                if self.cube_intersects_init(arena, &cube)? {
                    return Ok(BlockResult::Cex);
                }
                // Otherwise it cannot start at init; nothing to block at level 0.
                continue;
            }

            // Relative inductiveness: is F[level-1] ∧ ¬cube ∧ trans ∧ cube' SAT?
            match self.relative_inductive_predecessor(arena, &cube, level)? {
                RelInd::Blockable => {
                    let lemma = self.generalize(arena, &cube, level)?;
                    self.add_lemma(&lemma, level);
                }
                RelInd::Predecessor(pred) => {
                    // Re-queue the current obligation (must still be blocked) after
                    // its predecessor at level-1 is handled.
                    stack.push((cube, level));
                    stack.push((pred, level - 1));
                }
                RelInd::Decline(reason) => return Ok(BlockResult::Decline(reason)),
            }
        }
        Ok(BlockResult::Blocked)
    }

    /// Finds a state in `F[level] ∧ bad`, returned as a cube over the state vars,
    /// or `None` if `F[level] ∧ bad` is `unsat`.
    fn bad_cube_in_frame(
        &mut self,
        arena: &mut TermArena,
        level: usize,
    ) -> Result<Option<Cube>, SolverError> {
        let frame_term = self.frame_term(arena, level)?;
        let bad = self.system.bad(arena, &self.s.clone())?;
        match self.solve_one_shot(arena, &[frame_term, bad])? {
            SolveOutcome::Sat(model) => Ok(Some(Cube::from_model(&model, &self.s.clone()))),
            // No bad state in the frame; on an undecided query, conservatively
            // report none (the outer loop then attempts a frame push / fixpoint —
            // any missed bad state is still caught by the final trusted verify).
            SolveOutcome::Unsat | SolveOutcome::Unknown(_) => Ok(None),
        }
    }

    /// Relative-inductiveness query for blocking `(cube, level)`:
    /// `F[level-1] ∧ ¬cube ∧ trans(s, s') ∧ cube'`.
    ///
    /// * `unsat` ⇒ blockable at `level`.
    /// * `sat` ⇒ extract the **predecessor** state (the pre-state assignment) to
    ///   block at `level-1`.
    fn relative_inductive_predecessor(
        &mut self,
        arena: &mut TermArena,
        cube: &Cube,
        level: usize,
    ) -> Result<RelInd, SolverError> {
        let s = self.s.clone();
        let sp = self.sp.clone();
        let frame_prev = self.frame_term(arena, level - 1)?;
        let not_cube = cube.to_clause_term(arena, &s, &s)?;
        let cube_primed = cube.to_term(arena, &s, &sp)?;
        let trans = self.system.trans(arena, &s, &sp)?;
        match self.solve_one_shot(arena, &[frame_prev, not_cube, trans, cube_primed])? {
            SolveOutcome::Unsat => Ok(RelInd::Blockable),
            SolveOutcome::Sat(model) => {
                // Project the model onto the *pre*-state variables — the predecessor.
                let pred = Cube::from_model(&model, &s);
                Ok(RelInd::Predecessor(pred))
            }
            SolveOutcome::Unknown(reason) => Ok(RelInd::Decline(format!(
                "PDR relative-inductiveness query undecided: {reason}"
            ))),
        }
    }

    /// Inductive generalization: greedily drop literals from `cube` while the
    /// generalized clause `¬cube` stays relatively inductive at `level`
    /// (`F[level-1] ∧ ¬cube ∧ trans ∧ cube'` remains `unsat`). A smaller cube
    /// negates to a stronger (more general) blocking clause. Soundness is
    /// unaffected by this heuristic: any clause we add is independently
    /// re-validated by the final 3-query check before `Safe`.
    fn generalize(
        &mut self,
        arena: &mut TermArena,
        cube: &Cube,
        level: usize,
    ) -> Result<Cube, SolverError> {
        let mut lits = cube.lits.clone();
        let mut i = 0;
        while i < lits.len() {
            if self.timed_out() || lits.len() <= 1 {
                break;
            }
            // Try dropping literal i.
            let mut candidate = lits.clone();
            candidate.remove(i);
            let trial = Cube {
                lits: candidate.clone(),
            };
            // The dropped clause must (a) still exclude every init state and (b)
            // stay relatively inductive. Check both; if both hold, keep the drop.
            let init_ok = !self.cube_intersects_init(arena, &trial)?;
            let still_inductive = if init_ok {
                matches!(
                    self.relative_inductive_predecessor(arena, &trial, level)?,
                    RelInd::Blockable
                )
            } else {
                false
            };
            if init_ok && still_inductive {
                lits = candidate;
                // Do not advance i: the next literal shifted into this slot.
            } else {
                i += 1;
            }
        }
        Ok(Cube { lits })
    }

    /// Adds lemma `cube` (blocking clause `¬cube`) to every frame `F[1..=level]`
    /// (`IC3` keeps clauses in all lower frames too), deduplicating.
    fn add_lemma(&mut self, cube: &Lemma, level: usize) {
        let upto = level.min(self.frames.len());
        for frame in self.frames.iter_mut().take(upto) {
            if !frame.contains(cube) {
                frame.push(cube.clone());
            }
        }
    }

    /// Propagates lemmas forward: for each frame `i` and each lemma in `F[i]`, if
    /// `F[i] ∧ trans ⇒ clause'` (i.e. `F[i] ∧ trans ∧ ¬clause'` is `unsat`), add it
    /// to `F[i+1]`. If after propagation some `F[i] == F[i+1]` (equal lemma sets),
    /// a fixpoint is reached and `F[i]` is the invariant frame.
    fn propagate(&mut self, arena: &mut TermArena) -> Result<PropagateResult, SolverError> {
        let top = self.frames.len();
        // frames index 0 == F[1]; iterate F[1..k] pushing into F[i+1].
        for i in 1..top {
            if self.timed_out() {
                return Ok(PropagateResult::Decline(
                    "PDR timed out in propagate".to_owned(),
                ));
            }
            // Snapshot of F[i] lemmas (index i-1 in `frames`).
            let lemmas = self.frames[i - 1].clone();
            for lemma in lemmas {
                if self.timed_out() {
                    return Ok(PropagateResult::Decline(
                        "PDR timed out in propagate".to_owned(),
                    ));
                }
                match self.clause_pushes_forward(arena, &lemma, i)? {
                    Some(true) => {
                        // clause holds at F[i+1]; add it there (frames index i).
                        if !self.frames[i].contains(&lemma) {
                            self.frames[i].push(lemma.clone());
                        }
                    }
                    Some(false) => {}
                    None => {
                        return Ok(PropagateResult::Decline(
                            "PDR propagation query undecided".to_owned(),
                        ));
                    }
                }
            }
            // Fixpoint: F[i] ⊆ F[i+1] AND F[i+1] ⊆ F[i] (equal sets).
            if frames_equal(&self.frames[i - 1], &self.frames[i]) {
                return Ok(PropagateResult::Fixpoint(i));
            }
        }
        Ok(PropagateResult::Continue)
    }

    /// Does lemma `¬cube` push from `F[level]` to `F[level+1]`? Decides
    /// `F[level] ∧ trans ∧ cube'` (the negation of `clause'`): `unsat` ⇒ yes.
    /// Returns `None` if undecided.
    fn clause_pushes_forward(
        &mut self,
        arena: &mut TermArena,
        cube: &Cube,
        level: usize,
    ) -> Result<Option<bool>, SolverError> {
        let s = self.s.clone();
        let sp = self.sp.clone();
        let frame = self.frame_term(arena, level)?;
        let trans = self.system.trans(arena, &s, &sp)?;
        let cube_primed = cube.to_term(arena, &s, &sp)?;
        match self.solve_one_shot(arena, &[frame, trans, cube_primed])? {
            SolveOutcome::Unsat => Ok(Some(true)),
            SolveOutcome::Sat(_) => Ok(Some(false)),
            SolveOutcome::Unknown(_) => Ok(None),
        }
    }

    /// The conjunction defining frame `F[level]` over the **unprimed** state vars:
    /// `init ∧ ⋀ lemmas` for `level == 0` is just `init`; for `level >= 1` it is
    /// `⋀ (lemma clauses in F[level])`. (`F[i] ⊇ init` is implicit: every lemma was
    /// validated to exclude init, and the final invariant is checked against init
    /// explicitly.) For `level == 0` the frame is exactly `init`.
    fn frame_term(&mut self, arena: &mut TermArena, level: usize) -> Result<TermId, SolverError> {
        let s = self.s.clone();
        if level == 0 {
            return self.system.init(arena, &s);
        }
        // Conjoin all lemma clauses at this frame (index level-1).
        let lemmas = self.frames[level - 1].clone();
        let mut acc: Option<TermId> = None;
        for lemma in &lemmas {
            let clause = lemma.to_clause_term(arena, &s, &s)?;
            acc = Some(match acc {
                None => clause,
                Some(prev) => arena.and(prev, clause)?,
            });
        }
        match acc {
            Some(term) => Ok(term),
            None => Ok(arena.bool_const(true)),
        }
    }

    /// Is `cube` consistent with `init`? Decides `init(s) ∧ cube(s)`; `sat` ⇒ yes.
    /// On an undecided result, conservatively returns `true` (treats the cube as
    /// possibly-initial), which can only *prevent* a drop/block — never unsound.
    fn cube_intersects_init(
        &mut self,
        arena: &mut TermArena,
        cube: &Cube,
    ) -> Result<bool, SolverError> {
        let s = self.s.clone();
        let init = self.system.init(arena, &s)?;
        let cube_term = cube.to_term(arena, &s, &s)?;
        match self.solve_one_shot(arena, &[init, cube_term])? {
            SolveOutcome::Unsat => Ok(false),
            // Sat ⇒ intersects init; Unknown ⇒ conservatively assume it might
            // (which can only prevent a literal drop / block — never unsound).
            SolveOutcome::Sat(_) | SolveOutcome::Unknown(_) => Ok(true),
        }
    }

    /// Converges on a candidate invariant from frame `frame_index` (the converged
    /// frame), then runs the **mandatory** 3-query verification before returning
    /// `Safe`. A failed verification declines to `Unknown` (the search found a
    /// non-inductive candidate — a sound decline, never a wrong `Safe`).
    fn finish_with_invariant(
        &mut self,
        arena: &mut TermArena,
        frame_index: usize,
    ) -> Result<PdrOutcome, SolverError> {
        let s = self.s.clone();
        // Invariant = ⋀ lemma clauses at the converged frame, over step-0 vars.
        let lemmas = self.frames[frame_index - 1].clone();
        let mut acc: Option<TermId> = None;
        for lemma in &lemmas {
            let clause = lemma.to_clause_term(arena, &s, &s)?;
            acc = Some(match acc {
                None => clause,
                Some(prev) => arena.and(prev, clause)?,
            });
        }
        // An empty invariant (`true`) cannot exclude any bad state unless `bad` is
        // itself unsat — the 3-query check below handles that correctly either way.
        let invariant = match acc {
            Some(term) => term,
            None => arena.bool_const(true),
        };
        verify_invariant(arena, self.system, invariant, &self.config)
    }

    /// Confirms a believed counterexample via BMC — the only trusted route to a
    /// `Reachable` verdict. Searches up to a generous depth bounded by frame count;
    /// if BMC does not confirm, declines to `Unknown`.
    fn confirm_cex(&mut self, arena: &mut TermArena) -> Result<PdrOutcome, SolverError> {
        // Search depth: at least the current frame depth, capped.
        let depth = self.k().max(1).min(self.limits.max_frames);
        match bounded_model_check(arena, self.system, depth, &self.config)? {
            BmcOutcome::Reachable { steps, model } => Ok(PdrOutcome::Reachable { steps, model }),
            BmcOutcome::UnreachableWithinBound { bound } => Ok(unknown(&format!(
                "PDR believed a counterexample exists, but BMC found none within depth {bound} \
                 (declining rather than reporting an unconfirmed Reachable)"
            ))),
            BmcOutcome::Unknown { steps, reason } => Ok(unknown(&format!(
                "PDR counterexample confirmation undecided at BMC depth {steps}: {}",
                reason.detail
            ))),
        }
    }

    /// One-shot trusted-ish decision of a conjunction via the warm BV solver, used
    /// for the **untrusted** inner `IC3` queries. (The trusted final verification
    /// uses [`check_auto`] separately.) `Unsupported` degrades to `Unknown`.
    fn solve_one_shot(
        &self,
        arena: &TermArena,
        assertions: &[TermId],
    ) -> Result<SolveOutcome, SolverError> {
        let mut solver = IncrementalBvSolver::with_config(self.config.clone());
        for &term in assertions {
            match solver.assert(arena, term) {
                Ok(()) => {}
                Err(SolverError::Unsupported(detail)) => {
                    return Ok(SolveOutcome::Unknown(detail));
                }
                Err(other) => return Err(other),
            }
        }
        match solver.check(arena) {
            Ok(CheckResult::Sat(model)) => Ok(SolveOutcome::Sat(model)),
            Ok(CheckResult::Unsat) => Ok(SolveOutcome::Unsat),
            Ok(CheckResult::Unknown(reason)) => Ok(SolveOutcome::Unknown(reason.detail)),
            Err(SolverError::Unsupported(detail)) => Ok(SolveOutcome::Unknown(detail)),
            Err(other) => Err(other),
        }
    }
}

/// The **trusted soundness gate**: a candidate `invariant` is accepted as proving
/// safety only if it passes all three classical inductive-invariant checks, each
/// decided independently by [`check_auto`](crate::check_auto) returning `Unsat`.
///
/// 1. Initiation: `init(s) ∧ ¬Inv(s)` `unsat`.
/// 2. Consecution: `Inv(s) ∧ trans(s, s') ∧ ¬Inv(s')` `unsat`.
/// 3. Safety: `Inv(s) ∧ bad(s)` `unsat`.
///
/// Any non-`Unsat` (sat / unknown / error) on any check ⇒ decline to `Unknown`.
/// This makes the entire `IC3` search untrusted: a search bug can only cause a
/// decline, never a wrong `Safe`.
fn verify_invariant(
    arena: &mut TermArena,
    system: &impl TransitionSystem,
    invariant: TermId,
    config: &SolverConfig,
) -> Result<PdrOutcome, SolverError> {
    let s = system.state_vars(arena, 0)?;
    let sp = system.state_vars(arena, 1)?;

    // 1. Initiation: init(s) ∧ ¬Inv(s) must be UNSAT.
    let init = system.init(arena, &s)?;
    let not_inv = arena.not(invariant)?;
    if !is_unsat(arena, &[init, not_inv], config)? {
        return Ok(unknown(
            "discovered invariant failed the initiation check (init ⇒ Inv is not valid); \
             declining",
        ));
    }

    // 2. Consecution: Inv(s) ∧ trans(s, s') ∧ ¬Inv(s') must be UNSAT.
    let inv_primed = prime_invariant(arena, invariant, &s, &sp)?;
    let trans = system.trans(arena, &s, &sp)?;
    let not_inv_primed = arena.not(inv_primed)?;
    if !is_unsat(arena, &[invariant, trans, not_inv_primed], config)? {
        return Ok(unknown(
            "discovered invariant failed the consecution check (Inv is not transition-closed); \
             declining",
        ));
    }

    // 3. Safety: Inv(s) ∧ bad(s) must be UNSAT.
    let bad = system.bad(arena, &s)?;
    if !is_unsat(arena, &[invariant, bad], config)? {
        return Ok(unknown(
            "discovered invariant failed the safety check (Inv does not exclude bad); declining",
        ));
    }

    Ok(PdrOutcome::Safe { invariant })
}

/// Decides whether `assertions` is `unsat` under the **trusted**
/// [`check_auto`](crate::check_auto). Returns `true` only on `Unsat`; `Sat`,
/// `Unknown`, or any unsupported construct ⇒ `false` (a conservative decline, so
/// the caller never over-claims `Safe`).
fn is_unsat(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<bool, SolverError> {
    match check_auto(arena, assertions, config) {
        Ok(CheckResult::Unsat) => Ok(true),
        Ok(_) | Err(SolverError::Unsupported(_)) => Ok(false),
        Err(other) => Err(other),
    }
}

/// Rebuilds the invariant term over the **primed** state variables `sp` by
/// structural variable substitution `s[i] ↦ sp[i]`. The invariant is a conjunction
/// of cube-clauses over the unprimed state vars; the consecution check needs the
/// same predicate over the primed copy, which this produces.
fn prime_invariant(
    arena: &mut TermArena,
    invariant: TermId,
    s: &[SymbolId],
    sp: &[SymbolId],
) -> Result<TermId, SolverError> {
    let mut mapping: Vec<(SymbolId, SymbolId)> =
        s.iter().copied().zip(sp.iter().copied()).collect();
    mapping.sort_by_key(|&(from, _)| from);
    substitute_symbols(arena, invariant, &mapping)
}

/// Substitutes state-variable symbols in `term` per `mapping` (sorted by source
/// symbol), rebuilding the term over the target symbols. Used to express an
/// unprimed invariant over the primed copy for the consecution check.
fn substitute_symbols(
    arena: &mut TermArena,
    term: TermId,
    mapping: &[(SymbolId, SymbolId)],
) -> Result<TermId, SolverError> {
    use axeyum_ir::TermNode;
    match arena.node(term).clone() {
        TermNode::App { args, .. } => {
            let mut new_args = Vec::with_capacity(args.len());
            for &arg in &args {
                new_args.push(substitute_symbols(arena, arg, mapping)?);
            }
            Ok(arena.rebuild_with_args(term, &new_args))
        }
        TermNode::Symbol(sym) => {
            let replacement = mapping
                .binary_search_by_key(&sym, |&(from, _)| from)
                .ok()
                .map(|i| mapping[i].1);
            match replacement {
                Some(target) => Ok(arena.var(target)),
                None => Ok(term),
            }
        }
        _ => Ok(term),
    }
}

/// A concrete constant term for a state-variable value.
fn value_const(arena: &mut TermArena, value: &Value) -> Result<TermId, SolverError> {
    match value {
        Value::Bv { width, value } => Ok(arena.bv_const(*width, *value)?),
        Value::Bool(b) => Ok(arena.bool_const(*b)),
        other => Err(SolverError::Unsupported(format!(
            "PDR cube literal value {other:?} is not a Bool/BitVec"
        ))),
    }
}

/// Two frames are equal iff they hold the same lemma set (order-independent).
fn frames_equal(a: &[Lemma], b: &[Lemma]) -> bool {
    a.len() == b.len() && a.iter().all(|lemma| b.contains(lemma))
}

fn unknown(reason: &str) -> PdrOutcome {
    PdrOutcome::Unknown {
        reason: reason.to_owned(),
    }
}

/// Outcome of an inner one-shot solve.
enum SolveOutcome {
    Sat(Model),
    Unsat,
    Unknown(String),
}

/// Outcome of blocking all bad states at the top frame.
enum BlockResult {
    Blocked,
    Cex,
    Decline(String),
}

/// Outcome of a relative-inductiveness query while blocking an obligation.
enum RelInd {
    Blockable,
    Predecessor(Cube),
    Decline(String),
}

/// Outcome of forward propagation.
enum PropagateResult {
    Fixpoint(usize),
    Continue,
    Decline(String),
}
