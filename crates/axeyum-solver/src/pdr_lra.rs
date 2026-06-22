//! IC3/PDR (Spacer-style) inductive-invariant discovery over **linear real
//! arithmetic** (`LRA`) transition systems — the infinite-state analogue of the
//! `QF_BV` engine in [`pdr`](crate::pdr).
//!
//! Where [`prove_safety_pdr`](crate::prove_safety_pdr) discovers an inductive
//! invariant for finite (`QF_BV`/Bool) systems by learning relatively-inductive
//! blocking clauses over bit-equality cubes, [`prove_safety_pdr_lra`] does the
//! same for systems whose state variables are **`Real`**-sorted and whose
//! `init`/`trans`/`bad` are linear-real-arithmetic formulas. The structural
//! template (frames, the proof-obligation work-stack, relative-inductiveness
//! blocking, generalization, forward propagation, the fixpoint, and the trusted
//! 3-check gate) is exactly [`pdr`](crate::pdr); only the *cube* representation
//! and the *predecessor generalizer* differ:
//!
//! * A **cube** here is a conjunction of atomic `LRA` literals (a region of the
//!   real state space), not a conjunction of bit-equalities. A **lemma** is the
//!   negation of a cube — a disjunction of negated `LRA` literals (a blocking
//!   clause). Frames `F[0] = init`, `F[1..=k]` are sets of lemma clauses.
//! * The **predecessor cube** (the pre-states that can step into an obligation
//!   `c`) is generalized by **model-based projection**
//!   ([`mbp_lra`](crate::mbp_lra)): given the satisfying model `M` of
//!   `trans(s, s') ∧ c'`, project the next-state variables `s'` out of the
//!   conjunction `trans ∧ c'`, leaving a cube of `LRA` literals over `s` that
//!   `M` satisfies and that implies `∃s'. (trans ∧ c')` — exactly the Spacer
//!   predecessor generalization. (`mbp_lra` self-verifies every projection, so a
//!   bug there can only shrink coverage, never produce an unsound predecessor.)
//!
//! # The soundness contract (the whole point)
//!
//! The `IC3` search in this module is **untrusted**. Its frames, obligations,
//! cube extraction, `mbp_lra`-driven predecessor generalization, and lemma
//! generalization are all best-effort: a bug in any of them can only ever cause
//! an over-eager [`PdrLraOutcome::Unknown`], never a wrong
//! [`PdrLraOutcome::Safe`]. That guarantee is enforced by a *single* trusted gate,
//! [`verify_invariant`], run before any `Safe` is returned: the candidate
//! invariant `R` (the conjunction of a converged frame's lemma clauses) must pass
//! all three classical inductive-invariant checks, each decided independently by
//! the trusted decider [`check_auto`](crate::check_auto) returning `Unsat`:
//!
//! 1. **Initiation** — `init(s) ∧ ¬R(s)` is `unsat`.
//! 2. **Consecution** — `R(s) ∧ trans(s, s') ∧ ¬R(s')` is `unsat`.
//! 3. **Safety** — `R(s) ∧ bad(s)` is `unsat`.
//!
//! Any non-`Unsat` (sat / unknown / unsupported / error) on any check ⇒ decline to
//! [`PdrLraOutcome::Unknown`]. A [`PdrLraOutcome::Reachable`] is likewise gated: the
//! search may *believe* it found a counterexample, but the result is confirmed
//! only by [`confirm_cex`](PdrLraEngine::confirm_cex), an inline `LRA` k-unrolling
//! `init(s0) ∧ trans(s0,s1) ∧ … ∧ bad(s_i)` decided `Sat` by
//! [`check_auto`](crate::check_auto) (the model is replay-checked). A non-`LRA`
//! system (e.g. `BV` state variables) degrades gracefully: the inner queries and
//! `mbp_lra` decline and the engine reports `Unknown`, never a panic.
//!
//! Every resource cap (`max_frames`, proof obligations, iterations,
//! `config.timeout`) degrades to `Unknown`; the engine never hangs and never
//! panics on adversarial input.

use std::time::Instant;

use axeyum_ir::{Op, SymbolId, TermArena, TermId, TermNode};

use crate::auto::check_auto;
use crate::backend::{CheckResult, SolverConfig, SolverError};
use crate::bmc::TransitionSystem;
use crate::mbp::mbp_lra;
use crate::model::Model;

/// Resource caps for the `LRA` `IC3`/`PDR` search. All degrade to
/// [`PdrLraOutcome::Unknown`]; none can cause a wrong verdict.
#[derive(Debug, Clone)]
#[allow(clippy::struct_field_names)]
struct PdrLraLimits {
    /// Maximum number of frames `F[0..=max_frames]` before declining.
    max_frames: usize,
    /// Maximum proof obligations processed per `block` call.
    max_obligations: usize,
    /// Maximum top-level outer iterations (one per new frame attempt).
    max_iterations: usize,
    /// Maximum number of unrolling steps explored by [`confirm_cex`].
    max_cex_depth: usize,
}

impl Default for PdrLraLimits {
    fn default() -> Self {
        Self {
            max_frames: 32,
            max_obligations: 20_000,
            max_iterations: 1024,
            max_cex_depth: 64,
        }
    }
}

/// The result of [`prove_safety_pdr_lra`].
#[derive(Debug, Clone)]
pub enum PdrLraOutcome {
    /// The property holds in every reachable state, proven by the discovered
    /// inductive invariant `invariant` — a [`TermId`] (the conjunction of the
    /// converged frame's lemma clauses) over the step-0 state variables that
    /// **passed all three** independent implication checks (initiation,
    /// consecution, safety) under the trusted [`check_auto`](crate::check_auto)
    /// decider. This is an unbounded guarantee.
    Safe {
        /// The discovered inductive invariant `R(s)`, as a Boolean term over the
        /// step-0 state variables. Re-checkable: assert `init ∧ ¬R`,
        /// `R ∧ trans ∧ ¬R'`, and `R ∧ bad`; each must be `unsat`.
        invariant: TermId,
    },
    /// A bad state **is** reachable: `model` is a replay-checked counterexample at
    /// `steps` transitions, confirmed by an inline `LRA` k-unrolling decided `Sat`
    /// by [`check_auto`](crate::check_auto). The property is false.
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

/// A cube: a conjunction of atomic `LRA` literals (each a single inequality /
/// (dis)equality term over the canonical step-0 vocabulary `s`). Its negation is
/// a blocking clause (a lemma). Stored as the literal terms themselves so cube /
/// clause construction is a simple fold and literal-dropping during
/// generalization is a `Vec` removal.
#[derive(Debug, Clone)]
struct Cube {
    /// Atomic `LRA` literal terms, over the canonical step-0 vocabulary `s`.
    lits: Vec<TermId>,
}

impl Cube {
    /// The cube as a single Boolean term `⋀ lits` over `s`. An empty cube is
    /// `true`.
    fn to_term(&self, arena: &mut TermArena) -> Result<TermId, SolverError> {
        let mut acc: Option<TermId> = None;
        for &lit in &self.lits {
            acc = Some(match acc {
                None => lit,
                Some(prev) => arena.and(prev, lit)?,
            });
        }
        Ok(match acc {
            Some(term) => term,
            None => arena.bool_const(true),
        })
    }

    /// The blocking clause `¬cube = ⋁ ¬lits` over `s`.
    fn to_clause_term(&self, arena: &mut TermArena) -> Result<TermId, SolverError> {
        let cube = self.to_term(arena)?;
        Ok(arena.not(cube)?)
    }

    /// The cube over the **primed** vocabulary `sp` (each literal rebuilt with
    /// `s[i] ↦ sp[i]`).
    fn to_primed_term(
        &self,
        arena: &mut TermArena,
        s: &[SymbolId],
        sp: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let unprimed = self.to_term(arena)?;
        rename_symbols(arena, unprimed, s, sp)
    }
}

/// A learned lemma: a blocking clause, stored as the cube it negates (so literal
/// dropping during generalization is just cube-literal removal). Two lemmas are
/// "the same" when their literal term-id sets are equal.
type Lemma = Cube;

/// Proves a safety property (`bad` is *never* reachable) of a **linear-real**
/// transition system by **`IC3`/`PDR` (Spacer-style) inductive-invariant
/// discovery** — the infinite-state analogue of
/// [`prove_safety_pdr`](crate::prove_safety_pdr), and the method Z3's Spacer `CHC`
/// engine uses: model-based projection ([`mbp_lra`](crate::mbp_lra)) generalizes
/// predecessors during blocking.
///
/// The untrusted `IC3` search learns relatively-inductive blocking clauses across
/// a growing frame sequence until a frame converges (a fixpoint), then bundles
/// that frame's lemmas into a candidate invariant. **No `Safe` is returned until
/// that candidate passes all three independent implication checks** (initiation,
/// consecution, safety) under the trusted [`check_auto`](crate::check_auto)
/// decider; otherwise the engine declines to [`PdrLraOutcome::Unknown`]. A
/// [`PdrLraOutcome::Reachable`] is confirmed by an inline `LRA` k-unrolling decided
/// `Sat` by [`check_auto`](crate::check_auto) (the model is replay-checked).
///
/// Coverage is partial by design (the cube/predecessor machinery only handles the
/// `LRA` fragment `mbp_lra` and `check_auto` decide); a non-`LRA` system or a
/// shape the search cannot close degrades to `Unknown`. Soundness is total: a
/// search bug can only cause an over-eager `Unknown`.
///
/// # Errors
///
/// Returns [`SolverError`] only for a genuine internal failure while building the
/// system's terms; a solver `timeout`/`unsupported`/unsupported-construct or a
/// failed invariant verification is reported as [`PdrLraOutcome::Unknown`], never
/// an error.
pub fn prove_safety_pdr_lra<S: TransitionSystem>(
    arena: &mut TermArena,
    system: &S,
    config: &SolverConfig,
) -> Result<PdrLraOutcome, SolverError> {
    let limits = PdrLraLimits::default();
    let mut engine = match PdrLraEngine::new(arena, system, config, limits) {
        Ok(engine) => engine,
        Err(EngineSetup::Unsupported(reason)) => return Ok(PdrLraOutcome::Unknown { reason }),
        Err(EngineSetup::Error(error)) => return Err(error),
    };
    engine.run(arena)
}

/// Setup failures for [`PdrLraEngine::new`]: an unsupported construct degrades to
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

/// The `LRA` `IC3`/`PDR` engine over a fixed transition system. Frames are sets of
/// lemmas (blocking clauses, stored as the cubes they negate); `F[0]` is `init`.
struct PdrLraEngine<'sys, S: TransitionSystem> {
    system: &'sys S,
    config: SolverConfig,
    limits: PdrLraLimits,
    deadline: Option<Instant>,
    /// The canonical step-0 state-variable symbols (the "unprimed" copy).
    s: Vec<SymbolId>,
    /// The canonical step-1 state-variable symbols (the "primed" copy).
    sp: Vec<SymbolId>,
    /// `F[i]` for `i >= 1` is the set of lemmas at frame `i`; `F[0]` is `init`,
    /// handled specially. Index 0 of this vector corresponds to `F[1]`.
    frames: Vec<Vec<Lemma>>,
}

impl<'sys, S: TransitionSystem> PdrLraEngine<'sys, S> {
    fn new(
        arena: &mut TermArena,
        system: &'sys S,
        config: &SolverConfig,
        limits: PdrLraLimits,
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

    /// The current top frame index `k` (`F[k]` is the deepest frame).
    fn k(&self) -> usize {
        self.frames.len()
    }

    /// Drives the `IC3` loop. See the module docs for the soundness gate.
    fn run(&mut self, arena: &mut TermArena) -> Result<PdrLraOutcome, SolverError> {
        // A bad initial state is a length-0 counterexample; confirm via unrolling.
        match self.init_is_bad(arena)? {
            Decision::Sat => return self.confirm_cex(arena),
            Decision::Unknown(detail) => {
                return Ok(unknown(&format!(
                    "LRA PDR init-safety check undecided: {detail}"
                )));
            }
            Decision::Unsat => {}
        }

        // F[0] = init. Start with one empty learned frame F[1].
        self.frames.push(Vec::new());

        for _iteration in 0..self.limits.max_iterations {
            if self.timed_out() {
                return Ok(unknown("LRA PDR timed out"));
            }
            if self.k() > self.limits.max_frames {
                return Ok(unknown("LRA PDR exceeded the maximum frame count"));
            }

            // 1. Block all bad states at the top frame F[k].
            match self.block_bad_states(arena)? {
                BlockResult::Blocked => {}
                BlockResult::Cex => return self.confirm_cex(arena),
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

        Ok(unknown("LRA PDR exceeded the maximum iteration count"))
    }

    /// Repeatedly blocks bad cubes at the top frame `F[k]` until `F[k] ∧ bad` is
    /// `unsat` (all blocked) or a real predecessor chain reaches `F[0]`.
    fn block_bad_states(&mut self, arena: &mut TermArena) -> Result<BlockResult, SolverError> {
        let mut obligations_processed = 0usize;
        loop {
            if self.timed_out() {
                return Ok(BlockResult::Decline(
                    "LRA PDR timed out in block".to_owned(),
                ));
            }
            let k = self.k();
            let Some(bad_cube) = self.bad_cube_in_frame(arena, k)? else {
                return Ok(BlockResult::Blocked);
            };
            match self.block_obligation(arena, bad_cube, k, &mut obligations_processed)? {
                BlockResult::Blocked => {}
                other => return Ok(other),
            }
        }
    }

    /// Tries to block proof obligation `(cube, level)` via an explicit work-stack
    /// (bounded, panic-free): ensure `cube` is unreachable in `≤ level` steps,
    /// recursing on `mbp_lra`-generalized predecessors.
    fn block_obligation(
        &mut self,
        arena: &mut TermArena,
        cube: Cube,
        level: usize,
        processed: &mut usize,
    ) -> Result<BlockResult, SolverError> {
        let mut stack = vec![(cube, level)];
        while let Some((cube, level)) = stack.pop() {
            *processed += 1;
            if *processed > self.limits.max_obligations {
                return Ok(BlockResult::Decline(
                    "LRA PDR exceeded the proof-obligation budget".to_owned(),
                ));
            }
            if self.timed_out() {
                return Ok(BlockResult::Decline(
                    "LRA PDR timed out in block".to_owned(),
                ));
            }

            if level == 0 {
                // A cube at level 0 that intersects init is a genuine cex seed.
                if self.cube_intersects_init(arena, &cube)? {
                    return Ok(BlockResult::Cex);
                }
                continue;
            }

            match self.relative_inductive_predecessor(arena, &cube, level)? {
                RelInd::Blockable => {
                    let lemma = self.generalize(arena, &cube, level)?;
                    self.add_lemma(arena, &lemma, level)?;
                }
                RelInd::Predecessor(pred) => {
                    // Re-queue the current obligation after its predecessor at
                    // level-1 is handled.
                    stack.push((cube, level));
                    stack.push((pred, level - 1));
                }
                RelInd::UnprojectablePredecessor => return Ok(BlockResult::Cex),
                RelInd::Decline(reason) => return Ok(BlockResult::Decline(reason)),
            }
        }
        Ok(BlockResult::Blocked)
    }

    /// Finds a state in `F[level] ∧ bad`, returned as a cube of the `bad`-defining
    /// atomic `LRA` literals true at the witnessing model, or `None` if
    /// `F[level] ∧ bad` is `unsat` (or undecided — conservatively reported as
    /// none; any missed bad state is still caught by the final trusted verify).
    fn bad_cube_in_frame(
        &mut self,
        arena: &mut TermArena,
        level: usize,
    ) -> Result<Option<Cube>, SolverError> {
        let frame_term = self.frame_term(arena, level)?;
        let bad = self.system.bad(arena, &self.s.clone())?;
        match self.solve(arena, &[frame_term, bad])? {
            Decision::Sat => {
                // Re-solve to recover the model (decide returns no model);
                // build the bad cube from the bad-defining literals true at M.
                let Some(model) = self.model_of(arena, &[frame_term, bad])? else {
                    return Ok(None);
                };
                let cube = literals_true_at(arena, bad, &model);
                // A bad cube must be non-empty to make progress; if no atomic LRA
                // literal could be extracted, report none (the final verify still
                // catches an unblocked bad state).
                if cube.lits.is_empty() {
                    Ok(None)
                } else {
                    Ok(Some(cube))
                }
            }
            Decision::Unsat | Decision::Unknown(_) => Ok(None),
        }
    }

    /// Relative-inductiveness query for blocking `(cube, level)`:
    /// `F[level-1] ∧ ¬cube ∧ trans(s, s') ∧ cube'`.
    ///
    /// * `unsat` ⇒ blockable at `level`.
    /// * `sat` ⇒ extract the **predecessor** cube by **model-based projection**:
    ///   project the next-state vars `s'` out of `trans(s, s') ∧ cube'` at the
    ///   witnessing model `M` (via [`mbp_lra`]), yielding a cube over `s`.
    fn relative_inductive_predecessor(
        &mut self,
        arena: &mut TermArena,
        cube: &Cube,
        level: usize,
    ) -> Result<RelInd, SolverError> {
        let frame_prev = self.frame_term(arena, level - 1)?;
        let not_cube = cube.to_clause_term(arena)?;
        let cube_primed = cube.to_primed_term(arena, &self.s.clone(), &self.sp.clone())?;
        let trans = self
            .system
            .trans(arena, &self.s.clone(), &self.sp.clone())?;
        match self.solve(arena, &[frame_prev, not_cube, trans, cube_primed])? {
            Decision::Unsat => Ok(RelInd::Blockable),
            Decision::Sat => {
                let Some(model) =
                    self.model_of(arena, &[frame_prev, not_cube, trans, cube_primed])?
                else {
                    return Ok(RelInd::Decline(
                        "LRA PDR could not recover a predecessor model".to_owned(),
                    ));
                };
                match self.predecessor_cube(arena, cube, &model)? {
                    Some(pred) => Ok(RelInd::Predecessor(pred)),
                    // `mbp_lra` declined to generalize the predecessor, but a
                    // predecessor genuinely exists (the relative-inductiveness
                    // query was SAT). Rather than abandon the obligation, route to
                    // the trusted `confirm_cex` unrolling: it confirms a real
                    // `Reachable` or declines to `Unknown` — never an unsound
                    // verdict. (A spurious belief here only costs an `Unknown`.)
                    None => Ok(RelInd::UnprojectablePredecessor),
                }
            }
            Decision::Unknown(reason) => Ok(RelInd::Decline(format!(
                "LRA PDR relative-inductiveness query undecided: {reason}"
            ))),
        }
    }

    /// The **`mbp_lra` predecessor generalizer**. Builds the conjunction
    /// `trans(s, s') ∧ cube'` as a flat list of atomic `LRA` literals (all true at
    /// `model`), then projects out **every** next-state variable `sp[i]` one at a
    /// time via [`mbp_lra`]. The result is a cube of `LRA` literals over `s` (the
    /// remaining vocabulary) that `model` satisfies and that implies
    /// `∃s'. (trans ∧ cube')` — the pre-states that can step into `cube`. Returns
    /// `None` (decline) if the conjunction is not flattenable to `LRA` literals or
    /// any projection step declines.
    fn predecessor_cube(
        &mut self,
        arena: &mut TermArena,
        cube: &Cube,
        model: &Model,
    ) -> Result<Option<Cube>, SolverError> {
        // Conjunction whose s'-projection is the predecessor: trans ∧ cube'.
        let trans = self
            .system
            .trans(arena, &self.s.clone(), &self.sp.clone())?;
        let cube_primed = cube.to_primed_term(arena, &self.s.clone(), &self.sp.clone())?;

        // Flatten both into atomic LRA literals. A non-LRA shape declines.
        let mut literals = Vec::new();
        if !flatten_conjuncts(arena, trans, &mut literals)
            || !flatten_conjuncts(arena, cube_primed, &mut literals)
        {
            return Ok(None);
        }

        // Project out each next-state variable sp[i] in turn. After each
        // projection the variable is gone, so the conjunction shrinks vocabulary
        // toward s only.
        let mut current = literals;
        for &var in &self.sp.clone() {
            match mbp_lra(arena, &current, model, var) {
                Some(projected) => current = projected,
                None => return Ok(None),
            }
        }

        // Defensive: drop any literal still mentioning a primed var (mbp_lra
        // guarantees absence of the projected var, but be conservative if the
        // system shares variables across copies).
        let sp = self.sp.clone();
        current.retain(|&lit| !sp.iter().any(|&v| term_mentions(arena, lit, v)));

        Ok(Some(Cube { lits: current }))
    }

    /// Inductive generalization: greedily drop literals from `cube` while the
    /// generalized clause `¬cube` stays relatively inductive at `level` and still
    /// excludes every init state. A smaller cube negates to a stronger (more
    /// general) blocking clause. Soundness is unaffected: any clause added is
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
            let mut candidate = lits.clone();
            candidate.remove(i);
            let trial = Cube {
                lits: candidate.clone(),
            };
            // The dropped clause must (a) still exclude every init state and (b)
            // stay relatively inductive. Check both; if both hold, keep the drop.
            let init_ok = !self.cube_intersects_init(arena, &trial)?;
            let still_inductive = init_ok
                && matches!(
                    self.relative_inductive_predecessor(arena, &trial, level)?,
                    RelInd::Blockable
                );
            if init_ok && still_inductive {
                lits = candidate;
            } else {
                i += 1;
            }
        }
        Ok(Cube { lits })
    }

    /// Adds lemma `cube` (blocking clause `¬cube`) to every frame `F[1..=level]`,
    /// deduplicating by literal-set equality. The lemma must exclude init (it was
    /// validated to during blocking/generalization); we re-confirm it cheaply and
    /// skip adding a lemma that would wrongly exclude an initial state (which can
    /// only happen on an undecided inner query — a sound, conservative skip).
    fn add_lemma(
        &mut self,
        arena: &mut TermArena,
        cube: &Lemma,
        level: usize,
    ) -> Result<(), SolverError> {
        // Guard: never add a lemma whose clause excludes an init state.
        if self.cube_intersects_init(arena, cube)? {
            return Ok(());
        }
        let upto = level.min(self.frames.len());
        for frame in self.frames.iter_mut().take(upto) {
            if !frame.iter().any(|existing| lemmas_equal(existing, cube)) {
                frame.push(cube.clone());
            }
        }
        Ok(())
    }

    /// Propagates lemmas forward: for each frame `i` and each lemma in `F[i]`, if
    /// `F[i] ∧ trans ⇒ clause'` (`F[i] ∧ trans ∧ cube'` is `unsat`), add it to
    /// `F[i+1]`. If after propagation some `F[i] == F[i+1]` (equal lemma sets), a
    /// fixpoint is reached and `F[i]` is the invariant frame.
    fn propagate(&mut self, arena: &mut TermArena) -> Result<PropagateResult, SolverError> {
        let top = self.frames.len();
        for i in 1..top {
            if self.timed_out() {
                return Ok(PropagateResult::Decline(
                    "LRA PDR timed out in propagate".to_owned(),
                ));
            }
            let lemmas = self.frames[i - 1].clone();
            for lemma in lemmas {
                if self.timed_out() {
                    return Ok(PropagateResult::Decline(
                        "LRA PDR timed out in propagate".to_owned(),
                    ));
                }
                match self.clause_pushes_forward(arena, &lemma, i)? {
                    Some(true) => {
                        if !self.frames[i]
                            .iter()
                            .any(|existing| lemmas_equal(existing, &lemma))
                        {
                            self.frames[i].push(lemma.clone());
                        }
                    }
                    Some(false) => {}
                    None => {
                        return Ok(PropagateResult::Decline(
                            "LRA PDR propagation query undecided".to_owned(),
                        ));
                    }
                }
            }
            if frames_equal(&self.frames[i - 1], &self.frames[i]) {
                return Ok(PropagateResult::Fixpoint(i));
            }
        }
        Ok(PropagateResult::Continue)
    }

    /// Does lemma `¬cube` push from `F[level]` to `F[level+1]`? Decides
    /// `F[level] ∧ trans ∧ cube'`: `unsat` ⇒ yes. Returns `None` if undecided.
    fn clause_pushes_forward(
        &mut self,
        arena: &mut TermArena,
        cube: &Cube,
        level: usize,
    ) -> Result<Option<bool>, SolverError> {
        let frame = self.frame_term(arena, level)?;
        let trans = self
            .system
            .trans(arena, &self.s.clone(), &self.sp.clone())?;
        let cube_primed = cube.to_primed_term(arena, &self.s.clone(), &self.sp.clone())?;
        match self.solve(arena, &[frame, trans, cube_primed])? {
            Decision::Unsat => Ok(Some(true)),
            Decision::Sat => Ok(Some(false)),
            Decision::Unknown(_) => Ok(None),
        }
    }

    /// The conjunction defining frame `F[level]` over the **unprimed** state vars:
    /// `init` for `level == 0`; otherwise `⋀ (lemma clauses in F[level])`. (`F[i]`
    /// implicitly contains `init`: every lemma was validated to exclude init, and
    /// the final invariant is checked against init explicitly.)
    fn frame_term(&mut self, arena: &mut TermArena, level: usize) -> Result<TermId, SolverError> {
        if level == 0 {
            let s = self.s.clone();
            return self.system.init(arena, &s);
        }
        let lemmas = self.frames[level - 1].clone();
        conjoin_lemma_clauses(arena, &lemmas)
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
        let cube_term = cube.to_term(arena)?;
        match self.solve(arena, &[init, cube_term])? {
            Decision::Unsat => Ok(false),
            Decision::Sat | Decision::Unknown(_) => Ok(true),
        }
    }

    /// Converges on a candidate invariant from frame `frame_index`, then runs the
    /// **mandatory** 3-query verification before returning `Safe`. A failed
    /// verification declines to `Unknown` (a sound decline, never a wrong `Safe`).
    fn finish_with_invariant(
        &mut self,
        arena: &mut TermArena,
        frame_index: usize,
    ) -> Result<PdrLraOutcome, SolverError> {
        let lemmas = self.frames[frame_index - 1].clone();
        let invariant = conjoin_lemma_clauses(arena, &lemmas)?;
        verify_invariant(arena, self.system, invariant, &self.config)
    }

    /// Is `init(s)` itself bad? Decides `init(s) ∧ bad(s)`.
    fn init_is_bad(&mut self, arena: &mut TermArena) -> Result<Decision, SolverError> {
        let s = self.s.clone();
        let init = self.system.init(arena, &s)?;
        let bad = self.system.bad(arena, &s)?;
        self.solve(arena, &[init, bad])
    }

    /// Confirms a believed counterexample via an inline `LRA` k-unrolling — the
    /// only trusted route to a `Reachable` verdict. At each depth `i` it decides
    /// `init(s0) ∧ trans(s0,s1) ∧ … ∧ bad(s_i)` with [`check_auto`]; the first
    /// `Sat` is a replay-checked counterexample. If no depth up to the cap
    /// confirms, declines to `Unknown` (never reports an unconfirmed `Reachable`).
    fn confirm_cex(&mut self, arena: &mut TermArena) -> Result<PdrLraOutcome, SolverError> {
        // Search at least a generous floor (the cube chain that triggered the
        // belief may be shallower than the genuine path), bounded by the cap.
        let floor = self.limits.max_cex_depth.min(16);
        let depth = self.k().max(floor).min(self.limits.max_cex_depth);
        let mut states: Vec<Vec<SymbolId>> = vec![self.s.clone()];

        for i in 0..=depth {
            if self.timed_out() {
                return Ok(unknown(
                    "LRA PDR timed out confirming a believed counterexample",
                ));
            }
            if i > 0 {
                states.push(self.system.state_vars(arena, i)?);
            }

            // init(s0) ∧ trans(s0,s1) ∧ … ∧ trans(s_{i-1},s_i) ∧ bad(s_i).
            let mut assertions = vec![self.system.init(arena, &states[0])?];
            for window in states.windows(2) {
                assertions.push(self.system.trans(arena, &window[0], &window[1])?);
            }
            let bad_i = self.system.bad(arena, &states[i])?;
            assertions.push(bad_i);

            match check_auto(arena, &assertions, &self.config) {
                Ok(CheckResult::Sat(model)) => {
                    return Ok(PdrLraOutcome::Reachable { steps: i, model });
                }
                // Unsat / Unknown / unsupported at this depth: deepen the search.
                Ok(CheckResult::Unsat | CheckResult::Unknown(_))
                | Err(SolverError::Unsupported(_)) => {}
                Err(other) => return Err(other),
            }
        }

        Ok(unknown(
            "LRA PDR believed a counterexample exists, but no inline LRA unrolling up to the cap \
             confirmed one (declining rather than reporting an unconfirmed Reachable)",
        ))
    }

    /// Recovers a satisfying model of `assertions` via the **trusted**
    /// [`check_auto`] decider (the same decider that decided `Sat`); `None` on a
    /// non-`Sat` re-decision.
    fn model_of(
        &self,
        arena: &mut TermArena,
        assertions: &[TermId],
    ) -> Result<Option<Model>, SolverError> {
        match check_auto(arena, assertions, &self.config) {
            Ok(CheckResult::Sat(model)) => Ok(Some(model)),
            Ok(_) | Err(SolverError::Unsupported(_)) => Ok(None),
            Err(other) => Err(other),
        }
    }

    /// Decides a conjunction with the **trusted** [`check_auto`] decider, used for
    /// the inner `IC3` queries. `Unsupported` degrades to `Unknown`.
    fn solve(&self, arena: &mut TermArena, assertions: &[TermId]) -> Result<Decision, SolverError> {
        match check_auto(arena, assertions, &self.config) {
            Ok(CheckResult::Sat(_)) => Ok(Decision::Sat),
            Ok(CheckResult::Unsat) => Ok(Decision::Unsat),
            Ok(CheckResult::Unknown(reason)) => Ok(Decision::Unknown(reason.detail)),
            Err(SolverError::Unsupported(detail)) => Ok(Decision::Unknown(detail)),
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
) -> Result<PdrLraOutcome, SolverError> {
    let s = system.state_vars(arena, 0)?;
    let sp = system.state_vars(arena, 1)?;

    // 1. Initiation: init(s) ∧ ¬Inv(s) must be UNSAT.
    let init = system.init(arena, &s)?;
    let not_inv = arena.not(invariant)?;
    if !is_unsat(arena, &[init, not_inv], config)? {
        return Ok(unknown(
            "LRA PDR candidate failed the initiation check (init ⇒ Inv is not valid); declining",
        ));
    }

    // 2. Consecution: Inv(s) ∧ trans(s, s') ∧ ¬Inv(s') must be UNSAT.
    let inv_primed = prime_invariant(arena, invariant, &s, &sp)?;
    let trans = system.trans(arena, &s, &sp)?;
    let not_inv_primed = arena.not(inv_primed)?;
    if !is_unsat(arena, &[invariant, trans, not_inv_primed], config)? {
        return Ok(unknown(
            "LRA PDR candidate failed the consecution check (Inv is not transition-closed); \
             declining",
        ));
    }

    // 3. Safety: Inv(s) ∧ bad(s) must be UNSAT.
    let bad = system.bad(arena, &s)?;
    if !is_unsat(arena, &[invariant, bad], config)? {
        return Ok(unknown(
            "LRA PDR candidate failed the safety check (Inv does not exclude bad); declining",
        ));
    }

    Ok(PdrLraOutcome::Safe { invariant })
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

/// Rebuilds `invariant` (over `s`) onto the **primed** copy `sp` by structural
/// substitution `s[i] ↦ sp[i]` — the consecution check needs the same predicate
/// over the primed state.
fn prime_invariant(
    arena: &mut TermArena,
    invariant: TermId,
    s: &[SymbolId],
    sp: &[SymbolId],
) -> Result<TermId, SolverError> {
    rename_symbols(arena, invariant, s, sp)
}

/// Structurally rebuilds `term`, replacing each state symbol `from[i]` with
/// `to[i]`. The mapping is keyed on a deterministic sorted vector for stable,
/// panic-free lookups.
fn rename_symbols(
    arena: &mut TermArena,
    term: TermId,
    from: &[SymbolId],
    to: &[SymbolId],
) -> Result<TermId, SolverError> {
    let mut mapping: Vec<(SymbolId, SymbolId)> =
        from.iter().copied().zip(to.iter().copied()).collect();
    mapping.sort_by_key(|&(src, _)| src);
    substitute_symbols(arena, term, &mapping)
}

/// Substitutes symbols in `term` per `mapping` (sorted by source symbol),
/// rebuilding the term over the target symbols.
fn substitute_symbols(
    arena: &mut TermArena,
    term: TermId,
    mapping: &[(SymbolId, SymbolId)],
) -> Result<TermId, SolverError> {
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
                .binary_search_by_key(&sym, |&(src, _)| src)
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

/// Conjoins a list of lemmas into a single term `⋀ ¬cube` over `s`. An empty list
/// is `true`.
fn conjoin_lemma_clauses(arena: &mut TermArena, lemmas: &[Lemma]) -> Result<TermId, SolverError> {
    let mut acc: Option<TermId> = None;
    for lemma in lemmas {
        let clause = lemma.to_clause_term(arena)?;
        acc = Some(match acc {
            None => clause,
            Some(prev) => arena.and(prev, clause)?,
        });
    }
    Ok(match acc {
        Some(term) => term,
        None => arena.bool_const(true),
    })
}

/// The atomic `LRA` literals of `formula` that are true at `model`, as a cube over
/// `s`. Used to seed a bad cube from the `bad`-defining literals. Literals whose
/// truth cannot be determined are skipped (conservative).
fn literals_true_at(arena: &mut TermArena, formula: TermId, model: &Model) -> Cube {
    let mut atoms = Vec::new();
    collect_atoms(arena, formula, &mut atoms);
    let assignment = model.to_assignment();
    let mut lits = Vec::new();
    for atom in atoms {
        if matches!(
            axeyum_ir::eval(arena, atom, &assignment),
            Ok(axeyum_ir::Value::Bool(true))
        ) {
            lits.push(atom);
        }
    }
    Cube { lits }
}

/// Flattens a `BoolAnd`-tree `term` into its atomic `LRA` literal leaves, pushing
/// each leaf onto `out`. Returns `false` if any leaf is **not** an atomic `LRA`
/// literal (an inequality, an `Eq` over reals, or a single `BoolNot` of one) — so
/// the caller declines a non-`LRA`/non-conjunctive shape rather than feeding
/// `mbp_lra` something it cannot parse. `true` (a `BoolConst(true)`) flattens to
/// no leaves.
fn flatten_conjuncts(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) -> bool {
    match arena.node(term) {
        TermNode::BoolConst(true) => true,
        TermNode::App {
            op: Op::BoolAnd,
            args,
        } => {
            let args = args.clone();
            args.iter().all(|&arg| flatten_conjuncts(arena, arg, out))
        }
        _ => {
            if is_lra_atom(arena, term) {
                out.push(term);
                true
            } else {
                false
            }
        }
    }
}

/// Whether `term` is an atomic `LRA` literal that [`mbp_lra`] can parse: a real
/// comparison, an `Eq` between real-sorted operands, or a single `BoolNot` of
/// such a literal.
fn is_lra_atom(arena: &TermArena, term: TermId) -> bool {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolNot,
            args,
        } => is_lra_atom(arena, args[0]),
        TermNode::App {
            op: Op::RealLt | Op::RealLe | Op::RealGt | Op::RealGe,
            args,
        } => args
            .iter()
            .all(|&a| arena.sort_of(a) == axeyum_ir::Sort::Real),
        TermNode::App { op: Op::Eq, args } => args
            .iter()
            .all(|&a| arena.sort_of(a) == axeyum_ir::Sort::Real),
        _ => false,
    }
}

/// Collects the atomic `LRA`-literal leaves of `formula` (descending through
/// `BoolAnd`/`BoolOr`/`BoolNot`), used to seed a bad cube. Non-atomic, non-`LRA`
/// leaves are skipped.
fn collect_atoms(arena: &TermArena, formula: TermId, out: &mut Vec<TermId>) {
    match arena.node(formula) {
        TermNode::App {
            op: Op::BoolAnd | Op::BoolOr,
            args,
        } => {
            let args = args.clone();
            for &arg in &args {
                collect_atoms(arena, arg, out);
            }
        }
        TermNode::App {
            op: Op::BoolNot,
            args,
        } => {
            // A negated atom is itself an LRA atom mbp_lra handles; keep the whole
            // negation as the literal.
            let inner = args[0];
            if is_lra_atom(arena, formula) {
                out.push(formula);
            } else {
                collect_atoms(arena, inner, out);
            }
        }
        _ => {
            if is_lra_atom(arena, formula) {
                out.push(formula);
            }
        }
    }
}

/// Whether `term` structurally mentions symbol `var`.
fn term_mentions(arena: &TermArena, term: TermId, var: SymbolId) -> bool {
    match arena.node(term) {
        TermNode::Symbol(s) => *s == var,
        TermNode::App { args, .. } => {
            let args = args.clone();
            args.iter().any(|&a| term_mentions(arena, a, var))
        }
        _ => false,
    }
}

/// Two lemmas are equal iff they hold the same literal term-id set.
fn lemmas_equal(a: &Lemma, b: &Lemma) -> bool {
    a.lits.len() == b.lits.len() && a.lits.iter().all(|lit| b.lits.contains(lit))
}

/// Two frames are equal iff they hold the same lemma set (order-independent).
fn frames_equal(a: &[Lemma], b: &[Lemma]) -> bool {
    a.len() == b.len()
        && a.iter()
            .all(|lemma| b.iter().any(|other| lemmas_equal(lemma, other)))
}

fn unknown(reason: &str) -> PdrLraOutcome {
    PdrLraOutcome::Unknown {
        reason: reason.to_owned(),
    }
}

/// Outcome of an inner trusted decision.
enum Decision {
    Sat,
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
    /// A predecessor genuinely exists but `mbp_lra` could not generalize it; the
    /// caller routes to the trusted `confirm_cex` unrolling.
    UnprojectablePredecessor,
    Decline(String),
}

/// Outcome of forward propagation.
enum PropagateResult {
    Fixpoint(usize),
    Continue,
    Decline(String),
}
