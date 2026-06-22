//! `McMillan` interpolation-based model checking (`IMC`) over **linear real
//! arithmetic** (`LRA`) transition systems — the infinite-state analogue of the
//! `QF_BV` engine in [`imc`](crate::imc).
//!
//! Where [`prove_safety_imc`](crate::prove_safety_imc) proves unbounded safety of
//! finite (`QF_BV`/Bool) systems, [`prove_safety_imc_lra`] does the same for
//! systems whose state variables are **`Real`**-sorted and whose `init`/`trans`/
//! `bad` are conjunctive linear-real-arithmetic formulas. It grows an
//! over-approximation `R(s)` of the reachable states by interpolating an
//! unsatisfiable k-unrolling that cannot reach `bad`, until `R` is closed under
//! the transition image (`McMillan`, *Interpolation and SAT-based model checking*,
//! CAV 2003), now driven by the conjunctive `QF_LRA` Craig-interpolation engine
//! [`lra_interpolant`](crate::lra_interpolant) instead of the bit-level one.
//!
//! # The algorithm
//!
//! For increasing unrolling bound `k = 1, 2, …`:
//!
//! 1. **Bounded check at `k` (inline `LRA` unrolling).** Build the k-step
//!    unrolling over fresh per-step real state-var copies:
//!    `init(s0) ∧ trans(s0,s1) ∧ … ∧ trans(s_{k-1},s_k) ∧ (bad(s1) ∨ … ∨ bad(s_k))`
//!    and decide it with [`check_auto`](crate::check_auto). A `Sat` is a
//!    replay-checked counterexample ⇒ [`ImcLraOutcome::Reachable`]. An `Unsat`
//!    lets the interpolation fixpoint begin at this `k`; an `Unknown` declines.
//! 2. **Interpolation fixpoint.** Start from `R := init`. The unrolling is
//!    partitioned `A = R(s0) ∧ trans(s0, s1)`, `B = trans(s1, s2) ∧ … ∧
//!    trans(s_{k-1}, s_k) ∧ (bad(s1) ∨ … ∨ bad(s_k))`, with `A ∧ B` unsatisfiable.
//!    The Craig interpolant `I(s1)` over-approximates the one-step image of `R`
//!    while excluding states that reach `bad`. Renaming `I` from `s1` to `s0`
//!    gives `I'(s0)`, and `R_next := R ∨ I'`. If `R_next ⇒ R`, `R` is a fixpoint ⇒
//!    a candidate inductive invariant. If `R ∧ bad` becomes satisfiable during
//!    growth, this `k` is too coarse ⇒ deepen (reset `R := init`).
//!
//! # Which formula shapes get an interpolant vs deepen/decline
//!
//! [`lra_interpolant`](crate::lra_interpolant) is a **conjunctive** `QF_LRA`
//! engine: it reads the interpolant off a Farkas refutation of `A ∧ B`. It
//! therefore returns `Ok(Some(I))` only when both `A` and `B` are conjunctions of
//! linear-real atoms. In this engine:
//!
//! * The **first inner iteration** at any `k` is the favorable case: `A = init ∧
//!   trans(s0,s1)` is conjunctive (a conjunctive `init` and a conjunctive `trans`),
//!   and `B` is conjunctive exactly when the bad-disjunction collapses to a single
//!   disjunct — i.e. at `k = 1`, where `B = bad(s1)` alone. There a real
//!   interpolant is produced and can close the fixpoint immediately for systems
//!   whose `init` already over-approximates the reachable set (e.g. a monotone
//!   accumulator with `init : x = 0`, `bad : x < 0`, fixpoint `x ≥ 0`).
//! * Once `R` has grown into a **disjunction** `init ∨ I' ∨ …`, or once the
//!   bad-suffix is a genuine multi-step disjunction (`k ≥ 2`), `A`/`B` are no
//!   longer conjunctive, the Farkas route finds no interpolant, and
//!   `lra_interpolant` returns `Ok(None)` — which the engine treats as a signal to
//!   **deepen** (or, if exhausted, decline to `Unknown`). This is sound but
//!   partial coverage: closing a disjunctive fixpoint needs a disjunctive
//!   interpolation engine (future work).
//!
//! Partial coverage is acceptable; a wrong verdict is not. Every `Safe` is gated
//! by the three independent inductive-invariant checks below, so an interpolation
//! bug can only ever cause an over-eager `Unknown`.
//!
//! # The soundness contract (the whole point)
//!
//! The interpolation fixpoint is **untrusted**. A candidate `R` is accepted as
//! [`ImcLraOutcome::Safe`] only after [`verify_invariant`] passes all three
//! classical inductive-invariant checks, each decided independently by the trusted
//! decider [`check_auto`](crate::check_auto) returning `Unsat`:
//!
//! 1. **Initiation** — `init(s) ∧ ¬R(s)` is `unsat`.
//! 2. **Consecution** — `R(s) ∧ trans(s, s') ∧ ¬R(s')` is `unsat`.
//! 3. **Safety** — `R(s) ∧ bad(s)` is `unsat`.
//!
//! Any non-`Unsat` (sat / unknown / unsupported / error) on any check ⇒ decline to
//! [`ImcLraOutcome::Unknown`]. A [`ImcLraOutcome::Reachable`] is likewise gated: it
//! is returned only from a `check_auto`-`Sat` of the concrete k-unrolling (the
//! model is replay-checked by `check_auto`). A non-`LRA` system (e.g. `BV` state
//! variables) degrades gracefully: `lra_interpolant`/`check_auto` decline and the
//! engine reports `Unknown`, never a panic.
//!
//! Every resource cap (`max_k`, inner iterations, `config.timeout`) degrades to
//! `Unknown`; the engine never hangs and never panics on adversarial input.

use std::time::Instant;

use axeyum_ir::{SymbolId, TermArena, TermId, TermNode};

use crate::auto::check_auto;
use crate::backend::{CheckResult, SolverConfig, SolverError};
use crate::bmc::TransitionSystem;
use crate::interpolant::lra_interpolant;
use crate::model::Model;

/// Resource caps for the `LRA` `IMC` search. All degrade to
/// [`ImcLraOutcome::Unknown`]; none can cause a wrong verdict.
#[derive(Debug, Clone)]
struct ImcLraLimits {
    /// Maximum unrolling bound `k` before declining.
    max_k: usize,
    /// Maximum interpolation-fixpoint iterations per `k`.
    max_inner: usize,
}

impl Default for ImcLraLimits {
    fn default() -> Self {
        Self {
            max_k: 16,
            max_inner: 64,
        }
    }
}

/// The result of [`prove_safety_imc_lra`].
#[derive(Debug, Clone)]
pub enum ImcLraOutcome {
    /// The property holds in every reachable state, proven by the interpolation-
    /// derived over-approximation `invariant` — a [`TermId`] over the step-0 state
    /// variables that **passed all three** independent implication checks
    /// (initiation, consecution, safety) under the trusted
    /// [`check_auto`](crate::check_auto) decider. This is an unbounded guarantee.
    Safe {
        /// The discovered inductive invariant `R(s)`, as a Boolean term over the
        /// step-0 state variables. Re-checkable: assert `init ∧ ¬R`,
        /// `R ∧ trans ∧ ¬R'`, and `R ∧ bad`; each must be `unsat`.
        invariant: TermId,
    },
    /// A bad state **is** reachable: `model` is a replay-checked counterexample at
    /// `steps` transitions, confirmed by a [`check_auto`](crate::check_auto)-`Sat`
    /// of the concrete k-unrolling. The property is false.
    Reachable {
        /// The number of transitions in the witnessed unrolling.
        steps: usize,
        /// The witnessed trace.
        model: Model,
    },
    /// Undecided: a resource cap, an unsupported construct, an interpolant that
    /// could not be produced or renamed, a disjunctive partition outside the
    /// conjunctive-`QF_LRA` interpolation fragment, or a candidate
    /// over-approximation that failed its inductive verification. First-class and
    /// honest — never a (possibly wrong) `Safe`.
    Unknown {
        /// A human-readable reason for declining.
        reason: String,
    },
}

/// Proves a safety property (`bad` is *never* reachable) of a **linear-real**
/// transition system by **`McMillan` interpolation-based model checking** — the
/// infinite-state analogue of [`prove_safety_imc`](crate::prove_safety_imc).
///
/// The untrusted interpolation fixpoint grows an over-approximation `R(s)` of the
/// reachable states from `QF_LRA` Craig interpolants
/// ([`lra_interpolant`](crate::lra_interpolant)) of unsatisfiable k-unrollings,
/// until `R` is closed under the transition image. **No `Safe` is returned until
/// that candidate `R` passes all three independent implication checks**
/// (initiation, consecution, safety) under the trusted
/// [`check_auto`](crate::check_auto) decider; otherwise the engine declines to
/// [`ImcLraOutcome::Unknown`]. A [`ImcLraOutcome::Reachable`] is confirmed by a
/// `check_auto`-`Sat` of the concrete unrolling (the model is replay-checked).
///
/// Coverage is partial by design: the conjunctive `QF_LRA` interpolation engine
/// closes a fixpoint only when the `A`/`B` partition is conjunctive (see the
/// module docs); disjunctive shapes deepen or decline. Soundness is total: a
/// search bug can only cause an over-eager `Unknown`.
///
/// # Errors
///
/// Returns [`SolverError`] only for a genuine internal failure while building the
/// system's terms; a solver `timeout`/`unsupported`/unsupported-construct, an
/// absent interpolant, or a failed invariant verification is reported as
/// [`ImcLraOutcome::Unknown`], never an error.
pub fn prove_safety_imc_lra<S: TransitionSystem>(
    arena: &mut TermArena,
    system: &S,
    config: &SolverConfig,
) -> Result<ImcLraOutcome, SolverError> {
    let limits = ImcLraLimits::default();
    let mut engine = match ImcLraEngine::new(arena, system, config, limits) {
        Ok(engine) => engine,
        Err(EngineSetup::Unsupported(reason)) => return Ok(ImcLraOutcome::Unknown { reason }),
        Err(EngineSetup::Error(error)) => return Err(error),
    };
    engine.run(arena)
}

/// Setup failures for [`ImcLraEngine::new`]: an unsupported construct degrades to
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

/// The `LRA` `IMC` engine over a fixed transition system. The canonical step-0 /
/// step-1 symbol copies `s` / `sp` are the vocabulary the over-approximation `R`
/// and the final 3-check gate are expressed over.
struct ImcLraEngine<'sys, S: TransitionSystem> {
    system: &'sys S,
    config: SolverConfig,
    limits: ImcLraLimits,
    deadline: Option<Instant>,
    /// The canonical step-0 state-variable symbols (the vocabulary of `R`).
    s: Vec<SymbolId>,
    /// The canonical step-1 state-variable symbols (the "primed" copy).
    sp: Vec<SymbolId>,
}

impl<'sys, S: TransitionSystem> ImcLraEngine<'sys, S> {
    fn new(
        arena: &mut TermArena,
        system: &'sys S,
        config: &SolverConfig,
        limits: ImcLraLimits,
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
        })
    }

    /// `true` if the configured timeout has elapsed.
    fn timed_out(&self) -> bool {
        self.deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
    }

    /// Drives the outer `IMC` loop over the unrolling bound `k`.
    fn run(&mut self, arena: &mut TermArena) -> Result<ImcLraOutcome, SolverError> {
        for k in 1..=self.limits.max_k {
            if self.timed_out() {
                return Ok(unknown("LRA IMC timed out"));
            }

            // 1. Bounded check at depth k by an inline LRA unrolling. A Sat is a
            //    replay-checked counterexample (the only trusted Reachable source).
            //    An Unsat lets the interpolation fixpoint begin at this k.
            match self.bounded_check(arena, k)? {
                Decision::Sat => return self.confirm_cex(arena, k),
                Decision::Unknown(detail) => {
                    return Ok(unknown(&format!(
                        "LRA IMC bounded check undecided at depth {k}: {detail}"
                    )));
                }
                Decision::Unsat => {}
            }

            // 2. Interpolation fixpoint at this k.
            match self.interpolation_fixpoint(arena, k)? {
                FixpointResult::Invariant(candidate) => {
                    return verify_invariant(arena, self.system, candidate, &self.config);
                }
                // Too-coarse over-approximation or no usable interpolant ⇒ deepen.
                FixpointResult::Deepen => {}
                FixpointResult::Decline(reason) => return Ok(unknown(&reason)),
            }
        }

        Ok(unknown("LRA IMC exceeded the maximum unrolling bound"))
    }

    /// The concrete k-step unrolling
    /// `init(s0) ∧ trans(s0,s1) ∧ … ∧ trans(s_{k-1},s_k) ∧ (bad(s1) ∨ … ∨ bad(s_k))`
    /// decided by the trusted [`check_auto`](crate::check_auto). A `Sat` is a
    /// real, replay-checked counterexample; `Unsat` clears the way for the
    /// interpolation fixpoint.
    fn bounded_check(&self, arena: &mut TermArena, k: usize) -> Result<Decision, SolverError> {
        let mut states: Vec<Vec<SymbolId>> = vec![self.s.clone()];
        for step in 1..=k {
            states.push(self.system.state_vars(arena, step)?);
        }

        let mut assertions = vec![self.system.init(arena, &states[0])?];
        for window in states.windows(2) {
            assertions.push(self.system.trans(arena, &window[0], &window[1])?);
        }

        // (bad(s1) ∨ … ∨ bad(s_k)) — bad on step 0 is excluded by init's safety,
        // mirroring the McMillan suffix partition (the fixpoint also re-checks it).
        let mut bad_any: Option<TermId> = None;
        for state in states.iter().skip(1) {
            let bad_i = self.system.bad(arena, state)?;
            bad_any = Some(match bad_any {
                None => bad_i,
                Some(prev) => arena.or(prev, bad_i)?,
            });
        }
        if let Some(disjunction) = bad_any {
            assertions.push(disjunction);
        }

        self.decide(arena, &assertions)
    }

    /// The inner interpolation fixpoint at a fixed unrolling bound `k`. Returns a
    /// candidate invariant (for the trusted 3-check gate), `Deepen` to increase
    /// `k`, or `Decline` on an undecided/unsupported query.
    fn interpolation_fixpoint(
        &mut self,
        arena: &mut TermArena,
        k: usize,
    ) -> Result<FixpointResult, SolverError> {
        // R := init, over the canonical step-0 vars.
        let mut r = self.system.init(arena, &self.s.clone())?;

        for _inner in 0..self.limits.max_inner {
            if self.timed_out() {
                return Ok(FixpointResult::Decline(
                    "LRA IMC timed out in fixpoint".to_owned(),
                ));
            }

            // A/B partition of the k-unrolling with R at the frontier.
            //   A = R(s0) ∧ trans(s0, s1)
            //   B = trans(s1, s2) ∧ … ∧ trans(s_{k-1}, s_k) ∧ (bad(s1) ∨ … ∨ bad(s_k))
            // s0 == self.s (R's vocabulary); s1 == self.sp (shared interpolant
            // vocabulary); s2..sk are fresh per-step copies.
            let Partition { a, b } = self.build_partition(arena, r, k)?;

            // The interpolant I is over the shared vars s1 (== self.sp). Try the
            // cheap conjunctive Farkas route first; on its decline, fall back to
            // the DISJUNCTIVE interpolating-SMT route (`lra_interpolant_cnf`),
            // which closes the disjunctive A/B partitions the fixpoint generates
            // (a growing `R = init ∨ I' ∨ …` and the multi-step bad-disjunction).
            // Both `None` ⇒ deepen rather than fail.
            let conjunctive = match lra_interpolant(arena, &a, &b) {
                Ok(some) => some,
                Err(SolverError::Unsupported(_)) => None,
                Err(other) => return Err(other),
            };
            let interpolant = match conjunctive {
                Some(interpolant) => interpolant,
                None => match crate::lra_interpolant_cnf(arena, &a, &b) {
                    Ok(Some(interpolant)) => interpolant,
                    Ok(None) | Err(SolverError::Unsupported(_)) => {
                        return Ok(FixpointResult::Deepen);
                    }
                    Err(other) => return Err(other),
                },
            };

            // Rename I from s1 to s0 to express it over R's vocabulary.
            let interpolant_s0 = rename_symbols(arena, interpolant, &self.sp, &self.s)?;
            let r_next = arena.or(r, interpolant_s0)?;

            // Safety during growth: if R_next ∧ bad is SAT, this k is too coarse.
            let bad = self.system.bad(arena, &self.s.clone())?;
            match self.decide(arena, &[r_next, bad])? {
                Decision::Sat => return Ok(FixpointResult::Deepen),
                Decision::Unknown(detail) => {
                    return Ok(FixpointResult::Decline(format!(
                        "LRA IMC growth-safety check undecided: {detail}"
                    )));
                }
                Decision::Unsat => {}
            }

            // Fixpoint test: R_next ⇒ R, i.e. R_next ∧ ¬R is UNSAT.
            let not_r = arena.not(r)?;
            match self.decide(arena, &[r_next, not_r])? {
                Decision::Unsat => {
                    // R is closed under the image and excludes bad ⇒ candidate
                    // invariant. The trusted 3-check gate decides Safe vs decline.
                    return Ok(FixpointResult::Invariant(r));
                }
                Decision::Sat => {
                    // R grew; iterate.
                    r = r_next;
                }
                Decision::Unknown(detail) => {
                    return Ok(FixpointResult::Decline(format!(
                        "LRA IMC fixpoint test undecided: {detail}"
                    )));
                }
            }
        }

        // Inner loop exhausted at this k ⇒ deepen.
        Ok(FixpointResult::Deepen)
    }

    /// Builds the `McMillan` A/B partition for the current frontier `r` at bound
    /// `k`, each side a **slice of conjuncts** as [`lra_interpolant`] expects:
    /// `A = [r(s0), trans(s0, s1)]`, `B = [trans(s1, s2), …, (bad(s1) ∨ …)]`. The
    /// shared vocabulary is `s1 == self.sp`.
    fn build_partition(
        &mut self,
        arena: &mut TermArena,
        r: TermId,
        k: usize,
    ) -> Result<Partition, SolverError> {
        let s0 = self.s.clone();
        let s1 = self.sp.clone();

        // A side: r(s0) ∧ trans(s0, s1), as separate conjuncts.
        let trans01 = self.system.trans(arena, &s0, &s1)?;
        let a = vec![r, trans01];

        // B side: collect the suffix states s1..sk, chain trans, disjoin bad.
        let mut states: Vec<Vec<SymbolId>> = vec![s1];
        for step in 2..=k {
            states.push(self.system.state_vars(arena, step)?);
        }
        let mut b: Vec<TermId> = Vec::new();
        // trans(s1, s2) … trans(s_{k-1}, s_k): only when k >= 2.
        for window in states.windows(2) {
            b.push(self.system.trans(arena, &window[0], &window[1])?);
        }
        // (bad(s1) ∨ … ∨ bad(s_k)) — a single conjunct on the B side.
        let mut bad_any: Option<TermId> = None;
        for state in &states {
            let bad_i = self.system.bad(arena, state)?;
            bad_any = Some(match bad_any {
                None => bad_i,
                Some(prev) => arena.or(prev, bad_i)?,
            });
        }
        if let Some(disjunction) = bad_any {
            b.push(disjunction);
        }
        Ok(Partition { a, b })
    }

    /// Confirms a believed counterexample by re-deciding the concrete k-unrolling —
    /// the only trusted route to a `Reachable` verdict; the returned `model` is
    /// replay-checked by [`check_auto`](crate::check_auto). If the re-check does not
    /// reproduce the `Sat`, declines rather than reporting an unconfirmed verdict.
    fn confirm_cex(&self, arena: &mut TermArena, k: usize) -> Result<ImcLraOutcome, SolverError> {
        let mut states: Vec<Vec<SymbolId>> = vec![self.s.clone()];
        for step in 1..=k {
            states.push(self.system.state_vars(arena, step)?);
        }
        let mut assertions = vec![self.system.init(arena, &states[0])?];
        for window in states.windows(2) {
            assertions.push(self.system.trans(arena, &window[0], &window[1])?);
        }
        let mut bad_any: Option<TermId> = None;
        for state in states.iter().skip(1) {
            let bad_i = self.system.bad(arena, state)?;
            bad_any = Some(match bad_any {
                None => bad_i,
                Some(prev) => arena.or(prev, bad_i)?,
            });
        }
        if let Some(disjunction) = bad_any {
            assertions.push(disjunction);
        }

        match check_auto(arena, &assertions, &self.config) {
            Ok(CheckResult::Sat(model)) => Ok(ImcLraOutcome::Reachable { steps: k, model }),
            Ok(CheckResult::Unsat) => Ok(unknown(
                "LRA IMC believed a counterexample exists, but the re-checked unrolling was unsat \
                 (declining rather than reporting an unconfirmed Reachable)",
            )),
            Ok(CheckResult::Unknown(reason)) => Ok(unknown(&format!(
                "LRA IMC counterexample confirmation undecided at depth {k}: {}",
                reason.detail
            ))),
            Err(SolverError::Unsupported(detail)) => Ok(unknown(&detail)),
            Err(other) => Err(other),
        }
    }

    /// Decides a conjunction with the **trusted** [`check_auto`] decider, used for
    /// both the bounded check and the inner fixpoint/growth queries.
    /// `Unsupported` degrades to `Unknown`.
    fn decide(
        &self,
        arena: &mut TermArena,
        assertions: &[TermId],
    ) -> Result<Decision, SolverError> {
        match check_auto(arena, assertions, &self.config) {
            Ok(CheckResult::Sat(_)) => Ok(Decision::Sat),
            Ok(CheckResult::Unsat) => Ok(Decision::Unsat),
            Ok(CheckResult::Unknown(reason)) => Ok(Decision::Unknown(reason.detail)),
            Err(SolverError::Unsupported(detail)) => Ok(Decision::Unknown(detail)),
            Err(other) => Err(other),
        }
    }
}

/// The `McMillan` A/B partition of a k-unrolling, each side a slice of conjuncts.
struct Partition {
    a: Vec<TermId>,
    b: Vec<TermId>,
}

/// Outcome of the inner interpolation fixpoint at a fixed `k`.
enum FixpointResult {
    /// A fixpoint over-approximation, to be handed to the trusted 3-check gate.
    Invariant(TermId),
    /// This `k` is too coarse / no usable interpolant ⇒ increase `k`.
    Deepen,
    /// An undecided/unsupported inner query ⇒ decline.
    Decline(String),
}

/// Outcome of an inner trusted decision.
enum Decision {
    Sat,
    Unsat,
    Unknown(String),
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
/// This makes the entire interpolation fixpoint untrusted: a search bug can only
/// cause a decline, never a wrong `Safe`.
fn verify_invariant(
    arena: &mut TermArena,
    system: &impl TransitionSystem,
    invariant: TermId,
    config: &SolverConfig,
) -> Result<ImcLraOutcome, SolverError> {
    let s = system.state_vars(arena, 0)?;
    let sp = system.state_vars(arena, 1)?;

    // 1. Initiation: init(s) ∧ ¬Inv(s) must be UNSAT.
    let init = system.init(arena, &s)?;
    let not_inv = arena.not(invariant)?;
    if !is_unsat(arena, &[init, not_inv], config)? {
        return Ok(unknown(
            "LRA IMC candidate failed the initiation check (init ⇒ R is not valid); declining",
        ));
    }

    // 2. Consecution: Inv(s) ∧ trans(s, s') ∧ ¬Inv(s') must be UNSAT.
    let inv_primed = prime_invariant(arena, invariant, &s, &sp)?;
    let trans = system.trans(arena, &s, &sp)?;
    let not_inv_primed = arena.not(inv_primed)?;
    if !is_unsat(arena, &[invariant, trans, not_inv_primed], config)? {
        return Ok(unknown(
            "LRA IMC candidate failed the consecution check (R is not transition-closed); \
             declining",
        ));
    }

    // 3. Safety: Inv(s) ∧ bad(s) must be UNSAT.
    let bad = system.bad(arena, &s)?;
    if !is_unsat(arena, &[invariant, bad], config)? {
        return Ok(unknown(
            "LRA IMC candidate failed the safety check (R does not exclude bad); declining",
        ));
    }

    Ok(ImcLraOutcome::Safe { invariant })
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
/// `to[i]`. Used both to rename an interpolant from the `s1` copy to `s0` and to
/// prime an invariant from `s` to `s'`. The mapping is keyed on a deterministic
/// sorted vector for stable, panic-free lookups.
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

fn unknown(reason: &str) -> ImcLraOutcome {
    ImcLraOutcome::Unknown {
        reason: reason.to_owned(),
    }
}
