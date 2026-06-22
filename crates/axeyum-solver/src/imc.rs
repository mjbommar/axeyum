//! `McMillan` interpolation-based model checking (`IMC`) — unbounded safety by an
//! interpolant-derived reachable-state over-approximation.
//!
//! Bounded model checking ([`bounded_model_check`](crate::bounded_model_check))
//! refutes safety; k-induction
//! ([`prove_safety_k_induction`](crate::prove_safety_k_induction)) and
//! `IC3`/`PDR` ([`prove_safety_pdr`](crate::prove_safety_pdr)) prove it. `IMC`
//! is the third unbounded-safety route and the canonical **consumer** of the
//! Craig-interpolation engine ([`qf_bv_interpolant`](crate::qf_bv_interpolant)):
//! it grows an over-approximation `R(s)` of the reachable states by repeatedly
//! interpolating a k-unrolling that cannot reach `bad`, until `R` is closed under
//! the transition image (`McMillan`, *Interpolation and SAT-based model checking*,
//! CAV 2003).
//!
//! # The algorithm
//!
//! For increasing unrolling bound `k = 1, 2, …`:
//!
//! 1. **Bounded check at `k`.** If `bad` is reachable within `k` transitions of
//!    `init`, the property is false ⇒ [`ImcOutcome::Reachable`] (confirmed by
//!    [`bounded_model_check`](crate::bounded_model_check)). Otherwise the
//!    k-unrolling from `init` is unsatisfiable, and the interpolation fixpoint can
//!    begin at this `k`.
//! 2. **Interpolation fixpoint.** Start from `R := init`. The k-unrolling is
//!    partitioned as `A = R(s0) ∧ trans(s0, s1)` (the first step from the current
//!    frontier) and `B = trans(s1, s2) ∧ … ∧ trans(s_{k-1}, s_k) ∧ (bad(s1) ∨ … ∨
//!    bad(s_k))` (the suffix that reaches `bad`). `A ∧ B` is unsatisfiable, so the
//!    Craig interpolant `I(s1)` over-approximates the one-step image of `R` while
//!    excluding states that reach `bad` within `k-1` further steps. Renaming `I`
//!    from `s1` to `s0` gives `I'(s0)`, and `R_next := R ∨ I'`. If `R_next ⇒ R`,
//!    `R` is a fixpoint ⇒ a candidate inductive invariant. If `R ∧ bad` ever
//!    becomes satisfiable during growth, this `k` is too coarse ⇒ deepen.
//!
//! # The soundness contract (the whole point)
//!
//! The interpolation fixpoint in this module is **untrusted**. A bug in the
//! partition, the interpolant rename, the fixpoint test, or the growth loop can
//! only ever cause an over-eager [`ImcOutcome::Unknown`], never a wrong
//! [`ImcOutcome::Safe`]. That guarantee is enforced by a *single* trusted gate,
//! [`verify_invariant`], run before any `Safe` is returned: the candidate `R` must
//! pass all three classical inductive-invariant checks, each decided independently
//! by the trusted decider [`check_auto`](crate::check_auto):
//!
//! 1. **Initiation** — `init(s) ∧ ¬R(s)` is `unsat`.
//! 2. **Consecution** — `R(s) ∧ trans(s, s') ∧ ¬R(s')` is `unsat`.
//! 3. **Safety** — `R(s) ∧ bad(s)` is `unsat`.
//!
//! Only if all three are `Unsat` is `Safe { invariant }` returned; otherwise the
//! engine declines to [`ImcOutcome::Unknown`]. A [`ImcOutcome::Reachable`] verdict
//! is likewise gated: it is returned only when
//! [`bounded_model_check`](crate::bounded_model_check) confirms a replay-checked
//! trace. If [`qf_bv_interpolant`](crate::qf_bv_interpolant) returns `None`, the
//! engine deepens `k` rather than failing.
//!
//! Every resource cap (`max_k`, inner iterations, `config.timeout`) degrades to
//! `Unknown`; the engine never hangs and never panics on adversarial input.

use std::time::Instant;

use axeyum_ir::{SymbolId, TermArena, TermId, TermNode};

use crate::auto::check_auto;
use crate::backend::{CheckResult, SolverConfig, SolverError};
use crate::bmc::{BmcOutcome, TransitionSystem, bounded_model_check};
use crate::bv_interpolant::qf_bv_interpolant;
use crate::model::Model;

/// Resource caps for the `IMC` search. All degrade to [`ImcOutcome::Unknown`];
/// none can cause a wrong verdict.
#[derive(Debug, Clone)]
struct ImcLimits {
    /// Maximum unrolling bound `k` before declining.
    max_k: usize,
    /// Maximum interpolation-fixpoint iterations per `k`.
    max_inner: usize,
}

impl Default for ImcLimits {
    fn default() -> Self {
        Self {
            max_k: 32,
            max_inner: 256,
        }
    }
}

/// The result of [`prove_safety_imc`].
#[derive(Debug, Clone)]
pub enum ImcOutcome {
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
    /// `steps` transitions, confirmed by
    /// [`bounded_model_check`](crate::bounded_model_check). The property is false.
    Reachable {
        /// The number of transitions to the bad state.
        steps: usize,
        /// The witnessed trace.
        model: Model,
    },
    /// Undecided: a resource cap, an unsupported construct, an interpolant that
    /// could not be produced or renamed, or a candidate over-approximation that
    /// failed its inductive verification. First-class and honest — never a
    /// (possibly wrong) `Safe`.
    Unknown {
        /// A human-readable reason for declining.
        reason: String,
    },
}

/// Proves a safety property (`bad` is *never* reachable) by **`McMillan`
/// interpolation-based model checking** — the canonical consumer of the
/// Craig-interpolation engine, complementary to the unsat-core-based
/// [`prove_safety_pdr`](crate::prove_safety_pdr).
///
/// The untrusted interpolation fixpoint grows an over-approximation `R(s)` of the
/// reachable states from interpolants of unsatisfiable k-unrollings, until `R` is
/// closed under the transition image. **No `Safe` is returned until that candidate
/// `R` passes all three independent implication checks** (initiation, consecution,
/// safety) under the trusted [`check_auto`](crate::check_auto) decider; otherwise
/// the engine declines to [`ImcOutcome::Unknown`]. A [`ImcOutcome::Reachable`] is
/// confirmed by [`bounded_model_check`](crate::bounded_model_check). Array-free
/// `QF_BV`/Bool transition systems only.
///
/// # Errors
///
/// Returns [`SolverError`] only for a genuine internal failure while building the
/// system's terms; a solver `timeout`/`unsupported`/unsupported-construct, an
/// absent interpolant, or a failed invariant verification is reported as
/// [`ImcOutcome::Unknown`], never an error.
pub fn prove_safety_imc<S: TransitionSystem>(
    arena: &mut TermArena,
    system: &S,
    config: &SolverConfig,
) -> Result<ImcOutcome, SolverError> {
    let limits = ImcLimits::default();
    let mut engine = match ImcEngine::new(arena, system, config, limits) {
        Ok(engine) => engine,
        Err(EngineSetup::Unsupported(reason)) => return Ok(ImcOutcome::Unknown { reason }),
        Err(EngineSetup::Error(error)) => return Err(error),
    };
    engine.run(arena)
}

/// Setup failures for [`ImcEngine::new`]: an unsupported construct degrades to
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

/// The `IMC` engine over a fixed transition system. The canonical step-0 / step-1
/// symbol copies `s` / `sp` are the vocabulary the over-approximation `R` and the
/// final 3-check gate are expressed over.
struct ImcEngine<'sys, S: TransitionSystem> {
    system: &'sys S,
    config: SolverConfig,
    limits: ImcLimits,
    deadline: Option<Instant>,
    /// The canonical step-0 state-variable symbols (the vocabulary of `R`).
    s: Vec<SymbolId>,
    /// The canonical step-1 state-variable symbols (the "primed" copy).
    sp: Vec<SymbolId>,
}

impl<'sys, S: TransitionSystem> ImcEngine<'sys, S> {
    fn new(
        arena: &mut TermArena,
        system: &'sys S,
        config: &SolverConfig,
        limits: ImcLimits,
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
    fn run(&mut self, arena: &mut TermArena) -> Result<ImcOutcome, SolverError> {
        for k in 1..=self.limits.max_k {
            if self.timed_out() {
                return Ok(unknown("IMC timed out"));
            }

            // 1. Bounded check at depth k. A reachable bad state refutes safety
            //    outright (confirmed below via BMC, the only trusted Reachable
            //    source). UnreachableWithinBound ⇒ the k-unrolling from init is
            //    unsat, so the interpolation fixpoint can begin at this k.
            match bounded_model_check(arena, self.system, k, &self.config)? {
                BmcOutcome::Reachable { .. } => return self.confirm_cex(arena, k),
                BmcOutcome::Unknown { steps, reason } => {
                    return Ok(unknown(&format!(
                        "IMC bounded check undecided at depth {steps}: {}",
                        reason.detail
                    )));
                }
                BmcOutcome::UnreachableWithinBound { .. } => {}
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

        Ok(unknown("IMC exceeded the maximum unrolling bound"))
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
                    "IMC timed out in fixpoint".to_owned(),
                ));
            }

            // Build the A/B partition of the k-unrolling with R at the frontier.
            //   A = R(s0) ∧ trans(s0, s1)
            //   B = trans(s1, s2) ∧ … ∧ trans(s_{k-1}, s_k) ∧ (bad(s1) ∨ … ∨ bad(s_k))
            // s0 == self.s (R's vocabulary); s1 == self.sp (the shared interpolant
            // vocabulary); s2..sk are fresh per-step copies.
            let Some(Partition { a, b }) = self.build_partition(arena, r, k)? else {
                return Ok(FixpointResult::Decline(
                    "IMC partition undecided".to_owned(),
                ));
            };

            // The interpolant I is over the shared vars s1 (== self.sp). None ⇒
            // abandon this k (deepen) rather than fail.
            let Some(interpolant) = qf_bv_interpolant(arena, &a, &b) else {
                return Ok(FixpointResult::Deepen);
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
                        "IMC growth-safety check undecided: {detail}"
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
                        "IMC fixpoint test undecided: {detail}"
                    )));
                }
            }
        }

        // Inner loop exhausted at this k ⇒ deepen.
        Ok(FixpointResult::Deepen)
    }

    /// Builds the `McMillan` A/B partition for the current frontier `r` at bound `k`:
    /// `A = r(s0) ∧ trans(s0, s1)`, `B = trans(s1, s2) ∧ … ∧ (bad(s1) ∨ …)`. The
    /// shared vocabulary is `s1 == self.sp`. Returns `None` only if a state-var
    /// declaration fails (propagated as an error elsewhere); construction errors
    /// propagate.
    fn build_partition(
        &mut self,
        arena: &mut TermArena,
        r: TermId,
        k: usize,
    ) -> Result<Option<Partition>, SolverError> {
        let s0 = self.s.clone();
        let s1 = self.sp.clone();

        // A side: r(s0) ∧ trans(s0, s1).
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
            let trans = self.system.trans(arena, &window[0], &window[1])?;
            b.push(trans);
        }
        // (bad(s1) ∨ … ∨ bad(s_k)).
        let mut bad_any: Option<TermId> = None;
        for state in &states {
            let bad_i = self.system.bad(arena, state)?;
            bad_any = Some(match bad_any {
                None => bad_i,
                Some(prev) => arena.or(prev, bad_i)?,
            });
        }
        match bad_any {
            Some(disjunction) => b.push(disjunction),
            // No states ⇒ k == 0, never reached (outer loop starts at k = 1).
            None => return Ok(None),
        }
        Ok(Some(Partition { a, b }))
    }

    /// Confirms a believed counterexample via BMC — the only trusted route to a
    /// `Reachable` verdict. If BMC does not confirm at depth `k`, declines.
    fn confirm_cex(&self, arena: &mut TermArena, k: usize) -> Result<ImcOutcome, SolverError> {
        match bounded_model_check(arena, self.system, k, &self.config)? {
            BmcOutcome::Reachable { steps, model } => Ok(ImcOutcome::Reachable { steps, model }),
            BmcOutcome::UnreachableWithinBound { bound } => Ok(unknown(&format!(
                "IMC believed a counterexample exists, but BMC found none within depth {bound} \
                 (declining rather than reporting an unconfirmed Reachable)"
            ))),
            BmcOutcome::Unknown { steps, reason } => Ok(unknown(&format!(
                "IMC counterexample confirmation undecided at BMC depth {steps}: {}",
                reason.detail
            ))),
        }
    }

    /// Decides a conjunction with the **trusted** [`check_auto`] decider, used for
    /// the inner fixpoint/growth queries. `Unsupported` degrades to `Unknown`.
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

/// The `McMillan` A/B partition of a k-unrolling.
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
) -> Result<ImcOutcome, SolverError> {
    let s = system.state_vars(arena, 0)?;
    let sp = system.state_vars(arena, 1)?;

    // 1. Initiation: init(s) ∧ ¬Inv(s) must be UNSAT.
    let init = system.init(arena, &s)?;
    let not_inv = arena.not(invariant)?;
    if !is_unsat(arena, &[init, not_inv], config)? {
        return Ok(unknown(
            "IMC candidate failed the initiation check (init ⇒ R is not valid); declining",
        ));
    }

    // 2. Consecution: Inv(s) ∧ trans(s, s') ∧ ¬Inv(s') must be UNSAT.
    let inv_primed = prime_invariant(arena, invariant, &s, &sp)?;
    let trans = system.trans(arena, &s, &sp)?;
    let not_inv_primed = arena.not(inv_primed)?;
    if !is_unsat(arena, &[invariant, trans, not_inv_primed], config)? {
        return Ok(unknown(
            "IMC candidate failed the consecution check (R is not transition-closed); declining",
        ));
    }

    // 3. Safety: Inv(s) ∧ bad(s) must be UNSAT.
    let bad = system.bad(arena, &s)?;
    if !is_unsat(arena, &[invariant, bad], config)? {
        return Ok(unknown(
            "IMC candidate failed the safety check (R does not exclude bad); declining",
        ));
    }

    Ok(ImcOutcome::Safe { invariant })
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

fn unknown(reason: &str) -> ImcOutcome {
    ImcOutcome::Unknown {
        reason: reason.to_owned(),
    }
}
