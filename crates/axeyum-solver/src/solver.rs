//! A high-level incremental solver façade.
//!
//! [`Solver`] wraps any [`SolverBackend`] with an assertion stack and
//! SMT-LIB-style [`Solver::push`]/[`Solver::pop`] scopes, plus one-shot
//! [`Solver::check_assuming`] assumptions. It is the ergonomic surface a
//! consumer like a symbolic-execution engine wants: push a branch predicate,
//! check, pop, continue down another path.
//!
//! The façade is incremental at the interface level for **every** backend, and
//! incremental *in fact* on the pure-Rust bit-vector path: when the wrapped
//! backend is that path and the configuration sets no lever the warm engine
//! ignores, [`Solver::check`] is decided by a retained [`IncrementalBvSolver`]
//! whose lowering and CNF survive between calls, and [`Solver::push`] /
//! [`Solver::pop`] open and close real engine scopes (roadmap item 1.1b).
//! Anything else — another backend, a configuration lever the warm engine does
//! not read, a query outside the scalar `QF_BV` fragment, or a warm answer that
//! is not a verdict — falls back to re-submitting the active assertions to the
//! backend, exactly as before. `Solver::assertions` remains the single source
//! of truth for cores, proofs, interpolants and optimization either way, and
//! every `sat` is still checked by model replay against the original terms.
//!
//! [`WarmFacadeStats`] reports which route each check took.
//!
//! # Example
//!
//! ```
//! use axeyum_ir::{Sort, TermArena};
//! use axeyum_solver::{CheckResult, SatBvBackend, Solver};
//!
//! let mut arena = TermArena::new();
//! let x_sym = arena.declare("x", Sort::BitVec(8))?;
//! let x = arena.var(x_sym);
//! let ten = arena.bv_const(8, 10)?;
//! let x_lt_10 = arena.bv_ult(x, ten)?;
//!
//! let mut solver = Solver::new(SatBvBackend::new());
//! solver.assert(x_lt_10);
//!
//! // Explore a branch under a scope, then discard it.
//! solver.push();
//! let zero = arena.bv_const(8, 0)?;
//! let x_is_zero = arena.eq(x, zero)?;
//! solver.assert(x_is_zero);
//! assert!(matches!(solver.check(&arena)?, CheckResult::Sat(_)));
//! solver.pop();
//!
//! // A one-shot assumption does not persist after the check.
//! let five = arena.bv_const(8, 5)?;
//! let x_is_five = arena.eq(x, five)?;
//! assert!(matches!(
//!     solver.check_assuming(&arena, &[x_is_five])?,
//!     CheckResult::Sat(_)
//! ));
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```

use axeyum_ir::{Sort, SymbolId, TermArena, TermId};

use crate::backend::{
    Capabilities, CheckResult, SolveStats, SolverBackend, SolverConfig, SolverError,
};
use crate::incremental::IncrementalBvSolver;
use crate::interpolant::{DispatchedInterpolant, InterpolantCertificate};

/// A stateful, incremental front end over a [`SolverBackend`].
#[derive(Debug)]
pub struct Solver<B> {
    backend: B,
    config: SolverConfig,
    assertions: Vec<TermId>,
    scopes: Vec<usize>,
    /// The retained bit-vector engine, when this solver's backend and
    /// configuration make it an exact stand-in (roadmap item 1.1b).
    warm: Warm,
    warm_stats: WarmFacadeStats,
}

/// The classified result of [`Solver::interpolant_explained`] — the
/// "interpolant vs no-interpolant-exists vs declined" distinction a CHC/PDR
/// consumer needs to react correctly (generalize-with-`I` / cube-is-reachable /
/// fall-back-generalization).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InterpolantOutcome {
    /// A fully re-verified Craig interpolant for the partition.
    Interpolant(TermId),
    /// `A ∧ B` is **satisfiable** — no Craig interpolant exists for this
    /// partition (e.g. a blocked-cube query whose cube is actually reachable).
    NotInterpolable,
    /// `A ∧ B` is unsatisfiable or undecided, but every supported theory
    /// **declined** to produce a verified interpolant — the consumer should fall
    /// back to another generalization rather than treat this as "no interpolant".
    Declined,
}

impl<B: SolverBackend> Solver<B> {
    /// Creates a solver over `backend` with the default configuration.
    pub fn new(backend: B) -> Self {
        Self::with_config(backend, SolverConfig::default())
    }

    /// Creates a solver over `backend` with an explicit configuration.
    pub fn with_config(backend: B, config: SolverConfig) -> Self {
        Self {
            backend,
            config,
            assertions: Vec::new(),
            scopes: Vec::new(),
            warm: Warm::Idle,
            warm_stats: WarmFacadeStats::default(),
        }
    }

    /// The current per-check configuration.
    pub fn config(&self) -> &SolverConfig {
        &self.config
    }

    /// Replaces the per-check configuration.
    ///
    /// Any retained warm engine is discarded: it was built for the old
    /// configuration and both its admissibility ([`warm_config_is_honored`])
    /// and its own timeout/resource budgets are fixed at construction.
    pub fn set_config(&mut self, config: SolverConfig) {
        self.config = config;
        self.warm = Warm::Idle;
    }

    /// Reports what the underlying backend supports.
    pub fn capabilities(&self) -> Capabilities {
        self.backend.capabilities()
    }

    /// Adds a Boolean assertion to the current scope.
    ///
    /// The sort is validated by the backend at [`Solver::check`] time, which
    /// returns [`SolverError::NonBooleanAssertion`] for a non-Boolean term.
    pub fn assert(&mut self, term: TermId) {
        self.assertions.push(term);
    }

    /// Adds several assertions to the current scope.
    pub fn assert_all(&mut self, terms: &[TermId]) {
        self.assertions.extend_from_slice(terms);
    }

    /// Opens a new scope; assertions added afterwards are removed by the
    /// matching [`Solver::pop`].
    pub fn push(&mut self) {
        self.scopes.push(self.assertions.len());
    }

    /// Closes the most recent scope, discarding assertions added since the
    /// matching [`Solver::push`].
    ///
    /// Returns `false` if there was no open scope to close.
    ///
    /// On the warm route this closes the matching engine frame **eagerly**,
    /// which is what makes a later [`Solver::push`] a genuinely new scope. The
    /// engine's frame count is otherwise only compared against the façade's
    /// depth at check time, and depth alone cannot tell `pop; push` from "no
    /// change" — a `pop` followed by a `push` and a different assertion would
    /// then be decided against the *discarded* scope's assertion. That is a
    /// wrong `unsat`, and it is the exact bug `warm_scope_leak_is_caught` and
    /// the leak-catcher scripts exist to detect.
    pub fn pop(&mut self) -> bool {
        let Some(mark) = self.scopes.pop() else {
            return false;
        };
        self.assertions.truncate(mark);
        let mut broken = false;
        if let Warm::Live(state) = &mut self.warm {
            while state.synced.len() > self.scopes.len() + 1 {
                if !state.engine.pop() {
                    broken = true;
                    break;
                }
                state.synced.pop();
                self.warm_stats.scope_pops += 1;
            }
        }
        if broken {
            // The engine and the façade disagree about depth. Unreachable while
            // the invariant in `WarmState::synced` holds; retiring the engine is
            // the reaction that cannot decide a query against a stale frame.
            self.warm = Warm::Off;
        }
        true
    }

    /// The number of currently open scopes.
    pub fn scope_depth(&self) -> usize {
        self.scopes.len()
    }

    /// The assertions currently active across all open scopes.
    pub fn assertions(&self) -> &[TermId] {
        &self.assertions
    }

    /// Checks satisfiability of the active assertions.
    ///
    /// When the backend is the pure-Rust BV path and the configuration sets no
    /// lever the warm engine ignores, this is decided by a **retained**
    /// [`IncrementalBvSolver`] whose lowering and CNF survive between calls and
    /// whose frames mirror [`Solver::push`]/[`Solver::pop`] as real scopes
    /// (roadmap item 1.1b). Otherwise — and whenever the warm engine declines,
    /// is undecided, or errors — the wrapped backend re-decides the active
    /// assertions exactly as before. `self.assertions` stays the single source
    /// of truth either way, so [`Solver::unsat_core`],
    /// [`Solver::prove_unsat_to_lean`], [`Solver::check_auto_explained`] and the
    /// interpolant entry points are unaffected.
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the backend (for example a non-Boolean
    /// assertion or an unsupported construct). An undecided query is
    /// `Ok(CheckResult::Unknown)`.
    pub fn check(&mut self, arena: &TermArena) -> Result<CheckResult, SolverError> {
        if let Some(result) = self.warm_check(arena, &[]) {
            return Ok(result);
        }
        self.warm_stats.cold_checks += 1;
        self.backend.check(arena, &self.assertions, &self.config)
    }

    /// Reconstruct a kernel-checked Lean proof that the active assertions are UNSAT,
    /// dispatching to the matching theory emitter+reconstructor (see
    /// [`crate::prove_unsat_to_lean`]); returns the [`crate::ProofFragment`] routed.
    ///
    /// Call after [`Solver::check`] reports [`CheckResult::Unsat`]: this re-derives
    /// the refutation as a machine-checkable Lean term the trusted kernel accepts,
    /// over the supported fragments (`QF_BV`/`QF_UF`/`QF_UFBV`/`QF_ABV`, datatypes,
    /// `LRA`, `∀`/`∃`).
    /// `arena` is taken mutably because the emitters introduce fresh terms (skolems,
    /// lowered operators) during proof construction.
    ///
    /// # Errors
    ///
    /// Propagates [`crate::ReconstructError`] when the fragment is unsupported, the
    /// instance is not UNSAT through it, or reconstruction does not kernel-check.
    pub fn prove_unsat_to_lean(
        &self,
        arena: &mut TermArena,
    ) -> Result<crate::ProofFragment, crate::ReconstructError> {
        crate::prove_unsat_to_lean(arena, &self.assertions)
    }

    /// Like [`Solver::prove_unsat_to_lean`], but also returns a **self-contained
    /// Lean 4 module** (`prelude`-mode source) that re-proves the refutation and is
    /// checkable by an independent `lean` binary (see
    /// [`crate::prove_unsat_to_lean_module`]).
    ///
    /// # Errors
    ///
    /// Same as [`Solver::prove_unsat_to_lean`].
    pub fn prove_unsat_to_lean_module(
        &self,
        arena: &mut TermArena,
    ) -> Result<(crate::ProofFragment, String), crate::ReconstructError> {
        crate::prove_unsat_to_lean_module(arena, &self.assertions)
    }

    /// Decides the active assertions through the auto-dispatcher and additionally
    /// returns a [`crate::RouteTrace`]: the ordered record of which dispatch
    /// routes were tried and why each declined (see [`crate::check_auto_explained`]).
    ///
    /// This is purely additive telemetry — the returned [`CheckResult`] is
    /// **identical** to the one a plain auto-solve of the same assertions
    /// produces; the trace never changes the verdict.
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the underlying dispatch.
    pub fn check_auto_explained(
        &self,
        arena: &mut TermArena,
    ) -> Result<(CheckResult, crate::RouteTrace), SolverError> {
        crate::check_auto_explained(arena, &self.assertions, &self.config)
    }

    /// Computes a (deletion-minimized) unsat core of the active assertions as
    /// indices into them, or `None` if they are not `unsat` (see
    /// [`crate::unsat_core`]).
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the underlying solve.
    pub fn unsat_core(&self, arena: &mut TermArena) -> Result<Option<Vec<usize>>, SolverError> {
        crate::unsat_core(arena, &self.assertions, &self.config)
    }

    /// Computes a verified Craig interpolant for the partition of the active
    /// assertions in which `a_indices` selects the `A`-side and the remaining
    /// assertions form the `B`-side. Returns `Ok(Some(I))` with a fully
    /// re-checked interpolant, or `Ok(None)` when no Farkas interpolant is
    /// available (the conjunction is satisfiable, outside conjunctive `QF_LRA`,
    /// or the candidate fails its re-checks). Out-of-range indices are ignored.
    /// See [`crate::lra_interpolant`].
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the underlying Farkas decision / the
    /// interpolant re-verification.
    pub fn interpolant(
        &self,
        arena: &mut TermArena,
        a_indices: &[usize],
    ) -> Result<Option<TermId>, SolverError> {
        let (a, b) = self.partition(a_indices);
        Self::dispatch_interpolant(arena, &a, &b)
    }

    /// Like [`Solver::interpolant`], but also returns the **externally-checkable
    /// certificate** for the interpolant when the winning theory rung had a
    /// certified route covering this query (roadmap item 2.8).
    ///
    /// [`DispatchedInterpolant::interpolant`] is byte-identical to what
    /// [`Solver::interpolant`] returns for the same partition — the certificate
    /// is strictly additive assurance, and a rung that cannot certify still
    /// returns its `Validated` interpolant with
    /// [`certificate: None`](DispatchedInterpolant::certificate). The
    /// certificate itself carries Alethe refutations (Carcara-checkable) or
    /// Lean modules (kernel-checked before the certificate is built) for both
    /// Craig soundness conditions `A ⇒ I` and `I ∧ B ⇒ ⊥`; see
    /// [`InterpolantCertificate`].
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] exactly as [`Solver::interpolant`] does;
    /// certificate production never introduces an error of its own (a certified
    /// route that fails degrades to `certificate: None`).
    pub fn interpolant_certified(
        &self,
        arena: &mut TermArena,
        a_indices: &[usize],
    ) -> Result<Option<DispatchedInterpolant>, SolverError> {
        let (a, b) = self.partition(a_indices);
        Self::dispatch_interpolant_certified(arena, &a, &b)
    }

    /// Like [`Solver::interpolant`], but distinguishes *why* no interpolant was
    /// returned — the distinction a CHC/PDR consumer needs to tell "no interpolant
    /// exists" from "we declined". Returns:
    /// - [`InterpolantOutcome::Interpolant`] with a verified interpolant;
    /// - [`InterpolantOutcome::NotInterpolable`] when `A ∧ B` is *satisfiable*
    ///   (there is no Craig interpolant — e.g. a blocked-cube query whose cube is
    ///   actually reachable);
    /// - [`InterpolantOutcome::Declined`] when `A ∧ B` is unsat-or-undecided but
    ///   every supported theory declined to produce a verified interpolant (the
    ///   consumer should fall back to another generalization).
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the underlying interpolation / decision.
    pub fn interpolant_explained(
        &self,
        arena: &mut TermArena,
        a_indices: &[usize],
    ) -> Result<InterpolantOutcome, SolverError> {
        let (a, b) = self.partition(a_indices);
        if let Some(interpolant) = Self::dispatch_interpolant(arena, &a, &b)? {
            return Ok(InterpolantOutcome::Interpolant(interpolant));
        }
        // No interpolant produced: classify by re-deciding A ∧ B. A *satisfiable*
        // conjunction has no interpolant at all (NotInterpolable); otherwise the
        // theories declined on an unsat/undecided query (Declined).
        let mut combined = a;
        combined.extend_from_slice(&b);
        match crate::check_auto(arena, &combined, &self.config) {
            Ok(CheckResult::Sat(_)) => Ok(InterpolantOutcome::NotInterpolable),
            _ => Ok(InterpolantOutcome::Declined),
        }
    }

    /// Splits the active assertions into the `A`-side (the in-range `a_indices`)
    /// and the `B`-side (the rest). Out-of-range indices are ignored.
    fn partition(&self, a_indices: &[usize]) -> (Vec<TermId>, Vec<TermId>) {
        let n = self.assertions.len();
        let a_set: std::collections::BTreeSet<usize> =
            a_indices.iter().copied().filter(|&i| i < n).collect();
        let a: Vec<TermId> = a_set.iter().map(|&i| self.assertions[i]).collect();
        let b: Vec<TermId> = (0..n)
            .filter(|i| !a_set.contains(i))
            .map(|i| self.assertions[i])
            .collect();
        (a, b)
    }

    /// Tries each theory interpolator in turn: `QF_LRA` Farkas, disjunctive
    /// (CNF) `QF_LRA`, the conjunctive `QF_LIA` rational-relaxation interpolant,
    /// disjunctive (CNF) `QF_LIA`, ground EUF, combined `QF_UFLRA`, `QF_UFLIA`,
    /// then the `QF_BV` bit-blast interpolant — each a fallback for the earlier
    /// theories' declines (`Unsupported` or `Ok(None)`).
    ///
    /// The term-only projection of [`Self::dispatch_interpolant_certified`].
    fn dispatch_interpolant(
        arena: &mut TermArena,
        a: &[TermId],
        b: &[TermId],
    ) -> Result<Option<TermId>, SolverError> {
        Ok(Self::dispatch_interpolant_certified(arena, a, b)?
            .map(|dispatched| dispatched.interpolant))
    }

    /// The theory-interpolant dispatch, carrying the externally-checkable
    /// certificate of whichever rung won (roadmap item 2.8).
    ///
    /// The rung ORDER and every decline condition are exactly those of the
    /// uncertified dispatch: each rung is still entered through its plain
    /// `*_interpolant` entry point, and only *after* that rung has produced an
    /// interpolant do we ask its `*_certified` sibling for a certificate. So
    /// certification can never change which rung wins, whether an interpolant is
    /// produced, or which interpolant it is — a certified route that declines,
    /// errors, or (impossibly) disagrees on the term leaves the interpolant
    /// exactly as the uncertified dispatch had it, with `certificate: None`.
    ///
    /// The two disjunctive (CNF) rungs have no certified route at all and always
    /// report `None`; see [`InterpolantCertificate`].
    fn dispatch_interpolant_certified(
        arena: &mut TermArena,
        a: &[TermId],
        b: &[TermId],
    ) -> Result<Option<DispatchedInterpolant>, SolverError> {
        match crate::lra_interpolant(arena, a, b) {
            Ok(Some(interpolant)) => Ok(Some(Self::certify_lra(arena, a, b, interpolant))),
            Ok(None) | Err(SolverError::Unsupported(_)) => {
                // Disjunctive (CNF) QF_LRA: the conjunctive Farkas interpolant
                // declines when the assertions carry Boolean structure over real
                // atoms; the interpolating-SMT construction handles those. No
                // certified route exists for this shape (the certificate emitters
                // are conjunctive), so it stays `Validated`.
                if let Some(interpolant) = crate::lra_interpolant_cnf(arena, a, b)? {
                    return Ok(Some(DispatchedInterpolant::uncertified(interpolant)));
                }
                // QF_LIA via the rational relaxation (verified over the integers).
                if let Some(interpolant) = crate::lia_interpolant(arena, a, b)? {
                    return Ok(Some(Self::certify_lia(arena, a, b, interpolant)));
                }
                // Disjunctive (CNF) QF_LIA: the conjunctive integer interpolant
                // declines on Boolean structure over integer atoms; the
                // relaxation-driven interpolating-SMT construction handles those.
                // No certified route for this shape either.
                if let Some(interpolant) = crate::lia_interpolant_cnf(arena, a, b)? {
                    return Ok(Some(DispatchedInterpolant::uncertified(interpolant)));
                }
                match crate::qf_uf_interpolant(arena, a, b) {
                    Ok(Some(interpolant)) => {
                        Ok(Some(Self::certify_qf_uf(arena, a, b, interpolant)))
                    }
                    Ok(None) => match crate::uflra_interpolant(arena, a, b) {
                        Ok(Some(interpolant)) => {
                            Ok(Some(Self::certify_uflra(arena, a, b, interpolant)))
                        }
                        Ok(None) => match crate::uflia_interpolant(arena, a, b) {
                            Ok(Some(interpolant)) => {
                                Ok(Some(Self::certify_uflia(arena, a, b, interpolant)))
                            }
                            Ok(None) => {
                                let Some(interpolant) = crate::qf_bv_interpolant(arena, a, b)
                                else {
                                    return Ok(None);
                                };
                                Ok(Some(Self::certify_qf_bv(arena, a, b, interpolant)))
                            }
                            Err(other) => Err(other),
                        },
                        Err(other) => Err(other),
                    },
                    Err(other) => Err(other),
                }
            }
            Err(other) => Err(other),
        }
    }

    // --- Per-rung certificate attachment (roadmap item 2.8) -----------------
    //
    // Each helper asks one theory's `*_certified` entry point for an
    // externally-checkable certificate of an interpolant the PLAIN entry point
    // already produced. Every one of them is verdict-neutral by construction:
    //   - a certified route that declines (`Ok(None)`) or errors keeps the
    //     uncertified interpolant with no certificate;
    //   - a certified route that returns a DIFFERENT term (which the shared
    //     `build_verified_*` builders make impossible, so this is a guard, not a
    //     code path) also keeps the uncertified interpolant and drops the
    //     certificate. The shipping term never comes from the certified route.

    /// Attaches the conjunctive `QF_LRA` Alethe certificate when
    /// [`crate::lra_interpolant_certified`] covers this partition.
    fn certify_lra(
        arena: &mut TermArena,
        a: &[TermId],
        b: &[TermId],
        interpolant: TermId,
    ) -> DispatchedInterpolant {
        match crate::lra_interpolant_certified(arena, a, b) {
            Ok(Some(cert)) if cert.interpolant == interpolant => DispatchedInterpolant {
                interpolant,
                certificate: Some(InterpolantCertificate::Lra(Box::new(cert))),
            },
            _ => DispatchedInterpolant::uncertified(interpolant),
        }
    }

    /// Attaches the conjunctive `QF_LIA` Lean-kernel-checked certificate when
    /// [`crate::lia_interpolant_certified`] covers this partition.
    fn certify_lia(
        arena: &mut TermArena,
        a: &[TermId],
        b: &[TermId],
        interpolant: TermId,
    ) -> DispatchedInterpolant {
        match crate::lia_interpolant_certified(arena, a, b) {
            Ok(Some(cert)) if cert.interpolant == interpolant => DispatchedInterpolant {
                interpolant,
                certificate: Some(InterpolantCertificate::Lia(Box::new(cert))),
            },
            _ => DispatchedInterpolant::uncertified(interpolant),
        }
    }

    /// Attaches the ground-EUF Alethe certificate when
    /// [`crate::qf_uf_interpolant_certified`] covers this partition.
    fn certify_qf_uf(
        arena: &mut TermArena,
        a: &[TermId],
        b: &[TermId],
        interpolant: TermId,
    ) -> DispatchedInterpolant {
        match crate::qf_uf_interpolant_certified(arena, a, b) {
            Ok(Some(cert)) if cert.interpolant == interpolant => DispatchedInterpolant {
                interpolant,
                certificate: Some(InterpolantCertificate::QfUf(Box::new(cert))),
            },
            _ => DispatchedInterpolant::uncertified(interpolant),
        }
    }

    /// Attaches the combined `QF_UFLRA` Alethe certificate when
    /// [`crate::uflra_interpolant_certified`] covers this partition.
    fn certify_uflra(
        arena: &mut TermArena,
        a: &[TermId],
        b: &[TermId],
        interpolant: TermId,
    ) -> DispatchedInterpolant {
        match crate::uflra_interpolant_certified(arena, a, b) {
            Ok(Some(cert)) if cert.interpolant == interpolant => DispatchedInterpolant {
                interpolant,
                certificate: Some(InterpolantCertificate::Uflra(Box::new(cert))),
            },
            _ => DispatchedInterpolant::uncertified(interpolant),
        }
    }

    /// Attaches the combined `QF_UFLIA` Lean-kernel-checked certificate when
    /// [`crate::uflia_interpolant_certified`] covers this partition.
    fn certify_uflia(
        arena: &mut TermArena,
        a: &[TermId],
        b: &[TermId],
        interpolant: TermId,
    ) -> DispatchedInterpolant {
        match crate::uflia_interpolant_certified(arena, a, b) {
            Ok(Some(cert)) if cert.interpolant == interpolant => DispatchedInterpolant {
                interpolant,
                certificate: Some(InterpolantCertificate::Uflia(Box::new(cert))),
            },
            _ => DispatchedInterpolant::uncertified(interpolant),
        }
    }

    /// Attaches the `QF_BV` bit-blast Alethe certificate when
    /// [`crate::qf_bv_interpolant_certified`] covers this partition.
    fn certify_qf_bv(
        arena: &mut TermArena,
        a: &[TermId],
        b: &[TermId],
        interpolant: TermId,
    ) -> DispatchedInterpolant {
        match crate::qf_bv_interpolant_certified(arena, a, b) {
            Ok(Some(cert)) if cert.interpolant == interpolant => DispatchedInterpolant {
                interpolant,
                certificate: Some(InterpolantCertificate::QfBv(Box::new(cert))),
            },
            _ => DispatchedInterpolant::uncertified(interpolant),
        }
    }

    /// Maximizes the integer-linear `objective` subject to the active assertions
    /// (see [`crate::maximize_lia`]).
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the optimizer.
    pub fn maximize_lia(
        &self,
        arena: &mut TermArena,
        objective: TermId,
    ) -> Result<crate::OptOutcome, SolverError> {
        crate::maximize_lia(arena, &self.assertions, objective)
    }

    /// Maximizes the unsigned bit-vector `objective` subject to the active
    /// assertions (see [`crate::maximize_bv`]).
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the optimizer.
    pub fn maximize_bv(
        &self,
        arena: &mut TermArena,
        objective: TermId,
    ) -> Result<crate::OptOutcome, SolverError> {
        crate::maximize_bv_with_config(arena, &self.assertions, objective, &self.config)
    }

    /// Minimizes the unsigned bit-vector `objective` subject to the active
    /// assertions (see [`crate::minimize_bv`]).
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the optimizer.
    pub fn minimize_bv(
        &self,
        arena: &mut TermArena,
        objective: TermId,
    ) -> Result<crate::OptOutcome, SolverError> {
        crate::minimize_bv_with_config(arena, &self.assertions, objective, &self.config)
    }

    /// Minimizes the integer-linear `objective` subject to the active assertions
    /// (see [`crate::minimize_lia`]).
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the optimizer.
    pub fn minimize_lia(
        &self,
        arena: &mut TermArena,
        objective: TermId,
    ) -> Result<crate::OptOutcome, SolverError> {
        crate::minimize_lia(arena, &self.assertions, objective)
    }

    /// Returns a replay-checked model that is lexicographically minimized over
    /// `symbols` in the order provided, using the active assertions as the
    /// constraint set (see [`crate::minimize_model`]).
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the minimizer.
    pub fn minimize_model(
        &self,
        arena: &mut TermArena,
        symbols: &[SymbolId],
    ) -> Result<crate::ModelMinimizeOutcome, SolverError> {
        crate::minimize_model_with_config(arena, &self.assertions, symbols, &self.config)
    }

    /// Returns a replay-checked model that is lexicographically minimized over
    /// richer objective metadata, using the active assertions as the constraint
    /// set (see [`crate::minimize_model_objectives`]).
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the minimizer.
    pub fn minimize_model_objectives(
        &self,
        arena: &mut TermArena,
        objectives: &[crate::ModelMinimizeObjective],
    ) -> Result<crate::ModelMinimizeOutcome, SolverError> {
        crate::minimize_model_objectives_with_config(
            arena,
            &self.assertions,
            objectives,
            &self.config,
        )
    }

    /// Lexicographic multi-objective optimization over the active assertions (see
    /// [`crate::optimize_lia_lexicographic`]).
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the optimizer.
    pub fn optimize_lexicographic(
        &self,
        arena: &mut TermArena,
        objectives: &[crate::LexObjective],
    ) -> Result<crate::LexOutcome, SolverError> {
        crate::optimize_lia_lexicographic(arena, &self.assertions, objectives)
    }

    /// Box (independent) multi-objective optimization over the active assertions
    /// (see [`crate::optimize_lia_box`]).
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the optimizer.
    pub fn optimize_box(
        &self,
        arena: &mut TermArena,
        objectives: &[crate::LexObjective],
    ) -> Result<Vec<crate::OptOutcome>, SolverError> {
        crate::optimize_lia_box(arena, &self.assertions, objectives)
    }

    /// Pareto-front multi-objective optimization over the active assertions (see
    /// [`crate::optimize_lia_pareto`]).
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the optimizer.
    pub fn optimize_pareto(
        &self,
        arena: &mut TermArena,
        objectives: &[crate::LexObjective],
    ) -> Result<crate::ParetoOutcome, SolverError> {
        crate::optimize_lia_pareto(arena, &self.assertions, objectives)
    }

    /// Lexicographic multi-objective optimization over **bit-vector** objectives
    /// (see [`crate::optimize_bv_lexicographic`]).
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the optimizer.
    pub fn optimize_lexicographic_bv(
        &self,
        arena: &mut TermArena,
        objectives: &[crate::BvLexObjective],
    ) -> Result<crate::LexOutcome, SolverError> {
        crate::optimize_bv_lexicographic_with_config(
            arena,
            &self.assertions,
            objectives,
            &self.config,
        )
    }

    /// Box (independent) multi-objective optimization over **bit-vector**
    /// objectives (see [`crate::optimize_bv_box`]).
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the optimizer.
    pub fn optimize_box_bv(
        &self,
        arena: &mut TermArena,
        objectives: &[crate::BvLexObjective],
    ) -> Result<Vec<crate::OptOutcome>, SolverError> {
        crate::optimize_bv_box_with_config(arena, &self.assertions, objectives, &self.config)
    }

    /// Pareto-front multi-objective optimization over **bit-vector** objectives
    /// (see [`crate::optimize_bv_pareto`]).
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the optimizer.
    pub fn optimize_pareto_bv(
        &self,
        arena: &mut TermArena,
        objectives: &[crate::BvLexObjective],
    ) -> Result<crate::ParetoOutcome, SolverError> {
        crate::optimize_bv_pareto_with_config(arena, &self.assertions, objectives, &self.config)
    }

    /// Maximizes the number of satisfied `soft` constraints subject to the active
    /// assertions (`MaxSAT`), returning the witnessing model (see
    /// [`crate::max_satisfiable_model`]).
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the optimizer.
    pub fn max_satisfiable(
        &self,
        arena: &mut TermArena,
        soft: &[TermId],
    ) -> Result<crate::MaxSatOutcome, SolverError> {
        crate::max_satisfiable_model(arena, &self.assertions, soft)
    }

    /// Checks the active assertions together with one-shot `assumptions`.
    ///
    /// The assumptions hold only for this check and are not retained, matching
    /// SMT-LIB `check-sat-assuming` semantics.
    ///
    /// On the warm route the assumptions become the engine's own one-shot SAT
    /// assumptions rather than assertions appended to a re-submitted stack, so
    /// nothing about them is retained past this call either.
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the backend.
    pub fn check_assuming(
        &mut self,
        arena: &TermArena,
        assumptions: &[TermId],
    ) -> Result<CheckResult, SolverError> {
        if assumptions.is_empty() {
            return self.check(arena);
        }
        if let Some(result) = self.warm_check(arena, assumptions) {
            return Ok(result);
        }
        self.warm_stats.cold_checks += 1;
        let mut terms = Vec::with_capacity(self.assertions.len() + assumptions.len());
        terms.extend_from_slice(&self.assertions);
        terms.extend_from_slice(assumptions);
        self.backend.check(arena, &terms, &self.config)
    }

    /// Layer-attributed measurements from the most recent check, if recorded.
    pub fn last_stats(&self) -> Option<&SolveStats> {
        self.backend.last_stats()
    }

    /// Consumes the façade and returns the wrapped backend.
    pub fn into_backend(self) -> B {
        self.backend
    }

    // -----------------------------------------------------------------------
    // The warm bit-vector route (roadmap item 1.1b)
    // -----------------------------------------------------------------------

    /// Counts describing how this solver's checks were decided; see
    /// [`WarmFacadeStats`].
    #[must_use]
    pub fn warm_facade_stats(&self) -> WarmFacadeStats {
        self.warm_stats
    }

    /// Whether a retained warm engine is currently live on this solver.
    #[must_use]
    pub fn warm_engine_live(&self) -> bool {
        matches!(self.warm, Warm::Live(_))
    }

    /// Tries to decide the active assertions (plus one-shot `assumptions`) on
    /// the retained warm engine.
    ///
    /// Returns `None` whenever the caller must fall back to `self.backend`. The
    /// fallback is not a nicety — it is what makes this routing verdict-neutral
    /// by construction. The warm engine's answer is used *only* when it is a
    /// `Sat` or `Unsat` verdict, so the change can turn an `Unknown` into a
    /// verdict but can never take one away, and an error still surfaces from the
    /// backend, with the backend's own message.
    fn warm_check(&mut self, arena: &TermArena, assumptions: &[TermId]) -> Option<CheckResult> {
        if matches!(self.warm, Warm::Off) {
            return None;
        }
        if matches!(self.warm, Warm::Idle) {
            // Decided once: neither the backend's identity nor `self.config` can
            // change without going through `set_config`, which resets this.
            if self.backend.capabilities().name != WARM_BV_BACKEND_NAME
                || !warm_config_is_honored(&self.config)
            {
                self.warm = Warm::Off;
                return None;
            }
            self.warm_stats.cold_restarts += 1;
            self.warm = Warm::Live(Box::new(WarmState {
                engine: IncrementalBvSolver::with_config(self.config.clone()),
                synced: vec![0],
                arena_len: arena.len(),
            }));
        }

        // Frame boundaries: façade frame `j` holds
        // `assertions[bounds[j]..bounds[j + 1]]`. `scopes` is non-decreasing and
        // bounded by `assertions.len()` (push records the current length, pop
        // truncates back to it), so these are ordered and in range.
        let mut bounds = Vec::with_capacity(self.scopes.len() + 2);
        bounds.push(0);
        bounds.extend_from_slice(&self.scopes);
        bounds.push(self.assertions.len());

        let outcome = {
            let Warm::Live(state) = &mut self.warm else {
                return None;
            };
            warm_sync_and_check(
                state,
                &mut self.warm_stats,
                arena,
                &self.assertions,
                &bounds,
                assumptions,
            )
        };
        match outcome {
            Some(result @ (CheckResult::Sat(_) | CheckResult::Unsat)) => {
                self.warm_stats.warm_checks += 1;
                Some(result)
            }
            // An `Unknown` or an error is never *used*: the backend re-decides
            // from `self.assertions`, which is still the single source of truth.
            // The engine is retired rather than retried, because an error may
            // have left a frame half-encoded and a repeated `Unknown` would pay
            // the same budget again on every later check.
            _ => {
                self.warm = Warm::Off;
                None
            }
        }
    }
}

/// The [`Capabilities::name`] the pure-Rust SAT-backed BV backend reports.
///
/// This is the *interim* way [`Solver`] asks "is my backend the pure-Rust BV
/// path, so that [`IncrementalBvSolver`] decides exactly the same queries by
/// exactly the same procedure?". The durable answer is a defaulted
/// `SolverBackend::warm_bv_engine_equivalent()` that returns `false` everywhere
/// except `SatBvBackend`; until that trait method exists, the backend's own
/// reported name is the only thing a generic `Solver<B>` can observe.
///
/// Getting this wrong can only *lose* the warm route, never change a verdict:
/// every warm outcome that is not a verdict falls back to the backend.
const WARM_BV_BACKEND_NAME: &str = "axeyum-sat-bv native-cdcl";

/// How [`Solver::check`] and [`Solver::check_assuming`] were decided.
///
/// These are counts rather than clocks on purpose: a wall-time comparison
/// cannot distinguish "the engine kept its encoding" from "the machine was
/// quieter this time".
///
/// The load-bearing field is [`Self::assertions_encoded`]. `n` checks over a
/// stack that grows by one assertion each time encode `n` assertions in total
/// on the warm route, against `n * (n + 1) / 2` when every check restarts cold —
/// so the count, unlike a monotone clause total, cannot look the same both ways.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct WarmFacadeStats {
    /// Checks answered by the retained [`IncrementalBvSolver`].
    pub warm_checks: u64,
    /// Checks answered by the wrapped [`SolverBackend`] — either because the
    /// warm route was never admissible, or because it declined this query.
    pub cold_checks: u64,
    /// How many times a *fresh* warm engine had to be built. One is the healthy
    /// value for a solver that stays on the warm route; every increment past
    /// that is an encoding thrown away and rebuilt from nothing.
    pub cold_restarts: u64,
    /// Assertions handed to the warm engine, counted once each. An assertion
    /// already in a live frame is never re-encoded, so this counts the delta
    /// synced at each check and not the active set.
    pub assertions_encoded: u64,
    /// Real scopes opened on the warm engine (a fresh SAT selector each).
    pub scope_pushes: u64,
    /// Real scopes closed on the warm engine.
    pub scope_pops: u64,
}

/// The warm engine's lifecycle inside the façade.
#[derive(Debug)]
enum Warm {
    /// Admissibility has not been decided yet; the engine is built lazily at
    /// the first check.
    Idle,
    /// A live engine whose frames mirror the façade's scopes.
    Live(Box<WarmState>),
    /// Warm routing is off for the rest of this solver's life. Reached by an
    /// inadmissible backend or configuration, by a query outside the warm
    /// fragment, and by any warm outcome that was not a verdict.
    Off,
}

/// A retained warm engine plus exactly enough bookkeeping to keep its frames in
/// lockstep with the façade's `assertions`/`scopes`.
#[derive(Debug)]
struct WarmState {
    engine: IncrementalBvSolver,
    /// `synced[j]` is how many of façade frame `j`'s assertions the engine has
    /// encoded. `synced.len()` is the engine's frame count (base frame
    /// included) and is invariantly `<= scopes.len() + 1`: [`Solver::pop`]
    /// closes engine frames eagerly, so a `push` after a `pop` can never land
    /// on a stale frame.
    synced: Vec<usize>,
    /// `arena.len()` at the last sync. The engine caches a lowering keyed by
    /// [`TermId`], so it is bound to one arena; a *shorter* arena is a different
    /// one and the engine must not be reused against it.
    arena_len: usize,
}

/// Syncs the façade's frames into the warm engine and runs one check.
///
/// Returns `None` for "declined, fall back" — including for a query outside the
/// warm fragment, which is rejected *before* anything is encoded so no partial
/// state is left behind.
fn warm_sync_and_check(
    state: &mut WarmState,
    stats: &mut WarmFacadeStats,
    arena: &TermArena,
    assertions: &[TermId],
    bounds: &[usize],
    assumptions: &[TermId],
) -> Option<CheckResult> {
    if arena.len() < state.arena_len {
        // A shorter arena than the one the retained lowering was built against:
        // the cached `TermId` → bit mapping no longer describes these terms.
        return None;
    }
    state.arena_len = arena.len();
    let frames = bounds.len() - 1;
    if state.synced.len() > frames {
        // The engine holds more frames than the façade has. `Solver::pop` closes
        // them eagerly, so this is unreachable; declining is the safe reaction.
        return None;
    }

    // Everything the engine does not already hold, pre-screened against exactly
    // the admission tests `SatBvBackend::check` applies. Screening the delta
    // (not the active set) keeps the incrementality win, and screening *before*
    // asserting is what makes the warm and cold routes accept the same queries:
    // a term either engine would refuse never reaches this one.
    let mut pending = Vec::new();
    for j in 0..frames {
        let lo = bounds[j];
        let hi = bounds[j + 1];
        let already = state.synced.get(j).copied().unwrap_or(0);
        if hi < lo || lo + already > hi {
            return None;
        }
        pending.extend_from_slice(&assertions[lo + already..hi]);
    }
    if !warm_fragment_admits(arena, &pending) || !warm_fragment_admits(arena, assumptions) {
        return None;
    }

    for j in 0..frames {
        if j >= state.synced.len() {
            state.engine.push().ok()?;
            state.synced.push(0);
            stats.scope_pushes += 1;
        }
        let lo = bounds[j];
        let hi = bounds[j + 1];
        while lo + state.synced[j] < hi {
            let term = assertions[lo + state.synced[j]];
            state.engine.assert(arena, term).ok()?;
            state.synced[j] += 1;
            stats.assertions_encoded += 1;
        }
    }

    let result = if assumptions.is_empty() {
        state.engine.check(arena)
    } else {
        state.engine.check_assuming(arena, assumptions)
    };
    result.ok()
}

/// Whether every term is one the pure-Rust BV path admits.
///
/// These are the *same* three tests `SatBvBackend::check` runs before it
/// bit-blasts — a non-Boolean root, an operator outside the lowering subset, a
/// sort the bit-blaster cannot represent. Arrays and uninterpreted functions
/// fail here exactly as they fail there; the warm engine would instead *defer*
/// them and refuse at check time with a different message, so screening first
/// keeps the backend's own error the one a caller sees.
fn warm_fragment_admits(arena: &TermArena, terms: &[TermId]) -> bool {
    terms.iter().all(|&t| arena.sort_of(t) == Sort::Bool)
        && axeyum_bv::first_unsupported_op(arena, terms).is_none()
        && axeyum_bv::first_unsupported_sort(arena, terms).is_none()
}

/// Whether every [`SolverConfig`] lever this solver sets is one the warm engine
/// actually reads.
///
/// [`IncrementalBvSolver`] consults `timeout`, `resource_limit`,
/// `incremental_positive_and_flattening` and `preprocess`, and **silently
/// ignores every other field** — measured, not assumed: no other field name
/// appears anywhere in `incremental.rs`. Routing a query that sets one of them
/// through the warm engine would quietly drop it, and `prove_unsat` alone makes
/// that a downgrade from a DRAT-checked refutation to an unchecked one. So the
/// warm route is refused unless each ignored lever is at its default.
///
/// The destructuring is exhaustive on purpose: a new `SolverConfig` field does
/// not compile until someone decides which side of this line it belongs on.
fn warm_config_is_honored(config: &SolverConfig) -> bool {
    let defaults = SolverConfig::default();
    let SolverConfig {
        // Read by the warm engine.
        timeout: _,
        resource_limit: _,
        incremental_positive_and_flattening: _,
        // Read by neither route: `SatBvBackend::check` does not consult
        // `preprocess` either (the auto-dispatcher does), and the warm route
        // asserts raw for the same reason, so the two agree.
        preprocess: _,
        // Ignored by the warm engine — each must be at its default.
        memory_limit_mb,
        node_budget,
        cnf_variable_budget,
        cnf_clause_budget,
        prove_unsat,
        cnf_inprocessing,
        cnf_vivify,
        profile_bit_demand,
        profile_cnf_construction,
        bit_lowering_mode,
        xor_cdcl_fallback,
        lazy_bv,
        lazy_bv_abstract_ite,
        native_cdcl,
        proof_progress: ref proof,
        check_progress: ref check,
    } = *config;
    memory_limit_mb == defaults.memory_limit_mb
        && node_budget == defaults.node_budget
        && cnf_variable_budget == defaults.cnf_variable_budget
        && cnf_clause_budget == defaults.cnf_clause_budget
        && prove_unsat == defaults.prove_unsat
        && cnf_inprocessing == defaults.cnf_inprocessing
        && cnf_vivify == defaults.cnf_vivify
        && profile_bit_demand == defaults.profile_bit_demand
        && profile_cnf_construction == defaults.profile_cnf_construction
        && bit_lowering_mode == defaults.bit_lowering_mode
        && xor_cdcl_fallback == defaults.xor_cdcl_fallback
        && lazy_bv == defaults.lazy_bv
        && lazy_bv_abstract_ite == defaults.lazy_bv_abstract_ite
        && native_cdcl == defaults.native_cdcl
        && proof.is_none()
        && check.is_none()
}

#[cfg(test)]
mod tests {
    use axeyum_ir::{Sort, TermArena};

    use crate::{CheckResult, ProofFragment, SatBvBackend, Solver};

    /// End-to-end on the façade: assert an UNSAT bit-vector query, confirm the
    /// backend decides `Unsat`, then reconstruct a kernel-checked Lean proof of it
    /// via [`Solver::prove_unsat_to_lean`] — the full solve → machine-checkable-proof
    /// flow on the public API.
    #[test]
    fn facade_solve_then_prove_unsat_to_lean() {
        let mut arena = TermArena::new();
        let a = {
            let s = arena.declare("a", Sort::BitVec(2)).unwrap();
            arena.var(s)
        };
        let b = {
            let s = arena.declare("b", Sort::BitVec(2)).unwrap();
            arena.var(s)
        };
        let sub = arena.bv_sub(a, b).unwrap(); // a - b
        let e1 = arena.eq(sub, a).unwrap(); // a - b = a  ⇒ b = 0
        let e2 = arena.bv_ult(a, b).unwrap(); // a < b, with b = 0 ⇒ a < 0, impossible

        let mut solver = Solver::new(SatBvBackend::new());
        solver.assert(e1);
        solver.assert(e2);
        assert!(matches!(solver.check(&arena).unwrap(), CheckResult::Unsat));

        let fragment = solver
            .prove_unsat_to_lean(&mut arena)
            .expect("the UNSAT bit-vector query reconstructs to a kernel-checked Lean `False`");
        assert_eq!(fragment, ProofFragment::TermLevelEnum);
    }

    /// The façade exposes optimization end-to-end: assert `0 ≤ x ≤ 7`, then
    /// `maximize_lia` over the active assertions → 7.
    #[test]
    fn facade_maximize_lia() {
        use crate::OptOutcome;

        let mut arena = TermArena::new();
        let x = {
            let s = arena.declare("x", Sort::Int).unwrap();
            arena.var(s)
        };
        let zero = arena.int_const(0);
        let seven = arena.int_const(7);
        let lo = arena.int_ge(x, zero).unwrap();
        let hi = arena.int_le(x, seven).unwrap();

        let mut solver = Solver::new(SatBvBackend::new());
        solver.assert(lo);
        solver.assert(hi);
        assert_eq!(
            solver.maximize_lia(&mut arena, x).unwrap(),
            OptOutcome::Optimal(7)
        );
    }
    /// The façade exposes unsat-core extraction: of three assertions where two
    /// conflict (`x=5`, `x=6`) plus an irrelevant one, the core is a subset that
    /// excludes the irrelevant assertion.
    #[test]
    fn facade_unsat_core() {
        let mut arena = TermArena::new();
        let x = {
            let s = arena.declare("x", Sort::BitVec(8)).unwrap();
            arena.var(s)
        };
        let five = arena.bv_const(8, 5).unwrap();
        let six = arena.bv_const(8, 6).unwrap();
        let y = {
            let s = arena.declare("y", Sort::BitVec(8)).unwrap();
            arena.var(s)
        };
        let one = arena.bv_const(8, 1).unwrap();
        let x5 = arena.eq(x, five).unwrap();
        let x6 = arena.eq(x, six).unwrap();
        let irrelevant = arena.eq(y, one).unwrap();

        let mut solver = Solver::new(SatBvBackend::new());
        solver.assert(x5);
        solver.assert(irrelevant);
        solver.assert(x6);
        let core = solver
            .unsat_core(&mut arena)
            .unwrap()
            .expect("the query is unsat, so it has a core");
        // The conflict is x5 (index 0) and x6 (index 2); index 1 (irrelevant) is out.
        assert!(core.contains(&0) && core.contains(&2));
        assert!(
            !core.contains(&1),
            "irrelevant assertion must not be in the core"
        );
    }
}
