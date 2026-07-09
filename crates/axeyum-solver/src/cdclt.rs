//! Generic online CDCL(T) driver (Track 1, P1.5 slice a).
//!
//! A CDCL search over the Boolean skeleton of a quantifier-free query where a
//! [`TheorySolver`] runs **online**: each trail assignment of a theory atom is
//! notified to the theory as it happens ([`TheorySolver::assert`]), theory
//! propagations are enqueued as implied literals carrying their theory-explained
//! reasons ([`TheorySolver::propagate`]), theory conflicts become learned clauses
//! via the explained core, and the theory is pushed/popped in lockstep with the
//! search's decision levels ([`TheorySolver::push`]/[`TheorySolver::pop`]).
//!
//! [`CdclT`] is parameterised over any `T: TheorySolver`. The same driver now serves
//! EUF, strings, pure LIA/LRA, and the live EUF+LIA/EUF+LRA combined theories; the
//! adapters retain responsibility for model construction and original-assertion replay.
//!
//! ## Conflict learning — 1-UIP over the mixed implication graph
//! Both Boolean input clauses and theory clauses (a theory conflict `¬⋀core` or a
//! theory propagation `¬reason ∨ lit`, both entailed by the theory alone) live in
//! one clause database and one implication graph. Conflict analysis is standard
//! **1-UIP** resolution against that mixed graph ([`CdclT::analyze_conflict`]) with
//! non-chronological backjumping. This is the full first cut, not the
//! restart-on-theory-conflict fallback: the theory reason clauses are small (an
//! e-graph `explain` core), so 1-UIP over them stays cheap and yields short
//! asserting clauses — the same scheme the already-validated embedded EUF loop uses.
//!
//! ## Soundness posture
//! - `Unsat` is returned only when 1-UIP derives the empty asserting clause at
//!   decision level 0 — a resolution refutation over input clauses and
//!   theory-entailed clauses. The theory clauses come from the *same* EUF
//!   explanation machinery ([`axeyum_egraph::EGraph::explain`], independently
//!   re-checked by [`axeyum_egraph::check_congruence`] on the offline route) that
//!   the landed `check_qf_uf` path already relies on; this slice adds **no new**
//!   unsat trust surface. Tests gate every online `Unsat` against the offline route.
//! - `Sat` is *not* trusted from the driver: the caller assembles a model from the
//!   theory and **replays** it against the original assertions, downgrading to
//!   `Unknown` on any non-replay.
//! - Deterministic: conflict-side VSIDS selects the highest-activity unassigned
//!   variable with lowest-index ties, phase saving reuses its last polarity, Luby
//!   restarts are a pure function of conflict count, and every search data
//!   structure is a `Vec`; there is no hash-iteration order or clock-derived
//!   choice. The only clock read is the deadline check.
//! - Deadline: `deadline` is checked at the head of the search loop and of the
//!   propagation fixpoint, so the search degrades to `Unknown` under a deterministic
//!   resource bound (the deadline-hole class is designed out).
//! - Step budget (defense in depth): the main [`CdclT::solve`] loop also counts its
//!   iterations against a [`CdclT::step_budget`] and degrades to [`Outcome::Unknown`]
//!   on exhaustion. The driver is provably terminating for a well-behaved theory —
//!   the trigger-literal invariant (every theory conflict carries a current-level
//!   literal) makes every conflict force a strict backjump, so learning cannot
//!   repeat a trail state — but the theories driven here are **incomplete and
//!   non-monotone** (`StringTheory` re-runs its refuter per assert and may report a
//!   conflict at assert *k* it missed at *k-1*). The step budget is the belt to the
//!   deadline's braces: when no deadline is configured (e.g. `wasm32`, or a
//!   `SolverConfig` with no timeout) it still guarantees the loop cannot spin
//!   forever on a pathological theory. Exhaustion is *sound* — `Unknown` is always a
//!   permitted verdict — never a wrong sat/unsat.

use std::time::Instant;

use crate::euf_egraph::{TheoryLit, TheorySolver};

/// A CNF literal in the online skeleton: a variable index and its polarity. The
/// first `eq_count` variables (see [`CdclT::new`]) are the theory atoms, numbered to
/// match the [`TheorySolver`]'s atom indices.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Lit {
    pub(crate) var: usize,
    pub(crate) positive: bool,
}

impl Lit {
    /// The literal over the same variable with flipped polarity.
    fn negate(self) -> Self {
        Self {
            var: self.var,
            positive: !self.positive,
        }
    }
}

/// The result of a CDCL(T) search.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Outcome {
    /// The skeleton is UNSAT under the theory (a resolution refutation reached the
    /// empty clause at level 0).
    Unsat,
    /// A Boolean- and theory-consistent total assignment was reached; the theory is
    /// left in that satisfying state for the caller to build a model from.
    Sat,
    /// The deadline elapsed before the search closed (a deterministic give-up).
    Unknown,
}

/// How a variable came to be assigned, so backtracking can undo theory state in
/// lockstep with decisions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Cause {
    /// A branching decision; its level owns a matching theory `push`.
    Decision,
    /// Forced by unit propagation, a theory propagation, or a learned unit.
    Implied,
}

/// A conflict surfaced by propagation: the falsified clause to analyse, tagged with
/// whether it is a theory clause (entailed by the theory alone) so the theory-lemma
/// provenance can be tracked through 1-UIP resolution.
struct Conflict {
    clause: Vec<Lit>,
    is_theory: bool,
}

/// Defense-in-depth ceiling on [`CdclT::solve`] main-loop iterations when no
/// deadline is configured. The driver is terminating for a well-behaved theory;
/// this bound only bites on a pathological non-monotone theory that would
/// otherwise spin. It is deliberately large — orders of magnitude beyond what any
/// skeleton this driver receives today needs — so a legitimate search is never
/// capped, yet a true livelock still ends (in bounded, if large, time) as a sound
/// `Unknown`. Callers with a real problem should also set `config.timeout`, which
/// is the primary bound.
const DEFAULT_STEP_BUDGET: usize = 16_000_000;

/// VSIDS activity decay. Growing the bump increment by `1 / VSIDS_DECAY`
/// makes recent conflicts weigh more without scanning every activity.
const VSIDS_DECAY: f64 = 0.95;
/// Common rescale factor used before activity values approach floating-point
/// overflow. Multiplying every value preserves the decision order.
const VSIDS_RESCALE: f64 = 1e-100;
/// Activity ceiling that triggers a common rescale.
const VSIDS_RESCALE_LIMIT: f64 = 1e100;

/// Conflict interval unit multiplied by the current Luby value. The production
/// schedule matches the arithmetic-local and proof-producing CDCL engines.
const LUBY_UNIT: usize = 100;

/// The 1-indexed Luby sequence `1,1,2,1,1,2,4,...` in reluctant-doubling form.
fn luby(mut index: u64) -> u64 {
    let mut exponent = 1_u64;
    loop {
        let power = 1_u64 << exponent;
        if index == power - 1 {
            return 1_u64 << (exponent - 1);
        }
        let half = 1_u64 << (exponent - 1);
        if half <= index && index < power - 1 {
            index = index - half + 1;
            exponent = 1;
        } else {
            exponent += 1;
        }
    }
}

/// The outcome of one conflict-learning step.
enum Learn {
    /// The asserting clause was learned and the UIP enqueued; keep searching.
    Continue,
    /// The conflict was implied at level 0: UNSAT.
    Unsat,
}

/// A generic online CDCL(T) search over a CNF skeleton, driving any
/// [`TheorySolver`] online with 1-UIP theory-conflict learning, theory propagation,
/// non-chronological backjumping, and deadline-bounded termination.
pub(crate) struct CdclT {
    var_count: usize,
    /// The first `eq_count` variables are theory atoms mirrored into the theory.
    eq_count: usize,
    clauses: Vec<Vec<Lit>>,
    /// Current value per variable (`None` if unassigned).
    value: Vec<Option<bool>>,
    /// Trail of `(var, value, cause)` in assignment order.
    trail: Vec<(usize, bool, Cause)>,
    /// Per variable: the decision level it was assigned at (valid while assigned).
    level: Vec<usize>,
    /// Per variable: the reason clause that forced it (`None` for a decision).
    reason: Vec<Option<Vec<Lit>>>,
    /// Per variable: whether its reason clause is a theory clause. A 1-UIP clause
    /// resolved only through theory clauses is itself a theory lemma.
    reason_theory: Vec<bool>,
    /// Current decision level.
    decision_level: usize,
    /// When set, the search returns [`Outcome::Unknown`] once the deadline passes.
    deadline: Option<Instant>,
    /// Defense-in-depth ceiling on main-loop iterations (see
    /// [`DEFAULT_STEP_BUDGET`]); the search degrades to [`Outcome::Unknown`] when
    /// [`Self::steps`] reaches it.
    step_budget: usize,
    /// Main-loop iterations taken so far (telemetry + the step-budget counter).
    steps: usize,
    /// Set once the step budget was exhausted, so a caller/test can distinguish a
    /// budget-driven `Unknown` from a deadline- or fixpoint-driven one.
    step_budget_hit: bool,
    /// Number of literals assigned by theory propagation. Internal telemetry for
    /// routing/tests; decisions and Boolean unit propagation are not counted.
    theory_propagations: usize,
    /// VSIDS activity per variable. Conflict analysis bumps each variable when it
    /// first enters the conflict side; decisions choose the maximum activity with
    /// deterministic lowest-index ties.
    activity: Vec<f64>,
    /// Current VSIDS bump increment. It grows once per conflict so old activity
    /// decays relative to newly implicated variables.
    var_inc: f64,
    /// Last assigned polarity per variable. Initialized to the previous
    /// true-first behavior and retained across backtracking.
    saved_phase: Vec<bool>,
    /// Conflicts analyzed since the last restart.
    conflicts_since_restart: usize,
    /// 1-indexed position in the Luby schedule. The completed restart count is
    /// `restart_index - 1`.
    restart_index: u64,
    /// Test-only restart-unit override used to force or disable restarts on small
    /// deterministic fixtures.
    #[cfg(test)]
    restart_unit_override: Option<usize>,
}

impl CdclT {
    /// Builds a search over `clauses` on `var_count` variables, of which the first
    /// `eq_count` are theory atoms (their indices align with the [`TheorySolver`]).
    /// `deadline`, when set, bounds the search.
    pub(crate) fn new(
        var_count: usize,
        eq_count: usize,
        clauses: Vec<Vec<Lit>>,
        deadline: Option<Instant>,
    ) -> Self {
        Self {
            var_count,
            eq_count,
            clauses,
            value: vec![None; var_count],
            trail: Vec::new(),
            level: vec![0; var_count],
            reason: vec![None; var_count],
            reason_theory: vec![false; var_count],
            decision_level: 0,
            deadline,
            step_budget: DEFAULT_STEP_BUDGET,
            steps: 0,
            step_budget_hit: false,
            theory_propagations: 0,
            activity: vec![0.0; var_count],
            var_inc: 1.0,
            saved_phase: vec![true; var_count],
            conflicts_since_restart: 0,
            restart_index: 1,
            #[cfg(test)]
            restart_unit_override: None,
        }
    }

    /// Overrides the defense-in-depth step budget (see [`DEFAULT_STEP_BUDGET`]).
    /// Used by the non-monotone-theory property tests to detect a livelock with a
    /// tight, deterministic ceiling; production uses the generous default.
    #[cfg(test)]
    pub(crate) fn with_step_budget(mut self, budget: usize) -> Self {
        self.step_budget = budget;
        self
    }

    /// Overrides the Luby schedule unit for a deterministic restart test.
    #[cfg(test)]
    fn with_restart_unit(mut self, unit: usize) -> Self {
        self.restart_unit_override = Some(unit);
        self
    }

    /// Number of completed restarts.
    #[cfg(test)]
    fn restarts(&self) -> u64 {
        self.restart_index - 1
    }

    /// Whether the last [`Self::solve`] ended by exhausting the step budget (rather
    /// than the deadline or a real verdict).
    #[cfg(test)]
    pub(crate) fn step_budget_hit(&self) -> bool {
        self.step_budget_hit
    }

    /// Number of literals assigned by theory propagation during the last solve.
    pub(crate) fn theory_propagations(&self) -> usize {
        self.theory_propagations
    }

    /// The current value of `var` (for the caller's model-assembly injection path).
    pub(crate) fn value(&self, var: usize) -> Option<bool> {
        self.value[var]
    }

    /// Whether the deadline (if any) has elapsed.
    fn timed_out(&self) -> bool {
        self.deadline.is_some_and(|d| Instant::now() >= d)
    }

    fn lit_sat(&self, lit: Lit) -> Option<bool> {
        self.value[lit.var].map(|v| v == lit.positive)
    }

    /// The literal currently true for `var` (its trail polarity).
    fn true_literal(&self, var: usize) -> Lit {
        Lit {
            var,
            positive: self.value[var].expect("assigned variable has a value"),
        }
    }

    /// Assigns `var := value` at the current decision level, recording its level and
    /// reason and mirroring a theory atom into the theory. Returns the theory
    /// conflict core if the assertion is inconsistent.
    fn assign<T: TheorySolver>(
        &mut self,
        theory: &mut T,
        var: usize,
        value: bool,
        cause: Cause,
        reason: Option<Vec<Lit>>,
        reason_is_theory: bool,
    ) -> Result<(), Vec<TheoryLit>> {
        self.value[var] = Some(value);
        self.saved_phase[var] = value;
        self.level[var] = self.decision_level;
        self.reason[var] = reason;
        self.reason_theory[var] = reason_is_theory;
        self.trail.push((var, value, cause));
        if var < self.eq_count {
            theory.assert(var, value)?;
        }
        Ok(())
    }

    /// Boolean unit propagation to fixpoint. Returns a falsified conflict clause on a
    /// Boolean conflict, or a learned theory-conflict clause on a forced theory
    /// inconsistency (tagged accordingly).
    fn unit_propagate<T: TheorySolver>(&mut self, theory: &mut T) -> Result<(), Conflict> {
        let mut changed = true;
        while changed {
            changed = false;
            for ci in 0..self.clauses.len() {
                let mut unassigned: Option<Lit> = None;
                let mut satisfied = false;
                let mut count = 0;
                for &lit in &self.clauses[ci] {
                    match self.lit_sat(lit) {
                        Some(true) => {
                            satisfied = true;
                            break;
                        }
                        Some(false) => {}
                        None => {
                            unassigned = Some(lit);
                            count += 1;
                        }
                    }
                }
                if satisfied {
                    continue;
                }
                if count == 0 {
                    return Err(Conflict {
                        clause: self.clauses[ci].clone(),
                        is_theory: false,
                    });
                }
                if count == 1 {
                    let lit = unassigned.expect("count == 1 has the unit literal");
                    let reason = self.clauses[ci].clone();
                    if let Err(core) = self.assign(
                        theory,
                        lit.var,
                        lit.positive,
                        Cause::Implied,
                        Some(reason),
                        false,
                    ) {
                        return Err(Conflict {
                            clause: Self::theory_conflict_clause(&core),
                            is_theory: true,
                        });
                    }
                    changed = true;
                }
            }
        }
        Ok(())
    }

    /// Applies sound theory propagations to the trail until fixpoint. Returns the
    /// learned theory-conflict clause on a theory conflict, else `Ok(())`.
    fn theory_propagate<T: TheorySolver>(&mut self, theory: &mut T) -> Result<(), Conflict> {
        loop {
            let props = theory.propagate();
            let mut progress = false;
            for prop in props {
                let var = prop.lit.atom;
                match self.value[var] {
                    Some(v) if v == prop.lit.value => {}
                    Some(_) => {
                        // The theory entails the opposite of the current value: learn
                        // ¬(reason ∧ current literal).
                        let mut core = prop.reason.clone();
                        core.push(TheoryLit {
                            atom: var,
                            value: !prop.lit.value,
                        });
                        return Err(Conflict {
                            clause: Self::theory_conflict_clause(&core),
                            is_theory: true,
                        });
                    }
                    None => {
                        let reason_clause = Self::theory_reason_clause(&prop.reason, prop.lit);
                        if let Err(c) = self.assign(
                            theory,
                            var,
                            prop.lit.value,
                            Cause::Implied,
                            Some(reason_clause),
                            true,
                        ) {
                            return Err(Conflict {
                                clause: Self::theory_conflict_clause(&c),
                                is_theory: true,
                            });
                        }
                        self.theory_propagations += 1;
                        progress = true;
                    }
                }
            }
            if !progress {
                return Ok(());
            }
        }
    }

    /// Maps a theory conflict core to the learned CNF conflict clause `¬⋀core` (every
    /// literal currently false, so it is the falsified clause to analyse).
    fn theory_conflict_clause(core: &[TheoryLit]) -> Vec<Lit> {
        core.iter()
            .map(|l| Lit {
                var: l.atom,
                positive: !l.value,
            })
            .collect()
    }

    /// The reason clause for a theory propagation `reason ⊨ lit`, namely
    /// `¬(reason) ∨ lit`. Once every reason literal is asserted, this clause is unit
    /// and forces `lit` — the invariant [`Self::analyze_conflict`] relies on.
    fn theory_reason_clause(reason: &[TheoryLit], lit: TheoryLit) -> Vec<Lit> {
        let mut clause: Vec<Lit> = reason
            .iter()
            .map(|l| Lit {
                var: l.atom,
                positive: !l.value,
            })
            .collect();
        clause.push(Lit {
            var: lit.atom,
            positive: lit.value,
        });
        clause
    }

    /// 1-UIP conflict analysis over the mixed (Boolean + theory) implication graph.
    /// Resolves the falsified `conflict` clause against the reason clauses of
    /// current-level literals (newest-first on the trail) until a single current-level
    /// literal — the first UIP — remains. Returns the asserting clause (UIP at index
    /// 0, lower-level literals after), the backjump level, and whether the clause is a
    /// pure theory lemma (resolved through theory clauses only).
    fn analyze_conflict(
        &mut self,
        conflict: &[Lit],
        seed_is_theory: bool,
    ) -> (Vec<Lit>, usize, bool) {
        let mut seen = vec![false; self.var_count];
        let mut lower: Vec<Lit> = Vec::new();
        let mut path_count = 0_usize;
        let mut pivot: Option<usize> = None;
        let mut index = self.trail.len();
        let current = self.decision_level;
        let mut all_theory = seed_is_theory;
        let mut clause: Vec<Lit> = conflict.to_vec();

        loop {
            for lit in &clause {
                let v = lit.var;
                if Some(v) == pivot || seen[v] || self.level[v] == 0 {
                    continue;
                }
                seen[v] = true;
                self.bump_var(v);
                if self.level[v] >= current {
                    path_count += 1;
                } else {
                    lower.push(*lit);
                }
            }

            let mut found = false;
            while index > 0 {
                index -= 1;
                if seen[self.trail[index].0] {
                    found = true;
                    break;
                }
            }
            if !found {
                // Implied at level 0: the empty asserting clause (UNSAT).
                return (Vec::new(), 0, all_theory);
            }

            let var = self.trail[index].0;
            seen[var] = false;
            path_count -= 1;
            pivot = Some(var);

            if path_count == 0 {
                let mut learned = Vec::with_capacity(lower.len() + 1);
                learned.push(self.true_literal(var).negate());
                learned.extend(lower);
                let backjump = Self::backjump_level(&self.level, &learned);
                return (learned, backjump, all_theory);
            }

            all_theory = all_theory && self.reason_theory[var];
            clause.clone_from(
                self.reason[var]
                    .as_ref()
                    .expect("a current-level implied literal has a reason clause"),
            );
        }
    }

    /// The backjump level: the second-highest decision level among the clause's
    /// literals (the asserting literal at index 0 sits at the highest level), or `0`
    /// for a unit asserting clause.
    fn backjump_level(level: &[usize], learned: &[Lit]) -> usize {
        learned
            .iter()
            .skip(1)
            .map(|lit| level[lit.var])
            .max()
            .unwrap_or(0)
    }

    /// Backjumps to `target_level`: pops every trail entry strictly above it,
    /// unassigning each variable and popping the theory once per decision crossed (it
    /// was pushed once per decision, keeping the push/pop stack in lockstep).
    fn backjump_to<T: TheorySolver>(&mut self, theory: &mut T, target_level: usize) {
        while let Some(&(var, _, _)) = self.trail.last() {
            if self.level[var] <= target_level {
                break;
            }
            let (var, _, cause) = self.trail.pop().expect("non-empty trail");
            self.value[var] = None;
            self.reason[var] = None;
            self.reason_theory[var] = false;
            if cause == Cause::Decision {
                theory.pop();
            }
        }
        self.decision_level = target_level;
    }

    /// The highest-activity unassigned variable, with deterministic lowest-index
    /// ties, or `None` when the assignment is total.
    fn pick_unassigned(&self) -> Option<usize> {
        let mut best = None;
        for var in 0..self.var_count {
            if self.value[var].is_some() {
                continue;
            }
            match best {
                None => best = Some(var),
                Some(current) if self.activity[var] > self.activity[current] => {
                    best = Some(var);
                }
                Some(_) => {}
            }
        }
        best
    }

    /// Bumps one variable's VSIDS activity, rescaling all activities by the same
    /// positive factor before they can overflow. Rescaling preserves ordering.
    fn bump_var(&mut self, var: usize) {
        self.activity[var] += self.var_inc;
        if self.activity[var] > VSIDS_RESCALE_LIMIT {
            for activity in &mut self.activity {
                *activity *= VSIDS_RESCALE;
            }
            self.var_inc *= VSIDS_RESCALE;
        }
    }

    /// Advances the VSIDS recency window after one analyzed conflict.
    fn decay_activity(&mut self) {
        self.var_inc /= VSIDS_DECAY;
    }

    /// Number of conflicts allowed in the current restart interval. Saturation
    /// turns unreachable arithmetic overflow into a delayed restart, never a
    /// spuriously early one.
    fn restart_limit(&self) -> usize {
        #[cfg(test)]
        let unit = self.restart_unit_override.unwrap_or(LUBY_UNIT);
        #[cfg(not(test))]
        let unit = LUBY_UNIT;
        usize::try_from(luby(self.restart_index))
            .unwrap_or(usize::MAX)
            .saturating_mul(unit)
    }

    /// Unit propagation interleaved with theory propagation to a joint fixpoint.
    /// Returns `Ok(())` early (not at fixpoint) when the deadline elapses so the
    /// caller's loop can turn it into [`Outcome::Unknown`].
    fn propagate<T: TheorySolver>(&mut self, theory: &mut T) -> Result<(), Conflict> {
        loop {
            if self.timed_out() {
                return Ok(());
            }
            self.unit_propagate(theory)?;
            let before = self.trail.len();
            self.theory_propagate(theory)?;
            if self.trail.len() == before {
                return Ok(());
            }
        }
    }

    /// Handles a conflict by 1-UIP analysis: learns the asserting clause, jumps
    /// non-chronologically to the backjump level, and enqueues the UIP literal as an
    /// implied assignment with the learned clause as its reason. Returns
    /// [`Learn::Unsat`] when the conflict is implied at level 0.
    fn learn_and_backjump<T: TheorySolver>(
        &mut self,
        theory: &mut T,
        conflict: &Conflict,
    ) -> Learn {
        let (learned, backjump, is_theory_lemma) =
            self.analyze_conflict(&conflict.clause, conflict.is_theory);
        self.decay_activity();
        self.conflicts_since_restart += 1;
        if learned.is_empty() {
            return Learn::Unsat;
        }
        self.backjump_to(theory, backjump);
        let uip = learned[0];
        let reason = if learned.len() == 1 {
            None
        } else {
            Some(learned.clone())
        };
        self.clauses.push(learned);
        // Enqueue the UIP literal. Its theory assertion is consistent at the backjump
        // level (the asserting clause is an entailed resolvent), but a theory conflict
        // can still surface — re-analyse it. The learned clause is the UIP's reason,
        // a theory clause iff it is a theory lemma.
        match self.assign(
            theory,
            uip.var,
            uip.positive,
            Cause::Implied,
            reason,
            is_theory_lemma,
        ) {
            Ok(()) => Learn::Continue,
            Err(core) => self.learn_and_backjump(
                theory,
                &Conflict {
                    clause: Self::theory_conflict_clause(&core),
                    is_theory: true,
                },
            ),
        }
    }

    /// Runs the CDCL(T) search over the theory. Returns [`Outcome::Unsat`] on a
    /// refutation, [`Outcome::Sat`] on a Boolean- and theory-consistent total
    /// assignment (the theory is left in that state), or [`Outcome::Unknown`] on
    /// deadline.
    pub(crate) fn solve<T: TheorySolver>(&mut self, theory: &mut T) -> Outcome {
        loop {
            // Defense in depth against a non-monotone-theory livelock: bound the
            // main-loop iterations even with no deadline. Sound — `Unknown` is a
            // permitted verdict — never a wrong sat/unsat.
            if self.steps >= self.step_budget {
                self.step_budget_hit = true;
                return Outcome::Unknown;
            }
            self.steps += 1;
            if self.timed_out() {
                return Outcome::Unknown;
            }
            match self.propagate(theory) {
                Ok(()) => {}
                Err(conflict) => match self.learn_and_backjump(theory, &conflict) {
                    Learn::Unsat => return Outcome::Unsat,
                    Learn::Continue => continue,
                },
            }
            if self.timed_out() {
                return Outcome::Unknown;
            }
            if self.decision_level > 0 && self.conflicts_since_restart >= self.restart_limit() {
                self.backjump_to(theory, 0);
                self.conflicts_since_restart = 0;
                self.restart_index += 1;
                continue;
            }
            match self.pick_unassigned() {
                None => return Outcome::Sat,
                Some(var) => {
                    self.decision_level += 1;
                    theory.push();
                    let polarity = self.saved_phase[var];
                    if let Err(core) =
                        self.assign(theory, var, polarity, Cause::Decision, None, false)
                    {
                        let conflict = Conflict {
                            clause: Self::theory_conflict_clause(&core),
                            is_theory: true,
                        };
                        if let Learn::Unsat = self.learn_and_backjump(theory, &conflict) {
                            return Outcome::Unsat;
                        }
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod termination_tests {
    //! Termination + soundness of the generic [`CdclT`] driver under an
    //! **adversarial, non-monotone** theory (DEBT 1 of the default-on verification
    //! debt paydown).
    //!
    //! [`MockTheory`] is a deliberately hostile [`TheorySolver`]: its *truth* is a
    //! fixed set of forbidden cubes (a partial assignment the theory has no model
    //! for — so `¬cube` is a valid theory lemma), but its *reporting* is
    //! non-monotone — on a **partial** assignment it may report a contained cube,
    //! skip one it could report (miss), flip-flop, or report a superset core,
    //! mirroring how the real [`crate::string_theory::StringTheory`] re-runs an
    //! incomplete refuter per assert. It is **complete on total assignments** (when
    //! every atom is assigned it always reports a contained cube), and it always
    //! folds the current-decision-level trigger literal into the core — exactly the
    //! `c9d332c1` trigger-literal invariant the driver's 1-UIP analysis relies on.
    //!
    //! The property: over thousands of random instances the driver must (a)
    //! **terminate** without tripping the step budget (no livelock), and (b) return
    //! a verdict that matches an independent brute-force over the Boolean skeleton ∧
    //! the forbidden-cube semantics — a wrong `Sat`/`Unsat` is a hard failure.

    use super::{Cause, CdclT, Lit, Outcome, luby};
    use crate::euf_egraph::{TheoryLit, TheoryProp, TheorySolver};

    /// A deterministic linear-congruential PRNG (MMIX constants) — the house
    /// convention; no clock, no entropy, fully reproducible per seed.
    struct Lcg(u64);

    impl Lcg {
        fn new(seed: u64) -> Self {
            Lcg(seed
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407)
                .wrapping_add(0x9E37_79B9_7F4A_7C15))
        }
        fn next_u64(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            self.0
        }
        fn below(&mut self, n: usize) -> usize {
            usize::try_from(self.next_u64() % (n as u64)).expect("modulus fits usize")
        }
        fn coin(&mut self) -> bool {
            self.next_u64() & 1 == 1
        }
    }

    /// How the mock decides, on a **partial** assignment, whether to report a
    /// contained forbidden cube. All variants stay sound (every reported core is a
    /// genuine ¬cube lemma); they differ only in *when* they fire, so the driver
    /// meets a hostile, non-monotone conflict schedule.
    #[derive(Clone, Copy)]
    enum Mode {
        /// Report on every partial assert where a cube is contained (eager).
        Always,
        /// Never report on a partial assignment — only at a total one (maximally
        /// late; the driver reaches full models before the theory ever speaks).
        OnlyTotal,
        /// Report only on every `k`-th qualifying assert (periodic miss).
        Periodic(u64),
        /// Alternate report / skip on successive qualifying asserts (flip-flop).
        FlipFlop,
    }

    /// The adversarial non-monotone theory. `forbidden` fixes its semantics; the
    /// reporting schedule (`mode`) is hostile but never unsound.
    struct MockTheory {
        n: usize,
        forbidden: Vec<Vec<(usize, bool)>>,
        mode: Mode,
        /// Whether the core should be padded to a superset of a genuine cube (still
        /// sound). Independent of `mode`.
        report_superset: bool,
        /// Per atom: currently-asserted value (`None` if unassigned).
        assigned: Vec<Option<bool>>,
        /// Number of atoms currently assigned (for the total-assignment test).
        assigned_count: usize,
        /// Atoms assigned since the start, in order — the backtrack log.
        assigned_log: Vec<usize>,
        /// Backtrack trail: per `push`, the `assigned_log` length.
        trail: Vec<usize>,
        /// Count of qualifying (cube-contained) partial asserts, driving the
        /// periodic / flip-flop schedules.
        qualifying: u64,
    }

    impl MockTheory {
        fn new(n: usize, forbidden: Vec<Vec<(usize, bool)>>, mode: Mode, superset: bool) -> Self {
            Self {
                n,
                forbidden,
                mode,
                report_superset: superset,
                assigned: vec![None; n],
                assigned_count: 0,
                assigned_log: Vec::new(),
                trail: Vec::new(),
                qualifying: 0,
            }
        }

        /// Whether every literal of `cube` is currently asserted with the matching
        /// value (the cube is contained in the current assignment).
        fn contains_cube(&self, cube: &[(usize, bool)]) -> bool {
            cube.iter().all(|&(a, v)| self.assigned[a] == Some(v))
        }

        /// The first contained forbidden cube, if any.
        fn contained_cube(&self) -> Option<&Vec<(usize, bool)>> {
            self.forbidden.iter().find(|c| self.contains_cube(c))
        }

        /// Builds a genuine theory-conflict core from `cube`: its literals, plus (in
        /// superset mode) every currently-asserted literal, plus the current-level
        /// `trigger` literal (the `c9d332c1` invariant). Every literal is genuinely
        /// asserted, so `¬core` is entailed by `¬cube` — a sound lemma.
        fn core_from(&self, cube: &[(usize, bool)], trigger: (usize, bool)) -> Vec<TheoryLit> {
            let mut core: Vec<TheoryLit> = Vec::new();
            let push_lit = |core: &mut Vec<TheoryLit>, atom: usize, value: bool| {
                if !core.iter().any(|l| l.atom == atom) {
                    core.push(TheoryLit { atom, value });
                }
            };
            for &(a, v) in cube {
                push_lit(&mut core, a, v);
            }
            if self.report_superset {
                for &a in &self.assigned_log {
                    if let Some(v) = self.assigned[a] {
                        push_lit(&mut core, a, v);
                    }
                }
            }
            // Always carry the just-asserted current-level literal, so the driver's
            // 1-UIP analysis always finds a current-level literal to resolve on.
            push_lit(&mut core, trigger.0, trigger.1);
            core
        }
    }

    impl TheorySolver for MockTheory {
        fn assert(&mut self, atom: usize, value: bool) -> Result<(), Vec<TheoryLit>> {
            if self.assigned[atom].is_none() {
                self.assigned[atom] = Some(value);
                self.assigned_count += 1;
                self.assigned_log.push(atom);
            }
            let trigger = (atom, value);
            // A total assignment: the mock is COMPLETE here — always report a
            // contained cube, so the driver never accepts a theory-inconsistent model.
            let total = self.assigned_count == self.n;
            let Some(cube) = self.contained_cube().cloned() else {
                return Ok(());
            };
            if total {
                return Err(self.core_from(&cube, trigger));
            }
            // Partial: hostile, non-monotone schedule — but every fired core is sound.
            self.qualifying += 1;
            let fire = match self.mode {
                Mode::Always => true,
                Mode::OnlyTotal => false,
                Mode::Periodic(k) => self.qualifying.is_multiple_of(k),
                Mode::FlipFlop => self.qualifying.is_multiple_of(2),
            };
            if fire {
                Err(self.core_from(&cube, trigger))
            } else {
                Ok(())
            }
        }

        fn push(&mut self) {
            self.trail.push(self.assigned_log.len());
        }

        fn pop(&mut self) {
            if let Some(mark) = self.trail.pop() {
                while self.assigned_log.len() > mark {
                    if let Some(atom) = self.assigned_log.pop() {
                        self.assigned[atom] = None;
                        self.assigned_count -= 1;
                    }
                }
            }
        }

        fn propagate(&self) -> Vec<TheoryProp> {
            // Like the real StringTheory: no theory propagation this model.
            Vec::new()
        }
    }

    /// A generated instance: `n` atoms (all driver variables are theory atoms),
    /// CNF `clauses` over them, and the theory's forbidden cubes.
    struct Instance {
        n: usize,
        clauses: Vec<Vec<Lit>>,
        forbidden: Vec<Vec<(usize, bool)>>,
    }

    fn gen_instance(rng: &mut Lcg) -> Instance {
        let n = 1 + rng.below(6); // 1..=6 atoms
        let m = rng.below(2 * n + 1); // 0..=2n clauses
        let mut clauses = Vec::with_capacity(m);
        for _ in 0..m {
            let width = 1 + rng.below(3); // 1..=3 literals
            let mut clause = Vec::with_capacity(width);
            for _ in 0..width {
                let var = rng.below(n);
                let positive = rng.coin();
                if !clause.iter().any(|l: &Lit| l.var == var) {
                    clause.push(Lit { var, positive });
                }
            }
            clauses.push(clause);
        }
        let f = rng.below(n + 1); // 0..=n forbidden cubes
        let mut forbidden = Vec::with_capacity(f);
        for _ in 0..f {
            let width = 1 + rng.below(3); // 1..=3 literals
            let mut cube: Vec<(usize, bool)> = Vec::with_capacity(width);
            for _ in 0..width {
                let atom = rng.below(n);
                let value = rng.coin();
                // A cube with contradictory literals on one atom can never be
                // contained; drop the duplicate to keep cubes meaningful.
                if !cube.iter().any(|&(a, _)| a == atom) {
                    cube.push((atom, value));
                }
            }
            if !cube.is_empty() {
                forbidden.push(cube);
            }
        }
        Instance {
            n,
            clauses,
            forbidden,
        }
    }

    /// Whether `assignment` (bit `i` = value of atom `i`) satisfies every clause.
    fn sat_clauses(clauses: &[Vec<Lit>], assignment: u32) -> bool {
        clauses.iter().all(|clause| {
            clause
                .iter()
                .any(|l| ((assignment >> l.var) & 1 == 1) == l.positive)
        })
    }

    /// Whether `assignment` contains no forbidden cube (theory-consistent).
    fn theory_consistent(forbidden: &[Vec<(usize, bool)>], assignment: u32) -> bool {
        !forbidden
            .iter()
            .any(|cube| cube.iter().all(|&(a, v)| ((assignment >> a) & 1 == 1) == v))
    }

    /// Independent brute force over all `2^n` total assignments: `true` iff some
    /// assignment satisfies every clause and avoids every forbidden cube.
    fn brute_force_sat(inst: &Instance) -> bool {
        (0u32..(1u32 << inst.n))
            .any(|a| sat_clauses(&inst.clauses, a) && theory_consistent(&inst.forbidden, a))
    }

    /// Drives one instance through [`CdclT`] under `mode`/`superset`, with a tight
    /// step budget so a livelock trips it deterministically rather than hanging.
    fn run_once(inst: &Instance, mode: Mode, superset: bool) -> (Outcome, CdclT) {
        // A step ceiling far above any legitimate run on <=6 atoms (whose full CDCL
        // search is at most a few thousand steps) but finite — a true livelock trips
        // it and the test asserts it was NOT tripped.
        const TEST_STEP_BUDGET: usize = 200_000;
        let mut solver = CdclT::new(inst.n, inst.n, inst.clauses.clone(), None)
            .with_step_budget(TEST_STEP_BUDGET);
        let mut theory = MockTheory::new(inst.n, inst.forbidden.clone(), mode, superset);
        let outcome = solver.solve(&mut theory);
        (outcome, solver)
    }

    #[test]
    fn non_monotone_theory_terminates_and_is_sound() {
        // Every mode × superset-flag combination, over a large random sweep.
        let modes = [
            Mode::Always,
            Mode::OnlyTotal,
            Mode::Periodic(2),
            Mode::Periodic(3),
            Mode::FlipFlop,
        ];
        let mut runs = 0u64;
        let mut sat = 0u64;
        let mut unsat = 0u64;
        // 2000 base instances × 10 (mode × superset) schedules = 20_000 driver runs.
        for seed in 0..2000u64 {
            let mut rng = Lcg::new(seed);
            let inst = gen_instance(&mut rng);
            let truth = brute_force_sat(&inst);
            for &mode in &modes {
                for &superset in &[false, true] {
                    let (outcome, solver) = run_once(&inst, mode, superset);
                    runs += 1;

                    // (1) Termination: the driver must decide by its own logic, never
                    // by exhausting the step budget — a trip is a livelock.
                    assert!(
                        !solver.step_budget_hit(),
                        "LIVELOCK seed={seed} n={} mode-idx step-budget exhausted \
                         (took {} steps) — the non-monotone driver did not terminate",
                        inst.n,
                        solver.steps,
                    );
                    // With no deadline and the budget untripped, `Unknown` is impossible.
                    assert_ne!(
                        outcome,
                        Outcome::Unknown,
                        "seed={seed}: Unknown without a deadline or budget trip",
                    );

                    match outcome {
                        Outcome::Unsat => {
                            // (2a) Soundness of UNSAT: brute force must agree no model
                            // exists.
                            assert!(
                                !truth,
                                "WRONG UNSAT seed={seed} n={}: driver said Unsat but a \
                                 skeleton+theory model exists",
                                inst.n,
                            );
                            unsat += 1;
                        }
                        Outcome::Sat => {
                            // (2b) Soundness of SAT: read the driver's assignment and
                            // confirm it satisfies the skeleton AND avoids every
                            // forbidden cube (a genuine model), independent of the mock.
                            let mut assignment = 0u32;
                            for v in 0..inst.n {
                                let val = solver
                                    .value(v)
                                    .expect("a Sat verdict assigns every variable");
                                if val {
                                    assignment |= 1 << v;
                                }
                            }
                            assert!(
                                sat_clauses(&inst.clauses, assignment),
                                "WRONG SAT seed={seed}: model violates the skeleton",
                            );
                            assert!(
                                theory_consistent(&inst.forbidden, assignment),
                                "WRONG SAT seed={seed}: model contains a forbidden cube \
                                 (theory-inconsistent)",
                            );
                            // And it agrees with the brute-force existence verdict.
                            assert!(truth, "seed={seed}: driver Sat but brute force UNSAT");
                            sat += 1;
                        }
                        Outcome::Unknown => unreachable!("ruled out above"),
                    }
                }
            }
        }
        eprintln!(
            "cdclt non-monotone termination: runs={runs} sat={sat} unsat={unsat} \
             (all terminated within the step budget; no wrong verdicts)"
        );
        assert!(
            sat > 0 && unsat > 0,
            "degenerate sweep: sat={sat} unsat={unsat} — expected a mix",
        );
    }

    /// A pointed regression for the exact hazard DEBT 1 names: a mock that reports
    /// the **same** conflict on repeated queries (here, on every qualifying assert)
    /// must not cause the driver to re-learn/spin — it terminates with the correct
    /// verdict. The forbidden cube `{a=true}` forces `a=false`; the clause `(a)`
    /// then makes the instance UNSAT, reached without livelock.
    #[test]
    fn repeated_same_conflict_does_not_livelock() {
        let inst = Instance {
            n: 2,
            clauses: vec![
                vec![Lit {
                    var: 0,
                    positive: true,
                }], // a must be true
            ],
            forbidden: vec![vec![(0, true)]], // but a=true is forbidden
        };
        let (outcome, solver) = run_once(&inst, Mode::Always, false);
        assert!(
            !solver.step_budget_hit(),
            "livelocked on a repeated conflict"
        );
        assert_eq!(outcome, Outcome::Unsat, "a ∧ ¬a-forbidden is UNSAT");
        assert!(!brute_force_sat(&inst), "brute force agrees: UNSAT");
    }

    #[test]
    fn vsids_bumps_conflict_vars_and_reorders_decisions_deterministically() {
        fn run() -> (Vec<f64>, Vec<Lit>) {
            let mut solver = CdclT::new(4, 0, Vec::new(), None);
            solver.decision_level = 1;
            solver.value[0] = Some(true);
            solver.level[0] = 1;
            solver.trail.push((0, true, Cause::Decision));
            solver.value[1] = Some(true);
            solver.level[1] = 1;
            solver.reason[1] = Some(vec![
                Lit {
                    var: 0,
                    positive: false,
                },
                Lit {
                    var: 1,
                    positive: true,
                },
            ]);
            solver.trail.push((1, true, Cause::Implied));
            let conflict = vec![
                Lit {
                    var: 0,
                    positive: false,
                },
                Lit {
                    var: 1,
                    positive: false,
                },
            ];
            let (learned, _, _) = solver.analyze_conflict(&conflict, false);
            (solver.activity, learned)
        }

        let (activity, learned) = run();
        assert!(activity[0] > 0.0 && activity[1] > 0.0);
        assert!(activity[2] <= 0.0);
        assert!(activity[3] <= 0.0);
        assert_eq!(
            learned,
            vec![Lit {
                var: 0,
                positive: false,
            }]
        );

        let mut picker = CdclT::new(4, 0, Vec::new(), None);
        picker.bump_var(2);
        assert_eq!(picker.pick_unassigned(), Some(2));
        let plain = CdclT::new(4, 0, Vec::new(), None);
        assert_eq!(plain.pick_unassigned(), Some(0));

        let (activity_again, learned_again) = run();
        assert_eq!(activity, activity_again);
        assert_eq!(learned, learned_again);
    }

    #[test]
    fn phase_saving_survives_backtracking_and_preserves_true_first_default() {
        struct NoTheory;
        impl TheorySolver for NoTheory {
            fn assert(&mut self, _atom: usize, _value: bool) -> Result<(), Vec<TheoryLit>> {
                Ok(())
            }

            fn push(&mut self) {}

            fn pop(&mut self) {}

            fn propagate(&self) -> Vec<TheoryProp> {
                Vec::new()
            }
        }

        let mut theory = NoTheory;
        let mut solver = CdclT::new(3, 0, Vec::new(), None);
        assert_eq!(solver.saved_phase, vec![true, true, true]);

        solver.decision_level = 1;
        solver
            .assign(&mut theory, 0, false, Cause::Decision, None, false)
            .expect("pure Boolean assignment cannot conflict");
        solver
            .assign(&mut theory, 1, false, Cause::Implied, None, false)
            .expect("pure Boolean propagation cannot conflict");
        assert!(!solver.saved_phase[0]);
        assert!(!solver.saved_phase[1]);

        solver.backjump_to(&mut theory, 0);
        assert_eq!(solver.value[0], None);
        assert!(!solver.saved_phase[0]);
        assert!(solver.saved_phase[2]);
    }

    fn pigeonhole(pigeons: usize, holes: usize) -> (usize, Vec<Vec<Lit>>) {
        let variable = |pigeon: usize, hole: usize| pigeon * holes + hole;
        let mut clauses = Vec::new();
        for pigeon in 0..pigeons {
            clauses.push(
                (0..holes)
                    .map(|hole| Lit {
                        var: variable(pigeon, hole),
                        positive: true,
                    })
                    .collect(),
            );
            for left in 0..holes {
                for right in (left + 1)..holes {
                    clauses.push(vec![
                        Lit {
                            var: variable(pigeon, left),
                            positive: false,
                        },
                        Lit {
                            var: variable(pigeon, right),
                            positive: false,
                        },
                    ]);
                }
            }
        }
        for hole in 0..holes {
            for left in 0..pigeons {
                for right in (left + 1)..pigeons {
                    clauses.push(vec![
                        Lit {
                            var: variable(left, hole),
                            positive: false,
                        },
                        Lit {
                            var: variable(right, hole),
                            positive: false,
                        },
                    ]);
                }
            }
        }
        (pigeons * holes, clauses)
    }

    #[test]
    fn luby_restarts_fire_without_changing_verdict_or_theory_balance() {
        struct DepthTheory {
            depth: usize,
        }
        impl TheorySolver for DepthTheory {
            fn assert(&mut self, _atom: usize, _value: bool) -> Result<(), Vec<TheoryLit>> {
                Ok(())
            }

            fn push(&mut self) {
                self.depth += 1;
            }

            fn pop(&mut self) {
                self.depth = self.depth.checked_sub(1).expect("balanced theory pop");
            }

            fn propagate(&self) -> Vec<TheoryProp> {
                Vec::new()
            }
        }

        let (variables, clauses) = pigeonhole(5, 4);
        let run = |restart_unit| {
            let mut solver =
                CdclT::new(variables, 0, clauses.clone(), None).with_restart_unit(restart_unit);
            let mut theory = DepthTheory { depth: 0 };
            let outcome = solver.solve(&mut theory);
            (outcome, solver.restarts(), theory.depth)
        };

        let baseline = run(usize::MAX);
        assert_eq!(baseline, (Outcome::Unsat, 0, 0));
        let restarted = run(1);
        assert_eq!(restarted.0, baseline.0);
        assert!(restarted.1 > 0, "the lowered Luby schedule must restart");
        assert_eq!(restarted.2, 0, "restart must balance theory push/pop");
        assert_eq!(
            restarted,
            run(1),
            "restart trajectory must be deterministic"
        );
    }

    #[test]
    fn luby_sequence_matches_reluctant_doubling_prefix() {
        let actual: Vec<u64> = (1..=15).map(luby).collect();
        assert_eq!(actual, vec![1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8]);
    }
}
