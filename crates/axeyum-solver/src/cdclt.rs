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
//! This is the *generic* counterpart to the EUF-hardwired online search embedded in
//! [`crate::euf_egraph`]: [`CdclT`] is parameterised over any `T: TheorySolver`, so
//! the same driver serves EUF today and the arithmetic / combined theories
//! (UF/NRA/NIA) as they gain a [`TheorySolver`] impl. Slice (a) wires **EUF** as the
//! first theory (see [`crate::euf_egraph::check_qf_uf_online_cdclt`]).
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
//! - Deterministic: the decision heuristic is the lowest-index unassigned variable
//!   and every data structure is a `Vec`; there is no hash-iteration order and no
//!   clock-derived choice. The only clock read is the deadline check.
//! - Deadline: `deadline` is checked at the head of the search loop and of the
//!   propagation fixpoint, so the search degrades to `Unknown` under a deterministic
//!   resource bound (the deadline-hole class is designed out).

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
        }
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
    fn analyze_conflict(&self, conflict: &[Lit], seed_is_theory: bool) -> (Vec<Lit>, usize, bool) {
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

    /// The lowest-index unassigned variable, or `None` when the assignment is total.
    fn pick_unassigned(&self) -> Option<usize> {
        (0..self.var_count).find(|&v| self.value[v].is_none())
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
            match self.pick_unassigned() {
                None => return Outcome::Sat,
                Some(var) => {
                    self.decision_level += 1;
                    theory.push();
                    if let Err(core) = self.assign(theory, var, true, Cause::Decision, None, false)
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
