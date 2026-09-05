//! A persistent, assumption-capable interface to the native CDCL core
//! (ADR-1703).
//!
//! The one-shot entry points in [`super`] build a [`super::Cdcl`], solve once,
//! and drop it. This module keeps one alive: clauses can be added between
//! solves, assumptions hold for one solve only, and the learned clauses, VSIDS
//! activities and saved phases carry over. That is what
//! [`crate::IncrementalSat`] needs — and, through it, the LIA DPLL(T) driver
//! and the warm BV engine, which solve repeatedly over a growing database.
//!
//! ## What is retained, and why it is sound to retain it
//!
//! Every learned clause is derived by 1-UIP conflict analysis, which resolves
//! decisions away: the clause is entailed by the **clause database alone**,
//! never by the assumptions in force when it was learned. So a learned clause
//! stays valid when the assumption set changes, and stays valid when clauses
//! are *added* (the database only grows here — `IncrementalSat`'s database is
//! monotone). Activities and phases are pure heuristics and cannot affect a
//! verdict.
//!
//! Between solves the solver holds **no assignment at all**, including at level
//! zero: [`super::Cdcl::reset_search_state`] unwinds the whole trail and the
//! next solve re-propagates the accumulated units from
//! `Cdcl::initial_units`. That costs one level-zero propagation per solve and
//! buys the property that makes `add_clause` simple: a clause is always
//! registered into an unassigned solver, so watching its first two literals is
//! correct with no assignment-aware slot selection and no "already falsified at
//! level 0" special case.
//!
//! ## Proof emission
//!
//! Off by default — the warm path pays nothing for it, and with the sink
//! discarding, the search trajectory is exactly the trajectory of a recording
//! run (the sink is output-only; see [`super::Cdcl`]). When recording is on,
//! the emitted steps remain a valid DRAT proof of the **final** accumulated
//! formula even though earlier steps were derived before later clauses were
//! added: RUP is monotone in the clause set, so a clause that unit-propagates
//! to a conflict against a subset does so against the superset too.
//!
//! An `unsat` **under assumptions** derives no empty clause and is therefore
//! not a refutation; it reports a failed-assumption core instead.

use std::time::Duration;

#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use super::{Cdcl, DEFAULT_PROOF_SAT_CONFLICT_LIMIT, SearchOutcome};
use crate::drat::{DratSink, DratStep, ProofSinkError, VecProofSink};
use crate::{CnfAssignment, CnfLit};

/// Where an incremental solver's DRAT steps go.
///
/// Two states rather than a generic parameter, so [`NativeIncrementalCdcl`] is
/// one concrete type that [`crate::IncrementalSat`] can hold by value and that
/// stays `Send`.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
enum IncrementalSink {
    /// Steps are dropped. The default, and what the warm path uses.
    #[default]
    Discard,
    /// Steps accumulate in memory for later inspection.
    Record(VecProofSink),
}

impl DratSink for IncrementalSink {
    fn add_clause(&mut self, lits: &[CnfLit]) -> Result<(), ProofSinkError> {
        match self {
            IncrementalSink::Discard => Ok(()),
            IncrementalSink::Record(sink) => sink.add_clause(lits),
        }
    }

    fn delete_clause(&mut self, lits: &[CnfLit]) -> Result<(), ProofSinkError> {
        match self {
            IncrementalSink::Discard => Ok(()),
            IncrementalSink::Record(sink) => sink.delete_clause(lits),
        }
    }
}

/// The result of one incremental solve.
///
/// Distinguished from [`super::ProofSolveOutcome`] by
/// [`IncrementalSolveOutcome::UnsatUnderAssumptions`], which is a statement
/// about the assumptions and not about the formula.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IncrementalSolveOutcome {
    /// Satisfiable. The model assigns every variable the solver has seen and
    /// satisfies both the clause database and the assumptions.
    Sat(CnfAssignment),
    /// The clause database is unsatisfiable on its own: the empty clause was
    /// derived. When proof recording is on, the steps up to here are a DRAT
    /// refutation of the accumulated formula.
    Unsat,
    /// Unsatisfiable **under the assumptions passed to this solve**. The payload
    /// is the failed-assumption core: a subset of those assumptions already
    /// jointly inconsistent with the clause database. The database itself may be
    /// satisfiable, and no empty clause was derived.
    UnsatUnderAssumptions(Vec<CnfLit>),
    /// The conflict budget was exhausted (undecided).
    ResourceOut,
    /// The wall-clock deadline passed (undecided).
    Interrupted,
    /// The proof sink refused a step (only reachable with recording on). The
    /// search is abandoned with **no verdict** — a refutation whose proof could
    /// not be recorded is not a checked `unsat`.
    SinkFailed(ProofSinkError),
}

/// A persistent native CDCL solver: add clauses, solve, add more, solve again.
///
/// The clause database is monotone (clauses are never removed by the API;
/// `reduce_db` deletes only *learned* clauses, which are entailed and can be
/// re-derived). Learned clauses, VSIDS activities and saved phases survive
/// across [`NativeIncrementalCdcl::solve`] calls — see the module header for
/// why that is sound.
///
/// This type deliberately does **not** self-check its models; the layer above
/// it does, against the clause database it owns
/// ([`crate::IncrementalSat::solve`]).
pub struct NativeIncrementalCdcl {
    cdcl: Cdcl<'static, IncrementalSink>,
    /// Problem clauses accepted so far, including tautologies that were dropped
    /// from the database. Counts calls, not stored clauses.
    added_clauses: usize,
    /// Conflicts summed over every solve so far. `Cdcl::conflicts` is a
    /// per-solve budget counter and is reset by `reset_search_state`, so the
    /// cumulative figure is kept here.
    total_conflicts: usize,
    /// Conflicts consumed by the most recent solve.
    last_solve_conflicts: usize,
    /// Solves performed so far.
    solves: usize,
    /// Whether the core still holds a trail from the previous solve. Guards the
    /// reset so a run of `add_clause` calls costs one reset, not one per clause
    /// (the reset re-populates the order heap, which is O(variables)).
    needs_reset: bool,
}

impl core::fmt::Debug for NativeIncrementalCdcl {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("NativeIncrementalCdcl")
            .field("variable_count", &self.variable_count())
            .field("added_clauses", &self.added_clauses)
            .field("learned_clauses", &self.learned_clause_count())
            .field("total_conflicts", &self.total_conflicts)
            .field("solves", &self.solves)
            .finish_non_exhaustive()
    }
}

impl Default for NativeIncrementalCdcl {
    fn default() -> Self {
        Self::new()
    }
}

impl NativeIncrementalCdcl {
    /// An empty solver with proof recording **off**.
    #[must_use]
    pub fn new() -> Self {
        Self::with_sink(IncrementalSink::Discard)
    }

    /// An empty solver that records every emitted DRAT step in memory.
    ///
    /// Costs allocation proportional to the proof; use it when a refutation
    /// must be handed to [`crate::check_drat`], not on a hot warm path.
    #[must_use]
    pub fn with_proof_recording() -> Self {
        Self::with_sink(IncrementalSink::Record(VecProofSink::new()))
    }

    fn with_sink(sink: IncrementalSink) -> Self {
        Self {
            cdcl: Cdcl::new_empty(sink),
            added_clauses: 0,
            total_conflicts: 0,
            last_solve_conflicts: 0,
            solves: 0,
            needs_reset: false,
        }
    }

    /// Whether this solver is recording a DRAT proof.
    #[must_use]
    pub fn records_proof(&self) -> bool {
        matches!(self.cdcl.sink, IncrementalSink::Record(_))
    }

    /// Number of variables the solver has room for.
    #[must_use]
    pub fn variable_count(&self) -> usize {
        self.cdcl.assign.len()
    }

    /// Number of `add_clause` calls accepted so far.
    #[must_use]
    pub fn added_clause_count(&self) -> usize {
        self.added_clauses
    }

    /// Live (non-deleted) learned clauses right now.
    ///
    /// This is the observable that makes retention across solves checkable: it
    /// is nonzero after any solve that hit a conflict, and it does not reset at
    /// the start of the next solve.
    #[must_use]
    pub fn learned_clause_count(&self) -> usize {
        self.cdcl.learned_live
    }

    /// Conflicts summed over every solve so far.
    #[must_use]
    pub fn total_conflicts(&self) -> usize {
        self.total_conflicts
    }

    /// Conflicts consumed by the most recent solve (0 before the first).
    #[must_use]
    pub fn last_solve_conflicts(&self) -> usize {
        self.last_solve_conflicts
    }

    /// Solves performed so far.
    #[must_use]
    pub fn solve_count(&self) -> usize {
        self.solves
    }

    /// The DRAT steps recorded so far, or an empty slice when recording is off.
    #[must_use]
    pub fn proof_steps(&self) -> &[DratStep] {
        match &self.cdcl.sink {
            IncrementalSink::Discard => &[],
            IncrementalSink::Record(sink) => sink.steps(),
        }
    }

    /// Makes variable indices `0 .. count` legal without adding any clause.
    ///
    /// Reserved-but-unused variables are not branchable: they never delay a
    /// decision and default to `false` in a returned model, exactly as in the
    /// one-shot core.
    pub fn reserve(&mut self, count: usize) {
        self.cdcl.ensure_vars(count);
    }

    /// Adds one problem clause to the persistent database.
    ///
    /// Duplicated literals are removed and a tautology is dropped; both are
    /// logic-preserving. The variable namespace grows to cover the literals.
    pub fn add_clause(&mut self, lits: &[CnfLit]) {
        // A clause is always registered into an unassigned solver: unwind first
        // so `add_input_clause`'s "watch the first two literals" is correct.
        self.between_solves();
        self.cdcl.add_input_clause(lits);
        self.added_clauses += 1;
    }

    /// Unwinds the previous solve's trail, at most once per solve.
    fn between_solves(&mut self) {
        if self.needs_reset {
            self.cdcl.reset_search_state();
            self.needs_reset = false;
        }
    }

    /// Solves the accumulated database under `assumptions`, which hold for this
    /// solve only.
    ///
    /// `deadline` is checked on the same deterministic conflict cadence as the
    /// one-shot core, and `max_conflicts` bounds **this** solve (it is not a
    /// lifetime budget). Neither limit can produce a verdict: they yield
    /// [`IncrementalSolveOutcome::Interrupted`] /
    /// [`IncrementalSolveOutcome::ResourceOut`].
    pub fn solve(
        &mut self,
        assumptions: &[CnfLit],
        deadline: Option<Instant>,
        max_conflicts: usize,
    ) -> IncrementalSolveOutcome {
        // Make every assumption variable legal before the search reads
        // `value(p)`; an assumption may name a variable no clause mentions.
        let needed = assumptions
            .iter()
            .map(|lit| lit.var().index() + 1)
            .max()
            .unwrap_or(0);
        self.cdcl.ensure_vars(needed);

        self.between_solves();
        let outcome = self.cdcl.run(assumptions, deadline, max_conflicts);
        self.needs_reset = true;
        self.last_solve_conflicts = self.cdcl.conflicts;
        self.total_conflicts += self.cdcl.conflicts;
        self.solves += 1;
        match outcome {
            Ok(SearchOutcome::Sat(model)) => IncrementalSolveOutcome::Sat(model),
            Ok(SearchOutcome::Unsat) => IncrementalSolveOutcome::Unsat,
            Ok(SearchOutcome::UnsatUnderAssumptions(core)) => {
                IncrementalSolveOutcome::UnsatUnderAssumptions(core)
            }
            Ok(SearchOutcome::ResourceOut) => IncrementalSolveOutcome::ResourceOut,
            Ok(SearchOutcome::Interrupted) => IncrementalSolveOutcome::Interrupted,
            Err(error) => IncrementalSolveOutcome::SinkFailed(error),
        }
    }

    /// [`NativeIncrementalCdcl::solve`] with the default conflict budget and an
    /// optional cooperative wall-clock `timeout`.
    pub fn solve_within(
        &mut self,
        assumptions: &[CnfLit],
        timeout: Option<Duration>,
        max_conflicts: Option<usize>,
    ) -> IncrementalSolveOutcome {
        let deadline = timeout.and_then(|duration| Instant::now().checked_add(duration));
        self.solve(
            assumptions,
            deadline,
            max_conflicts.unwrap_or(DEFAULT_PROOF_SAT_CONFLICT_LIMIT),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CnfClause, CnfFormula, CnfVar, check_drat};

    fn lit(value: i64) -> CnfLit {
        let index = usize::try_from(value.abs()).expect("index") - 1;
        let var = CnfVar::new(index).expect("variable");
        if value < 0 {
            CnfLit::positive(var).negated()
        } else {
            CnfLit::positive(var)
        }
    }

    fn lits(values: &[i64]) -> Vec<CnfLit> {
        values.iter().copied().map(lit).collect()
    }

    fn budget() -> usize {
        100_000
    }

    /// `PHP(pigeons -> pigeons-1)`, each clause guarded by the *negation* of a
    /// selector literal `s` (variable `sel`). Asserting `s` switches the whole
    /// unsatisfiable core on; without it the database is trivially satisfiable.
    fn guarded_pigeonhole(pigeons: i64, sel: i64) -> Vec<Vec<i64>> {
        let holes = pigeons - 1;
        // 1-based dimacs numbering starting at 2, so no core variable collides
        // with the selector at 1.
        let var = |p: i64, h: i64| p * holes + h + 2;
        let mut clauses = Vec::new();
        for p in 0..pigeons {
            let mut clause = vec![-sel];
            for h in 0..holes {
                clause.push(var(p, h));
            }
            clauses.push(clause);
        }
        for h in 0..holes {
            for p in 0..pigeons {
                for q in (p + 1)..pigeons {
                    clauses.push(vec![-sel, -var(p, h), -var(q, h)]);
                }
            }
        }
        clauses
    }

    fn load(solver: &mut NativeIncrementalCdcl, clauses: &[Vec<i64>]) {
        for clause in clauses {
            solver.add_clause(&lits(clause));
        }
    }

    #[test]
    fn assumptions_flip_the_verdict_on_the_same_database() {
        // sel is variable index 0 (dimacs 1); the guarded core uses 2.. .
        let clauses = guarded_pigeonhole(4, 1);
        let mut solver = NativeIncrementalCdcl::new();
        load(&mut solver, &clauses);

        // Without the selector the database is satisfiable.
        let free = solver.solve(&[], None, budget());
        assert!(
            matches!(free, IncrementalSolveOutcome::Sat(_)),
            "unguarded database must be satisfiable, got {free:?}"
        );

        // Asserting the selector switches on PHP(4 -> 3), which is not.
        let assumed = solver.solve(&[lit(1)], None, budget());
        let IncrementalSolveOutcome::UnsatUnderAssumptions(core) = assumed else {
            panic!("assuming the selector must be unsat under assumptions, got {assumed:?}");
        };
        assert_eq!(core, vec![lit(1)], "the selector is the whole core");

        // And the database is still satisfiable without it: the unsat verdict
        // belonged to the assumption, not to the formula.
        let again = solver.solve(&[], None, budget());
        assert!(
            matches!(again, IncrementalSolveOutcome::Sat(_)),
            "database must remain satisfiable after an assumption-only unsat, got {again:?}"
        );
    }

    #[test]
    fn a_clause_added_after_an_assumption_unsat_changes_the_verdict() {
        let mut solver = NativeIncrementalCdcl::new();
        // (1 or 2), and assume -1: satisfiable by 2.
        solver.add_clause(&lits(&[1, 2]));
        let first = solver.solve(&lits(&[-1]), None, budget());
        assert!(
            matches!(first, IncrementalSolveOutcome::Sat(_)),
            "expected sat under -1, got {first:?}"
        );

        // Now forbid 2 as well. The same assumption is no longer satisfiable.
        solver.add_clause(&lits(&[-2]));
        let second = solver.solve(&lits(&[-1]), None, budget());
        let IncrementalSolveOutcome::UnsatUnderAssumptions(core) = second else {
            panic!("expected unsat under -1 after adding (-2), got {second:?}");
        };
        assert_eq!(core, lits(&[-1]));

        // The database alone is still satisfiable (by 1).
        let free = solver.solve(&[], None, budget());
        assert!(
            matches!(free, IncrementalSolveOutcome::Sat(_)),
            "expected the database itself to stay sat, got {free:?}"
        );

        // One more clause makes it unsatisfiable outright — a different verdict
        // from "unsat under assumptions", and this one derives the empty clause.
        solver.add_clause(&lits(&[-1]));
        let third = solver.solve(&[], None, budget());
        assert_eq!(third, IncrementalSolveOutcome::Unsat);
    }

    #[test]
    fn learned_clauses_and_conflicts_carry_over_between_solves() {
        let clauses = guarded_pigeonhole(5, 1);
        let mut solver = NativeIncrementalCdcl::new();
        load(&mut solver, &clauses);

        // Negative control: nothing is learned before a search runs.
        assert_eq!(solver.learned_clause_count(), 0);
        assert_eq!(solver.total_conflicts(), 0);

        let first = solver.solve(&[lit(1)], None, budget());
        assert!(matches!(
            first,
            IncrementalSolveOutcome::UnsatUnderAssumptions(_)
        ));
        let learned_after_first = solver.learned_clause_count();
        let conflicts_first = solver.last_solve_conflicts();
        assert!(
            conflicts_first > 0,
            "PHP(5 -> 4) must cost conflicts, got {conflicts_first}"
        );
        assert!(
            learned_after_first > 0,
            "conflicts must leave learned clauses behind, got {learned_after_first}"
        );

        // Retention is directly observable: the count entering the second solve
        // is the count leaving the first, and the cumulative conflict counter
        // keeps climbing rather than restarting.
        let second = solver.solve(&[lit(1)], None, budget());
        assert!(matches!(
            second,
            IncrementalSolveOutcome::UnsatUnderAssumptions(_)
        ));
        assert!(
            solver.learned_clause_count() >= learned_after_first,
            "learned clauses must survive the solve boundary: {} then {}",
            learned_after_first,
            solver.learned_clause_count()
        );
        assert_eq!(
            solver.total_conflicts(),
            conflicts_first + solver.last_solve_conflicts()
        );
        assert_eq!(solver.solve_count(), 2);

        // A fresh solver over the same clauses starts from nothing — so the
        // counters above are measuring retention, not a constant.
        let mut fresh = NativeIncrementalCdcl::new();
        load(&mut fresh, &clauses);
        assert_eq!(fresh.learned_clause_count(), 0);
    }

    #[test]
    fn a_failed_assumption_core_is_genuine_and_a_wrong_core_is_rejected() {
        // Selector 1 guards a contradiction; selector 3 guards a harmless
        // constraint. Assuming both is unsatisfiable, but only selector 1 is
        // responsible -- so "assume 3 alone" is a *wrong* core and must be
        // rejected, which is what makes the positive check below non-vacuous.
        let mut solver = NativeIncrementalCdcl::new();
        solver.add_clause(&lits(&[-1, 2]));
        solver.add_clause(&lits(&[-1, -2]));
        solver.add_clause(&lits(&[-3, 4]));

        let outcome = solver.solve(&lits(&[1, 3]), None, budget());
        let IncrementalSolveOutcome::UnsatUnderAssumptions(core) = outcome else {
            panic!("expected unsat under both selectors, got {outcome:?}");
        };
        assert!(!core.is_empty(), "a core must name at least one assumption");
        assert!(
            core.contains(&lit(1)),
            "the responsible selector must be in the core, got {core:?}"
        );

        // Positive: re-solving under the reported core alone must still be
        // unsatisfiable. If it came back sat, the core would be a false claim.
        let recheck = solver.solve(&core, None, budget());
        assert!(
            matches!(recheck, IncrementalSolveOutcome::UnsatUnderAssumptions(_)),
            "the reported core must be sufficient on its own, got {recheck:?}"
        );

        // Negative control: the same check applied to a NON-core assumption must
        // come back satisfiable. Without this the positive check above could
        // pass for a checker that reports unsat unconditionally.
        let wrong_core = solver.solve(&[lit(3)], None, budget());
        assert!(
            matches!(wrong_core, IncrementalSolveOutcome::Sat(_)),
            "the innocent selector must NOT be a core; got {wrong_core:?}"
        );
    }

    #[test]
    fn an_outright_unsat_can_carry_a_checkable_drat_proof() {
        // PHP(4 -> 3) with no selector: unsatisfiable outright.
        let clauses = guarded_pigeonhole(4, 1);
        let mut solver = NativeIncrementalCdcl::with_proof_recording();
        assert!(solver.records_proof());
        load(&mut solver, &clauses);
        // Force the selector on as a unit clause so the database itself is unsat.
        solver.add_clause(&lits(&[1]));

        let outcome = solver.solve(&[], None, budget());
        assert_eq!(outcome, IncrementalSolveOutcome::Unsat);

        // Rebuild the formula the proof is against and check it independently.
        let mut formula = CnfFormula::new(solver.variable_count());
        for clause in &clauses {
            formula
                .add_clause(CnfClause::new(lits(clause)))
                .expect("clause fits the formula");
        }
        formula
            .add_clause(CnfClause::new(lits(&[1])))
            .expect("unit fits");
        assert!(
            check_drat(&formula, solver.proof_steps()).expect("checker ran"),
            "the recorded steps must be a DRAT refutation"
        );
    }

    #[test]
    fn proof_recording_is_off_by_default() {
        let mut solver = NativeIncrementalCdcl::new();
        assert!(!solver.records_proof());
        solver.add_clause(&lits(&[1]));
        solver.add_clause(&lits(&[-1]));
        assert_eq!(
            solver.solve(&[], None, budget()),
            IncrementalSolveOutcome::Unsat
        );
        assert!(
            solver.proof_steps().is_empty(),
            "the discarding sink must keep nothing"
        );
    }

    #[test]
    fn a_zero_conflict_budget_is_undecided_never_a_verdict() {
        let clauses = guarded_pigeonhole(5, 1);
        let mut solver = NativeIncrementalCdcl::new();
        load(&mut solver, &clauses);
        assert_eq!(
            solver.solve(&[lit(1)], None, 0),
            IncrementalSolveOutcome::ResourceOut
        );
        // ... and the same solver still decides it with a real budget, so the
        // ResourceOut above was the budget and not a broken database.
        assert!(matches!(
            solver.solve(&[lit(1)], None, budget()),
            IncrementalSolveOutcome::UnsatUnderAssumptions(_)
        ));
    }

    #[test]
    fn duplicate_literals_and_tautologies_are_handled() {
        let mut solver = NativeIncrementalCdcl::new();
        solver.add_clause(&lits(&[1, 1, 2]));
        solver.add_clause(&lits(&[3, -3])); // tautology: no constraint
        solver.add_clause(&lits(&[-1]));
        solver.add_clause(&lits(&[-2]));
        assert_eq!(
            solver.solve(&[], None, budget()),
            IncrementalSolveOutcome::Unsat
        );
    }

    #[test]
    fn an_assumption_on_an_unconstrained_variable_is_satisfiable() {
        let mut solver = NativeIncrementalCdcl::new();
        solver.add_clause(&lits(&[1]));
        // Variable 9 appears in no clause at all.
        let outcome = solver.solve(&lits(&[9]), None, budget());
        let IncrementalSolveOutcome::Sat(model) = outcome else {
            panic!("expected sat, got {outcome:?}");
        };
        assert!(model.values().len() >= 9);
        assert!(model.values()[8], "the assumption must hold in the model");
    }

    #[test]
    fn contradictory_assumptions_report_both_of_them() {
        let mut solver = NativeIncrementalCdcl::new();
        solver.add_clause(&lits(&[1, 2]));
        let outcome = solver.solve(&lits(&[1, -1]), None, budget());
        let IncrementalSolveOutcome::UnsatUnderAssumptions(core) = outcome else {
            panic!("expected unsat under assumptions, got {outcome:?}");
        };
        let mut sorted = core.clone();
        sorted.sort_by_key(|l| (l.var().index(), l.is_negated()));
        assert_eq!(sorted, vec![lit(1), lit(-1)]);
    }
}
