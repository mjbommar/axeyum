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

use super::theory::{NativeTheory, NullTheory};
use super::{
    Cdcl, DEFAULT_PROOF_SAT_CONFLICT_LIMIT, NativeLayerStats, SearchOutcome, TheoryRefutation,
    TheorySolveOptions,
};
use crate::drat::{DratSink, DratStep, ProofSinkError, VecProofSink};
use crate::{CnfAssignment, CnfClause, CnfFormula, CnfLit};

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
pub struct NativeIncrementalCdcl<T: NativeTheory = NullTheory> {
    cdcl: Cdcl<'static, IncrementalSink, T>,
    /// The problem clauses, retained verbatim so a theory refutation can name
    /// the formula it refutes. `None` unless the caller asked for it, because
    /// it costs a second copy of the whole input.
    retained_cnf: Option<Vec<Vec<CnfLit>>>,
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

impl<T: NativeTheory> core::fmt::Debug for NativeIncrementalCdcl<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("NativeIncrementalCdcl")
            .field("variable_count", &self.variable_count())
            .field("added_clauses", &self.added_clauses)
            .field("learned_clauses", &self.learned_clause_count())
            .field("total_conflicts", &self.total_conflicts)
            .field("theory_lemmas", &self.theory_lemma_count())
            .field("solves", &self.solves)
            .finish_non_exhaustive()
    }
}

impl Default for NativeIncrementalCdcl<NullTheory> {
    fn default() -> Self {
        Self::new()
    }
}

impl NativeIncrementalCdcl<NullTheory> {
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
            retained_cnf: None,
            added_clauses: 0,
            total_conflicts: 0,
            last_solve_conflicts: 0,
            solves: 0,
            needs_reset: false,
        }
    }
}

impl<T: NativeTheory> NativeIncrementalCdcl<T> {
    /// A persistent solver with `theory` attached: **warm CDCL(T)**.
    ///
    /// This is the constructor the core could not express. `Cdcl::new_empty` --
    /// the only persistent seed -- lives in an impl block bound to
    /// [`NullTheory`], so until now no public route paired a theory with a
    /// `Cdcl` that outlived one solve, and the two remaining CDCL(T)
    /// migrations were blocked at the type level rather than on effort.
    ///
    /// `options` are the **same** [`TheorySolveOptions`] the one-shot entry
    /// point takes and are applied identically, so a query decided through this
    /// object and through `solve_with_theory_and_drat_proof_with_options` runs
    /// the same heuristics. Two fields are read differently and both are
    /// documented where they are read:
    ///
    /// * `record_proof` -- governs DRAT recording as it does on the one-shot
    ///   path, but a warm route wants it **off**, and
    ///   [`TheorySolveOptions::default`] has it on. ADR-1703 point 1 made the
    ///   same call for the `NullTheory` warm object: the stream is every
    ///   learned clause of every solve, held in memory, and a route that needs
    ///   only a verdict must not pay it.
    ///   [`NativeIncrementalCdcl::warm_theory`] is the constructor that does
    ///   that.
    /// * `proof_literal_budget` -- **not honoured**. The warm sink carries no
    ///   budget counter, so recording here is all-or-nothing. A caller needing
    ///   a bounded stream keeps recording off and re-runs the decided query
    ///   through the one-shot path, which does honour it.
    ///
    /// # Theory state across a solve boundary
    ///
    /// Each solve runs inside one theory `push`/`pop` pair opened below
    /// decision level zero (`Cdcl::theory_epoch`), so the theory's
    /// **assertions** are undone at the boundary while its **registration** --
    /// the var-to-atom map it built, the terms it knows -- survives. That split
    /// is what `push`/`pop` already mean, which is why warm CDCL(T) needs no
    /// new `NativeTheory` method and no fresh theory instance per solve.
    #[must_use]
    pub fn with_theory(theory: T, options: TheorySolveOptions) -> Self {
        let sink = if options.record_proof {
            IncrementalSink::Record(VecProofSink::new())
        } else {
            IncrementalSink::Discard
        };
        let mut cdcl = Cdcl::new_empty_with_theory(sink, theory);
        cdcl.collect_layer_stats = options.collect_layer_stats;
        cdcl.use_target_rephase = options.target_rephase;
        if let Some(policies) = options.search_profile.policies() {
            cdcl.set_policies(&policies);
        }
        // The one-shot path fills all three phase vectors here, because its
        // constructor already sized them to the formula. A warm solver has no
        // variables yet, so filling now would fill nothing; the equivalent work
        // happens in `NativeIncrementalCdcl::grow_to` as variables arrive.
        cdcl.initial_phase = options.initial_phase;
        // Retained only when a refutation could be assembled from it; see the
        // field doc.
        let retained_cnf = options.record_proof.then(Vec::new);
        Self {
            cdcl,
            retained_cnf,
            added_clauses: 0,
            total_conflicts: 0,
            last_solve_conflicts: 0,
            solves: 0,
            needs_reset: false,
        }
    }

    /// [`NativeIncrementalCdcl::with_theory`] with DRAT recording **off** and
    /// every other knob at its shipped default: the shape a warm route wants.
    ///
    /// Off by default is not a guess. The warm `NullTheory` object made the
    /// same choice for the same reason (see the module header), and
    /// `TheorySolveOptions::record_proof`'s own doc prices it: on a long
    /// CDCL(T) search the stream is gigabytes, and warm means *many* such
    /// searches accumulating into one sink.
    #[must_use]
    pub fn warm_theory(theory: T) -> Self {
        Self::with_theory(
            theory,
            TheorySolveOptions {
                record_proof: false,
                ..TheorySolveOptions::default()
            },
        )
    }

    /// The attached theory.
    ///
    /// Readable straight after a solve, with that solve's assertions still in
    /// place -- which is what a model builder needs, and why the per-solve
    /// theory epoch is closed lazily at the *next* boundary rather than on the
    /// way out of `solve`.
    pub fn theory(&self) -> &T {
        &self.cdcl.theory
    }

    /// The attached theory, mutably. Same visibility rule as
    /// [`NativeIncrementalCdcl::theory`].
    pub fn theory_mut(&mut self) -> &mut T {
        &mut self.cdcl.theory
    }

    /// Takes the theory back with its push/pop stack **balanced**: the open
    /// per-solve epoch, if any, is closed first.
    ///
    /// Use this rather than dropping the solver whenever the theory is borrowed
    /// (`T = &mut Theory`) and the caller goes on using it, since a dropped
    /// solver leaves the last solve's epoch -- and its assertions -- in place.
    pub fn into_theory(mut self) -> T {
        self.between_solves();
        self.cdcl.theory
    }

    /// Theory lemmas installed into the clause database over every solve so
    /// far (ADR-1704's `lemmas` stream).
    ///
    /// Cumulative, and deliberately not reset at a solve boundary: a theory
    /// lemma is valid in the theory outright, so it stays a legitimate input
    /// clause of the extended formula for the life of the object.
    #[must_use]
    pub fn theory_lemma_count(&self) -> usize {
        self.cdcl.theory_lemmas.len()
    }

    /// The ADR-1704 two-stream artifact for a refutation reached by this
    /// object, or `None` when recording is off.
    ///
    /// `None` means **not recorded**. It never means "no theory lemma was
    /// assumed" -- that is `Some(artifact)` with `theory_lemma_count() == 0`.
    ///
    /// The CNF named is every problem clause added so far and the lemmas are
    /// every lemma installed so far, which is the formula the accumulated DRAT
    /// stream refutes: RUP is monotone in the clause set, so a step derived
    /// against an earlier subset is still RUP against this superset.
    ///
    /// Only meaningful after a solve returned
    /// [`IncrementalSolveOutcome::Unsat`] -- an `unsat` *under assumptions*
    /// derives no empty clause and is not a refutation at all.
    ///
    /// # Panics
    ///
    /// Cannot panic in practice, and the `expect` is deliberate rather than a
    /// silent fallback: a retained clause is retained by
    /// [`NativeIncrementalCdcl::add_clause`], which grows the variable
    /// namespace to cover its own literals first, so every retained clause is
    /// within [`NativeIncrementalCdcl::variable_count`] by construction. If
    /// that ever stopped holding, the artifact would be naming a formula it
    /// does not have, which must fail loudly rather than produce a refutation
    /// of the wrong CNF.
    #[must_use]
    pub fn theory_refutation(&self) -> Option<TheoryRefutation> {
        let clauses = self.retained_cnf.as_ref()?;
        let mut cnf = CnfFormula::new(self.variable_count());
        for clause in clauses {
            cnf.add_clause(CnfClause::new(clause.clone()))
                .expect("a retained problem clause is over the solver's own variables");
        }
        Some(TheoryRefutation::from_cnf_and_lemmas(
            cnf,
            self.cdcl.theory_lemmas.clone(),
            self.proof_steps().to_vec(),
        ))
    }

    /// Per-layer counters accumulated so far, or an all-zero record when
    /// `collect_layer_stats` was not set.
    #[must_use]
    pub fn layer_stats(&self) -> NativeLayerStats {
        self.cdcl.native_layer_stats()
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

    /// Grows the variable namespace to `count`, giving every **newly created**
    /// variable the phase the one-shot constructor would have given it.
    ///
    /// This is where `TheorySolveOptions::initial_phase` is honoured on the
    /// warm path, and it exists to make the two paths agree rather than to
    /// improve on either. The one-shot path fills `phase`, `best_phase` and
    /// `target_phase` in its constructor, for the variables the formula
    /// declared; a warm solver learns its variables one `add_clause` at a time,
    /// so the same fill has to happen as they arrive.
    ///
    /// # The asymmetry this deliberately reproduces
    ///
    /// `Cdcl::ensure_vars` grows `target_phase` with `initial_phase` but
    /// `phase` and `best_phase` with `false`. So a variable created *after*
    /// construction does not get the initial phase the option names — and that
    /// is reachable on the SHIPPING one-shot route, whose theory registers
    /// atoms mid-search through `Cdcl::register_theory_atoms`, and which sets
    /// `initial_phase: true`.
    ///
    /// That is a pre-existing defect in what `initial_phase` means, it is
    /// heuristic-only (a decision polarity, never a verdict), and repairing it
    /// would move the trajectory of the one-shot CDCL(T) routes that have just
    /// migrated onto this core. So it is reproduced here, not repaired: this
    /// method fills only for variables the CALLER declares, exactly as the
    /// one-shot constructor does for the variables the FORMULA declares, and
    /// leaves theory-registered atoms to `ensure_vars` on both paths. Repairing
    /// it is a separate change with its own measurement.
    fn grow_to(&mut self, count: usize) {
        let before = self.cdcl.assign.len();
        self.cdcl.ensure_vars(count);
        if self.cdcl.initial_phase {
            for var in before..self.cdcl.assign.len() {
                self.cdcl.phase[var] = true;
                self.cdcl.best_phase[var] = true;
                // `target_phase` already grew with `initial_phase`.
            }
        }
    }

    /// Makes variable indices `0 .. count` legal without adding any clause.
    ///
    /// Reserved-but-unused variables are not branchable: they never delay a
    /// decision and default to `false` in a returned model, exactly as in the
    /// one-shot core.
    pub fn reserve(&mut self, count: usize) {
        self.grow_to(count);
    }

    /// Adds one problem clause to the persistent database.
    ///
    /// Duplicated literals are removed and a tautology is dropped; both are
    /// logic-preserving. The variable namespace grows to cover the literals.
    pub fn add_clause(&mut self, lits: &[CnfLit]) {
        // A clause is always registered into an unassigned solver: unwind first
        // so `add_input_clause`'s "watch the first two literals" is correct.
        // For a warm CDCL(T) this is also what closes the previous solve's
        // theory epoch, so the theory is told about this clause's literals from
        // a clean assertion state on the next solve rather than on top of the
        // last one's.
        self.between_solves();
        if let Some(retained) = self.retained_cnf.as_mut() {
            retained.push(lits.to_vec());
        }
        // Pre-grow so the new variables get their initial phase; this is the
        // same bound `add_input_clause` computes, so its own `ensure_vars` is
        // then a no-op rather than a second, phase-blind growth.
        let needed = lits
            .iter()
            .map(|lit| lit.var().index() + 1)
            .max()
            .unwrap_or(0);
        self.grow_to(needed);
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
        self.grow_to(needed);

        self.between_solves();
        // Open this solve's theory epoch: one `push` below decision level zero,
        // closed by the next `between_solves`. A no-op for `NullTheory`, whose
        // `HAS_THEORY` is false, so the Boolean warm object's trajectory is
        // exactly what it was.
        self.cdcl.open_theory_epoch();
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

/// Warm CDCL(T): the persistent solver with a theory attached.
///
/// Everything here exercises [`NativeIncrementalCdcl::with_theory`], the
/// constructor that did not exist. The tests are grouped by what they are
/// evidence for: that the object *decides* things (and decides them the way the
/// one-shot path does), that it is genuinely *warm*, and that the per-solve
/// theory epoch — the one invariant the whole design rests on — is load
/// bearing.
#[cfg(test)]
mod warm_theory {
    use super::*;
    use crate::theory::{FinalCheckOutcome, NativeTheory, PropagationQueue};
    use crate::{
        CnfClause, CnfFormula, CnfVar, TheorySolveOptions, TheorySolveOutcome,
        solve_with_theory_and_drat_proof_with_options,
    };

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

    fn formula(vars: usize, clauses: &[&[i64]]) -> CnfFormula {
        let mut f = CnfFormula::new(vars);
        for clause in clauses {
            f.add_clause(CnfClause::new(lits(clause)))
                .expect("clause is over the formula's variables");
        }
        f
    }

    /// "At most one of the designated atoms is true" — small, but a complete
    /// decision procedure for what it claims, so `final_check` has nothing left
    /// to do and every verdict it forces comes through `assert`.
    ///
    /// `asserted` is a **list, not a set**, and that is deliberate.
    /// [`NativeTheory`] promises the driver asserts a given variable at most
    /// once inside a `push`/`pop` scope, so a duplicate in this list is a
    /// driver-side contract violation. Keeping a list rather than de-duplicating
    /// is what turns that violation into an observable wrong verdict instead of
    /// a silent no-op — see
    /// `a_solve_boundary_must_not_re_assert_into_a_theory_that_never_forgot`.
    #[derive(Debug)]
    struct AtMostOne {
        /// SAT variable indices in the mutex group.
        group: Vec<usize>,
        /// Group atoms currently asserted true, in assertion order.
        asserted: Vec<usize>,
        /// One entry per `push`: the `asserted` length to truncate back to.
        marks: Vec<usize>,
        /// Net push depth. Zero means the theory's stack is balanced.
        depth: isize,
        /// Deepest push depth reached, over the object's whole life.
        max_depth: isize,
        /// Total `assert` calls, over the object's whole life. The instrument
        /// for "is this the same theory instance the previous solve used".
        asserts: usize,
        /// Total `final_check` calls.
        final_checks: usize,
    }

    impl AtMostOne {
        fn new(group: &[usize]) -> Self {
            Self {
                group: group.to_vec(),
                asserted: Vec::new(),
                marks: Vec::new(),
                depth: 0,
                max_depth: 0,
                asserts: 0,
                final_checks: 0,
            }
        }
    }

    impl NativeTheory for AtMostOne {
        fn assert(&mut self, var: usize, value: bool) -> Result<(), Vec<CnfLit>> {
            self.asserts += 1;
            if !value || !self.group.contains(&var) {
                return Ok(());
            }
            self.asserted.push(var);
            if self.asserted.len() > 1 {
                // The conflict CLAUSE (this crate's convention): the negation of
                // the asserted conjunction, so every literal is false under the
                // current assignment. De-duplicated so the clause the driver
                // installs is well formed even when the driver handed us the
                // same variable twice — the wrong verdict that follows is then
                // the *search's*, not an artefact of a malformed lemma.
                let mut clause: Vec<CnfLit> = Vec::new();
                for &v in &self.asserted {
                    let l = CnfLit::positive(CnfVar::new(v).expect("group variable")).negated();
                    if !clause.contains(&l) {
                        clause.push(l);
                    }
                }
                return Err(clause);
            }
            Ok(())
        }

        fn push(&mut self) {
            self.marks.push(self.asserted.len());
            self.depth += 1;
            self.max_depth = self.max_depth.max(self.depth);
        }

        fn pop(&mut self) {
            let mark = self
                .marks
                .pop()
                .expect("a `pop` without a matching `push`: the driver's stack is unbalanced");
            self.asserted.truncate(mark);
            self.depth -= 1;
        }

        fn propagate_into(&mut self, _queue: &mut PropagationQueue) {}

        fn final_check(&mut self) -> FinalCheckOutcome {
            self.final_checks += 1;
            FinalCheckOutcome::Sat
        }
    }

    /// One verdict vocabulary for both engines, so a mismatch in the *kind* of
    /// answer — including a give-up reason — is a test failure rather than
    /// something two different enums quietly hide.
    #[derive(Debug, PartialEq, Eq)]
    enum Verdict {
        Sat(Vec<bool>),
        Unsat,
        ResourceOut,
        Interrupted,
        /// Only reachable under assumptions. Present so it can never be folded
        /// into one of the above.
        UnsatUnderAssumptions,
    }

    fn from_one_shot(outcome: &TheorySolveOutcome) -> Verdict {
        match outcome {
            TheorySolveOutcome::Sat(model) => Verdict::Sat(model.values().to_vec()),
            TheorySolveOutcome::Unsat(_) => Verdict::Unsat,
            TheorySolveOutcome::ResourceOut => Verdict::ResourceOut,
            TheorySolveOutcome::Interrupted => Verdict::Interrupted,
        }
    }

    fn from_warm(outcome: &IncrementalSolveOutcome) -> Verdict {
        match outcome {
            IncrementalSolveOutcome::Sat(model) => Verdict::Sat(model.values().to_vec()),
            IncrementalSolveOutcome::Unsat => Verdict::Unsat,
            IncrementalSolveOutcome::UnsatUnderAssumptions(_) => Verdict::UnsatUnderAssumptions,
            IncrementalSolveOutcome::ResourceOut => Verdict::ResourceOut,
            IncrementalSolveOutcome::Interrupted => Verdict::Interrupted,
            IncrementalSolveOutcome::SinkFailed(error) => {
                panic!("the in-memory sink cannot fail: {error:?}")
            }
        }
    }

    /// Loads `formula` into a warm object, reserving the formula's declared
    /// variable count first so a variable that occurs in no clause exists on
    /// both engines rather than only on the one-shot side.
    fn load(solver: &mut NativeIncrementalCdcl<AtMostOne>, formula: &CnfFormula) {
        solver.reserve(formula.variable_count());
        for clause in formula.clauses() {
            solver.add_clause(clause.lits());
        }
    }

    /// Whether `model` satisfies every clause in `clauses` **and** the
    /// at-most-one constraint over `group`.
    ///
    /// The theory constraint is replayed too, deliberately: a model that
    /// satisfies the CNF but violates the theory is exactly the wrong answer a
    /// CDCL(T) engine can give, and a check that replayed only the clauses
    /// would accept it.
    fn model_is_valid(model: &[bool], clauses: &[&[i64]], group: &[usize]) -> bool {
        let satisfies = |clause: &&[i64]| {
            clause.iter().any(|&value| {
                let index = usize::try_from(value.abs()).expect("index") - 1;
                model.get(index).copied().unwrap_or(false) == (value > 0)
            })
        };
        let true_in_group = group
            .iter()
            .filter(|&&var| model.get(var).copied().unwrap_or(false))
            .count();
        clauses.iter().all(satisfies) && true_in_group <= 1
    }

    fn verdict_only() -> TheorySolveOptions {
        TheorySolveOptions {
            record_proof: false,
            ..TheorySolveOptions::default()
        }
    }

    /// The option sets equivalence is measured under.
    ///
    /// The defaults alone would not measure the option plumbing at all: with
    /// `search_profile: Shipped` and `target_rephase: true`, every line of
    /// `with_theory` that copies an option into the `Cdcl` writes the value the
    /// constructor already installed, so deleting those lines changes nothing
    /// and a suite that only ran the defaults would be blind to it. The second
    /// row is the `CdclT`-shaped one a migrating route asks for (`CdclT`
    /// decides TRUE first and does no target rephasing, per
    /// `TheorySolveOptions`' own doc) and the third moves the search profile,
    /// so between them every field `with_theory` copies differs from the
    /// default in at least one row.
    fn option_sets() -> [(&'static str, TheorySolveOptions); 3] {
        [
            ("shipped defaults", verdict_only()),
            (
                "CdclT-shaped",
                TheorySolveOptions {
                    initial_phase: true,
                    target_rephase: false,
                    search_profile: crate::SearchProfile::ModeSwitching,
                    record_proof: false,
                    ..TheorySolveOptions::default()
                },
            ),
            (
                "scheduled phase",
                TheorySolveOptions {
                    search_profile: crate::SearchProfile::ScheduledPhase,
                    record_proof: false,
                    ..TheorySolveOptions::default()
                },
            ),
        ]
    }

    // ---------------------------------------------------------------- decides

    /// The capability itself: a theory paired with a solver that outlives one
    /// solve, deciding something across three solves with clauses added between
    /// them.
    #[test]
    fn a_warm_theory_solver_decides_across_solves_with_clauses_added_between() {
        // Group {x1, x2}: at most one of them true.
        let mut solver = NativeIncrementalCdcl::warm_theory(AtMostOne::new(&[0, 1]));

        // Solve 1: nothing constrains anything. Satisfiable.
        solver.add_clause(&lits(&[1, 2, 3]));
        let first = solver.solve(&[], None, budget());
        assert!(
            matches!(first, IncrementalSolveOutcome::Sat(_)),
            "first solve: {first:?}"
        );

        // Solve 2: force x1. Still satisfiable — the theory only forbids x2
        // alongside it, and x3 can carry the first clause.
        solver.add_clause(&lits(&[1]));
        let second = solver.solve(&[], None, budget());
        let IncrementalSolveOutcome::Sat(model) = second else {
            panic!("second solve: {second:?}");
        };
        assert!(model.values()[0], "x1 is forced true");
        assert!(
            !model.values()[1],
            "the THEORY must rule out x2: the Boolean side alone permits it"
        );

        // Solve 3: force x2 as well. Now the theory refutes, and the Boolean
        // side on its own cannot — {[1,2,3], [1], [2]} is propositionally
        // satisfiable.
        solver.add_clause(&lits(&[2]));
        let third = solver.solve(&[], None, budget());
        assert_eq!(
            from_warm(&third),
            Verdict::Unsat,
            "the theory must refute: {third:?}"
        );

        // Control: the same clause set with NO theory is satisfiable, so solve 3
        // measured the theory and not the clauses.
        let mut boolean_only = NativeIncrementalCdcl::new();
        for clause in [&[1i64, 2, 3][..], &[1][..], &[2][..]] {
            boolean_only.add_clause(&lits(clause));
        }
        assert!(
            matches!(
                boolean_only.solve(&[], None, budget()),
                IncrementalSolveOutcome::Sat(_)
            ),
            "control: the clause set alone must be satisfiable"
        );
    }

    /// Assumptions still work with a theory attached, and an `unsat` under
    /// assumptions is reported as such rather than as a refutation.
    #[test]
    fn assumptions_hold_for_one_solve_and_their_core_is_reported() {
        let mut solver = NativeIncrementalCdcl::warm_theory(AtMostOne::new(&[0, 1]));
        solver.add_clause(&lits(&[1, 3]));
        solver.add_clause(&lits(&[2, 3]));

        // Assuming both group atoms is theory-inconsistent.
        let assumed = solver.solve(&lits(&[1, 2]), None, budget());
        assert!(
            matches!(
                assumed,
                IncrementalSolveOutcome::Unsat | IncrementalSolveOutcome::UnsatUnderAssumptions(_)
            ),
            "assuming both mutex atoms must fail: {assumed:?}"
        );

        // Without the assumptions the very same database is satisfiable, which
        // is what makes the line above a statement about the assumptions.
        let free = solver.solve(&[], None, budget());
        assert!(
            matches!(free, IncrementalSolveOutcome::Sat(_)),
            "the database alone must be satisfiable: {free:?}"
        );
    }

    // ------------------------------------------------------------ equivalence

    /// Every query below is decided the same way by the warm object and by the
    /// one-shot entry point, **including the give-up reason**.
    ///
    /// Run with one fresh warm object per query, so this isolates "the warm
    /// constructor decides correctly" from "warmth preserves verdicts", which
    /// the next test covers separately.
    #[test]
    fn a_warm_solve_and_a_one_shot_solve_agree_on_verdict_and_model() {
        struct Case {
            name: &'static str,
            vars: usize,
            clauses: &'static [&'static [i64]],
            group: &'static [usize],
            conflicts: usize,
        }

        let cases = [
            Case {
                name: "theory-refuted, Boolean-satisfiable",
                vars: 3,
                clauses: &[&[1], &[2], &[3]],
                group: &[0, 1],
                conflicts: 100_000,
            },
            Case {
                name: "satisfiable, theory prunes one branch",
                vars: 3,
                clauses: &[&[1], &[2, 3], &[-2, -3]],
                group: &[0, 1],
                conflicts: 100_000,
            },
            Case {
                name: "Boolean-refuted, theory silent",
                vars: 2,
                clauses: &[&[1], &[-1]],
                group: &[0, 1],
                conflicts: 100_000,
            },
            Case {
                name: "satisfiable, theory never fires",
                vars: 4,
                clauses: &[&[1, 2], &[-1, 3], &[-3, 4]],
                group: &[8, 9],
                conflicts: 100_000,
            },
            Case {
                // A zero budget admits no search at all on either engine, so
                // both must give up for the same reason rather than one of them
                // answering. This is the give-up-reason arm.
                name: "zero conflict budget: ResourceOut on both",
                vars: 3,
                clauses: &[&[1], &[2], &[3]],
                group: &[0, 1],
                conflicts: 0,
            },
        ];

        for case in cases {
            let f = formula(case.vars, case.clauses);
            for (profile, options) in option_sets() {
                let mut one_shot_theory = AtMostOne::new(case.group);
                let (one_shot, _stats) = solve_with_theory_and_drat_proof_with_options(
                    &f,
                    &mut one_shot_theory,
                    None,
                    case.conflicts,
                    options,
                );

                let mut warm =
                    NativeIncrementalCdcl::with_theory(AtMostOne::new(case.group), options);
                load(&mut warm, &f);
                let warm_outcome = warm.solve(&[], None, case.conflicts);

                assert_eq!(
                    from_warm(&warm_outcome),
                    from_one_shot(&one_shot),
                    "{} under {profile}: warm {warm_outcome:?} vs one-shot {one_shot:?}",
                    case.name
                );
            }
        }
    }

    /// The harder equivalence claim: after each batch of added clauses, the
    /// **warm** object (which has been running since the first batch) agrees
    /// with a **fresh one-shot** run over everything accumulated so far.
    ///
    /// This is the property a migration actually needs, and it is the one that
    /// retained learned clauses, retained activities and a retained theory could
    /// break.
    #[test]
    fn a_warm_object_agrees_with_a_fresh_one_shot_after_every_batch() {
        let batches: &[&[&[i64]]] = &[
            &[&[1, 2, 3], &[-1, 4]],
            &[&[-4, 5], &[-5, 2]],
            &[&[1]],
            &[&[2]],
        ];
        let group = &[0usize, 1];
        let vars = 5;

        for (profile, options) in option_sets() {
            run_batches(batches, group, vars, profile, options);
        }
    }

    fn run_batches(
        batches: &[&[&[i64]]],
        group: &[usize],
        vars: usize,
        profile: &str,
        options: TheorySolveOptions,
    ) {
        let mut warm = NativeIncrementalCdcl::with_theory(AtMostOne::new(group), options);
        warm.reserve(vars);

        let mut accumulated: Vec<&[i64]> = Vec::new();
        let mut saw_sat = false;
        let mut saw_unsat = false;

        for (index, batch) in batches.iter().enumerate() {
            for clause in *batch {
                warm.add_clause(&lits(clause));
                accumulated.push(clause);
            }
            let warm_outcome = warm.solve(&[], None, budget());

            let f = formula(vars, &accumulated);
            let mut fresh_theory = AtMostOne::new(group);
            let (one_shot, _stats) = solve_with_theory_and_drat_proof_with_options(
                &f,
                &mut fresh_theory,
                None,
                budget(),
                options,
            );

            let warm_verdict = from_warm(&warm_outcome);
            let one_shot_verdict = from_one_shot(&one_shot);
            match &warm_verdict {
                Verdict::Sat(_) => saw_sat = true,
                Verdict::Unsat => saw_unsat = true,
                other => panic!("batch {index} under {profile}: unexpected {other:?}"),
            }
            assert_eq!(
                core::mem::discriminant(&warm_verdict),
                core::mem::discriminant(&one_shot_verdict),
                "batch {index} under {profile}: warm {warm_outcome:?} vs one-shot {one_shot:?}"
            );
            if let Verdict::Sat(warm_model) = &warm_verdict {
                // Model EQUALITY is deliberately not asserted here, and the
                // reason is a measured property of warmth rather than a
                // weakness of this object: a warm solver enters its second
                // solve holding the previous solve's SAVED PHASES, while a
                // fresh one-shot starts from `initial_phase`. Measured on batch
                // 1 under the `CdclT`-shaped options, warm returns
                // `[F,F,T,F,F]` where one-shot returns `[F,T,T,T,T]`; both
                // satisfy the clauses and the theory.
                //
                // That is the hazard `TheorySolveOptions` already names — a
                // model-based consumer can lose a verdict on a
                // different-but-correct model — and it is INHERENT to moving a
                // route from a one-shot engine onto a warm one, not something
                // this constructor could arrange away. Any such migration has
                // to re-measure its own consumer; it cannot inherit this test's
                // result.
                //
                // What IS asserted is the part that must hold: the model is
                // valid, against the clauses AND against the theory.
                assert!(
                    model_is_valid(warm_model, &accumulated, group),
                    "batch {index} under {profile}: warm model {warm_model:?} does not \
                     satisfy the accumulated clauses and the theory"
                );
            }
        }

        // The sequence must actually exercise both verdicts, or the loop above
        // is a check on one answer repeated.
        assert!(
            saw_sat,
            "{profile}: no batch was satisfiable, the fixture proves nothing"
        );
        assert!(
            saw_unsat,
            "{profile}: no batch was unsatisfiable, the theory never fired"
        );
    }

    // ------------------------------------------------------------------ warmth

    /// Warm means warm: learned clauses and the cumulative conflict count
    /// survive a solve boundary, and the *same theory instance* is still
    /// attached.
    #[test]
    fn learned_clauses_and_the_theory_instance_both_survive_a_solve_boundary() {
        // A formula that costs conflicts: at-most-one over a group of five, with
        // the Boolean side asserting a five-way disjunction and pairwise
        // constraints that force the search to backtrack.
        let group: Vec<usize> = (0..5).collect();
        let mut solver = NativeIncrementalCdcl::warm_theory(AtMostOne::new(&group));
        solver.add_clause(&lits(&[1, 2, 3, 4, 5]));
        for a in 1..=5i64 {
            solver.add_clause(&lits(&[-a, 6]));
        }
        solver.add_clause(&lits(&[-6, 7]));

        let first = solver.solve(&[], None, budget());
        assert!(
            matches!(first, IncrementalSolveOutcome::Sat(_)),
            "first solve: {first:?}"
        );
        let asserts_after_first = solver.theory().asserts;
        assert!(
            asserts_after_first > 0,
            "the theory must have been consulted at all"
        );
        let learned_after_first = solver.learned_clause_count();

        let second = solver.solve(&[], None, budget());
        assert!(
            matches!(second, IncrementalSolveOutcome::Sat(_)),
            "second solve: {second:?}"
        );
        assert!(
            solver.learned_clause_count() >= learned_after_first,
            "learned clauses must survive: {} then {}",
            learned_after_first,
            solver.learned_clause_count()
        );
        assert!(
            solver.theory().asserts > asserts_after_first,
            "the SAME theory instance must be reused across solves: asserts went {} -> {}",
            asserts_after_first,
            solver.theory().asserts
        );
        assert_eq!(solver.solve_count(), 2);

        // The theory's own registration — the group it was built with — is
        // untouched by the boundary, which is the half of its state that must
        // NOT be reset.
        assert_eq!(solver.theory().group, group);
    }

    /// The theory comes back with a balanced push/pop stack, so a caller that
    /// keeps using it is not handed a solver-shaped residue.
    #[test]
    fn into_theory_returns_a_balanced_theory() {
        let mut solver = NativeIncrementalCdcl::warm_theory(AtMostOne::new(&[0, 1]));
        solver.add_clause(&lits(&[1, 2, 3]));
        solver.add_clause(&lits(&[-1, 2]));
        let outcome = solver.solve(&[], None, budget());
        assert!(matches!(outcome, IncrementalSolveOutcome::Sat(_)));

        let theory = solver.into_theory();
        assert!(
            theory.max_depth > 0,
            "the search must have pushed at all, or balance is trivial"
        );
        assert_eq!(
            theory.depth, 0,
            "push/pop must balance across the solve boundary"
        );
        assert!(
            theory.asserted.is_empty(),
            "every assertion must be undone, including the level-zero ones: {:?}",
            theory.asserted
        );
        assert!(theory.marks.is_empty(), "marks: {:?}", theory.marks);
    }

    // ------------------------------------------------------------- the invariant

    /// **The guard.** A solve boundary must return the theory to its pre-solve
    /// assertion state, and the level-zero assertions are the half that the
    /// per-decision-level pops cannot reach.
    ///
    /// Without the per-solve theory epoch, the second solve re-propagates
    /// `initial_units` and asserts `x1` into a theory that is still holding the
    /// `x1` of the first solve. `AtMostOne` then sees two group atoms asserted,
    /// refutes, and the object answers **`Unsat` on a database whose only
    /// clause is `[x1]`** — a wrong verdict, not a slowdown.
    ///
    /// Mutation that kills this test: delete the `theory_epoch` arm of
    /// `Cdcl::reset_search_state`, or the `open_theory_epoch` call in
    /// `NativeIncrementalCdcl::solve`.
    #[test]
    fn a_solve_boundary_must_not_re_assert_into_a_theory_that_never_forgot() {
        let mut solver = NativeIncrementalCdcl::warm_theory(AtMostOne::new(&[0, 1]));
        // `[x1]` forces x1 at level ZERO on every solve, which is precisely the
        // assertion the decision-level pops cannot undo. The other two clauses
        // force at least one decision, so the search has levels to pop and the
        // level-zero case is not the only thing being tested.
        solver.add_clause(&lits(&[1]));
        solver.add_clause(&lits(&[2, 3]));
        solver.add_clause(&lits(&[-2, -3]));

        let first = solver.solve(&[], None, budget());
        assert!(
            matches!(first, IncrementalSolveOutcome::Sat(_)),
            "first solve must be satisfiable: {first:?}"
        );

        let second = solver.solve(&[], None, budget());
        assert!(
            matches!(second, IncrementalSolveOutcome::Sat(_)),
            "SECOND solve of an UNCHANGED satisfiable database returned {second:?}. The \
             theory was re-asserted on top of the previous solve's state instead of being \
             returned to it."
        );

        let third = solver.solve(&[], None, budget());
        assert!(
            matches!(third, IncrementalSolveOutcome::Sat(_)),
            "third solve: {third:?}"
        );

        // And the theory really did see x1 three times over — once per solve —
        // rather than the boundary having been made safe by the driver simply
        // not telling it anything the second time round.
        let theory = solver.into_theory();
        assert!(
            theory.asserts >= 3,
            "the theory must have been re-told about the database on each solve, got {} \
             asserts over three solves",
            theory.asserts
        );
        assert_eq!(theory.depth, 0, "balanced after three solves");
    }

    /// A theory that registers `batch` fresh atoms the first time it is asked
    /// and none afterwards, recording every variable it is asserted about.
    ///
    /// Dynamic atom registration is the one piece of theory state that must
    /// NOT be undone at a solve boundary, so it is the direct test of the
    /// registration-versus-assertions split the per-solve epoch rests on.
    #[derive(Debug)]
    struct RegisteringTheory {
        batch: usize,
        registered: bool,
        seen_vars: Vec<usize>,
        depth: isize,
    }

    impl NativeTheory for RegisteringTheory {
        fn assert(&mut self, var: usize, _value: bool) -> Result<(), Vec<CnfLit>> {
            if !self.seen_vars.contains(&var) {
                self.seen_vars.push(var);
            }
            Ok(())
        }

        fn push(&mut self) {
            self.depth += 1;
        }

        fn pop(&mut self) {
            self.depth -= 1;
        }

        fn propagate_into(&mut self, _queue: &mut PropagationQueue) {}

        fn take_new_atoms(&mut self) -> usize {
            if self.registered {
                return 0;
            }
            self.registered = true;
            self.batch
        }
    }

    /// Atom registration survives a solve boundary — it is the half of the
    /// theory's state the epoch must NOT undo — and the core appends the new
    /// variables at its **current** variable count.
    ///
    /// That second half is a contract, not a detail, and it is the one a warm
    /// CDCL(T) client has to meet. `axeyum_solver::native_cdclt`'s
    /// `NativeTheoryAdapter` keeps its own `next_var` counter and mirrors the
    /// core's growth with no callback, which is exact on a one-shot path —
    /// where the variable count is fixed at construction and only
    /// `register_theory_atoms` moves it — and **stale on a warm one**, where
    /// `add_clause` moves it between solves with the adapter never told. Its
    /// own `debug_assert_eq!(self.atom_for_var.len(), var, "variable indices
    /// are dense")` is the assertion that would fire.
    ///
    /// So this test pins the observable a warm client must read —
    /// `variable_count()` — rather than the one the adapter currently assumes.
    #[test]
    fn atom_registration_survives_a_solve_boundary_and_appends_at_the_current_count() {
        let mut solver = NativeIncrementalCdcl::warm_theory(RegisteringTheory {
            batch: 2,
            registered: false,
            seen_vars: Vec::new(),
            depth: 0,
        });
        solver.add_clause(&lits(&[1, 2]));
        let before = solver.variable_count();
        assert_eq!(before, 2, "two variables so far");

        let first = solver.solve(&[], None, budget());
        assert!(
            matches!(first, IncrementalSolveOutcome::Sat(_)),
            "first solve: {first:?}"
        );
        let after_first = solver.variable_count();
        assert_eq!(
            after_first,
            before + 2,
            "the core must append the two registered atoms at its current count"
        );
        assert!(
            solver.theory().registered,
            "the theory must have been asked for atoms"
        );

        // A clause added between solves introduces variable 9 (index 8), so the
        // namespace grows by something that is NOT an atom registration. This
        // is the growth a mirroring adapter does not see.
        solver.add_clause(&lits(&[9]));
        let after_clause = solver.variable_count();
        assert_eq!(
            after_clause, 9,
            "add_clause grows the namespace with no theory involvement"
        );

        let second = solver.solve(&[], None, budget());
        assert!(
            matches!(second, IncrementalSolveOutcome::Sat(_)),
            "second solve: {second:?}"
        );

        // Registration was NOT repeated: the theory is the same instance and
        // still believes it has registered, so the boundary undid assertions
        // and left registration alone — which is the whole design.
        assert_eq!(
            solver.variable_count(),
            after_clause,
            "no second round of atom registration"
        );

        let theory = solver.into_theory();
        assert_eq!(theory.depth, 0, "balanced");
        assert!(
            theory.seen_vars.len() >= 3,
            "the theory must have been told about the registered atoms and the \
             clause variables, got {:?}",
            theory.seen_vars
        );
    }

    /// The `NullTheory` warm object takes no epoch at all, so nothing above
    /// changed the Boolean warm path. `HAS_THEORY` is `false`, so the epoch code
    /// is not merely skipped at run time — it is not compiled.
    #[test]
    fn the_boolean_warm_path_takes_no_theory_epoch() {
        let mut solver = NativeIncrementalCdcl::new();
        solver.add_clause(&lits(&[1]));
        solver.add_clause(&lits(&[2, 3]));
        for round in 0..3 {
            let outcome = solver.solve(&[], None, budget());
            assert!(
                matches!(outcome, IncrementalSolveOutcome::Sat(_)),
                "round {round}: {outcome:?}"
            );
        }
        assert_eq!(solver.solve_count(), 3);
    }

    // -------------------------------------------------------------- evidence

    /// With recording on, a warm refutation comes back as the ADR-1704
    /// two-stream artifact and the artifact checks.
    #[test]
    fn a_warm_refutation_carries_a_checkable_two_stream_artifact() {
        let options = TheorySolveOptions {
            record_proof: true,
            ..TheorySolveOptions::default()
        };
        let mut solver = NativeIncrementalCdcl::with_theory(AtMostOne::new(&[0, 1]), options);
        assert!(solver.records_proof());
        solver.add_clause(&lits(&[1]));
        solver.add_clause(&lits(&[2]));

        let outcome = solver.solve(&[], None, budget());
        assert_eq!(from_warm(&outcome), Verdict::Unsat, "{outcome:?}");

        let artifact = solver
            .theory_refutation()
            .expect("recording is on, so the artifact is present");
        assert!(
            artifact.theory_lemma_count() > 0,
            "the refutation is the theory's: it must name the lemmas it assumed"
        );
        assert_eq!(
            artifact.theory_lemma_count(),
            solver.theory_lemma_count(),
            "the artifact's lemma count is the object's, not a second opinion"
        );
        match artifact.check() {
            crate::TheoryRefutationCheck::CheckedModuloLemmas { lemmas } => {
                assert_eq!(lemmas, artifact.theory_lemma_count());
            }
            other => panic!("the artifact must check modulo its lemmas, got {other:?}"),
        }
    }

    /// Recording is **off** by default on the warm path, and "no artifact" is
    /// reported as absent rather than as an empty one — `None` means not
    /// recorded, never "no lemma was assumed".
    #[test]
    fn the_warm_path_records_no_proof_by_default() {
        let mut solver = NativeIncrementalCdcl::warm_theory(AtMostOne::new(&[0, 1]));
        assert!(
            !solver.records_proof(),
            "ADR-1703 point 1: the warm path pays nothing for a proof it was not asked for"
        );
        solver.add_clause(&lits(&[1]));
        solver.add_clause(&lits(&[2]));
        let outcome = solver.solve(&[], None, budget());
        assert_eq!(from_warm(&outcome), Verdict::Unsat, "{outcome:?}");

        assert!(solver.proof_steps().is_empty());
        assert!(
            solver.theory_refutation().is_none(),
            "absent, not an empty artifact"
        );
        // ...while the lemma COUNT is still available, which is the distinction
        // `None` would otherwise destroy: the refutation did assume lemmas.
        assert!(
            solver.theory_lemma_count() > 0,
            "the search did assume theory lemmas even with recording off"
        );
    }
}
