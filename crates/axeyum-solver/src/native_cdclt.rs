//! Driving the **native** CDCL(T) core from a [`TheorySolver`] (plan slice
//! S7b step 2).
//!
//! S7a taught `axeyum_cnf`'s proof-producing core to decide under a theory and
//! to hand back the ADR-1704 two-stream artifact. Nothing reached it: every
//! shipping route builds `crate::cdclt::CdclT`, which is a second CDCL(T)
//! driver with the same watch scheme, the same order heap and the same clause
//! minimizer (S1, S1b ported all three verbatim) and **no proof output at all**.
//! A refutation from it arrives at the front door as `Evidence::Unsat(None)`
//! with no trusted step: the theory reasoning is trusted and uncounted.
//!
//! This module is the bridge. It is deliberately only the *one-shot* half of
//! the protocol, because that is all but one route needs:
//!
//! | route | protocol |
//! |---|---|
//! | `dl_online`, `lra_theory`, `lia_theory`, `euf_egraph`, `string_theory`, `uflra_online`, `uflia_online` | `CdclT::new` then **one** `solve` |
//! | `ufbv_online` | `with_inactive_variables`, `add_theory_variable`, `add_permanent_clause`, resumed `solve` |
//!
//! So the incremental refinement protocol — dormant variables, permanent
//! clauses, a resumed search retaining the learned database — has exactly one
//! client, and porting it is a separate slice. Everything else can move now.
//!
//! # The two literal conventions, negated once here
//!
//! [`TheorySolver`] carries **asserted literals**: an `assert` conflict is the
//! refuted conjunction (`¬⋀lits` is the lemma), and a propagation reason is the
//! antecedents that force the implied literal.
//! [`axeyum_cnf::theory::NativeTheory`] carries **clauses**: every literal is
//! false under the current assignment, and a propagation reason additionally
//! contains the implied literal itself.
//!
//! [`NativeTheoryAdapter`] is the single place that translation happens, and it
//! happens once per literal. Nothing downstream of it sees the asserted form
//! and nothing upstream of it sees the clause form.

use std::time::Instant;

use axeyum_cnf::theory::{
    ExplanationId as NativeExplanationId, FinalCheckOutcome as NativeFinalCheck, NativeTheory,
    PropagationQueue as NativeQueue, TheoryExplanation as NativeExplanation,
};
use axeyum_cnf::{
    CnfAssignment, CnfClause, CnfFormula, CnfLit, CnfVar, TheoryProofOutcome, TheoryRefutation,
    solve_with_theory_and_drat_proof,
};

use crate::cdclt::{Lit, Outcome};
use crate::euf_egraph::{
    ExplanationId, FinalCheckOutcome, PropagationQueue, TheoryExplanation, TheoryLit, TheorySolver,
};

/// What a native CDCL(T) solve produced.
///
/// `Unsat` carries the ADR-1704 artifact rather than a bare verdict, which is
/// the whole reason this route exists: a `CdclT` refutation has no artifact to
/// carry, so the theory reasoning behind it is trusted and *uncounted*.
#[derive(Debug, Clone)]
pub(crate) enum NativeSolveOutcome {
    /// A Boolean- and theory-consistent total assignment. The theory is left in
    /// that state, exactly as `CdclT::solve` leaves it, so the caller builds its
    /// model from the theory plus [`NativeModel`] for the Boolean leaves.
    Sat(NativeModel),
    /// Unsatisfiable modulo the enumerated theory lemmas.
    Unsat(Box<TheoryRefutation>),
    /// Undecided: the deadline passed, the theory step budget was exhausted, or
    /// the theory could not substantiate an answer. Never a verdict.
    Unknown,
}

impl NativeSolveOutcome {
    /// The bare verdict, for a caller that only needs to branch the way it
    /// branched on `CdclT::solve`'s [`Outcome`].
    pub(crate) fn outcome(&self) -> Outcome {
        match self {
            NativeSolveOutcome::Sat(_) => Outcome::Sat,
            NativeSolveOutcome::Unsat(_) => Outcome::Unsat,
            NativeSolveOutcome::Unknown => Outcome::Unknown,
        }
    }
}

/// The Boolean assignment behind a native `sat`, in the shape the routes'
/// model-assembly code already expects (`CdclT::value`).
#[derive(Debug, Clone)]
pub(crate) struct NativeModel {
    assignment: CnfAssignment,
    /// Variables that occur in no clause and were therefore never decided.
    /// `CdclT::value` reports `None` for these; the native core defaults them
    /// `false` in a total assignment. Reporting `None` keeps the routes'
    /// model-injection behaviour identical rather than adding bindings for
    /// symbols the skeleton never constrained.
    occurring: Vec<bool>,
}

impl NativeModel {
    /// The value of `var`, or `None` when the search never assigned it — the
    /// same contract as `CdclT::value`.
    ///
    /// A variable beyond the initial count was appended for a dynamically
    /// registered atom, and the core marks every one of those branchable, so it
    /// is assigned in any total assignment: the `occurring` filter applies only
    /// to the variables the formula was built with.
    pub(crate) fn value(&self, var: usize) -> Option<bool> {
        if var < self.occurring.len() && !self.occurring[var] {
            return None;
        }
        self.assignment.values().get(var).copied()
    }
}

/// Wraps a [`TheorySolver`] so the native CDCL core can drive it.
///
/// Owns the atom↔variable map the native core does not keep: there, atoms *are*
/// variable indices; here atom `a` is variable `var_for_atom[a]`, seeded as the
/// identity over the first `theory_atom_count` variables (exactly what
/// `CdclT::new` builds) and extended on each dynamic registration.
struct NativeTheoryAdapter<'a, T: TheorySolver> {
    theory: &'a mut T,
    /// The atom a SAT variable stands for, `None` for a pure Tseitin variable.
    atom_for_var: Vec<Option<usize>>,
    /// The SAT variable an atom stands for.
    var_for_atom: Vec<usize>,
    /// The index the native core will give the next variable it appends for a
    /// registered atom. The core appends at `assign.len()` and grows by one per
    /// atom, so mirroring that counter keeps the map aligned with no callback.
    next_var: usize,
    /// The solver-side queue, kept for its allocation across rounds exactly as
    /// the native core keeps its own.
    queue: PropagationQueue,
}

impl<'a, T: TheorySolver> NativeTheoryAdapter<'a, T> {
    fn new(theory: &'a mut T, var_count: usize, theory_atom_count: usize) -> Self {
        assert!(
            theory_atom_count <= var_count,
            "every theory atom needs a SAT variable"
        );
        let mut atom_for_var = vec![None; var_count];
        for (atom, slot) in atom_for_var.iter_mut().take(theory_atom_count).enumerate() {
            *slot = Some(atom);
        }
        Self {
            theory,
            atom_for_var,
            var_for_atom: (0..theory_atom_count).collect(),
            next_var: var_count,
            queue: PropagationQueue::new(),
        }
    }

    /// A `TheoryLit` as the CNF literal that is TRUE when the atom holds the
    /// value the theory named.
    fn cnf_lit(&self, lit: TheoryLit) -> CnfLit {
        let positive = CnfLit::positive(
            CnfVar::new(self.var_for_atom[lit.atom]).expect("atom variable index in range"),
        );
        if lit.value {
            positive
        } else {
            positive.negated()
        }
    }

    /// The conflict CLAUSE for a refuted conjunction of asserted literals:
    /// `¬⋀core`, so every literal is false under the current assignment. This
    /// is the one negation the two conventions differ by.
    fn conflict_clause(&self, core: &[TheoryLit]) -> Vec<CnfLit> {
        core.iter().map(|&l| self.cnf_lit(l).negated()).collect()
    }

    /// The reason CLAUSE for `antecedents ⊨ implied`: `¬⋀antecedents ∨ implied`.
    /// Unit once every antecedent is asserted, which is the invariant 1-UIP
    /// analysis relies on.
    fn reason_clause(&self, antecedents: &[TheoryLit], implied: CnfLit) -> Vec<CnfLit> {
        let mut clause = self.conflict_clause(antecedents);
        clause.push(implied);
        clause
    }
}

impl<T: TheorySolver> NativeTheory for NativeTheoryAdapter<'_, T> {
    fn assert(&mut self, var: usize, value: bool) -> Result<(), Vec<CnfLit>> {
        // A pure Tseitin variable is not an atom and the theory is never told
        // about it — the same test `CdclT::assign` makes.
        let Some(atom) = self.atom_for_var.get(var).copied().flatten() else {
            return Ok(());
        };
        self.theory
            .assert(atom, value)
            .map_err(|core| self.conflict_clause(&core))
    }

    fn push(&mut self) {
        self.theory.push();
    }

    fn pop(&mut self) {
        self.theory.pop();
    }

    fn propagate_into(&mut self, queue: &mut NativeQueue) {
        // Taken out so the translation loop can borrow `self` immutably while
        // the theory has already finished writing; the allocation goes back.
        let mut solver_queue = core::mem::take(&mut self.queue);
        solver_queue.clear();
        self.theory.propagate_into(&mut solver_queue);
        for (lit, explanation) in solver_queue.entries() {
            let implied = self.cnf_lit(*lit);
            match explanation {
                TheoryExplanation::Eager(antecedents) => {
                    queue.push_eager(implied, self.reason_clause(antecedents, implied));
                }
                // The lazy channel survives the translation: nothing is
                // materialised until conflict analysis walks past the literal,
                // and `explain` below is told which literal it is explaining so
                // the asserted form can be turned back into a clause then.
                TheoryExplanation::Lazy(handle) => {
                    queue.push_lazy(implied, NativeExplanationId(handle.0));
                }
            }
        }
        self.queue = solver_queue;
    }

    fn final_check(&mut self) -> NativeFinalCheck {
        match self.theory.final_check() {
            FinalCheckOutcome::Sat => NativeFinalCheck::Sat,
            FinalCheckOutcome::Unknown => NativeFinalCheck::Unknown,
            FinalCheckOutcome::Conflict(TheoryExplanation::Eager(core)) => {
                NativeFinalCheck::Conflict(NativeExplanation::Eager(self.conflict_clause(&core)))
            }
            FinalCheckOutcome::Conflict(TheoryExplanation::Lazy(handle)) => {
                NativeFinalCheck::Conflict(NativeExplanation::Lazy(NativeExplanationId(handle.0)))
            }
        }
    }

    fn explain(
        &mut self,
        handle: NativeExplanationId,
        implied: Option<CnfLit>,
    ) -> Option<Vec<CnfLit>> {
        let asserted = self.theory.explain(ExplanationId(handle.0))?;
        Some(match implied {
            // A propagation reason: the implied literal plus one false literal
            // per antecedent.
            Some(lit) => self.reason_clause(&asserted, lit),
            // A conflict core: every literal false, nothing else.
            None => self.conflict_clause(&asserted),
        })
    }

    fn take_new_atoms(&mut self) -> usize {
        let fresh = self.theory.take_new_atoms();
        // The core appends `fresh` variables starting at its current variable
        // count, in order, immediately after this call. Mirroring the counter
        // here keeps the map aligned without the core having to report back —
        // and it must happen BEFORE the core asserts any of them.
        for _ in 0..fresh {
            let var = self.next_var;
            self.next_var += 1;
            debug_assert_eq!(self.atom_for_var.len(), var, "variable indices are dense");
            self.atom_for_var.push(Some(self.var_for_atom.len()));
            self.var_for_atom.push(var);
        }
        fresh
    }
}

/// Runs the native CDCL(T) core over `clauses` with `theory` attached — the
/// one-shot counterpart of `CdclT::new(..).solve(&mut theory)`.
///
/// `theory_atom_count` has the same meaning as `CdclT::new`'s: atoms `0 ..
/// theory_atom_count` are the first that many SAT variables, and every other
/// variable is a Tseitin variable the theory is never told about.
///
/// The conflict budget is unbounded on purpose. `CdclT` has none either; both
/// are bounded by the deadline and by the native core's `THEORY_STEP_BUDGET`,
/// and introducing a conflict cap here would turn searches `CdclT` decides into
/// `Unknown` for a reason unrelated to the engine swap.
pub(crate) fn solve_native<T: TheorySolver>(
    var_count: usize,
    theory_atom_count: usize,
    clauses: Vec<Vec<Lit>>,
    deadline: Option<Instant>,
    theory: &mut T,
) -> NativeSolveOutcome {
    let mut formula = CnfFormula::new(var_count);
    let mut occurring = vec![false; var_count];
    for clause in &clauses {
        let lits = clause
            .iter()
            .map(|l| {
                occurring[l.var] = true;
                let positive =
                    CnfLit::positive(CnfVar::new(l.var).expect("clause variable index in range"));
                if l.positive {
                    positive
                } else {
                    positive.negated()
                }
            })
            .collect::<Vec<_>>();
        // The only rejection is an out-of-range variable, which the map above
        // has already made impossible.
        formula
            .add_clause(CnfClause::new(lits))
            .expect("clause literals are in range");
    }
    let mut adapter = NativeTheoryAdapter::new(theory, var_count, theory_atom_count);
    match solve_with_theory_and_drat_proof(&formula, &mut adapter, deadline, usize::MAX) {
        TheoryProofOutcome::Sat(assignment) => NativeSolveOutcome::Sat(NativeModel {
            assignment,
            occurring,
        }),
        TheoryProofOutcome::Unsat(refutation) => NativeSolveOutcome::Unsat(Box::new(refutation)),
        TheoryProofOutcome::ResourceOut | TheoryProofOutcome::Interrupted => {
            NativeSolveOutcome::Unknown
        }
    }
}

#[cfg(test)]
mod tests;
