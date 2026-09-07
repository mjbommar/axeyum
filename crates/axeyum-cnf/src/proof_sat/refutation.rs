//! The ADR-1704 two-stream artifact: a Boolean refutation over the CNF
//! **extended by the enumerated theory lemmas as input clauses**.
//!
//! A theory lemma is not RUP against the CNF, so a CDCL(T) `unsat` is not a
//! DRAT refutation of the CNF and must never be labelled as one ([ADR-1704]).
//! What it *is* is a DRAT refutation of `cnf ++ lemmas`, plus a per-lemma
//! theory obligation that the propositional checker cannot see. This module is
//! that artifact and the composition that checks it.
//!
//! **The trusted base does not grow here.** [`crate::check_drat`] is called
//! unchanged; the whole contract is a statement about *which formula* it is
//! handed.
//!
//! # Why `extended` is carried and not computed
//!
//! [`TheoryRefutation`] holds four parts — `cnf`, `lemmas`, `extended`, and the
//! Boolean stream — and `extended` is **supplied by the producer**, not derived
//! from the other two. Deriving it would make ADR-1704's failure mode 4 (a
//! listed lemma absent from the formula the checker actually saw, or a clause
//! in that formula the lemma list does not name) unreachable, and a guard that
//! cannot fire is worse than no guard. Carrying it means
//! [`TheoryRefutation::check`] compares the two halves against the whole, and
//! the comparison has teeth
//! (`an_unlisted_extra_clause_is_a_lemma_list_mismatch`,
//! `a_listed_lemma_that_is_not_the_carried_one_is_a_mismatch`).
//!
//! # What this artifact CANNOT catch, and where that is caught instead
//!
//! A producer that files a theory lemma in `cnf` itself, and reports no
//! lemmas, hands over an artifact that is internally consistent and refutes
//! exactly what it says it refutes. **Nothing propositional can detect that** —
//! the clause carries no mark saying where it came from, and the checker has no
//! copy of the "real" CNF to compare against. ADR-1704's prohibition 1 is
//! therefore enforced at the *producer*: `Cdcl::install_theory_lemma_clause` is
//! the only route by which a theory-derived clause enters the database, and it
//! appends to `Cdcl::theory_lemmas` in the same statement. The test that this
//! stays true is `every_theory_origin_clause_is_enumerated`, which counts
//! input clauses in the arena rather than trusting the list.
//!
//! # The counting rule
//!
//! [`TheoryRefutation::theory_lemma_count`] is
//! `extended.clauses().len() - cnf.clauses().len()` — a subtraction over two
//! carried artifacts, computed on every call, never a field a producer writes.
//!
//! [ADR-1704]: ../../../../docs/research/09-decisions/adr-1704-cdclt-unsat-is-two-streams-a-boolean-refutation-over-cnf-plus-enumerated-theory-lemmas.md

use crate::{CnfClause, CnfFormula, CnfLit, DratError, DratStep, check_drat};

/// A CDCL(T) refutation as ADR-1704 defines it: the Boolean CNF exactly as
/// encoded, the enumerated theory lemmas in installation order, the extended
/// formula the checker is handed, and a Boolean DRAT stream over that extended
/// formula.
///
/// Construct one with [`TheoryRefutation::new`]; the native core produces one
/// through [`crate::solve_with_theory_and_drat_proof`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TheoryRefutation {
    cnf: CnfFormula,
    lemmas: Vec<Vec<CnfLit>>,
    extended: CnfFormula,
    boolean_stream: Vec<DratStep>,
}

/// Why [`TheoryRefutation::check`] declined an artifact. Each variant is one of
/// ADR-1704 section 4's failure modes and is a **soundness alarm**, not a
/// missing-checker report.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TheoryRefutationError {
    /// Mode 1: the Boolean stream does not check over the extended formula.
    BooleanStreamRejected(DratError),
    /// Mode 2: the Boolean stream verified but derived no empty clause, so it
    /// refutes nothing.
    NoEmptyClauseDerived,
    /// Mode 4: the extended formula is not `cnf` followed by `lemmas` — a lemma
    /// hidden among the input clauses, a listed lemma absent from the extended
    /// formula, or an input clause silently rewritten.
    LemmaListMismatch {
        /// Lemmas the artifact lists.
        listed: usize,
        /// Clauses the extended formula carries beyond the CNF's count.
        extra: usize,
    },
}

/// What checking a [`TheoryRefutation`] established.
///
/// Deliberately three-valued rather than a `bool`: "the Boolean half checks and
/// N theory lemmas are undischarged" is neither a pass nor a failure, and
/// collapsing it into either is the dishonesty ADR-1704 exists to prevent.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TheoryRefutationCheck {
    /// No theory lemma was used: this is a pure propositional refutation and
    /// the Boolean stream checks over the CNF itself (ADR-1704 mode 6).
    Verified,
    /// The Boolean stream checks over `cnf ++ lemmas`, and `lemmas` of them
    /// carry no theory-level discharge. **Not** a pass: the refutation is
    /// established modulo the theory (ADR-1704 mode 5).
    CheckedModuloLemmas {
        /// How many lemmas remain undischarged (always at least one).
        lemmas: usize,
    },
    /// The artifact is rejected (ADR-1704 section 4).
    Failed(TheoryRefutationError),
}

impl TheoryRefutation {
    /// Assembles the artifact from its four parts.
    ///
    /// Nothing is validated here — validation is [`Self::check`]'s job, and a
    /// constructor that refused a bad artifact would leave the checker with
    /// nothing to reject.
    #[must_use]
    pub fn new(
        cnf: CnfFormula,
        lemmas: Vec<Vec<CnfLit>>,
        extended: CnfFormula,
        boolean_stream: Vec<DratStep>,
    ) -> Self {
        Self {
            cnf,
            lemmas,
            extended,
            boolean_stream,
        }
    }

    /// Builds the artifact from a CNF, its lemmas and a stream, forming the
    /// extended formula as `cnf ++ lemmas` — the shape a well-behaved producer
    /// emits.
    ///
    /// # Panics
    ///
    /// Panics if a lemma names a variable outside the CNF's variable count,
    /// which no producer in this crate can do (a lemma is a clause over the
    /// search's own variables).
    #[must_use]
    pub fn from_cnf_and_lemmas(
        cnf: CnfFormula,
        lemmas: Vec<Vec<CnfLit>>,
        boolean_stream: Vec<DratStep>,
    ) -> Self {
        let mut extended = CnfFormula::new(cnf.variable_count());
        for clause in cnf.clauses() {
            extended
                .add_clause(CnfClause::new(clause.lits().to_vec()))
                .expect("the extended formula has the CNF's variable count");
        }
        for lemma in &lemmas {
            extended
                .add_clause(CnfClause::new(lemma.clone()))
                .expect("a theory lemma is a clause over the search's own variables");
        }
        Self::new(cnf, lemmas, extended, boolean_stream)
    }

    /// The Boolean CNF exactly as encoded.
    #[must_use]
    pub fn cnf(&self) -> &CnfFormula {
        &self.cnf
    }

    /// The enumerated theory lemmas, in installation order.
    #[must_use]
    pub fn lemmas(&self) -> &[Vec<CnfLit>] {
        &self.lemmas
    }

    /// The formula the checker is handed: `cnf` followed by `lemmas`, nothing
    /// interleaved and nothing reordered.
    #[must_use]
    pub fn extended(&self) -> &CnfFormula {
        &self.extended
    }

    /// The Boolean DRAT stream over [`Self::extended`].
    #[must_use]
    pub fn boolean_stream(&self) -> &[DratStep] {
        &self.boolean_stream
    }

    /// The ADR-1704 metric: how many theory lemmas this refutation assumed,
    /// **read off the artifact** as `|extended| - |cnf|` rather than asserted.
    ///
    /// Zero means the refutation is propositional and grades at the pure
    /// `sat-refutation` assurance level; anything else means it does not.
    #[must_use]
    pub fn theory_lemma_count(&self) -> usize {
        self.extended
            .clauses()
            .len()
            .saturating_sub(self.cnf.clauses().len())
    }

    /// Checks the artifact: the lemma-list contract, then `check_drat` over the
    /// extended formula, then the per-lemma discharge (no per-theory checker is
    /// wired yet, so every lemma is reported undischarged and counted).
    ///
    /// The composition is ADR-1704 section 2 verbatim, and the propositional
    /// checker is [`crate::check_drat`] unchanged.
    #[must_use]
    pub fn check(&self) -> TheoryRefutationCheck {
        let listed = self.lemmas.len();
        let extra = self
            .extended
            .clauses()
            .len()
            .saturating_sub(self.cnf.clauses().len());
        let mismatch = TheoryRefutationCheck::Failed(TheoryRefutationError::LemmaListMismatch {
            listed,
            extra,
        });
        if extra != listed || self.extended.clauses().len() < self.cnf.clauses().len() {
            return mismatch;
        }
        // The extension must be a *suffix*: the CNF's clauses come first and
        // unchanged, then exactly the listed lemmas in order. A lemma smuggled
        // in among the input clauses leaves the counts equal and is caught
        // here, which is the half of mode 4 a count alone cannot see.
        for (input, carried) in self.cnf.clauses().iter().zip(self.extended.clauses()) {
            if input.lits() != carried.lits() {
                return mismatch;
            }
        }
        for (lemma, carried) in self
            .lemmas
            .iter()
            .zip(&self.extended.clauses()[self.cnf.clauses().len()..])
        {
            if lemma.as_slice() != carried.lits() {
                return mismatch;
            }
        }
        match check_drat(&self.extended, &self.boolean_stream) {
            Err(error) => {
                TheoryRefutationCheck::Failed(TheoryRefutationError::BooleanStreamRejected(error))
            }
            Ok(false) => TheoryRefutationCheck::Failed(TheoryRefutationError::NoEmptyClauseDerived),
            Ok(true) => {
                let lemmas = self.theory_lemma_count();
                if lemmas == 0 {
                    TheoryRefutationCheck::Verified
                } else {
                    TheoryRefutationCheck::CheckedModuloLemmas { lemmas }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{TheoryRefutation, TheoryRefutationCheck, TheoryRefutationError};
    use crate::{CnfClause, CnfFormula, CnfLit, CnfVar, DratStep};

    fn lit(value: i64) -> CnfLit {
        let var = CnfVar::new(usize::try_from(value.unsigned_abs() - 1).unwrap()).unwrap();
        if value < 0 {
            CnfLit::positive(var).negated()
        } else {
            CnfLit::positive(var)
        }
    }

    fn formula(variable_count: usize, clauses: &[&[i64]]) -> CnfFormula {
        let mut f = CnfFormula::new(variable_count);
        for clause in clauses {
            f.add_clause(CnfClause::new(clause.iter().copied().map(lit).collect()))
                .unwrap();
        }
        f
    }

    /// ADR-1704's fixture: three asserted atoms, propositionally satisfiable,
    /// refuted only by the difference-logic negative cycle the lemma records.
    fn skeleton() -> CnfFormula {
        formula(3, &[&[1], &[2], &[3]])
    }

    fn lemma() -> Vec<CnfLit> {
        vec![lit(-1), lit(-2), lit(-3)]
    }

    #[test]
    fn the_two_stream_artifact_checks_modulo_its_one_lemma() {
        let artifact = TheoryRefutation::from_cnf_and_lemmas(
            skeleton(),
            vec![lemma()],
            vec![DratStep::Add(Vec::new())],
        );
        assert_eq!(artifact.theory_lemma_count(), 1);
        assert_eq!(
            artifact.check(),
            TheoryRefutationCheck::CheckedModuloLemmas { lemmas: 1 },
            "the Boolean half checks; the lemma is undischarged and counted"
        );
    }

    /// The same stream over the same CNF with the lemma dropped is rejected —
    /// so `CheckedModuloLemmas` above is about the extension, not about the
    /// checker accepting anything.
    #[test]
    fn dropping_the_lemma_makes_the_same_stream_fail() {
        let artifact = TheoryRefutation::from_cnf_and_lemmas(
            skeleton(),
            Vec::new(),
            vec![DratStep::Add(Vec::new())],
        );
        assert_eq!(artifact.theory_lemma_count(), 0);
        assert!(
            matches!(
                artifact.check(),
                TheoryRefutationCheck::Failed(TheoryRefutationError::BooleanStreamRejected(_))
            ),
            "without the lemma the empty clause is not RUP: {:?}",
            artifact.check()
        );
    }

    /// A lemma that does not close the formula cannot make the empty clause
    /// RUP, so it is rejected rather than counted.
    #[test]
    fn a_lemma_that_does_not_close_the_formula_is_rejected() {
        let weak = TheoryRefutation::from_cnf_and_lemmas(
            skeleton(),
            vec![vec![lit(-1), lit(2)]],
            vec![DratStep::Add(Vec::new())],
        );
        assert!(
            matches!(
                weak.check(),
                TheoryRefutationCheck::Failed(TheoryRefutationError::BooleanStreamRejected(_))
            ),
            "got {:?}",
            weak.check()
        );
    }

    /// ADR-1704 failure mode 4: the extended formula carries a clause the lemma
    /// list does not name.
    #[test]
    fn an_unlisted_extra_clause_is_a_lemma_list_mismatch() {
        let artifact = TheoryRefutation::new(
            skeleton(),
            Vec::new(),
            formula(3, &[&[1], &[2], &[3], &[-1, -2, -3]]),
            vec![DratStep::Add(Vec::new())],
        );
        assert_eq!(
            artifact.check(),
            TheoryRefutationCheck::Failed(TheoryRefutationError::LemmaListMismatch {
                listed: 0,
                extra: 1,
            })
        );
    }

    /// And the third: the counts agree but the carried clause is not the lemma
    /// that was listed.
    #[test]
    fn a_listed_lemma_that_is_not_the_carried_one_is_a_mismatch() {
        let artifact = TheoryRefutation::new(
            skeleton(),
            vec![vec![lit(-1), lit(-2)]],
            formula(3, &[&[1], &[2], &[3], &[-1, -2, -3]]),
            vec![DratStep::Add(Vec::new())],
        );
        assert_eq!(
            artifact.check(),
            TheoryRefutationCheck::Failed(TheoryRefutationError::LemmaListMismatch {
                listed: 1,
                extra: 1,
            })
        );
    }

    /// A refutation with no lemmas at all is a plain propositional one and is
    /// graded `Verified` — ADR-1704 mode 6.
    #[test]
    fn a_lemma_free_refutation_is_verified_outright() {
        let f = formula(1, &[&[1], &[-1]]);
        let artifact =
            TheoryRefutation::from_cnf_and_lemmas(f, Vec::new(), vec![DratStep::Add(Vec::new())]);
        assert_eq!(artifact.theory_lemma_count(), 0);
        assert_eq!(artifact.check(), TheoryRefutationCheck::Verified);
    }

    /// A stream that checks but never derives the empty clause refutes nothing
    /// (mode 2).
    #[test]
    fn a_stream_that_derives_no_empty_clause_is_failed_not_verified() {
        let f = formula(2, &[&[1], &[-1, 2]]);
        let artifact =
            TheoryRefutation::from_cnf_and_lemmas(f, Vec::new(), vec![DratStep::Add(vec![lit(2)])]);
        assert_eq!(
            artifact.check(),
            TheoryRefutationCheck::Failed(TheoryRefutationError::NoEmptyClauseDerived)
        );
    }
}
