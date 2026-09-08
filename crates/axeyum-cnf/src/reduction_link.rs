//! The link between the formula a caller handed in and the formula a search
//! actually ran over — as a *checkable object* rather than a trusted assumption.
//!
//! # The gap this closes
//!
//! [ADR-1750] settled what a reducing pass owes: it records what it **derived**,
//! and the concatenation of that derivation with the search's own `DRAT` steps
//! is a proof of the original formula. [`crate::inprocess`] implements exactly
//! that, and [`crate::solve_with_drat_proof_inprocessed`] ships it end to end.
//!
//! That covers passes which only **weaken** the formula. It does not cover
//! passes which **renumber** it, and the shipping `QF_BV` backend runs one:
//! after BVE it calls [`crate::compact`], which densely renumbers the live
//! variables so the admission gate sees the real count. A search over the
//! compacted formula emits `DRAT` steps about *compacted* variables, while the
//! reducing prefix is about *original* ones — the two halves cannot be
//! concatenated, so the backend checked its proof against the reduced formula
//! and the BVE link was trusted rather than checked. ADR-1750 named this in its
//! own "Open" section.
//!
//! [ADR-1750]: https://github.com/../docs/research/09-decisions/adr-1750-a-reducing-pass-must-record-what-it-derived-not-what-it-deleted.md
//!
//! # What a link carries
//!
//! Two halves, because there are exactly two ways a pass can move the formula
//! away from the caller's:
//!
//! | a pass … | owes | carried by |
//! |---|---|---|
//! | weakens (adds/deletes clauses) | a `DRAT` derivation of what it added | [`ReductionLink::record`] |
//! | renumbers (a variable bijection) | the bijection | [`ReductionLink::rename`] |
//! | neither, but changes the formula | nothing it can express | [`ReductionLink::mark_unjustified`] |
//!
//! The prefix is stored in the **original** variable space at all times:
//! [`ReductionLink::record`] maps incoming steps through whatever renaming is
//! already composed. So passes may be interleaved with renamings in any order
//! and the link stays a single flat `DRAT` prefix plus a single composed
//! bijection — which is what makes it reusable rather than a BVE special case.
//!
//! # The flag that must not lie
//!
//! A checker that reports "checked against the original" when it checked
//! against the reduced formula is worse than no checker (`CLAUDE.md`). So the
//! coverage flag is **not** a parameter the caller sets: it is returned by the
//! same call that chose which formula to check against
//! ([`LinkedProofCheck::coverage`]), and the two cannot disagree because there
//! is only one place that decides. Every route to a [`ProofCoverage::Reduced`]
//! carries the reason with it.

use core::fmt;

#[cfg(not(target_arch = "wasm32"))]
use std::time::{Duration, Instant};
#[cfg(target_arch = "wasm32")]
use web_time::{Duration, Instant};

use crate::{
    CnfFormula, CnfLit, CnfVar, DratError, DratSink, DratStep, ProofSinkError, check_drat_backward,
};

/// Which formula an `unsat` proof was actually verified against.
///
/// Returned by [`ReductionLink::check_unsat`]; never constructed by a caller
/// who wants to *claim* a coverage level.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofCoverage {
    /// Verified against the formula the caller handed in. The reduction is part
    /// of the certificate, not part of the trusted base.
    Original,
    /// Verified only against the reduced formula the search ran over. The link
    /// from the original to it is **trusted, not checked**, for the stated
    /// reason.
    Reduced(ReducedReason),
}

impl ProofCoverage {
    /// Whether the check covered the caller's own formula.
    #[must_use]
    pub const fn is_original(&self) -> bool {
        matches!(self, Self::Original)
    }
}

/// Why a check fell back to the reduced formula.
///
/// An enum rather than a string so a caller can branch on the cause (and so a
/// new cause cannot be added silently as free-form prose).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReducedReason {
    /// A pass changed the formula in a way it could not express as `DRAT`.
    /// Carries the pass's own description.
    Unjustified(String),
    /// The concatenated proof would exceed the caller's step budget. Carries
    /// the step count that would have been checked and the budget.
    OverBudget {
        /// Steps the full proof would have had (prefix + search).
        steps: usize,
        /// The budget it exceeded.
        budget: usize,
    },
    /// A search step named a variable outside the renaming's domain — a
    /// producer bug, not a policy decision. Carries the offending index.
    RenamingOutOfRange(usize),
}

impl fmt::Display for ReducedReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unjustified(reason) => write!(f, "unjustified reduction: {reason}"),
            Self::OverBudget { steps, budget } => {
                write!(f, "proof of {steps} steps exceeds the {budget}-step budget")
            }
            Self::RenamingOutOfRange(index) => {
                write!(
                    f,
                    "search proof names variable {index}, outside the renaming"
                )
            }
        }
    }
}

/// The outcome of checking a search proof through a link.
///
/// [`Self::coverage`] and [`Self::verified`] are independent: a proof can be
/// verified against the reduced formula (`verified == true`, `coverage ==
/// Reduced(..)`), which is exactly the state this module exists to make
/// visible rather than to hide.
#[derive(Debug, Clone, PartialEq)]
pub struct LinkedProofCheck {
    /// Which formula the check ran against.
    pub coverage: ProofCoverage,
    /// Whether the proof verified **and** derived the empty clause.
    pub verified: bool,
    /// The checker's error, when a step failed to verify.
    pub error: Option<DratError>,
    /// Steps in the reduction prefix that were checked (zero when the check
    /// fell back to the reduced formula).
    pub prefix_steps: usize,
    /// Steps the search itself emitted.
    pub search_steps: usize,
    /// Wall time spent inside the checker.
    pub check_duration: Duration,
}

/// A checkable link from an original formula to the one a search ran over.
///
/// Build it with [`Self::identity`] and grow it as passes run: [`Self::record`]
/// for a pass that weakened the formula, [`Self::rename`] for one that
/// renumbered it, [`Self::mark_unjustified`] for one that did neither
/// expressibly. Then hand the search's own proof to [`Self::check_unsat`].
///
/// `Default` is [`Self::identity`]: no pass ran, so the search formula *is* the
/// original and a proof of one is a proof of the other.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ReductionLink {
    /// The reduction's own derivation, in derivation order, in the **original**
    /// variable space.
    prefix: Vec<DratStep>,
    /// `searched_to_original[i]` is the original index of searched variable `i`.
    /// `None` is the identity (no renaming pass ran).
    searched_to_original: Option<Vec<usize>>,
    /// Set by [`Self::mark_unjustified`]; once set, never cleared. The first
    /// reason wins, because it is the one that broke the chain.
    unjustified: Option<String>,
}

impl ReductionLink {
    /// A link across no reduction at all: empty prefix, identity renaming.
    #[must_use]
    pub fn identity() -> Self {
        Self::default()
    }

    /// Appends a pass's `DRAT` derivation, mapping it through whatever renaming
    /// is already composed so the prefix stays in the original variable space.
    ///
    /// Order is the caller's responsibility and is the same obligation
    /// [`crate::inprocess`] carries: each `Add` must be recorded while the
    /// clauses that justify it are still live.
    ///
    /// A step naming a variable outside the current renaming's domain cannot be
    /// mapped, so it breaks the link rather than being dropped — dropping an
    /// `Add` is precisely the corruption ADR-1750 measured as rejected 38 of 38
    /// times, and silently producing an *unrejectable* prefix instead would be
    /// worse.
    pub fn record<I: IntoIterator<Item = DratStep>>(&mut self, steps: I) {
        for step in steps {
            match self.lift_step(&step) {
                Some(lifted) => self.prefix.push(lifted),
                None => {
                    self.mark_unjustified(
                        "a recorded step named a variable outside the composed renaming",
                    );
                    return;
                }
            }
        }
    }

    /// Composes a variable renaming: `new_to_old[i]` is the index, in the space
    /// *before* this pass, of the renamed variable `i`.
    ///
    /// This is exactly [`crate::CompactMap`]'s `new_to_old`. Composing rather
    /// than replacing is what lets a second renumbering pass run later without
    /// the link having to know about the first.
    pub fn rename(&mut self, new_to_old: &[usize]) {
        let composed: Option<Vec<usize>> = match &self.searched_to_original {
            None => Some(new_to_old.to_vec()),
            Some(existing) => new_to_old
                .iter()
                .map(|&mid| existing.get(mid).copied())
                .collect(),
        };
        match composed {
            Some(map) => self.searched_to_original = Some(map),
            None => self.mark_unjustified(
                "a renaming referenced a variable outside the previous renaming's range",
            ),
        }
    }

    /// Records that a pass changed the formula in a way it cannot express as
    /// `DRAT`, so no proof over the reduced formula can be lifted to the
    /// original one.
    ///
    /// The first reason is kept: it is the one that broke the chain, and later
    /// passes' complaints are downstream of it.
    pub fn mark_unjustified(&mut self, reason: impl Into<String>) {
        if self.unjustified.is_none() {
            self.unjustified = Some(reason.into());
        }
    }

    /// Whether a proof over the searched formula can be lifted to the original.
    #[must_use]
    pub fn is_checkable(&self) -> bool {
        self.unjustified.is_none()
    }

    /// The reason the link is broken, if it is.
    #[must_use]
    pub fn unjustified_reason(&self) -> Option<&str> {
        self.unjustified.as_deref()
    }

    /// The reduction's derivation, in the original variable space.
    #[must_use]
    pub fn prefix(&self) -> &[DratStep] {
        &self.prefix
    }

    /// How many steps the prefix holds.
    #[must_use]
    pub fn prefix_len(&self) -> usize {
        self.prefix.len()
    }

    /// Whether a renaming pass has been composed into this link.
    #[must_use]
    pub fn has_renaming(&self) -> bool {
        self.searched_to_original.is_some()
    }

    /// Maps a literal from the searched variable space to the original one.
    /// `None` when the literal's variable is outside the renaming's domain.
    #[must_use]
    pub fn lift_lit(&self, lit: CnfLit) -> Option<CnfLit> {
        let original = match &self.searched_to_original {
            None => lit.var().index(),
            Some(map) => *map.get(lit.var().index())?,
        };
        let positive = CnfLit::positive(CnfVar::new(original).ok()?);
        Some(if lit.is_negated() {
            positive.negated()
        } else {
            positive
        })
    }

    /// Maps a whole step from the searched variable space to the original one.
    #[must_use]
    pub fn lift_step(&self, step: &DratStep) -> Option<DratStep> {
        let lift_all = |lits: &[CnfLit]| -> Option<Vec<CnfLit>> {
            lits.iter().map(|&lit| self.lift_lit(lit)).collect()
        };
        Some(match step {
            DratStep::Add(lits) => DratStep::Add(lift_all(lits)?),
            DratStep::Delete(lits) => DratStep::Delete(lift_all(lits)?),
        })
    }

    /// Wraps `inner` so every step written through it is first lifted into the
    /// original variable space.
    ///
    /// This is the streaming counterpart of [`Self::check_unsat`]: a search
    /// that writes to `link.lifting_sink(&mut file_sink)`, after the prefix has
    /// been written to the same sink, produces one on-disk `DRAT` proof of the
    /// original formula with no `Vec` of the whole thing in RAM. That is the
    /// only viable route at the sizes ADR-1750 measured (a 37.7 M-step BVE
    /// prefix).
    pub fn lifting_sink<'a, S: DratSink>(&'a self, inner: &'a mut S) -> LiftingSink<'a, S> {
        LiftingSink { link: self, inner }
    }

    /// Checks a search's `unsat` proof, against the **original** formula when
    /// the link allows it and against the reduced formula when it does not,
    /// reporting which in [`LinkedProofCheck::coverage`].
    ///
    /// `max_total_steps` bounds the concatenated proof: a prefix that would
    /// blow the caller's memory or time budget produces a
    /// [`ReducedReason::OverBudget`] fallback rather than a hang. Pass
    /// `usize::MAX` for no bound.
    ///
    /// Backward checking is used ([`check_drat_backward`]), which ADR-1750
    /// measured at 231x the forward checker's throughput on a corpus-scale
    /// proof; it only verifies the steps in the empty clause's dependency cone,
    /// which is what makes the prefix affordable at all.
    #[must_use]
    pub fn check_unsat(
        &self,
        original: &CnfFormula,
        reduced: &CnfFormula,
        search_proof: &[DratStep],
        max_total_steps: usize,
    ) -> LinkedProofCheck {
        let total = self.prefix.len().saturating_add(search_proof.len());
        if let Some(reason) = self.unjustified.clone() {
            return self.check_reduced(reduced, search_proof, ReducedReason::Unjustified(reason));
        }
        if total > max_total_steps {
            return self.check_reduced(
                reduced,
                search_proof,
                ReducedReason::OverBudget {
                    steps: total,
                    budget: max_total_steps,
                },
            );
        }

        let mut full = Vec::with_capacity(total);
        full.extend_from_slice(&self.prefix);
        for step in search_proof {
            let Some(lifted) = self.lift_step(step) else {
                // A search step outside the renaming's domain: the producer and
                // the link disagree about the formula. Fall back rather than
                // check a proof we know is mistranslated.
                let bad = out_of_range_var(self, step).unwrap_or(usize::MAX);
                return self.check_reduced(
                    reduced,
                    search_proof,
                    ReducedReason::RenamingOutOfRange(bad),
                );
            };
            full.push(lifted);
        }

        let start = Instant::now();
        let checked = check_drat_backward(original, &full);
        let check_duration = start.elapsed();
        LinkedProofCheck {
            coverage: ProofCoverage::Original,
            verified: matches!(checked, Ok(true)),
            error: checked.err(),
            prefix_steps: self.prefix.len(),
            search_steps: search_proof.len(),
            check_duration,
        }
    }

    /// The fallback half of [`Self::check_unsat`]: check the search's own proof
    /// against the formula it was produced from, and say so.
    fn check_reduced(
        &self,
        reduced: &CnfFormula,
        search_proof: &[DratStep],
        reason: ReducedReason,
    ) -> LinkedProofCheck {
        let start = Instant::now();
        let checked = check_drat_backward(reduced, search_proof);
        let check_duration = start.elapsed();
        LinkedProofCheck {
            coverage: ProofCoverage::Reduced(reason),
            verified: matches!(checked, Ok(true)),
            error: checked.err(),
            prefix_steps: 0,
            search_steps: search_proof.len(),
            check_duration,
        }
    }
}

/// The first searched-space variable in `step` that the link cannot map, for
/// the diagnostic in [`ReducedReason::RenamingOutOfRange`].
fn out_of_range_var(link: &ReductionLink, step: &DratStep) -> Option<usize> {
    let lits = match step {
        DratStep::Add(lits) | DratStep::Delete(lits) => lits,
    };
    lits.iter()
        .find(|&&lit| link.lift_lit(lit).is_none())
        .map(|lit| lit.var().index())
}

/// A [`DratSink`] that lifts every step from the searched variable space into
/// the original one before forwarding it. See [`ReductionLink::lifting_sink`].
///
/// A step it cannot lift is reported as a sink failure rather than dropped or
/// forwarded unmapped: the producer then surfaces an *undecided* verdict, which
/// is the workspace's standing contract for a proof that could not be written.
#[derive(Debug)]
pub struct LiftingSink<'a, S: DratSink> {
    link: &'a ReductionLink,
    inner: &'a mut S,
}

impl<S: DratSink> LiftingSink<'_, S> {
    fn lift(&self, lits: &[CnfLit]) -> Result<Vec<CnfLit>, ProofSinkError> {
        lits.iter()
            .map(|&lit| self.link.lift_lit(lit))
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| {
                ProofSinkError::new(
                    std::io::ErrorKind::InvalidData,
                    "a proof step named a variable outside the reduction link's renaming",
                )
            })
    }
}

impl<S: DratSink> DratSink for LiftingSink<'_, S> {
    fn add_clause(&mut self, lits: &[CnfLit]) -> Result<(), ProofSinkError> {
        let lifted = self.lift(lits)?;
        self.inner.add_clause(&lifted)
    }

    fn delete_clause(&mut self, lits: &[CnfLit]) -> Result<(), ProofSinkError> {
        let lifted = self.lift(lits)?;
        self.inner.delete_clause(&lifted)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        BveOptions, CnfClause, InprocessOptions, ProofSolveOutcome, VecProofSink, compact,
        eliminate_variables, inprocess_into, solve_with_drat_proof,
    };

    fn v(i: usize) -> CnfVar {
        CnfVar::new(i).expect("var")
    }
    fn p(i: usize) -> CnfLit {
        CnfLit::positive(v(i))
    }
    fn n(i: usize) -> CnfLit {
        CnfLit::positive(v(i)).negated()
    }
    fn formula(nvars: usize, clauses: &[&[CnfLit]]) -> CnfFormula {
        let mut f = CnfFormula::new(nvars);
        for c in clauses {
            f.add_clause(CnfClause::new(c.to_vec())).expect("in range");
        }
        f
    }

    /// 3 pigeons, 2 holes: unsatisfiable, and small enough that BVE refutes a
    /// good deal of it on its own.
    fn pigeonhole_3_2() -> CnfFormula {
        pigeonhole(3, 2, 0)
    }

    /// `pigeons` into `holes`, with every variable shifted up by `shift` and
    /// the declared width raised to match, so indices `0..shift` are declared
    /// but dead.
    ///
    /// The shift is not decoration: without it the live set after BVE is a
    /// contiguous prefix and [`compact`] is the **identity**, which makes any
    /// test of the renaming vacuous. `renamings_are_not_the_identity_here`
    /// pins that the shifted fixture really does renumber.
    fn pigeonhole(pigeons: usize, holes: usize, shift: usize) -> CnfFormula {
        let idx = |pigeon: usize, hole: usize| shift + pigeon * holes + hole;
        let mut f = CnfFormula::new(shift + pigeons * holes);
        for pigeon in 0..pigeons {
            f.add_clause(CnfClause::new(
                (0..holes).map(|hole| p(idx(pigeon, hole))).collect(),
            ))
            .expect("in range");
        }
        for hole in 0..holes {
            for a in 0..pigeons {
                for b in (a + 1)..pigeons {
                    f.add_clause(CnfClause::new(vec![n(idx(a, hole)), n(idx(b, hole))]))
                        .expect("in range");
                }
            }
        }
        f
    }

    /// Reduce + compact `f`, returning the compacted formula and the link.
    fn reduce_and_link(f: &CnfFormula) -> (CnfFormula, ReductionLink) {
        let mut sink = VecProofSink::new();
        let reduced = inprocess_into(f, InprocessOptions::preprocess(), None, &mut sink)
            .expect("VecProofSink is infallible");
        let (compacted, map) = compact(&reduced.formula);
        let mut link = ReductionLink::identity();
        link.record(sink.into_steps());
        link.rename(
            &(0..map.live_count())
                .map(|i| map.original_of(i))
                .collect::<Vec<_>>(),
        );
        (compacted, link)
    }

    #[test]
    fn identity_link_lifts_nothing_and_covers_the_original() {
        let f = pigeonhole_3_2();
        let ProofSolveOutcome::Unsat(proof) = solve_with_drat_proof(&f) else {
            panic!("pigeonhole 3/2 is unsat");
        };
        let link = ReductionLink::identity();
        let check = link.check_unsat(&f, &f, &proof, usize::MAX);
        assert_eq!(check.coverage, ProofCoverage::Original);
        assert!(
            check.verified,
            "identity link must verify: {:?}",
            check.error
        );
        assert_eq!(check.prefix_steps, 0);
    }

    /// Composition, which is the property that makes this reusable: renaming
    /// twice must equal renaming once by the composed map.
    #[test]
    fn renamings_compose() {
        let mut link = ReductionLink::identity();
        // First pass: dense 0,1,2 came from originals 2,5,7.
        link.rename(&[2, 5, 7]);
        // Second pass: dense 0,1 came from the *first* pass's 1,2 → originals 5,7.
        link.rename(&[1, 2]);
        assert_eq!(link.lift_lit(p(0)), Some(p(5)));
        assert_eq!(link.lift_lit(n(1)), Some(n(7)));
        assert_eq!(link.lift_lit(p(2)), None, "outside the composed domain");
    }

    #[test]
    fn recording_after_a_renaming_stores_original_space() {
        let mut link = ReductionLink::identity();
        link.rename(&[3, 4]);
        link.record([DratStep::Add(vec![p(0), n(1)])]);
        assert_eq!(link.prefix(), &[DratStep::Add(vec![p(3), n(4)])]);
    }

    #[test]
    fn an_unjustified_pass_forces_the_reduced_coverage() {
        let f = pigeonhole_3_2();
        let ProofSolveOutcome::Unsat(proof) = solve_with_drat_proof(&f) else {
            panic!("unsat");
        };
        let mut link = ReductionLink::identity();
        link.mark_unjustified("xor units are not RUP");
        let check = link.check_unsat(&f, &f, &proof, usize::MAX);
        assert!(matches!(
            check.coverage,
            ProofCoverage::Reduced(ReducedReason::Unjustified(_))
        ));
        assert!(check.verified, "still a valid proof of the reduced formula");
    }

    #[test]
    fn a_step_budget_forces_the_reduced_coverage() {
        let f = pigeonhole_3_2();
        let ProofSolveOutcome::Unsat(proof) = solve_with_drat_proof(&f) else {
            panic!("unsat");
        };
        let link = ReductionLink::identity();
        let check = link.check_unsat(&f, &f, &proof, 0);
        assert!(matches!(
            check.coverage,
            ProofCoverage::Reduced(ReducedReason::OverBudget { .. })
        ));
    }

    /// The renaming these end-to-end tests rely on is not the identity.
    ///
    /// Without this the two tests below would both pass for a link whose
    /// `rename` did nothing, because "lifted" and "unlifted" would be the same
    /// bytes. It is the control that makes them mean something.
    #[test]
    fn renamings_are_not_the_identity_here() {
        // Only the fixture the end-to-end tests use. `pigeonhole(3,2)` is NOT
        // usable here: ADR-1750 measured that BVE refutes it outright, so the
        // reduced formula has no live variables and there is nothing to
        // renumber — a real property of that instance, not a defect.
        let f = pigeonhole(4, 3, 1);
        let (_compacted, link) = reduce_and_link(&f);
        assert!(link.has_renaming(), "compaction must produce a renaming");
        let mut moved = false;
        let mut live = 0usize;
        while let Some(lit) = link.lift_lit(p(live)) {
            moved |= lit.var().index() != live;
            live += 1;
        }
        assert!(
            live > 0,
            "the reduced formula must still have live variables"
        );
        assert!(moved, "the shifted fixture must actually renumber");
    }

    /// THE end-to-end shape the backend needs: reduce, **compact**, search the
    /// compacted formula, and check the concatenation against the ORIGINAL.
    #[test]
    fn bve_then_compact_then_search_checks_against_the_original() {
        let f = pigeonhole(4, 3, 1);
        let (compacted, link) = reduce_and_link(&f);
        assert!(link.is_checkable());

        let ProofSolveOutcome::Unsat(search) = solve_with_drat_proof(&compacted) else {
            panic!("the compacted pigeonhole must still be unsat");
        };
        let check = link.check_unsat(&f, &compacted, &search, usize::MAX);
        assert_eq!(
            check.coverage,
            ProofCoverage::Original,
            "the link must be checkable"
        );
        assert!(
            check.verified,
            "compacted search proof must verify against the ORIGINAL formula: {:?}",
            check.error
        );
        assert!(
            check.prefix_steps > 0,
            "the passes must have derived something"
        );
        assert!(
            check.search_steps > 0,
            "the search must have derived something"
        );
    }

    /// The same shape, but with the search proof left in compacted numbering —
    /// i.e. what the backend did before this module existed. It must NOT verify
    /// against the original, or the test above would pass for a link that does
    /// nothing.
    ///
    /// Guarded against the vacuity ADR-1750 hit on the same family: if the
    /// prefix ALONE already derives the empty clause, the concatenation
    /// verifies whatever follows it and the control proves nothing.
    #[test]
    fn an_unlifted_search_proof_does_not_check_against_the_original() {
        let f = pigeonhole(4, 3, 1);
        let (compacted, link) = reduce_and_link(&f);
        assert_eq!(
            check_drat_backward(&f, link.prefix()),
            Ok(false),
            "the prefix alone must NOT refute, or this control is vacuous"
        );

        let ProofSolveOutcome::Unsat(search) = solve_with_drat_proof(&compacted) else {
            panic!("unsat");
        };
        let mut naive: Vec<DratStep> = link.prefix().to_vec();
        naive.extend_from_slice(&search);
        let naive_ok = matches!(check_drat_backward(&f, &naive), Ok(true));
        let lifted = link.check_unsat(&f, &compacted, &search, usize::MAX);
        assert!(
            lifted.verified,
            "lifted proof must verify: {:?}",
            lifted.error
        );
        assert!(
            !naive_ok,
            "the unlifted concatenation must NOT verify — otherwise the renaming is a no-op \
             and the lift is untested"
        );
    }

    /// A `LiftingSink` produces exactly what `lift_step` produces, so the
    /// streaming route and the in-RAM route cannot drift apart.
    #[test]
    fn lifting_sink_matches_lift_step() {
        let mut link = ReductionLink::identity();
        link.rename(&[2, 0, 5]);
        let steps = vec![
            DratStep::Add(vec![p(0), n(2)]),
            DratStep::Delete(vec![p(1)]),
        ];
        let mut out = VecProofSink::new();
        {
            let mut sink = link.lifting_sink(&mut out);
            for step in &steps {
                match step {
                    DratStep::Add(lits) => sink.add_clause(lits).expect("infallible"),
                    DratStep::Delete(lits) => sink.delete_clause(lits).expect("infallible"),
                }
            }
        }
        let expected: Vec<DratStep> = steps
            .iter()
            .map(|s| link.lift_step(s).expect("in range"))
            .collect();
        assert_eq!(out.into_steps(), expected);
    }

    /// A sink step outside the renaming is a reported failure, never a silently
    /// unmapped forward.
    #[test]
    fn lifting_sink_refuses_an_out_of_range_step() {
        let mut link = ReductionLink::identity();
        link.rename(&[0, 1]);
        let mut out = VecProofSink::new();
        let mut sink = link.lifting_sink(&mut out);
        assert!(sink.add_clause(&[p(9)]).is_err());
    }

    /// `record` must not silently drop a step it cannot map — it breaks the
    /// link, which downgrades coverage, which is visible.
    #[test]
    fn recording_an_unmappable_step_breaks_the_link() {
        let mut link = ReductionLink::identity();
        link.rename(&[0, 1]);
        link.record([DratStep::Add(vec![p(7)])]);
        assert!(!link.is_checkable());
        assert!(link.unjustified_reason().is_some());
    }

    /// Compaction on a formula BVE actually renumbers, checked against the
    /// `CompactMap`'s own `expand` so the two directions agree.
    #[test]
    fn rename_agrees_with_compact_map() {
        let f = formula(
            5,
            &[
                &[n(0), p(1)],
                &[n(0), p(2)],
                &[p(0), n(1), n(2)],
                &[p(1), p(3)],
            ],
        );
        let bve = eliminate_variables(&f, BveOptions::default());
        let (_compacted, map) = compact(&bve.formula);
        let mut link = ReductionLink::identity();
        link.rename(
            &(0..map.live_count())
                .map(|i| map.original_of(i))
                .collect::<Vec<_>>(),
        );
        for new in 0..map.live_count() {
            assert_eq!(
                link.lift_lit(p(new)).map(|l| l.var().index()),
                Some(map.original_of(new))
            );
        }
    }
}
