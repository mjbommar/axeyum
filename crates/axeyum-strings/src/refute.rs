//! Word-level **refutation** (slice T-B.7) — the sole route to word-level
//! `unsat`, and only ever behind an independently re-checked derivation.
//!
//! [`refute_word_equations`] is the ADR-0053 `unsat` arm: it runs the T-B.3
//! [`infer`](crate::infer) fixpoint (the untrusted search) over the asserted
//! equalities and, on a reported [`Conflict`](crate::Conflict), only returns
//! [`RefuteOutcome::Unsat`] when [`check_conflict`] **independently re-derives**
//! that conflict from its cited premises. A disequality `a ≠ b` whose two sides
//! are placed in one class by a *direct* equality chain is likewise refuted, its
//! premise chain re-verified by [`check_equality`]. Everything else is
//! [`RefuteOutcome::Unknown`].
//!
//! # No search-based `unsat`
//!
//! This is **not** a search. An exhausted or over-budget arrangement search is
//! never `unsat` — that is [`solve_word_equations`](crate::solve_word_equations)'s
//! job and it has no `unsat` variant by construction (ADR-0053). Refutation only
//! reports `unsat` for a *self-evident, re-checked* contradiction:
//!
//! - a T-B.3 conflict (a constant clash at an aligned position) that
//!   [`check_conflict`] confirms; or
//! - a disequality contradicted by a directly-chained equality that
//!   [`check_equality`] confirms.
//!
//! Loops, parity/length arguments, and any conflict that only arises after an
//! inference step are conservatively left `unknown` — the checker rejects what it
//! cannot re-derive from first principles, so a wrong `unsat` is impossible.
//!
//! # Budget
//!
//! The [`SearchBudget`](crate::SearchBudget) deadline is honored at entry (the
//! deadline-hole bug class is designed out); the fixpoint is itself hard-bounded
//! ([`MAX_ROUNDS`](crate::infer::MAX_ROUNDS)) and a hit budget is reported as
//! `unknown`, never `unsat`.

use std::collections::BTreeSet;

use axeyum_ir::{TermArena, TermId};

use crate::arrange::SearchBudget;
use crate::check_derivation::{check_conflict, check_equality};
use crate::classes::Classes;
use crate::infer::infer;

/// The verdict of a refutation attempt. There is a `Unsat` variant here (unlike
/// the arrangement search) precisely because every `Unsat` it produces has passed
/// an independent derivation re-check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RefuteOutcome {
    /// The equality/disequality system is unsatisfiable, witnessed by a
    /// re-checked derivation over the cited **original** premise indices.
    Unsat {
        /// A sufficient subset of original equality-premise indices whose
        /// re-checked contradiction establishes `unsat`. (For a disequality-driven
        /// refutation the contradicting disequality is the implicit companion
        /// premise.)
        premises: BTreeSet<usize>,
    },
    /// No re-checked contradiction was found — first-class `unknown`, never a
    /// claim of satisfiability.
    Unknown,
}

/// Attempts to refute `equalities ∧ ¬disequalities` over unbounded `Seq`-sorted
/// terms, returning [`RefuteOutcome::Unsat`] **only** through an independently
/// re-checked derivation (ADR-0053, T-B.7) and [`RefuteOutcome::Unknown`]
/// otherwise. Never claims `sat`. Deterministic for a fixed input.
#[must_use]
pub fn refute_word_equations(
    arena: &mut TermArena,
    equalities: &[(TermId, TermId)],
    disequalities: &[(TermId, TermId)],
    budget: &SearchBudget,
) -> RefuteOutcome {
    // Honor the deadline up front — refutation is cheap and non-recursive, but the
    // discipline (every solve checks the deadline) is uniform.
    if budget.past_deadline() {
        return RefuteOutcome::Unknown;
    }

    // (a) Conflict-driven refutation: run the untrusted fixpoint, then let the
    // independent checker gate any reported conflict.
    let inf = infer(arena, equalities);
    if !inf.hit_budget
        && let Some(conflict) = inf.conflict()
    {
        // Clone the premises before the (immutable) `inf` borrow of `arena` is
        // released for the `&mut` re-check call.
        let premises = conflict.premises.clone();
        let conflict = conflict.clone();
        if check_conflict(arena, equalities, &conflict) {
            return RefuteOutcome::Unsat { premises };
        }
    }

    // (b) Disequality-driven refutation: a disequality `a ≠ b` whose two sides are
    // joined by a *direct* equality chain is unsat. The chain (a sufficient
    // premise set) is proposed by the class substrate and then **re-verified**
    // independently by `check_equality`, so a wrong proposal cannot ship `unsat`.
    // Derived-equality (inference-dependent) diseq contradictions are deliberately
    // out of scope for this slice and stay `unknown`.
    let classes = Classes::new(equalities);
    for &(a, b) in disequalities {
        if let Some(cited) = classes.explain(a, b)
            && check_equality(equalities, &cited, a, b)
        {
            return RefuteOutcome::Unsat { premises: cited };
        }
    }

    RefuteOutcome::Unknown
}
