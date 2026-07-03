//! Word-level **refutation** (slice T-B.7) — the sole route to word-level
//! `unsat`, and only ever behind an independently re-checked derivation.
//!
//! [`refute_word_equations`] is the ADR-0053 `unsat` arm: it runs the T-B.3
//! [`infer`](crate::infer) fixpoint (the untrusted search) over the asserted
//! equalities and ships [`RefuteOutcome::Unsat`] only through an **independent
//! re-check from ORIGINAL premises**. Everything the fixpoint reports — a
//! [`Conflict`](crate::Conflict) record and every derived
//! [`Fact`](crate::Fact) — is a hint, never trusted.
//!
//! # The re-checked arms (slice 2)
//!
//! Slice 1 shipped only the *direct* constant-clash conflict and the
//! *directly-chained* disequality. Slice 2 adds the **inference-dependent**
//! shapes, each behind an independent re-derivation:
//!
//! - **direct conflict** — a T-B.3 constant clash [`check_conflict`] re-derives
//!   from a direct equality chain (slice 1);
//! - **chained conflict** — a clash that only closes *through* a derived equality:
//!   every derived [`Fact`](crate::Fact) is first re-verified by
//!   [`check_fact`] from the ORIGINAL premises, then those certified facts join
//!   the premise union-find and [`check_conflict`] re-verifies the clash;
//! - **self-loop constant contradiction** — `x ≈ "a" ++ x` and friends: a cycle
//!   forcing a nonempty constant to ε, re-derived by
//!   [`check_cycle_constant_conflict`];
//! - **augmented constant clash** — `x ≈ y ++ x ∧ y ≈ "a"`: the cycle forces the
//!   variable `y ≈ ε` (a certified [`check_fact`]), which then clashes with
//!   `y ≈ "a"` — two distinct constants in one augmented class;
//! - **direct / augmented disequality** — a disequality contradicted by a direct
//!   equality chain ([`check_equality`]) or one that closes only through certified
//!   facts.
//!
//! # No search-based `unsat`
//!
//! This is **not** a search. An exhausted or over-budget arrangement search is
//! never `unsat` — that is [`solve_word_equations`](crate::solve_word_equations)'s
//! job and it has no `unsat` variant by construction (ADR-0053). Every appended
//! fact is a theory consequence re-checked by [`check_fact`], so a contradiction it
//! exposes is a contradiction of the originals alone. Multi-node containment
//! cycles, parity/length arguments, and any conflict whose derived facts
//! [`check_fact`] cannot re-derive are conservatively left `unknown` — a wrong
//! `unsat` is impossible.
//!
//! # Budget
//!
//! The [`SearchBudget`](crate::SearchBudget) deadline is honored at entry (the
//! deadline-hole bug class is designed out); the fixpoint is itself hard-bounded
//! ([`MAX_ROUNDS`](crate::infer::MAX_ROUNDS)) and a hit budget is reported as
//! `unknown`, never `unsat`.

use std::collections::BTreeSet;

use axeyum_ir::{Assignment, TermArena, TermId, Value, eval};

use crate::arrange::SearchBudget;
use crate::check_derivation::{
    check_conflict, check_cycle_constant_conflict, check_equality, check_fact,
};
use crate::classes::Classes;
use crate::infer::{Conflict, Fact, Rule, infer};

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

    // Run the untrusted T-B.3 fixpoint once; every arm below re-checks its output
    // from ORIGINAL premises before shipping `unsat` (a conflict record and a
    // derived fact are both hints, never trusted).
    let inf = infer(arena, equalities);

    if !inf.hit_budget {
        // Independently re-verify each derived fact from its cited ORIGINAL
        // premises. Only certified facts are ever added to a premise set below, so
        // the chained / augmented arms inherit `check_fact`'s soundness.
        let certified: Vec<Fact> = inf
            .facts()
            .filter(|f| check_fact(arena, equalities, f))
            .cloned()
            .collect();

        // (a) Conflict-driven refutation. First the DIRECT re-check (slice 1);
        // then the CHAINED re-check, which lets the certified derived facts join
        // the premise union-find so a conflict that only closes THROUGH a derived
        // equality re-verifies.
        if let Some(conflict) = inf.conflict() {
            let conflict = conflict.clone();
            if check_conflict(arena, equalities, &conflict) {
                return RefuteOutcome::Unsat {
                    premises: conflict.premises,
                };
            }
            if let Some(premises) = chained_conflict(arena, equalities, &certified, &conflict) {
                return RefuteOutcome::Unsat { premises };
            }
        }

        // (b) Self-loop constant contradiction (`x ≈ "a" ++ x` family): a cycle
        // that forces a nonempty constant to ε is unsat, re-derived independently
        // from the cycle premises.
        for f in inf.facts() {
            if f.rule == Rule::CycleEpsilon && check_cycle_constant_conflict(arena, equalities, f) {
                return RefuteOutcome::Unsat {
                    premises: f.premises.clone(),
                };
            }
        }

        // (c) A whole-term constant clash exposed only after certified ε / equality
        // facts (`x ≈ y ++ x ∧ y ≈ "a"` forces `y ≈ ε` then `"a" ≈ ε`).
        if let Some(premises) = augmented_constant_clash(arena, equalities, &certified) {
            return RefuteOutcome::Unsat { premises };
        }

        // (d) A disequality contradicted only through certified derived facts.
        if let Some(premises) = augmented_disequality(equalities, &certified, disequalities) {
            return RefuteOutcome::Unsat { premises };
        }
    }

    // (e) Disequality-driven refutation over a *direct* equality chain (works even
    // when the fixpoint hit its budget). The chain is proposed by the class
    // substrate and re-verified independently by `check_equality`.
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

/// The augmented equality list `equalities ++ [certified fact equalities]`. The
/// appended facts are theory consequences of the originals (each re-checked by
/// [`check_fact`]), so any contradiction they expose is a contradiction of the
/// originals alone.
fn augment(equalities: &[(TermId, TermId)], certified: &[Fact]) -> Vec<(TermId, TermId)> {
    let mut aug = equalities.to_vec();
    aug.extend(certified.iter().map(|f| f.equality));
    aug
}

/// Rewrites a premise set over the augmented indexing back to **original**
/// premise indices: an index `< orig_len` is an original premise; an appended
/// certified fact contributes its own original-premise closure.
fn to_original_premises(
    cited: &BTreeSet<usize>,
    orig_len: usize,
    certified: &[Fact],
) -> BTreeSet<usize> {
    let mut out = BTreeSet::new();
    for &idx in cited {
        if idx < orig_len {
            out.insert(idx);
        } else if let Some(f) = certified.get(idx - orig_len) {
            out.extend(f.premises.iter().copied());
        }
    }
    out
}

/// Re-checks a conflict that closes only THROUGH certified derived facts: the
/// certified facts join the premise union-find (as extra premise equalities) and
/// [`check_conflict`] re-verifies the same clash. Returns the ORIGINAL premise set
/// on success. Independent, because every appended equality is itself
/// [`check_fact`]-certified.
fn chained_conflict(
    arena: &mut TermArena,
    equalities: &[(TermId, TermId)],
    certified: &[Fact],
    conflict: &Conflict,
) -> Option<BTreeSet<usize>> {
    if certified.is_empty() {
        return None;
    }
    let orig_len = equalities.len();
    let aug = augment(equalities, certified);
    let mut aug_conflict = conflict.clone();
    for i in orig_len..aug.len() {
        aug_conflict.premises.insert(i);
    }
    if !check_conflict(arena, &aug, &aug_conflict) {
        return None;
    }
    // Original premises: the conflict's own (already original) plus every appended
    // fact's original closure. A superset of a genuine unsat core, hence sound.
    let mut premises = conflict.premises.clone();
    for f in certified {
        premises.extend(f.premises.iter().copied());
    }
    Some(premises)
}

/// A whole-sequence constant clash exposed by the certified facts: two constant
/// terms placed in one class by `equalities ++ certified` that denote **different**
/// sequences. Because the appended facts are consequences of the originals, the
/// originals alone entail `c₁ ≈ c₂`, so their differing values are a contradiction.
fn augmented_constant_clash(
    arena: &mut TermArena,
    equalities: &[(TermId, TermId)],
    certified: &[Fact],
) -> Option<BTreeSet<usize>> {
    if certified.is_empty() {
        return None;
    }
    let orig_len = equalities.len();
    let aug = augment(equalities, certified);
    let classes = Classes::new(&aug);

    // Every constant endpoint of the augmented system, with its closed value.
    let mut endpoints: BTreeSet<TermId> = BTreeSet::new();
    for &(a, b) in &aug {
        endpoints.insert(a);
        endpoints.insert(b);
    }
    let consts: Vec<(TermId, Vec<Value>)> = endpoints
        .iter()
        .filter_map(|&t| seq_value(arena, t).map(|v| (t, v)))
        .collect();

    for i in 0..consts.len() {
        for j in (i + 1)..consts.len() {
            let (t1, v1) = &consts[i];
            let (t2, v2) = &consts[j];
            if v1 == v2 || classes.representative(*t1) != classes.representative(*t2) {
                continue;
            }
            // Two distinct constants forced into one class — a contradiction.
            if let Some(path) = classes.explain(*t1, *t2) {
                return Some(to_original_premises(&path, orig_len, certified));
            }
        }
    }
    None
}

/// A disequality `a ≠ b` contradicted only through certified derived facts: the
/// two sides land in one class of `equalities ++ certified`. The connecting path
/// (re-verified as a sequence of original premises and check_fact-certified facts)
/// is mapped back to original premise indices.
fn augmented_disequality(
    equalities: &[(TermId, TermId)],
    certified: &[Fact],
    disequalities: &[(TermId, TermId)],
) -> Option<BTreeSet<usize>> {
    if certified.is_empty() || disequalities.is_empty() {
        return None;
    }
    let orig_len = equalities.len();
    let aug = augment(equalities, certified);
    let classes = Classes::new(&aug);
    for &(a, b) in disequalities {
        if classes.representative(a) == classes.representative(b)
            && let Some(path) = classes.explain(a, b)
        {
            return Some(to_original_premises(&path, orig_len, certified));
        }
    }
    None
}

/// The closed sequence value of `t`, or `None` if it does not evaluate closed.
/// (A small local mirror — refutation shares no reasoning code with the checker.)
fn seq_value(arena: &TermArena, t: TermId) -> Option<Vec<Value>> {
    match eval(arena, t, &Assignment::new()) {
        Ok(Value::Seq(v)) => Some(v),
        _ => None,
    }
}
