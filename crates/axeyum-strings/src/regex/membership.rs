//! The regex-membership sub-solver over the symbolic-derivative engine (T-C.5,
//! ADR-0054).
//!
//! Given a single string variable constrained **only** by regex-membership atoms
//! (positive `x ∈ Rᵢ`, negative `x ∉ Rⱼ`) plus optional length bounds, this
//! module decides the variable's constraint set:
//!
//! * **`sat`** — a concrete witness code-point string is found by searching the
//!   transition-regex derivative graph for an accepting (nullable) residual, then
//!   **replayed** through the independent reference [`matches()`](super::matches)
//!   for every atom (positive *and* negative) and checked against the length
//!   bounds. The replay is mandatory and is the sole gate on `sat` — it mirrors
//!   the word-equation core's ground-evaluator replay, so no wrong `sat` is
//!   possible even if the derivative search had a bug.
//! * **`unsat`** — only behind a **re-checkable emptiness certificate**: the
//!   derivative closure of the combined regex is finite and contains **no**
//!   nullable residual, and an independent pass ([`recheck_empty`]) confirms the
//!   claimed closure set is closed under derivative and nullable-free. The
//!   certificate is the closure set itself; the checker verifies the closure
//!   invariant regardless of how the set was produced, so soundness rests only on
//!   `derivative`/`nullable`/`canon` — the substrate anchored by the
//!   fundamental-derivative-theorem property test. Anything short of a complete,
//!   re-checked closure declines to `unknown` (ADR-0054's decline-by-default unsat
//!   rule).
//!
//! Every search path is bounded by a [`SearchBudget`] (state cap + native
//! deadline) and a witness-length cap, so an intractable instance is a first-class
//! `unknown`, never a hang (the deadline-hole class is designed out).

use std::collections::BTreeSet;

use super::ast::Regex;
use super::derivative::{Closure, canon, derivative, derivative_closure, nullable};
use super::matcher::matches;
use crate::arrange::SearchBudget;

/// The default hard cap on the number of distinct canonical derivative residuals
/// the membership search will materialize (for both the emptiness closure and the
/// witness BFS) before declining to `unknown`.
pub const DEFAULT_MAX_STATES: usize = 20_000;

/// The default hard cap on a materialized witness's length (code points). A
/// witness longer than this — e.g. forced by a very large length lower bound —
/// declines to `unknown` rather than allocate unboundedly.
pub const DEFAULT_MAX_WITNESS_LEN: usize = 4_096;

/// A single-variable regex-membership problem: the variable must match every
/// [`positives`](Self::positives) regex, no [`negatives`](Self::negatives) regex,
/// and have length within `[len_lo, len_hi]`.
#[derive(Clone, Debug, Default)]
pub struct Membership {
    /// Positive membership constraints `x ∈ Rᵢ` (all must hold).
    pub positives: Vec<Regex>,
    /// Negative membership constraints `x ∉ Rⱼ` (none may hold).
    pub negatives: Vec<Regex>,
    /// Inclusive length lower bound (`0` when unconstrained).
    pub len_lo: u32,
    /// Inclusive length upper bound, or `None` when unconstrained.
    pub len_hi: Option<u32>,
}

/// The verdict of the membership sub-solver.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MembershipOutcome {
    /// A concrete satisfying witness (the variable's code points), already
    /// replayed through the reference matcher against every atom and the length
    /// bounds.
    Sat(Vec<u32>),
    /// The constraint set is unsatisfiable, behind a re-checked emptiness
    /// certificate (a finite nullable-free derivative closure).
    Unsat,
    /// Undecided within the budget / outside the decided fragment. First-class —
    /// never a wrong verdict.
    Unknown,
}

impl Membership {
    /// The `Σ{len_lo, len_hi}` length-shape regex, or [`Regex::None`] when the
    /// bound range is empty (`len_lo > len_hi`). `Σ` is [`Regex::any_char`].
    #[must_use]
    fn length_shape(&self) -> Option<Regex> {
        match self.len_hi {
            Some(hi) if self.len_lo > hi => Some(Regex::none()),
            // Only build a shape when a bound is actually present; an all-`Σ*`
            // shape (`{0,}`) is the identity of intersection and needlessly grows
            // the state space, so skip it.
            Some(hi) => Some(Regex::repeat(Regex::any_char(), self.len_lo, Some(hi))),
            None if self.len_lo > 0 => Some(Regex::repeat(Regex::any_char(), self.len_lo, None)),
            None => None,
        }
    }

    /// The combined regex `⋂ positives ∩ ⋂ ∁negatives ∩ Σ{len_lo,len_hi}`,
    /// canonicalized. An empty problem (no atoms, no bounds) is `Σ*`.
    #[must_use]
    fn combined(&self) -> Regex {
        let mut acc: Option<Regex> = None;
        let mut push = |r: Regex| {
            acc = Some(match acc.take() {
                None => r,
                Some(prev) => Regex::inter(prev, r),
            });
        };
        for p in &self.positives {
            push(p.clone());
        }
        for n in &self.negatives {
            push(Regex::comp(n.clone()));
        }
        if let Some(shape) = self.length_shape() {
            push(shape);
        }
        canon(&acc.unwrap_or_else(Regex::universal))
    }

    /// Decides this membership problem with the default caps.
    #[must_use]
    pub fn solve(&self, budget: &SearchBudget) -> MembershipOutcome {
        self.solve_with_caps(budget, DEFAULT_MAX_STATES, DEFAULT_MAX_WITNESS_LEN)
    }

    /// Decides this membership problem with explicit state / witness-length caps.
    ///
    /// The pipeline is: (1) build the combined regex; (2) try the re-checked
    /// emptiness certificate → `unsat`; (3) otherwise search the derivative graph
    /// for a witness, replay it → `sat`; (4) otherwise `unknown`.
    #[must_use]
    pub fn solve_with_caps(
        &self,
        budget: &SearchBudget,
        max_states: usize,
        max_witness_len: usize,
    ) -> MembershipOutcome {
        let combined = self.combined();

        // (2) Emptiness certificate: a complete, nullable-free, re-checked closure
        // proves the language empty ⇒ `unsat`.
        if let Closure::Complete(states) = derivative_closure(&combined, max_states)
            && states.iter().all(|s| !nullable(s))
            && recheck_empty(&combined, &states)
        {
            return MembershipOutcome::Unsat;
        }
        if budget.past_deadline() {
            return MembershipOutcome::Unknown;
        }

        // (3) Witness search over the derivative graph, then mandatory replay.
        match witness_search(&combined, budget, max_states, max_witness_len) {
            Some(w) if self.replay(&w) => MembershipOutcome::Sat(w),
            // A witness that fails replay must never be returned `sat`; the engine
            // and matcher disagreeing is a bug, and the honest response is
            // `unknown` (the property fuzz drives replay to never fail).
            _ => MembershipOutcome::Unknown,
        }
    }

    /// Whether this membership problem is provably **unsatisfiable** behind the
    /// re-checked emptiness certificate — the `unsat`-only half of
    /// [`solve_with_caps`](Self::solve_with_caps) *without* the witness search.
    ///
    /// Returns `true` iff the combined regex `⋂ positives ∩ ⋂ ∁negatives ∩
    /// Σ{len_lo,len_hi}` has a complete, nullable-free, independently
    /// [`recheck_empty`]-verified derivative closure (⇒ its language is empty).
    /// A `false` means "not proven empty within `max_states`" — it is **not** a
    /// claim of satisfiability. Soundness rests only on the
    /// `derivative`/`nullable`/`canon` substrate, exactly as `solve`'s `unsat`
    /// arm does.
    ///
    /// This is the cheap consistency check the online CDCL(T) string route runs
    /// per-assert on a per-variable membership intersection: it never allocates a
    /// witness, so an intractable-but-satisfiable class is a fast `false`, never a
    /// witness-search hang.
    #[must_use]
    pub fn refute_empty(&self, max_states: usize) -> bool {
        let combined = self.combined();
        matches!(
            derivative_closure(&combined, max_states),
            Closure::Complete(states)
                if states.iter().all(|s| !nullable(s)) && recheck_empty(&combined, &states)
        )
    }

    /// Whether the concrete code-point string `w` satisfies this membership
    /// problem — it matches every positive regex, no negative regex, and the
    /// length bounds. Each check goes through the **independent** reference
    /// [`matches()`](super::matches), so this is the trust anchor a caller uses to validate a
    /// pinned/fixed witness (e.g. a variable forced equal to a string literal).
    #[must_use]
    pub fn accepts(&self, w: &[u32]) -> bool {
        self.replay(w)
    }

    /// The mandatory replay gate: a candidate witness `w` is accepted only if it
    /// matches every positive regex, no negative regex, and the length bounds —
    /// each checked by the **independent** reference [`matches()`](super::matches), sharing no code
    /// with the derivative search that produced `w`.
    #[must_use]
    fn replay(&self, w: &[u32]) -> bool {
        let len = u32::try_from(w.len()).unwrap_or(u32::MAX);
        if len < self.len_lo || self.len_hi.is_some_and(|hi| len > hi) {
            return false;
        }
        self.positives.iter().all(|p| matches(p, w))
            && self.negatives.iter().all(|n| !matches(n, w))
    }
}

/// Searches the transition-regex derivative graph of `combined` for an accepting
/// (nullable) residual reachable within the state and witness-length caps,
/// returning the code-point witness on the path that reaches it.
///
/// **Depth-first** from `canon(combined)`: each state contributes one witness code
/// point (the [`witness`](super::CharPred::witness) of a covering guard) per
/// outgoing branch. Whether a state can reach a nullable residual is a property of
/// the *state* (Brzozowski: the residual determines the rest of the string), not of
/// the path that reached it, so a global visited set never blocks an accepting
/// path — yet it bounds the search to the number of distinct canonical residuals.
/// DFS is essential when a length lower bound forces the shortest accepting string
/// deep: a breadth-first sweep would enumerate every shallower state first (an
/// exponential frontier), whereas DFS dives straight to an accepting leaf. The
/// state cap / deadline / length cap bound the search — an over-budget search
/// returns `None` (⇒ the caller's `unknown`).
fn witness_search(
    combined: &Regex,
    budget: &SearchBudget,
    max_states: usize,
    max_witness_len: usize,
) -> Option<Vec<u32>> {
    let start = canon(combined);
    if nullable(&start) {
        return Some(Vec::new());
    }
    // DFS stack: each entry is a state plus the witness path that reaches it.
    let mut seen: BTreeSet<Regex> = BTreeSet::new();
    seen.insert(start.clone());
    let mut stack: Vec<(Regex, Vec<u32>)> = vec![(start, Vec::new())];

    let mut nodes: u64 = 0;
    while let Some((state, path)) = stack.pop() {
        nodes += 1;
        if nodes > budget.max_nodes || budget.past_deadline() {
            return None;
        }
        if path.len() >= max_witness_len {
            continue;
        }
        for (guard, residual) in derivative(&state).branches() {
            // A witness character for this branch (the guard is non-empty, since
            // `coalesce` drops empty guards).
            let Some(c) = guard.witness() else { continue };
            if seen.contains(residual) {
                continue;
            }
            let mut next_path = path.clone();
            next_path.push(c);
            if nullable(residual) {
                return Some(next_path);
            }
            if seen.len() >= max_states {
                return None;
            }
            seen.insert(residual.clone());
            stack.push((residual.clone(), next_path));
        }
    }
    None
}

/// Independently re-checks that `states` is a valid **emptiness certificate** for
/// `combined`: it contains `canon(combined)`, is closed under the transition-regex
/// derivative (every residual of every member is a member), and contains no
/// nullable member. When all three hold, `L(combined) = ∅` — the certificate is a
/// self-contained finite proof that no string is accepted.
///
/// This shares only the derivative/nullable/canon substrate with the search that
/// produced the set (there is no other transition relation to check against); it
/// verifies the closure invariant on the claimed set from first principles, so a
/// wrong `unsat` is impossible unless the substrate itself (guarded by the
/// fundamental-derivative-theorem property test) is wrong.
#[must_use]
pub fn recheck_empty(combined: &Regex, states: &[Regex]) -> bool {
    let set: BTreeSet<&Regex> = states.iter().collect();
    let start = canon(combined);
    if !set.contains(&start) {
        return false;
    }
    for s in states {
        if nullable(s) {
            return false;
        }
        for (_, residual) in derivative(s).branches() {
            if !set.contains(residual) {
                return false;
            }
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    fn budget() -> SearchBudget {
        SearchBudget::new(1_000_000)
    }

    fn lit(s: &str) -> Regex {
        let mut acc: Option<Regex> = None;
        for c in s.chars() {
            let ch = Regex::character(c as u32);
            acc = Some(match acc {
                None => ch,
                Some(prev) => Regex::concat(prev, ch),
            });
        }
        acc.unwrap_or(Regex::Empty)
    }

    #[test]
    fn single_membership_sat_replays() {
        // x ∈ (ab)*  with len ≥ 2  ⇒ witness "ab".
        let m = Membership {
            positives: vec![Regex::star(lit("ab"))],
            len_lo: 2,
            ..Membership::default()
        };
        match m.solve(&budget()) {
            MembershipOutcome::Sat(w) => {
                assert!(matches(&Regex::star(lit("ab")), &w));
                assert!(w.len() >= 2);
            }
            other => panic!("expected sat, got {other:?}"),
        }
    }

    #[test]
    fn intersection_empty_is_unsat() {
        // (ab)* ∩ (ababac)* ∩ len>1 is empty (only common string is ε).
        let m = Membership {
            positives: vec![Regex::star(lit("ab")), Regex::star(lit("ababac"))],
            len_lo: 2,
            ..Membership::default()
        };
        assert_eq!(m.solve(&budget()), MembershipOutcome::Unsat);
    }

    #[test]
    fn inclusion_unsat() {
        // s ∈ A*  ∧  s ∉ (A|B)*  is unsat (A* ⊆ (A|B)*).
        let only_a = Regex::star(lit("A"));
        let a_or_b = Regex::star(Regex::union(lit("A"), lit("B")));
        let m = Membership {
            positives: vec![only_a],
            negatives: vec![a_or_b],
            ..Membership::default()
        };
        assert_eq!(m.solve(&budget()), MembershipOutcome::Unsat);
    }

    #[test]
    fn complement_singleton_sat() {
        // x ∈ ∁("a") with len 1 ⇒ some single char ≠ "a".
        let m = Membership {
            negatives: vec![lit("a")],
            len_lo: 1,
            len_hi: Some(1),
            ..Membership::default()
        };
        match m.solve(&budget()) {
            MembershipOutcome::Sat(w) => {
                assert_eq!(w.len(), 1);
                assert_ne!(w, vec![u32::from(b'a')]);
            }
            other => panic!("expected sat, got {other:?}"),
        }
    }

    #[test]
    fn refute_empty_matches_solve_unsat() {
        // The same empty intersection `solve` reports `unsat`, `refute_empty`
        // certifies directly; a satisfiable set is `false` (not proven empty).
        let empty = Membership {
            positives: vec![Regex::star(lit("ab")), Regex::star(lit("ababac"))],
            len_lo: 2,
            ..Membership::default()
        };
        assert!(empty.refute_empty(DEFAULT_MAX_STATES));
        assert_eq!(empty.solve(&budget()), MembershipOutcome::Unsat);

        let sat = Membership {
            positives: vec![Regex::star(lit("ab"))],
            len_lo: 2,
            ..Membership::default()
        };
        assert!(!sat.refute_empty(DEFAULT_MAX_STATES));

        // Inclusion emptiness (A* ∩ ∁(A|B)*) is likewise certified.
        let incl = Membership {
            positives: vec![Regex::star(lit("A"))],
            negatives: vec![Regex::star(Regex::union(lit("A"), lit("B")))],
            ..Membership::default()
        };
        assert!(incl.refute_empty(DEFAULT_MAX_STATES));
    }

    #[test]
    fn recheck_rejects_non_closed_set() {
        // A bogus "certificate" missing residuals must fail the re-check.
        let combined = Regex::star(lit("a"));
        // a* is nullable, so any real closure has a nullable member; an empty or
        // partial set is not a valid emptiness certificate.
        assert!(!recheck_empty(&combined, std::slice::from_ref(&combined)));
    }
}
