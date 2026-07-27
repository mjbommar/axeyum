//! The regex-membership sub-solver over the symbolic-derivative engine (T-C.5,
//! ADR-0054).
//!
//! Given a single string variable constrained **only** by regex-membership atoms
//! (positive `x ∈ Rᵢ`, negative `x ∉ Rⱼ`) plus optional length bounds, this
//! module decides the variable's constraint set:
//!
//! * **`sat`** — a concrete witness code-point string is found either by a compact
//!   structural construction (notably for large native loops) or by searching the
//!   transition-regex derivative graph. Structural witnesses carry a separately
//!   checked construction proof; searched witnesses are **replayed** through the
//!   independent reference [`matches()`](super::matches) for every atom (positive
//!   and negative) and checked against the length bounds. A successful check is the
//!   sole gate on `sat`, so no wrong `sat` is possible even if either search has a
//!   bug.
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
use super::derivative::{
    Closure, canon, canon_within, derivative, derivative_closure, derivative_closure_within,
    derivative_within, nullable,
};
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

/// Default cap for a compact structurally checked witness. Unlike derivative
/// search, construction does not clone the growing prefix at every state, so the
/// larger materialization envelope does not widen the generic search budget.
const DEFAULT_MAX_CONSTRUCTED_WITNESS_LEN: usize = 2_000_000;

/// Hard recursion cap for the compact structural witness constructor and its
/// independent checker. Deep or adversarial regex trees simply skip the fast path
/// and fall back to the bounded derivative route.
const CONSTRUCT_MAX_DEPTH: usize = 256;

/// The structural constructor delegates Boolean regex nodes (`inter`/`comp`) to
/// the ordinary derivative witness search. Keep those local witnesses small so
/// their independent reference-matcher replay stays cheap; native outer loops can
/// then repeat the checked local witness compactly.
const CONSTRUCT_REFERENCE_MAX_LEN: usize = 4_096;

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
    /// checked by either the compact structural proof checker or the independent
    /// reference matcher against every represented constraint.
    Sat(Vec<u32>),
    /// The constraint set is unsatisfiable, behind a re-checked emptiness
    /// certificate (a finite nullable-free derivative closure).
    Unsat,
    /// Undecided within the budget / outside the decided fragment. First-class —
    /// never a wrong verdict.
    Unknown,
}

/// Compact proof of how one concrete word was assembled from a regex. The proof
/// is produced with the witness but checked by [`recheck_constructed`] in a
/// separate recursive pass before any `sat` result is returned.
#[derive(Clone, Debug)]
enum ConstructedProof {
    Empty,
    Pred,
    Concat {
        split: usize,
        left: Box<Self>,
        right: Box<Self>,
    },
    UnionLeft(Box<Self>),
    UnionRight(Box<Self>),
    StarZero,
    Loop {
        count: u32,
        unit_len: usize,
        unit: Option<Box<Self>>,
    },
    /// A short Boolean-regex subproblem checked by the independent reference
    /// matcher. This is never used for a large native-loop body as a whole.
    Reference,
}

impl Membership {
    /// Tries a small deterministic set of structurally-derived candidate words and
    /// returns the first one that the independent matcher accepts for the complete
    /// membership problem.
    ///
    /// This is a SAT-only fast path for conjunctions whose combined derivative
    /// product is much larger than their concrete witness. Candidates come from
    /// individual positive regexes and pairwise concatenations of those candidates;
    /// acceptance is always checked against every positive, negative, and length
    /// constraint. Failure therefore means only "no quick witness", never UNSAT.
    #[must_use]
    pub fn quick_witness(&self, budget: &SearchBudget, max_len: usize) -> Option<Vec<u32>> {
        const MAX_BASE_CANDIDATES: usize = 64;

        let mut bases = vec![Vec::new()];
        // A single unconstrained code point is the smallest witness for the very
        // common `w != ""` shape (represented as a negative membership in
        // `{epsilon}`). It also supplies neutral filler when pairwise composition
        // must extend a required prefix/infix. Acceptance still goes through the
        // complete replay below.
        if let Some(word) = simple_structural_witness(&Regex::any_char(), max_len, 0) {
            bases.push(word);
        }
        for regex in &self.positives {
            if budget.past_deadline() {
                return None;
            }
            let Some(word) = simple_structural_witness(regex, max_len, 0) else {
                continue;
            };
            if !bases.contains(&word) {
                bases.push(word);
                if bases.len() == MAX_BASE_CANDIDATES {
                    break;
                }
            }
        }
        // A negative membership in a complemented language is itself a positive
        // requirement: `w ∉ ∁R` iff `w ∈ R`. Generated QF_SLIA formulas
        // commonly encode `contains` this way (negating an `indexof = -1` atom).
        // Seed the same structural candidates from `R`; the full problem replay
        // below remains the sole acceptance gate, so this can only find SAT sooner.
        for regex in &self.negatives {
            if budget.past_deadline() {
                return None;
            }
            let Regex::Comp(inner) = regex else {
                continue;
            };
            let Some(word) = simple_structural_witness(inner, max_len, 0) else {
                continue;
            };
            if !bases.contains(&word) {
                bases.push(word);
                if bases.len() == MAX_BASE_CANDIDATES {
                    break;
                }
            }
        }

        let mut best = Vec::new();
        let mut best_misses = self.miss_count(&best);
        for candidate in &bases {
            if let Some(word) =
                self.consider_quick_candidate(candidate.clone(), &mut best, &mut best_misses)
            {
                return Some(word);
            }
        }

        // Deep generated regexes often have a trivially extensible language but
        // a nullable structural witness: nested `star`/`plus` nodes collapse the
        // seed above to epsilon even when a length lower bound requires a long
        // word. Try constant words made from concrete character predicates in
        // the positive language. This is only candidate generation; complete
        // independent replay remains the SAT gate.
        if let Some(word) = self.quick_length_floor_witness(
            budget,
            max_len,
            MAX_BASE_CANDIDATES,
            &mut best,
            &mut best_misses,
        ) {
            return Some(word);
        }
        if let Some(word) =
            self.quick_pairwise_witness(budget, max_len, &bases, &mut best, &mut best_misses)
        {
            return Some(word);
        }

        // A few PyEx paths need three independent features (for example contains
        // `A`, contains `O`, and ends in carriage return). Greedily extend the best
        // replay-scored candidate instead of enumerating all O(n^3) triples.
        for _ in 0..8 {
            if budget.past_deadline() {
                return None;
            }
            let prior_misses = best_misses;
            let prior = best.clone();
            for base in &bases {
                let Some(len) = prior.len().checked_add(base.len()) else {
                    continue;
                };
                if len > max_len {
                    continue;
                }
                for position in 0..=prior.len() {
                    let mut candidate = Vec::with_capacity(len);
                    candidate.extend_from_slice(&prior[..position]);
                    candidate.extend(base);
                    candidate.extend_from_slice(&prior[position..]);
                    if let Some(word) =
                        self.consider_quick_candidate(candidate, &mut best, &mut best_misses)
                    {
                        return Some(word);
                    }
                }
            }
            if best_misses >= prior_misses {
                break;
            }
        }
        None
    }

    fn quick_pairwise_witness(
        &self,
        budget: &SearchBudget,
        max_len: usize,
        bases: &[Vec<u32>],
        best: &mut Vec<u32>,
        best_misses: &mut usize,
    ) -> Option<Vec<u32>> {
        for left in bases {
            for right in bases {
                if budget.past_deadline() {
                    return None;
                }
                let Some(len) = left.len().checked_add(right.len()) else {
                    continue;
                };
                if len > max_len {
                    continue;
                }
                let mut candidate = Vec::with_capacity(len);
                candidate.extend(left);
                candidate.extend(right);
                if let Some(word) = self.consider_quick_candidate(candidate, best, best_misses) {
                    return Some(word);
                }
            }
        }
        None
    }

    fn quick_length_floor_witness(
        &self,
        budget: &SearchBudget,
        max_len: usize,
        max_candidates: usize,
        best: &mut Vec<u32>,
        best_misses: &mut usize,
    ) -> Option<Vec<u32>> {
        if self.len_lo <= 1 {
            return None;
        }
        let target_len = usize::try_from(self.len_lo).ok()?;
        if target_len > max_len {
            return None;
        }

        let mut chars = Vec::new();
        for regex in &self.positives {
            collect_predicate_witnesses(regex, &mut chars, max_candidates, 0);
        }
        for character in chars {
            if budget.past_deadline() {
                return None;
            }
            if let Some(word) =
                self.consider_quick_candidate(vec![character; target_len], best, best_misses)
            {
                return Some(word);
            }
        }
        None
    }

    fn miss_count(&self, w: &[u32]) -> usize {
        let len = u32::try_from(w.len()).unwrap_or(u32::MAX);
        usize::from(len < self.len_lo || self.len_hi.is_some_and(|hi| len > hi))
            + self.positives.iter().filter(|p| !matches(p, w)).count()
            + self.negatives.iter().filter(|n| matches(n, w)).count()
    }

    fn consider_quick_candidate(
        &self,
        candidate: Vec<u32>,
        best: &mut Vec<u32>,
        best_misses: &mut usize,
    ) -> Option<Vec<u32>> {
        let misses = self.miss_count(&candidate);
        if misses == 0 {
            return Some(candidate);
        }
        if misses < *best_misses
            || (misses == *best_misses
                && (candidate.len(), candidate.as_slice()) < (best.len(), best.as_slice()))
        {
            *best_misses = misses;
            *best = candidate;
        }
        None
    }

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
        self.combined_within(&mut || false)
            .expect("combined_within with a never-tripping budget cannot abort")
    }

    /// [`combined`](Self::combined) with a caller stop poll threaded through the
    /// final similarity canonicalization.
    fn combined_within<F: FnMut() -> bool>(&self, over: &mut F) -> Option<Regex> {
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
        canon_within(&acc.unwrap_or_else(Regex::universal), over)
    }

    /// The combined canonical regex `⋂ positives ∩ ⋂ ∁negatives ∩ Σ{len_lo,len_hi}`
    /// — the single object whose language emptiness *is* this problem's
    /// unsatisfiability.
    ///
    /// Exposed for the Lean-reconstruction of a regex-membership
    /// derivative-emptiness `unsat` (P3.7): the reconstructor re-establishes the
    /// emptiness certificate ([`derivative_closure`] +
    /// [`recheck_empty`]) over this regex before building its kernel-checked
    /// `False`. It is the same object [`refute_empty`](Self::refute_empty) certifies.
    #[must_use]
    pub fn combined_regex(&self) -> Regex {
        self.combined()
    }

    /// Decides this membership problem with the default caps.
    #[must_use]
    pub fn solve(&self, budget: &SearchBudget) -> MembershipOutcome {
        self.solve_with_separate_caps(
            budget,
            DEFAULT_MAX_STATES,
            DEFAULT_MAX_WITNESS_LEN,
            DEFAULT_MAX_CONSTRUCTED_WITNESS_LEN,
        )
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
        self.solve_with_separate_caps(budget, max_states, max_witness_len, max_witness_len)
    }

    fn solve_with_separate_caps(
        &self,
        budget: &SearchBudget,
        max_states: usize,
        max_witness_len: usize,
        max_constructed_witness_len: usize,
    ) -> MembershipOutcome {
        if budget.past_deadline() {
            return MembershipOutcome::Unknown;
        }

        if let Some(word) = self.quick_witness(budget, max_witness_len) {
            return MembershipOutcome::Sat(word);
        }

        // A single positive membership with no other constraint admits a compact
        // structural witness. This avoids walking one derivative state per copy of
        // a large native loop (the ReDoS corpus uses exact counts up to 80,000).
        // The separately checked proof is the SAT gate; no unverified construction
        // escapes this branch.
        if self.positives.len() == 1
            && self.negatives.is_empty()
            && self.len_lo == 0
            && self.len_hi.is_none()
            && let Some((word, proof)) = construct_witness(
                &self.positives[0],
                budget,
                max_states,
                max_constructed_witness_len,
                0,
            )
            && recheck_constructed(&self.positives[0], &word, &proof, 0)
        {
            return MembershipOutcome::Sat(word);
        }

        let mut ticks: u64 = 0;
        let mut poll = || {
            ticks = ticks.wrapping_add(1);
            ticks.is_multiple_of(256) && budget.past_deadline()
        };
        let Some(combined) = self.combined_within(&mut poll) else {
            return MembershipOutcome::Unknown;
        };

        // (2) Emptiness certificate: a complete, nullable-free, re-checked closure
        // proves the language empty ⇒ `unsat`. The closure is bounded by the deadline
        // too (not only `max_states`) so a complex regex is a timely `unknown`, never
        // a grind — an abandoned (`Budget`) closure is not `Complete`, so it declines.
        if let Closure::Complete(states) =
            derivative_closure_within(&combined, max_states, || budget.past_deadline())
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

    /// Searches for a satisfying witness **without** the emptiness-closure pre-pass
    /// [`solve_with_caps`](Self::solve_with_caps) runs first — for callers that only
    /// need a `sat` witness and treat "no witness within budget" as `unknown`, never
    /// `unsat`.
    ///
    /// The emptiness pass ([`derivative_closure`]) materializes the *whole* residual
    /// set and does **not** poll the deadline, so on a regex whose closure is large
    /// (e.g. a `re.comp`/`re.inter` intersected with the `Σ*` runs of a
    /// membership-over-concat shape) it can grind well past the configured timeout.
    /// The witness search alone polls [`SearchBudget::past_deadline`] on every node,
    /// so this is the deadline-bounded path for such shapes: it returns `Some(w)` for
    /// a replay-checked witness, or `None` (⇒ the caller's `unknown`) on an empty
    /// language, an over-budget search, or a witness that fails the mandatory replay.
    #[must_use]
    pub fn witness(
        &self,
        budget: &SearchBudget,
        max_states: usize,
        max_witness_len: usize,
    ) -> Option<Vec<u32>> {
        if budget.past_deadline() {
            return None;
        }
        if let Some(word) = self.quick_witness(budget, max_witness_len) {
            return Some(word);
        }
        let mut ticks: u64 = 0;
        let mut poll = || {
            ticks = ticks.wrapping_add(1);
            ticks.is_multiple_of(256) && budget.past_deadline()
        };
        let combined = self.combined_within(&mut poll)?;
        match witness_search(&combined, budget, max_states, max_witness_len) {
            Some(w) if self.replay(&w) => Some(w),
            _ => None,
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

    /// [`refute_empty`](Self::refute_empty) with a `budget` **deadline**: the
    /// emptiness closure abandons (⇒ `false`, "not proven empty") once the deadline
    /// passes, instead of grinding to `max_states`. Used on the online string route's
    /// hot per-assert consistency check, where a complex regex-intersection must not
    /// stall the CDCL loop past its timeout. Soundness is identical to
    /// [`refute_empty`](Self::refute_empty): `true` only behind a **complete**,
    /// nullable-free, re-checked closure, so an abandoned closure can only *miss* a
    /// conflict (a safe under-approximation), never fabricate one.
    #[must_use]
    pub fn refute_empty_within(&self, max_states: usize, budget: &SearchBudget) -> bool {
        if budget.past_deadline() {
            return false;
        }
        let mut ticks: u64 = 0;
        let mut poll = || {
            ticks = ticks.wrapping_add(1);
            ticks.is_multiple_of(256) && budget.past_deadline()
        };
        let Some(combined) = self.combined_within(&mut poll) else {
            return false;
        };
        matches!(
            derivative_closure_within(&combined, max_states, || budget.past_deadline()),
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

fn collect_predicate_witnesses(regex: &Regex, witnesses: &mut Vec<u32>, cap: usize, depth: usize) {
    if depth > CONSTRUCT_MAX_DEPTH || witnesses.len() == cap {
        return;
    }
    match regex {
        Regex::Pred(pred) => {
            if let Some(character) = pred.witness()
                && !witnesses.contains(&character)
            {
                witnesses.push(character);
            }
        }
        Regex::Concat(left, right) | Regex::Union(left, right) | Regex::Inter(left, right) => {
            collect_predicate_witnesses(left, witnesses, cap, depth + 1);
            collect_predicate_witnesses(right, witnesses, cap, depth + 1);
        }
        Regex::Comp(inner) | Regex::Star(inner) | Regex::Loop { inner, .. } => {
            collect_predicate_witnesses(inner, witnesses, cap, depth + 1);
        }
        Regex::Empty | Regex::None => {}
    }
}

/// Constructs one small word from the non-Boolean structure of `regex`.
/// `Inter`/`Comp` deliberately decline: the caller combines candidates across
/// constraints and independently replays them, so guessing through Boolean regex
/// structure is unnecessary and would duplicate the derivative engine.
fn simple_structural_witness(regex: &Regex, max_len: usize, depth: usize) -> Option<Vec<u32>> {
    if depth > CONSTRUCT_MAX_DEPTH {
        return None;
    }
    match regex {
        Regex::None | Regex::Inter(_, _) | Regex::Comp(_) => None,
        Regex::Pred(pred) => {
            if max_len < 1 {
                return None;
            }
            Some(vec![pred.witness()?])
        }
        Regex::Concat(left, right) => {
            let mut word = simple_structural_witness(left, max_len, depth + 1)?;
            let remaining = max_len.checked_sub(word.len())?;
            word.extend(simple_structural_witness(right, remaining, depth + 1)?);
            Some(word)
        }
        Regex::Union(left, right) => simple_structural_witness(left, max_len, depth + 1)
            .or_else(|| simple_structural_witness(right, max_len, depth + 1)),
        Regex::Empty | Regex::Star(_) => Some(Vec::new()),
        Regex::Loop { inner, lo, hi } => {
            if hi.is_some_and(|upper| *lo > upper) {
                return None;
            }
            let count = usize::try_from(*lo).ok()?;
            if count == 0 {
                return Some(Vec::new());
            }
            let unit = simple_structural_witness(inner, max_len, depth + 1)?;
            let total = unit.len().checked_mul(count)?;
            if total > max_len {
                return None;
            }
            Some(unit.repeat(count))
        }
    }
}

/// Builds one word together with a compact proof. Concatenation and repetition
/// are assembled directly; Boolean regex nodes use the bounded derivative search
/// only for their local (normally short) witness.
fn construct_witness(
    regex: &Regex,
    budget: &SearchBudget,
    max_states: usize,
    max_len: usize,
    depth: usize,
) -> Option<(Vec<u32>, ConstructedProof)> {
    if depth > CONSTRUCT_MAX_DEPTH || budget.past_deadline() {
        return None;
    }
    match regex {
        Regex::Empty => Some((Vec::new(), ConstructedProof::Empty)),
        Regex::None => None,
        Regex::Pred(pred) => {
            let c = pred.witness()?;
            (max_len >= 1).then_some((vec![c], ConstructedProof::Pred))
        }
        Regex::Concat(left, right) => {
            let (mut left_word, left_proof) =
                construct_witness(left, budget, max_states, max_len, depth + 1)?;
            let remaining = max_len.checked_sub(left_word.len())?;
            let (right_word, right_proof) =
                construct_witness(right, budget, max_states, remaining, depth + 1)?;
            let split = left_word.len();
            left_word.extend(right_word);
            Some((
                left_word,
                ConstructedProof::Concat {
                    split,
                    left: Box::new(left_proof),
                    right: Box::new(right_proof),
                },
            ))
        }
        Regex::Union(left, right) => {
            construct_witness(left, budget, max_states, max_len, depth + 1)
                .map(|(word, proof)| (word, ConstructedProof::UnionLeft(Box::new(proof))))
                .or_else(|| {
                    construct_witness(right, budget, max_states, max_len, depth + 1)
                        .map(|(word, proof)| (word, ConstructedProof::UnionRight(Box::new(proof))))
                })
        }
        Regex::Star(_) => Some((Vec::new(), ConstructedProof::StarZero)),
        Regex::Loop { inner, lo, hi } => {
            if hi.is_some_and(|upper| *lo > upper) {
                return None;
            }
            if *lo == 0 {
                return Some((
                    Vec::new(),
                    ConstructedProof::Loop {
                        count: 0,
                        unit_len: 0,
                        unit: None,
                    },
                ));
            }
            let (unit_word, unit_proof) =
                construct_witness(inner, budget, max_states, max_len, depth + 1)?;
            let count = usize::try_from(*lo).ok()?;
            let total_len = unit_word.len().checked_mul(count)?;
            if total_len > max_len {
                return None;
            }
            let mut word = Vec::with_capacity(total_len);
            if !unit_word.is_empty() {
                for i in 0..count {
                    if i.is_multiple_of(1_024) && budget.past_deadline() {
                        return None;
                    }
                    word.extend_from_slice(&unit_word);
                }
            }
            Some((
                word,
                ConstructedProof::Loop {
                    count: *lo,
                    unit_len: unit_word.len(),
                    unit: Some(Box::new(unit_proof)),
                },
            ))
        }
        Regex::Inter(_, _) | Regex::Comp(_) => {
            let local_cap = max_len.min(CONSTRUCT_REFERENCE_MAX_LEN);
            let word = witness_search(regex, budget, max_states, local_cap)?;
            Some((word, ConstructedProof::Reference))
        }
    }
}

/// Independently checks a compact structural witness proof against the regex and
/// the exact materialized word. In particular, a large loop checks one unit proof,
/// the declared count, and that every concrete chunk equals that unit; it never
/// trusts the constructor's repetition arithmetic.
fn recheck_constructed(
    regex: &Regex,
    word: &[u32],
    proof: &ConstructedProof,
    depth: usize,
) -> bool {
    if depth > CONSTRUCT_MAX_DEPTH {
        return false;
    }
    match (regex, proof) {
        (Regex::Empty, ConstructedProof::Empty) | (Regex::Star(_), ConstructedProof::StarZero) => {
            word.is_empty()
        }
        (Regex::Pred(pred), ConstructedProof::Pred) => word.len() == 1 && pred.contains(word[0]),
        (
            Regex::Concat(left, right),
            ConstructedProof::Concat {
                split,
                left: left_proof,
                right: right_proof,
            },
        ) => {
            *split <= word.len()
                && recheck_constructed(left, &word[..*split], left_proof, depth + 1)
                && recheck_constructed(right, &word[*split..], right_proof, depth + 1)
        }
        (Regex::Union(left, _), ConstructedProof::UnionLeft(inner)) => {
            recheck_constructed(left, word, inner, depth + 1)
        }
        (Regex::Union(_, right), ConstructedProof::UnionRight(inner)) => {
            recheck_constructed(right, word, inner, depth + 1)
        }
        (
            Regex::Loop { inner, lo, hi },
            ConstructedProof::Loop {
                count,
                unit_len,
                unit,
            },
        ) => {
            if *count < *lo || hi.is_some_and(|upper| *count > upper) {
                return false;
            }
            if *count == 0 {
                return *lo == 0 && word.is_empty() && unit.is_none();
            }
            let Some(unit_proof) = unit else {
                return false;
            };
            let Ok(count) = usize::try_from(*count) else {
                return false;
            };
            if unit_len.checked_mul(count) != Some(word.len()) {
                return false;
            }
            if *unit_len == 0 {
                return word.is_empty() && recheck_constructed(inner, &[], unit_proof, depth + 1);
            }
            let unit_word = &word[..*unit_len];
            recheck_constructed(inner, unit_word, unit_proof, depth + 1)
                && word
                    .chunks_exact(*unit_len)
                    .all(|candidate| candidate == unit_word)
        }
        (Regex::Inter(_, _) | Regex::Comp(_), ConstructedProof::Reference) => {
            word.len() <= CONSTRUCT_REFERENCE_MAX_LEN && matches(regex, word)
        }
        _ => false,
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
    if budget.past_deadline() {
        return None;
    }
    let mut canon_ticks: u64 = 0;
    let mut canon_poll = || {
        canon_ticks = canon_ticks.wrapping_add(1);
        canon_ticks.is_multiple_of(256) && budget.past_deadline()
    };
    let start = canon_within(combined, &mut canon_poll)?;
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
        // Poll the deadline INSIDE the derivative too (not only per node above):
        // a single `∂state` over a `Σ*`-enlarged intersection can multiply out a
        // huge `product` before the next node-level poll, so abandon mid-derivative
        // once the deadline passes — the tripped poll ⇒ `None` ⇒ the caller's
        // `unknown`, never a wrong verdict.
        let mut ticks: u64 = 0;
        let mut poll = || {
            ticks = ticks.wrapping_add(1);
            ticks.is_multiple_of(256) && budget.past_deadline()
        };
        // A tripped poll ⇒ `None` ⇒ this over-budget witness search declines.
        let tr = derivative_within(&state, &mut poll)?;
        for (guard, residual) in tr.branches() {
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

    fn contains_lit(s: &str) -> Regex {
        Regex::concat(
            Regex::star(Regex::any_char()),
            Regex::concat(lit(s), Regex::star(Regex::any_char())),
        )
    }

    fn starts_with_lit(s: &str) -> Regex {
        Regex::concat(lit(s), Regex::star(Regex::any_char()))
    }

    fn ends_with_lit(s: &str) -> Regex {
        Regex::concat(Regex::star(Regex::any_char()), lit(s))
    }

    #[test]
    fn quick_witness_combines_individual_structural_candidates() {
        // PyEx-style constraints often have an obvious concrete model while the
        // combined derivative product is large: a prefix requirement contributes
        // " ", a contains requirement contributes "Z", and their concatenation
        // satisfies the whole class. Every excluded character is replayed too.
        let mut m = Membership {
            positives: vec![starts_with_lit(" "), contains_lit("Z")],
            negatives: vec![contains_lit(",")],
            ..Membership::default()
        };
        for c in 'A'..='Y' {
            m.negatives.push(contains_lit(&c.to_string()));
        }
        assert_eq!(
            m.quick_witness(&budget(), 256),
            Some(vec![u32::from(b' '), u32::from(b'Z')])
        );
    }

    #[test]
    fn quick_witness_seeds_a_nonempty_neutral_character() {
        // `w != ""` is a negative membership in the singleton epsilon language.
        // The smallest useful filler must also respect the positive `no '='`
        // language and the excluded comma.
        let m = Membership {
            positives: vec![Regex::comp(contains_lit("="))],
            negatives: vec![
                Regex::repeat(Regex::any_char(), 0, Some(0)),
                contains_lit(","),
            ],
            ..Membership::default()
        };
        assert_eq!(m.quick_witness(&budget(), 256), Some(vec![0]));
    }

    #[test]
    fn quick_witness_uses_a_negated_complement_as_a_positive_seed() {
        // `w notin complement(contains("="))` is exactly `contains(w,"=")`.
        // Candidate generation may exploit that equivalence because replay over
        // the complete constraint set remains the acceptance gate.
        let m = Membership {
            positives: vec![Regex::comp(contains_lit(","))],
            negatives: vec![Regex::comp(contains_lit("="))],
            ..Membership::default()
        };
        assert_eq!(m.quick_witness(&budget(), 256), Some(vec![u32::from(b'=')]));
    }

    #[test]
    fn quick_witness_greedily_combines_three_features() {
        let m = Membership {
            positives: vec![starts_with_lit("A"), contains_lit("O"), ends_with_lit("\r")],
            negatives: vec![contains_lit(",")],
            ..Membership::default()
        };
        let witness = m
            .quick_witness(&budget(), 256)
            .expect("three-feature replayed witness");
        assert!(m.accepts(&witness));
    }

    #[test]
    fn quick_witness_fills_a_deep_nullable_language_to_its_length_floor() {
        // StringFuzz regex-deep formulas commonly wrap every concrete token in
        // nullable star/plus structure. Their minimal structural witness is then
        // epsilon even though the formula requires a long word. A concrete leaf
        // character can fill that floor, but only complete membership replay may
        // authorize the candidate as SAT.
        let language = Regex::concat(
            Regex::star(Regex::union(lit("a"), lit("bb"))),
            Regex::star(lit("c")),
        );
        let m = Membership {
            positives: vec![language],
            len_lo: 15,
            ..Membership::default()
        };
        let witness = m
            .quick_witness(&budget(), 256)
            .expect("replayed length-floor witness");
        assert_eq!(witness.len(), 15);
        assert!(m.accepts(&witness));
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
    fn native_loop_large_witness_is_constructed_and_checked_linearly() {
        // The derivative route needs one residual per consumed copy and the old
        // 4,096-character witness cap declined this SMT-COMP ReDoS shape. The
        // compact proof checks one "ab" unit plus the exact 5,000-copy layout.
        let regex = Regex::repeat(lit("ab"), 5_000, Some(5_000));
        let m = Membership {
            positives: vec![regex],
            ..Membership::default()
        };
        assert_eq!(
            m.solve_with_caps(&budget(), DEFAULT_MAX_STATES, 4_096),
            MembershipOutcome::Unknown,
            "an explicit materialization cap remains authoritative"
        );
        match m.solve(&budget()) {
            MembershipOutcome::Sat(w) => {
                assert_eq!(w.len(), 10_000);
                assert!(
                    w.chunks_exact(2)
                        .all(|chunk| chunk == [u32::from(b'a'), u32::from(b'b')])
                );
            }
            other => panic!("expected compact native-loop witness, got {other:?}"),
        }
    }

    #[test]
    fn constructed_loop_checker_rejects_tampered_materialization() {
        let regex = Regex::repeat(lit("ab"), 4, Some(4));
        let (mut word, proof) = construct_witness(
            &regex,
            &budget(),
            DEFAULT_MAX_STATES,
            DEFAULT_MAX_WITNESS_LEN,
            0,
        )
        .expect("construct repeated witness");
        assert!(recheck_constructed(&regex, &word, &proof, 0));
        word[3] = u32::from(b'x');
        assert!(!recheck_constructed(&regex, &word, &proof, 0));
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
    fn tight_whole_with_concat_shape_witnesses_the_whole_string() {
        // The concat-membership route witnesses `whole ∈ "AB" ∩ Σ*"B"Σ*` before
        // asking the word solver to factor `whole = x ++ "B" ++ y`. The pure
        // membership witness must be the tight whole string, not just the shape's
        // middle literal.
        let m = Membership {
            positives: vec![lit("AB"), contains_lit("B")],
            ..Membership::default()
        };
        assert_eq!(
            m.witness(&budget(), DEFAULT_MAX_STATES, DEFAULT_MAX_WITNESS_LEN),
            Some(vec![u32::from(b'A'), u32::from(b'B')])
        );
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
