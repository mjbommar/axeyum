//! Clause vivification — a clause-strengthening inprocessing pass (Track 1, P1.1).
//!
//! Vivification strengthens (or removes) clauses by **asymmetric literal
//! elimination through unit propagation against the rest of the formula**
//! (the "Vivifying propositional clausal formulae" pass of Piette, Hamadi &
//! Saïs, IJCAI 2008; `CaDiCaL` `vivify.cpp`, `Kissat` `vivify.c`). Subsumption
//! and bounded variable elimination collapse *redundant clauses and variables*;
//! vivification is the complementary lever that **shrinks the surviving clauses
//! themselves**, removing literals that are entailed-redundant given the others.
//!
//! # The pass
//!
//! Each clause `C = (l₁ ∨ … ∨ lₖ)` is processed against the rest of the formula
//! `F \ {C}` (every other clause, kept fixed). We assume the literals of `C`
//! **false** one at a time and unit-propagate over `F \ {C}` after each:
//!
//! 1. **Conflict before every literal is assumed.** Suppose assuming
//!    `¬l₁ … ¬lⱼ` (a prefix of `C`) already drives `F \ {C}` to a conflict by
//!    unit propagation. Then `F \ {C} ⊨ (l₁ ∨ … ∨ lⱼ)`, so `C` is entailed by
//!    that strict-prefix clause `C' = (l₁ ∨ … ∨ lⱼ)`. We replace `C` by `C'`
//!    (dropping the untouched suffix). `C'` is **`RUP`** w.r.t. the current
//!    clauses by exactly the propagation that produced the conflict.
//! 2. **A not-yet-assumed literal `lᵢ` is propagated _true_.** While assuming
//!    `¬l₁ … ¬lⱼ` (`j < k`), if unit propagation forces some later literal
//!    `lᵢ` (`i > j`) to **true**, then `F \ {C} ⊨ (l₁ ∨ … ∨ lⱼ ∨ lᵢ)`. That
//!    clause subsumes `C` (its literals are a subset), so `C` may be replaced
//!    by the **strengthened** `C'' = (l₁ ∨ … ∨ lⱼ ∨ lᵢ)`, which is `RUP`. This
//!    is asymmetric literal elimination (ALA): every literal of `C` outside the
//!    assumed prefix except `lᵢ` is dropped.
//!
//! When neither fires for any prefix, `C` is left unchanged. We never apply a
//! step whose result is not `RUP`, so soundness never depends on the (untrusted)
//! propagation order — only the independently re-checkable `DRAT` does.
//!
//! # Model preservation (no reconstruction trail needed)
//!
//! Every strengthening replaces `C` by a clause `C'` with `C' ⊆ C` (as literal
//! sets) **and** `F \ {C} ⊨ C'`. Two consequences:
//!
//! * Because `C' ⊆ C`, every assignment satisfying `C'` satisfies `C` — so
//!   `F' = (F \ {C}) ∪ {C'} ⊨ F`: a model of the vivified formula is a model of
//!   the original *verbatim*, no extension required.
//! * Because `F \ {C} ⊨ C'`, the converse holds too: `F ⊨ F'` (`F` already
//!   entails `C'`). So `F` and `F'` have **exactly the same models** — the pass
//!   is model-preserving, strictly stronger than equisatisfiable. Unlike
//!   [`crate::bve`], **no reconstruction trail is required**, and
//!   [`VivifyOutcome`] carries none. (Clause *removal* is the special case where
//!   the strengthened clause is already present / subsumed; it removes a clause
//!   entailed by the rest, again model-preserving.)
//!
//! # `DRAT` accounting (the trust anchor)
//!
//! [`vivify`] emits a [`Vec<DratStep>`] recording every change in order. A
//! strengthening of `C` to `C'` emits `Add(C')` then `Delete(C)`; the `Add`
//! comes first so the shorter clause is justified while `C` (and the rest) are
//! still present. Each added clause is `RUP` by construction (the conflict *is*
//! the reverse-unit-propagation refutation of its negation), so the whole
//! derivation re-verifies independently:
//! **`check_drat(original, &outcome.proof) == Ok(true)`** for the standalone
//! formula, and the empty clause is derived whenever a strengthening collapses a
//! clause to `()`. If a candidate strengthening cannot be justified as `RUP`
//! against the current clause state, it is **not applied** — soundness over
//! power.
//!
//! # Determinism and bounds
//!
//! Clauses are processed in index order; the per-literal occurrence index is
//! built in sorted order; propagation is a deterministic fixpoint. A
//! per-call propagation budget and a round cap bound the work, and
//! [`vivify_within`] additionally honours a wasm-safe monotonic-clock deadline
//! (ADR-0017). The formula never grows: every applied step removes at least one
//! literal or one clause.

// Monotonic clock for the optional inprocessing deadline: on wasm32 the browser
// has no `std` clock, so use `web-time`'s drop-in `Instant` (ADR-0017).
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use crate::drat::DratStep;
use crate::simplify::NormClause;
use crate::{CnfClause, CnfFormula, CnfLit};

/// Tuning knobs for [`vivify`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VivifyOptions {
    /// Maximum number of fixpoint rounds. Each round sweeps every clause once;
    /// strengthening one clause can expose new strengthenings for others, so the
    /// pass repeats until a round changes nothing or this cap is hit. Stopping
    /// early only leaves fewer strengthenings — the result is always sound.
    pub max_rounds: usize,
    /// Total unit-propagation step budget across the whole call (each literal a
    /// propagation assigns counts once). When exceeded, the current clause
    /// finishes and the pass stops; the partial result is still model-preserving.
    pub propagation_budget: usize,
    /// Clauses longer than this are not used as vivification candidates (their
    /// propagation cost is not worth the strengthening; they are kept verbatim).
    /// Mirrors `CaDiCaL`'s clause-size guard.
    pub clause_size_limit: usize,
}

impl Default for VivifyOptions {
    fn default() -> Self {
        Self {
            max_rounds: 4,
            propagation_budget: 1 << 22,
            clause_size_limit: 100,
        }
    }
}

/// What a [`vivify`] run did, for diagnostics / benchmark accounting.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct VivifyStats {
    /// Clauses that were shrunk (at least one literal removed) but kept.
    pub clauses_strengthened: usize,
    /// Total literals removed across all strengthenings.
    pub literals_removed: usize,
    /// Clauses removed entirely (collapsed to a subsumed/duplicate or to the
    /// empty clause — the latter means the formula is unsat).
    pub clauses_removed: usize,
    /// Number of fixpoint rounds actually executed.
    pub rounds: usize,
    /// Unit-propagation steps consumed (for budget diagnostics).
    pub propagations: usize,
}

impl VivifyStats {
    /// Whether the pass changed anything.
    #[must_use]
    pub fn is_empty(self) -> bool {
        self.clauses_strengthened == 0 && self.clauses_removed == 0
    }
}

/// The result of [`vivify`].
///
/// Unlike [`crate::bve::BveOutcome`] there is **no reconstruction trail**:
/// vivification is model-preserving (see the module docs), so a model of
/// [`Self::formula`] satisfies the original verbatim.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VivifyOutcome {
    /// The strengthened formula (same `variable_count` as the input).
    pub formula: CnfFormula,
    /// What changed.
    pub stats: VivifyStats,
    /// A `DRAT` derivation of every change, in order. Verifiable against the
    /// **original** formula by [`crate::check_drat`]; see the module docs.
    pub proof: Vec<DratStep>,
}

/// Zero-based occurrence-list index for a literal: `2 * variable + sign`.
fn lit_index(lit: CnfLit) -> usize {
    2 * lit.var().index() + usize::from(lit.is_negated())
}

/// Whether `original` and the deduplicated `norm` denote the same literal set
/// with the same multiplicity — i.e. `original` had no repeated literals. When
/// `false`, the `DRAT` checker (which counts repeated literals separately during
/// unit propagation) sees a different clause than our deduped one, so a
/// normalization proof step is required (see [`vivify_within`]).
fn same_literal_multiset(original: &[CnfLit], norm: &[CnfLit]) -> bool {
    original.len() == norm.len()
}

/// Mutable vivification state: the live clause set as normalized literal lists
/// (`None` = removed), per-literal occurrence lists, and a unit-propagation
/// trail scratch reused across clauses.
struct Vivifier {
    /// Live clauses (`None` marks a removed clause). Indices are stable.
    clauses: Vec<Option<Vec<CnfLit>>>,
    /// `occ[lit_index(l)]` = ids of live clauses containing `l`.
    occ: Vec<Vec<usize>>,
    /// Per-variable assignment scratch for unit propagation: `Some(true/false)`
    /// or `None` (unassigned). Reset between candidate clauses.
    value: Vec<Option<bool>>,
    /// Variables touched since the last reset, so propagation state can be
    /// cleared in O(touched) without rescanning every variable.
    touched: Vec<usize>,
    /// Propagation steps consumed so far (against the budget).
    propagations: usize,
}

/// Outcome of vivifying one candidate clause.
enum Vivified {
    /// Replace the clause by this strictly shorter, `RUP` clause.
    Strengthen(Vec<CnfLit>),
    /// Leave the clause unchanged.
    Keep,
}

impl Vivifier {
    /// Reads the truth value of `lit` under the current propagation assignment.
    fn lit_value(&self, lit: CnfLit) -> Option<bool> {
        self.value[lit.var().index()].map(|v| v != lit.is_negated())
    }

    /// Assigns `lit` true, recording the variable for later reset.
    fn assign_true(&mut self, lit: CnfLit) {
        let var = lit.var().index();
        self.value[var] = Some(!lit.is_negated());
        self.touched.push(var);
    }

    /// Clears the propagation assignment touched during one candidate clause.
    fn reset(&mut self) {
        for &var in &self.touched {
            self.value[var] = None;
        }
        self.touched.clear();
    }

    /// Unit-propagates the current assignment over every live clause **except**
    /// `skip` (the candidate clause itself). Returns `true` on a conflict (some
    /// clause has all literals false). New forced literals are assigned true.
    ///
    /// This is a deterministic fixpoint: it repeats full sweeps until no clause
    /// forces a fresh literal. Each literal inspection counts one propagation
    /// step; on exceeding `budget` it returns `false` (no conflict claimed),
    /// which only ever weakens the pass (a strengthening is *missed*, never
    /// wrongly applied).
    fn propagate(&mut self, skip: usize, budget: usize) -> bool {
        loop {
            let mut changed = false;
            for ci in 0..self.clauses.len() {
                if ci == skip {
                    continue;
                }
                let Some(clause) = self.clauses[ci].as_ref() else {
                    continue;
                };
                let mut unassigned: Option<CnfLit> = None;
                let mut unassigned_count = 0usize;
                let mut satisfied = false;
                for &lit in clause {
                    self.propagations += 1;
                    match self.lit_value(lit) {
                        Some(true) => {
                            satisfied = true;
                            break;
                        }
                        Some(false) => {}
                        None => {
                            unassigned_count += 1;
                            unassigned = Some(lit);
                        }
                    }
                }
                if satisfied {
                    continue;
                }
                if unassigned_count == 0 {
                    return true; // every literal false: conflict
                }
                if unassigned_count == 1 {
                    let unit = unassigned.expect("exactly one unassigned literal");
                    self.assign_true(unit);
                    changed = true;
                }
                if self.propagations > budget {
                    return false; // out of budget: claim no conflict (sound)
                }
            }
            if !changed {
                return false;
            }
        }
    }

    /// Vivifies clause `ci` against the rest of the formula.
    ///
    /// Assumes the clause's literals false one at a time (in stored order),
    /// propagating over the other clauses after each assumption:
    ///
    /// * if the assumed prefix already conflicts, the prefix entails the clause
    ///   → strengthen to the prefix (rule 1, prefix-conflict);
    /// * if propagation forces a not-yet-assumed literal of the clause *true*,
    ///   the prefix-plus-that-literal entails the clause → strengthen to that
    ///   subset (rule 2, asymmetric literal elimination).
    ///
    /// Both produce a clause that is a strict subset of the original **and** is
    /// `RUP` (the propagation is the refutation of its negation). Returns
    /// [`Vivified::Keep`] when no prefix triggers either rule.
    fn vivify_clause(&mut self, ci: usize, budget: usize) -> Vivified {
        let clause = self.clauses[ci].as_ref().expect("live candidate").clone();
        self.reset();
        let mut prefix: Vec<CnfLit> = Vec::with_capacity(clause.len());

        for (pos, &lit) in clause.iter().enumerate() {
            // Rule 2: an earlier propagation already forced a clause literal true.
            // The current prefix (literals assumed so far) plus that literal is a
            // RUP subset; drop everything else.
            if self.lit_value(lit) == Some(true) {
                let mut strengthened = prefix.clone();
                strengthened.push(lit);
                if strengthened.len() < clause.len() {
                    return Vivified::Strengthen(strengthened);
                }
                return Vivified::Keep;
            }
            // If `lit` is already forced false, assuming `¬lit` is consistent
            // with what propagation derived; it adds no new information but the
            // literal stays in the prefix so a later conflict maps to a valid
            // sub-clause. (It cannot be dropped on its own without a witness.)
            self.assign_true(lit.negated());
            prefix.push(lit);
            let last = pos + 1 == clause.len();
            if self.propagate(ci, budget) {
                // Rule 1: the assumed prefix conflicts → the prefix entails C.
                if prefix.len() < clause.len() {
                    return Vivified::Strengthen(prefix);
                }
                // A full-clause conflict means C is RUP from the others, i.e.
                // C is redundant. Strengthening to a strict subset is unsound
                // here (we have no shorter witness), so keep C; a separate
                // subsumption pass removes it. Only act on strict prefixes.
                return Vivified::Keep;
            }
            if last {
                break;
            }
        }
        Vivified::Keep
    }

    /// Removes clause `ci` from the live set and its occurrence lists.
    fn remove_clause(&mut self, ci: usize) {
        if let Some(lits) = self.clauses[ci].take() {
            for lit in lits {
                let slot = &mut self.occ[lit_index(lit)];
                if let Some(p) = slot.iter().position(|&c| c == ci) {
                    slot.swap_remove(p);
                }
            }
        }
    }

    /// Installs `lits` as the new content of clause `ci`, updating occ lists.
    fn replace_clause(&mut self, ci: usize, lits: Vec<CnfLit>) {
        self.remove_clause(ci);
        for &lit in &lits {
            self.occ[lit_index(lit)].push(ci);
        }
        self.clauses[ci] = Some(lits);
    }

    /// Independently re-checks that `candidate` is `RUP` against the current live
    /// clauses *except* `ci` (the clause being strengthened, which is about to be
    /// replaced). This is the soundness gate: a strengthening is emitted only if
    /// this returns `true`, so a non-`RUP` clause can never reach the proof, no
    /// matter how the candidate was derived. `RUP` means assuming every literal of
    /// `candidate` false and unit-propagating over the rest yields a conflict.
    fn is_rup_against_live(&mut self, ci: usize, candidate: &[CnfLit]) -> bool {
        self.reset();
        // Falsify the candidate's literals; a literal appearing in both phases
        // makes the negation trivially contradictory (vacuously RUP).
        for &lit in candidate {
            match self.value[lit.var().index()] {
                // `lit` already forced true while we are about to assert it false:
                // the negated candidate is immediately contradictory (vacuously RUP).
                Some(v) if v != lit.is_negated() => return true,
                _ => self.assign_true(lit.negated()),
            }
        }
        let conflict = self.propagate(ci, usize::MAX);
        self.reset();
        conflict
    }
}

/// Strengthens clauses of `formula` by vivification (see module docs).
///
/// The result is **model-preserving**: it has exactly the same satisfying
/// assignments as `formula` (same `variable_count`). The returned
/// [`VivifyOutcome::proof`] is a `DRAT` derivation of every change that
/// re-verifies against the original via [`crate::check_drat`].
#[must_use]
pub fn vivify(formula: &CnfFormula, options: VivifyOptions) -> VivifyOutcome {
    vivify_within(formula, options, None)
}

/// Like [`vivify`], but stops starting new work once `deadline` passes (checked
/// between clauses and between rounds, with a wasm-safe monotonic clock,
/// ADR-0017). The partial result is still model-preserving with a checkable
/// proof; only fewer clauses are strengthened. `None` means no deadline.
#[must_use]
pub fn vivify_within(
    formula: &CnfFormula,
    options: VivifyOptions,
    deadline: Option<Instant>,
) -> VivifyOutcome {
    let nvars = formula.variable_count();
    let mut proof: Vec<DratStep> = Vec::new();
    let mut stats = VivifyStats::default();

    // Normalize clauses (sort + dedup literals, drop input tautologies) and emit
    // the matching DRAT prelude so the checker's active set tracks our live set
    // exactly. This is essential: the checker's RUP propagation treats a clause's
    // literals verbatim, so a clause with a repeated literal (`b ∨ b`) is NOT a
    // unit to it, while our deduped `(b)` is — without the prelude, a later RUP
    // strengthening that relies on `(b)` propagating would verify in our engine
    // but be rejected by the checker. For each input clause we therefore:
    //   * tautology → `Delete(original)` (always sound; deletion is unconditional);
    //   * dedup changed the clause → `Add(deduped)` then `Delete(original)` (the
    //     deduped clause is RUP from the original: its negation falsifies every
    //     copy of each literal, an immediate conflict);
    //   * unchanged → keep verbatim, no step.
    let mut clauses: Vec<Option<Vec<CnfLit>>> = Vec::with_capacity(formula.clauses().len());
    for clause in formula.clauses() {
        let original = clause.lits().to_vec();
        match NormClause::from_clause(clause) {
            Some(nc) => {
                if !same_literal_multiset(&original, &nc.lits) {
                    // Deduped: Add the shorter normalized clause (RUP), Delete the
                    // original. Order matters — Add while the original is present.
                    proof.push(DratStep::Add(nc.lits.clone()));
                    proof.push(DratStep::Delete(original));
                }
                clauses.push(Some(nc.lits));
            }
            None => proof.push(DratStep::Delete(original)), // tautology
        }
    }

    let mut occ: Vec<Vec<usize>> = vec![Vec::new(); 2 * nvars];
    for (ci, slot) in clauses.iter().enumerate() {
        if let Some(lits) = slot {
            for &lit in lits {
                occ[lit_index(lit)].push(ci);
            }
        }
    }

    let mut viv = Vivifier {
        clauses,
        occ,
        value: vec![None; nvars],
        touched: Vec::new(),
        propagations: 0,
    };

    let budget = options.propagation_budget;
    let max_rounds = options.max_rounds.max(1);
    for _ in 0..max_rounds {
        if deadline.is_some_and(|dl| Instant::now() >= dl) || viv.propagations > budget {
            break;
        }
        stats.rounds += 1;
        let changed = vivify_round(&mut viv, &options, deadline, budget, &mut proof, &mut stats);
        if !changed {
            break; // fixpoint: nothing strengthened or removed this round
        }
    }
    stats.propagations = viv.propagations;

    let mut out = CnfFormula::new(nvars);
    for lits in viv.clauses.into_iter().flatten() {
        // Infallible: variables are a subset of the original's, already validated.
        let _ = out.add_clause(CnfClause::new(lits));
    }
    VivifyOutcome {
        formula: out,
        stats,
        proof,
    }
}

/// One vivification round: sweeps every live clause in index order, applying any
/// strengthening (with its `DRAT` `Add`/`Delete` steps). Returns whether the
/// round changed the formula.
fn vivify_round(
    viv: &mut Vivifier,
    options: &VivifyOptions,
    deadline: Option<Instant>,
    budget: usize,
    proof: &mut Vec<DratStep>,
    stats: &mut VivifyStats,
) -> bool {
    let mut changed = false;
    for ci in 0..viv.clauses.len() {
        let Some(clause) = viv.clauses[ci].as_ref() else {
            continue; // removed earlier
        };
        // Skip empty (already unsat-marking) and over-long clauses, and trivial
        // unit clauses (no proper prefix to strengthen).
        let len = clause.len();
        if len <= 1 || len > options.clause_size_limit {
            continue;
        }
        if viv.propagations > budget || deadline.is_some_and(|dl| Instant::now() >= dl) {
            break;
        }
        if let Vivified::Strengthen(new_lits) = viv.vivify_clause(ci, budget)
            && apply_strengthening(viv, ci, new_lits, proof, stats)
        {
            changed = true;
        }
    }
    viv.reset();
    changed
}

/// Applies a vivification strengthening of clause `ci` to `new_lits`, returning
/// whether it was applied. The strengthening is **gated on an independent `RUP`
/// re-check** ([`Vivifier::is_rup_against_live`]): only when `new_lits` is
/// provably `RUP` against the current live clauses does this emit the `DRAT`
/// `Add(new)` then `Delete(old)` steps, update the live clause set, and record
/// the stats. A candidate that fails the check is silently skipped — soundness
/// over power — so the proof can never contain an unjustified clause.
fn apply_strengthening(
    viv: &mut Vivifier,
    ci: usize,
    new_lits: Vec<CnfLit>,
    proof: &mut Vec<DratStep>,
    stats: &mut VivifyStats,
) -> bool {
    if !viv.is_rup_against_live(ci, &new_lits) {
        return false; // not RUP against the live set: do not strengthen
    }
    let old = viv.clauses[ci].as_ref().expect("live candidate").clone();
    // Add the shorter clause first (justified while the old clause and the rest
    // are still present), then delete the longer one.
    proof.push(DratStep::Add(new_lits.clone()));
    proof.push(DratStep::Delete(old.clone()));

    stats.literals_removed += old.len() - new_lits.len();
    stats.clauses_strengthened += 1;
    // An empty `new_lits` is kept live so the rebuilt formula reflects the
    // derived unsatisfiability (the empty clause).
    viv.replace_clause(ci, new_lits);
    true
}

#[cfg(test)]
mod tests {
    use super::{VivifyOptions, vivify};
    use crate::{
        CnfClause, CnfFormula, CnfLit, CnfVar, DratStep, ProofSolveOutcome, check_drat,
        solve_with_drat_proof,
    };

    fn v(i: usize) -> CnfVar {
        CnfVar::new(i).unwrap()
    }
    fn p(i: usize) -> CnfLit {
        CnfLit::positive(v(i))
    }
    fn n(i: usize) -> CnfLit {
        CnfLit::positive(v(i)).negated()
    }
    fn clause(lits: &[CnfLit]) -> CnfClause {
        CnfClause::new(lits.to_vec())
    }
    fn formula(nvars: usize, clauses: &[&[CnfLit]]) -> CnfFormula {
        let mut f = CnfFormula::new(nvars);
        for c in clauses {
            f.add_clause(clause(c)).unwrap();
        }
        f
    }

    /// A literal set, order-independent, for comparing clauses.
    fn lit_set(lits: &[CnfLit]) -> std::collections::BTreeSet<(usize, bool)> {
        lits.iter()
            .map(|l| (l.var().index(), l.is_negated()))
            .collect()
    }

    /// Brute-force: two formulas over `nvars` variables agree on every assignment
    /// (model preservation — the soundness contract).
    fn equivalent(a: &CnfFormula, b: &CnfFormula, nvars: usize) {
        for mask in 0u32..(1u32 << nvars) {
            let asg: Vec<bool> = (0..nvars).map(|i| (mask >> i) & 1 == 1).collect();
            assert_eq!(
                a.evaluate(&asg).unwrap(),
                b.evaluate(&asg).unwrap(),
                "disagree on assignment {asg:?}"
            );
        }
    }

    /// Whether `f` is satisfiable, brute force over `nvars` variables.
    fn sat(f: &CnfFormula, nvars: usize) -> bool {
        (0u32..(1u32 << nvars)).any(|mask| {
            let asg: Vec<bool> = (0..nvars).map(|i| (mask >> i) & 1 == 1).collect();
            f.evaluate(&asg).unwrap()
        })
    }

    #[test]
    fn strengthens_via_prefix_conflict() {
        // Candidate (a∨b∨c) over 4 vars, with helpers (a∨d) and (b∨¬d).
        // Assume ¬a (a=F): (a∨d) forces d=T. Assume ¬b (b=F): (b∨¬d) forces
        // ¬d, i.e. d=F — conflict. The decided prefix (a∨b) therefore entails
        // (a∨b∨c), so the clause is strengthened to (a∨b), dropping c. (a∨b) is
        // RUP (its negation propagates the same conflict). This is rule 1.
        let f = formula(4, &[&[p(0), p(1), p(2)], &[p(0), p(3)], &[p(1), n(3)]]);
        let out = vivify(&f, VivifyOptions::default());
        let has_ab = out
            .formula
            .clauses()
            .iter()
            .any(|c| lit_set(c.lits()) == lit_set(&[p(0), p(1)]));
        assert!(
            has_ab,
            "expected (a∨b) after prefix-conflict vivification, got {:?}",
            out.formula
                .clauses()
                .iter()
                .map(|c| c.lits().to_vec())
                .collect::<Vec<_>>()
        );
        assert!(out.stats.literals_removed >= 1, "c removed");
        equivalent(&f, &out.formula, 4);
        assert!(
            check_drat(&f, &out.proof).is_ok(),
            "every DRAT step verifies"
        );
    }

    #[test]
    fn strengthens_via_implied_literal() {
        // Candidate (a∨b∨c) with helper (a∨b). Assume ¬a (a=F): (a∨b) forces
        // b=T. The next clause literal b is implied true, so the prefix (a) plus
        // b subsumes the candidate → strengthen to (a∨b), dropping c. (a∨b) is
        // RUP. This is rule 2 (asymmetric literal elimination via an implied
        // literal of the clause).
        let f = formula(3, &[&[p(0), p(1), p(2)], &[p(0), p(1)]]);
        let out = vivify(&f, VivifyOptions::default());
        let has_ab = out
            .formula
            .clauses()
            .iter()
            .any(|c| lit_set(c.lits()) == lit_set(&[p(0), p(1)]));
        assert!(
            has_ab,
            "expected (a∨b) via implied-literal strengthening, got {:?}",
            out.formula
                .clauses()
                .iter()
                .map(|c| c.lits().to_vec())
                .collect::<Vec<_>>()
        );
        assert!(out.stats.literals_removed >= 1);
        equivalent(&f, &out.formula, 3);
        assert!(check_drat(&f, &out.proof).is_ok());
    }

    #[test]
    fn no_change_on_already_minimal() {
        let f = formula(3, &[&[p(0), p(1)], &[n(1), p(2)], &[n(0), n(2)]]);
        let out = vivify(&f, VivifyOptions::default());
        assert!(
            out.stats.is_empty(),
            "minimal formula unchanged: {:?}",
            out.stats
        );
        equivalent(&f, &out.formula, 3);
        assert!(check_drat(&f, &out.proof).is_ok());
    }

    #[test]
    fn empty_and_unit_edge_cases_do_not_panic() {
        // Empty formula.
        let empty = CnfFormula::new(0);
        let out = vivify(&empty, VivifyOptions::default());
        assert!(out.stats.is_empty());
        assert!(check_drat(&empty, &out.proof).is_ok());

        // A single unit clause: no proper prefix, nothing to do.
        let unit = formula(1, &[&[p(0)]]);
        let out = vivify(&unit, VivifyOptions::default());
        assert!(out.stats.is_empty());
        equivalent(&unit, &out.formula, 1);
    }

    #[test]
    fn unsat_is_preserved_and_proof_verifies() {
        // (a)(¬a)(a∨b): unsat. Vivifying (a∨b) against (a) makes b implied... but
        // the key contract here is that satisfiability is preserved and every
        // emitted DRAT step verifies against the original.
        let f = formula(2, &[&[p(0)], &[n(0)], &[p(0), p(1)]]);
        let out = vivify(&f, VivifyOptions::default());
        assert!(!sat(&f, 2));
        assert!(!sat(&out.formula, 2));
        assert!(check_drat(&f, &out.proof).is_ok());
    }

    #[test]
    fn idempotent_second_pass_is_a_fixpoint_and_never_grows() {
        let f = formula(
            4,
            &[
                &[p(0), p(1), p(2)],
                &[n(1)],
                &[n(2)],
                &[p(0), p(3)],
                &[n(3), p(0)],
            ],
        );
        let once = vivify(&f, VivifyOptions::default());
        assert!(once.formula.clauses().len() <= f.clauses().len());
        let twice = vivify(&once.formula, VivifyOptions::default());
        assert!(
            twice.stats.is_empty(),
            "second pass should be a fixpoint: {:?}",
            twice.stats
        );
        equivalent(&f, &once.formula, 4);
        assert!(check_drat(&f, &once.proof).is_ok());
    }

    /// Deterministic LCG (no rand/clock; reproducible).
    fn lcg(state: &mut u64) -> u64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        *state
    }
    fn rand_below(state: &mut u64, bound: usize) -> usize {
        usize::try_from(lcg(state) >> 33).unwrap_or(0) % bound
    }

    fn random_formula(state: &mut u64, nvars: usize) -> CnfFormula {
        let nclauses = 1 + rand_below(state, 14);
        let mut f = CnfFormula::new(nvars);
        for _ in 0..nclauses {
            let width = 1 + rand_below(state, 4);
            let mut lits = Vec::new();
            for _ in 0..width {
                let var = rand_below(state, nvars);
                lits.push(if lcg(state) & 1 == 0 { p(var) } else { n(var) });
            }
            f.add_clause(clause(&lits)).unwrap();
        }
        f
    }

    #[test]
    fn drat_self_verifies_on_many_random_cnfs() {
        // Load-bearing: the emitted proof must independently re-check against the
        // ORIGINAL formula for every random instance.
        const NVARS: usize = 5;
        let mut state = 0xC0FF_EE12_3456_789Au64;
        let mut checked = 0usize;
        for _ in 0..600 {
            let f = random_formula(&mut state, NVARS);
            let out = vivify(&f, VivifyOptions::default());
            // Every emitted step must verify (no `StepNotVerified`). `Ok(false)`
            // (all steps verify, no empty clause) is fine for SAT/no-change
            // formulas; `Err` would mean a non-RUP strengthening leaked through.
            assert!(
                check_drat(&f, &out.proof).is_ok(),
                "DRAT must self-verify against the original; formula {:?}",
                f.clauses()
                    .iter()
                    .map(|c| c.lits().to_vec())
                    .collect::<Vec<_>>()
            );
            assert!(out.formula.clauses().len() <= f.clauses().len());
            checked += 1;
        }
        assert_eq!(checked, 600);
    }

    #[test]
    fn equisatisfiability_differential_with_model_replay() {
        // Load-bearing: vivified and original agree on SAT/UNSAT (via the
        // proof-producing core), and every SAT model of the vivified formula
        // satisfies the ORIGINAL verbatim (model preservation). Track coverage.
        const NVARS: usize = 5;
        let mut state = 0x1357_9BDF_2468_ACE0u64;
        let mut sat_count = 0usize;
        let mut unsat_count = 0usize;
        let mut strengthen_count = 0usize;
        let mut disagreements = 0usize;
        for _ in 0..600 {
            let f = random_formula(&mut state, NVARS);
            let out = vivify(&f, VivifyOptions::default());
            if out.stats.literals_removed > 0 || out.stats.clauses_removed > 0 {
                strengthen_count += 1;
            }
            // Independently verify the proof too (defense in depth).
            assert!(check_drat(&f, &out.proof).is_ok());

            let orig = solve_with_drat_proof(&f);
            let viv = solve_with_drat_proof(&out.formula);
            match (&orig, &viv) {
                (ProofSolveOutcome::Sat(_), ProofSolveOutcome::Sat(model)) => {
                    sat_count += 1;
                    // The vivified model must satisfy the ORIGINAL formula.
                    assert!(
                        f.evaluate(model.values()).unwrap(),
                        "vivified model must satisfy the original"
                    );
                }
                (ProofSolveOutcome::Unsat(_), ProofSolveOutcome::Unsat(proof)) => {
                    unsat_count += 1;
                    assert_eq!(check_drat(&out.formula, proof), Ok(true));
                }
                (ProofSolveOutcome::Sat(_), ProofSolveOutcome::Unsat(_))
                | (ProofSolveOutcome::Unsat(_), ProofSolveOutcome::Sat(_)) => {
                    disagreements += 1;
                }
                // ResourceOut/Interrupted: skip (undecided), small instances rarely hit.
                _ => {}
            }
        }
        assert_eq!(disagreements, 0, "vivification changed satisfiability");
        assert!(sat_count > 0, "no SAT coverage");
        assert!(unsat_count > 0, "no UNSAT coverage");
        assert!(strengthen_count > 0, "no strengthening coverage");
    }

    #[test]
    fn brute_force_model_preservation_on_many_random_cnfs() {
        // Strongest soundness check: brute-force equivalence (same models) over
        // every assignment, for many random instances.
        const NVARS: usize = 5;
        let mut state = 0xABCD_EF01_2345_6789u64;
        for _ in 0..600 {
            let f = random_formula(&mut state, NVARS);
            let out = vivify(&f, VivifyOptions::default());
            equivalent(&f, &out.formula, NVARS);
            // A second pass is a fixpoint and never grows.
            let again = vivify(&out.formula, VivifyOptions::default());
            assert!(again.formula.clauses().len() <= out.formula.clauses().len());
        }
    }

    #[test]
    fn proof_steps_are_add_then_delete_in_order() {
        // White-box: a strengthening emits Add(shorter) immediately before
        // Delete(longer), each Add being RUP at that point (checked by check_drat
        // above). Here just assert the structural shape on a known case.
        let f = formula(3, &[&[p(0), p(1), p(2)], &[p(0), p(1)]]);
        let out = vivify(&f, VivifyOptions::default());
        assert!(!out.proof.is_empty());
        // Every Delete must be immediately preceded by an Add (strengthening pair).
        for (i, step) in out.proof.iter().enumerate() {
            if let DratStep::Delete(_) = step {
                assert!(i > 0, "a Delete cannot be the first step");
                assert!(
                    matches!(out.proof[i - 1], DratStep::Add(_)),
                    "each Delete follows its Add"
                );
            }
        }
    }
}
