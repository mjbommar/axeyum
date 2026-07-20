//! Bounded variable elimination (Track 1, P1.1 / tasks T1.1.2, T1.1.4).
//!
//! BVE eliminates a variable `x` by **clause distribution** (Davis–Putnam
//! resolution): every clause with `+x` is resolved against every clause with `¬x`
//! on `x`, the non-tautological resolvents replace both occurrence sets, and `x`
//! disappears. On bit-blasted CNF — which is dense with Tseitin intermediate
//! variables — this is the single highest-leverage simplification, collapsing the
//! gate variables that subsumption alone cannot remove.
//!
//! **Soundness: the result is _equisatisfiable_, not model-preserving** (unlike
//! [`crate::simplify`]). `∃x. F ≡ other ∪ {resolvents}`: any model of the reduced
//! formula extends to a model of the original by choosing a value for each
//! eliminated `x`. That extension is what [`Reconstruction::extend`] does, replaying
//! the eliminated clauses in reverse order (the `CaDiCaL` extension-stack rule:
//! tentatively set `x` true, and flip it false if a clause that needed `¬x` is left
//! unsatisfied). `F` is SAT iff the reduced formula is SAT.
//!
//! A variable is eliminated only when it does not blow up the formula: the number
//! of non-tautological resolvents must not exceed `|pos| + |neg| + growth`, no
//! resolvent may exceed [`BveOptions::clause_size_limit`], and hub variables past
//! [`BveOptions::occurrence_limit`] are skipped (`CaDiCaL` `elimclslim`/`elimocclim`
//! defaults of 100, the non-increasing-resolvent bound).
//!
//! **Implementation (T1.1.4): full literal occurrence lists + a touched queue**
//! (`CaDiCaL` `elim.cpp`, `Kissat` `eliminate.c`). `occ[lit]` gives a candidate's
//! positive/negative clause sets directly in `O(occ)` rather than by rescanning
//! every clause, and after eliminating `x` only the variables whose neighbourhood
//! changed are re-queued — so the pass is near-linear instead of the earlier
//! `O(variables · clauses)` per round. Clause removal is lazy (a removed clause's
//! id is left in its occurrence lists and skipped on scan); resolvents are appended
//! and their variables re-queued. A size-scaled resolution budget bounds the worst
//! case. Occurrence lists are transient and rebuilt per call (correctness-first);
//! per-literal incremental count maintenance is a later refinement.

use std::collections::VecDeque;

// Monotonic clock for the optional inprocessing deadline: on wasm32 the browser
// has no `std` clock, so use `web-time`'s drop-in `Instant` (ADR-0017).
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use crate::simplify::NormClause;
use crate::{CnfClause, CnfFormula, CnfLit, CnfVar};

/// Tuning knobs for bounded variable elimination.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BveOptions {
    /// Max literals in any resolvent; `x` is not eliminated if a resolvent
    /// exceeds this. `CaDiCaL` `elimclslim` default 100.
    pub clause_size_limit: usize,
    /// Additive growth allowance on the resolvent-count bound: eliminate iff
    /// `#non_taut_resolvents <= |pos| + |neg| + growth`. 0 = strict non-increasing.
    pub growth: usize,
    /// Skip a variable whose smaller occurrence side exceeds this (bounds the
    /// O(|pos|·|neg|) resolvent scan). `CaDiCaL` `elimocclim` default 100.
    pub occurrence_limit: usize,
    /// Resolution work-budget multiplier. The touched-queue schedule runs to a
    /// fixpoint, bounded by roughly `max_rounds · 30 · (literals + variables)`
    /// total resolution attempts (the near-linear guarantee's safety net).
    pub max_rounds: usize,
}

impl Default for BveOptions {
    fn default() -> Self {
        Self {
            clause_size_limit: 100,
            growth: 0,
            occurrence_limit: 100,
            max_rounds: 4,
        }
    }
}

/// What a [`eliminate_variables`] run did, for diagnostics / benchmark accounting.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct BveStats {
    /// Variables eliminated.
    pub variables_eliminated: usize,
    /// Original (`pos`/`neg`) clauses removed.
    pub clauses_removed: usize,
    /// Resolvent clauses added.
    pub clauses_added: usize,
    /// Tautological resolvents discarded.
    pub tautological_resolvents_skipped: usize,
    /// Variables left in place because elimination would exceed a bound.
    pub variables_skipped_bound: usize,
    /// `1` if any variable was eliminated, else `0` (the schedule runs to a single
    /// fixpoint drain; retained for source compatibility with the round-based API).
    pub rounds: usize,
}

impl BveStats {
    /// Whether anything was eliminated.
    #[must_use]
    pub fn is_empty(self) -> bool {
        self.variables_eliminated == 0
    }
}

/// One eliminated variable's recovery record: the original clauses it occurred in.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ElimRecord {
    var: usize,
    /// Clauses that contained `+var`.
    pos_clauses: Vec<Vec<CnfLit>>,
    /// Clauses that contained `¬var`.
    neg_clauses: Vec<Vec<CnfLit>>,
}

/// The reverse-order replay log produced by BVE: turns a model of the reduced
/// formula into a model of the original. Opaque except for [`Self::extend`].
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Reconstruction {
    /// Records in elimination order; [`Self::extend`] replays them in reverse.
    records: Vec<ElimRecord>,
}

impl Reconstruction {
    /// Extends a model of the reduced formula to a model of the **original**.
    ///
    /// `reduced_model` is indexed by zero-based CNF variable (as
    /// [`crate::CnfAssignment::values`]); eliminated slots may hold arbitrary
    /// placeholders on input — they are overwritten. The returned assignment
    /// satisfies the original formula.
    ///
    /// The rule (per variable, in reverse elimination order): set `x = true`
    /// (satisfying every clause that contained `+x`); if any clause that contained
    /// `¬x` is then unsatisfied, set `x = false` instead. Because later-eliminated
    /// variables are replayed first, every "other literal" already has its value.
    #[must_use]
    pub fn extend(&self, reduced_model: &[bool]) -> Vec<bool> {
        let mut full = reduced_model.to_vec();
        for rec in self.records.iter().rev() {
            full[rec.var] = true;
            let neg_ok = rec
                .neg_clauses
                .iter()
                .all(|c| c.iter().any(|&l| lit_true(l, &full)));
            if !neg_ok {
                full[rec.var] = false;
            }
        }
        full
    }
}

/// The result of [`eliminate_variables`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BveOutcome {
    /// The reduced, equisatisfiable formula (same `variable_count` as the input).
    pub formula: CnfFormula,
    /// Replay log to lift a reduced model back to the original variables.
    pub reconstruction: Reconstruction,
    /// What was eliminated.
    pub stats: BveStats,
}

fn lit_true(lit: CnfLit, asg: &[bool]) -> bool {
    let v = asg[lit.var().index()];
    if lit.is_negated() { !v } else { v }
}

/// Zero-based occurrence-list index for a literal: `2 * variable + sign`.
fn lit_index(lit: CnfLit) -> usize {
    2 * lit.var().index() + usize::from(lit.is_negated())
}

/// The mutable elimination state: live clauses, literal occurrence lists, the
/// touched-variable schedule, and the reconstruction log.
struct Eliminator {
    /// Live clauses; `None` marks a removed (garbage) clause.
    clauses: Vec<Option<Vec<CnfLit>>>,
    /// `occ[lit_index(l)]` = clause ids that contain `l` (lazily maintained).
    occ: Vec<Vec<usize>>,
    /// Variables waiting to be (re)considered.
    queue: VecDeque<usize>,
    /// Membership flag for `queue`, to avoid duplicate enqueues.
    in_queue: Vec<bool>,
    /// Eliminated-variable flags.
    eliminated: Vec<bool>,
    /// Reverse-replay records in elimination order.
    records: Vec<ElimRecord>,
    /// Total resolution attempts so far (bounded by the work budget).
    resolutions: usize,
}

impl Eliminator {
    /// Live clause ids containing `lit` (skipping lazily-removed clauses). A clause
    /// is immutable once created, so membership in `occ[lit]` never goes stale
    /// except by removal.
    fn live_ids(&self, lit: CnfLit) -> Vec<usize> {
        self.occ[lit_index(lit)]
            .iter()
            .copied()
            .filter(|&ci| self.clauses[ci].is_some())
            .collect()
    }

    /// Re-queues `var` for reconsideration unless it is eliminated or already queued.
    fn enqueue(&mut self, var: usize) {
        if !self.eliminated[var] && !self.in_queue[var] {
            self.in_queue[var] = true;
            self.queue.push_back(var);
        }
    }

    /// Attempts to eliminate `x` by bounded resolution. Returns whether it was
    /// eliminated; on success it has rewritten clauses/occ lists and re-queued the
    /// affected neighbour variables.
    fn try_eliminate(&mut self, x: usize, opts: BveOptions, stats: &mut BveStats) -> bool {
        let pos_lit = CnfLit::positive(CnfVar::new(x).expect("var index in range"));
        let neg_lit = pos_lit.negated();
        let pos_ids = self.live_ids(pos_lit);
        let neg_ids = self.live_ids(neg_lit);

        if pos_ids.is_empty() && neg_ids.is_empty() {
            return false; // already gone
        }
        if pos_ids.len().min(neg_ids.len()) > opts.occurrence_limit {
            stats.variables_skipped_bound += 1;
            return false;
        }

        // Build non-tautological, deduplicated resolvents.
        let mut resolvents: Vec<Vec<CnfLit>> = Vec::new();
        let mut taut_skipped = 0usize;
        for &pi in &pos_ids {
            for &ni in &neg_ids {
                self.resolutions += 1;
                let p = self.clauses[pi].as_ref().expect("live");
                let n = self.clauses[ni].as_ref().expect("live");
                let mut merged: Vec<CnfLit> = p.iter().copied().filter(|&l| l != pos_lit).collect();
                merged.extend(n.iter().copied().filter(|&l| l != neg_lit));
                match NormClause::from_lits(&merged) {
                    Some(nc) => {
                        if nc.lits.len() > opts.clause_size_limit {
                            stats.variables_skipped_bound += 1;
                            return false; // a resolvent too large: do not eliminate
                        }
                        if !resolvents.contains(&nc.lits) {
                            resolvents.push(nc.lits);
                        }
                    }
                    None => taut_skipped += 1, // tautology
                }
            }
        }

        // Non-increasing bound: resolvents must not exceed the eliminated clauses.
        if resolvents.len() > pos_ids.len() + neg_ids.len() + opts.growth {
            stats.variables_skipped_bound += 1;
            return false;
        }

        // Commit: record the original occurrences for reconstruction.
        let pos_clauses: Vec<Vec<CnfLit>> = pos_ids
            .iter()
            .map(|&ci| self.clauses[ci].clone().expect("live"))
            .collect();
        let neg_clauses: Vec<Vec<CnfLit>> = neg_ids
            .iter()
            .map(|&ci| self.clauses[ci].clone().expect("live"))
            .collect();

        // Neighbour variables (from the clauses being removed) whose environment
        // shrinks and that should be reconsidered.
        let mut neighbours: Vec<usize> = Vec::new();
        for &ci in pos_ids.iter().chain(neg_ids.iter()) {
            if let Some(lits) = &self.clauses[ci] {
                for &l in lits {
                    if l.var().index() != x {
                        neighbours.push(l.var().index());
                    }
                }
            }
        }

        self.records.push(ElimRecord {
            var: x,
            pos_clauses,
            neg_clauses,
        });

        // Remove pivot clauses (lazy: ids stay in occ lists, skipped on scan).
        for &ci in pos_ids.iter().chain(neg_ids.iter()) {
            self.clauses[ci] = None;
        }
        stats.clauses_removed += pos_ids.len() + neg_ids.len();
        stats.tautological_resolvents_skipped += taut_skipped;
        stats.clauses_added += resolvents.len();

        // Append resolvents, connecting their literals and noting their variables.
        for r in resolvents {
            let new_id = self.clauses.len();
            for &l in &r {
                self.occ[lit_index(l)].push(new_id);
                neighbours.push(l.var().index());
            }
            self.clauses.push(Some(r));
        }
        stats.variables_eliminated += 1;

        neighbours.sort_unstable();
        neighbours.dedup();
        for nbr in neighbours {
            if nbr != x {
                self.enqueue(nbr);
            }
        }
        true
    }
}

/// Eliminates variables from `formula` by bounded resolution (see module docs).
///
/// The result is **equisatisfiable** to `formula`: it is SAT iff `formula` is, and
/// every model of `outcome.formula`, after `outcome.reconstruction.extend(..)`,
/// satisfies `formula`. The reduced formula keeps the same `variable_count` (an
/// eliminated variable simply occurs in no clause), so variable indices — and
/// therefore reconstruction — stay stable.
#[must_use]
pub fn eliminate_variables(formula: &CnfFormula, opts: BveOptions) -> BveOutcome {
    eliminate_variables_within(formula, opts, None)
}

/// Like [`eliminate_variables`], but stops scheduling new eliminations once
/// `deadline` passes (checked between variables, so already-committed eliminations
/// always complete). The partial result is still equisatisfiable with a valid
/// reconstruction; only fewer variables are eliminated. `None` means no deadline.
#[must_use]
pub fn eliminate_variables_within(
    formula: &CnfFormula,
    opts: BveOptions,
    deadline: Option<Instant>,
) -> BveOutcome {
    let nvars = formula.variable_count();
    let mut stats = BveStats::default();

    // Live clauses as normalized literal sets. Tautologies and duplicate literals
    // in the input are dropped up front.
    let clauses: Vec<Option<Vec<CnfLit>>> = formula
        .clauses()
        .filter_map(|c| NormClause::from_lits(c).map(|nc| Some(nc.lits)))
        .collect();

    // Full literal occurrence lists.
    let mut occ: Vec<Vec<usize>> = vec![Vec::new(); 2 * nvars];
    let mut total_lits = 0usize;
    for (ci, slot) in clauses.iter().enumerate() {
        if let Some(lits) = slot {
            for &l in lits {
                occ[lit_index(l)].push(ci);
            }
            total_lits += lits.len();
        }
    }

    let mut elim = Eliminator {
        clauses,
        occ,
        queue: VecDeque::new(),
        in_queue: vec![false; nvars],
        eliminated: vec![false; nvars],
        records: Vec::new(),
        resolutions: 0,
    };

    // Seed the schedule with every occurring variable, fewest occurrences first
    // (cheap eliminations — pure and near-pure literals — go first).
    let mut seed: Vec<usize> = (0..nvars)
        .filter(|&x| !elim.occ[2 * x].is_empty() || !elim.occ[2 * x + 1].is_empty())
        .collect();
    seed.sort_by_key(|&x| (elim.occ[2 * x].len() + elim.occ[2 * x + 1].len(), x));
    for x in seed {
        elim.in_queue[x] = true;
        elim.queue.push_back(x);
    }

    let budget = opts.max_rounds.max(1) * 30 * (total_lits + nvars);
    let mut eliminated_any = false;
    while let Some(x) = elim.queue.pop_front() {
        elim.in_queue[x] = false;
        if elim.eliminated[x] {
            continue;
        }
        if elim.resolutions > budget {
            break; // bounded work: stop (the partial result is still equisatisfiable)
        }
        // Per-variable deadline poll (`Instant::now()` is tens of ns; a single
        // `try_eliminate` is bounded by `occurrence_limit²`, so overshoot is tiny).
        if deadline.is_some_and(|dl| Instant::now() >= dl) {
            break; // out of time: keep the partial (equisatisfiable) result
        }
        if elim.try_eliminate(x, opts, &mut stats) {
            elim.eliminated[x] = true;
            eliminated_any = true;
        }
    }
    stats.rounds = usize::from(eliminated_any);

    // Rebuild the reduced formula from the live clauses.
    let mut out = CnfFormula::new(nvars);
    for lits in elim.clauses.into_iter().flatten() {
        // Infallible: variables are a subset of the original's.
        let _ = out.add_clause(CnfClause::new(lits));
    }
    BveOutcome {
        formula: out,
        reconstruction: Reconstruction {
            records: elim.records,
        },
        stats,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CnfFormula, CnfLit, CnfVar, ProofSolveOutcome, SatResult, check_drat,
        solve_with_drat_proof, solve_with_rustsat_batsat,
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
    fn formula(nvars: usize, clauses: &[&[CnfLit]]) -> CnfFormula {
        let mut f = CnfFormula::new(nvars);
        for c in clauses {
            f.add_clause(CnfClause::new(c.to_vec())).unwrap();
        }
        f
    }

    /// Whether `f` has a satisfying assignment, brute force over `nvars` variables.
    fn sat(f: &CnfFormula, nvars: usize) -> bool {
        (0u32..(1u32 << nvars)).any(|mask| {
            let asg: Vec<bool> = (0..nvars).map(|i| (mask >> i) & 1 == 1).collect();
            f.evaluate(&asg).unwrap()
        })
    }

    #[test]
    fn equisatisfiable_and_reconstruction_correct() {
        // x is an "and-gate"-ish definition: (¬x∨a)(¬x∨b)(x∨¬a∨¬b).
        let f = formula(3, &[&[n(0), p(1)], &[n(0), p(2)], &[p(0), n(1), n(2)]]);
        let out = eliminate_variables(&f, BveOptions::default());
        assert!(
            out.stats.variables_eliminated >= 1,
            "x should be eliminated"
        );

        // Equisatisfiable: same SAT status over the reduced var set.
        assert_eq!(sat(&out.formula, 3), sat(&f, 3));

        // Every model of the reduced formula extends to a model of the original.
        for mask in 0u32..(1 << 3) {
            let m: Vec<bool> = (0..3).map(|i| (mask >> i) & 1 == 1).collect();
            if out.formula.evaluate(&m).unwrap() {
                let full = out.reconstruction.extend(&m);
                assert!(
                    f.evaluate(&full).unwrap(),
                    "reconstructed model {full:?} must satisfy the original"
                );
            }
        }
    }

    #[test]
    fn eliminates_a_pure_literal() {
        // x occurs only positively → eliminating it just drops its clauses.
        let f = formula(2, &[&[p(0), p(1)], &[p(0)], &[p(1)]]);
        let out = eliminate_variables(&f, BveOptions::default());
        assert!(out.stats.variables_eliminated >= 1);
        // x (var 0) occurs in no remaining clause.
        for c in out.formula.clauses() {
            assert!(c.iter().all(|l| l.var() != v(0)));
        }
        assert_eq!(sat(&out.formula, 2), sat(&f, 2));
        for mask in 0u32..4 {
            let m: Vec<bool> = (0..2).map(|i| (mask >> i) & 1 == 1).collect();
            if out.formula.evaluate(&m).unwrap() {
                assert!(f.evaluate(&out.reconstruction.extend(&m)).unwrap());
            }
        }
    }

    #[test]
    fn growth_zero_never_increases_clause_count() {
        // The non-increasing bound guarantees: with growth = 0, the total
        // resolvents added never exceeds the clauses removed — on any formula.
        let formulas = [
            formula(3, &[&[n(0), p(1)], &[n(0), p(2)], &[p(0), n(1), n(2)]]),
            formula(
                7,
                &[
                    &[p(0), p(1)],
                    &[p(0), p(2)],
                    &[p(0), p(3)],
                    &[n(0), p(4)],
                    &[n(0), p(5)],
                    &[n(0), p(6)],
                ],
            ),
            formula(
                4,
                &[&[p(0), p(1)], &[n(0), p(2)], &[n(1), p(3)], &[n(2), n(3)]],
            ),
        ];
        for (i, f) in formulas.iter().enumerate() {
            let out = eliminate_variables(f, BveOptions::default());
            assert!(
                out.stats.clauses_added <= out.stats.clauses_removed,
                "formula {i}: added {} > removed {} (bound violated)",
                out.stats.clauses_added,
                out.stats.clauses_removed
            );
            let nvars = f.variable_count();
            assert_eq!(sat(&out.formula, nvars), sat(f, nvars), "formula {i}");
        }
    }

    #[test]
    fn clause_size_limit_causes_a_bound_skip() {
        // No pure literals (every var both phases, all occ 2), so x = var 0 is the
        // first candidate and is genuinely resolved: its one resolvent (a∨b∨c∨d)
        // has size 4. With a limit of 3 it is rejected (a bound skip); the result
        // stays equisatisfiable.
        let f = formula(
            5,
            &[
                &[p(0), p(1), p(2)],
                &[n(0), p(3), p(4)],
                &[n(1), n(2)],
                &[n(3), n(4)],
            ],
        );
        let tight = eliminate_variables(
            &f,
            BveOptions {
                clause_size_limit: 3,
                ..BveOptions::default()
            },
        );
        assert!(
            tight.stats.variables_skipped_bound >= 1,
            "the size-4 resolvent must be rejected at limit 3"
        );
        assert_eq!(sat(&tight.formula, 5), sat(&f, 5));

        // With the default (100) limit the size-4 resolvent is allowed.
        let loose = eliminate_variables(&f, BveOptions::default());
        assert_eq!(sat(&loose.formula, 5), sat(&f, 5));
        for mask in 0u32..(1 << 5) {
            let m: Vec<bool> = (0..5).map(|i| (mask >> i) & 1 == 1).collect();
            if loose.formula.evaluate(&m).unwrap() {
                assert!(f.evaluate(&loose.reconstruction.extend(&m)).unwrap());
            }
        }
    }

    #[test]
    fn sat_result_and_drat_preserved() {
        // SAT case: a definitional x, formula satisfiable; reduced model extends.
        let sat_f = formula(3, &[&[n(0), p(1)], &[p(0), p(2)], &[p(1), p(2)]]);
        let out = eliminate_variables(&sat_f, BveOptions::default());
        let SatResult::Sat(model) = solve_with_rustsat_batsat(&out.formula).unwrap() else {
            panic!("reduced formula should be sat");
        };
        assert!(matches!(
            solve_with_rustsat_batsat(&sat_f).unwrap(),
            SatResult::Sat(_)
        ));
        let full = out.reconstruction.extend(model.values());
        assert!(
            sat_f.evaluate(&full).unwrap(),
            "extended model must satisfy the original"
        );

        // UNSAT case: (a)(¬a∨b)(¬b) with `a` eliminable; reduced still UNSAT + DRAT.
        let unsat_f = formula(2, &[&[p(0)], &[n(0), p(1)], &[n(1)]]);
        let out = eliminate_variables(&unsat_f, BveOptions::default());
        assert!(matches!(
            solve_with_rustsat_batsat(&out.formula).unwrap(),
            SatResult::Unsat(_)
        ));
        match solve_with_drat_proof(&out.formula) {
            ProofSolveOutcome::Unsat(proof) => {
                assert!(check_drat(&out.formula, &proof).unwrap(), "DRAT must check");
            }
            other => panic!("expected unsat proof, got {other:?}"),
        }
    }

    #[test]
    fn larger_formula_reconstructs_for_every_model() {
        // 5 variables, several eliminable; brute-force the reconstruction contract.
        let f = formula(
            5,
            &[
                &[n(0), p(1)],
                &[n(0), p(2)],
                &[p(0), n(1), n(2)],
                &[n(3), p(4)],
                &[p(3), n(4)],
                &[p(1), p(3)],
            ],
        );
        let out = eliminate_variables(&f, BveOptions::default());
        assert!(out.stats.variables_eliminated >= 1);
        assert_eq!(sat(&out.formula, 5), sat(&f, 5));
        for mask in 0u32..(1 << 5) {
            let m: Vec<bool> = (0..5).map(|i| (mask >> i) & 1 == 1).collect();
            if out.formula.evaluate(&m).unwrap() {
                assert!(
                    f.evaluate(&out.reconstruction.extend(&m)).unwrap(),
                    "model {m:?} must reconstruct"
                );
            }
        }
    }

    /// Deterministic xorshift PRNG (no clock/`Math.random`; reproducible).
    fn xorshift(state: &mut u64) -> u64 {
        let mut x = *state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        *state = x;
        x
    }

    fn rand_usize(state: &mut u64) -> usize {
        usize::try_from(xorshift(state)).unwrap_or(usize::MAX)
    }

    #[test]
    fn random_formulas_stay_equisatisfiable_and_reconstruct() {
        // Stress the occurrence-list elimination + touched queue against the
        // brute-force semantics on many random 5-variable formulas: equisatisfiable,
        // and every model of the reduced formula reconstructs to a model of the
        // original.
        const NVARS: usize = 5;
        let mut state = 0xDEAD_BEEF_CAFE_F00Du64;
        for _ in 0..400 {
            let nclauses = 1 + rand_usize(&mut state) % 10;
            let mut f = CnfFormula::new(NVARS);
            for _ in 0..nclauses {
                let width = 1 + rand_usize(&mut state) % 3;
                let mut lits = Vec::new();
                for _ in 0..width {
                    let var = rand_usize(&mut state) % NVARS;
                    lits.push(if xorshift(&mut state) & 1 == 0 {
                        p(var)
                    } else {
                        n(var)
                    });
                }
                f.add_clause(CnfClause::new(lits)).unwrap();
            }
            let out = eliminate_variables(&f, BveOptions::default());
            assert_eq!(
                sat(&out.formula, NVARS),
                sat(&f, NVARS),
                "equisatisfiability must hold"
            );
            for mask in 0u32..(1 << NVARS) {
                let m: Vec<bool> = (0..NVARS).map(|i| (mask >> i) & 1 == 1).collect();
                if out.formula.evaluate(&m).unwrap() {
                    assert!(
                        f.evaluate(&out.reconstruction.extend(&m)).unwrap(),
                        "reconstructed model must satisfy the original"
                    );
                }
            }
        }
    }
}
