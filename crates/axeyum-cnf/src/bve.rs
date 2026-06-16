//! Bounded variable elimination (Track 1, P1.1 / task T1.1.2).
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
//! This first slice is a clear, deterministic transform; it does not yet emit DRAT
//! steps relating the reduced formula's proof back to the original (a separate
//! proof-pipeline task, as for `simplify`). Occurrence lists are recomputed per
//! candidate (correctness-first); incremental maintenance is the follow-up.

use crate::simplify::NormClause;
use crate::{CnfClause, CnfFormula, CnfLit};

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
    /// Max elimination rounds before stopping at a fixpoint.
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
    /// Elimination rounds executed.
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

/// Eliminates variables from `formula` by bounded resolution (see module docs).
///
/// The result is **equisatisfiable** to `formula`: it is SAT iff `formula` is, and
/// every model of `outcome.formula`, after `outcome.reconstruction.extend(..)`,
/// satisfies `formula`. The reduced formula keeps the same `variable_count` (an
/// eliminated variable simply occurs in no clause), so variable indices — and
/// therefore reconstruction — stay stable.
#[must_use]
pub fn eliminate_variables(formula: &CnfFormula, opts: BveOptions) -> BveOutcome {
    let nvars = formula.variable_count();
    let mut stats = BveStats::default();

    // Live clauses as normalized literal sets (`None` = removed). Tautologies and
    // duplicate literals in the input are dropped up front.
    let mut clauses: Vec<Option<Vec<CnfLit>>> = formula
        .clauses()
        .iter()
        .filter_map(|c| NormClause::from_clause(c).map(|nc| Some(nc.lits)))
        .collect();

    let mut eliminated = vec![false; nvars];
    let mut records: Vec<ElimRecord> = Vec::new();

    for round in 0..opts.max_rounds {
        // Round-start occurrence counts give a deterministic candidate order
        // (fewest occurrences first, var index as tiebreak). Per-candidate
        // occurrences are recomputed fresh below, so staleness here is harmless.
        let mut occ = vec![0usize; nvars];
        for lits in clauses.iter().flatten() {
            for &l in lits {
                occ[l.var().index()] += 1;
            }
        }
        let mut candidates: Vec<usize> = (0..nvars)
            .filter(|&x| !eliminated[x] && occ[x] > 0)
            .collect();
        candidates.sort_by_key(|&x| (occ[x], x));

        let mut changed = false;
        for x in candidates {
            if eliminated[x] {
                continue;
            }
            if try_eliminate(x, &mut clauses, &mut records, &mut stats, opts) {
                eliminated[x] = true;
                changed = true;
            }
        }

        stats.rounds = round + 1;
        if !changed {
            break;
        }
    }

    let mut out = CnfFormula::new(nvars);
    for lits in clauses.into_iter().flatten() {
        // Infallible: variables are a subset of the original's.
        let _ = out.add_clause(CnfClause::new(lits));
    }
    BveOutcome {
        formula: out,
        reconstruction: Reconstruction { records },
        stats,
    }
}

/// Attempts to eliminate `x`, mutating the live clause store. Returns whether `x`
/// was eliminated. Occurrences are scanned fresh, so this is always correct after
/// earlier eliminations in the same round.
fn try_eliminate(
    x: usize,
    clauses: &mut Vec<Option<Vec<CnfLit>>>,
    records: &mut Vec<ElimRecord>,
    stats: &mut BveStats,
    opts: BveOptions,
) -> bool {
    let pos_lit = CnfLit::positive(crate::CnfVar::new(x).expect("var index in range"));
    let neg_lit = pos_lit.negated();

    let mut pos_idx = Vec::new();
    let mut neg_idx = Vec::new();
    for (ci, slot) in clauses.iter().enumerate() {
        if let Some(lits) = slot {
            if lits.contains(&pos_lit) {
                pos_idx.push(ci);
            } else if lits.contains(&neg_lit) {
                neg_idx.push(ci);
            }
        }
    }
    if pos_idx.is_empty() && neg_idx.is_empty() {
        return false; // already gone
    }
    if pos_idx.len().min(neg_idx.len()) > opts.occurrence_limit {
        stats.variables_skipped_bound += 1;
        return false;
    }

    // Build non-tautological, deduplicated resolvents.
    let mut resolvents: Vec<Vec<CnfLit>> = Vec::new();
    let mut taut_skipped = 0usize;
    for &pi in &pos_idx {
        let p = clauses[pi].as_ref().expect("live");
        for &ni in &neg_idx {
            let n = clauses[ni].as_ref().expect("live");
            let mut merged: Vec<CnfLit> = p.iter().copied().filter(|&l| l != pos_lit).collect();
            merged.extend(n.iter().copied().filter(|&l| l != neg_lit));
            match NormClause::from_clause(&CnfClause::new(merged)) {
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
    if resolvents.len() > pos_idx.len() + neg_idx.len() + opts.growth {
        stats.variables_skipped_bound += 1;
        return false;
    }

    // Commit: record the original occurrences, remove them, add the resolvents.
    let pos_clauses: Vec<Vec<CnfLit>> = pos_idx
        .iter()
        .map(|&ci| clauses[ci].as_ref().expect("live").clone())
        .collect();
    let neg_clauses: Vec<Vec<CnfLit>> = neg_idx
        .iter()
        .map(|&ci| clauses[ci].as_ref().expect("live").clone())
        .collect();
    records.push(ElimRecord {
        var: x,
        pos_clauses,
        neg_clauses,
    });

    for &ci in pos_idx.iter().chain(neg_idx.iter()) {
        clauses[ci] = None;
    }
    stats.clauses_removed += pos_idx.len() + neg_idx.len();
    stats.tautological_resolvents_skipped += taut_skipped;
    stats.clauses_added += resolvents.len();
    for r in resolvents {
        clauses.push(Some(r));
    }
    stats.variables_eliminated += 1;
    true
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
            assert!(c.lits().iter().all(|l| l.var() != v(0)));
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
}
