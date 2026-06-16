//! CNF subsumption simplification (Track 1, P1.1 / task T1.1.1).
//!
//! Bit-blasting an AIG via Tseitin floods the CNF with intermediate variables
//! and redundant clauses; collapsing them before (and during) solving is the
//! single biggest performance lever for a bit-blasting solver. This module is the
//! warm-up step toward bounded variable elimination: **forward subsumption** plus
//! **self-subsuming resolution**, the cheapest high-value inprocessing.
//!
//! All three transformations applied here are **model-preserving** (the simplified
//! formula has exactly the same satisfying assignments), so they are sound for
//! both `sat` (models lift back unchanged) and `unsat`:
//!
//! * **Tautology removal** — a clause containing both `l` and `¬l` is always true;
//!   dropping it changes no model.
//! * **Forward subsumption** — if clause `D ⊆ C` (as literal sets) and `D` remains
//!   in the formula, then `C` is entailed by `D`, so removing `C` is sound and
//!   model-preserving (`F ≡ F \ {C}`).
//! * **Self-subsuming resolution** — if some clause `D` contains `¬l` and
//!   `D \ {¬l} ⊆ C \ {l}`, then `C` can be strengthened to `C \ {l}`; because the
//!   witness `D` stays in the formula, `F'' ∧ C ≡ F'' ∧ (C \ {l})` (model-preserving,
//!   not merely equisatisfiable).
//!
//! This first slice is a straightforward O(clauses²) sweep with a 64-bit literal
//! signature (à la Z3's `var_approx_set`) as a fast reject; an occurrence-list
//! index is the natural follow-up once profiling calls for it. It is a pure
//! `CnfFormula → CnfFormula` transform and does not yet emit DRAT deletion steps
//! (the proof-pipeline integration is the next task).

use crate::{CnfClause, CnfFormula, CnfLit};

/// What a [`simplify`] pass removed, for diagnostics and benchmark accounting.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct SubsumeStats {
    /// Always-true clauses (containing `l` and `¬l`) dropped.
    pub tautologies_removed: usize,
    /// Clauses removed because another clause subsumes them (incl. duplicates).
    pub clauses_subsumed: usize,
    /// Literals removed by self-subsuming resolution.
    pub literals_strengthened: usize,
}

impl SubsumeStats {
    /// Whether the pass changed anything.
    #[must_use]
    pub fn is_empty(self) -> bool {
        self == SubsumeStats::default()
    }
}

/// A normalized clause: literals sorted + deduplicated, with a 64-bit signature
/// over literal identities for fast subset rejection. Shared with [`crate::bve`].
#[derive(Debug, Clone)]
pub(crate) struct NormClause {
    pub(crate) lits: Vec<CnfLit>,
    pub(crate) sig: u64,
}

/// One bit of the signature for a literal (variable index + sign folded mod 64).
pub(crate) fn lit_bit(lit: CnfLit) -> u64 {
    let key = lit.var().index().wrapping_mul(2) + usize::from(lit.is_negated());
    1u64 << (key % 64)
}

impl NormClause {
    /// Normalizes a clause; returns `None` if it is a tautology (always true).
    pub(crate) fn from_clause(clause: &CnfClause) -> Option<Self> {
        let mut lits = clause.lits().to_vec();
        lits.sort_unstable();
        lits.dedup();
        // Tautology: some variable appears both positive and negative. After
        // sorting, a literal and its complement are adjacent only if the positive
        // form sorts right before the negative; check directly instead.
        for (i, &l) in lits.iter().enumerate() {
            if lits[i + 1..].iter().any(|&m| m == l.negated()) {
                return None;
            }
        }
        let sig = lits.iter().fold(0u64, |acc, &l| acc | lit_bit(l));
        Some(Self { lits, sig })
    }

    /// Whether `self`'s literal set is a subset of `other`'s (so `self` subsumes
    /// `other`). Both literal vectors are sorted; uses the signature to reject
    /// fast, then a two-pointer subset check.
    pub(crate) fn subsumes(&self, other: &NormClause) -> bool {
        if self.lits.len() > other.lits.len() || (self.sig & !other.sig) != 0 {
            return false;
        }
        let mut it = other.lits.iter();
        'outer: for &want in &self.lits {
            for &have in it.by_ref() {
                if have == want {
                    continue 'outer;
                }
                if have > want {
                    return false; // sorted: `want` can no longer appear
                }
            }
            return false;
        }
        true
    }
}

/// Simplifies `formula` by tautology removal, forward subsumption, and one round
/// of self-subsuming resolution. Returns the simplified formula and the
/// [`SubsumeStats`]. The result is **logically equivalent** to the input (same
/// variable count, same satisfying assignments).
#[must_use]
pub fn simplify(formula: &CnfFormula) -> (CnfFormula, SubsumeStats) {
    let mut stats = SubsumeStats::default();

    // 1. Normalize; drop tautologies.
    let mut norm: Vec<NormClause> = Vec::with_capacity(formula.clauses().len());
    for clause in formula.clauses() {
        match NormClause::from_clause(clause) {
            Some(nc) => norm.push(nc),
            None => stats.tautologies_removed += 1,
        }
    }

    // 2. Forward subsumption. Process shortest clauses first and keep a clause
    //    only if no already-kept clause subsumes it. This removes duplicates
    //    (keeps one) and longer clauses subsumed by shorter ones.
    norm.sort_by_key(|c| c.lits.len());
    let mut kept: Vec<NormClause> = Vec::with_capacity(norm.len());
    for c in norm {
        if kept.iter().any(|k| k.subsumes(&c)) {
            stats.clauses_subsumed += 1;
        } else {
            kept.push(c);
        }
    }

    // 3. Self-subsuming resolution (one round): for each clause C and literal l,
    //    if some other clause D contains ¬l and D\{¬l} ⊆ C\{l}, drop l from C.
    let snapshot = kept.clone();
    for c in &mut kept {
        let mut i = 0;
        while i < c.lits.len() {
            let l = c.lits[i];
            if self_subsumes_on(&snapshot, c, l) {
                c.lits.remove(i);
                c.sig = c.lits.iter().fold(0u64, |acc, &m| acc | lit_bit(m));
                stats.literals_strengthened += 1;
            } else {
                i += 1;
            }
        }
    }

    // Rebuild the formula.
    let mut out = CnfFormula::new(formula.variable_count());
    for c in kept {
        // Infallible: variables are unchanged from `formula`, already validated.
        let _ = out.add_clause(CnfClause::new(c.lits));
    }
    (out, stats)
}

/// Whether clause `c` can be strengthened by removing literal `l`: some clause in
/// `others` contains `¬l` and (that clause minus `¬l`) is a subset of (`c` minus
/// `l`). `c` itself is skipped (matched by identity of the remaining literals).
fn self_subsumes_on(others: &[NormClause], c: &NormClause, l: CnfLit) -> bool {
    let not_l = l.negated();
    // The "C minus l" literal set, as a signature-bearing pseudo-clause.
    let c_minus_l: Vec<CnfLit> = c.lits.iter().copied().filter(|&m| m != l).collect();
    let c_minus_sig = c_minus_l.iter().fold(0u64, |acc, &m| acc | lit_bit(m));
    let c_minus = NormClause {
        lits: c_minus_l,
        sig: c_minus_sig,
    };
    for d in others {
        if !d.lits.contains(&not_l) {
            continue;
        }
        // d_minus = D \ {¬l}; require d_minus ⊆ c_minus.
        let d_minus_lits: Vec<CnfLit> = d.lits.iter().copied().filter(|&m| m != not_l).collect();
        // Skip the degenerate self-match (D\{¬l} identical situation): D must be a
        // genuinely different clause; if d_minus == c_minus and D has ¬l where C
        // has l, D is a different clause, which is exactly the resolution witness.
        let d_minus_sig = d_minus_lits.iter().fold(0u64, |acc, &m| acc | lit_bit(m));
        let d_minus = NormClause {
            lits: d_minus_lits,
            sig: d_minus_sig,
        };
        if d_minus.subsumes(&c_minus) {
            return true;
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CnfFormula, CnfLit, CnfVar};

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

    /// Brute-force: two formulas over `nvars` variables agree on every assignment.
    fn equivalent(a: &CnfFormula, b: &CnfFormula, nvars: usize) {
        assert_eq!(a.variable_count(), b.variable_count());
        for mask in 0u32..(1u32 << nvars) {
            let asg: Vec<bool> = (0..nvars).map(|i| (mask >> i) & 1 == 1).collect();
            assert_eq!(
                a.evaluate(&asg).unwrap(),
                b.evaluate(&asg).unwrap(),
                "disagree on assignment {asg:?}"
            );
        }
    }

    #[test]
    fn removes_a_subsumed_clause() {
        // (a) subsumes (a ∨ b): drop the longer clause.
        let f = formula(2, &[&[p(0)], &[p(0), p(1)]]);
        let (out, stats) = simplify(&f);
        assert_eq!(stats.clauses_subsumed, 1);
        assert_eq!(out.clauses().len(), 1);
        assert_eq!(out.clauses()[0].lits(), &[p(0)]);
        equivalent(&f, &out, 2);
    }

    #[test]
    fn removes_duplicate_clauses() {
        let f = formula(2, &[&[p(0), p(1)], &[p(1), p(0)]]);
        let (out, stats) = simplify(&f);
        assert_eq!(
            stats.clauses_subsumed, 1,
            "one of the duplicates is dropped"
        );
        assert_eq!(out.clauses().len(), 1);
        equivalent(&f, &out, 2);
    }

    #[test]
    fn drops_tautologies() {
        // (a ∨ ¬a) is always true; (b) stays.
        let f = formula(2, &[&[p(0), n(0)], &[p(1)]]);
        let (out, stats) = simplify(&f);
        assert_eq!(stats.tautologies_removed, 1);
        assert_eq!(out.clauses().len(), 1);
        assert_eq!(out.clauses()[0].lits(), &[p(1)]);
        equivalent(&f, &out, 2);
    }

    #[test]
    fn self_subsuming_resolution_strengthens() {
        // (a ∨ b) and (¬a ∨ b): resolving on a gives (b), strengthening both.
        // Self-subsumption: (¬a ∨ b) lets us drop a from (a ∨ b) → (b), and
        // symmetrically. The result is equivalent to the original.
        let f = formula(2, &[&[p(0), p(1)], &[n(0), p(1)]]);
        let (out, stats) = simplify(&f);
        assert!(
            stats.literals_strengthened >= 1,
            "expected a strengthening, got {stats:?}"
        );
        equivalent(&f, &out, 2);
        // The strengthened formula entails (b).
        for mask in 0u32..4 {
            let asg: Vec<bool> = (0..2).map(|i| (mask >> i) & 1 == 1).collect();
            if out.evaluate(&asg).unwrap() {
                assert!(asg[1], "every model of the simplified formula has b true");
            }
        }
    }

    #[test]
    fn is_idempotent() {
        let f = formula(
            3,
            &[
                &[p(0), p(1), p(2)],
                &[p(0)],
                &[p(0), p(1)],
                &[p(1), n(1)],
                &[n(2), p(0)],
            ],
        );
        let (once, _) = simplify(&f);
        let (twice, stats2) = simplify(&once);
        assert!(
            stats2.is_empty(),
            "second pass should be a fixpoint: {stats2:?}"
        );
        assert_eq!(once, twice);
        equivalent(&f, &once, 3);
    }

    #[test]
    fn sat_result_and_drat_are_preserved_after_simplification() {
        use crate::{
            ProofSolveOutcome, SatResult, check_drat, solve_with_drat_proof,
            solve_with_rustsat_batsat,
        };
        // UNSAT: (a) ∧ (¬a) ∧ (a ∨ b) — the last clause is subsumed by (a).
        let f = formula(2, &[&[p(0)], &[n(0)], &[p(0), p(1)]]);
        let (out, stats) = simplify(&f);
        assert!(stats.clauses_subsumed >= 1, "expected a subsumed clause");
        assert!(
            out.clauses().len() < f.clauses().len(),
            "clause count dropped"
        );

        // Both formulas are still UNSAT (satisfiability preserved).
        assert!(matches!(
            solve_with_rustsat_batsat(&f).unwrap(),
            SatResult::Unsat(_)
        ));
        assert!(matches!(
            solve_with_rustsat_batsat(&out).unwrap(),
            SatResult::Unsat(_)
        ));

        // The simplified UNSAT still carries a DRAT proof that re-checks.
        match solve_with_drat_proof(&out) {
            ProofSolveOutcome::Unsat(proof) => {
                assert!(check_drat(&out, &proof).unwrap(), "DRAT must still check");
            }
            other => panic!("expected an unsat proof, got {other:?}"),
        }
    }

    #[test]
    fn preserves_models_on_a_larger_random_ish_formula() {
        // A hand-built formula with redundancy across 4 variables; brute-force
        // confirms exact equivalence (the soundness contract).
        let f = formula(
            4,
            &[
                &[p(0), p(1)],
                &[p(0), p(1), p(2)], // subsumed by (a ∨ b)
                &[n(0), p(1)],       // self-subsumes (a ∨ b) on a
                &[p(2), p(3)],
                &[p(2), p(3), n(0)], // subsumed by (c ∨ d)
                &[p(3), n(3)],       // tautology
            ],
        );
        let (out, stats) = simplify(&f);
        assert!(!stats.is_empty());
        assert!(out.clauses().len() < f.clauses().len());
        equivalent(&f, &out, 4);
    }
}
