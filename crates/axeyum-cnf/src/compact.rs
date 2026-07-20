//! Sound CNF variable compaction (Track 1, P1.1 — perf front, BVE companion).
//!
//! Bounded variable elimination ([`crate::bve`]) removes clauses and variables,
//! but it never *renumbers*: the reduced formula keeps the same
//! [`CnfFormula::variable_count`] as the input (an eliminated variable simply
//! occurs in no clause). On bit-blasted CNF this leaves large gaps — millions of
//! dead indices below the unchanged max — so the variable-bound admission gate
//! (which reads `variable_count`) still refuses formulas whose live variable set
//! is tiny.
//!
//! [`compact`] closes the gap with a pure renumbering bijection on the *live*
//! variables (those that actually appear in some clause): it densely renumbers
//! them to `0..m`, rewrites every clause's literals to the new dense variables
//! (preserving sign), and returns a formula whose `variable_count` is exactly the
//! live count `m` (≤ the original). Because compaction is a bijection on the live
//! set and the dead variables constrain nothing, it cannot change sat/unsat: a
//! model of the compacted formula corresponds exactly to a model of the reduced
//! formula restricted to its live variables.
//!
//! The companion [`CompactMap::expand`] lifts a model of the compacted formula
//! back to the reduced formula's original variable width, ready to feed
//! [`crate::Reconstruction::extend`].

use std::collections::BTreeSet;

use crate::{CnfClause, CnfFormula, CnfLit, CnfVar};

/// The bijection between the live variables of a formula and the dense
/// `0..new_to_old.len()` range produced by [`compact`], plus the original width
/// so a compacted model can be lifted back.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompactMap {
    /// The original formula's [`CnfFormula::variable_count`] (the width an
    /// expanded model must have, so it lines up with the pre-compaction —
    /// i.e. BVE-reduced — variable space).
    original_width: usize,
    /// `new_to_old[i]` is the original index of dense variable `i`. Sorted
    /// ascending (deterministic), so `new_to_old` is strictly increasing.
    new_to_old: Vec<usize>,
}

impl CompactMap {
    /// The original formula's variable count (the width of an [`Self::expand`]ed
    /// model).
    #[must_use]
    pub fn original_width(&self) -> usize {
        self.original_width
    }

    /// Number of live (dense) variables, i.e. the compacted formula's
    /// `variable_count`.
    #[must_use]
    pub fn live_count(&self) -> usize {
        self.new_to_old.len()
    }

    /// Original index of dense variable `new` (in `0..live_count`).
    #[must_use]
    pub fn original_of(&self, new: usize) -> usize {
        self.new_to_old[new]
    }

    /// Lifts a model of the **compacted** formula back to a model indexed by the
    /// **original** (pre-compaction, BVE-reduced) variable space.
    ///
    /// The returned vector has width exactly [`Self::original_width`]:
    /// `out[new_to_old[i]] = compact_model[i]` for every dense variable `i`, and
    /// `false` (a placeholder) for every original index that is not in the live
    /// set.
    ///
    /// # Soundness of the placeholder
    ///
    /// A placeholder index is a variable that appears in **no clause** of the
    /// compacted formula — equivalently, in no clause of the pre-compaction
    /// (BVE-reduced) formula, since [`compact`] only renumbers and never drops a
    /// literal. So its value is free with respect to every clause of the reduced
    /// formula: choosing `false` cannot falsify any clause. The expanded vector
    /// is therefore a valid model of the BVE-reduced formula whenever
    /// `compact_model` is a model of the compacted one.
    ///
    /// The intended lift order is:
    /// `solve(compacted)` → `compact_model` → `CompactMap::expand` (→
    /// original-width, BVE-reduced model) → [`crate::Reconstruction::extend`] (→
    /// full original model). `Reconstruction::extend` then overwrites exactly the
    /// BVE-eliminated indices (reading the now-correctly-placed live values), and
    /// any index that is *still* dead after that step appears in no clause of the
    /// original formula either (BVE only removes clauses; it never introduces a
    /// variable), so the final model satisfies the original CNF regardless of the
    /// placeholder.
    ///
    /// # Panics
    ///
    /// Panics if `compact_model` is shorter than [`Self::live_count`] (a caller
    /// bug: the compacted solve must cover every dense variable).
    #[must_use]
    pub fn expand(&self, compact_model: &[bool]) -> Vec<bool> {
        assert!(
            compact_model.len() >= self.new_to_old.len(),
            "compact model has {} values, need at least {} (one per live var)",
            compact_model.len(),
            self.new_to_old.len(),
        );
        let mut out = vec![false; self.original_width];
        for (new, &old) in self.new_to_old.iter().enumerate() {
            out[old] = compact_model[new];
        }
        out
    }
}

/// Densely renumbers the live variables of `formula`.
///
/// Collects every variable index that appears in some clause (sorted ascending,
/// deterministically), assigns them dense new indices `0..m`, and rewrites every
/// clause's literals to the new variables, preserving each literal's sign. The
/// returned formula has `variable_count() == m`, which is `≤` the original count
/// and strictly less whenever any original index is dead.
///
/// The pairing is a [`CompactMap`]; use [`CompactMap::expand`] to lift a model of
/// the returned formula back to the original variable width.
///
/// Compaction is a bijection on the live set, so it preserves satisfiability
/// exactly. It is deterministic: the live set is gathered into a sorted
/// [`BTreeSet`], so no hash-map iteration order reaches the output.
///
/// # Panics
///
/// Does not panic on any valid [`CnfFormula`]: the dense indices are bounded by
/// the live count (itself `≤` the input's variable count, which is already a
/// valid `CnfVar` range), so every internal index/`CnfVar` construction succeeds.
#[must_use]
pub fn compact(formula: &CnfFormula) -> (CnfFormula, CompactMap) {
    // Live set: every variable that appears in some clause, sorted ascending.
    let mut live: BTreeSet<usize> = BTreeSet::new();
    for clause in formula.clauses() {
        for lit in clause {
            live.insert(lit.var().index());
        }
    }
    let new_to_old: Vec<usize> = live.into_iter().collect();

    // Old → new lookup over the original width (dense vector; -1 sentinel for
    // dead vars via `Option`). Deterministic and O(original_width + literals).
    let mut old_to_new: Vec<Option<u32>> = vec![None; formula.variable_count()];
    for (new, &old) in new_to_old.iter().enumerate() {
        // `new < new_to_old.len() ≤ formula.variable_count() ≤ u32::MAX` because
        // the input formula's variables are already valid `CnfVar`s.
        old_to_new[old] = Some(u32::try_from(new).expect("live var index fits u32"));
    }

    let mut out = CnfFormula::new(new_to_old.len());
    for clause in formula.clauses() {
        let lits: Vec<CnfLit> = clause
            .iter()
            .map(|lit| {
                let new_index = old_to_new[lit.var().index()]
                    .expect("a literal's variable is in the live set by construction");
                // `new_index < new_to_old.len()`, which is `out`'s variable count.
                let var = CnfVar::new(new_index as usize).expect("dense var index in range");
                let positive = CnfLit::positive(var);
                if lit.is_negated() {
                    positive.negated()
                } else {
                    positive
                }
            })
            .collect();
        // Infallible: every rewritten variable is `< out.variable_count()`.
        let _ = out.add_clause(CnfClause::new(lits));
    }

    (
        out,
        CompactMap {
            original_width: formula.variable_count(),
            new_to_old,
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BveOptions, eliminate_variables};

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

    #[test]
    fn all_live_compacts_to_identity_width() {
        // Every variable 0..3 appears, so compaction is width-preserving.
        let f = formula(3, &[&[p(0), p(1)], &[n(1), p(2)], &[n(0), n(2)]]);
        let (c, map) = compact(&f);
        assert_eq!(c.variable_count(), f.variable_count());
        assert_eq!(map.live_count(), 3);
        assert_eq!(map.original_width(), 3);
        // Identity renumber: new i maps to old i.
        for i in 0..3 {
            assert_eq!(map.original_of(i), i);
        }
        // The clause structure is unchanged.
        assert!(c.clauses().eq(f.clauses()));
    }

    #[test]
    fn dead_variable_lowers_variable_count() {
        // Declared width 5 but only vars 0, 2, 4 appear: compaction drops to 3.
        let f = formula(5, &[&[p(0), n(2)], &[p(4), p(0)]]);
        let (c, map) = compact(&f);
        assert!(
            c.variable_count() < f.variable_count(),
            "dead vars must lower the count: {} !< {}",
            c.variable_count(),
            f.variable_count(),
        );
        assert_eq!(c.variable_count(), 3);
        assert_eq!(map.new_to_old, vec![0, 2, 4]);
    }

    #[test]
    fn compaction_is_deterministic() {
        let f = formula(6, &[&[p(5), n(1)], &[p(3), p(1)], &[n(5)]]);
        let (c1, m1) = compact(&f);
        let (c2, m2) = compact(&f);
        assert_eq!(c1, c2);
        assert_eq!(m1, m2);
        // Sorted live set, no hash order.
        assert_eq!(m1.new_to_old, vec![1, 3, 5]);
    }

    #[test]
    fn expand_places_live_values_and_falses_the_dead() {
        let f = formula(5, &[&[p(0), n(2)], &[p(4)]]);
        let (_c, map) = compact(&f);
        // dense 0→old0, 1→old2, 2→old4
        let expanded = map.expand(&[true, false, true]);
        assert_eq!(expanded.len(), 5);
        assert!(expanded[0]); // live, true
        assert!(!expanded[1]); // dead placeholder
        assert!(!expanded[2]); // live, false
        assert!(!expanded[3]); // dead placeholder
        assert!(expanded[4]); // live, true
    }

    /// Brute-force every assignment of an `nvars`-variable formula and return
    /// whether any satisfies it (small `nvars` only).
    fn sat(f: &CnfFormula, nvars: usize) -> bool {
        (0u32..(1u32 << nvars)).any(|mask| {
            let asg: Vec<bool> = (0..nvars).map(|i| (mask >> i) & 1 == 1).collect();
            f.evaluate(&asg).unwrap()
        })
    }

    #[test]
    fn compaction_preserves_satisfiability() {
        let cases = [
            formula(5, &[&[p(0), n(2)], &[p(4), p(0)], &[n(4), p(2)]]),
            formula(4, &[&[p(0)], &[n(0), p(3)], &[n(3)]]), // unsat
            formula(6, &[&[p(1), p(5)], &[n(1), p(3)], &[n(3), n(5)]]),
        ];
        for f in &cases {
            let (c, map) = compact(f);
            let orig = sat(f, f.variable_count());
            let comp = sat(&c, c.variable_count());
            assert_eq!(orig, comp, "compaction changed satisfiability");
            // Every compacted model expands to a model of the original formula.
            for mask in 0u32..(1u32 << c.variable_count()) {
                let cm: Vec<bool> = (0..c.variable_count())
                    .map(|i| (mask >> i) & 1 == 1)
                    .collect();
                if c.evaluate(&cm).unwrap() {
                    let full = map.expand(&cm);
                    assert!(
                        f.evaluate(&full).unwrap(),
                        "expanded compacted model {full:?} must satisfy the original"
                    );
                }
            }
        }
    }

    /// THE soundness round-trip: BVE → compact → solve compacted → expand →
    /// `Reconstruction::extend` → assert the full model satisfies the ORIGINAL
    /// formula. Includes a case where BVE eliminates ≥1 var AND a variable
    /// becomes dead, so compaction actually renumbers.
    #[test]
    fn bve_then_compact_roundtrip_satisfies_original() {
        // var 4 is declared but unused → already dead before BVE.
        // The and-gate definition over var 0 lets BVE eliminate var 0, which then
        // becomes dead too; compaction renumbers what remains.
        let originals = [
            formula(
                5,
                &[
                    &[n(0), p(1)],
                    &[n(0), p(2)],
                    &[p(0), n(1), n(2)],
                    &[p(1), p(3)],
                    // var 4 never appears → dead from the start.
                ],
            ),
            formula(
                4,
                &[&[p(0), p(1)], &[n(0), p(2)], &[n(1), p(3)], &[n(2), n(3)]],
            ),
            // Pure-literal var 0 (drops on BVE) plus an isolated chain.
            formula(5, &[&[p(0), p(1)], &[p(0)], &[n(1), p(3)], &[n(3), p(4)]]),
        ];

        let mut renumber_seen = false;
        for original in &originals {
            let bve = eliminate_variables(original, BveOptions::default());
            let (compacted, map) = compact(&bve.formula);

            // Sanity: compaction never raises the var count, and the BVE-reduced
            // formula's declared width matches the original (BVE preserves it).
            assert_eq!(bve.formula.variable_count(), original.variable_count());
            assert!(compacted.variable_count() <= bve.formula.variable_count());
            if compacted.variable_count() < bve.formula.variable_count() {
                renumber_seen = true;
            }
            assert_eq!(map.original_width(), bve.formula.variable_count());

            // Equisatisfiable through the whole chain.
            assert_eq!(
                sat(&compacted, compacted.variable_count()),
                sat(original, original.variable_count()),
                "compacted formula must agree on satisfiability with the original"
            );

            // Every model of the compacted formula must, after expand + extend,
            // satisfy the ORIGINAL formula.
            for mask in 0u32..(1u32 << compacted.variable_count()) {
                let cm: Vec<bool> = (0..compacted.variable_count())
                    .map(|i| (mask >> i) & 1 == 1)
                    .collect();
                if compacted.evaluate(&cm).unwrap() {
                    let reduced_model = map.expand(&cm);
                    assert_eq!(
                        reduced_model.len(),
                        original.variable_count(),
                        "expanded model width must match the original variable count"
                    );
                    let full = bve.reconstruction.extend(&reduced_model);
                    assert!(
                        original.evaluate(&full).unwrap(),
                        "expand→extend model {full:?} must satisfy the original formula"
                    );
                }
            }
        }
        assert!(
            renumber_seen,
            "at least one case must actually renumber (BVE-eliminates AND a var goes dead)"
        );
    }

    /// Deterministic xorshift PRNG (no clock; reproducible) for the stress test.
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
    fn random_bve_compact_roundtrip_is_sound() {
        const NVARS: usize = 6;
        let mut state = 0x0C0F_FEE0_BADC_0DE5u64;
        for _ in 0..400 {
            let nclauses = 1 + rand_usize(&mut state) % 8;
            let mut f = CnfFormula::new(NVARS);
            for _ in 0..nclauses {
                let width = 1 + rand_usize(&mut state) % 3;
                // Bias toward a smaller variable range so some of NVARS go dead.
                let mut lits = Vec::new();
                for _ in 0..width {
                    let var = rand_usize(&mut state) % (NVARS - 1);
                    lits.push(if xorshift(&mut state) & 1 == 0 {
                        p(var)
                    } else {
                        n(var)
                    });
                }
                f.add_clause(CnfClause::new(lits)).unwrap();
            }
            let bve = eliminate_variables(&f, BveOptions::default());
            let (compacted, map) = compact(&bve.formula);
            assert!(compacted.variable_count() <= bve.formula.variable_count());
            assert_eq!(
                sat(&compacted, compacted.variable_count()),
                sat(&f, NVARS),
                "compacted+BVE must agree on satisfiability with the original"
            );
            for mask in 0u32..(1u32 << compacted.variable_count()) {
                let cm: Vec<bool> = (0..compacted.variable_count())
                    .map(|i| (mask >> i) & 1 == 1)
                    .collect();
                if compacted.evaluate(&cm).unwrap() {
                    let full = bve.reconstruction.extend(&map.expand(&cm));
                    assert!(
                        f.evaluate(&full).unwrap(),
                        "expand→extend model must satisfy the original"
                    );
                }
            }
        }
    }
}
