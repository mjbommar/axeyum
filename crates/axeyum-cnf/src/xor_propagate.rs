//! Sound XOR-derived unit propagation as a pure CNF preprocessing pass.
//!
//! This module is the third slice of the CDCL(XOR) path (see
//! `docs/research/05-algorithms/multiplier-sat-wall-and-algebraic-paths.md`,
//! path 2). The first slice landed the GF(2) Gaussian solver in [`crate::gf2`];
//! the second recognized XOR gates out of CNF in [`crate::xor_extract`]. This
//! slice **composes** them into a sound preprocessing pass: recover the XOR
//! subsystem entailed by the formula, solve it over GF(2), and either report the
//! whole formula UNSAT (the XOR subsystem alone is contradictory) or return the
//! formula augmented with the XOR-entailed unit clauses.
//!
//! It follows the same pure-function idiom as [`crate::simplify`] and
//! [`crate::eliminate_variables`]: it takes `&CnfFormula`, performs no mutation
//! of the input, and returns a fresh result.
//!
//! Scope: this slice does not wire the pass into the live solve/preprocess
//! pipeline — that is a deliberately deferred next slice. It also applies only
//! the implied *units*; the implied *equalities* (which would drive
//! substitution / variable merging) are intentionally NOT applied here, since
//! that is a later refinement. The recovered `xors_recognized` count is taken
//! straight from extraction.
//!
//! # Soundness
//!
//! The contract is **logical equivalence**: a `Propagated` result has the same
//! variable count and exactly the same set of satisfying assignments as the
//! input, and an `Unsat` result is reported only when the input genuinely has no
//! satisfying assignment. The argument has two halves.
//!
//! * **Entailment of the XOR subsystem.** Each gate recovered by
//!   [`extract_xors`] is *logically equivalent* to a subset of the formula's
//!   clauses (extraction demands an exact match against the complete encoding;
//!   false positives are impossible). So the formula entails every recovered XOR
//!   constraint, hence entails their conjunction — the whole [`Gf2System`].
//!
//! * **`Unsat` is sound.** If that XOR subsystem is itself contradictory
//!   ([`Gf2Outcome::Unsat`]), then since the formula entails the subsystem, the
//!   formula entails a contradiction and is therefore UNSAT.
//!
//! * **Adding units preserves the model set.** When the subsystem is SAT, every
//!   `(var, value)` in [`Gf2Solution::implied_units`] is *entailed* by the
//!   subsystem (it is a fully reduced single-variable row), hence entailed by
//!   the formula. Adding an entailed clause cannot remove any model (every model
//!   of the formula already satisfies it) and obviously cannot add one (it is a
//!   strictly-more clauses formula). The variable count is unchanged. So the
//!   output is logically equivalent to the input, and no model reconstruction is
//!   needed: a model of the output is a model of the input and vice versa.

use crate::{CnfClause, CnfFormula, CnfLit, CnfVar, Gf2Outcome, extract_xors};

/// Statistics from an [`xor_propagate`] pass.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct XorPropagateStats {
    /// Number of XOR gates recognized in the formula (from extraction).
    pub xors_recognized: usize,
    /// Number of entailed unit clauses added to the formula.
    pub units_added: usize,
    /// Number of implied two-variable equalities the GF(2) solve exposes but this
    /// pass does *not* apply (the substitution slice). Surfaced as a measurement
    /// signal: it tells whether equality substitution is worth building on a given
    /// corpus before any reconstruction machinery is written.
    pub equalities_available: usize,
}

/// Outcome of an [`xor_propagate`] pass.
#[derive(Debug, Clone)]
pub enum XorPropagation {
    /// The XOR subsystem entailed by the formula is itself contradictory, so the
    /// whole formula is UNSAT.
    Unsat,
    /// The formula augmented with entailed unit clauses. This is **logically
    /// equivalent** to the input: same variable count, same satisfying
    /// assignments.
    Propagated {
        /// The augmented formula.
        formula: CnfFormula,
        /// Pass statistics.
        stats: XorPropagateStats,
    },
}

/// Propagates XOR-entailed units into `formula` as a sound preprocessing pass.
///
/// Recognizes the XOR gates in `formula` (see [`extract_xors`]), solves the
/// recovered GF(2) subsystem, and either:
///
/// * returns [`XorPropagation::Unsat`] when that subsystem is contradictory —
///   sound because the formula entails the whole subsystem; or
/// * returns [`XorPropagation::Propagated`] with the formula plus one unit
///   clause per [`Gf2Solution::implied_units`](crate::Gf2Solution::implied_units)
///   entry, each of which is entailed by the formula, so the model set is
///   preserved exactly.
///
/// Only implied *units* are applied; implied *equalities* are left for a later
/// substitution slice. The variable count is unchanged, so no model
/// reconstruction is required. The output is deterministic: extraction emits
/// gates in sorted order and units are appended in the sorted order
/// [`Gf2Solution::implied_units`](crate::Gf2Solution::implied_units) guarantees.
///
/// # Panics
///
/// Does not panic in practice: every implied-unit variable comes from the GF(2)
/// system, which is sized to `formula`'s variable count, so the variable index
/// always fits and the unit clause is always over an in-range variable.
#[must_use]
pub fn xor_propagate(formula: &CnfFormula) -> XorPropagation {
    let ex = extract_xors(formula);
    let xors_recognized = ex.num_recognized;

    match ex.system.solve() {
        Gf2Outcome::Unsat => XorPropagation::Unsat,
        Gf2Outcome::Sat(sol) => {
            let mut out = formula.clone();
            let mut units_added = 0usize;
            let equalities_available = sol.implied_equalities().len();

            for &(var, value) in sol.implied_units() {
                // `var` is a variable of the original system, which is sized to
                // the formula's variable count, so this construction and the
                // subsequent `add_clause` are infallible.
                let cnf_var = CnfVar::new(var).expect("xor-system var fits the formula");
                let lit = if value {
                    CnfLit::positive(cnf_var)
                } else {
                    CnfLit::positive(cnf_var).negated()
                };
                out.add_clause(CnfClause::new(vec![lit]))
                    .expect("unit clause over an in-range variable");
                units_added += 1;
            }

            XorPropagation::Propagated {
                formula: out,
                stats: XorPropagateStats {
                    xors_recognized,
                    units_added,
                    equalities_available,
                },
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CnfClause, CnfFormula, CnfLit, CnfVar};

    /// Builds a clause from `(var_index, negated)` pairs.
    fn clause(lits: &[(usize, bool)]) -> CnfClause {
        let lits = lits
            .iter()
            .map(|&(v, neg)| {
                let lit = CnfLit::positive(CnfVar::new(v).expect("var fits u32"));
                if neg { lit.negated() } else { lit }
            })
            .collect();
        CnfClause::new(lits)
    }

    fn formula(num_vars: usize, clauses: &[Vec<(usize, bool)>]) -> CnfFormula {
        let mut f = CnfFormula::new(num_vars);
        for c in clauses {
            f.add_clause(clause(c)).expect("valid clause");
        }
        f
    }

    /// Generates the complete clause set encoding `(⊕ of `vars`) = p`.
    ///
    /// Mirrors `xor_extract`'s own test helper so extraction actually fires:
    /// a clause forbids a parity-`(1 - p)` assignment, with `literal_j` negated
    /// iff `var_j` is 1 in that forbidden assignment.
    fn xor_clauses(vars: &[usize], p: bool) -> Vec<Vec<(usize, bool)>> {
        let k = vars.len();
        let target_parity = !p;
        let mut clauses = Vec::new();
        for assign in 0u32..(1u32 << k) {
            let parity = (assign.count_ones() & 1) == 1;
            if parity != target_parity {
                continue;
            }
            let lits: Vec<(usize, bool)> = vars
                .iter()
                .enumerate()
                .map(|(j, &v)| (v, (assign >> j) & 1 == 1))
                .collect();
            clauses.push(lits);
        }
        clauses
    }

    /// Brute-force every assignment over `0..n` and return those that satisfy
    /// every clause of `f`, as the set of bit-packed assignments (`var_j` = bit j).
    fn models(f: &CnfFormula) -> Vec<u32> {
        let n = f.variable_count();
        assert!(n <= 16, "brute force only intended for small formulas");
        let mut out = Vec::new();
        for assign in 0u32..(1u32 << n) {
            let values: Vec<bool> = (0..n).map(|j| (assign >> j) & 1 == 1).collect();
            if f.evaluate(&values).expect("assignment length matches") {
                out.push(assign);
            }
        }
        out
    }

    /// Convenience: the `Propagated` payload, panicking on `Unsat`.
    fn propagated(f: &CnfFormula) -> (CnfFormula, XorPropagateStats) {
        match xor_propagate(f) {
            XorPropagation::Propagated { formula, stats } => (formula, stats),
            XorPropagation::Unsat => panic!("expected Propagated, got Unsat"),
        }
    }

    #[test]
    fn model_set_preserved_with_forced_units() {
        // x0 = 1 (a k=1 fact via two gates) — build something the GF(2) solver
        // forces a unit from: x0 ⊕ x1 = 1 AND x1 = ... is not a gate (k=1), so
        // instead force a unit via two width-2 gates that pin both variables.
        // x0 ⊕ x1 = 1 and x0 ⊕ x1 ⊕ x2 = 0 give x2 = 1 (a forced unit).
        let mut clauses = xor_clauses(&[0, 1], true);
        clauses.extend(xor_clauses(&[0, 1, 2], false));
        let f = formula(3, &clauses);

        let (out, stats) = propagated(&f);
        assert!(stats.units_added > 0, "expected at least one forced unit");
        assert_eq!(stats.xors_recognized, 2);

        // Logical equivalence: identical model sets.
        let mut before = models(&f);
        let mut after = models(&out);
        before.sort_unstable();
        after.sort_unstable();
        assert_eq!(before, after, "model set must be preserved");
        // The forced unit really did add a clause not present before.
        assert!(out.clauses().len() > f.clauses().len());
    }

    #[test]
    fn no_xor_structure_is_a_noop() {
        // Ordinary non-XOR CNF: nothing recognized, nothing added, model set
        // identical (the output is clause-for-clause the input).
        let f = formula(
            4,
            &[
                vec![(0, false), (1, true)],
                vec![(1, false), (2, false), (3, true)],
                vec![(0, true)],
            ],
        );
        let (out, stats) = propagated(&f);
        assert_eq!(stats.xors_recognized, 0);
        assert_eq!(stats.units_added, 0);

        let mut before = models(&f);
        let mut after = models(&out);
        before.sort_unstable();
        after.sort_unstable();
        assert_eq!(before, after);
        // No-op: output is identical to input.
        assert_eq!(out, f);
    }

    #[test]
    fn mixed_xor_and_ordinary_clauses_preserve_model_set() {
        // Two XOR gates plus ordinary clauses over the same variables. The
        // ordinary clauses constrain the models further but must not perturb the
        // logical-equivalence guarantee of the pass.
        let mut clauses = xor_clauses(&[0, 1], true); // x0 ⊕ x1 = 1
        clauses.extend(xor_clauses(&[1, 2, 3], false)); // x1 ⊕ x2 ⊕ x3 = 0
        clauses.push(vec![(0, false), (3, false)]); // x0 ∨ x3
        clauses.push(vec![(2, true)]); // ¬x2
        let f = formula(4, &clauses);

        let (out, stats) = propagated(&f);
        assert_eq!(stats.xors_recognized, 2);

        let mut before = models(&f);
        let mut after = models(&out);
        before.sort_unstable();
        after.sort_unstable();
        assert_eq!(before, after, "model set must be preserved");
    }

    #[test]
    fn contradictory_xor_subsystem_is_unsat_and_truly_unsat() {
        // Three width-2 gates over DISTINCT variable sets (so each is recognized
        // individually) that are jointly contradictory:
        //   x0 ⊕ x1 = 0, x1 ⊕ x2 = 0, x0 ⊕ x2 = 1.
        // Summing the three rows: (x0⊕x1)⊕(x1⊕x2)⊕(x0⊕x2) = 0 on the left, but
        // 0 ⊕ 0 ⊕ 1 = 1 on the right ⇒ the inconsistent row 0 = 1.
        let mut clauses = xor_clauses(&[0, 1], false);
        clauses.extend(xor_clauses(&[1, 2], false));
        clauses.extend(xor_clauses(&[0, 2], true));
        let f = formula(3, &clauses);

        // Guard: extraction really did recognize all three gates (else the
        // "Unsat" below would be vacuous).
        assert_eq!(extract_xors(&f).num_recognized, 3);

        match xor_propagate(&f) {
            XorPropagation::Unsat => {}
            XorPropagation::Propagated { .. } => panic!("expected Unsat"),
        }
        // Brute force confirms the INPUT formula has zero satisfying assignments.
        assert!(models(&f).is_empty(), "input must truly be UNSAT");
    }

    #[test]
    fn satisfiable_formula_with_xor_is_never_reported_unsat() {
        // A consistent XOR gate plus extra clauses: must be Propagated, not Unsat.
        let mut clauses = xor_clauses(&[0, 1, 2], false);
        clauses.push(vec![(0, false), (1, false)]);
        let f = formula(3, &clauses);
        assert!(!models(&f).is_empty(), "guard: input is satisfiable");

        match xor_propagate(&f) {
            XorPropagation::Propagated { formula: out, .. } => {
                let mut before = models(&f);
                let mut after = models(&out);
                before.sort_unstable();
                after.sort_unstable();
                assert_eq!(before, after);
            }
            XorPropagation::Unsat => panic!("satisfiable formula must not be Unsat"),
        }
    }

    #[test]
    fn satisfiable_formula_without_xor_is_never_reported_unsat() {
        // Plain satisfiable CNF with no XOR structure: must be Propagated.
        let f = formula(3, &[vec![(0, false), (1, false)], vec![(2, true)]]);
        assert!(!models(&f).is_empty(), "guard: input is satisfiable");
        match xor_propagate(&f) {
            XorPropagation::Propagated { stats, .. } => {
                assert_eq!(stats.xors_recognized, 0);
                assert_eq!(stats.units_added, 0);
            }
            XorPropagation::Unsat => panic!("satisfiable formula must not be Unsat"),
        }
    }

    #[test]
    fn empty_formula_is_a_noop_propagation() {
        let f = CnfFormula::new(4);
        let (out, stats) = propagated(&f);
        assert_eq!(stats.xors_recognized, 0);
        assert_eq!(stats.units_added, 0);
        assert_eq!(out, f);
    }

    #[test]
    fn determinism_identical_output_on_repeated_runs() {
        let mut clauses = xor_clauses(&[0, 1], true);
        clauses.extend(xor_clauses(&[0, 1, 2], false));
        let f = formula(3, &clauses);

        let (out1, stats1) = propagated(&f);
        let (out2, stats2) = propagated(&f);
        // Identical clause order and counts across runs.
        assert_eq!(out1, out2);
        assert_eq!(stats1, stats2);
    }

    #[test]
    fn added_units_are_entailed_by_every_input_model() {
        // The forcing case: confirm each model of the INPUT already satisfies the
        // added units, i.e. the units are entailed (covered by model-set equality
        // too, but checked directly here).
        let mut clauses = xor_clauses(&[0, 1], true);
        clauses.extend(xor_clauses(&[0, 1, 2], false));
        let f = formula(3, &clauses);

        let (out, stats) = propagated(&f);
        assert!(stats.units_added > 0);

        // Every newly added unit clause is satisfied by every model of the input.
        let added = &out.clauses()[f.clauses().len()..];
        assert_eq!(added.len(), stats.units_added);
        for &assign in &models(&f) {
            let values: Vec<bool> = (0..f.variable_count())
                .map(|j| (assign >> j) & 1 == 1)
                .collect();
            for unit in added {
                assert!(
                    unit.evaluate(&values),
                    "added unit {unit:?} not entailed by input model {assign:b}"
                );
            }
        }
    }
}
