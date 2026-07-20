//! Sound XOR-gate extraction from CNF.
//!
//! This module is the second slice of the CDCL(XOR) path (see
//! `docs/research/05-algorithms/multiplier-sat-wall-and-algebraic-paths.md`,
//! path 2). The first slice landed the GF(2) Gaussian solver in [`crate::gf2`];
//! this slice recognizes sets of CNF clauses that *together* encode an XOR
//! constraint and exposes them as a populated [`Gf2System`] so the Gaussian
//! solver can derive implied units and equalities.
//!
//! Scope: extraction only. Wiring the recovered XOR constraints and their
//! derived facts into the SAT loop is a separate, later slice and is
//! intentionally not implemented here.
//!
//! # Soundness
//!
//! The whole point is that a recognized XOR constraint must be **logically
//! equivalent** to the clauses it was recovered from. A clause set that is not a
//! complete XOR gate is never recognized: false negatives are safe, false
//! positives would be a soundness bug. The recognition therefore demands an
//! *exact* match against the complete encoding (see [`extract_xors`]).
//!
//! # The encoding
//!
//! An XOR constraint `x_{i1} ⊕ x_{i2} ⊕ ... ⊕ x_{ik} = p` (`p ∈ {0, 1}`) over a
//! fixed set of `k` variables is logically equivalent to a specific set of
//! exactly `2^(k-1)` clauses over those `k` variables. The satisfying
//! assignments of the XOR are the `2^(k-1)` assignments whose popcount has
//! parity `p`; the *forbidden* assignments are the `2^(k-1)` of parity `1 - p`.
//! Each clause `(l_1 ∨ ... ∨ l_k)` rules out exactly one assignment: the one
//! that makes every literal false, i.e. `var_j = 1` iff `l_j` is negated. That
//! ruled-out assignment has popcount equal to the clause's negated-literal
//! count `n`, so its parity is `n mod 2`. For the clause to belong to the gate
//! it must forbid a parity-`(1 - p)` assignment, hence every gate clause shares
//! the same `n mod 2`, and `p = 1 - (n mod 2)`.
//!
//! Recognition therefore is: group candidate clauses by their (sorted,
//! repeat-free) variable set; for a set of size `k`, the group is an XOR gate
//! iff it contains exactly `2^(k-1)` distinct clauses whose forbidden
//! assignments are *exactly* the `2^(k-1)` assignments of one parity class. The
//! parity class fixes `p`. Anything short of an exact match recognizes nothing.

use crate::{CnfFormula, Gf2System};
use std::collections::BTreeMap;

/// Maximum XOR-gate width attempted, in variables.
///
/// A width-`k` gate is encoded by `2^(k-1)` clauses, so the work to confirm a
/// gate grows exponentially. Wider gates are rare in practice; `CryptoMiniSat`
/// caps the search the same way. Gates wider than this are simply not
/// recognized (a safe false negative).
const MAX_XOR_VARS: usize = 8;

/// Result of extracting XOR gates from a CNF formula.
#[derive(Debug, Clone)]
pub struct ExtractedXors {
    /// A GF(2) system containing one constraint per recognized XOR gate, sized
    /// to the formula's variable count. Empty when no gate was recognized.
    pub system: Gf2System,
    /// Number of XOR gates recognized (equal to `system.num_constraints()`).
    pub num_recognized: usize,
}

/// Recognizes complete XOR gates in `cnf` and returns them as a [`Gf2System`].
///
/// The scan groups clauses by their variable set and recognizes a group as an
/// XOR gate only when it is *exactly* the complete `2^(k-1)`-clause encoding of
/// some `x ⊕ ... = p` constraint (see the module docs). One constraint is added
/// per recognized gate; the recovered variable set is added in ascending index
/// order, and gates are emitted in ascending order of their variable sets, so
/// the output is deterministic. Recognizing zero gates yields an empty system.
///
/// Only gates of width `2..=MAX_XOR_VARS` are attempted. Clauses with a
/// repeated variable (e.g. `x ∨ ¬x ∨ y`) cannot be part of a clean gate and are
/// skipped during grouping.
#[must_use]
pub fn extract_xors(cnf: &CnfFormula) -> ExtractedXors {
    // Group clauses by their variable set. The key is the sorted, repeat-free
    // list of variable indices; the value collects each clause's "negated-mask"
    // — bit j set iff the j-th variable (in sorted order) appears negated. A
    // clause with a repeated variable is dropped (it cannot be a clean gate
    // clause). We use a BTreeMap so iteration over groups is in sorted variable
    // order, keeping the output deterministic without a later sort.
    let mut groups: BTreeMap<Vec<usize>, Vec<u32>> = BTreeMap::new();

    for clause in cnf.clauses() {
        let lits = clause;
        let k = lits.len();
        if !(2..=MAX_XOR_VARS).contains(&k) {
            continue;
        }
        // Collect (variable, negated) pairs, sorted by variable, rejecting any
        // clause whose variables are not all distinct.
        let mut pairs: Vec<(usize, bool)> = lits
            .iter()
            .map(|lit| (lit.var().index(), lit.is_negated()))
            .collect();
        pairs.sort_unstable_by_key(|&(var, _)| var);
        if pairs.windows(2).any(|w| w[0].0 == w[1].0) {
            // A variable repeats in the clause; not a clean gate clause.
            continue;
        }

        let vars: Vec<usize> = pairs.iter().map(|&(var, _)| var).collect();
        // Negated-mask over the sorted variable order.
        let mut mask = 0u32;
        for (bit, &(_, negated)) in pairs.iter().enumerate() {
            if negated {
                mask |= 1u32 << bit;
            }
        }
        groups.entry(vars).or_default().push(mask);
    }

    let mut system = Gf2System::new(cnf.variable_count());
    let mut num_recognized = 0usize;

    for (vars, masks) in &groups {
        if let Some(rhs) = recognize_gate(vars.len(), masks) {
            system.add_constraint(vars, rhs);
            num_recognized += 1;
        }
    }

    ExtractedXors {
        system,
        num_recognized,
    }
}

/// Decides whether the negated-masks of a `k`-variable clause group form a
/// complete XOR gate, returning the gate's right-hand-side parity `p` if so.
///
/// `masks` carries, for each clause in the group, the bitmask (over the `k`
/// sorted variable positions) of which literals are negated. A clause with
/// negated-mask `m` rules out the single assignment `var_j = bit_j(m)`, whose
/// popcount is `m.count_ones()`. The group is a complete gate for parity `p`
/// iff the masks are *exactly* the set of all `2^(k-1)` masks of one popcount
/// parity, each appearing once.
fn recognize_gate(k: usize, masks: &[u32]) -> Option<bool> {
    debug_assert!((2..=MAX_XOR_VARS).contains(&k));
    let expected = 1usize << (k - 1);
    if masks.len() != expected {
        // Wrong number of clauses (too few — a near-miss — or too many — an
        // extra clause in the group). Either way it cannot be the exact gate.
        return None;
    }

    // The full mask range over k variables is 0..2^k. Each mask in the group
    // must be in range, distinct, and share one popcount parity. We record the
    // parity from the first clause and require every clause to match it, then
    // confirm we covered *every* mask of that parity (no missing, no duplicate).
    let parity = (masks[0].count_ones() & 1) == 1;
    let full = 1u32 << k;
    let mut seen = vec![false; full as usize];
    for &mask in masks {
        if mask >= full {
            // A bit outside the k-variable range was set — impossible given how
            // masks are built, but check defensively rather than index OOB.
            return None;
        }
        if (mask.count_ones() & 1 == 1) != parity {
            // Mixed parity: not a single parity class, so not an XOR gate.
            return None;
        }
        if seen[mask as usize] {
            // Duplicate clause: cannot complete the parity class to 2^(k-1)
            // distinct masks.
            return None;
        }
        seen[mask as usize] = true;
    }

    // Confirm full coverage of the parity class: every mask of this parity is
    // present. (Count already equals 2^(k-1) and all are distinct of this
    // parity, so this is guaranteed; assert it as a soundness backstop.)
    for m in 0..full {
        if (m.count_ones() & 1 == 1) == parity {
            debug_assert!(seen[m as usize], "parity class not fully covered");
            if !seen[m as usize] {
                return None;
            }
        }
    }

    // A clause forbids a parity-`parity` assignment; the XOR's forbidden
    // assignments are those of parity `1 - p`, so `parity == 1 - p`, giving
    // `p = !parity`.
    Some(!parity)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CnfClause, CnfLit, CnfVar};

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
    /// A clause forbids an assignment of parity `1 - p`; the clause's negated
    /// literals are exactly the variables set to 1 in that forbidden assignment.
    /// So we enumerate every parity-`(1 - p)` assignment over `vars` and emit
    /// one clause per assignment with `literal_j` negated iff `var_j` is 1.
    fn xor_clauses(vars: &[usize], p: bool) -> Vec<Vec<(usize, bool)>> {
        let k = vars.len();
        let target_parity = !p; // forbidden assignments have parity 1 - p.
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

    /// Brute-force: returns every assignment over `vars` (as a popcount-indexed
    /// truth table value, `var_j` = bit j) that satisfies all `clauses` restricted
    /// to those vars. Used to confirm the recognized constraint matches the
    /// intended XOR exactly.
    fn clause_models(vars: &[usize], clauses: &[Vec<(usize, bool)>]) -> Vec<u32> {
        let k = vars.len();
        let mut models = Vec::new();
        for assign in 0u32..(1u32 << k) {
            let value = |v: usize| -> bool {
                let j = vars.iter().position(|&x| x == v).expect("var in set");
                (assign >> j) & 1 == 1
            };
            let all = clauses.iter().all(|c| {
                c.iter()
                    .any(|&(v, neg)| if neg { !value(v) } else { value(v) })
            });
            if all {
                models.push(assign);
            }
        }
        models
    }

    /// XOR truth table: assignments over `vars` with `⊕ x = p`, as a bit-packed
    /// mask matching `clause_models`' encoding (`var_j` = bit j).
    fn xor_models(vars: &[usize], p: bool) -> Vec<u32> {
        let k = vars.len();
        (0u32..(1u32 << k))
            .filter(|a| ((a.count_ones() & 1) == 1) == p)
            .collect()
    }

    #[test]
    fn round_trip_k2_parity_zero() {
        // x0 ⊕ x1 = 0.
        let f = formula(2, &xor_clauses(&[0, 1], false));
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 1);
        // x0 == x1, exposed by the GF(2) solver as an equality.
        match extracted.system.solve() {
            crate::Gf2Outcome::Sat(sol) => {
                assert_eq!(sol.implied_equalities(), &[(0, 1, false)]);
            }
            crate::Gf2Outcome::Unsat => panic!("gate system should be SAT"),
        }
    }

    #[test]
    fn round_trip_k2_parity_one() {
        // x0 ⊕ x1 = 1.
        let f = formula(2, &xor_clauses(&[0, 1], true));
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 1);
        match extracted.system.solve() {
            crate::Gf2Outcome::Sat(sol) => {
                assert_eq!(sol.implied_equalities(), &[(0, 1, true)]);
            }
            crate::Gf2Outcome::Unsat => panic!("gate system should be SAT"),
        }
    }

    #[test]
    fn round_trip_k3_parity_zero() {
        // x0 ⊕ x1 ⊕ x2 = 0 ⇒ 4 clauses.
        let clauses = xor_clauses(&[0, 1, 2], false);
        assert_eq!(clauses.len(), 4);
        let f = formula(3, &clauses);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 1);
        // Every satisfying assignment of the recovered system must satisfy the XOR.
        match extracted.system.solve() {
            crate::Gf2Outcome::Sat(sol) => {
                let xor = sol.value(0) ^ sol.value(1) ^ sol.value(2);
                assert!(!xor, "solution must satisfy x0 ⊕ x1 ⊕ x2 = 0");
            }
            crate::Gf2Outcome::Unsat => panic!("gate system should be SAT"),
        }
    }

    #[test]
    fn round_trip_k3_parity_one() {
        let clauses = xor_clauses(&[0, 1, 2], true);
        let f = formula(3, &clauses);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 1);
        match extracted.system.solve() {
            crate::Gf2Outcome::Sat(sol) => {
                let xor = sol.value(0) ^ sol.value(1) ^ sol.value(2);
                assert!(xor, "solution must satisfy x0 ⊕ x1 ⊕ x2 = 1");
            }
            crate::Gf2Outcome::Unsat => panic!("gate system should be SAT"),
        }
    }

    #[test]
    fn parity_matches_truth_table_k2_k3_k4() {
        // For each width and parity, the recognized gate's models (brute force
        // over the clauses) must equal exactly the XOR truth table.
        for k in 2usize..=4 {
            let vars: Vec<usize> = (0..k).collect();
            for &p in &[false, true] {
                let clauses = xor_clauses(&vars, p);
                let f = formula(k, &clauses);
                let extracted = extract_xors(&f);
                assert_eq!(
                    extracted.num_recognized, 1,
                    "k={k} p={p} should recognize one gate"
                );
                // The clauses are UNSAT exactly on assignments violating the XOR.
                let mut models = clause_models(&vars, &clauses);
                let mut expected = xor_models(&vars, p);
                models.sort_unstable();
                expected.sort_unstable();
                assert_eq!(models, expected, "clause models must equal XOR k={k} p={p}");
            }
        }
    }

    #[test]
    fn no_false_positive_missing_one_clause() {
        // Drop one clause of a k=3 gate ⇒ not recognized.
        let mut clauses = xor_clauses(&[0, 1, 2], false);
        clauses.pop();
        assert_eq!(clauses.len(), 3);
        let f = formula(3, &clauses);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 0);
    }

    #[test]
    fn no_false_positive_extra_clause_in_group() {
        // The complete k=3 even gate plus an extra clause over the same vars
        // (an odd-parity clause) ⇒ 5 clauses in the group, not 4 ⇒ not a gate.
        let mut clauses = xor_clauses(&[0, 1, 2], false);
        // Add the all-positive clause (x0 ∨ x1 ∨ x2), which is odd parity (0
        // negated literals → forbids 000, parity 0... actually it belongs to
        // the OTHER gate). Adding it makes 5 clauses over the same var set.
        clauses.push(vec![(0, false), (1, false), (2, false)]);
        assert_eq!(clauses.len(), 5);
        let f = formula(3, &clauses);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 0);
    }

    #[test]
    fn no_false_positive_duplicate_clause() {
        // Right count (4) but a duplicate ⇒ parity class not fully covered.
        let mut clauses = xor_clauses(&[0, 1, 2], false);
        clauses.pop();
        clauses.push(clauses[0].clone()); // duplicate the first
        assert_eq!(clauses.len(), 4);
        let f = formula(3, &clauses);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 0);
    }

    #[test]
    fn no_false_positive_mixed_parity() {
        // Four clauses over {0,1,2} but mixing both parity classes ⇒ not a gate.
        let even = xor_clauses(&[0, 1, 2], false); // even-parity clauses
        let odd = xor_clauses(&[0, 1, 2], true); // odd-parity clauses
        let clauses = vec![
            even[0].clone(),
            even[1].clone(),
            odd[0].clone(),
            odd[1].clone(),
        ];
        let f = formula(3, &clauses);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 0);
    }

    #[test]
    fn no_false_positive_plain_clauses() {
        // Ordinary non-XOR CNF ⇒ nothing recognized.
        let f = formula(
            4,
            &[
                vec![(0, false), (1, true)],
                vec![(1, false), (2, false), (3, true)],
                vec![(0, true)],
            ],
        );
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 0);
    }

    #[test]
    fn two_independent_gates_both_recognized() {
        // x0 ⊕ x1 = 1 and x2 ⊕ x3 ⊕ x4 = 0 over disjoint variables.
        let mut clauses = xor_clauses(&[0, 1], true);
        clauses.extend(xor_clauses(&[2, 3, 4], false));
        let f = formula(5, &clauses);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 2);
        // Confirm consistency: every model satisfies both XORs.
        match extracted.system.solve() {
            crate::Gf2Outcome::Sat(sol) => {
                assert!(sol.value(0) ^ sol.value(1));
                assert!(!(sol.value(2) ^ sol.value(3) ^ sol.value(4)));
            }
            crate::Gf2Outcome::Unsat => panic!("two independent gates should be SAT"),
        }
    }

    #[test]
    fn near_miss_with_unrelated_clause_does_not_block_gate() {
        // A complete k=3 gate over {0,1,2} plus an unrelated clause over {3,4}.
        // The unrelated clause is a different variable group, so it neither
        // joins nor blocks the gate.
        let mut clauses = xor_clauses(&[0, 1, 2], false);
        clauses.push(vec![(3, false), (4, true)]);
        let f = formula(5, &clauses);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 1);
    }

    #[test]
    fn clause_with_repeated_variable_is_skipped() {
        // A "clause" with a repeated variable can't be a clean gate clause; it
        // is dropped during grouping, so the otherwise-complete gate is broken.
        let mut clauses = xor_clauses(&[0, 1, 2], false);
        // Replace one clause with one having a repeated variable over {0,1,2}.
        clauses[0] = vec![(0, false), (0, true), (1, false)];
        let f = formula(3, &clauses);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 0);
    }

    #[test]
    fn empty_formula_recognizes_nothing() {
        let f = CnfFormula::new(4);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 0);
        assert_eq!(extracted.system.num_constraints(), 0);
        assert_eq!(extracted.system.num_vars(), 4);
    }

    #[test]
    fn unit_clauses_are_not_gates() {
        // Single-literal clauses (k=1) are below the k>=2 threshold.
        let f = formula(2, &[vec![(0, false)], vec![(1, true)]]);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 0);
    }

    #[test]
    fn determinism_constraints_in_sorted_order() {
        // Two gates added out of natural order; constraints come back grouped by
        // sorted variable set. Build gate over {2,3} after gate over {0,1}.
        let mut clauses = xor_clauses(&[2, 3], false);
        clauses.extend(xor_clauses(&[0, 1], true));
        let f = formula(4, &clauses);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 2);
        // Running extraction again must yield an identical system shape.
        let again = extract_xors(&f);
        assert_eq!(again.num_recognized, extracted.num_recognized);
        assert_eq!(
            again.system.num_constraints(),
            extracted.system.num_constraints()
        );
    }

    #[test]
    fn k4_round_trip() {
        // A wider gate to exercise the 2^(k-1) = 8 clause case.
        let clauses = xor_clauses(&[0, 1, 2, 3], true);
        assert_eq!(clauses.len(), 8);
        let f = formula(4, &clauses);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 1);
        match extracted.system.solve() {
            crate::Gf2Outcome::Sat(sol) => {
                assert!(sol.value(0) ^ sol.value(1) ^ sol.value(2) ^ sol.value(3));
            }
            crate::Gf2Outcome::Unsat => panic!("k4 gate should be SAT"),
        }
    }

    #[test]
    fn gate_wider_than_cap_not_recognized() {
        // A complete gate of width MAX_XOR_VARS + 1: every clause exceeds the
        // per-clause width cap, so all are skipped during grouping.
        let vars: Vec<usize> = (0..=MAX_XOR_VARS).collect();
        let clauses = xor_clauses(&vars, false);
        let f = formula(MAX_XOR_VARS + 1, &clauses);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 0);
    }
}
