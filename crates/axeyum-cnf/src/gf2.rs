//! GF(2) linear (XOR) constraint system solver via Gaussian elimination.
//!
//! This module is the standalone algebraic core that CDCL(XOR) builds on (see
//! `docs/research/05-algorithms/multiplier-sat-wall-and-algebraic-paths.md`,
//! path 2). It models a system of XOR constraints over Boolean variables
//! `0..num_vars`, where each constraint is the XOR of a set of variables equal
//! to a parity bit, e.g. `x0 ⊕ x2 ⊕ x5 = 1`.
//!
//! Solving is exact: [`Gf2System::solve`] row-reduces the system over GF(2) to
//! reduced row-echelon form and reports either [`Gf2Outcome::Unsat`] (an
//! inconsistent `0 = 1` row) or [`Gf2Outcome::Sat`] with a concrete satisfying
//! assignment plus the *derived facts* — forced units and variable equalities —
//! that make this useful for SAT inprocessing in a later slice.
//!
//! Scope: this is the solver over **explicit** XOR constraints only. Extracting
//! XOR constraints out of CNF and wiring the derived facts into the SAT loop are
//! separate, later slices and are intentionally not implemented here.
//!
//! Determinism: columns and rows are processed in index order, and the returned
//! units and equalities are sorted by variable index. No hash-map iteration
//! order influences any output.

/// A system of XOR (GF(2) linear) constraints over Boolean variables `0..n`.
///
/// Each constraint is the XOR of a set of variables equal to a right-hand-side
/// parity bit. Variables that appear an even number of times in a single
/// constraint cancel (`x ⊕ x = 0`).
#[derive(Debug, Clone)]
pub struct Gf2System {
    num_vars: usize,
    /// Number of `u64` words needed to hold one bit per variable.
    words: usize,
    /// One bitset row per constraint: bit `v` set ⇒ variable `v` participates.
    rows: Vec<Vec<u64>>,
    /// Right-hand-side parity bit, parallel to `rows`.
    rhs: Vec<bool>,
}

impl Gf2System {
    /// Creates an empty system over `num_vars` variables (`0..num_vars`).
    #[must_use]
    pub fn new(num_vars: usize) -> Self {
        let words = num_vars.div_ceil(64);
        Self {
            num_vars,
            words,
            rows: Vec::new(),
            rhs: Vec::new(),
        }
    }

    /// Number of variables in this system.
    #[must_use]
    pub fn num_vars(&self) -> usize {
        self.num_vars
    }

    /// Number of constraints added so far.
    #[must_use]
    pub fn num_constraints(&self) -> usize {
        self.rows.len()
    }

    /// Returns the added constraints as `(variables, rhs)` pairs.
    ///
    /// Each pair is the XOR-folded variable set of a single added constraint
    /// (duplicate variables already cancelled by parity during
    /// [`Gf2System::add_constraint`]) together with its right-hand-side parity
    /// bit. Variables within a pair are in ascending index order, and the pairs
    /// are returned in the order the constraints were added, so the output is
    /// deterministic.
    ///
    /// This is the `(Vec<usize>, bool)` shape consumed by
    /// [`crate::xor_implications`], letting a search recover the per-constraint
    /// XOR system from an [`crate::extract_xors`] result.
    #[must_use]
    pub fn constraints(&self) -> Vec<(Vec<usize>, bool)> {
        self.rows
            .iter()
            .zip(&self.rhs)
            .map(|(row, &rhs)| (set_bits(row, self.num_vars), rhs))
            .collect()
    }

    /// Adds the constraint `(⊕ of `vars`) = rhs`.
    ///
    /// Variables are XOR-folded into the row, so a variable listed an even
    /// number of times cancels out (`x ⊕ x = 0`).
    ///
    /// # Panics
    ///
    /// Panics if any variable index is `>= num_vars`.
    pub fn add_constraint(&mut self, vars: &[usize], rhs: bool) {
        let mut row = vec![0u64; self.words];
        for &var in vars {
            assert!(
                var < self.num_vars,
                "variable index {var} out of range for system of {} vars",
                self.num_vars
            );
            // XOR-toggle the bit so duplicates cancel by parity.
            row[var / 64] ^= 1u64 << (var % 64);
        }
        self.rows.push(row);
        self.rhs.push(rhs);
    }

    /// Solves the system via Gaussian elimination over GF(2).
    ///
    /// Returns [`Gf2Outcome::Unsat`] when the reduced system contains an
    /// inconsistent `0 = 1` row, otherwise [`Gf2Outcome::Sat`] carrying a
    /// satisfying assignment and the derived units/equalities.
    #[must_use]
    pub fn solve(&self) -> Gf2Outcome {
        let words = self.words;
        // Working copy of the augmented matrix.
        let mut rows = self.rows.clone();
        let mut rhs = self.rhs.clone();

        // Reduce to reduced row-echelon form, processing columns in index order.
        // `pivot_row` is the next free row to receive a pivot.
        let mut pivot_row = 0usize;
        for col in 0..self.num_vars {
            // Find a row at or below `pivot_row` whose pivot column is set.
            let Some(sel) = (pivot_row..rows.len()).find(|&r| bit_is_set(&rows[r], col)) else {
                continue;
            };
            rows.swap(pivot_row, sel);
            rhs.swap(pivot_row, sel);
            // Snapshot the pivot row/rhs so the elimination loop can mutate
            // other rows without aliasing the pivot.
            let pivot = rows[pivot_row].clone();
            let pivot_rhs = rhs[pivot_row];
            // Eliminate this column from every other row.
            for r in 0..rows.len() {
                if r != pivot_row && bit_is_set(&rows[r], col) {
                    xor_into(&mut rows[r], &pivot, words);
                    rhs[r] ^= pivot_rhs;
                }
            }
            pivot_row += 1;
            if pivot_row == rows.len() {
                break;
            }
        }

        // Inconsistency check: an all-zero variable row with rhs == true (0 = 1).
        for (r, row) in rows.iter().enumerate() {
            if rhs[r] && row_is_zero(row) {
                return Gf2Outcome::Unsat;
            }
        }

        // Build the satisfying assignment and the derived facts from the
        // reduced rows. A row is now either all-zero (dropped) or has a unique
        // pivot variable (its lowest set bit) thanks to RREF.
        let mut values = vec![false; self.num_vars];
        let mut units: Vec<(usize, bool)> = Vec::new();
        let mut equalities: Vec<(usize, usize, bool)> = Vec::new();

        for (r, row) in rows.iter().enumerate() {
            let set: Vec<usize> = set_bits(row, self.num_vars);
            match set.as_slice() {
                [] => {
                    // 0 = 0 row: already verified consistent above; drop it.
                }
                [only] => {
                    // Single-variable row: x_only = rhs (a forced unit).
                    values[*only] = rhs[r];
                    units.push((*only, rhs[r]));
                }
                [first, ..] => {
                    // Pivot variable is the lowest-index variable in the row;
                    // free variables default to false, so the pivot equals rhs.
                    values[*first] = rhs[r];
                    if let [xi, xj] = set.as_slice() {
                        // Exactly two variables: xi ⊕ xj = c is an equality.
                        equalities.push((*xi, *xj, rhs[r]));
                    }
                }
            }
        }

        units.sort_unstable_by_key(|&(var, _)| var);
        equalities.sort_unstable_by_key(|&(xi, xj, _)| (xi, xj));

        Gf2Outcome::Sat(Gf2Solution {
            values,
            units,
            equalities,
        })
    }

    /// Returns the subset of original constraint indices whose GF(2)-sum is the
    /// inconsistent row `0 = 1`, if and only if the system is unsatisfiable by
    /// pure Gaussian elimination (no branching).
    ///
    /// This is the **conflict-reason subset** the per-query DRAT certificate
    /// route ([`crate::xor_gauss_drat_refutation`]) consumes: the few original
    /// constraints the elimination actually summed to reach `0 = 1`. It returns
    /// `Some(subset)` exactly when [`Gf2System::solve`] returns
    /// [`Gf2Outcome::Unsat`], and `None` for a satisfiable system.
    ///
    /// The reduction is the same column-order Gaussian elimination
    /// [`Gf2System::solve`] runs, additionally tracking, per working row, the set
    /// of original-row indices summed into it (a provenance bitset). When a
    /// reduced row becomes all-zero in the variable columns with parity `1`, its
    /// provenance is exactly a subset summing to `0 = 1`. The returned indices
    /// are sorted ascending and the GF(2)-sum of the indexed
    /// [`Gf2System::constraints`] is verified to be `0 = 1` before returning, so
    /// the result is always a genuine refutation subset (or `None`).
    ///
    /// Determinism: the same column order and the first inconsistent row found
    /// give a stable subset for a given system.
    #[must_use]
    pub fn unsat_reason_subset(&self) -> Option<Vec<usize>> {
        let words = self.words;
        let mut rows = self.rows.clone();
        let mut rhs = self.rhs.clone();
        // Provenance: row `r` started as the XOR of original constraints in
        // `prov[r]` (a bitset over constraint indices). Initially each row is
        // itself.
        let prov_words = self.rows.len().div_ceil(64).max(1);
        let mut prov: Vec<Vec<u64>> = (0..self.rows.len())
            .map(|r| {
                let mut p = vec![0u64; prov_words];
                p[r / 64] |= 1u64 << (r % 64);
                p
            })
            .collect();

        let mut pivot_row = 0usize;
        for col in 0..self.num_vars {
            let Some(sel) = (pivot_row..rows.len()).find(|&r| bit_is_set(&rows[r], col)) else {
                continue;
            };
            rows.swap(pivot_row, sel);
            rhs.swap(pivot_row, sel);
            prov.swap(pivot_row, sel);
            let pivot = rows[pivot_row].clone();
            let pivot_rhs = rhs[pivot_row];
            let pivot_prov = prov[pivot_row].clone();
            for r in 0..rows.len() {
                if r != pivot_row && bit_is_set(&rows[r], col) {
                    xor_into(&mut rows[r], &pivot, words);
                    rhs[r] ^= pivot_rhs;
                    xor_into(&mut prov[r], &pivot_prov, prov_words);
                }
            }
            pivot_row += 1;
            if pivot_row == rows.len() {
                break;
            }
        }

        // First inconsistent `0 = 1` row: read its provenance subset.
        for (r, row) in rows.iter().enumerate() {
            if rhs[r] && row_is_zero(row) {
                let subset = set_bits(&prov[r], self.rows.len());
                debug_assert!(
                    self.subset_sums_to_zero_eq_one(&subset),
                    "unsat_reason_subset produced a subset not summing to 0 = 1"
                );
                if self.subset_sums_to_zero_eq_one(&subset) {
                    return Some(subset);
                }
                return None;
            }
        }
        None
    }

    /// Verifies the GF(2)-sum of the constraints at `subset` is the inconsistent
    /// row `0 = 1` (empty variable support, parity `1`). The soundness check on
    /// the reason subset before it is returned.
    fn subset_sums_to_zero_eq_one(&self, subset: &[usize]) -> bool {
        if subset.is_empty() {
            return false;
        }
        let mut acc = vec![0u64; self.words];
        let mut parity = false;
        for &idx in subset {
            let Some(row) = self.rows.get(idx) else {
                return false;
            };
            xor_into(&mut acc, row, self.words);
            parity ^= self.rhs[idx];
        }
        row_is_zero(&acc) && parity
    }
}

/// Outcome of solving a [`Gf2System`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Gf2Outcome {
    /// The system is inconsistent (a `0 = 1` row).
    Unsat,
    /// The system is satisfiable; carries an assignment and derived facts.
    Sat(Gf2Solution),
}

/// A satisfying assignment plus the facts derived from the reduced system.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Gf2Solution {
    /// Concrete value per variable; free variables are `false`.
    values: Vec<bool>,
    /// Variables forced to a fixed value, sorted by variable index.
    units: Vec<(usize, bool)>,
    /// Reduced rows of the form `xi ⊕ xj = c`, sorted by `(xi, xj)`.
    equalities: Vec<(usize, usize, bool)>,
}

impl Gf2Solution {
    /// Value assigned to `var` (free variables are `false`).
    ///
    /// # Panics
    ///
    /// Panics if `var` is outside the system's variable range.
    #[must_use]
    pub fn value(&self, var: usize) -> bool {
        self.values[var]
    }

    /// All variable values in index order; free variables are `false`.
    #[must_use]
    pub fn values(&self) -> &[bool] {
        &self.values
    }

    /// Variables forced to a fixed value by the reduced system (a fully
    /// reduced row with a single variable), sorted by variable index.
    ///
    /// Each `(var, value)` means the reduced system implies `x_var = value`.
    #[must_use]
    pub fn implied_units(&self) -> &[(usize, bool)] {
        &self.units
    }

    /// Reduced rows with exactly two variables, sorted by `(xi, xj)`.
    ///
    /// Each `(xi, xj, c)` means `xi ⊕ xj = c`, i.e. `xi == xj` when `c` is
    /// `false` and `xi == !xj` when `c` is `true`.
    #[must_use]
    pub fn implied_equalities(&self) -> &[(usize, usize, bool)] {
        &self.equalities
    }
}

/// Returns `true` if bit `col` is set in `row`.
fn bit_is_set(row: &[u64], col: usize) -> bool {
    (row[col / 64] >> (col % 64)) & 1 == 1
}

/// XORs `src` into `dst` word by word.
fn xor_into(dst: &mut [u64], src: &[u64], words: usize) {
    for i in 0..words {
        dst[i] ^= src[i];
    }
}

/// Returns `true` if no bit is set in `row`.
fn row_is_zero(row: &[u64]) -> bool {
    row.iter().all(|&w| w == 0)
}

/// Returns the indices of the set bits in `row`, in ascending order, limited to
/// `num_vars` (so padding bits above the variable range are never reported).
fn set_bits(row: &[u64], num_vars: usize) -> Vec<usize> {
    let mut out = Vec::new();
    for (w, &word) in row.iter().enumerate() {
        let mut bits = word;
        while bits != 0 {
            let tz = bits.trailing_zeros() as usize;
            let var = w * 64 + tz;
            if var < num_vars {
                out.push(var);
            }
            bits &= bits - 1;
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A constraint as a variable set plus its rhs parity bit.
    type Constraint = (Vec<usize>, bool);

    /// Evaluates one input constraint (variable set + rhs) under a solution:
    /// the XOR of the listed variable values must equal `rhs`.
    fn constraint_holds(sol: &Gf2Solution, vars: &[usize], rhs: bool) -> bool {
        // Fold by parity so duplicate variables cancel, matching `add_constraint`.
        let mut acc = false;
        for &v in vars {
            acc ^= sol.value(v);
        }
        acc == rhs
    }

    /// Asserts a solution satisfies every constraint in `constraints` — the
    /// backbone invariant for every SAT case.
    fn assert_satisfies_all(sol: &Gf2Solution, constraints: &[Constraint]) {
        for (vars, rhs) in constraints {
            assert!(
                constraint_holds(sol, vars, *rhs),
                "assignment violates constraint {vars:?} = {rhs}"
            );
        }
    }

    fn build(num_vars: usize, constraints: &[Constraint]) -> Gf2System {
        let mut sys = Gf2System::new(num_vars);
        for (vars, rhs) in constraints {
            sys.add_constraint(vars, *rhs);
        }
        sys
    }

    fn solve_sat(num_vars: usize, constraints: &[Constraint]) -> Gf2Solution {
        match build(num_vars, constraints).solve() {
            Gf2Outcome::Sat(sol) => sol,
            Gf2Outcome::Unsat => panic!("expected SAT for {constraints:?}"),
        }
    }

    #[test]
    fn sat_unique_solution() {
        // x0 ⊕ x1 = 1, x1 = 1  ⇒  x1 = 1, x0 = 0.
        let constraints = vec![(vec![0, 1], true), (vec![1], true)];
        let sol = solve_sat(2, &constraints);
        assert!(!sol.value(0));
        assert!(sol.value(1));
        assert_satisfies_all(&sol, &constraints);
    }

    #[test]
    fn unsat_direct_contradiction() {
        // x0 ⊕ x1 = 0 and x0 ⊕ x1 = 1 cannot both hold.
        let sys = build(2, &[(vec![0, 1], false), (vec![0, 1], true)]);
        assert_eq!(sys.solve(), Gf2Outcome::Unsat);
    }

    #[test]
    fn larger_consistent_system_satisfies_all() {
        // 5 vars, several constraints, consistent.
        let constraints = vec![
            (vec![0, 1, 2], true),
            (vec![1, 3], false),
            (vec![2, 4], true),
            (vec![0, 4], false),
        ];
        let sol = solve_sat(5, &constraints);
        assert_satisfies_all(&sol, &constraints);
    }

    #[test]
    fn fixed_random_systems_satisfy_all() {
        // Hand-listed, deterministic systems (no RNG). Each is consistent.
        let systems: Vec<(usize, Vec<Constraint>)> = vec![
            (
                6,
                vec![
                    (vec![0, 1], true),
                    (vec![1, 2, 3], false),
                    (vec![3, 4], true),
                    (vec![4, 5], false),
                    (vec![0, 5], true),
                ],
            ),
            (
                4,
                vec![
                    (vec![0, 1, 2, 3], false),
                    (vec![0, 2], true),
                    (vec![1, 3], true),
                ],
            ),
            (
                8,
                vec![
                    (vec![0, 7], true),
                    (vec![1, 6], false),
                    (vec![2, 5], true),
                    (vec![3, 4], false),
                    (vec![0, 1, 2, 3], true),
                ],
            ),
            (
                3,
                vec![(vec![0], true), (vec![1], false), (vec![0, 1, 2], true)],
            ),
        ];
        for (num_vars, constraints) in &systems {
            let sol = solve_sat(*num_vars, constraints);
            assert_satisfies_all(&sol, constraints);
        }
    }

    #[test]
    fn implied_units_exposes_forced_variable() {
        // x0 ⊕ x2 = 1, x0 = 1  ⇒  x2 forced to 0; x0 forced to 1.
        let constraints = vec![(vec![0, 2], true), (vec![0], true)];
        let sol = solve_sat(3, &constraints);
        let units = sol.implied_units();
        assert!(units.contains(&(0, true)), "units = {units:?}");
        assert!(units.contains(&(2, false)), "units = {units:?}");
        assert_satisfies_all(&sol, &constraints);
    }

    #[test]
    fn implied_units_single_forced_value() {
        // A system forcing x2 = 1 directly.
        let constraints = vec![(vec![2], true)];
        let sol = solve_sat(3, &constraints);
        assert_eq!(sol.implied_units(), &[(2, true)]);
        assert!(sol.value(2));
    }

    #[test]
    fn implied_equalities_equal() {
        // x0 ⊕ x1 = 0  ⇒  x0 == x1, exposed as (0, 1, false).
        let constraints = vec![(vec![0, 1], false)];
        let sol = solve_sat(2, &constraints);
        assert_eq!(sol.implied_equalities(), &[(0, 1, false)]);
        assert_satisfies_all(&sol, &constraints);
    }

    #[test]
    fn implied_equalities_inequal() {
        // x0 ⊕ x1 = 1  ⇒  x0 == !x1, exposed as (0, 1, true).
        let constraints = vec![(vec![0, 1], true)];
        let sol = solve_sat(2, &constraints);
        assert_eq!(sol.implied_equalities(), &[(0, 1, true)]);
        assert_satisfies_all(&sol, &constraints);
    }

    #[test]
    fn empty_system_is_sat_all_false() {
        let sol = solve_sat(4, &[]);
        assert_eq!(sol.values(), &[false, false, false, false]);
        assert!(sol.implied_units().is_empty());
        assert!(sol.implied_equalities().is_empty());
    }

    #[test]
    fn duplicate_vars_cancel_trivially_true() {
        // x0 ⊕ x0 = 0 is trivially true (the row reduces to 0 = 0).
        let sol = solve_sat(1, &[(vec![0, 0], false)]);
        assert!(sol.implied_units().is_empty());
        assert!(sol.implied_equalities().is_empty());
    }

    #[test]
    fn duplicate_vars_cancel_unsat() {
        // x0 ⊕ x0 = 1 reduces to 0 = 1, which is unsatisfiable.
        let sys = build(1, &[(vec![0, 0], true)]);
        assert_eq!(sys.solve(), Gf2Outcome::Unsat);
    }

    #[test]
    fn triple_duplicate_keeps_one_occurrence() {
        // x0 ⊕ x0 ⊕ x0 = 1 has odd parity ⇒ x0 = 1 (a single occurrence).
        let sol = solve_sat(1, &[(vec![0, 0, 0], true)]);
        assert!(sol.value(0));
        assert_eq!(sol.implied_units(), &[(0, true)]);
    }

    #[test]
    fn trivial_zero_rows_dropped() {
        // 0 = 0 rows (empty var set, rhs false) contribute no units/equalities.
        let constraints = vec![(vec![], false), (vec![0, 1], true)];
        let sol = solve_sat(2, &constraints);
        assert_satisfies_all(&sol, &constraints);
        // Only the real equality should be reported.
        assert_eq!(sol.implied_equalities(), &[(0, 1, true)]);
        assert!(sol.implied_units().is_empty());
    }

    #[test]
    fn empty_constraint_with_true_rhs_is_unsat() {
        // An explicit `() = 1` constraint is the inconsistent row 0 = 1.
        let sys = build(2, &[(vec![], true)]);
        assert_eq!(sys.solve(), Gf2Outcome::Unsat);
    }

    #[test]
    fn many_variables_cross_word_boundary() {
        // Exercise the multi-word bitset path (variables above index 63).
        let constraints = vec![
            (vec![0, 64], false),
            (vec![64, 127], true),
            (vec![100], true),
        ];
        let sol = solve_sat(128, &constraints);
        assert_satisfies_all(&sol, &constraints);
        assert!(sol.implied_units().contains(&(100, true)));
    }

    #[test]
    fn outputs_are_sorted() {
        // Construct units/equalities out of natural order and confirm sorting.
        let constraints = vec![
            (vec![5], true),
            (vec![1], false),
            (vec![3, 7], true),
            (vec![2, 4], false),
        ];
        let sol = solve_sat(8, &constraints);
        let units = sol.implied_units();
        assert!(units.windows(2).all(|w| w[0].0 <= w[1].0));
        let eqs = sol.implied_equalities();
        assert!(eqs.windows(2).all(|w| (w[0].0, w[0].1) <= (w[1].0, w[1].1)));
        assert_satisfies_all(&sol, &constraints);
    }

    /// The XOR-fold of the constraints at `subset` (`(support, parity)`),
    /// duplicates cancelling by parity — the test-side oracle for "sums to
    /// `0 = 1`".
    fn fold_subset(constraints: &[Constraint], subset: &[usize]) -> (Vec<usize>, bool) {
        let mut counts: std::collections::BTreeMap<usize, usize> =
            std::collections::BTreeMap::new();
        let mut parity = false;
        for &i in subset {
            let (vars, rhs) = &constraints[i];
            for &v in vars {
                *counts.entry(v).or_insert(0) += 1;
            }
            parity ^= *rhs;
        }
        let support: Vec<usize> = counts
            .into_iter()
            .filter(|&(_, c)| c % 2 == 1)
            .map(|(v, _)| v)
            .collect();
        (support, parity)
    }

    #[test]
    fn reason_subset_none_for_sat_system() {
        // A satisfiable system has no `0 = 1` row, so no reason subset.
        let sys = build(3, &[(vec![0, 1], true), (vec![1, 2], false)]);
        assert!(matches!(sys.solve(), Gf2Outcome::Sat(_)));
        assert!(sys.unsat_reason_subset().is_none());
    }

    #[test]
    fn reason_subset_direct_contradiction() {
        // x0 ⊕ x1 = 0 and x0 ⊕ x1 = 1: the two rows sum to 0 = 1.
        let constraints = vec![(vec![0, 1], false), (vec![0, 1], true)];
        let sys = build(2, &constraints);
        let subset = sys.unsat_reason_subset().expect("unsat reason subset");
        assert_eq!(subset, vec![0, 1]);
        assert_eq!(fold_subset(&constraints, &subset), (vec![], true));
    }

    #[test]
    fn reason_subset_chained_three_rows() {
        // x0⊕x1=1, x1⊕x2=1, x0⊕x2=1 sum to 0 = 1 (the classic odd-parity cycle).
        let constraints = vec![(vec![0, 1], true), (vec![1, 2], true), (vec![0, 2], true)];
        let sys = build(3, &constraints);
        let subset = sys.unsat_reason_subset().expect("unsat reason subset");
        // Every subset returned must genuinely sum to 0 = 1.
        assert_eq!(fold_subset(&constraints, &subset), (vec![], true));
        assert_eq!(sys.solve(), Gf2Outcome::Unsat);
    }

    #[test]
    fn reason_subset_ignores_irrelevant_rows() {
        // Two inconsistent rows plus an unrelated consistent one; the subset
        // must not include the irrelevant row (it is not needed to reach 0 = 1).
        let constraints = vec![
            (vec![5, 6], false), // irrelevant
            (vec![0, 1], false),
            (vec![0, 1], true),
        ];
        let sys = build(7, &constraints);
        let subset = sys.unsat_reason_subset().expect("unsat reason subset");
        assert_eq!(fold_subset(&constraints, &subset), (vec![], true));
        assert!(!subset.contains(&0), "irrelevant row must not appear");
    }

    #[test]
    fn reason_subset_empty_constraint_unsat() {
        // An explicit () = 1 is itself the inconsistent row.
        let constraints = vec![(vec![], true)];
        let sys = build(2, &constraints);
        let subset = sys.unsat_reason_subset().expect("unsat reason subset");
        assert_eq!(subset, vec![0]);
        assert_eq!(fold_subset(&constraints, &subset), (vec![], true));
    }

    #[test]
    fn reason_subset_soundness_fuzz_no_false_subset() {
        // Deterministic LCG over many random small XOR systems. Soundness
        // invariant: `unsat_reason_subset` is `Some` iff `solve` is `Unsat`, and
        // every returned subset genuinely sums to 0 = 1 (so a downstream DRAT
        // certificate over CNF(S) is always a real refutation — never a false one).
        let mut state: u64 = 0x9E37_79B9_7F4A_7C15;
        let mut next = || {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            state
        };
        let mut unsat_seen = 0u32;
        for _ in 0..4000 {
            let num_vars = 1 + (next() % 6) as usize;
            let num_rows = 1 + (next() % 7) as usize;
            let mut constraints: Vec<Constraint> = Vec::new();
            for _ in 0..num_rows {
                let mut vars: Vec<usize> = Vec::new();
                for v in 0..num_vars {
                    if next() & 1 == 1 {
                        vars.push(v);
                    }
                }
                let rhs = next() & 1 == 1;
                constraints.push((vars, rhs));
            }
            let sys = build(num_vars, &constraints);
            let is_unsat = matches!(sys.solve(), Gf2Outcome::Unsat);
            match sys.unsat_reason_subset() {
                Some(subset) => {
                    assert!(is_unsat, "reason subset for a SAT system: {constraints:?}");
                    assert_eq!(
                        fold_subset(&constraints, &subset),
                        (vec![], true),
                        "subset {subset:?} does not sum to 0 = 1 for {constraints:?}"
                    );
                    unsat_seen += 1;
                }
                None => assert!(
                    !is_unsat,
                    "no reason subset for an UNSAT system: {constraints:?}"
                ),
            }
        }
        assert!(unsat_seen > 0, "fuzz must exercise some UNSAT systems");
    }

    #[test]
    fn reason_subset_cross_word_boundary() {
        // Variables above index 63 plus an inconsistency, exercising multi-word
        // rows alongside multi-word provenance is not needed (few rows) but the
        // variable path is multi-word.
        let constraints = vec![
            (vec![0, 64, 100], true),
            (vec![64, 100], false),
            (vec![0], false), // forces x0=false, but row 0 ⇒ x0=true ⇒ 0 = 1
        ];
        let sys = build(128, &constraints);
        assert_eq!(sys.solve(), Gf2Outcome::Unsat);
        let subset = sys.unsat_reason_subset().expect("unsat reason subset");
        assert_eq!(fold_subset(&constraints, &subset), (vec![], true));
    }
}
