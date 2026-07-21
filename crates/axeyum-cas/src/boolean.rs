//! Boolean algebra over named variables — a self-contained analogue of `SymPy`'s
//! `logic` module, independent of the polynomial [`crate::CasExpr`] kernel.
//!
//! A [`BoolExpr`] is a propositional formula tree over `bool` constants and
//! string-named variables, closed under negation, conjunction, disjunction,
//! exclusive-or, implication and bi-implication. Every operation here is total
//! and panic-free.
//!
//! The semantic core is the **exhaustive truth table**: because a formula has
//! finitely many variables, evaluating it over all `2ᵏ` assignments decides every
//! semantic question exactly. So [`BoolExpr::equivalent`] — normalize nothing,
//! just compare the two truth tables over the union of variables — *is* the
//! certificate of logical equivalence, and the normal-form builders
//! ([`BoolExpr::to_dnf`], [`BoolExpr::to_cnf`]) and the `Quine-McCluskey`
//! minimizer ([`BoolExpr::simplify_qmc`]) are all checked against it in tests.
//!
//! To bound cost, table enumeration is capped at [`MAX_VARS`] variables; past
//! that the table-based queries return `None`.

use std::collections::{BTreeMap, BTreeSet};

/// The largest number of distinct variables for which a full truth table is
/// enumerated. `2²⁰ ≈ 10⁶` rows bounds the work; formulas with more variables
/// make the table-based queries return `None`.
pub const MAX_VARS: usize = 20;

/// A propositional formula over `bool` constants and string-named variables.
///
/// `And`, `Or` and `Xor` are variadic (an empty `And` is `true`, an empty `Or`
/// and an empty `Xor` are `false`, matching the usual identities).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BoolExpr {
    /// A literal truth value.
    Const(bool),
    /// A named propositional variable.
    Var(String),
    /// Logical negation `¬x`.
    Not(Box<BoolExpr>),
    /// Variadic conjunction `x₀ ∧ x₁ ∧ …` (empty ⇒ `true`).
    And(Vec<BoolExpr>),
    /// Variadic disjunction `x₀ ∨ x₁ ∨ …` (empty ⇒ `false`).
    Or(Vec<BoolExpr>),
    /// Variadic exclusive-or `x₀ ⊕ x₁ ⊕ …` (parity; empty ⇒ `false`).
    Xor(Vec<BoolExpr>),
    /// Material implication `a → b`.
    Implies(Box<BoolExpr>, Box<BoolExpr>),
    /// Bi-implication `a ↔ b`.
    Iff(Box<BoolExpr>, Box<BoolExpr>),
}

impl BoolExpr {
    /// A constant `true`/`false` leaf.
    #[must_use]
    pub fn constant(value: bool) -> BoolExpr {
        BoolExpr::Const(value)
    }

    /// A variable leaf named `name`.
    #[must_use]
    pub fn var(name: &str) -> BoolExpr {
        BoolExpr::Var(name.to_string())
    }

    /// The negation `¬inner`.
    #[must_use]
    pub fn negate(inner: BoolExpr) -> BoolExpr {
        BoolExpr::Not(Box::new(inner))
    }

    /// The conjunction of `operands`.
    #[must_use]
    pub fn and(operands: Vec<BoolExpr>) -> BoolExpr {
        BoolExpr::And(operands)
    }

    /// The disjunction of `operands`.
    #[must_use]
    pub fn or(operands: Vec<BoolExpr>) -> BoolExpr {
        BoolExpr::Or(operands)
    }

    /// The exclusive-or of `operands`.
    #[must_use]
    pub fn xor(operands: Vec<BoolExpr>) -> BoolExpr {
        BoolExpr::Xor(operands)
    }

    /// The implication `antecedent → consequent`.
    #[must_use]
    pub fn implies(antecedent: BoolExpr, consequent: BoolExpr) -> BoolExpr {
        BoolExpr::Implies(Box::new(antecedent), Box::new(consequent))
    }

    /// The bi-implication `left ↔ right`.
    #[must_use]
    pub fn iff(left: BoolExpr, right: BoolExpr) -> BoolExpr {
        BoolExpr::Iff(Box::new(left), Box::new(right))
    }

    /// The number of nodes in the formula tree (its structural size).
    #[must_use]
    pub fn size(&self) -> usize {
        match self {
            BoolExpr::Const(_) | BoolExpr::Var(_) => 1,
            BoolExpr::Not(inner) => 1 + inner.size(),
            BoolExpr::And(operands) | BoolExpr::Or(operands) | BoolExpr::Xor(operands) => {
                1 + operands.iter().map(BoolExpr::size).sum::<usize>()
            }
            BoolExpr::Implies(left, right) | BoolExpr::Iff(left, right) => {
                1 + left.size() + right.size()
            }
        }
    }

    /// The distinct variable names occurring in the formula, sorted.
    #[must_use]
    pub fn variables(&self) -> Vec<String> {
        let mut names = BTreeSet::new();
        self.collect_variables(&mut names);
        names.into_iter().collect()
    }

    /// Accumulate this formula's variable names into `names`.
    fn collect_variables(&self, names: &mut BTreeSet<String>) {
        match self {
            BoolExpr::Const(_) => {}
            BoolExpr::Var(name) => {
                names.insert(name.clone());
            }
            BoolExpr::Not(inner) => inner.collect_variables(names),
            BoolExpr::And(operands) | BoolExpr::Or(operands) | BoolExpr::Xor(operands) => {
                for operand in operands {
                    operand.collect_variables(names);
                }
            }
            BoolExpr::Implies(left, right) | BoolExpr::Iff(left, right) => {
                left.collect_variables(names);
                right.collect_variables(names);
            }
        }
    }

    /// Evaluate the formula under a truth `assignment`.
    ///
    /// Returns `None` if any variable occurring in the formula is missing from
    /// `assignment` (evaluation is strict: every operand is consulted).
    #[must_use]
    pub fn evaluate(&self, assignment: &BTreeMap<String, bool>) -> Option<bool> {
        match self {
            BoolExpr::Const(value) => Some(*value),
            BoolExpr::Var(name) => assignment.get(name).copied(),
            BoolExpr::Not(inner) => inner.evaluate(assignment).map(|value| !value),
            BoolExpr::And(operands) => {
                let mut result = true;
                for operand in operands {
                    result &= operand.evaluate(assignment)?;
                }
                Some(result)
            }
            BoolExpr::Or(operands) => {
                let mut result = false;
                for operand in operands {
                    result |= operand.evaluate(assignment)?;
                }
                Some(result)
            }
            BoolExpr::Xor(operands) => {
                let mut result = false;
                for operand in operands {
                    result ^= operand.evaluate(assignment)?;
                }
                Some(result)
            }
            BoolExpr::Implies(antecedent, consequent) => {
                let left = antecedent.evaluate(assignment)?;
                let right = consequent.evaluate(assignment)?;
                Some(!left || right)
            }
            BoolExpr::Iff(left, right) => {
                let left = left.evaluate(assignment)?;
                let right = right.evaluate(assignment)?;
                Some(left == right)
            }
        }
    }

    /// The full truth table over the formula's own variables.
    ///
    /// Each row is `(values, output)`, where `values[i]` is the assignment to the
    /// `i`-th variable of [`BoolExpr::variables`] and `output` is the formula's
    /// value there. Rows run in ascending binary order with the first variable as
    /// the most-significant bit. Returns `None` if the formula has more than
    /// [`MAX_VARS`] variables.
    #[must_use]
    pub fn truth_table(&self) -> Option<Vec<(Vec<bool>, bool)>> {
        let variables = self.variables();
        self.truth_table_over(&variables)
    }

    /// The truth table over an explicit variable list `variables`, which must
    /// contain every variable occurring in the formula. `None` if `variables` has
    /// more than [`MAX_VARS`] entries.
    fn truth_table_over(&self, variables: &[String]) -> Option<Vec<(Vec<bool>, bool)>> {
        let count = variables.len();
        if count > MAX_VARS {
            return None;
        }
        let rows = 1_usize << count;
        let mut table = Vec::with_capacity(rows);
        for mask in 0..rows {
            let mut assignment = BTreeMap::new();
            let mut values = Vec::with_capacity(count);
            for (index, name) in variables.iter().enumerate() {
                let bit = (mask >> (count - 1 - index)) & 1 == 1;
                assignment.insert(name.clone(), bit);
                values.push(bit);
            }
            table.push((values, self.evaluate(&assignment)?));
        }
        Some(table)
    }

    /// Whether the formula is a tautology (true under every assignment). `None`
    /// past the [`MAX_VARS`] cap.
    #[must_use]
    pub fn is_tautology(&self) -> Option<bool> {
        let table = self.truth_table()?;
        Some(table.iter().all(|(_, output)| *output))
    }

    /// Whether the formula is satisfiable (true under some assignment). `None`
    /// past the [`MAX_VARS`] cap.
    #[must_use]
    pub fn is_satisfiable(&self) -> Option<bool> {
        let table = self.truth_table()?;
        Some(table.iter().any(|(_, output)| *output))
    }

    /// Whether the formula is a contradiction (false under every assignment).
    /// `None` past the [`MAX_VARS`] cap.
    #[must_use]
    pub fn is_contradiction(&self) -> Option<bool> {
        self.is_satisfiable().map(|satisfiable| !satisfiable)
    }

    /// Whether `self` and `other` are logically equivalent — the truth-table
    /// certificate, compared over the union of both formulas' variables. `None`
    /// if that union exceeds [`MAX_VARS`].
    #[must_use]
    pub fn equivalent(&self, other: &BoolExpr) -> Option<bool> {
        let mut names = BTreeSet::new();
        self.collect_variables(&mut names);
        other.collect_variables(&mut names);
        let variables: Vec<String> = names.into_iter().collect();
        let left = self.truth_table_over(&variables)?;
        let right = other.truth_table_over(&variables)?;
        Some(
            left.iter()
                .zip(right.iter())
                .all(|(left_row, right_row)| left_row.1 == right_row.1),
        )
    }

    /// The disjunctive normal form (sum of minterms) read off the truth table:
    /// one conjunctive minterm per satisfying assignment, or `Const(false)` if
    /// unsatisfiable. Beyond the [`MAX_VARS`] cap the formula is returned
    /// unchanged.
    #[must_use]
    pub fn to_dnf(&self) -> BoolExpr {
        let variables = self.variables();
        if variables.is_empty() {
            return BoolExpr::Const(self.evaluate(&BTreeMap::new()).unwrap_or(false));
        }
        let Some(table) = self.truth_table_over(&variables) else {
            return self.clone();
        };
        let mut minterms = Vec::new();
        for (values, output) in &table {
            if !output {
                continue;
            }
            let mut literals = Vec::with_capacity(variables.len());
            for (name, value) in variables.iter().zip(values.iter()) {
                literals.push(literal(name, *value));
            }
            minterms.push(make_and(literals));
        }
        if minterms.is_empty() {
            return BoolExpr::Const(false);
        }
        make_or(minterms)
    }

    /// The conjunctive normal form (product of maxterms) read off the truth
    /// table: one disjunctive maxterm per falsifying assignment, or `Const(true)`
    /// if the formula is a tautology. Beyond the [`MAX_VARS`] cap the formula is
    /// returned unchanged.
    #[must_use]
    pub fn to_cnf(&self) -> BoolExpr {
        let variables = self.variables();
        if variables.is_empty() {
            return BoolExpr::Const(self.evaluate(&BTreeMap::new()).unwrap_or(false));
        }
        let Some(table) = self.truth_table_over(&variables) else {
            return self.clone();
        };
        let mut maxterms = Vec::new();
        for (values, output) in &table {
            if *output {
                continue;
            }
            // A maxterm is the negation of a falsifying minterm (De Morgan): a
            // variable that is `true` there appears negated, and vice versa.
            let mut literals = Vec::with_capacity(variables.len());
            for (name, value) in variables.iter().zip(values.iter()) {
                literals.push(literal(name, !*value));
            }
            maxterms.push(make_or(literals));
        }
        if maxterms.is_empty() {
            return BoolExpr::Const(true);
        }
        make_and(maxterms)
    }

    /// A minimized sum-of-products equivalent, via the `Quine-McCluskey`
    /// algorithm: derive all prime implicants by iterated adjacency merging, then
    /// cover the minterms with a greedy essential-first selection.
    ///
    /// Returns `Const(false)` for an unsatisfiable formula and `Const(true)` for a
    /// tautology. `None` if the formula has more than [`MAX_VARS`] variables. The
    /// result is logically equivalent to the input (checked in tests) and never
    /// larger than the full DNF.
    #[must_use]
    pub fn simplify_qmc(&self) -> Option<BoolExpr> {
        let variables = self.variables();
        let count = variables.len();
        if count == 0 {
            return Some(BoolExpr::Const(
                self.evaluate(&BTreeMap::new()).unwrap_or(false),
            ));
        }
        let table = self.truth_table_over(&variables)?;

        // Minterm numbers: row indices whose output is true. The row index equals
        // the bit pattern with variable 0 as the most-significant bit.
        let mut minterms: Vec<u32> = Vec::new();
        for (index, (_, output)) in table.iter().enumerate() {
            if *output {
                minterms.push(u32::try_from(index).ok()?);
            }
        }
        if minterms.is_empty() {
            return Some(BoolExpr::Const(false));
        }

        let primes = prime_implicants(&minterms);
        let coverage: Vec<Vec<u32>> = primes
            .iter()
            .map(|&(bits, dashes)| {
                minterms
                    .iter()
                    .copied()
                    .filter(|&minterm| (minterm & !dashes) == bits)
                    .collect()
            })
            .collect();
        let chosen = select_cover(&minterms, &coverage);

        // Bit position of the `index`-th variable (variable 0 is most significant).
        let mut terms: Vec<BoolExpr> = Vec::new();
        for &prime_index in &chosen {
            let (bits, dashes) = primes[prime_index];
            let mut literals = Vec::new();
            for (index, name) in variables.iter().enumerate() {
                let position = count - 1 - index;
                let selector = 1_u32 << position;
                if dashes & selector != 0 {
                    continue; // don't-care position
                }
                literals.push(literal(name, bits & selector != 0));
            }
            if literals.is_empty() {
                // An all-dashes implicant covers everything: the formula is a
                // tautology.
                return Some(BoolExpr::Const(true));
            }
            terms.push(make_and(literals));
        }
        if terms.is_empty() {
            return Some(BoolExpr::Const(false));
        }
        Some(make_or(terms))
    }
}

/// A single literal: the variable `name` when `value` is `true`, its negation
/// otherwise.
fn literal(name: &str, value: bool) -> BoolExpr {
    let variable = BoolExpr::Var(name.to_string());
    if value {
        variable
    } else {
        BoolExpr::Not(Box::new(variable))
    }
}

/// A conjunction of `terms`, unwrapping the singleton case to the term itself.
fn make_and(mut terms: Vec<BoolExpr>) -> BoolExpr {
    if terms.len() == 1 {
        terms.remove(0)
    } else {
        BoolExpr::And(terms)
    }
}

/// A disjunction of `terms`, unwrapping the singleton case to the term itself.
fn make_or(mut terms: Vec<BoolExpr>) -> BoolExpr {
    if terms.len() == 1 {
        terms.remove(0)
    } else {
        BoolExpr::Or(terms)
    }
}

/// The prime implicants of a minterm set, each as `(bits, dashes)` where `dashes`
/// marks don't-care bit positions and `bits` holds the fixed values (zero at dash
/// positions). Computed by iterated `Quine-McCluskey` adjacency merging.
fn prime_implicants(minterms: &[u32]) -> Vec<(u32, u32)> {
    let mut current: Vec<(u32, u32)> = minterms.iter().map(|&minterm| (minterm, 0)).collect();
    let mut primes: Vec<(u32, u32)> = Vec::new();
    loop {
        let mut used = vec![false; current.len()];
        let mut next: Vec<(u32, u32)> = Vec::new();
        for i in 0..current.len() {
            for j in (i + 1)..current.len() {
                let (bits_i, dashes_i) = current[i];
                let (bits_j, dashes_j) = current[j];
                if dashes_i != dashes_j {
                    continue;
                }
                let diff = bits_i ^ bits_j;
                // Combine when the pair differs in exactly one fixed bit.
                if diff.is_power_of_two() {
                    used[i] = true;
                    used[j] = true;
                    let combined = (bits_i & !diff, dashes_i | diff);
                    if !next.contains(&combined) {
                        next.push(combined);
                    }
                }
            }
        }
        for (implicant, &is_used) in current.iter().zip(used.iter()) {
            if !is_used && !primes.contains(implicant) {
                primes.push(*implicant);
            }
        }
        if next.is_empty() {
            break;
        }
        current = next;
    }
    primes
}

/// Choose a set of prime implicants (by index) covering every minterm: take all
/// essential primes first, then greedily add the prime covering the most
/// still-uncovered minterms.
fn select_cover(minterms: &[u32], coverage: &[Vec<u32>]) -> Vec<usize> {
    let mut chosen: Vec<usize> = Vec::new();
    let mut covered: BTreeSet<u32> = BTreeSet::new();

    // Essential prime implicants: any minterm covered by exactly one prime forces
    // that prime into the cover.
    for &minterm in minterms {
        let covering: Vec<usize> = coverage
            .iter()
            .enumerate()
            .filter(|(_, covered_minterms)| covered_minterms.contains(&minterm))
            .map(|(index, _)| index)
            .collect();
        if covering.len() == 1 {
            let prime_index = covering[0];
            if !chosen.contains(&prime_index) {
                chosen.push(prime_index);
                for &value in &coverage[prime_index] {
                    covered.insert(value);
                }
            }
        }
    }

    // Greedy fill for whatever the essentials left uncovered.
    while covered.len() < minterms.len() {
        let mut best: Option<usize> = None;
        let mut best_count = 0;
        for (index, covered_minterms) in coverage.iter().enumerate() {
            if chosen.contains(&index) {
                continue;
            }
            let gain = covered_minterms
                .iter()
                .filter(|value| !covered.contains(value))
                .count();
            if gain > best_count {
                best_count = gain;
                best = Some(index);
            }
        }
        match best {
            Some(index) => {
                chosen.push(index);
                for &value in &coverage[index] {
                    covered.insert(value);
                }
            }
            None => break,
        }
    }
    chosen
}

#[cfg(test)]
mod tests {
    use super::*;

    fn a() -> BoolExpr {
        BoolExpr::var("a")
    }
    fn b() -> BoolExpr {
        BoolExpr::var("b")
    }
    fn c() -> BoolExpr {
        BoolExpr::var("c")
    }

    #[test]
    fn de_morgan_law_holds() {
        // ¬(a ∧ b) ≡ (¬a ∨ ¬b).
        let left = BoolExpr::negate(BoolExpr::and(vec![a(), b()]));
        let right = BoolExpr::or(vec![BoolExpr::negate(a()), BoolExpr::negate(b())]);
        assert_eq!(left.equivalent(&right), Some(true));
        // The dual: ¬(a ∨ b) ≡ (¬a ∧ ¬b).
        let left2 = BoolExpr::negate(BoolExpr::or(vec![a(), b()]));
        let right2 = BoolExpr::and(vec![BoolExpr::negate(a()), BoolExpr::negate(b())]);
        assert_eq!(left2.equivalent(&right2), Some(true));
        // A non-equivalence is reported as such.
        assert_eq!(left.equivalent(&right2), Some(false));
    }

    #[test]
    fn distributivity_holds() {
        // a ∧ (b ∨ c) ≡ (a ∧ b) ∨ (a ∧ c).
        let left = BoolExpr::and(vec![a(), BoolExpr::or(vec![b(), c()])]);
        let right = BoolExpr::or(vec![
            BoolExpr::and(vec![a(), b()]),
            BoolExpr::and(vec![a(), c()]),
        ]);
        assert_eq!(left.equivalent(&right), Some(true));
    }

    #[test]
    fn excluded_middle_and_contradiction() {
        // a ∨ ¬a is a tautology; a ∧ ¬a is a contradiction.
        let tautology = BoolExpr::or(vec![a(), BoolExpr::negate(a())]);
        assert_eq!(tautology.is_tautology(), Some(true));
        assert_eq!(tautology.is_satisfiable(), Some(true));
        assert_eq!(tautology.is_contradiction(), Some(false));

        let contradiction = BoolExpr::and(vec![a(), BoolExpr::negate(a())]);
        assert_eq!(contradiction.is_contradiction(), Some(true));
        assert_eq!(contradiction.is_satisfiable(), Some(false));
        assert_eq!(contradiction.is_tautology(), Some(false));
    }

    #[test]
    fn implication_unfolds_to_disjunction() {
        // (a → b) ≡ (¬a ∨ b).
        let implication = BoolExpr::implies(a(), b());
        let unfolded = BoolExpr::or(vec![BoolExpr::negate(a()), b()]);
        assert_eq!(implication.equivalent(&unfolded), Some(true));
    }

    #[test]
    fn xor_expands_via_and_or_not() {
        // (a ⊕ b) ≡ (a ∨ b) ∧ ¬(a ∧ b).
        let xor = BoolExpr::xor(vec![a(), b()]);
        let expansion = BoolExpr::and(vec![
            BoolExpr::or(vec![a(), b()]),
            BoolExpr::negate(BoolExpr::and(vec![a(), b()])),
        ]);
        assert_eq!(xor.equivalent(&expansion), Some(true));
    }

    #[test]
    fn evaluate_and_truth_table() {
        let expr = BoolExpr::and(vec![a(), b()]);
        let mut assignment = BTreeMap::new();
        assignment.insert("a".to_string(), true);
        assignment.insert("b".to_string(), true);
        assert_eq!(expr.evaluate(&assignment), Some(true));
        assignment.insert("b".to_string(), false);
        assert_eq!(expr.evaluate(&assignment), Some(false));
        // Missing variable ⇒ None.
        let mut partial = BTreeMap::new();
        partial.insert("a".to_string(), true);
        assert_eq!(expr.evaluate(&partial), None);

        // Truth table of a ∧ b: only the all-true row is true.
        let table = expr.truth_table().unwrap();
        assert_eq!(table.len(), 4);
        assert_eq!(table[0], (vec![false, false], false));
        assert_eq!(table[3], (vec![true, true], true));
    }

    #[test]
    fn dnf_and_cnf_round_trip_equivalent() {
        // A mixed formula and its two normal forms all agree semantically.
        let expr = BoolExpr::iff(BoolExpr::xor(vec![a(), b()]), BoolExpr::implies(c(), a()));
        let dnf = expr.to_dnf();
        let cnf = expr.to_cnf();
        assert_eq!(expr.equivalent(&dnf), Some(true));
        assert_eq!(expr.equivalent(&cnf), Some(true));

        // Constant formulas collapse cleanly.
        let contradiction = BoolExpr::and(vec![a(), BoolExpr::negate(a())]);
        assert_eq!(contradiction.to_dnf(), BoolExpr::Const(false));
        let tautology = BoolExpr::or(vec![a(), BoolExpr::negate(a())]);
        assert_eq!(tautology.to_cnf(), BoolExpr::Const(true));
    }

    #[test]
    fn qmc_reduces_to_single_variable() {
        // (a ∧ b) ∨ (a ∧ ¬b) minimizes to a.
        let expr = BoolExpr::or(vec![
            BoolExpr::and(vec![a(), b()]),
            BoolExpr::and(vec![a(), BoolExpr::negate(b())]),
        ]);
        let simplified = expr.simplify_qmc().unwrap();
        assert_eq!(simplified.equivalent(&expr), Some(true));
        assert_eq!(simplified.equivalent(&a()), Some(true));
        // The minimized form is strictly smaller than the original.
        assert!(simplified.size() < expr.size());
        // Specifically it is exactly the single variable a.
        assert_eq!(simplified, a());
    }

    #[test]
    fn qmc_minimizes_majority_function() {
        // Majority(a, b, c) = (a ∧ b) ∨ (a ∧ c) ∨ (b ∧ c).
        let majority = BoolExpr::or(vec![
            BoolExpr::and(vec![a(), b()]),
            BoolExpr::and(vec![a(), c()]),
            BoolExpr::and(vec![b(), c()]),
        ]);
        let simplified = majority.simplify_qmc().unwrap();
        assert_eq!(simplified.equivalent(&majority), Some(true));
        assert!(simplified.size() <= majority.size());

        // A tautology and a contradiction collapse to constants.
        let tautology = BoolExpr::implies(a(), BoolExpr::or(vec![a(), b()]));
        assert_eq!(tautology.simplify_qmc(), Some(BoolExpr::Const(true)));
        let contradiction = BoolExpr::and(vec![a(), BoolExpr::negate(a())]);
        assert_eq!(contradiction.simplify_qmc(), Some(BoolExpr::Const(false)));
    }

    #[test]
    fn variables_are_sorted_and_distinct() {
        let expr = BoolExpr::or(vec![c(), a(), BoolExpr::and(vec![b(), a()])]);
        assert_eq!(
            expr.variables(),
            vec!["a".to_string(), "b".to_string(), "c".to_string()]
        );
    }
}
