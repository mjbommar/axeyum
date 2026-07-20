//! Correctness-first XOR-aware DPLL decider for CDCL(XOR) integration.
//!
//! This module is the *integration* slice of the CDCL(XOR) path (see
//! `docs/research/05-algorithms/cdcl-xor-integration-design.md`, the "bounded
//! first implementation slice"). The earlier slices built and brute-force
//! validated the algebraic pieces in isolation: the GF(2) Gaussian solver
//! ([`crate::gf2`]), sound XOR-gate recovery from CNF ([`crate::extract_xors`]),
//! and the in-search XOR propagation primitive ([`crate::xor_implications`]).
//! This slice is the first thing that *runs all three together inside a search*
//! — a small DPLL that decides a [`CnfFormula`] conjoined with the XOR system
//! recovered from it, interleaving clause unit propagation with XOR propagation
//! to a fixpoint.
//!
//! Its job is to **prove the integration is sound**, differential-tested against
//! a brute-force oracle and the production [`crate::solve_with_rustsat_batsat`]
//! adapter. It is deliberately *not* the production solver:
//!
//! * chronological backtracking only — **no** learned clauses / 1-UIP;
//! * a fresh-recompute XOR primitive per call — **no** watched-literal matrix or
//!   incremental Gaussian rows;
//! * **no** proof emission (the [`crate::TrustId`]-style `XorGaussian` ledger
//!   wiring into the solver dispatch is a later slice).
//!
//! Performance is explicitly a non-goal: the decider carries a step budget and
//! returns [`XorDpllResult::Unknown`] when it is exhausted, which makes it total
//! and guarantees it cannot hang.
//!
//! # Soundness
//!
//! Because the recovered XOR gates *are* clauses already present in the formula
//! (extraction recognizes the complete `2^(k-1)`-clause encoding), the clause
//! set is the ground truth: a model satisfying every clause already satisfies
//! every XOR constraint. The XOR propagation is therefore pure *acceleration* —
//! it can only prune assignments the clauses already forbid, never add new
//! models. A returned [`XorDpllResult::Sat`] model is checked (in debug builds)
//! against **both** every clause and every XOR constraint before it is handed
//! back; the public guarantee is that a `Sat(model)` satisfies both.
//!
//! # Determinism
//!
//! The search is fully deterministic: it always decides the lowest-index
//! unassigned variable, always tries `false` before `true`, and every primitive
//! it calls ([`crate::xor_implications`]) is itself deterministic. No hash-map
//! iteration order influences the result.

use crate::{CnfFormula, XorConstraintInput, XorImplication, extract_xors, xor_implications};

/// Maximum number of propagation/decision steps before the decider gives up.
///
/// Reaching this cap yields [`XorDpllResult::Unknown`], keeping the decider
/// total and non-hanging. The bound is generous (this is a correctness-first
/// decider, not a performance one) but finite.
const STEP_BUDGET: u64 = 2_000_000;

/// Outcome of [`solve_with_xor`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum XorDpllResult {
    /// The formula and all recovered XOR constraints are jointly satisfiable.
    ///
    /// The carried assignment is a full model (one Boolean per variable, in
    /// index order) that satisfies **every clause and every XOR constraint**.
    Sat(Vec<bool>),
    /// The formula (equivalently, the formula plus its XOR system) is
    /// unsatisfiable.
    Unsat,
    /// The step budget was exhausted before a verdict was reached. The decider
    /// is total: this is how it stays non-hanging, never an error.
    Unknown,
}

/// Decides `formula` conjoined with the XOR constraints recovered from it.
///
/// The XOR system is recovered with [`extract_xors`] and then driven, alongside
/// clause unit propagation, by a small chronological-backtracking DPLL:
///
/// 1. **Propagation fixpoint.** Clause unit propagation and
///    [`xor_implications`] are interleaved to a fixpoint: a clause with all but
///    one literal false forces the last literal (an all-false clause is a
///    conflict); the XOR engine's implied literals are enqueued (a clash with
///    the current assignment is a conflict) and its `Conflict` is a conflict.
/// 2. **Decision.** With no conflict and free variables remaining, the
///    lowest-index unassigned variable is decided `false` first, then `true` on
///    backtrack.
/// 3. **Backtrack.** Chronological: on conflict, undo to the most recent
///    decision whose other phase is untried, flip it, and continue; if none
///    remains the formula is [`XorDpllResult::Unsat`].
/// 4. **Budget.** Each propagation/decision step is counted; exceeding
///    `STEP_BUDGET` returns [`XorDpllResult::Unknown`].
///
/// Because the recovered XOR gates are clauses already in `formula`, every
/// returned [`XorDpllResult::Sat`] model satisfies both the clauses and the XOR
/// constraints (asserted in debug builds before returning).
///
/// # Panics
///
/// Does not panic in release builds. In debug builds it asserts the internal
/// invariant that a returned `Sat` model satisfies every clause and every XOR
/// constraint; that assertion holding is the module's soundness guarantee.
#[must_use]
pub fn solve_with_xor(formula: &CnfFormula) -> XorDpllResult {
    let num_vars = formula.variable_count();
    let constraints = extract_xors(formula).system.constraints();

    let mut solver = Dpll::new(formula, &constraints, num_vars);
    let result = solver.run();

    if let XorDpllResult::Sat(model) = &result {
        debug_assert!(
            model_satisfies_all(formula, &constraints, model),
            "solve_with_xor returned a Sat model violating a clause or XOR constraint"
        );
    }
    result
}

/// Returns `true` iff `model` satisfies every clause of `formula` and every XOR
/// constraint in `constraints`. The public `Sat` guarantee.
fn model_satisfies_all(
    formula: &CnfFormula,
    constraints: &[XorConstraintInput],
    model: &[bool],
) -> bool {
    if model.len() != formula.variable_count() {
        return false;
    }
    let clauses_ok = formula.evaluate(model).unwrap_or(false);
    let xors_ok = constraints.iter().all(|(vars, parity)| {
        let mut acc = false;
        for &v in vars {
            acc ^= model[v];
        }
        acc == *parity
    });
    clauses_ok && xors_ok
}

/// A trail entry: which variable was assigned, and whether it was a *decision*
/// (a guessed value whose opposite phase may still be tried on backtrack) or a
/// *propagation* (forced by a clause or the XOR engine).
struct TrailEntry {
    var: usize,
    decision: bool,
}

/// The chronological-backtracking DPLL search state.
struct Dpll<'a> {
    formula: &'a CnfFormula,
    constraints: &'a [XorConstraintInput],
    num_vars: usize,
    /// Current partial assignment, one slot per variable.
    assignment: Vec<Option<bool>>,
    /// Assignment order, for chronological undo.
    trail: Vec<TrailEntry>,
    /// Steps consumed; the budget guard against hanging.
    steps: u64,
}

/// Internal outcome of one propagation fixpoint.
enum PropagateOutcome {
    /// Propagation reached a fixpoint with no conflict.
    Ok,
    /// A clause or the XOR engine produced a conflict.
    Conflict,
    /// The step budget was exhausted mid-propagation.
    BudgetExhausted,
}

impl<'a> Dpll<'a> {
    fn new(
        formula: &'a CnfFormula,
        constraints: &'a [XorConstraintInput],
        num_vars: usize,
    ) -> Self {
        Self {
            formula,
            constraints,
            num_vars,
            assignment: vec![None; num_vars],
            trail: Vec::new(),
            steps: 0,
        }
    }

    /// Drives the DPLL loop to a verdict.
    fn run(&mut self) -> XorDpllResult {
        loop {
            match self.propagate() {
                PropagateOutcome::BudgetExhausted => return XorDpllResult::Unknown,
                PropagateOutcome::Conflict => {
                    // Chronological backtrack: undo to the last untried decision
                    // and flip it. If there is none, the formula is UNSAT.
                    if !self.backtrack() {
                        return XorDpllResult::Unsat;
                    }
                }
                PropagateOutcome::Ok => {
                    // No conflict: either fully assigned (SAT) or branch.
                    match self.first_unassigned() {
                        None => {
                            let model: Vec<bool> =
                                self.assignment.iter().map(|v| v.unwrap_or(false)).collect();
                            return XorDpllResult::Sat(model);
                        }
                        Some(var) => {
                            if self.tick() {
                                return XorDpllResult::Unknown;
                            }
                            // Decide `false` first (fixed phase order).
                            self.push(var, false, true);
                        }
                    }
                }
            }
        }
    }

    /// Counts one step; returns `true` when the budget is now exhausted.
    fn tick(&mut self) -> bool {
        self.steps += 1;
        self.steps > STEP_BUDGET
    }

    /// Assigns `var = value`, recording whether it was a decision on the trail.
    fn push(&mut self, var: usize, value: bool, decision: bool) {
        self.assignment[var] = Some(value);
        self.trail.push(TrailEntry { var, decision });
    }

    /// The lowest-index unassigned variable, if any.
    fn first_unassigned(&self) -> Option<usize> {
        self.assignment.iter().position(Option::is_none)
    }

    /// Interleaves clause unit propagation with XOR propagation to a fixpoint.
    fn propagate(&mut self) -> PropagateOutcome {
        loop {
            // (a) Clause unit propagation to its own fixpoint.
            match self.clause_propagate() {
                PropagateOutcome::Ok => {}
                other => return other,
            }

            // (b) One XOR propagation round over the current trail.
            if self.tick() {
                return PropagateOutcome::BudgetExhausted;
            }
            match xor_implications(self.constraints, self.num_vars, &self.assignment) {
                XorImplication::Conflict { .. } => return PropagateOutcome::Conflict,
                XorImplication::Implied { implied } => {
                    let mut progressed = false;
                    for imp in implied {
                        match self.assignment[imp.var] {
                            Some(existing) if existing != imp.value => {
                                // The XOR engine forces a literal the trail
                                // already contradicts: a conflict.
                                return PropagateOutcome::Conflict;
                            }
                            Some(_) => {} // already consistent; nothing to do
                            None => {
                                self.push(imp.var, imp.value, false);
                                progressed = true;
                            }
                        }
                    }
                    // If XOR added nothing new, clause UP already saw a fixpoint,
                    // so the interleaving as a whole has reached a fixpoint.
                    if !progressed {
                        return PropagateOutcome::Ok;
                    }
                }
            }
        }
    }

    /// Clause unit propagation to a fixpoint over the current assignment.
    ///
    /// A clause whose literals are all false is a conflict; a clause with
    /// exactly one unassigned literal and every other literal false forces that
    /// literal.
    fn clause_propagate(&mut self) -> PropagateOutcome {
        loop {
            if self.tick() {
                return PropagateOutcome::BudgetExhausted;
            }
            let mut forced: Option<(usize, bool)> = None;
            for clause in self.formula.clauses() {
                let mut unassigned: Option<(usize, bool)> = None;
                let mut satisfied = false;
                let mut unassigned_count = 0usize;
                for lit in clause.lits() {
                    let var = lit.var().index();
                    if let Some(value) = self.assignment[var] {
                        // Literal is true iff value matches the (un)negated
                        // polarity: a positive lit wants `true`.
                        if value != lit.is_negated() {
                            satisfied = true;
                            break;
                        }
                    } else {
                        unassigned_count += 1;
                        // The value that would satisfy this literal.
                        unassigned = Some((var, !lit.is_negated()));
                    }
                }
                if satisfied {
                    continue;
                }
                match (unassigned_count, unassigned) {
                    (0, _) => return PropagateOutcome::Conflict,
                    (1, Some(unit)) => {
                        forced = Some(unit);
                        break;
                    }
                    _ => {} // two or more unassigned: clause not yet unit
                }
            }
            match forced {
                Some((var, value)) => self.push(var, value, false),
                None => return PropagateOutcome::Ok, // clause fixpoint, no conflict
            }
        }
    }

    /// Chronological backtrack: pop the trail back to (and including) the most
    /// recent decision whose other phase is untried, flip that decision to its
    /// other phase (now a forced propagation, not a re-decision), and report
    /// `true`. Returns `false` when no untried decision remains (UNSAT).
    ///
    /// Decisions are always pushed `false` first (see [`Dpll::run`]), so the
    /// untried phase of a popped decision is always `true`. The flipped value is
    /// recorded as a propagation, not a decision, so a later conflict
    /// backtracks past it to an earlier decision.
    fn backtrack(&mut self) -> bool {
        while let Some(entry) = self.trail.pop() {
            self.assignment[entry.var] = None;
            if entry.decision {
                self.push(entry.var, true, false);
                return true;
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CnfClause, CnfLit, CnfVar, SatResult, solve_with_rustsat_batsat_timeout};
    use std::time::Duration;

    // --- formula construction helpers --------------------------------------

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

    /// Generates the complete clause set encoding `(⊕ of `vars`) = p`, in the
    /// exact form `extract_xors` recognizes (mirrors `xor_extract`'s helper).
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

    // --- oracle -------------------------------------------------------------

    /// Brute-force every assignment over `0..n` and collect the models (as
    /// bit-packed `u32`, `var_j` = bit j) satisfying every clause of `f`.
    fn brute_force_models(f: &CnfFormula) -> Vec<u32> {
        let n = f.variable_count();
        assert!(n <= 14, "brute force only intended for small formulas");
        let mut out = Vec::new();
        for assign in 0u32..(1u32 << n) {
            let values: Vec<bool> = (0..n).map(|j| (assign >> j) & 1 == 1).collect();
            if f.evaluate(&values).expect("length matches") {
                out.push(assign);
            }
        }
        out
    }

    /// Packs a `Vec<bool>` model into the same bit-packed `u32` the oracle uses.
    fn pack(model: &[bool]) -> u32 {
        let mut bits = 0u32;
        for (j, &b) in model.iter().enumerate() {
            if b {
                bits |= 1u32 << j;
            }
        }
        bits
    }

    /// Re-checks a `Sat` model against the formula's clauses and its recovered
    /// XOR constraints — the headline public invariant.
    fn assert_sat_model_valid(f: &CnfFormula, model: &[bool]) {
        let constraints = extract_xors(f).system.constraints();
        assert!(
            model_satisfies_all(f, &constraints, model),
            "Sat model {model:?} violates a clause or XOR constraint"
        );
    }

    // --- hand cases ---------------------------------------------------------

    #[test]
    fn sat_small_formula_with_xor_model_valid() {
        // A k=3 XOR gate x0 ⊕ x1 ⊕ x2 = 1 plus a unit forcing x0 = true.
        let mut clauses = xor_clauses(&[0, 1, 2], true);
        clauses.push(vec![(0, false)]);
        let f = formula(3, &clauses);
        match solve_with_xor(&f) {
            XorDpllResult::Sat(model) => {
                assert!(model[0], "x0 forced true");
                // x0 ⊕ x1 ⊕ x2 = 1 must hold.
                assert!(model[0] ^ model[1] ^ model[2]);
                assert_sat_model_valid(&f, &model);
            }
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    #[test]
    fn unsat_by_xor_system_alone() {
        // x0 ⊕ x1 = 0, x1 ⊕ x2 = 0, x0 ⊕ x2 = 1 is XOR-contradictory.
        let mut clauses = xor_clauses(&[0, 1], false);
        clauses.extend(xor_clauses(&[1, 2], false));
        clauses.extend(xor_clauses(&[0, 2], true));
        let f = formula(3, &clauses);
        assert_eq!(solve_with_xor(&f), XorDpllResult::Unsat);
        // And the clause oracle agrees there is no model.
        assert!(brute_force_models(&f).is_empty());
    }

    #[test]
    fn unsat_by_clauses_alone() {
        // x0 and ¬x0: no XOR gate, contradictory by clauses.
        let f = formula(1, &[vec![(0, false)], vec![(0, true)]]);
        assert_eq!(solve_with_xor(&f), XorDpllResult::Unsat);
    }

    #[test]
    fn sat_by_clauses_pruned_by_xor_to_specific_model() {
        // Clauses leave x0 free, but x0 ⊕ x1 = 1 and a unit x1 = false pin
        // x0 = true. The XOR gate is what forces x0.
        let mut clauses = xor_clauses(&[0, 1], true);
        clauses.push(vec![(1, true)]); // x1 = false
        let f = formula(2, &clauses);
        match solve_with_xor(&f) {
            XorDpllResult::Sat(model) => {
                assert!(!model[1], "x1 forced false");
                assert!(model[0], "x0 forced true by the XOR gate");
                assert_sat_model_valid(&f, &model);
            }
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    #[test]
    fn empty_formula_is_sat() {
        let f = CnfFormula::new(0);
        match solve_with_xor(&f) {
            XorDpllResult::Sat(model) => assert!(model.is_empty()),
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    #[test]
    fn plain_formula_no_xor_still_decides() {
        // No XOR gate present; pure clause reasoning.
        let f = formula(
            3,
            &[
                vec![(0, false), (1, false)],
                vec![(0, true), (2, false)],
                vec![(1, true), (2, true)],
            ],
        );
        match solve_with_xor(&f) {
            XorDpllResult::Sat(model) => assert_sat_model_valid(&f, &model),
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    // --- deterministic random generation ------------------------------------

    /// A tiny deterministic LCG (Numerical Recipes constants) so the random
    /// suite is reproducible with no external RNG dependency.
    struct Lcg(u64);

    impl Lcg {
        fn new(seed: u64) -> Self {
            Self(seed)
        }
        fn next_u32(&mut self) -> u32 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (self.0 >> 32) as u32
        }
        /// A value in `0..bound` (bound is small, so the modulo bias is moot for
        /// this deterministic test generator).
        fn below(&mut self, bound: usize) -> usize {
            (self.next_u32() as usize) % bound
        }
        fn coin(&mut self) -> bool {
            self.next_u32() & 1 == 1
        }
    }

    /// Builds a random small formula: a handful of random short clauses plus a
    /// few planted XOR gates (in the exact form `extract_xors` recognizes), so
    /// the XOR engine actually fires.
    fn random_formula(rng: &mut Lcg) -> CnfFormula {
        let num_vars = 3 + rng.below(11); // 3..=13 (<= 14 for brute force)
        let mut clauses: Vec<Vec<(usize, bool)>> = Vec::new();

        // A few plain random clauses of width 1..=3.
        let plain = rng.below(5); // 0..=4
        for _ in 0..plain {
            let width = 1 + rng.below(3); // 1..=3
            let mut lits = Vec::new();
            for _ in 0..width {
                let v = rng.below(num_vars);
                lits.push((v, rng.coin()));
            }
            clauses.push(lits);
        }

        // A few planted XOR gates of width 2..=3 over random variable sets.
        let gates = rng.below(3); // 0..=2
        for _ in 0..gates {
            let width = 2 + rng.below(2); // 2..=3
            // Pick `width` distinct variables.
            let mut vars: Vec<usize> = Vec::new();
            let mut guard = 0;
            while vars.len() < width && guard < 64 {
                let v = rng.below(num_vars);
                if !vars.contains(&v) {
                    vars.push(v);
                }
                guard += 1;
            }
            if vars.len() == width {
                vars.sort_unstable();
                clauses.extend(xor_clauses(&vars, rng.coin()));
            }
        }

        formula(num_vars, &clauses)
    }

    // --- the core agreement test --------------------------------------------

    #[test]
    fn brute_force_agreement_random() {
        let mut rng = Lcg::new(0x5eed_1234_abcd_0001);
        let runs = 400;
        let mut decided = 0;
        for _ in 0..runs {
            let f = random_formula(&mut rng);
            let models = brute_force_models(&f);
            match solve_with_xor(&f) {
                XorDpllResult::Sat(model) => {
                    decided += 1;
                    // The returned model must be a real model of the clause set
                    // (the ground truth), and satisfy the XOR constraints.
                    assert_sat_model_valid(&f, &model);
                    assert!(
                        models.contains(&pack(&model)),
                        "Sat model not in the oracle model set"
                    );
                }
                XorDpllResult::Unsat => {
                    decided += 1;
                    assert!(
                        models.is_empty(),
                        "decider says Unsat but the oracle found {} models",
                        models.len()
                    );
                }
                XorDpllResult::Unknown => {} // budget: skip (these tiny ones never hit it)
            }
        }
        // The instances are tiny, so the budget should never trigger.
        assert_eq!(decided, runs, "every small instance must be decided");
    }

    // --- differential vs the production solver ------------------------------

    #[test]
    fn differential_vs_batsat_random() {
        let mut rng = Lcg::new(0xabcd_0099_5eed_2222);
        let runs = 300;
        let timeout = Some(Duration::from_secs(5));
        for _ in 0..runs {
            let f = random_formula(&mut rng);
            let ours = solve_with_xor(&f);
            let theirs = solve_with_rustsat_batsat_timeout(&f, timeout)
                .expect("batsat solve must not error on a tiny formula");

            // If either side did not decide, there is nothing to cross-check.
            if matches!(ours, XorDpllResult::Unknown) || matches!(theirs, SatResult::Unknown(_)) {
                continue;
            }

            match (&ours, &theirs) {
                (XorDpllResult::Sat(model), SatResult::Sat(_)) => {
                    // Verdicts agree; our model must satisfy the formula.
                    assert!(
                        f.evaluate(model).expect("length matches"),
                        "our Sat model does not satisfy the formula"
                    );
                    assert_sat_model_valid(&f, model);
                }
                (XorDpllResult::Unsat, SatResult::Unsat(_)) => {}
                (ours, theirs) => {
                    panic!("verdict disagreement: ours={ours:?}, batsat={theirs:?}");
                }
            }
        }
    }

    // --- budget totality ----------------------------------------------------

    #[test]
    fn budget_makes_decider_total() {
        // A trivially decidable formula returns a real verdict well under budget;
        // this just exercises the public path end to end.
        let f = formula(2, &[vec![(0, false)], vec![(1, true)]]);
        assert!(matches!(solve_with_xor(&f), XorDpllResult::Sat(_)));
    }
}
