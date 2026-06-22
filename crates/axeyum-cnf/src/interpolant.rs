//! Propositional (pure-CNF) Craig interpolation (`McMillan` 2003), read off the
//! elaborated LRAT resolution proof of `A ∧ B` (Track 3, the propositional
//! analogue of the theory interpolators in `axeyum-solver`).
//!
//! Given two CNF formulas `A` and `B` over a **shared** variable space (the same
//! [`CnfFormula::variable_count`]) whose conjunction `A ∧ B` is unsatisfiable, a
//! propositional Craig interpolant `I` is a Boolean formula over the **global**
//! (shared) variables such that:
//!
//! 1. `A ⇒ I` (equivalently `A ∧ ¬I` is unsatisfiable);
//! 2. `I ∧ B ⇒ ⊥` (equivalently `I ∧ B` is unsatisfiable);
//! 3. every variable of `I` is in `vars(A) ∩ vars(B)`.
//!
//! ## Method (`McMillan`, *Interpolation and SAT-based model checking*, 2003)
//!
//! The combined formula `A ∪ B` is refuted by the proof-producing CDCL core; its
//! DRAT proof is elaborated to LRAT, giving an explicit resolution derivation of
//! the empty clause with antecedent hints. Each clause in the derivation carries
//! a **partial interpolant** `I(c)`:
//!
//! - an **input** clause `c` from `A` contributes the disjunction of its
//!   *global* literals (`⊥` if it has none); an input clause from `B`
//!   contributes `⊤`;
//! - a **learned** (resolvent) clause folds its antecedents: replaying the
//!   forward unit propagation of the RUP hints recovers the pivot variable of
//!   each resolution; folding backward over the chain combines the antecedent
//!   partial interpolants with `∨` at an `A`-local pivot and `∧` at a global or
//!   `B`-local pivot.
//!
//! The partial interpolant of the final (empty) learned clause is the
//! interpolant.
//!
//! ## Soundness
//!
//! The fold is **untrusted**: a partial or buggy generator is acceptable because
//! every candidate is independently re-verified before return. After building a
//! candidate `I` this module re-checks all three Craig conditions — `A ∧ ¬I`
//! unsat and `I ∧ B` unsat are each decided by Tseitin-encoding the relevant
//! formula over the shared variable space and discharging it with
//! [`solve_with_drat_proof`] + [`check_drat`]; the vocabulary condition is a set
//! containment check. Any failure (or any unsupported step in the fold) declines
//! to `None` rather than returning an unverified interpolant.

use std::collections::{BTreeMap, BTreeSet};

use crate::drat::DratStep;
use crate::lrat::{LratStep, elaborate_drat_to_lrat};
use crate::proof_sat::{ProofSolveOutcome, solve_with_drat_proof};
use crate::{CnfClause, CnfFormula, CnfLit, CnfVar, check_drat};

/// A small Boolean expression over CNF variables, the carrier for a
/// propositional Craig interpolant.
///
/// Constructed by the `McMillan` fold and re-encoded to CNF (via
/// [`BoolExpr::tseitin`]) for independent verification. The smart constructors
/// [`BoolExpr::and`], [`BoolExpr::or`], and [`BoolExpr::not`] keep terms small by
/// folding the obvious constant laws, which keeps the verification cheap.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BoolExpr {
    /// The constant `true`.
    Top,
    /// The constant `false`.
    Bot,
    /// A variable occurrence.
    Var(CnfVar),
    /// Logical negation.
    Not(Box<BoolExpr>),
    /// Logical conjunction.
    And(Box<BoolExpr>, Box<BoolExpr>),
    /// Logical disjunction.
    Or(Box<BoolExpr>, Box<BoolExpr>),
}

impl BoolExpr {
    /// Smart `not`, folding `¬⊤ = ⊥`, `¬⊥ = ⊤`, and `¬¬x = x`.
    ///
    /// This intentionally shares the name of [`std::ops::Not::not`]: it is the
    /// expression-level negation constructor, taking `self` by value and folding
    /// the constant laws, not a trait implementation.
    #[must_use]
    #[allow(clippy::should_implement_trait)]
    pub fn not(self) -> Self {
        match self {
            BoolExpr::Top => BoolExpr::Bot,
            BoolExpr::Bot => BoolExpr::Top,
            BoolExpr::Not(inner) => *inner,
            other => BoolExpr::Not(Box::new(other)),
        }
    }

    /// Smart `and`, folding the constant laws `⊤ ∧ x = x`, `x ∧ ⊤ = x`,
    /// `⊥ ∧ _ = ⊥`, `_ ∧ ⊥ = ⊥`.
    #[must_use]
    pub fn and(self, other: BoolExpr) -> Self {
        match (self, other) {
            (BoolExpr::Bot, _) | (_, BoolExpr::Bot) => BoolExpr::Bot,
            (BoolExpr::Top, expr) | (expr, BoolExpr::Top) => expr,
            (lhs, rhs) => BoolExpr::And(Box::new(lhs), Box::new(rhs)),
        }
    }

    /// Smart `or`, folding the constant laws `⊥ ∨ x = x`, `x ∨ ⊥ = x`,
    /// `⊤ ∨ _ = ⊤`, `_ ∨ ⊤ = ⊤`.
    #[must_use]
    pub fn or(self, other: BoolExpr) -> Self {
        match (self, other) {
            (BoolExpr::Top, _) | (_, BoolExpr::Top) => BoolExpr::Top,
            (BoolExpr::Bot, expr) | (expr, BoolExpr::Bot) => expr,
            (lhs, rhs) => BoolExpr::Or(Box::new(lhs), Box::new(rhs)),
        }
    }

    /// Builds the expression for a single CNF literal: `Var(v)` or `¬Var(v)`.
    #[must_use]
    fn from_lit(lit: CnfLit) -> Self {
        let var = BoolExpr::Var(lit.var());
        if lit.is_negated() { var.not() } else { var }
    }

    /// The set of variables occurring in this expression.
    #[must_use]
    pub fn vars(&self) -> BTreeSet<CnfVar> {
        let mut out = BTreeSet::new();
        self.collect_vars(&mut out);
        out
    }

    fn collect_vars(&self, out: &mut BTreeSet<CnfVar>) {
        match self {
            BoolExpr::Top | BoolExpr::Bot => {}
            BoolExpr::Var(var) => {
                out.insert(*var);
            }
            BoolExpr::Not(inner) => inner.collect_vars(out),
            BoolExpr::And(lhs, rhs) | BoolExpr::Or(lhs, rhs) => {
                lhs.collect_vars(out);
                rhs.collect_vars(out);
            }
        }
    }

    /// Evaluates the expression under `assignment` (indexed by zero-based CNF
    /// variable). A variable beyond the assignment length reads as `false`.
    #[must_use]
    pub fn eval(&self, assignment: &[bool]) -> bool {
        match self {
            BoolExpr::Top => true,
            BoolExpr::Bot => false,
            BoolExpr::Var(var) => assignment.get(var.index()).copied().unwrap_or(false),
            BoolExpr::Not(inner) => !inner.eval(assignment),
            BoolExpr::And(lhs, rhs) => lhs.eval(assignment) && rhs.eval(assignment),
            BoolExpr::Or(lhs, rhs) => lhs.eval(assignment) || rhs.eval(assignment),
        }
    }

    /// Tseitin-encodes this expression into `formula`, allocating fresh
    /// variables (growing [`CnfFormula::variable_count`]) and returning a literal
    /// that is logically equivalent to the whole expression.
    ///
    /// The caller can then assert the returned literal (or its negation) by
    /// adding it as a unit clause. The defining clauses fully constrain each
    /// fresh variable, so the encoding is equisatisfiable with the expression.
    ///
    /// # Panics
    ///
    /// Panics only if the fresh-variable counter overflows the `u32` CNF variable
    /// space, which cannot happen for any realistic interpolant.
    pub fn tseitin(&self, formula: &mut CnfFormula) -> CnfLit {
        match self {
            BoolExpr::Top => {
                let lit = fresh_lit(formula);
                // Force the fresh variable true: a one-literal clause.
                add_clause(formula, vec![lit]);
                lit
            }
            BoolExpr::Bot => {
                let lit = fresh_lit(formula);
                add_clause(formula, vec![lit.negated()]);
                lit
            }
            BoolExpr::Var(var) => {
                // The variable must already be in the shared space; if not, grow.
                if var.index() >= formula.variable_count() {
                    grow_to(formula, var.index() + 1);
                }
                CnfLit::positive(*var)
            }
            BoolExpr::Not(inner) => inner.tseitin(formula).negated(),
            BoolExpr::And(lhs, rhs) => {
                let a = lhs.tseitin(formula);
                let b = rhs.tseitin(formula);
                let out = fresh_lit(formula);
                // out <-> (a ∧ b): (¬out ∨ a)(¬out ∨ b)(out ∨ ¬a ∨ ¬b).
                add_clause(formula, vec![out.negated(), a]);
                add_clause(formula, vec![out.negated(), b]);
                add_clause(formula, vec![out, a.negated(), b.negated()]);
                out
            }
            BoolExpr::Or(lhs, rhs) => {
                let a = lhs.tseitin(formula);
                let b = rhs.tseitin(formula);
                let out = fresh_lit(formula);
                // out <-> (a ∨ b): (out ∨ ¬a)(out ∨ ¬b)(¬out ∨ a ∨ b).
                add_clause(formula, vec![out, a.negated()]);
                add_clause(formula, vec![out, b.negated()]);
                add_clause(formula, vec![out.negated(), a, b]);
                out
            }
        }
    }
}

/// Grows `formula` to at least `count` variables, preserving its clauses.
fn grow_to(formula: &mut CnfFormula, count: usize) {
    if count > formula.variable_count() {
        let mut grown = CnfFormula::new(count);
        for clause in formula.clauses() {
            // Existing clauses reference only in-range variables, so this cannot
            // fail; the impossible error is ignored rather than panicked on.
            let _ = grown.add_clause(CnfClause::new(clause.lits().to_vec()));
        }
        *formula = grown;
    }
}

/// Allocates one fresh variable in `formula` and returns its positive literal.
fn fresh_lit(formula: &mut CnfFormula) -> CnfLit {
    let index = formula.variable_count();
    grow_to(formula, index + 1);
    let var = CnfVar::new(index).expect("fresh CNF variable index fits in u32");
    CnfLit::positive(var)
}

/// Adds `lits` as a clause to `formula`; the literals are in-range by
/// construction in this module, so the add never fails.
fn add_clause(formula: &mut CnfFormula, lits: Vec<CnfLit>) {
    let _ = formula.add_clause(CnfClause::new(lits));
}

/// Produces a verified propositional Craig interpolant for the unsatisfiable
/// conjunction `A ∧ B` over a shared variable space.
///
/// `a` and `b` must have the same [`CnfFormula::variable_count`] (the shared
/// space). Returns `Some(I)` with a fully re-checked interpolant Boolean
/// expression over the global (shared) variables, or `None` when `A ∧ B` is
/// satisfiable, a step of the `McMillan` fold is not supported, or the candidate
/// fails any of its three independent post-checks. It **never** returns an
/// unverified interpolant.
#[must_use]
pub fn propositional_interpolant(a: &CnfFormula, b: &CnfFormula) -> Option<BoolExpr> {
    if a.variable_count() != b.variable_count() {
        return None;
    }
    let shared_vars = a.variable_count();

    // 1. Combine: A's clauses first (ids 1..=a_len), then B's.
    let a_len = a.clauses().len();
    let mut combined = CnfFormula::new(shared_vars);
    for clause in a.clauses() {
        combined
            .add_clause(CnfClause::new(clause.lits().to_vec()))
            .ok()?;
    }
    for clause in b.clauses() {
        combined
            .add_clause(CnfClause::new(clause.lits().to_vec()))
            .ok()?;
    }

    // 2. Refute and elaborate to an LRAT resolution proof.
    let drat = match solve_with_drat_proof(&combined) {
        ProofSolveOutcome::Unsat(drat) => drat,
        // Sat / resource-out / interrupted: not a refutation we can interpolate.
        ProofSolveOutcome::Sat(_)
        | ProofSolveOutcome::ResourceOut
        | ProofSolveOutcome::Interrupted => return None,
    };
    let lrat = elaborate_drat_to_lrat(&combined, &drat).ok()?;

    // 3. Classify variables into A-local / global / B-local.
    let classes = VarClasses::new(a, b);

    // 4. Fold the McMillan partial interpolants over the LRAT proof.
    let candidate = fold_interpolant(&combined, a_len, &lrat, &classes)?;

    // 5. Independently re-verify all three Craig conditions; decline on doubt.
    if verify_interpolant(a, b, &classes, &candidate) {
        Some(candidate)
    } else {
        None
    }
}

/// Variable colouring for the partition `A ∧ B`.
struct VarClasses {
    in_a: Vec<bool>,
    in_b: Vec<bool>,
}

impl VarClasses {
    fn new(a: &CnfFormula, b: &CnfFormula) -> Self {
        let count = a.variable_count();
        let mut in_a = vec![false; count];
        let mut in_b = vec![false; count];
        for clause in a.clauses() {
            for lit in clause.lits() {
                if let Some(slot) = in_a.get_mut(lit.var().index()) {
                    *slot = true;
                }
            }
        }
        for clause in b.clauses() {
            for lit in clause.lits() {
                if let Some(slot) = in_b.get_mut(lit.var().index()) {
                    *slot = true;
                }
            }
        }
        Self { in_a, in_b }
    }

    /// A variable is global (shared) when it appears in both `A` and `B`.
    fn is_global(&self, var: CnfVar) -> bool {
        let idx = var.index();
        self.in_a.get(idx).copied().unwrap_or(false) && self.in_b.get(idx).copied().unwrap_or(false)
    }

    /// A variable is `A`-local when it appears in `A` but not in `B`.
    fn is_a_local(&self, var: CnfVar) -> bool {
        let idx = var.index();
        self.in_a.get(idx).copied().unwrap_or(false)
            && !self.in_b.get(idx).copied().unwrap_or(false)
    }
}

/// Folds the `McMillan` partial interpolants over the elaborated LRAT proof and
/// returns the partial interpolant of the derived empty clause.
fn fold_interpolant(
    combined: &CnfFormula,
    a_len: usize,
    lrat: &[LratStep],
    classes: &VarClasses,
) -> Option<BoolExpr> {
    // Partial interpolant and clause content, keyed by LRAT clause id.
    let mut partial: BTreeMap<u64, BoolExpr> = BTreeMap::new();
    let mut clause_of: BTreeMap<u64, Vec<CnfLit>> = BTreeMap::new();

    // Input clauses take ids 1..=n in combined order; A first, then B.
    for (index, clause) in combined.clauses().iter().enumerate() {
        let id = u64::try_from(index + 1).ok()?;
        let is_a = index < a_len;
        let lits = clause.lits().to_vec();
        let interp = if is_a {
            input_a_interpolant(&lits, classes)
        } else {
            BoolExpr::Top
        };
        partial.insert(id, interp);
        clause_of.insert(id, lits);
    }

    let mut last_empty: Option<u64> = None;
    for step in lrat {
        match step {
            LratStep::Delete { .. } => {
                // Deletions do not affect the interpolant fold; the partial
                // interpolants of antecedents we still need remain stored.
            }
            LratStep::Add { id, clause, hints } => {
                let interp = learned_interpolant(clause, hints, &partial, &clause_of, classes)?;
                partial.insert(*id, interp);
                clause_of.insert(*id, clause.clone());
                if clause.is_empty() {
                    last_empty = Some(*id);
                }
            }
        }
    }

    let empty_id = last_empty?;
    partial.get(&empty_id).cloned()
}

/// Partial interpolant of an `A`-side input clause: the OR of its *global*
/// literals (`⊥` when it has none).
fn input_a_interpolant(lits: &[CnfLit], classes: &VarClasses) -> BoolExpr {
    let mut acc = BoolExpr::Bot;
    for &lit in lits {
        if classes.is_global(lit.var()) {
            acc = acc.or(BoolExpr::from_lit(lit));
        }
    }
    acc
}

/// Partial interpolant of a learned (resolvent) clause.
///
/// Replays the forward unit propagation of the RUP `hints` to recover the pivot
/// variable each non-final hint propagates, then folds backward over the chain:
/// starting from the final (conflict) hint's partial interpolant, each earlier
/// hint with pivot `v` combines with `∨` when `v` is `A`-local and with `∧`
/// otherwise (global or `B`-local). The clause content is tracked through
/// resolution so the pivot lookups stay consistent.
fn learned_interpolant(
    clause: &[CnfLit],
    hints: &[u64],
    partial: &BTreeMap<u64, BoolExpr>,
    clause_of: &BTreeMap<u64, Vec<CnfLit>>,
    classes: &VarClasses,
) -> Option<BoolExpr> {
    if hints.is_empty() {
        // A tautological clause RUP-checks with no antecedents; we cannot read a
        // resolution chain off it, so decline (the verifier would anyway).
        return None;
    }

    // Forward pass: assign every literal of `clause` false, then process hints in
    // order. Each non-final hint must be unit, forcing a literal; its variable is
    // that hint's pivot. The final hint is the conflict.
    let mut assign: BTreeMap<usize, bool> = BTreeMap::new();
    for &lit in clause {
        let falsifying = lit.is_negated();
        match assign.get(&lit.var().index()) {
            // A tautological target clause: decline (cannot fold a chain).
            Some(&prev) if prev != falsifying => return None,
            _ => {
                assign.insert(lit.var().index(), falsifying);
            }
        }
    }

    // Pivot variable per hint position (`None` for the final conflict hint).
    let mut pivots: Vec<Option<CnfVar>> = Vec::with_capacity(hints.len());
    for (position, &hint_id) in hints.iter().enumerate() {
        let hinted = clause_of.get(&hint_id)?;
        let is_last = position + 1 == hints.len();
        match classify(hinted, &assign) {
            ClauseStatus::Conflict => {
                if is_last {
                    pivots.push(None);
                } else {
                    // Conflict before the chain end: malformed for our fold.
                    return None;
                }
            }
            ClauseStatus::Unit(lit) => {
                if is_last {
                    return None;
                }
                pivots.push(Some(lit.var()));
                assign.insert(lit.var().index(), !lit.is_negated());
            }
            ClauseStatus::Satisfied | ClauseStatus::Unresolved => return None,
        }
    }

    // Backward fold: start at the final hint (the conflict), then walk earlier
    // hints, resolving the running clause on each pivot and combining the partial
    // interpolants per McMillan's colouring.
    let last_id = *hints.last()?;
    let mut cur_clause = clause_of.get(&last_id)?.clone();
    let mut cur_interp = partial.get(&last_id)?.clone();

    for position in (0..hints.len() - 1).rev() {
        let hint_id = hints[position];
        let pivot = pivots[position]?;
        let h_clause = clause_of.get(&hint_id)?;
        let h_interp = partial.get(&hint_id)?;

        cur_interp = if classes.is_a_local(pivot) {
            cur_interp.or(h_interp.clone())
        } else {
            cur_interp.and(h_interp.clone())
        };
        cur_clause = resolve(&cur_clause, h_clause, pivot);
    }

    // `cur_clause` ends as the resolvent; it is unused after the final fold but
    // kept consistent through the loop so each pivot lookup is well defined.
    let _ = cur_clause;
    Some(cur_interp)
}

/// Resolves `lhs` and `rhs` on `pivot`: the union of their literals with both
/// polarities of `pivot` removed, de-duplicated.
fn resolve(lhs: &[CnfLit], rhs: &[CnfLit], pivot: CnfVar) -> Vec<CnfLit> {
    let mut seen: BTreeSet<CnfLit> = BTreeSet::new();
    let mut out = Vec::new();
    for &lit in lhs.iter().chain(rhs.iter()) {
        if lit.var() == pivot {
            continue;
        }
        if seen.insert(lit) {
            out.push(lit);
        }
    }
    out
}

/// Tri-valued status of a clause under a partial assignment (mirrors the LRAT
/// checker's classifier).
enum ClauseStatus {
    Satisfied,
    Conflict,
    Unit(CnfLit),
    Unresolved,
}

fn classify(clause: &[CnfLit], assign: &BTreeMap<usize, bool>) -> ClauseStatus {
    let mut unassigned: Option<CnfLit> = None;
    let mut unassigned_count = 0usize;
    for &lit in clause {
        if let Some(&value) = assign.get(&lit.var().index()) {
            if value != lit.is_negated() {
                return ClauseStatus::Satisfied;
            }
        } else {
            unassigned_count += 1;
            unassigned = Some(lit);
        }
    }
    match unassigned_count {
        0 => ClauseStatus::Conflict,
        1 => ClauseStatus::Unit(unassigned.expect("one unassigned literal")),
        _ => ClauseStatus::Unresolved,
    }
}

/// Independently re-checks the three Craig conditions for `candidate`.
fn verify_interpolant(
    a: &CnfFormula,
    b: &CnfFormula,
    classes: &VarClasses,
    candidate: &BoolExpr,
) -> bool {
    // Condition 3: vocabulary — every variable of I is global (shared).
    if !candidate.vars().iter().all(|&var| classes.is_global(var)) {
        return false;
    }
    // Condition 1: A ∧ ¬I unsat.
    if !unsat_with_expr(a, candidate, true) {
        return false;
    }
    // Condition 2: I ∧ B unsat.
    if !unsat_with_expr(b, candidate, false) {
        return false;
    }
    true
}

/// Decides whether `base ∧ expr` (when `negate` is `false`) or `base ∧ ¬expr`
/// (when `negate` is `true`) is unsatisfiable, by Tseitin-encoding the expression
/// over the shared variable space, asserting the (possibly negated) equivalent
/// literal, and discharging with the proof-producing core plus DRAT check.
///
/// Returns `true` only when the conjunction is proven unsat (the empty clause is
/// derived and the DRAT proof verifies). Any other outcome — sat, resource-out,
/// interrupt, or a proof that fails to verify — returns `false`, declining.
fn unsat_with_expr(base: &CnfFormula, expr: &BoolExpr, negate: bool) -> bool {
    // Start from `base` over the shared space, then grow with aux Tseitin vars.
    let mut formula = CnfFormula::new(base.variable_count());
    for clause in base.clauses() {
        if formula
            .add_clause(CnfClause::new(clause.lits().to_vec()))
            .is_err()
        {
            return false;
        }
    }
    let lit = expr.tseitin(&mut formula);
    let asserted = if negate { lit.negated() } else { lit };
    add_clause(&mut formula, vec![asserted]);

    match solve_with_drat_proof(&formula) {
        ProofSolveOutcome::Unsat(drat) => verify_drat(&formula, &drat),
        ProofSolveOutcome::Sat(_)
        | ProofSolveOutcome::ResourceOut
        | ProofSolveOutcome::Interrupted => false,
    }
}

/// Verifies a DRAT proof against `formula`, returning `true` only on a checked
/// empty-clause derivation.
fn verify_drat(formula: &CnfFormula, drat: &[DratStep]) -> bool {
    matches!(check_drat(formula, drat), Ok(true))
}
