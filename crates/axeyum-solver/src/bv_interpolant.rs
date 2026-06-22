//! Craig interpolation for `QF_BV` Boolean partitions, lifted from the verified
//! propositional interpolant of a single joint bit-blasting (Track 3, the
//! bit-vector analogue of the `QF_LRA` Farkas and `QF_UF` congruence
//! interpolators).
//!
//! Given two sets of `QF_BV` Boolean assertions `A` and `B` whose conjunction is
//! unsatisfiable, a Craig interpolant `I` is a Boolean formula over the **shared**
//! bit-vector terms such that:
//!
//! 1. `A ⇒ I` (equivalently `A ∧ ¬I` is unsatisfiable);
//! 2. `I ∧ B ⇒ ⊥` (equivalently `I ∧ B` is unsatisfiable);
//! 3. every uninterpreted symbol of `I` occurs in both `A` and `B`.
//!
//! ## Method (single joint lowering + node-indexed partition + lift)
//!
//! 1. **Joint lowering.** Bit-blast `A ++ B` together into one AIG. Structural
//!    hashing and per-`TermId` memoization collapse a shared term or symbol bit to
//!    one [`AigLit`] across both sides — a genuinely-shared bit is the *same* AIG
//!    node, hence (below) the same CNF variable.
//! 2. **Node-indexed joint CNF.** Each non-constant AIG node `n` is assigned the
//!    fixed CNF variable `index(n) - 1`, so the `A`-side and `B`-side
//!    sub-formulas live in one shared variable space *by construction* and a
//!    shared node is a *global* variable. Every AND gate `v = l ∧ r` is Tseitin-
//!    encoded (`(¬v∨l)(¬v∨r)(v∨¬l∨¬r)`) into the side(s) it is reachable from
//!    (a shared gate goes into both — sound, since the union is the original
//!    constraint set). Each assertion's root bit is asserted as a *side-private*
//!    unit clause (`A`-roots into the `A`-CNF only, `B`-roots into the `B`-CNF
//!    only); this is the one place reachability cannot decide ownership, and it is
//!    why the root assertions are partitioned by provenance instead.
//! 3. **Propositional interpolant** over the shared variable space
//!    ([`propositional_interpolant`](axeyum_cnf::propositional_interpolant)) — a
//!    [`BoolExpr`] over global (shared) variables, already re-verified at the CNF
//!    level.
//! 4. **Lift** each `BoolExpr::Var(v)` (a shared AIG node) to the bit-vector
//!    predicate "bit `i` of term `t` is 1", recovered from the lowering's term-bit
//!    map (preferring a symbol-leaf bit). Only shared-term bits are accepted; a
//!    variable that maps to no shared-term bit declines the whole lift.
//!
//! ## Soundness
//!
//! The lowering, partition, and lift are **untrusted**. After building a candidate
//! `I` this module independently re-checks all three Craig conditions with the
//! `QF_BV` decider ([`check_auto`](crate::check_auto)) — `A ∧ ¬I` unsat, `I ∧ B`
//! unsat, and the shared-vocabulary containment — and returns `Some(I)` only when
//! all pass. Any other outcome (`Sat`/`Unknown`/error, an unsupported lift step,
//! or a non-shared variable) declines to `None` rather than returning an
//! unverified interpolant.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_aig::{AigLit, AigNode};
use axeyum_bv::{BitLowering, lower_terms};
use axeyum_cnf::{
    BoolExpr, CnfClause, CnfFormula, CnfLit, CnfVar, propositional_interpolant, reachable_node_mask,
};
use axeyum_ir::{Sort, SymbolId, TermArena, TermId, TermNode};

use crate::{CheckResult, SolverConfig, check_auto};

/// Produces a verified `QF_BV` Craig interpolant for the unsatisfiable
/// conjunction `A ∧ B`, where `a_assertions` is `A` and `b_assertions` is `B`
/// (each a set of `QF_BV` Boolean assertions, interpreted conjunctively).
///
/// Returns `Some(I)` with a fully re-checked interpolant term `I` — a Boolean
/// `TermId` over shared bit-vector terms — or `None` when `A ∧ B` is satisfiable,
/// when any lowering / partition / lift step cannot be completed, or when the
/// candidate fails any of its three independent post-checks. It **never** returns
/// an unverified interpolant.
#[must_use]
pub fn qf_bv_interpolant(
    arena: &mut TermArena,
    a_assertions: &[TermId],
    b_assertions: &[TermId],
) -> Option<TermId> {
    if a_assertions.is_empty() || b_assertions.is_empty() {
        return None;
    }

    // Decline cleanly on any non-`QF_BV` input. `lower_terms` *panics* (an
    // `unreachable!` in `axeyum-bv`) on real/int-sorted terms rather than
    // returning `Err`, so a sort pre-check is required to keep this total
    // ("graceful unknown, never crash" — the dispatch may hand us a real/int
    // partition that earlier theories declined).
    if a_assertions
        .iter()
        .chain(b_assertions)
        .any(|&t| !is_bv_lowerable(arena, t, &mut BTreeSet::new()))
    {
        return None;
    }

    // 1. Joint lowering of A ++ B. Structural hashing + memoization collapse a
    //    shared term/symbol bit to one AigLit across both sides.
    let mut combined = Vec::with_capacity(a_assertions.len() + b_assertions.len());
    combined.extend_from_slice(a_assertions);
    combined.extend_from_slice(b_assertions);
    let a_len = a_assertions.len();
    let lowering = lower_terms(arena, &combined).ok()?;
    let aig = lowering.aig();

    // Each assertion's Boolean root bit (Bool roots lower to a single bit).
    let mut root_bits = Vec::with_capacity(combined.len());
    for root in lowering.roots() {
        let bits = root.bits();
        if bits.len() != 1 {
            return None; // a non-Boolean root cannot be an assertion.
        }
        root_bits.push(bits[0]);
    }
    let (a_roots, b_roots) = root_bits.split_at(a_len);

    // 2. Node-indexed joint CNF over a shared variable space (var = node - 1).
    let shared_var_count = aig.node_count().checked_sub(1)?;
    let a_reach = reachable_node_mask(aig, a_roots);
    let b_reach = reachable_node_mask(aig, b_roots);

    let mut a_cnf = CnfFormula::new(shared_var_count);
    let mut b_cnf = CnfFormula::new(shared_var_count);

    // Gate clauses: each reachable AND node, into the side(s) it is reachable from.
    for (node_id, node) in aig.nodes() {
        let idx = node_id.index();
        if idx == 0 {
            continue; // constant-false node has no variable.
        }
        let AigNode::And(lhs, rhs) = node else {
            continue; // inputs need no defining clauses.
        };
        let to_a = a_reach.get(idx).copied().unwrap_or(false);
        let to_b = b_reach.get(idx).copied().unwrap_or(false);
        if !to_a && !to_b {
            continue;
        }
        let out = CnfLit::positive(node_var(node_id.index())?);
        for clause in tseitin_and_clauses(out, lhs, rhs) {
            let Some(clause) = clause else {
                continue;
            };
            if to_a {
                a_cnf.add_clause(CnfClause::new(clause.clone())).ok()?;
            }
            if to_b {
                b_cnf.add_clause(CnfClause::new(clause)).ok()?;
            }
        }
    }

    // Root assertions: side-private unit clauses (this is the provenance the
    // reachability test cannot recover, so it is partitioned explicitly).
    for &root in a_roots {
        assert_root(&mut a_cnf, root)?;
    }
    for &root in b_roots {
        assert_root(&mut b_cnf, root)?;
    }

    debug_assert_eq!(a_cnf.variable_count(), b_cnf.variable_count());

    // 3. Verified propositional interpolant over the shared variable space.
    let prop = propositional_interpolant(&a_cnf, &b_cnf)?;

    // 4. Lift BoolExpr -> a Boolean TermId over shared bit-vector terms.
    let lift = LiftTable::build(arena, &lowering, a_assertions, b_assertions);
    let interpolant = lift.lower_expr(arena, &prop)?;

    // 5. Independently re-verify the three Craig conditions. Decline on any doubt.
    if verify_interpolant(arena, a_assertions, b_assertions, interpolant) {
        Some(interpolant)
    } else {
        None
    }
}

/// The CNF variable for a non-constant AIG node index (`node - 1`).
fn node_var(node_index: usize) -> Option<CnfVar> {
    CnfVar::new(node_index.checked_sub(1)?).ok()
}

/// Maps one AIG literal to a CNF literal over the node-indexed variable space.
/// Constant literals (node 0) have no variable and are reported as `Const`.
enum LitMap {
    Const(bool),
    Lit(CnfLit),
}

fn map_lit(lit: AigLit) -> Option<LitMap> {
    if lit.node().index() == 0 {
        // node 0 is constant false; the inverted literal is constant true.
        return Some(LitMap::Const(lit.is_inverted()));
    }
    let var = node_var(lit.node().index())?;
    let cnf = CnfLit::positive(var);
    Some(LitMap::Lit(if lit.is_inverted() {
        cnf.negated()
    } else {
        cnf
    }))
}

/// Tseitin clauses for `out ↔ (lhs ∧ rhs)`:
/// `(¬out ∨ lhs)`, `(¬out ∨ rhs)`, `(out ∨ ¬lhs ∨ ¬rhs)`, simplified for any
/// constant child. A returned `None` clause is a tautology (dropped); a clause
/// reduced to empty is kept (it correctly forces `out`).
fn tseitin_and_clauses(out: CnfLit, lhs: AigLit, rhs: AigLit) -> [Option<Vec<CnfLit>>; 3] {
    let lhs = map_lit(lhs);
    let rhs = map_lit(rhs);
    // If a child mapping failed (out-of-range), drop all three — the gate is left
    // unconstrained, which the final verify-guard catches as a decline if it ever
    // mattered. In practice every reachable child node has a variable.
    let (Some(lhs), Some(rhs)) = (lhs, rhs) else {
        return [None, None, None];
    };

    // (¬out ∨ lhs)
    let c1 = match &lhs {
        LitMap::Const(true) => None,                       // tautology
        LitMap::Const(false) => Some(vec![out.negated()]), // ¬out
        LitMap::Lit(l) => Some(vec![out.negated(), *l]),
    };
    // (¬out ∨ rhs)
    let c2 = match &rhs {
        LitMap::Const(true) => None,
        LitMap::Const(false) => Some(vec![out.negated()]),
        LitMap::Lit(r) => Some(vec![out.negated(), *r]),
    };
    // (out ∨ ¬lhs ∨ ¬rhs)
    let c3 = match (&lhs, &rhs) {
        (LitMap::Const(false), _) | (_, LitMap::Const(false)) => None, // ¬false = true: tautology
        (LitMap::Const(true), LitMap::Const(true)) => Some(vec![out]),
        (LitMap::Const(true), LitMap::Lit(r)) => Some(vec![out, r.negated()]),
        (LitMap::Lit(l), LitMap::Const(true)) => Some(vec![out, l.negated()]),
        (LitMap::Lit(l), LitMap::Lit(r)) => Some(vec![out, l.negated(), r.negated()]),
    };
    [c1, c2, c3]
}

/// Asserts the root literal `root` as a side-private clause in `formula`.
///
/// A non-constant root becomes the unit clause `[root]`. A constant-true root is
/// vacuous (no clause). A constant-false root adds the empty clause (the side is
/// then trivially unsatisfiable, which is sound).
fn assert_root(formula: &mut CnfFormula, root: AigLit) -> Option<()> {
    match map_lit(root)? {
        LitMap::Const(true) => Some(()),
        LitMap::Const(false) => formula.add_clause(CnfClause::new(Vec::new())).ok(),
        LitMap::Lit(lit) => formula.add_clause(CnfClause::new(vec![lit])).ok(),
    }
}

/// One lifted predicate: bit `bit_index` of `term` equals 1, optionally negated
/// (when the term bit's AIG literal is inverted relative to the node variable's
/// positive polarity).
#[derive(Debug, Clone, Copy)]
struct BitPredicate {
    term: TermId,
    bit_index: u32,
    invert: bool,
}

/// Maps each shared-space CNF variable (an AIG node) to a bit-vector predicate
/// over a **shared** term, for lifting a propositional [`BoolExpr`] back to the
/// typed IR.
struct LiftTable {
    /// CNF-variable index -> the predicate, present only for shared-term bits.
    by_var: BTreeMap<usize, BitPredicate>,
}

impl LiftTable {
    fn build(
        arena: &TermArena,
        lowering: &BitLowering,
        a_assertions: &[TermId],
        b_assertions: &[TermId],
    ) -> Self {
        let a_terms = subterms_of(arena, a_assertions);
        let b_terms = subterms_of(arena, b_assertions);
        let is_shared = |term: TermId| a_terms.contains(&term) && b_terms.contains(&term);

        // AIG node index -> a candidate predicate over a SHARED term. Symbol-leaf
        // bits are preferred over interior term bits (the cleanest shared
        // vocabulary); among candidates of the same rank, the first shared one
        // wins. `invert` records whether the term bit's AIG literal is inverted,
        // so the positive node variable matches the right polarity.
        let mut node_pred: BTreeMap<usize, BitPredicate> = BTreeMap::new();

        // Pass 1: shared symbol-leaf bits (a symbol's term is recorded as a
        // term-bit binding with the interned leaf handle).
        for binding in lowering.term_bits() {
            if !matches!(arena.node(binding.term), TermNode::Symbol(_)) {
                continue;
            }
            if !is_shared(binding.term) {
                continue;
            }
            node_pred
                .entry(binding.literal.node().index())
                .or_insert(BitPredicate {
                    term: binding.term,
                    bit_index: binding.bit_index,
                    invert: binding.literal.is_inverted(),
                });
        }

        // Pass 2: any other shared-term bit, filling nodes not already covered.
        for binding in lowering.term_bits() {
            if !is_shared(binding.term) {
                continue;
            }
            node_pred
                .entry(binding.literal.node().index())
                .or_insert(BitPredicate {
                    term: binding.term,
                    bit_index: binding.bit_index,
                    invert: binding.literal.is_inverted(),
                });
        }

        // CNF variable `v` corresponds to AIG node `v + 1`.
        let mut by_var = BTreeMap::new();
        for (&node, &pred) in &node_pred {
            if let Some(var_index) = node.checked_sub(1) {
                by_var.insert(var_index, pred);
            }
        }

        Self { by_var }
    }

    /// Lowers a propositional [`BoolExpr`] over shared variables into a Boolean
    /// `TermId`. Returns `None` if a variable maps to no shared-term bit or any
    /// term-builder step fails.
    fn lower_expr(&self, arena: &mut TermArena, expr: &BoolExpr) -> Option<TermId> {
        match expr {
            BoolExpr::Top => Some(arena.bool_const(true)),
            BoolExpr::Bot => Some(arena.bool_const(false)),
            BoolExpr::Var(var) => self.lower_var(arena, *var),
            BoolExpr::Not(inner) => {
                let t = self.lower_expr(arena, inner)?;
                arena.not(t).ok()
            }
            BoolExpr::And(lhs, rhs) => {
                let l = self.lower_expr(arena, lhs)?;
                let r = self.lower_expr(arena, rhs)?;
                arena.and(l, r).ok()
            }
            BoolExpr::Or(lhs, rhs) => {
                let l = self.lower_expr(arena, lhs)?;
                let r = self.lower_expr(arena, rhs)?;
                arena.or(l, r).ok()
            }
        }
    }

    /// Lowers a single global variable to its shared-term bit predicate.
    fn lower_var(&self, arena: &mut TermArena, var: CnfVar) -> Option<TermId> {
        let pred = self.by_var.get(&var.index())?;
        let atom = bit_is_one(arena, pred.term, pred.bit_index)?;
        if pred.invert {
            arena.not(atom).ok()
        } else {
            Some(atom)
        }
    }
}

/// Builds the Boolean atom "bit `bit_index` of `term` is 1".
///
/// For a `Bool` term (bit 0) the term is itself the predicate. For a `BitVec`
/// term it is `extract(bit, bit, term) == #b1`.
fn bit_is_one(arena: &mut TermArena, term: TermId, bit_index: u32) -> Option<TermId> {
    match arena.sort_of(term) {
        Sort::Bool => {
            if bit_index == 0 {
                Some(term)
            } else {
                None
            }
        }
        Sort::BitVec(width) => {
            if bit_index >= width {
                return None;
            }
            let bit = arena.extract(bit_index, bit_index, term).ok()?;
            let one = arena.bv_const(1, 1).ok()?;
            arena.eq(bit, one).ok()
        }
        _ => None,
    }
}

/// Re-checks the three Craig conditions for `interpolant` over `(A, B)` with the
/// independent `QF_BV` decider. Returns `true` iff all hold.
fn verify_interpolant(
    arena: &mut TermArena,
    a_assertions: &[TermId],
    b_assertions: &[TermId],
    interpolant: TermId,
) -> bool {
    // (3) Vocabulary: every uninterpreted symbol of I occurs in both A and B.
    let a_symbols = symbols_of(arena, a_assertions);
    let b_symbols = symbols_of(arena, b_assertions);
    let i_symbols = symbols_of(arena, std::slice::from_ref(&interpolant));
    if !i_symbols
        .iter()
        .all(|s| a_symbols.contains(s) && b_symbols.contains(s))
    {
        return false;
    }

    let config = SolverConfig::default();

    // (1) A ⇒ I  ≡  A ∧ ¬I unsat.
    let Ok(not_i) = arena.not(interpolant) else {
        return false;
    };
    let mut a_not_i = a_assertions.to_vec();
    a_not_i.push(not_i);
    if !matches!(check_auto(arena, &a_not_i, &config), Ok(CheckResult::Unsat)) {
        return false;
    }

    // (2) I ∧ B unsat.
    let mut i_and_b = Vec::with_capacity(b_assertions.len() + 1);
    i_and_b.push(interpolant);
    i_and_b.extend_from_slice(b_assertions);
    matches!(check_auto(arena, &i_and_b, &config), Ok(CheckResult::Unsat))
}

/// Collects every free symbol appearing in any of `terms`.
fn symbols_of(arena: &TermArena, terms: &[TermId]) -> BTreeSet<SymbolId> {
    let mut out = BTreeSet::new();
    let mut seen = BTreeSet::new();
    for &term in terms {
        collect_symbols(arena, term, &mut out, &mut seen);
    }
    out
}

fn collect_symbols(
    arena: &TermArena,
    term: TermId,
    out: &mut BTreeSet<SymbolId>,
    seen: &mut BTreeSet<TermId>,
) {
    if !seen.insert(term) {
        return;
    }
    match arena.node(term) {
        TermNode::Symbol(symbol) => {
            out.insert(*symbol);
        }
        TermNode::App { args, .. } => {
            for &arg in args {
                collect_symbols(arena, arg, out, seen);
            }
        }
        _ => {}
    }
}

/// Collects every subterm `TermId` appearing in a set of terms.
fn subterms_of(arena: &TermArena, terms: &[TermId]) -> BTreeSet<TermId> {
    let mut out = BTreeSet::new();
    for &term in terms {
        collect_subterms(arena, term, &mut out);
    }
    out
}

fn collect_subterms(arena: &TermArena, term: TermId, out: &mut BTreeSet<TermId>) {
    if !out.insert(term) {
        return;
    }
    if let TermNode::App { args, .. } = arena.node(term) {
        for &arg in args {
            collect_subterms(arena, arg, out);
        }
    }
}

/// Whether `term` and all its subterms are bit-lowerable — every sort is `Bool`
/// or `BitVec`. `lower_terms` panics (an `unreachable!` in `axeyum-bv`) on
/// real/int (and other non-`QF_BV`) terms rather than returning `Err`, so the
/// `QF_BV` interpolant pre-filters with this to stay total (decline, never crash).
fn is_bv_lowerable(arena: &TermArena, term: TermId, seen: &mut BTreeSet<TermId>) -> bool {
    if !seen.insert(term) {
        return true;
    }
    if !matches!(arena.sort_of(term), Sort::Bool | Sort::BitVec(_)) {
        return false;
    }
    if let TermNode::App { args, .. } = arena.node(term) {
        return args.iter().all(|&arg| is_bv_lowerable(arena, arg, seen));
    }
    true
}
