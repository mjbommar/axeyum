//! Phase E first slice (P2.5): integer nonlinear **UNSAT** refutation via product
//! abstraction + valid integer sign lemmas, solved over the integer DPLL(T).
//!
//! Abstracts each integer product `a·b` (both operands non-constant) to a fresh
//! `Int` variable `r`, adds the valid integer sign/zero lemmas relating `r` to `a`
//! and `b`, and solves the relaxation with [`crate::dpll_lia::check_with_lia_dpll`].
//! An `unsat` of the relaxation transfers to the original — the abstraction only
//! enlarges the model space and every lemma is a valid consequence of `r = a·b` —
//! so this is a **sound refuter**: it returns `Unsat` or declines (`None`), never
//! `sat`.
//!
//! Unlike the real relaxation (`int_real_relax` → `check_with_nra`), it keeps
//! **integrality**, so integer bound tightening (`q < 1 ⟹ q ≤ 0`, valid only over
//! ℤ) combines with a sign lemma (`q ≤ 0 ∧ n ≥ 0 ⟹ q·n ≤ 0`) to refute e.g. the
//! Euclidean-eliminated `div.03` (`n>0 ∧ x≥n ∧ q<1 ∧ x=q·n+r ∧ 0≤r<n`), which is
//! unsat over ℤ but *sat over ℝ* (so the real relaxation cannot refute it).

use std::collections::{BTreeSet, HashMap};

use axeyum_ir::{IrError, Op, Sort, TermArena, TermId, TermNode};
use axeyum_rewrite::replace_subterms;

use crate::backend::{CheckResult, SolverConfig, SolverError};
use crate::dpll_lia::check_with_lia_dpll;

/// Distinct integer products `a·b` reachable from `roots`, with both operands
/// non-constant (a `const·term` is linear and not abstracted).
fn int_products(arena: &TermArena, roots: &[TermId]) -> BTreeSet<TermId> {
    let mut products = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        let TermNode::App { op, args } = arena.node(term) else {
            continue;
        };
        let op = *op;
        let args = args.clone();
        if op == Op::IntMul && args.len() == 2 {
            let a_const = matches!(arena.node(args[0]), TermNode::IntConst(_));
            let b_const = matches!(arena.node(args[1]), TermNode::IntConst(_));
            if !a_const && !b_const {
                products.insert(term);
            }
        }
        stack.extend(args);
    }
    products
}

/// The valid integer sign/zero lemmas for `r = a·b` (each is a consequence of the
/// abstracted equality, so adding them only restricts the relaxation's models).
fn sign_lemmas(
    arena: &mut TermArena,
    a: TermId,
    b: TermId,
    r: TermId,
    zero: TermId,
) -> Result<Vec<TermId>, SolverError> {
    let err = |e: IrError| SolverError::Backend(e.to_string());
    let a_nonneg = arena.int_ge(a, zero).map_err(err)?;
    let a_nonpos = arena.int_le(a, zero).map_err(err)?;
    let b_nonneg = arena.int_ge(b, zero).map_err(err)?;
    let b_nonpos = arena.int_le(b, zero).map_err(err)?;
    let prod_nonneg = arena.int_ge(r, zero).map_err(err)?;
    let prod_nonpos = arena.int_le(r, zero).map_err(err)?;
    let a_zero = arena.eq(a, zero).map_err(err)?;
    let b_zero = arena.eq(b, zero).map_err(err)?;
    let prod_zero = arena.eq(r, zero).map_err(err)?;

    let mut out = Vec::with_capacity(6);
    // (a≥0 ∧ b≥0) → r≥0 ; (a≤0 ∧ b≤0) → r≥0
    let p = arena.and(a_nonneg, b_nonneg).map_err(err)?;
    out.push(arena.implies(p, prod_nonneg).map_err(err)?);
    let p = arena.and(a_nonpos, b_nonpos).map_err(err)?;
    out.push(arena.implies(p, prod_nonneg).map_err(err)?);
    // (a≥0 ∧ b≤0) → r≤0 ; (a≤0 ∧ b≥0) → r≤0
    let p = arena.and(a_nonneg, b_nonpos).map_err(err)?;
    out.push(arena.implies(p, prod_nonpos).map_err(err)?);
    let p = arena.and(a_nonpos, b_nonneg).map_err(err)?;
    out.push(arena.implies(p, prod_nonpos).map_err(err)?);
    // a=0 → r=0 ; b=0 → r=0 (the two easy halves of `r=0 ⟺ a=0 ∨ b=0`)
    out.push(arena.implies(a_zero, prod_zero).map_err(err)?);
    out.push(arena.implies(b_zero, prod_zero).map_err(err)?);
    Ok(out)
}

/// Sound integer-nonlinear **UNSAT** refuter (Phase E first slice). Returns
/// `Some(Unsat)` when the sign-lemma-augmented integer relaxation is unsatisfiable
/// (which transfers to the original), or `None` (declines) — never `sat`.
///
/// # Errors
///
/// Propagates [`SolverError`] from term construction or the integer solver.
pub fn refute_nia_by_sign_lemmas(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<CheckResult>, SolverError> {
    let products = int_products(arena, assertions);
    if products.is_empty() {
        return Ok(None);
    }
    let err = |e: IrError| SolverError::Backend(e.to_string());
    let zero = arena.int_const(0);

    // Abstract each product to a fresh `Int` var, recording `(a, b, r)`.
    let mut map: HashMap<TermId, TermId> = HashMap::new();
    let mut triples: Vec<(TermId, TermId, TermId)> = Vec::new();
    for (i, &product) in products.iter().enumerate() {
        let TermNode::App { args, .. } = arena.node(product) else {
            continue;
        };
        let (a, b) = (args[0], args[1]);
        let fresh = arena
            .declare(&format!("!nia_{i}"), Sort::Int)
            .map_err(err)?;
        let r = arena.var(fresh);
        map.insert(product, r);
        triples.push((a, b, r));
    }

    // Relaxation = the assertions with products replaced by their fresh vars, plus
    // the valid sign lemmas (with nested products in `a`/`b` likewise replaced).
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut relaxed: Vec<TermId> = Vec::with_capacity(assertions.len() + triples.len() * 6);
    for &a in assertions {
        relaxed.push(replace_subterms(arena, a, &map, &mut memo).map_err(err)?);
    }
    for &(a, b, r) in &triples {
        let a = replace_subterms(arena, a, &map, &mut memo).map_err(err)?;
        let b = replace_subterms(arena, b, &map, &mut memo).map_err(err)?;
        relaxed.extend(sign_lemmas(arena, a, b, r, zero)?);
    }

    // `unsat` of the (relaxation + valid lemmas) transfers soundly to the original.
    // A `sat`/`unknown` of the relaxation says nothing about the original (the
    // abstraction dropped the exact product equalities), so we decline. This is a
    // best-effort *refuter*: any solver error (e.g. the integer DPLL rejecting an
    // augmented shape) is also a decline — we never propagate an error out of a
    // path whose only job is to opportunistically turn `unknown` into `unsat`.
    match check_with_lia_dpll(arena, &relaxed, config) {
        Ok(CheckResult::Unsat) => Ok(Some(CheckResult::Unsat)),
        Ok(_) | Err(_) => Ok(None),
    }
}
