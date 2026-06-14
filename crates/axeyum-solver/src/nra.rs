//! A first nonlinear-real-arithmetic (NRA) slice by **linear abstraction +
//! replay** — the same sound relaxation pattern used for the lazy bit-vector and
//! datatype paths.
//!
//! Each genuinely nonlinear product `x·y` (a `RealMul` whose operands are *both*
//! non-constant; `c·y` stays linear) is replaced by a fresh, unconstrained real
//! variable, and the residual — now pure linear real arithmetic — is sent to the
//! LRA solver. Because the fresh variable is unconstrained, the abstraction only
//! *enlarges* the model space, so:
//!
//! - `unsat` of the abstraction ⇒ `unsat` of the original (sound): if even the
//!   relaxation has no model, neither does the original. This already decides
//!   queries where the contradiction does not need the nonlinear fact — e.g.
//!   `x·y = 5 ∧ x·y = 6` (the *same* product maps to one variable).
//! - `sat` of the abstraction is a *candidate*: it is **replayed** against the
//!   original assertions with the ground evaluator (which computes the true
//!   products), and accepted only if it genuinely satisfies them; otherwise the
//!   result is `unknown` (a refinement loop — adding `r = x·y` lemmas — is future
//!   work). So `x·y = 6 ∧ x = 2 ∧ y = 3` is `sat`, while `x·x < 0` is `unknown`
//!   (proving `x² ≥ 0` needs nonlinear reasoning this slice does not do).
//!
//! Sound in both directions; incomplete. `unknown` is first-class, never wrong.

use std::collections::{BTreeSet, HashMap};

use axeyum_ir::{IrError, Op, Sort, TermArena, TermId, TermNode, Value, eval};
use axeyum_rewrite::replace_subterms;

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::dpll_t::check_with_lra_dpll;
use crate::model::Model;

/// Decides a (possibly nonlinear) real-arithmetic query by linear abstraction of
/// nonlinear products, LRA solving, and replay.
///
/// # Errors
///
/// Returns [`SolverError`] from the rewrite or the LRA solver.
pub fn check_with_nra(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let products = nonlinear_products(arena, assertions);
    if products.is_empty() {
        // Already linear — straight to LRA.
        return check_with_lra_dpll(arena, assertions, config);
    }

    // Abstract each distinct nonlinear product with a fresh real variable,
    // recording (operand_a, operand_b, fresh_var) for the lemmas below.
    let mut map: HashMap<TermId, TermId> = HashMap::new();
    let mut triples: Vec<(TermId, TermId, TermId)> = Vec::new();
    for (i, &product) in products.iter().enumerate() {
        let TermNode::App { args, .. } = arena.node(product) else {
            continue;
        };
        let (pa, pb) = (args[0], args[1]);
        let fresh = arena
            .declare(&format!("!nra_{i}"), Sort::Real)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        let var = arena.var(fresh);
        map.insert(product, var);
        triples.push((pa, pb, var));
    }
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut reduced = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        reduced.push(
            replace_subterms(arena, assertion, &map, &mut memo)
                .map_err(|e| SolverError::Backend(e.to_string()))?,
        );
    }

    // Strengthen the relaxation with *sound* linear facts about each product
    // (sign and zero rules). These are valid for `r = a·b`, so they preserve the
    // relaxation (original models still satisfy them) while letting LRA decide
    // sign-based nonlinear queries — e.g. `x·x < 0` is now unsat (x² ≥ 0).
    for (pa, pb, r) in triples {
        for lemma in product_lemmas(arena, pa, pb, r)? {
            let rewritten = replace_subterms(arena, lemma, &map, &mut memo)
                .map_err(|e| SolverError::Backend(e.to_string()))?;
            reduced.push(rewritten);
        }
    }

    let result = check_with_lra_dpll(arena, &reduced, config)?;
    let CheckResult::Sat(model) = result else {
        // `unsat`/`unknown` transfer: the abstraction is a relaxation.
        return Ok(result);
    };

    // Replay the candidate against the original (nonlinear) assertions.
    let assignment = model.to_assignment();
    for &assertion in assertions {
        if !matches!(eval(arena, assertion, &assignment), Ok(Value::Bool(true))) {
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::Incomplete,
                detail: "nonlinear abstraction: the linear candidate does not satisfy the \
                         nonlinear constraints; refinement (r = x·y lemmas) is not implemented"
                    .to_owned(),
            }));
        }
    }

    // Build a model over the original symbols, dropping the fresh abstraction
    // variables.
    let mut out = Model::new();
    for (symbol, name, _sort) in arena.symbols() {
        if name.starts_with("!nra_") {
            continue;
        }
        if let Some(value) = assignment.get(symbol) {
            out.set(symbol, value);
        }
    }
    Ok(CheckResult::Sat(out))
}

/// Sound linear lemmas about the product `r = a·b`: the sign rules and the zero
/// rule. All are valid facts about real multiplication, so adding them keeps the
/// abstraction a relaxation (original models, with `r = a·b`, satisfy them) while
/// making it strong enough to decide sign-based nonlinear queries.
#[allow(clippy::similar_names)] // a_ge/a_le/b_ge/… mirror the sign-rule structure
fn product_lemmas(
    arena: &mut TermArena,
    a: TermId,
    b: TermId,
    r: TermId,
) -> Result<Vec<TermId>, IrError> {
    let zero = arena.real_const(axeyum_ir::Rational::integer(0));
    let a_ge = arena.real_ge(a, zero)?;
    let a_le = arena.real_le(a, zero)?;
    let b_ge = arena.real_ge(b, zero)?;
    let b_le = arena.real_le(b, zero)?;
    let r_ge = arena.real_ge(r, zero)?;
    let r_le = arena.real_le(r, zero)?;
    let a_z = arena.eq(a, zero)?;
    let b_z = arena.eq(b, zero)?;
    let r_z = arena.eq(r, zero)?;

    // implication p → q, as ¬p ∨ q.
    let imp = |arena: &mut TermArena, p: TermId, q: TermId| -> Result<TermId, IrError> {
        let np = arena.not(p)?;
        arena.or(np, q)
    };
    let mut out = Vec::new();
    // sign rules
    let pp = arena.and(a_ge, b_ge)?;
    out.push(imp(arena, pp, r_ge)?); // (a≥0 ∧ b≥0) → r≥0
    let nn = arena.and(a_le, b_le)?;
    out.push(imp(arena, nn, r_ge)?); // (a≤0 ∧ b≤0) → r≥0
    let pn = arena.and(a_ge, b_le)?;
    out.push(imp(arena, pn, r_le)?); // (a≥0 ∧ b≤0) → r≤0
    let np_ = arena.and(a_le, b_ge)?;
    out.push(imp(arena, np_, r_le)?); // (a≤0 ∧ b≥0) → r≤0
    // zero rule, both directions: r = 0 ⟺ a = 0 ∨ b = 0
    let either_z = arena.or(a_z, b_z)?;
    out.push(imp(arena, either_z, r_z)?);
    out.push(imp(arena, r_z, either_z)?);
    Ok(out)
}

/// Collects every `RealMul` subterm whose operands are both non-constant (a
/// genuinely nonlinear product; `const · term` is linear and left alone).
fn nonlinear_products(arena: &TermArena, roots: &[TermId]) -> BTreeSet<TermId> {
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
        if op == Op::RealMul && args.len() == 2 {
            let a_const = matches!(arena.node(args[0]), TermNode::RealConst(_));
            let b_const = matches!(arena.node(args[1]), TermNode::RealConst(_));
            if !a_const && !b_const {
                products.insert(term);
            }
        }
        stack.extend(args.iter().copied());
    }
    products
}
