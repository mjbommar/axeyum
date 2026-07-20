//! Checked refutation for an exact nested-XOR integer universal (ADR-0099).
//!
//! The supported theorem is
//!
//! ```text
//! forall a b.
//!   xor (xor (a = pa) (b = pb))
//!       (forall c.
//!         ite(a = pa, t, e) = ite(c = pc, t, e))
//! ```
//!
//! for integer constants `pa`, `pb`, `pc`, `t`, and `e` with `t != e`.
//! Instantiating `a := pa` and `b := pb` makes the first XOR false, so the
//! assertion entails the nested universal. Instantiating `c` away from `pc`
//! then forces the false equality `t = e`.

use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode};

use crate::term_walk::collect_top_binary_conjuncts as collect_top_conjuncts;

/// A self-checking refutation of the exact nested-XOR theorem in ADR-0099.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IntNestedXorRefutationCertificate {
    /// The original top-level universal assertion.
    pub assertion: TermId,
    /// The outer binder used by the nested selector.
    pub active: SymbolId,
    /// The other outer binder.
    pub passive: SymbolId,
    /// The direct nested universal binder.
    pub nested: SymbolId,
    /// The selector pivot for `active`.
    pub active_pivot: i128,
    /// The selector pivot for `passive`.
    pub passive_pivot: i128,
    /// The selector pivot for `nested`.
    pub nested_pivot: i128,
    /// The common then-branch integer constant.
    pub then_value: i128,
    /// The distinct common else-branch integer constant.
    pub else_value: i128,
}

/// Returns a certificate when the assertions contain the exact false universal
/// described by [`IntNestedXorRefutationCertificate`].
///
/// The matcher independently scans the original arena and accepts only two
/// outer integer binders, one direct nested integer binder, exact binary XORs,
/// and matching constant-valued selectors. Other top-level conjuncts are
/// irrelevant once this false universal is present.
#[must_use]
pub fn int_nested_xor_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<IntNestedXorRefutationCertificate> {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        collect_top_conjuncts(arena, assertion, &mut conjuncts);
    }
    conjuncts
        .into_iter()
        .find_map(|assertion| match_nested_xor_universal(arena, assertion))
}

fn match_nested_xor_universal(
    arena: &TermArena,
    assertion: TermId,
) -> Option<IntNestedXorRefutationCertificate> {
    let (outer, body) = peel_foralls(arena, assertion)?;
    if outer.len() != 2
        || outer[0] == outer[1]
        || outer.iter().any(|&var| arena.symbol(var).1 != Sort::Int)
    {
        return None;
    }

    let (selector, nested_quantifier) = split_outer_xor(arena, body)?;
    let selector_pivots = match_selector_xor(arena, selector, &outer)?;
    let (nested, nested_body) = as_forall(arena, nested_quantifier)?;
    if outer.contains(&nested) || arena.symbol(nested).1 != Sort::Int {
        return None;
    }

    let selector = match_nested_selector_equality(arena, nested_body, &outer, nested)?;
    let active_pivot = selector_pivots
        .iter()
        .find_map(|&(var, pivot)| (var == selector.active).then_some(pivot))?;
    if active_pivot != selector.active_pivot {
        return None;
    }
    let (passive, passive_pivot) = selector_pivots
        .iter()
        .find_map(|&(var, pivot)| (var != selector.active).then_some((var, pivot)))?;

    Some(IntNestedXorRefutationCertificate {
        assertion,
        active: selector.active,
        passive,
        nested,
        active_pivot,
        passive_pivot,
        nested_pivot: selector.nested_pivot,
        then_value: selector.then_value,
        else_value: selector.else_value,
    })
}

#[derive(Clone, Copy)]
struct NestedSelector {
    active: SymbolId,
    active_pivot: i128,
    nested_pivot: i128,
    then_value: i128,
    else_value: i128,
}

fn match_nested_selector_equality(
    arena: &TermArena,
    term: TermId,
    outer: &[SymbolId],
    nested: SymbolId,
) -> Option<NestedSelector> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    match_selector_ites(arena, *left, *right, outer, nested)
        .or_else(|| match_selector_ites(arena, *right, *left, outer, nested))
}

fn match_selector_ites(
    arena: &TermArena,
    active_ite: TermId,
    nested_ite: TermId,
    outer: &[SymbolId],
    nested: SymbolId,
) -> Option<NestedSelector> {
    let (active_guard, active_then, active_else) = as_ite(arena, active_ite)?;
    let (nested_guard, nested_then, nested_else) = as_ite(arena, nested_ite)?;
    let (active, active_pivot) = match_symbol_int_equality(arena, active_guard)?;
    if !outer.contains(&active) {
        return None;
    }
    let (found_nested, nested_pivot) = match_symbol_int_equality(arena, nested_guard)?;
    if found_nested != nested {
        return None;
    }
    let then_value = as_int_const(arena, active_then)?;
    let else_value = as_int_const(arena, active_else)?;
    if then_value == else_value
        || as_int_const(arena, nested_then) != Some(then_value)
        || as_int_const(arena, nested_else) != Some(else_value)
    {
        return None;
    }
    Some(NestedSelector {
        active,
        active_pivot,
        nested_pivot,
        then_value,
        else_value,
    })
}

fn split_outer_xor(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let TermNode::App {
        op: Op::BoolXor,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    if as_forall(arena, *right).is_some() && as_forall(arena, *left).is_none() {
        Some((*left, *right))
    } else if as_forall(arena, *left).is_some() && as_forall(arena, *right).is_none() {
        Some((*right, *left))
    } else {
        None
    }
}

fn match_selector_xor(
    arena: &TermArena,
    term: TermId,
    outer: &[SymbolId],
) -> Option<[(SymbolId, i128); 2]> {
    let TermNode::App {
        op: Op::BoolXor,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    let first = match_symbol_int_equality(arena, *left)?;
    let second = match_symbol_int_equality(arena, *right)?;
    if first.0 == second.0 || !outer.contains(&first.0) || !outer.contains(&second.0) {
        return None;
    }
    Some([first, second])
}

fn match_symbol_int_equality(arena: &TermArena, term: TermId) -> Option<(SymbolId, i128)> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    match (arena.node(*left), arena.node(*right)) {
        (TermNode::Symbol(symbol), _) => Some((*symbol, as_int_const(arena, *right)?)),
        (_, TermNode::Symbol(symbol)) => Some((*symbol, as_int_const(arena, *left)?)),
        _ => None,
    }
}

fn as_ite(arena: &TermArena, term: TermId) -> Option<(TermId, TermId, TermId)> {
    let TermNode::App { op: Op::Ite, args } = arena.node(term) else {
        return None;
    };
    let [condition, then_value, else_value] = &**args else {
        return None;
    };
    Some((*condition, *then_value, *else_value))
}

fn as_int_const(arena: &TermArena, term: TermId) -> Option<i128> {
    match arena.node(term) {
        TermNode::IntConst(value) => Some(*value),
        TermNode::App {
            op: Op::IntNeg,
            args,
        } => {
            let [inner] = &**args else {
                return None;
            };
            match arena.node(*inner) {
                TermNode::IntConst(value) => value.checked_neg(),
                _ => None,
            }
        }
        _ => None,
    }
}

fn peel_foralls(arena: &TermArena, mut term: TermId) -> Option<(Vec<SymbolId>, TermId)> {
    let mut vars = Vec::new();
    while let Some((var, body)) = as_forall(arena, term) {
        vars.push(var);
        term = body;
    }
    (!vars.is_empty()).then_some((vars, term))
}

fn as_forall(arena: &TermArena, term: TermId) -> Option<(SymbolId, TermId)> {
    let TermNode::App {
        op: Op::Forall(var),
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [body] = &**args else {
        return None;
    };
    Some((*var, *body))
}
