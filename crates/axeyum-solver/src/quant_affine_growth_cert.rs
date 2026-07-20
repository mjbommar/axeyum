//! Checked refutation for an exact positive-slope piecewise integer universal.
//!
//! For a positive integer constant `c`, consider
//!
//! ```text
//! forall xs. not (c*x - ite(x = p, a, b) >= t)
//! ```
//!
//! where `x` is one of the binders and `p`, `a`, `b`, and `t` contain no bound
//! variable. Let `q = div(b + t, c) + 1`. Both `q` and `q + 1` make
//! `c*x - b >= t`; at most one equals `p`, so the other selects the else branch
//! and falsifies the universal. This module independently re-matches that exact
//! theorem over original IR. It does not call the instantiation search.

use std::collections::BTreeSet;

use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode};

use crate::term_walk::collect_top_binary_conjuncts as collect_top_conjuncts;

/// A self-checking refutation of an exact affine-growth universal (ADR-0097).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IntAffineGrowthRefutationCertificate {
    /// The original universal assertion.
    pub assertion: TermId,
    /// The positive-slope integer binder.
    pub variable: SymbolId,
    /// The strictly positive constant multiplying `variable`.
    pub coefficient: i128,
    /// The bound-variable-free term compared with `variable` by the `ite`.
    pub pivot: TermId,
    /// The bound-variable-free then branch.
    pub then_value: TermId,
    /// The bound-variable-free else branch used to derive the counterexamples.
    pub else_value: TermId,
    /// The bound-variable-free lower threshold.
    pub threshold: TermId,
}

/// Returns a certificate when an assertion contains the exact false universal
/// described by [`IntAffineGrowthRefutationCertificate`].
///
/// The matcher rejects non-positive slopes, binder-dependent parameters,
/// duplicate/non-integer binders, extra Boolean structure, and arithmetic
/// spellings other than subtraction or addition with an exact `-1` multiplier.
#[must_use]
pub fn int_affine_growth_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<IntAffineGrowthRefutationCertificate> {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        collect_top_conjuncts(arena, assertion, &mut conjuncts);
    }
    conjuncts
        .into_iter()
        .find_map(|assertion| match_affine_growth_universal(arena, assertion))
}

fn match_affine_growth_universal(
    arena: &TermArena,
    assertion: TermId,
) -> Option<IntAffineGrowthRefutationCertificate> {
    let (vars, body) = peel_foralls(arena, assertion)?;
    let bound: BTreeSet<_> = vars.iter().copied().collect();
    if bound.len() != vars.len() || vars.iter().any(|&var| arena.symbol(var).1 != Sort::Int) {
        return None;
    }

    let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(body)
    else {
        return None;
    };
    let [comparison] = &**args else {
        return None;
    };
    let TermNode::App {
        op: Op::IntGe,
        args,
    } = arena.node(*comparison)
    else {
        return None;
    };
    let [difference, threshold] = &**args else {
        return None;
    };
    if contains_any_bound(arena, *threshold, &bound) {
        return None;
    }

    let (variable, coefficient, piecewise) = match_difference(arena, *difference)?;
    if coefficient <= 0 || !bound.contains(&variable) {
        return None;
    }
    let (pivot, then_value, else_value) = match_piecewise(arena, piecewise, variable)?;
    if [pivot, then_value, else_value]
        .into_iter()
        .any(|term| contains_any_bound(arena, term, &bound))
    {
        return None;
    }

    Some(IntAffineGrowthRefutationCertificate {
        assertion,
        variable,
        coefficient,
        pivot,
        then_value,
        else_value,
        threshold: *threshold,
    })
}

fn peel_foralls(arena: &TermArena, mut term: TermId) -> Option<(Vec<SymbolId>, TermId)> {
    let mut vars = Vec::new();
    while let TermNode::App {
        op: Op::Forall(var),
        args,
    } = arena.node(term)
    {
        let [body] = &**args else {
            return None;
        };
        vars.push(*var);
        term = *body;
    }
    (!vars.is_empty()).then_some((vars, term))
}

fn match_difference(arena: &TermArena, term: TermId) -> Option<(SymbolId, i128, TermId)> {
    match arena.node(term) {
        TermNode::App {
            op: Op::IntSub,
            args,
        } => {
            let [scaled, piecewise] = &**args else {
                return None;
            };
            let (variable, coefficient) = match_scaled_variable(arena, *scaled)?;
            Some((variable, coefficient, *piecewise))
        }
        TermNode::App {
            op: Op::IntAdd,
            args,
        } => {
            let [left, right] = &**args else {
                return None;
            };
            match_scaled_plus_negated(arena, *left, *right)
                .or_else(|| match_scaled_plus_negated(arena, *right, *left))
        }
        _ => None,
    }
}

fn match_scaled_plus_negated(
    arena: &TermArena,
    scaled: TermId,
    negated: TermId,
) -> Option<(SymbolId, i128, TermId)> {
    let (variable, coefficient) = match_scaled_variable(arena, scaled)?;
    let TermNode::App {
        op: Op::IntMul,
        args,
    } = arena.node(negated)
    else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    let piecewise = if is_minus_one(arena, *left) {
        *right
    } else if is_minus_one(arena, *right) {
        *left
    } else {
        return None;
    };
    Some((variable, coefficient, piecewise))
}

fn is_minus_one(arena: &TermArena, term: TermId) -> bool {
    match arena.node(term) {
        TermNode::IntConst(-1) => true,
        TermNode::App {
            op: Op::IntNeg,
            args,
        } => matches!(&**args, [one] if matches!(arena.node(*one), TermNode::IntConst(1))),
        _ => false,
    }
}

fn match_scaled_variable(arena: &TermArena, term: TermId) -> Option<(SymbolId, i128)> {
    let TermNode::App {
        op: Op::IntMul,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    match (arena.node(*left), arena.node(*right)) {
        (TermNode::IntConst(coefficient), TermNode::Symbol(variable))
        | (TermNode::Symbol(variable), TermNode::IntConst(coefficient)) => {
            Some((*variable, *coefficient))
        }
        _ => None,
    }
}

fn match_piecewise(
    arena: &TermArena,
    term: TermId,
    variable: SymbolId,
) -> Option<(TermId, TermId, TermId)> {
    let TermNode::App { op: Op::Ite, args } = arena.node(term) else {
        return None;
    };
    let [condition, then_value, else_value] = &**args else {
        return None;
    };
    let TermNode::App { op: Op::Eq, args } = arena.node(*condition) else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    let pivot = match (arena.node(*left), arena.node(*right)) {
        (TermNode::Symbol(found), _) if *found == variable => *right,
        (_, TermNode::Symbol(found)) if *found == variable => *left,
        _ => return None,
    };
    Some((pivot, *then_value, *else_value))
}

fn contains_any_bound(arena: &TermArena, term: TermId, bound: &BTreeSet<SymbolId>) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = vec![term];
    while let Some(current) = stack.pop() {
        if !seen.insert(current) {
            continue;
        }
        match arena.node(current) {
            TermNode::Symbol(symbol) if bound.contains(symbol) => return true,
            TermNode::App {
                op: Op::Forall(_) | Op::Exists(_),
                ..
            } => return true,
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use axeyum_smtlib::parse_script;

    use super::int_affine_growth_refutation;

    #[test]
    fn recognizes_repair_const_shape() {
        let script = parse_script(include_str!(
            "../../../corpus/public-curated/quantified/LIA/cvc5-regress-clean/cli__regress1__quantifiers__repair-const-nterm.smt2"
        ))
        .unwrap();
        let cert =
            int_affine_growth_refutation(&script.arena, &script.assertions).unwrap_or_else(|| {
                panic!(
                    "repair-const-nterm must match the exact theorem: {}",
                    axeyum_ir::render(&script.arena, script.assertions[0])
                )
            });
        assert_eq!(cert.coefficient, 3);
    }

    #[test]
    fn rejects_nonpositive_or_binder_dependent_shapes() {
        for text in [
            "(set-logic LIA) (declare-fun p () Int) (declare-fun a () Int) \
             (declare-fun b () Int) (assert (forall ((x Int)) \
             (not (>= (- (* 0 x) (ite (= x p) a b)) 1)))) (check-sat)",
            "(set-logic LIA) (declare-fun p () Int) (declare-fun a () Int) \
             (assert (forall ((x Int)) \
             (not (>= (- (* 3 x) (ite (= x p) a x)) 1)))) (check-sat)",
            "(set-logic LIA) (declare-fun p () Int) (declare-fun a () Int) \
             (declare-fun b () Int) (assert (forall ((x Int) (y Int)) \
             (not (>= (- (* 3 x) (ite (= x y) a b)) 1)))) (check-sat)",
        ] {
            let script = parse_script(text).unwrap();
            assert!(int_affine_growth_refutation(&script.arena, &script.assertions).is_none());
        }
    }
}
