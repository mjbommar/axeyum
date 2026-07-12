//! Checked refutation for the exact Euclidean quotient/remainder universal.
//!
//! For every integer dividend `t` and positive integer modulus `k`, SMT-LIB
//! integer division and modulo satisfy
//!
//! ```text
//! t = k * (div t k) + (mod t k)
//! 0 <= mod t k < k
//! ```
//!
//! Therefore the universal
//!
//! ```text
//! forall s m. k*m + s != t or s < 0 or s >= k
//! ```
//!
//! is false at `s := mod(t, k)` and `m := div(t, k)`. This module is the small
//! checker for that theorem schema. It deliberately re-matches the original IR
//! independently of the counterexample-instantiation search in `qinst_egraph`.

use std::collections::BTreeSet;

use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode};

/// A self-checking refutation of an exact Euclidean-residue universal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IntEuclideanResidueRefutationCertificate {
    /// The original top-level universal assertion.
    pub assertion: TermId,
    /// The bound symbol used as the Euclidean remainder.
    pub remainder: SymbolId,
    /// The bound symbol used as the Euclidean quotient.
    pub quotient: SymbolId,
    /// The bound-variable-free integer dividend.
    pub dividend: TermId,
    /// The strictly positive constant modulus.
    pub modulus: i128,
}

/// Returns a certificate when an assertion contains the exact false universal
/// described by [`IntEuclideanResidueRefutationCertificate`].
///
/// Other assertions are irrelevant once this universal is present. The matcher
/// accepts no weakened bounds, extra disjuncts, non-positive modulus, or dividend
/// that depends on either bound variable.
#[must_use]
pub fn int_euclidean_residue_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<IntEuclideanResidueRefutationCertificate> {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        collect_top_conjuncts(arena, assertion, &mut conjuncts);
    }
    conjuncts
        .into_iter()
        .find_map(|assertion| match_residue_universal(arena, assertion))
}

fn match_residue_universal(
    arena: &TermArena,
    assertion: TermId,
) -> Option<IntEuclideanResidueRefutationCertificate> {
    let (vars, body) = peel_foralls(arena, assertion)?;
    if vars.len() != 2 || vars.iter().any(|&var| arena.symbol(var).1 != Sort::Int) {
        return None;
    }
    let bound: BTreeSet<SymbolId> = vars.iter().copied().collect();
    let mut disjuncts = Vec::new();
    flatten_or(arena, body, &mut disjuncts);
    if disjuncts.len() != 3 {
        return None;
    }

    let (remainder, quotient, dividend, modulus) = disjuncts
        .iter()
        .find_map(|&term| match_negated_recomposition(arena, term, &bound))?;
    if remainder == quotient {
        return None;
    }

    let mut lower = false;
    let mut upper = false;
    let mut recomposition = false;
    for disjunct in disjuncts {
        if match_negated_recomposition(arena, disjunct, &bound)
            == Some((remainder, quotient, dividend, modulus))
        {
            if recomposition {
                return None;
            }
            recomposition = true;
        } else if is_lower_guard(arena, disjunct, remainder) {
            if lower {
                return None;
            }
            lower = true;
        } else if is_upper_guard(arena, disjunct, remainder, modulus) {
            if upper {
                return None;
            }
            upper = true;
        } else {
            return None;
        }
    }
    if !(recomposition && lower && upper) {
        return None;
    }

    Some(IntEuclideanResidueRefutationCertificate {
        assertion,
        remainder,
        quotient,
        dividend,
        modulus,
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

fn collect_top_conjuncts(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    if let TermNode::App {
        op: Op::BoolAnd,
        args,
    } = arena.node(term)
        && let [left, right] = &**args
    {
        collect_top_conjuncts(arena, *left, out);
        collect_top_conjuncts(arena, *right, out);
    } else {
        out.push(term);
    }
}

fn flatten_or(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    if let TermNode::App {
        op: Op::BoolOr,
        args,
    } = arena.node(term)
    {
        for &arg in args {
            flatten_or(arena, arg, out);
        }
    } else {
        out.push(term);
    }
}

fn match_negated_recomposition(
    arena: &TermArena,
    term: TermId,
    bound: &BTreeSet<SymbolId>,
) -> Option<(SymbolId, SymbolId, TermId, i128)> {
    let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [equality] = &**args else {
        return None;
    };
    let TermNode::App { op: Op::Eq, args } = arena.node(*equality) else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    match_recomposition(arena, *left, *right, bound)
        .or_else(|| match_recomposition(arena, *right, *left, bound))
}

fn match_recomposition(
    arena: &TermArena,
    sum: TermId,
    dividend: TermId,
    bound: &BTreeSet<SymbolId>,
) -> Option<(SymbolId, SymbolId, TermId, i128)> {
    if contains_any_bound(arena, dividend, bound) {
        return None;
    }
    let TermNode::App {
        op: Op::IntAdd,
        args,
    } = arena.node(sum)
    else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    let (remainder, quotient, modulus) = match_scaled_sum(arena, *left, *right)
        .or_else(|| match_scaled_sum(arena, *right, *left))?;
    if modulus <= 0 || !bound.contains(&remainder) || !bound.contains(&quotient) {
        return None;
    }
    Some((remainder, quotient, dividend, modulus))
}

fn match_scaled_sum(
    arena: &TermArena,
    scaled: TermId,
    remainder: TermId,
) -> Option<(SymbolId, SymbolId, i128)> {
    let TermNode::Symbol(remainder) = arena.node(remainder) else {
        return None;
    };
    let TermNode::App {
        op: Op::IntMul,
        args,
    } = arena.node(scaled)
    else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    let (modulus, quotient) = match (arena.node(*left), arena.node(*right)) {
        (TermNode::IntConst(modulus), TermNode::Symbol(quotient))
        | (TermNode::Symbol(quotient), TermNode::IntConst(modulus)) => (*modulus, *quotient),
        _ => return None,
    };
    Some((*remainder, quotient, modulus))
}

fn is_lower_guard(arena: &TermArena, term: TermId, remainder: SymbolId) -> bool {
    let TermNode::App {
        op: Op::IntLt,
        args,
    } = arena.node(term)
    else {
        return false;
    };
    let [left, right] = &**args else {
        return false;
    };
    matches!(arena.node(*left), TermNode::Symbol(found) if *found == remainder)
        && matches!(arena.node(*right), TermNode::IntConst(0))
}

fn is_upper_guard(arena: &TermArena, term: TermId, remainder: SymbolId, modulus: i128) -> bool {
    let TermNode::App {
        op: Op::IntGe,
        args,
    } = arena.node(term)
    else {
        return false;
    };
    let [left, right] = &**args else {
        return false;
    };
    matches!(arena.node(*left), TermNode::Symbol(found) if *found == remainder)
        && matches!(arena.node(*right), TermNode::IntConst(found) if *found == modulus)
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

    use super::int_euclidean_residue_refutation;

    #[test]
    fn recognizes_exact_clock_shapes() {
        for modulus in [3, 10] {
            let text = format!(
                "(set-logic LIA) (declare-fun t () Int) \
                 (assert (forall ((s Int) (m Int)) \
                   (or (not (= (+ (* {modulus} m) s) t)) (< s 0) (>= s {modulus})))) \
                 (check-sat)"
            );
            let script = parse_script(&text).unwrap();
            let cert = int_euclidean_residue_refutation(&script.arena, &script.assertions)
                .expect("exact Euclidean partition must certify");
            assert_eq!(cert.modulus, modulus);
        }
    }

    #[test]
    fn rejects_weakened_or_nonpositive_shapes() {
        for text in [
            "(set-logic LIA) (declare-fun t () Int) \
             (assert (forall ((s Int) (m Int)) \
               (or (not (= (+ (* 3 m) s) t)) (< s 0) (>= s 2)))) (check-sat)",
            "(set-logic LIA) (declare-fun t () Int) \
             (assert (forall ((s Int) (m Int)) \
               (or (not (= (+ (* 0 m) s) t)) (< s 0) (>= s 0)))) (check-sat)",
            "(set-logic LIA) (declare-fun t () Int) \
             (assert (forall ((s Int) (m Int)) \
               (or (not (= (+ (* 3 m) s) t)) (< s 0) (>= s 3) true))) (check-sat)",
        ] {
            let script = parse_script(text).unwrap();
            assert!(int_euclidean_residue_refutation(&script.arena, &script.assertions).is_none());
        }
    }
}
