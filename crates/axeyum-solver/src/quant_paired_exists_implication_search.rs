//! Untrusted refutation for paired positive/negated existential assertions.
//!
//! This is a narrow unsat-only bridge for rows that share the same outer
//! conjuncts and differ only in the existential body on the same witness.
//! The checker is just a QF replay of the witness-transfer implication:
//! `outer ∧ body_left[w] ∧ ¬body_right[w]` must be unsat.

use std::collections::{BTreeSet, HashMap};

use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode};
use axeyum_rewrite::replace_subterms;

use crate::auto::check_auto;
use crate::backend::{CheckResult, SolverConfig, SolverError};

/// Searches for a paired existential implication refutation.
pub(crate) fn find_paired_existential_implication_refutation(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<()>, SolverError> {
    if assertions.len() != 2 {
        return Ok(None);
    }

    if let Some(result) = try_pair(arena, assertions[0], assertions[1], config)? {
        return Ok(Some(result));
    }
    if let Some(result) = try_pair(arena, assertions[1], assertions[0], config)? {
        return Ok(Some(result));
    }
    Ok(None)
}

fn try_pair(
    arena: &TermArena,
    positive: TermId,
    negative: TermId,
    config: &SolverConfig,
) -> Result<Option<()>, SolverError> {
    let Some((positive_outer, positive_binder, positive_body)) =
        peel_positive_existential_conjunction(arena, positive)
    else {
        return Ok(None);
    };
    let Some((negative_outer, negative_binder, negative_body)) =
        peel_negated_existential_conjunction(arena, negative)
    else {
        return Ok(None);
    };
    if arena.symbol(positive_binder).1 != arena.symbol(negative_binder).1
        || !same_conjunctions(arena, &positive_outer, &negative_outer)
    {
        return Ok(None);
    }

    let mut scratch = arena.clone();
    let witness_sort = scratch.symbol(positive_binder).1;
    let witness = declare_fresh_witness(&mut scratch, positive, witness_sort)?;

    let positive_inst = instantiate_body(&mut scratch, positive_body, positive_binder, witness)?;
    let negative_inst = instantiate_body(&mut scratch, negative_body, negative_binder, witness)?;

    let mut query = fold_conjunction(&mut scratch, &positive_outer)?;
    query = scratch
        .and(query, positive_inst)
        .map_err(|error| SolverError::Backend(error.to_string()))?;
    let negated = scratch
        .not(negative_inst)
        .map_err(|error| SolverError::Backend(error.to_string()))?;
    query = scratch
        .and(query, negated)
        .map_err(|error| SolverError::Backend(error.to_string()))?;

    match check_auto(&mut scratch, &[query], config)? {
        CheckResult::Unsat => Ok(Some(())),
        CheckResult::Sat(_) | CheckResult::Unknown(_) => Ok(None),
    }
}

fn peel_positive_existential_conjunction(
    arena: &TermArena,
    assertion: TermId,
) -> Option<(Vec<TermId>, SymbolId, TermId)> {
    let mut conjuncts = Vec::new();
    collect_top_conjuncts(arena, assertion, &mut conjuncts);
    let mut existential = None;
    let mut outer = Vec::new();
    for conjunct in conjuncts {
        match arena.node(conjunct) {
            TermNode::App {
                op: Op::Exists(binder),
                args,
            } if args.len() == 1 => {
                if existential.is_some()
                    || contains_quantifier(arena, args[0])
                    || !occurs(arena, args[0], *binder)
                {
                    return None;
                }
                existential = Some((*binder, args[0]));
            }
            _ => {
                if contains_quantifier(arena, conjunct) {
                    return None;
                }
                outer.push(conjunct);
            }
        }
    }
    let Some((binder, body)) = existential else {
        return None;
    };
    Some((outer, binder, body))
}

fn peel_negated_existential_conjunction(
    arena: &TermArena,
    assertion: TermId,
) -> Option<(Vec<TermId>, SymbolId, TermId)> {
    let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(assertion)
    else {
        return None;
    };
    let [inner] = &**args else {
        return None;
    };
    let mut conjuncts = Vec::new();
    collect_top_conjuncts(arena, *inner, &mut conjuncts);
    let mut existential = None;
    let mut outer = Vec::new();
    for conjunct in conjuncts {
        match arena.node(conjunct) {
            TermNode::App {
                op: Op::Exists(binder),
                args,
            } if args.len() == 1 => {
                if existential.is_some()
                    || contains_quantifier(arena, args[0])
                    || !occurs(arena, args[0], *binder)
                {
                    return None;
                }
                existential = Some((*binder, args[0]));
            }
            _ => {
                if contains_quantifier(arena, conjunct) {
                    return None;
                }
                outer.push(conjunct);
            }
        }
    }
    let Some((binder, body)) = existential else {
        return None;
    };
    Some((outer, binder, body))
}

fn instantiate_body(
    arena: &mut TermArena,
    body: TermId,
    binder: SymbolId,
    witness: SymbolId,
) -> Result<TermId, SolverError> {
    let mut replacements = HashMap::new();
    replacements.insert(arena.var(binder), arena.var(witness));
    let mut memo = HashMap::new();
    replace_subterms(arena, body, &replacements, &mut memo)
        .map_err(|error| SolverError::Backend(error.to_string()))
}

fn fold_conjunction(arena: &mut TermArena, terms: &[TermId]) -> Result<TermId, SolverError> {
    let mut iter = terms.iter().copied();
    let Some(first) = iter.next() else {
        return Ok(arena.bool_const(true));
    };
    iter.try_fold(first, |acc, term| {
        arena
            .and(acc, term)
            .map_err(|error| SolverError::Backend(error.to_string()))
    })
}

fn declare_fresh_witness(
    arena: &mut TermArena,
    assertion: TermId,
    sort: Sort,
) -> Result<SymbolId, SolverError> {
    let mut nonce = arena.symbols().count();
    loop {
        let name = format!("!paired_exists_witness_{}_{}", assertion.index(), nonce);
        nonce += 1;
        if arena.find_internal_symbol(&name).is_none() {
            return arena
                .declare_internal(&name, sort)
                .map_err(|error| SolverError::Backend(error.to_string()));
        }
    }
}

fn collect_top_conjuncts(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    if let TermNode::App {
        op: Op::BoolAnd,
        args,
    } = arena.node(term)
    {
        for &arg in args {
            collect_top_conjuncts(arena, arg, out);
        }
    } else {
        out.push(term);
    }
}

fn same_conjunctions(arena: &TermArena, left: &[TermId], right: &[TermId]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut used = vec![false; right.len()];
    for &term in left {
        let mut matched = false;
        for (index, &candidate) in right.iter().enumerate() {
            if !used[index] && structurally_equal(arena, term, candidate) {
                used[index] = true;
                matched = true;
                break;
            }
        }
        if !matched {
            return false;
        }
    }
    true
}

fn structurally_equal(arena: &TermArena, left: TermId, right: TermId) -> bool {
    if left == right {
        return true;
    }
    match (arena.node(left), arena.node(right)) {
        (TermNode::BoolConst(a), TermNode::BoolConst(b)) => a == b,
        (TermNode::IntConst(a), TermNode::IntConst(b)) => a == b,
        (TermNode::RealConst(a), TermNode::RealConst(b)) => a == b,
        (
            TermNode::BvConst {
                width: aw,
                value: av,
            },
            TermNode::BvConst {
                width: bw,
                value: bv,
            },
        ) => aw == bw && av == bv,
        (TermNode::WideBvConst(a), TermNode::WideBvConst(b)) => a == b,
        (TermNode::Symbol(a), TermNode::Symbol(b)) => a == b,
        (
            TermNode::App {
                op: aop,
                args: aargs,
            },
            TermNode::App {
                op: bop,
                args: bargs,
            },
        ) => {
            aop == bop
                && aargs.len() == bargs.len()
                && aargs
                    .iter()
                    .zip(bargs.iter())
                    .all(|(&a, &b)| structurally_equal(arena, a, b))
        }
        _ => false,
    }
}

fn contains_quantifier(arena: &TermArena, term: TermId) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = vec![term];
    while let Some(current) = stack.pop() {
        if !seen.insert(current) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(current) {
            if matches!(op, Op::Forall(_) | Op::Exists(_)) {
                return true;
            }
            stack.extend(args.iter().copied());
        }
    }
    false
}

fn occurs(arena: &TermArena, term: TermId, symbol: SymbolId) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = vec![term];
    while let Some(current) = stack.pop() {
        if !seen.insert(current) {
            continue;
        }
        match arena.node(current) {
            TermNode::Symbol(found) if *found == symbol => return true,
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backend::SolverConfig;

    #[test]
    fn debug_nested9_pair_match() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__nested9_true-unreach-call.i_575.smt2");
        let text = std::fs::read_to_string(&path).expect("read nested9");
        let script = axeyum_smtlib::parse_script(&text).expect("parse nested9");
        assert_eq!(script.assertions.len(), 2);
        let a0 = script.assertions[0];
        let a1 = script.assertions[1];
        let p0 = peel_positive_existential_conjunction(&script.arena, a0);
        let n0 = peel_negated_existential_conjunction(&script.arena, a1);
        assert!(p0.is_some() && n0.is_some());
        assert!(matches!(
            find_paired_existential_implication_refutation(
                &script.arena,
                &script.assertions,
                &SolverConfig::default()
            ),
            Ok(Some(()))
        ));
    }
}
