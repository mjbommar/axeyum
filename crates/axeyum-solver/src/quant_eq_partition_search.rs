//! Untrusted finite equality-partition expansion for ADR-0101.

use std::collections::{BTreeSet, HashMap};

use axeyum_ir::{Assignment, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};
use axeyum_rewrite::{build_app, replace_subterms};

use crate::quant_eq_partition_cert::{
    EQ_PARTITION_CASE_CAP, EqualityPartitionRefutationCertificate,
    check_equality_partition_refutation,
};

pub(crate) fn equality_partition_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<EqualityPartitionRefutationCertificate> {
    for &assertion in assertions {
        if !has_quantifier(arena, assertion) || !search_admissible(arena, assertion) {
            continue;
        }
        let mut expanded_arena = arena.clone();
        let Some((expanded, cases)) = expand(&mut expanded_arena, assertion) else {
            continue;
        };
        if !matches!(
            eval(&expanded_arena, expanded, &Assignment::new()),
            Ok(Value::Bool(false))
        ) {
            continue;
        }
        let certificate = EqualityPartitionRefutationCertificate {
            assertion,
            representative_cases: cases,
        };
        if check_equality_partition_refutation(arena, assertions, &certificate) {
            return Some(certificate);
        }
    }
    None
}

fn expand(arena: &mut TermArena, term: TermId) -> Option<(TermId, u64)> {
    let node = arena.node(term).clone();
    match node {
        TermNode::App {
            op: Op::Forall(var) | Op::Exists(var),
            args,
        } => {
            let is_forall = matches!(
                arena.node(term),
                TermNode::App {
                    op: Op::Forall(_),
                    ..
                }
            );
            let (body, body_cases) = expand(arena, args[0])?;
            let values = representative_terms(arena, args[0], var)?;
            let cases = u64::try_from(values.len())
                .ok()?
                .checked_mul(body_cases.checked_add(1)?)?;
            if cases > EQ_PARTITION_CASE_CAP {
                return None;
            }
            let mut instances = Vec::with_capacity(values.len());
            for value in values {
                let var_term = arena.var(var);
                let replacements = HashMap::from([(var_term, value)]);
                let mut memo = HashMap::new();
                instances.push(replace_subterms(arena, body, &replacements, &mut memo).ok()?);
            }
            let mut iter = instances.into_iter();
            let mut folded = iter.next()?;
            for instance in iter {
                folded = if is_forall {
                    arena.and(folded, instance).ok()?
                } else {
                    arena.or(folded, instance).ok()?
                };
            }
            Some((folded, cases))
        }
        TermNode::App { op, args } => {
            let mut expanded = Vec::with_capacity(args.len());
            let mut cases = 0u64;
            for &arg in &args {
                let (next, next_cases) = expand(arena, arg)?;
                expanded.push(next);
                cases = cases.checked_add(next_cases)?;
            }
            Some((build_app(arena, op, &expanded).ok()?, cases))
        }
        _ => Some((term, 0)),
    }
}

fn representative_terms(arena: &mut TermArena, body: TermId, var: SymbolId) -> Option<Vec<TermId>> {
    match arena.symbol(var).1 {
        Sort::Bool => Some(vec![arena.bool_const(false), arena.bool_const(true)]),
        Sort::Int => {
            let mut constants = BTreeSet::new();
            search_constants(arena, body, var, &mut constants);
            let other = (0..=constants.len())
                .filter_map(|value| i128::try_from(value).ok())
                .find(|value| !constants.contains(value))?;
            let mut values: Vec<TermId> = constants
                .into_iter()
                .map(|value| arena.int_const(value))
                .collect();
            values.push(arena.int_const(other));
            Some(values)
        }
        _ => None,
    }
}

fn search_constants(
    arena: &TermArena,
    term: TermId,
    var: SymbolId,
    constants: &mut BTreeSet<i128>,
) {
    let TermNode::App { op, args } = arena.node(term) else {
        return;
    };
    if matches!(op, Op::Eq) && args.len() == 2 {
        for index in 0..2 {
            if matches!(arena.node(args[index]), TermNode::Symbol(symbol) if *symbol == var)
                && let Some(value) = search_int_constant(arena, args[1 - index])
            {
                constants.insert(value);
            }
        }
    }
    for &arg in args {
        search_constants(arena, arg, var, constants);
    }
}

fn search_admissible(arena: &TermArena, root: TermId) -> bool {
    search_scan(arena, root, &mut BTreeSet::new(), None)
}

fn search_scan(
    arena: &TermArena,
    term: TermId,
    bound: &mut BTreeSet<SymbolId>,
    equality_other: Option<TermId>,
) -> bool {
    if !matches!(arena.sort_of(term), Sort::Bool | Sort::Int) {
        return false;
    }
    match arena.node(term) {
        TermNode::BoolConst(_) | TermNode::IntConst(_) => true,
        TermNode::Symbol(symbol) => {
            if !bound.contains(symbol) {
                return false;
            }
            match arena.symbol(*symbol).1 {
                Sort::Bool => true,
                Sort::Int => {
                    equality_other.is_some_and(|other| search_int_constant(arena, other).is_some())
                }
                _ => false,
            }
        }
        TermNode::App {
            op: Op::Forall(var) | Op::Exists(var),
            args,
        } => {
            if args.len() != 1
                || !matches!(arena.symbol(*var).1, Sort::Bool | Sort::Int)
                || !bound.insert(*var)
            {
                return false;
            }
            let accepted = search_scan(arena, args[0], bound, None);
            bound.remove(var);
            accepted
        }
        TermNode::App {
            op: Op::Apply(_), ..
        } => false,
        TermNode::App { op, args } => args.iter().enumerate().all(|(index, &arg)| {
            let other = (matches!(op, Op::Eq) && args.len() == 2).then(|| args[1 - index]);
            search_scan(arena, arg, bound, other)
        }),
        _ => false,
    }
}

fn search_int_constant(arena: &TermArena, term: TermId) -> Option<i128> {
    match arena.node(term) {
        TermNode::IntConst(value) => Some(*value),
        TermNode::App {
            op: Op::IntNeg,
            args,
        } if args.len() == 1 => {
            let TermNode::IntConst(value) = arena.node(args[0]) else {
                return None;
            };
            value.checked_neg()
        }
        _ => None,
    }
}

fn has_quantifier(arena: &TermArena, root: TermId) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if matches!(op, Op::Forall(_) | Op::Exists(_)) {
                return true;
            }
            stack.extend(args.iter().copied());
        }
    }
    false
}
