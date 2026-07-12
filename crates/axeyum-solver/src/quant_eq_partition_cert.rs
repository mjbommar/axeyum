//! Checked finite equality partitions for closed Bool/Int quantifiers (ADR-0101).

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::{Assignment, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};

/// Maximum representative branches the checker will visit.
pub const EQ_PARTITION_CASE_CAP: u64 = 1 << 20;

/// A reduction-free refutation of one closed equality-partitioned assertion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EqualityPartitionRefutationCertificate {
    /// The original top-level assertion proved false.
    pub assertion: TermId,
    /// Number of quantifier representative branches visited by the checker.
    pub representative_cases: u64,
}

/// Rechecks an equality-partitioned quantified refutation against original IR.
#[must_use]
pub fn check_equality_partition_refutation(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &EqualityPartitionRefutationCertificate,
) -> bool {
    if certificate.assertion.index() >= arena.len()
        || !assertions.contains(&certificate.assertion)
        || arena.sort_of(certificate.assertion) != Sort::Bool
        || !contains_quantifier(arena, certificate.assertion)
        || !admissible(arena, certificate.assertion)
    {
        return false;
    }
    let mut cases = 0;
    matches!(
        truth(arena, certificate.assertion, &Assignment::new(), &mut cases),
        Some(false)
    ) && cases == certificate.representative_cases
}

fn admissible(arena: &TermArena, root: TermId) -> bool {
    scan(arena, root, &mut BTreeMap::new(), None)
}

fn scan(
    arena: &TermArena,
    term: TermId,
    bound: &mut BTreeMap<SymbolId, Sort>,
    equality_other: Option<TermId>,
) -> bool {
    if !matches!(arena.sort_of(term), Sort::Bool | Sort::Int) {
        return false;
    }
    match arena.node(term) {
        TermNode::BoolConst(_) | TermNode::IntConst(_) => true,
        TermNode::BvConst { .. }
        | TermNode::WideBvConst(_)
        | TermNode::RealConst(_)
        | TermNode::App {
            op: Op::Apply(_), ..
        } => false,
        TermNode::Symbol(symbol) => match bound.get(symbol) {
            Some(Sort::Bool) => true,
            Some(Sort::Int) => {
                equality_other.is_some_and(|other| int_constant(arena, other).is_some())
            }
            _ => false,
        },
        TermNode::App {
            op: Op::Forall(var) | Op::Exists(var),
            args,
        } => {
            if args.len() != 1 {
                return false;
            }
            let sort = arena.symbol(*var).1;
            if !matches!(sort, Sort::Bool | Sort::Int) || bound.insert(*var, sort).is_some() {
                return false;
            }
            let accepted = scan(arena, args[0], bound, None);
            bound.remove(var);
            accepted
        }
        TermNode::App { op, args } => {
            for (index, &arg) in args.iter().enumerate() {
                let other = if matches!(op, Op::Eq) && args.len() == 2 {
                    Some(args[1 - index])
                } else {
                    None
                };
                if !scan(arena, arg, bound, other) {
                    return false;
                }
            }
            true
        }
    }
}

fn truth(
    arena: &TermArena,
    term: TermId,
    assignment: &Assignment,
    cases: &mut u64,
) -> Option<bool> {
    match arena.node(term) {
        TermNode::BoolConst(value) => Some(*value),
        TermNode::Symbol(symbol) if arena.symbol(*symbol).1 == Sort::Bool => {
            assignment.get(*symbol)?.as_bool()
        }
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
            let values = representatives(arena, args[0], *var)?;
            let mut outcomes = Vec::with_capacity(values.len());
            for value in values {
                *cases = cases.checked_add(1)?;
                if *cases > EQ_PARTITION_CASE_CAP {
                    return None;
                }
                let mut branch = assignment.clone();
                branch.set(*var, value);
                outcomes.push(truth(arena, args[0], &branch, cases)?);
            }
            Some(if is_forall {
                outcomes.into_iter().all(|value| value)
            } else {
                outcomes.into_iter().any(|value| value)
            })
        }
        TermNode::App {
            op: Op::BoolNot,
            args,
        } if args.len() == 1 => Some(!truth(arena, args[0], assignment, cases)?),
        TermNode::App { op, args }
            if args.len() == 2
                && matches!(op, Op::BoolAnd | Op::BoolOr | Op::BoolXor | Op::BoolImplies) =>
        {
            let left = truth(arena, args[0], assignment, cases)?;
            let right = truth(arena, args[1], assignment, cases)?;
            Some(match op {
                Op::BoolAnd => left && right,
                Op::BoolOr => left || right,
                Op::BoolXor => left ^ right,
                Op::BoolImplies => !left || right,
                _ => unreachable!("guarded Boolean operator"),
            })
        }
        TermNode::App { op: Op::Eq, args }
            if args.len() == 2 && arena.sort_of(args[0]) == Sort::Bool =>
        {
            Some(
                truth(arena, args[0], assignment, cases)?
                    == truth(arena, args[1], assignment, cases)?,
            )
        }
        TermNode::App { op: Op::Ite, args }
            if args.len() == 3 && arena.sort_of(term) == Sort::Bool =>
        {
            let condition = truth(arena, args[0], assignment, cases)?;
            let then_value = truth(arena, args[1], assignment, cases)?;
            let else_value = truth(arena, args[2], assignment, cases)?;
            Some(if condition { then_value } else { else_value })
        }
        _ if !contains_quantifier(arena, term) => eval(arena, term, assignment).ok()?.as_bool(),
        _ => None,
    }
}

fn representatives(arena: &TermArena, body: TermId, var: SymbolId) -> Option<Vec<Value>> {
    match arena.symbol(var).1 {
        Sort::Bool => Some(vec![Value::Bool(false), Value::Bool(true)]),
        Sort::Int => {
            let mut constants = BTreeSet::new();
            collect_constants(arena, body, var, &mut constants);
            let other = (0..=constants.len())
                .map(|value| i128::try_from(value).ok())
                .find_map(|value| value.filter(|candidate| !constants.contains(candidate)))?;
            let mut values: Vec<Value> = constants.into_iter().map(Value::Int).collect();
            values.push(Value::Int(other));
            Some(values)
        }
        _ => None,
    }
}

fn collect_constants(
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
                && let Some(value) = int_constant(arena, args[1 - index])
            {
                constants.insert(value);
            }
        }
    }
    for &arg in args {
        collect_constants(arena, arg, var, constants);
    }
}

fn int_constant(arena: &TermArena, term: TermId) -> Option<i128> {
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

fn contains_quantifier(arena: &TermArena, root: TermId) -> bool {
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
