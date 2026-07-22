//! Checked finite-profile models for the almost-uninterpreted quantified fragment.
//!
//! MBQI search is not evidence. This module independently checks one exact
//! source assertion against the returned total uninterpreted-function model.
//! Unsupported shapes decline rather than sampling an infinite domain.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use axeyum_ir::{FuncId, Op, Rational, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};

use crate::Model;

/// Maximum number of finite-profile representatives checked for one universal.
pub const QUANTIFIED_UF_PROFILE_CAP: usize = 4096;

/// Source binding for one checked almost-uninterpreted universal model.
///
/// The function interpretation itself lives in [`Model`]. The checker trusts
/// neither a search-generated candidate list nor any derived profile metadata:
/// it reconstructs the complete finite representative set from `assertion` and
/// the model's finite function tables.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifiedUfModelSatCertificate {
    /// Exact original quantified assertion covered by this certificate.
    pub assertion: TermId,
    /// Exact source binder, redundantly recorded so stale/tampered certificates
    /// fail closed before finite-profile evaluation.
    pub binder: SymbolId,
}

/// Checks an almost-uninterpreted quantified-UF model against one exact source
/// assertion.
///
/// Accepted assertions have shape `forall x. body`, where `x` is `Int` or
/// `Real`, `body` is quantifier-free, and every occurrence of `x` is a direct
/// argument of an uninterpreted-function application. For every exact argument
/// position occupied by `x`, the checker evaluates `body` at all corresponding
/// finite-table key components plus one value outside the finite set. Those
/// representatives exhaust every possible table/default profile.
#[must_use]
pub fn check_quantified_uf_model_sat(
    arena: &TermArena,
    assertion: TermId,
    model: &Model,
    certificate: &QuantifiedUfModelSatCertificate,
) -> bool {
    if certificate.assertion != assertion {
        return false;
    }
    let TermNode::App {
        op: Op::Forall(binder),
        args,
    } = arena.node(assertion)
    else {
        return false;
    };
    let [body] = &**args else {
        return false;
    };
    if *binder != certificate.binder || contains_quantifier(arena, *body) {
        return false;
    }
    let binder_sort = arena.symbol(*binder).1;
    if !matches!(binder_sort, Sort::Int | Sort::Real) {
        return false;
    }

    let Some(positions) = relevant_function_positions(arena, *body, *binder) else {
        return false;
    };
    if positions.is_empty() {
        return false;
    }

    let mut representatives = Vec::new();
    for (function, argument_positions) in positions {
        let (_, declared_params, declared_result) = arena.function(function);
        let Some(interpretation) = model.function(function) else {
            return false;
        };
        if interpretation.params() != declared_params
            || interpretation.result() != declared_result
            || !interpretation.uses_value_storage()
        {
            return false;
        }
        for (key, _) in interpretation.value_entries() {
            if key.len() != declared_params.len() {
                return false;
            }
            for &position in &argument_positions {
                let Some(component) = key.get(position) else {
                    return false;
                };
                if component.sort() != binder_sort {
                    return false;
                }
                if !representatives.contains(component) {
                    representatives.push(component.clone());
                    if representatives.len() >= QUANTIFIED_UF_PROFILE_CAP {
                        return false;
                    }
                }
            }
        }
    }

    let Some(generic) = fresh_value(binder_sort, &representatives) else {
        return false;
    };
    representatives.push(generic);
    if representatives.len() > QUANTIFIED_UF_PROFILE_CAP {
        return false;
    }

    let assignment = model.to_assignment();
    let mut cloned = arena.clone();
    let binder_term = cloned.var(*binder);
    for representative in representatives {
        let Some(replacement) = value_to_const(&mut cloned, &representative) else {
            return false;
        };
        let mut memo = HashMap::new();
        let instantiated = substitute_term(&mut cloned, *body, binder_term, replacement, &mut memo);
        if !matches!(
            eval(&cloned, instantiated, &assignment),
            Ok(Value::Bool(true))
        ) {
            return false;
        }
    }
    true
}

/// Constructs the minimal source-binding certificate only after the independent
/// checker accepts it.
pub(crate) fn certify_quantified_uf_model_sat(
    arena: &TermArena,
    assertion: TermId,
    model: &Model,
) -> Option<QuantifiedUfModelSatCertificate> {
    let TermNode::App {
        op: Op::Forall(binder),
        ..
    } = arena.node(assertion)
    else {
        return None;
    };
    let certificate = QuantifiedUfModelSatCertificate {
        assertion,
        binder: *binder,
    };
    check_quantified_uf_model_sat(arena, assertion, model, &certificate).then_some(certificate)
}

/// Returns the exact UF argument positions occupied by `binder`, or `None` when
/// an occurrence is not a direct UF argument.
fn relevant_function_positions(
    arena: &TermArena,
    root: TermId,
    binder: SymbolId,
) -> Option<BTreeMap<FuncId, BTreeSet<usize>>> {
    fn visit(
        arena: &TermArena,
        term: TermId,
        binder: SymbolId,
        direct_position: Option<(FuncId, usize)>,
        positions: &mut BTreeMap<FuncId, BTreeSet<usize>>,
    ) -> bool {
        match arena.node(term) {
            TermNode::Symbol(symbol) if *symbol == binder => {
                let Some((function, position)) = direct_position else {
                    return false;
                };
                positions.entry(function).or_default().insert(position);
                true
            }
            TermNode::App { op, args } => {
                let application = match op {
                    Op::Apply(function) => Some(*function),
                    _ => None,
                };
                let args = args.clone();
                args.iter().enumerate().all(|(position, &argument)| {
                    visit(
                        arena,
                        argument,
                        binder,
                        application.map(|function| (function, position)),
                        positions,
                    )
                })
            }
            _ => true,
        }
    }

    let mut positions = BTreeMap::new();
    visit(arena, root, binder, None, &mut positions).then_some(positions)
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

fn fresh_value(sort: Sort, avoid: &[Value]) -> Option<Value> {
    let bound = avoid.len().checked_add(2)?;
    let mut integer = 0_i128;
    for _ in 0..=bound {
        let candidate = match sort {
            Sort::Int => Value::Int(integer),
            Sort::Real => Value::Real(Rational::integer(integer)),
            _ => return None,
        };
        if !avoid.contains(&candidate) {
            return Some(candidate);
        }
        integer = if integer > 0 { -integer } else { -integer + 1 };
    }
    None
}

fn value_to_const(arena: &mut TermArena, value: &Value) -> Option<TermId> {
    match value {
        Value::Int(integer) => Some(arena.int_const(*integer)),
        Value::Real(real) => Some(arena.real_const(*real)),
        _ => None,
    }
}

fn substitute_term(
    arena: &mut TermArena,
    term: TermId,
    needle: TermId,
    replacement: TermId,
    memo: &mut HashMap<TermId, TermId>,
) -> TermId {
    if term == needle {
        return replacement;
    }
    if let Some(&cached) = memo.get(&term) {
        return cached;
    }
    let rebuilt = match arena.node(term).clone() {
        TermNode::App { args, .. } => {
            let arguments: Vec<_> = args
                .iter()
                .map(|&argument| substitute_term(arena, argument, needle, replacement, memo))
                .collect();
            arena.rebuild_with_args(term, &arguments)
        }
        _ => term,
    };
    memo.insert(term, rebuilt);
    rebuilt
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn position_gate_accepts_direct_and_repeated_arguments() {
        let mut arena = TermArena::new();
        let function = arena
            .declare_fun("f", &[Sort::Int, Sort::Int], Sort::Int)
            .unwrap();
        let binder = arena.declare("x", Sort::Int).unwrap();
        let variable = arena.var(binder);
        let application = arena.apply(function, &[variable, variable]).unwrap();
        let zero = arena.int_const(0);
        let body = arena.int_ge(application, zero).unwrap();
        assert_eq!(
            relevant_function_positions(&arena, body, binder),
            Some(BTreeMap::from([(function, BTreeSet::from([0, 1]))]))
        );
    }

    #[test]
    fn position_gate_rejects_interpreted_occurrence() {
        let mut arena = TermArena::new();
        let function = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
        let binder = arena.declare("x", Sort::Int).unwrap();
        let variable = arena.var(binder);
        let application = arena.apply(function, &[variable]).unwrap();
        let sum = arena.int_add(application, variable).unwrap();
        let zero = arena.int_const(0);
        let body = arena.int_ge(sum, zero).unwrap();
        assert_eq!(relevant_function_positions(&arena, body, binder), None);
    }

    #[test]
    fn fresh_value_avoids_the_complete_special_set() {
        let avoid = vec![Value::Int(0), Value::Int(1), Value::Int(-1), Value::Int(2)];
        let generic = fresh_value(Sort::Int, &avoid).unwrap();
        assert!(!avoid.contains(&generic));
    }
}
