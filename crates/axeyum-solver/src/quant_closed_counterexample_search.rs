//! Untrusted search for ADR-0100 closed-universal counterexamples.

use std::collections::{HashMap, HashSet};

use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode, well_founded_default};
use axeyum_rewrite::replace_subterms;

use crate::auto::check_auto;
use crate::backend::{CheckResult, SolverConfig, SolverError};
use crate::quant_closed_counterexample_cert::{
    ClosedUniversalCounterexampleCertificate, check_closed_universal_counterexample,
};

/// Searches for one concrete falsifying assignment to a top-level closed
/// universal assertion. The returned artifact has already passed the separate
/// original-IR evaluator checker.
pub(crate) fn find_closed_universal_counterexample(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<ClosedUniversalCounterexampleCertificate>, SolverError> {
    for &assertion in assertions {
        let Some((binders, body)) = admitted_closed_universal(arena, assertion) else {
            continue;
        };

        let mut search_arena = arena.clone();
        let mut replacements = HashMap::new();
        let mut fresh_binders = Vec::with_capacity(binders.len());
        let mut nonce = search_arena.symbols().count();
        for &binder in &binders {
            let sort = search_arena.symbol(binder).1;
            let fresh = loop {
                let name = format!(
                    "!closed_counterexample_{}_{}_{}",
                    assertion.index(),
                    binder.index(),
                    nonce
                );
                nonce += 1;
                if search_arena.find_internal_symbol(&name).is_none() {
                    break search_arena
                        .declare_internal(&name, sort)
                        .map_err(|error| SolverError::Backend(error.to_string()))?;
                }
            };
            let binder_term = search_arena.var(binder);
            let fresh_term = search_arena.var(fresh);
            replacements.insert(binder_term, fresh_term);
            fresh_binders.push((binder, fresh, sort));
        }

        let mut memo = HashMap::new();
        let instance = replace_subterms(&mut search_arena, body, &replacements, &mut memo)
            .map_err(|error| SolverError::Backend(error.to_string()))?;
        let negated = search_arena
            .not(instance)
            .map_err(|error| SolverError::Backend(error.to_string()))?;
        let result = match check_auto(&mut search_arena, &[negated], config) {
            Ok(result) => result,
            Err(SolverError::Unsupported(_)) => continue,
            Err(error) => return Err(error),
        };
        let CheckResult::Sat(model) = result else {
            continue;
        };

        let mut bindings = Vec::with_capacity(fresh_binders.len());
        for (binder, fresh, sort) in fresh_binders {
            let Some(value) = model
                .get(fresh)
                .or_else(|| well_founded_default(&search_arena, sort))
            else {
                bindings.clear();
                break;
            };
            bindings.push((binder, value));
        }
        if bindings.len() != binders.len() {
            continue;
        }

        let certificate = ClosedUniversalCounterexampleCertificate {
            assertion,
            bindings,
        };
        if check_closed_universal_counterexample(arena, assertions, &certificate) {
            return Ok(Some(certificate));
        }
    }
    Ok(None)
}

fn admitted_closed_universal(
    arena: &TermArena,
    mut term: TermId,
) -> Option<(Vec<SymbolId>, TermId)> {
    let mut binders = Vec::new();
    while let TermNode::App {
        op: Op::Forall(binder),
        args,
    } = arena.node(term)
    {
        if args.len() != 1 || !is_admitted_scalar(arena.symbol(*binder).1) {
            return None;
        }
        binders.push(*binder);
        term = args[0];
    }
    let bound: HashSet<SymbolId> = binders.iter().copied().collect();
    if bound.len() != binders.len() || !body_is_closed_qf(arena, term, &bound) {
        return None;
    }
    Some((binders, term))
}

fn body_is_closed_qf(arena: &TermArena, body: TermId, bound: &HashSet<SymbolId>) -> bool {
    if arena.sort_of(body) != Sort::Bool {
        return false;
    }
    let mut seen = HashSet::new();
    let mut stack = vec![body];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.node(term) {
            TermNode::Symbol(symbol) if !bound.contains(symbol) => return false,
            TermNode::App { op, args } => {
                if matches!(op, Op::Forall(_) | Op::Exists(_) | Op::Apply(_)) {
                    return false;
                }
                stack.extend(args.iter().copied());
            }
            _ => {}
        }
    }
    true
}

const fn is_admitted_scalar(sort: Sort) -> bool {
    matches!(sort, Sort::Bool | Sort::BitVec(_) | Sort::Int | Sort::Real)
}
