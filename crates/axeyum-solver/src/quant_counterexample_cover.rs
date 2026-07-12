//! Checked finite counterexample covers for positive Bool/Int universals.
//!
//! Search may discover sufficient free-Boolean cubes by any means. The checker
//! accepts a cover only after regenerating every carried universal instance from
//! original IR, refuting each cube with that source consequence, and refuting the
//! weakened ground skeleton with all resulting blocking clauses (ADR-0108).

use std::collections::{BTreeSet, HashMap};

use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode, Value};

use crate::auto::lift_arith_ite;
use crate::quant_bool_model_sat::{
    admitted_free_booleans, block_values, erase_quantifiers, rewrite_positive_universals,
};
use crate::{ArithDpllOutcome, Model, SolverConfig, SolverError, certify_arith_dpll_unsat};

#[cfg(not(target_arch = "wasm32"))]
use std::time::{Duration, Instant};
#[cfg(target_arch = "wasm32")]
use web_time::{Duration, Instant};

/// Maximum number of source-bound cubes in one checked cover.
pub const QUANT_COUNTEREXAMPLE_COVER_CASE_CAP: usize = 256;

const MAX_COVER_BINDERS: usize = 128;
const MAX_COVER_SOURCE_NODES: usize = 100_000;

/// One source-derived universal counterexample that excludes a free-Boolean cube.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifiedCounterexampleCoverCase {
    /// Original quantified assertion from which the instance is regenerated.
    pub assertion: TermId,
    /// Complete positive-universal binder assignment in source traversal order.
    pub bindings: Vec<(SymbolId, Value)>,
    /// Sorted, nonempty sufficient assignment to original free Boolean symbols.
    pub cube: Vec<(SymbolId, bool)>,
}

/// A finite source-bound cover proving a quantified Bool/Int query unsatisfiable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifiedCounterexampleCoverCertificate {
    /// Counterexample cubes whose checked negations close the weakened skeleton.
    pub cases: Vec<QuantifiedCounterexampleCoverCase>,
}

/// Independently checks a quantified counterexample-cover certificate.
#[must_use]
pub fn check_quantified_counterexample_cover(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &QuantifiedCounterexampleCoverCertificate,
) -> bool {
    let config = SolverConfig::default().with_timeout(Duration::from_secs(30));
    check_quantified_counterexample_cover_with_config(arena, assertions, certificate, &config)
}

/// Searches for a finite checked counterexample cover of a quantified query.
///
/// Search is untrusted; a certificate is returned only after the independent
/// source-instance and cover-closure checker above accepts it.
///
/// # Errors
///
/// Returns an underlying solver error encountered during bounded candidate or
/// counterexample search. Unsupported/incomplete shapes return `Ok(None)`.
pub fn quantified_counterexample_cover_refutation(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<QuantifiedCounterexampleCoverCertificate>, SolverError> {
    crate::quant_bool_model_sat::find_quantified_counterexample_cover(arena, assertions, config)
}

pub(crate) fn check_quantified_counterexample_cover_with_config(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &QuantifiedCounterexampleCoverCertificate,
    config: &SolverConfig,
) -> bool {
    if certificate.cases.is_empty() || certificate.cases.len() > QUANT_COUNTEREXAMPLE_COVER_CASE_CAP
    {
        return false;
    }
    let Some(free) = admitted_free_booleans(arena, assertions) else {
        return false;
    };
    if !source_shape_is_bounded(arena, assertions)
        || assertions.iter().copied().any(|assertion| {
            contains_quantifier(arena, assertion)
                && positive_universal_binders(arena, assertion)
                    .is_none_or(|binders| binders.is_empty())
        })
    {
        return false;
    }
    let free = free.into_iter().collect::<BTreeSet<_>>();
    if free.is_empty() {
        return false;
    }

    let assertion_set = assertions.iter().copied().collect::<BTreeSet<_>>();
    let mut seen_cases = Vec::new();
    let mut scratch = arena.clone();
    let deadline = config
        .timeout
        .and_then(|timeout| Instant::now().checked_add(timeout));
    for case in &certificate.cases {
        let Some(case_config) = config_with_deadline(config, deadline) else {
            return false;
        };
        if !assertion_set.contains(&case.assertion)
            || !case_shape_is_valid(&scratch, case, &free)
            || seen_cases.contains(case)
            || !check_case(&mut scratch, case, &case_config)
        {
            return false;
        }
        seen_cases.push(case.clone());
    }

    let mut closure = assertions
        .iter()
        .map(|&assertion| erase_quantifiers(&mut scratch, assertion, &mut HashMap::new()))
        .collect::<Vec<_>>();
    for case in &certificate.cases {
        let Ok(block) = block_values(&mut scratch, &case.cube) else {
            return false;
        };
        closure.push(block);
    }
    let Ok(closure) = lift_arith_ite(&mut scratch, &closure) else {
        return false;
    };
    let Some(closure_config) = config_with_deadline(config, deadline) else {
        return false;
    };
    matches!(
        certify_arith_dpll_unsat(&mut scratch, &closure, &closure_config),
        Ok(ArithDpllOutcome::Unsat(_))
    )
}

fn case_shape_is_valid(
    arena: &TermArena,
    case: &QuantifiedCounterexampleCoverCase,
    free: &BTreeSet<SymbolId>,
) -> bool {
    let Some(binders) = positive_universal_binders(arena, case.assertion) else {
        return false;
    };
    if binders.is_empty()
        || binders.len() > MAX_COVER_BINDERS
        || case.bindings.len() != binders.len()
        || case.cube.is_empty()
        || case
            .bindings
            .iter()
            .zip(&binders)
            .any(|((symbol, value), expected)| {
                symbol != expected || value.sort() != arena.symbol(*expected).1
            })
    {
        return false;
    }
    case.cube.windows(2).all(|pair| pair[0].0 < pair[1].0)
        && case.cube.iter().all(|(symbol, _)| free.contains(symbol))
}

fn config_with_deadline(config: &SolverConfig, deadline: Option<Instant>) -> Option<SolverConfig> {
    let mut bounded = config.clone();
    if let Some(deadline) = deadline {
        let remaining = deadline.checked_duration_since(Instant::now())?;
        if remaining.is_zero() {
            return None;
        }
        bounded.timeout = Some(remaining);
    }
    Some(bounded)
}

fn source_shape_is_bounded(arena: &TermArena, assertions: &[TermId]) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if seen.len() > MAX_COVER_SOURCE_NODES {
            return false;
        }
        if let TermNode::App { args, .. } = arena.node(term) {
            stack.extend(args.iter().copied());
        }
    }
    true
}

fn check_case(
    arena: &mut TermArena,
    case: &QuantifiedCounterexampleCoverCase,
    config: &SolverConfig,
) -> bool {
    let Some(instance) = instantiate_case(arena, case) else {
        return false;
    };
    let mut query = vec![instance];
    for &(symbol, value) in &case.cube {
        let variable = arena.var(symbol);
        let literal = if value {
            variable
        } else {
            let Ok(negated) = arena.not(variable) else {
                return false;
            };
            negated
        };
        query.push(literal);
    }
    let Ok(query) = lift_arith_ite(arena, &query) else {
        return false;
    };
    matches!(
        certify_arith_dpll_unsat(arena, &query, config),
        Ok(ArithDpllOutcome::Unsat(_))
    )
}

fn instantiate_case(
    arena: &mut TermArena,
    case: &QuantifiedCounterexampleCoverCase,
) -> Option<TermId> {
    let replacements = case
        .bindings
        .iter()
        .map(|(symbol, value)| value_term(arena, value).map(|term| (arena.var(*symbol), term)))
        .collect::<Option<HashMap<_, _>>>();
    let replacements = replacements?;
    rewrite_positive_universals(
        arena,
        case.assertion,
        true,
        &replacements,
        &mut HashMap::new(),
    )
}

pub(crate) fn case_from_counterexample(
    arena: &TermArena,
    assertion: TermId,
    cube: Vec<(SymbolId, bool)>,
    counterexample: &Model,
) -> Option<QuantifiedCounterexampleCoverCase> {
    let binders = positive_universal_binders(arena, assertion)?;
    let bindings = binders
        .into_iter()
        .map(|symbol| {
            let value =
                counterexample
                    .get(symbol)
                    .unwrap_or_else(|| match arena.symbol(symbol).1 {
                        Sort::Bool => Value::Bool(false),
                        Sort::Int => Value::Int(0),
                        _ => unreachable!("admission restricts cover binders to Bool/Int"),
                    });
            (symbol, value)
        })
        .collect();
    Some(QuantifiedCounterexampleCoverCase {
        assertion,
        bindings,
        cube,
    })
}

fn value_term(arena: &mut TermArena, value: &Value) -> Option<TermId> {
    match value {
        Value::Bool(value) => Some(arena.bool_const(*value)),
        Value::Int(value) => Some(arena.int_const(*value)),
        _ => None,
    }
}

fn positive_universal_binders(arena: &TermArena, root: TermId) -> Option<Vec<SymbolId>> {
    let mut binders = Vec::new();
    collect_positive_universal_binders(arena, root, true, &mut binders)?;
    Some(binders)
}

fn collect_positive_universal_binders(
    arena: &TermArena,
    term: TermId,
    positive: bool,
    binders: &mut Vec<SymbolId>,
) -> Option<()> {
    let TermNode::App { op, args } = arena.node(term) else {
        return Some(());
    };
    match op {
        Op::Forall(symbol) if positive => {
            if !matches!(arena.symbol(*symbol).1, Sort::Bool | Sort::Int)
                || binders.contains(symbol)
            {
                return None;
            }
            binders.push(*symbol);
            collect_positive_universal_binders(arena, args[0], positive, binders)
        }
        Op::Forall(_) | Op::Exists(_) => None,
        Op::BoolNot => collect_positive_universal_binders(arena, args[0], !positive, binders),
        Op::BoolImplies => {
            collect_positive_universal_binders(arena, args[0], !positive, binders)?;
            collect_positive_universal_binders(arena, args[1], positive, binders)
        }
        Op::BoolXor | Op::Eq
            if args
                .iter()
                .any(|&argument| contains_quantifier(arena, argument)) =>
        {
            None
        }
        Op::Ite if contains_quantifier(arena, args[0]) => None,
        _ => {
            for &argument in args {
                collect_positive_universal_binders(arena, argument, positive, binders)?;
            }
            Some(())
        }
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
