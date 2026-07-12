//! Untrusted candidate search for ADR-0130/0131 quantified-BV model certificates.

use std::collections::BTreeSet;

use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, WideUint, eval};

#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use crate::quant_bv_model_sat_cert::{
    QuantifiedBvModelSatCertificate, QuantifiedBvModelSatProof, admitted_free_bv_symbols,
    check_quantified_bv_model_sat, direct_negated_universal, negated_existential_interval_shape,
};
use crate::{CheckResult, Model, SolverConfig, SolverError};

const FREE_BV_CANDIDATE_BITS: usize = 8;
const TOTAL_FREE_BV_BITS_CAP: u32 = 4_096;

/// Searches low-bit-complete free-BV candidates and checks every source assertion.
pub(crate) fn decide_quantified_bv_model_sat(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<CheckResult>, SolverError> {
    if assertions.is_empty()
        || !assertions
            .iter()
            .any(|&term| contains_quantifier(arena, term))
    {
        return Ok(None);
    }
    let mut free = BTreeSet::new();
    for &assertion in assertions {
        if contains_quantifier(arena, assertion) {
            let Some(symbols) = admitted_free_bv_symbols(arena, assertion) else {
                return Ok(None);
            };
            free.extend(symbols);
        }
    }
    let free = free.into_iter().collect::<Vec<_>>();
    if free
        .iter()
        .try_fold(0u32, |total, symbol| {
            let Sort::BitVec(width) = arena.symbol(*symbol).1 else {
                return None;
            };
            total.checked_add(width)
        })
        .is_none_or(|bits| bits > TOTAL_FREE_BV_BITS_CAP)
    {
        return Ok(None);
    }
    let deadline = config
        .timeout
        .and_then(|timeout| Instant::now().checked_add(timeout));

    if let [assertion] = assertions
        && let Some(candidate_config) = config_with_deadline(config, deadline)
        && let Some(model) =
            find_negated_existential_interval_model(arena, *assertion, &free, &candidate_config)?
    {
        return Ok(Some(CheckResult::Sat(model)));
    }
    if free.len() > FREE_BV_CANDIDATE_BITS {
        return Ok(None);
    }

    for mask in 0usize..(1usize << free.len()) {
        let Some(candidate_config) = config_with_deadline(config, deadline) else {
            return Ok(None);
        };
        let values = free
            .iter()
            .enumerate()
            .map(|(index, &symbol)| {
                let Sort::BitVec(width) = arena.symbol(symbol).1 else {
                    unreachable!()
                };
                (
                    symbol,
                    bv_value(width, u128::from((mask >> index) & 1 == 1)),
                )
            })
            .collect::<Vec<_>>();
        if let Some(model) = check_candidate(arena, assertions, &values, &candidate_config)? {
            return Ok(Some(CheckResult::Sat(model)));
        }
    }
    Ok(None)
}

fn find_negated_existential_interval_model(
    arena: &TermArena,
    assertion: TermId,
    free: &[SymbolId],
    config: &SolverConfig,
) -> Result<Option<Model>, SolverError> {
    let Some(shape) = negated_existential_interval_shape(arena, assertion) else {
        return Ok(None);
    };
    let mut scratch = arena.clone();
    let lower_le_upper = scratch
        .bv_sle(shape.lower, shape.upper)
        .map_err(|error| SolverError::Backend(error.to_string()))?;
    let upper_le_cap = scratch
        .bv_sle(shape.upper, shape.cap)
        .map_err(|error| SolverError::Backend(error.to_string()))?;
    let false_conclusion = scratch
        .not(shape.ground_false)
        .map_err(|error| SolverError::Backend(error.to_string()))?;
    let mut query = shape.ground_true;
    query.extend([lower_le_upper, upper_le_cap, false_conclusion]);
    let outcome = match crate::auto::check_auto(&mut scratch, &query, config) {
        Ok(outcome) => outcome,
        Err(SolverError::Unsupported(_)) => return Ok(None),
        Err(error) => return Err(error),
    };
    let CheckResult::Sat(candidate) = outcome else {
        return Ok(None);
    };
    let free_values = free
        .iter()
        .map(|&symbol| {
            (
                symbol,
                candidate
                    .get(symbol)
                    .unwrap_or_else(|| zero_value(scratch.symbol(symbol).1)),
            )
        })
        .collect::<Vec<_>>();
    let certificate = QuantifiedBvModelSatCertificate {
        assertion,
        free_values: free_values.clone(),
        proof: QuantifiedBvModelSatProof::NegatedExistentialIntervalImplication {
            binder: shape.binder,
        },
    };
    if !check_quantified_bv_model_sat(arena, assertion, &certificate) {
        return Ok(None);
    }
    let mut model = Model::new();
    for (symbol, value) in free_values {
        model.set(symbol, value);
    }
    model.set_quantified_bv_model_sat_certificate(certificate);
    if crate::check_model(arena, &[assertion], &model)? {
        Ok(Some(model))
    } else {
        Err(SolverError::Backend(
            "generated interval-certified quantified-BV model failed canonical source replay"
                .to_owned(),
        ))
    }
}

fn check_candidate(
    arena: &TermArena,
    assertions: &[TermId],
    values: &[(SymbolId, Value)],
    config: &SolverConfig,
) -> Result<Option<Model>, SolverError> {
    let mut model = Model::new();
    for (symbol, value) in values {
        model.set(*symbol, value.clone());
    }
    let assignment = model.to_assignment();
    for &assertion in assertions {
        if !contains_quantifier(arena, assertion) {
            if !matches!(eval(arena, assertion, &assignment), Ok(Value::Bool(true))) {
                return Ok(None);
            }
            continue;
        }
        let Some(expected) = admitted_free_bv_symbols(arena, assertion) else {
            return Ok(None);
        };
        let free_values = expected
            .iter()
            .map(|symbol| {
                values
                    .iter()
                    .find(|(candidate, _)| candidate == symbol)
                    .cloned()
            })
            .collect::<Option<Vec<_>>>();
        let Some(free_values) = free_values else {
            return Ok(None);
        };

        let parity = QuantifiedBvModelSatCertificate {
            assertion,
            free_values: free_values.clone(),
            proof: QuantifiedBvModelSatProof::AffineLsbUniversal,
        };
        let certificate = if check_quantified_bv_model_sat(arena, assertion, &parity) {
            parity
        } else if let Some(witness) =
            find_negated_universal_witness(arena, assertion, free_values, values, config)?
        {
            witness
        } else {
            return Ok(None);
        };
        model.set_quantified_bv_model_sat_certificate(certificate);
    }
    if crate::check_model(arena, assertions, &model)? {
        Ok(Some(model))
    } else {
        Err(SolverError::Backend(
            "generated quantified-BV model failed canonical source replay".to_owned(),
        ))
    }
}

fn find_negated_universal_witness(
    arena: &TermArena,
    assertion: TermId,
    free_values: Vec<(SymbolId, Value)>,
    all_values: &[(SymbolId, Value)],
    config: &SolverConfig,
) -> Result<Option<QuantifiedBvModelSatCertificate>, SolverError> {
    let Some((binders, body)) = direct_negated_universal(arena, assertion) else {
        return Ok(None);
    };
    let mut scratch = arena.clone();
    let negated_body = scratch
        .not(body)
        .map_err(|error| SolverError::Backend(error.to_string()))?;
    let mut query = vec![negated_body];
    for (symbol, value) in all_values {
        let variable = scratch.var(*symbol);
        let constant = value_term(&mut scratch, value)?;
        query.push(
            scratch
                .eq(variable, constant)
                .map_err(|error| SolverError::Backend(error.to_string()))?,
        );
    }
    let outcome = match crate::auto::check_auto(&mut scratch, &query, config) {
        Ok(outcome) => outcome,
        Err(SolverError::Unsupported(_)) => return Ok(None),
        Err(error) => return Err(error),
    };
    let CheckResult::Sat(candidate) = outcome else {
        return Ok(None);
    };
    let values = binders
        .iter()
        .map(|binder| {
            candidate
                .get(*binder)
                .unwrap_or_else(|| zero_value(scratch.symbol(*binder).1))
        })
        .collect::<Vec<_>>();
    let certificate = QuantifiedBvModelSatCertificate {
        assertion,
        free_values,
        proof: QuantifiedBvModelSatProof::NegatedUniversalWitness { binders, values },
    };
    Ok(check_quantified_bv_model_sat(arena, assertion, &certificate).then_some(certificate))
}

fn value_term(arena: &mut TermArena, value: &Value) -> Result<TermId, SolverError> {
    match value {
        Value::Bv { width, value } => arena
            .bv_const(*width, *value)
            .map_err(|error| SolverError::Backend(error.to_string())),
        Value::WideBv(value) => Ok(arena.wide_bv_const(value.clone())),
        _ => Err(SolverError::Backend(
            "quantified-BV candidate carried a non-BV value".to_owned(),
        )),
    }
}

fn zero_value(sort: Sort) -> Value {
    match sort {
        Sort::Bool => Value::Bool(false),
        Sort::BitVec(width) => bv_value(width, 0),
        _ => unreachable!("admission permits only Bool/BV binders"),
    }
}

fn bv_value(width: u32, value: u128) -> Value {
    if width <= 128 {
        Value::Bv { width, value }
    } else {
        Value::WideBv(WideUint::from_u128(value, width))
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

fn config_with_deadline(config: &SolverConfig, deadline: Option<Instant>) -> Option<SolverConfig> {
    let mut candidate = config.clone();
    if let Some(deadline) = deadline {
        let remaining = deadline.checked_duration_since(Instant::now())?;
        if remaining.is_zero() {
            return None;
        }
        candidate.timeout = Some(remaining);
    }
    Some(candidate)
}
