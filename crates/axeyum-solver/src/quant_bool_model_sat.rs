//! Checked free-Boolean models for quantified Bool/Int/BV assertions
//! (ADR-0107/0123/0133).
//!
//! Search erases quantifiers to obtain a ground Boolean candidate, but that
//! erasure has no proof status. A result is returned only when the independent
//! checker below proves every untouched original assertion under the candidate
//! free-Boolean assignment. Bound Booleans are enumerated; bound integers stay
//! symbolic and are compared only by checked affine normalization. Admitted
//! positive Bool/BV universals may instead carry a source-bound proof of their
//! exact negated quantifier-free residual.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use axeyum_ir::{
    Assignment, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval, well_founded_default,
};

use crate::auto::check_auto;
#[cfg(not(target_arch = "wasm32"))]
use crate::proof::export_qf_bv_unsat_proof_within;
use crate::proof::{UnsatProof, UnsatProofOutcome};
use crate::quant_counterexample_cover::{
    QuantifiedCounterexampleCoverCertificate, case_from_counterexample,
    check_quantified_counterexample_cover_with_config,
};
use crate::{
    ArithDpllOutcome, CheckResult, Model, SolverConfig, SolverError, certify_arith_dpll_unsat,
};

#[cfg(not(target_arch = "wasm32"))]
use std::time::{Duration, Instant};
#[cfg(target_arch = "wasm32")]
use web_time::{Duration, Instant};

const MAX_FREE_BOOLEANS: usize = 64;
const MAX_CANDIDATES: usize = 256;
const MAX_BOUND_BOOL_BRANCHES: u64 = 131_072;
const MAX_CHECK_NODES: u64 = 100_000;
/// Maximum binders admitted by a residual-QF_BV model proof.
pub const QUANT_BOOL_BV_MODEL_BINDER_CAP: usize = 128;
/// Maximum distinct source nodes admitted by a residual-QF_BV model proof.
pub const QUANT_BOOL_BV_MODEL_NODE_CAP: usize = 4_096;
/// Maximum source depth admitted before recursive residual reconstruction.
pub const QUANT_BOOL_BV_MODEL_DEPTH_CAP: usize = 256;

/// Independently checked reason that a complete free-Boolean model satisfies
/// one quantified assertion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QuantifiedBoolModelSatProof {
    /// Boolean structure, bounded Boolean enumeration, and affine integer
    /// normalization prove the untouched assertion directly (ADR-0107/0123).
    Structural,
    /// Opening admitted positive universals under the complete free-Boolean
    /// model leaves a `QF_BV` validity whose negation has this checked proof.
    PositiveUniversalQfBv {
        /// Source-bound refutation of the deterministically rebuilt residual.
        residual_proof: UnsatProof,
    },
}

/// A checked free-Boolean interpretation for one original quantified assertion.
///
/// Values are strictly ordered by symbol ID and cover exactly the assertion's
/// free Boolean symbols. Canonical model replay checks both this structure and
/// agreement with the enclosing [`Model`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifiedBoolModelSatCertificate {
    /// The untouched original assertion proved by this certificate.
    pub assertion: TermId,
    /// Complete free-Boolean interpretation for that assertion.
    pub values: Vec<(SymbolId, bool)>,
    /// Independently checked source-level proof mode.
    pub proof: QuantifiedBoolModelSatProof,
}

/// Independently checks a Boolean-guard SAT certificate against original IR.
#[must_use]
pub fn check_quantified_bool_model_sat(
    arena: &TermArena,
    assertion: TermId,
    cert: &QuantifiedBoolModelSatCertificate,
) -> bool {
    let config = SolverConfig::default().with_timeout(Duration::from_secs(10));
    matches!(
        check_quantified_bool_model_sat_internal(arena, assertion, cert, &config),
        CertificateCheck::Valid
    )
}

pub(crate) enum CertificateCheck {
    Valid,
    Counterexample(Model),
    Declined,
}

pub(crate) fn check_quantified_bool_model_sat_internal(
    arena: &TermArena,
    assertion: TermId,
    cert: &QuantifiedBoolModelSatCertificate,
    config: &SolverConfig,
) -> CertificateCheck {
    if cert.assertion != assertion || !contains_quantifier(arena, assertion) {
        return CertificateCheck::Declined;
    }
    let Some(free) = admitted_free_booleans(arena, &[assertion]) else {
        return CertificateCheck::Declined;
    };
    if cert.values.len() != free.len()
        || cert
            .values
            .iter()
            .zip(&free)
            .any(|(&(symbol, _), expected)| symbol != *expected)
    {
        return CertificateCheck::Declined;
    }
    let mut environment = BTreeMap::new();
    for &(symbol, value) in &cert.values {
        if environment.insert(symbol, value).is_some() {
            return CertificateCheck::Declined;
        }
    }
    match &cert.proof {
        QuantifiedBoolModelSatProof::Structural => {
            let mut budget = CheckBudget::default();
            let truth = eval_truth(arena, assertion, &mut environment, &mut budget);
            if truth == Truth::True {
                return CertificateCheck::Valid;
            }
            if contains_bv_syntax(arena, assertion) {
                return CertificateCheck::Declined;
            }
            let mut scratch = arena.clone();
            let Some(counterexample) =
                quantified_counterexample(&mut scratch, assertion, &cert.values)
            else {
                return CertificateCheck::Declined;
            };
            let Ok(outcome) = certify_arith_dpll_unsat(&mut scratch, &counterexample, config)
            else {
                return CertificateCheck::Declined;
            };
            match outcome {
                ArithDpllOutcome::Unsat(_) => CertificateCheck::Valid,
                ArithDpllOutcome::Sat(model) => CertificateCheck::Counterexample(model),
                ArithDpllOutcome::Unknown(_) => CertificateCheck::Declined,
            }
        }
        QuantifiedBoolModelSatProof::PositiveUniversalQfBv { residual_proof } => {
            let Ok(Some((scratch, residual, _))) =
                positive_universal_bv_residual(arena, assertion, &cert.values)
            else {
                return CertificateCheck::Declined;
            };
            match residual_proof.recheck_for_bool_terms(&scratch, &[residual]) {
                Ok(true) => CertificateCheck::Valid,
                Ok(false) | Err(_) => CertificateCheck::Declined,
            }
        }
    }
}

/// Searches for a checked free-Boolean model of a quantified Bool/Int query.
///
/// Quantifier erasure and QF solving only propose candidates. Failure to prove
/// an original assertion blocks that complete Boolean assignment or declines;
/// it never produces a verdict.
pub(crate) fn decide_quantified_by_bool_model(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<CheckResult>, SolverError> {
    Ok(
        match search_quantified_bool_model(arena, assertions, config)? {
            QuantifiedBoolSearch::Sat(model) => Some(CheckResult::Sat(model)),
            QuantifiedBoolSearch::Unsat(_) => Some(CheckResult::Unsat),
            QuantifiedBoolSearch::Declined => None,
        },
    )
}

pub(crate) fn find_quantified_counterexample_cover(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<QuantifiedCounterexampleCoverCertificate>, SolverError> {
    Ok(
        match search_quantified_bool_model(arena, assertions, config)? {
            QuantifiedBoolSearch::Unsat(certificate) => Some(certificate),
            QuantifiedBoolSearch::Sat(_) | QuantifiedBoolSearch::Declined => None,
        },
    )
}

enum QuantifiedBoolSearch {
    Sat(Model),
    Unsat(QuantifiedCounterexampleCoverCertificate),
    Declined,
}

fn search_quantified_bool_model(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<QuantifiedBoolSearch, SolverError> {
    let Some(free) = admitted_free_booleans(arena, assertions) else {
        return Ok(QuantifiedBoolSearch::Declined);
    };
    if free.is_empty() || free.len() > MAX_FREE_BOOLEANS {
        return Ok(QuantifiedBoolSearch::Declined);
    }

    let mut memo = HashMap::new();
    let mut skeleton = assertions
        .iter()
        .map(|&assertion| erase_quantifiers(arena, assertion, &mut memo))
        .collect::<Vec<_>>();
    let deadline = config
        .timeout
        .and_then(|timeout| Instant::now().checked_add(timeout));
    let mut cases = Vec::new();
    let mut refinements = BTreeSet::new();

    for _ in 0..MAX_CANDIDATES {
        let Some(candidate_config) = config_with_deadline(config, deadline) else {
            return Ok(QuantifiedBoolSearch::Declined);
        };
        let mut model = match check_auto(arena, &skeleton, &candidate_config)? {
            CheckResult::Sat(model) => model,
            CheckResult::Unsat if !cases.is_empty() => {
                let certificate = QuantifiedCounterexampleCoverCertificate { cases };
                return Ok(
                    if check_quantified_counterexample_cover_with_config(
                        arena,
                        assertions,
                        &certificate,
                        &candidate_config,
                    ) {
                        QuantifiedBoolSearch::Unsat(certificate)
                    } else {
                        QuantifiedBoolSearch::Declined
                    },
                );
            }
            CheckResult::Unsat | CheckResult::Unknown(_) => {
                return Ok(QuantifiedBoolSearch::Declined);
            }
        };
        complete_free_booleans(&mut model, &free);
        match assess_candidate(arena, assertions, &mut model, &candidate_config, deadline)? {
            CandidateAssessment::Valid => return Ok(QuantifiedBoolSearch::Sat(model)),
            CandidateAssessment::Block { cube, case } => {
                if let Some(case) = case {
                    if cases.contains(&case) {
                        return Ok(QuantifiedBoolSearch::Declined);
                    }
                    cases.push(case);
                }
                skeleton.push(block_values(arena, &cube)?);
            }
            CandidateAssessment::Refine { instance, cube } => {
                if refinements.insert(instance) {
                    skeleton.push(instance);
                } else {
                    skeleton.push(block_values(arena, &cube)?);
                }
            }
        }
    }
    Ok(QuantifiedBoolSearch::Declined)
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

fn complete_free_booleans(model: &mut Model, free: &[SymbolId]) {
    for &symbol in free {
        if !matches!(model.get(symbol), Some(Value::Bool(_))) {
            model.set(symbol, Value::Bool(false));
        }
    }
}

enum CandidateAssessment {
    Valid,
    Block {
        cube: Vec<(SymbolId, bool)>,
        case: Option<crate::QuantifiedCounterexampleCoverCase>,
    },
    Refine {
        instance: TermId,
        cube: Vec<(SymbolId, bool)>,
    },
}

fn assess_candidate(
    arena: &mut TermArena,
    assertions: &[TermId],
    model: &mut Model,
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> Result<CandidateAssessment, SolverError> {
    let assignment = model.to_assignment();
    let all_free = admitted_free_booleans(arena, assertions).unwrap_or_default();
    let mut certificates = Vec::new();
    for &assertion in assertions {
        if contains_quantifier(arena, assertion) {
            let Some(free) = admitted_free_booleans(arena, &[assertion]) else {
                return Ok(CandidateAssessment::Block {
                    cube: model_values(model, &all_free),
                    case: None,
                });
            };
            let mut values = Vec::with_capacity(free.len());
            for &symbol in &free {
                let Some(Value::Bool(value)) = model.get(symbol) else {
                    return Ok(CandidateAssessment::Block {
                        cube: model_values(model, &free),
                        case: None,
                    });
                };
                values.push((symbol, value));
            }
            let cert = QuantifiedBoolModelSatCertificate {
                assertion,
                values,
                proof: QuantifiedBoolModelSatProof::Structural,
            };
            match check_quantified_bool_model_sat_internal(arena, assertion, &cert, config) {
                CertificateCheck::Valid => certificates.push(cert),
                CertificateCheck::Counterexample(counterexample) => {
                    let cube = counterexample_cube(arena, assertion, &cert, &counterexample)
                        .unwrap_or_else(|| cert.values.clone());
                    let case =
                        case_from_counterexample(arena, assertion, cube.clone(), &counterexample);
                    return Ok(CandidateAssessment::Block { cube, case });
                }
                CertificateCheck::Declined => {
                    match assess_positive_universal_bv_candidate(
                        arena,
                        assertion,
                        &cert.values,
                        model,
                        config,
                        deadline,
                    )? {
                        PositiveUniversalBvAssessment::Valid(cert) => certificates.push(cert),
                        PositiveUniversalBvAssessment::Counterexample(instance) => {
                            return Ok(CandidateAssessment::Refine {
                                instance,
                                cube: cert.values,
                            });
                        }
                        PositiveUniversalBvAssessment::Declined => {
                            return Ok(CandidateAssessment::Block {
                                cube: cert.values,
                                case: None,
                            });
                        }
                    }
                }
            }
        } else if !matches!(eval(arena, assertion, &assignment), Ok(Value::Bool(true))) {
            return Ok(CandidateAssessment::Block {
                cube: model_values(
                    model,
                    &admitted_free_booleans(arena, assertions).unwrap_or_default(),
                ),
                case: None,
            });
        }
    }
    for cert in certificates {
        model.set_quantified_bool_model_sat_certificate(cert);
    }
    Ok(CandidateAssessment::Valid)
}

enum PositiveUniversalBvAssessment {
    Valid(QuantifiedBoolModelSatCertificate),
    Counterexample(TermId),
    Declined,
}

fn assess_positive_universal_bv_candidate(
    arena: &mut TermArena,
    assertion: TermId,
    values: &[(SymbolId, bool)],
    model: &Model,
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> Result<PositiveUniversalBvAssessment, SolverError> {
    let Some((mut scratch, residual, admitted)) =
        positive_universal_bv_residual(arena, assertion, values)?
    else {
        return Ok(PositiveUniversalBvAssessment::Declined);
    };
    let outcome = match check_auto(&mut scratch, &[residual], config) {
        Ok(outcome) => outcome,
        Err(SolverError::Unsupported(_)) => {
            return Ok(PositiveUniversalBvAssessment::Declined);
        }
        Err(error) => return Err(error),
    };
    match outcome {
        CheckResult::Sat(counterexample) => {
            let Some(instance) = instantiate_positive_universal_bv_counterexample(
                arena,
                assertion,
                &admitted,
                &counterexample,
            )?
            else {
                return Ok(PositiveUniversalBvAssessment::Declined);
            };
            if !matches!(
                eval(arena, instance, &model.to_assignment()),
                Ok(Value::Bool(false))
            ) {
                return Ok(PositiveUniversalBvAssessment::Declined);
            }
            Ok(PositiveUniversalBvAssessment::Counterexample(instance))
        }
        CheckResult::Unsat => {
            let proof = match export_positive_universal_bv_proof(&scratch, residual, deadline)? {
                UnsatProofOutcome::Proved(proof) => proof,
                UnsatProofOutcome::Satisfiable | UnsatProofOutcome::Inconclusive => {
                    return Ok(PositiveUniversalBvAssessment::Declined);
                }
            };
            let cert = QuantifiedBoolModelSatCertificate {
                assertion,
                values: values.to_vec(),
                proof: QuantifiedBoolModelSatProof::PositiveUniversalQfBv {
                    residual_proof: proof,
                },
            };
            if matches!(
                check_quantified_bool_model_sat_internal(arena, assertion, &cert, config),
                CertificateCheck::Valid
            ) {
                Ok(PositiveUniversalBvAssessment::Valid(cert))
            } else {
                Err(SolverError::Backend(
                    "generated residual-QF_BV free-Boolean model proof failed independent replay"
                        .to_owned(),
                ))
            }
        }
        CheckResult::Unknown(_) => Ok(PositiveUniversalBvAssessment::Declined),
    }
}

#[cfg(not(target_arch = "wasm32"))]
fn export_positive_universal_bv_proof(
    arena: &TermArena,
    residual: TermId,
    deadline: Option<Instant>,
) -> Result<UnsatProofOutcome, SolverError> {
    export_qf_bv_unsat_proof_within(arena, &[residual], deadline)
}

#[cfg(target_arch = "wasm32")]
fn export_positive_universal_bv_proof(
    _arena: &TermArena,
    _residual: TermId,
    _deadline: Option<Instant>,
) -> Result<UnsatProofOutcome, SolverError> {
    // The proof exporter currently uses `std::time::Instant`; preserve the
    // existing browser-safe search clock and decline this new route instead.
    Ok(UnsatProofOutcome::Inconclusive)
}

#[derive(Debug, Clone)]
struct AdmittedPositiveUniversalBv {
    binders: Vec<SymbolId>,
    free: Vec<SymbolId>,
}

fn positive_universal_bv_residual(
    arena: &TermArena,
    assertion: TermId,
    values: &[(SymbolId, bool)],
) -> Result<Option<(TermArena, TermId, AdmittedPositiveUniversalBv)>, SolverError> {
    let Some(admitted) = admitted_positive_universal_bv(arena, assertion) else {
        return Ok(None);
    };
    if values.len() != admitted.free.len()
        || values
            .iter()
            .zip(&admitted.free)
            .any(|(&(symbol, _), expected)| symbol != *expected)
    {
        return Ok(None);
    }
    let mut scratch = arena.clone();
    let replacements = values
        .iter()
        .map(|&(symbol, value)| (scratch.var(symbol), scratch.bool_const(value)))
        .collect::<HashMap<_, _>>();
    let Some(opened) = rewrite_positive_universals(
        &mut scratch,
        assertion,
        true,
        &replacements,
        &mut HashMap::new(),
    ) else {
        return Ok(None);
    };
    if contains_quantifier(&scratch, opened) {
        return Ok(None);
    }
    let residual = scratch
        .not(opened)
        .map_err(|error| SolverError::Backend(error.to_string()))?;
    Ok(Some((scratch, residual, admitted)))
}

fn instantiate_positive_universal_bv_counterexample(
    arena: &mut TermArena,
    assertion: TermId,
    admitted: &AdmittedPositiveUniversalBv,
    counterexample: &Model,
) -> Result<Option<TermId>, SolverError> {
    let mut replacements = HashMap::new();
    for &binder in &admitted.binders {
        let sort = arena.symbol(binder).1;
        let Some(value) = counterexample
            .get(binder)
            .or_else(|| well_founded_default(arena, sort))
        else {
            return Ok(None);
        };
        if value.sort() != sort {
            return Ok(None);
        }
        let constant = bool_bv_value_to_const(arena, &value)?;
        replacements.insert(arena.var(binder), constant);
    }
    let Some(instance) =
        rewrite_positive_universals(arena, assertion, true, &replacements, &mut HashMap::new())
    else {
        return Ok(None);
    };
    Ok((!contains_quantifier(arena, instance)).then_some(instance))
}

fn bool_bv_value_to_const(arena: &mut TermArena, value: &Value) -> Result<TermId, SolverError> {
    match value {
        Value::Bool(value) => Ok(arena.bool_const(*value)),
        Value::Bv { width, value } => arena
            .bv_const(*width, *value)
            .map_err(|error| SolverError::Backend(error.to_string())),
        Value::WideBv(value) => Ok(arena.wide_bv_const(value.clone())),
        _ => Err(SolverError::Backend(
            "positive-universal BV counterexample carried a non-Bool/BV value".to_owned(),
        )),
    }
}

fn admitted_positive_universal_bv(
    arena: &TermArena,
    assertion: TermId,
) -> Option<AdmittedPositiveUniversalBv> {
    let mut source_nodes = BTreeSet::new();
    let mut visited = BTreeSet::new();
    let mut binders = BTreeSet::new();
    let mut binder_order = Vec::new();
    let mut free = BTreeSet::new();
    let mut stack = vec![(assertion, true, 1usize, BTreeSet::new())];
    while let Some((term, positive, depth, bound)) = stack.pop() {
        if depth > QUANT_BOOL_BV_MODEL_DEPTH_CAP
            || !matches!(arena.sort_of(term), Sort::Bool | Sort::BitVec(_))
        {
            return None;
        }
        source_nodes.insert(term);
        if source_nodes.len() > QUANT_BOOL_BV_MODEL_NODE_CAP {
            return None;
        }
        let context = bound.iter().copied().collect::<Vec<_>>();
        if !visited.insert((term, positive, context)) {
            continue;
        }
        if visited.len() > QUANT_BOOL_BV_MODEL_NODE_CAP {
            return None;
        }
        match arena.node(term) {
            TermNode::Symbol(symbol) => {
                if !bound.contains(symbol) {
                    if binders.contains(symbol) || arena.symbol(*symbol).1 != Sort::Bool {
                        return None;
                    }
                    free.insert(*symbol);
                }
            }
            TermNode::App {
                op: Op::Apply(_) | Op::Exists(_),
                ..
            }
            | TermNode::IntConst(_)
            | TermNode::RealConst(_) => return None,
            TermNode::App {
                op: Op::Forall(binder),
                args,
            } => {
                let [body] = &**args else { return None };
                if !positive
                    || !matches!(arena.symbol(*binder).1, Sort::Bool | Sort::BitVec(_))
                    || free.contains(binder)
                    || !binders.insert(*binder)
                    || binders.len() > QUANT_BOOL_BV_MODEL_BINDER_CAP
                {
                    return None;
                }
                binder_order.push(*binder);
                let mut nested = bound;
                if !nested.insert(*binder) {
                    return None;
                }
                stack.push((*body, positive, depth + 1, nested));
            }
            TermNode::App { op, args } => {
                let quantified_args = args
                    .iter()
                    .map(|&argument| contains_quantifier(arena, argument))
                    .collect::<Vec<_>>();
                let has_quantified_arg = quantified_args.iter().any(|&found| found);
                if has_quantified_arg
                    && !matches!(
                        op,
                        Op::BoolNot | Op::BoolAnd | Op::BoolOr | Op::BoolImplies | Op::Ite
                    )
                {
                    return None;
                }
                if *op == Op::Ite && quantified_args.first() == Some(&true) {
                    return None;
                }
                for (index, &argument) in args.iter().enumerate().rev() {
                    let argument_positive = match op {
                        Op::BoolNot => !positive,
                        Op::BoolImplies if index == 0 => !positive,
                        _ => positive,
                    };
                    stack.push((argument, argument_positive, depth + 1, bound.clone()));
                }
            }
            TermNode::BoolConst(_) | TermNode::BvConst { .. } | TermNode::WideBvConst(_) => {}
        }
    }
    if binder_order.is_empty() || free.is_empty() || free.len() > MAX_FREE_BOOLEANS {
        return None;
    }
    Some(AdmittedPositiveUniversalBv {
        binders: binder_order,
        free: free.into_iter().collect(),
    })
}

fn model_values(model: &Model, symbols: &[SymbolId]) -> Vec<(SymbolId, bool)> {
    symbols
        .iter()
        .filter_map(|&symbol| match model.get(symbol) {
            Some(Value::Bool(value)) => Some((symbol, value)),
            _ => None,
        })
        .collect()
}

pub(crate) fn counterexample_cube(
    arena: &mut TermArena,
    assertion: TermId,
    cert: &QuantifiedBoolModelSatCertificate,
    counterexample: &Model,
) -> Option<Vec<(SymbolId, bool)>> {
    let unquantified =
        rewrite_positive_universals(arena, assertion, true, &HashMap::new(), &mut HashMap::new())?;
    if contains_quantifier(arena, unquantified) {
        return None;
    }
    let free = cert
        .values
        .iter()
        .map(|&(symbol, _)| symbol)
        .collect::<BTreeSet<_>>();
    let mut assignment = counterexample.to_assignment();
    for &(symbol, value) in &cert.values {
        assignment.set(symbol, Value::Bool(value));
    }
    let (value, dependencies) = bool_value_dependencies(arena, unquantified, &assignment, &free)?;
    if value {
        return None;
    }
    let cube = cert
        .values
        .iter()
        .copied()
        .filter(|(symbol, _)| dependencies.contains(symbol))
        .collect::<Vec<_>>();
    (!cube.is_empty()).then_some(cube)
}

fn bool_value_dependencies(
    arena: &TermArena,
    term: TermId,
    assignment: &Assignment,
    free: &BTreeSet<SymbolId>,
) -> Option<(bool, BTreeSet<SymbolId>)> {
    let Value::Bool(value) = eval(arena, term, assignment).ok()? else {
        return None;
    };
    let dependencies = match arena.node(term) {
        TermNode::BoolConst(_) => BTreeSet::new(),
        TermNode::Symbol(symbol) => {
            if free.contains(symbol) {
                BTreeSet::from([*symbol])
            } else {
                BTreeSet::new()
            }
        }
        TermNode::App { op, args } => match op {
            Op::BoolNot => bool_value_dependencies(arena, args[0], assignment, free)?.1,
            Op::BoolAnd => {
                let left = bool_value_dependencies(arena, args[0], assignment, free)?;
                let right = bool_value_dependencies(arena, args[1], assignment, free)?;
                if value {
                    union(left.1, right.1)
                } else if !left.0 {
                    left.1
                } else {
                    right.1
                }
            }
            Op::BoolOr => {
                let left = bool_value_dependencies(arena, args[0], assignment, free)?;
                let right = bool_value_dependencies(arena, args[1], assignment, free)?;
                if !value {
                    union(left.1, right.1)
                } else if left.0 {
                    left.1
                } else {
                    right.1
                }
            }
            Op::BoolImplies => {
                let left = bool_value_dependencies(arena, args[0], assignment, free)?;
                let right = bool_value_dependencies(arena, args[1], assignment, free)?;
                if !value {
                    union(left.1, right.1)
                } else if !left.0 {
                    left.1
                } else {
                    right.1
                }
            }
            Op::Ite if arena.sort_of(term) == Sort::Bool => {
                let condition = bool_value_dependencies(arena, args[0], assignment, free)?;
                let branch = bool_value_dependencies(
                    arena,
                    args[if condition.0 { 1 } else { 2 }],
                    assignment,
                    free,
                )?;
                union(condition.1, branch.1)
            }
            Op::BoolXor | Op::Eq if arena.sort_of(args[0]) == Sort::Bool => {
                let left = bool_value_dependencies(arena, args[0], assignment, free)?;
                let right = bool_value_dependencies(arena, args[1], assignment, free)?;
                union(left.1, right.1)
            }
            _ => free_bool_occurrences(arena, term, free),
        },
        _ => return None,
    };
    Some((value, dependencies))
}

fn union(mut left: BTreeSet<SymbolId>, right: BTreeSet<SymbolId>) -> BTreeSet<SymbolId> {
    left.extend(right);
    left
}

fn free_bool_occurrences(
    arena: &TermArena,
    term: TermId,
    free: &BTreeSet<SymbolId>,
) -> BTreeSet<SymbolId> {
    let mut found = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut stack = vec![term];
    while let Some(current) = stack.pop() {
        if !seen.insert(current) {
            continue;
        }
        match arena.node(current) {
            TermNode::Symbol(symbol) if free.contains(symbol) => {
                found.insert(*symbol);
            }
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    found
}

fn quantified_counterexample(
    arena: &mut TermArena,
    assertion: TermId,
    values: &[(SymbolId, bool)],
) -> Option<Vec<TermId>> {
    let replacements = values
        .iter()
        .map(|&(symbol, value)| (arena.var(symbol), arena.bool_const(value)))
        .collect::<HashMap<_, _>>();
    let rewritten =
        rewrite_positive_universals(arena, assertion, true, &replacements, &mut HashMap::new())?;
    if contains_quantifier(arena, rewritten) {
        return None;
    }
    let Ok(simplified) = axeyum_rewrite::canonicalize_terms(arena, &[rewritten]) else {
        return None;
    };
    let result = arena.not(simplified.terms[0]).ok();
    crate::auto::lift_arith_ite(arena, &[result?]).ok()
}

pub(crate) fn rewrite_positive_universals(
    arena: &mut TermArena,
    term: TermId,
    positive: bool,
    replacements: &HashMap<TermId, TermId>,
    memo: &mut HashMap<(TermId, bool), TermId>,
) -> Option<TermId> {
    if let Some(&replacement) = replacements.get(&term) {
        return Some(replacement);
    }
    if let Some(&cached) = memo.get(&(term, positive)) {
        return Some(cached);
    }
    let rebuilt = match arena.node(term).clone() {
        TermNode::App {
            op: Op::Forall(_),
            args,
        } if positive => {
            let [body] = &*args else { return None };
            rewrite_positive_universals(arena, *body, positive, replacements, memo)?
        }
        TermNode::App {
            op: Op::Forall(_) | Op::Exists(_),
            ..
        } => return None,
        TermNode::App { op, args } => {
            let mut polarities = vec![positive; args.len()];
            match op {
                Op::BoolNot => polarities[0] = !positive,
                Op::BoolImplies => {
                    polarities[0] = !positive;
                    polarities[1] = positive;
                }
                Op::BoolXor | Op::Eq
                    if args
                        .iter()
                        .any(|&argument| contains_quantifier(arena, argument)) =>
                {
                    return None;
                }
                Op::Ite if contains_quantifier(arena, args[0]) => return None,
                _ => {}
            }
            let rewritten = args
                .iter()
                .zip(polarities)
                .map(|(&argument, polarity)| {
                    rewrite_positive_universals(arena, argument, polarity, replacements, memo)
                })
                .collect::<Option<Vec<_>>>()?;
            arena.rebuild_with_args(term, &rewritten)
        }
        _ => term,
    };
    memo.insert((term, positive), rebuilt);
    Some(rebuilt)
}

pub(crate) fn block_values(
    arena: &mut TermArena,
    values: &[(SymbolId, bool)],
) -> Result<TermId, SolverError> {
    let mut literals = Vec::with_capacity(values.len());
    for &(symbol, value) in values {
        let variable = arena.var(symbol);
        let literal = if value {
            arena
                .not(variable)
                .map_err(|error| SolverError::Backend(error.to_string()))?
        } else {
            variable
        };
        literals.push(literal);
    }
    fold_balanced(arena, &literals, false)
}

fn fold_balanced(
    arena: &mut TermArena,
    terms: &[TermId],
    conjunction: bool,
) -> Result<TermId, SolverError> {
    if terms.is_empty() {
        return Ok(arena.bool_const(conjunction));
    }
    let mut layer = terms.to_vec();
    while layer.len() > 1 {
        let mut next = Vec::with_capacity(layer.len().div_ceil(2));
        for pair in layer.chunks(2) {
            let term = if let [left, right] = pair {
                if conjunction {
                    arena.and(*left, *right)
                } else {
                    arena.or(*left, *right)
                }
                .map_err(|error| SolverError::Backend(error.to_string()))?
            } else {
                pair[0]
            };
            next.push(term);
        }
        layer = next;
    }
    Ok(layer[0])
}

pub(crate) fn erase_quantifiers(
    arena: &mut TermArena,
    term: TermId,
    memo: &mut HashMap<TermId, TermId>,
) -> TermId {
    if let Some(&cached) = memo.get(&term) {
        return cached;
    }
    let rebuilt = match arena.node(term).clone() {
        TermNode::App {
            op: Op::Forall(_) | Op::Exists(_),
            ..
        } => arena.bool_const(true),
        TermNode::App { args, .. } => {
            let args = args
                .iter()
                .map(|&argument| erase_quantifiers(arena, argument, memo))
                .collect::<Vec<_>>();
            arena.rebuild_with_args(term, &args)
        }
        _ => term,
    };
    memo.insert(term, rebuilt);
    rebuilt
}

pub(crate) fn admitted_free_booleans(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<Vec<SymbolId>> {
    let mut free = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut saw_quantifier = false;
    for &assertion in assertions {
        if arena.sort_of(assertion) != Sort::Bool
            || !collect_admitted(
                arena,
                assertion,
                &mut BTreeSet::new(),
                &mut free,
                &mut saw_quantifier,
                &mut seen,
            )
        {
            return None;
        }
    }
    saw_quantifier.then(|| free.into_iter().collect())
}

fn collect_admitted(
    arena: &TermArena,
    term: TermId,
    bound: &mut BTreeSet<SymbolId>,
    free: &mut BTreeSet<SymbolId>,
    saw_quantifier: &mut bool,
    seen: &mut BTreeSet<(TermId, Vec<SymbolId>)>,
) -> bool {
    let context = bound.iter().copied().collect();
    if !seen.insert((term, context)) {
        return true;
    }
    if !matches!(
        arena.sort_of(term),
        Sort::Bool | Sort::Int | Sort::BitVec(_)
    ) {
        return false;
    }
    match arena.node(term) {
        TermNode::Symbol(symbol) => {
            if !bound.contains(symbol) {
                match arena.symbol(*symbol).1 {
                    Sort::Bool => {
                        free.insert(*symbol);
                    }
                    Sort::BitVec(_) => {}
                    _ => return false,
                }
            }
            true
        }
        TermNode::App {
            op: Op::Apply(_), ..
        } => false,
        TermNode::App {
            op: Op::Forall(symbol) | Op::Exists(symbol),
            args,
        } => {
            let [body] = &**args else {
                return false;
            };
            *saw_quantifier = true;
            let inserted = bound.insert(*symbol);
            let admitted =
                inserted && collect_admitted(arena, *body, bound, free, saw_quantifier, seen);
            bound.remove(symbol);
            admitted
        }
        TermNode::App { args, .. } => args
            .iter()
            .all(|&argument| collect_admitted(arena, argument, bound, free, saw_quantifier, seen)),
        _ => true,
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

fn contains_bv_syntax(arena: &TermArena, term: TermId) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = vec![term];
    while let Some(current) = stack.pop() {
        if !seen.insert(current) {
            continue;
        }
        if matches!(arena.sort_of(current), Sort::BitVec(_)) {
            return true;
        }
        if let TermNode::App { args, .. } = arena.node(current) {
            stack.extend(args.iter().copied());
        }
    }
    false
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Truth {
    True,
    False,
    Unknown,
}

impl Truth {
    fn not(self) -> Self {
        match self {
            Self::True => Self::False,
            Self::False => Self::True,
            Self::Unknown => Self::Unknown,
        }
    }

    fn and(self, other: Self) -> Self {
        match (self, other) {
            (Self::False, _) | (_, Self::False) => Self::False,
            (Self::True, Self::True) => Self::True,
            _ => Self::Unknown,
        }
    }

    fn or(self, other: Self) -> Self {
        match (self, other) {
            (Self::True, _) | (_, Self::True) => Self::True,
            (Self::False, Self::False) => Self::False,
            _ => Self::Unknown,
        }
    }
}

#[derive(Default)]
struct CheckBudget {
    nodes: u64,
    bool_branches: u64,
    exhausted: bool,
}

fn eval_truth(
    arena: &TermArena,
    term: TermId,
    environment: &mut BTreeMap<SymbolId, bool>,
    budget: &mut CheckBudget,
) -> Truth {
    budget.nodes += 1;
    if budget.nodes > MAX_CHECK_NODES || budget.exhausted {
        budget.exhausted = true;
        return Truth::Unknown;
    }
    match arena.node(term) {
        TermNode::BoolConst(value) => Truth::from(*value),
        TermNode::Symbol(symbol) if arena.symbol(*symbol).1 == Sort::Bool => environment
            .get(symbol)
            .copied()
            .map_or(Truth::Unknown, Truth::from),
        TermNode::App { op, args } => match op {
            Op::BoolNot => unary_truth(arena, args, environment, budget).not(),
            Op::BoolAnd => binary_truth(arena, args, environment, budget, Truth::and),
            Op::BoolOr => binary_truth(arena, args, environment, budget, Truth::or),
            Op::BoolXor => binary_truth(arena, args, environment, budget, |left, right| {
                match (left, right) {
                    (Truth::True, Truth::True) | (Truth::False, Truth::False) => Truth::False,
                    (Truth::True, Truth::False) | (Truth::False, Truth::True) => Truth::True,
                    _ => Truth::Unknown,
                }
            }),
            Op::BoolImplies => binary_truth(arena, args, environment, budget, |left, right| {
                left.not().or(right)
            }),
            Op::Eq => eval_equality(arena, args, environment, budget),
            Op::Ite if arena.sort_of(term) == Sort::Bool => {
                eval_bool_ite(arena, args, environment, budget)
            }
            Op::IntLt | Op::IntLe | Op::IntGt | Op::IntGe => {
                eval_int_comparison(arena, *op, args, environment, budget)
            }
            Op::Forall(symbol) => eval_quantifier(arena, *symbol, args, true, environment, budget),
            Op::Exists(symbol) => eval_quantifier(arena, *symbol, args, false, environment, budget),
            _ => Truth::Unknown,
        },
        _ => Truth::Unknown,
    }
}

impl From<bool> for Truth {
    fn from(value: bool) -> Self {
        if value { Self::True } else { Self::False }
    }
}

fn unary_truth(
    arena: &TermArena,
    args: &[TermId],
    environment: &mut BTreeMap<SymbolId, bool>,
    budget: &mut CheckBudget,
) -> Truth {
    let [argument] = args else {
        return Truth::Unknown;
    };
    eval_truth(arena, *argument, environment, budget)
}

fn binary_truth(
    arena: &TermArena,
    args: &[TermId],
    environment: &mut BTreeMap<SymbolId, bool>,
    budget: &mut CheckBudget,
    combine: impl FnOnce(Truth, Truth) -> Truth,
) -> Truth {
    let [left, right] = args else {
        return Truth::Unknown;
    };
    let left = eval_truth(arena, *left, environment, budget);
    let right = eval_truth(arena, *right, environment, budget);
    combine(left, right)
}

fn eval_bool_ite(
    arena: &TermArena,
    args: &[TermId],
    environment: &mut BTreeMap<SymbolId, bool>,
    budget: &mut CheckBudget,
) -> Truth {
    let [condition, then_term, else_term] = args else {
        return Truth::Unknown;
    };
    match eval_truth(arena, *condition, environment, budget) {
        Truth::True => eval_truth(arena, *then_term, environment, budget),
        Truth::False => eval_truth(arena, *else_term, environment, budget),
        Truth::Unknown => {
            let then_value = eval_truth(arena, *then_term, environment, budget);
            let else_value = eval_truth(arena, *else_term, environment, budget);
            if then_value == else_value {
                then_value
            } else {
                Truth::Unknown
            }
        }
    }
}

fn eval_quantifier(
    arena: &TermArena,
    symbol: SymbolId,
    args: &[TermId],
    forall: bool,
    environment: &mut BTreeMap<SymbolId, bool>,
    budget: &mut CheckBudget,
) -> Truth {
    let [body] = args else {
        return Truth::Unknown;
    };
    if arena.symbol(symbol).1 != Sort::Bool {
        return eval_truth(arena, *body, environment, budget);
    }
    budget.bool_branches += 2;
    if budget.bool_branches > MAX_BOUND_BOOL_BRANCHES {
        budget.exhausted = true;
        return Truth::Unknown;
    }
    let previous = environment.insert(symbol, false);
    let when_false = eval_truth(arena, *body, environment, budget);
    environment.insert(symbol, true);
    let when_true = eval_truth(arena, *body, environment, budget);
    if let Some(value) = previous {
        environment.insert(symbol, value);
    } else {
        environment.remove(&symbol);
    }
    if forall {
        when_false.and(when_true)
    } else {
        when_false.or(when_true)
    }
}

fn eval_equality(
    arena: &TermArena,
    args: &[TermId],
    environment: &mut BTreeMap<SymbolId, bool>,
    budget: &mut CheckBudget,
) -> Truth {
    let [left, right] = args else {
        return Truth::Unknown;
    };
    if left == right {
        return Truth::True;
    }
    match arena.sort_of(*left) {
        Sort::Bool => {
            let left = eval_truth(arena, *left, environment, budget);
            let right = eval_truth(arena, *right, environment, budget);
            match (left, right) {
                (Truth::True, Truth::True) | (Truth::False, Truth::False) => Truth::True,
                (Truth::True, Truth::False) | (Truth::False, Truth::True) => Truth::False,
                _ => Truth::Unknown,
            }
        }
        Sort::Int => compare_affine(arena, *left, *right, environment, budget, Op::Eq),
        _ => Truth::Unknown,
    }
}

fn eval_int_comparison(
    arena: &TermArena,
    op: Op,
    args: &[TermId],
    environment: &mut BTreeMap<SymbolId, bool>,
    budget: &mut CheckBudget,
) -> Truth {
    let [left, right] = args else {
        return Truth::Unknown;
    };
    compare_affine(arena, *left, *right, environment, budget, op)
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Affine {
    constant: i128,
    terms: BTreeMap<TermId, i128>,
}

impl Affine {
    fn constant(value: i128) -> Self {
        Self {
            constant: value,
            terms: BTreeMap::new(),
        }
    }

    fn atom(term: TermId) -> Self {
        Self {
            constant: 0,
            terms: BTreeMap::from([(term, 1)]),
        }
    }

    fn add_scaled(&mut self, other: &Self, scale: i128) -> Option<()> {
        self.constant = self
            .constant
            .checked_add(other.constant.checked_mul(scale)?)?;
        for (&term, &coefficient) in &other.terms {
            let scaled = coefficient.checked_mul(scale)?;
            let updated = self
                .terms
                .get(&term)
                .copied()
                .unwrap_or(0)
                .checked_add(scaled)?;
            if updated == 0 {
                self.terms.remove(&term);
            } else {
                self.terms.insert(term, updated);
            }
        }
        Some(())
    }

    fn scale(mut self, scale: i128) -> Option<Self> {
        self.constant = self.constant.checked_mul(scale)?;
        for coefficient in self.terms.values_mut() {
            *coefficient = coefficient.checked_mul(scale)?;
        }
        Some(self)
    }
}

fn compare_affine(
    arena: &TermArena,
    left: TermId,
    right: TermId,
    environment: &mut BTreeMap<SymbolId, bool>,
    budget: &mut CheckBudget,
    op: Op,
) -> Truth {
    let Some(mut difference) = normalize_affine(arena, left, environment, budget) else {
        return Truth::Unknown;
    };
    let Some(right) = normalize_affine(arena, right, environment, budget) else {
        return Truth::Unknown;
    };
    if difference.add_scaled(&right, -1).is_none() || !difference.terms.is_empty() {
        return Truth::Unknown;
    }
    Truth::from(match op {
        Op::Eq => difference.constant == 0,
        Op::IntLt => difference.constant < 0,
        Op::IntLe => difference.constant <= 0,
        Op::IntGt => difference.constant > 0,
        Op::IntGe => difference.constant >= 0,
        _ => return Truth::Unknown,
    })
}

fn normalize_affine(
    arena: &TermArena,
    term: TermId,
    environment: &mut BTreeMap<SymbolId, bool>,
    budget: &mut CheckBudget,
) -> Option<Affine> {
    budget.nodes += 1;
    if budget.nodes > MAX_CHECK_NODES || budget.exhausted {
        budget.exhausted = true;
        return None;
    }
    match arena.node(term) {
        TermNode::IntConst(value) => Some(Affine::constant(*value)),
        TermNode::Symbol(_) => Some(Affine::atom(term)),
        TermNode::App { op, args } => match op {
            Op::IntNeg => {
                let [argument] = &**args else { return None };
                normalize_affine(arena, *argument, environment, budget)?.scale(-1)
            }
            Op::IntAdd | Op::IntSub => {
                let [left, right] = &**args else { return None };
                let mut result = normalize_affine(arena, *left, environment, budget)?;
                let right = normalize_affine(arena, *right, environment, budget)?;
                result.add_scaled(&right, if *op == Op::IntAdd { 1 } else { -1 })?;
                Some(result)
            }
            Op::IntMul => {
                let [left, right] = &**args else { return None };
                let left = normalize_affine(arena, *left, environment, budget)?;
                let right = normalize_affine(arena, *right, environment, budget)?;
                if left.terms.is_empty() {
                    right.scale(left.constant)
                } else if right.terms.is_empty() {
                    left.scale(right.constant)
                } else {
                    None
                }
            }
            Op::Ite => {
                let [condition, then_term, else_term] = &**args else {
                    return None;
                };
                match eval_truth(arena, *condition, environment, budget) {
                    Truth::True => normalize_affine(arena, *then_term, environment, budget),
                    Truth::False => normalize_affine(arena, *else_term, environment, budget),
                    Truth::Unknown => {
                        let then_value = normalize_affine(arena, *then_term, environment, budget)?;
                        let else_value = normalize_affine(arena, *else_term, environment, budget)?;
                        (then_value == else_value).then_some(then_value)
                    }
                }
            }
            _ if arena.sort_of(term) == Sort::Int => Some(Affine::atom(term)),
            _ => None,
        },
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bound_boolean_enumeration_stops_at_hard_checker_caps() {
        let mut arena = TermArena::new();
        let mut binders = Vec::new();
        for index in 0..17 {
            binders.push(arena.declare(&format!("b{index}"), Sort::Bool).unwrap());
        }
        let mut formula = arena.var(binders[0]);
        for &binder in binders.iter().rev() {
            formula = arena.forall(binder, formula).unwrap();
        }

        let mut budget = CheckBudget::default();
        let result = eval_truth(&arena, formula, &mut BTreeMap::new(), &mut budget);
        assert_ne!(result, Truth::True);
        assert!(budget.exhausted);
        assert!(budget.nodes > MAX_CHECK_NODES || budget.bool_branches > MAX_BOUND_BOOL_BRANCHES);
    }
}
