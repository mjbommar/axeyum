//! Source-bound paired-existential witness transfer over Bool/BV (ADR-0129).

use std::collections::{BTreeMap, BTreeSet, HashMap};

use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode};
use axeyum_rewrite::replace_subterms;

use crate::backend::SolverError;
use crate::proof::UnsatProof;

/// Maximum total binders across both existential prefixes.
pub const BV_PAIRED_EXISTS_BINDER_CAP: usize = 128;
/// Maximum distinct nodes across both complete source assertions.
pub const BV_PAIRED_EXISTS_NODE_CAP: usize = 4_096;

/// One independently replayed reason for a transferred body conjunct.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BvPairedExistentialTransferJustification {
    /// Word-level signed monotonicity: `x <=s bound` and `x+strong <=s k`
    /// imply `x+weak <=s k`, with all no-wrap side conditions rechecked.
    SignedAddMonotonicity {
        /// Source conjunct `x + strong <=s k`.
        strong: TermId,
        /// Source conjunct `x <=s bound`.
        bound: TermId,
    },
    /// Generic `QF_BV` implication proof for a bounded selected source subset.
    QfProof {
        /// Exact shared outer premises or positive-body conjuncts used.
        assumptions: Vec<TermId>,
        /// Refutation of the instantiated assumptions plus the negated
        /// consequent.
        proof: UnsatProof,
    },
}

/// One source-bound implication needed to transfer a shared existential tuple.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BvPairedExistentialTransferObligation {
    /// One top-level conjunct of the negative existential body.
    pub consequent: TermId,
    /// Independently replayed reason for this consequence.
    pub justification: BvPairedExistentialTransferJustification,
}

/// A source-bound proof that one existential body transfers its witness to a
/// second existential under identical ground premises.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BvPairedExistentialTransferCertificate {
    /// Original positive assertion `premises && exists xs. strong`.
    pub positive_assertion: TermId,
    /// Original assertion `not (premises && exists ys. weak)`.
    pub negative_assertion: TermId,
    /// Exact positive existential leaf reached only through conjunctions.
    pub positive_existential: TermId,
    /// Exact existential leaf below the negative assertion's conjunction.
    pub negative_existential: TermId,
    /// Proofs for weak-body conjuncts not already alpha-identical to an
    /// available shared premise or positive-body conjunct.
    pub obligations: Vec<BvPairedExistentialTransferObligation>,
}

#[derive(Debug, Clone)]
pub(crate) struct AdmittedPairedExistentials {
    pub premises: Vec<TermId>,
    pub positive_binders: Vec<SymbolId>,
    pub positive_body: TermId,
    pub positive_conjuncts: Vec<TermId>,
    pub negative_binders: Vec<SymbolId>,
    pub negative_body: TermId,
    pub negative_conjuncts: Vec<TermId>,
}

pub(crate) struct InstantiatedPairedTransfer {
    pub arena: TermArena,
    pub aligned_binders: Vec<(SymbolId, Sort)>,
    pub available: BTreeMap<TermId, TermId>,
    pub consequents: BTreeMap<TermId, TermId>,
}

/// Rechecks paired-existential witness transfer against exact original IR.
///
/// # Errors
///
/// Returns [`SolverError`] if deterministic source instantiation or proof
/// replay fails. Structural mismatches return `Ok(false)`.
pub fn check_bv_paired_existential_transfer(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &BvPairedExistentialTransferCertificate,
) -> Result<bool, SolverError> {
    if certificate.positive_assertion == certificate.negative_assertion
        || !assertions.contains(&certificate.positive_assertion)
        || !assertions.contains(&certificate.negative_assertion)
    {
        return Ok(false);
    }
    let Some(admitted) = admitted_paired_existentials(
        arena,
        certificate.positive_assertion,
        certificate.negative_assertion,
        certificate.positive_existential,
        certificate.negative_existential,
    ) else {
        return Ok(false);
    };
    let mut replay = instantiate_transfer_terms(
        arena,
        certificate.positive_assertion,
        certificate.negative_assertion,
        &admitted,
    )?;

    let available_terms = replay.available.values().copied().collect::<BTreeSet<_>>();
    let mut required = replay
        .consequents
        .iter()
        .filter_map(|(&source, &instantiated)| {
            (!available_terms.contains(&instantiated)).then_some(source)
        })
        .collect::<BTreeSet<_>>();
    if certificate.obligations.len() != required.len() {
        return Ok(false);
    }

    for obligation in &certificate.obligations {
        if !required.remove(&obligation.consequent) {
            return Ok(false);
        }
        let Some(&consequent) = replay.consequents.get(&obligation.consequent) else {
            return Ok(false);
        };
        match &obligation.justification {
            BvPairedExistentialTransferJustification::SignedAddMonotonicity { strong, bound } => {
                let Some(&strong) = replay.available.get(strong) else {
                    return Ok(false);
                };
                let Some(&bound) = replay.available.get(bound) else {
                    return Ok(false);
                };
                if !check_signed_add_monotonicity(&replay.arena, consequent, strong, bound) {
                    return Ok(false);
                }
            }
            BvPairedExistentialTransferJustification::QfProof { assumptions, proof } => {
                let unique_assumptions = assumptions.iter().copied().collect::<BTreeSet<_>>();
                if unique_assumptions.len() != assumptions.len() {
                    return Ok(false);
                }
                let mut residual = Vec::with_capacity(assumptions.len() + 1);
                for source in assumptions {
                    let Some(&instantiated) = replay.available.get(source) else {
                        return Ok(false);
                    };
                    residual.push(instantiated);
                }
                let not_consequent = replay
                    .arena
                    .not(consequent)
                    .map_err(|error| SolverError::Backend(error.to_string()))?;
                residual.push(not_consequent);
                if !proof.recheck_for_bool_terms(&replay.arena, &residual)? {
                    return Ok(false);
                }
            }
        }
    }
    Ok(required.is_empty())
}

pub(crate) fn check_signed_add_monotonicity(
    arena: &TermArena,
    consequent: TermId,
    strong: TermId,
    bound: TermId,
) -> bool {
    let Some((variable, weak_offset, upper, width)) = signed_add_upper_bound(arena, consequent)
    else {
        return false;
    };
    let Some((strong_variable, strong_offset, strong_upper, strong_width)) =
        signed_add_upper_bound(arena, strong)
    else {
        return false;
    };
    let Some((bound_variable, bound_value, bound_width)) = signed_variable_bound(arena, bound)
    else {
        return false;
    };
    if variable != strong_variable
        || variable != bound_variable
        || upper != strong_upper
        || width != strong_width
        || width != bound_width
    {
        return false;
    }

    let weak = signed_bv(weak_offset, width);
    let strong = signed_bv(strong_offset, width);
    let bound = signed_bv(bound_value, width);
    let max_signed = i128::MAX >> (128 - width);
    weak >= 0 && weak <= strong && bound <= max_signed.checked_sub(strong).unwrap_or(i128::MIN)
}

fn signed_add_upper_bound(arena: &TermArena, term: TermId) -> Option<(TermId, u128, TermId, u32)> {
    let (lhs, upper) = match arena.node(term) {
        TermNode::App {
            op: Op::BvSle,
            args,
        } if args.len() == 2 => (args[0], args[1]),
        _ => return None,
    };
    let args = match arena.node(lhs) {
        TermNode::App {
            op: Op::BvAdd,
            args,
        } if args.len() == 2 => args,
        _ => return None,
    };
    let (variable, offset, width) = match (arena.node(args[0]), arena.node(args[1])) {
        (TermNode::Symbol(_), TermNode::BvConst { width, value }) => (args[0], *value, *width),
        (TermNode::BvConst { width, value }, TermNode::Symbol(_)) => (args[1], *value, *width),
        _ => return None,
    };
    (arena.sort_of(upper) == Sort::BitVec(width)).then_some((variable, offset, upper, width))
}

fn signed_variable_bound(arena: &TermArena, term: TermId) -> Option<(TermId, u128, u32)> {
    let args = match arena.node(term) {
        TermNode::App {
            op: Op::BvSle,
            args,
        } if args.len() == 2 => args,
        _ => return None,
    };
    match (arena.node(args[0]), arena.node(args[1])) {
        (TermNode::Symbol(_), TermNode::BvConst { width, value }) => {
            Some((args[0], *value, *width))
        }
        _ => None,
    }
}

fn signed_bv(value: u128, width: u32) -> i128 {
    let shift = 128 - width;
    (value << shift).cast_signed() >> shift
}

pub(crate) fn paired_existential_terms(
    arena: &TermArena,
    positive_assertion: TermId,
    negative_assertion: TermId,
) -> Option<(TermId, TermId)> {
    if positive_assertion.index() >= arena.len()
        || negative_assertion.index() >= arena.len()
        || positive_assertion == negative_assertion
    {
        return None;
    }
    let positive = split_conjunctive_existential(arena, positive_assertion)?;
    let negative_inner = negated_body(arena, negative_assertion)?;
    let negative = split_conjunctive_existential(arena, negative_inner)?;
    Some((positive.1, negative.1))
}

pub(crate) fn admitted_paired_existentials(
    arena: &TermArena,
    positive_assertion: TermId,
    negative_assertion: TermId,
    positive_existential: TermId,
    negative_existential: TermId,
) -> Option<AdmittedPairedExistentials> {
    if positive_assertion.index() >= arena.len()
        || negative_assertion.index() >= arena.len()
        || positive_existential.index() >= arena.len()
        || negative_existential.index() >= arena.len()
        || positive_assertion == negative_assertion
        || !sources_within_cap(arena, positive_assertion, negative_assertion)
    {
        return None;
    }

    let (mut positive_premises, selected_positive) =
        split_conjunctive_existential(arena, positive_assertion)?;
    let negative_inner = negated_body(arena, negative_assertion)?;
    let (mut negative_premises, selected_negative) =
        split_conjunctive_existential(arena, negative_inner)?;
    if selected_positive != positive_existential || selected_negative != negative_existential {
        return None;
    }
    sort_dedup_terms(&mut positive_premises);
    sort_dedup_terms(&mut negative_premises);
    if positive_premises != negative_premises
        || positive_premises
            .iter()
            .any(|&premise| !term_is_qf_bv(arena, premise))
    {
        return None;
    }

    let (positive_binders, positive_body) = peel_exists(arena, positive_existential)?;
    let (negative_binders, negative_body) = peel_exists(arena, negative_existential)?;
    if positive_binders.len() != negative_binders.len()
        || positive_binders.len() + negative_binders.len() > BV_PAIRED_EXISTS_BINDER_CAP
        || !term_is_qf_bv(arena, positive_body)
        || !term_is_qf_bv(arena, negative_body)
    {
        return None;
    }

    let all_binders = positive_binders
        .iter()
        .chain(&negative_binders)
        .copied()
        .collect::<BTreeSet<_>>();
    if all_binders.len() != positive_binders.len() + negative_binders.len() {
        return None;
    }
    for (&positive, &negative) in positive_binders.iter().zip(&negative_binders) {
        if arena.symbol(positive).1 != arena.symbol(negative).1 {
            return None;
        }
    }

    let positive_set = positive_binders.iter().copied().collect::<BTreeSet<_>>();
    let negative_set = negative_binders.iter().copied().collect::<BTreeSet<_>>();
    if contains_any_symbol(arena, positive_body, &negative_set)
        || contains_any_symbol(arena, negative_body, &positive_set)
        || positive_premises
            .iter()
            .any(|&premise| contains_any_symbol(arena, premise, &all_binders))
    {
        return None;
    }

    let mut positive_conjuncts = conjunction_leaves(arena, positive_body);
    let mut negative_conjuncts = conjunction_leaves(arena, negative_body);
    sort_dedup_terms(&mut positive_conjuncts);
    sort_dedup_terms(&mut negative_conjuncts);
    Some(AdmittedPairedExistentials {
        premises: positive_premises,
        positive_binders,
        positive_body,
        positive_conjuncts,
        negative_binders,
        negative_body,
        negative_conjuncts,
    })
}

pub(crate) fn instantiate_transfer_terms(
    arena: &TermArena,
    positive_assertion: TermId,
    negative_assertion: TermId,
    admitted: &AdmittedPairedExistentials,
) -> Result<InstantiatedPairedTransfer, SolverError> {
    let mut scratch = arena.clone();
    let mut positive_replacements = HashMap::new();
    let mut negative_replacements = HashMap::new();
    let mut aligned_binders = Vec::with_capacity(admitted.positive_binders.len());
    let mut nonce = scratch.symbols().count();
    for (&positive, &negative) in admitted
        .positive_binders
        .iter()
        .zip(&admitted.negative_binders)
    {
        let sort = scratch.symbol(positive).1;
        let fresh = loop {
            let name = format!(
                "!paired_exists_transfer_{}_{}_{}_{}_{}",
                positive_assertion.index(),
                negative_assertion.index(),
                positive.index(),
                negative.index(),
                nonce
            );
            nonce += 1;
            if scratch.find_internal_symbol(&name).is_none() {
                break scratch
                    .declare_internal(&name, sort)
                    .map_err(|error| SolverError::Backend(error.to_string()))?;
            }
        };
        aligned_binders.push((fresh, sort));
        let fresh_term = scratch.var(fresh);
        let positive_term = scratch.var(positive);
        let negative_term = scratch.var(negative);
        positive_replacements.insert(positive_term, fresh_term);
        negative_replacements.insert(negative_term, fresh_term);
    }

    let mut available = BTreeMap::new();
    for &premise in &admitted.premises {
        available.insert(premise, premise);
    }
    let mut positive_memo = HashMap::new();
    for &source in &admitted.positive_conjuncts {
        let instantiated = replace_subterms(
            &mut scratch,
            source,
            &positive_replacements,
            &mut positive_memo,
        )
        .map_err(|error| SolverError::Backend(error.to_string()))?;
        available.insert(source, instantiated);
    }
    let mut consequents = BTreeMap::new();
    let mut negative_memo = HashMap::new();
    for &source in &admitted.negative_conjuncts {
        let instantiated = replace_subterms(
            &mut scratch,
            source,
            &negative_replacements,
            &mut negative_memo,
        )
        .map_err(|error| SolverError::Backend(error.to_string()))?;
        consequents.insert(source, instantiated);
    }
    Ok(InstantiatedPairedTransfer {
        arena: scratch,
        aligned_binders,
        available,
        consequents,
    })
}

fn split_conjunctive_existential(arena: &TermArena, root: TermId) -> Option<(Vec<TermId>, TermId)> {
    if arena.sort_of(root) != Sort::Bool {
        return None;
    }
    let mut leaves = conjunction_leaves(arena, root);
    let existentials = leaves
        .iter()
        .copied()
        .filter(|&term| {
            matches!(
                arena.node(term),
                TermNode::App {
                    op: Op::Exists(_),
                    ..
                }
            )
        })
        .collect::<Vec<_>>();
    if existentials.len() != 1 {
        return None;
    }
    let selected = existentials[0];
    leaves.retain(|&term| term != selected);
    Some((leaves, selected))
}

fn negated_body(arena: &TermArena, term: TermId) -> Option<TermId> {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolNot,
            args,
        } if args.len() == 1 => Some(args[0]),
        _ => None,
    }
}

fn conjunction_leaves(arena: &TermArena, root: TermId) -> Vec<TermId> {
    let mut leaves = Vec::new();
    let mut seen = BTreeSet::new();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.node(term) {
            TermNode::App {
                op: Op::BoolAnd,
                args,
            } if args.len() == 2 => stack.extend(args.iter().copied()),
            _ => leaves.push(term),
        }
    }
    leaves
}

fn sort_dedup_terms(terms: &mut Vec<TermId>) {
    terms.sort_by_key(|term| term.index());
    terms.dedup();
}

fn peel_exists(arena: &TermArena, mut term: TermId) -> Option<(Vec<SymbolId>, TermId)> {
    let mut binders = Vec::new();
    while let TermNode::App {
        op: Op::Exists(binder),
        args,
    } = arena.node(term)
    {
        if args.len() != 1 || !is_bool_bv(arena.symbol(*binder).1) {
            return None;
        }
        binders.push(*binder);
        term = args[0];
    }
    (!binders.is_empty()).then_some((binders, term))
}

fn sources_within_cap(arena: &TermArena, positive: TermId, negative: TermId) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = vec![positive, negative];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if seen.len() > BV_PAIRED_EXISTS_NODE_CAP || !is_bool_bv(arena.sort_of(term)) {
            return false;
        }
        if let TermNode::App { args, .. } = arena.node(term) {
            stack.extend(args.iter().copied());
        }
    }
    true
}

fn term_is_qf_bv(arena: &TermArena, root: TermId) -> bool {
    if arena.sort_of(root) != Sort::Bool {
        return false;
    }
    let mut seen = BTreeSet::new();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if !is_bool_bv(arena.sort_of(term)) {
            return false;
        }
        match arena.node(term) {
            TermNode::App {
                op: Op::Forall(_) | Op::Exists(_) | Op::Apply(_),
                ..
            } => return false,
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    true
}

fn contains_any_symbol(arena: &TermArena, root: TermId, symbols: &BTreeSet<SymbolId>) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.node(term) {
            TermNode::Symbol(symbol) if symbols.contains(symbol) => return true,
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    false
}

const fn is_bool_bv(sort: Sort) -> bool {
    matches!(sort, Sort::Bool | Sort::BitVec(_))
}
