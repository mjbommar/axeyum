//! Untrusted search for paired-existential witness transfer (ADR-0129).

use std::collections::BTreeSet;
use std::time::Instant;

use axeyum_ir::{SymbolId, TermArena, TermId, TermNode};

use crate::backend::{SolverConfig, SolverError};
use crate::proof::{UnsatProof, UnsatProofOutcome, export_qf_bv_unsat_proof_within};
use crate::quant_bv_paired_exists_cert::{
    BvPairedExistentialTransferCertificate, BvPairedExistentialTransferJustification,
    BvPairedExistentialTransferObligation, InstantiatedPairedTransfer,
    admitted_paired_existentials, check_bv_paired_existential_transfer,
    check_signed_add_monotonicity, instantiate_transfer_terms, paired_existential_terms,
};

const PAIRED_EXISTS_PAIR_CAP: usize = 256;
const TRANSFER_SUBSET_CAP: usize = 256;

pub(crate) fn find_bv_paired_existential_transfer(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<BvPairedExistentialTransferCertificate>, SolverError> {
    let deadline = config
        .timeout
        .and_then(|timeout| Instant::now().checked_add(timeout));
    let mut attempted_pairs = 0usize;
    for &positive_assertion in assertions {
        for &negative_assertion in assertions {
            if deadline.is_some_and(|end| Instant::now() >= end) {
                return Ok(None);
            }
            let Some((positive_existential, negative_existential)) =
                paired_existential_terms(arena, positive_assertion, negative_assertion)
            else {
                continue;
            };
            if attempted_pairs == PAIRED_EXISTS_PAIR_CAP {
                return Ok(None);
            }
            attempted_pairs += 1;
            let Some(admitted) = admitted_paired_existentials(
                arena,
                positive_assertion,
                negative_assertion,
                positive_existential,
                negative_existential,
            ) else {
                continue;
            };
            let mut replay = instantiate_transfer_terms(
                arena,
                positive_assertion,
                negative_assertion,
                &admitted,
            )?;
            let Some(obligations) = prove_transfer_obligations(&mut replay, deadline)? else {
                continue;
            };
            let certificate = BvPairedExistentialTransferCertificate {
                positive_assertion,
                negative_assertion,
                positive_existential,
                negative_existential,
                obligations,
            };
            if check_bv_paired_existential_transfer(arena, assertions, &certificate)? {
                return Ok(Some(certificate));
            }
            return Err(SolverError::Backend(
                "generated paired-existential transfer failed independent replay".to_owned(),
            ));
        }
    }
    Ok(None)
}

fn prove_transfer_obligations(
    replay: &mut InstantiatedPairedTransfer,
    deadline: Option<Instant>,
) -> Result<Option<Vec<BvPairedExistentialTransferObligation>>, SolverError> {
    let available_terms = replay.available.values().copied().collect::<BTreeSet<_>>();
    let available = replay
        .available
        .iter()
        .map(|(&source, &instantiated)| (source, instantiated))
        .collect::<Vec<_>>();
    let consequents = replay
        .consequents
        .iter()
        .map(|(&source, &instantiated)| (source, instantiated))
        .collect::<Vec<_>>();
    let mut obligations = Vec::new();
    let mut attempted_subsets = 0usize;
    for (source, consequent) in consequents {
        if available_terms.contains(&consequent) {
            continue;
        }
        if let Some((strong, bound)) =
            find_signed_add_monotonicity(&replay.arena, &available, consequent)
        {
            obligations.push(BvPairedExistentialTransferObligation {
                consequent: source,
                justification: BvPairedExistentialTransferJustification::SignedAddMonotonicity {
                    strong,
                    bound,
                },
            });
            continue;
        }
        let not_consequent = replay
            .arena
            .not(consequent)
            .map_err(|error| SolverError::Backend(error.to_string()))?;
        let consequent_symbols = symbol_support(&replay.arena, consequent);
        let relevant = available
            .iter()
            .copied()
            .filter(|(_, instantiated)| {
                symbol_support(&replay.arena, *instantiated).is_subset(&consequent_symbols)
            })
            .collect::<Vec<_>>();
        let Some((assumptions, proof)) = find_sufficient_subset(
            &replay.arena,
            &relevant,
            not_consequent,
            deadline,
            &mut attempted_subsets,
        )?
        else {
            return Ok(None);
        };
        obligations.push(BvPairedExistentialTransferObligation {
            consequent: source,
            justification: BvPairedExistentialTransferJustification::QfProof { assumptions, proof },
        });
    }
    Ok(Some(obligations))
}

fn find_signed_add_monotonicity(
    arena: &TermArena,
    available: &[(TermId, TermId)],
    consequent: TermId,
) -> Option<(TermId, TermId)> {
    for &(strong_source, strong) in available {
        for &(bound_source, bound) in available {
            if strong_source != bound_source
                && check_signed_add_monotonicity(arena, consequent, strong, bound)
            {
                return Some((strong_source, bound_source));
            }
        }
    }
    None
}

fn symbol_support(arena: &TermArena, root: TermId) -> BTreeSet<SymbolId> {
    let mut symbols = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.node(term) {
            TermNode::Symbol(symbol) => {
                symbols.insert(*symbol);
            }
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    symbols
}

fn find_sufficient_subset(
    arena: &TermArena,
    available: &[(TermId, TermId)],
    not_consequent: TermId,
    deadline: Option<Instant>,
    attempted: &mut usize,
) -> Result<Option<(Vec<TermId>, UnsatProof)>, SolverError> {
    if available.len() > 1 {
        let all = (0..available.len()).collect::<Vec<_>>();
        if let Some(proof) =
            try_subset(arena, available, &all, not_consequent, deadline, attempted)?
        {
            return Ok(Some((
                available.iter().map(|(source, _)| *source).collect(),
                proof,
            )));
        }
    }
    for first in 0..available.len() {
        if let Some(proof) = try_subset(
            arena,
            available,
            &[first],
            not_consequent,
            deadline,
            attempted,
        )? {
            return Ok(Some((vec![available[first].0], proof)));
        }
    }
    if let Some(proof) = try_subset(arena, available, &[], not_consequent, deadline, attempted)? {
        return Ok(Some((Vec::new(), proof)));
    }
    Ok(None)
}

fn try_subset(
    arena: &TermArena,
    available: &[(TermId, TermId)],
    selected: &[usize],
    not_consequent: TermId,
    deadline: Option<Instant>,
    attempted: &mut usize,
) -> Result<Option<UnsatProof>, SolverError> {
    if *attempted == TRANSFER_SUBSET_CAP || deadline.is_some_and(|end| Instant::now() >= end) {
        return Ok(None);
    }
    *attempted += 1;
    let mut residual = selected
        .iter()
        .map(|&index| available[index].1)
        .collect::<Vec<_>>();
    residual.push(not_consequent);
    match export_qf_bv_unsat_proof_within(arena, &residual, deadline)? {
        UnsatProofOutcome::Proved(proof) => Ok(Some(proof)),
        UnsatProofOutcome::Satisfiable | UnsatProofOutcome::Inconclusive => Ok(None),
    }
}
