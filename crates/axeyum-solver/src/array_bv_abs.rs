//! Small BV-abstraction refutations for array queries.
//!
//! This recognizes the case where an array query is already inconsistent after
//! every array-dependent scalar leaf is replaced by an unconstrained Bool/BV
//! symbol. That is a sound over-approximation: if the abstracted BV formula is
//! UNSAT for arbitrary read/equality values, the original array formula is UNSAT.

use std::collections::{BTreeMap, BTreeSet};
use std::time::Duration;

use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode};

use crate::{Evidence, SolverConfig};

const MAX_ABSTRACTED_TERMS: usize = 64;
const MAX_ABSTRACTED_NODES: usize = 512;
const BV_ABSTRACTION_TIMEOUT: Duration = Duration::from_secs(1);

/// A self-checking refutation of an array query by scalar BV abstraction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BvAbstractionRefutationCertificate {
    /// Original scalar terms replaced by fresh unconstrained Bool/BV symbols.
    pub abstracted_terms: Vec<TermId>,
}

/// Returns a certificate when replacing array-dependent scalar leaves by fresh
/// Bool/BV variables yields a certified-unsat pure `QF_BV` problem.
#[must_use]
pub fn bv_abstraction_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<BvAbstractionRefutationCertificate> {
    let abstraction = build_bv_abstraction(arena, assertions)?;
    if abstraction.abstracted_terms.is_empty()
        || abstraction.abstracted_terms.len() > MAX_ABSTRACTED_TERMS
        || reachable_node_count(&abstraction.arena, &abstraction.assertions) > MAX_ABSTRACTED_NODES
        || contains_array(&abstraction.arena, &abstraction.assertions)
    {
        return None;
    }

    let config = SolverConfig::new().with_timeout(BV_ABSTRACTION_TIMEOUT);
    let report = crate::evidence::produce_qf_bv_evidence(
        &abstraction.arena,
        &abstraction.assertions,
        &config,
    )
    .ok()?;
    if !abstract_unsat_evidence(&report.evidence)
        || !report
            .evidence
            .check(&abstraction.arena, &abstraction.assertions)
            .ok()?
    {
        return None;
    }

    Some(BvAbstractionRefutationCertificate {
        abstracted_terms: abstraction.abstracted_terms,
    })
}

fn abstract_unsat_evidence(evidence: &Evidence) -> bool {
    matches!(
        evidence,
        Evidence::Unsat(Some(_))
            | Evidence::UnsatAletheProof(_)
            | Evidence::UnsatTermLevel { .. }
            | Evidence::UnsatFiniteDomainEnum { .. }
    )
}

struct BvAbstraction {
    arena: TermArena,
    assertions: Vec<TermId>,
    abstracted_terms: Vec<TermId>,
}

fn build_bv_abstraction(arena: &TermArena, assertions: &[TermId]) -> Option<BvAbstraction> {
    let mut state = AbstractionState {
        original: arena,
        scratch: arena.clone(),
        replacements: BTreeMap::new(),
        abstracted_terms: Vec::new(),
        next_fresh: 0,
    };
    let mut abstracted_assertions = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        if arena.sort_of(assertion) != Sort::Bool {
            return None;
        }
        abstracted_assertions.push(state.abstract_term(assertion)?);
    }
    Some(BvAbstraction {
        arena: state.scratch,
        assertions: abstracted_assertions,
        abstracted_terms: state.abstracted_terms,
    })
}

struct AbstractionState<'a> {
    original: &'a TermArena,
    scratch: TermArena,
    replacements: BTreeMap<TermId, TermId>,
    abstracted_terms: Vec<TermId>,
    next_fresh: usize,
}

impl AbstractionState<'_> {
    fn abstract_term(&mut self, term: TermId) -> Option<TermId> {
        match self.original.sort_of(term) {
            Sort::Bool | Sort::BitVec(_) => {}
            Sort::Array { .. }
            | Sort::Int
            | Sort::Real
            | Sort::Datatype(_)
            | Sort::Uninterpreted(_)
            | Sort::Float { .. } => return None,
        }

        if self.is_array_dependent_scalar_leaf(term) {
            return self.fresh_scalar(term);
        }

        let TermNode::App { args, .. } = self.original.node(term) else {
            return Some(term);
        };
        let mut changed = false;
        let mut new_args = Vec::with_capacity(args.len());
        for &arg in args {
            let new_arg = if is_scalar(self.original.sort_of(arg)) {
                self.abstract_term(arg)?
            } else {
                arg
            };
            changed |= new_arg != arg;
            new_args.push(new_arg);
        }
        if changed {
            Some(self.scratch.rebuild_with_args(term, &new_args))
        } else {
            Some(term)
        }
    }

    fn is_array_dependent_scalar_leaf(&self, term: TermId) -> bool {
        let TermNode::App { op, args } = self.original.node(term) else {
            return false;
        };
        match op {
            Op::Select => is_scalar(self.original.sort_of(term)),
            Op::Eq => args
                .first()
                .is_some_and(|&arg| matches!(self.original.sort_of(arg), Sort::Array { .. })),
            Op::Apply(_) => {
                is_scalar(self.original.sort_of(term))
                    && args
                        .iter()
                        .any(|&arg| matches!(self.original.sort_of(arg), Sort::Array { .. }))
            }
            _ => false,
        }
    }

    fn fresh_scalar(&mut self, term: TermId) -> Option<TermId> {
        if let Some(&fresh) = self.replacements.get(&term) {
            return Some(fresh);
        }
        if self.abstracted_terms.len() >= MAX_ABSTRACTED_TERMS {
            return None;
        }
        let sort = self.original.sort_of(term);
        let fresh = loop {
            let name = format!("!array_bv_abs_{}", self.next_fresh);
            self.next_fresh += 1;
            if self.scratch.find_symbol(&name).is_some() {
                continue;
            }
            break match sort {
                Sort::Bool => self.scratch.bool_var(&name).ok()?,
                Sort::BitVec(width) => self.scratch.bv_var(&name, width).ok()?,
                _ => return None,
            };
        };
        self.replacements.insert(term, fresh);
        self.abstracted_terms.push(term);
        Some(fresh)
    }
}

fn is_scalar(sort: Sort) -> bool {
    matches!(sort, Sort::Bool | Sort::BitVec(_))
}

fn reachable_node_count(arena: &TermArena, roots: &[TermId]) -> usize {
    let mut seen = BTreeSet::new();
    let mut stack = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { args, .. } = arena.node(term) {
            stack.extend(args.iter().copied());
        }
    }
    seen.len()
}

fn contains_array(arena: &TermArena, roots: &[TermId]) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if matches!(arena.sort_of(term), Sort::Array { .. }) {
            return true;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if matches!(op, Op::Select | Op::Store | Op::ConstArray { .. }) {
                return true;
            }
            stack.extend(args.iter().copied());
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use axeyum_smtlib::parse_script;

    use super::*;

    #[test]
    fn refutes_rw213_by_bv_abstraction() {
        let text = include_str!(
            "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/rewrite__array__rw213.smt2"
        );
        let script = parse_script(text).expect("parse rw213");
        let cert = bv_abstraction_refutation(&script.arena, &script.assertions)
            .expect("rw213 is inconsistent after array-read abstraction");
        assert_eq!(cert.abstracted_terms.len(), 2);
    }
}
