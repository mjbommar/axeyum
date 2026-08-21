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

/// Hard cap on [`AbstractionState::abstract_term`] invocations for one build.
///
/// Every other cap in this module (`MAX_ABSTRACTED_TERMS`, `MAX_ABSTRACTED_NODES`,
/// `BV_ABSTRACTION_TIMEOUT`) is applied to the *result* of `build_bv_abstraction`,
/// so none of them bound the walk that produces it. This one does. It is
/// deliberately far above what a memoized walk needs (it visits each reached term
/// at most once), so it can only fire if the memo is defeated -- which turns an
/// unbounded hang into a bounded decline, and declining a refutation route is
/// always sound.
const MAX_ABSTRACTION_VISITS: u64 = 1 << 22;

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
    let mut state = AbstractionState::new(arena);
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
    /// Memo for [`Self::abstract_term`], keyed by the ORIGINAL term.
    ///
    /// Without it this walk is a tree walk over a DAG: a shared subterm is
    /// re-explored once per path to it, which is exponential in the sharing.
    /// Measured on `QF_FP/bitwuzla-regress-clean/solver__fp__fp_misc.smt2`
    /// (5,762 reachable nodes, depth 424) it did not finish in 125 s.
    ///
    /// Memoizing is sound because `abstract_term` is a function of the term
    /// alone: the `Sort` decline is fixed by the sort, `fresh_scalar` already
    /// memoizes through `replacements`, and its cap-`None` is monotone (the
    /// abstracted-term count never decreases), so no decision can flip back.
    memo: BTreeMap<TermId, Option<TermId>>,
    /// `abstract_term` invocations so far, against `visit_budget`.
    visits: u64,
    /// Budget for `visits`; exceeding it declines the whole abstraction.
    visit_budget: u64,
}

impl<'a> AbstractionState<'a> {
    fn new(arena: &'a TermArena) -> Self {
        Self {
            original: arena,
            scratch: arena.clone(),
            replacements: BTreeMap::new(),
            abstracted_terms: Vec::new(),
            next_fresh: 0,
            memo: BTreeMap::new(),
            visits: 0,
            visit_budget: MAX_ABSTRACTION_VISITS,
        }
    }

    fn abstract_term(&mut self, term: TermId) -> Option<TermId> {
        if let Some(&cached) = self.memo.get(&term) {
            return cached;
        }
        self.visits += 1;
        if self.visits > self.visit_budget {
            return None;
        }
        let result = self.abstract_term_uncached(term);
        self.memo.insert(term, result);
        result
    }

    fn abstract_term_uncached(&mut self, term: TermId) -> Option<TermId> {
        match self.original.sort_of(term) {
            Sort::Bool | Sort::BitVec(_) => {}
            Sort::Array { .. }
            | Sort::Int
            | Sort::Real
            | Sort::RoundingMode
            | Sort::Datatype(_)
            | Sort::Uninterpreted(_)
            | Sort::Float { .. }
            | Sort::Seq(_) => return None,
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

    const FP_MISC: &str = include_str!(
        "../../../corpus/public-curated/non-incremental/QF_FP/bitwuzla-regress-clean/solver__fp__fp_misc.smt2"
    );

    /// The walk must be a DAG walk, not a tree walk.
    ///
    /// `fp_misc` is a 20-line `QF_FP` file that lowers to 5,762 reachable nodes
    /// with heavy sharing. Unmemoized, `abstract_term` re-explores a shared
    /// subterm once per path: measured 2026-08-21 it burned the whole
    /// 4,194,304-visit budget and the audit's `lean-reconstruction` phase did not
    /// finish inside 125 s. Memoized it visits 4,365 terms.
    ///
    /// The bound is `reachable_node_count`, which is what "each reached term is
    /// walked at most once" means; `visits` counts memo MISSES only, so any
    /// re-exploration shows up immediately.
    #[test]
    fn fp_misc_abstraction_walk_visits_each_term_at_most_once() {
        let script = parse_script(FP_MISC).expect("parse fp_misc");
        let nodes = reachable_node_count(&script.arena, &script.assertions) as u64;
        let mut state = AbstractionState::new(&script.arena);
        for &assertion in &script.assertions {
            let _ = state.abstract_term(assertion);
        }
        assert!(
            state.visits <= nodes,
            "abstract_term re-explored shared subterms: {} visits over {nodes} reachable nodes",
            state.visits
        );
    }

    /// Exceeding the visit budget declines, it does not run forever.
    ///
    /// Nothing in `MAX_ABSTRACTED_TERMS` / `MAX_ABSTRACTED_NODES` /
    /// `BV_ABSTRACTION_TIMEOUT` bounds the walk -- they all apply to its result --
    /// so this is the only cap that can stop a walk that is going wrong, and
    /// declining a refutation route is always sound.
    #[test]
    fn abstraction_declines_when_the_visit_budget_is_exhausted() {
        let script = parse_script(FP_MISC).expect("parse fp_misc");
        let mut state = AbstractionState::new(&script.arena);
        state.visit_budget = 4;
        let abstracted: Option<Vec<TermId>> = script
            .assertions
            .iter()
            .map(|&assertion| state.abstract_term(assertion))
            .collect();
        assert!(
            abstracted.is_none(),
            "a walk past its visit budget must decline, got {abstracted:?}"
        );
        assert!(state.visits > state.visit_budget);
    }

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
