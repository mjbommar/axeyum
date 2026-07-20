//! Local finite-BV equality facts plus UF congrence refutations.
//!
//! This certificate covers small mixed BV/UF rows where the arithmetic part is
//! not worth a broad proof route, but a tiny local BV enumeration derives
//! equality facts that make the UF part contradictory. The motivating `QF_UFFF`
//! regressions parse finite-field values as small `BitVec`s; their field
//! constraints force equalities such as `a = b`, after which ordinary UF
//! congruence closes the contradiction.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::{Assignment, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};

use crate::term_walk::collect_top_binary_conjuncts as collect_top_conjuncts;

const MAX_LOCAL_BV_WIDTH: u32 = 8;
const MAX_LOCAL_ENUM_BITS: u32 = 12;

/// The final checked contradiction shape.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BvUfLocalRefutationKind {
    /// Derived BV equalities plus asserted equalities make an asserted
    /// disequality's sides congruent.
    CongruentDisequality,
    /// A congruence-derived BV equality makes an original pure-BV assertion
    /// impossible by a tiny local enumeration.
    PureBvConflictAfterCongruence,
}

/// One equality fact derived by exhaustive evaluation of the original pure-BV
/// assertions whose free symbols are contained in the two endpoints.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BvUfLocalDerivedEquality {
    /// Left endpoint of the derived equality.
    pub lhs: TermId,
    /// Right endpoint of the derived equality.
    pub rhs: TermId,
    /// Number of assignments enumerated while deriving this fact.
    pub cases: u64,
}

/// A self-checking local BV+UF refutation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BvUfLocalRefutationCertificate {
    /// The final contradiction kind.
    pub kind: BvUfLocalRefutationKind,
    /// Equality facts derived from local pure-BV enumeration.
    pub derived_equalities: Vec<BvUfLocalDerivedEquality>,
    /// The original assertion that supplied the final contradiction.
    pub conflict_assertion: TermId,
    /// Left side of the final conflicting equality/disequality.
    pub conflict_lhs: TermId,
    /// Right side of the final conflicting equality/disequality.
    pub conflict_rhs: TermId,
    /// Extra cases checked for the final pure-BV conflict, if any.
    pub conflict_cases: u64,
}

/// Returns a certificate when local finite-BV equality facts plus congruence
/// refute the assertions.
#[must_use]
pub fn bv_uf_local_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<BvUfLocalRefutationCertificate> {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        collect_top_conjuncts(arena, assertion, &mut conjuncts);
    }

    let pure_assertions: Vec<TermId> = conjuncts
        .iter()
        .copied()
        .filter(|&term| arena.sort_of(term) == Sort::Bool && is_pure_bool_bv_term(arena, term))
        .collect();
    if pure_assertions.is_empty() {
        return None;
    }

    let bv_symbols = collect_bv_symbol_terms(arena, assertions);
    if bv_symbols.len() < 2 {
        return None;
    }
    let derived_equalities = derive_local_equalities(arena, &pure_assertions, &bv_symbols)?;
    if derived_equalities.is_empty() {
        return None;
    }

    let mut closure = CongruenceClosure::new(arena, assertions);
    for &conjunct in &conjuncts {
        if let Some((lhs, rhs)) = match_equality(arena, conjunct) {
            closure.union_terms(lhs, rhs);
        }
    }
    for equality in &derived_equalities {
        closure.union_terms(equality.lhs, equality.rhs);
    }
    closure.close(arena);

    for &conjunct in &conjuncts {
        let Some((lhs, rhs)) = match_disequality(arena, conjunct) else {
            continue;
        };
        if closure.equal_terms(lhs, rhs) {
            return Some(BvUfLocalRefutationCertificate {
                kind: BvUfLocalRefutationKind::CongruentDisequality,
                derived_equalities,
                conflict_assertion: conjunct,
                conflict_lhs: lhs,
                conflict_rhs: rhs,
                conflict_cases: 0,
            });
        }
    }

    for (lhs, rhs) in closure.equal_bv_symbol_pairs(arena, &bv_symbols) {
        for &conjunct in &pure_assertions {
            if !matches!(arena.node(conjunct), TermNode::App { op: Op::Eq, .. }) {
                continue;
            }
            let Some(cases) = assertion_refuted_by_local_equality(arena, conjunct, lhs, rhs) else {
                continue;
            };
            return Some(BvUfLocalRefutationCertificate {
                kind: BvUfLocalRefutationKind::PureBvConflictAfterCongruence,
                derived_equalities,
                conflict_assertion: conjunct,
                conflict_lhs: lhs,
                conflict_rhs: rhs,
                conflict_cases: cases,
            });
        }
    }

    None
}

fn match_equality(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    Some((*lhs, *rhs))
}

fn match_disequality(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [inner] = &**args else {
        return None;
    };
    match_equality(arena, *inner)
}

fn collect_bv_symbol_terms(arena: &TermArena, assertions: &[TermId]) -> Vec<(SymbolId, TermId)> {
    let mut out = BTreeMap::new();
    let mut seen = BTreeSet::new();
    let mut stack = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.node(term) {
            TermNode::Symbol(symbol) if matches!(arena.sort_of(term), Sort::BitVec(w) if w <= MAX_LOCAL_BV_WIDTH) =>
            {
                out.insert(*symbol, term);
            }
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    out.into_iter().collect()
}

fn derive_local_equalities(
    arena: &TermArena,
    pure_assertions: &[TermId],
    symbols: &[(SymbolId, TermId)],
) -> Option<Vec<BvUfLocalDerivedEquality>> {
    let mut out = Vec::new();
    for i in 0..symbols.len() {
        for j in (i + 1)..symbols.len() {
            let (left_symbol, left_term) = symbols[i];
            let (right_symbol, right_term) = symbols[j];
            let Sort::BitVec(left_width) = arena.sort_of(left_term) else {
                continue;
            };
            if arena.sort_of(right_term) != Sort::BitVec(left_width) {
                continue;
            }
            let total_bits = left_width.checked_mul(2)?;
            if total_bits > MAX_LOCAL_ENUM_BITS {
                continue;
            }
            let local: Vec<TermId> = pure_assertions
                .iter()
                .copied()
                .filter(|&assertion| {
                    let assertion_symbols = symbols_in_term(arena, assertion);
                    !assertion_symbols.is_empty()
                        && assertion_symbols
                            .iter()
                            .all(|&s| s == left_symbol || s == right_symbol)
                })
                .collect();
            if local.is_empty() {
                continue;
            }
            let cases = 1_u64.checked_shl(total_bits)?;
            let mut satisfying = 0_u64;
            let mut entails_equal = true;
            for case in 0..cases {
                let mut assignment = Assignment::new();
                let mask = bit_mask(left_width);
                let left_value = u128::from(case) & mask;
                let right_value = (u128::from(case) >> left_width) & mask;
                assignment.set(
                    left_symbol,
                    Value::Bv {
                        width: left_width,
                        value: left_value,
                    },
                );
                assignment.set(
                    right_symbol,
                    Value::Bv {
                        width: left_width,
                        value: right_value,
                    },
                );
                if !all_assertions_true(arena, &local, &assignment)? {
                    continue;
                }
                satisfying += 1;
                if left_value != right_value {
                    entails_equal = false;
                    break;
                }
            }
            if satisfying > 0 && entails_equal {
                out.push(BvUfLocalDerivedEquality {
                    lhs: left_term,
                    rhs: right_term,
                    cases,
                });
            }
        }
    }
    Some(out)
}

fn assertion_refuted_by_local_equality(
    arena: &TermArena,
    assertion: TermId,
    lhs: TermId,
    rhs: TermId,
) -> Option<u64> {
    let mut symbols = symbols_in_term(arena, assertion);
    symbols.extend(symbols_in_term(arena, lhs));
    symbols.extend(symbols_in_term(arena, rhs));
    let mut symbol_terms = Vec::new();
    for symbol in symbols {
        let term = find_symbol_term(arena, assertion, symbol)
            .or_else(|| find_symbol_term(arena, lhs, symbol))
            .or_else(|| find_symbol_term(arena, rhs, symbol))?;
        let sort = arena.sort_of(term);
        if !matches!(sort, Sort::Bool | Sort::BitVec(_)) {
            return None;
        }
        symbol_terms.push((symbol, sort));
    }
    symbol_terms.sort_unstable_by_key(|&(symbol, _)| symbol.index());
    symbol_terms.dedup_by_key(|&mut (symbol, _)| symbol.index());
    let total_bits = symbol_terms
        .iter()
        .try_fold(0_u32, |acc, &(_, sort)| acc.checked_add(sort_bits(sort)?))?;
    if total_bits > MAX_LOCAL_ENUM_BITS {
        return None;
    }
    let cases = 1_u64.checked_shl(total_bits)?;
    let mut equality_satisfying = 0_u64;
    for case in 0..cases {
        let assignment = decode_assignment(&symbol_terms, u128::from(case))?;
        if eval(arena, lhs, &assignment).ok()? != eval(arena, rhs, &assignment).ok()? {
            continue;
        }
        equality_satisfying += 1;
        if eval_bool(arena, assertion, &assignment)? {
            return None;
        }
    }
    (equality_satisfying > 0).then_some(cases)
}

fn all_assertions_true(
    arena: &TermArena,
    assertions: &[TermId],
    assignment: &Assignment,
) -> Option<bool> {
    for &assertion in assertions {
        if !eval_bool(arena, assertion, assignment)? {
            return Some(false);
        }
    }
    Some(true)
}

fn eval_bool(arena: &TermArena, term: TermId, assignment: &Assignment) -> Option<bool> {
    match eval(arena, term, assignment).ok()? {
        Value::Bool(value) => Some(value),
        _ => None,
    }
}

fn decode_assignment(symbols: &[(SymbolId, Sort)], mut code: u128) -> Option<Assignment> {
    let mut assignment = Assignment::new();
    for &(symbol, sort) in symbols {
        match sort {
            Sort::Bool => {
                assignment.set(symbol, Value::Bool((code & 1) != 0));
                code >>= 1;
            }
            Sort::BitVec(width) => {
                let mask = bit_mask(width);
                assignment.set(
                    symbol,
                    Value::Bv {
                        width,
                        value: code & mask,
                    },
                );
                code >>= width;
            }
            _ => return None,
        }
    }
    Some(assignment)
}

fn sort_bits(sort: Sort) -> Option<u32> {
    match sort {
        Sort::Bool => Some(1),
        Sort::BitVec(width) => Some(width),
        _ => None,
    }
}

fn bit_mask(width: u32) -> u128 {
    if width == 128 {
        u128::MAX
    } else {
        (1_u128 << width) - 1
    }
}

fn symbols_in_term(arena: &TermArena, term: TermId) -> BTreeSet<SymbolId> {
    let mut out = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut stack = vec![term];
    while let Some(next) = stack.pop() {
        if !seen.insert(next) {
            continue;
        }
        match arena.node(next) {
            TermNode::Symbol(symbol) => {
                out.insert(*symbol);
            }
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    out
}

fn find_symbol_term(arena: &TermArena, root: TermId, target: SymbolId) -> Option<TermId> {
    let mut seen = BTreeSet::new();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.node(term) {
            TermNode::Symbol(symbol) if *symbol == target => return Some(term),
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    None
}

fn is_pure_bool_bv_term(arena: &TermArena, term: TermId) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = vec![term];
    while let Some(next) = stack.pop() {
        if !seen.insert(next) {
            continue;
        }
        match arena.node(next) {
            TermNode::BoolConst(_) | TermNode::BvConst { .. } | TermNode::WideBvConst(_) => {}
            TermNode::Symbol(_) if matches!(arena.sort_of(next), Sort::Bool | Sort::BitVec(_)) => {}
            TermNode::App { op, args } if is_pure_bool_bv_op(*op) => {
                stack.extend(args.iter().copied());
            }
            _ => return false,
        }
    }
    true
}

fn is_pure_bool_bv_op(op: Op) -> bool {
    matches!(
        op,
        Op::BoolNot
            | Op::BoolAnd
            | Op::BoolOr
            | Op::BoolXor
            | Op::BoolImplies
            | Op::BvNot
            | Op::BvAnd
            | Op::BvOr
            | Op::BvXor
            | Op::BvNand
            | Op::BvNor
            | Op::BvXnor
            | Op::BvNeg
            | Op::BvAdd
            | Op::BvSub
            | Op::BvMul
            | Op::BvUdiv
            | Op::BvUrem
            | Op::BvSdiv
            | Op::BvSrem
            | Op::BvSmod
            | Op::BvShl
            | Op::BvLshr
            | Op::BvAshr
            | Op::BvUlt
            | Op::BvUle
            | Op::BvUgt
            | Op::BvUge
            | Op::BvSlt
            | Op::BvSle
            | Op::BvSgt
            | Op::BvSge
            | Op::Eq
            | Op::Ite
            | Op::BvComp
            | Op::Extract { .. }
            | Op::Concat
            | Op::ZeroExt { .. }
            | Op::SignExt { .. }
            | Op::RotateLeft { .. }
            | Op::RotateRight { .. }
    )
}

struct CongruenceClosure {
    terms: Vec<TermId>,
    index: BTreeMap<TermId, usize>,
    parent: Vec<usize>,
}

impl CongruenceClosure {
    fn new(arena: &TermArena, assertions: &[TermId]) -> Self {
        let mut terms = Vec::new();
        let mut seen = BTreeSet::new();
        let mut stack = assertions.to_vec();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            terms.push(term);
            if let TermNode::App { args, .. } = arena.node(term) {
                stack.extend(args.iter().copied());
            }
        }
        terms.sort_unstable_by_key(|term| term.index());
        let index = terms
            .iter()
            .enumerate()
            .map(|(i, &term)| (term, i))
            .collect();
        let parent = (0..terms.len()).collect();
        Self {
            terms,
            index,
            parent,
        }
    }

    fn union_terms(&mut self, lhs: TermId, rhs: TermId) {
        let (Some(&li), Some(&ri)) = (self.index.get(&lhs), self.index.get(&rhs)) else {
            return;
        };
        self.union(li, ri);
    }

    fn equal_terms(&mut self, lhs: TermId, rhs: TermId) -> bool {
        let (Some(&li), Some(&ri)) = (self.index.get(&lhs), self.index.get(&rhs)) else {
            return false;
        };
        self.find(li) == self.find(ri)
    }

    fn equal_bv_symbol_pairs(
        &mut self,
        arena: &TermArena,
        symbols: &[(SymbolId, TermId)],
    ) -> Vec<(TermId, TermId)> {
        let mut out = Vec::new();
        for i in 0..symbols.len() {
            for j in (i + 1)..symbols.len() {
                let lhs = symbols[i].1;
                let rhs = symbols[j].1;
                if !matches!(arena.sort_of(lhs), Sort::BitVec(_))
                    || arena.sort_of(lhs) != arena.sort_of(rhs)
                {
                    continue;
                }
                if self.equal_terms(lhs, rhs) {
                    out.push((lhs, rhs));
                }
            }
        }
        out
    }

    fn close(&mut self, arena: &TermArena) {
        let apps: Vec<(TermId, Op, Box<[TermId]>)> = self
            .terms
            .iter()
            .filter_map(|&term| match arena.node(term) {
                TermNode::App { op, args } => Some((term, *op, args.clone())),
                _ => None,
            })
            .collect();
        loop {
            let mut changed = false;
            for i in 0..apps.len() {
                for j in (i + 1)..apps.len() {
                    let (lhs, lhs_op, lhs_args) = &apps[i];
                    let (rhs, rhs_op, rhs_args) = &apps[j];
                    if lhs_op != rhs_op || lhs_args.len() != rhs_args.len() {
                        continue;
                    }
                    if lhs_args
                        .iter()
                        .zip(rhs_args.iter())
                        .all(|(&l, &r)| self.equal_terms(l, r))
                    {
                        let before = self.equal_terms(*lhs, *rhs);
                        self.union_terms(*lhs, *rhs);
                        changed |= !before;
                    }
                }
            }
            if !changed {
                break;
            }
        }
    }

    fn find(&mut self, node: usize) -> usize {
        if self.parent[node] != node {
            let root = self.find(self.parent[node]);
            self.parent[node] = root;
        }
        self.parent[node]
    }

    fn union(&mut self, lhs: usize, rhs: usize) {
        let lroot = self.find(lhs);
        let rroot = self.find(rhs);
        if lroot != rroot {
            let (small, large) = if lroot < rroot {
                (lroot, rroot)
            } else {
                (rroot, lroot)
            };
            self.parent[large] = small;
        }
    }
}

#[cfg(test)]
mod tests {
    use axeyum_smtlib::parse_script;

    use super::{BvUfLocalRefutationKind, bv_uf_local_refutation};

    #[test]
    fn recognizes_qf_ufff_congruent_disequality_row() {
        let script = parse_script(include_str!(
            "../../../corpus/public-curated/non-incremental/QF_UFFF/cvc5-regress-clean/cli__regress0__ff__with_uf2.smt2"
        ))
        .expect("QF_UFFF row parses");
        let cert = bv_uf_local_refutation(&script.arena, &script.assertions)
            .expect("local BV+UF refutes row");
        assert_eq!(cert.kind, BvUfLocalRefutationKind::CongruentDisequality);
        assert!(!cert.derived_equalities.is_empty());
    }

    #[test]
    fn recognizes_qf_ufff_pure_bv_conflict_after_congruence_row() {
        let script = parse_script(include_str!(
            "../../../corpus/public-curated/non-incremental/QF_UFFF/cvc5-regress-clean/cli__regress0__ff__with_uf5.smt2"
        ))
        .expect("QF_UFFF row parses");
        let cert = bv_uf_local_refutation(&script.arena, &script.assertions)
            .expect("local BV+UF refutes row");
        assert_eq!(
            cert.kind,
            BvUfLocalRefutationKind::PureBvConflictAfterCongruence
        );
        assert_ne!(cert.conflict_cases, 0);
    }
}
