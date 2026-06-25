//! Small checked array-axiom refutations.
//!
//! This module recognizes single top-level negations of array identities that are
//! valid by the SMT array axioms, then records the matched schema as evidence.
//! It is deliberately narrow: it is a bridge for repeated corpus shapes, not a
//! general array-elimination certificate.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::{ArraySortKey, Assignment, Op, Sort, TermArena, TermId, TermNode, Value, eval};

/// The small array axiom schema used by a checked refutation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArrayAxiomKind {
    /// `select(store(a, i, v), j) = ite(i = j, v, select(a, j))`.
    ReadOverWrite,
    /// `select(ite(c, a, b), i) = ite(c, select(a, i), select(b, i))`.
    SelectIte,
    /// `select(ite(c, store(a,i,v), store(b,i,v)), j)
    ///  = select(store(ite(c,a,b), i, v), j)`.
    StoreIteSelect,
    /// Read congruence: equal arrays read at equal indices have equal values.
    ReadCongruence,
    /// Store shadowing: an earlier write to the same syntactic index is
    /// overwritten by a later write.
    StoreShadowing,
}

/// A self-checking refutation of `not (= lhs rhs)` where `lhs = rhs` is one of
/// the checked array axiom schemas above.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArrayAxiomRefutationCertificate {
    /// The original top-level disequality assertion.
    pub assertion: TermId,
    /// The left side of the asserted equality inside the negation.
    pub lhs: TermId,
    /// The right side of the asserted equality inside the negation.
    pub rhs: TermId,
    /// Which valid array axiom schema refutes the assertion.
    pub kind: ArrayAxiomKind,
}

/// Returns a certificate when any top-level conjunct is the negation of one of
/// the checked array-axiom schemas.
///
/// BTOR-derived ABV files often encode Boolean propositions as BV1 terms
/// asserted equal to `#b1`. For those, the recognizer only descends through
/// BV1 conjunctions under an asserted-true bit, so every candidate it accepts is
/// entailed by the original assertion.
#[must_use]
pub fn array_axiom_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<ArrayAxiomRefutationCertificate> {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        collect_top_conjuncts(arena, assertion, &mut conjuncts);
    }

    for assertion in conjuncts {
        let Some((lhs, rhs)) = match_disequality(arena, assertion) else {
            continue;
        };
        if let Some(kind) = valid_array_axiom(arena, lhs, rhs) {
            return Some(ArrayAxiomRefutationCertificate {
                assertion,
                lhs,
                rhs,
                kind,
            });
        }
        if let Some(kind) = valid_array_axiom(arena, rhs, lhs) {
            return Some(ArrayAxiomRefutationCertificate {
                assertion,
                lhs,
                rhs,
                kind,
            });
        }
    }

    for &assertion in assertions {
        if let Some(cert) = read_congruence_refutation(arena, assertion) {
            return Some(cert);
        }
    }
    None
}

fn read_congruence_refutation(
    arena: &TermArena,
    assertion: TermId,
) -> Option<ArrayAxiomRefutationCertificate> {
    let mut probe = ReadCongruenceProbe::default();
    if let Some(bit) = match_bv1_asserted_true(arena, assertion) {
        collect_bit_assertion(arena, bit, true, &mut probe);
        if let Some((lhs, rhs)) = prove_bit_term(arena, &probe.facts, bit, false) {
            return Some(ArrayAxiomRefutationCertificate {
                assertion,
                lhs,
                rhs,
                kind: ArrayAxiomKind::ReadCongruence,
            });
        }
    } else {
        collect_bool_assertion(arena, assertion, true, &mut probe)?;
    }
    let (lhs, rhs) = probe.refuted_pair(arena)?;
    Some(ArrayAxiomRefutationCertificate {
        assertion,
        lhs,
        rhs,
        kind: ArrayAxiomKind::ReadCongruence,
    })
}

#[derive(Default)]
struct ReadCongruenceProbe {
    facts: EqFacts,
    disequalities: Vec<(TermId, TermId)>,
    asserted_or: Vec<Vec<BitLiteral>>,
    denied_and: Vec<Vec<BitLiteral>>,
    asserted_or_terms: Vec<Vec<TermId>>,
    denied_and_terms: Vec<Vec<TermId>>,
}

impl ReadCongruenceProbe {
    fn refuted_pair(&self, arena: &TermArena) -> Option<(TermId, TermId)> {
        for (idx, &(lhs, rhs)) in self.disequalities.iter().enumerate() {
            let distinct: Vec<_> = self
                .disequalities
                .iter()
                .enumerate()
                .filter_map(|(other_idx, pair)| (other_idx != idx).then_some(*pair))
                .collect();
            if terms_equivalent_with_distinct(arena, &self.facts, &distinct, lhs, rhs) {
                return Some((lhs, rhs));
            }
        }
        for disjunction in &self.asserted_or {
            if disjunction
                .iter()
                .all(|literal| literal.is_false(arena, &self.facts))
            {
                return disjunction
                    .iter()
                    .find_map(|literal| literal.false_witness(arena, &self.facts));
            }
        }
        for conjunction in &self.denied_and {
            if conjunction
                .iter()
                .all(|literal| literal.is_true(arena, &self.facts))
            {
                return conjunction
                    .iter()
                    .find_map(|literal| literal.true_witness(arena, &self.facts));
            }
        }
        for disjunction in &self.asserted_or_terms {
            let mut witness = None;
            if disjunction.iter().all(|&term| {
                let term_witness = prove_bit_term(arena, &self.facts, term, false);
                if witness.is_none() {
                    witness = term_witness;
                }
                term_witness.is_some()
            }) {
                return witness;
            }
        }
        for conjunction in &self.denied_and_terms {
            let mut witness = None;
            if conjunction.iter().all(|&term| {
                let term_witness = prove_bit_term(arena, &self.facts, term, true);
                if witness.is_none() {
                    witness = term_witness;
                }
                term_witness.is_some()
            }) {
                return witness;
            }
        }
        None
    }
}

#[derive(Clone, Default)]
struct EqFacts {
    parent: BTreeMap<TermId, TermId>,
    bv1_values: BTreeMap<TermId, bool>,
    store_self_reads: Vec<(TermId, TermId, TermId)>,
}

impl EqFacts {
    fn add(&mut self, lhs: TermId, rhs: TermId) {
        let lhs_root = self.find(lhs);
        let rhs_root = self.find(rhs);
        if lhs_root == rhs_root {
            return;
        }
        let (parent, child) = if lhs_root <= rhs_root {
            (lhs_root, rhs_root)
        } else {
            (rhs_root, lhs_root)
        };
        self.parent.insert(child, parent);
        self.parent.entry(parent).or_insert(parent);
    }

    fn find(&self, term: TermId) -> TermId {
        let mut current = term;
        while let Some(&parent) = self.parent.get(&current) {
            if parent == current {
                break;
            }
            current = parent;
        }
        current
    }

    fn same(&self, lhs: TermId, rhs: TermId) -> bool {
        self.find(lhs) == self.find(rhs)
    }

    fn set_bv1(&mut self, term: TermId, value: bool) {
        self.bv1_values.insert(term, value);
    }

    fn add_store_self_read(&mut self, base: TermId, index: TermId, value: TermId) {
        let fact = (base, index, value);
        if !self.store_self_reads.contains(&fact) {
            self.store_self_reads.push(fact);
        }
    }
}

#[derive(Clone, Copy)]
struct BitLiteral {
    lhs: TermId,
    rhs: TermId,
    equal_when_true: bool,
}

impl BitLiteral {
    fn assert(
        &self,
        arena: &TermArena,
        facts: &mut EqFacts,
        disequalities: &mut Vec<(TermId, TermId)>,
    ) {
        if self.equal_when_true {
            facts.add(self.lhs, self.rhs);
            add_derived_equality_facts(arena, facts, self.lhs, self.rhs);
        } else {
            disequalities.push((self.lhs, self.rhs));
            add_bvnot_injectivity_disequality(arena, disequalities, self.lhs, self.rhs);
        }
    }

    fn deny(
        &self,
        arena: &TermArena,
        facts: &mut EqFacts,
        disequalities: &mut Vec<(TermId, TermId)>,
    ) {
        if self.equal_when_true {
            disequalities.push((self.lhs, self.rhs));
            add_bvnot_injectivity_disequality(arena, disequalities, self.lhs, self.rhs);
        } else {
            facts.add(self.lhs, self.rhs);
            add_derived_equality_facts(arena, facts, self.lhs, self.rhs);
        }
    }

    fn is_true(&self, arena: &TermArena, facts: &EqFacts) -> bool {
        self.equal_when_true && terms_equivalent(arena, facts, self.lhs, self.rhs)
    }

    fn is_false(&self, arena: &TermArena, facts: &EqFacts) -> bool {
        !self.equal_when_true && terms_equivalent(arena, facts, self.lhs, self.rhs)
    }

    fn true_witness(&self, arena: &TermArena, facts: &EqFacts) -> Option<(TermId, TermId)> {
        if self.is_true(arena, facts) {
            Some((self.lhs, self.rhs))
        } else {
            None
        }
    }

    fn false_witness(&self, arena: &TermArena, facts: &EqFacts) -> Option<(TermId, TermId)> {
        if self.is_false(arena, facts) {
            Some((self.lhs, self.rhs))
        } else {
            None
        }
    }
}

fn add_derived_equality_facts(arena: &TermArena, facts: &mut EqFacts, lhs: TermId, rhs: TermId) {
    add_bvnot_injectivity_fact(arena, facts, lhs, rhs);
    add_bvxor_zero_equality_fact(arena, facts, lhs, rhs);
    add_concat_injectivity_fact(arena, facts, lhs, rhs);
    add_store_same_cell_injectivity_fact(arena, facts, lhs, rhs);
    add_store_self_update_read_fact(arena, facts, lhs, rhs);
}

fn add_bvnot_injectivity_fact(arena: &TermArena, facts: &mut EqFacts, lhs: TermId, rhs: TermId) {
    if let (Some(lhs_inner), Some(rhs_inner)) = (match_bv_not(arena, lhs), match_bv_not(arena, rhs))
    {
        if arena.sort_of(lhs_inner) == arena.sort_of(rhs_inner) {
            facts.add(lhs_inner, rhs_inner);
        }
    }
}

fn add_bvnot_injectivity_disequality(
    arena: &TermArena,
    disequalities: &mut Vec<(TermId, TermId)>,
    lhs: TermId,
    rhs: TermId,
) {
    if let (Some(lhs_inner), Some(rhs_inner)) = (match_bv_not(arena, lhs), match_bv_not(arena, rhs))
    {
        if arena.sort_of(lhs_inner) == arena.sort_of(rhs_inner) {
            disequalities.push((lhs_inner, rhs_inner));
        }
    }
}

fn add_bvxor_zero_equality_fact(arena: &TermArena, facts: &mut EqFacts, lhs: TermId, rhs: TermId) {
    add_bvxor_zero_equality_fact_one(arena, facts, lhs, rhs);
    add_bvxor_zero_equality_fact_one(arena, facts, rhs, lhs);
}

fn add_bvxor_zero_equality_fact_one(
    arena: &TermArena,
    facts: &mut EqFacts,
    xor_term: TermId,
    zero_term: TermId,
) {
    if !is_bv_zero(arena, zero_term) {
        return;
    }
    let Some((lhs, rhs)) = match_bv_xor(arena, xor_term) else {
        return;
    };
    facts.add(lhs, rhs);
    add_concat_injectivity_fact(arena, facts, lhs, rhs);
}

fn add_concat_injectivity_fact(arena: &TermArena, facts: &mut EqFacts, lhs: TermId, rhs: TermId) {
    let Some((lhs_hi, lhs_lo)) = match_concat(arena, lhs) else {
        return;
    };
    let Some((rhs_hi, rhs_lo)) = match_concat(arena, rhs) else {
        return;
    };
    if arena.sort_of(lhs_hi) == arena.sort_of(rhs_hi)
        && arena.sort_of(lhs_lo) == arena.sort_of(rhs_lo)
    {
        facts.add(lhs_hi, rhs_hi);
        facts.add(lhs_lo, rhs_lo);
    }
}

fn add_store_same_cell_injectivity_fact(
    arena: &TermArena,
    facts: &mut EqFacts,
    lhs: TermId,
    rhs: TermId,
) {
    let Some((lhs_base, lhs_index, lhs_value)) = match_store(arena, lhs) else {
        return;
    };
    let Some((rhs_base, rhs_index, rhs_value)) = match_store(arena, rhs) else {
        return;
    };
    if lhs_base == rhs_base && indices_definitely_equal(arena, lhs_index, rhs_index) {
        facts.add(lhs_value, rhs_value);
    }
}

fn add_store_self_update_read_fact(
    arena: &TermArena,
    facts: &mut EqFacts,
    lhs: TermId,
    rhs: TermId,
) {
    add_store_self_update_read_fact_one(arena, facts, lhs, rhs);
    add_store_self_update_read_fact_one(arena, facts, rhs, lhs);
}

fn add_store_self_update_read_fact_one(
    arena: &TermArena,
    facts: &mut EqFacts,
    base_term: TermId,
    store_term: TermId,
) {
    let Some((store_base, index, value)) = match_store(arena, store_term) else {
        return;
    };
    if base_term == store_base {
        facts.add_store_self_read(store_base, index, value);
    }
}

fn match_bv_not(arena: &TermArena, term: TermId) -> Option<TermId> {
    let TermNode::App {
        op: Op::BvNot,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [inner] = &**args else {
        return None;
    };
    matches!(arena.sort_of(term), Sort::BitVec(_)).then_some(*inner)
}

fn match_bv_xor(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let TermNode::App {
        op: Op::BvXor,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    matches!(arena.sort_of(term), Sort::BitVec(_)).then_some((*lhs, *rhs))
}

fn match_concat(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let TermNode::App {
        op: Op::Concat,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    matches!(arena.sort_of(term), Sort::BitVec(_)).then_some((*lhs, *rhs))
}

fn collect_bit_assertion(
    arena: &TermArena,
    bit: TermId,
    polarity: bool,
    probe: &mut ReadCongruenceProbe,
) {
    if let TermNode::App { op, args } = arena.node(bit) {
        match (op, polarity) {
            (Op::BvAnd, true) if args.len() == 2 && arena.sort_of(bit) == Sort::BitVec(1) => {
                collect_bit_assertion(arena, args[0], true, probe);
                collect_bit_assertion(arena, args[1], true, probe);
                return;
            }
            (Op::BvOr, false) if args.len() == 2 && arena.sort_of(bit) == Sort::BitVec(1) => {
                collect_bit_assertion(arena, args[0], false, probe);
                collect_bit_assertion(arena, args[1], false, probe);
                return;
            }
            (Op::BvOr, true) if args.len() == 2 && arena.sort_of(bit) == Sort::BitVec(1) => {
                let mut literals = Vec::new();
                if collect_or_literals(arena, bit, &mut literals) && !literals.is_empty() {
                    probe.asserted_or.push(literals);
                } else {
                    let mut terms = Vec::new();
                    collect_bv1_or_terms(arena, bit, &mut terms);
                    if !terms.is_empty() {
                        probe.asserted_or_terms.push(terms);
                    }
                }
                return;
            }
            (Op::BvAnd, false) if args.len() == 2 && arena.sort_of(bit) == Sort::BitVec(1) => {
                let mut literals = Vec::new();
                if collect_and_literals(arena, bit, &mut literals) && !literals.is_empty() {
                    probe.denied_and.push(literals);
                } else {
                    let mut terms = Vec::new();
                    collect_bv1_and_terms(arena, bit, &mut terms);
                    if !terms.is_empty() {
                        probe.denied_and_terms.push(terms);
                    }
                }
                return;
            }
            (Op::BvNot, _) if args.len() == 1 && arena.sort_of(bit) == Sort::BitVec(1) => {
                collect_bit_assertion(arena, args[0], !polarity, probe);
                return;
            }
            _ => {}
        }
    }

    if let Some(literal) = match_bit_literal(arena, bit) {
        if polarity {
            literal.assert(arena, &mut probe.facts, &mut probe.disequalities);
        } else {
            literal.deny(arena, &mut probe.facts, &mut probe.disequalities);
        }
    } else if record_bv1_ult_assertion(arena, bit, polarity, &mut probe.facts) {
        // The order assertion contributed forced BV1 endpoint values.
    } else if arena.sort_of(bit) == Sort::BitVec(1) {
        probe.facts.set_bv1(bit, polarity);
    }
}

fn collect_bool_assertion(
    arena: &TermArena,
    term: TermId,
    polarity: bool,
    probe: &mut ReadCongruenceProbe,
) -> Option<()> {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolAnd,
            args,
        } if polarity && args.len() == 2 => {
            collect_bool_assertion(arena, args[0], true, probe)?;
            collect_bool_assertion(arena, args[1], true, probe)?;
            Some(())
        }
        TermNode::App {
            op: Op::BoolOr,
            args,
        } if !polarity && args.len() == 2 => {
            collect_bool_assertion(arena, args[0], false, probe)?;
            collect_bool_assertion(arena, args[1], false, probe)?;
            Some(())
        }
        TermNode::App {
            op: Op::BoolNot,
            args,
        } if args.len() == 1 => collect_bool_assertion(arena, args[0], !polarity, probe),
        TermNode::App { op: Op::Eq, args } if args.len() == 2 => {
            let literal = BitLiteral {
                lhs: args[0],
                rhs: args[1],
                equal_when_true: true,
            };
            if polarity {
                literal.assert(arena, &mut probe.facts, &mut probe.disequalities);
            } else {
                literal.deny(arena, &mut probe.facts, &mut probe.disequalities);
            }
            Some(())
        }
        _ => None,
    }
}

fn record_bv1_ult_assertion(
    arena: &TermArena,
    bit: TermId,
    polarity: bool,
    facts: &mut EqFacts,
) -> bool {
    let Some((lhs, rhs, bit_true_means_ult)) = match_bv1_ult_bit(arena, bit) else {
        return false;
    };
    if polarity != bit_true_means_ult {
        return false;
    }
    facts.set_bv1(lhs, false);
    facts.set_bv1(rhs, true);
    true
}

fn collect_or_literals(arena: &TermArena, bit: TermId, out: &mut Vec<BitLiteral>) -> bool {
    match arena.node(bit) {
        TermNode::App { op: Op::BvOr, args }
            if args.len() == 2 && arena.sort_of(bit) == Sort::BitVec(1) =>
        {
            collect_or_literals(arena, args[0], out) && collect_or_literals(arena, args[1], out)
        }
        _ => {
            if let Some(literal) = match_bit_literal(arena, bit) {
                out.push(literal);
                true
            } else {
                false
            }
        }
    }
}

fn collect_and_literals(arena: &TermArena, bit: TermId, out: &mut Vec<BitLiteral>) -> bool {
    match arena.node(bit) {
        TermNode::App {
            op: Op::BvAnd,
            args,
        } if args.len() == 2 && arena.sort_of(bit) == Sort::BitVec(1) => {
            collect_and_literals(arena, args[0], out) && collect_and_literals(arena, args[1], out)
        }
        _ => {
            if let Some(literal) = match_bit_literal(arena, bit) {
                out.push(literal);
                true
            } else {
                false
            }
        }
    }
}

fn collect_bv1_or_terms(arena: &TermArena, bit: TermId, out: &mut Vec<TermId>) {
    match arena.node(bit) {
        TermNode::App { op: Op::BvOr, args }
            if args.len() == 2 && arena.sort_of(bit) == Sort::BitVec(1) =>
        {
            collect_bv1_or_terms(arena, args[0], out);
            collect_bv1_or_terms(arena, args[1], out);
        }
        _ => out.push(bit),
    }
}

fn collect_bv1_and_terms(arena: &TermArena, bit: TermId, out: &mut Vec<TermId>) {
    match arena.node(bit) {
        TermNode::App {
            op: Op::BvAnd,
            args,
        } if args.len() == 2 && arena.sort_of(bit) == Sort::BitVec(1) => {
            collect_bv1_and_terms(arena, args[0], out);
            collect_bv1_and_terms(arena, args[1], out);
        }
        _ => out.push(bit),
    }
}

fn match_bit_literal(arena: &TermArena, bit: TermId) -> Option<BitLiteral> {
    if let Some((lhs, rhs, equal_when_true)) = match_bv1_literal_bit(arena, bit) {
        return Some(BitLiteral {
            lhs,
            rhs,
            equal_when_true,
        });
    }
    if let TermNode::App {
        op: Op::BvNot,
        args,
    } = arena.node(bit)
    {
        let [inner] = &**args else {
            return None;
        };
        let mut literal = match_bit_literal(arena, *inner)?;
        literal.equal_when_true = !literal.equal_when_true;
        return Some(literal);
    }
    None
}

fn collect_top_conjuncts(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolAnd,
            args,
        } if args.len() == 2 => {
            collect_top_conjuncts(arena, args[0], out);
            collect_top_conjuncts(arena, args[1], out);
        }
        _ => {
            if let Some(bit) = match_bv1_asserted_true(arena, term) {
                collect_bv1_conjuncts(arena, bit, out);
            } else {
                out.push(term);
            }
        }
    }
}

fn collect_bv1_conjuncts(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    match arena.node(term) {
        TermNode::App {
            op: Op::BvAnd,
            args,
        } if args.len() == 2 && arena.sort_of(term) == Sort::BitVec(1) => {
            collect_bv1_conjuncts(arena, args[0], out);
            collect_bv1_conjuncts(arena, args[1], out);
        }
        _ => out.push(term),
    }
}

fn match_disequality(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    if let Some(bit) = match_bv1_asserted_true(arena, term) {
        return match_disequality(arena, bit);
    }

    if let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(term)
    {
        let [inner] = &**args else {
            return None;
        };
        let TermNode::App { op: Op::Eq, args } = arena.node(*inner) else {
            return None;
        };
        let [lhs, rhs] = &**args else {
            return None;
        };
        return Some((*lhs, *rhs));
    }

    if let TermNode::App {
        op: Op::BvNot,
        args,
    } = arena.node(term)
    {
        let [inner] = &**args else {
            return None;
        };
        return match_bit_literal(arena, *inner)
            .filter(|literal| literal.equal_when_true)
            .map(|literal| (literal.lhs, literal.rhs));
    }

    match_bit_literal(arena, term)
        .filter(|literal| !literal.equal_when_true)
        .map(|literal| (literal.lhs, literal.rhs))
}

fn valid_array_axiom(arena: &TermArena, lhs: TermId, rhs: TermId) -> Option<ArrayAxiomKind> {
    if is_read_over_write_reduction(arena, lhs, rhs)
        || is_read_over_write_same_index(arena, lhs, rhs)
        || is_read_over_write(arena, lhs, rhs)
    {
        Some(ArrayAxiomKind::ReadOverWrite)
    } else if is_select_ite(arena, lhs, rhs) {
        Some(ArrayAxiomKind::SelectIte)
    } else if is_store_ite_select(arena, lhs, rhs) {
        Some(ArrayAxiomKind::StoreIteSelect)
    } else if is_store_shadowing(arena, lhs, rhs) {
        Some(ArrayAxiomKind::StoreShadowing)
    } else {
        None
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RowExpr {
    Term(TermId),
    Select { array: TermId, index: TermId },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct RowNorm {
    expr: RowExpr,
    changed: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct StoreNorm {
    base: TermId,
    writes: Vec<(TermId, TermId)>,
    changed: bool,
}

fn is_store_shadowing(arena: &TermArena, lhs: TermId, rhs: TermId) -> bool {
    let lhs_norm = normalize_store_shadows(arena, lhs);
    let rhs_norm = normalize_store_shadows(arena, rhs);
    (lhs_norm.changed || rhs_norm.changed)
        && lhs_norm.base == rhs_norm.base
        && lhs_norm.writes == rhs_norm.writes
}

fn normalize_store_shadows(arena: &TermArena, term: TermId) -> StoreNorm {
    let (base, writes) = collect_store_chain(arena, term);
    let mut normalized = Vec::with_capacity(writes.len());
    let mut changed = false;

    for (idx, &(index, value)) in writes.iter().enumerate() {
        if writes[idx + 1..]
            .iter()
            .any(|&(later_index, _)| later_index == index)
        {
            changed = true;
            continue;
        }
        normalized.push((index, value));
    }

    StoreNorm {
        base,
        writes: normalized,
        changed,
    }
}

fn collect_store_chain(arena: &TermArena, mut term: TermId) -> (TermId, Vec<(TermId, TermId)>) {
    let mut writes = Vec::new();
    while let Some((base, index, value)) = match_store(arena, term) {
        writes.push((index, value));
        term = base;
    }
    writes.reverse();
    (term, writes)
}

fn is_read_over_write_reduction(arena: &TermArena, lhs: TermId, rhs: TermId) -> bool {
    let lhs_norm = normalize_read_over_writes(arena, lhs);
    let rhs_norm = normalize_read_over_writes(arena, rhs);
    (lhs_norm.changed || rhs_norm.changed) && lhs_norm.expr == rhs_norm.expr
}

fn normalize_read_over_writes(arena: &TermArena, term: TermId) -> RowNorm {
    let Some((mut array, index)) = match_select(arena, term) else {
        return RowNorm {
            expr: RowExpr::Term(term),
            changed: false,
        };
    };
    let mut changed = false;
    while let Some((base, write_idx, value)) = match_store(arena, array) {
        if indices_definitely_equal(arena, index, write_idx) {
            return RowNorm {
                expr: RowExpr::Term(value),
                changed: true,
            };
        }
        if !indices_definitely_distinct(arena, index, write_idx) {
            break;
        }
        array = base;
        changed = true;
    }
    RowNorm {
        expr: RowExpr::Select { array, index },
        changed,
    }
}

fn indices_definitely_equal(arena: &TermArena, lhs: TermId, rhs: TermId) -> bool {
    lhs == rhs
        || matches!(
            (const_bv_value(arena, lhs), const_bv_value(arena, rhs)),
            (Some((lhs_width, lhs_value)), Some((rhs_width, rhs_value)))
                if lhs_width == rhs_width && lhs_value == rhs_value
        )
}

fn indices_definitely_distinct(arena: &TermArena, lhs: TermId, rhs: TermId) -> bool {
    matches!(
        (const_bv_value(arena, lhs), const_bv_value(arena, rhs)),
        (Some((lhs_width, lhs_value)), Some((rhs_width, rhs_value)))
            if lhs_width == rhs_width && lhs_value != rhs_value
    ) || bv_nonzero_offset_pair(arena, lhs, rhs)
        || bv_nonzero_offset_pair(arena, rhs, lhs)
        || bv_low_suffix_pair_distinct(arena, lhs, rhs)
}

fn const_bv_value(arena: &TermArena, term: TermId) -> Option<(u32, u128)> {
    match arena.node(term) {
        TermNode::BvConst { width, value } => Some((*width, *value)),
        _ => match eval(arena, term, &Assignment::new()).ok()? {
            Value::Bv { width, value } => Some((width, value)),
            _ => None,
        },
    }
}

fn bv_low_suffix_pair_distinct(arena: &TermArena, lhs: TermId, rhs: TermId) -> bool {
    let Some((lhs_width, lhs_value)) = bv_low_const_suffix(arena, lhs) else {
        return false;
    };
    let Some((rhs_width, rhs_value)) = bv_low_const_suffix(arena, rhs) else {
        return false;
    };
    let overlap = lhs_width.min(rhs_width);
    if overlap == 0 {
        return false;
    }
    let mask = bv_mask(overlap);
    (lhs_value & mask) != (rhs_value & mask)
}

fn bv_low_const_suffix(arena: &TermArena, term: TermId) -> Option<(u32, u128)> {
    match arena.node(term) {
        TermNode::BvConst { width, value } => Some((*width, *value)),
        TermNode::App {
            op: Op::Concat,
            args,
        } if args.len() == 2 => bv_low_const_suffix(arena, args[1]),
        _ => None,
    }
}

fn bv_mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1_u128 << width) - 1
    }
}

fn bv_nonzero_offset_pair(arena: &TermArena, base: TermId, offset: TermId) -> bool {
    let Some((offset_base, _width, value)) = match_bv_add_const(arena, offset) else {
        return false;
    };
    base == offset_base && value != 0
}

fn match_bv_add_const(arena: &TermArena, term: TermId) -> Option<(TermId, u32, u128)> {
    let TermNode::App {
        op: Op::BvAdd,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    if let Some((width, value)) = const_bv_value(arena, *lhs) {
        if arena.sort_of(*rhs) == Sort::BitVec(width) {
            return Some((*rhs, width, value));
        }
    }
    if let Some((width, value)) = const_bv_value(arena, *rhs) {
        if arena.sort_of(*lhs) == Sort::BitVec(width) {
            return Some((*lhs, width, value));
        }
    }
    None
}

fn terms_equivalent(arena: &TermArena, facts: &EqFacts, lhs: TermId, rhs: TermId) -> bool {
    terms_equivalent_with_distinct(arena, facts, &[], lhs, rhs)
}

fn prove_bit_term(
    arena: &TermArena,
    facts: &EqFacts,
    term: TermId,
    polarity: bool,
) -> Option<(TermId, TermId)> {
    if let TermNode::App { op, args } = arena.node(term) {
        match (op, polarity) {
            (Op::BvNot, _) if args.len() == 1 && arena.sort_of(term) == Sort::BitVec(1) => {
                return prove_bit_term(arena, facts, args[0], !polarity);
            }
            (Op::BvAnd, true) if args.len() == 2 && arena.sort_of(term) == Sort::BitVec(1) => {
                let mut witness = None;
                for &arg in args {
                    let arg_witness = prove_bit_term(arena, facts, arg, true)?;
                    if witness.is_none() {
                        witness = Some(arg_witness);
                    }
                }
                return witness;
            }
            (Op::BvAnd, false) if args.len() == 2 && arena.sort_of(term) == Sort::BitVec(1) => {
                if let Some(witness) = prove_bv1_conjunction_false(arena, facts, term) {
                    return Some(witness);
                }
                for &arg in args {
                    if let Some(witness) = prove_bit_term(arena, facts, arg, false) {
                        return Some(witness);
                    }
                }
                return None;
            }
            (Op::BvOr, false) if args.len() == 2 && arena.sort_of(term) == Sort::BitVec(1) => {
                let mut witness = None;
                for &arg in args {
                    let arg_witness = prove_bit_term(arena, facts, arg, false)?;
                    if witness.is_none() {
                        witness = Some(arg_witness);
                    }
                }
                return witness;
            }
            (Op::BvOr, true) if args.len() == 2 && arena.sort_of(term) == Sort::BitVec(1) => {
                for &arg in args {
                    if let Some(witness) = prove_bit_term(arena, facts, arg, true) {
                        return Some(witness);
                    }
                }
                return None;
            }
            _ => {}
        }
    }

    if let Some(literal) = match_bit_literal(arena, term) {
        let literal_witness = if polarity {
            literal.true_witness(arena, facts)
        } else {
            literal.false_witness(arena, facts)
        };
        if literal_witness.is_some() {
            return literal_witness;
        }
    }

    let mut memo = BTreeMap::new();
    let value = known_bv1_value_in_context(arena, facts, &[], term, &mut memo)?;
    if value == polarity {
        let const_term = find_bv1_const_term(arena, term, value)?;
        Some((term, const_term))
    } else {
        None
    }
}

fn prove_bv1_conjunction_false(
    arena: &TermArena,
    facts: &EqFacts,
    term: TermId,
) -> Option<(TermId, TermId)> {
    let mut terms = Vec::new();
    collect_bv1_and_terms(arena, term, &mut terms);
    if terms.is_empty() {
        return None;
    }

    let mut branch_probe = ReadCongruenceProbe {
        facts: facts.clone(),
        ..ReadCongruenceProbe::default()
    };
    for term in terms {
        collect_bit_assertion(arena, term, true, &mut branch_probe);
    }
    branch_probe.refuted_pair(arena)
}

fn terms_equivalent_with_distinct(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    lhs: TermId,
    rhs: TermId,
) -> bool {
    let mut memo = BTreeMap::new();
    terms_equivalent_inner(arena, facts, distinct, lhs, rhs, &mut memo)
}

fn terms_equivalent_inner(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    lhs: TermId,
    rhs: TermId,
    memo: &mut BTreeMap<(TermId, TermId), bool>,
) -> bool {
    let key = if lhs <= rhs { (lhs, rhs) } else { (rhs, lhs) };
    if let Some(result) = memo.get(&key) {
        return *result;
    }

    let lhs_simplified = simplify_contextual_term(arena, facts, distinct, lhs, memo);
    let rhs_simplified = simplify_contextual_term(arena, facts, distinct, rhs, memo);
    if lhs_simplified != lhs || rhs_simplified != rhs {
        let result =
            terms_equivalent_inner(arena, facts, distinct, lhs_simplified, rhs_simplified, memo);
        memo.insert(key, result);
        return result;
    }

    let lhs_row = normalize_read_over_writes_in_context(arena, facts, distinct, lhs, memo);
    let rhs_row = normalize_read_over_writes_in_context(arena, facts, distinct, rhs, memo);
    if lhs_row.changed || rhs_row.changed {
        let result = row_expr_equivalent(arena, facts, distinct, lhs_row.expr, rhs_row.expr, memo);
        memo.insert(key, result);
        return result;
    }

    if store_self_update_read_equivalent(arena, facts, lhs, rhs) {
        memo.insert(key, true);
        return true;
    }

    if equal_array_readback_equivalent(arena, facts, distinct, lhs, rhs) {
        memo.insert(key, true);
        return true;
    }

    let known_bv1_equal = match (
        known_bv1_value_in_context(arena, facts, distinct, lhs, memo),
        known_bv1_value_in_context(arena, facts, distinct, rhs, memo),
    ) {
        (Some(lhs_value), Some(rhs_value)) => lhs_value == rhs_value,
        _ => false,
    };

    let known_const_bv_equal = match (const_bv_value(arena, lhs), const_bv_value(arena, rhs)) {
        (Some((lhs_width, lhs_value)), Some((rhs_width, rhs_value))) => {
            lhs_width == rhs_width && lhs_value == rhs_value
        }
        _ => false,
    };

    let finite_array_extensional_equal =
        finite_array_extensional_bit_equivalence(arena, facts, distinct, lhs, rhs, memo);
    let finite_array_known_reads_equal =
        finite_array_known_read_equivalence(arena, facts, distinct, lhs, rhs, memo);
    let finite_array_read_facts_equal =
        finite_array_read_fact_equivalence(arena, facts, distinct, lhs, rhs, memo);

    let result = facts.same(lhs, rhs)
        || known_bv1_equal
        || known_const_bv_equal
        || finite_array_extensional_equal
        || finite_array_known_reads_equal
        || finite_array_read_facts_equal
        || match (arena.node(lhs), arena.node(rhs)) {
            (
                TermNode::BvConst {
                    width: lhs_width,
                    value: lhs_value,
                },
                TermNode::BvConst {
                    width: rhs_width,
                    value: rhs_value,
                },
            ) => lhs_width == rhs_width && lhs_value == rhs_value,
            (TermNode::WideBvConst(lhs_value), TermNode::WideBvConst(rhs_value)) => {
                lhs_value == rhs_value
            }
            (TermNode::BoolConst(lhs_value), TermNode::BoolConst(rhs_value)) => {
                lhs_value == rhs_value
            }
            (
                TermNode::App {
                    op: lhs_op,
                    args: lhs_args,
                },
                TermNode::App {
                    op: rhs_op,
                    args: rhs_args,
                },
            ) if lhs_op == rhs_op && lhs_args.len() == rhs_args.len() => lhs_args
                .iter()
                .zip(rhs_args.iter())
                .all(|(&lhs_arg, &rhs_arg)| {
                    terms_equivalent_inner(arena, facts, distinct, lhs_arg, rhs_arg, memo)
                }),
            _ => false,
        };
    memo.insert(key, result);
    result
}

fn equal_array_readback_equivalent(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    lhs: TermId,
    rhs: TermId,
) -> bool {
    let target_sort = arena.sort_of(lhs);
    if target_sort != arena.sort_of(rhs) {
        return false;
    }

    let arrays: Vec<_> = facts
        .parent
        .keys()
        .copied()
        .filter(|&term| matches!(arena.sort_of(term), Sort::Array { .. }))
        .collect();
    for (idx, &lhs_array) in arrays.iter().enumerate() {
        let Sort::Array { element, .. } = arena.sort_of(lhs_array) else {
            continue;
        };
        if element.to_sort() != target_sort {
            continue;
        }
        for &rhs_array in &arrays[idx + 1..] {
            if lhs_array == rhs_array
                || arena.sort_of(lhs_array) != arena.sort_of(rhs_array)
                || !facts.same(lhs_array, rhs_array)
            {
                continue;
            }

            let mut candidate_indices = BTreeSet::new();
            collect_store_write_indices(arena, lhs_array, &mut candidate_indices);
            collect_store_write_indices(arena, rhs_array, &mut candidate_indices);
            collect_target_select_index(arena, lhs, &mut candidate_indices);
            collect_target_select_index(arena, rhs, &mut candidate_indices);

            for index in candidate_indices {
                let lhs_read =
                    normalize_select_over_writes_direct(arena, facts, distinct, lhs_array, index);
                let rhs_read =
                    normalize_select_over_writes_direct(arena, facts, distinct, rhs_array, index);
                if row_expr_directly_matches_term(arena, facts, lhs_read.expr, lhs)
                    && row_expr_directly_matches_term(arena, facts, rhs_read.expr, rhs)
                {
                    return true;
                }
                if row_expr_directly_matches_term(arena, facts, lhs_read.expr, rhs)
                    && row_expr_directly_matches_term(arena, facts, rhs_read.expr, lhs)
                {
                    return true;
                }
            }
        }
    }
    false
}

fn collect_store_write_indices(arena: &TermArena, mut term: TermId, out: &mut BTreeSet<TermId>) {
    while let Some((base, index, _value)) = match_store(arena, term) {
        out.insert(index);
        term = base;
    }
}

fn collect_target_select_index(arena: &TermArena, term: TermId, out: &mut BTreeSet<TermId>) {
    if let Some((_array, index)) = match_select(arena, term) {
        out.insert(index);
    }
}

fn normalize_select_over_writes_direct(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    mut array: TermId,
    index: TermId,
) -> RowNorm {
    let mut changed = false;
    while let Some((base, write_idx, value)) = match_store(arena, array) {
        if terms_directly_equal(arena, facts, index, write_idx) {
            return RowNorm {
                expr: RowExpr::Term(value),
                changed: true,
            };
        }
        if !terms_directly_distinct_in_context(arena, facts, distinct, index, write_idx) {
            break;
        }
        array = base;
        changed = true;
    }
    RowNorm {
        expr: RowExpr::Select { array, index },
        changed,
    }
}

fn row_expr_directly_matches_term(
    arena: &TermArena,
    facts: &EqFacts,
    expr: RowExpr,
    term: TermId,
) -> bool {
    match expr {
        RowExpr::Term(expr_term) => terms_directly_equal(arena, facts, expr_term, term),
        RowExpr::Select { array, index } => {
            match_select(arena, term).is_some_and(|(term_array, term_index)| {
                terms_directly_equal(arena, facts, array, term_array)
                    && terms_directly_equal(arena, facts, index, term_index)
            })
        }
    }
}

fn terms_directly_distinct_in_context(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    lhs: TermId,
    rhs: TermId,
) -> bool {
    indices_definitely_distinct(arena, lhs, rhs)
        || distinct.iter().any(|&(a, b)| {
            (terms_directly_equal(arena, facts, lhs, a)
                && terms_directly_equal(arena, facts, rhs, b))
                || (terms_directly_equal(arena, facts, lhs, b)
                    && terms_directly_equal(arena, facts, rhs, a))
        })
}

fn terms_directly_equal(arena: &TermArena, facts: &EqFacts, lhs: TermId, rhs: TermId) -> bool {
    lhs == rhs
        || facts.same(lhs, rhs)
        || matches!(
            (const_bv_value(arena, lhs), const_bv_value(arena, rhs)),
            (Some((lhs_width, lhs_value)), Some((rhs_width, rhs_value)))
                if lhs_width == rhs_width && lhs_value == rhs_value
        )
        || matches!(
            (arena.node(lhs), arena.node(rhs)),
            (TermNode::BoolConst(lhs_value), TermNode::BoolConst(rhs_value))
                if lhs_value == rhs_value
        )
}

fn store_self_update_read_equivalent(
    arena: &TermArena,
    facts: &EqFacts,
    lhs: TermId,
    rhs: TermId,
) -> bool {
    store_self_update_read_equivalent_one(arena, facts, lhs, rhs)
        || store_self_update_read_equivalent_one(arena, facts, rhs, lhs)
}

fn store_self_update_read_equivalent_one(
    arena: &TermArena,
    facts: &EqFacts,
    select_term: TermId,
    value_term: TermId,
) -> bool {
    let Some((array, index)) = match_select(arena, select_term) else {
        return false;
    };
    facts
        .store_self_reads
        .iter()
        .any(|&(base, write_index, value)| {
            facts.same(array, base)
                && (facts.same(index, write_index)
                    || indices_definitely_equal(arena, index, write_index))
                && facts.same(value_term, value)
        })
}

fn simplify_contextual_term(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    term: TermId,
    memo: &mut BTreeMap<(TermId, TermId), bool>,
) -> TermId {
    if let TermNode::App { op: Op::Ite, args } = arena.node(term) {
        if let [cond, then_term, else_term] = &**args {
            if let Some(value) = bool_condition_value(arena, facts, distinct, *cond, memo) {
                return facts.find(if value { *then_term } else { *else_term });
            }
        }
    }
    simplify_idempotent_bitop(arena, facts, distinct, term, memo)
}

fn bool_condition_value(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    term: TermId,
    memo: &mut BTreeMap<(TermId, TermId), bool>,
) -> Option<bool> {
    match arena.node(term) {
        TermNode::BoolConst(value) => Some(*value),
        TermNode::App {
            op: Op::BoolNot,
            args,
        } if args.len() == 1 => {
            bool_condition_value(arena, facts, distinct, args[0], memo).map(|value| !value)
        }
        TermNode::App { op: Op::Eq, args } if args.len() == 2 => {
            if let (Some(lhs_value), Some(rhs_value)) = (
                known_bv1_value_in_context(arena, facts, distinct, args[0], memo),
                known_bv1_value_in_context(arena, facts, distinct, args[1], memo),
            ) {
                return Some(lhs_value == rhs_value);
            }
            if terms_equivalent_inner(arena, facts, distinct, args[0], args[1], memo) {
                Some(true)
            } else if terms_definitely_distinct_in_context(
                arena, facts, distinct, args[0], args[1], memo,
            ) {
                Some(false)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn simplify_idempotent_bitop(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    term: TermId,
    memo: &mut BTreeMap<(TermId, TermId), bool>,
) -> TermId {
    let TermNode::App { op, args } = arena.node(term) else {
        return facts.find(term);
    };
    if !matches!(op, Op::BvAnd | Op::BvOr) || args.len() != 2 {
        return facts.find(term);
    }
    if terms_equivalent_inner(arena, facts, distinct, args[0], args[1], memo) {
        facts.find(args[0])
    } else {
        facts.find(term)
    }
}

fn normalize_read_over_writes_in_context(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    term: TermId,
    memo: &mut BTreeMap<(TermId, TermId), bool>,
) -> RowNorm {
    let Some((mut array, index)) = match_select(arena, term) else {
        return RowNorm {
            expr: RowExpr::Term(term),
            changed: false,
        };
    };
    let mut changed = false;
    loop {
        if let Some((cond, then_array, else_array)) = match_ite(arena, array) {
            if let Some(cond_value) = bool_condition_value(arena, facts, distinct, cond, memo) {
                array = if cond_value { then_array } else { else_array };
                changed = true;
                continue;
            }
        }
        let Some((base, write_idx, value)) = match_store(arena, array) else {
            break;
        };
        if terms_equivalent_inner(arena, facts, distinct, index, write_idx, memo) {
            return RowNorm {
                expr: RowExpr::Term(value),
                changed: true,
            };
        }
        if !terms_definitely_distinct_in_context(arena, facts, distinct, index, write_idx, memo) {
            break;
        }
        array = base;
        changed = true;
    }
    RowNorm {
        expr: RowExpr::Select { array, index },
        changed,
    }
}

fn row_expr_equivalent(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    lhs: RowExpr,
    rhs: RowExpr,
    memo: &mut BTreeMap<(TermId, TermId), bool>,
) -> bool {
    match (lhs, rhs) {
        (RowExpr::Term(lhs), RowExpr::Term(rhs)) => {
            terms_equivalent_inner(arena, facts, distinct, lhs, rhs, memo)
        }
        (
            RowExpr::Select {
                array: lhs_array,
                index: lhs_index,
            },
            RowExpr::Select {
                array: rhs_array,
                index: rhs_index,
            },
        ) => {
            terms_equivalent_inner(arena, facts, distinct, lhs_array, rhs_array, memo)
                && terms_equivalent_inner(arena, facts, distinct, lhs_index, rhs_index, memo)
        }
        (RowExpr::Term(term), RowExpr::Select { array, index })
        | (RowExpr::Select { array, index }, RowExpr::Term(term)) => {
            let Some((term_array, term_index)) = match_select(arena, term) else {
                return false;
            };
            terms_equivalent_inner(arena, facts, distinct, term_array, array, memo)
                && terms_equivalent_inner(arena, facts, distinct, term_index, index, memo)
        }
    }
}

fn terms_definitely_distinct_in_context(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    lhs: TermId,
    rhs: TermId,
    memo: &mut BTreeMap<(TermId, TermId), bool>,
) -> bool {
    if indices_definitely_distinct(arena, lhs, rhs) {
        return true;
    }
    if bv1_negation_pair_in_context(arena, facts, distinct, lhs, rhs, memo)
        || bv1_negation_pair_in_context(arena, facts, distinct, rhs, lhs, memo)
    {
        return true;
    }
    if let (Some(lhs_value), Some(rhs_value)) = (
        known_bv1_value_in_context(arena, facts, distinct, lhs, memo),
        known_bv1_value_in_context(arena, facts, distinct, rhs, memo),
    ) {
        if lhs_value != rhs_value {
            return true;
        }
    }
    distinct.iter().any(|&(a, b)| {
        let mut lhs_a_memo = BTreeMap::new();
        let mut rhs_b_memo = BTreeMap::new();
        let direct = terms_equivalent_inner(arena, facts, &[], lhs, a, &mut lhs_a_memo)
            && terms_equivalent_inner(arena, facts, &[], rhs, b, &mut rhs_b_memo);
        if direct {
            return true;
        }
        let mut lhs_b_memo = BTreeMap::new();
        let mut rhs_a_memo = BTreeMap::new();
        terms_equivalent_inner(arena, facts, &[], lhs, b, &mut lhs_b_memo)
            && terms_equivalent_inner(arena, facts, &[], rhs, a, &mut rhs_a_memo)
    })
}

fn finite_array_extensional_bit_equivalence(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    lhs: TermId,
    rhs: TermId,
    memo: &mut BTreeMap<(TermId, TermId), bool>,
) -> bool {
    finite_array_extensional_bit_equivalence_direct(arena, facts, distinct, lhs, rhs, memo)
        || finite_array_extensional_bit_equivalence_direct(arena, facts, distinct, rhs, lhs, memo)
}

fn finite_array_known_read_equivalence(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    lhs_array: TermId,
    rhs_array: TermId,
    memo: &mut BTreeMap<(TermId, TermId), bool>,
) -> bool {
    let Sort::Array {
        index: ArraySortKey::BitVec(index_width),
        element: ArraySortKey::BitVec(1),
    } = arena.sort_of(lhs_array)
    else {
        return false;
    };
    if arena.sort_of(rhs_array) != arena.sort_of(lhs_array) {
        return false;
    }
    let Some(domain_size) = finite_bv_domain_size(index_width) else {
        return false;
    };

    let lhs_reads = known_bv1_select_values(arena, facts, lhs_array);
    let rhs_reads = known_bv1_select_values(arena, facts, rhs_array);
    if lhs_reads.is_empty() || rhs_reads.is_empty() {
        return false;
    }

    let mut covered_reads = Vec::new();
    for lhs in &lhs_reads {
        if rhs_reads.iter().any(|rhs| {
            lhs.value == rhs.value
                && terms_equivalent_inner(arena, facts, distinct, lhs.index, rhs.index, memo)
        }) {
            covered_reads.push(ExtensionalReadBit {
                index: lhs.index,
                const_index: const_bv_value(arena, lhs.index).map(|(_width, value)| value),
            });
        }
    }
    extensional_reads_cover_domain(arena, facts, distinct, &covered_reads, domain_size, memo)
}

fn finite_array_read_fact_equivalence(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    lhs_array: TermId,
    rhs_array: TermId,
    memo: &mut BTreeMap<(TermId, TermId), bool>,
) -> bool {
    let Sort::Array {
        index: ArraySortKey::BitVec(index_width),
        ..
    } = arena.sort_of(lhs_array)
    else {
        return false;
    };
    if arena.sort_of(rhs_array) != arena.sort_of(lhs_array) {
        return false;
    }
    let Some(domain_size) = finite_bv_domain_size(index_width) else {
        return false;
    };

    let lhs_reads = select_terms_for_array(arena, facts, lhs_array);
    let rhs_reads = select_terms_for_array(arena, facts, rhs_array);
    if lhs_reads.is_empty() || rhs_reads.is_empty() {
        return false;
    }

    let mut covered_reads = Vec::new();
    for lhs in &lhs_reads {
        if rhs_reads.iter().any(|rhs| {
            facts.same(lhs.term, rhs.term)
                && terms_equivalent_inner(arena, facts, distinct, lhs.index, rhs.index, memo)
        }) {
            covered_reads.push(ExtensionalReadBit {
                index: lhs.index,
                const_index: const_bv_value(arena, lhs.index).map(|(_width, value)| value),
            });
        }
    }
    extensional_reads_cover_domain(arena, facts, distinct, &covered_reads, domain_size, memo)
}

#[derive(Debug, Clone, Copy)]
struct SelectRead {
    term: TermId,
    index: TermId,
}

fn select_terms_for_array(
    arena: &TermArena,
    facts: &EqFacts,
    expected_array: TermId,
) -> Vec<SelectRead> {
    facts
        .parent
        .keys()
        .copied()
        .filter_map(|term| {
            let (array, index) = match_select(arena, term)?;
            array_terms_match(facts, array, expected_array).then_some(SelectRead { term, index })
        })
        .collect()
}

#[derive(Debug, Clone, Copy)]
struct KnownBv1Read {
    index: TermId,
    value: bool,
}

fn known_bv1_select_values(
    arena: &TermArena,
    facts: &EqFacts,
    expected_array: TermId,
) -> Vec<KnownBv1Read> {
    facts
        .bv1_values
        .iter()
        .filter_map(|(&term, &value)| {
            let (array, index) = match_select(arena, term)?;
            array_terms_match(facts, array, expected_array).then_some(KnownBv1Read { index, value })
        })
        .collect()
}

fn finite_array_extensional_bit_equivalence_direct(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    reads_bit: TermId,
    array_eq_bit: TermId,
    memo: &mut BTreeMap<(TermId, TermId), bool>,
) -> bool {
    let Some((lhs_array, rhs_array, index_width)) = match_array_eq_bit(arena, array_eq_bit) else {
        return false;
    };
    let Some(domain_size) = finite_bv_domain_size(index_width) else {
        return false;
    };
    let mut leaves = Vec::new();
    collect_bv1_and_terms(arena, reads_bit, &mut leaves);
    if leaves.is_empty() {
        return false;
    }

    let mut reads = Vec::with_capacity(leaves.len());
    for leaf in leaves {
        let Some(read) =
            match_extensional_read_eq_bit(arena, facts, distinct, leaf, lhs_array, rhs_array, memo)
        else {
            return false;
        };
        reads.push(read);
    }
    extensional_reads_cover_domain(arena, facts, distinct, &reads, domain_size, memo)
}

#[derive(Debug, Clone, Copy)]
struct ExtensionalReadBit {
    index: TermId,
    const_index: Option<u128>,
}

fn match_array_eq_bit(arena: &TermArena, bit: TermId) -> Option<(TermId, TermId, u32)> {
    let literal = match_bit_literal(arena, bit)?;
    if !literal.equal_when_true || arena.sort_of(literal.lhs) != arena.sort_of(literal.rhs) {
        return None;
    }
    let Sort::Array {
        index: ArraySortKey::BitVec(index_width),
        ..
    } = arena.sort_of(literal.lhs)
    else {
        return None;
    };
    finite_bv_domain_size(index_width)?;
    Some((literal.lhs, literal.rhs, index_width))
}

fn finite_bv_domain_size(index_width: u32) -> Option<u128> {
    let domain_size = 1_u128.checked_shl(index_width)?;
    (domain_size <= crate::array_finite::MAX_FINITE_ARRAY_EXT_READS).then_some(domain_size)
}

fn match_extensional_read_eq_bit(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    bit: TermId,
    lhs_array: TermId,
    rhs_array: TermId,
    memo: &mut BTreeMap<(TermId, TermId), bool>,
) -> Option<ExtensionalReadBit> {
    let literal = match_bit_literal(arena, bit)?;
    if !literal.equal_when_true {
        return None;
    }
    let (literal_lhs_array, literal_lhs_index) = match_select(arena, literal.lhs)?;
    let (literal_rhs_array, literal_rhs_index) = match_select(arena, literal.rhs)?;
    if arena.sort_of(literal_lhs_array) != arena.sort_of(literal_rhs_array)
        || arena.sort_of(literal.lhs) != arena.sort_of(literal.rhs)
    {
        return None;
    }

    let direct = array_terms_match(facts, literal_lhs_array, lhs_array)
        && array_terms_match(facts, literal_rhs_array, rhs_array);
    let swapped = array_terms_match(facts, literal_lhs_array, rhs_array)
        && array_terms_match(facts, literal_rhs_array, lhs_array);
    if !direct && !swapped {
        return None;
    }
    if !terms_equivalent_inner(
        arena,
        facts,
        distinct,
        literal_lhs_index,
        literal_rhs_index,
        memo,
    ) {
        return None;
    }
    let const_index = match const_bv_value(arena, literal_lhs_index) {
        Some((_, value)) => Some(value),
        None => const_bv_value(arena, literal_rhs_index).map(|(_, value)| value),
    };
    Some(ExtensionalReadBit {
        index: literal_lhs_index,
        const_index,
    })
}

fn array_terms_match(facts: &EqFacts, actual: TermId, expected: TermId) -> bool {
    actual == expected || facts.same(actual, expected)
}

fn extensional_reads_cover_domain(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    reads: &[ExtensionalReadBit],
    domain_size: u128,
    memo: &mut BTreeMap<(TermId, TermId), bool>,
) -> bool {
    let concrete: BTreeSet<_> = reads
        .iter()
        .filter_map(|read| read.const_index)
        .filter(|&value| value < domain_size)
        .collect();
    if concrete.len() == domain_size as usize {
        return true;
    }
    if domain_size == 2 {
        return reads.iter().enumerate().any(|(idx, lhs)| {
            reads[idx + 1..].iter().any(|rhs| {
                terms_definitely_distinct_in_context(
                    arena, facts, distinct, lhs.index, rhs.index, memo,
                )
            })
        });
    }
    false
}

fn is_read_over_write_same_index(arena: &TermArena, lhs: TermId, rhs: TermId) -> bool {
    let Some((stored, read_idx)) = match_select(arena, lhs) else {
        return false;
    };
    let Some((_array, write_idx, value)) = match_store(arena, stored) else {
        return false;
    };
    read_idx == write_idx && rhs == value
}

fn is_read_over_write(arena: &TermArena, lhs: TermId, rhs: TermId) -> bool {
    let Some((stored, read_idx)) = match_select(arena, lhs) else {
        return false;
    };
    let Some((array, write_idx, value)) = match_store(arena, stored) else {
        return false;
    };
    let Some((cond, then_term, else_term)) = match_ite(arena, rhs) else {
        return false;
    };
    then_term == value
        && is_eq_over(arena, cond, write_idx, read_idx)
        && match_select(arena, else_term).is_some_and(|(a, i)| a == array && i == read_idx)
}

fn is_select_ite(arena: &TermArena, lhs: TermId, rhs: TermId) -> bool {
    let Some((ite_array, index)) = match_select(arena, lhs) else {
        return false;
    };
    let Some((cond, then_array, else_array)) = match_ite(arena, ite_array) else {
        return false;
    };
    let Some((rhs_cond, then_read, else_read)) = match_ite(arena, rhs) else {
        return false;
    };
    cond == rhs_cond
        && match_select(arena, then_read).is_some_and(|(a, i)| a == then_array && i == index)
        && match_select(arena, else_read).is_some_and(|(a, i)| a == else_array && i == index)
}

fn is_store_ite_select(arena: &TermArena, lhs: TermId, rhs: TermId) -> bool {
    let Some((lhs_array, read_idx)) = match_select(arena, lhs) else {
        return false;
    };
    let Some((cond, then_store, else_store)) = match_ite(arena, lhs_array) else {
        return false;
    };
    let Some((then_array, write_idx, value)) = match_store(arena, then_store) else {
        return false;
    };
    let Some((else_array, else_write_idx, else_value)) = match_store(arena, else_store) else {
        return false;
    };
    if else_write_idx != write_idx || else_value != value {
        return false;
    }

    let Some((rhs_store, rhs_read_idx)) = match_select(arena, rhs) else {
        return false;
    };
    if rhs_read_idx != read_idx {
        return false;
    }
    let Some((rhs_array, rhs_write_idx, rhs_value)) = match_store(arena, rhs_store) else {
        return false;
    };
    if rhs_write_idx != write_idx || rhs_value != value {
        return false;
    }
    match_ite(arena, rhs_array)
        .is_some_and(|(c, a, b)| c == cond && a == then_array && b == else_array)
}

fn match_select(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let TermNode::App {
        op: Op::Select,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [array, index] = &**args else {
        return None;
    };
    Some((*array, *index))
}

fn match_store(arena: &TermArena, term: TermId) -> Option<(TermId, TermId, TermId)> {
    let TermNode::App {
        op: Op::Store,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [array, index, value] = &**args else {
        return None;
    };
    Some((*array, *index, *value))
}

fn match_ite(arena: &TermArena, term: TermId) -> Option<(TermId, TermId, TermId)> {
    let TermNode::App { op: Op::Ite, args } = arena.node(term) else {
        return None;
    };
    let [cond, then_term, else_term] = &**args else {
        return None;
    };
    Some((*cond, *then_term, *else_term))
}

fn is_eq_over(arena: &TermArena, term: TermId, lhs: TermId, rhs: TermId) -> bool {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return false;
    };
    let [a, b] = &**args else {
        return false;
    };
    (*a == lhs && *b == rhs) || (*a == rhs && *b == lhs)
}

fn match_bv1_asserted_true(arena: &TermArena, term: TermId) -> Option<TermId> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    if is_bv_const(arena, *lhs, 1, 1) && arena.sort_of(*rhs) == Sort::BitVec(1) {
        Some(*rhs)
    } else if is_bv_const(arena, *rhs, 1, 1) && arena.sort_of(*lhs) == Sort::BitVec(1) {
        Some(*lhs)
    } else {
        None
    }
}

fn match_bv1_literal_bit(arena: &TermArena, term: TermId) -> Option<(TermId, TermId, bool)> {
    let (cond, then_term, else_term) = match_ite(arena, term)?;
    let bit_true_means_cond =
        if is_bv_const(arena, then_term, 1, 1) && is_bv_const(arena, else_term, 1, 0) {
            true
        } else if is_bv_const(arena, then_term, 1, 0) && is_bv_const(arena, else_term, 1, 1) {
            false
        } else {
            return None;
        };
    let (lhs, rhs, cond_true_means_equal) = match_eq_condition(arena, cond)?;
    let equal_when_true = if bit_true_means_cond {
        cond_true_means_equal
    } else {
        !cond_true_means_equal
    };
    Some((lhs, rhs, equal_when_true))
}

fn match_bv1_ult_bit(arena: &TermArena, term: TermId) -> Option<(TermId, TermId, bool)> {
    let (cond, then_term, else_term) = match_ite(arena, term)?;
    let bit_true_means_cond =
        if is_bv_const(arena, then_term, 1, 1) && is_bv_const(arena, else_term, 1, 0) {
            true
        } else if is_bv_const(arena, then_term, 1, 0) && is_bv_const(arena, else_term, 1, 1) {
            false
        } else {
            return None;
        };
    let TermNode::App {
        op: Op::BvUlt,
        args,
    } = arena.node(cond)
    else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    if arena.sort_of(*lhs) == Sort::BitVec(1) && arena.sort_of(*rhs) == Sort::BitVec(1) {
        Some((*lhs, *rhs, bit_true_means_cond))
    } else {
        None
    }
}

fn match_eq(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    Some((*lhs, *rhs))
}

fn match_eq_condition(arena: &TermArena, term: TermId) -> Option<(TermId, TermId, bool)> {
    if let Some((lhs, rhs)) = match_eq(arena, term) {
        return Some((lhs, rhs, true));
    }
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
    let (lhs, rhs) = match_eq(arena, *inner)?;
    Some((lhs, rhs, false))
}

fn known_bv1_value_in_context(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    term: TermId,
    memo: &mut BTreeMap<(TermId, TermId), bool>,
) -> Option<bool> {
    if arena.sort_of(term) != Sort::BitVec(1) {
        return None;
    }
    match arena.node(term) {
        TermNode::BvConst { width, value } if *width == 1 => {
            return Some(*value != 0);
        }
        TermNode::App {
            op: Op::BvNot,
            args,
        } if args.len() == 1 => {
            return known_bv1_value_in_context(arena, facts, distinct, args[0], memo)
                .map(|value| !value);
        }
        TermNode::App {
            op: Op::BvAnd,
            args,
        } if args.len() == 2 => {
            if bv1_bitop_has_negation_pair_in_context(arena, facts, distinct, term, Op::BvAnd, memo)
            {
                return Some(false);
            }
            let lhs = known_bv1_value_in_context(arena, facts, distinct, args[0], memo);
            let rhs = known_bv1_value_in_context(arena, facts, distinct, args[1], memo);
            if lhs == Some(false)
                || rhs == Some(false)
                || terms_definitely_distinct_in_context(
                    arena, facts, distinct, args[0], args[1], memo,
                )
            {
                return Some(false);
            }
            if lhs == Some(true) && rhs == Some(true) {
                return Some(true);
            }
        }
        TermNode::App { op: Op::BvOr, args } if args.len() == 2 => {
            if bv1_bitop_has_negation_pair_in_context(arena, facts, distinct, term, Op::BvOr, memo)
            {
                return Some(true);
            }
            let lhs = known_bv1_value_in_context(arena, facts, distinct, args[0], memo);
            let rhs = known_bv1_value_in_context(arena, facts, distinct, args[1], memo);
            if lhs == Some(true)
                || rhs == Some(true)
                || terms_definitely_distinct_in_context(
                    arena, facts, distinct, args[0], args[1], memo,
                )
            {
                return Some(true);
            }
            if lhs == Some(false) && rhs == Some(false) {
                return Some(false);
            }
        }
        TermNode::App { op: Op::Ite, args } if args.len() == 3 => {
            if let Some(cond_value) = bool_condition_value(arena, facts, distinct, args[0], memo) {
                let branch = if cond_value { args[1] } else { args[2] };
                return known_bv1_value_in_context(arena, facts, distinct, branch, memo);
            }
        }
        _ => {}
    }

    if let Some(literal) = match_bit_literal(arena, term) {
        if terms_equivalent_inner(arena, facts, distinct, literal.lhs, literal.rhs, memo) {
            return Some(literal.equal_when_true);
        }
        if terms_definitely_distinct_in_context(
            arena,
            facts,
            distinct,
            literal.lhs,
            literal.rhs,
            memo,
        ) {
            return Some(!literal.equal_when_true);
        }
    }

    let row = normalize_read_over_writes_in_context(arena, facts, distinct, term, memo);
    if row.changed {
        if let RowExpr::Term(simplified) = row.expr {
            if simplified != term {
                return known_bv1_value_in_context(arena, facts, distinct, simplified, memo);
            }
        }
    }
    if let Some(value) = known_bv1_value(arena, facts, term) {
        return Some(value);
    }
    None
}

fn bv1_bitop_has_negation_pair_in_context(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    term: TermId,
    op: Op,
    memo: &mut BTreeMap<(TermId, TermId), bool>,
) -> bool {
    let mut leaves = Vec::new();
    collect_bv1_bitop_leaves(arena, term, op, &mut leaves);
    leaves.iter().enumerate().any(|(idx, &lhs)| {
        leaves[idx + 1..].iter().any(|&rhs| {
            bv1_negation_pair_in_context(arena, facts, distinct, lhs, rhs, memo)
                || bv1_negation_pair_in_context(arena, facts, distinct, rhs, lhs, memo)
        })
    })
}

fn collect_bv1_bitop_leaves(arena: &TermArena, term: TermId, op: Op, leaves: &mut Vec<TermId>) {
    if let TermNode::App { op: term_op, args } = arena.node(term) {
        if *term_op == op && args.len() == 2 {
            collect_bv1_bitop_leaves(arena, args[0], op, leaves);
            collect_bv1_bitop_leaves(arena, args[1], op, leaves);
            return;
        }
    }
    leaves.push(term);
}

fn bv1_negation_pair_in_context(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    lhs: TermId,
    rhs: TermId,
    memo: &mut BTreeMap<(TermId, TermId), bool>,
) -> bool {
    let TermNode::App {
        op: Op::BvNot,
        args,
    } = arena.node(lhs)
    else {
        return false;
    };
    let [inner] = &**args else {
        return false;
    };
    arena.sort_of(lhs) == Sort::BitVec(1)
        && terms_equivalent_inner(arena, facts, distinct, *inner, rhs, memo)
}

fn known_bv1_value(arena: &TermArena, facts: &EqFacts, term: TermId) -> Option<bool> {
    if arena.sort_of(term) != Sort::BitVec(1) {
        return None;
    }
    match arena.node(term) {
        TermNode::BvConst { width, value } if *width == 1 => return Some(*value != 0),
        TermNode::App {
            op: Op::BvNot,
            args,
        } if args.len() == 1 => return known_bv1_value(arena, facts, args[0]).map(|v| !v),
        _ => {}
    }
    let root = facts.find(term);
    facts
        .bv1_values
        .iter()
        .find_map(|(&known_term, &value)| (facts.find(known_term) == root).then_some(value))
}

fn find_bv1_const_term(arena: &TermArena, term: TermId, value: bool) -> Option<TermId> {
    match arena.node(term) {
        TermNode::BvConst {
            width: 1,
            value: term_value,
        } if (*term_value != 0) == value => Some(term),
        TermNode::App { args, .. } => args
            .iter()
            .find_map(|&arg| find_bv1_const_term(arena, arg, value)),
        _ => None,
    }
}

fn is_bv_const(arena: &TermArena, term: TermId, expected_width: u32, expected_value: u128) -> bool {
    matches!(
        arena.node(term),
        TermNode::BvConst { width, value }
            if *width == expected_width && *value == expected_value
    )
}

fn is_bv_zero(arena: &TermArena, term: TermId) -> bool {
    const_bv_value(arena, term).is_some_and(|(_width, value)| value == 0)
}

#[cfg(test)]
mod tests {
    use axeyum_ir::TermArena;
    use axeyum_smtlib::parse_script;

    use super::*;

    #[test]
    fn recognizes_mccarthy_read_over_write() {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 4, 8).unwrap();
        let i = arena.bv_var("i", 4).unwrap();
        let j = arena.bv_var("j", 4).unwrap();
        let v = arena.bv_var("v", 8).unwrap();
        let stored = arena.store(a, i, v).unwrap();
        let lhs = arena.select(stored, j).unwrap();
        let cond = arena.eq(i, j).unwrap();
        let fallback = arena.select(a, j).unwrap();
        let rhs = arena.ite(cond, v, fallback).unwrap();
        let diseq = {
            let eq = arena.eq(lhs, rhs).unwrap();
            arena.not(eq).unwrap()
        };

        let cert = array_axiom_refutation(&arena, &[diseq]).expect("McCarthy axiom refutes");
        assert_eq!(cert.kind, ArrayAxiomKind::ReadOverWrite);
    }

    #[test]
    fn recognizes_bv1_encoded_read_over_write_same_index() {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 1, 1).unwrap();
        let i = arena.bv_var("i", 1).unwrap();
        let v = arena.bv_var("v", 1).unwrap();
        let one = arena.bv_const(1, 1).unwrap();
        let zero = arena.bv_const(1, 0).unwrap();
        let stored = arena.store(a, i, v).unwrap();
        let read = arena.select(stored, i).unwrap();
        let eq = arena.eq(v, read).unwrap();
        let eq_bit = arena.ite(eq, one, zero).unwrap();
        let diseq_bit = arena.bv_not(eq_bit).unwrap();
        let assertion = arena.eq(one, diseq_bit).unwrap();

        let cert = array_axiom_refutation(&arena, &[assertion])
            .expect("BV1-encoded same-index read-over-write refutes");
        assert_eq!(cert.kind, ArrayAxiomKind::ReadOverWrite);
    }

    #[test]
    fn recognizes_bv1_encoded_constant_distinct_store_chain_read() {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 8, 8).unwrap();
        let v0 = arena.bv_var("v0", 8).unwrap();
        let v1 = arena.bv_var("v1", 8).unwrap();
        let read_idx = arena.bv_const(8, 0x7b).unwrap();
        let write_idx0 = arena.bv_const(8, 0x05).unwrap();
        let write_idx1 = arena.bv_const(8, 0x1b).unwrap();
        let one = arena.bv_const(1, 1).unwrap();
        let zero = arena.bv_const(1, 0).unwrap();
        let lhs = arena.select(a, read_idx).unwrap();
        let stored0 = arena.store(a, write_idx0, v0).unwrap();
        let stored1 = arena.store(stored0, write_idx1, v1).unwrap();
        let rhs = arena.select(stored1, read_idx).unwrap();
        let eq = arena.eq(lhs, rhs).unwrap();
        let eq_bit = arena.ite(eq, one, zero).unwrap();
        let diseq_bit = arena.bv_not(eq_bit).unwrap();
        let assertion = arena.eq(one, diseq_bit).unwrap();

        let cert = array_axiom_refutation(&arena, &[assertion])
            .expect("constant-distinct read-over-write chain refutes");
        assert_eq!(cert.kind, ArrayAxiomKind::ReadOverWrite);
    }

    #[test]
    fn recognizes_btor_read_congruence_regressions() {
        let cases = [
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read1.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read4.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read10.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read22.btor.smt2"
            ),
        ];

        for text in cases {
            let script = parse_script(text).expect("ABV read-congruence case parses");
            let cert = array_axiom_refutation(&script.arena, &script.assertions)
                .expect("read congruence refutes");
            assert_eq!(cert.kind, ArrayAxiomKind::ReadCongruence);
        }
    }

    #[test]
    fn recognizes_btor_conditional_select_regressions() {
        let cases = [
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw30.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw31.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw32.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw33.btor.smt2"
            ),
        ];

        for text in cases {
            let script = parse_script(text).expect("ABV conditional-select case parses");
            let cert = array_axiom_refutation(&script.arena, &script.assertions)
                .expect("conditional select congruence refutes");
            assert_eq!(cert.kind, ArrayAxiomKind::ReadCongruence);
        }
    }

    #[test]
    fn recognizes_btor_contextual_false_bv1_regressions() {
        let cases = [
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write14.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycondconst.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycondconstaig.btor.smt2"
            ),
        ];

        for text in cases {
            let script = parse_script(text).expect("ABV contextual-false BV1 case parses");
            let cert = array_axiom_refutation(&script.arena, &script.assertions)
                .expect("contextual BV1 false refutes");
            assert_eq!(cert.kind, ArrayAxiomKind::ReadCongruence);
        }
    }

    #[test]
    fn recognizes_btor_finite_extensionality_bit_regressions() {
        let cases = [
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext5.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext21.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext23.btor.smt2"
            ),
        ];

        for text in cases {
            let script = parse_script(text).expect("ABV finite-extensionality bit case parses");
            let cert = array_axiom_refutation(&script.arena, &script.assertions)
                .expect("finite-extensionality bit refutes");
            assert_eq!(cert.kind, ArrayAxiomKind::ReadCongruence);
        }
    }

    #[test]
    fn recognizes_btor_bv1_order_extensionality_regressions() {
        let cases = [
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext16.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext26.btor.smt2"
            ),
        ];

        for text in cases {
            let script = parse_script(text).expect("ABV BV1-order extensionality case parses");
            let cert = array_axiom_refutation(&script.arena, &script.assertions)
                .expect("BV1-order extensionality case refutes");
            assert_eq!(cert.kind, ArrayAxiomKind::ReadCongruence);
        }
    }

    #[test]
    fn recognizes_btor_guarded_write_regressions() {
        let cases = [
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write2.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write4.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write7.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write8.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write9.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write10.btor.smt2"
            ),
        ];

        for text in cases {
            let script = parse_script(text).expect("ABV guarded-write case parses");
            let cert = array_axiom_refutation(&script.arena, &script.assertions)
                .expect("guarded write/read-over-write case refutes");
            assert_eq!(cert.kind, ArrayAxiomKind::ReadCongruence);
        }
    }

    #[test]
    fn recognizes_btor_nonzero_offset_row_regressions() {
        let cases = [
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rwpropindexplusconst1.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rwpropindexplusconst2.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rwpropindexplusconst3.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rwpropindexplusconst4.btor.smt2"
            ),
        ];

        for text in cases {
            let script = parse_script(text).expect("ABV nonzero-offset ROW case parses");
            let cert = array_axiom_refutation(&script.arena, &script.assertions)
                .expect("nonzero-offset read-over-write case refutes");
            assert_eq!(cert.kind, ArrayAxiomKind::ReadOverWrite);
        }
    }

    #[test]
    fn recognizes_btor_concat_suffix_row_regression() {
        let script = parse_script(include_str!(
            "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__3vl1.btor.smt2"
        ))
        .expect("ABV concat-suffix ROW case parses");
        let cert = array_axiom_refutation(&script.arena, &script.assertions)
            .expect("concat-suffix read-over-write case refutes");
        assert_eq!(cert.kind, ArrayAxiomKind::ReadOverWrite);
    }

    #[test]
    fn recognizes_btor_store_same_cell_injectivity_regression() {
        let script = parse_script(include_str!(
            "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__extarraywrite1.btor.smt2"
        ))
        .expect("ABV store same-cell injectivity case parses");
        let cert = array_axiom_refutation(&script.arena, &script.assertions)
            .expect("store same-cell injectivity case refutes");
        assert_eq!(cert.kind, ArrayAxiomKind::ReadCongruence);
    }

    #[test]
    fn recognizes_btor_store_self_update_read_regression() {
        let script = parse_script(include_str!(
            "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext22.btor.smt2"
        ))
        .expect("ABV store self-update read case parses");
        let cert = array_axiom_refutation(&script.arena, &script.assertions)
            .expect("store self-update read case refutes");
        assert_eq!(cert.kind, ArrayAxiomKind::ReadCongruence);
    }

    #[test]
    fn recognizes_btor_equal_store_chain_readback_regressions() {
        let cases = [
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext27.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext28.btor.smt2"
            ),
        ];

        for text in cases {
            let script = parse_script(text).expect("ABV equal-store readback case parses");
            let cert = array_axiom_refutation(&script.arena, &script.assertions)
                .expect("equal-store readback case refutes");
            assert_eq!(cert.kind, ArrayAxiomKind::ReadCongruence);
        }
    }

    #[test]
    fn does_not_refute_zero_offset_row_regression() {
        let script = parse_script(include_str!(
            "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rwpropindexpluszero1.btor.smt2"
        ))
        .expect("ABV zero-offset ROW case parses");
        assert!(
            array_axiom_refutation(&script.arena, &script.assertions).is_none(),
            "zero-offset ROW propagation row is satisfiable and must not refute"
        );
    }

    #[test]
    fn recognizes_btor_store_shadowing_regressions() {
        let cases = [
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write22.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write23.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write24.btor.smt2"
            ),
        ];

        for text in cases {
            let script = parse_script(text).expect("ABV store-shadowing case parses");
            let cert = array_axiom_refutation(&script.arena, &script.assertions)
                .expect("store-shadowing case refutes");
            assert_eq!(cert.kind, ArrayAxiomKind::StoreShadowing);
        }
    }

    #[test]
    fn recognizes_select_over_array_ite() {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 4, 8).unwrap();
        let b = arena.array_var("b", 4, 8).unwrap();
        let i = arena.bv_var("i", 4).unwrap();
        let c = arena.bool_var("c").unwrap();
        let ite_array = arena.ite(c, a, b).unwrap();
        let lhs = arena.select(ite_array, i).unwrap();
        let select_a = arena.select(a, i).unwrap();
        let select_b = arena.select(b, i).unwrap();
        let rhs = arena.ite(c, select_a, select_b).unwrap();
        let diseq = {
            let eq = arena.eq(rhs, lhs).unwrap();
            arena.not(eq).unwrap()
        };

        let cert = array_axiom_refutation(&arena, &[diseq]).expect("select-ite axiom refutes");
        assert_eq!(cert.kind, ArrayAxiomKind::SelectIte);
    }

    #[test]
    fn recognizes_store_over_ite_under_select() {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 4, 8).unwrap();
        let b = arena.array_var("b", 4, 8).unwrap();
        let i = arena.bv_var("i", 4).unwrap();
        let j = arena.bv_var("j", 4).unwrap();
        let v = arena.bv_var("v", 8).unwrap();
        let c = arena.bool_var("c").unwrap();
        let store_a = arena.store(a, i, v).unwrap();
        let store_b = arena.store(b, i, v).unwrap();
        let lhs_array = arena.ite(c, store_a, store_b).unwrap();
        let lhs = arena.select(lhs_array, j).unwrap();
        let ite_array = arena.ite(c, a, b).unwrap();
        let rhs_array = arena.store(ite_array, i, v).unwrap();
        let rhs = arena.select(rhs_array, j).unwrap();
        let diseq = {
            let eq = arena.eq(lhs, rhs).unwrap();
            arena.not(eq).unwrap()
        };

        let cert =
            array_axiom_refutation(&arena, &[diseq]).expect("store-ite-select axiom refutes");
        assert_eq!(cert.kind, ArrayAxiomKind::StoreIteSelect);
    }
}
