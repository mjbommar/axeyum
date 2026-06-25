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
        if let Some(witness) = conflicting_equalities(arena, &self.facts) {
            return Some(witness);
        }
        if let Some(witness) = conflicting_bv1_values(arena, &self.facts) {
            return Some(witness);
        }
        if let Some(witness) = conflicting_bool_negation_equalities(arena, &self.facts) {
            return Some(witness);
        }
        if let Some(witness) =
            conflicting_ite_branch_disequalities(arena, &self.facts, &self.disequalities)
        {
            return Some(witness);
        }
        if let Some(witness) =
            forced_select_store_ite_bv1_value_conflict(arena, &self.facts, &self.disequalities)
        {
            return Some(witness);
        }
        if let Some(witness) =
            bv1_array_ite_all_true_refutation(arena, &self.facts, &self.denied_and_terms)
        {
            return Some(witness);
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
        saturate_contextual_ite_equality_facts(arena, facts, disequalities);
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
        saturate_contextual_ite_equality_facts(arena, facts, disequalities);
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

fn saturate_contextual_ite_equality_facts(
    arena: &TermArena,
    facts: &mut EqFacts,
    disequalities: &[(TermId, TermId)],
) {
    loop {
        let mut known_terms = BTreeSet::new();
        known_terms.extend(facts.parent.keys().copied());
        known_terms.extend(facts.bv1_values.keys().copied());

        let mut additions = Vec::new();
        for term in known_terms {
            let Some((cond, then_term, else_term)) = match_ite(arena, term) else {
                continue;
            };
            let mut memo = BTreeMap::new();
            let Some(branch) = contextual_ite_branch(
                arena,
                facts,
                disequalities,
                cond,
                then_term,
                else_term,
                &mut memo,
            ) else {
                continue;
            };
            if !facts.same(term, branch) {
                additions.push((term, branch));
            }
        }

        if additions.is_empty() {
            break;
        }

        let mut changed = false;
        for (lhs, rhs) in additions {
            if facts.same(lhs, rhs) {
                continue;
            }
            facts.add(lhs, rhs);
            add_derived_equality_facts(arena, facts, lhs, rhs);
            changed = true;
        }
        if !changed {
            break;
        }
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

fn match_bool_not(arena: &TermArena, term: TermId) -> Option<TermId> {
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
    (arena.sort_of(term) == Sort::Bool).then_some(*inner)
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
                probe.facts.set_bv1(bit, true);
                saturate_contextual_ite_equality_facts(
                    arena,
                    &mut probe.facts,
                    &probe.disequalities,
                );
                collect_bit_assertion(arena, args[0], true, probe);
                collect_bit_assertion(arena, args[1], true, probe);
                return;
            }
            (Op::BvOr, false) if args.len() == 2 && arena.sort_of(bit) == Sort::BitVec(1) => {
                probe.facts.set_bv1(bit, false);
                saturate_contextual_ite_equality_facts(
                    arena,
                    &mut probe.facts,
                    &probe.disequalities,
                );
                collect_bit_assertion(arena, args[0], false, probe);
                collect_bit_assertion(arena, args[1], false, probe);
                return;
            }
            (Op::BvOr, true) if args.len() == 2 && arena.sort_of(bit) == Sort::BitVec(1) => {
                probe.facts.set_bv1(bit, true);
                saturate_contextual_ite_equality_facts(
                    arena,
                    &mut probe.facts,
                    &probe.disequalities,
                );
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
                probe.facts.set_bv1(bit, false);
                saturate_contextual_ite_equality_facts(
                    arena,
                    &mut probe.facts,
                    &probe.disequalities,
                );
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
        saturate_contextual_ite_equality_facts(arena, &mut probe.facts, &probe.disequalities);
    } else if arena.sort_of(bit) == Sort::BitVec(1) {
        probe.facts.set_bv1(bit, polarity);
        saturate_contextual_ite_equality_facts(arena, &mut probe.facts, &probe.disequalities);
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
    if is_store_restore_noop_chain(arena, lhs, rhs) {
        return true;
    }
    if is_same_value_store_chain_coverage(arena, lhs, rhs) {
        return true;
    }

    let lhs_norm = normalize_store_shadows(arena, lhs);
    let rhs_norm = normalize_store_shadows(arena, rhs);
    (lhs_norm.changed || rhs_norm.changed)
        && lhs_norm.base == rhs_norm.base
        && lhs_norm.writes == rhs_norm.writes
}

fn is_store_restore_noop_chain(arena: &TermArena, lhs: TermId, rhs: TermId) -> bool {
    let (base, writes) = collect_store_chain(arena, lhs);
    let [
        (first_index, _first_value),
        (noop_index, noop_value),
        (restore_index, restore_value),
    ] = writes.as_slice()
    else {
        return false;
    };

    base == rhs
        && indices_definitely_equal(arena, *first_index, *restore_index)
        && indices_definitely_distinct(arena, *first_index, *noop_index)
        && is_base_select_at(arena, *noop_value, base, *noop_index)
        && is_base_select_at(arena, *restore_value, base, *first_index)
}

fn is_base_select_at(arena: &TermArena, term: TermId, base: TermId, index: TermId) -> bool {
    match_select(arena, term).is_some_and(|(array, read_index)| {
        array == base && indices_definitely_equal(arena, read_index, index)
    })
}

fn is_same_value_store_chain_coverage(arena: &TermArena, lhs: TermId, rhs: TermId) -> bool {
    let (lhs_base, lhs_writes) = collect_store_chain(arena, lhs);
    let (rhs_base, rhs_writes) = collect_store_chain(arena, rhs);
    if lhs_base != rhs_base || lhs_writes.is_empty() || rhs_writes.is_empty() {
        return false;
    }

    let Some(first_value) = lhs_writes.first().map(|&(_index, value)| value) else {
        return false;
    };
    if lhs_writes
        .iter()
        .chain(rhs_writes.iter())
        .any(|&(_index, value)| !values_definitely_equal(arena, value, first_value))
    {
        return false;
    }

    let lhs_indices: Vec<_> = lhs_writes.iter().map(|&(index, _value)| index).collect();
    let rhs_indices: Vec<_> = rhs_writes.iter().map(|&(index, _value)| index).collect();
    store_indices_cover(arena, &lhs_indices, &rhs_indices)
        && store_indices_cover(arena, &rhs_indices, &lhs_indices)
}

fn store_indices_cover(arena: &TermArena, source: &[TermId], target: &[TermId]) -> bool {
    source
        .iter()
        .all(|&index| store_index_covered_by(arena, index, target))
}

fn store_index_covered_by(arena: &TermArena, index: TermId, target: &[TermId]) -> bool {
    if target
        .iter()
        .any(|&target_index| indices_definitely_equal(arena, index, target_index))
    {
        return true;
    }

    let Some(range) = bv_unsigned_range(arena, index) else {
        return false;
    };
    let Some(range_len) = range
        .max
        .checked_sub(range.min)
        .and_then(|span| span.checked_add(1))
    else {
        return false;
    };
    if range_len > crate::array_finite::MAX_FINITE_ARRAY_EXT_READS {
        return false;
    }

    (range.min..=range.max).all(|value| {
        target.iter().any(|&target_index| {
            matches!(
                const_bv_value(arena, target_index),
                Some((width, target_value)) if width == range.width && target_value == value
            )
        })
    })
}

fn values_definitely_equal(arena: &TermArena, lhs: TermId, rhs: TermId) -> bool {
    lhs == rhs
        || matches!(
            (const_bv_value(arena, lhs), const_bv_value(arena, rhs)),
            (Some((lhs_width, lhs_value)), Some((rhs_width, rhs_value)))
                if lhs_width == rhs_width && lhs_value == rhs_value
        )
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
                if let Some(witness) = prove_bv1_disjunction_true_by_implication(arena, facts, term)
                {
                    return Some(witness);
                }
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

fn prove_bv1_disjunction_true_by_implication(
    arena: &TermArena,
    facts: &EqFacts,
    term: TermId,
) -> Option<(TermId, TermId)> {
    let mut terms = Vec::new();
    collect_bv1_or_terms(arena, term, &mut terms);
    if terms.len() < 2 {
        return None;
    }

    for (guard_idx, &guard) in terms.iter().enumerate() {
        let Some(antecedent) = match_bv_not(arena, guard) else {
            continue;
        };
        let mut branch_probe = ReadCongruenceProbe {
            facts: facts.clone(),
            ..ReadCongruenceProbe::default()
        };
        collect_bit_assertion(arena, antecedent, true, &mut branch_probe);

        for (consequent_idx, &consequent) in terms.iter().enumerate() {
            if consequent_idx == guard_idx {
                continue;
            }
            if let Some(witness) = prove_bit_term(arena, &branch_probe.facts, consequent, true) {
                return Some(witness);
            }
        }
    }
    None
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
    memo.insert(key, false);

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

    if equal_array_readback_equivalent(arena, facts, distinct, lhs, rhs, memo) {
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
    let known_singleton_bv_range_equal = bv_unsigned_ranges_same_singleton(arena, lhs, rhs);

    let finite_array_extensional_equal =
        finite_array_extensional_bit_equivalence(arena, facts, distinct, lhs, rhs, memo);
    let finite_array_known_reads_equal =
        finite_array_known_read_equivalence(arena, facts, distinct, lhs, rhs, memo);
    let finite_array_read_facts_equal =
        finite_array_read_fact_equivalence(arena, facts, distinct, lhs, rhs, memo);
    let finite_array_row_equal =
        finite_array_row_equivalence(arena, facts, distinct, lhs, rhs, memo);
    let finite_array_bv1_order_profile_equal =
        finite_array_bv1_order_profile_equivalence(arena, facts, distinct, lhs, rhs);
    let bv1_order_equal =
        bv1_terms_equal_by_equal_order_bits(arena, facts, distinct, lhs, rhs, memo);

    let result = facts.same(lhs, rhs)
        || known_bv1_equal
        || known_const_bv_equal
        || known_singleton_bv_range_equal
        || finite_array_extensional_equal
        || finite_array_known_reads_equal
        || finite_array_read_facts_equal
        || finite_array_row_equal
        || finite_array_bv1_order_profile_equal
        || bv1_order_equal
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
    memo: &mut BTreeMap<(TermId, TermId), bool>,
) -> bool {
    let target_sort = arena.sort_of(lhs);
    if target_sort != arena.sort_of(rhs) {
        return false;
    }

    let arrays = fact_array_terms(arena, facts);
    for (idx, &lhs_array) in arrays.iter().enumerate() {
        let Sort::Array { element, .. } = arena.sort_of(lhs_array) else {
            continue;
        };
        if element.to_sort() != target_sort {
            continue;
        }
        for &rhs_array in &arrays[idx + 1..] {
            if lhs_array == rhs_array || arena.sort_of(lhs_array) != arena.sort_of(rhs_array) {
                continue;
            }
            let can_infer_stored_array_equality =
                match_store(arena, lhs_array).is_some() || match_store(arena, rhs_array).is_some();
            if !facts.same(lhs_array, rhs_array)
                && (!can_infer_stored_array_equality
                    || !terms_equivalent_inner(arena, facts, distinct, lhs_array, rhs_array, memo))
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

fn fact_array_terms(arena: &TermArena, facts: &EqFacts) -> Vec<TermId> {
    let mut arrays = BTreeSet::new();
    for &term in facts.parent.keys() {
        collect_fact_array_term(arena, term, &mut arrays);
    }
    for &term in facts.bv1_values.keys() {
        collect_fact_array_term(arena, term, &mut arrays);
    }
    arrays.into_iter().collect()
}

fn collect_fact_array_term(arena: &TermArena, term: TermId, out: &mut BTreeSet<TermId>) {
    if matches!(arena.sort_of(term), Sort::Array { .. }) {
        out.insert(term);
    }
    if let Some((array, _index)) = match_select(arena, term) {
        collect_array_chain_terms(arena, array, out);
    }
}

fn collect_array_chain_terms(arena: &TermArena, mut term: TermId, out: &mut BTreeSet<TermId>) {
    while matches!(arena.sort_of(term), Sort::Array { .. }) {
        out.insert(term);
        let Some((base, _index, _value)) = match_store(arena, term) else {
            break;
        };
        term = base;
    }
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
        || known_bv1_values_directly_distinct(arena, facts, lhs, rhs)
        || bv1_direct_negation_pair(arena, facts, lhs, rhs)
        || bv1_direct_negation_pair(arena, facts, rhs, lhs)
        || bv1_indices_distinct_by_known_array_read_values(arena, facts, lhs, rhs)
        || distinct.iter().any(|&(a, b)| {
            (terms_directly_equal(arena, facts, lhs, a)
                && terms_directly_equal(arena, facts, rhs, b))
                || (terms_directly_equal(arena, facts, lhs, b)
                    && terms_directly_equal(arena, facts, rhs, a))
        })
}

fn bv1_direct_negation_pair(arena: &TermArena, facts: &EqFacts, lhs: TermId, rhs: TermId) -> bool {
    let Some(inner) = match_bv_not(arena, lhs) else {
        return false;
    };
    arena.sort_of(lhs) == Sort::BitVec(1) && terms_directly_equal(arena, facts, inner, rhs)
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
            (
                known_bv1_value(arena, facts, lhs),
                known_bv1_value(arena, facts, rhs),
            ),
            (Some(lhs_value), Some(rhs_value)) if lhs_value == rhs_value
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
    if let Some(inner) = match_identity_extract(arena, term) {
        return facts.find(inner);
    }
    if let TermNode::App { op: Op::Ite, args } = arena.node(term) {
        if let [cond, then_term, else_term] = &**args {
            if let Some(branch) =
                contextual_ite_branch(arena, facts, distinct, *cond, *then_term, *else_term, memo)
            {
                return facts.find(branch);
            }
        }
    }
    simplify_idempotent_bitop(arena, facts, distinct, term, memo)
}

fn contextual_ite_branch(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    cond: TermId,
    then_term: TermId,
    else_term: TermId,
    memo: &mut BTreeMap<(TermId, TermId), bool>,
) -> Option<TermId> {
    if let Some(value) = bool_condition_value(arena, facts, distinct, cond, memo) {
        return Some(if value { then_term } else { else_term });
    }
    terms_equivalent_inner(arena, facts, distinct, then_term, else_term, memo).then_some(then_term)
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
        TermNode::App {
            op: Op::BvUlt,
            args,
        } if args.len() == 2 => bv_ult_condition_value(arena, args[0], args[1]),
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
            if let Some(branch) =
                contextual_ite_branch(arena, facts, distinct, cond, then_array, else_array, memo)
            {
                array = branch;
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
    if bv_unsigned_ranges_disjoint(arena, lhs, rhs) {
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

fn known_bv1_values_directly_distinct(
    arena: &TermArena,
    facts: &EqFacts,
    lhs: TermId,
    rhs: TermId,
) -> bool {
    matches!(
        (
            known_bv1_value(arena, facts, lhs),
            known_bv1_value(arena, facts, rhs),
        ),
        (Some(lhs_value), Some(rhs_value)) if lhs_value != rhs_value
    )
}

fn bv1_indices_distinct_by_known_array_read_values(
    arena: &TermArena,
    facts: &EqFacts,
    lhs_index: TermId,
    rhs_index: TermId,
) -> bool {
    facts.bv1_values.iter().any(|(&lhs_read, &lhs_value)| {
        let Some((lhs_array, left_index)) = match_select(arena, lhs_read) else {
            return false;
        };
        facts.bv1_values.iter().any(|(&rhs_read, &rhs_value)| {
            if lhs_value == rhs_value {
                return false;
            }
            let Some((rhs_array, right_index)) = match_select(arena, rhs_read) else {
                return false;
            };
            array_terms_match(facts, lhs_array, rhs_array)
                && ((terms_directly_equal(arena, facts, left_index, lhs_index)
                    && terms_directly_equal(arena, facts, right_index, rhs_index))
                    || (terms_directly_equal(arena, facts, left_index, rhs_index)
                        && terms_directly_equal(arena, facts, right_index, lhs_index)))
        })
    })
}

fn bv1_terms_equal_by_equal_order_bits(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    lhs: TermId,
    rhs: TermId,
    _memo: &mut BTreeMap<(TermId, TermId), bool>,
) -> bool {
    if arena.sort_of(lhs) != Sort::BitVec(1) || arena.sort_of(rhs) != Sort::BitVec(1) {
        return false;
    }

    let order_bits: Vec<_> = facts
        .parent
        .keys()
        .copied()
        .filter_map(|term| {
            let (lo, hi, bit_true_means_ult) = match_bv1_ult_bit(arena, term)?;
            Some((term, lo, hi, bit_true_means_ult))
        })
        .collect();

    for (idx, &(lhs_bit, lhs_lo, lhs_hi, lhs_positive)) in order_bits.iter().enumerate() {
        if !bv1_order_pair_directly_distinct(arena, facts, distinct, lhs_lo, lhs_hi) {
            continue;
        }
        for &(rhs_bit, rhs_lo, rhs_hi, rhs_positive) in &order_bits[idx + 1..] {
            if !facts.same(lhs_bit, rhs_bit)
                || !bv1_order_pair_directly_distinct(arena, facts, distinct, rhs_lo, rhs_hi)
            {
                continue;
            }

            let endpoint_pairs = if lhs_positive == rhs_positive {
                [(lhs_lo, rhs_lo), (lhs_hi, rhs_hi)]
            } else {
                [(lhs_lo, rhs_hi), (lhs_hi, rhs_lo)]
            };
            if endpoint_pairs.iter().any(|&(left, right)| {
                (terms_directly_equal(arena, facts, lhs, left)
                    && terms_directly_equal(arena, facts, rhs, right))
                    || (terms_directly_equal(arena, facts, lhs, right)
                        && terms_directly_equal(arena, facts, rhs, left))
            }) {
                return true;
            }
        }
    }
    false
}

fn bv1_order_pair_directly_distinct(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    lhs: TermId,
    rhs: TermId,
) -> bool {
    arena.sort_of(lhs) == Sort::BitVec(1)
        && arena.sort_of(rhs) == Sort::BitVec(1)
        && terms_directly_distinct_in_context(arena, facts, distinct, lhs, rhs)
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

fn finite_array_row_equivalence(
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

    let mut candidate_indices = BTreeSet::new();
    collect_store_write_indices(arena, lhs_array, &mut candidate_indices);
    collect_store_write_indices(arena, rhs_array, &mut candidate_indices);
    collect_fact_select_indices(arena, facts, &mut candidate_indices);

    let mut covered_reads = Vec::new();
    for index in candidate_indices {
        let lhs_read =
            normalize_select_over_writes_direct(arena, facts, distinct, lhs_array, index);
        let rhs_read =
            normalize_select_over_writes_direct(arena, facts, distinct, rhs_array, index);
        if row_exprs_equal_by_facts_or_values(
            arena,
            facts,
            distinct,
            lhs_read.expr,
            rhs_read.expr,
            memo,
        ) {
            covered_reads.push(ExtensionalReadBit {
                index,
                const_index: const_bv_value(arena, index).map(|(_width, value)| value),
            });
        }
    }
    extensional_reads_cover_domain(arena, facts, distinct, &covered_reads, domain_size, memo)
}

#[derive(Debug, Clone, Copy)]
struct Bv1OrderProfile {
    low_value_index: TermId,
    high_value_index: TermId,
}

fn finite_array_bv1_order_profile_equivalence(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    lhs_array: TermId,
    rhs_array: TermId,
) -> bool {
    if arena.sort_of(lhs_array)
        != (Sort::Array {
            index: ArraySortKey::BitVec(1),
            element: ArraySortKey::BitVec(1),
        })
        || arena.sort_of(rhs_array) != arena.sort_of(lhs_array)
    {
        return false;
    }

    let lhs_profiles = bv1_order_profiles_for_array(arena, facts, distinct, lhs_array);
    let rhs_profiles = bv1_order_profiles_for_array(arena, facts, distinct, rhs_array);
    lhs_profiles.iter().any(|lhs| {
        rhs_profiles.iter().any(|rhs| {
            equal_positive_bv1_order_bits(
                arena,
                facts,
                lhs.low_value_index,
                lhs.high_value_index,
                rhs.low_value_index,
                rhs.high_value_index,
            )
        })
    })
}

fn bv1_order_profiles_for_array(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    array: TermId,
) -> Vec<Bv1OrderProfile> {
    let reads = known_bv1_select_values(arena, facts, array);
    let mut profiles = Vec::new();
    for low in reads.iter().filter(|read| !read.value) {
        for high in reads.iter().filter(|read| read.value) {
            if arena.sort_of(low.index) == Sort::BitVec(1)
                && arena.sort_of(high.index) == Sort::BitVec(1)
                && bv1_order_pair_directly_distinct(arena, facts, distinct, low.index, high.index)
            {
                profiles.push(Bv1OrderProfile {
                    low_value_index: low.index,
                    high_value_index: high.index,
                });
            }
        }
    }
    profiles
}

fn equal_positive_bv1_order_bits(
    arena: &TermArena,
    facts: &EqFacts,
    lhs_low: TermId,
    lhs_high: TermId,
    rhs_low: TermId,
    rhs_high: TermId,
) -> bool {
    let order_bits: Vec<_> = facts
        .parent
        .keys()
        .copied()
        .filter_map(|term| {
            let (low, high, positive) = match_bv1_ult_bit(arena, term)?;
            positive.then_some((term, low, high))
        })
        .collect();

    order_bits
        .iter()
        .any(|&(lhs_bit, bit_lhs_low, bit_lhs_high)| {
            terms_directly_equal(arena, facts, bit_lhs_low, lhs_low)
                && terms_directly_equal(arena, facts, bit_lhs_high, lhs_high)
                && order_bits
                    .iter()
                    .any(|&(rhs_bit, bit_rhs_low, bit_rhs_high)| {
                        facts.same(lhs_bit, rhs_bit)
                            && terms_directly_equal(arena, facts, bit_rhs_low, rhs_low)
                            && terms_directly_equal(arena, facts, bit_rhs_high, rhs_high)
                    })
        })
}

fn bv1_array_ite_all_true_refutation(
    arena: &TermArena,
    facts: &EqFacts,
    denied_and_terms: &[Vec<TermId>],
) -> Option<(TermId, TermId)> {
    for array in fact_array_terms(arena, facts) {
        if !matches!(
            arena.sort_of(array),
            Sort::Array {
                index: ArraySortKey::BitVec(1),
                element: ArraySortKey::BitVec(1),
            }
        ) || match_ite(arena, array).is_none()
        {
            continue;
        }

        let Some((zero_read, one_read)) = known_true_bv1_domain_reads(arena, facts, array) else {
            continue;
        };

        let mut leaves = BTreeSet::new();
        collect_array_ite_leaves(arena, array, &mut leaves);
        if leaves.len() < 2 {
            continue;
        }
        if leaves.iter().all(|&leaf| {
            array_denies_both_bv1_domain_reads_true(arena, facts, denied_and_terms, leaf)
        }) {
            return Some((zero_read, one_read));
        }
    }
    None
}

fn known_true_bv1_domain_reads(
    arena: &TermArena,
    facts: &EqFacts,
    array: TermId,
) -> Option<(TermId, TermId)> {
    let mut zero_read = None;
    let mut one_read = None;
    for (&term, &value) in &facts.bv1_values {
        if !value {
            continue;
        }
        let Some((read_array, index)) = match_select(arena, term) else {
            continue;
        };
        if !array_terms_match(facts, read_array, array) {
            continue;
        }
        match const_bv_value(arena, index) {
            Some((1, 0)) => zero_read = Some(term),
            Some((1, 1)) => one_read = Some(term),
            _ => {}
        }
    }
    Some((zero_read?, one_read?))
}

fn conflicting_equalities(arena: &TermArena, facts: &EqFacts) -> Option<(TermId, TermId)> {
    let terms: Vec<_> = facts.parent.keys().copied().collect();
    for (idx, &lhs) in terms.iter().enumerate() {
        for &rhs in &terms[idx + 1..] {
            if facts.same(lhs, rhs) && bv_unsigned_ranges_disjoint(arena, lhs, rhs) {
                return Some((lhs, rhs));
            }
        }
    }
    None
}

#[derive(Debug, Clone, Copy)]
struct BvUnsignedRange {
    width: u32,
    min: u128,
    max: u128,
}

fn bv_unsigned_ranges_disjoint(arena: &TermArena, lhs: TermId, rhs: TermId) -> bool {
    let Some(lhs_range) = bv_unsigned_range(arena, lhs) else {
        return false;
    };
    let Some(rhs_range) = bv_unsigned_range(arena, rhs) else {
        return false;
    };
    lhs_range.width == rhs_range.width
        && (lhs_range.max < rhs_range.min || rhs_range.max < lhs_range.min)
}

fn bv_unsigned_ranges_same_singleton(arena: &TermArena, lhs: TermId, rhs: TermId) -> bool {
    let Some(lhs_range) = bv_unsigned_range(arena, lhs) else {
        return false;
    };
    let Some(rhs_range) = bv_unsigned_range(arena, rhs) else {
        return false;
    };
    lhs_range.width == rhs_range.width
        && lhs_range.min == lhs_range.max
        && rhs_range.min == rhs_range.max
        && lhs_range.min == rhs_range.min
}

fn bv_ult_condition_value(arena: &TermArena, lhs: TermId, rhs: TermId) -> Option<bool> {
    let lhs_range = bv_unsigned_range(arena, lhs)?;
    let rhs_range = bv_unsigned_range(arena, rhs)?;
    if lhs_range.width != rhs_range.width {
        return None;
    }
    if lhs_range.max < rhs_range.min {
        Some(true)
    } else if lhs_range.min >= rhs_range.max {
        Some(false)
    } else {
        None
    }
}

fn static_bool_condition_value(arena: &TermArena, term: TermId) -> Option<bool> {
    match arena.node(term) {
        TermNode::BoolConst(value) => Some(*value),
        TermNode::App {
            op: Op::BoolNot,
            args,
        } if args.len() == 1 => static_bool_condition_value(arena, args[0]).map(|value| !value),
        TermNode::App {
            op: Op::BvUlt,
            args,
        } if args.len() == 2 => bv_ult_condition_value(arena, args[0], args[1]),
        TermNode::App { op: Op::Eq, args } if args.len() == 2 => {
            if bv_unsigned_ranges_same_singleton(arena, args[0], args[1]) {
                Some(true)
            } else if bv_unsigned_ranges_disjoint(arena, args[0], args[1]) {
                Some(false)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn bv_unsigned_range(arena: &TermArena, term: TermId) -> Option<BvUnsignedRange> {
    let Sort::BitVec(width) = arena.sort_of(term) else {
        return None;
    };
    if width > 128 {
        return None;
    }

    match arena.node(term) {
        TermNode::BvConst { width, value } => Some(BvUnsignedRange {
            width: *width,
            min: *value,
            max: *value,
        }),
        TermNode::Symbol(_) => Some(BvUnsignedRange {
            width,
            min: 0,
            max: bv_mask(width),
        }),
        TermNode::App { op, args } => match op {
            Op::ZeroExt { .. } if args.len() == 1 => {
                let inner = bv_unsigned_range(arena, args[0])?;
                (inner.width <= width).then_some(BvUnsignedRange {
                    width,
                    min: inner.min,
                    max: inner.max,
                })
            }
            Op::SignExt { .. } if args.len() == 1 => sign_ext_unsigned_range(arena, width, args[0]),
            Op::Extract { hi, lo } if args.len() == 1 => {
                extract_unsigned_range(arena, width, term, args[0], *hi, *lo)
            }
            Op::Concat if args.len() == 2 => {
                let high = bv_unsigned_range(arena, args[0])?;
                let low = bv_unsigned_range(arena, args[1])?;
                if high.width + low.width != width || low.width >= 128 {
                    return None;
                }
                let high_min = high.min.checked_shl(low.width)?;
                let high_max = high.max.checked_shl(low.width)?;
                Some(BvUnsignedRange {
                    width,
                    min: high_min.checked_add(low.min)?,
                    max: high_max.checked_add(low.max)?,
                })
            }
            Op::BvAdd if args.len() == 2 => {
                let lhs = bv_unsigned_range(arena, args[0])?;
                let rhs = bv_unsigned_range(arena, args[1])?;
                if lhs.width != width || rhs.width != width {
                    return None;
                }
                let min = lhs.min.checked_add(rhs.min)?;
                let max = lhs.max.checked_add(rhs.max)?;
                (max <= bv_mask(width)).then_some(BvUnsignedRange { width, min, max })
            }
            Op::Ite if args.len() == 3 => {
                ite_unsigned_range(arena, width, args[0], args[1], args[2])
            }
            _ => None,
        },
        _ => None,
    }
}

fn sign_ext_unsigned_range(
    arena: &TermArena,
    width: u32,
    inner_term: TermId,
) -> Option<BvUnsignedRange> {
    let inner = bv_unsigned_range(arena, inner_term)?;
    if inner.width == 0 || inner.width > width {
        return None;
    }
    let sign_bit = 1_u128.checked_shl(inner.width - 1)?;
    let inner_mask = bv_mask(inner.width);
    if inner.max < sign_bit {
        Some(BvUnsignedRange {
            width,
            min: inner.min,
            max: inner.max,
        })
    } else if inner.min >= sign_bit {
        let high_bits = bv_mask(width) ^ inner_mask;
        Some(BvUnsignedRange {
            width,
            min: inner.min | high_bits,
            max: inner.max | high_bits,
        })
    } else {
        None
    }
}

fn extract_unsigned_range(
    arena: &TermArena,
    width: u32,
    term: TermId,
    inner_term: TermId,
    hi: u32,
    lo: u32,
) -> Option<BvUnsignedRange> {
    if let Some(inner) = match_identity_extract(arena, term) {
        return bv_unsigned_range(arena, inner);
    }
    let inner = bv_unsigned_range(arena, inner_term)?;
    if inner.min != inner.max || hi < lo {
        return None;
    }
    let extracted_width = hi.checked_sub(lo)?.checked_add(1)?;
    if extracted_width != width {
        return None;
    }
    let value = (inner.min >> lo) & bv_mask(width);
    Some(BvUnsignedRange {
        width,
        min: value,
        max: value,
    })
}

fn ite_unsigned_range(
    arena: &TermArena,
    width: u32,
    cond: TermId,
    then_term: TermId,
    else_term: TermId,
) -> Option<BvUnsignedRange> {
    if let Some(cond_value) = static_bool_condition_value(arena, cond) {
        let branch = if cond_value { then_term } else { else_term };
        let branch_range = bv_unsigned_range(arena, branch)?;
        return (branch_range.width == width).then_some(branch_range);
    }
    let then_range = bv_unsigned_range(arena, then_term)?;
    let else_range = bv_unsigned_range(arena, else_term)?;
    if then_range.width != width || else_range.width != width {
        return None;
    }
    Some(BvUnsignedRange {
        width,
        min: then_range.min.min(else_range.min),
        max: then_range.max.max(else_range.max),
    })
}

fn conflicting_bv1_values(arena: &TermArena, facts: &EqFacts) -> Option<(TermId, TermId)> {
    let entries: Vec<_> = facts
        .bv1_values
        .iter()
        .map(|(&term, &value)| (term, value))
        .collect();
    for (idx, &(lhs, lhs_value)) in entries.iter().enumerate() {
        for &(rhs, rhs_value) in &entries[idx + 1..] {
            if lhs_value != rhs_value && terms_equivalent(arena, facts, lhs, rhs) {
                return Some((lhs, rhs));
            }
        }
    }
    None
}

fn conflicting_bool_negation_equalities(
    arena: &TermArena,
    facts: &EqFacts,
) -> Option<(TermId, TermId)> {
    let terms: Vec<_> = facts.parent.keys().copied().collect();
    for &negated in &terms {
        let Some(inner) = match_bool_not(arena, negated) else {
            continue;
        };
        for &term in &terms {
            if !facts.same(term, negated) {
                continue;
            }
            if terms_equivalent(arena, facts, term, inner) {
                return Some((term, inner));
            }
        }
    }
    None
}

fn conflicting_ite_branch_disequalities(
    arena: &TermArena,
    facts: &EqFacts,
    disequalities: &[(TermId, TermId)],
) -> Option<(TermId, TermId)> {
    for &(lhs, rhs) in disequalities {
        if let Some(witness) =
            conflicting_ite_branch_disequality_one(arena, facts, disequalities, lhs, rhs)
        {
            return Some(witness);
        }
        if let Some(witness) =
            conflicting_ite_branch_disequality_one(arena, facts, disequalities, rhs, lhs)
        {
            return Some(witness);
        }
    }
    None
}

fn conflicting_ite_branch_disequality_one(
    arena: &TermArena,
    facts: &EqFacts,
    disequalities: &[(TermId, TermId)],
    ite_term: TermId,
    branch_term: TermId,
) -> Option<(TermId, TermId)> {
    let (_cond, then_term, else_term) = match_ite(arena, ite_term)?;
    let branch_is_then = terms_equivalent(arena, facts, branch_term, then_term);
    let branch_is_else = terms_equivalent(arena, facts, branch_term, else_term);
    if !branch_is_then && !branch_is_else {
        return None;
    }
    let opposite_branch = if branch_is_then { else_term } else { then_term };
    disequalities
        .iter()
        .any(|&(lhs, rhs)| {
            disequality_matches_ite_branch(arena, facts, lhs, rhs, ite_term, opposite_branch)
                || disequality_matches_ite_branch(arena, facts, rhs, lhs, ite_term, opposite_branch)
        })
        .then_some((ite_term, branch_term))
}

fn disequality_matches_ite_branch(
    arena: &TermArena,
    facts: &EqFacts,
    lhs: TermId,
    rhs: TermId,
    ite_term: TermId,
    branch_term: TermId,
) -> bool {
    terms_equivalent(arena, facts, lhs, ite_term)
        && terms_equivalent(arena, facts, rhs, branch_term)
}

fn forced_select_store_ite_bv1_value_conflict(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
) -> Option<(TermId, TermId)> {
    for (&term, &asserted_value) in &facts.bv1_values {
        let mut memo = BTreeMap::new();
        let Some((forced_value, forced_term)) =
            select_store_ite_index_forced_bv1_value(arena, facts, distinct, term, &mut memo)
        else {
            continue;
        };
        if forced_value != asserted_value {
            return Some((term, forced_term));
        }
    }
    None
}

fn select_store_ite_index_forced_bv1_value(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    term: TermId,
    memo: &mut BTreeMap<(TermId, TermId), bool>,
) -> Option<(bool, TermId)> {
    if arena.sort_of(term) != Sort::BitVec(1) {
        return None;
    }
    let (stored, _read_index) = match_select(arena, term)?;
    let (_base, write_index, stored_value) = match_store(arena, stored)?;
    let (cond, _then_index, _else_index) = match_ite(arena, write_index)?;
    let forced_value = known_bv1_value_in_context(arena, facts, distinct, stored_value, memo)?;

    for polarity in [true, false] {
        let mut branch_probe = ReadCongruenceProbe {
            facts: facts.clone(),
            ..ReadCongruenceProbe::default()
        };
        collect_bool_assertion(arena, cond, polarity, &mut branch_probe)?;
        branch_probe.disequalities.extend_from_slice(distinct);
        let mut branch_memo = BTreeMap::new();
        let row = normalize_read_over_writes_in_context(
            arena,
            &branch_probe.facts,
            &branch_probe.disequalities,
            term,
            &mut branch_memo,
        );
        if !row_exprs_equal_by_facts_or_values(
            arena,
            &branch_probe.facts,
            &branch_probe.disequalities,
            row.expr,
            RowExpr::Term(stored_value),
            &mut branch_memo,
        ) {
            return None;
        }
    }
    Some((forced_value, stored_value))
}

fn collect_array_ite_leaves(arena: &TermArena, array: TermId, leaves: &mut BTreeSet<TermId>) {
    if let Some((_cond, then_array, else_array)) = match_ite(arena, array) {
        collect_array_ite_leaves(arena, then_array, leaves);
        collect_array_ite_leaves(arena, else_array, leaves);
    } else {
        leaves.insert(array);
    }
}

fn array_denies_both_bv1_domain_reads_true(
    arena: &TermArena,
    facts: &EqFacts,
    denied_and_terms: &[Vec<TermId>],
    array: TermId,
) -> bool {
    denied_and_terms.iter().any(|terms| {
        terms
            .iter()
            .any(|&term| is_select_of_bv1_index(arena, facts, term, array, 0))
            && terms
                .iter()
                .any(|&term| is_select_of_bv1_index(arena, facts, term, array, 1))
    })
}

fn is_select_of_bv1_index(
    arena: &TermArena,
    facts: &EqFacts,
    term: TermId,
    expected_array: TermId,
    expected_index: u128,
) -> bool {
    let Some((array, index)) = match_select(arena, term) else {
        return false;
    };
    array_terms_match(facts, array, expected_array)
        && const_bv_value(arena, index) == Some((1, expected_index))
}

fn collect_fact_select_indices(arena: &TermArena, facts: &EqFacts, out: &mut BTreeSet<TermId>) {
    for &term in facts.parent.keys() {
        if let Some((_array, index)) = match_select(arena, term) {
            out.insert(index);
        }
    }
    for &term in facts.bv1_values.keys() {
        if let Some((_array, index)) = match_select(arena, term) {
            out.insert(index);
        }
    }
}

fn row_exprs_equal_by_facts_or_values(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    lhs: RowExpr,
    rhs: RowExpr,
    memo: &mut BTreeMap<(TermId, TermId), bool>,
) -> bool {
    if row_exprs_equal_by_facts(arena, facts, distinct, lhs, rhs, memo) {
        return true;
    }
    match (
        row_expr_bv1_value(arena, facts, distinct, lhs, memo),
        row_expr_bv1_value(arena, facts, distinct, rhs, memo),
    ) {
        (Some(lhs_value), Some(rhs_value)) => lhs_value == rhs_value,
        _ => false,
    }
}

fn row_exprs_equal_by_facts(
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
            if array_terms_match(facts, lhs_array, rhs_array)
                && terms_equivalent_inner(arena, facts, distinct, lhs_index, rhs_index, memo)
            {
                return true;
            }
            select_terms_for_row(arena, facts, lhs_array, lhs_index)
                .iter()
                .any(|&lhs_term| {
                    select_terms_for_row(arena, facts, rhs_array, rhs_index)
                        .iter()
                        .any(|&rhs_term| facts.same(lhs_term, rhs_term))
                })
        }
        (RowExpr::Term(term), RowExpr::Select { array, index })
        | (RowExpr::Select { array, index }, RowExpr::Term(term)) => {
            if store_self_update_row_equivalent(arena, facts, array, index, term) {
                return true;
            }
            select_terms_for_row(arena, facts, array, index)
                .iter()
                .any(|&select_term| {
                    terms_equivalent_inner(arena, facts, distinct, term, select_term, memo)
                })
        }
    }
}

fn store_self_update_row_equivalent(
    arena: &TermArena,
    facts: &EqFacts,
    array: TermId,
    index: TermId,
    value_term: TermId,
) -> bool {
    facts
        .store_self_reads
        .iter()
        .any(|&(base, write_index, value)| {
            facts.same(array, base)
                && terms_directly_equal(arena, facts, index, write_index)
                && terms_directly_equal(arena, facts, value_term, value)
        })
}

fn select_terms_for_row(
    arena: &TermArena,
    facts: &EqFacts,
    expected_array: TermId,
    expected_index: TermId,
) -> Vec<TermId> {
    facts
        .parent
        .keys()
        .copied()
        .filter(|&term| {
            match_select(arena, term).is_some_and(|(array, index)| {
                array_terms_match(facts, array, expected_array)
                    && terms_directly_equal(arena, facts, index, expected_index)
            })
        })
        .collect()
}

fn row_expr_bv1_value(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    expr: RowExpr,
    memo: &mut BTreeMap<(TermId, TermId), bool>,
) -> Option<bool> {
    match expr {
        RowExpr::Term(term) => known_bv1_value_in_context(arena, facts, distinct, term, memo),
        RowExpr::Select { array, index } => facts.bv1_values.iter().find_map(|(&term, &value)| {
            let (known_array, known_index) = match_select(arena, term)?;
            let known_row = normalize_select_over_writes_direct(
                arena,
                facts,
                distinct,
                known_array,
                known_index,
            );
            row_exprs_same_location_in_context(
                arena,
                facts,
                distinct,
                known_row.expr,
                RowExpr::Select { array, index },
                memo,
            )
            .then_some(value)
        }),
    }
}

fn row_exprs_same_location_in_context(
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
            array_terms_match(facts, lhs_array, rhs_array)
                && terms_equivalent_inner(arena, facts, distinct, lhs_index, rhs_index, memo)
        }
        (RowExpr::Term(term), RowExpr::Select { array, index })
        | (RowExpr::Select { array, index }, RowExpr::Term(term)) => match_select(arena, term)
            .is_some_and(|(term_array, term_index)| {
                array_terms_match(facts, term_array, array)
                    && terms_equivalent_inner(arena, facts, distinct, term_index, index, memo)
            }),
    }
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
    pairwise_distinct_reads_cover_domain(arena, facts, distinct, reads, domain_size, memo)
}

fn pairwise_distinct_reads_cover_domain(
    arena: &TermArena,
    facts: &EqFacts,
    distinct: &[(TermId, TermId)],
    reads: &[ExtensionalReadBit],
    domain_size: u128,
    memo: &mut BTreeMap<(TermId, TermId), bool>,
) -> bool {
    let Ok(needed) = usize::try_from(domain_size) else {
        return false;
    };
    if needed == 0 || reads.len() < needed {
        return false;
    }
    let mut selected = Vec::with_capacity(needed);
    let mut search = PairwiseReadCoverSearch {
        arena,
        facts,
        distinct,
        reads,
        memo,
    };
    search.choose(needed, 0, &mut selected)
}

struct PairwiseReadCoverSearch<'a> {
    arena: &'a TermArena,
    facts: &'a EqFacts,
    distinct: &'a [(TermId, TermId)],
    reads: &'a [ExtensionalReadBit],
    memo: &'a mut BTreeMap<(TermId, TermId), bool>,
}

impl PairwiseReadCoverSearch<'_> {
    fn choose(&mut self, needed: usize, start: usize, selected: &mut Vec<usize>) -> bool {
        if selected.len() == needed {
            return true;
        }
        let remaining_needed = needed - selected.len();
        if self.reads.len().saturating_sub(start) < remaining_needed {
            return false;
        }

        for idx in start..self.reads.len() {
            let candidate = &self.reads[idx];
            if selected.iter().all(|&selected_idx| {
                terms_definitely_distinct_in_context(
                    self.arena,
                    self.facts,
                    self.distinct,
                    candidate.index,
                    self.reads[selected_idx].index,
                    self.memo,
                )
            }) {
                selected.push(idx);
                if self.choose(needed, idx + 1, selected) {
                    return true;
                }
                selected.pop();
            }
        }
        false
    }
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

fn match_identity_extract(arena: &TermArena, term: TermId) -> Option<TermId> {
    let TermNode::App {
        op: Op::Extract { hi, lo },
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [inner] = &**args else {
        return None;
    };
    let Sort::BitVec(inner_width) = arena.sort_of(*inner) else {
        return None;
    };
    let Sort::BitVec(term_width) = arena.sort_of(term) else {
        return None;
    };
    (*lo == 0 && hi.checked_add(1) == Some(inner_width) && term_width == inner_width)
        .then_some(*inner)
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
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read9.btor.smt2"
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
    fn recognizes_btor_bv1_array_ite_all_true_regressions() {
        let cases = [
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond3.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond5.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond6.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond7.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond8.btor.smt2"
            ),
        ];

        for text in cases {
            let script = parse_script(text).expect("ABV BV1 array-ITE all-true case parses");
            let cert = array_axiom_refutation(&script.arena, &script.assertions)
                .expect("BV1 array-ITE all-true branch cover refutes");
            assert_eq!(cert.kind, ArrayAxiomKind::ReadCongruence);
        }
    }

    #[test]
    fn recognizes_btor_contextual_ite_branch_regressions() {
        let cases = [
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond11.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond12.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond13.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond14.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond18.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext11.btor.smt2"
            ),
        ];

        for text in cases {
            let script = parse_script(text).expect("ABV contextual ITE branch case parses");
            let cert = array_axiom_refutation(&script.arena, &script.assertions)
                .expect("contextual ITE branch read congruence refutes");
            assert_eq!(cert.kind, ArrayAxiomKind::ReadCongruence);
        }
    }

    #[test]
    fn recognizes_cvc5_same_cell_store_bv_range_regressions() {
        let cases = [
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__bv__issue9519.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__bv__proj-issue321.smt2"
            ),
        ];

        for text in cases {
            let script = parse_script(text).expect("cvc5 same-cell store BV range case parses");
            let cert = array_axiom_refutation(&script.arena, &script.assertions)
                .expect("same-cell store value equality has disjoint BV ranges");
            assert_eq!(cert.kind, ArrayAxiomKind::ReadCongruence);
        }
    }

    #[test]
    fn recognizes_cvc5_store_restore_noop_regression() {
        let script = parse_script(include_str!(
            "../../../corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__arrays__bug637.delta.smt2"
        ))
        .expect("cvc5 store-restore no-op case parses");
        let cert = array_axiom_refutation(&script.arena, &script.assertions)
            .expect("store-restore no-op chain refutes");
        assert_eq!(cert.kind, ArrayAxiomKind::StoreShadowing);
    }

    #[test]
    fn recognizes_cvc5_same_value_store_chain_coverage_regression() {
        let script = parse_script(include_str!(
            "../../../corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__bv__bvproof2.smt2"
        ))
        .expect("cvc5 same-value store-chain coverage case parses");
        let cert = array_axiom_refutation(&script.arena, &script.assertions)
            .expect("same-value store-chain coverage refutes");
        assert_eq!(cert.kind, ArrayAxiomKind::StoreShadowing);
    }

    #[test]
    fn recognizes_cvc5_signed_bv1_read_congruence_regression() {
        let script = parse_script(include_str!(
            "../../../corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__arrays__issue9041.smt2"
        ))
        .expect("cvc5 signed BV1 read-congruence case parses");
        let cert = array_axiom_refutation(&script.arena, &script.assertions)
            .expect("signed BV1 read congruence refutes");
        assert_eq!(cert.kind, ArrayAxiomKind::ReadCongruence);
    }

    #[test]
    fn recognizes_btor_array_ite_read_congruence_regression() {
        let script = parse_script(include_str!(
            "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw34.btor.smt2"
        ))
        .expect("BTOR array-ITE read-congruence case parses");
        let cert = array_axiom_refutation(&script.arena, &script.assertions)
            .expect("array equality contradicts disequal reads at the same index");
        assert_eq!(cert.kind, ArrayAxiomKind::ReadCongruence);
    }

    #[test]
    fn recognizes_btor_array_ite_branch_exhaustion_regression() {
        let script = parse_script(include_str!(
            "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond9.btor.smt2"
        ))
        .expect("BTOR array-ITE branch-exhaustion case parses");
        let cert = array_axiom_refutation(&script.arena, &script.assertions)
            .expect("ITE term cannot be disequal from both branches");
        assert_eq!(cert.kind, ArrayAxiomKind::ReadCongruence);
    }

    #[test]
    fn does_not_refute_uncovered_same_value_store_chains() {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 2, 2).unwrap();
        let zero_idx = arena.bv_const(2, 0).unwrap();
        let one_idx = arena.bv_const(2, 1).unwrap();
        let zero_val = arena.bv_const(2, 0).unwrap();
        let lhs = arena.store(a, zero_idx, zero_val).unwrap();
        let rhs = arena.store(a, one_idx, zero_val).unwrap();
        let diseq = {
            let eq = arena.eq(lhs, rhs).unwrap();
            arena.not(eq).unwrap()
        };

        assert!(
            array_axiom_refutation(&arena, &[diseq]).is_none(),
            "same-value chains at uncovered distinct indices are satisfiable"
        );
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
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext13.btor.smt2"
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
    fn recognizes_btor_finite_store_row_extensionality_regressions() {
        let cases = [
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext19.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext24.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext25.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write16.btor.smt2"
            ),
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write17.btor.smt2"
            ),
        ];

        for text in cases {
            let script = parse_script(text).expect("ABV finite store-row case parses");
            let cert = array_axiom_refutation(&script.arena, &script.assertions)
                .expect("finite store-row extensionality case refutes");
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
