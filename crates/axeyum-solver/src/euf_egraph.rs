//! EUF reasoning on the congruence-closure e-graph (Track 1, P1.5 / T1.5.5, first
//! slice).
//!
//! [`prove_unsat_by_congruence`] is the e-graph's first consumer in the solver: a
//! **sound** unsatisfiability prover for the conjunctive equality fragment. It
//! abstracts the assertions as uninterpreted equality logic — every term is an
//! e-node, every interpreted operator is treated as an uninterpreted function
//! (congruence still holds), and distinct literal constants are kept apart — then
//! asserts the top-level equalities into the [`EGraph`] and checks whether any
//! asserted disequality (or constant distinctness) is violated by congruence.
//!
//! Because the uninterpreted abstraction knows *less* than the real theory, a
//! contradiction it finds is a real contradiction: **proving UNSAT this way is
//! sound** (`x = f(a) ∧ a = b ∧ f(b) ≠ x` is UNSAT by congruence regardless of the
//! base sort). It is intentionally *incomplete* — consistency of the abstraction
//! says nothing, so the prover only ever returns a proof of UNSAT or "don't know",
//! and SAT is left to the bit-blaster. Every conflict it reports is re-validated by
//! the independent [`check_congruence`] checker before being returned, keeping it
//! inside the "trusted small checking" identity.
//!
//! This is the congruence core that the full lazy CDCL(T) loop (boolean search +
//! theory propagation, the rest of P1.5) and theory combination (P1.6) build on.

use std::collections::HashMap;

use axeyum_egraph::{EGraph, ENodeId, check_congruence};
use axeyum_ir::{Op, TermArena, TermId, TermNode};

/// A congruence conflict proving the assertions UNSAT: the subset of original
/// assertions that, under congruence, are contradictory.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EufConflict {
    /// Original assertion ids whose conjunction is UNSAT by congruence.
    pub core: Vec<TermId>,
}

/// Tries to prove `assertions` UNSAT by congruence closure over their equality
/// structure (see module docs). Returns the conflict when proven, or `None` when
/// the abstraction is consistent (no claim about the real formula).
///
/// # Panics
///
/// Every returned conflict is re-checked by the independent congruence checker; a
/// conflict that fails that check is a soundness bug and panics rather than being
/// returned.
#[must_use]
pub fn prove_unsat_by_congruence(arena: &TermArena, assertions: &[TermId]) -> Option<EufConflict> {
    let mut bridge = Bridge::new();

    // Collect the definite top-level equality / disequality atoms (descending
    // through top-level conjunctions; an `or`/`ite`/predicate we cannot pin is just
    // dropped — using fewer constraints keeps an UNSAT proof sound).
    let mut eqs: Vec<Atom> = Vec::new();
    let mut diseqs: Vec<Atom> = Vec::new();
    for &assertion in assertions {
        bridge.collect(arena, assertion, true, assertion, &mut eqs, &mut diseqs);
    }

    // Assert every equality, tagging each with its index as the e-graph reason.
    for (reason, atom) in eqs.iter().enumerate() {
        bridge.egraph.merge(
            atom.a,
            atom.b,
            u32::try_from(reason).expect("equality count fits u32"),
        );
    }

    // A conflict is an asserted disequality whose sides are now congruent, or two
    // distinct literal constants that became congruent.
    if let Some(conflict) = bridge.first_diseq_conflict(&eqs, &diseqs) {
        return Some(conflict);
    }
    bridge.first_constant_conflict(&eqs)
}

/// An equality/disequality atom between two e-nodes, tagged with the original
/// assertion it came from.
struct Atom {
    a: ENodeId,
    b: ENodeId,
    origin: TermId,
}

/// Builds e-nodes for terms and assigns each symbol/function/constant a distinct
/// `decl`, so the e-graph's congruence matches the terms' structure.
struct Bridge {
    egraph: EGraph,
    term_to_node: HashMap<TermId, ENodeId>,
    decls: HashMap<DeclKey, u32>,
    /// Literal-constant e-nodes (kept pairwise distinct).
    constants: Vec<ENodeId>,
    next_decl: u32,
}

/// What a `decl` identifies: a symbol, an uninterpreted function, an interpreted
/// operator (treated uninterpreted), or a literal constant value.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum DeclKey {
    Symbol(usize),
    Op(String),
    Const(String),
}

impl Bridge {
    fn new() -> Self {
        Self {
            egraph: EGraph::new(),
            term_to_node: HashMap::new(),
            decls: HashMap::new(),
            constants: Vec::new(),
            next_decl: 0,
        }
    }

    /// A stable `decl` id for `key`.
    fn decl(&mut self, key: DeclKey) -> u32 {
        if let Some(&d) = self.decls.get(&key) {
            return d;
        }
        let d = self.next_decl;
        self.next_decl += 1;
        self.decls.insert(key, d);
        d
    }

    /// The e-node for `term`, creating it (and its subterms) on first use.
    fn node(&mut self, arena: &TermArena, term: TermId) -> ENodeId {
        if let Some(&n) = self.term_to_node.get(&term) {
            return n;
        }
        let n = match arena.node(term) {
            TermNode::Symbol(s) => {
                let decl = self.decl(DeclKey::Symbol(s.index()));
                self.egraph.add(decl, &[])
            }
            TermNode::BoolConst(_)
            | TermNode::BvConst { .. }
            | TermNode::WideBvConst(_)
            | TermNode::IntConst(_)
            | TermNode::RealConst(_) => {
                // Each distinct literal value is a distinct constant node.
                let key = DeclKey::Const(format!("{:?}", arena.node(term)));
                let decl = self.decl(key);
                let node = self.egraph.add(decl, &[]);
                if !self.constants.contains(&node) {
                    self.constants.push(node);
                }
                node
            }
            TermNode::App { op, args } => {
                let key = DeclKey::Op(format!("{op:?}"));
                let args = args.clone();
                let child_nodes: Vec<ENodeId> = args.iter().map(|&a| self.node(arena, a)).collect();
                let decl = self.decl(key);
                self.egraph.add(decl, &child_nodes)
            }
        };
        self.term_to_node.insert(term, n);
        n
    }

    /// Collects definite eq/diseq atoms reachable from `term` asserted with
    /// `polarity`, descending through Boolean connectives where it is sound.
    fn collect(
        &mut self,
        arena: &TermArena,
        term: TermId,
        polarity: bool,
        origin_term: TermId,
        eqs: &mut Vec<Atom>,
        diseqs: &mut Vec<Atom>,
    ) {
        if let TermNode::App { op, args } = arena.node(term) {
            match op {
                Op::Eq if args.len() == 2 => {
                    let (l, r) = (args[0], args[1]);
                    let a = self.node(arena, l);
                    let b = self.node(arena, r);
                    let atom = Atom {
                        a,
                        b,
                        origin: origin_term,
                    };
                    if polarity {
                        eqs.push(atom);
                    } else {
                        diseqs.push(atom);
                    }
                }
                Op::BoolNot if args.len() == 1 => {
                    let inner = args[0];
                    self.collect(arena, inner, !polarity, origin_term, eqs, diseqs);
                }
                Op::BoolAnd if polarity => {
                    let children = args.clone();
                    for &a in &children {
                        self.collect(arena, a, true, origin_term, eqs, diseqs);
                    }
                }
                Op::BoolOr if !polarity => {
                    // ¬(a ∨ b) ≡ ¬a ∧ ¬b.
                    let children = args.clone();
                    for &a in &children {
                        self.collect(arena, a, false, origin_term, eqs, diseqs);
                    }
                }
                _ => {}
            }
        }
    }

    /// The first asserted disequality whose sides became congruent.
    fn first_diseq_conflict(&self, eqs: &[Atom], diseqs: &[Atom]) -> Option<EufConflict> {
        for d in diseqs {
            if self.egraph.equal(d.a, d.b) {
                return Some(self.build_conflict(eqs, d.a, d.b, Some(d.origin)));
            }
        }
        None
    }

    /// The first pair of distinct literal constants that became congruent.
    fn first_constant_conflict(&self, eqs: &[Atom]) -> Option<EufConflict> {
        for i in 0..self.constants.len() {
            for j in (i + 1)..self.constants.len() {
                let (ci, cj) = (self.constants[i], self.constants[j]);
                if self.egraph.equal(ci, cj) {
                    return Some(self.build_conflict(eqs, ci, cj, None));
                }
            }
        }
        None
    }

    /// Builds and independently re-checks the conflict that `a` and `b` are forced
    /// equal: the core is the originating assertions of the equalities in the
    /// explanation plus (for a disequality conflict) the disequality's assertion.
    fn build_conflict(
        &self,
        eqs: &[Atom],
        a: ENodeId,
        b: ENodeId,
        diseq_origin: Option<TermId>,
    ) -> EufConflict {
        let reasons = self.egraph.explain(a, b);
        let premises: Vec<(ENodeId, ENodeId)> = reasons
            .iter()
            .map(|&r| (eqs[r as usize].a, eqs[r as usize].b))
            .collect();
        assert!(
            check_congruence(&self.egraph, &premises, a, b),
            "congruence conflict failed the independent checker (soundness bug)"
        );
        let mut core: Vec<TermId> = reasons.iter().map(|&r| eqs[r as usize].origin).collect();
        if let Some(origin) = diseq_origin {
            core.push(origin);
        }
        core.sort_by_key(|t| t.index());
        core.dedup();
        EufConflict { core }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::{Sort, TermArena};

    #[test]
    fn congruence_contradiction_is_proven_unsat() {
        // a = b ∧ f(a) ≠ f(b): UNSAT by congruence.
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let a_eq_b = arena.eq(a, b).unwrap();
        let fa_eq_fb = arena.eq(fa, fb).unwrap();
        let fa_ne_fb = arena.not(fa_eq_fb).unwrap();

        let conflict = prove_unsat_by_congruence(&arena, &[a_eq_b, fa_ne_fb])
            .expect("a=b ∧ f(a)≠f(b) is UNSAT by congruence");
        assert!(conflict.core.contains(&a_eq_b));
        assert!(conflict.core.contains(&fa_ne_fb));
    }

    #[test]
    fn transitivity_chain_contradiction() {
        // a=b ∧ b=c ∧ a≠c is UNSAT; the core names the relevant assertions.
        let mut arena = TermArena::new();
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let c = arena.bv_var("c", 8).unwrap();
        let ab = arena.eq(a, b).unwrap();
        let bc = arena.eq(b, c).unwrap();
        let ac = arena.eq(a, c).unwrap();
        let a_ne_c = arena.not(ac).unwrap();

        let conflict =
            prove_unsat_by_congruence(&arena, &[ab, bc, a_ne_c]).expect("transitivity UNSAT");
        assert!(conflict.core.contains(&ab));
        assert!(conflict.core.contains(&bc));
        assert!(conflict.core.contains(&a_ne_c));
    }

    #[test]
    fn distinct_constants_force_unsat() {
        // x = 3 ∧ x = 5 is UNSAT because the literals 3 and 5 are kept distinct.
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 8).unwrap();
        let three = arena.bv_const(8, 3).unwrap();
        let five = arena.bv_const(8, 5).unwrap();
        let x3 = arena.eq(x, three).unwrap();
        let x5 = arena.eq(x, five).unwrap();

        let conflict = prove_unsat_by_congruence(&arena, &[x3, x5])
            .expect("x=3 ∧ x=5 contradicts constant distinctness");
        assert!(conflict.core.contains(&x3));
        assert!(conflict.core.contains(&x5));
    }

    #[test]
    fn consistent_assertions_are_not_claimed_unsat() {
        // a = b ∧ f(a) = f(b): consistent; the prover must not claim UNSAT.
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let ab = arena.eq(a, b).unwrap();
        let fa_eq_fb = arena.eq(fa, fb).unwrap();

        assert!(prove_unsat_by_congruence(&arena, &[ab, fa_eq_fb]).is_none());
    }

    #[test]
    fn conjunction_is_traversed() {
        // (a=b ∧ f(a)≠f(b)) as a single conjunctive assertion is still UNSAT.
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let ab = arena.eq(a, b).unwrap();
        let fa_eq_fb = arena.eq(fa, fb).unwrap();
        let fa_ne_fb = arena.not(fa_eq_fb).unwrap();
        let conj = arena.and(ab, fa_ne_fb).unwrap();

        assert!(prove_unsat_by_congruence(&arena, &[conj]).is_some());
    }
}
