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
use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode};
use axeyum_rewrite::replace_subterms;

use crate::backend::{CheckResult, SolverBackend, SolverConfig};
use crate::sat_bv_backend::SatBvBackend;

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

/// Proves `assertions` UNSAT over **arbitrary boolean structure** by the offline
/// DPLL(T) loop (Track 1, P1.5): abstract each equality atom to a Boolean variable,
/// SAT-solve the boolean skeleton, theory-check the model on the e-graph, and on a
/// congruence conflict feed back a blocking clause built from the conflict's
/// `explain`, until the skeleton is UNSAT (⇒ the original is UNSAT) or a
/// theory-consistent model is found (⇒ not proven).
///
/// Like [`prove_unsat_by_congruence`] this is a **sound, incomplete** UNSAT prover:
/// the uninterpreted abstraction proves real contradictions, while a consistent
/// boolean model says nothing (the base-sort theory is left to the bit-blaster).
/// It strictly strengthens the conjunctive prover — e.g. `(a=b ∨ a=c) ∧ a≠b ∧ a≠c`
/// needs the boolean search to refute both disjuncts.
///
/// Returns `true` iff UNSAT was proven. Mutates `arena` (fresh atom variables and
/// blocking-clause terms).
///
/// # Panics
///
/// Panics on a soundness bug: a congruence conflict whose explanation fails the
/// independent [`check_congruence`] re-check (which cannot happen for a correct
/// e-graph).
#[must_use]
pub fn prove_unsat_lazy(arena: &mut TermArena, assertions: &[TermId]) -> bool {
    // Distinct equality atoms over the whole assertion set.
    let mut atom_terms: Vec<TermId> = Vec::new();
    let mut seen = std::collections::HashSet::new();
    for &a in assertions {
        collect_eq_atoms(arena, a, &mut atom_terms, &mut seen);
    }
    if atom_terms.is_empty() {
        return false; // no equalities: congruence cannot prove anything
    }

    // A fresh Boolean variable per atom, and the boolean skeleton (atoms replaced
    // by their variables).
    let mut subst: HashMap<TermId, TermId> = HashMap::new();
    let mut atoms: Vec<(TermId, SymbolId)> = Vec::new();
    for (i, &atom) in atom_terms.iter().enumerate() {
        let sym = arena
            .declare(&format!("!euf_atom_{i}"), Sort::Bool)
            .expect("fresh atom symbol");
        let var = arena.var(sym);
        subst.insert(atom, var);
        atoms.push((atom, sym));
    }
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut skeleton: Vec<TermId> = assertions
        .iter()
        .map(|&a| replace_subterms(arena, a, &subst, &mut memo).expect("skeleton substitution"))
        .collect();

    loop {
        let mut backend = SatBvBackend::new();
        let result = backend.check(arena, &skeleton, &SolverConfig::default());
        match result {
            Ok(CheckResult::Unsat) => return true,
            Ok(CheckResult::Sat(model)) => {
                let Some(conflict_lits) = lazy_theory_check(arena, &atoms, &model) else {
                    return false; // theory-consistent boolean model: not proven UNSAT
                };
                // Block this assignment: negate the conjunction of the conflicting
                // atom literals.
                let blocking = build_blocking_clause(arena, &atoms, &conflict_lits);
                skeleton.push(blocking);
            }
            _ => return false, // unknown / unsupported boolean skeleton
        }
    }
}

/// Collects distinct equality subterms of `term`.
fn collect_eq_atoms(
    arena: &TermArena,
    term: TermId,
    out: &mut Vec<TermId>,
    seen: &mut std::collections::HashSet<TermId>,
) {
    if let TermNode::App { op, args } = arena.node(term) {
        if matches!(op, Op::Eq) && args.len() == 2 && seen.insert(term) {
            out.push(term);
        }
        let args = args.clone();
        for a in args {
            collect_eq_atoms(arena, a, out, seen);
        }
    }
}

/// Theory-checks a boolean model: asserts the true equality atoms into a fresh
/// e-graph and looks for a congruence conflict (a false equality whose sides are
/// congruent, or a constant clash). Returns the conflicting atom literals as
/// `(atom index, assigned value)` when inconsistent, else `None`.
fn lazy_theory_check(
    arena: &TermArena,
    atoms: &[(TermId, SymbolId)],
    model: &crate::model::Model,
) -> Option<Vec<(usize, bool)>> {
    use axeyum_ir::Value;

    let mut bridge = Bridge::new();
    // (s-node, t-node, assigned value) per atom.
    let mut eq_nodes: Vec<(ENodeId, ENodeId, bool)> = Vec::with_capacity(atoms.len());
    for &(eq_term, sym) in atoms {
        let TermNode::App { args, .. } = arena.node(eq_term) else {
            unreachable!("atom is an equality")
        };
        let (s, t) = (args[0], args[1]);
        let ns = bridge.node(arena, s);
        let nt = bridge.node(arena, t);
        let val = model.get(sym) == Some(Value::Bool(true));
        eq_nodes.push((ns, nt, val));
    }
    for (i, &(ns, nt, val)) in eq_nodes.iter().enumerate() {
        if val {
            bridge
                .egraph
                .merge(ns, nt, u32::try_from(i).expect("atom count fits u32"));
        }
    }
    // A false equality whose sides are congruent is a conflict.
    for (i, &(ns, nt, val)) in eq_nodes.iter().enumerate() {
        if !val && bridge.egraph.equal(ns, nt) {
            let mut lits = explain_as_true_lits(&bridge.egraph, &eq_nodes, ns, nt);
            lits.push((i, false));
            return Some(lits);
        }
    }
    // Two distinct constants forced congruent is a conflict.
    for i in 0..bridge.constants.len() {
        for j in (i + 1)..bridge.constants.len() {
            let (ci, cj) = (bridge.constants[i], bridge.constants[j]);
            if bridge.egraph.equal(ci, cj) {
                return Some(explain_as_true_lits(&bridge.egraph, &eq_nodes, ci, cj));
            }
        }
    }
    None
}

/// The equality atoms (all assigned true) that force `a = b`, as `(index, true)`
/// literals, after re-validating the explanation with the independent checker.
fn explain_as_true_lits(
    egraph: &EGraph,
    eq_nodes: &[(ENodeId, ENodeId, bool)],
    a: ENodeId,
    b: ENodeId,
) -> Vec<(usize, bool)> {
    let reasons = egraph.explain(a, b);
    let premises: Vec<(ENodeId, ENodeId)> = reasons
        .iter()
        .map(|&r| (eq_nodes[r as usize].0, eq_nodes[r as usize].1))
        .collect();
    assert!(
        check_congruence(egraph, &premises, a, b),
        "lazy congruence conflict failed the independent checker (soundness bug)"
    );
    reasons.iter().map(|&r| (r as usize, true)).collect()
}

/// Builds the blocking clause `¬(⋀ conflicting literals)`: for an atom assigned
/// true the clause gets `¬atom`, for one assigned false it gets `atom`.
fn build_blocking_clause(
    arena: &mut TermArena,
    atoms: &[(TermId, SymbolId)],
    conflict_lits: &[(usize, bool)],
) -> TermId {
    let mut clause: Option<TermId> = None;
    for &(idx, assigned) in conflict_lits {
        let var = arena.var(atoms[idx].1);
        let lit = if assigned {
            arena.not(var).expect("not of a boolean")
        } else {
            var
        };
        clause = Some(match clause {
            None => lit,
            Some(acc) => arena.or(acc, lit).expect("or of booleans"),
        });
    }
    clause.expect("a conflict has at least one literal")
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
    fn lazy_loop_refutes_a_disjunction() {
        // (a=b ∨ a=c) ∧ a≠b ∧ a≠c is UNSAT: both disjuncts contradict a diseq.
        // The conjunctive prover cannot see this (the ∨); the lazy loop can.
        let mut arena = TermArena::new();
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let c = arena.bv_var("c", 8).unwrap();
        let ab = arena.eq(a, b).unwrap();
        let ac = arena.eq(a, c).unwrap();
        let ab_or_ac = arena.or(ab, ac).unwrap();
        let a_ne_b = arena.not(ab).unwrap();
        let a_ne_c = arena.not(ac).unwrap();

        // The conjunctive prover misses it (the disjunction is not a definite atom).
        assert!(prove_unsat_by_congruence(&arena, &[ab_or_ac, a_ne_b, a_ne_c]).is_none());
        // The lazy loop proves it.
        assert!(prove_unsat_lazy(&mut arena, &[ab_or_ac, a_ne_b, a_ne_c]));
    }

    #[test]
    #[allow(clippy::similar_names)]
    fn lazy_loop_refutes_transitive_disjunction_with_functions() {
        // f(a)=f(b) is forced by a=b; (a=b) ∧ (f(a)≠f(c) ∨ f(b)≠f(c)) ∧ f(a)=f(c)
        // ∧ f(b)=f(c): unsat once congruence makes f(a)=f(b).
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let c = arena.bv_var("c", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let fc = arena.apply(f, &[c]).unwrap();
        let ab = arena.eq(a, b).unwrap();
        let fa_eq_fc0 = arena.eq(fa, fc).unwrap();
        let fa_ne_fc = arena.not(fa_eq_fc0).unwrap();
        let fb_eq_fc0 = arena.eq(fb, fc).unwrap();
        let fb_ne_fc = arena.not(fb_eq_fc0).unwrap();
        let disj = arena.or(fa_ne_fc, fb_ne_fc).unwrap();
        let fa_eq_fc = arena.eq(fa, fc).unwrap();
        let fb_eq_fc = arena.eq(fb, fc).unwrap();

        assert!(prove_unsat_lazy(
            &mut arena,
            &[ab, disj, fa_eq_fc, fb_eq_fc]
        ));
    }

    #[test]
    fn lazy_loop_does_not_claim_satisfiable_unsat() {
        // (a=b ∨ a=c): satisfiable; the lazy loop must not claim UNSAT.
        let mut arena = TermArena::new();
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let c = arena.bv_var("c", 8).unwrap();
        let ab = arena.eq(a, b).unwrap();
        let ac = arena.eq(a, c).unwrap();
        let disj = arena.or(ab, ac).unwrap();
        assert!(!prove_unsat_lazy(&mut arena, &[disj]));
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
