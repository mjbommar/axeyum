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

use std::collections::{HashMap, HashSet};

use axeyum_egraph::{EGraph, ENodeId, check_congruence};
use axeyum_ir::{
    Assignment, FuncId, FuncValue, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval,
};
use axeyum_rewrite::replace_subterms;

use crate::backend::{CheckResult, SolverBackend, SolverConfig};
use crate::model::Model;
use crate::sat_bv_backend::SatBvBackend;

/// A congruence conflict proving the assertions UNSAT: the subset of original
/// assertions that, under congruence, are contradictory.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EufConflict {
    /// Original assertion ids whose conjunction is UNSAT by congruence.
    pub core: Vec<TermId>,
}

/// A theory literal in an online CDCL(T) search: a registered atom index and the
/// polarity it is currently asserted with. The negation of a conflict's literal
/// conjunction is a theory lemma the SAT layer can learn.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TheoryLit {
    /// Index into the atoms the theory was constructed with.
    pub atom: usize,
    /// Whether the atom is asserted true or false.
    pub value: bool,
}

/// The online theory-solver interface a CDCL(T) loop drives (Track 1, P1.5): the
/// SAT search asserts theory atoms as its trail grows ([`Self::assert`]) and
/// backtracks in lockstep ([`Self::push`]/[`Self::pop`]); the theory answers with a
/// conflict — the asserted literals whose conjunction it refutes — or `Ok(())`.
///
/// This is the *online* counterpart to the offline [`prove_unsat_lazy`]
/// enumeration: instead of rebuilding the e-graph for each complete Boolean model,
/// the theory keeps one backtrackable [`EGraph`] in sync with the search.
pub trait TheorySolver {
    /// Asserts `atom` at `value`. Returns the conflicting literal set if the
    /// resulting theory state is inconsistent (so `¬⋀lits` is a valid lemma);
    /// otherwise `Ok(())`. Assertions accumulate until the next [`Self::pop`].
    ///
    /// # Errors
    ///
    /// Returns the conflicting literals when the assertion makes the theory state
    /// inconsistent.
    fn assert(&mut self, atom: usize, value: bool) -> Result<(), Vec<TheoryLit>>;
    /// Saves a backtrack point aligned with a SAT decision level.
    fn push(&mut self);
    /// Undoes every assertion back to the most recent [`Self::push`].
    fn pop(&mut self);
}

/// Online EUF theory solver over the backtrackable congruence-closure e-graph
/// (Track 1, P1.5). Atoms are equality atoms `(= s t)`: asserting one **true**
/// merges its sides — justified by the atom index, so [`EGraph::explain`]
/// reconstructs the conflict core — and asserting one **false** records a
/// disequality. A conflict is an asserted disequality whose sides have become
/// congruent, or two distinct literal constants forced equal. Non-equality atoms
/// register as no-ops, keeping atom indices aligned with the caller's Boolean
/// variable numbering.
pub struct EufTheory {
    bridge: Bridge,
    /// Per atom index: the e-nodes of its two sides, or `None` for a non-equality
    /// atom (asserting it is a congruence no-op).
    atoms: Vec<Option<(ENodeId, ENodeId)>>,
    /// Currently-asserted disequalities: (atom index, side a, side b).
    diseqs: Vec<(usize, ENodeId, ENodeId)>,
    /// Backtrack trail of `diseqs` lengths, one entry per [`EufTheory::push`].
    diseq_trail: Vec<usize>,
}

impl EufTheory {
    /// Builds an online EUF theory over the given atom terms. Each `(= s t)` atom
    /// registers its two sides' e-nodes; any other atom registers as a no-op so
    /// indices stay aligned with the caller's atom numbering.
    #[must_use]
    pub fn new(arena: &TermArena, atom_terms: &[TermId]) -> Self {
        let mut bridge = Bridge::new();
        let mut atoms = Vec::with_capacity(atom_terms.len());
        for &t in atom_terms {
            let sides = match arena.node(t) {
                TermNode::App { op: Op::Eq, args } if args.len() == 2 => {
                    let (l, r) = (args[0], args[1]);
                    let a = bridge.node(arena, l);
                    let b = bridge.node(arena, r);
                    Some((a, b))
                }
                _ => None,
            };
            atoms.push(sides);
        }
        Self {
            bridge,
            atoms,
            diseqs: Vec::new(),
            diseq_trail: Vec::new(),
        }
    }

    /// The first conflict in the current state: an asserted disequality whose sides
    /// are congruent, or two distinct constants merged into one class. The conflict
    /// is the asserted literals (recovered via [`EGraph::explain`]) whose
    /// conjunction is refuted.
    fn first_conflict(&self) -> Option<Vec<TheoryLit>> {
        // An asserted disequality whose sides are now congruent.
        for &(atom, a, b) in &self.diseqs {
            if self.bridge.egraph.equal(a, b) {
                let mut lits = self.explain_true(a, b);
                lits.push(TheoryLit { atom, value: false });
                return Some(lits);
            }
        }
        // Two distinct literal constants forced into the same class.
        let constants = &self.bridge.constants;
        for i in 0..constants.len() {
            for j in (i + 1)..constants.len() {
                if self.bridge.egraph.equal(constants[i], constants[j]) {
                    return Some(self.explain_true(constants[i], constants[j]));
                }
            }
        }
        None
    }

    /// The asserted-true literals (atom indices) explaining `a = b`.
    fn explain_true(&self, a: ENodeId, b: ENodeId) -> Vec<TheoryLit> {
        self.bridge
            .egraph
            .explain(a, b)
            .into_iter()
            .map(|reason| TheoryLit {
                atom: reason as usize,
                value: true,
            })
            .collect()
    }
}

impl TheorySolver for EufTheory {
    fn assert(&mut self, atom: usize, value: bool) -> Result<(), Vec<TheoryLit>> {
        let Some((a, b)) = self.atoms[atom] else {
            return Ok(()); // non-equality atom: nothing for congruence to do
        };
        if value {
            let reason = u32::try_from(atom).expect("atom index fits u32");
            self.bridge.egraph.merge(a, b, reason);
        } else {
            self.diseqs.push((atom, a, b));
        }
        match self.first_conflict() {
            Some(lits) => Err(lits),
            None => Ok(()),
        }
    }

    fn push(&mut self) {
        self.bridge.egraph.push();
        self.diseq_trail.push(self.diseqs.len());
    }

    fn pop(&mut self) {
        self.bridge.egraph.pop();
        if let Some(len) = self.diseq_trail.pop() {
            self.diseqs.truncate(len);
        }
    }
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

/// Decides a `QF_UF`(-equality) conjunction by the lazy DPLL(T) loop, returning a
/// **replay-checked** model on `sat`.
///
/// Like [`prove_unsat_lazy`] it abstracts equalities to Boolean atoms and searches;
/// on a theory-consistent boolean model it builds a candidate model from the
/// e-graph classes (each class a distinct value, literal constants their own value,
/// uninterpreted functions an interpretation consistent with congruence) and
/// **replays it against the original assertions**. The replay is the soundness
/// gate: a model that does not satisfy the originals (e.g. because the
/// uninterpreted abstraction missed base-sort semantics) yields
/// [`CheckResult::Unknown`], never a wrong `sat`. So this is a sound decider for
/// the equality-and-uninterpreted-function fragment and conservative elsewhere.
///
/// Mutates `arena` (fresh atom variables and blocking-clause terms).
///
/// # Panics
///
/// Panics on a soundness bug: a congruence conflict whose explanation fails the
/// independent [`check_congruence`] re-check (which cannot happen for a correct
/// e-graph).
#[must_use]
pub fn check_qf_uf(arena: &mut TermArena, assertions: &[TermId]) -> CheckResult {
    let mut atom_terms: Vec<TermId> = Vec::new();
    let mut seen = HashSet::new();
    for &a in assertions {
        collect_eq_atoms(arena, a, &mut atom_terms, &mut seen);
    }
    if atom_terms.is_empty() {
        return CheckResult::Unknown(unknown("no equality atoms for the e-graph path"));
    }

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
        match backend.check(arena, &skeleton, &SolverConfig::default()) {
            Ok(CheckResult::Unsat) => return CheckResult::Unsat,
            Ok(CheckResult::Sat(bool_model)) => {
                let (bridge, eq_nodes) = theory_state(arena, &atoms, &bool_model);
                if let Some(lits) = find_conflict(&bridge, &eq_nodes) {
                    let blocking = build_blocking_clause(arena, &atoms, &lits);
                    skeleton.push(blocking);
                    continue;
                }
                // Theory-consistent: build a candidate model and replay it.
                return match build_model(arena, &bridge) {
                    Some(model) if replays(arena, assertions, &model) => CheckResult::Sat(model),
                    _ => CheckResult::Unknown(unknown(
                        "e-graph model did not replay (base-sort semantics outside congruence)",
                    )),
                };
            }
            _ => return CheckResult::Unknown(unknown("boolean skeleton undecided")),
        }
    }
}

/// Constructs a candidate model from a theory-consistent e-graph: each class gets
/// a distinct value (a literal constant's value if it has one), symbols take their
/// class value, and each function gets an interpretation from its applications.
/// Returns `None` for sorts outside `Bool`/`BitVec(≤128)` (the caller treats that
/// as `Unknown`).
fn build_model(arena: &TermArena, bridge: &Bridge) -> Option<Model> {
    let mut class_width: HashMap<ENodeId, u32> = HashMap::new();
    for (&term, &node) in &bridge.term_to_node {
        let root = bridge.egraph.root(node);
        let width = match arena.sort_of(term) {
            Sort::Bool => 1,
            Sort::BitVec(w) if w <= 128 => w,
            _ => return None,
        };
        class_width.insert(root, width);
    }

    // Class codes: constants pin their class, the rest get fresh distinct codes.
    let mut class_code: HashMap<ENodeId, u128> = HashMap::new();
    let mut used: HashMap<u32, HashSet<u128>> = HashMap::new();
    for (&term, &node) in &bridge.term_to_node {
        if is_constant(arena.node(term)) {
            let root = bridge.egraph.root(node);
            let code = eval(arena, term, &Assignment::new()).ok()?.scalar_code();
            class_code.insert(root, code);
            used.entry(class_width[&root]).or_default().insert(code);
        }
    }
    for (&root, &width) in &class_width {
        if class_code.contains_key(&root) {
            continue;
        }
        let set = used.entry(width).or_default();
        let max = if width >= 128 {
            u128::MAX
        } else {
            (1u128 << width) - 1
        };
        let mut v = 0u128;
        while set.contains(&v) {
            if v == max {
                return None; // too many distinct classes for this width
            }
            v += 1;
        }
        set.insert(v);
        class_code.insert(root, v);
    }

    let mut model = Model::new();
    let mut tables: HashMap<FuncId, Vec<(Vec<u128>, u128)>> = HashMap::new();
    for (&term, &node) in &bridge.term_to_node {
        let code = class_code[&bridge.egraph.root(node)];
        match arena.node(term) {
            TermNode::Symbol(s) => {
                model.set(*s, value_from_code(arena.sort_of(term), code));
            }
            TermNode::App {
                op: Op::Apply(func),
                args,
            } => {
                let arg_codes: Vec<u128> = args
                    .iter()
                    .map(|&a| class_code[&bridge.egraph.root(bridge.term_to_node[&a])])
                    .collect();
                tables.entry(*func).or_default().push((arg_codes, code));
            }
            _ => {}
        }
    }
    for (func, entries) in tables {
        let (_, params, result) = arena.function(func);
        let mut fv = FuncValue::constant(params.to_vec(), result, 0);
        for (args, res) in entries {
            fv = fv.define(&args, res);
        }
        model.set_function(func, fv);
    }
    Some(model)
}

/// Whether a term node is a literal constant of any sort.
fn is_constant(node: &TermNode) -> bool {
    matches!(
        node,
        TermNode::BoolConst(_)
            | TermNode::BvConst { .. }
            | TermNode::WideBvConst(_)
            | TermNode::IntConst(_)
            | TermNode::RealConst(_)
    )
}

/// A [`Value`] of `sort` carrying the encoded `code`.
fn value_from_code(sort: Sort, code: u128) -> Value {
    match sort {
        Sort::Bool => Value::Bool(code != 0),
        Sort::BitVec(width) => {
            let mask = if width >= 128 {
                u128::MAX
            } else {
                (1u128 << width) - 1
            };
            Value::Bv {
                width,
                value: code & mask,
            }
        }
        _ => unreachable!("build_model filtered to Bool/BitVec"),
    }
}

/// Whether `model` satisfies every original assertion (the soundness gate for a
/// constructed `sat` model).
fn replays(arena: &TermArena, assertions: &[TermId], model: &Model) -> bool {
    let assignment = model.to_assignment();
    assertions
        .iter()
        .all(|&a| matches!(eval(arena, a, &assignment), Ok(Value::Bool(true))))
}

/// An [`UnknownReason`] for the e-graph path.
fn unknown(detail: &str) -> crate::backend::UnknownReason {
    crate::backend::UnknownReason {
        kind: crate::backend::UnknownKind::Other,
        detail: detail.to_owned(),
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

/// Builds the e-graph theory state for a boolean model: every equality atom's
/// sides as e-nodes (with the atom's assigned truth value), with the true
/// equalities merged in.
fn theory_state(
    arena: &TermArena,
    atoms: &[(TermId, SymbolId)],
    model: &Model,
) -> (Bridge, Vec<(ENodeId, ENodeId, bool)>) {
    let mut bridge = Bridge::new();
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
    (bridge, eq_nodes)
}

/// Looks for a congruence conflict in a theory state — a false equality whose
/// sides are congruent, or two distinct constants forced equal — returning the
/// conflicting atom literals `(index, assigned value)`, else `None` (consistent).
fn find_conflict(
    bridge: &Bridge,
    eq_nodes: &[(ENodeId, ENodeId, bool)],
) -> Option<Vec<(usize, bool)>> {
    for (i, &(ns, nt, val)) in eq_nodes.iter().enumerate() {
        if !val && bridge.egraph.equal(ns, nt) {
            let mut lits = explain_as_true_lits(&bridge.egraph, eq_nodes, ns, nt);
            lits.push((i, false));
            return Some(lits);
        }
    }
    for i in 0..bridge.constants.len() {
        for j in (i + 1)..bridge.constants.len() {
            let (ci, cj) = (bridge.constants[i], bridge.constants[j]);
            if bridge.egraph.equal(ci, cj) {
                return Some(explain_as_true_lits(&bridge.egraph, eq_nodes, ci, cj));
            }
        }
    }
    None
}

/// Theory-checks a boolean model, returning conflicting atom literals if
/// inconsistent (used by [`prove_unsat_lazy`]).
fn lazy_theory_check(
    arena: &TermArena,
    atoms: &[(TermId, SymbolId)],
    model: &Model,
) -> Option<Vec<(usize, bool)>> {
    let (bridge, eq_nodes) = theory_state(arena, atoms, model);
    find_conflict(&bridge, &eq_nodes)
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
    #[allow(clippy::many_single_char_names)]
    fn online_euf_detects_congruence_conflict_and_explains_it() {
        // Atoms: 0: a=b, 1: f(a)=f(b). Assert a=b true, f(a)=f(b) false.
        // Congruence forces f(a)=f(b), contradicting the disequality. The conflict
        // core must name atom 0 (true) and atom 1 (false) — the minimal lemma.
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let a_eq_b = arena.eq(a, b).unwrap();
        let fa_eq_fb = arena.eq(fa, fb).unwrap();

        let mut theory = EufTheory::new(&arena, &[a_eq_b, fa_eq_fb]);
        assert!(theory.assert(0, true).is_ok());
        let conflict = theory.assert(1, false).expect_err("congruence conflict");
        assert!(conflict.contains(&TheoryLit {
            atom: 0,
            value: true
        }));
        assert!(conflict.contains(&TheoryLit {
            atom: 1,
            value: false
        }));
    }

    #[test]
    fn online_euf_backtracks_a_merge_on_pop() {
        // After a=b is asserted and then popped, a≠b must no longer conflict —
        // the e-graph merge was undone in lockstep with the search.
        let mut arena = TermArena::new();
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let a_eq_b = arena.eq(a, b).unwrap();

        let mut theory = EufTheory::new(&arena, &[a_eq_b]);
        theory.push();
        assert!(theory.assert(0, true).is_ok());
        theory.pop();
        // a=b is gone; asserting a≠b (atom 0 false) is now consistent.
        assert!(theory.assert(0, false).is_ok());
    }

    #[test]
    fn online_euf_detects_distinct_constant_collision() {
        // x = 1 ∧ x = 2 forces the distinct constants 1 and 2 into one class.
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 8).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let two = arena.bv_const(8, 2).unwrap();
        let x_eq_1 = arena.eq(x, one).unwrap();
        let x_eq_2 = arena.eq(x, two).unwrap();

        let mut theory = EufTheory::new(&arena, &[x_eq_1, x_eq_2]);
        assert!(theory.assert(0, true).is_ok());
        let conflict = theory.assert(1, true).expect_err("1 = 2 is impossible");
        // Both equalities are needed to force the constant collision.
        assert!(conflict.contains(&TheoryLit {
            atom: 0,
            value: true
        }));
        assert!(conflict.contains(&TheoryLit {
            atom: 1,
            value: true
        }));
    }

    #[test]
    fn online_euf_transitivity_conflict_core_is_complete() {
        // a=b, b=c, a≠c: the disequality conflict must cite both equalities.
        let mut arena = TermArena::new();
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let c = arena.bv_var("c", 8).unwrap();
        let ab = arena.eq(a, b).unwrap();
        let bc = arena.eq(b, c).unwrap();
        let ac = arena.eq(a, c).unwrap();

        let mut theory = EufTheory::new(&arena, &[ab, bc, ac]);
        assert!(theory.assert(0, true).is_ok()); // a=b
        assert!(theory.assert(1, true).is_ok()); // b=c
        let conflict = theory.assert(2, false).expect_err("a≠c after a=b=c"); // a≠c
        assert!(conflict.contains(&TheoryLit {
            atom: 0,
            value: true
        }));
        assert!(conflict.contains(&TheoryLit {
            atom: 1,
            value: true
        }));
        assert!(conflict.contains(&TheoryLit {
            atom: 2,
            value: false
        }));
    }

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
    fn check_qf_uf_sat_model_replays() {
        // a=b ∧ f(a)=f(b): SAT; check_qf_uf must return a model that satisfies the
        // original assertions (the replay gate).
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let ab = arena.eq(a, b).unwrap();
        let fa_eq_fb = arena.eq(fa, fb).unwrap();
        let originals = [ab, fa_eq_fb];

        let CheckResult::Sat(model) = check_qf_uf(&mut arena, &originals) else {
            panic!("expected sat");
        };
        let assignment = model.to_assignment();
        for &asrt in &originals {
            assert_eq!(
                axeyum_ir::eval(&arena, asrt, &assignment).unwrap(),
                Value::Bool(true),
                "returned model must satisfy the original assertions"
            );
        }
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn check_qf_uf_decides_unsat_and_sat() {
        // UNSAT: a=b ∧ f(a)≠f(b).
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
        assert_eq!(check_qf_uf(&mut arena, &[ab, fa_ne_fb]), CheckResult::Unsat);

        // SAT: a disequality alone (distinct values exist).
        let mut arena2 = TermArena::new();
        let x = arena2.bv_var("x", 8).unwrap();
        let y = arena2.bv_var("y", 8).unwrap();
        let xy = arena2.eq(x, y).unwrap();
        let x_ne_y = arena2.not(xy).unwrap();
        assert!(matches!(
            check_qf_uf(&mut arena2, &[x_ne_y]),
            CheckResult::Sat(_)
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
