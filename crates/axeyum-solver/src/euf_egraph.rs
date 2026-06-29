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
use std::time::Instant;

use axeyum_egraph::{EGraph, ENodeId, check_congruence};
use axeyum_ir::{
    Assignment, FuncId, FuncValue, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval,
    well_founded_default,
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
    /// Sound theory propagation: the literals the theory entails under the current
    /// assertions, each with the asserted literals that force it (its explanation).
    /// A CDCL(T) loop can assign these without a decision. Only genuinely-entailed
    /// literals are emitted — an under-approximation that never fabricates one.
    fn propagate(&self) -> Vec<TheoryProp>;
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
    /// Per atom index: the value it is currently asserted at (`None` if unassigned).
    /// Lets [`EufTheory::propagate`] skip already-decided atoms.
    assigned: Vec<Option<bool>>,
    /// Atom indices assigned since the start, in order — the backtrack log for
    /// `assigned` (cleared back to a marker on [`EufTheory::pop`]).
    assigned_log: Vec<usize>,
    /// Currently-asserted disequalities: (atom index, side a, side b).
    diseqs: Vec<(usize, ENodeId, ENodeId)>,
    /// Backtrack trail: per [`EufTheory::push`], the `(diseqs, assigned_log)` lengths.
    trail: Vec<(usize, usize)>,
}

/// A sound theory propagation: a literal the theory entails under the current
/// assertions, with the asserted literals that force it (its explanation).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TheoryProp {
    /// The entailed literal.
    pub lit: TheoryLit,
    /// The asserted literals whose conjunction entails `lit`.
    pub reason: Vec<TheoryLit>,
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
        let n = atoms.len();
        Self {
            bridge,
            atoms,
            assigned: vec![None; n],
            assigned_log: Vec::new(),
            diseqs: Vec::new(),
            trail: Vec::new(),
        }
    }

    /// Sound EUF theory propagation: the unassigned equality atoms whose two sides
    /// are **already congruent** under the current assertions — each entailed
    /// `true`, with the explanation (the asserted equalities forcing the merge). A
    /// CDCL(T) loop can assign these without a decision. (Disequality entailment —
    /// an atom forced `false` — needs the fuller "distinct classes" analysis and is
    /// deferred.)
    #[must_use]
    pub fn propagate(&self) -> Vec<TheoryProp> {
        let mut out = Vec::new();
        for (atom, sides) in self.atoms.iter().enumerate() {
            if self.assigned[atom].is_some() {
                continue; // already decided by the search
            }
            let Some((a, b)) = *sides else { continue };
            if self.bridge.egraph.equal(a, b) {
                out.push(TheoryProp {
                    lit: TheoryLit { atom, value: true },
                    reason: self.explain_true(a, b),
                });
            }
        }
        out
    }

    /// Builds a candidate model from the current e-graph state — valid to call when
    /// the theory is **consistent** (no conflict), e.g. once a DPLL(T) search reaches
    /// a total, theory-consistent assignment. Each congruence class takes a distinct
    /// value (a literal constant keeps its own), symbols take their class value, and
    /// each function an interpretation from its applications. Returns `None` for a
    /// sort the model builder does not cover (the caller treats that as `unknown`).
    #[must_use]
    pub fn model(&self, arena: &TermArena) -> Option<Model> {
        build_model(arena, &self.bridge)
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
        // Record the assignment (even for non-equality atoms) so propagation and a
        // future re-assert are consistent; backtracked in lockstep on `pop`.
        if self.assigned[atom].is_none() {
            self.assigned[atom] = Some(value);
            self.assigned_log.push(atom);
        }
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
        self.trail
            .push((self.diseqs.len(), self.assigned_log.len()));
    }

    fn pop(&mut self) {
        self.bridge.egraph.pop();
        if let Some((diseq_len, assigned_len)) = self.trail.pop() {
            self.diseqs.truncate(diseq_len);
            while self.assigned_log.len() > assigned_len {
                if let Some(atom) = self.assigned_log.pop() {
                    self.assigned[atom] = None;
                }
            }
        }
    }

    fn propagate(&self) -> Vec<TheoryProp> {
        EufTheory::propagate(self)
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

/// Online DPLL(T) refutation for the `QF_UF` equality fragment (Track 1, P1.5):
/// a small self-contained CDCL-free DPLL search drives the **online** [`EufTheory`]
/// over the backtrackable congruence-closure e-graph, instead of the offline
/// SAT-then-recheck enumeration of [`prove_unsat_lazy`].
///
/// The assertions are Tseitin-encoded into a CNF skeleton whose atom variables are
/// the distinct equality atoms (registered with [`EufTheory`]) plus Boolean-sorted
/// leaves; auxiliary variables gate the Boolean connectives. A simple-scan DPLL
/// loop then explores assignments: each equality-atom assignment is mirrored into
/// the theory ([`EufTheory::assert`]), theory conflicts are learned as blocking
/// clauses, theory propagations ([`EufTheory::propagate`]) extend the trail, and the
/// theory is pushed/popped in lockstep with the decision levels.
///
/// Like [`prove_unsat_lazy`] this is a **sound, incomplete** prover with the *same*
/// uninterpreted abstraction, so the two must return the identical Boolean verdict:
/// it returns `true` only when it genuinely refutes the assertions, and `false`
/// (proved nothing) for a Boolean- and theory-consistent assignment or for any
/// skeleton it cannot encode. Mutates `arena` only by registering atoms in the
/// theory's bridge (no new terms are created).
#[must_use]
pub fn prove_unsat_qf_uf_online(arena: &mut TermArena, assertions: &[TermId]) -> bool {
    matches!(solve_qf_uf_online(arena, assertions), CheckResult::Unsat)
}

/// Decides the `QF_UF`(-equality) fragment by the **online DPLL(T)** loop, returning
/// a **replay-checked** model on `sat`. This is the decision-procedure form of
/// [`prove_unsat_qf_uf_online`]: the same online search (Tseitin skeleton + one
/// backtrackable [`EufTheory`]), but on a Boolean- and theory-consistent total
/// assignment it builds a candidate model from the e-graph classes
/// ([`EufTheory::model`]) and **replays it against the original assertions** — the
/// soundness gate, so a model the uninterpreted abstraction cannot justify (base-sort
/// semantics outside congruence) yields [`CheckResult::Unknown`], never a wrong
/// `sat`. `unsat` is a sound refutation (only ever returned at a root-level conflict).
///
/// Returns [`CheckResult::Unknown`] when there are no equality atoms or the Boolean
/// skeleton has structure the encoder does not cover (the same conservative
/// give-ups as the offline [`check_qf_uf`], leaving those to the bit-blaster).
///
/// Mutates `arena` only via the model builder's read path (no fresh symbols, unlike
/// the offline loop).
#[must_use]
pub fn solve_qf_uf_online(arena: &mut TermArena, assertions: &[TermId]) -> CheckResult {
    // Distinct equality atoms over the whole assertion set (these become the
    // theory's atom indices and the first variables 0..eq_count).
    let mut atom_terms: Vec<TermId> = Vec::new();
    let mut seen = HashSet::new();
    for &a in assertions {
        collect_eq_atoms(arena, a, &mut atom_terms, &mut seen);
    }
    if atom_terms.is_empty() {
        return CheckResult::Unknown(unknown("no equality atoms for the online e-graph path"));
    }

    // Variable map: each equality atom keeps its collected index; Boolean-sorted
    // leaves that surface as atoms get fresh indices after the equalities. The
    // theory is built over exactly `atom_terms`, so theory atom indices line up
    // with the first `atom_terms.len()` variables.
    let mut enc = Encoder::new(&atom_terms);
    let mut clauses: Vec<Vec<Lit>> = Vec::new();
    for &assertion in assertions {
        let Some(top) = enc.encode(arena, assertion, &mut clauses) else {
            // Un-encodable Boolean structure: conservative `unknown` (the bit-blaster
            // handles it), never a guess.
            return CheckResult::Unknown(unknown("boolean skeleton outside the online encoder"));
        };
        clauses.push(vec![Lit {
            var: top,
            positive: true,
        }]);
    }

    let eq_count = atom_terms.len();
    let mut theory = EufTheory::new(arena, &atom_terms);
    let mut solver = Dpll::new(enc.var_count, eq_count, clauses);
    if solver.solve(&mut theory) {
        return CheckResult::Unsat;
    }
    // The search ended on a theory-consistent total assignment: the theory's e-graph
    // holds that satisfying state. Build a model and replay it against the originals.
    match theory.model(arena) {
        Some(model) if replays(arena, assertions, &model) => CheckResult::Sat(model),
        _ => CheckResult::Unknown(unknown(
            "online e-graph model did not replay (base-sort semantics outside congruence)",
        )),
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
    check_qf_uf_with_config(arena, assertions, &SolverConfig::default())
}

/// Deadline-aware variant of [`check_qf_uf`]: the offline lazy-DPLL(T) refinement
/// loop and every inner [`SatBvBackend`] solve are bounded by `config.timeout`, so
/// the path degrades to `Unknown` under a deterministic resource bound (hard rule)
/// instead of running unbounded. With a `config` carrying no timeout the behaviour
/// is byte-identical to [`check_qf_uf`].
///
/// # Panics
///
/// Panics on a soundness bug: a congruence conflict whose explanation fails the
/// independent [`check_congruence`] re-check (which cannot happen for a correct
/// e-graph).
#[must_use]
pub fn check_qf_uf_with_config(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> CheckResult {
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

    let deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));
    loop {
        if deadline.is_some_and(|d| Instant::now() >= d) {
            return CheckResult::Unknown(unknown("timeout in the QF_UF e-graph refinement loop"));
        }
        // Hand each inner SAT solve the *remaining* time budget so it is itself
        // bounded (mirrors uflra_online's deadline threading).
        let inner_config = match deadline {
            Some(d) => {
                SolverConfig::default().with_timeout(d.saturating_duration_since(Instant::now()))
            }
            None => SolverConfig::default(),
        };
        let mut backend = SatBvBackend::new();
        match backend.check(arena, &skeleton, &inner_config) {
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
/// Returns `None` for sorts outside `Bool`/`BitVec(≤128)`/uninterpreted carriers
/// (the caller treats that as `Unknown`).
fn build_model(arena: &TermArena, bridge: &Bridge) -> Option<Model> {
    let mut class_sort: HashMap<ENodeId, Sort> = HashMap::new();
    for (&term, &node) in &bridge.term_to_node {
        let root = bridge.egraph.root(node);
        let sort = match arena.sort_of(term) {
            sort @ (Sort::Bool | Sort::Uninterpreted(_)) => sort,
            sort @ Sort::BitVec(w) if w <= 128 => sort,
            _ => return None,
        };
        if let Some(existing) = class_sort.insert(root, sort)
            && existing != sort
        {
            return None;
        }
    }

    // Class codes: constants pin their class, the rest get fresh distinct codes.
    let mut class_code: HashMap<ENodeId, u128> = HashMap::new();
    let mut used: HashMap<Sort, HashSet<u128>> = HashMap::new();
    for (&term, &node) in &bridge.term_to_node {
        if is_constant(arena.node(term)) {
            let root = bridge.egraph.root(node);
            let value = eval(arena, term, &Assignment::new()).ok()?;
            let code = euf_model_code(&value)?;
            class_code.insert(root, code);
            used.entry(class_sort[&root]).or_default().insert(code);
        }
    }
    for (&root, &sort) in &class_sort {
        if class_code.contains_key(&root) {
            continue;
        }
        let set = used.entry(sort).or_default();
        let max = match sort {
            Sort::Bool => 1,
            Sort::BitVec(width) if width >= 128 => u128::MAX,
            Sort::BitVec(width) => (1u128 << width) - 1,
            Sort::Uninterpreted(_) => u128::MAX,
            _ => return None,
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
        let use_value_storage = FuncValue::uses_value_storage_for(params, result);
        let mut fv = if use_value_storage {
            let default = well_founded_default(arena, result)?;
            FuncValue::constant_value(params.to_vec(), result, default)
        } else {
            FuncValue::constant(params.to_vec(), result, 0)
        };
        for (args, res) in entries {
            if use_value_storage {
                let arg_values: Vec<Value> = params
                    .iter()
                    .zip(args)
                    .map(|(&sort, code)| value_from_code(sort, code))
                    .collect();
                fv = fv.define_value(&arg_values, value_from_code(result, res));
            } else {
                fv = fv.define(&args, res);
            }
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
        Sort::BitVec(width) => Value::from_scalar_code(Sort::BitVec(width), code),
        Sort::Uninterpreted(sort) => Value::Uninterpreted { sort, value: code },
        _ => unreachable!("build_model filtered to Bool/BitVec"),
    }
}

fn euf_model_code(value: &Value) -> Option<u128> {
    match value {
        Value::WideBv(_) => None,
        _ => Some(value.scalar_code()),
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
        // Only equalities over a *data* sort (uninterpreted carrier / BV / …) are
        // theory atoms for the congruence closure. A Bool-sorted equality is an
        // `iff` — a logical connective the Boolean skeleton must keep verbatim, not
        // a congruence atom. Abstracting `iff` as an atom (and merging its Bool
        // operands as e-graph nodes) is the "base-sort semantics outside
        // congruence" confusion that makes the model fail to replay. We still
        // recurse into it to collect the *inner* data-sorted equality atoms.
        if matches!(op, Op::Eq)
            && args.len() == 2
            && !matches!(arena.sort_of(args[0]), Sort::Bool)
            && seen.insert(term)
        {
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

/// A CNF literal in the online DPLL(T) skeleton: a variable index and its polarity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Lit {
    var: usize,
    positive: bool,
}

impl Lit {
    fn negate(self) -> Self {
        Self {
            var: self.var,
            positive: !self.positive,
        }
    }
}

/// Tseitin encoder from the typed Boolean IR into a CNF skeleton. The first
/// `atom_index` variables are reserved for the equality atoms (numbered to match
/// [`EufTheory`]); Boolean-sorted leaves reuse those slots or take fresh indices,
/// and connective gates allocate fresh auxiliary variables.
struct Encoder {
    /// Variable index per already-encoded term (atoms and gates), so structurally
    /// shared subterms share a variable.
    term_var: HashMap<TermId, usize>,
    var_count: usize,
}

impl Encoder {
    fn new(atom_terms: &[TermId]) -> Self {
        let mut term_var = HashMap::new();
        for (i, &t) in atom_terms.iter().enumerate() {
            term_var.insert(t, i);
        }
        Self {
            term_var,
            var_count: atom_terms.len(),
        }
    }

    /// A fresh auxiliary variable index.
    fn fresh(&mut self) -> usize {
        let v = self.var_count;
        self.var_count += 1;
        v
    }

    /// Encodes the Boolean term `t` into `clauses`, returning the variable whose
    /// truth equals `t`, or `None` if `t` has Boolean-position structure outside the
    /// supported connectives (the caller then soundly gives up).
    fn encode(
        &mut self,
        arena: &TermArena,
        t: TermId,
        clauses: &mut Vec<Vec<Lit>>,
    ) -> Option<usize> {
        if let Some(&v) = self.term_var.get(&t) {
            return Some(v);
        }
        let v = match arena.node(t) {
            // A registered equality atom is handled by the map lookup above; a leaf
            // Boolean symbol becomes its own variable.
            TermNode::Symbol(_) if arena.sort_of(t) == Sort::Bool => self.fresh(),
            TermNode::BoolConst(b) => {
                let value = *b;
                let g = self.fresh();
                // Force g to the constant.
                clauses.push(vec![Lit {
                    var: g,
                    positive: value,
                }]);
                g
            }
            TermNode::App { op, args } => {
                let op = *op;
                let args = args.clone();
                self.encode_app(arena, op, &args, clauses)?
            }
            // Non-Boolean leaf at a Boolean position cannot be encoded.
            _ => return None,
        };
        self.term_var.insert(t, v);
        Some(v)
    }

    /// Encodes a connective application into a fresh gate variable with the standard
    /// Tseitin clauses. Returns `None` for an unsupported operator at Boolean
    /// position (e.g. `Op::Eq` over non-Boolean sides is already an atom; any other
    /// operator yielding a non-Boolean is a give-up).
    fn encode_app(
        &mut self,
        arena: &TermArena,
        op: Op,
        args: &[TermId],
        clauses: &mut Vec<Vec<Lit>>,
    ) -> Option<usize> {
        let lits: Vec<Lit> = args
            .iter()
            .map(|&a| {
                self.encode(arena, a, clauses).map(|var| Lit {
                    var,
                    positive: true,
                })
            })
            .collect::<Option<Vec<_>>>()?;
        let g = self.fresh();
        let gl = Lit {
            var: g,
            positive: true,
        };
        match (op, lits.as_slice()) {
            (Op::BoolNot, [a]) => {
                // g <-> ¬a
                clauses.push(vec![gl.negate(), a.negate()]);
                clauses.push(vec![gl, *a]);
            }
            (Op::BoolAnd, [a, b]) => {
                // g <-> a ∧ b
                clauses.push(vec![gl.negate(), *a]);
                clauses.push(vec![gl.negate(), *b]);
                clauses.push(vec![a.negate(), b.negate(), gl]);
            }
            (Op::BoolOr, [a, b]) => {
                // g <-> a ∨ b
                clauses.push(vec![gl, a.negate()]);
                clauses.push(vec![gl, b.negate()]);
                clauses.push(vec![gl.negate(), *a, *b]);
            }
            (Op::BoolImplies, [a, b]) => {
                // g <-> (¬a ∨ b)
                clauses.push(vec![gl, *a]);
                clauses.push(vec![gl, b.negate()]);
                clauses.push(vec![gl.negate(), a.negate(), *b]);
            }
            (Op::BoolXor, [a, b]) => {
                // g <-> a xor b
                clauses.push(vec![gl.negate(), *a, *b]);
                clauses.push(vec![gl.negate(), a.negate(), b.negate()]);
                clauses.push(vec![gl, a.negate(), *b]);
                clauses.push(vec![gl, *a, b.negate()]);
            }
            (Op::Ite, [c, x, y]) => {
                // g <-> (c ? x : y), over Boolean branches only.
                clauses.push(vec![c.negate(), x.negate(), gl]);
                clauses.push(vec![c.negate(), *x, gl.negate()]);
                clauses.push(vec![*c, y.negate(), gl]);
                clauses.push(vec![*c, *y, gl.negate()]);
            }
            _ => return None,
        }
        Some(g)
    }
}

/// How a variable came to be assigned, so backtracking can undo theory state and
/// (for theory propagations) chronological backtracking stays correct.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Cause {
    /// A branching decision; its level owns a theory `push`.
    Decision,
    /// Forced by unit propagation, a theory propagation, or a learned unit.
    Implied,
}

/// A conflict surfaced by propagation: the falsified clause to analyze, tagged
/// with whether it is a **theory** clause (a theory conflict `¬⋀core`, entailed by
/// the theory alone) or a Boolean input clause. The tag seeds the theory-lemma
/// provenance tracked through 1-UIP resolution.
struct Conflict {
    clause: Vec<Lit>,
    is_theory: bool,
}

/// A self-contained DPLL(T) search over the CNF skeleton, driving an [`EufTheory`]
/// online. **1-UIP** theory-conflict learning with non-chronological backjumping;
/// the theory is pushed on each decision and popped once per decision crossed when
/// backjumping, so its e-graph stays in lockstep with the trail. Mirrors
/// [`crate::lra_online`]'s `Dpll` retargeted to [`EufTheory`].
struct Dpll {
    var_count: usize,
    eq_count: usize,
    clauses: Vec<Vec<Lit>>,
    /// Current value per variable (`None` if unassigned).
    value: Vec<Option<bool>>,
    /// Trail of `(var, value, cause)` in assignment order.
    trail: Vec<(usize, bool, Cause)>,
    /// Per variable: the decision level it was assigned at (valid only while the
    /// variable is assigned).
    level: Vec<usize>,
    /// Per variable: the reason clause that forced it (a clause that, once all its
    /// other literals are false, propagates this variable). `None` for a decision.
    /// Valid only while the variable is assigned.
    reason: Vec<Option<Vec<Lit>>>,
    /// Per variable: whether its reason clause is a *theory* clause (a theory
    /// conflict `¬⋀core` or a theory propagation `¬reason ∨ lit`, both entailed by
    /// the theory alone) rather than a Boolean input clause. A 1-UIP clause resolved
    /// only through theory clauses is itself a theory lemma — the test gate uses this
    /// to pick clauses it can independently re-validate with the trusted congruence
    /// checker.
    reason_theory: Vec<bool>,
    /// The current decision level (incremented on every decision, restored on
    /// backjump).
    decision_level: usize,
    /// Test-only diagnostics for the 1-UIP path (fires counter and learned-vs-full
    /// conflict-clause lengths). Compiled out of the production library.
    #[cfg(test)]
    diag: Diagnostics,
}

/// Test-only counters proving the 1-UIP analysis fires and that its asserting
/// clauses are shorter than the full `¬⋀core` clause the old chronological scheme
/// would have learned.
#[cfg(test)]
#[derive(Default)]
struct Diagnostics {
    /// The number of 1-UIP analyses run.
    analyze_fires: usize,
    /// Summed length of every learned asserting clause.
    learned_len_total: u64,
    /// Summed length of the corresponding full conflict clause (`¬⋀core`).
    conflict_len_total: u64,
    /// The number of clauses present before any learning (the encoded skeleton);
    /// every clause at or after this index is a learned 1-UIP asserting clause.
    initial_clauses: usize,
    /// Per stored learned clause (aligned with `clauses[initial_clauses..]`):
    /// whether it is a pure theory lemma (entailed by the theory plus the level-0
    /// facts), so the test gate can re-validate it with the congruence checker.
    lemma_flags: Vec<bool>,
}

impl Dpll {
    fn new(var_count: usize, eq_count: usize, clauses: Vec<Vec<Lit>>) -> Self {
        #[cfg(test)]
        let diag = Diagnostics {
            initial_clauses: clauses.len(),
            ..Diagnostics::default()
        };
        Self {
            var_count,
            eq_count,
            clauses,
            value: vec![None; var_count],
            trail: Vec::new(),
            level: vec![0; var_count],
            reason: vec![None; var_count],
            reason_theory: vec![false; var_count],
            decision_level: 0,
            #[cfg(test)]
            diag,
        }
    }

    fn lit_sat(&self, lit: Lit) -> Option<bool> {
        self.value[lit.var].map(|v| v == lit.positive)
    }

    /// The literal currently true for `var` (its trail polarity).
    fn true_literal(&self, var: usize) -> Lit {
        Lit {
            var,
            positive: self.value[var].expect("assigned variable has a value"),
        }
    }

    /// Assigns `var := value` at the current decision level, recording its level and
    /// reason and mirroring an equality atom into the theory. `reason` is the forcing
    /// clause for a propagation, `None` for a decision. Returns the theory conflict if
    /// the assertion is inconsistent.
    fn assign(
        &mut self,
        theory: &mut EufTheory,
        var: usize,
        value: bool,
        cause: Cause,
        reason: Option<Vec<Lit>>,
        reason_is_theory: bool,
    ) -> Result<(), Vec<TheoryLit>> {
        self.value[var] = Some(value);
        self.level[var] = self.decision_level;
        self.reason[var] = reason;
        self.reason_theory[var] = reason_is_theory;
        self.trail.push((var, value, cause));
        if var < self.eq_count {
            theory.assert(var, value)?;
        }
        Ok(())
    }

    /// Boolean unit propagation to fixpoint over the current clauses. Returns `Err`
    /// with a falsified conflict clause (literals all currently false) on a Boolean
    /// conflict, or a learned theory-conflict clause on a forced theory inconsistency
    /// — tagged with which. `Ok(())` at a (Boolean-)consistent fixpoint.
    fn unit_propagate(&mut self, theory: &mut EufTheory) -> Result<(), Conflict> {
        let mut changed = true;
        while changed {
            changed = false;
            for ci in 0..self.clauses.len() {
                let mut unassigned: Option<Lit> = None;
                let mut satisfied = false;
                let mut count = 0;
                for &lit in &self.clauses[ci] {
                    match self.lit_sat(lit) {
                        Some(true) => {
                            satisfied = true;
                            break;
                        }
                        Some(false) => {}
                        None => {
                            unassigned = Some(lit);
                            count += 1;
                        }
                    }
                }
                if satisfied {
                    continue;
                }
                if count == 0 {
                    // The whole clause is falsified: a Boolean conflict clause.
                    return Err(Conflict {
                        clause: self.clauses[ci].clone(),
                        is_theory: false,
                    });
                }
                if count == 1 {
                    let lit = unassigned.expect("count == 1 has the unit literal");
                    // The reason for `lit` is this clause itself: once its other
                    // literals are false, it forces `lit`.
                    let reason = self.clauses[ci].clone();
                    if let Err(core) = self.assign(
                        theory,
                        lit.var,
                        lit.positive,
                        Cause::Implied,
                        Some(reason),
                        false,
                    ) {
                        return Err(Conflict {
                            clause: Self::theory_conflict_clause(&core),
                            is_theory: true,
                        });
                    }
                    changed = true;
                }
            }
        }
        Ok(())
    }

    /// Applies sound theory propagations to the trail until fixpoint. Returns the
    /// learned theory-conflict clause on a theory conflict, else `Ok(())`.
    fn theory_propagate(&mut self, theory: &mut EufTheory) -> Result<(), Conflict> {
        loop {
            let props = theory.propagate();
            let mut progress = false;
            for prop in props {
                let var = prop.lit.atom;
                match self.value[var] {
                    Some(v) if v == prop.lit.value => {}
                    Some(_) => {
                        // Theory entails the opposite of the current value: a
                        // conflict. Learn ¬(reason ∧ current literal).
                        let mut core = prop.reason.clone();
                        core.push(TheoryLit {
                            atom: var,
                            value: !prop.lit.value,
                        });
                        return Err(Conflict {
                            clause: Self::theory_conflict_clause(&core),
                            is_theory: true,
                        });
                    }
                    None => {
                        // The reason clause for the propagated literal is
                        // `¬(reason) ∨ lit`: once every reason literal (the asserted
                        // equalities the congruence `explain` returned) is asserted,
                        // this clause forces `lit`.
                        let reason_clause = Self::theory_reason_clause(&prop.reason, prop.lit);
                        if let Err(c) = self.assign(
                            theory,
                            var,
                            prop.lit.value,
                            Cause::Implied,
                            Some(reason_clause),
                            true,
                        ) {
                            return Err(Conflict {
                                clause: Self::theory_conflict_clause(&c),
                                is_theory: true,
                            });
                        }
                        progress = true;
                    }
                }
            }
            if !progress {
                return Ok(());
            }
        }
    }

    /// Maps a theory conflict core to a learned CNF conflict clause `¬⋀core` (every
    /// literal currently false, so it is the falsified clause to analyze): the
    /// disjunction of the negated core literals, each over the matching atom variable.
    fn theory_conflict_clause(core: &[TheoryLit]) -> Vec<Lit> {
        core.iter()
            .map(|l| Lit {
                var: l.atom,
                positive: !l.value,
            })
            .collect()
    }

    /// The reason clause for a theory propagation `reason ⊨ lit`, namely
    /// `¬(reason) ∨ lit`: each reason literal contributes its negation, plus the
    /// propagated literal. Once every reason literal is asserted, this clause is unit
    /// and forces `lit` — the invariant [`Self::analyze_conflict`] relies on.
    fn theory_reason_clause(reason: &[TheoryLit], lit: TheoryLit) -> Vec<Lit> {
        let mut clause: Vec<Lit> = reason
            .iter()
            .map(|l| Lit {
                var: l.atom,
                positive: !l.value,
            })
            .collect();
        clause.push(Lit {
            var: lit.atom,
            positive: lit.value,
        });
        clause
    }

    /// 1-UIP conflict analysis: resolves the falsified `conflict` clause against the
    /// reason clauses of current-decision-level literals (newest-first on the trail)
    /// until a single current-level literal — the first UIP — remains. Returns the
    /// asserting clause (the UIP literal at index 0, the lower-level literals after
    /// it), the backjump level (the second-highest decision level among the clause's
    /// literals, `0` if it has none), and whether the clause is a pure **theory
    /// lemma** — derived by resolving only theory clauses (the seed conflict and
    /// every resolved reason were theory clauses), so it is entailed by the theory
    /// alone. A mirror of `axeyum_cnf::proof_sat`'s `analyze`, without the
    /// VSIDS/LBD/minimization machinery (kept deliberately minimal for the online
    /// theory loop).
    fn analyze_conflict(&self, conflict: &[Lit], seed_is_theory: bool) -> (Vec<Lit>, usize, bool) {
        let mut seen = vec![false; self.var_count];
        let mut lower: Vec<Lit> = Vec::new();
        let mut path_count = 0_usize;
        let mut pivot: Option<usize> = None;
        let mut index = self.trail.len();
        let current = self.decision_level;
        let mut all_theory = seed_is_theory;
        // Seed the worklist with the falsified conflict clause; afterwards each
        // iteration resolves against the popped literal's reason clause.
        let mut clause: Vec<Lit> = conflict.to_vec();

        loop {
            for lit in &clause {
                let v = lit.var;
                if Some(v) == pivot || seen[v] || self.level[v] == 0 {
                    continue;
                }
                seen[v] = true;
                if self.level[v] >= current {
                    path_count += 1;
                } else {
                    lower.push(*lit);
                }
            }

            // Walk the trail newest-first for the next seen variable.
            let mut found = false;
            while index > 0 {
                index -= 1;
                if seen[self.trail[index].0] {
                    found = true;
                    break;
                }
            }
            if !found {
                // The conflict is implied at level 0: the empty asserting clause.
                return (Vec::new(), 0, all_theory);
            }

            let var = self.trail[index].0;
            seen[var] = false;
            path_count -= 1;
            pivot = Some(var);

            if path_count == 0 {
                // `var` is the 1-UIP. The asserting literal is the negation of its
                // trail polarity (the clause forces it the opposite way after the
                // backjump).
                let mut learned = Vec::with_capacity(lower.len() + 1);
                learned.push(self.true_literal(var).negate());
                learned.extend(lower);
                let backjump = Self::backjump_level(&self.level, &learned);
                return (learned, backjump, all_theory);
            }

            // Resolve against the reason clause of the next current-level literal;
            // the result is a theory lemma only if that reason is also a theory
            // clause.
            all_theory = all_theory && self.reason_theory[var];
            clause.clone_from(
                self.reason[var]
                    .as_ref()
                    .expect("a current-level implied literal has a reason clause"),
            );
        }
    }

    /// The backjump level of an asserting clause: the second-highest decision level
    /// among its literals (the asserting literal at index 0 sits at the highest
    /// level), or `0` for a unit asserting clause.
    fn backjump_level(level: &[usize], learned: &[Lit]) -> usize {
        learned
            .iter()
            .skip(1)
            .map(|lit| level[lit.var])
            .max()
            .unwrap_or(0)
    }

    /// Backjumps to `target_level`: pops every trail entry strictly above it,
    /// unassigning each variable and popping the theory **once per decision crossed**
    /// (the theory was pushed once per decision, so this keeps the push/pop stack in
    /// lockstep).
    fn backjump_to(&mut self, theory: &mut EufTheory, target_level: usize) {
        while let Some(&(var, _, _)) = self.trail.last() {
            if self.level[var] <= target_level {
                break;
            }
            let (var, _, cause) = self.trail.pop().expect("non-empty trail");
            self.value[var] = None;
            self.reason[var] = None;
            self.reason_theory[var] = false;
            if cause == Cause::Decision {
                theory.pop();
            }
        }
        self.decision_level = target_level;
    }

    /// The lowest-index unassigned variable, or `None` when the assignment is total.
    fn pick_unassigned(&self) -> Option<usize> {
        (0..self.var_count).find(|&v| self.value[v].is_none())
    }

    /// Runs the DPLL(T) search. Returns `true` iff the skeleton is UNSAT under the
    /// theory (a proof of UNSAT), `false` on a Boolean- and theory-consistent total
    /// assignment.
    fn solve(&mut self, theory: &mut EufTheory) -> bool {
        loop {
            match self.propagate(theory) {
                Ok(()) => {}
                Err(conflict) => {
                    if !self.learn_and_backjump(theory, &conflict) {
                        return true; // exhausted under a conflict: UNSAT
                    }
                    continue;
                }
            }
            match self.pick_unassigned() {
                None => return false, // total, consistent assignment: not UNSAT
                Some(var) => {
                    self.decision_level += 1;
                    theory.push();
                    if let Err(core) = self.assign(theory, var, true, Cause::Decision, None, false)
                    {
                        let conflict = Conflict {
                            clause: Self::theory_conflict_clause(&core),
                            is_theory: true,
                        };
                        if !self.learn_and_backjump(theory, &conflict) {
                            return true;
                        }
                    }
                }
            }
        }
    }

    /// Unit propagation interleaved with theory propagation to a joint fixpoint.
    fn propagate(&mut self, theory: &mut EufTheory) -> Result<(), Conflict> {
        loop {
            self.unit_propagate(theory)?;
            let before = self.trail.len();
            self.theory_propagate(theory)?;
            if self.trail.len() == before {
                return Ok(());
            }
        }
    }

    /// Handles a conflict by 1-UIP analysis: learns the asserting clause, jumps
    /// non-chronologically to the backjump level, and enqueues the UIP literal as an
    /// implied assignment with the learned clause as its reason. `false` when the
    /// conflict is implied at level 0 (UNSAT) — there is nothing to assert.
    fn learn_and_backjump(&mut self, theory: &mut EufTheory, conflict: &Conflict) -> bool {
        let (learned, backjump, is_theory_lemma) =
            self.analyze_conflict(&conflict.clause, conflict.is_theory);
        #[cfg(test)]
        {
            self.diag.analyze_fires += 1;
            self.diag.conflict_len_total +=
                u64::try_from(conflict.clause.len()).expect("clause length fits u64");
        }
        if learned.is_empty() {
            return false; // exhausted: UNSAT
        }
        #[cfg(test)]
        {
            // Only non-empty learned clauses are stored in `clauses`; keep the
            // length-total and lemma-flag streams aligned with that storage.
            self.diag.learned_len_total +=
                u64::try_from(learned.len()).expect("clause length fits u64");
            self.diag.lemma_flags.push(is_theory_lemma);
        }
        self.backjump_to(theory, backjump);
        let uip = learned[0];
        let reason = if learned.len() == 1 {
            None
        } else {
            Some(learned.clone())
        };
        self.clauses.push(learned);
        // Enqueue the UIP literal. At the backjump level its theory assertion is
        // consistent (the asserting clause is an entailed resolvent), but a *theory*
        // conflict can still surface here — re-analyze that conflict. The learned
        // clause is the UIP's reason, a theory clause iff it is a theory lemma.
        match self.assign(
            theory,
            uip.var,
            uip.positive,
            Cause::Implied,
            reason,
            is_theory_lemma,
        ) {
            Ok(()) => true,
            Err(core) => self.learn_and_backjump(
                theory,
                &Conflict {
                    clause: Self::theory_conflict_clause(&core),
                    is_theory: true,
                },
            ),
        }
    }
}

/// Test-only diagnostic run of the online EUF driver over `assertions`: returns the
/// registered equality-atom terms, the atom count, the learned 1-UIP asserting
/// clauses, the per-clause theory-lemma flags, and the fires/length diagnostics.
/// Mirrors the setup of [`solve_qf_uf_online`]. Used by the in-source soundness test
/// to confirm each learned theory-lemma clause is entailed (its negation is
/// congruence-UNSAT) and that 1-UIP fired and shrank the learned clauses below the
/// full conflict cores.
#[cfg(test)]
struct OnlineDiag {
    atom_terms: Vec<TermId>,
    atom_count: usize,
    learned: Vec<Vec<Lit>>,
    lemma_flags: Vec<bool>,
    analyze_fires: usize,
    learned_len_total: u64,
    conflict_len_total: u64,
}

#[cfg(test)]
fn run_online_diag(arena: &TermArena, assertions: &[TermId]) -> Option<OnlineDiag> {
    let mut atom_terms: Vec<TermId> = Vec::new();
    let mut seen = HashSet::new();
    for &a in assertions {
        collect_eq_atoms(arena, a, &mut atom_terms, &mut seen);
    }
    if atom_terms.is_empty() {
        return None;
    }
    let mut enc = Encoder::new(&atom_terms);
    let mut clauses: Vec<Vec<Lit>> = Vec::new();
    for &assertion in assertions {
        let top = enc.encode(arena, assertion, &mut clauses)?;
        clauses.push(vec![Lit {
            var: top,
            positive: true,
        }]);
    }
    let atom_count = atom_terms.len();
    let mut theory = EufTheory::new(arena, &atom_terms);
    let mut solver = Dpll::new(enc.var_count, atom_count, clauses);
    let _ = solver.solve(&mut theory);
    let learned = solver.clauses[solver.diag.initial_clauses..].to_vec();
    debug_assert_eq!(
        learned.len(),
        solver.diag.lemma_flags.len(),
        "one lemma flag per stored learned clause"
    );
    Some(OnlineDiag {
        atom_terms,
        atom_count,
        learned,
        lemma_flags: solver.diag.lemma_flags,
        analyze_fires: solver.diag.analyze_fires,
        learned_len_total: solver.diag.learned_len_total,
        conflict_len_total: solver.diag.conflict_len_total,
    })
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

    /// Whether the conjunction of equality literals `lits` (each `(atom_term, value)`,
    /// `value=true` meaning the equality holds, `false` a disequality) is UNSAT by
    /// congruence: asserts them into a fresh [`EufTheory`] and reports whether any
    /// assertion conflicts. The independent EUF oracle for the learned-clause gate.
    fn congruence_unsat(arena: &TermArena, atom_terms: &[TermId], lits: &[(usize, bool)]) -> bool {
        let mut theory = EufTheory::new(arena, atom_terms);
        for &(atom, value) in lits {
            if theory.assert(atom, value).is_err() {
                return true;
            }
        }
        false
    }

    /// SOUNDNESS gate for **1-UIP theory-conflict learning** (the EUF mirror): over
    /// two deterministic UNSAT families (a pigeonhole family that forces deep,
    /// multi-level branching, and a transitivity-chain family whose theory
    /// propagation makes 1-UIP resolution strictly shorten the clause), drive the
    /// online driver and, for EVERY learned asserting clause that is a pure theory
    /// lemma over atom-only literals, independently verify with the trusted
    /// congruence checker that the clause is *entailed* — i.e. `¬clause` (every
    /// literal asserted at its falsifying polarity) is congruence-UNSAT. A learned
    /// clause that isn't implied is a hard failure (an unsound lemma would corrupt
    /// the search). Also proves the 1-UIP path FIRES and that learned clauses are
    /// strictly SHORTER on average than the full `¬⋀core` conflict clauses the old
    /// chronological scheme learned.
    #[test]
    #[allow(clippy::many_single_char_names)]
    fn learned_clauses_are_entailed_and_shorter() {
        let mut fires_total = 0_usize;
        let mut learned_len_total = 0_u64;
        let mut conflict_len_total = 0_u64;
        let mut clauses_checked = 0_usize;

        // Accumulates the diagnostics and re-validates every theory-lemma clause.
        let mut absorb = |arena: &TermArena, assertions: &[TermId]| {
            let Some(diag) = run_online_diag(arena, assertions) else {
                return;
            };
            fires_total += diag.analyze_fires;
            learned_len_total += diag.learned_len_total;
            conflict_len_total += diag.conflict_len_total;
            for (clause, &is_lemma) in diag.learned.iter().zip(&diag.lemma_flags) {
                // Only PURE THEORY LEMMAS are entailed by the theory alone — a 1-UIP
                // clause that resolved through Boolean input clauses is entailed by
                // formula+theory, not the theory. Restrict to atom-only lemma clauses.
                if !is_lemma || clause.iter().any(|l| l.var >= diag.atom_count) {
                    continue;
                }
                // ¬clause: every clause literal falsified (atom `var` at `!positive`)
                // must be congruence-UNSAT.
                let neg: Vec<(usize, bool)> = clause.iter().map(|l| (l.var, !l.positive)).collect();
                assert!(
                    congruence_unsat(arena, &diag.atom_terms, &neg),
                    "UNSOUND LEARNED CLAUSE: ¬clause is congruence-SAT\nclause={clause:?}\n\
                     assertions={assertions:?}"
                );
                clauses_checked += 1;
            }
        };

        // (1) A transitivity-resolution family whose conflict CORE is longer than its
        // 1-UIP asserting clause: chain equalities x0=x1, …, x_{m-1}=xm are unit
        // facts that theory-PROPAGATE x0=xm; a disjunction then forces a decision that
        // collides with x0=xm. Analyzing the conflict resolves through the propagated
        // literal's reason (the whole chain) — but the 1-UIP clause keeps only the
        // single decision literal, strictly shorter than the full chain core.
        for m in 3..7usize {
            let mut arena = TermArena::new();
            let xs: Vec<TermId> = (0..=m)
                .map(|i| arena.bv_var(&format!("x{i}"), 8).unwrap())
                .collect();
            // Unit chain x_{i} = x_{i+1}.
            let mut assertions: Vec<TermId> = (0..m)
                .map(|i| arena.eq(xs[i], xs[i + 1]).unwrap())
                .collect();
            // The collision atom x0 = xm, and a disjunction forcing it false while
            // another (independently false) literal is the only alternative, so the
            // search must set x0 ≠ xm and conflict against the propagated x0 = xm.
            let x0_xm = arena.eq(xs[0], xs[m]).unwrap();
            let ne_x0_xm = arena.not(x0_xm).unwrap();
            let extra = arena.eq(xs[0], xs[1]).unwrap(); // already forced true
            let ne_extra = arena.not(extra).unwrap();
            // (x0 ≠ xm ∨ ¬extra): with extra forced true, this forces x0 ≠ xm, which
            // congruence refutes — a deep theory conflict resolving the chain.
            let disj = arena.or(ne_x0_xm, ne_extra).unwrap();
            assertions.push(disj);
            absorb(&arena, &assertions);
        }

        // (2) A parametric **pigeonhole** UNSAT family that guarantees deep,
        // multi-level theory conflicts (so the loop learns NON-empty 1-UIP asserting
        // clauses): n pigeons each forced (by a disjunction) to equal one of k < n
        // distinct holes, with the holes pairwise distinct literal constants. The
        // search must branch on the per-pigeon hole choices and refute every
        // assignment by a congruence collision, exercising real backjump learning.
        for shape in 0..120_u64 {
            let n = 3 + usize::try_from(shape % 3).unwrap(); // 3..=5 pigeons
            let k = n - 1 - usize::try_from((shape / 3) % 2).unwrap(); // k = n-1 or n-2
            let mut arena = TermArena::new();
            let holes: Vec<TermId> = (0..k)
                .map(|h| arena.bv_const(8, u128::try_from(h).unwrap()).unwrap())
                .collect();
            let pigeons: Vec<TermId> = (0..n)
                .map(|p| arena.bv_var(&format!("p{p}"), 8).unwrap())
                .collect();
            // Each pigeon p: (p = hole0 ∨ p = hole1 ∨ … ∨ p = hole_{k-1}).
            let assertions: Vec<TermId> = pigeons
                .iter()
                .map(|&p| {
                    let mut disj: Option<TermId> = None;
                    for &h in &holes {
                        let eq = arena.eq(p, h).unwrap();
                        disj = Some(match disj {
                            None => eq,
                            Some(acc) => arena.or(acc, eq).unwrap(),
                        });
                    }
                    disj.expect("k >= 1")
                })
                .collect();
            absorb(&arena, &assertions);
        }

        eprintln!(
            "EUF 1-UIP gate: fires={fires_total}, clauses_checked={clauses_checked}, \
             learned_len_total={learned_len_total}, conflict_len_total={conflict_len_total}"
        );
        assert!(fires_total > 50, "1-UIP analysis never meaningfully fired");
        assert!(
            clauses_checked > 20,
            "too few learned clauses entailment-checked ({clauses_checked})"
        );
        // The improvement metric: 1-UIP asserting clauses are strictly SHORTER on
        // average than the full `¬⋀core` conflict clauses — the transitivity family's
        // chain-resolution conflicts contribute clauses strictly below their cores
        // (the pigeonhole family's direct constant collisions contribute equal-length
        // clauses), so the sum is strictly less overall.
        assert!(
            learned_len_total < conflict_len_total,
            "learned clauses not shorter on average ({learned_len_total} vs {conflict_len_total})"
        );
    }

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
    #[allow(clippy::many_single_char_names)]
    fn online_euf_propagates_entailed_equalities() {
        // Atoms: 0:a=b, 1:b=c, 2:a=c, 3:f(a)=f(c). Assert a=b and b=c. Congruence
        // then entails a=c (atom 2) and f(a)=f(c) (atom 3) — both unassigned — and
        // propagation must surface them with the equalities that force them.
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let c = arena.bv_var("c", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fc = arena.apply(f, &[c]).unwrap();
        let ab = arena.eq(a, b).unwrap();
        let bc = arena.eq(b, c).unwrap();
        let ac = arena.eq(a, c).unwrap();
        let fa_eq_fc = arena.eq(fa, fc).unwrap();

        let mut theory = EufTheory::new(&arena, &[ab, bc, ac, fa_eq_fc]);
        assert!(theory.propagate().is_empty(), "nothing entailed yet");
        assert!(theory.assert(0, true).is_ok());
        assert!(theory.assert(1, true).is_ok());

        let props = theory.propagate();
        let lits: Vec<TheoryLit> = props.iter().map(|p| p.lit).collect();
        assert!(
            lits.contains(&TheoryLit {
                atom: 2,
                value: true
            }),
            "a=c must be propagated"
        );
        assert!(
            lits.contains(&TheoryLit {
                atom: 3,
                value: true
            }),
            "f(a)=f(c) must be propagated by congruence"
        );
        // The already-asserted equalities are not re-propagated.
        assert!(!lits.contains(&TheoryLit {
            atom: 0,
            value: true
        }));
        // a=c is justified by exactly the two asserted equalities.
        let ac_prop = props.iter().find(|p| p.lit.atom == 2).unwrap();
        assert!(ac_prop.reason.contains(&TheoryLit {
            atom: 0,
            value: true
        }));
        assert!(ac_prop.reason.contains(&TheoryLit {
            atom: 1,
            value: true
        }));

        // After popping both asserts, nothing is entailed again.
        theory.push(); // (no-op marker so the asserts below pop cleanly in a real loop)
        theory.pop();
    }

    #[test]
    fn online_euf_propagation_retracts_on_backtrack() {
        // a=b entails f(a)=f(b); popping the a=b decision must retract that.
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let ab = arena.eq(a, b).unwrap();
        let fa_eq_fb = arena.eq(fa, fb).unwrap();

        let mut theory = EufTheory::new(&arena, &[ab, fa_eq_fb]);
        theory.push();
        assert!(theory.assert(0, true).is_ok());
        assert!(
            theory.propagate().iter().any(|p| p.lit
                == TheoryLit {
                    atom: 1,
                    value: true
                }),
            "f(a)=f(b) entailed while a=b holds"
        );
        theory.pop();
        assert!(
            theory.propagate().is_empty(),
            "entailment retracted once a=b is backtracked"
        );
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

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn prove_unsat_qf_uf_online_refutes_a_disjunction() {
        // (a=b ∨ a=c) ∧ a≠b ∧ a≠c is UNSAT; the online loop must prove it.
        let mut arena = TermArena::new();
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let c = arena.bv_var("c", 8).unwrap();
        let ab = arena.eq(a, b).unwrap();
        let ac = arena.eq(a, c).unwrap();
        let ab_or_ac = arena.or(ab, ac).unwrap();
        let a_ne_b = arena.not(ab).unwrap();
        let a_ne_c = arena.not(ac).unwrap();

        assert!(prove_unsat_qf_uf_online(
            &mut arena,
            &[ab_or_ac, a_ne_b, a_ne_c]
        ));
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn prove_unsat_qf_uf_online_refutes_transitivity() {
        // a=b ∧ b=c ∧ a≠c is UNSAT.
        let mut arena = TermArena::new();
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let c = arena.bv_var("c", 8).unwrap();
        let ab = arena.eq(a, b).unwrap();
        let bc = arena.eq(b, c).unwrap();
        let ac = arena.eq(a, c).unwrap();
        let a_ne_c = arena.not(ac).unwrap();

        assert!(prove_unsat_qf_uf_online(&mut arena, &[ab, bc, a_ne_c]));
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn prove_unsat_qf_uf_online_refutes_congruence() {
        // a=b ∧ f(a)≠f(b) is UNSAT by congruence.
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

        assert!(prove_unsat_qf_uf_online(&mut arena, &[ab, fa_ne_fb]));
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn prove_unsat_qf_uf_online_does_not_claim_satisfiable_unsat() {
        // (a=b ∨ c=d) with nothing else is SAT; the online loop must return false.
        let mut arena = TermArena::new();
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let c = arena.bv_var("c", 8).unwrap();
        let d = arena.bv_var("d", 8).unwrap();
        let ab = arena.eq(a, b).unwrap();
        let cd = arena.eq(c, d).unwrap();
        let disj = arena.or(ab, cd).unwrap();

        assert!(!prove_unsat_qf_uf_online(&mut arena, &[disj]));
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn prove_unsat_qf_uf_online_matches_lazy_differential() {
        // ~50 small random QF_UF formulas: the online loop and the offline lazy
        // loop share the same uninterpreted abstraction, so they must agree on the
        // boolean verdict for every formula. Deterministic LCG, no `rand` crate.
        let mut rng: u64 = 0x9E37_79B9_7F4A_7C15;
        // Returns a 31-bit value; `u32 -> usize` is lossless on every target.
        let next = |rng: &mut u64| -> usize {
            *rng = rng
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            u32::try_from((*rng >> 33) & 0x7FFF_FFFF).expect("31-bit value fits u32") as usize
        };

        let mut agree = 0;
        let mut proved = 0;
        let rounds = 500;
        for _ in 0..rounds {
            // Fresh arena per formula keeps atom numbering clean across runs.
            let mut arena = TermArena::new();
            let sort = Sort::BitVec(8);
            let consts: Vec<TermId> = ["a", "b", "c", "d"]
                .iter()
                .map(|n| arena.bv_var(n, 8).unwrap())
                .collect();
            let f = arena.declare_fun("f", &[sort], sort).unwrap();

            // Build a handful of base equality atoms over constants and f-applies.
            let mut atoms: Vec<TermId> = Vec::new();
            let atom_count = 3 + next(&mut rng) % 3; // 3..=5
            for _ in 0..atom_count {
                let mk_term = |rng: &mut u64, arena: &mut TermArena| -> TermId {
                    let base = consts[next(rng) % consts.len()];
                    if next(rng) % 2 == 0 {
                        arena.apply(f, &[base]).unwrap()
                    } else {
                        base
                    }
                };
                let l = mk_term(&mut rng, &mut arena);
                let r = mk_term(&mut rng, &mut arena);
                let eq = arena.eq(l, r).unwrap();
                let lit = if next(&mut rng) % 2 == 0 {
                    eq
                } else {
                    arena.not(eq).unwrap()
                };
                atoms.push(lit);
            }

            // Combine the literals into a few assertions with and/or/not.
            let mut assertions: Vec<TermId> = Vec::new();
            let assertion_count = 1 + next(&mut rng) % 3; // 1..=3
            for _ in 0..assertion_count {
                let x = atoms[next(&mut rng) % atoms.len()];
                let y = atoms[next(&mut rng) % atoms.len()];
                let combined = match next(&mut rng) % 3 {
                    0 => arena.and(x, y).unwrap(),
                    1 => arena.or(x, y).unwrap(),
                    _ => arena.not(x).unwrap(),
                };
                assertions.push(combined);
            }

            let online = prove_unsat_qf_uf_online(&mut arena, &assertions);
            let lazy = prove_unsat_lazy(&mut arena, &assertions);
            assert_eq!(
                online, lazy,
                "online vs lazy disagree on {assertions:?} (online={online}, lazy={lazy})"
            );
            agree += 1;
            if online {
                proved += 1;
            }
        }
        assert_eq!(agree, rounds, "all formulas compared");
        // Sanity: the random mix should hit a healthy number of UNSAT cases.
        assert!(proved > 0, "differential set proved at least one UNSAT");
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn solve_qf_uf_online_returns_a_replayed_sat_model() {
        // a = b ∧ f(a) = c: satisfiable; the online decider must return a model that
        // replays against the original assertions.
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let c = arena.bv_var("c", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let ab = arena.eq(a, b).unwrap();
        let fa_c = arena.eq(fa, c).unwrap();

        match solve_qf_uf_online(&mut arena, &[ab, fa_c]) {
            CheckResult::Sat(model) => {
                let assignment = model.to_assignment();
                for &assertion in &[ab, fa_c] {
                    assert_eq!(
                        eval(&arena, assertion, &assignment).unwrap(),
                        Value::Bool(true),
                        "sat model must satisfy the original assertion"
                    );
                }
            }
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    #[test]
    #[allow(clippy::similar_names)]
    fn solve_qf_uf_online_decides_unsat() {
        // The disjunctive refutation, now via the decision entry point.
        let mut arena = TermArena::new();
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let c = arena.bv_var("c", 8).unwrap();
        let ab = arena.eq(a, b).unwrap();
        let ac = arena.eq(a, c).unwrap();
        let or = arena.or(ab, ac).unwrap();
        let ne_ab = arena.not(ab).unwrap();
        let ne_ac = arena.not(ac).unwrap();
        assert_eq!(
            solve_qf_uf_online(&mut arena, &[or, ne_ab, ne_ac]),
            CheckResult::Unsat
        );
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn solve_qf_uf_online_matches_check_qf_uf_differential() {
        // The decision procedure must agree with the offline check_qf_uf whenever
        // both decide (Sat/Unsat); an Unknown on either side is not a disagreement
        // (the two use different give-up boundaries). Every online Sat model is
        // additionally replay-checked above by construction.
        let mut rng: u64 = 0x2545_F491_4F6C_DD1D;
        let next = |rng: &mut u64| -> usize {
            *rng = rng
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            u32::try_from((*rng >> 33) & 0x7FFF_FFFF).expect("31-bit value fits u32") as usize
        };

        let rounds = 400;
        let mut both_decided = 0;
        for _ in 0..rounds {
            let mut arena = TermArena::new();
            let sort = Sort::BitVec(8);
            let consts: Vec<TermId> = ["a", "b", "c", "d"]
                .iter()
                .map(|n| arena.bv_var(n, 8).unwrap())
                .collect();
            let f = arena.declare_fun("f", &[sort], sort).unwrap();

            let mut atoms: Vec<TermId> = Vec::new();
            let atom_count = 3 + next(&mut rng) % 3;
            for _ in 0..atom_count {
                let mk = |rng: &mut u64, arena: &mut TermArena| -> TermId {
                    let base = consts[next(rng) % consts.len()];
                    if next(rng) % 2 == 0 {
                        arena.apply(f, &[base]).unwrap()
                    } else {
                        base
                    }
                };
                let l = mk(&mut rng, &mut arena);
                let r = mk(&mut rng, &mut arena);
                let eq = arena.eq(l, r).unwrap();
                atoms.push(if next(&mut rng) % 2 == 0 {
                    eq
                } else {
                    arena.not(eq).unwrap()
                });
            }
            let mut assertions: Vec<TermId> = Vec::new();
            let assertion_count = 1 + next(&mut rng) % 3;
            for _ in 0..assertion_count {
                let x = atoms[next(&mut rng) % atoms.len()];
                let y = atoms[next(&mut rng) % atoms.len()];
                assertions.push(match next(&mut rng) % 3 {
                    0 => arena.and(x, y).unwrap(),
                    1 => arena.or(x, y).unwrap(),
                    _ => arena.not(x).unwrap(),
                });
            }

            // Reduce each result to a decisive verdict (`Some(sat?)`) or `None`
            // (`unknown`); the two procedures have different give-up boundaries, so
            // only a clash where *both* decide is a real bug.
            let verdict = |r: &CheckResult| match r {
                CheckResult::Unsat => Some(false),
                CheckResult::Sat(_) => Some(true),
                CheckResult::Unknown(_) => None,
            };
            let online = solve_qf_uf_online(&mut arena, &assertions);
            let reference = check_qf_uf(&mut arena, &assertions);
            if let (Some(o), Some(r)) = (verdict(&online), verdict(&reference)) {
                assert_eq!(
                    o, r,
                    "online {online:?} vs check_qf_uf {reference:?} on {assertions:?}"
                );
                both_decided += 1;
            }
        }
        assert!(
            both_decided > 0,
            "the differential set jointly decided some cases"
        );
    }

    /// Builds a deliberately heavy `QF_UF` instance: a pigeonhole-style UNSAT core
    /// (`n+1` pigeons into `n` holes, encoded over `f`) AND'd with a wide
    /// disjunctive padding that makes the boolean skeleton enumerate many
    /// theory-inconsistent models — each forcing a blocking-clause refinement
    /// iteration and an inner bit-blast solve. Returned `assertions` exercise the
    /// offline lazy-DPLL(T) loop hard enough that an unbounded run is slow.
    fn build_heavy_qf_uf(arena: &mut TermArena) -> Vec<TermId> {
        let sort = Sort::BitVec(16);
        let f = arena.declare_fun("ph_f", &[sort], sort).unwrap();
        let holes = 9_usize;
        let pigeons: Vec<TermId> = (0..=holes)
            .map(|i| arena.bv_var(&format!("pigeon_{i}"), 16).unwrap())
            .collect();
        let mut assertions: Vec<TermId> = Vec::new();
        // Each pigeon maps to *some* hole value: f(p_i) in {0..holes-1}.
        for &p in &pigeons {
            let fp = arena.apply(f, &[p]).unwrap();
            let mut clause: Option<TermId> = None;
            for h in 0..holes {
                let hole = arena.bv_const(16, u128::try_from(h).unwrap()).unwrap();
                let eq = arena.eq(fp, hole).unwrap();
                clause = Some(match clause {
                    None => eq,
                    Some(acc) => arena.or(acc, eq).unwrap(),
                });
            }
            assertions.push(clause.unwrap());
        }
        // No two pigeons share a hole: f(p_i) != f(p_j). With holes+1 pigeons this
        // is UNSAT (pigeonhole), but only after the loop has chased many models.
        for i in 0..pigeons.len() {
            for j in (i + 1)..pigeons.len() {
                let fi = arena.apply(f, &[pigeons[i]]).unwrap();
                let fj = arena.apply(f, &[pigeons[j]]).unwrap();
                let eq = arena.eq(fi, fj).unwrap();
                assertions.push(arena.not(eq).unwrap());
            }
        }
        assertions
    }

    /// Hard rule: the offline `QF_UF` e-graph path must degrade to `Unknown` under a
    /// deterministic resource bound. A tight `config.timeout` on a heavy instance
    /// returns `Unknown` *within a small multiple of the budget* (bounded, never an
    /// unbounded hang); a generous budget on the SAME instance still decides it.
    #[test]
    fn check_qf_uf_with_config_is_bounded_by_timeout() {
        use std::time::Duration;

        let mut arena = TermArena::new();
        let assertions = build_heavy_qf_uf(&mut arena);

        // Tight budget: must come back Unknown and must NOT overrun wall-clock by
        // more than a small multiple of the budget (the inner solve is itself
        // bounded by the remaining time).
        let budget = Duration::from_millis(50);
        let tight = SolverConfig::default().with_timeout(budget);
        let start = Instant::now();
        let bounded = check_qf_uf_with_config(&mut arena, &assertions, &tight);
        let elapsed = start.elapsed();
        assert!(
            matches!(bounded, CheckResult::Unknown(_)),
            "tight-timeout heavy QF_UF must degrade to Unknown, got {bounded:?}"
        );
        assert!(
            elapsed < budget * 40,
            "bounded run overran its budget: {elapsed:?} for a {budget:?} budget"
        );

        // Generous budget on the same instance still decides it (pigeonhole UNSAT).
        let mut arena2 = TermArena::new();
        let assertions2 = build_heavy_qf_uf(&mut arena2);
        let generous = SolverConfig::default().with_timeout(Duration::from_secs(60));
        assert_eq!(
            check_qf_uf_with_config(&mut arena2, &assertions2, &generous),
            CheckResult::Unsat,
            "heavy QF_UF instance is pigeonhole-UNSAT under a generous budget"
        );
    }

    /// Verdict invariance: the default [`check_qf_uf`] wrapper and
    /// [`check_qf_uf_with_config`] under a generous timeout give IDENTICAL verdicts
    /// on small known sat/unsat instances (the deadline plumbing changes only the
    /// give-up boundary, never a verdict).
    #[test]
    #[allow(clippy::many_single_char_names)]
    fn check_qf_uf_with_config_verdict_invariant() {
        use std::time::Duration;
        let generous = SolverConfig::default().with_timeout(Duration::from_secs(30));

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
        let unsat_assertions = [ab, fa_ne_fb];
        let default_unsat = check_qf_uf(&mut arena, &unsat_assertions);
        let config_unsat = check_qf_uf_with_config(&mut arena, &unsat_assertions, &generous);
        assert_eq!(default_unsat, CheckResult::Unsat);
        assert_eq!(default_unsat, config_unsat);

        // SAT: a disequality alone.
        let mut arena2 = TermArena::new();
        let x = arena2.bv_var("x", 8).unwrap();
        let y = arena2.bv_var("y", 8).unwrap();
        let xy = arena2.eq(x, y).unwrap();
        let x_ne_y = arena2.not(xy).unwrap();
        let default_sat = check_qf_uf(&mut arena2, &[x_ne_y]);
        let config_sat = check_qf_uf_with_config(&mut arena2, &[x_ne_y], &generous);
        assert!(matches!(default_sat, CheckResult::Sat(_)));
        assert!(matches!(config_sat, CheckResult::Sat(_)));
    }
}
