//! The word-level string theory driven **online** by the generic CDCL(T) loop
//! (Track 1, P1.5 slice b).
//!
//! `StringTheory` plugs the ADR-0053 unbounded word core ([`axeyum_strings`])
//! into the reusable `CdclT` (`crate::cdclt::CdclT`) driver as a
//! [`TheorySolver`]. Where the existing word-equation *side channel*
//! ([`crate::smtlib::word_route_verdict`]) is all-or-nothing over a **top-level
//! conjunction** of equalities/disequalities, the CDCL(T) route handles arbitrary
//! Boolean structure (`or` / `ite` / negations) natively: the SAT search explores
//! the skeleton and the theory refutes each theory-inconsistent branch behind a
//! re-checked derivation, so disjunctive word problems the side channel cannot
//! touch are decided here.
//!
//! ## Atoms and representability
//!
//! The theory's atoms are the `Seq` equality atoms `(= s t)` collected from the
//! assertions ([`collect_eq_atoms`]) **plus** the regex membership atoms
//! `(str.in_re X R)` the caller passes in (P2.7 T-C.6). An equality atom asserted
//! *true* records a word equality and *false* a word disequality; a membership
//! atom asserted *true* records `X ∈ R` and *false* records `X ∉ R` (a single
//! atom kind for both polarities — the negative language is the engine's native
//! complement). The entry point
//! [`check_qf_s_online_cdclt_with_memberships`] **declines the whole query** up
//! front when a non-`Seq` equality atom is present, so the online path only ever
//! runs on the pure `QF_S` fragment.
//!
//! ## Verdict discipline (ADR-0053 / ADR-0054)
//!
//! - **`unsat`** is theory-driven *only* through a checked derivation. On every
//!   assertion the theory (a) re-runs the T-B.7 [`refute_word_equations`] refuter
//!   over the currently-asserted equalities and disequalities, and (b) checks the
//!   regex-membership consistency: it groups the asserted memberships by the
//!   equivalence classes the word equalities induce and refutes any class whose
//!   positive/negative regex intersection is provably empty behind the re-checked
//!   derivative-emptiness certificate ([`Membership::refute_empty`], ADR-0054).
//!   Both refutations map their premises back to the exact asserted literals, so
//!   the theory conflict — and hence every 1-UIP lemma the driver learns from it —
//!   is a genuine theory entailment. A telemetry invariant
//!   ([`StringTheory::assert_conflicts_certified`]) pins that no conflict is ever
//!   reported without a certified refutation behind it.
//! - **`sat`** is never trusted from the search. When the driver reaches a total,
//!   theory-consistent assignment the entry point assembles a concrete model: a
//!   [`solve_word_equations`] assignment for the word part, a matcher-replayed
//!   [`Membership::solve`] witness per membership class (spread across its
//!   word-equal members), and each membership atom's truth **recomputed by the
//!   independent reference [`matches()`]** on the model's string binding — never
//!   trusted from the SAT search. The combined [`Model`] is then **replayed against
//!   the original assertions** through the ground evaluator ([`replays`]). A
//!   non-replay (or a search that finds no witnessing model) downgrades to
//!   [`CheckResult::Unknown`], never a wrong `sat`.
//! - **Deadline / budget.** The CDCL search is deadline-bounded like the EUF
//!   route; the per-assert refuter and the final word search honor the same
//!   [`SearchBudget`] deadline, so the path degrades to `Unknown` under a
//!   deterministic resource bound.
//!
//! ## What this slice does not do
//!
//! - **Theory propagation** is skipped ([`StringTheory::propagate`] returns
//!   nothing). The word core's derived [`Fact`](axeyum_strings::Fact)s are
//!   equalities over *sub-components*, which rarely coincide with a whole asserted
//!   atom, so there is no clean atom-to-fact mapping to propagate this slice.
//!   Correctness first; propagation is a later optimization.
//! - **Incrementality.** The word core is not incremental: the theory re-runs the
//!   refuter from scratch on each representable assertion (a one-shot inside the
//!   theory). This is correct but not cheap; a backtrackable word core is the
//!   incrementality TODO.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::time::Instant;

use axeyum_ir::{ArraySortKey, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value};
use axeyum_strings::regex::{Regex, matches};
use axeyum_strings::{
    Membership, RefuteOutcome, SearchBudget, SearchOutcome, refute_word_equations,
    solve_word_equations,
};

use crate::backend::{CheckResult, SolverConfig, UnknownKind, UnknownReason};
use crate::cdclt::{CdclT, Lit as CdcltLit, Outcome};
use crate::euf_egraph::{
    Encoder, Lit, TheoryLit, TheoryProp, TheorySolver, collect_eq_atoms, replays,
};
use crate::model::Model;

/// The branch-node budget the per-assert refuter and the final word search spend.
/// Generous: the T-B.3 fixpoint prunes hard and the search additionally honors an
/// absolute deadline; this cap is the sole guard when no timeout is set (and under
/// `wasm32`, where the deadline is absent). Mirrors `smtlib::WORD_ROUTE_MAX_NODES`.
const WORD_MAX_NODES: u64 = 200_000;

/// The distinct-canonical-residual cap the per-class regex-membership emptiness
/// check materializes before declining (⇒ no conflict detected on that class).
/// Mirrors `axeyum_strings::regex::membership::DEFAULT_MAX_STATES`.
const MEMBERSHIP_MAX_STATES: usize = 20_000;

/// The derivative-residual cap for a **concat operand's** shape-augmented witness
/// search (`R ∩ shape`). Smaller than [`MEMBERSHIP_MAX_STATES`] because the shape's
/// `Σ*` runs enlarge the closure and the emptiness pass does not poll the deadline —
/// a tight cap keeps a pathological concat regex a fast `Unknown`. Ample for the
/// real corpus rows, whose regexes close in well under this bound.
const CONCAT_WITNESS_MAX_STATES: usize = 4_000;

/// The witness-length cap for a concat operand's shape-augmented witness search.
const CONCAT_WITNESS_MAX_LEN: usize = 512;

/// A theory atom of the online string route.
enum AtomKind {
    /// A `Seq` equality `(= l r)`: asserted `true` ⇒ a word equality, `false` ⇒ a
    /// word disequality.
    Eq(TermId, TermId),
    /// A regex membership `(str.in_re operand R)` on a single string variable:
    /// asserted `true` ⇒ `operand ∈ R` (a positive constraint), `false` ⇒
    /// `operand ∉ R` (a negative constraint, i.e. `operand ∈ ∁R`).
    Membership { operand: SymbolId, regex: Regex },
}

/// A tiny union-find over `Seq` variable symbols, for grouping memberships into
/// equivalence classes under the asserted word equalities. Path-halving find over
/// a `HashMap` parent table; deterministic because it is only ever queried for
/// class-root equality, never iterated for output.
#[derive(Default)]
struct UnionFind {
    parent: HashMap<SymbolId, SymbolId>,
}

impl UnionFind {
    /// Registers `s` as its own singleton class if unseen.
    fn make(&mut self, s: SymbolId) {
        self.parent.entry(s).or_insert(s);
    }

    /// The class root of `s` (registering `s` first if unseen).
    fn find(&mut self, s: SymbolId) -> SymbolId {
        self.make(s);
        let mut root = s;
        while self.parent[&root] != root {
            let grand = self.parent[&self.parent[&root]];
            self.parent.insert(root, grand); // path halving
            root = grand;
        }
        root
    }

    /// Merges the classes of `a` and `b`.
    fn union(&mut self, a: SymbolId, b: SymbolId) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra != rb {
            self.parent.insert(ra, rb);
        }
    }
}

/// Online word-level string theory over the CDCL(T) driver.
///
/// Owns a mutable borrow of the arena because the word core
/// ([`refute_word_equations`]) is re-run from arena terms on each representable
/// assertion (it is not incremental). Atom indices align with the driver's
/// variable numbering: the first `atoms.len()` skeleton variables are these atoms.
pub(crate) struct StringTheory<'a> {
    arena: &'a mut TermArena,
    /// Per atom index: its kind (a word equality or a regex membership).
    atoms: Vec<AtomKind>,
    /// Per atom index: the value it is currently asserted at (`None` if
    /// unassigned). Guards against a double-assert of the same atom.
    assigned: Vec<Option<bool>>,
    /// Atom indices assigned since the start, in order — the backtrack log for
    /// `assigned` (truncated on [`StringTheory::pop`]).
    assigned_log: Vec<usize>,
    /// Currently-asserted **equalities**: `(atom index, (l, r))` in assertion
    /// order. The position in this vector is the premise index the refuter cites.
    active_eqs: Vec<(usize, (TermId, TermId))>,
    /// Currently-asserted **disequalities**: `(atom index, (l, r))`.
    active_diseqs: Vec<(usize, (TermId, TermId))>,
    /// Currently-asserted **positive** memberships: `(atom index, operand, R)`.
    active_pos_mem: Vec<(usize, SymbolId, Regex)>,
    /// Currently-asserted **negative** memberships: `(atom index, operand, R)`.
    active_neg_mem: Vec<(usize, SymbolId, Regex)>,
    /// Backtrack trail: per [`StringTheory::push`], the
    /// `(active_eqs, active_diseqs, active_pos_mem, active_neg_mem, assigned_log)`
    /// lengths.
    trail: Vec<(usize, usize, usize, usize, usize)>,
    /// The refuter budget (deadline + node cap).
    budget: SearchBudget,
    /// Telemetry: theory conflicts reported to the driver.
    conflicts_reported: u64,
    /// Telemetry: of those, how many were backed by a certified
    /// [`RefuteOutcome::Unsat`] (always equal to `conflicts_reported` by
    /// construction — a soundness invariant, see
    /// [`StringTheory::assert_conflicts_certified`]).
    conflicts_certified: u64,
}

impl<'a> StringTheory<'a> {
    /// Builds the theory over `atom_kinds` (per atom, its kind), borrowing `arena`
    /// for the word core and using `budget` for the per-assert refuter.
    fn new(arena: &'a mut TermArena, atom_kinds: Vec<AtomKind>, budget: SearchBudget) -> Self {
        let n = atom_kinds.len();
        Self {
            arena,
            atoms: atom_kinds,
            assigned: vec![None; n],
            assigned_log: Vec::new(),
            active_eqs: Vec::new(),
            active_diseqs: Vec::new(),
            active_pos_mem: Vec::new(),
            active_neg_mem: Vec::new(),
            trail: Vec::new(),
            budget,
            conflicts_reported: 0,
            conflicts_certified: 0,
        }
    }

    /// The currently-asserted equalities as bare `(l, r)` pairs (assertion order),
    /// for the caller's final [`solve_word_equations`] model search.
    pub(crate) fn equalities(&self) -> Vec<(TermId, TermId)> {
        self.active_eqs.iter().map(|&(_, p)| p).collect()
    }

    /// The currently-asserted disequalities as bare `(l, r)` pairs.
    pub(crate) fn disequalities(&self) -> Vec<(TermId, TermId)> {
        self.active_diseqs.iter().map(|&(_, p)| p).collect()
    }

    /// The currently-asserted positive memberships as `(operand, regex)` pairs.
    fn positive_memberships(&self) -> Vec<(SymbolId, Regex)> {
        self.active_pos_mem
            .iter()
            .map(|&(_, op, ref r)| (op, r.clone()))
            .collect()
    }

    /// The currently-asserted negative memberships as `(operand, regex)` pairs.
    fn negative_memberships(&self) -> Vec<(SymbolId, Regex)> {
        self.active_neg_mem
            .iter()
            .map(|&(_, op, ref r)| (op, r.clone()))
            .collect()
    }

    /// The soundness telemetry: every reported theory conflict was backed by a
    /// certified [`RefuteOutcome::Unsat`]. Holds by construction — the theory only
    /// ever builds a conflict core from a certified refutation.
    pub(crate) fn assert_conflicts_certified(&self) {
        assert_eq!(
            self.conflicts_reported, self.conflicts_certified,
            "a StringTheory conflict was reported without a certified refutation \
             behind it — a soundness bug"
        );
    }

    /// Re-runs the T-B.7 refuter over the current equality/disequality set. On a
    /// certified [`RefuteOutcome::Unsat`] returns the theory conflict core: the
    /// asserted literals named by the refuter's cited premise indices (each cited
    /// equality as a `true` literal) together with **every** currently-asserted
    /// disequality (a `false` literal) and the just-asserted `trigger` literal.
    ///
    /// Including all asserted disequalities is a sound over-approximation of the
    /// unsat core — a superset of a genuine core is still a valid theory lemma, and
    /// every such literal is on the trail so the conflict clause is fully
    /// falsified. Including `trigger` is what keeps the driver's 1-UIP analysis
    /// well-formed: the word refuter is **incomplete and non-monotone**, so the
    /// conflict it reports on this assertion need not cite the atom just asserted;
    /// yet `CdclT`'s conflict analysis requires the conflict clause to carry at
    /// least one **current-decision-level** literal (the reason it fired now). The
    /// trigger was assigned in this very `assert`, so it is exactly that literal.
    /// (Without it, a core of only lower-level literals underflows the analysis's
    /// path counter.) A tight core is an optimization TODO.
    fn check_conflict(&mut self, trigger: (usize, bool)) -> Result<(), Vec<TheoryLit>> {
        if self.active_eqs.is_empty() && self.active_diseqs.is_empty() {
            return Ok(());
        }
        let eqs: Vec<(TermId, TermId)> = self.active_eqs.iter().map(|&(_, p)| p).collect();
        let diseqs: Vec<(TermId, TermId)> = self.active_diseqs.iter().map(|&(_, p)| p).collect();
        let premises = match refute_word_equations(self.arena, &eqs, &diseqs, &self.budget) {
            RefuteOutcome::Unsat { premises } => premises,
            RefuteOutcome::Unknown => return Ok(()),
        };

        // A certified refutation (its `unsat` passed `axeyum-strings`'s own
        // independent re-check). Map the cited ORIGINAL premise indices back to the
        // exact asserted equality literals, and add every asserted disequality.
        let mut core: Vec<TheoryLit> = premises
            .iter()
            .filter_map(|&i| {
                self.active_eqs
                    .get(i)
                    .map(|&(atom, _)| TheoryLit { atom, value: true })
            })
            .collect();
        for &(atom, _) in &self.active_diseqs {
            core.push(TheoryLit { atom, value: false });
        }
        // Always carry the just-asserted (current-level) literal, deduplicated —
        // see the method docs for why the 1-UIP analysis needs it.
        let (t_atom, t_value) = trigger;
        if !core.iter().any(|l| l.atom == t_atom) {
            core.push(TheoryLit {
                atom: t_atom,
                value: t_value,
            });
        }
        self.conflicts_reported += 1;
        self.conflicts_certified += 1;
        Err(core)
    }

    /// Re-checks the **regex-membership** consistency of the current assertion set.
    /// Groups the asserted memberships into equivalence classes by the word
    /// equalities that merge single-variable operands (`(= x y)` over two `Seq`
    /// *variables*), intersects each class's positive/negative regexes, and — on a
    /// **certified emptiness** ([`Membership::refute_empty`], the same re-checked
    /// derivative-closure certificate the one-shot route uses for `unsat`) — reports
    /// a theory conflict.
    ///
    /// The conflict core is the class's membership literals (at their asserted
    /// polarity) together with the variable-variable equalities that built the class
    /// (each `true`) and the just-asserted `trigger` (for the same 1-UIP
    /// well-formedness reason as [`Self::check_conflict`]). Every such literal is on
    /// the trail at the stated value, so the clause `¬⋀core` is a genuine theory
    /// lemma: the class members are all equal and jointly constrained to an empty
    /// language.
    ///
    /// Only variable-variable equalities merge classes; an equality with a compound
    /// or literal side is **not** used (a conservative under-merge that can only
    /// *miss* a conflict, never fabricate one — the missed branch is caught later by
    /// the mandatory `sat`-model replay). A class that is not proven empty within the
    /// state cap, or a past-deadline budget, reports no conflict.
    fn check_membership_conflict(&mut self, trigger: (usize, bool)) -> Result<(), Vec<TheoryLit>> {
        if (self.active_pos_mem.is_empty() && self.active_neg_mem.is_empty())
            || self.budget.past_deadline()
        {
            return Ok(());
        }

        // Union-find over the `Seq` variable symbols, merged by variable-variable
        // equalities. Record those equalities so the conflict core can cite them.
        let mut uf: UnionFind = UnionFind::default();
        for &(_, op, _) in self.active_pos_mem.iter().chain(&self.active_neg_mem) {
            uf.make(op);
        }
        let mut var_eqs: Vec<(usize, SymbolId, SymbolId)> = Vec::new();
        for &(atom, (l, r)) in &self.active_eqs {
            if let (TermNode::Symbol(a), TermNode::Symbol(b)) =
                (self.arena.node(l), self.arena.node(r))
                && matches!(self.arena.sort_of(l), Sort::Seq(_))
                && matches!(self.arena.sort_of(r), Sort::Seq(_))
            {
                let (a, b) = (*a, *b);
                uf.make(a);
                uf.make(b);
                uf.union(a, b);
                var_eqs.push((atom, a, b));
            }
        }

        // Group the memberships by class root: `(atom, regex, positive)`.
        let mut classes: BTreeMap<SymbolId, Vec<(usize, Regex, bool)>> = BTreeMap::new();
        for &(atom, op, ref regex) in &self.active_pos_mem {
            classes
                .entry(uf.find(op))
                .or_default()
                .push((atom, regex.clone(), true));
        }
        for &(atom, op, ref regex) in &self.active_neg_mem {
            classes
                .entry(uf.find(op))
                .or_default()
                .push((atom, regex.clone(), false));
        }

        for (root, members) in &classes {
            let mut problem = Membership::default();
            for (_, regex, positive) in members {
                if *positive {
                    problem.positives.push(regex.clone());
                } else {
                    problem.negatives.push(regex.clone());
                }
            }
            // Deadline-bounded: the emptiness closure of a complex regex-intersection
            // must not stall the CDCL loop past its timeout. An abandoned closure just
            // misses this conflict (safe — caught later by the mandatory sat replay).
            if !problem.refute_empty_within(MEMBERSHIP_MAX_STATES, &self.budget) {
                continue;
            }
            // Certified empty ⇒ theory conflict. Core = this class's membership
            // literals + the variable-variable equalities inside the class + trigger.
            let mut core: Vec<TheoryLit> = members
                .iter()
                .map(|&(atom, _, positive)| TheoryLit {
                    atom,
                    value: positive,
                })
                .collect();
            for &(atom, a, b) in &var_eqs {
                if uf.find(a) == *root && uf.find(b) == *root {
                    core.push(TheoryLit { atom, value: true });
                }
            }
            let (t_atom, t_value) = trigger;
            if !core.iter().any(|l| l.atom == t_atom) {
                core.push(TheoryLit {
                    atom: t_atom,
                    value: t_value,
                });
            }
            self.conflicts_reported += 1;
            self.conflicts_certified += 1;
            return Err(core);
        }
        Ok(())
    }
}

impl TheorySolver for StringTheory<'_> {
    fn assert(&mut self, atom: usize, value: bool) -> Result<(), Vec<TheoryLit>> {
        if self.assigned[atom].is_none() {
            self.assigned[atom] = Some(value);
            self.assigned_log.push(atom);
        }
        match &self.atoms[atom] {
            AtomKind::Eq(l, r) => {
                let (l, r) = (*l, *r);
                if value {
                    self.active_eqs.push((atom, (l, r)));
                } else {
                    self.active_diseqs.push((atom, (l, r)));
                }
            }
            AtomKind::Membership { operand, regex } => {
                let (operand, regex) = (*operand, regex.clone());
                if value {
                    self.active_pos_mem.push((atom, operand, regex));
                } else {
                    self.active_neg_mem.push((atom, operand, regex));
                }
            }
        }
        // Both refuters are certified; report the first conflict found.
        self.check_conflict((atom, value))?;
        self.check_membership_conflict((atom, value))
    }

    fn push(&mut self) {
        self.trail.push((
            self.active_eqs.len(),
            self.active_diseqs.len(),
            self.active_pos_mem.len(),
            self.active_neg_mem.len(),
            self.assigned_log.len(),
        ));
    }

    fn pop(&mut self) {
        if let Some((eqs_len, diseqs_len, pos_len, neg_len, assigned_len)) = self.trail.pop() {
            self.active_eqs.truncate(eqs_len);
            self.active_diseqs.truncate(diseqs_len);
            self.active_pos_mem.truncate(pos_len);
            self.active_neg_mem.truncate(neg_len);
            while self.assigned_log.len() > assigned_len {
                if let Some(atom) = self.assigned_log.pop() {
                    self.assigned[atom] = None;
                }
            }
        }
    }

    fn propagate(&self) -> Vec<TheoryProp> {
        // Skipped this slice (see the module docs): no clean atom-to-fact mapping.
        Vec::new()
    }
}

/// The word-search / refuter [`SearchBudget`]: an absolute deadline from
/// `config.timeout` (native targets) plus the [`WORD_MAX_NODES`] node cap. Mirrors
/// `smtlib::word_route_budget`.
fn word_budget(config: &SolverConfig) -> SearchBudget {
    #[cfg(not(target_arch = "wasm32"))]
    {
        if let Some(t) = config.timeout
            && let Some(deadline) = Instant::now().checked_add(t)
        {
            return SearchBudget::with_deadline(WORD_MAX_NODES, deadline);
        }
        SearchBudget::new(WORD_MAX_NODES)
    }
    #[cfg(target_arch = "wasm32")]
    {
        let _ = config;
        SearchBudget::new(WORD_MAX_NODES)
    }
}

fn unknown(detail: &str) -> UnknownReason {
    UnknownReason {
        kind: UnknownKind::Other,
        detail: detail.to_owned(),
    }
}

/// The `Seq` equality sides of `atom`, or `None` when it is not a `Seq` equality.
fn seq_eq_sides(arena: &TermArena, atom: TermId) -> Option<(TermId, TermId)> {
    match arena.node(atom) {
        TermNode::App { op: Op::Eq, args } if args.len() == 2 => {
            let (l, r) = (args[0], args[1]);
            matches!(arena.sort_of(l), Sort::Seq(_)).then_some((l, r))
        }
        _ => None,
    }
}

/// Collects the distinct `Seq`-sorted symbols reachable from `terms` (a model must
/// bind these). Deterministic: symbols are collected in first-encounter order.
fn collect_seq_symbols(arena: &TermArena, terms: &[TermId]) -> Vec<SymbolId> {
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    let mut stack: Vec<TermId> = terms.to_vec();
    let mut visited = HashSet::new();
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        if let TermNode::Symbol(sym) = arena.node(t)
            && matches!(arena.sort_of(t), Sort::Seq(_))
            && seen.insert(*sym)
        {
            out.push(*sym);
        } else if let TermNode::App { args, .. } = arena.node(t) {
            for &a in args {
                stack.push(a);
            }
        }
    }
    // First-encounter order over a DFS is deterministic for a fixed arena; sort by
    // the symbol id so the model-build order is independent of traversal details.
    out.sort_unstable_by_key(|s| s.index());
    out.dedup();
    out
}

/// Decides the quantifier-free string fragment (`QF_S`: `Seq`/`String` equality
/// and disequality under arbitrary Boolean structure) via the generic online
/// CDCL(T) driver `CdclT` with `StringTheory` as the theory (Track 1, P1.5
/// slice b).
///
/// This is the disjunction-aware counterpart to the top-level-conjunction word
/// side channel ([`crate::smtlib::word_route_verdict`]): the Boolean skeleton over
/// the string equality atoms is searched by `CdclT`, and each
/// theory-inconsistent branch is refuted behind a re-checked derivation, so
/// `or`/`ite`/negated word problems are decided here.
///
/// Verdict discipline (see the module docs): `unsat` only through certified theory
/// conflicts (or a pure propositional refutation of the skeleton); `sat` only via a
/// [`solve_word_equations`] model that **replays** against the original assertions;
/// `Unknown` on deadline, on an unrepresentable/out-of-fragment query, or when the
/// word search finds no replaying model.
///
/// Returns [`CheckResult::Unknown`] up front when there are no `Seq` equality
/// atoms, when a **non-`Seq`** equality atom is present (out of the `QF_S` scope),
/// or when the Boolean skeleton has structure the shared `Encoder` does not
/// cover. **Not** wired into default dispatch this slice (opt-in).
#[must_use]
pub fn check_qf_s_online_cdclt(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> CheckResult {
    check_qf_s_online_cdclt_with_memberships(arena, assertions, &[], config)
}

/// The prepared inputs to the online CDCL(T) driver: the theory atom kinds, the
/// encoded Boolean skeleton, and the model-assembly metadata.
struct Prepared {
    atom_kinds: Vec<AtomKind>,
    driver_clauses: Vec<Vec<CdcltLit>>,
    eq_count: usize,
    var_count: usize,
    seq_syms: Vec<SymbolId>,
    mem_proxy_syms: HashSet<SymbolId>,
    term_vars: Vec<(TermId, usize)>,
}

/// Collects the theory atoms (`Seq` equalities followed by the membership atoms),
/// encodes the Boolean skeleton, and gathers the model-assembly metadata. Returns
/// `Err(decline)` — a [`CheckResult::Unknown`] — when the query is out of the
/// route's fragment (a non-`Seq` equality atom, no atoms, or skeleton structure the
/// shared [`Encoder`] does not cover).
fn prepare_skeleton(
    arena: &mut TermArena,
    assertions: &[TermId],
    memberships: &[(TermId, SymbolId, Regex)],
) -> Result<Prepared, CheckResult> {
    // Distinct equality atoms — the first theory atoms / skeleton variables.
    let mut atom_terms: Vec<TermId> = Vec::new();
    let mut seen = HashSet::new();
    for &a in assertions {
        collect_eq_atoms(arena, a, &mut atom_terms, &mut seen);
    }

    // Scope gate: every equality atom must be `Seq`-sorted. A non-`Seq` equality is
    // outside the `QF_S` fragment this route decides — decline the whole query.
    let mut atom_kinds: Vec<AtomKind> = Vec::with_capacity(atom_terms.len() + memberships.len());
    for &t in &atom_terms {
        match seq_eq_sides(arena, t) {
            Some((l, r)) => atom_kinds.push(AtomKind::Eq(l, r)),
            None => {
                return Err(CheckResult::Unknown(unknown(
                    "non-sequence equality atom outside the QF_S online CDCL(T) scope",
                )));
            }
        }
    }

    // Membership atoms follow the equality atoms in the theory's atom-index space.
    // Deduplicate on the proxy atom term (the parser interns identical atoms, but
    // guard against a caller passing a repeat).
    for &(atom, operand, ref regex) in memberships {
        if seen.insert(atom) {
            atom_terms.push(atom);
            atom_kinds.push(AtomKind::Membership {
                operand,
                regex: regex.clone(),
            });
        }
    }

    if atom_terms.is_empty() {
        return Err(CheckResult::Unknown(unknown(
            "no theory atoms for the online CDCL(T) string path",
        )));
    }

    // Encode the Boolean skeleton over the atoms with the shared Tseitin encoder.
    let mut enc = Encoder::new(&atom_terms);
    let mut clauses: Vec<Vec<Lit>> = Vec::new();
    for &assertion in assertions {
        let Some(top) = enc.encode(arena, assertion, &mut clauses) else {
            return Err(CheckResult::Unknown(unknown(
                "boolean skeleton outside the online CDCL(T) encoder",
            )));
        };
        clauses.push(vec![Lit {
            var: top,
            positive: true,
        }]);
    }
    let driver_clauses: Vec<Vec<CdcltLit>> = clauses
        .iter()
        .map(|clause| {
            clause
                .iter()
                .map(|l| CdcltLit {
                    var: l.var,
                    positive: l.positive,
                })
                .collect()
        })
        .collect();

    let eq_count = atom_terms.len();
    let var_count = enc.var_count;
    // The `Seq` symbols a model must bind: those reachable from the equality atoms,
    // plus every membership operand (a membership-only variable never surfaces as an
    // equality side, yet the replay must bind it).
    let mut seq_syms = collect_seq_symbols(arena, &atom_terms);
    for &(_, operand, _) in memberships {
        if !seq_syms.contains(&operand) {
            seq_syms.push(operand);
        }
    }
    seq_syms.sort_unstable_by_key(|s| s.index());
    seq_syms.dedup();
    // The membership proxy symbols — skipped by the generic skeleton-Bool injection
    // (their truth comes from the matcher, never the SAT search).
    let mem_proxy_syms: HashSet<SymbolId> = memberships
        .iter()
        .filter_map(|&(atom, _, _)| match arena.node(atom) {
            TermNode::Symbol(s) => Some(*s),
            _ => None,
        })
        .collect();
    // A deterministic (TermId-sorted) view of the encoder's Bool-symbol variables,
    // for skeleton-only Bool injection after the search (`term_var` is a HashMap).
    let mut term_vars: Vec<(TermId, usize)> = enc.term_var.iter().map(|(&t, &v)| (t, v)).collect();
    term_vars.sort_by_key(|(term, _)| *term);

    Ok(Prepared {
        atom_kinds,
        driver_clauses,
        eq_count,
        var_count,
        seq_syms,
        mem_proxy_syms,
        term_vars,
    })
}

/// The online CDCL(T) string route (P1.5b / P2.7 T-C.6) extended with **regex
/// membership** theory atoms.
///
/// `memberships` maps each `(str.in_re X R)` atom the skeleton references to
/// `(proxy_atom_term, operand_symbol, regex)`: `proxy_atom_term` is the
/// `Sort::Bool` symbol standing for the atom inside `assertions`, `operand_symbol`
/// is the single `Seq` variable it constrains, and `regex` is the code-point
/// language (see [`axeyum_smtlib::Script::word_skeleton_memberships`]). Asserting
/// the atom `true` is `operand ∈ R`; `false` is `operand ∉ R` (the complemented
/// language) — a single atom kind for both polarities.
///
/// Verdict discipline is unchanged and extended to memberships:
/// - **`unsat`** — only via a certified theory conflict. Word (dis)equalities are
///   refuted by the T-B.7 word core; membership intersections are refuted by the
///   re-checked derivative-emptiness certificate ([`Membership::refute_empty`]),
///   grouped by the equivalence classes the word equalities induce.
/// - **`sat`** — only via a model that **replays** against the original assertions:
///   each membership class contributes a matcher-replayed witness, and each
///   membership proxy's truth is recomputed by the independent reference
///   [`matches()`] on the model's string binding (never trusted from the SAT search).
/// - **`Unknown`** — on deadline/budget, an out-of-fragment atom, or when no
///   replaying model is found.
#[must_use]
pub fn check_qf_s_online_cdclt_with_memberships(
    arena: &mut TermArena,
    assertions: &[TermId],
    memberships: &[(TermId, SymbolId, Regex)],
    config: &SolverConfig,
) -> CheckResult {
    let prepared = match prepare_skeleton(arena, assertions, memberships) {
        Ok(prepared) => prepared,
        Err(decline) => return decline,
    };
    let Prepared {
        atom_kinds,
        driver_clauses,
        eq_count,
        var_count,
        seq_syms,
        mem_proxy_syms,
        term_vars,
    } = prepared;

    let deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));
    let budget = word_budget(config);
    let mut solver = CdclT::new(var_count, eq_count, driver_clauses, deadline);
    let mut theory = StringTheory::new(arena, atom_kinds, budget.clone());
    let outcome = solver.solve(&mut theory);

    match outcome {
        Outcome::Unsat => {
            // Soundness telemetry: no conflict was ever fabricated without a
            // certified refutation behind it.
            theory.assert_conflicts_certified();
            CheckResult::Unsat
        }
        Outcome::Unknown => {
            CheckResult::Unknown(unknown("timeout in the online CDCL(T) string driver"))
        }
        Outcome::Sat => {
            // The driver reached a total, theory-consistent assignment. The refuters
            // are incomplete, so "no conflict" is not a model — assemble a concrete,
            // replay-checked model over the asserted word + membership set, then
            // replay it against the ORIGINAL assertions.
            theory.assert_conflicts_certified();
            let eqs = theory.equalities();
            let diseqs = theory.disequalities();
            let pos_mem = theory.positive_memberships();
            let neg_mem = theory.negative_memberships();
            drop(theory); // release the arena borrow for the model search + replay
            let ctx = SatModelCtx {
                assertions,
                eqs: &eqs,
                diseqs: &diseqs,
                pos_mem: &pos_mem,
                neg_mem: &neg_mem,
                budget: &budget,
                seq_syms: &seq_syms,
                memberships,
                mem_proxy_syms: &mem_proxy_syms,
                term_vars: &term_vars,
                solver: &solver,
            };
            string_sat_model(arena, &ctx)
        }
    }
}

/// The inputs to [`string_sat_model`] on a theory-consistent branch, bundled to
/// keep the argument list bounded.
struct SatModelCtx<'a> {
    assertions: &'a [TermId],
    eqs: &'a [(TermId, TermId)],
    diseqs: &'a [(TermId, TermId)],
    pos_mem: &'a [(SymbolId, Regex)],
    neg_mem: &'a [(SymbolId, Regex)],
    budget: &'a SearchBudget,
    seq_syms: &'a [SymbolId],
    memberships: &'a [(TermId, SymbolId, Regex)],
    mem_proxy_syms: &'a HashSet<SymbolId>,
    term_vars: &'a [(TermId, usize)],
    solver: &'a CdclT,
}

/// Assembles and replay-checks a `sat` model on a theory-consistent branch:
/// 1. solve the asserted word (dis)equalities for a base string assignment;
/// 2. override each membership equivalence class with a matcher-replayed witness;
/// 3. inject each membership proxy's truth via the reference [`matches()`] on the
///    model's operand binding, and any other skeleton-only Bool from the SAT trail;
/// 4. replay the combined [`Model`] against the original assertions.
///
/// Returns [`CheckResult::Unknown`] when no model is found or the combined model
/// does not replay — never a wrong `sat`.
fn string_sat_model(arena: &mut TermArena, ctx: &SatModelCtx) -> CheckResult {
    // When membership atoms are present, witness each membership equivalence class
    // (a matcher-replayed string per class) and **pin** each class symbol to its
    // witness as an extra word equation, then solve the *augmented* word system.
    //
    // This is what composes membership with `str.++` word equations soundly. The
    // earlier design solved the word part first and then *overrode* each membership
    // symbol with an independently-searched witness — but a symbol a `str.++`
    // equation also constrains (e.g. `w ∈ R ∧ w = x ++ "B" ++ y`, or the coupled
    // `action ∈ R ∧ action = a1 ++ k ++ a2` shape) would then desync from its
    // decomposition, and the mandatory replay would reject the model to `Unknown`.
    // Pinning `symbol = witness` and re-solving instead threads the witness THROUGH
    // the word arrangement, so the concat components (`x`/`y`, `a1`/`k`/`a2`) are
    // chosen consistently with the witnessed whole. Soundness is unchanged: the
    // combined model still must replay against the original assertions, and the pin
    // only ever *adds* a constraint (a pinned system that fails to solve degrades to
    // `Unknown`, never a wrong `sat`).
    let mut pin_eqs: Vec<(TermId, TermId)> = Vec::new();
    if !ctx.pos_mem.is_empty() || !ctx.neg_mem.is_empty() {
        let Some(witnesses) =
            membership_witnesses(arena, ctx.eqs, ctx.pos_mem, ctx.neg_mem, ctx.budget)
        else {
            return CheckResult::Unknown(unknown(
                "online CDCL(T) membership class has no witnessing model within budget",
            ));
        };
        // Deterministic (symbol-index) order for stable arena construction.
        let mut pairs: Vec<(SymbolId, Vec<u32>)> = witnesses.into_iter().collect();
        pairs.sort_by_key(|(s, _)| s.index());
        for (sym, codepoints) in pairs {
            let Some(lit) = seq_term_from_code_points(arena, &codepoints) else {
                return CheckResult::Unknown(unknown(
                    "online CDCL(T) string membership witness term construction failed",
                ));
            };
            let var = arena.var(sym);
            pin_eqs.push((var, lit));
        }
    }

    let all_eqs: Vec<(TermId, TermId)> = ctx.eqs.iter().copied().chain(pin_eqs).collect();
    let SearchOutcome::Sat(assignment) =
        solve_word_equations(arena, &all_eqs, ctx.diseqs, ctx.budget)
    else {
        return CheckResult::Unknown(unknown(
            "online CDCL(T) string search found no replaying model on a \
             theory-consistent branch",
        ));
    };

    let mut model = Model::new();
    for &sym in ctx.seq_syms {
        if let Some(value) = assignment.get(sym) {
            model.set(sym, value);
        }
    }

    // Inject each membership proxy's truth from the reference matcher on the model's
    // operand binding — the sole (faithful) source for a membership atom's value.
    for &(atom, operand, ref regex) in ctx.memberships {
        let TermNode::Symbol(proxy) = arena.node(atom) else {
            continue;
        };
        let proxy = *proxy;
        let holds = match model.get(operand) {
            Some(Value::Seq(elems)) => matches(regex, &seq_code_points(&elems)),
            // An unbound operand cannot be matched — leave the proxy unset so replay
            // reports Unknown rather than guess.
            _ => continue,
        };
        model.set(proxy, Value::Bool(holds));
    }

    // Inject any remaining skeleton-only Bool symbol (never a Seq atom side, never a
    // membership proxy) from the solver trail. Additive and replay-gated.
    for (term, var) in ctx.term_vars {
        if let TermNode::Symbol(sym) = arena.node(*term)
            && arena.sort_of(*term) == Sort::Bool
            && !ctx.mem_proxy_syms.contains(sym)
            && model.get(*sym).is_none()
            && let Some(value) = ctx.solver.value(*var)
        {
            model.set(*sym, Value::Bool(value));
        }
    }

    if replays(arena, ctx.assertions, &model) {
        CheckResult::Sat(model)
    } else {
        CheckResult::Unknown(unknown(
            "online CDCL(T) string model did not replay against the assertions",
        ))
    }
}

/// One component of a `str.in_re` `str.++` subject's defining concatenation: a
/// fixed literal, or a `Seq` variable symbol.
enum ConcatPart {
    /// A constant component (a fused literal run), as code points.
    Lit(Vec<u32>),
    /// A variable component (a `Seq` symbol).
    Var(SymbolId),
}

/// The parts of the defining concatenation of a membership operand `w`, if some
/// asserted equality binds `w = <str.++ …>` (a genuine concatenation, i.e. **not**
/// a plain variable-variable equality). Each part is a fixed literal (a fused
/// constant run) or a `Seq` variable symbol. `None` when `w` has no such defining
/// equation (it is an ordinary variable operand).
///
/// This is how the online route recognizes a *membership-over-concat*: the parser
/// rewrote `(str.in_re (str.++ p…) R)` into `w ∈ R ∧ w = p…` with a fresh `w`, so
/// the concat structure is recoverable from the equalities alone — no extra side
/// channel is needed.
fn concat_parts_for(
    arena: &TermArena,
    eqs: &[(TermId, TermId)],
    w: SymbolId,
) -> Option<Vec<ConcatPart>> {
    for &(l, r) in eqs {
        let other = match (arena.node(l), arena.node(r)) {
            (TermNode::Symbol(a), _) if *a == w => r,
            (_, TermNode::Symbol(b)) if *b == w => l,
            _ => continue,
        };
        // A genuine concatenation, not a bare symbol/constant (a bare symbol is a
        // variable-variable equality handled by the union-find; a bare constant is a
        // pin the arrangement solves directly).
        if !matches!(
            arena.node(other),
            TermNode::App {
                op: Op::SeqConcat,
                ..
            }
        ) {
            continue;
        }
        let comps = axeyum_strings::normal_form::concat_components(arena, other);
        let mut parts = Vec::with_capacity(comps.len());
        for c in comps {
            if let TermNode::Symbol(s) = arena.node(c) {
                parts.push(ConcatPart::Var(*s));
            } else if let Ok(Value::Seq(elems)) =
                axeyum_ir::eval(arena, c, &axeyum_ir::Assignment::new())
            {
                parts.push(ConcatPart::Lit(seq_code_points(&elems)));
            } else {
                // A non-constant, non-variable component (should not occur for a
                // word-fragment concat) — decline the decomposition.
                return None;
            }
        }
        return Some(parts);
    }
    None
}

/// A code-point literal sequence as a `Regex` (concat of single-character
/// predicates; empty ⇒ `ε`). Mirrors `axeyum_smtlib`'s `literal_regex`.
fn literal_regex(cps: &[u32]) -> Regex {
    let mut acc: Option<Regex> = None;
    for &c in cps {
        let ch = Regex::character(c);
        acc = Some(match acc {
            None => ch,
            Some(prev) => Regex::concat(prev, ch),
        });
    }
    acc.unwrap_or(Regex::Empty)
}

/// Solves each membership equivalence class (grouped by the variable-variable word
/// equalities, exactly as [`StringTheory::check_membership_conflict`]) for a
/// concrete matcher-replayed witness, returning `symbol → witness code points` for
/// every symbol in a witnessed class. Returns `None` if any class has no witness
/// within budget (or is unexpectedly empty), so the caller reports `Unknown`.
///
/// A **membership-over-concat** operand `w` (one bound by `w = p₁ ++ p₂ ++ …`, see
/// [`concat_parts_for`]) is witnessed in a second stage: its witness is searched over
/// `R ∩ shape`, where `shape` concatenates each part's language — a first-stage
/// witness (as a fixed literal) for a constrained component variable, the literal for
/// a constant part, and `Σ*` for a free component variable. The intersection makes
/// `w`'s witness *decomposable* into the parts (so the caller's pin-and-resolve can
/// solve `w = p₁ ++ …` for the free components); the whole model still replays at the
/// `Seq` level, so a wrong `sat` is impossible even if `shape` were imprecise.
fn membership_witnesses(
    arena: &TermArena,
    eqs: &[(TermId, TermId)],
    pos_mem: &[(SymbolId, Regex)],
    neg_mem: &[(SymbolId, Regex)],
    budget: &SearchBudget,
) -> Option<HashMap<SymbolId, Vec<u32>>> {
    let mut uf = UnionFind::default();
    for &(op, _) in pos_mem.iter().chain(neg_mem) {
        uf.make(op);
    }
    // Merge classes on variable-variable equalities, and collect every symbol so we
    // can assign the class witness to non-membership members too.
    let mut all_syms: Vec<SymbolId> = Vec::new();
    for &(op, _) in pos_mem.iter().chain(neg_mem) {
        all_syms.push(op);
    }
    for &(l, r) in eqs {
        if let (TermNode::Symbol(a), TermNode::Symbol(b)) = (arena.node(l), arena.node(r))
            && matches!(arena.sort_of(l), Sort::Seq(_))
            && matches!(arena.sort_of(r), Sort::Seq(_))
        {
            let (a, b) = (*a, *b);
            uf.make(a);
            uf.make(b);
            uf.union(a, b);
            all_syms.push(a);
            all_syms.push(b);
        }
    }

    // Per class root: the membership problem.
    let mut classes: BTreeMap<SymbolId, Membership> = BTreeMap::new();
    for &(op, ref regex) in pos_mem {
        classes
            .entry(uf.find(op))
            .or_default()
            .positives
            .push(regex.clone());
    }
    for &(op, ref regex) in neg_mem {
        classes
            .entry(uf.find(op))
            .or_default()
            .negatives
            .push(regex.clone());
    }

    // Recover the concat structure of each membership operand (a `str.in_re` over a
    // `str.++`, rewritten by the parser to `w ∈ R ∧ w = parts`). A concat operand's
    // witness is deferred to a second stage so its parts' first-stage witnesses can
    // guide (shape) the search.
    let concat_parts: BTreeMap<SymbolId, Vec<ConcatPart>> = classes
        .keys()
        .filter_map(|&root| concat_parts_for(arena, eqs, root).map(|parts| (root, parts)))
        .collect();

    // Stage 1: witness the ordinary (non-concat) class roots.
    let mut witness_by_root: BTreeMap<SymbolId, Vec<u32>> = BTreeMap::new();
    for (root, problem) in &classes {
        if concat_parts.contains_key(root) {
            continue;
        }
        match problem.solve(budget) {
            axeyum_strings::MembershipOutcome::Sat(w) => {
                witness_by_root.insert(*root, w);
            }
            // On a theory-consistent branch the class is not certified-empty, but the
            // witness search may still be over budget (`Unknown`) — report no model.
            _ => return None,
        }
    }

    // Stage 2: witness each concat operand over `R ∩ shape`, the shape built from the
    // parts' Stage-1 witnesses (constrained), literals, or `Σ*` (free).
    for (root, parts) in &concat_parts {
        // The `R ∩ shape` intersection adds `Σ*` runs, so its derivative closure can
        // be markedly larger than a bare `R`. Cap the closure/witness search
        // conservatively (and bail on a past deadline) so a pathological concat regex
        // is a fast decline-to-`Unknown`, never a multi-second grind — the emptiness
        // closure itself does not poll the deadline.
        if budget.past_deadline() {
            return None;
        }
        let mut shape: Option<Regex> = None;
        let mut push = |r: Regex| {
            shape = Some(match shape.take() {
                None => r,
                Some(prev) => Regex::concat(prev, r),
            });
        };
        for part in parts {
            match part {
                ConcatPart::Lit(cps) => push(literal_regex(cps)),
                ConcatPart::Var(s) => match witness_by_root.get(&uf.find(*s)) {
                    Some(w) => push(literal_regex(w)),
                    None => push(Regex::star(Regex::any_char())),
                },
            }
        }
        let mut problem = classes.get(root).cloned().unwrap_or_default();
        problem.positives.push(shape.unwrap_or(Regex::Empty));
        // Witness-only (no emptiness pre-pass): the concat route never emits `unsat`,
        // and the emptiness closure over `R ∩ shape` does not poll the deadline, so a
        // pathological shape would grind. `Membership::witness` polls per node.
        match problem.witness(budget, CONCAT_WITNESS_MAX_STATES, CONCAT_WITNESS_MAX_LEN) {
            Some(w) => {
                witness_by_root.insert(*root, w);
            }
            None => return None,
        }
    }

    // Spread each class witness to every symbol in the class.
    let mut out: HashMap<SymbolId, Vec<u32>> = HashMap::new();
    for sym in all_syms {
        let root = uf.find(sym);
        if let Some(w) = witness_by_root.get(&root) {
            out.insert(sym, w.clone());
        }
    }
    Some(out)
}

/// Builds the `Seq(BitVec(18))` **term** for a witness's Unicode code points, as
/// the right-associated `seq.unit` chain (mirrors
/// `axeyum_smtlib::parse::seq_from_code_points`; the empty sequence is `seq.empty`).
///
/// Used to pin a membership-class symbol to its matcher-replayed witness as an extra
/// word equation, so the word arrangement solves the concat components consistently
/// with the witnessed whole. Returns `None` only on an arena construction failure
/// (never expected for the scalar string element sort).
fn seq_term_from_code_points(arena: &mut TermArena, codepoints: &[u32]) -> Option<TermId> {
    let key = ArraySortKey::BitVec(Sort::STRING_ELEM_WIDTH);
    if codepoints.is_empty() {
        return Some(arena.seq_empty(key));
    }
    let mut acc: Option<TermId> = None;
    for &cp in codepoints.iter().rev() {
        let elem = arena
            .bv_const(Sort::STRING_ELEM_WIDTH, u128::from(cp))
            .ok()?;
        let unit = arena.seq_unit(elem).ok()?;
        acc = Some(match acc {
            None => unit,
            Some(rest) => arena.seq_concat(unit, rest).ok()?,
        });
    }
    acc
}

/// The Unicode code points of a `Seq(BitVec(18))` string value's elements, for the
/// reference matcher. A non-scalar element (never produced by
/// [`seq_term_from_code_points`]) maps to `0`.
fn seq_code_points(elems: &[Value]) -> Vec<u32> {
    elems
        .iter()
        .map(|v| u32::try_from(v.scalar_code()).unwrap_or(0))
        .collect()
}

/// The largest solved string length the length↔LIA route will materialize as an
/// `'a'`-fill witness. A LIA model is free to pick a needlessly large length for an
/// under-constrained variable; capping keeps the witness build (and the subsequent
/// ground-evaluator replay) bounded and deterministic. Exceeding the cap declines to
/// `Unknown` — never a wrong verdict, since the cap only *misses* a witness.
const LENGTH_SAT_MAX_LEN: i128 = 20_000;

/// The `'a'`-fill code point (U+0061) — the canonical single-character filler whose
/// concatenation is length-homomorphic (`'a'^m ++ 'a'^n = 'a'^(m+n)`), so a length
/// assignment satisfying the concat length homomorphism yields string bindings that
/// satisfy the word `str.++` equalities automatically.
const FILL_CODE_POINT: u128 = 0x61;

/// Collects the distinct `Int`-sorted symbols reachable from `terms` (deterministic,
/// sorted by symbol id) — the free integer variables a length↔LIA model must bind
/// for the replay.
fn collect_int_symbols(arena: &TermArena, terms: &[TermId]) -> Vec<SymbolId> {
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    let mut visited = HashSet::new();
    let mut stack: Vec<TermId> = terms.to_vec();
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        match arena.node(t) {
            // A first-encounter `Int` symbol (the `seen.insert` side effect in the
            // guard dedups; a repeat / non-`Int` symbol falls to the `_` arm).
            TermNode::Symbol(sym) if arena.sort_of(t) == Sort::Int && seen.insert(*sym) => {
                out.push(*sym);
            }
            TermNode::App { args, .. } => {
                for &a in args {
                    stack.push(a);
                }
            }
            _ => {}
        }
    }
    out.sort_unstable_by_key(|s| s.index());
    out
}

/// The `Int`-valued length of a `Seq` term as a term over the fresh per-variable
/// length symbols `lmap` — pushing `len` through `str.++`
/// (`len(a++b) = len(a)+len(b)`), `seq.unit` (`1`), `seq.empty` (`0`), decoding a
/// string constant to its element count, and mapping a bare `Seq` variable to its
/// length symbol. Returns `None` for an opaque `Seq` term outside this fragment
/// (the caller then declines to `Unknown`).
fn abstract_length_of(
    arena: &mut TermArena,
    t: TermId,
    lmap: &HashMap<SymbolId, TermId>,
    memo: &mut HashMap<TermId, TermId>,
) -> Option<TermId> {
    if let Some(&c) = memo.get(&t) {
        return Some(c);
    }
    let node = arena.node(t).clone();
    let r = match node {
        TermNode::Symbol(s) => *lmap.get(&s)?,
        TermNode::App {
            op: Op::SeqConcat,
            args,
        } => {
            let mut acc: Option<TermId> = None;
            for a in args {
                let e = abstract_length_of(arena, a, lmap, memo)?;
                acc = Some(match acc {
                    None => e,
                    Some(prev) => arena.int_add(prev, e).ok()?,
                });
            }
            acc.unwrap_or_else(|| arena.int_const(0))
        }
        TermNode::App {
            op: Op::SeqUnit, ..
        } => arena.int_const(1),
        TermNode::App {
            op: Op::SeqEmpty(_),
            ..
        } => arena.int_const(0),
        _ => {
            // A folded string/sequence constant: decode to its element count.
            match axeyum_ir::eval(arena, t, &axeyum_ir::Assignment::new()) {
                Ok(Value::Seq(elems)) => arena.int_const(i128::try_from(elems.len()).ok()?),
                _ => return None,
            }
        }
    };
    memo.insert(t, r);
    Some(r)
}

/// Walks `t`, recording in `map` the length-abstraction replacement for every
/// `str.len` subterm (`SeqLen(w) → len_of(w)`) and every `Seq` equality atom
/// (`(= a b) → (= len_of(a) len_of(b))`, a **necessary** length condition of the
/// word equality). Both replacements are handed to
/// [`axeyum_rewrite::replace_subterms`] to build the pure `Bool`+`LIA` abstraction.
/// Returns `None` if a length cannot be abstracted (opaque `Seq` term).
fn collect_length_abstraction(
    arena: &mut TermArena,
    t: TermId,
    lmap: &HashMap<SymbolId, TermId>,
    map: &mut HashMap<TermId, TermId>,
    lenmemo: &mut HashMap<TermId, TermId>,
    visited: &mut HashSet<TermId>,
) -> Option<()> {
    if !visited.insert(t) {
        return Some(());
    }
    let node = arena.node(t).clone();
    match node {
        TermNode::App {
            op: Op::SeqLen,
            args,
        } => {
            let e = abstract_length_of(arena, args[0], lmap, lenmemo)?;
            map.insert(t, e);
        }
        TermNode::App { op: Op::Eq, args } if args.len() == 2 => {
            if matches!(arena.sort_of(args[0]), Sort::Seq(_)) {
                let la = abstract_length_of(arena, args[0], lmap, lenmemo)?;
                let lb = abstract_length_of(arena, args[1], lmap, lenmemo)?;
                let e = arena.eq(la, lb).ok()?;
                map.insert(t, e);
                // The `Seq` children are replaced wholesale — do not descend.
            } else {
                for a in args {
                    collect_length_abstraction(arena, a, lmap, map, lenmemo, visited)?;
                }
            }
        }
        TermNode::App { args, .. } => {
            for a in args {
                collect_length_abstraction(arena, a, lmap, map, lenmemo, visited)?;
            }
        }
        _ => {}
    }
    Some(())
}

/// The **length↔LIA `sat` bridge** (P2.7 Phase A, LenAbs): decides the
/// `str.len`-coupled `QF_SLIA` fragment the bounded packed encoder cannot witness
/// (its length is capped at `STRING_MAX_LEN`), by linking `str.len` to the LIA
/// solver Nelson-Oppen-style over fresh per-variable length symbols.
///
/// `assertions` is the parser's faithful, first-class `Seq`-level re-encoding of the
/// script's length-coupled fragment ([`axeyum_smtlib::Script::length_skeleton`]):
/// Boolean structure over `Seq` equality atoms and linear-`Int` atoms whose only
/// string content is `str.len` of a word.
///
/// The route:
/// 1. builds a pure `Bool`+`LIA` **length abstraction** — a fresh `Int` length
///    variable `len(x) ≥ 0` per `Seq` symbol, `str.len(w)` rewritten to the length
///    homomorphism over those, and each `Seq` equality atom rewritten to the
///    corresponding length equality (a necessary condition of the word equality);
/// 2. solves it with the exact LIA engine ([`crate::dpll_lia::check_with_arith_dpll`]);
/// 3. on a LIA `sat` model, binds each `Seq` symbol to an **`'a'`-fill** of its
///    solved length (length-homomorphic under `str.++`, so the word equalities
///    hold), binds each free `Int` symbol from the LIA model, and **replays the
///    combined model against `assertions` through the ground evaluator**.
///
/// **Soundness.** The route only ever returns [`CheckResult::Sat`] — and only when
/// the concrete `Seq`-level model **replays** against the original assertions (the
/// length abstraction is a mere *heuristic* for picking candidate lengths; the
/// replay is the sole `sat` gate, so a wrong `sat` is impossible even if the
/// abstraction were imprecise). It never returns `unsat` (the bounded `unsat` gate /
/// `StringGate` owns the length-abstraction refutation). A LIA `unsat`/`unknown`, a
/// length past the witness cap (`LENGTH_SAT_MAX_LEN`), or a non-replaying candidate
/// all degrade to [`CheckResult::Unknown`], leaving the caller's prior verdict
/// untouched.
#[must_use]
pub fn check_qf_slia_length(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> CheckResult {
    if assertions.is_empty() {
        return CheckResult::Unknown(unknown("no length-skeleton assertions"));
    }
    let seq_syms = collect_seq_symbols(arena, assertions);
    if seq_syms.is_empty() {
        return CheckResult::Unknown(unknown("length skeleton binds no Seq variable"));
    }

    // A fresh `Int` length symbol `len(x)` per `Seq` variable, `≥ 0`.
    let mut lmap: HashMap<SymbolId, TermId> = HashMap::new();
    let mut len_syms: Vec<(SymbolId, SymbolId)> = Vec::new(); // (seq sym, len sym)
    let mut zero_facts: Vec<TermId> = Vec::new();
    for (i, &sym) in seq_syms.iter().enumerate() {
        let Ok(len_sym) = arena.declare(&format!("!len!{i}"), Sort::Int) else {
            return CheckResult::Unknown(unknown("length symbol declaration failed"));
        };
        let len_term = arena.var(len_sym);
        lmap.insert(sym, len_term);
        len_syms.push((sym, len_sym));
        let zero = arena.int_const(0);
        let Ok(ge) = arena.int_ge(len_term, zero) else {
            return CheckResult::Unknown(unknown("length non-negativity fact build failed"));
        };
        zero_facts.push(ge);
    }

    // Build the pure Bool+LIA length abstraction: replace every `str.len`/`Seq`
    // equality atom with its length term / length equality.
    let mut repl: HashMap<TermId, TermId> = HashMap::new();
    let mut lenmemo: HashMap<TermId, TermId> = HashMap::new();
    let mut visited: HashSet<TermId> = HashSet::new();
    for &a in assertions {
        if collect_length_abstraction(arena, a, &lmap, &mut repl, &mut lenmemo, &mut visited)
            .is_none()
        {
            return CheckResult::Unknown(unknown(
                "length skeleton has an opaque Seq term outside the length↔LIA fragment",
            ));
        }
    }
    let mut abstraction: Vec<TermId> = Vec::with_capacity(assertions.len() + zero_facts.len());
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    for &a in assertions {
        match axeyum_rewrite::replace_subterms(arena, a, &repl, &mut memo) {
            Ok(t) => abstraction.push(t),
            Err(_) => {
                return CheckResult::Unknown(unknown("length abstraction rewrite failed"));
            }
        }
    }
    abstraction.extend(zero_facts);

    // Solve the abstraction with the exact LIA engine. No `sat` candidate (a LIA
    // `unsat`/`unknown` or an unsupported-fragment error) leaves the verdict as
    // `unknown` — the route never emits `unsat`.
    let Ok(CheckResult::Sat(model)) =
        crate::dpll_lia::check_with_arith_dpll(arena, &abstraction, config)
    else {
        return CheckResult::Unknown(unknown(
            "length↔LIA abstraction did not yield a sat length model",
        ));
    };

    // Assemble the concrete `Seq`-level model: each string an `'a'`-fill of its
    // solved length, each free `Int` symbol from the LIA model.
    let mut witness = Model::new();
    for &(seq_sym, len_sym) in &len_syms {
        let len = match model.get(len_sym) {
            Some(Value::Int(n)) => n,
            // An unconstrained length the LIA model left unbound is a free 0-length
            // choice (the empty string satisfies no length constraint on it).
            None => 0,
            _ => {
                return CheckResult::Unknown(unknown("length model bound a non-integer length"));
            }
        };
        if !(0..=LENGTH_SAT_MAX_LEN).contains(&len) {
            return CheckResult::Unknown(unknown(
                "solved string length is negative or exceeds the witness cap",
            ));
        }
        #[allow(clippy::cast_sign_loss)] // guarded `0 ≤ len ≤ LENGTH_SAT_MAX_LEN`
        let n = len as usize;
        let elems =
            vec![
                Value::from_scalar_code(Sort::BitVec(Sort::STRING_ELEM_WIDTH), FILL_CODE_POINT);
                n
            ];
        witness.set(seq_sym, Value::Seq(elems));
    }
    for int_sym in collect_int_symbols(arena, assertions) {
        if let Some(value) = model.get(int_sym) {
            witness.set(int_sym, value);
        }
    }

    // The sole `sat` gate: the concrete model must replay against the original
    // (faithful) assertions at the `Seq` level through the ground evaluator.
    if replays(arena, assertions, &witness) {
        CheckResult::Sat(witness)
    } else {
        CheckResult::Unknown(unknown(
            "length↔LIA candidate model did not replay against the assertions",
        ))
    }
}
