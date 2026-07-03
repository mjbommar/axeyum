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
//! The theory's atoms are the equality atoms `(= s t)` collected from the
//! assertions ([`collect_eq_atoms`]). An atom is **representable** iff both sides
//! are `Seq`-sorted — then asserting it *true* records a word equality and
//! asserting it *false* records a word disequality. Any other atom (a non-`Seq`
//! equality) is declined: the theory treats it as an uninterpreted Boolean-only
//! atom (a no-op for the word core, exactly as [`EufTheory`](crate::euf_egraph)
//! treats a non-equality atom), keeping atom indices aligned with the caller's
//! variable numbering. The entry point [`check_qf_s_online_cdclt`] additionally
//! **declines the whole query** up front when a non-`Seq` equality atom is
//! present, so the online path only ever runs on the pure `QF_S` fragment.
//!
//! ## Verdict discipline (ADR-0053 / ADR-0054)
//!
//! - **`unsat`** is theory-driven *only* through a checked derivation. On every
//!   representable assertion the theory re-runs the T-B.7
//!   [`refute_word_equations`] refuter over the currently-asserted equalities and
//!   disequalities; a [`RefuteOutcome::Unsat`] is produced by
//!   `axeyum-strings` **only** behind its own independent `check_conflict` /
//!   `check_fact` re-checks. The theory maps the refuter's cited **original
//!   premise indices** back to the exact asserted literals that named them (this
//!   is what the word core's premise tracking buys us), so the theory conflict —
//!   and hence every 1-UIP lemma the driver learns from it — is a genuine theory
//!   entailment. A telemetry invariant ([`StringTheory::assert_conflicts_certified`])
//!   pins that no conflict is ever reported without a certified refutation behind
//!   it.
//! - **`sat`** is never trusted from the search. When the driver reaches a total,
//!   theory-consistent assignment the entry point runs
//!   [`solve_word_equations`] over the asserted set to obtain a concrete,
//!   `axeyum-strings`-replayed model, assembles a combined [`Model`], and
//!   **replays it against the original assertions** through the ground evaluator
//!   ([`replays`]). A non-replay (or a word search that finds no model) downgrades
//!   to [`CheckResult::Unknown`], never a wrong `sat`.
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

use std::collections::HashSet;
use std::time::Instant;

use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode, Value};
use axeyum_strings::{
    RefuteOutcome, SearchBudget, SearchOutcome, refute_word_equations, solve_word_equations,
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

/// Online word-level string theory over the CDCL(T) driver.
///
/// Owns a mutable borrow of the arena because the word core
/// ([`refute_word_equations`]) is re-run from arena terms on each representable
/// assertion (it is not incremental). Atom indices align with the driver's
/// variable numbering: the first `atoms.len()` skeleton variables are these atoms.
pub(crate) struct StringTheory<'a> {
    arena: &'a mut TermArena,
    /// Per atom index: the `Seq` equality sides `(l, r)`, or `None` for a
    /// non-representable atom (a no-op — treated as uninterpreted Boolean-only).
    atoms: Vec<Option<(TermId, TermId)>>,
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
    /// Backtrack trail: per [`StringTheory::push`], the
    /// `(active_eqs, active_diseqs, assigned_log)` lengths.
    trail: Vec<(usize, usize, usize)>,
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
    /// Builds the theory over `atom_sides` (per atom, its `Seq` equality sides or
    /// `None`), borrowing `arena` for the word core and using `budget` for the
    /// per-assert refuter.
    pub(crate) fn new(
        arena: &'a mut TermArena,
        atom_sides: Vec<Option<(TermId, TermId)>>,
        budget: SearchBudget,
    ) -> Self {
        let n = atom_sides.len();
        Self {
            arena,
            atoms: atom_sides,
            assigned: vec![None; n],
            assigned_log: Vec::new(),
            active_eqs: Vec::new(),
            active_diseqs: Vec::new(),
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
}

impl TheorySolver for StringTheory<'_> {
    fn assert(&mut self, atom: usize, value: bool) -> Result<(), Vec<TheoryLit>> {
        if self.assigned[atom].is_none() {
            self.assigned[atom] = Some(value);
            self.assigned_log.push(atom);
        }
        let Some((l, r)) = self.atoms[atom] else {
            // Non-representable atom: uninterpreted Boolean-only, nothing for the
            // word core to do (indices stay aligned).
            return Ok(());
        };
        if value {
            self.active_eqs.push((atom, (l, r)));
        } else {
            self.active_diseqs.push((atom, (l, r)));
        }
        self.check_conflict((atom, value))
    }

    fn push(&mut self) {
        self.trail.push((
            self.active_eqs.len(),
            self.active_diseqs.len(),
            self.assigned_log.len(),
        ));
    }

    fn pop(&mut self) {
        if let Some((eqs_len, diseqs_len, assigned_len)) = self.trail.pop() {
            self.active_eqs.truncate(eqs_len);
            self.active_diseqs.truncate(diseqs_len);
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
    // Distinct equality atoms — the theory's atom indices and the first
    // `atom_terms.len()` skeleton variables.
    let mut atom_terms: Vec<TermId> = Vec::new();
    let mut seen = HashSet::new();
    for &a in assertions {
        collect_eq_atoms(arena, a, &mut atom_terms, &mut seen);
    }
    if atom_terms.is_empty() {
        return CheckResult::Unknown(unknown(
            "no equality atoms for the online CDCL(T) string path",
        ));
    }

    // Scope gate: every equality atom must be `Seq`-sorted. A non-`Seq` equality
    // is outside the pure `QF_S` fragment this route decides — decline the whole
    // query rather than let the theory silently ignore it (which could otherwise
    // manufacture a Boolean model the replay would then have to catch).
    let mut atom_sides: Vec<Option<(TermId, TermId)>> = Vec::with_capacity(atom_terms.len());
    let mut any_seq = false;
    for &t in &atom_terms {
        match seq_eq_sides(arena, t) {
            Some(sides) => {
                any_seq = true;
                atom_sides.push(Some(sides));
            }
            None => {
                return CheckResult::Unknown(unknown(
                    "non-sequence equality atom outside the QF_S online CDCL(T) scope",
                ));
            }
        }
    }
    if !any_seq {
        return CheckResult::Unknown(unknown(
            "no sequence equality atoms for the online CDCL(T) string path",
        ));
    }

    // Encode the Boolean skeleton over the atoms with the shared Tseitin encoder.
    let mut enc = Encoder::new(&atom_terms);
    let mut clauses: Vec<Vec<Lit>> = Vec::new();
    for &assertion in assertions {
        let Some(top) = enc.encode(arena, assertion, &mut clauses) else {
            return CheckResult::Unknown(unknown(
                "boolean skeleton outside the online CDCL(T) encoder",
            ));
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
    let deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));
    let budget = word_budget(config);
    // The `Seq` symbols a model must bind (before the theory borrows the arena).
    let seq_syms = collect_seq_symbols(arena, &atom_terms);
    // A deterministic (TermId-sorted) view of the encoder's Bool-symbol variables,
    // for skeleton-only Bool injection after the search (`term_var` is a HashMap).
    let mut term_vars: Vec<(TermId, usize)> = enc.term_var.iter().map(|(&t, &v)| (t, v)).collect();
    term_vars.sort_by_key(|(term, _)| *term);

    let mut solver = CdclT::new(var_count, eq_count, driver_clauses, deadline);
    let mut theory = StringTheory::new(arena, atom_sides, budget.clone());
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
            // The driver reached a total, theory-consistent assignment. The refuter
            // is incomplete, so "no conflict" is not a model — search for a concrete,
            // replay-checked word model over the asserted set, then replay the
            // combined model against the ORIGINAL assertions.
            theory.assert_conflicts_certified();
            let eqs = theory.equalities();
            let diseqs = theory.disequalities();
            drop(theory); // release the arena borrow for the model search + replay
            string_sat_model(
                arena, assertions, &eqs, &diseqs, &budget, &seq_syms, &term_vars, &solver,
            )
        }
    }
}

/// Assembles and replay-checks a `sat` model on a theory-consistent branch: search
/// the asserted word system for a concrete, `axeyum-strings`-replayed assignment,
/// inject any skeleton-only Bool symbols from the solver trail, and replay the
/// combined [`Model`] against the original assertions. Returns
/// [`CheckResult::Unknown`] when no word model is found or the combined model does
/// not replay — never a wrong `sat`.
#[allow(clippy::too_many_arguments)]
fn string_sat_model(
    arena: &mut TermArena,
    assertions: &[TermId],
    eqs: &[(TermId, TermId)],
    diseqs: &[(TermId, TermId)],
    budget: &SearchBudget,
    seq_syms: &[SymbolId],
    term_vars: &[(TermId, usize)],
    solver: &CdclT,
) -> CheckResult {
    match solve_word_equations(arena, eqs, diseqs, budget) {
        SearchOutcome::Sat(assignment) => {
            let mut model = Model::new();
            for &sym in seq_syms {
                if let Some(value) = assignment.get(sym) {
                    model.set(sym, value);
                }
            }
            // Inject any skeleton-only Bool symbol (never a Seq atom side, so absent
            // from the word model) from the solver trail. Additive and replay-gated,
            // so it cannot manufacture a wrong `sat`.
            for (term, var) in term_vars {
                if let TermNode::Symbol(sym) = arena.node(*term)
                    && arena.sort_of(*term) == Sort::Bool
                    && model.get(*sym).is_none()
                    && let Some(value) = solver.value(*var)
                {
                    model.set(*sym, Value::Bool(value));
                }
            }
            if replays(arena, assertions, &model) {
                CheckResult::Sat(model)
            } else {
                CheckResult::Unknown(unknown(
                    "online CDCL(T) string model did not replay against the assertions",
                ))
            }
        }
        SearchOutcome::Unknown { .. } => CheckResult::Unknown(unknown(
            "online CDCL(T) string search found no replaying model on a \
             theory-consistent branch",
        )),
    }
}
