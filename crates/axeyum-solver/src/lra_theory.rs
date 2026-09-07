//! Linear real arithmetic (`QF_LRA`) on the **generic online CDCL(T) driver**
//! [`crate::cdclt::CdclT`] (ADR-0055 criterion 2, slice a-lra — the LRA companion
//! to the [`crate::lia_theory`] integer slice).
//!
//! [`crate::euf_egraph::check_qf_uf_online_cdclt`] proved the generic driver drives
//! EUF; [`crate::string_theory`] drives strings; [`crate::lia_theory`] drives integer
//! arithmetic. This module drives **linear real arithmetic** through the *same*
//! [`CdclT`], establishing that the one theory-agnostic search spine serves a fourth
//! theory. It is the CDCL(T)-driver counterpart to the self-contained
//! [`crate::lra_online::check_qf_lra_online`] search (whose `DPLL(T)` loop lives in
//! [`crate::lra_online`]): the Boolean skeleton, the Tseitin [`Encoder`], and the
//! incremental [`LraTheory`] are identical — only the search loop differs.
//!
//! ## Wrap, don't rewrite
//! The heavy lifting is the already-validated [`LraTheory`] from
//! [`crate::lra_online`]: it *is* a [`TheorySolver`] (`assert` re-decides real
//! feasibility of the live asserted set on the warm exact-rational simplex;
//! `push`/`pop` snapshot the assert stack in lockstep; conflict cores
//! are the Farkas-participating subset of asserted atoms). So this slice adds **no**
//! new arithmetic reasoning. The only gap between [`LraTheory`] and the generic
//! driver is the driver's documented *trigger-literal precondition*: its 1-UIP
//! conflict analysis requires every theory conflict to carry a
//! current-decision-level literal (the `c9d332c1` invariant). [`CdcltLraTheory`] is
//! a thin adapter that guarantees exactly that — see its docs.
//!
//! ## Granularity & propagation
//! - **Per-assert consistency (eager).** The wrapped [`LraTheory`] re-decides
//!   feasibility of the live set on every theory-atom assignment. This makes the
//!   theory **complete per assert**: a wrong `sat` is impossible because every total
//!   Boolean assignment is theory-checked. The simplex always terminates under
//!   Bland's rule and a deterministic pivot budget, but a check can still be
//!   expensive, so the caller's absolute
//!   deadline is threaded into every feasibility, propagation, and model-rebuild
//!   pass. Termination of the *driver* is the standard argument (each conflict,
//!   carrying its trigger literal, forces a strict backjump), with deadline/step
//!   budgets as backstops.
//! - **Propagation forwarded.** [`CdcltLraTheory::propagate`] forwards the
//!   already-validated [`LraTheory::propagate`] negation probes into the generic
//!   driver, so entailed order atoms can be assigned before a decision. Completeness
//!   still comes from per-assert feasibility; propagation is a pruning layer whose
//!   reasons are replayed as theory clauses by [`CdclT`].
//!
//! ## Soundness posture (no new trust surface over the offline route)
//! - `unsat` is a sound refutation. Its theory conflict clauses are `¬core` where
//!   `core` is a subset of asserted literals whose constraints carry a nonzero Farkas
//!   multiplier in the derived contradiction — the *same* explained-conflict
//!   machinery the offline [`crate::lra_online::check_qf_lra_online`] / the trusted
//!   [`crate::lra::check_with_lra`] route relies on; 1-UIP resolution over the mixed
//!   clause database is standard, model-independent inference. Tests gate every
//!   online `unsat` against those offline routes.
//! - `sat` is **not** trusted from the driver: a candidate real model is
//!   reconstructed from the live atoms ([`LraTheory::real_model`], materialized from
//!   the simplex's feasible point), Boolean skeleton leaves are injected
//!   from the driver trail, and the model is **replayed** against the original
//!   assertions — a non-replay yields [`CheckResult::Unknown`], never a wrong `sat`.
//! - Deadline-bounded (`config.timeout`) with the driver's step budget as the
//!   defense-in-depth backstop, so the search degrades to `Unknown` under a
//!   deterministic resource bound.
//!
//! The pure `QF_LRA` front door now tries this generic route first (ADR-0060's
//! 2026-07-09 update). Budget exhaustion is terminal for that query; structural
//! or arithmetic-incompleteness declines retain the established mixed fallback.

use std::collections::HashSet;
use std::time::Instant;

use axeyum_ir::{Sort, TermArena, TermId, TermNode, Value};

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::cdclt::{CdclT, Lit as CdcltLit, Outcome};
use crate::euf_egraph::{
    FinalCheckOutcome, PropagationQueue, TheoryEngineCounters, TheoryLit, TheoryProp, TheorySolver,
};
use crate::lra_online::{Encoder, Lit, LraTheory, LraTheoryBuildStop, collect_lra_atoms, replays};
use crate::model::Model;

/// The **memory budget** one online CDCL(T) LRA construction is allowed
/// (ADR-1752), in bytes. Used when `SolverConfig::memory_limit_mb` is unset;
/// when it is set, that is the budget.
///
/// # What this replaced, and why the count had to go
///
/// This was `MAX_ONLINE_LRA_ATOMS = 1_024`, a flat ceiling on the distinct-atom
/// count applied *before* normalization. It accounted for 23 of the 54 censused
/// `QF_LRA` losses and, per the `QF_NRA` lane's 2026-09-07 A/B, is the real gate
/// behind 62 `QF_NRA` losses as well — those queries reach it with 23,385 atoms
/// after the cross-product bound above it is lifted.
///
/// A count is the wrong currency. The construction's footprint is
/// `atoms x coefficients-per-atom`, so 23,385 atoms over a handful of variables
/// cost less than 1,492 atoms over 700 — and the count refused both identically.
/// The budget below is charged in the currency the cost is actually in, from the
/// builder's own deterministic coefficient counters, so it is machine-independent
/// and admits a wide-and-shallow query however many atoms it carries.
///
/// # The measurement, including the part that was stale
///
/// The count's own doc recorded that raising it to 16,384 made
/// `QF_LRA/sc/sc-39.base.cvc.smt2` (1,492 atoms) abort at the 8 GiB memory cap,
/// and named `AtomBuilder` normalization as the cost. That measurement was taken
/// on 2026-08-03 (`e62086742`). The bound that caps exactly that cost —
/// `MAX_LRA_CACHED_COEFFICIENTS`, on the linearization memo — landed on
/// 2026-08-06 (`96ff85930`), **three days later**. So the number the cap rested
/// on described a tree in which the thing it was protecting against was
/// unbounded, and it was never re-taken. The re-measurement is in
/// `docs/research/12-performance/lra-theory-side-2026-09-07.md`.
pub(crate) const DEFAULT_ONLINE_LRA_BUDGET_BYTES: usize =
    crate::lra_online::DEFAULT_ONLINE_LRA_BUDGET_BYTES;

/// Adapts the validated online [`LraTheory`] to the generic [`CdclT`] driver's
/// **trigger-literal precondition**.
///
/// [`LraTheory`] already implements [`TheorySolver`], so it could in principle be
/// handed to [`CdclT`] verbatim. The one behavioural gap is the driver's documented
/// precondition (the `c9d332c1` invariant): its 1-UIP analysis ([`CdclT`]) resolves
/// the conflict clause against current-decision-level literals, so **every theory
/// conflict must contain the just-asserted literal**, which sits at the current
/// level. [`LraTheory`]'s Farkas-derived cores almost always retain it — a
/// refutation of a set that was feasible before this assert *must* involve the new
/// constraint — but a degenerate multiplier vector (or the `rows_to_core` fallback
/// to the full asserted set, which does include it) could in principle name a core
/// the trigger is absent from. This wrapper closes that gap deterministically: on
/// any conflict it ensures the trigger literal `(index, value)` is present. Adding
/// one more *currently-asserted* literal to an `unsat` core keeps it `unsat` (a
/// superset of an infeasible set is infeasible), so `¬core` remains a valid theory
/// lemma — the fix is sound and never widens a verdict.
///
/// Theory propagation forwards the wrapped [`LraTheory`]'s checked negation-probe
/// entailments; see the module docs.
struct CdcltLraTheory {
    inner: LraTheory,
}

impl CdcltLraTheory {
    /// Wraps a fresh [`LraTheory`] over `atom_terms` (per-assert exact-rational
    /// feasibility), bounded by the online driver's absolute `deadline`.
    fn new(
        arena: &TermArena,
        atom_terms: &[TermId],
        deadline: Option<Instant>,
        budget_bytes: usize,
    ) -> Result<Self, LraTheoryBuildStop> {
        Ok(Self {
            // ADR-1701: this adapter is driven by `CdclT`, which calls
            // `final_check` at every total Boolean assignment, so the wrapped
            // theory may keep only the cheap bound check on `assert` and run
            // the complete simplex decision once per candidate model.
            inner: LraTheory::try_new_with_budget(arena, atom_terms, deadline, budget_bytes)?
                .with_deferred_final_check(),
        })
    }

    /// The wrapped theory, for model reconstruction after a `sat` verdict.
    fn inner(&self) -> &LraTheory {
        &self.inner
    }
}

impl TheorySolver for CdcltLraTheory {
    fn assert(&mut self, index: usize, value: bool) -> Result<(), Vec<TheoryLit>> {
        self.inner.assert(index, value).map_err(|mut core| {
            // Guarantee the driver's trigger-literal precondition: fold the
            // just-asserted (current-decision-level) literal into the core when the
            // Farkas core dropped it. Sound — a currently-asserted literal added to
            // an unsat core keeps it unsat (see the type docs).
            if !core.iter().any(|l| l.atom == index) {
                core.push(TheoryLit { atom: index, value });
            }
            core
        })
    }

    fn push(&mut self) {
        self.inner.push();
    }

    fn pop(&mut self) {
        self.inner.pop();
    }

    fn propagate(&self) -> Vec<TheoryProp> {
        self.inner.propagate()
    }

    /// Forwards the wrapped theory's complete check (ADR-1701). The driver
    /// backjumps to the highest level a final-check core names before analysing
    /// it, so — unlike an `assert` conflict — this core does not need the
    /// trigger literal folded in.
    fn final_check(&mut self) -> FinalCheckOutcome {
        self.inner.final_check()
    }

    /// Forwards the wrapped theory's queue-based propagation (ADR-1701).
    fn propagate_into(&mut self, queue: &mut PropagationQueue) {
        self.inner.propagate_into(queue);
    }

    /// Forwards the wrapped theory's engine counters (S4, diagnostic only).
    fn engine_counters(&self) -> Option<TheoryEngineCounters> {
        self.inner.engine_counters()
    }
}

/// Decides a `QF_LRA` query (an arbitrary Boolean combination of linear real
/// order/equality atoms) via the **generic online CDCL(T)** driver `CdclT` with
/// [`LraTheory`] as the theory (ADR-0055 criterion 2, slice a-lra). The
/// CDCL(T)-driver counterpart to [`crate::lra_online::check_qf_lra_online`]: the
/// skeleton, the Tseitin encoder, and the incremental theory are identical; the
/// search is the theory-agnostic `CdclT` that already drives EUF, strings, and
/// integer arithmetic.
///
/// Verdict discipline (see the module docs): `unsat` is a sound refutation carrying
/// no new trust surface over the offline route; `sat` is a driver assignment whose
/// reconstructed real model is **replayed** against the original assertions (a
/// non-replay is `Unknown`, never a wrong `sat`); the search is deadline-bounded.
///
/// Returns [`CheckResult::Unknown`] when there are no `LRA` atoms or the Boolean
/// skeleton has structure the encoder does not cover — the same conservative
/// give-ups as [`crate::lra_online::check_qf_lra_online`]. This is the default
/// first route for pure `QF_LRA`; non-budget incompleteness can still fall back.
///
/// # Errors
///
/// Never returns `Err` in this slice (every give-up is a conservative
/// [`CheckResult::Unknown`]); the [`SolverError`] return type matches the sibling
/// [`crate::lra_online::check_qf_lra_online`] for interchange.
// Linear route driver: atom collection, the ADR-1752 admission screen, Tseitin
// encoding, theory construction, the search, and model replay. Splitting it
// would hide the ORDER those stages run in, which is the thing a reader of this
// function needs.
#[allow(clippy::too_many_lines)]
pub fn check_qf_lra_online_cdclt(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));
    // Distinct real atoms — the theory's atom indices and the first `atom_count`
    // skeleton variables.
    let mut atom_terms: Vec<TermId> = Vec::new();
    let mut seen = HashSet::new();
    for &a in assertions {
        collect_lra_atoms(arena, a, &mut atom_terms, &mut seen);
    }
    if atom_terms.is_empty() {
        return Ok(CheckResult::Unknown(unknown(
            "no linear-real atoms for the online CDCL(T) LRA path",
        )));
    }

    let mut enc = Encoder::new(&atom_terms);
    let mut clauses: Vec<Vec<Lit>> = Vec::new();
    for &assertion in assertions {
        let Some(top) = enc.encode(arena, assertion, &mut clauses) else {
            return Ok(CheckResult::Unknown(unknown(
                "boolean skeleton outside the online CDCL(T) LRA encoder",
            )));
        };
        clauses.push(vec![Lit {
            var: top,
            positive: true,
        }]);
    }

    // The generic driver has its own literal type; the two are structurally
    // identical (var index + polarity).
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

    let atom_count = atom_terms.len();
    // ADR-1752: the budget is the caller's memory limit when it set one, and the
    // measured default otherwise. Nothing here caps the ATOM COUNT any more.
    let budget_bytes = config
        .memory_limit_mb
        .and_then(|mb| usize::try_from(mb).ok())
        .and_then(|mb| mb.checked_mul(1024 * 1024))
        .unwrap_or(DEFAULT_ONLINE_LRA_BUDGET_BYTES);
    // ADR-1752's outer, conservative admission screen. At the default budget this
    // is byte-identical to the `MAX_ONLINE_LRA_ATOMS = 1_024` count it replaces;
    // what changed is that it MOVES with the budget and says its numbers. See
    // `lra_online::BYTES_PER_ADMITTED_ATOM` for the three cost models that were
    // built, measured and falsified before settling for a screen.
    let admitted_atoms = budget_bytes / crate::lra_online::BYTES_PER_ADMITTED_ATOM;
    if atom_terms.len() > admitted_atoms {
        return Ok(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::ResourceLimit,
            detail: format!(
                "online CDCL(T) LRA admission screen: {} atoms exceeds the {admitted_atoms} \
                 a {} MiB budget admits (raise SolverConfig::memory_limit_mb)",
                atom_terms.len(),
                budget_bytes / (1024 * 1024),
            ),
        }));
    }
    let mut theory = match CdcltLraTheory::new(arena, &atom_terms, deadline, budget_bytes) {
        Ok(theory) => theory,
        Err(LraTheoryBuildStop::Deadline) => {
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::Timeout,
                detail: "timeout in the online CDCL(T) LRA driver while constructing its theory"
                    .to_owned(),
            }));
        }
        Err(LraTheoryBuildStop::ResourceLimit) => {
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::ResourceLimit,
                detail: "online CDCL(T) LRA normalization node ceiling exceeded".to_owned(),
            }));
        }
        // ADR-1752: a memory refusal states what it would have cost, what it was
        // allowed, and the shape it got there with. The flat atom cap said only
        // "1,493 > 1,024", which is why nobody could tell for a month whether it
        // was still load-bearing.
        Err(LraTheoryBuildStop::MemoryBudget {
            estimated_bytes,
            budget_bytes,
            atoms,
            vars,
        }) => {
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::ResourceLimit,
                detail: format!(
                    "online CDCL(T) LRA memory budget exceeded: projected {} MiB > budget {} MiB \
                     at {atoms} atoms over {vars} variables",
                    estimated_bytes / (1024 * 1024),
                    budget_bytes / (1024 * 1024),
                ),
            }));
        }
    };
    let mut solver = CdclT::new(enc.var_count, atom_count, driver_clauses, deadline);
    match solver.solve(&mut theory) {
        Outcome::Unsat => Ok(CheckResult::Unsat),
        Outcome::Unknown => Ok(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::Timeout,
            detail: "timeout in the online CDCL(T) LRA driver".to_owned(),
        })),
        Outcome::Sat => {
            // Reconstruct a real model from the live atoms (the simplex's feasible
            // point, materialized), inject Boolean skeleton leaves from
            // the driver trail, and replay against the originals — the soundness gate.
            let Some(mut model) = theory.inner().real_model() else {
                return Ok(CheckResult::Unknown(unknown(
                    "online CDCL(T) LRA model did not replay (arithmetic outside the incremental engine)",
                )));
            };
            add_boolean_leaf_values(arena, &enc, atom_count, &solver, &mut model);
            if replays(arena, assertions, &model) {
                Ok(CheckResult::Sat(model))
            } else {
                Ok(CheckResult::Unknown(unknown(
                    "online CDCL(T) LRA model did not replay (arithmetic outside the incremental engine)",
                )))
            }
        }
    }
}

/// Injects each genuine Bool skeleton leaf (a skeleton variable that is not a
/// registered `LRA` atom, so absent from the reconstructed real model) from the
/// driver trail. Additive and replay-gated by the caller, so it cannot manufacture a
/// wrong `sat`. Visited in sorted `(TermId, var)` order for determinism (`term_var`
/// is a `HashMap`).
fn add_boolean_leaf_values(
    arena: &TermArena,
    enc: &Encoder,
    atom_count: usize,
    solver: &CdclT,
    model: &mut Model,
) {
    let mut term_vars: Vec<(TermId, usize)> = enc.term_var.iter().map(|(&t, &v)| (t, v)).collect();
    term_vars.sort_by_key(|(term, _)| *term);
    for (term, var) in term_vars {
        if var < atom_count {
            continue; // a registered LRA atom, handled by the real model
        }
        if let TermNode::Symbol(symbol) = arena.node(term)
            && arena.sort_of(term) == Sort::Bool
            && let Some(value) = solver.value(var)
        {
            model.set(*symbol, Value::Bool(value));
        }
    }
}

/// A classified `unknown` reason for the online CDCL(T) LRA path.
fn unknown(detail: impl Into<String>) -> UnknownReason {
    UnknownReason {
        kind: UnknownKind::Incomplete,
        detail: detail.into(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lra::check_with_lra;
    use axeyum_ir::Rational;

    fn rvar(arena: &mut TermArena, name: &str) -> TermId {
        let s = arena.declare(name, Sort::Real).expect("declare real");
        arena.var(s)
    }

    fn rconst(arena: &mut TermArena, n: i128) -> TermId {
        arena.real_const(Rational::integer(n))
    }

    /// **This is the test the ADR-1752 budget is pinned by, and it is the exact
    /// inversion of the two tests it replaces.**
    ///
    /// 1,025 atoms of the form `xᵢ >= 0`, each over its own variable, is
    /// *wide and shallow*: one coefficient per atom, so the whole construction
    /// costs about 1,025 coefficients. The flat `MAX_ONLINE_LRA_ATOMS = 1_024`
    /// count refused it — and refused it identically to a query of the same
    /// atom count over 700 shared variables, which costs ~700x more. The budget
    /// is charged in coefficients, so this one is admitted.
    ///
    /// The assertion is on the REASON, not on the verdict: what changed is that
    /// the route is allowed to run, not that this particular query is decided.
    #[test]
    fn a_wide_shallow_atom_set_is_admitted_where_the_count_cap_refused_it() {
        let mut arena = TermArena::new();
        let zero = rconst(&mut arena, 0);
        let mut assertions = Vec::with_capacity(1_025);
        for index in 0..1_025 {
            let x = rvar(&mut arena, &format!("x{index}"));
            assertions.push(arena.real_ge(x, zero).expect("x>=0"));
        }
        // At the DEFAULT budget the screen still refuses this — deliberately, and
        // byte-identically to the `MAX_ONLINE_LRA_ATOMS = 1_024` it replaces, so
        // the shipped build's admission behaviour cannot have regressed.
        let CheckResult::Unknown(default_reason) =
            check_qf_lra_online_cdclt(&arena, &assertions, &SolverConfig::default())
                .expect("result")
        else {
            panic!("1,025 atoms must still be refused at the default budget");
        };
        assert_eq!(default_reason.kind, UnknownKind::ResourceLimit);
        assert!(
            default_reason.detail.contains("admission screen"),
            "the refusal must name the screen and its numbers: {}",
            default_reason.detail
        );
        assert!(
            default_reason
                .detail
                .contains("raise SolverConfig::memory_limit_mb"),
            "the refusal must say what to DO about it: {}",
            default_reason.detail
        );

        // And this is the whole point of ADR-1752: the gate MOVES. Before it,
        // no amount of memory bought a single atom past 1,024.
        let generous = SolverConfig::default().with_memory_limit_mb(4096);
        let result = check_qf_lra_online_cdclt(&arena, &assertions, &generous).expect("result");
        if let CheckResult::Unknown(reason) = &result {
            assert!(
                !reason.detail.contains("admission screen"),
                "a 4 GiB budget must admit 1,025 atoms: {}",
                reason.detail
            );
        }
    }

    /// **This is the test the budget's refusal path is pinned by.** A budget
    /// that can never refuse is not a budget, so this drives the route with a
    /// deliberately tiny `memory_limit_mb` and requires both that it refuses and
    /// that the refusal *states the numbers* — which is the whole complaint
    /// against the constant it replaces, whose message was "1493 > 1024" and
    /// left nobody able to tell whether it was still load-bearing.
    #[test]
    fn a_construction_over_its_memory_budget_refuses_and_names_the_numbers() {
        let mut arena = TermArena::new();
        let zero = rconst(&mut arena, 0);
        // Wide AND deep: each atom sums a fresh variable onto a growing chain, so
        // the coefficient count is quadratic in the atom count.
        let mut sum = rconst(&mut arena, 1);
        let mut assertions = Vec::new();
        for index in 0..400 {
            let x = rvar(&mut arena, &format!("x{index}"));
            sum = arena.real_add(sum, x).expect("chain");
            assertions.push(arena.real_ge(sum, zero).expect("sum>=0"));
        }
        // Driven at the THEORY constructor rather than through the route,
        // deliberately: the route's outer admission screen (a plain atom count,
        // see `lra_online::BYTES_PER_ADMITTED_ATOM`) fires first at any budget
        // small enough to starve the coefficient ceiling, so going through the
        // front door here would test the screen twice and this ceiling never.
        let stop = LraTheory::try_new_with_budget(&arena, &assertions, None, 1024 * 1024)
            .err()
            .expect("a construction over a 1 MiB budget must decline");
        let LraTheoryBuildStop::MemoryBudget {
            estimated_bytes,
            budget_bytes,
            atoms,
            ..
        } = stop
        else {
            panic!("the refusal must be the memory budget, not {stop:?}");
        };
        assert!(
            estimated_bytes > budget_bytes,
            "the refusal must report a projection that exceeds the budget: \
             {estimated_bytes} vs {budget_bytes}"
        );
        assert!(
            atoms > 0,
            "the refusal must say at what atom count it stopped"
        );

        // The SAME query under a generous budget must be BUILT — else the
        // refusal above is a blanket one and pins nothing.
        assert!(
            LraTheory::try_new_with_budget(&arena, &assertions, None, 4096 * 1024 * 1024).is_ok(),
            "the same query must fit a 4 GiB budget"
        );
    }

    /// The wrapper must always fold the just-asserted (current-level) literal into a
    /// conflict core — the driver's trigger-literal precondition.
    #[test]
    fn wrapper_conflict_core_carries_the_trigger() {
        // x < 0  and  x > 0: real-infeasible; the second assert triggers it.
        let mut arena = TermArena::new();
        let x = rvar(&mut arena, "x");
        let zero = rconst(&mut arena, 0);
        let lt = arena.real_lt(x, zero).expect("x<0");
        let gt = arena.real_gt(x, zero).expect("x>0");

        let mut theory =
            CdcltLraTheory::new(&arena, &[lt, gt], None, DEFAULT_ONLINE_LRA_BUDGET_BYTES)
                .expect("unbounded theory");
        assert!(theory.assert(0, true).is_ok());
        let core = theory.assert(1, true).expect_err("real-infeasible");
        assert!(
            core.iter().any(|l| l.atom == 1 && l.value),
            "conflict core must carry the just-asserted trigger literal (atom 1, true): {core:?}"
        );
    }

    /// A trigger the Farkas core keeps is not duplicated by the wrapper.
    #[test]
    fn wrapper_does_not_duplicate_a_kept_trigger() {
        let mut arena = TermArena::new();
        let x = rvar(&mut arena, "x");
        let zero = rconst(&mut arena, 0);
        let lt = arena.real_lt(x, zero).expect("x<0");
        let gt = arena.real_gt(x, zero).expect("x>0");

        let mut theory =
            CdcltLraTheory::new(&arena, &[lt, gt], None, DEFAULT_ONLINE_LRA_BUDGET_BYTES)
                .expect("unbounded theory");
        assert!(theory.assert(0, true).is_ok());
        let core = theory.assert(1, true).expect_err("infeasible");
        let occurrences = core.iter().filter(|l| l.atom == 1).count();
        assert_eq!(
            occurrences, 1,
            "trigger atom appears exactly once: {core:?}"
        );
    }

    /// The generic-driver wrapper must expose the underlying `LraTheory`
    /// propagation reasons unchanged: `x >= 1` entails `x > 0`.
    #[test]
    fn wrapper_forwards_lra_theory_propagation() {
        let mut arena = TermArena::new();
        let x = rvar(&mut arena, "x");
        let zero = rconst(&mut arena, 0);
        let one = rconst(&mut arena, 1);
        let ge_one = arena.real_ge(x, one).expect("x>=1");
        let gt_zero = arena.real_gt(x, zero).expect("x>0");

        let mut theory = CdcltLraTheory::new(
            &arena,
            &[ge_one, gt_zero],
            None,
            DEFAULT_ONLINE_LRA_BUDGET_BYTES,
        )
        .expect("unbounded theory");
        theory.assert(0, true).expect("x>=1 feasible");
        let props = theory.propagate();
        assert!(
            props.iter().any(|p| {
                p.lit.atom == 1 && p.lit.value && p.reason.iter().any(|r| r.atom == 0 && r.value)
            }),
            "expected propagation x>=1 entails x>0 with reason x>=1, got {props:?}"
        );
    }

    /// A strict-bound `unsat` (`x < 0 ∧ x > 0`) decided by the CDCL(T) driver, and
    /// confirmed `unsat` offline.
    #[test]
    fn strict_bounds_unsat_via_cdclt() {
        let mut arena = TermArena::new();
        let x = rvar(&mut arena, "x");
        let zero = rconst(&mut arena, 0);
        let lt = arena.real_lt(x, zero).expect("x<0");
        let gt = arena.real_gt(x, zero).expect("x>0");
        let assertions = [lt, gt];

        assert_eq!(
            check_qf_lra_online_cdclt(&arena, &assertions, &SolverConfig::default())
                .expect("decidable"),
            CheckResult::Unsat,
        );
        assert_eq!(
            check_with_lra(&arena, &assertions).expect("offline decidable"),
            CheckResult::Unsat,
            "offline route agrees",
        );
    }

    /// [`crate::layers::TheoryLayerStats`] must come back with real, nonzero
    /// content on a query that forces at least one theory conflict: the same
    /// `x < 0 ∧ x > 0` fixture as [`strict_bounds_unsat_via_cdclt`], but with
    /// collection enabled via [`crate::cdclt::TheoryLayerStatsGuard`]. This is
    /// the CDCL(T) counterpart to `BvLayerStats` coming back populated for the
    /// `sat-bv` backend.
    #[test]
    fn theory_layer_stats_are_populated_on_a_theory_conflict() {
        let mut arena = TermArena::new();
        let x = rvar(&mut arena, "x");
        let zero = rconst(&mut arena, 0);
        let lt = arena.real_lt(x, zero).expect("x<0");
        let gt = arena.real_gt(x, zero).expect("x>0");
        let assertions = [lt, gt];

        // Baseline: no guard, no collection — a caller who never opts in sees
        // no stats at all, and the query still decides the same way.
        assert_eq!(
            check_qf_lra_online_cdclt(&arena, &assertions, &SolverConfig::default())
                .expect("decidable"),
            CheckResult::Unsat,
        );

        let guard = crate::cdclt::TheoryLayerStatsGuard::enable();
        assert_eq!(
            check_qf_lra_online_cdclt(&arena, &assertions, &SolverConfig::default())
                .expect("decidable"),
            CheckResult::Unsat,
            "collection must never change the verdict",
        );
        let stats = crate::cdclt::last_theory_layer_stats()
            .expect("stats collected once the guard is active");
        drop(guard);

        assert!(
            stats.theory_conflicts >= 1,
            "x<0 ∧ x>0 must force at least one theory conflict: {stats:?}"
        );
        assert!(
            stats.theory_assert > std::time::Duration::ZERO,
            "at least one TheorySolver::assert call must be timed: {stats:?}"
        );
    }

    /// A disjunctive refutation needing the Boolean search: `(x<0 ∨ x>0) ∧ x=0`.
    #[test]
    fn disjunctive_refutation_via_cdclt() {
        let mut arena = TermArena::new();
        let x = rvar(&mut arena, "x");
        let zero = rconst(&mut arena, 0);
        let lt0 = arena.real_lt(x, zero).expect("x<0");
        let gt0 = arena.real_gt(x, zero).expect("x>0");
        let disj = arena.or(lt0, gt0).expect("or");
        let eq0 = arena.eq(x, zero).expect("x=0");

        assert_eq!(
            check_qf_lra_online_cdclt(&arena, &[disj, eq0], &SolverConfig::default())
                .expect("decidable"),
            CheckResult::Unsat,
        );
    }

    /// A `sat` instance: the reconstructed real model must replay.
    #[test]
    fn decides_sat_and_replays_via_cdclt() {
        let mut arena = TermArena::new();
        let x = rvar(&mut arena, "x");
        let five = rconst(&mut arena, 5);
        let ten = rconst(&mut arena, 10);
        let ge = arena.real_ge(x, five).expect("x>=5");
        let le = arena.real_le(x, ten).expect("x<=10");

        let verdict = check_qf_lra_online_cdclt(&arena, &[ge, le], &SolverConfig::default())
            .expect("decidable");
        assert!(
            matches!(verdict, CheckResult::Sat(_)),
            "expected sat: {verdict:?}"
        );
    }

    /// A zero-duration deadline must degrade to `Unknown`, never a verdict.
    #[test]
    fn deadline_yields_unknown() {
        let mut arena = TermArena::new();
        let x = rvar(&mut arena, "x");
        let zero = rconst(&mut arena, 0);
        let lt = arena.real_lt(x, zero).expect("x<0");
        let gt = arena.real_gt(x, zero).expect("x>0");
        let cfg = SolverConfig::default().with_timeout(std::time::Duration::ZERO);
        let r = check_qf_lra_online_cdclt(&arena, &[lt, gt], &cfg).expect("result");
        assert!(
            matches!(r, CheckResult::Unknown(_)),
            "zero-timeout → Unknown: {r:?}"
        );
    }

    /// Termination discipline: the eager [`LraTheory`] is complete and its
    /// Fourier–Motzkin feasibility check always terminates (no branch-and-bound), so
    /// the driver must decide within a tight, deterministic step budget — never trip
    /// it (a trip would signal a livelock). Runs several Boolean-structured shapes
    /// with a small budget and confirms each verdict matches the sibling online route.
    #[test]
    fn terminates_within_a_tight_step_budget() {
        let shapes: &[fn(&mut TermArena) -> Vec<TermId>] = &[
            // UNSAT strict bounds.
            |arena| {
                let x = rvar(arena, "x");
                let zero = rconst(arena, 0);
                vec![
                    arena.real_lt(x, zero).unwrap(),
                    arena.real_gt(x, zero).unwrap(),
                ]
            },
            // UNSAT disjunction ∧ pin.
            |arena| {
                let x = rvar(arena, "x");
                let zero = rconst(arena, 0);
                let lt0 = arena.real_lt(x, zero).unwrap();
                let gt0 = arena.real_gt(x, zero).unwrap();
                let disj = arena.or(lt0, gt0).unwrap();
                let eq0 = arena.eq(x, zero).unwrap();
                vec![disj, eq0]
            },
            // SAT bounded range.
            |arena| {
                let x = rvar(arena, "x");
                let y = rvar(arena, "y");
                let five = rconst(arena, 5);
                let ten = rconst(arena, 10);
                vec![
                    arena.real_ge(x, five).unwrap(),
                    arena.real_le(y, ten).unwrap(),
                ]
            },
        ];

        for (i, build) in shapes.iter().enumerate() {
            let mut arena = TermArena::new();
            let assertions = build(&mut arena);

            // Replicate the entry point but drive with a tight step budget so a
            // livelock trips it deterministically rather than hanging.
            let mut atom_terms: Vec<TermId> = Vec::new();
            let mut seen = HashSet::new();
            for &a in &assertions {
                collect_lra_atoms(&arena, a, &mut atom_terms, &mut seen);
            }
            let mut enc = Encoder::new(&atom_terms);
            let mut clauses: Vec<Vec<Lit>> = Vec::new();
            for &a in &assertions {
                let top = enc.encode(&arena, a, &mut clauses).expect("encodable");
                clauses.push(vec![Lit {
                    var: top,
                    positive: true,
                }]);
            }
            let driver_clauses: Vec<Vec<CdcltLit>> = clauses
                .iter()
                .map(|c| {
                    c.iter()
                        .map(|l| CdcltLit {
                            var: l.var,
                            positive: l.positive,
                        })
                        .collect()
                })
                .collect();
            let atom_count = atom_terms.len();
            let mut theory =
                CdcltLraTheory::new(&arena, &atom_terms, None, DEFAULT_ONLINE_LRA_BUDGET_BYTES)
                    .expect("unbounded theory");
            let mut solver = CdclT::new(enc.var_count, atom_count, driver_clauses, None)
                .with_step_budget(50_000);
            let outcome = solver.solve(&mut theory);
            assert!(
                !solver.step_budget_hit(),
                "shape {i}: LRA CDCL(T) driver tripped the step budget (livelock)"
            );
            assert_ne!(
                outcome,
                Outcome::Unknown,
                "shape {i}: Unknown with no deadline and no budget trip"
            );
            // Verdict must match the sibling online route on the same query.
            let sibling = crate::lra_online::check_qf_lra_online(
                &arena,
                &assertions,
                &SolverConfig::default(),
            )
            .expect("sibling decidable");
            match (&outcome, &sibling) {
                (Outcome::Unsat, CheckResult::Unsat) | (Outcome::Sat, CheckResult::Sat(_)) => {}
                (Outcome::Sat, CheckResult::Unsat) | (Outcome::Unsat, CheckResult::Sat(_)) => {
                    panic!("shape {i}: CDCL(T) {outcome:?} disagrees with sibling {sibling:?}")
                }
                other => panic!("shape {i}: unexpected pairing {other:?}"),
            }
        }
    }

    /// End-to-end through `CdclT`: the wrapper's forwarded propagation must assign
    /// an entailed theory atom before the driver needs to decide it.
    #[test]
    fn cdclt_driver_counts_forwarded_lra_propagation() {
        let mut arena = TermArena::new();
        let x = rvar(&mut arena, "x");
        let b_sym = arena.declare("b", Sort::Bool).expect("declare bool");
        let b = arena.var(b_sym);
        let zero = rconst(&mut arena, 0);
        let one = rconst(&mut arena, 1);
        let ge_one = arena.real_ge(x, one).expect("x>=1");
        let gt_zero = arena.real_gt(x, zero).expect("x>0");
        let clause = arena.or(gt_zero, b).expect("gt_zero or b");
        let assertions = [ge_one, clause];

        let mut atom_terms: Vec<TermId> = Vec::new();
        let mut seen = HashSet::new();
        for &a in &assertions {
            collect_lra_atoms(&arena, a, &mut atom_terms, &mut seen);
        }
        let mut enc = Encoder::new(&atom_terms);
        let mut clauses: Vec<Vec<Lit>> = Vec::new();
        for &a in &assertions {
            let top = enc.encode(&arena, a, &mut clauses).expect("encodable");
            clauses.push(vec![Lit {
                var: top,
                positive: true,
            }]);
        }
        let driver_clauses: Vec<Vec<CdcltLit>> = clauses
            .iter()
            .map(|c| {
                c.iter()
                    .map(|l| CdcltLit {
                        var: l.var,
                        positive: l.positive,
                    })
                    .collect()
            })
            .collect();
        let atom_count = atom_terms.len();
        let mut theory =
            CdcltLraTheory::new(&arena, &atom_terms, None, DEFAULT_ONLINE_LRA_BUDGET_BYTES)
                .expect("unbounded theory");
        let mut solver = CdclT::new(enc.var_count, atom_count, driver_clauses, None);

        assert_eq!(solver.solve(&mut theory), Outcome::Sat);
        assert!(
            solver.theory_propagations() > 0,
            "expected the LRA propagation path to fire"
        );
        assert_eq!(solver.value(1), Some(true), "x>0 should be propagated");
    }
}
