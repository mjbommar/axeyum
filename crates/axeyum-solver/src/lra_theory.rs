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
use crate::cdclt::Lit as CdcltLit;
use crate::euf_egraph::{
    FinalCheckOutcome, PropagationQueue, TheoryEngineCounters, TheoryLit, TheoryProp, TheorySolver,
};
use crate::lazy_smt_counters::OnlineProbe;
use crate::lra_online::{
    Encoder, Lit, LraOnlineLevers, LraTheory, LraTheoryBuildStop, collect_lra_atoms, replays,
};
use crate::model::Model;
use crate::native_cdclt::{NativeModel, NativeSolveOutcome};

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
/// The legacy flat atom ceiling, retained because
/// [`DEFAULT_ONLINE_LRA_BUDGET_BYTES`] is calibrated to reproduce it EXACTLY on
/// the default build, and because `nra.rs`'s projection screen compares against
/// it directly (ADR-1751 made NRA admission the consuming engine's atom
/// capacity, so the two must name the same number). Prefer the byte budget for
/// new code; this stays as the number ADR-1752's default is pinned to.
pub(crate) const MAX_ONLINE_LRA_ATOMS: usize = 1_024;

pub(crate) const DEFAULT_ONLINE_LRA_BUDGET_BYTES: usize =
    crate::lra_online::DEFAULT_ONLINE_LRA_BUDGET_BYTES;

/// Multiplier on the online admission screen's atom allowance (ADR-2111).
///
/// `1` is the shipped default and reproduces today's behaviour **exactly**; `n`
/// admits `n × admitted_atoms`. Read once from `AXEYUM_LRA_ATOM_SCREEN`, because
/// determinism is a public API promise and the screen must not move between two
/// solves in one process. An unrecognised value, `0`, or an unset variable is
/// `1`: this is a measurement lever and a typo in a sweep script must not change
/// a verdict.
///
/// # Why this is a LEVER and emphatically not a constant to raise
///
/// ADR-2111's census found the largest ADDRESSABLE bucket in `QF_LRA` is the 32
/// rows that die inside `lra.rs` before the simplex gets a system — **28 of 32
/// decided by some reference at the same budget** — and this screen is what
/// routes them there, at `admitted_atoms = budget / BYTES_PER_ADMITTED_ATOM`,
/// which is **exactly 1,024** at the default budget. The obvious move is to
/// raise it. The repository's own history says why that is a trap, and the
/// history is specific rather than cautionary:
///
/// **Three cost models were built to replace this screen and the corpus
/// falsified all three** (`ad2b40370`, recorded as a sized negative):
///
/// 1. *retained coefficients* — `_sanfoundry_10_ground.i_6_3_3.bpl_13.smt2`
///    went from a 0.82 s decline at 121 MB to a **7.8 GB abort**; those bytes
///    are not coefficients;
/// 2. *the dense tableau* — caught that file and **refused a file
///    Fourier–Motzkin decides** (`TM/p5-driverlogNumeric_s9.smt2`, `unsat` in
///    0.18 s at 41 MB); net 97 → 97, one gain and one loss;
/// 3. *Fourier–Motzkin's own allocations, bounded in bytes where they are made*
///    — correct as far as it goes, and `miplib/danoint-266.smt2` still reached
///    **7.8 GB in 11 s** where it had declined in 0.04 s at 15 MB, with
///    `simplex_rows=n/a` and `final_checks=1`.
///
/// That third result is the one that matters here. `simplex_rows=n/a` means the
/// simplex engine **did not exist**, so those 7.8 GB were never the tableau —
/// and ADR-2111's sparse tableau therefore **cannot have removed them**. What
/// the sparse storage does remove is cost model 2's quantity: the tableau is no
/// longer quadratic in the row count, so one of the things above this screen is
/// gone. At least one other, unidentified, is not.
///
/// `memory_budget.rs` says why nobody has named it: there is no
/// `#[global_allocator]` hook, so nothing at this altitude can attribute an
/// allocation it did not itself make.
///
/// **So the screen is not protecting one named mechanism — it is a conservative
/// stand-in for an allocation nobody has found**, and a lane that raises it owes
/// a measurement on the two files that defined the problem, by name:
/// `QF_LRA/miplib/danoint-266.smt2` and
/// `QF_LRA/2017-Heizmann-UltimateInvariantSynthesis/_sanfoundry_10_ground.i_6_3_3.bpl_13.smt2`.
/// Both are in ADR-2111's 93-row population; `danoint-266` is in the largest
/// addressable sub-bucket and z3 decides it `sat` in 2.3 s, so it is
/// simultaneously the best reason to raise the screen and the control that says
/// whether raising it is safe.
///
/// The related experiment has already been run and did NOT pay: [ADR-2045]
/// raised `memory_limit_mb` to 8 GiB, which moves this same screen to 13,107
/// atoms, and got **21 rows reaching the engine, 0 newly decided, and 19 dying
/// at "model did not replay"**. Opening the screen without fixing that wall
/// repeats that result.
pub(crate) fn atom_screen_multiplier() -> usize {
    static MULT: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *MULT.get_or_init(|| {
        std::env::var("AXEYUM_LRA_ATOM_SCREEN")
            .ok()
            .and_then(|v| v.trim().parse::<usize>().ok())
            .filter(|&n| n > 0)
            .unwrap_or(1)
    })
}

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
    /// feasibility), bounded by the online driver's absolute `deadline`, under
    /// the process-wide lever arms.
    #[cfg(test)]
    fn new(
        arena: &TermArena,
        atom_terms: &[TermId],
        deadline: Option<Instant>,
        budget_bytes: usize,
    ) -> Result<Self, LraTheoryBuildStop> {
        Self::new_with_levers(
            arena,
            atom_terms,
            deadline,
            budget_bytes,
            LraOnlineLevers::from_env(),
        )
    }

    /// [`Self::new`] with the ADR-2146 / ADR-2147 arms named by the caller.
    fn new_with_levers(
        arena: &TermArena,
        atom_terms: &[TermId],
        deadline: Option<Instant>,
        budget_bytes: usize,
        levers: LraOnlineLevers,
    ) -> Result<Self, LraTheoryBuildStop> {
        Ok(Self {
            // ADR-1701: this adapter is driven by `CdclT`, which calls
            // `final_check` at every total Boolean assignment, so the wrapped
            // theory may keep only the cheap bound check on `assert` and run
            // the complete simplex decision once per candidate model.
            // ADR-2147: the split is switched on HERE and nowhere else, because
            // this is the one adapter whose driver polls `take_new_atoms`.
            inner: LraTheory::try_new_with_budget_and_levers(
                arena,
                atom_terms,
                deadline,
                budget_bytes,
                levers,
            )?
            .with_deferred_final_check()
            .with_diseq_split(levers.diseq_split),
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

    /// Forwards the driver's branch notice (ADR-2122, diagnostic only).
    fn note_decision(&mut self, atom: usize, value: bool) {
        self.inner.note_decision(atom, value);
    }

    /// Forwards the ADR-2147 split registrations. Without this forwarder the
    /// trait default answers `0`, the driver never learns of the strict halves,
    /// and the lever is inert while looking armed — the ADR-2125 failure shape.
    fn take_new_atoms(&mut self) -> usize {
        self.inner.take_new_atoms()
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
    check_qf_lra_online_cdclt_with_levers(arena, assertions, config, LraOnlineLevers::from_env())
}

/// [`check_qf_lra_online_cdclt`] with the ADR-2146 / ADR-2147 arms passed as a
/// value, so one process can run every arm of both levers against each other
/// (the ADR-2132 fixture shape). The production caller reads the environment
/// once and calls this.
///
/// # Errors
///
/// As [`check_qf_lra_online_cdclt`]: never, in practice.
#[allow(clippy::too_many_lines)]
pub fn check_qf_lra_online_cdclt_with_levers(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    levers: LraOnlineLevers,
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
        crate::lazy_smt_counters::record_online_probe(OnlineProbe::NoAtoms);
        return Ok(CheckResult::Unknown(unknown(
            "no linear-real atoms for the online CDCL(T) LRA path",
        )));
    }

    let mut enc = Encoder::new(&atom_terms);
    let mut clauses: Vec<Vec<Lit>> = Vec::new();
    for &assertion in assertions {
        let Some(top) = enc.encode(arena, assertion, &mut clauses) else {
            crate::lazy_smt_counters::record_online_probe(OnlineProbe::SkeletonUnsupported);
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
    // ADR-2111: the multiplier is 1 on the shipped build, so `admitted_atoms` is
    // byte-identical to what it was; see `atom_screen_multiplier` for why this is
    // a lever and what a lane that moves it owes.
    let admitted_atoms = (budget_bytes / crate::lra_online::BYTES_PER_ADMITTED_ATOM)
        .saturating_mul(atom_screen_multiplier());
    if atom_terms.len() > admitted_atoms {
        crate::lazy_smt_counters::record_online_probe(OnlineProbe::AdmissionScreen);
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
    let mut theory = match CdcltLraTheory::new_with_levers(
        arena,
        &atom_terms,
        deadline,
        budget_bytes,
        levers,
    ) {
        Ok(theory) => theory,
        Err(LraTheoryBuildStop::Deadline) => {
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::Timeout,
                detail: "timeout in the online CDCL(T) LRA driver while constructing its theory"
                    .to_owned(),
            }));
        }
        Err(LraTheoryBuildStop::ResourceLimit) => {
            crate::lazy_smt_counters::record_online_probe(OnlineProbe::BuildNodeCeiling);
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
            crate::lazy_smt_counters::record_online_probe(OnlineProbe::BuildMemoryBudget);
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
    // The NATIVE proof-producing core, not `CdclT` (plan slice S7b step 4, this
    // lane). Same watch scheme, same order heap, same clause minimizer -- S1 and
    // S1b ported all three into `CdclT` verbatim so this is a swap and not a
    // reconciliation -- and, unlike `CdclT`, it emits a DRAT stream and
    // enumerates every clause the theory contributed, so a refutation can reach
    // the evidence layer as the ADR-1704 two-stream artifact instead of a bare
    // `unsat` whose theory reasoning is trusted and uncounted.
    let solved = crate::native_cdclt::solve_native(
        enc.var_count,
        atom_count,
        &driver_clauses,
        deadline,
        &mut theory,
    );
    match solved {
        NativeSolveOutcome::Unsat => {
            crate::lazy_smt_counters::record_online_probe(OnlineProbe::Took);
            Ok(CheckResult::Unsat)
        }
        // The driver reports one `Unknown` whatever produced it, so ask the
        // memory watchdog first: this route's Fourier–Motzkin fallback was
        // measured at 15.3 GB under an 8 GiB `memory_limit_mb` on 2026-09-08,
        // and reporting that as a TIMEOUT would send a reader to the clock when
        // the machine is what ran out. The flag is sticky for the life of the
        // guard, so a `Some` here is a real observation of this query having
        // been over budget.
        //
        // `Took` either way: the probe is recorded by what the engine DID, not
        // by what stopped it, and in both cases it built its theory and ran the
        // search. `dpll_t` separately refuses to fall through to the offline
        // loop on a `MemoryLimit` reason, which is where that distinction
        // belongs.
        NativeSolveOutcome::Unknown => {
            crate::lazy_smt_counters::record_online_probe(OnlineProbe::Took);
            Ok(CheckResult::Unknown(
                crate::memory_budget::watchdog_decline("online CDCL(T) LRA driver").unwrap_or(
                    UnknownReason {
                        kind: UnknownKind::Timeout,
                        detail: "timeout in the online CDCL(T) LRA driver".to_owned(),
                    },
                ),
            ))
        }
        NativeSolveOutcome::Sat(assignment) => {
            // Reconstruct a real model from the live atoms (the simplex's feasible
            // point, materialized), inject Boolean skeleton leaves from
            // the driver trail, and replay against the originals — the soundness gate.
            // THESE TWO ARMS ARE DIFFERENT FAILURES BEHIND ONE SENTENCE, and
            // ADR-2045 sized this division's capability wall from that sentence.
            // `real_model()` returning `None` is a RECONSTRUCTION failure (the
            // engine could not produce a point at all, for one of five reasons
            // `lra_online::model` now names); a model that fails `replays` was
            // produced and does not satisfy the originals, which is an encoding
            // or skeleton-leaf gap. `AXEYUM_LRAMODELPROBE=1` separates them.
            let Some(mut model) = theory.inner().real_model() else {
                crate::lazy_smt_counters::record_online_probe(OnlineProbe::ModelDidNotReplay);
                crate::lra_online::model_probe("lra_theory:no-model-reconstructed");
                return Ok(CheckResult::Unknown(unknown(
                    "online CDCL(T) LRA model did not replay (arithmetic outside the incremental engine)",
                )));
            };
            add_boolean_leaf_values(arena, &enc, atom_count, &assignment, &mut model);
            if replays(arena, assertions, &model) {
                crate::lazy_smt_counters::record_online_probe(OnlineProbe::Took);
                Ok(CheckResult::Sat(model))
            } else {
                crate::lazy_smt_counters::record_online_probe(OnlineProbe::ModelDidNotReplay);
                crate::lra_online::model_probe("lra_theory:model-built-but-does-not-replay");
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
    solver: &NativeModel,
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
    use crate::cdclt::{CdclT, Outcome};
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
    /// The atom-screen lever must default to the SHIPPED behaviour and must
    /// actually move the allowance when it is set (ADR-2111).
    ///
    /// Both halves matter and they fail in opposite directions. A lever whose
    /// default is not `1` has silently changed every build; a lever whose
    /// multiplier does not reach `admitted_atoms` is inert, and an inert arm in
    /// an A/B prints `net +0` — indistinguishable from a working arm that does
    /// not help. This lane has already been caught by the second shape once
    /// (`TableauReserve::Sparse` cannot reach the screen that refuses its target
    /// population), which is why the arithmetic is asserted here rather than
    /// inferred from the source.
    ///
    /// The default is asserted only when the variable is genuinely unset,
    /// because a test that passes only under an ambient env var is a gate on one
    /// shell.
    #[test]
    fn the_atom_screen_lever_defaults_to_one_and_multiplies_the_allowance() {
        if std::env::var_os("AXEYUM_LRA_ATOM_SCREEN").is_none() {
            assert_eq!(
                atom_screen_multiplier(),
                1,
                "with the lever unset the screen must admit exactly what it \
                 admitted before ADR-2111"
            );
        }
        assert_eq!(
            atom_screen_multiplier(),
            atom_screen_multiplier(),
            "the multiplier is read once and must not move within a process"
        );
        // The arithmetic the screen performs, at the default budget, derived
        // from the constants rather than written as literals -- a test repeating
        // `1024` would keep passing after someone moved `BYTES_PER_ADMITTED_ATOM`.
        let base = DEFAULT_ONLINE_LRA_BUDGET_BYTES / crate::lra_online::BYTES_PER_ADMITTED_ATOM;
        assert_eq!(
            base, MAX_ONLINE_LRA_ATOMS,
            "the byte budget must still reproduce the flat atom cap EXACTLY at \
             the default, or ADR-1752's calibration has drifted and the lever's \
             base arm is not the shipped one"
        );
        for mult in [1usize, 2, 8] {
            assert_eq!(
                base.saturating_mul(mult),
                base * mult,
                "the multiplier must scale the allowance, not saturate at it"
            );
        }
    }

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

    // ------------------------------------------------------------------
    // ADR-2147: the disequality split, through the CDCL(T) route, both arms
    // in ONE process.
    // ------------------------------------------------------------------

    const SPLIT_ON: LraOnlineLevers = LraOnlineLevers {
        admit_nonzeros: false,
        diseq_split: true,
    };

    /// `(not (= x y))` alone. The shipped arm builds the origin, which fails
    /// the replay gate, and answers `unknown` with the census's sentence; the
    /// split arm answers `sat` with a witness that replays. This is the 11-file
    /// wall in one line.
    #[test]
    fn a_bare_disequality_is_unknown_shipped_and_sat_split() {
        let mut arena = TermArena::new();
        let x = rvar(&mut arena, "x");
        let y = rvar(&mut arena, "y");
        let eq = arena.eq(x, y).expect("x=y");
        let neq = arena.not(eq).expect("x!=y");
        let config = SolverConfig::default();
        let shipped =
            check_qf_lra_online_cdclt_with_levers(&arena, &[neq], &config, LraOnlineLevers::off())
                .expect("result");
        let CheckResult::Unknown(reason) = shipped else {
            panic!("the shipped arm must not decide a bare disequality: {shipped:?}");
        };
        assert!(
            reason.detail.contains("did not replay"),
            "and it must stop at the replay gate, not elsewhere: {reason:?}"
        );
        let split = check_qf_lra_online_cdclt_with_levers(&arena, &[neq], &config, SPLIT_ON)
            .expect("result");
        let CheckResult::Sat(model) = split else {
            panic!("the split arm must decide x ≠ y: {split:?}");
        };
        assert!(
            replays(&arena, &[neq], &model),
            "and its witness must replay"
        );
    }

    /// SOUNDNESS-NEGATIVE, the `unsat` side: `x ≠ y ∧ x ≤ y ∧ x ≥ y` is
    /// infeasible. The split arm must refute it — and a split that turned the
    /// disequality into anything weaker than `x < y ∨ x > y`, or dropped the
    /// bound a true half imposes, would find a "model" here instead. The
    /// shipped arm cannot refute it at all (the dropped disequality leaves
    /// `x = y` feasible and the replay gate says `unknown`), which is the wall
    /// itself; what it must never do is say `sat`.
    #[test]
    fn a_split_never_manufactures_a_model_for_an_infeasible_disequality() {
        let mut arena = TermArena::new();
        let x = rvar(&mut arena, "x");
        let y = rvar(&mut arena, "y");
        let eq = arena.eq(x, y).expect("x=y");
        let neq = arena.not(eq).expect("x!=y");
        let le = arena.real_le(x, y).expect("x<=y");
        let ge = arena.real_ge(x, y).expect("x>=y");
        let config = SolverConfig::default();
        let shipped = check_qf_lra_online_cdclt_with_levers(
            &arena,
            &[neq, le, ge],
            &config,
            LraOnlineLevers::off(),
        )
        .expect("result");
        assert!(
            matches!(shipped, CheckResult::Unknown(_)),
            "the shipped arm stops at the replay gate on this shape: {shipped:?}"
        );
        let split =
            check_qf_lra_online_cdclt_with_levers(&arena, &[neq, le, ge], &config, SPLIT_ON)
                .expect("result");
        assert!(
            matches!(split, CheckResult::Unsat),
            "the split arm refutes x ≠ y with x ≤ y and x ≥ y, got {split:?}"
        );
    }

    /// SOUNDNESS-NEGATIVE, the `sat` side, and the one that pins the SHAPE of
    /// the trichotomy clause: `x ≤ y`, `x ≥ y`, and `x < 0 → x ≠ y`. The only
    /// models have `x = y ≥ 0`. The search decides atoms in collection order
    /// and true first, so it takes `x < 0` FIRST, which propagates `x ≠ y`;
    /// the point sits on the hyperplane, the halves are registered, each is
    /// refuted by a level-zero bound, and the trichotomy conflict fires with
    /// both halves false at level zero. The clause it learns must therefore
    /// carry `eq`: `eq ∨ lt ∨ gt` reduces to the unit `eq`, which refutes
    /// `x < 0` and the search finds `x = y`. A split whose clause dropped `eq`
    /// learns `lt ∨ gt` over two level-zero-false literals -- the empty clause
    /// -- and refutes a satisfiable query.
    ///
    /// The first fixture written for this ((x = y) ∨ (x ≠ y ∧ x < 0 ∧ x > 0))
    /// SURVIVED the mutation it was meant to catch: `eq` is decided true first
    /// and the disequality branch is never explored, so the split never runs.
    /// The mutation control is what said so.
    #[test]
    fn a_split_lemma_must_keep_the_equality_or_it_refutes_a_satisfiable_query() {
        let mut arena = TermArena::new();
        let x = rvar(&mut arena, "x");
        let y = rvar(&mut arena, "y");
        let zero = rconst(&mut arena, 0);
        let lt0 = arena.real_lt(x, zero).expect("x<0");
        let eq = arena.eq(x, y).expect("x=y");
        let not_lt0 = arena.not(lt0).expect("not");
        let neq = arena.not(eq).expect("x!=y");
        let guard = arena.or(not_lt0, neq).expect("x<0 -> x!=y");
        let le = arena.real_le(x, y).expect("x<=y");
        let ge = arena.real_ge(x, y).expect("x>=y");
        let assertions = [guard, le, ge];
        let config = SolverConfig::default();
        // The shipped arm takes the same first branch, builds the hyperplane
        // point, and stops at the replay gate: `unknown`, and never `unsat`.
        let shipped = check_qf_lra_online_cdclt_with_levers(
            &arena,
            &assertions,
            &config,
            LraOnlineLevers::off(),
        )
        .expect("result");
        assert!(
            matches!(shipped, CheckResult::Unknown(_)),
            "the shipped arm stops at the replay gate on this shape: {shipped:?}"
        );
        let split = check_qf_lra_online_cdclt_with_levers(&arena, &assertions, &config, SPLIT_ON)
            .expect("result");
        let CheckResult::Sat(model) = split else {
            panic!("the split arm must find x = y ≥ 0, got {split:?}");
        };
        assert!(replays(&arena, &assertions, &model), "the witness replays");
    }

    /// Several disequalities over shared variables, where a GREEDY choice of
    /// sides can paint itself into a corner: `a ≠ b`, `b ≠ c`, `a ≠ c` with
    /// `0 ≤ a, b, c ≤ 1`. The search must backtrack over the halves it
    /// registered and still find three distinct values; every one of the
    /// three splits is exercised and the model replays against all of them.
    #[test]
    fn three_mutual_disequalities_are_decided_by_backtracking_over_the_halves() {
        let mut arena = TermArena::new();
        let a = rvar(&mut arena, "a");
        let b = rvar(&mut arena, "b");
        let c = rvar(&mut arena, "c");
        let zero = rconst(&mut arena, 0);
        let one = rconst(&mut arena, 1);
        let mut assertions = Vec::new();
        for (p, q) in [(a, b), (b, c), (a, c)] {
            let eq = arena.eq(p, q).expect("eq");
            assertions.push(arena.not(eq).expect("neq"));
        }
        for v in [a, b, c] {
            assertions.push(arena.real_ge(v, zero).expect(">=0"));
            assertions.push(arena.real_le(v, one).expect("<=1"));
        }
        let config = SolverConfig::default();
        let verdict = check_qf_lra_online_cdclt_with_levers(&arena, &assertions, &config, SPLIT_ON)
            .expect("result");
        let CheckResult::Sat(model) = verdict else {
            panic!("three distinct reals in [0, 1] exist: {verdict:?}");
        };
        assert!(replays(&arena, &assertions, &model));
    }

    /// An `unsat` that FOLLOWS a split lemma carries what it carried before:
    /// the ADR-1704 two-stream artifact, checked `CheckedModuloLemmas` and not
    /// `Failed`. The split's clauses are theory lemmas like every Farkas core,
    /// enumerated in the same list and read by the same checker — and they
    /// mention variables the CNF did not declare (the strict halves), which is
    /// exactly what this pins: the extended formula must carry them, or the
    /// Boolean stream fails to check and a verdict this route used to certify
    /// modulo lemmas would silently lose its artifact.
    #[test]
    fn an_unsat_after_a_split_lemma_still_carries_the_two_stream_artifact() {
        let mut arena = TermArena::new();
        let x = rvar(&mut arena, "x");
        let y = rvar(&mut arena, "y");
        let eq = arena.eq(x, y).expect("x=y");
        let neq = arena.not(eq).expect("x!=y");
        let le = arena.real_le(x, y).expect("x<=y");
        let ge = arena.real_ge(x, y).expect("x>=y");
        let config = SolverConfig::default();
        let verdict = crate::native_cdclt::with_artifact_recording(|| {
            check_qf_lra_online_cdclt_with_levers(&arena, &[neq, le, ge], &config, SPLIT_ON)
        })
        .expect("result");
        assert!(matches!(verdict, CheckResult::Unsat), "got {verdict:?}");
        let artifact = crate::native_cdclt::take_last_theory_refutation()
            .expect("the native core recorded the refutation");
        assert!(
            artifact.theory_lemma_count() > 0,
            "a split refutation uses theory lemmas; a lemma-free artifact here means the \
             split never ran"
        );
        let check = artifact.check();
        assert!(
            matches!(
                check,
                axeyum_cnf::TheoryRefutationCheck::CheckedModuloLemmas { .. }
            ),
            "the artifact must check modulo its enumerated lemmas, got {check:?}"
        );
        let step = crate::trust::theory_refutation_trust_step(&artifact);
        assert_eq!(
            step.id,
            crate::trust::TrustId::SatRefutationModuloTheory,
            "the grade this route has always carried for a lemma-bearing refutation"
        );
    }

    /// The shipped arms are the ENVIRONMENT's arms when nothing is set, and the
    /// spellings are what the registry says: for the OFF-shipping nonzero
    /// admission `1` and `on` arm it and anything else is OFF; for the
    /// ON-shipping split `0` and `off` disarm it and anything else is ON. In
    /// both directions a typo measures the shipped route.
    #[test]
    fn the_lever_spellings_and_the_shipped_defaults() {
        use crate::lra_online::{parse_lever, parse_lever_default_on};
        assert!(parse_lever(Some("1")));
        assert!(parse_lever(Some("on")));
        assert!(parse_lever(Some(" ON ")));
        assert!(!parse_lever(Some("")));
        assert!(!parse_lever(Some("0")));
        assert!(!parse_lever(Some("off")));
        assert!(!parse_lever(Some("yes")));
        assert!(!parse_lever(Some("true")));
        assert!(!parse_lever(None));
        assert!(parse_lever_default_on(None));
        assert!(parse_lever_default_on(Some("")));
        assert!(parse_lever_default_on(Some("1")));
        assert!(parse_lever_default_on(Some("on")));
        assert!(parse_lever_default_on(Some("nonsense")));
        assert!(!parse_lever_default_on(Some("0")));
        assert!(!parse_lever_default_on(Some("off")));
        assert!(!parse_lever_default_on(Some(" OFF ")));
        assert_eq!(
            LraOnlineLevers::shipped(),
            LraOnlineLevers {
                admit_nonzeros: false,
                diseq_split: true,
            },
            "ADR-2147 ships the split ON and ADR-2146 ships the admission OFF"
        );
        if std::env::var_os("AXEYUM_LRA_ADMIT_NONZEROS").is_none()
            && std::env::var_os("AXEYUM_LRA_DISEQ_SPLIT").is_none()
        {
            assert_eq!(
                LraOnlineLevers::from_env(),
                LraOnlineLevers::shipped(),
                "with both variables unset the route must be the shipped one"
            );
        }
    }

    /// The default-carrying test, ADR-2140's shape: exactly this dies on a
    /// moved default. `x ≠ y` alone through the PRODUCTION entry point, with
    /// no lever named, is `sat` — the replay wall is gone from the shipped
    /// route. Skipped by name when the variable is set, because a test that
    /// passes only under an ambient value is a gate on one shell.
    #[test]
    fn the_shipped_route_decides_a_bare_disequality() {
        if std::env::var_os("AXEYUM_LRA_DISEQ_SPLIT").is_some() {
            return;
        }
        let mut arena = TermArena::new();
        let x = rvar(&mut arena, "x");
        let y = rvar(&mut arena, "y");
        let eq = arena.eq(x, y).expect("x=y");
        let neq = arena.not(eq).expect("x!=y");
        let verdict =
            check_qf_lra_online_cdclt(&arena, &[neq], &SolverConfig::default()).expect("result");
        let CheckResult::Sat(model) = verdict else {
            panic!("the shipped route must decide x ≠ y: {verdict:?}");
        };
        assert!(replays(&arena, &[neq], &model));
    }

    // ------------------------------------------------------------------
    // ADR-2146: the nonzero admission, through the CDCL(T) route.
    // ------------------------------------------------------------------

    /// A wide-shallow query (one variable per atom) under the online route's
    /// screen (`k ≤ 1_024`) whose dense tableau exceeds `MAX_TABLEAU_CELLS`
    /// only with the rows doubled — so equality atoms, two rows each:
    /// `k = 1_000` equalities is 2,000 rows over 3,000 columns, 6,000,000
    /// cells against 2,000 nonzeros. Both arms must decide it, and agree; the
    /// dense arm decides by Fourier–Motzkin over 1,000 variables (which the
    /// route's budget admits) and the sparse arm by the tableau.
    #[test]
    fn the_admission_arms_agree_through_the_route_on_a_query_the_dense_cap_refuses() {
        const K: usize = 1_000;
        const _: () = assert!(K <= MAX_ONLINE_LRA_ATOMS);
        const _: () = assert!(2 * K * (K + 2 * K) > crate::simplex::MAX_TABLEAU_CELLS);
        // The DENSE arm decides by the Fourier–Motzkin fallback, whose every
        // step polls the process-global memory watchdog; a concurrent test
        // that trips it for its own purposes (`trip_watchdog_for_test`, or a
        // real 1 GiB budget under a 4-thread sweep whose resident set is
        // mostly other tests) would make this arm decline for a reason that
        // has nothing to do with the admission. Serialized the way every
        // watchdog-touching test in `lra.rs` is.
        let _lock = crate::memory_budget::WATCHDOG_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        // ...and against the SCRIPTED resident-set probes (`sat_bv_backend`'s
        // memory tests install a real 1 GiB watchdog over scripted readings
        // that trip it), which serialize on the other lock. No test takes
        // both, so this order cannot deadlock.
        let _probe = crate::memory_budget::PROBE_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let mut arena = TermArena::new();
        let mut assertions = Vec::with_capacity(K);
        for i in 0..K {
            let x = rvar(&mut arena, &format!("e{i}"));
            let c = rconst(&mut arena, i128::try_from(i).expect("small"));
            assertions.push(arena.eq(x, c).expect("x=i"));
        }
        // Mechanism first: the two admissions really do differ on this shape.
        let dense = LraTheory::try_new_with_budget_and_levers(
            &arena,
            &assertions,
            None,
            DEFAULT_ONLINE_LRA_BUDGET_BYTES,
            LraOnlineLevers::off(),
        )
        .expect("built");
        assert!(
            !dense.uses_simplex(),
            "the dense cap must refuse 6,000,000 cells"
        );
        let sparse = LraTheory::try_new_with_budget_and_levers(
            &arena,
            &assertions,
            None,
            DEFAULT_ONLINE_LRA_BUDGET_BYTES,
            LraOnlineLevers {
                admit_nonzeros: true,
                diseq_split: false,
            },
        )
        .expect("built");
        assert!(
            sparse.uses_simplex(),
            "the nonzero admission must build 2,000 nonzeros"
        );
        let config = SolverConfig::default();
        for levers in [
            LraOnlineLevers::off(),
            LraOnlineLevers {
                admit_nonzeros: true,
                diseq_split: false,
            },
        ] {
            let verdict =
                check_qf_lra_online_cdclt_with_levers(&arena, &assertions, &config, levers)
                    .expect("result");
            let CheckResult::Sat(model) = verdict else {
                panic!("arm {levers:?}: 1,000 independent equalities are satisfiable: {verdict:?}");
            };
            assert!(
                replays(&arena, &assertions, &model),
                "arm {levers:?}: the witness replays"
            );
        }
        // And the infeasible neighbour: `e0 = 0` with `e0 > 0`.
        let e0 = arena.var(arena.find_symbol("e0").expect("declared"));
        let zero = rconst(&mut arena, 0);
        let mut infeasible = assertions.clone();
        infeasible.push(arena.real_gt(e0, zero).expect("e0>0"));
        for levers in [
            LraOnlineLevers::off(),
            LraOnlineLevers {
                admit_nonzeros: true,
                diseq_split: false,
            },
        ] {
            let verdict =
                check_qf_lra_online_cdclt_with_levers(&arena, &infeasible, &config, levers)
                    .expect("result");
            assert!(
                matches!(verdict, CheckResult::Unsat),
                "arm {levers:?}: e0 = 0 and e0 > 0 is unsat, got {verdict:?}"
            );
        }
    }
}
