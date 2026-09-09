//! Lazy SMT (DPLL(T)) over linear real arithmetic, **combined with the
//! bit-blasted theories** (ADR-0015 follow-on).
//!
//! [`check_with_lra_dpll`] first sends pure linear-real Boolean structure through
//! the generic online [`crate::cdclt::CdclT`] + [`crate::lra_online::LraTheory`]
//! route. Structural or arithmetic-incompleteness declines retain the established
//! refinement loop below, which decides linear real constraints **and** bit-vector /
//! array / uninterpreted-function / bounded-integer constraints in one query.
//! Reals share no sort with those
//! theories, so the only coupling is propositional — making this lazy-SMT loop a
//! *complete* combination procedure (no interface-equality propagation needed).
//! Only the real atoms are abstracted to fresh Boolean propositions; every
//! non-real subterm is left intact for the bit-blasting composition
//! ([`crate::check_with_all_theories`]) to decide natively. It is the classic
//! lazy-SMT loop:
//!
//! 1. **Boolean abstraction.** Each distinct real order atom (`<`, `<=`, `>`,
//!    `>=`) is replaced by a fresh Boolean proposition, yielding a pure-Boolean
//!    skeleton over those propositions (and any original Boolean variables).
//! 2. **SAT.** The skeleton (plus learned blocking clauses) is solved by the
//!    pure-Rust [`SatBvBackend`]; a propositional model fixes each atom's truth.
//! 3. **Theory.** The chosen atom literals form a *conjunction*, decided by the
//!    exact-rational [`crate::check_with_lra`]. Theory-consistent → done; a
//!    theory conflict adds the blocking clause (the negation of the offending
//!    assignment) and the loop repeats.
//!
//! Termination is guaranteed: each round blocks at least one of the finitely
//! many atom assignments. **Trust:** a `sat` real model is replayed through the
//! ground evaluator against the *original* assertions, so neither the SAT search
//! nor the theory search can yield an unsound `sat`. Real **equality** atoms are
//! abstracted to `(a <= b) and (a >= b)`, so equality and **disequality** (the
//! negation `a < b or a > b`) are handled by the order-atom machinery and the
//! SAT case split.

use std::collections::HashMap;
use std::time::Duration;

use axeyum_ir::{Assignment, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};

// Native uses the std clock; wasm uses the `web_time` drop-in (ADR-0017).
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::combined::check_with_all_theories;
use crate::lazy_smt_counters::{CoreSource, LazySmtLoop, RoundOutcome};
use crate::lia::DEFAULT_INT_WIDTH;
use crate::lra::{
    FarkasCertificate, check_with_lra, check_with_lra_within_certified,
    lra_farkas_certificate_within,
};
use crate::model::Model;
use crate::sat_bv_backend::SatBvBackend;

/// A hard cap on lazy-SMT rounds, a backstop against a refinement bug (the loop
/// is otherwise bounded by the number of distinct atom assignments).
const MAX_ROUNDS: usize = 100_000;

/// How a lazy-SMT loop decides its propositional skeleton each round.
///
/// **The skeleton never changes between rounds.** Only the learned blocking
/// clauses grow, and they grow monotonically — a round adds clauses, never
/// retracts one. Rebuilding `skeleton.clone() + blocking` and handing it to a
/// cold [`SatBvBackend`] therefore re-bit-blasts an IDENTICAL formula and reruns
/// CDCL from scratch over a strictly larger clause set every round, so the
/// per-round cost rises with the round number.
///
/// # What that costs, measured 2026-09-09
///
/// The `QF_NRA` parity-loss population
/// (`bench-results/parity-losses-20260908/QF_NRA.txt`, 75 files, the largest
/// single division gap after the 2026-09-08 re-cut) was swept at the parity
/// protocol (24 s, 8 GiB, `taskset -c 0-7`) with `--trace`. On the
/// `LassoRanker` template family the loop's own counters read:
///
/// | file (abbrev)            | rounds | `skeleton_ms` | `theory_ms` |
/// |--------------------------|-------:|--------------:|------------:|
/// | `polyrank4…Loop_2`       |    313 |        23,702 |         225 |
/// | `Brockschmidt…Fig1`      |    217 |        23,649 |         273 |
/// | `heidy7…Lasso_2`         |    217 |        23,620 |         271 |
/// | `eric2…Loop_3`           |    153 |        23,448 |         444 |
/// | `spiral…Loop_4`          |    119 |        23,224 |         544 |
///
/// 97–99% of a 24 s budget in the propositional half, ~1% in the theory. The
/// per-round histogram is monotone in the round number — `polyrank4` reads
/// `nra_hist=2:3,3:12,4:23,5:34,6:61,7:118,8:62` with `nra_max_round=306`, i.e.
/// the first rounds cost ~4 ms and the last ~256 ms — which is the signature of
/// re-solving a growing formula from cold, not of a hard propositional problem.
///
/// The warm machinery for this already exists and is not new work: ADR-0009's
/// [`crate::incremental::IncrementalBvSolver`] takes monotone assertions over a
/// persistent lowering and CNF encoding, which is exactly the shape of "assert
/// the skeleton once, add one blocking clause per round".
///
/// # Why it is a policy and not a rewrite
///
/// The warm path is only applicable when the skeleton is a pure propositional
/// formula (see [`skeleton_is_pure_boolean`]); a skeleton that still carries
/// bit-vector, array, integer or uninterpreted content must go through the full
/// bit-blasting composition. Both arms are kept, selected by one value, so the
/// cold arm reproduces the pre-2026-09-09 behaviour byte for byte and an A/B is
/// one binary rather than two builds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SkeletonSolvePolicy {
    /// The arm's name, as `AXEYUM_LAZY_SKELETON` spells it. Carried so a trace
    /// or a registry row can name the arm that ran; nothing branches on it.
    pub name: &'static str,
    /// Keep ONE warm solver for the whole loop and add each round's blocking
    /// clause to it, instead of rebuilding a cold backend from
    /// `skeleton + blocking` every round.
    ///
    /// `false` is the pre-2026-09-09 behaviour on every loop.
    pub warm: bool,
}

impl SkeletonSolvePolicy {
    /// A cold [`SatBvBackend`] per round over `skeleton + blocking` — what every
    /// lazy-SMT loop did before 2026-09-09. Kept as the A/B control arm.
    pub const COLD: Self = Self {
        name: "cold",
        warm: false,
    };

    /// One [`crate::incremental::IncrementalBvSolver`] for the whole loop, with
    /// each blocking clause asserted as it is learned. Falls back to
    /// [`Self::COLD`] for a skeleton the warm solver does not cover.
    pub const WARM: Self = Self {
        name: "warm",
        warm: true,
    };
}

/// The skeleton-solve policy in force, read once from `AXEYUM_LAZY_SKELETON`.
///
/// Read once into a `OnceLock`: determinism is a public API promise, so the
/// policy cannot change between two solves in one process. `scripts/parity-run.sh`
/// records any `AXEYUM_*` lever it sees in the ledger entry, so a swept arm can
/// never be mistaken for a default-configuration one.
fn skeleton_solve_policy() -> SkeletonSolvePolicy {
    use std::sync::OnceLock;
    static POLICY: OnceLock<SkeletonSolvePolicy> = OnceLock::new();
    *POLICY.get_or_init(|| match std::env::var("AXEYUM_LAZY_SKELETON") {
        Ok(v) if v.trim() == "cold" => SkeletonSolvePolicy::COLD,
        Ok(v) if v.trim() == "warm" => SkeletonSolvePolicy::WARM,
        _ => SKELETON_SOLVE_DEFAULT,
    })
}

/// The arm used when `AXEYUM_LAZY_SKELETON` is unset or unrecognized.
///
/// **`COLD`, and set from the A/B, not from the mechanism.** The warm arm is a
/// 3–4x speedup of the propositional half where that half is not already the
/// whole budget — measured 2026-09-09 on the 16 skeleton-dominated `QF_NRA`
/// parity losses, one binary, arms differing only in this env override:
///
/// | file                          | cold `skeleton_ms` | warm `skeleton_ms` |
/// |-------------------------------|-------------------:|-------------------:|
/// | `atan-vega-3-chunk-0242`      |              1,211 |                263 |
/// | `sin-cos-346-b-chunk-0419`    |                480 |                122 |
/// | `MulliganEconomicsModel0051a` |              1,674 |                570 |
/// | `sqrt-1mcosq-8-chunk-0627`    |                147 |                 35 |
///
/// and it **decided nothing new**: cold 2 of 16, warm 2 of 16, the same two
/// files. On the seven `LassoRanker` files it is a wash (23,708 → 23,323 ms),
/// because there the cost is the CDCL search over a few hundred whole-cube
/// blocking clauses, not the re-encoding the warm arm removes.
///
/// So the default stays `COLD` for a reason about EVIDENCE, not about the
/// mechanism: this switch changes the propositional half of **every** lazy-SMT
/// query in the workspace — `QF_LRA`, `QF_NRA`, and every combination that runs
/// through these two loops — and 16 files of one division is not a basis for
/// that. A division-wide A/B is now one binary and one env var; whoever runs it
/// owns flipping this line. The cold arm is byte-identical to the pre-2026-09-09
/// engine, confirmed against the same population's baseline sweep (identical
/// verdicts on all 16, `sin-problem-7-chunk-0353` 1,909 ms vs 1,909 ms,
/// `sqrt-1mcosq-8-chunk-0627` 306 ms vs 308 ms).
///
/// Full record: `docs/research/12-performance/qf-nra-loss-attribution-2026-09-09.md`.
const SKELETON_SOLVE_DEFAULT: SkeletonSolvePolicy = SkeletonSolvePolicy::COLD;

/// Whether every node reachable from `terms` is `Bool`-sorted and built only
/// from Boolean connectives, constants and `Bool` symbols.
///
/// This is the applicability test for the warm arm. It is deliberately a
/// whitelist over the node kinds rather than a sort test alone: a `Bool`-sorted
/// `Op::Apply` (an uninterpreted predicate) or a `Bool`-sorted `Op::Eq` over
/// non-`Bool` operands would pass a sort test while carrying theory content the
/// warm solver must not silently drop. Anything not on the list declines, and a
/// decline costs only the cold arm we would have run anyway.
fn skeleton_is_pure_boolean(arena: &TermArena, terms: &[TermId]) -> bool {
    let mut seen: std::collections::HashSet<TermId> = std::collections::HashSet::new();
    let mut stack: Vec<TermId> = terms.to_vec();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        // GUARD 1 — the sort of EVERY node, not just the roots. `Eq` and `Ite`
        // are polymorphic and `Bool` at the root, so a root-only test admits
        // `(= x y)` over two reals. This is what excludes it, and it is the
        // ONLY thing that does.
        if arena.sort_of(t) != Sort::Bool {
            return false;
        }
        match arena.node(t) {
            TermNode::BoolConst(_) => {}
            TermNode::Symbol(_) => {}
            // GUARD 2 — the operator whitelist. A `Bool`-sorted THEORY atom
            // (`x < 0`, `bvult a b`, an uninterpreted predicate) passes guard 1
            // unharmed; only this refuses it.
            TermNode::App { op, args } => {
                match op {
                    Op::BoolNot
                    | Op::BoolAnd
                    | Op::BoolOr
                    | Op::BoolXor
                    | Op::BoolImplies
                    | Op::Ite
                    | Op::Eq => {}
                    _ => return false,
                }
                for &a in args.iter() {
                    stack.push(a);
                }
            }
            // Every non-`Bool` constant node. Unreachable through guard 1
            // today, kept because the match must be total and a silent
            // `true` here would be the wrong direction.
            _ => return false,
        }
    }
    true
}

/// The propositional half of a lazy-SMT loop: either a cold backend rebuilt from
/// `skeleton + blocking` every round ([`SkeletonSolvePolicy::COLD`]) or one warm
/// solver carried across rounds ([`SkeletonSolvePolicy::WARM`]).
///
/// The two arms decide the SAME set of clauses in every round — the warm arm
/// holds the skeleton plus every blocking clause learned so far, which is
/// exactly what the cold arm rebuilds — so the round's verdict cannot differ
/// between them. Only the cost does.
enum SkeletonSolver {
    /// The cold arm: one `SatBvBackend`, re-fed the whole formula each round.
    Cold(SatBvBackend),
    /// The warm arm: the skeleton asserted once, blocking clauses appended.
    Warm {
        solver: Box<crate::incremental::IncrementalBvSolver>,
        /// How many entries of the caller's `blocking` vector have already been
        /// asserted into `solver`. The caller only ever pushes, so the tail past
        /// this index is exactly what is new this round.
        asserted_blocking: usize,
    },
}

impl SkeletonSolver {
    /// Builds the solver for `policy`, asserting `skeleton` up front on the warm
    /// arm. Falls back to the cold arm when the skeleton is out of the warm
    /// arm's scope, or when asserting it fails — a fallback costs only the cold
    /// work we would otherwise have done, and never changes a verdict.
    fn new(
        policy: SkeletonSolvePolicy,
        arena: &TermArena,
        skeleton: &[TermId],
        config: &SolverConfig,
    ) -> Self {
        if !policy.warm || !skeleton_is_pure_boolean(arena, skeleton) {
            return Self::Cold(SatBvBackend::new());
        }
        let mut solver = Box::new(crate::incremental::IncrementalBvSolver::with_config(
            config.clone(),
        ));
        for &term in skeleton {
            if solver.assert(arena, term).is_err() {
                return Self::Cold(SatBvBackend::new());
            }
        }
        Self::Warm {
            solver,
            asserted_blocking: 0,
        }
    }

    /// Decides `skeleton + blocking` for this round under `config`'s timeout.
    ///
    /// `blocking` is the caller's whole learned-clause vector, append-only. The
    /// warm arm asserts just the tail it has not seen; the cold arm rebuilds the
    /// full formula, as it always did.
    fn solve_round(
        &mut self,
        arena: &mut TermArena,
        skeleton: &[TermId],
        blocking: &[TermId],
        config: &SolverConfig,
    ) -> Result<CheckResult, SolverError> {
        match self {
            Self::Cold(backend) => {
                let mut sat_assertions = skeleton.to_vec();
                sat_assertions.extend(blocking.iter().copied());
                check_with_all_theories(backend, arena, &sat_assertions, DEFAULT_INT_WIDTH, config)
            }
            Self::Warm {
                solver,
                asserted_blocking,
            } => {
                for &clause in &blocking[*asserted_blocking..] {
                    solver.assert(arena, clause)?;
                }
                *asserted_blocking = blocking.len();
                solver.set_timeout(config.timeout);
                solver.check(arena)
            }
        }
    }
}

/// Decides a Boolean combination of linear real order constraints by lazy SMT.
///
/// The returned [`Model`] carries real variable values (and original Boolean
/// variable values) and replays against the original assertions.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] if an assertion is outside Boolean
/// structure over real order atoms (e.g. a real equality atom, or a non-real
/// arithmetic atom), or [`SolverError`] from the underlying SAT backend; a
/// `sat` model that fails to replay is a [`SolverError::Backend`].
pub fn check_with_lra_dpll(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    // Derive the absolute deadline from the configured budget, then delegate.
    let deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));
    check_with_lra_dpll_within(arena, assertions, config, deadline)
}

/// Whether `deadline` (if set) has passed.
fn past_deadline(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|d| Instant::now() >= d)
}

/// Re-bases a relative solver timeout onto the caller-owned absolute deadline
/// after the online probe has consumed part of the budget.
fn config_with_remaining_deadline(
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> SolverConfig {
    let Some(deadline) = deadline else {
        return config.clone();
    };
    let mut fallback = config.clone();
    fallback.timeout = Some(deadline.saturating_duration_since(Instant::now()));
    fallback
}

/// Lazy-SMT entry that respects an **absolute** wall-clock `deadline` (rather
/// than re-deriving one from `config.timeout`, which would reset the clock on
/// every call). The deadline is checked once per refinement round, so a caller
/// that already started the clock — e.g. the NRA branch-and-bound / refinement
/// loop, which can issue many of these solves on a growing system — bails to a
/// timely `unknown` instead of overrunning its budget inside one solve.
///
/// `deadline == None` means "no wall-clock bound" (the loop is still bounded by
/// `MAX_ROUNDS`). Bailing to `unknown` is sound: `unknown` is first-class and
/// the deadline never converts a `sat`/`unsat` into a wrong verdict.
///
/// # Errors
///
/// Same as [`check_with_lra_dpll`].
pub fn check_with_lra_dpll_within(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> Result<CheckResult, SolverError> {
    // Prefer the shared generic CDCL(T) spine for pure Boolean-structured LRA.
    // Mixed real+BV/array/UF shapes decline its skeleton encoder quickly and retain
    // the established abstraction/refinement loop below. A pure-LRA timeout owns
    // the caller's remaining budget and returns directly; only structural or
    // arithmetic-incompleteness declines fall through to the legacy mixed route.
    let probe_config = config_with_remaining_deadline(config, deadline);
    let route = crate::lra_route::configured();
    match crate::lra_theory::check_qf_lra_online_cdclt(arena, assertions, &probe_config)? {
        result @ (CheckResult::Sat(_) | CheckResult::Unsat) => return Ok(result),
        // A `Timeout`/`ResourceLimit` decline USED to end the query
        // unconditionally, on the reading that the online engine had owned the
        // caller's budget. That is true of a timeout and false of the ADR-1752
        // admission screen and the two build ceilings, which refuse in
        // microseconds on a structural property of the input — leaving the
        // budget entirely unspent and the offline loop, which is exactly their
        // fallback, unrun. `past_deadline` is the observation that separates
        // the two, so the rule tests it instead of the reason kind.
        //
        // `MemoryLimit` is the exception the memory-watchdog lane established
        // and it is NOT a cheap decline: the flag is sticky, so the reason says
        // the PROCESS is already over `memory_limit_mb`. Falling through would
        // start a whole second search — its own skeleton, its own tableaux — on
        // a process that has nothing left to spend, which is the same reasoning
        // as `lra.rs`'s `Feasibility::OutOfMemory` arm declining to retry on the
        // simplex. It ends the query whatever the policy arm says.
        CheckResult::Unknown(reason)
            if past_deadline(deadline)
                || reason.kind == UnknownKind::MemoryLimit
                || (!route.fall_through_on_cheap_decline
                    && matches!(
                        reason.kind,
                        UnknownKind::Timeout | UnknownKind::ResourceLimit
                    )) =>
        {
            return Ok(CheckResult::Unknown(reason));
        }
        CheckResult::Unknown(_) => {}
    }
    let fallback_config = config_with_remaining_deadline(config, deadline);

    // 1. Boolean abstraction: skeleton terms + the atom map.
    let mut ctx = Abstractor::default();
    let mut skeleton = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        skeleton.push(ctx.abstract_term(arena, assertion)?);
    }

    let mut solver =
        SkeletonSolver::new(skeleton_solve_policy(), arena, &skeleton, &fallback_config);
    let mut blocking: Vec<TermId> = Vec::new();
    // The previous round's cube polarities, for the churn counter. The question
    // the Farkas fix left open: the loop now runs 1.63x the rounds and still
    // loses, so either each round hands the theory a genuinely different problem
    // or it hands it nearly the same one and pays a cold decision for it. Only
    // allocated when counting is armed.
    let mut previous_cube: Option<Vec<bool>> = None;
    // The route trail labels this whole function `nra` and reports its share of
    // the budget; nothing said how that time divides between the two halves of
    // a round, or how many rounds there were. On the 22 `QF_LRA` files that
    // print no theory-layer line, this loop is where the budget goes.
    crate::lazy_smt_counters::record_entry(LazySmtLoop::Lra, ctx.atoms.len() as u64);

    for _ in 0..MAX_ROUNDS {
        // Wall-clock bound: the per-round SAT+theory work grows as blocking
        // clauses accumulate, so a long-running solve must bail here rather than
        // overrun the caller's deterministic budget (#15).
        if past_deadline(deadline) {
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::ResourceLimit,
                detail: "lazy SMT: wall-clock timeout reached".to_owned(),
            }));
        }
        // Memory bound, at the same boundary and for the same reason: the
        // per-round work grows as blocking clauses accumulate, so this loop is
        // where an over-budget process spends the rest of its life. One relaxed
        // atomic load, and it reports the memory reason rather than borrowing
        // the timeout's — the two demand opposite fixes.
        if let Some(reason) = crate::memory_budget::watchdog_decline("lazy SMT refinement round") {
            return Ok(CheckResult::Unknown(reason));
        }
        // 2. Decide the skeleton (real atoms abstracted to props; every other
        //    theory — bit-vectors, arrays, functions, bounded integers — left
        //    intact) plus learned blocking clauses, with the full bit-blasting
        //    composition. Reals share no sort with those theories, so the only
        //    coupling is propositional and this loop is a complete combination.
        // Clocked only when counting is armed: `--trace` off is one
        // thread-local `bool` read, and a round already contains a whole
        // `sat-bv` check, so four clock reads per round cannot perturb it.
        let skeleton_started = crate::lazy_smt_counters::enabled().then(Instant::now);
        let skeleton_result = solver.solve_round(arena, &skeleton, &blocking, &fallback_config);
        if let Some(started) = skeleton_started {
            let outcome = match &skeleton_result {
                Ok(CheckResult::Sat(_)) => RoundOutcome::Sat,
                Ok(CheckResult::Unsat) => RoundOutcome::Unsat,
                // A backend error is counted with `unknown`: both end the loop,
                // and inventing a fourth token for a case the loop does not
                // distinguish would put a distinction in the line that the
                // producer does not make.
                Ok(CheckResult::Unknown(_)) | Err(_) => RoundOutcome::Unknown,
            };
            crate::lazy_smt_counters::record_skeleton(LazySmtLoop::Lra, started.elapsed(), outcome);
        }
        let propositional = match skeleton_result? {
            CheckResult::Sat(model) => model,
            CheckResult::Unsat => return Ok(CheckResult::Unsat),
            CheckResult::Unknown(reason) => return Ok(CheckResult::Unknown(reason)),
        };

        // 3. Read each atom's truth and form the theory conjunction.
        let mut theory_lits = Vec::with_capacity(ctx.atoms.len());
        let mut assignment: Vec<(SymbolId, bool)> = Vec::with_capacity(ctx.atoms.len());
        for atom in &ctx.atoms {
            let truth = propositional
                .get(atom.prop)
                .and_then(|v| v.as_bool())
                .unwrap_or(false);
            assignment.push((atom.prop, truth));
            theory_lits.push(if truth {
                atom.term
            } else {
                arena.not(atom.term)?
            });
        }

        record_cube_churn(&assignment, &mut previous_cube);

        let (verdict, carried) = decide_cube(arena, &theory_lits, deadline)?;
        match verdict {
            CheckResult::Sat(theory_model) => {
                return finish_sat(arena, assertions, &ctx, &propositional, &theory_model);
            }
            CheckResult::Unsat => {
                blocking.push(learn_blocking_clause(
                    arena,
                    &theory_lits,
                    &assignment,
                    carried.as_ref(),
                    deadline,
                )?);
            }
            CheckResult::Unknown(reason) => return Ok(CheckResult::Unknown(reason)),
        }
    }

    Ok(CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::Incomplete,
        detail: format!("lazy SMT exceeded {MAX_ROUNDS} refinement rounds"),
    }))
}

/// Lazy-SMT loop for **Boolean-structured nonlinear real arithmetic**.
///
/// Same skeleton as [`check_with_lra_dpll_within`] — abstract atoms to
/// propositions, decide the Boolean skeleton (plus learned blocking clauses) with
/// the full bit-blasting composition, read the chosen atoms into a conjunctive
/// *cube* — but each cube is decided by the **exact NRA conjunction decider**
/// ([`crate::nra_real_root::decide_real_poly_constraint`], the sign-cell / CAD
/// engine) instead of the linear theory check. This unlocks the
/// decision-complete CAD on `QF_NRA` queries whose Boolean structure
/// (`or`/`distinct`/`ite` over nonlinear atoms) makes the flat-conjunction CAD
/// entry decline outright — the measured dominant gap (see
/// `docs/plan/track-2-theories/P2.5-nra/08-evaluation-and-soundness.md`).
///
/// **Soundness.** Every cube `sat` is replay-checked by [`finish_sat`] against
/// *all* original assertions (a witness that fails to evaluate declines to
/// `unknown`; one that definitely violates an assertion is a loud alarm); every
/// cube `unsat` blocks that atom assignment (the whole cube — a sound, coarser
/// core than the LRA Farkas one); a cube the CAD cannot decide yields a
/// first-class `unknown`. Confirmed `DISAGREE=0` over the 2000-instance
/// `nra_differential_fuzz` vs Z3. It never calls back into `check_with_nra`, so
/// there is no recursion.
///
/// # Errors
///
/// Propagates backend/abstraction errors; a `sat` model that definitely violates
/// an assertion is a [`SolverError::Backend`] soundness alarm (via [`finish_sat`]).
pub fn check_with_nra_dpll_within(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> Result<CheckResult, SolverError> {
    let mut ctx = Abstractor::default();
    let mut skeleton = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        skeleton.push(ctx.abstract_term(arena, assertion)?);
    }
    let mut solver = SkeletonSolver::new(skeleton_solve_policy(), arena, &skeleton, config);
    let mut blocking: Vec<TermId> = Vec::new();
    crate::lazy_smt_counters::record_entry(LazySmtLoop::Nra, ctx.atoms.len() as u64);

    for _ in 0..MAX_ROUNDS {
        if past_deadline(deadline) {
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::ResourceLimit,
                detail: "nra lazy SMT: wall-clock timeout reached".to_owned(),
            }));
        }
        // Bound this round's propositional solve by the budget REMAINING to the
        // shared deadline, so a round entered near the deadline cannot run a further
        // full `config.timeout` past it (the loop-head check then bails promptly).
        let round_config = {
            let mut c = config.clone();
            if let Some(d) = deadline {
                c.timeout = Some(d.saturating_duration_since(Instant::now()));
            }
            c
        };
        let skeleton_started = crate::lazy_smt_counters::enabled().then(Instant::now);
        let skeleton_result = solver.solve_round(arena, &skeleton, &blocking, &round_config);
        if let Some(started) = skeleton_started {
            let outcome = match &skeleton_result {
                Ok(CheckResult::Sat(_)) => RoundOutcome::Sat,
                Ok(CheckResult::Unsat) => RoundOutcome::Unsat,
                Ok(CheckResult::Unknown(_)) | Err(_) => RoundOutcome::Unknown,
            };
            crate::lazy_smt_counters::record_skeleton(LazySmtLoop::Nra, started.elapsed(), outcome);
        }
        let propositional = match skeleton_result? {
            CheckResult::Sat(model) => model,
            CheckResult::Unsat => return Ok(CheckResult::Unsat),
            CheckResult::Unknown(reason) => return Ok(CheckResult::Unknown(reason)),
        };
        let mut theory_lits = Vec::with_capacity(ctx.atoms.len());
        let mut assignment: Vec<(SymbolId, bool)> = Vec::with_capacity(ctx.atoms.len());
        for atom in &ctx.atoms {
            let truth = propositional
                .get(atom.prop)
                .and_then(|v| v.as_bool())
                .unwrap_or(false);
            assignment.push((atom.prop, truth));
            theory_lits.push(if truth {
                atom.term
            } else {
                arena.not(atom.term)?
            });
        }
        let theory_started = crate::lazy_smt_counters::enabled().then(Instant::now);
        let theory_result =
            crate::nra_real_root::decide_real_poly_constraint(arena, &theory_lits, deadline);
        if let Some(started) = theory_started {
            let outcome = match &theory_result {
                Ok(Some(CheckResult::Sat(_))) => RoundOutcome::Sat,
                Ok(Some(CheckResult::Unsat)) => RoundOutcome::Unsat,
                // `None` is "the CAD declined this cube", which ends the loop
                // exactly as an `unknown` does.
                Ok(Some(CheckResult::Unknown(_)) | None) | Err(_) => RoundOutcome::Unknown,
            };
            crate::lazy_smt_counters::record_theory(started.elapsed(), outcome);
        }
        match theory_result? {
            Some(CheckResult::Sat(theory_model)) => {
                return finish_sat(arena, assertions, &ctx, &propositional, &theory_model);
            }
            Some(CheckResult::Unsat) => {
                // The nonlinear loop blocks the whole cube rather than a Farkas
                // core, so there is no second solve here — but it is timed the
                // same way, because "this stage is free on this loop" is a
                // measurement worth being able to read rather than assume.
                let core_started = crate::lazy_smt_counters::enabled().then(Instant::now);
                let clause = block_clause(arena, &assignment)?;
                crate::lazy_smt_counters::record_blocking(
                    assignment.len() as u64,
                    core_started.map_or(Duration::ZERO, |s| s.elapsed()),
                );
                blocking.push(clause);
            }
            Some(CheckResult::Unknown(reason)) => return Ok(CheckResult::Unknown(reason)),
            None => {
                return Ok(CheckResult::Unknown(UnknownReason {
                    kind: UnknownKind::Incomplete,
                    detail: "nra lazy SMT: theory cube not decided".to_owned(),
                }));
            }
        }
    }
    Ok(CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::Incomplete,
        detail: format!("nra lazy SMT exceeded {MAX_ROUNDS} refinement rounds"),
    }))
}

/// Hard cap on the number of Boolean symbols (atom propositions + original
/// Boolean variables) a refutation may have for its propositional half to be
/// verified by exhaustive enumeration. Above this the certificate is declined
/// (`unknown`), never produced unverified.
const MAX_CERTIFIABLE_BOOLS: usize = 22;

/// A checkable refutation of a **pure real** (Boolean structure over real order
/// atoms, no bit-vector/integer/array/function content) `QF_LRA` query.
///
/// It records the Boolean skeleton (one term per assertion, real atoms replaced
/// by fresh propositions) and the theory lemmas the lazy-SMT loop learned — each
/// lemma is the infeasible core of a theory conflict. [`Self::verify`] re-checks
/// it independently of the search:
///
/// 1. **Each lemma is a valid theory fact.** Its core literals are re-decided by
///    [`check_with_lra`] (itself Farkas-self-checked) and must be `unsat`, so the
///    lemma clause (the core's negation) holds in every real model.
/// 2. **The skeleton with all lemma clauses is propositionally unsatisfiable**,
///    confirmed by enumerating every truth assignment to the Boolean symbols.
///
/// Soundness: any real model of the original query induces a truth assignment
/// that satisfies the skeleton (by the abstraction) and every lemma clause (by
/// (1)); (2) says no such assignment exists, so the query is `unsat`. The
/// abstraction (skeleton faithfully represents the originals over the atoms) is
/// the trusted reduction here, exactly as bit-blasting is trusted on the DRAT
/// route.
#[derive(Debug, Clone)]
pub struct LraDpllRefutation {
    /// The Boolean skeleton: one term per original assertion, over fresh atom
    /// propositions and any original Boolean variables.
    pub skeleton: Vec<TermId>,
    /// The learned theory lemmas; each is an infeasible core of real-atom
    /// literals.
    pub lemmas: Vec<Vec<LemmaLiteral>>,
}

/// One literal of a theory lemma: an abstracted atom proposition, the truth
/// value it took in the conflicting assignment, and the corresponding real
/// order literal (`atom` or its negation) used to re-check the lemma.
#[derive(Debug, Clone, Copy)]
pub struct LemmaLiteral {
    /// The fresh Boolean proposition standing for the atom.
    pub prop: SymbolId,
    /// The truth value the proposition took in the (infeasible) assignment.
    pub truth: bool,
    /// The real order literal: the atom term when `truth`, else its negation.
    pub literal: TermId,
}

/// The outcome of [`certify_lra_dpll_unsat`].
#[derive(Debug, Clone)]
pub enum LraDpllOutcome {
    /// Satisfiable, with a replayed model.
    Sat(Model),
    /// Unsatisfiable, with a self-checked refutation.
    Unsat(LraDpllRefutation),
    /// Undecided / not certifiable, with a reason.
    Unknown(UnknownReason),
}

/// Decides a **pure real** Boolean-structured `QF_LRA` query and, on `unsat`,
/// returns a self-checked [`LraDpllRefutation`] — the lazy-SMT generalization of
/// the conjunctive Farkas certificate to arbitrary Boolean structure.
///
/// On `unsat` the refutation is verified (theory lemmas + propositional
/// enumeration) before it is returned; a failed self-check is a
/// [`SolverError::Backend`] soundness alarm. If the refutation has too many
/// Boolean symbols to enumerate, the result is a classified `unknown` rather
/// than an unverified certificate.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] if the query carries non-real,
/// non-Boolean content (bit-vectors, integers, arrays, functions, quantifiers),
/// or [`SolverError`] from the underlying solvers; a failed self-check is a
/// [`SolverError::Backend`].
pub fn certify_lra_dpll_unsat(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<LraDpllOutcome, SolverError> {
    for &assertion in assertions {
        if !is_pure_bool_real(arena, assertion) {
            return Err(SolverError::Unsupported(
                "lra-dpll certificate: query has non-real/Boolean theory content".to_owned(),
            ));
        }
    }

    let mut ctx = Abstractor::default();
    let mut skeleton = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        skeleton.push(ctx.abstract_term(arena, assertion)?);
    }

    let mut backend = SatBvBackend::new();
    let mut blocking: Vec<TermId> = Vec::new();
    let mut lemmas: Vec<Vec<LemmaLiteral>> = Vec::new();

    for _ in 0..MAX_ROUNDS {
        let mut sat_assertions = skeleton.clone();
        sat_assertions.extend(blocking.iter().copied());
        let propositional = match check_with_all_theories(
            &mut backend,
            arena,
            &sat_assertions,
            DEFAULT_INT_WIDTH,
            config,
        )? {
            CheckResult::Sat(model) => model,
            CheckResult::Unsat => {
                // Propositional refutation reached: the skeleton plus learned
                // lemmas is unsatisfiable. Package and self-check the certificate.
                let refutation = LraDpllRefutation {
                    skeleton: skeleton.clone(),
                    lemmas,
                };
                return finish_certified_unsat(arena, refutation);
            }
            CheckResult::Unknown(reason) => return Ok(LraDpllOutcome::Unknown(reason)),
        };

        let mut theory_lits = Vec::with_capacity(ctx.atoms.len());
        let mut assignment: Vec<(SymbolId, bool)> = Vec::with_capacity(ctx.atoms.len());
        for atom in &ctx.atoms {
            let truth = propositional
                .get(atom.prop)
                .and_then(|v| v.as_bool())
                .unwrap_or(false);
            assignment.push((atom.prop, truth));
            theory_lits.push(if truth {
                atom.term
            } else {
                arena.not(atom.term)?
            });
        }

        // Same reuse as the refinement loop above: the decision that refutes
        // the cube is the only place the Farkas multipliers exist without a
        // second `QF_LRA` solve.
        let (verdict, evidence) = check_with_lra_within_certified(arena, &theory_lits, None)?;
        let carried = evidence.map(|certificate| CarriedCertificate {
            lits: theory_lits.clone(),
            certificate,
        });
        match verdict {
            CheckResult::Sat(theory_model) => {
                return match finish_sat(arena, assertions, &ctx, &propositional, &theory_model)? {
                    CheckResult::Sat(model) => Ok(LraDpllOutcome::Sat(model)),
                    _ => unreachable!("finish_sat returns Sat or Err"),
                };
            }
            CheckResult::Unsat => {
                // Record the infeasible core as a lemma (the same minimized core
                // used for the blocking clause), then block it.
                let core = conflict_core(arena, &theory_lits, &assignment, carried.as_ref(), None)?;
                let mut lemma = Vec::with_capacity(core.len());
                for &(prop, truth) in &core {
                    let atom_term = ctx
                        .atoms
                        .iter()
                        .find(|a| a.prop == prop)
                        .map(|a| a.term)
                        .ok_or_else(|| {
                            SolverError::Backend(
                                "lra-dpll lemma references an unknown atom proposition".to_owned(),
                            )
                        })?;
                    let literal = if truth {
                        atom_term
                    } else {
                        arena.not(atom_term)?
                    };
                    lemma.push(LemmaLiteral {
                        prop,
                        truth,
                        literal,
                    });
                }
                lemmas.push(lemma);
                blocking.push(block_clause(arena, &core)?);
            }
            CheckResult::Unknown(reason) => return Ok(LraDpllOutcome::Unknown(reason)),
        }
    }

    Ok(LraDpllOutcome::Unknown(UnknownReason {
        kind: UnknownKind::Incomplete,
        detail: format!("lazy SMT exceeded {MAX_ROUNDS} refinement rounds"),
    }))
}

/// Size-gates and self-verifies a freshly built refutation.
fn finish_certified_unsat(
    arena: &TermArena,
    refutation: LraDpllRefutation,
) -> Result<LraDpllOutcome, SolverError> {
    let bools = refutation.bool_symbols(arena);
    if bools.len() > MAX_CERTIFIABLE_BOOLS {
        return Ok(LraDpllOutcome::Unknown(UnknownReason {
            kind: UnknownKind::Incomplete,
            detail: format!(
                "lra-dpll refutation has {} Boolean symbols, over the enumeration cap {MAX_CERTIFIABLE_BOOLS}",
                bools.len()
            ),
        }));
    }
    if !refutation.verify(arena)? {
        return Err(SolverError::Backend(
            "lra-dpll refutation failed its own self-check (lazy-SMT bug)".to_owned(),
        ));
    }
    Ok(LraDpllOutcome::Unsat(refutation))
}

impl LraDpllRefutation {
    /// The Boolean symbols (atom propositions and original Boolean variables)
    /// the refutation ranges over, in deterministic order.
    fn bool_symbols(&self, arena: &TermArena) -> Vec<SymbolId> {
        let mut set = std::collections::BTreeSet::new();
        let mut stack: Vec<TermId> = self.skeleton.clone();
        let mut seen = std::collections::HashSet::new();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match arena.node(t) {
                TermNode::Symbol(symbol) if arena.sort_of(t) == Sort::Bool => {
                    set.insert(*symbol);
                }
                TermNode::App { args, .. } => stack.extend(args.iter().copied()),
                _ => {}
            }
        }
        for lemma in &self.lemmas {
            for literal in lemma {
                set.insert(literal.prop);
            }
        }
        set.into_iter().collect()
    }

    /// Independently re-checks the refutation; see the type docs for the
    /// soundness argument. Returns `Ok(true)` iff it holds up.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::Unsupported`] if there are too many Boolean
    /// symbols to enumerate, or [`SolverError`] from the theory re-check or an
    /// evaluation error.
    pub fn verify(&self, arena: &TermArena) -> Result<bool, SolverError> {
        // (1) Every lemma's core must be a genuine theory contradiction.
        for lemma in &self.lemmas {
            let lits: Vec<TermId> = lemma.iter().map(|l| l.literal).collect();
            if lits.is_empty() || !matches!(check_with_lra(arena, &lits)?, CheckResult::Unsat) {
                return Ok(false);
            }
        }

        // (2) skeleton AND every lemma clause (the core's negation) must be
        //     propositionally unsatisfiable — enumerate all Boolean assignments.
        let bools = self.bool_symbols(arena);
        if bools.len() > MAX_CERTIFIABLE_BOOLS {
            return Err(SolverError::Unsupported(format!(
                "lra-dpll refutation has {} Boolean symbols, too many to verify by enumeration",
                bools.len()
            )));
        }
        let index_of: std::collections::HashMap<SymbolId, usize> =
            bools.iter().enumerate().map(|(i, &s)| (s, i)).collect();
        let n = bools.len();
        for mask in 0u64..(1u64 << n) {
            let mut assignment = Assignment::new();
            for (i, &symbol) in bools.iter().enumerate() {
                assignment.set(symbol, Value::Bool((mask >> i) & 1 == 1));
            }
            // Does this assignment satisfy the whole skeleton?
            let mut skeleton_holds = true;
            for &term in &self.skeleton {
                match eval(arena, term, &assignment) {
                    Ok(Value::Bool(true)) => {}
                    Ok(_) => {
                        skeleton_holds = false;
                        break;
                    }
                    Err(error) => {
                        return Err(SolverError::Backend(format!(
                            "lra-dpll verify: skeleton evaluation error: {error}"
                        )));
                    }
                }
            }
            if !skeleton_holds {
                continue;
            }
            // Does it also satisfy every lemma clause? A clause (the core's
            // negation) is false exactly when the core is fully satisfied (every
            // literal's proposition equals its recorded truth).
            let all_clauses_hold = self.lemmas.iter().all(|lemma| {
                let core_fully_satisfied = lemma
                    .iter()
                    .all(|l| (mask >> index_of[&l.prop]) & 1 == u64::from(l.truth));
                !core_fully_satisfied
            });
            if all_clauses_hold {
                // A model of skeleton AND all clauses exists: not a refutation.
                return Ok(false);
            }
        }
        Ok(true)
    }
}

/// Whether `term` is built only from Boolean and real sorts (no bit-vector,
/// integer, array, function, or quantifier content) — the fragment the
/// [`LraDpllRefutation`] enumeration certificate covers.
fn is_pure_bool_real(arena: &TermArena, term: TermId) -> bool {
    let mut seen = std::collections::HashSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match arena.sort_of(t) {
            Sort::Bool | Sort::Real => {}
            _ => return false,
        }
        if let TermNode::App { op, args } = arena.node(t) {
            if matches!(op, Op::Apply(_) | Op::Forall(_) | Op::Exists(_)) {
                return false;
            }
            stack.extend(args.iter().copied());
        }
    }
    true
}

/// Builds the final `sat` model (real values + original Boolean values) and
/// replays it against the original assertions.
fn finish_sat(
    arena: &TermArena,
    assertions: &[TermId],
    ctx: &Abstractor,
    propositional: &Model,
    theory_model: &Model,
) -> Result<CheckResult, SolverError> {
    let mut assignment = Assignment::new();
    let mut model = Model::new();
    // Real variable values from the theory solver.
    for (symbol, value) in theory_model.iter() {
        assignment.set(symbol, value.clone());
        model.set(symbol, value);
    }
    // Everything else from the bit-blasting model (Booleans, bit-vectors,
    // integers, arrays, functions). Skip the fresh atom propositions, and skip
    // real values — the backend default-completes real symbols to `Real(0)`,
    // which must not overwrite the theory solver's real assignment.
    for (symbol, value) in propositional.iter() {
        if ctx.is_atom_prop(symbol) || matches!(value, Value::Real(_)) {
            continue;
        }
        assignment.set(symbol, value.clone());
        model.set(symbol, value);
    }
    for (func, interp) in propositional.functions() {
        assignment.set_function(func, interp.clone());
        model.set_function(func, interp.clone());
    }

    for &assertion in assertions {
        match eval(arena, assertion, &assignment) {
            Ok(Value::Bool(true)) => {}
            Ok(_) => {
                return Err(SolverError::Backend(format!(
                    "lazy-SMT sat model replay failed: assertion #{} not satisfied",
                    assertion.index()
                )));
            }
            Err(_error) => {
                // The candidate could not be *evaluated* (e.g. an exact-rational
                // comparison overflowed `i128`). This is not a wrong model — we
                // simply cannot certify `sat` — so decline to a graceful `unknown`
                // rather than raise a backend error (matching the LRA-replay fix in
                // `lra.rs`; `unknown` is a first-class result, never an error).
                return Ok(CheckResult::Unknown(UnknownReason {
                    kind: UnknownKind::Incomplete,
                    detail: format!(
                        "lazy-SMT: sat model replay could not be verified (assertion #{})",
                        assertion.index()
                    ),
                }));
            }
        }
    }
    Ok(CheckResult::Sat(model))
}

/// Decides one round's cube with the exact linear theory, times the stage, and
/// **keeps** the Farkas certificate bound to the conjunction it refutes.
///
/// Keeping it is the whole point: `CheckResult` cannot carry the evidence, so
/// this loop used to drop the certificate here and have the core extraction
/// decide the identical literal set a second time. That second decision was
/// 48.6% of the wall clock across the 22 `QF_LRA` files bound by this route
/// (`bench-results/watchdog-blind-files-20260908/qf_lra_blind22/`).
///
/// # Errors
///
/// Propagates the theory decision's errors.
/// Counts how far the round's cube moved from the previous round's, and keeps
/// the cube for the next comparison.
///
/// The question the Farkas fix left open. With the second LP gone the loop runs
/// 1.63x the rounds and still loses, so either each round hands the theory a
/// genuinely different problem or it hands it nearly the same one and pays a
/// cold decision for the difference. Measured 2026-09-08 over the 22 `QF_LRA`
/// files bound by this loop, the answer is the second: **1.1 to 4.2 flipped
/// literals out of 265 to 1,736 atoms**, with `cube_identical` zero everywhere.
///
/// The first round of an entry has no predecessor and is not recorded, so the
/// churn denominator is `rounds - entries` and never `rounds`. Costs one
/// thread-local `bool` read when counting is off.
fn record_cube_churn(assignment: &[(SymbolId, bool)], previous: &mut Option<Vec<bool>>) {
    if !crate::lazy_smt_counters::enabled() {
        return;
    }
    let cube: Vec<bool> = assignment.iter().map(|&(_, truth)| truth).collect();
    if let Some(previous) = previous.as_ref()
        && previous.len() == cube.len()
    {
        let flips = previous
            .iter()
            .zip(&cube)
            .filter(|(a, b)| a != b)
            .count()
            .try_into()
            .unwrap_or(u64::MAX);
        crate::lazy_smt_counters::record_cube_churn(flips);
    }
    *previous = Some(cube);
}

fn decide_cube(
    arena: &TermArena,
    theory_lits: &[TermId],
    deadline: Option<Instant>,
) -> Result<(CheckResult, Option<CarriedCertificate>), SolverError> {
    let started = crate::lazy_smt_counters::enabled().then(Instant::now);
    let decision = check_with_lra_within_certified(arena, theory_lits, deadline);
    if let Some(started) = started {
        let outcome = match &decision {
            Ok((CheckResult::Sat(_), _)) => RoundOutcome::Sat,
            Ok((CheckResult::Unsat, _)) => RoundOutcome::Unsat,
            Ok((CheckResult::Unknown(_), _)) | Err(_) => RoundOutcome::Unknown,
        };
        crate::lazy_smt_counters::record_theory(started.elapsed(), outcome);
    }
    let (verdict, evidence) = decision?;
    Ok((
        verdict,
        evidence.map(|certificate| CarriedCertificate {
            lits: theory_lits.to_vec(),
            certificate,
        }),
    ))
}

/// Turns one theory conflict into the blocking clause the next round solves
/// against, and times the whole stage.
///
/// The Farkas certificate names the infeasible core — the atoms with a nonzero
/// multiplier — so only those are blocked: a sound, strictly stronger clause
/// that rules out every assignment sharing the core, not just this one.
/// `theory_lits`, `assignment` and the certificate atoms are all in `ctx.atoms`
/// order, so multiplier index `i` is `assignment[i]`.
///
/// Still timed as its own stage even though it no longer re-solves the refuted
/// conjunction — that SECOND LP per round is what the 2026-09-08 measurement
/// found holding about half of this route's wall clock. The stage keeps its own
/// clock so the reading stays comparable across the fix, and so the
/// re-derivation paths that survive are still attributed.
///
/// # Errors
///
/// Propagates the core extraction's and the clause construction's errors.
fn learn_blocking_clause(
    arena: &mut TermArena,
    theory_lits: &[TermId],
    assignment: &[(SymbolId, bool)],
    carried: Option<&CarriedCertificate>,
    deadline: Option<Instant>,
) -> Result<TermId, SolverError> {
    let started = crate::lazy_smt_counters::enabled().then(Instant::now);
    let core = conflict_core(arena, theory_lits, assignment, carried, deadline)?;
    let clause = block_clause(arena, &core)?;
    crate::lazy_smt_counters::record_blocking(
        core.len() as u64,
        started.map_or(Duration::ZERO, |s| s.elapsed()),
    );
    Ok(clause)
}

/// Builds the blocking clause that rules out the current atom assignment: the
/// disjunction of each proposition's complement.
fn block_clause(
    arena: &mut TermArena,
    assignment: &[(SymbolId, bool)],
) -> Result<TermId, SolverError> {
    let mut clause: Option<TermId> = None;
    for &(prop, truth) in assignment {
        let var = arena.var(prop);
        let literal = if truth { arena.not(var)? } else { var };
        clause = Some(match clause {
            Some(acc) => arena.or(acc, literal)?,
            None => literal,
        });
    }
    // A non-empty assignment always yields a clause; an empty one (no atoms)
    // cannot reach here because a theory conflict implies at least one atom.
    clause.ok_or_else(|| SolverError::Backend("empty theory conflict".to_owned()))
}

/// A Farkas certificate together with **the literal set it refutes**.
///
/// The two halves travel as one value because the certificate alone cannot say
/// what it is a refutation *of*: [`FarkasCertificate::verify`] proves the
/// multipliers collapse its own atoms to a contradiction, and that stays true
/// after the surrounding cube has changed. Applying those multipliers to a
/// different assignment would name a "core" that is not infeasible, and the
/// blocking clause built from it would rule out satisfiable assignments — a
/// wrong `unsat`, not a slow one. So reuse is gated on
/// [`CarriedCertificate::binds_to`], never on the certificate being present.
struct CarriedCertificate {
    /// The conjunction handed to the theory decision that produced
    /// [`Self::certificate`], in that order. `TermId`s are interned in one
    /// arena, so slice equality is term equality.
    lits: Vec<TermId>,
    /// The refutation that decision self-checked before returning it.
    certificate: FarkasCertificate,
}

impl CarriedCertificate {
    /// Whether this certificate is a refutation of `theory_lits` — i.e. whether
    /// it came from deciding exactly this conjunction, in this order.
    ///
    /// Order matters as well as membership: the multipliers are positional, and
    /// `conflict_core` reads multiplier `i` as assignment entry `i`.
    fn binds_to(&self, theory_lits: &[TermId]) -> bool {
        self.lits == theory_lits
    }
}

/// Returns the sub-assignment forming the infeasible core of a theory conflict.
///
/// The Farkas certificate's nonzero-multiplier atoms are exactly the literals
/// that participate in the refutation, so blocking only those is sound (that
/// subset is genuinely infeasible) and strictly stronger than blocking the whole
/// assignment. Falls back to the full assignment when no certificate is
/// available or its shape does not line up one-to-one with the literals — still
/// sound, since a larger blocking clause only rules out fewer assignments.
///
/// # The certificate is the round's own, or it is rebuilt
///
/// `carried` is the certificate the theory decision that refuted this very cube
/// already produced. Before this parameter existed, that certificate was
/// dropped on the floor by `check_with_lra_within`'s `CheckResult` and this
/// function re-decided the identical literal set to get it back — 48.6% of the
/// wall clock across the 22 `QF_LRA` files bound by this route, measured
/// 2026-09-08. Reuse is admitted only when the certificate **binds to**
/// `theory_lits` and re-verifies here, on the path that consumes it; anything
/// else re-derives, and the reason is counted.
///
/// The re-derivation now takes `deadline`. The unbounded form is a whole
/// `QF_LRA` decision with no interruption point, so a loop that checks its
/// deadline once per round could still spend unbounded time inside one round.
fn conflict_core(
    arena: &TermArena,
    theory_lits: &[TermId],
    assignment: &[(SymbolId, bool)],
    carried: Option<&CarriedCertificate>,
    deadline: Option<Instant>,
) -> Result<Vec<(SymbolId, bool)>, SolverError> {
    // The reused certificate is re-verified HERE, not merely where it was
    // built: a check that only ever runs on the producing path cannot fail on
    // the consuming one, and the consuming one is what turns multipliers into a
    // blocking clause.
    let certificate = match carried {
        Some(carried) if !carried.binds_to(theory_lits) => {
            crate::lazy_smt_counters::record_core_source(CoreSource::RederivedStale);
            lra_farkas_certificate_within(arena, theory_lits, deadline)?
        }
        Some(carried) if !carried.certificate.verify() => {
            crate::lazy_smt_counters::record_core_source(CoreSource::RederivedUnverified);
            lra_farkas_certificate_within(arena, theory_lits, deadline)?
        }
        Some(carried) => {
            crate::lazy_smt_counters::record_core_source(CoreSource::Reused);
            Some(carried.certificate.clone())
        }
        None => {
            crate::lazy_smt_counters::record_core_source(CoreSource::RederivedAbsent);
            lra_farkas_certificate_within(arena, theory_lits, deadline)?
        }
    };

    if let Some(certificate) = certificate
        && certificate.multipliers.len() == assignment.len()
    {
        let core: Vec<(SymbolId, bool)> = assignment
            .iter()
            .zip(&certificate.multipliers)
            .filter(|(_, multiplier)| !multiplier.is_zero())
            .map(|(entry, _)| *entry)
            .collect();
        if !core.is_empty() {
            return Ok(core);
        }
    }
    crate::lazy_smt_counters::record_full_assignment_core();
    Ok(assignment.to_vec())
}

/// Whether `term` contains any real-sorted subterm.
fn contains_real(arena: &TermArena, term: TermId) -> bool {
    let mut seen = std::collections::HashSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if arena.sort_of(t) == Sort::Real {
            return true;
        }
        if let TermNode::App { args, .. } = arena.node(t) {
            stack.extend(args.iter().copied());
        }
    }
    false
}

/// One abstracted real atom: its fresh Boolean proposition and the original
/// comparison term.
struct AtomBinding {
    prop: SymbolId,
    term: TermId,
}

#[derive(Default)]
struct Abstractor {
    /// Maps an original atom term to its fresh proposition.
    atom_of: HashMap<TermId, SymbolId>,
    /// Maps a fresh proposition back, to filter it from the final model.
    props: std::collections::HashSet<SymbolId>,
    atoms: Vec<AtomBinding>,
    fresh_counter: usize,
}

impl Abstractor {
    fn is_atom_prop(&self, symbol: SymbolId) -> bool {
        self.props.contains(&symbol)
    }

    /// Rewrites an assertion into a skeleton: real atoms become fresh Boolean
    /// propositions, while every subterm that contains no real (bit-vectors,
    /// arrays, functions, integers, and the Boolean structure over them) is left
    /// intact for the bit-blasting backend to decide natively.
    fn abstract_term(
        &mut self,
        arena: &mut TermArena,
        term: TermId,
    ) -> Result<TermId, SolverError> {
        // No real subterm: leave it for the bit-blasting composition.
        if !contains_real(arena, term) {
            return Ok(term);
        }
        let node = arena.node(term).clone();
        match node {
            TermNode::BoolConst(_) | TermNode::Symbol(_) => Ok(term),
            TermNode::App { op, args } => match op {
                Op::BoolNot => {
                    let a = self.abstract_term(arena, args[0])?;
                    Ok(arena.not(a)?)
                }
                Op::BoolAnd => self.rebuild_binary(arena, &args, TermArena::and),
                Op::BoolOr => self.rebuild_binary(arena, &args, TermArena::or),
                Op::BoolXor => self.rebuild_binary(arena, &args, TermArena::xor),
                Op::BoolImplies => self.rebuild_binary(arena, &args, TermArena::implies),
                // Boolean `=` (iff) and `ite` keep their structure when their
                // operands are Boolean; otherwise they are not a skeleton.
                Op::Eq if arena.sort_of(args[0]) == Sort::Bool => {
                    self.rebuild_binary(arena, &args, TermArena::eq)
                }
                Op::Ite if arena.sort_of(term) == Sort::Bool => {
                    let c = self.abstract_term(arena, args[0])?;
                    let t = self.abstract_term(arena, args[1])?;
                    let e = self.abstract_term(arena, args[2])?;
                    Ok(arena.ite(c, t, e)?)
                }
                Op::RealLt | Op::RealLe | Op::RealGt | Op::RealGe => {
                    let prop = self.atom(arena, term);
                    Ok(arena.var(prop))
                }
                Op::Eq if arena.sort_of(args[0]) == Sort::Real => {
                    // Real equality `a = b` abstracts to `(a <= b) and (a >= b)`,
                    // so equality *and* disequality (its negation, `a < b or
                    // a > b`) flow through the order-atom machinery and the SAT
                    // case split — no special disequality reasoning in the theory
                    // solver.
                    let le = arena.real_le(args[0], args[1])?;
                    let ge = arena.real_ge(args[0], args[1])?;
                    let le_prop = self.abstract_term(arena, le)?;
                    let ge_prop = self.abstract_term(arena, ge)?;
                    Ok(arena.and(le_prop, ge_prop)?)
                }
                _ => Err(SolverError::Unsupported(
                    "lazy SMT: assertion is not Boolean structure over real order atoms".to_owned(),
                )),
            },
            TermNode::BvConst { .. }
            | TermNode::WideBvConst(_)
            | TermNode::IntConst(_)
            | TermNode::WideIntConst(_)
            | TermNode::RealConst(_) => Err(SolverError::Unsupported(
                "lazy SMT: non-Boolean constant at a Boolean position".to_owned(),
            )),
        }
    }

    fn rebuild_binary(
        &mut self,
        arena: &mut TermArena,
        args: &[TermId],
        build: fn(&mut TermArena, TermId, TermId) -> Result<TermId, axeyum_ir::IrError>,
    ) -> Result<TermId, SolverError> {
        let a = self.abstract_term(arena, args[0])?;
        let b = self.abstract_term(arena, args[1])?;
        Ok(build(arena, a, b)?)
    }

    /// Returns the fresh proposition for an atom term, creating it once.
    fn atom(&mut self, arena: &mut TermArena, term: TermId) -> SymbolId {
        if let Some(&prop) = self.atom_of.get(&term) {
            return prop;
        }
        let name = format!("!lra_atom_{}", self.fresh_counter);
        self.fresh_counter += 1;
        let prop = arena
            .declare_internal(&name, Sort::Bool)
            .expect("fresh Boolean proposition declares");
        self.atom_of.insert(term, prop);
        self.props.insert(prop);
        self.atoms.push(AtomBinding { prop, term });
        prop
    }
}

#[cfg(test)]
mod tests {
    use super::{
        CarriedCertificate, SkeletonSolvePolicy, SkeletonSolver, conflict_core,
        skeleton_is_pure_boolean,
    };
    use axeyum_ir::{Rational, Sort, SymbolId, TermArena, TermId};

    use crate::lazy_smt_counters::{LazySmtCountersGuard, last_lazy_smt_counters};
    use crate::lra::{check_with_lra, check_with_lra_within_certified};
    use crate::{CheckResult, SolverError};

    /// A carried certificate for `lits`, obtained the way the refinement loop
    /// obtains it: from the theory decision that refutes them.
    fn carry(arena: &TermArena, lits: &[TermId]) -> CarriedCertificate {
        let (verdict, evidence) =
            check_with_lra_within_certified(arena, lits, None).expect("decides");
        assert!(
            matches!(verdict, CheckResult::Unsat),
            "fixture must be unsat"
        );
        CarriedCertificate {
            lits: lits.to_vec(),
            certificate: evidence.expect("a linear refutation carries a certificate"),
        }
    }

    /// Whether the sub-conjunction named by `core` is genuinely unsatisfiable —
    /// the property a blocking clause built from that core depends on.
    fn core_is_infeasible(
        arena: &TermArena,
        lits: &[TermId],
        assignment: &[(SymbolId, bool)],
        core: &[(SymbolId, bool)],
    ) -> Result<bool, SolverError> {
        let selected: Vec<TermId> = assignment
            .iter()
            .zip(lits)
            .filter(|(entry, _)| core.contains(entry))
            .map(|(_, &lit)| lit)
            .collect();
        Ok(matches!(
            check_with_lra(arena, &selected)?,
            CheckResult::Unsat
        ))
    }

    /// `n` fresh `true` propositions, one per literal of a cube.
    fn props(arena: &mut TermArena, prefix: &str, n: usize) -> Vec<(SymbolId, bool)> {
        (0..n)
            .map(|i| {
                (
                    arena.declare(&format!("{prefix}{i}"), Sort::Bool).unwrap(),
                    true,
                )
            })
            .collect()
    }

    /// **The staleness guard.** A Farkas certificate keeps verifying after the
    /// cube it refutes has changed — `verify()` is a statement about the
    /// certificate's own atoms, not about the literals it is being applied to.
    /// So reuse must be gated on the certificate BINDING to the literal set, and
    /// this test is what says that gate is load-bearing.
    ///
    /// Both systems have three literals, so the length check
    /// `multipliers.len() == assignment.len()` cannot catch the substitution;
    /// the multiplier vectors differ only in WHICH entry is zero. Applying the
    /// donor's `(nonzero, nonzero, 0)` to the recipient names `{p0, p1}` —
    /// `y < 0` and `x > 0`, which are jointly SATISFIABLE. A blocking clause
    /// built from that would rule out satisfiable assignments: a wrong `unsat`.
    ///
    /// Mutation control: make reuse unconditional in `conflict_core` (drop the
    /// `binds_to` arm) and exactly this test dies.
    #[test]
    fn a_certificate_from_a_different_literal_set_is_rejected_and_rebuilt() {
        let mut arena = TermArena::new();
        let x = arena.real_var("x").unwrap();
        let y = arena.real_var("y").unwrap();
        let zero = arena.real_const(Rational::integer(0));
        let seven = arena.real_const(Rational::integer(7));

        let x_neg = arena.real_lt(x, zero).unwrap();
        let x_pos = arena.real_lt(zero, x).unwrap();
        let y_neg = arena.real_lt(y, zero).unwrap();
        let y_over_seven = arena.real_lt(seven, y).unwrap();

        // Donor cube: refuted by literals 0 and 1; literal 2 is a spectator, so
        // its multiplier is zero and the donor core is `{0, 1}`.
        let donor = vec![x_neg, x_pos, y_over_seven];
        // Recipient cube: refuted by literals 0 and 2. Same length, different
        // infeasible pair.
        let recipient = vec![y_neg, x_pos, y_over_seven];

        let assignment = props(&mut arena, "p", 3);

        let carried = carry(&arena, &donor);
        assert_eq!(
            carried.certificate.multipliers.len(),
            assignment.len(),
            "the fixture is only adversarial if the length check cannot reject it"
        );
        assert!(
            carried.certificate.multipliers[2].is_zero(),
            "the donor must leave a spectator, or its core is the whole cube and \
             the substitution is invisible"
        );
        assert!(
            carried.certificate.verify(),
            "the stale certificate still self-verifies: that is exactly why \
             `verify()` alone cannot gate reuse"
        );

        let core = conflict_core(&arena, &recipient, &assignment, Some(&carried), None)
            .expect("core extraction decides");

        // The property, stated over the recipient: whatever core comes back, the
        // literals it names must actually be jointly unsatisfiable.
        assert!(
            core_is_infeasible(&arena, &recipient, &assignment, &core).expect("re-decides"),
            "the returned core must refute the recipient cube; got {core:?}"
        );
        // And the identity, so a future change that returns the full assignment
        // (sound but coarse) is still visible as a change.
        assert_eq!(
            core,
            vec![assignment[0], assignment[2]],
            "the rebuilt core is the recipient's own infeasible pair"
        );
    }

    /// The reuse path is the one that runs on every real conflict, and it must
    /// produce the same core the re-derivation would — otherwise the fix trades
    /// a wrong answer for a fast one.
    #[test]
    fn a_bound_certificate_is_reused_and_gives_the_same_core_as_re_deriving() {
        let mut arena = TermArena::new();
        let x = arena.real_var("x").unwrap();
        let y = arena.real_var("y").unwrap();
        let zero = arena.real_const(Rational::integer(0));
        let seven = arena.real_const(Rational::integer(7));

        let lits = vec![
            arena.real_lt(y, zero).unwrap(),
            arena.real_lt(zero, x).unwrap(),
            arena.real_lt(seven, y).unwrap(),
        ];
        let assignment = props(&mut arena, "q", 3);
        let carried = carry(&arena, &lits);

        let guard = LazySmtCountersGuard::enable();
        let reused = conflict_core(&arena, &lits, &assignment, Some(&carried), None).unwrap();
        let counters = last_lazy_smt_counters().expect("armed");
        assert_eq!(counters.cores_reused, 1);
        assert_eq!(
            counters.cores_rederived(),
            0,
            "a certificate for this very cube must not be re-derived"
        );
        drop(guard);

        let guard = LazySmtCountersGuard::enable();
        let rederived = conflict_core(&arena, &lits, &assignment, None, None).unwrap();
        let counters = last_lazy_smt_counters().expect("armed");
        assert_eq!(counters.cores_reused, 0);
        assert_eq!(counters.cores_rederived_absent, 1);
        drop(guard);

        assert_eq!(
            reused, rederived,
            "reuse must not change which literals are blocked"
        );
        assert_eq!(reused, vec![assignment[0], assignment[2]]);
    }

    /// A certificate that does not line up one-to-one with the assignment blocks
    /// the whole cube, and that coarsening has its own counter rather than being
    /// invisible inside the reuse total.
    #[test]
    fn a_certificate_that_does_not_line_up_blocks_the_whole_cube() {
        let mut arena = TermArena::new();
        let x = arena.real_var("x").unwrap();
        let zero = arena.real_const(Rational::integer(0));
        let lits = vec![
            arena.real_lt(x, zero).unwrap(),
            arena.real_lt(zero, x).unwrap(),
        ];
        // One proposition too few: the multiplier vector cannot be read
        // positionally against this assignment.
        let assignment = props(&mut arena, "r", 1);

        let _guard = LazySmtCountersGuard::enable();
        let core = conflict_core(&arena, &lits, &assignment, None, None).unwrap();
        let counters = last_lazy_smt_counters().expect("armed");
        assert_eq!(counters.cores_rederived_absent, 1);
        assert_eq!(counters.cores_rederived_stale, 0);
        assert_eq!(counters.cores_reused, 0);
        assert_eq!(counters.cores_full_assignment, 1);
        assert_eq!(core, assignment);
    }
    // --- the skeleton-solve policy (2026-09-09) --------------------------------

    /// Three `Bool` propositions and a skeleton over them, the shape the lazy-SMT
    /// loops build: two clauses with room for blocking clauses to accumulate.
    fn bool_skeleton(arena: &mut TermArena) -> (Vec<TermId>, Vec<SymbolId>) {
        let p0 = arena.declare("p0", Sort::Bool).unwrap();
        let p1 = arena.declare("p1", Sort::Bool).unwrap();
        let p2 = arena.declare("p2", Sort::Bool).unwrap();
        let (a, b, c) = (arena.var(p0), arena.var(p1), arena.var(p2));
        let ab = arena.or(a, b).unwrap();
        let bc = arena.or(b, c).unwrap();
        (vec![ab, bc], vec![p0, p1, p2])
    }

    /// The applicability test admits a pure propositional skeleton.
    #[test]
    fn a_pure_boolean_skeleton_is_admitted_to_the_warm_arm() {
        let mut arena = TermArena::new();
        let (skeleton, _) = bool_skeleton(&mut arena);
        assert!(skeleton_is_pure_boolean(&arena, &skeleton));
    }

    /// ...and refuses one that still carries a real atom. A `Bool`-sorted atom
    /// at the root, so a root-only sort test would have admitted it.
    ///
    /// This term is refused by EITHER guard on its own (the whitelist rejects
    /// `Op::RealLt`; the per-node sort test rejects the real operand), so it is
    /// a coverage case, not a discriminating one — `a_bool_sorted_uninterpreted
    /// _predicate_is_refused_by_the_operator_whitelist` is what pins GUARD 2.
    #[test]
    fn a_skeleton_carrying_a_real_atom_is_refused_by_the_warm_arm() {
        let mut arena = TermArena::new();
        let x = arena.real_var("x").unwrap();
        let zero = arena.real_const(Rational::integer(0));
        let atom = arena.real_lt(x, zero).unwrap();
        assert_eq!(arena.sort_of(atom), Sort::Bool);
        assert!(!skeleton_is_pure_boolean(&arena, &[atom]));
    }

    /// GUARD 2's case and only GUARD 2's: an uninterpreted predicate over a
    /// `Bool` argument, `p(q)`. EVERY node of it is `Bool`-sorted — the
    /// application, the argument, the result — so the per-node sort test passes
    /// it unharmed and the operator whitelist is the only thing that refuses
    /// it. Removing the whitelist kills this test and nothing else.
    ///
    /// It exists because the obvious fixture does not discriminate: `x < 0` is
    /// refused by both guards, so deleting the whitelist left every test green.
    /// A guard needs a term the OTHER guard admits, or the mutation says
    /// nothing.
    #[test]
    fn a_bool_sorted_uninterpreted_predicate_is_refused_by_the_operator_whitelist() {
        let mut arena = TermArena::new();
        let q = arena.declare("q", Sort::Bool).unwrap();
        let arg = arena.var(q);
        let p = arena.declare_fun("p", &[Sort::Bool], Sort::Bool).unwrap();
        let app = arena.apply(p, &[arg]).unwrap();
        assert_eq!(arena.sort_of(app), Sort::Bool);
        assert_eq!(arena.sort_of(arg), Sort::Bool);
        assert!(!skeleton_is_pure_boolean(&arena, &[app]));
    }

    /// A `Bool`-sorted `Eq` between two REALS must still be refused. This is
    /// GUARD 1's case and only GUARD 1's: `Op::Eq` is ON the whitelist, so the
    /// per-node sort test is the only thing that refuses it. Removing that test
    /// kills this test and nothing else.
    ///
    /// An earlier version of this function ALSO tested each `App`'s arguments,
    /// and the two tests were redundant — each alone refused this term, so
    /// deleting either one left every test green. Two guards that reject
    /// through the same case cannot be told apart by a single-guard mutation,
    /// which is exactly why the mutation was run before the shape was trusted.
    #[test]
    fn a_real_equality_is_refused_even_though_its_sort_is_bool() {
        let mut arena = TermArena::new();
        let x = arena.real_var("x").unwrap();
        let y = arena.real_var("y").unwrap();
        let eq = arena.eq(x, y).unwrap();
        assert_eq!(arena.sort_of(eq), Sort::Bool);
        assert!(!skeleton_is_pure_boolean(&arena, &[eq]));
    }

    /// THE POINT OF THE POLICY: the two arms return the same verdict in every
    /// round of the same blocking sequence. They decide the same clause set —
    /// the warm arm holds the skeleton plus everything learned so far, which is
    /// exactly what the cold arm rebuilds — so only the cost may differ.
    ///
    /// Driven over a real blocking sequence rather than one call: the warm arm's
    /// whole risk is that an assertion carried across rounds diverges from the
    /// formula the cold arm rebuilds, and a single-round comparison cannot see
    /// that.
    #[test]
    fn the_warm_and_cold_arms_agree_round_by_round() {
        let mut arena = TermArena::new();
        let (skeleton, props) = bool_skeleton(&mut arena);
        let config = crate::SolverConfig::new();

        let mut warm = SkeletonSolver::new(SkeletonSolvePolicy::WARM, &arena, &skeleton, &config);
        let mut cold = SkeletonSolver::new(SkeletonSolvePolicy::COLD, &arena, &skeleton, &config);
        assert!(
            matches!(warm, SkeletonSolver::Warm { .. }),
            "a pure Boolean skeleton must reach the warm arm, else this test is vacuous"
        );

        // Block every model one at a time, exactly as the loops do, until the
        // formula is exhausted. Both arms must agree at every step, INCLUDING
        // the final `unsat`.
        let mut blocking: Vec<TermId> = Vec::new();
        let mut rounds = 0usize;
        loop {
            let w = warm
                .solve_round(&mut arena, &skeleton, &blocking, &config)
                .expect("warm round");
            let c = cold
                .solve_round(&mut arena, &skeleton, &blocking, &config)
                .expect("cold round");
            match (&w, &c) {
                (CheckResult::Sat(_), CheckResult::Sat(_)) => {}
                (CheckResult::Unsat, CheckResult::Unsat) => break,
                _ => panic!("arms disagreed at round {rounds}: warm={w:?} cold={c:?}"),
            }
            let CheckResult::Sat(model) = &w else {
                unreachable!()
            };
            // Block this model: the clause is the negation of the assignment.
            let assignment = model.to_assignment();
            let mut lits = Vec::new();
            for &p in &props {
                let truth = assignment.get(p).and_then(|v| v.as_bool()).unwrap_or(false);
                let v = arena.var(p);
                lits.push(if truth { arena.not(v).unwrap() } else { v });
            }
            let mut clause = lits[0];
            for &l in &lits[1..] {
                clause = arena.or(clause, l).unwrap();
            }
            blocking.push(clause);
            rounds += 1;
            assert!(rounds < 32, "the blocking sequence should exhaust quickly");
        }
        assert!(
            rounds >= 2,
            "the comparison must run several rounds to be worth anything, ran {rounds}"
        );
    }

    /// A skeleton the warm arm cannot take falls back to the cold arm rather
    /// than erroring — the fallback is what makes the policy safe to default on.
    #[test]
    fn an_out_of_scope_skeleton_falls_back_to_the_cold_arm() {
        let mut arena = TermArena::new();
        let x = arena.real_var("x").unwrap();
        let zero = arena.real_const(Rational::integer(0));
        let atom = arena.real_lt(x, zero).unwrap();
        let config = crate::SolverConfig::new();
        let solver = SkeletonSolver::new(SkeletonSolvePolicy::WARM, &arena, &[atom], &config);
        assert!(matches!(solver, SkeletonSolver::Cold(_)));
    }
}
