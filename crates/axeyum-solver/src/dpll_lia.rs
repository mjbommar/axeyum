//! Boolean-structured linear arithmetic (`QF_LIA`, `QF_LRA`, and their
//! combination `QF_LIRA`) by lazy-SMT / DPLL(T) over the exact-rational
//! simplices.
//!
//! The conjunctive procedures decide a *conjunction* of linear constraints —
//! [`crate::check_with_lia_simplex`] for integers (ADR-0020),
//! [`crate::check_with_lra`] for reals (ADR-0015). This module lifts them to
//! **arbitrary Boolean structure** (disjunctions, implications, negations of
//! arithmetic atoms, over both sorts at once):
//!
//! 1. **Abstract** every linear-arithmetic order atom to a fresh Boolean
//!    proposition (equality `a = b` split to `(a <= b) AND (a >= b)`), tagging
//!    each by its theory (`Int`/`Real`), and keep the Boolean structure.
//! 2. **Decide the skeleton** (pure Boolean) for a truth assignment.
//! 3. **Theory-check** each theory's implied conjunction independently — integers
//!    and reals share no sort, so the combination is just propositional (no
//!    interface equalities). `sat` in both ⇒ build and replay a model; `unsat` in
//!    either ⇒ block the minimized conflict core and retry.
//!
//! Soundness: every model induces a skeleton-satisfying truth assignment whose
//! per-theory conjunctions are each satisfiable; the loop returns `sat` only
//! after replaying the original assertions, and `unsat` only when the skeleton
//! plus learned lemmas is propositionally unsatisfiable. A round budget bounds
//! the search (`unknown`, never wrong).

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::time::{Duration, Instant};

use axeyum_cnf::{CnfClause, CnfLit, CnfVar, IncrementalSat, SatError, SatResult};
use axeyum_ir::{
    Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval, well_founded_default,
};

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::lra::{
    check_with_lia_opaque_apps, check_with_lia_simplex, check_with_lra,
    lia_lp_relaxation_unsat_core,
};
use crate::model::Model;

const ATOM_PREFIX: &str = "!arith_atom_";
const MAX_DPLL_ROUNDS: usize = 10_000;
const MAX_INITIAL_BOUND_MUTEX_LEMMAS: usize = 8_192;
const MAX_INITIAL_BOUND_IMPLICATION_LEMMAS: usize = 4_096;
const MAX_INITIAL_BOUND_IMPLICATION_ATOMS: usize = 512;
const MAX_MINIMIZED_THEORY_CORE_ATOMS: usize = 128;
const MAX_TWO_EDGE_DIFF_EDGES: usize = 512;
const MAX_BELLMAN_FORD_DIFF_EDGES: usize = 256;
const MAX_DYNAMIC_BOUND_CONFLICT_BATCH: usize = 32;

/// The arithmetic theory an atom belongs to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Theory {
    Int,
    Real,
}

/// Hard cap on Boolean symbols a refutation's propositional half may have to be
/// verified by exhaustive enumeration; above it the certificate is declined.
const MAX_CERTIFIABLE_BOOLS: usize = 22;

/// One literal of a learned theory lemma: the atom's proposition, the truth it
/// took in the conflict, the arithmetic literal (atom or its negation) used to
/// re-check the lemma, and the theory that decides it.
#[derive(Debug, Clone, Copy)]
pub struct ArithLemmaLiteral {
    /// The fresh Boolean proposition standing for the atom.
    pub prop: SymbolId,
    /// The truth value the proposition took in the (infeasible) assignment.
    pub truth: bool,
    /// The arithmetic literal: the atom term when `truth`, else its negation.
    pub literal: TermId,
    theory: Theory,
}

/// A checkable refutation of a Boolean-structured linear-arithmetic query: the
/// Boolean skeleton plus the learned theory lemmas (each an infeasible core).
/// [`Self::verify`] re-checks it independently of the search: every lemma core is
/// re-decided `unsat` by its theory's exact procedure, and the skeleton with all
/// lemma clauses is shown propositionally unsatisfiable by enumeration.
#[derive(Debug, Clone)]
pub struct ArithDpllRefutation {
    /// The Boolean skeleton (one term per assertion, arithmetic atoms as props).
    pub skeleton: Vec<TermId>,
    /// The learned theory lemmas; each is an infeasible core of arithmetic
    /// literals from a single theory.
    pub lemmas: Vec<Vec<ArithLemmaLiteral>>,
}

/// The outcome of [`certify_arith_dpll_unsat`].
#[derive(Debug, Clone)]
pub enum ArithDpllOutcome {
    /// Satisfiable, with a replayed model.
    Sat(Model),
    /// Unsatisfiable, with a self-checked refutation.
    Unsat(ArithDpllRefutation),
    /// Undecided / not certifiable, with a reason.
    Unknown(UnknownReason),
}

/// Decides a Boolean-structured linear-arithmetic query and, on `unsat`, returns
/// a self-checked [`ArithDpllRefutation`].
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for input outside Boolean-structured
/// linear arithmetic or with too many Boolean symbols to verify; or
/// [`SolverError::Backend`] if the refutation fails its own check (a soundness
/// alarm).
pub fn certify_arith_dpll_unsat(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<ArithDpllOutcome, SolverError> {
    let run = run_arith_dpll(arena, assertions, config)?;
    match run.result {
        CheckResult::Sat(model) => Ok(ArithDpllOutcome::Sat(model)),
        CheckResult::Unknown(reason) => Ok(ArithDpllOutcome::Unknown(reason)),
        CheckResult::Unsat => {
            let refutation = ArithDpllRefutation {
                skeleton: run.skeleton,
                lemmas: run.lemmas,
            };
            if refutation.verify(arena)? {
                Ok(ArithDpllOutcome::Unsat(refutation))
            } else {
                Err(SolverError::Backend(
                    "arith-dpll refutation failed its own self-check".to_string(),
                ))
            }
        }
    }
}

impl ArithDpllRefutation {
    /// The Boolean symbols (atom props and original Boolean variables) the
    /// refutation ranges over, in deterministic order.
    fn bool_symbols(&self, arena: &TermArena) -> Vec<SymbolId> {
        let mut set = std::collections::BTreeSet::new();
        let mut stack = self.skeleton.clone();
        let mut seen = HashSet::new();
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

    /// Independently re-checks the refutation. Returns `Ok(true)` iff it holds.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::Unsupported`] if there are too many Boolean symbols
    /// to enumerate, or [`SolverError`] from a theory re-check or evaluation.
    pub fn verify(&self, arena: &TermArena) -> Result<bool, SolverError> {
        // (1) Every lemma core is a genuine theory contradiction.
        for lemma in &self.lemmas {
            let lits: Vec<TermId> = lemma.iter().map(|l| l.literal).collect();
            if lits.is_empty() {
                return Ok(false);
            }
            let theory = lemma[0].theory;
            let unsat = match theory {
                Theory::Int => {
                    matches!(
                        check_with_lia_opaque_apps(arena, &lits)?,
                        CheckResult::Unsat
                    )
                }
                Theory::Real => matches!(check_with_lra(arena, &lits)?, CheckResult::Unsat),
            };
            if !unsat {
                return Ok(false);
            }
        }

        // (2) skeleton AND every lemma clause is propositionally unsatisfiable.
        let bools = self.bool_symbols(arena);
        if bools.len() > MAX_CERTIFIABLE_BOOLS {
            return Err(SolverError::Unsupported(format!(
                "arith-dpll refutation has {} Boolean symbols, too many to verify by enumeration",
                bools.len()
            )));
        }
        let index_of: HashMap<SymbolId, usize> =
            bools.iter().enumerate().map(|(i, &s)| (s, i)).collect();
        let n = bools.len();
        for mask in 0u64..(1u64 << n) {
            let mut assignment = axeyum_ir::Assignment::new();
            for (i, &symbol) in bools.iter().enumerate() {
                assignment.set(symbol, Value::Bool((mask >> i) & 1 == 1));
            }
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
                            "arith-dpll verify: skeleton evaluation error: {error}"
                        )));
                    }
                }
            }
            if !skeleton_holds {
                continue;
            }
            // A lemma clause (the core's negation) is false exactly when the core
            // is fully satisfied; the refutation needs at least one clause false.
            let all_clauses_hold = self.lemmas.iter().all(|lemma| {
                let core_fully_satisfied = lemma
                    .iter()
                    .all(|l| (mask >> index_of[&l.prop]) & 1 == u64::from(l.truth));
                !core_fully_satisfied
            });
            if all_clauses_hold {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

/// Decides a Boolean-structured `QF_LIA` query (integer atoms only) by lazy-SMT.
///
/// A thin wrapper over [`check_with_arith_dpll`]; kept as a named entry point for
/// the integer dispatcher.
///
/// # Errors
///
/// See [`check_with_arith_dpll`].
pub fn check_with_lia_dpll(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    check_with_arith_dpll(arena, assertions, config)
}

/// Decides a Boolean-structured linear-arithmetic query — integer, real, or
/// combined `QF_LIRA` — by lazy-SMT over the exact-rational simplices.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] if an assertion is not Boolean structure
/// over linear-arithmetic atoms (e.g. it mentions bit-vectors, arrays, or
/// functions), so the caller can fall back; or [`SolverError::Backend`] on a
/// replay alarm.
pub fn check_with_arith_dpll(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    if contains_smtlib_unspecified_arith(arena, assertions) {
        return Err(SolverError::Unsupported(
            "lazy arithmetic: integer/real division or modulo with a divisor \
             that may be zero needs an explicit SMT-LIB underspecification encoding"
                .to_owned(),
        ));
    }
    // Prefer the shared CDCL(T) spine for pure-integer arithmetic
    // searches: it has 1-UIP learning, non-chronological backjumping, restarts,
    // and theory propagation, whereas the legacy path below repeatedly launches
    // a fresh SAT solve plus full simplex checks. With a configured wall-clock
    // budget, the online route gets a bounded probe and the legacy fallback
    // receives only the remaining time. Certification still uses
    // `run_arith_dpll` directly, preserving its explicit refutation artifact.
    let probe_started = Instant::now();
    let probe_config = online_lia_probe_config(config);
    match crate::lia_online::check_qf_lia_online(arena, assertions, &probe_config)? {
        CheckResult::Sat(model) => return Ok(CheckResult::Sat(model)),
        CheckResult::Unsat => return Ok(CheckResult::Unsat),
        CheckResult::Unknown(reason) if budget_unknown_kind(reason.kind) => {
            let Some(fallback_config) = remaining_config(config, probe_started) else {
                return Ok(CheckResult::Unknown(reason));
            };
            return Ok(run_arith_dpll(arena, assertions, &fallback_config)?.result);
        }
        CheckResult::Unknown(_) => {}
    }
    let fallback_config = remaining_config(config, probe_started).unwrap_or_else(|| config.clone());
    Ok(run_arith_dpll(arena, assertions, &fallback_config)?.result)
}

fn online_lia_probe_config(config: &SolverConfig) -> SolverConfig {
    let mut probe = config.clone();
    if let Some(timeout) = probe.timeout {
        let half = timeout.checked_div(2).unwrap_or(timeout);
        let bounded = half.min(Duration::from_secs(1));
        probe.timeout = Some(if bounded.is_zero() { timeout } else { bounded });
    }
    probe
}

fn remaining_config(config: &SolverConfig, started: Instant) -> Option<SolverConfig> {
    let Some(timeout) = config.timeout else {
        return Some(config.clone());
    };
    let remaining = timeout.checked_sub(started.elapsed())?;
    let mut fallback = config.clone();
    fallback.timeout = Some(remaining);
    Some(fallback)
}

fn config_with_deadline(config: &SolverConfig, deadline: Option<Instant>) -> SolverConfig {
    let Some(deadline) = deadline else {
        return config.clone();
    };
    let remaining = deadline
        .checked_duration_since(Instant::now())
        .unwrap_or(Duration::ZERO);
    let mut scoped = config.clone();
    scoped.timeout = Some(match config.timeout {
        Some(existing) => existing.min(remaining),
        None => remaining,
    });
    scoped
}

fn budget_unknown_kind(kind: UnknownKind) -> bool {
    matches!(
        kind,
        UnknownKind::Timeout
            | UnknownKind::ResourceLimit
            | UnknownKind::MemoryLimit
            | UnknownKind::NodeBudget
            | UnknownKind::EncodingBudget
    )
}

/// The lazy-SMT loop plus the trace needed to certify an `unsat` (the Boolean
/// skeleton and the learned theory lemmas).
struct ArithRun {
    result: CheckResult,
    skeleton: Vec<TermId>,
    lemmas: Vec<Vec<ArithLemmaLiteral>>,
}

#[derive(Default)]
struct ArithCoreStats {
    count: usize,
    total_len: usize,
    min_len: usize,
    max_len: usize,
    last_len: usize,
}

impl ArithCoreStats {
    fn record(&mut self, len: usize) {
        self.count += 1;
        self.total_len += len;
        self.last_len = len;
        self.min_len = if self.count == 1 {
            len
        } else {
            self.min_len.min(len)
        };
        self.max_len = self.max_len.max(len);
    }

    fn summary(&self) -> String {
        if self.count == 0 {
            return "core_lengths=none".to_owned();
        }
        let avg_tenths = self.total_len.saturating_mul(10) / self.count;
        format!(
            "core_len_last={}, core_len_min={}, core_len_max={}, core_len_avg={}.{}",
            self.last_len,
            self.min_len,
            self.max_len,
            avg_tenths / 10,
            avg_tenths % 10
        )
    }
}

#[derive(Default)]
struct ArithSupportStats {
    attempts: usize,
    unavailable: usize,
    conflict_batches: usize,
    model_attempts: usize,
    replay_failures: usize,
    full_fallbacks: usize,
}

impl ArithSupportStats {
    fn summary(&self) -> String {
        format!(
            "support_attempts={}, support_unavailable={}, support_conflict_batches={}, \
             support_model_attempts={}, support_replay_failures={}, full_fallbacks={}",
            self.attempts,
            self.unavailable,
            self.conflict_batches,
            self.model_attempts,
            self.replay_failures,
            self.full_fallbacks
        )
    }
}

#[allow(clippy::too_many_lines)]
fn run_arith_dpll(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<ArithRun, SolverError> {
    let mut ctx = ArithAbstractor::default();
    let mut skeleton = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        skeleton.push(ctx.abstract_term(arena, assertion)?);
    }

    let mut initial_lemmas = initial_int_bound_mutex_lemmas(arena, &ctx)?;
    initial_lemmas.extend(initial_int_bound_implication_lemmas(arena, &ctx)?);
    let mut prop_solver = BoolSkeletonSolver::new();
    prop_solver.assert_all(arena, &skeleton)?;
    for (clause, _) in &initial_lemmas {
        prop_solver.assert(arena, *clause)?;
    }
    let mut blocking: Vec<TermId> = Vec::new();
    let mut lemmas: Vec<Vec<ArithLemmaLiteral>> = initial_lemmas
        .iter()
        .map(|(_, lemma)| lemma.clone())
        .collect();
    let mut core_stats = ArithCoreStats::default();
    let mut support_stats = ArithSupportStats::default();

    // Wall-clock deadline (graceful `Unknown`, never an unbounded hang — the
    // standing hard rule). The lazy-SMT loop can need up to `MAX_DPLL_ROUNDS`
    // refinements, each a fresh SAT solve plus simplex over a growing clause set;
    // on a large instance that is effectively unbounded, so honor `config.timeout`
    // by checking the deadline at the top of every round. Exceeding it degrades to
    // the same sound `Unknown(ResourceLimit)` the round-exhaustion path returns —
    // a decided verdict is only ever reached *inside* a round, never by timeout.
    let deadline = config.timeout.map(|t| Instant::now() + t);

    for round in 0..MAX_DPLL_ROUNDS {
        if deadline.is_some_and(|d| Instant::now() >= d) {
            return Ok(ArithRun {
                result: CheckResult::Unknown(UnknownReason {
                    kind: UnknownKind::ResourceLimit,
                    detail: format!(
                        "lazy linear arithmetic exhausted the configured timeout after {round} \
                         rounds (atoms={}, bound_lemmas={}, blocking_lemmas={}, {}, {})",
                        ctx.atoms.len(),
                        initial_lemmas.len(),
                        blocking.len(),
                        core_stats.summary(),
                        support_stats.summary()
                    ),
                }),
                skeleton,
                lemmas,
            });
        }
        let round_config = config_with_deadline(config, deadline);
        let propositional = match prop_solver.solve(&round_config)? {
            CheckResult::Sat(model) => model,
            CheckResult::Unsat => {
                return Ok(ArithRun {
                    result: CheckResult::Unsat,
                    skeleton,
                    lemmas,
                });
            }
            CheckResult::Unknown(reason) => {
                return Ok(ArithRun {
                    result: CheckResult::Unknown(UnknownReason {
                        kind: reason.kind,
                        detail: format!(
                            "lazy linear arithmetic SAT skeleton declined after round {round} \
                             (atoms={}, bound_lemmas={}, blocking_lemmas={}, {}, {}): {}",
                            ctx.atoms.len(),
                            initial_lemmas.len(),
                            blocking.len(),
                            core_stats.summary(),
                            support_stats.summary(),
                            reason.detail
                        ),
                    }),
                    skeleton,
                    lemmas,
                });
            }
        };

        // The arithmetic literal implied by this assignment for each atom, in
        // `ctx.atoms` order.
        let mut truths = Vec::with_capacity(ctx.atoms.len());
        let mut lits = Vec::with_capacity(ctx.atoms.len());
        for atom in &ctx.atoms {
            let truth = propositional
                .get(atom.prop)
                .and_then(|v| v.as_bool())
                .unwrap_or(false);
            truths.push(truth);
            lits.push(if truth {
                atom.term
            } else {
                arena.not(atom.term)?
            });
        }

        // First check only the arithmetic atoms needed to justify the current
        // Boolean model. SAT solvers assign every Boolean variable, including
        // atoms sitting in dead branches of generated selector ladders; those
        // irrelevant choices need not be theory-consistent for a real model.
        if let Some(support) = justified_theory_indices(arena, &ctx, &skeleton, &propositional) {
            support_stats.attempts += 1;
            let int_conflicts = theory_conflicts_for_indices(
                arena,
                &ctx,
                &lits,
                &support,
                Theory::Int,
                check_with_lia_opaque_apps,
            )?;
            if !int_conflicts.is_empty() {
                support_stats.conflict_batches += 1;
                let mut learn = ArithLearnState {
                    prop_solver: &mut prop_solver,
                    blocking: &mut blocking,
                    lemmas: &mut lemmas,
                    core_stats: &mut core_stats,
                };
                record_conflict_batch(arena, &ctx, &truths, &lits, &int_conflicts, &mut learn)?;
                continue;
            }
            let real_conflicts = theory_conflicts_for_indices(
                arena,
                &ctx,
                &lits,
                &support,
                Theory::Real,
                check_with_lra,
            )?;
            if !real_conflicts.is_empty() {
                support_stats.conflict_batches += 1;
                let mut learn = ArithLearnState {
                    prop_solver: &mut prop_solver,
                    blocking: &mut blocking,
                    lemmas: &mut lemmas,
                    core_stats: &mut core_stats,
                };
                record_conflict_batch(arena, &ctx, &truths, &lits, &real_conflicts, &mut learn)?;
                continue;
            }
            if !ctx.has_opaque_int_apps(arena) {
                support_stats.model_attempts += 1;
                if let Some(result) =
                    try_finish_sat(arena, assertions, &ctx, &propositional, &lits, &support)?
                {
                    return Ok(ArithRun {
                        result,
                        skeleton,
                        lemmas,
                    });
                }
                support_stats.replay_failures += 1;
            }
        } else {
            support_stats.unavailable += 1;
        }

        // If the support path did not produce a replaying model, fall back to
        // the traditional full-assignment theory check.
        support_stats.full_fallbacks += 1;
        let int_conflicts =
            theory_conflicts(arena, &ctx, &lits, Theory::Int, check_with_lia_opaque_apps)?;
        if !int_conflicts.is_empty() {
            let mut learn = ArithLearnState {
                prop_solver: &mut prop_solver,
                blocking: &mut blocking,
                lemmas: &mut lemmas,
                core_stats: &mut core_stats,
            };
            record_conflict_batch(arena, &ctx, &truths, &lits, &int_conflicts, &mut learn)?;
            continue;
        }
        let real_conflicts = theory_conflicts(arena, &ctx, &lits, Theory::Real, check_with_lra)?;
        if !real_conflicts.is_empty() {
            let mut learn = ArithLearnState {
                prop_solver: &mut prop_solver,
                blocking: &mut blocking,
                lemmas: &mut lemmas,
                core_stats: &mut core_stats,
            };
            record_conflict_batch(arena, &ctx, &truths, &lits, &real_conflicts, &mut learn)?;
            continue;
        }

        // Both theories consistent: build and replay the combined model.
        if ctx.has_opaque_int_apps(arena) {
            return Ok(ArithRun {
                result: CheckResult::Unknown(UnknownReason {
                    kind: UnknownKind::Incomplete,
                    detail: "linear-arithmetic abstraction with opaque integer UF applications is \
                             satisfiable; use the UFLIA backend for model lifting"
                        .to_owned(),
                }),
                skeleton,
                lemmas,
            });
        }
        let result = finish_sat(arena, assertions, &ctx, &propositional, &lits)?;
        return Ok(ArithRun {
            result,
            skeleton,
            lemmas,
        });
    }

    Ok(ArithRun {
        result: CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::Incomplete,
            detail: format!("lazy linear arithmetic exceeded {MAX_DPLL_ROUNDS} refinement rounds"),
        }),
        skeleton,
        lemmas,
    })
}

/// Records a theory conflict core as a structured lemma for certification.
fn record_lemma(
    ctx: &ArithAbstractor,
    truths: &[bool],
    lits: &[TermId],
    core: &[usize],
) -> Vec<ArithLemmaLiteral> {
    core.iter()
        .map(|&i| ArithLemmaLiteral {
            prop: ctx.atoms[i].prop,
            truth: truths[i],
            literal: lits[i],
            theory: ctx.atoms[i].theory,
        })
        .collect()
}

struct ArithLearnState<'a> {
    prop_solver: &'a mut BoolSkeletonSolver,
    blocking: &'a mut Vec<TermId>,
    lemmas: &'a mut Vec<Vec<ArithLemmaLiteral>>,
    core_stats: &'a mut ArithCoreStats,
}

fn record_conflict_batch(
    arena: &mut TermArena,
    ctx: &ArithAbstractor,
    truths: &[bool],
    lits: &[TermId],
    conflicts: &[Vec<usize>],
    learn: &mut ArithLearnState<'_>,
) -> Result<(), SolverError> {
    for conflict in conflicts {
        learn.core_stats.record(conflict.len());
        learn.lemmas.push(record_lemma(ctx, truths, lits, conflict));
        let clause = block_clause(arena, &ctx.atoms, truths, conflict)?;
        learn.prop_solver.assert(arena, clause)?;
        learn.blocking.push(clause);
    }
    Ok(())
}

/// Checks one theory's conjunction; on `unsat`, returns one or more conflict
/// cores as global atom indices. `oracle` is the conjunctive decision procedure
/// for the theory.
fn theory_conflicts(
    arena: &TermArena,
    ctx: &ArithAbstractor,
    lits: &[TermId],
    theory: Theory,
    oracle: fn(&TermArena, &[TermId]) -> Result<CheckResult, SolverError>,
) -> Result<Vec<Vec<usize>>, SolverError> {
    let indices: Vec<usize> = (0..ctx.atoms.len())
        .filter(|&i| ctx.atoms[i].theory == theory)
        .collect();
    theory_conflicts_for_indices(arena, ctx, lits, &indices, theory, oracle)
}

fn theory_conflicts_for_indices(
    arena: &TermArena,
    ctx: &ArithAbstractor,
    lits: &[TermId],
    indices: &[usize],
    theory: Theory,
    oracle: fn(&TermArena, &[TermId]) -> Result<CheckResult, SolverError>,
) -> Result<Vec<Vec<usize>>, SolverError> {
    let indices: Vec<usize> = indices
        .iter()
        .copied()
        .filter(|&i| ctx.atoms[i].theory == theory)
        .collect();
    if indices.is_empty() {
        return Ok(Vec::new());
    }
    let conj: Vec<TermId> = indices.iter().map(|&i| lits[i]).collect();
    if !matches!(oracle(arena, &conj)?, CheckResult::Unsat) {
        return Ok(Vec::new());
    }
    if theory == Theory::Int {
        let bound_cores = cheap_int_bound_conflict_cores(arena, ctx, lits, &indices);
        if !bound_cores.is_empty() {
            return Ok(bound_cores);
        }
        if let Some(core) = cheap_int_difference_conflict_core(arena, ctx, lits, &indices) {
            return Ok(vec![core]);
        }
        if let Some(core) = lp_relaxation_conflict_core(arena, lits, &indices)? {
            return Ok(vec![core]);
        }
    }
    if indices.len() > MAX_MINIMIZED_THEORY_CORE_ATOMS {
        return Ok(vec![indices]);
    }
    Ok(vec![minimize_core(arena, &indices, lits, oracle)?])
}

/// Extracts an LP-relaxation Farkas-supported core from the integer side of a
/// theory conflict. The integer oracle has already established the full
/// conjunction is `unsat`; this helper applies only when the real relaxation is
/// also infeasible, in which case the returned core is a sound LIA conflict.
fn lp_relaxation_conflict_core(
    arena: &TermArena,
    lits: &[TermId],
    indices: &[usize],
) -> Result<Option<Vec<usize>>, SolverError> {
    let conj: Vec<TermId> = indices.iter().map(|&i| lits[i]).collect();
    let Some(local_core) = lia_lp_relaxation_unsat_core(arena, &conj, true)? else {
        return Ok(None);
    };
    let mut core: Vec<usize> = local_core.into_iter().map(|local| indices[local]).collect();
    core.sort_unstable();
    core.dedup();
    Ok((!core.is_empty()).then_some(core))
}

/// Extracts a small conflicting integer-bound core from the current SAT
/// assignment. The oracle has already established that the full integer slice is
/// unsatisfiable; this helper only replaces a large low-relevance core with an
/// independently checkable two-literal bound conflict when one is obvious.
fn cheap_int_bound_conflict_cores(
    arena: &TermArena,
    ctx: &ArithAbstractor,
    lits: &[TermId],
    indices: &[usize],
) -> Vec<Vec<usize>> {
    let mut bounds = Vec::new();
    for &idx in indices {
        let Some(truth) = assigned_atom_truth(arena, &ctx.atoms[idx], lits[idx]) else {
            return Vec::new();
        };
        bounds.extend(
            simple_int_literal_bounds(arena, idx, &ctx.atoms[idx])
                .into_iter()
                .filter(|bound| bound.truth == truth),
        );
    }

    let mut conflicts = Vec::new();
    let mut seen = HashSet::new();
    for i in 0..bounds.len() {
        for j in (i + 1)..bounds.len() {
            let Some((lower, upper)) = conflicting_bounds(&bounds[i], &bounds[j]) else {
                continue;
            };
            let key = if lower.atom_idx <= upper.atom_idx {
                (lower.atom_idx, upper.atom_idx)
            } else {
                (upper.atom_idx, lower.atom_idx)
            };
            if !seen.insert(key) {
                continue;
            }
            conflicts.push(vec![lower.atom_idx, upper.atom_idx]);
            if conflicts.len() >= MAX_DYNAMIC_BOUND_CONFLICT_BATCH {
                return conflicts;
            }
        }
    }
    conflicts
}

fn assigned_atom_truth(arena: &TermArena, atom: &ArithAtom, lit: TermId) -> Option<bool> {
    if lit == atom.term {
        return Some(true);
    }
    let TermNode::App { op, args } = arena.node(lit) else {
        return None;
    };
    (*op == Op::BoolNot && args[0] == atom.term).then_some(false)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum DiffVar {
    Zero,
    Sym(SymbolId),
}

#[derive(Clone, Copy)]
struct AffineUnit {
    var: DiffVar,
    constant: i128,
}

#[derive(Clone, Copy)]
struct DifferenceEdge {
    from: DiffVar,
    to: DiffVar,
    weight: i128,
    atom_idx: usize,
}

/// Extracts a small integer-difference-logic conflict core from the current SAT
/// assignment. This recognizes only unit-coefficient affine terms (`x + c`) and
/// strict/non-strict order atoms. It is deliberately a cheap pre-core heuristic:
/// the full LIA oracle has already said the conjunction is unsat, and the normal
/// arithmetic lemma verifier still checks any returned cycle.
fn cheap_int_difference_conflict_core(
    arena: &TermArena,
    ctx: &ArithAbstractor,
    lits: &[TermId],
    indices: &[usize],
) -> Option<Vec<usize>> {
    let mut edges = Vec::new();
    for &idx in indices {
        let truth = assigned_atom_truth(arena, &ctx.atoms[idx], lits[idx])?;
        if let Some(edge) = difference_edge_for_atom(arena, idx, &ctx.atoms[idx], truth) {
            edges.push(edge);
        }
    }
    negative_cycle_core(&edges)
}

fn difference_edge_for_atom(
    arena: &TermArena,
    atom_idx: usize,
    atom: &ArithAtom,
    truth: bool,
) -> Option<DifferenceEdge> {
    if atom.theory != Theory::Int {
        return None;
    }
    let TermNode::App { op, args } = arena.node(atom.term) else {
        return None;
    };
    let strict = match op {
        Op::IntLt => true,
        Op::IntLe => false,
        _ => return None,
    };
    if truth {
        difference_edge_for_order(arena, atom_idx, args[0], args[1], strict)
    } else {
        // not (a <= b)  ==  b < a
        // not (a < b)   ==  b <= a
        difference_edge_for_order(arena, atom_idx, args[1], args[0], !strict)
    }
}

fn difference_edge_for_order(
    arena: &TermArena,
    atom_idx: usize,
    lhs: TermId,
    rhs: TermId,
    strict: bool,
) -> Option<DifferenceEdge> {
    let lhs = affine_unit(arena, lhs)?;
    let rhs = affine_unit(arena, rhs)?;
    let mut weight = rhs.constant.checked_sub(lhs.constant)?;
    if strict {
        weight = weight.checked_sub(1)?;
    }
    Some(DifferenceEdge {
        from: rhs.var,
        to: lhs.var,
        weight,
        atom_idx,
    })
}

fn affine_unit(arena: &TermArena, term: TermId) -> Option<AffineUnit> {
    match arena.node(term) {
        TermNode::IntConst(value) => Some(AffineUnit {
            var: DiffVar::Zero,
            constant: *value,
        }),
        TermNode::Symbol(symbol) if arena.sort_of(term) == Sort::Int => Some(AffineUnit {
            var: DiffVar::Sym(*symbol),
            constant: 0,
        }),
        TermNode::App {
            op: Op::IntAdd,
            args,
        } => affine_unit_const_add(arena, args[0], args[1]),
        TermNode::App {
            op: Op::IntSub,
            args,
        } => {
            let mut base = affine_unit(arena, args[0])?;
            let c = int_const_value(arena, args[1])?;
            base.constant = base.constant.checked_sub(c)?;
            Some(base)
        }
        _ => None,
    }
}

fn affine_unit_const_add(arena: &TermArena, lhs: TermId, rhs: TermId) -> Option<AffineUnit> {
    if let Some(c) = int_const_value(arena, lhs) {
        let mut base = affine_unit(arena, rhs)?;
        base.constant = base.constant.checked_add(c)?;
        return Some(base);
    }
    let c = int_const_value(arena, rhs)?;
    let mut base = affine_unit(arena, lhs)?;
    base.constant = base.constant.checked_add(c)?;
    Some(base)
}

fn negative_cycle_core(edges: &[DifferenceEdge]) -> Option<Vec<usize>> {
    if edges.is_empty() {
        return None;
    }
    if edges.len() > MAX_TWO_EDGE_DIFF_EDGES {
        return None;
    }
    if let Some(core) = two_edge_negative_cycle_core(edges) {
        return Some(core);
    }
    if edges.len() > MAX_BELLMAN_FORD_DIFF_EDGES {
        return None;
    }
    let mut vars = BTreeMap::new();
    for edge in edges {
        let next = vars.len();
        vars.entry(edge.from).or_insert(next);
        let next = vars.len();
        vars.entry(edge.to).or_insert(next);
    }

    let n = vars.len();
    let mut dist = vec![0_i128; n];
    let mut pred_vertex: Vec<Option<usize>> = vec![None; n];
    let mut pred_edge: Vec<Option<usize>> = vec![None; n];
    let mut changed = None;

    for _ in 0..n {
        changed = None;
        for (edge_idx, edge) in edges.iter().enumerate() {
            let from = vars[&edge.from];
            let to = vars[&edge.to];
            let candidate = dist[from].checked_add(edge.weight)?;
            if candidate < dist[to] {
                dist[to] = candidate;
                pred_vertex[to] = Some(from);
                pred_edge[to] = Some(edge_idx);
                changed = Some(to);
            }
        }
    }

    let mut v = changed?;
    for _ in 0..n {
        v = pred_vertex[v]?;
    }
    let start = v;
    let mut core = Vec::new();
    for _ in 0..=n {
        let edge_idx = pred_edge[v]?;
        core.push(edges[edge_idx].atom_idx);
        v = pred_vertex[v]?;
        if v == start {
            core.sort_unstable();
            core.dedup();
            return Some(core);
        }
    }
    None
}

fn two_edge_negative_cycle_core(edges: &[DifferenceEdge]) -> Option<Vec<usize>> {
    let mut best: BTreeMap<(DiffVar, DiffVar), (i128, usize)> = BTreeMap::new();
    for edge in edges {
        let entry = best
            .entry((edge.from, edge.to))
            .or_insert((edge.weight, edge.atom_idx));
        if edge.weight < entry.0 {
            *entry = (edge.weight, edge.atom_idx);
        }
    }
    for (&(from, to), &(weight, atom_idx)) in &best {
        let Some(&(reverse_weight, reverse_atom_idx)) = best.get(&(to, from)) else {
            continue;
        };
        if weight
            .checked_add(reverse_weight)
            .is_some_and(|sum| sum < 0)
        {
            let mut core = vec![atom_idx, reverse_atom_idx];
            core.sort_unstable();
            core.dedup();
            return Some(core);
        }
    }
    None
}

/// Deletion-based minimization: returns a minimal still-unsatisfiable subset of
/// `indices` (global atom indices). Each surviving member is necessary, so the
/// negated core is a strong, sound lemma.
fn minimize_core(
    arena: &TermArena,
    indices: &[usize],
    lits: &[TermId],
    oracle: fn(&TermArena, &[TermId]) -> Result<CheckResult, SolverError>,
) -> Result<Vec<usize>, SolverError> {
    let mut core: Vec<usize> = indices.to_vec();
    for &candidate in indices {
        if !core.contains(&candidate) {
            continue;
        }
        let trial: Vec<TermId> = core
            .iter()
            .filter(|&&i| i != candidate)
            .map(|&i| lits[i])
            .collect();
        if !trial.is_empty() && matches!(oracle(arena, &trial)?, CheckResult::Unsat) {
            core.retain(|&i| i != candidate);
        }
    }
    Ok(core)
}

fn justified_theory_indices(
    arena: &TermArena,
    ctx: &ArithAbstractor,
    skeleton: &[TermId],
    propositional: &Model,
) -> Option<Vec<usize>> {
    let prop_to_atom: HashMap<SymbolId, usize> = ctx
        .atoms
        .iter()
        .enumerate()
        .map(|(idx, atom)| (atom.prop, idx))
        .collect();
    let mut support = BTreeSet::new();
    for &assertion in skeleton {
        collect_bool_support(
            arena,
            assertion,
            true,
            propositional,
            &prop_to_atom,
            &mut support,
        )?;
    }
    Some(support.into_iter().collect())
}

fn collect_bool_support(
    arena: &TermArena,
    term: TermId,
    expected: bool,
    propositional: &Model,
    prop_to_atom: &HashMap<SymbolId, usize>,
    support: &mut BTreeSet<usize>,
) -> Option<()> {
    if skeleton_bool_value(arena, term, propositional)? != expected {
        return None;
    }
    match arena.node(term) {
        TermNode::BoolConst(_) => Some(()),
        TermNode::Symbol(symbol) if arena.sort_of(term) == Sort::Bool => {
            if let Some(&idx) = prop_to_atom.get(symbol) {
                support.insert(idx);
            }
            Some(())
        }
        TermNode::App { op, args } => match op {
            Op::BoolNot => collect_bool_support(
                arena,
                args[0],
                !expected,
                propositional,
                prop_to_atom,
                support,
            ),
            Op::BoolAnd => {
                collect_and_support(arena, args, expected, propositional, prop_to_atom, support)
            }
            Op::BoolOr => {
                collect_or_support(arena, args, expected, propositional, prop_to_atom, support)
            }
            Op::BoolImplies => {
                collect_implies_support(arena, args, expected, propositional, prop_to_atom, support)
            }
            Op::BoolXor => {
                collect_binary_value_support(arena, args, propositional, prop_to_atom, support)
            }
            Op::Eq if arena.sort_of(args[0]) == Sort::Bool => {
                collect_binary_value_support(arena, args, propositional, prop_to_atom, support)
            }
            Op::Ite if arena.sort_of(term) == Sort::Bool => {
                collect_ite_support(arena, args, expected, propositional, prop_to_atom, support)
            }
            _ => None,
        },
        _ => None,
    }
}

fn collect_all_bool_support(
    arena: &TermArena,
    args: &[TermId],
    expected: bool,
    propositional: &Model,
    prop_to_atom: &HashMap<SymbolId, usize>,
    support: &mut BTreeSet<usize>,
) -> Option<()> {
    for &arg in args {
        collect_bool_support(arena, arg, expected, propositional, prop_to_atom, support)?;
    }
    Some(())
}

fn collect_and_support(
    arena: &TermArena,
    args: &[TermId],
    expected: bool,
    propositional: &Model,
    prop_to_atom: &HashMap<SymbolId, usize>,
    support: &mut BTreeSet<usize>,
) -> Option<()> {
    if expected {
        collect_all_bool_support(arena, args, true, propositional, prop_to_atom, support)
    } else {
        let witness = args
            .iter()
            .copied()
            .find(|&arg| skeleton_bool_value(arena, arg, propositional) == Some(false))?;
        collect_bool_support(arena, witness, false, propositional, prop_to_atom, support)
    }
}

fn collect_or_support(
    arena: &TermArena,
    args: &[TermId],
    expected: bool,
    propositional: &Model,
    prop_to_atom: &HashMap<SymbolId, usize>,
    support: &mut BTreeSet<usize>,
) -> Option<()> {
    if expected {
        let witness = args
            .iter()
            .copied()
            .find(|&arg| skeleton_bool_value(arena, arg, propositional) == Some(true))?;
        collect_bool_support(arena, witness, true, propositional, prop_to_atom, support)
    } else {
        collect_all_bool_support(arena, args, false, propositional, prop_to_atom, support)
    }
}

fn collect_implies_support(
    arena: &TermArena,
    args: &[TermId],
    expected: bool,
    propositional: &Model,
    prop_to_atom: &HashMap<SymbolId, usize>,
    support: &mut BTreeSet<usize>,
) -> Option<()> {
    let lhs = skeleton_bool_value(arena, args[0], propositional)?;
    let rhs = skeleton_bool_value(arena, args[1], propositional)?;
    if expected {
        if lhs {
            collect_bool_support(arena, args[1], true, propositional, prop_to_atom, support)
        } else {
            collect_bool_support(arena, args[0], false, propositional, prop_to_atom, support)
        }
    } else if lhs && !rhs {
        collect_bool_support(arena, args[0], true, propositional, prop_to_atom, support)?;
        collect_bool_support(arena, args[1], false, propositional, prop_to_atom, support)
    } else {
        None
    }
}

fn collect_ite_support(
    arena: &TermArena,
    args: &[TermId],
    expected: bool,
    propositional: &Model,
    prop_to_atom: &HashMap<SymbolId, usize>,
    support: &mut BTreeSet<usize>,
) -> Option<()> {
    let condition = skeleton_bool_value(arena, args[0], propositional)?;
    collect_bool_support(
        arena,
        args[0],
        condition,
        propositional,
        prop_to_atom,
        support,
    )?;
    collect_bool_support(
        arena,
        args[if condition { 1 } else { 2 }],
        expected,
        propositional,
        prop_to_atom,
        support,
    )
}

fn collect_binary_value_support(
    arena: &TermArena,
    args: &[TermId],
    propositional: &Model,
    prop_to_atom: &HashMap<SymbolId, usize>,
    support: &mut BTreeSet<usize>,
) -> Option<()> {
    let lhs = skeleton_bool_value(arena, args[0], propositional)?;
    let rhs = skeleton_bool_value(arena, args[1], propositional)?;
    collect_bool_support(arena, args[0], lhs, propositional, prop_to_atom, support)?;
    collect_bool_support(arena, args[1], rhs, propositional, prop_to_atom, support)
}

fn skeleton_bool_value(arena: &TermArena, term: TermId, propositional: &Model) -> Option<bool> {
    match arena.node(term) {
        TermNode::BoolConst(value) => Some(*value),
        TermNode::Symbol(symbol) if arena.sort_of(term) == Sort::Bool => propositional
            .get(*symbol)
            .and_then(|value| value.as_bool())
            .or(Some(false)),
        TermNode::App { op, args } => match op {
            Op::BoolNot => Some(!skeleton_bool_value(arena, args[0], propositional)?),
            Op::BoolAnd => Some(
                skeleton_bool_value(arena, args[0], propositional)?
                    && skeleton_bool_value(arena, args[1], propositional)?,
            ),
            Op::BoolOr => Some(
                skeleton_bool_value(arena, args[0], propositional)?
                    || skeleton_bool_value(arena, args[1], propositional)?,
            ),
            Op::BoolImplies => Some(
                !skeleton_bool_value(arena, args[0], propositional)?
                    || skeleton_bool_value(arena, args[1], propositional)?,
            ),
            Op::BoolXor => Some(
                skeleton_bool_value(arena, args[0], propositional)?
                    ^ skeleton_bool_value(arena, args[1], propositional)?,
            ),
            Op::Eq if arena.sort_of(args[0]) == Sort::Bool => Some(
                skeleton_bool_value(arena, args[0], propositional)?
                    == skeleton_bool_value(arena, args[1], propositional)?,
            ),
            Op::Ite if arena.sort_of(term) == Sort::Bool => {
                if skeleton_bool_value(arena, args[0], propositional)? {
                    skeleton_bool_value(arena, args[1], propositional)
                } else {
                    skeleton_bool_value(arena, args[2], propositional)
                }
            }
            _ => None,
        },
        _ => None,
    }
}

/// Builds the combined model (integers from the integer simplex, reals from the
/// real engine, Booleans from the skeleton) and replays the original assertions.
fn finish_sat(
    arena: &mut TermArena,
    assertions: &[TermId],
    ctx: &ArithAbstractor,
    propositional: &Model,
    lits: &[TermId],
) -> Result<CheckResult, SolverError> {
    let all_indices = (0..ctx.atoms.len()).collect::<Vec<_>>();
    try_finish_sat(arena, assertions, ctx, propositional, lits, &all_indices)?.ok_or_else(|| {
        SolverError::Backend(
            "arith dpll sat model replay failed after full theory check".to_owned(),
        )
    })
}

fn try_finish_sat(
    arena: &mut TermArena,
    assertions: &[TermId],
    ctx: &ArithAbstractor,
    propositional: &Model,
    lits: &[TermId],
    indices: &[usize],
) -> Result<Option<CheckResult>, SolverError> {
    // Re-decide each theory's conjunction to recover its model (the loop only
    // learned that they are *consistent*).
    let int_lits: Vec<TermId> = atom_lits(ctx, lits, indices, Theory::Int);
    let real_lits: Vec<TermId> = atom_lits(ctx, lits, indices, Theory::Real);
    let int_model = theory_model(arena, &int_lits, check_with_lia_simplex)?;
    let real_model = theory_model(arena, &real_lits, check_with_lra)?;

    let mut model = Model::new();
    let mut assignment = axeyum_ir::Assignment::new();
    for (symbol, name, sort) in arena.symbols() {
        if ctx.is_atom_prop(symbol) || name.starts_with(ATOM_PREFIX) {
            continue;
        }
        let value = (match sort {
            Sort::Int => int_model.as_ref().and_then(|m| m.get(symbol)),
            Sort::Real => real_model.as_ref().and_then(|m| m.get(symbol)),
            Sort::Bool => propositional.get(symbol),
            _ => None,
        })
        .or_else(|| well_founded_default(arena, sort));
        let Some(value) = value else {
            continue;
        };
        model.set(symbol, value.clone());
        assignment.set(symbol, value);
    }
    for &assertion in assertions {
        match eval(arena, assertion, &assignment) {
            Ok(Value::Bool(true)) => {}
            Ok(_) => return Ok(None),
            Err(error) => {
                return Err(SolverError::Backend(format!(
                    "arith dpll sat model replay error on assertion #{}: {error}",
                    assertion.index()
                )));
            }
        }
    }
    Ok(Some(CheckResult::Sat(model)))
}

/// The literals of one theory's atoms.
fn atom_lits(
    ctx: &ArithAbstractor,
    lits: &[TermId],
    indices: &[usize],
    theory: Theory,
) -> Vec<TermId> {
    indices
        .iter()
        .copied()
        .filter(|&i| ctx.atoms[i].theory == theory)
        .map(|i| lits[i])
        .collect()
}

/// Re-decides a consistent theory conjunction to recover its model.
fn theory_model(
    arena: &TermArena,
    lits: &[TermId],
    oracle: fn(&TermArena, &[TermId]) -> Result<CheckResult, SolverError>,
) -> Result<Option<Model>, SolverError> {
    if lits.is_empty() {
        return Ok(None);
    }
    match oracle(arena, lits)? {
        CheckResult::Sat(model) => Ok(Some(model)),
        // The loop already established consistency, so this is unreachable; treat
        // as no extra bindings rather than failing.
        _ => Ok(None),
    }
}

/// Warm propositional SAT solver for the arithmetic skeleton.
///
/// The legacy arithmetic loop repeatedly adds theory blocking clauses over the
/// same Boolean skeleton. Re-lowering that pure-Boolean formula through the
/// general BV backend every round spends most of the budget on Bool→AIG→CNF
/// rebuilding once the learned clause set grows. This small encoder builds a
/// Tseitin CNF for the skeleton once, keeps `BatSat` warm, and adds each learned
/// theory clause incrementally. SAT candidates still flow through
/// `finish_sat`, which reconstructs arithmetic models and replays the original
/// assertions before returning `sat`.
#[derive(Default)]
struct BoolSkeletonSolver {
    sat: IncrementalSat,
    next_var: usize,
    term_lit: HashMap<TermId, BoolCnfLit>,
    symbol_var: HashMap<SymbolId, CnfVar>,
}

impl BoolSkeletonSolver {
    fn new() -> Self {
        Self::default()
    }

    fn assert_all(&mut self, arena: &TermArena, assertions: &[TermId]) -> Result<(), SolverError> {
        for &assertion in assertions {
            self.assert(arena, assertion)?;
        }
        Ok(())
    }

    fn assert(&mut self, arena: &TermArena, assertion: TermId) -> Result<(), SolverError> {
        let lit = self.encode(arena, assertion)?;
        self.add_clause(&[lit])
    }

    fn solve(&mut self, config: &SolverConfig) -> Result<CheckResult, SolverError> {
        match self
            .sat
            .solve(config.timeout)
            .map_err(|error| map_incremental_sat_error(&error))?
        {
            SatResult::Sat(assignment) => Ok(CheckResult::Sat(self.model_from(&assignment))),
            SatResult::Unsat(_) => Ok(CheckResult::Unsat),
            SatResult::Unknown(reason) => Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::Timeout,
                detail: reason.detail,
            })),
        }
    }

    fn model_from(&self, assignment: &axeyum_cnf::CnfAssignment) -> Model {
        let mut model = Model::new();
        for (&symbol, &var) in &self.symbol_var {
            if let Some(value) = assignment.value(var) {
                model.set(symbol, Value::Bool(value));
            }
        }
        model
    }

    fn encode(&mut self, arena: &TermArena, term: TermId) -> Result<BoolCnfLit, SolverError> {
        if let Some(&lit) = self.term_lit.get(&term) {
            return Ok(lit);
        }
        let lit = match arena.node(term).clone() {
            TermNode::BoolConst(value) => BoolCnfLit::Const(value),
            TermNode::Symbol(symbol) if arena.sort_of(term) == Sort::Bool => {
                BoolCnfLit::Lit(CnfLit::positive(self.symbol_var(symbol)?))
            }
            TermNode::App { op, args } => self.encode_app(arena, term, op, &args)?,
            _ => {
                return Err(SolverError::Unsupported(
                    "arithmetic skeleton SAT: non-Boolean term in Boolean skeleton".to_owned(),
                ));
            }
        };
        self.term_lit.insert(term, lit);
        Ok(lit)
    }

    fn encode_app(
        &mut self,
        arena: &TermArena,
        term: TermId,
        op: Op,
        args: &[TermId],
    ) -> Result<BoolCnfLit, SolverError> {
        if arena.sort_of(term) != Sort::Bool {
            return Err(SolverError::Unsupported(
                "arithmetic skeleton SAT: non-Boolean application in skeleton".to_owned(),
            ));
        }
        match op {
            Op::BoolNot => Ok(self.encode(arena, args[0])?.negated()),
            Op::BoolAnd => self.encode_and(arena, args),
            Op::BoolOr => self.encode_or(arena, args),
            Op::BoolImplies => {
                let lhs = self.encode(arena, args[0])?.negated();
                let rhs = self.encode(arena, args[1])?;
                self.encode_or_lits(&[lhs, rhs])
            }
            Op::BoolXor => {
                let lhs = self.encode(arena, args[0])?;
                let rhs = self.encode(arena, args[1])?;
                self.encode_xor_lits(lhs, rhs)
            }
            Op::Eq if arena.sort_of(args[0]) == Sort::Bool => {
                let lhs = self.encode(arena, args[0])?;
                let rhs = self.encode(arena, args[1])?;
                self.encode_iff_lits(lhs, rhs)
            }
            Op::Ite => {
                let condition = self.encode(arena, args[0])?;
                let then_lit = self.encode(arena, args[1])?;
                let else_lit = self.encode(arena, args[2])?;
                self.encode_ite_lits(condition, then_lit, else_lit)
            }
            _ => Err(SolverError::Unsupported(format!(
                "arithmetic skeleton SAT: unsupported Boolean op {op:?}"
            ))),
        }
    }

    fn encode_and(
        &mut self,
        arena: &TermArena,
        args: &[TermId],
    ) -> Result<BoolCnfLit, SolverError> {
        let mut lits = Vec::with_capacity(args.len());
        for &arg in args {
            lits.push(self.encode(arena, arg)?);
        }
        self.encode_and_lits(&lits)
    }

    fn encode_or(&mut self, arena: &TermArena, args: &[TermId]) -> Result<BoolCnfLit, SolverError> {
        let mut lits = Vec::with_capacity(args.len());
        for &arg in args {
            lits.push(self.encode(arena, arg)?);
        }
        self.encode_or_lits(&lits)
    }

    fn encode_and_lits(&mut self, lits: &[BoolCnfLit]) -> Result<BoolCnfLit, SolverError> {
        let mut active = Vec::new();
        for &lit in lits {
            match lit {
                BoolCnfLit::Const(false) => return Ok(BoolCnfLit::Const(false)),
                BoolCnfLit::Const(true) => {}
                BoolCnfLit::Lit(_) => active.push(lit),
            }
        }
        match active.as_slice() {
            [] => Ok(BoolCnfLit::Const(true)),
            [lit] => Ok(*lit),
            _ => {
                let out = self.fresh_lit()?;
                for &lit in &active {
                    self.add_clause(&[out.negated(), lit])?;
                }
                let mut down = Vec::with_capacity(active.len() + 1);
                down.push(out);
                down.extend(active.iter().map(|lit| lit.negated()));
                self.add_clause(&down)?;
                Ok(out)
            }
        }
    }

    fn encode_or_lits(&mut self, lits: &[BoolCnfLit]) -> Result<BoolCnfLit, SolverError> {
        let mut active = Vec::new();
        for &lit in lits {
            match lit {
                BoolCnfLit::Const(true) => return Ok(BoolCnfLit::Const(true)),
                BoolCnfLit::Const(false) => {}
                BoolCnfLit::Lit(_) => active.push(lit),
            }
        }
        match active.as_slice() {
            [] => Ok(BoolCnfLit::Const(false)),
            [lit] => Ok(*lit),
            _ => {
                let out = self.fresh_lit()?;
                for &lit in &active {
                    self.add_clause(&[out, lit.negated()])?;
                }
                let mut down = Vec::with_capacity(active.len() + 1);
                down.push(out.negated());
                down.extend(active.iter().copied());
                self.add_clause(&down)?;
                Ok(out)
            }
        }
    }

    fn encode_xor_lits(
        &mut self,
        lhs: BoolCnfLit,
        rhs: BoolCnfLit,
    ) -> Result<BoolCnfLit, SolverError> {
        match (lhs, rhs) {
            (BoolCnfLit::Const(a), BoolCnfLit::Const(b)) => Ok(BoolCnfLit::Const(a ^ b)),
            (BoolCnfLit::Const(false), lit) | (lit, BoolCnfLit::Const(false)) => Ok(lit),
            (BoolCnfLit::Const(true), lit) | (lit, BoolCnfLit::Const(true)) => Ok(lit.negated()),
            _ if lhs == rhs => Ok(BoolCnfLit::Const(false)),
            _ => {
                let out = self.fresh_lit()?;
                self.add_clause(&[lhs, rhs, out.negated()])?;
                self.add_clause(&[lhs.negated(), rhs.negated(), out.negated()])?;
                self.add_clause(&[lhs, rhs.negated(), out])?;
                self.add_clause(&[lhs.negated(), rhs, out])?;
                Ok(out)
            }
        }
    }

    fn encode_iff_lits(
        &mut self,
        lhs: BoolCnfLit,
        rhs: BoolCnfLit,
    ) -> Result<BoolCnfLit, SolverError> {
        match (lhs, rhs) {
            (BoolCnfLit::Const(a), BoolCnfLit::Const(b)) => Ok(BoolCnfLit::Const(a == b)),
            (BoolCnfLit::Const(true), lit) | (lit, BoolCnfLit::Const(true)) => Ok(lit),
            (BoolCnfLit::Const(false), lit) | (lit, BoolCnfLit::Const(false)) => Ok(lit.negated()),
            _ if lhs == rhs => Ok(BoolCnfLit::Const(true)),
            _ => {
                let out = self.fresh_lit()?;
                self.add_clause(&[lhs, rhs, out])?;
                self.add_clause(&[lhs.negated(), rhs.negated(), out])?;
                self.add_clause(&[lhs, rhs.negated(), out.negated()])?;
                self.add_clause(&[lhs.negated(), rhs, out.negated()])?;
                Ok(out)
            }
        }
    }

    fn encode_ite_lits(
        &mut self,
        condition: BoolCnfLit,
        then_lit: BoolCnfLit,
        else_lit: BoolCnfLit,
    ) -> Result<BoolCnfLit, SolverError> {
        match condition {
            BoolCnfLit::Const(true) => return Ok(then_lit),
            BoolCnfLit::Const(false) => return Ok(else_lit),
            BoolCnfLit::Lit(_) if then_lit == else_lit => return Ok(then_lit),
            _ => {}
        }
        let out = self.fresh_lit()?;
        self.add_clause(&[condition.negated(), then_lit.negated(), out])?;
        self.add_clause(&[condition.negated(), then_lit, out.negated()])?;
        self.add_clause(&[condition, else_lit.negated(), out])?;
        self.add_clause(&[condition, else_lit, out.negated()])?;
        Ok(out)
    }

    fn symbol_var(&mut self, symbol: SymbolId) -> Result<CnfVar, SolverError> {
        if let Some(&var) = self.symbol_var.get(&symbol) {
            return Ok(var);
        }
        let var = self.alloc_var()?;
        self.symbol_var.insert(symbol, var);
        Ok(var)
    }

    fn fresh_lit(&mut self) -> Result<BoolCnfLit, SolverError> {
        Ok(BoolCnfLit::Lit(CnfLit::positive(self.alloc_var()?)))
    }

    fn alloc_var(&mut self) -> Result<CnfVar, SolverError> {
        let var = CnfVar::new(self.next_var)
            .map_err(|error| SolverError::Backend(format!("arithmetic skeleton SAT: {error}")))?;
        self.next_var += 1;
        self.sat
            .reserve(self.next_var)
            .map_err(|error| map_incremental_sat_error(&error))?;
        Ok(var)
    }

    fn add_clause(&mut self, lits: &[BoolCnfLit]) -> Result<(), SolverError> {
        let mut clause = Vec::with_capacity(lits.len());
        for &lit in lits {
            match lit {
                BoolCnfLit::Const(true) => return Ok(()),
                BoolCnfLit::Const(false) => {}
                BoolCnfLit::Lit(lit) => clause.push(lit),
            }
        }
        self.sat
            .add_clause(CnfClause::new(clause))
            .map_err(|error| map_incremental_sat_error(&error))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum BoolCnfLit {
    Const(bool),
    Lit(CnfLit),
}

impl BoolCnfLit {
    fn negated(self) -> Self {
        match self {
            Self::Const(value) => Self::Const(!value),
            Self::Lit(lit) => Self::Lit(lit.negated()),
        }
    }
}

fn map_incremental_sat_error(error: &SatError) -> SolverError {
    SolverError::Backend(format!("arithmetic skeleton SAT failed: {error}"))
}

/// A clause forcing at least one atom in `core` to flip from `truths`. `core`
/// indexes `atoms`/`truths`.
fn block_clause(
    arena: &mut TermArena,
    atoms: &[ArithAtom],
    truths: &[bool],
    core: &[usize],
) -> Result<TermId, SolverError> {
    let mut clause: Option<TermId> = None;
    for &i in core {
        let prop = arena.var(atoms[i].prop);
        let lit = if truths[i] { arena.not(prop)? } else { prop };
        clause = Some(match clause {
            None => lit,
            Some(acc) => arena.or(acc, lit)?,
        });
    }
    clause.ok_or_else(|| SolverError::Backend("arith dpll: empty conflict clause".to_string()))
}

/// Adds cheap theory lemmas for contradictory simple integer bounds before the
/// first SAT solve.
///
/// Generated benchmark families often encode finite branch selectors as
/// disjunctions over `x = 0`, `x = 1`, ... . Integer equality is represented as a
/// pair of order atoms, so the Boolean skeleton alone does not know that
/// `x >= 1` and `x <= 0` are mutually exclusive. Without these clauses the
/// DPLL(T) loop rediscovers those contradictions one SAT model at a time. Each
/// lemma recorded here is just the two-literal theory conflict
/// `{lower-bound, upper-bound}` and is verified by the same certificate checker
/// as dynamically learned conflicts. Only asserted bounds are pre-seeded here;
/// negated/complement bounds are still handled by the dynamic theory loop. This
/// keeps the Boolean skeleton small enough for large scalar abstractions while
/// pruning the common branch-selector conflict pattern.
fn initial_int_bound_mutex_lemmas(
    arena: &mut TermArena,
    ctx: &ArithAbstractor,
) -> Result<Vec<(TermId, Vec<ArithLemmaLiteral>)>, SolverError> {
    let mut bounds = Vec::new();
    for (idx, atom) in ctx.atoms.iter().enumerate() {
        bounds.extend(simple_int_literal_bounds(arena, idx, atom));
    }

    let mut conflicts = Vec::new();
    let mut seen = HashSet::new();
    for i in 0..bounds.len() {
        for j in (i + 1)..bounds.len() {
            let Some((lower, upper)) = conflicting_bounds(&bounds[i], &bounds[j]) else {
                continue;
            };
            if !lower.truth || !upper.truth {
                continue;
            }
            let key = (lower.atom_idx, lower.truth, upper.atom_idx, upper.truth);
            if seen.insert(key) {
                conflicts.push((*lower, *upper));
                if conflicts.len() >= MAX_INITIAL_BOUND_MUTEX_LEMMAS {
                    break;
                }
            }
        }
        if conflicts.len() >= MAX_INITIAL_BOUND_MUTEX_LEMMAS {
            break;
        }
    }

    let mut out = Vec::with_capacity(conflicts.len());
    for (lower, upper) in conflicts {
        let mut truths = vec![false; ctx.atoms.len()];
        truths[lower.atom_idx] = lower.truth;
        truths[upper.atom_idx] = upper.truth;
        let core = [lower.atom_idx, upper.atom_idx];
        let clause = block_clause(arena, &ctx.atoms, &truths, &core)?;
        let lemma = vec![
            static_lemma_literal(arena, &ctx.atoms[lower.atom_idx], lower.truth)?,
            static_lemma_literal(arena, &ctx.atoms[upper.atom_idx], upper.truth)?,
        ];
        out.push((clause, lemma));
    }
    Ok(out)
}

/// Adds adjacent monotonicity lemmas for simple integer bounds before the first
/// SAT solve.
///
/// For a fixed expression, a stronger lower bound implies the next weaker lower
/// bound (`x >= 2 => x >= 1`), and a stronger upper bound implies the next
/// weaker upper bound (`x <= 1 => x <= 2`). The same monotonicity applies to
/// complement literals once they are viewed as bounds (`not (x <= 1)` is
/// `x >= 2`). We seed only adjacent distinct thresholds, so the clause count is
/// linear in the discovered bound ladder rather than quadratic. Each implication
/// is recorded as the unsatisfiable core `{stronger_bound, not weaker_bound}`,
/// so it is checked by the same LIA certificate route as dynamic theory lemmas.
fn initial_int_bound_implication_lemmas(
    arena: &mut TermArena,
    ctx: &ArithAbstractor,
) -> Result<Vec<(TermId, Vec<ArithLemmaLiteral>)>, SolverError> {
    if ctx.atoms.len() > MAX_INITIAL_BOUND_IMPLICATION_ATOMS {
        return Ok(Vec::new());
    }

    let mut groups: BTreeMap<(TermId, BoundSide), Vec<SimpleIntBound>> = BTreeMap::new();
    for (idx, atom) in ctx.atoms.iter().enumerate() {
        for bound in simple_int_literal_bounds(arena, idx, atom) {
            groups
                .entry((bound.expr, bound.side))
                .or_default()
                .push(bound);
        }
    }

    let mut implications = Vec::new();
    let mut seen = HashSet::new();
    for ((_expr, side), mut bounds) in groups {
        bounds.sort_by_key(|bound| (bound.value, bound.atom_idx, bound.truth));
        let mut distinct = Vec::new();
        for bound in bounds {
            if distinct
                .last()
                .is_none_or(|previous: &SimpleIntBound| previous.value != bound.value)
            {
                distinct.push(bound);
            }
        }

        for pair in distinct.windows(2) {
            let (stronger, weaker) = match side {
                BoundSide::Lower => (pair[1], pair[0]),
                BoundSide::Upper => (pair[0], pair[1]),
            };
            if stronger.atom_idx == weaker.atom_idx {
                continue;
            }
            let key = (
                stronger.atom_idx,
                stronger.truth,
                weaker.atom_idx,
                weaker.truth,
            );
            if seen.insert(key) {
                implications.push((stronger, weaker));
                if implications.len() >= MAX_INITIAL_BOUND_IMPLICATION_LEMMAS {
                    break;
                }
            }
        }
        if implications.len() >= MAX_INITIAL_BOUND_IMPLICATION_LEMMAS {
            break;
        }
    }

    let mut out = Vec::with_capacity(implications.len());
    for (stronger, weaker) in implications {
        let mut truths = vec![false; ctx.atoms.len()];
        truths[stronger.atom_idx] = stronger.truth;
        truths[weaker.atom_idx] = !weaker.truth;
        let core = [stronger.atom_idx, weaker.atom_idx];
        let clause = block_clause(arena, &ctx.atoms, &truths, &core)?;
        let lemma = vec![
            static_lemma_literal(arena, &ctx.atoms[stronger.atom_idx], stronger.truth)?,
            static_lemma_literal(arena, &ctx.atoms[weaker.atom_idx], !weaker.truth)?,
        ];
        out.push((clause, lemma));
    }
    Ok(out)
}

fn static_lemma_literal(
    arena: &mut TermArena,
    atom: &ArithAtom,
    truth: bool,
) -> Result<ArithLemmaLiteral, SolverError> {
    let literal = if truth {
        atom.term
    } else {
        arena
            .not(atom.term)
            .map_err(|e| SolverError::Backend(format!("arith bound lemma build failed: {e}")))?
    };
    Ok(ArithLemmaLiteral {
        prop: atom.prop,
        truth,
        literal,
        theory: atom.theory,
    })
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum BoundSide {
    Lower,
    Upper,
}

#[derive(Clone, Copy)]
struct SimpleIntBound {
    atom_idx: usize,
    expr: TermId,
    value: i128,
    side: BoundSide,
    truth: bool,
}

fn simple_int_literal_bounds(
    arena: &TermArena,
    atom_idx: usize,
    atom: &ArithAtom,
) -> Vec<SimpleIntBound> {
    if atom.theory != Theory::Int {
        return Vec::new();
    }
    let TermNode::App { op, args } = arena.node(atom.term) else {
        return Vec::new();
    };
    let strict = match op {
        Op::IntLt => true,
        Op::IntLe => false,
        _ => return Vec::new(),
    };
    let left_const = int_const_value(arena, args[0]);
    let right_const = int_const_value(arena, args[1]);
    match (left_const, right_const) {
        (None, Some(c)) => bounds_for_expr_le_const(atom_idx, args[0], c, strict),
        (Some(c), None) => bounds_for_const_le_expr(atom_idx, args[1], c, strict),
        _ => Vec::new(),
    }
}

fn bounds_for_expr_le_const(
    atom_idx: usize,
    expr: TermId,
    c: i128,
    strict: bool,
) -> Vec<SimpleIntBound> {
    let Some(true_upper) = (if strict { c.checked_sub(1) } else { Some(c) }) else {
        return Vec::new();
    };
    let Some(false_lower) = (if strict { Some(c) } else { c.checked_add(1) }) else {
        return Vec::new();
    };
    vec![
        SimpleIntBound {
            atom_idx,
            expr,
            value: true_upper,
            side: BoundSide::Upper,
            truth: true,
        },
        SimpleIntBound {
            atom_idx,
            expr,
            value: false_lower,
            side: BoundSide::Lower,
            truth: false,
        },
    ]
}

fn bounds_for_const_le_expr(
    atom_idx: usize,
    expr: TermId,
    c: i128,
    strict: bool,
) -> Vec<SimpleIntBound> {
    let Some(true_lower) = (if strict { c.checked_add(1) } else { Some(c) }) else {
        return Vec::new();
    };
    let Some(false_upper) = (if strict { Some(c) } else { c.checked_sub(1) }) else {
        return Vec::new();
    };
    vec![
        SimpleIntBound {
            atom_idx,
            expr,
            value: true_lower,
            side: BoundSide::Lower,
            truth: true,
        },
        SimpleIntBound {
            atom_idx,
            expr,
            value: false_upper,
            side: BoundSide::Upper,
            truth: false,
        },
    ]
}

fn int_const_value(arena: &TermArena, term: TermId) -> Option<i128> {
    match arena.node(term) {
        TermNode::IntConst(value) => Some(*value),
        _ => None,
    }
}

fn conflicting_bounds<'a>(
    a: &'a SimpleIntBound,
    b: &'a SimpleIntBound,
) -> Option<(&'a SimpleIntBound, &'a SimpleIntBound)> {
    if a.expr != b.expr || a.side == b.side {
        return None;
    }
    if a.atom_idx == b.atom_idx && a.truth != b.truth {
        return None;
    }
    let (lower, upper) = if a.side == BoundSide::Lower {
        (a, b)
    } else {
        (b, a)
    };
    (lower.value > upper.value).then_some((lower, upper))
}

/// One abstracted arithmetic order atom: its fresh proposition, the atom term,
/// and which theory decides it.
struct ArithAtom {
    prop: SymbolId,
    term: TermId,
    theory: Theory,
}

/// Abstracts Boolean structure over linear-arithmetic atoms into a propositional
/// skeleton.
#[derive(Default)]
struct ArithAbstractor {
    atom_of: HashMap<TermId, SymbolId>,
    props: HashSet<SymbolId>,
    atoms: Vec<ArithAtom>,
    fresh_counter: usize,
}

impl ArithAbstractor {
    fn is_atom_prop(&self, symbol: SymbolId) -> bool {
        self.props.contains(&symbol)
    }

    fn abstract_term(
        &mut self,
        arena: &mut TermArena,
        term: TermId,
    ) -> Result<TermId, SolverError> {
        let node = arena.node(term).clone();
        match node {
            TermNode::BoolConst(_) => Ok(term),
            TermNode::Symbol(_) if arena.sort_of(term) == Sort::Bool => Ok(term),
            TermNode::App { op, args } => match op {
                Op::BoolNot => self.abstract_negation(arena, args[0]),
                Op::BoolAnd => self.abstract_and(arena, &args),
                Op::BoolOr => self.abstract_or(arena, &args),
                Op::BoolXor => self.abstract_xor(arena, &args),
                Op::BoolImplies => self.abstract_implies(arena, &args),
                Op::Eq if args[0] == args[1] => Ok(arena.bool_const(true)),
                Op::Eq if arena.sort_of(args[0]) == Sort::Bool => {
                    self.abstract_bool_eq(arena, &args)
                }
                Op::Ite if arena.sort_of(term) == Sort::Bool => {
                    let c = self.abstract_term(arena, args[0])?;
                    if let Some(value) = bool_const_value(arena, c) {
                        return self.abstract_term(arena, args[if value { 1 } else { 2 }]);
                    }
                    let t = self.abstract_term(arena, args[1])?;
                    let e = self.abstract_term(arena, args[2])?;
                    if t == e {
                        return Ok(t);
                    }
                    match (bool_const_value(arena, t), bool_const_value(arena, e)) {
                        (Some(true), Some(false)) => Ok(c),
                        (Some(false), Some(true)) => Self::negate_abstracted(arena, c),
                        _ => Ok(arena.ite(c, t, e)?),
                    }
                }
                Op::IntLt | Op::IntLe | Op::IntGt | Op::IntGe => {
                    self.order_atom(arena, term, op, &args, Theory::Int)
                }
                Op::RealLt | Op::RealLe | Op::RealGt | Op::RealGe => {
                    self.order_atom(arena, term, op, &args, Theory::Real)
                }
                Op::Eq if arena.sort_of(args[0]) == Sort::Int => {
                    let le = arena.int_le(args[0], args[1])?;
                    let ge = arena.int_ge(args[0], args[1])?;
                    let le_prop = self.abstract_term(arena, le)?;
                    let ge_prop = self.abstract_term(arena, ge)?;
                    Ok(arena.and(le_prop, ge_prop)?)
                }
                Op::Eq if arena.sort_of(args[0]) == Sort::Real => {
                    let le = arena.real_le(args[0], args[1])?;
                    let ge = arena.real_ge(args[0], args[1])?;
                    let le_prop = self.abstract_term(arena, le)?;
                    let ge_prop = self.abstract_term(arena, ge)?;
                    Ok(arena.and(le_prop, ge_prop)?)
                }
                _ => Err(SolverError::Unsupported(
                    "lazy arithmetic: assertion is not Boolean structure over linear-arithmetic \
                     atoms"
                        .to_owned(),
                )),
            },
            _ => Err(SolverError::Unsupported(
                "lazy arithmetic: non-Boolean, non-arithmetic-atom term in a Boolean position"
                    .to_owned(),
            )),
        }
    }

    fn abstract_and(
        &mut self,
        arena: &mut TermArena,
        args: &[TermId],
    ) -> Result<TermId, SolverError> {
        let mut terms = Vec::with_capacity(args.len());
        for &arg in args {
            let term = self.abstract_term(arena, arg)?;
            if matches!(bool_const_value(arena, term), Some(false)) {
                return Ok(term);
            }
            terms.push(term);
        }
        simplify_bool_and(arena, terms)
    }

    fn abstract_or(
        &mut self,
        arena: &mut TermArena,
        args: &[TermId],
    ) -> Result<TermId, SolverError> {
        let mut terms = Vec::with_capacity(args.len());
        for &arg in args {
            let term = self.abstract_term(arena, arg)?;
            if matches!(bool_const_value(arena, term), Some(true)) {
                return Ok(term);
            }
            terms.push(term);
        }
        simplify_bool_or(arena, terms)
    }

    fn abstract_xor(
        &mut self,
        arena: &mut TermArena,
        args: &[TermId],
    ) -> Result<TermId, SolverError> {
        let a = self.abstract_term(arena, args[0])?;
        let b = self.abstract_term(arena, args[1])?;
        match (bool_const_value(arena, a), bool_const_value(arena, b)) {
            (Some(x), Some(y)) => Ok(arena.bool_const(x ^ y)),
            (Some(false), _) => Ok(b),
            (_, Some(false)) => Ok(a),
            (Some(true), _) => Self::negate_abstracted(arena, b),
            (_, Some(true)) => Self::negate_abstracted(arena, a),
            _ if a == b => Ok(arena.bool_const(false)),
            _ => Ok(arena.xor(a, b)?),
        }
    }

    fn abstract_implies(
        &mut self,
        arena: &mut TermArena,
        args: &[TermId],
    ) -> Result<TermId, SolverError> {
        let a = self.abstract_term(arena, args[0])?;
        match bool_const_value(arena, a) {
            Some(false) => return Ok(arena.bool_const(true)),
            Some(true) => return self.abstract_term(arena, args[1]),
            None => {}
        }
        let b = self.abstract_term(arena, args[1])?;
        match bool_const_value(arena, b) {
            Some(true) => Ok(arena.bool_const(true)),
            Some(false) => Self::negate_abstracted(arena, a),
            None if a == b => Ok(arena.bool_const(true)),
            None => Ok(arena.implies(a, b)?),
        }
    }

    fn abstract_bool_eq(
        &mut self,
        arena: &mut TermArena,
        args: &[TermId],
    ) -> Result<TermId, SolverError> {
        let a = self.abstract_term(arena, args[0])?;
        let b = self.abstract_term(arena, args[1])?;
        match (bool_const_value(arena, a), bool_const_value(arena, b)) {
            (Some(x), Some(y)) => Ok(arena.bool_const(x == y)),
            (Some(true), _) => Ok(b),
            (_, Some(true)) => Ok(a),
            (Some(false), _) => Self::negate_abstracted(arena, b),
            (_, Some(false)) => Self::negate_abstracted(arena, a),
            _ if a == b => Ok(arena.bool_const(true)),
            _ => Ok(arena.eq(a, b)?),
        }
    }

    fn negate_abstracted(arena: &mut TermArena, term: TermId) -> Result<TermId, SolverError> {
        if let Some(value) = bool_const_value(arena, term) {
            return Ok(arena.bool_const(!value));
        }
        if let Some(inner) = bool_not_child(arena, term) {
            return Ok(inner);
        }
        Ok(arena.not(term)?)
    }

    fn abstract_negation(
        &mut self,
        arena: &mut TermArena,
        inner: TermId,
    ) -> Result<TermId, SolverError> {
        let node = arena.node(inner).clone();
        match node {
            TermNode::BoolConst(value) => Ok(arena.bool_const(!value)),
            TermNode::App { op, args } => match op {
                Op::Eq if args[0] == args[1] => Ok(arena.bool_const(false)),
                _ => {
                    let a = self.abstract_term(arena, inner)?;
                    Self::negate_abstracted(arena, a)
                }
            },
            _ => {
                let a = self.abstract_term(arena, inner)?;
                Self::negate_abstracted(arena, a)
            }
        }
    }

    fn order_atom(
        &mut self,
        arena: &mut TermArena,
        term: TermId,
        op: Op,
        args: &[TermId],
        theory: Theory,
    ) -> Result<TermId, SolverError> {
        if args[0] == args[1] {
            return Ok(arena.bool_const(matches!(
                op,
                Op::IntLe | Op::IntGe | Op::RealLe | Op::RealGe
            )));
        }
        let (canonical, polarity) = match op {
            Op::IntLe | Op::RealLe => (term, true),
            Op::IntGe => (arena.int_le(args[1], args[0])?, true),
            Op::IntLt => (arena.int_le(args[1], args[0])?, false),
            Op::IntGt => (arena.int_le(args[0], args[1])?, false),
            Op::RealGe => (arena.real_le(args[1], args[0])?, true),
            Op::RealLt => (arena.real_le(args[1], args[0])?, false),
            Op::RealGt => (arena.real_le(args[0], args[1])?, false),
            _ => unreachable!("order_atom called only for arithmetic order atoms"),
        };
        Self::ensure_supported_atom(arena, canonical, theory)?;
        let prop = self.atom(arena, canonical, theory);
        let prop_term = arena.var(prop);
        if polarity {
            Ok(prop_term)
        } else {
            Self::negate_abstracted(arena, prop_term)
        }
    }

    fn ensure_supported_atom(
        arena: &TermArena,
        atom: TermId,
        theory: Theory,
    ) -> Result<(), SolverError> {
        let result = match theory {
            Theory::Int => check_with_lia_opaque_apps(arena, &[atom]),
            Theory::Real => check_with_lra(arena, &[atom]),
        };
        match result {
            Ok(_) => Ok(()),
            Err(SolverError::Unsupported(detail)) => Err(SolverError::Unsupported(format!(
                "lazy arithmetic: unsupported arithmetic atom: {detail}"
            ))),
            Err(error) => Err(error),
        }
    }

    fn atom(&mut self, arena: &mut TermArena, term: TermId, theory: Theory) -> SymbolId {
        if let Some(&prop) = self.atom_of.get(&term) {
            return prop;
        }
        let name = format!("{ATOM_PREFIX}{}", self.fresh_counter);
        self.fresh_counter += 1;
        let prop = arena
            .declare(&name, Sort::Bool)
            .expect("fresh Boolean proposition declares");
        self.atom_of.insert(term, prop);
        self.props.insert(prop);
        self.atoms.push(ArithAtom { prop, term, theory });
        prop
    }

    fn has_opaque_int_apps(&self, arena: &TermArena) -> bool {
        self.atoms.iter().any(|atom| {
            atom.theory == Theory::Int
                && contains_int_uf_application(arena, atom.term, &mut HashSet::new())
        })
    }
}

fn bool_const_value(arena: &TermArena, term: TermId) -> Option<bool> {
    match arena.node(term) {
        TermNode::BoolConst(value) => Some(*value),
        _ => None,
    }
}

fn simplify_bool_and(arena: &mut TermArena, terms: Vec<TermId>) -> Result<TermId, SolverError> {
    let mut flat = Vec::new();
    for term in terms {
        flatten_bool_and(arena, term, &mut flat);
    }

    let mut active = Vec::new();
    for term in flat {
        match bool_const_value(arena, term) {
            Some(false) => return Ok(arena.bool_const(false)),
            Some(true) => continue,
            None => {}
        }
        if active.contains(&term) {
            continue;
        }
        if active
            .iter()
            .any(|&existing| bool_terms_are_complements(arena, existing, term))
        {
            return Ok(arena.bool_const(false));
        }
        active.push(term);
    }
    if bool_and_is_contradiction(arena, &active) {
        return Ok(arena.bool_const(false));
    }
    rebuild_bool_and(arena, active)
}

fn simplify_bool_or(arena: &mut TermArena, terms: Vec<TermId>) -> Result<TermId, SolverError> {
    let mut flat = Vec::new();
    for term in terms {
        flatten_bool_or(arena, term, &mut flat);
    }

    let mut active = Vec::new();
    for term in flat {
        match bool_const_value(arena, term) {
            Some(true) => return Ok(arena.bool_const(true)),
            Some(false) => continue,
            None => {}
        }
        if active.contains(&term) {
            continue;
        }
        if active
            .iter()
            .any(|&existing| bool_terms_are_complements(arena, existing, term))
        {
            return Ok(arena.bool_const(true));
        }
        active.push(term);
    }
    if bool_or_is_tautology(arena, &active) {
        return Ok(arena.bool_const(true));
    }
    rebuild_bool_or(arena, active)
}

fn flatten_bool_and(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    if let TermNode::App {
        op: Op::BoolAnd,
        args,
    } = arena.node(term)
    {
        for &arg in args {
            flatten_bool_and(arena, arg, out);
        }
    } else {
        out.push(term);
    }
}

fn flatten_bool_or(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    if let TermNode::App {
        op: Op::BoolOr,
        args,
    } = arena.node(term)
    {
        for &arg in args {
            flatten_bool_or(arena, arg, out);
        }
    } else {
        out.push(term);
    }
}

fn bool_not_child(arena: &TermArena, term: TermId) -> Option<TermId> {
    let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    Some(args[0])
}

fn bool_terms_are_complements(arena: &TermArena, a: TermId, b: TermId) -> bool {
    bool_not_child(arena, a) == Some(b) || bool_not_child(arena, b) == Some(a)
}

fn bool_or_is_tautology(arena: &TermArena, terms: &[TermId]) -> bool {
    for &term in terms {
        if let Some(inner) = bool_not_child(arena, term) {
            let mut and_children = Vec::new();
            flatten_bool_and(arena, inner, &mut and_children);
            if and_children.len() > 1 && and_children.iter().any(|child| terms.contains(child)) {
                return true;
            }

            let mut or_children = Vec::new();
            flatten_bool_or(arena, inner, &mut or_children);
            if or_children.len() > 1 && or_children.iter().all(|child| terms.contains(child)) {
                return true;
            }
        } else {
            let mut and_children = Vec::new();
            flatten_bool_and(arena, term, &mut and_children);
            if and_children.len() > 1
                && and_children.iter().all(|&child| {
                    terms
                        .iter()
                        .any(|&t| bool_terms_are_complements(arena, t, child))
                })
            {
                return true;
            }
        }
    }
    false
}

fn bool_and_is_contradiction(arena: &TermArena, terms: &[TermId]) -> bool {
    for &term in terms {
        if let Some(inner) = bool_not_child(arena, term) {
            let mut or_children = Vec::new();
            flatten_bool_or(arena, inner, &mut or_children);
            if or_children.len() > 1 && or_children.iter().any(|child| terms.contains(child)) {
                return true;
            }

            let mut and_children = Vec::new();
            flatten_bool_and(arena, inner, &mut and_children);
            if and_children.len() > 1 && and_children.iter().all(|child| terms.contains(child)) {
                return true;
            }
        } else {
            let mut or_children = Vec::new();
            flatten_bool_or(arena, term, &mut or_children);
            if or_children.len() > 1
                && or_children.iter().all(|&child| {
                    terms
                        .iter()
                        .any(|&t| bool_terms_are_complements(arena, t, child))
                })
            {
                return true;
            }
        }
    }
    false
}

fn rebuild_bool_and(arena: &mut TermArena, terms: Vec<TermId>) -> Result<TermId, SolverError> {
    let mut iter = terms.into_iter();
    let Some(mut acc) = iter.next() else {
        return Ok(arena.bool_const(true));
    };
    for term in iter {
        acc = arena.and(acc, term)?;
    }
    Ok(acc)
}

fn rebuild_bool_or(arena: &mut TermArena, terms: Vec<TermId>) -> Result<TermId, SolverError> {
    let mut iter = terms.into_iter();
    let Some(mut acc) = iter.next() else {
        return Ok(arena.bool_const(false));
    };
    for term in iter {
        acc = arena.or(acc, term)?;
    }
    Ok(acc)
}

fn contains_int_uf_application(
    arena: &TermArena,
    term: TermId,
    seen: &mut HashSet<TermId>,
) -> bool {
    if !seen.insert(term) {
        return false;
    }
    let TermNode::App { op, args } = arena.node(term) else {
        return false;
    };
    if matches!(op, Op::Apply(_)) && arena.sort_of(term) == Sort::Int {
        return true;
    }
    args.iter()
        .any(|&arg| contains_int_uf_application(arena, arg, seen))
}

fn contains_smtlib_unspecified_arith(arena: &TermArena, assertions: &[TermId]) -> bool {
    let mut seen = HashSet::new();
    let mut stack = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            match op {
                Op::IntDiv | Op::IntMod
                    if args
                        .get(1)
                        .is_none_or(|&divisor| !is_known_nonzero_int(arena, divisor)) =>
                {
                    return true;
                }
                Op::RealDiv
                    if args
                        .get(1)
                        .is_none_or(|&divisor| !is_known_nonzero_real(arena, divisor)) =>
                {
                    return true;
                }
                _ => {}
            }
            stack.extend(args.iter().copied());
        }
    }
    false
}

fn is_known_nonzero_int(arena: &TermArena, term: TermId) -> bool {
    matches!(arena.node(term), TermNode::IntConst(value) if *value != 0)
}

fn is_known_nonzero_real(arena: &TermArena, term: TermId) -> bool {
    matches!(arena.node(term), TermNode::RealConst(value) if !value.is_zero())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn abstractor_reuses_reversed_order_atoms() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let y = arena.declare("y", Sort::Int).unwrap();
        let xv = arena.var(x);
        let yv = arena.var(y);
        let x_ge_y = arena.int_ge(xv, yv).unwrap();
        let y_le_x = arena.int_le(yv, xv).unwrap();
        let both = arena.and(x_ge_y, y_le_x).unwrap();

        let mut ctx = ArithAbstractor::default();
        let _ = ctx.abstract_term(&mut arena, both).unwrap();
        assert_eq!(
            ctx.atoms.len(),
            1,
            "x >= y and y <= x must share one canonical arithmetic atom"
        );
    }

    #[test]
    fn abstractor_folds_self_order_atoms_and_equalities() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let xv = arena.var(x);
        let x_lt_x = arena.int_lt(xv, xv).unwrap();
        let x_eq_x = arena.eq(xv, xv).unwrap();

        let mut ctx = ArithAbstractor::default();
        let lt = ctx.abstract_term(&mut arena, x_lt_x).unwrap();
        let eq = ctx.abstract_term(&mut arena, x_eq_x).unwrap();
        assert!(matches!(arena.node(lt), TermNode::BoolConst(false)));
        assert!(matches!(arena.node(eq), TermNode::BoolConst(true)));
        assert!(
            ctx.atoms.is_empty(),
            "trivial self-comparisons/equalities should not allocate arithmetic atoms"
        );
    }

    #[test]
    fn abstractor_reuses_negated_order_atoms() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let y = arena.declare("y", Sort::Int).unwrap();
        let xv = arena.var(x);
        let yv = arena.var(y);
        let x_lt_y = arena.int_lt(xv, yv).unwrap();
        let not_x_lt_y = arena.not(x_lt_y).unwrap();
        let y_le_x = arena.int_le(yv, xv).unwrap();
        let both = arena.and(not_x_lt_y, y_le_x).unwrap();

        let mut ctx = ArithAbstractor::default();
        let _ = ctx.abstract_term(&mut arena, both).unwrap();
        assert_eq!(
            ctx.atoms.len(),
            1,
            "not (x < y) and y <= x must share one canonical arithmetic atom"
        );
    }

    #[test]
    fn abstractor_collapses_order_complements_to_boolean_negations() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let xv = arena.var(x);
        let zero = arena.int_const(0);
        let x_le_zero = arena.int_le(xv, zero).unwrap();
        let not_x_le_zero = arena.not(x_le_zero).unwrap();
        let both = arena.and(x_le_zero, not_x_le_zero).unwrap();

        let mut ctx = ArithAbstractor::default();
        let folded = ctx.abstract_term(&mut arena, both).unwrap();
        assert!(matches!(arena.node(folded), TermNode::BoolConst(false)));
        assert_eq!(
            ctx.atoms.len(),
            1,
            "an order atom and its negation should share one Boolean proposition"
        );
    }

    #[test]
    fn abstractor_folds_generated_boolean_definition_tautologies() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let xv = arena.var(x);
        let zero = arena.int_const(0);
        let x_le_zero = arena.int_le(xv, zero).unwrap();
        let x_ge_zero = arena.int_ge(xv, zero).unwrap();
        let equality_pair = arena.and(x_le_zero, x_ge_zero).unwrap();
        let not_pair = arena.not(equality_pair).unwrap();
        let pair_implies_le = arena.or(not_pair, x_le_zero).unwrap();

        let mut ctx = ArithAbstractor::default();
        let folded = ctx.abstract_term(&mut arena, pair_implies_le).unwrap();
        assert!(matches!(arena.node(folded), TermNode::BoolConst(true)));

        let not_le = arena.not(x_le_zero).unwrap();
        let not_ge = arena.not(x_ge_zero).unwrap();
        let not_le_or_not_ge = arena.or(not_le, not_ge).unwrap();
        let reverse_definition = arena.or(not_le_or_not_ge, equality_pair).unwrap();
        let folded = ctx.abstract_term(&mut arena, reverse_definition).unwrap();
        assert!(matches!(arena.node(folded), TermNode::BoolConst(true)));
        assert_eq!(
            ctx.atoms.len(),
            2,
            "the equality-pair tautologies should allocate only the two real bounds"
        );
    }

    #[test]
    fn abstractor_short_circuits_boolean_constants() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let y = arena.declare("y", Sort::Int).unwrap();
        let xv = arena.var(x);
        let yv = arena.var(y);
        let expensive = arena.int_lt(xv, yv).unwrap();
        let false_term = arena.bool_const(false);
        let dead_and = arena.and(false_term, expensive).unwrap();

        let mut ctx = ArithAbstractor::default();
        let folded = ctx.abstract_term(&mut arena, dead_and).unwrap();
        assert!(matches!(arena.node(folded), TermNode::BoolConst(false)));
        assert!(
            ctx.atoms.is_empty(),
            "a dead Boolean branch must not allocate arithmetic atoms"
        );
    }

    #[test]
    fn abstractor_rejects_unsupported_integer_mod_atom() {
        let mut arena = TermArena::new();
        let zero = arena.int_const(0);
        let large = arena.int_const(775);
        let modulo = arena.int_mod(zero, zero).unwrap();
        let atom = arena.int_lt(large, modulo).unwrap();

        let mut ctx = ArithAbstractor::default();
        let err = ctx
            .abstract_term(&mut arena, atom)
            .expect_err("mod-by-zero atom is outside linear arithmetic");
        assert!(
            matches!(err, SolverError::Unsupported(_)),
            "expected unsupported arithmetic atom, got {err:?}"
        );
        assert!(
            ctx.atoms.is_empty(),
            "unsupported arithmetic atoms must not enter the Boolean skeleton"
        );
    }

    #[test]
    fn upfront_integer_bound_mutex_lemmas_are_certified() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let xv = arena.var(x);
        let zero = arena.int_const(0);
        let one = arena.int_const(1);
        let x_eq_zero = arena.eq(xv, zero).unwrap();
        let x_eq_one = arena.eq(xv, one).unwrap();
        let both = arena.and(x_eq_zero, x_eq_one).unwrap();

        let run = run_arith_dpll(&mut arena, &[both], &SolverConfig::default()).unwrap();
        assert!(matches!(run.result, CheckResult::Unsat));
        assert!(
            !run.lemmas.is_empty(),
            "distinct integer equalities should produce an upfront bound-conflict lemma"
        );
        let refutation = ArithDpllRefutation {
            skeleton: run.skeleton,
            lemmas: run.lemmas,
        };
        assert!(
            refutation.verify(&arena).unwrap(),
            "upfront bound lemmas must be checkable by the normal verifier"
        );
    }

    #[test]
    fn upfront_integer_bound_implication_lemmas_are_certified() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let xv = arena.var(x);
        let zero = arena.int_const(0);
        let one = arena.int_const(1);
        let x_le_zero = arena.int_le(xv, zero).unwrap();
        let x_le_one = arena.int_le(xv, one).unwrap();
        let either = arena.or(x_le_zero, x_le_one).unwrap();

        let mut ctx = ArithAbstractor::default();
        let _ = ctx.abstract_term(&mut arena, either).unwrap();
        let x_le_zero_idx = ctx
            .atoms
            .iter()
            .position(|atom| atom.term == x_le_zero)
            .unwrap();
        let x_le_one_idx = ctx
            .atoms
            .iter()
            .position(|atom| atom.term == x_le_one)
            .unwrap();

        let lemmas = initial_int_bound_implication_lemmas(&mut arena, &ctx).unwrap();
        let expected_core = lemmas
            .iter()
            .map(|(_, lemma)| lemma)
            .find(|lemma| {
                lemma.iter().any(|lit| {
                    lit.prop == ctx.atoms[x_le_zero_idx].prop
                        && lit.truth
                        && lit.literal == x_le_zero
                }) && lemma.iter().any(|lit| {
                    lit.prop == ctx.atoms[x_le_one_idx].prop
                        && !lit.truth
                        && matches!(
                            arena.node(lit.literal),
                            TermNode::App { op: Op::BoolNot, args }
                                if args[0] == x_le_one
                        )
                })
            })
            .expect("x <= 0 should imply x <= 1");

        let core_lits = expected_core
            .iter()
            .map(|literal| literal.literal)
            .collect::<Vec<_>>();
        assert!(matches!(
            check_with_lia_simplex(&arena, &core_lits).unwrap(),
            CheckResult::Unsat
        ));
    }

    #[test]
    fn upfront_integer_bound_complement_implication_lemmas_are_certified() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let xv = arena.var(x);
        let zero = arena.int_const(0);
        let one = arena.int_const(1);
        let x_le_zero = arena.int_le(xv, zero).unwrap();
        let x_le_one = arena.int_le(xv, one).unwrap();
        let either = arena.or(x_le_zero, x_le_one).unwrap();

        let mut ctx = ArithAbstractor::default();
        let _ = ctx.abstract_term(&mut arena, either).unwrap();
        let x_le_zero_idx = ctx
            .atoms
            .iter()
            .position(|atom| atom.term == x_le_zero)
            .unwrap();
        let x_le_one_idx = ctx
            .atoms
            .iter()
            .position(|atom| atom.term == x_le_one)
            .unwrap();

        let lemmas = initial_int_bound_implication_lemmas(&mut arena, &ctx).unwrap();
        let expected_core = lemmas
            .iter()
            .map(|(_, lemma)| lemma)
            .find(|lemma| {
                lemma.iter().any(|lit| {
                    lit.prop == ctx.atoms[x_le_one_idx].prop
                        && !lit.truth
                        && matches!(
                            arena.node(lit.literal),
                            TermNode::App { op: Op::BoolNot, args }
                                if args[0] == x_le_one
                        )
                }) && lemma.iter().any(|lit| {
                    lit.prop == ctx.atoms[x_le_zero_idx].prop
                        && lit.truth
                        && lit.literal == x_le_zero
                })
            })
            .expect("not (x <= 1) should imply not (x <= 0)");

        let core_lits = expected_core
            .iter()
            .map(|literal| literal.literal)
            .collect::<Vec<_>>();
        assert!(matches!(
            check_with_lia_simplex(&arena, &core_lits).unwrap(),
            CheckResult::Unsat
        ));
    }

    #[test]
    fn justified_support_ignores_dead_or_branch_conflict() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let xv = arena.var(x);
        let zero = arena.int_const(0);
        let one = arena.int_const(1);
        let two = arena.int_const(2);
        let x_le_zero = arena.int_le(xv, zero).unwrap();
        let x_ge_two = arena.int_ge(xv, two).unwrap();
        let x_le_one = arena.int_le(xv, one).unwrap();
        let dead_conflict = arena.and(x_ge_two, x_le_one).unwrap();
        let assertion = arena.or(x_le_zero, dead_conflict).unwrap();

        let mut ctx = ArithAbstractor::default();
        let skeleton = vec![ctx.abstract_term(&mut arena, assertion).unwrap()];
        let mut propositional = Model::new();
        for atom in &ctx.atoms {
            propositional.set(atom.prop, Value::Bool(true));
        }

        let support = justified_theory_indices(&arena, &ctx, &skeleton, &propositional).unwrap();
        let x_le_zero_idx = ctx
            .atoms
            .iter()
            .position(|atom| atom.term == x_le_zero)
            .unwrap();
        assert_eq!(support, vec![x_le_zero_idx]);

        let lits = ctx.atoms.iter().map(|atom| atom.term).collect::<Vec<_>>();
        let all = (0..ctx.atoms.len()).collect::<Vec<_>>();
        assert!(
            !theory_conflicts_for_indices(
                &arena,
                &ctx,
                &lits,
                &all,
                Theory::Int,
                check_with_lia_opaque_apps,
            )
            .unwrap()
            .is_empty(),
            "the full arbitrary SAT assignment is theory-inconsistent"
        );
        assert!(
            theory_conflicts_for_indices(
                &arena,
                &ctx,
                &lits,
                &support,
                Theory::Int,
                check_with_lia_opaque_apps,
            )
            .unwrap()
            .is_empty(),
            "the Boolean justification branch is theory-consistent"
        );
        assert!(matches!(
            try_finish_sat(
                &mut arena,
                &[assertion],
                &ctx,
                &propositional,
                &lits,
                &support,
            )
            .unwrap(),
            Some(CheckResult::Sat(_))
        ));
    }

    #[test]
    fn lia_budget_unknown_reports_support_stats() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let xv = arena.var(x);
        let zero = arena.int_const(0);
        let ge = arena.int_ge(xv, zero).unwrap();
        let config = SolverConfig::default().with_timeout(Duration::ZERO);

        let run = run_arith_dpll(&mut arena, &[ge], &config).unwrap();
        let CheckResult::Unknown(reason) = run.result else {
            panic!("expected a timeout unknown");
        };
        assert!(reason.detail.contains("support_attempts=0"));
        assert!(reason.detail.contains("full_fallbacks=0"));
    }

    #[test]
    fn cheap_integer_bound_core_uses_current_literal_polarity() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let xv = arena.var(x);
        let zero = arena.int_const(0);
        let one = arena.int_const(1);
        let x_le_zero = arena.int_le(xv, zero).unwrap();
        let x_le_one = arena.int_le(xv, one).unwrap();
        let both_atoms = arena.and(x_le_zero, x_le_one).unwrap();

        let mut ctx = ArithAbstractor::default();
        let _ = ctx.abstract_term(&mut arena, both_atoms).unwrap();
        let upper_zero_idx = ctx
            .atoms
            .iter()
            .position(|atom| atom.term == x_le_zero)
            .unwrap();
        let upper_one_idx = ctx
            .atoms
            .iter()
            .position(|atom| atom.term == x_le_one)
            .unwrap();
        let upper_one_term = ctx.atoms[upper_one_idx].term;
        let not_x_le_one = arena.not(upper_one_term).unwrap();
        let mut lits: Vec<TermId> = ctx.atoms.iter().map(|atom| atom.term).collect();
        lits[upper_one_idx] = not_x_le_one;

        let indices = vec![upper_zero_idx, upper_one_idx];
        let mut core = cheap_int_bound_conflict_cores(&arena, &ctx, &lits, &indices)
            .into_iter()
            .next()
            .unwrap();
        core.sort_unstable();
        let mut expected = indices;
        expected.sort_unstable();
        assert_eq!(core, expected);

        let core_lits = core.iter().map(|&idx| lits[idx]).collect::<Vec<_>>();
        assert!(matches!(
            check_with_lia_simplex(&arena, &core_lits).unwrap(),
            CheckResult::Unsat
        ));
    }

    #[test]
    fn cheap_integer_bound_cores_batch_independent_conflicts() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let y = arena.declare("y", Sort::Int).unwrap();
        let xv = arena.var(x);
        let yv = arena.var(y);
        let zero = arena.int_const(0);
        let one = arena.int_const(1);
        let x_le_zero = arena.int_le(xv, zero).unwrap();
        let x_le_one = arena.int_le(xv, one).unwrap();
        let y_le_zero = arena.int_le(yv, zero).unwrap();
        let y_le_one = arena.int_le(yv, one).unwrap();
        let x_pair = arena.and(x_le_zero, x_le_one).unwrap();
        let y_pair = arena.and(y_le_zero, y_le_one).unwrap();
        let all_atoms = arena.and(x_pair, y_pair).unwrap();

        let mut ctx = ArithAbstractor::default();
        let _ = ctx.abstract_term(&mut arena, all_atoms).unwrap();
        let idx = |term| ctx.atoms.iter().position(|atom| atom.term == term).unwrap();
        let x_le_zero_idx = idx(x_le_zero);
        let x_le_one_idx = idx(x_le_one);
        let y_le_zero_idx = idx(y_le_zero);
        let y_le_one_idx = idx(y_le_one);

        let mut lits: Vec<TermId> = ctx.atoms.iter().map(|atom| atom.term).collect();
        lits[x_le_one_idx] = arena.not(ctx.atoms[x_le_one_idx].term).unwrap();
        lits[y_le_one_idx] = arena.not(ctx.atoms[y_le_one_idx].term).unwrap();

        let indices = vec![x_le_zero_idx, x_le_one_idx, y_le_zero_idx, y_le_one_idx];
        let mut cores = cheap_int_bound_conflict_cores(&arena, &ctx, &lits, &indices);
        for core in &mut cores {
            core.sort_unstable();
        }
        cores.sort();

        let mut expected = vec![
            vec![x_le_zero_idx, x_le_one_idx],
            vec![y_le_zero_idx, y_le_one_idx],
        ];
        for core in &mut expected {
            core.sort_unstable();
        }
        expected.sort();
        assert_eq!(cores, expected);

        for core in cores {
            let core_lits = core.iter().map(|&idx| lits[idx]).collect::<Vec<_>>();
            assert!(matches!(
                check_with_lia_simplex(&arena, &core_lits).unwrap(),
                CheckResult::Unsat
            ));
        }
    }

    #[test]
    fn cheap_integer_difference_core_finds_negative_cycle() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let y = arena.declare("y", Sort::Int).unwrap();
        let xv = arena.var(x);
        let yv = arena.var(y);
        let one = arena.int_const(1);
        let y_plus_one = arena.int_add(yv, one).unwrap();
        let x_le_y = arena.int_le(xv, yv).unwrap();
        let y_plus_one_le_x = arena.int_le(y_plus_one, xv).unwrap();
        let both = arena.and(x_le_y, y_plus_one_le_x).unwrap();

        let mut ctx = ArithAbstractor::default();
        let _ = ctx.abstract_term(&mut arena, both).unwrap();
        let lits: Vec<TermId> = ctx.atoms.iter().map(|atom| atom.term).collect();
        let indices: Vec<usize> = (0..ctx.atoms.len()).collect();
        let mut core = cheap_int_difference_conflict_core(&arena, &ctx, &lits, &indices).unwrap();
        core.sort_unstable();
        assert_eq!(core, indices);

        let core_lits = core.iter().map(|&idx| lits[idx]).collect::<Vec<_>>();
        assert!(matches!(
            check_with_lia_simplex(&arena, &core_lits).unwrap(),
            CheckResult::Unsat
        ));
    }
}
