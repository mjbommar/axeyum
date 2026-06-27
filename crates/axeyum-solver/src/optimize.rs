//! Linear integer optimization (a first slice of optimization modulo theories).
//!
//! Z3/cvc5 expose `maximize`/`minimize`; this provides the integer-linear case,
//! directly serving the "constrained program optimization" north star. It is
//! built **on top of** the sound conjunctive integer decision procedure
//! ([`crate::check_with_lia_simplex`], ADR-0020) by feasibility queries, so it
//! inherits that procedure's soundness with no new core machinery:
//!
//! - feasibility of `assertions` gives a starting objective value;
//! - an **exponential** search raises the bound `objective >= k` until it becomes
//!   unsatisfiable (or a magnitude cap suggests the objective is unbounded);
//! - a **binary** search then finds the largest `k` with `objective >= k`
//!   satisfiable — that `k` is the maximum.
//!
//! Every probe is a sound `unsat`/`sat` decision; the result is the exact optimum
//! when one exists, [`OptOutcome::Unbounded`] when the objective grows past the
//! magnitude cap, [`OptOutcome::Infeasible`] when the constraints are `unsat`, and
//! [`OptOutcome::Unknown`] if a probe is undecided. `minimize` is `maximize` of
//! the negated objective. Feasibility probes go through the full dispatcher
//! ([`crate::check_auto`]: preprocessing, div/mod elimination, and all theory
//! routing), so the constraints may be arbitrary Boolean structure over integer
//! atoms (disjunctions, implications) and use `div`/`mod`-by-constant — and an
//! objective or constraint outside the deciding fragment makes the optimizer
//! return a graceful [`OptOutcome::Unknown`], never a hard error.

use axeyum_ir::{Sort, TermArena, TermId, Value, eval};

use crate::auto::check_auto;
use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};

// Native uses the std clock; wasm uses the `web_time` drop-in (ADR-0017).
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

/// Whether `deadline` (if set) has passed.
fn past_deadline(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|d| Instant::now() >= d)
}

/// An [`UnknownReason`] attributed to the wall-clock timeout (a resource limit,
/// not fundamental incompleteness).
fn timed_out_reason() -> UnknownReason {
    UnknownReason {
        kind: UnknownKind::ResourceLimit,
        detail: "optimization: wall-clock timeout reached".to_owned(),
    }
}

/// A deadline derived from `config.timeout`, or `None` when no timeout is set.
fn deadline_from(config: &SolverConfig) -> Option<Instant> {
    config.timeout.and_then(|t| Instant::now().checked_add(t))
}

/// Maps a feasibility-probe error to a graceful optimizer outcome: a
/// fragment-`Unsupported` becomes an `Unknown` reason (the probe could not decide
/// this fragment, so the optimizer reports `Unknown` rather than a wrong optimum),
/// while a genuine internal `Backend` (or other) error still propagates as `Err`.
fn probe_unsupported_to_unknown(err: SolverError) -> Result<UnknownReason, SolverError> {
    match err {
        SolverError::Unsupported(detail) => Ok(UnknownReason {
            kind: UnknownKind::Incomplete,
            detail,
        }),
        other => Err(other),
    }
}

/// Doubling steps before the objective is declared unbounded. `2^126` overflows
/// `i128` magnitude, so this is effectively an overflow guard, not a real bound.
const MAX_DOUBLINGS: u32 = 126;

/// The result of a linear-integer optimization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OptOutcome {
    /// The exact optimal objective value.
    Optimal(i128),
    /// The objective is unbounded in the optimization direction.
    Unbounded,
    /// The constraints are unsatisfiable, so there is no optimum.
    Infeasible,
    /// A feasibility probe was undecided.
    Unknown(UnknownReason),
}

/// Maximizes the integer-linear `objective` subject to `assertions`.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] if `objective` is not integer-sorted or
/// the query is outside the conjunctive integer fragment, or
/// [`SolverError::Backend`] on an internal error.
pub fn maximize_lia(
    arena: &mut TermArena,
    assertions: &[TermId],
    objective: TermId,
) -> Result<OptOutcome, SolverError> {
    maximize_lia_with_config(arena, assertions, objective, &SolverConfig::default())
}

/// Like [`maximize_lia`], but honoring `config` (notably `config.timeout`):
/// every feasibility probe is decided under `config`, and the bound-search loop
/// checks a wall-clock deadline, returning the best value found so far as
/// [`OptOutcome::Unknown`] (a [`UnknownKind::ResourceLimit`]) on expiry.
///
/// # Errors
///
/// See [`maximize_lia`].
pub fn maximize_lia_with_config(
    arena: &mut TermArena,
    assertions: &[TermId],
    objective: TermId,
    config: &SolverConfig,
) -> Result<OptOutcome, SolverError> {
    let deadline = deadline_from(config);
    // Starting point: any feasible value of the objective.
    let mut lo = match objective_value(arena, assertions, objective, config)? {
        Probe::Sat(value) => value,
        Probe::Unsat => return Ok(OptOutcome::Infeasible),
        Probe::Unknown(reason) => return Ok(OptOutcome::Unknown(reason)),
    };

    // Exponential search for an unsatisfiable upper bound `hi` (objective >= hi
    // is infeasible). Bounded by MAX_DOUBLINGS / i128 overflow -> Unbounded.
    let mut delta: i128 = 1;
    let mut doublings: u32 = 0;
    let mut hi = loop {
        if past_deadline(deadline) {
            return Ok(OptOutcome::Unknown(timed_out_reason()));
        }
        let Some(probe_point) = lo.checked_add(delta) else {
            return Ok(OptOutcome::Unbounded);
        };
        match objective_ge(arena, assertions, objective, probe_point, config)? {
            Probe::Sat(value) => lo = value.max(probe_point),
            Probe::Unsat => break probe_point,
            Probe::Unknown(reason) => return Ok(OptOutcome::Unknown(reason)),
        }
        doublings += 1;
        if doublings >= MAX_DOUBLINGS {
            return Ok(OptOutcome::Unbounded);
        }
        match delta.checked_mul(2) {
            Some(next) => delta = next,
            None => return Ok(OptOutcome::Unbounded),
        }
    };

    // Binary search in [lo, hi): objective >= lo is sat, objective >= hi is unsat.
    while hi - lo > 1 {
        if past_deadline(deadline) {
            // `lo` is a probe-verified feasible value but not certified optimal;
            // report it as undecided rather than a wrong optimum.
            return Ok(OptOutcome::Unknown(timed_out_reason()));
        }
        let mid = lo + (hi - lo) / 2;
        match objective_ge(arena, assertions, objective, mid, config)? {
            Probe::Sat(value) => lo = value.max(mid),
            Probe::Unsat => hi = mid,
            Probe::Unknown(reason) => return Ok(OptOutcome::Unknown(reason)),
        }
    }
    Ok(OptOutcome::Optimal(lo))
}

/// Minimizes the integer-linear `objective` subject to `assertions`.
///
/// # Errors
///
/// See [`maximize_lia`].
pub fn minimize_lia(
    arena: &mut TermArena,
    assertions: &[TermId],
    objective: TermId,
) -> Result<OptOutcome, SolverError> {
    minimize_lia_with_config(arena, assertions, objective, &SolverConfig::default())
}

/// Like [`minimize_lia`], but honoring `config` (notably `config.timeout`).
///
/// # Errors
///
/// See [`maximize_lia`].
pub fn minimize_lia_with_config(
    arena: &mut TermArena,
    assertions: &[TermId],
    objective: TermId,
    config: &SolverConfig,
) -> Result<OptOutcome, SolverError> {
    let negated = arena.int_neg(objective)?;
    Ok(
        match maximize_lia_with_config(arena, assertions, negated, config)? {
            OptOutcome::Optimal(max_of_neg) => match max_of_neg.checked_neg() {
                Some(min) => OptOutcome::Optimal(min),
                None => OptOutcome::Unbounded,
            },
            other => other,
        },
    )
}

/// One objective in a lexicographic optimization (P4.3): the integer-linear
/// `objective` term and its direction.
#[derive(Debug, Clone, Copy)]
pub struct LexObjective {
    /// The integer-sorted objective term.
    pub objective: TermId,
    /// `true` to maximize, `false` to minimize.
    pub maximize: bool,
}

/// The result of a lexicographic optimization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LexOutcome {
    /// Every objective was optimized; the lexicographically-optimal value of each,
    /// in the input order.
    Optimal(Vec<i128>),
    /// Optimization stopped at objective `index` (it was unbounded, infeasible, or
    /// undecided). `prefix` holds the optimal values of the objectives before it.
    Stopped {
        /// The index of the objective that did not yield a finite optimum.
        index: usize,
        /// Optimal values of the strictly-earlier objectives.
        prefix: Vec<i128>,
        /// Why this objective stopped the chain.
        outcome: OptOutcome,
    },
}

/// **Lexicographic multi-objective optimization** over integer-linear objectives
/// (z3 `(maximize …)`/`(minimize …)` with the default lexicographic combination).
///
/// Optimizes `objectives` in order: each is optimized (via the checked
/// single-objective [`maximize_lia`]/[`minimize_lia`]) subject to `assertions`
/// **plus** the earlier objectives pinned at their optima (`objᵢ ≥ vᵢ` for a
/// maximized objective, `objᵢ ≤ vᵢ` for a minimized one — which, at the optimum,
/// pins `objᵢ = vᵢ`). So later objectives range only over the optimal face of the
/// earlier ones — exactly lexicographic semantics. Sound and terminating: it is a
/// bounded composition of the single-objective optimizer (each value is its exact,
/// probe-verified optimum), adding no unbounded search.
///
/// Returns [`LexOutcome::Stopped`] at the first objective that is unbounded /
/// infeasible / undecided (the chain cannot continue past it).
///
/// # Errors
///
/// [`SolverError::Unsupported`] if an objective is not integer-sorted, or
/// [`SolverError`] from a feasibility probe / term builder.
pub fn optimize_lia_lexicographic(
    arena: &mut TermArena,
    assertions: &[TermId],
    objectives: &[LexObjective],
) -> Result<LexOutcome, SolverError> {
    optimize_lia_lexicographic_with_config(arena, assertions, objectives, &SolverConfig::default())
}

/// Like [`optimize_lia_lexicographic`], honoring `config` (notably
/// `config.timeout`): the deadline is checked before each objective and threaded
/// into the single-objective optimizer, so a timeout stops the chain with a
/// [`LexOutcome::Stopped`] carrying an [`OptOutcome::Unknown`].
///
/// # Errors
///
/// See [`optimize_lia_lexicographic`].
pub fn optimize_lia_lexicographic_with_config(
    arena: &mut TermArena,
    assertions: &[TermId],
    objectives: &[LexObjective],
    config: &SolverConfig,
) -> Result<LexOutcome, SolverError> {
    let deadline = deadline_from(config);
    let mut constraints = assertions.to_vec();
    let mut values: Vec<i128> = Vec::with_capacity(objectives.len());
    for (index, obj) in objectives.iter().enumerate() {
        if past_deadline(deadline) {
            return Ok(LexOutcome::Stopped {
                index,
                prefix: values,
                outcome: OptOutcome::Unknown(timed_out_reason()),
            });
        }
        let outcome = if obj.maximize {
            maximize_lia_with_config(arena, &constraints, obj.objective, config)?
        } else {
            minimize_lia_with_config(arena, &constraints, obj.objective, config)?
        };
        match outcome {
            OptOutcome::Optimal(value) => {
                values.push(value);
                // Pin this objective at its optimum before optimizing the next, so
                // the chain ranges only over the current optimal face.
                let vc = arena.int_const(value);
                let pin = if obj.maximize {
                    arena.int_ge(obj.objective, vc)
                } else {
                    arena.int_le(obj.objective, vc)
                }
                .map_err(|e| SolverError::Backend(e.to_string()))?;
                constraints.push(pin);
            }
            other => {
                return Ok(LexOutcome::Stopped {
                    index,
                    prefix: values,
                    outcome: other,
                });
            }
        }
    }
    Ok(LexOutcome::Optimal(values))
}

/// **Box (independent) multi-objective optimization** over integer-linear
/// objectives — z3's `box` OMT mode. Each objective is optimized *independently*
/// over the same `assertions` (no pinning between them), so the result is the
/// per-objective optimum as if each were solved alone. Contrast
/// [`optimize_lia_lexicographic`], where earlier objectives constrain later ones:
/// for `0≤x,y≤10 ∧ x+y≤12`, box `max x`/`max y` is `[10, 10]` (each reachable
/// alone) while lex is `[10, 2]`.
///
/// Returns each objective's [`OptOutcome`] in input order. Sound and terminating
/// by construction (a `map` of the checked single-objective optimizer; no shared
/// state, no extra search).
///
/// # Errors
///
/// Propagates any per-objective [`SolverError`] (e.g. a non-integer objective).
pub fn optimize_lia_box(
    arena: &mut TermArena,
    assertions: &[TermId],
    objectives: &[LexObjective],
) -> Result<Vec<OptOutcome>, SolverError> {
    optimize_lia_box_with_config(arena, assertions, objectives, &SolverConfig::default())
}

/// Like [`optimize_lia_box`], honoring `config` (notably `config.timeout`): once
/// the deadline passes, the remaining objectives report [`OptOutcome::Unknown`]
/// (a [`UnknownKind::ResourceLimit`]) rather than running on.
///
/// # Errors
///
/// See [`optimize_lia_box`].
pub fn optimize_lia_box_with_config(
    arena: &mut TermArena,
    assertions: &[TermId],
    objectives: &[LexObjective],
    config: &SolverConfig,
) -> Result<Vec<OptOutcome>, SolverError> {
    let deadline = deadline_from(config);
    let mut out = Vec::with_capacity(objectives.len());
    for obj in objectives {
        if past_deadline(deadline) {
            out.push(OptOutcome::Unknown(timed_out_reason()));
            continue;
        }
        let outcome = if obj.maximize {
            maximize_lia_with_config(arena, assertions, obj.objective, config)?
        } else {
            minimize_lia_with_config(arena, assertions, obj.objective, config)?
        };
        out.push(outcome);
    }
    Ok(out)
}

/// Deterministic caps for [`optimize_lia_pareto`] (resource discipline): the most
/// Pareto points enumerated, and the most guided-improvement steps spent certifying
/// one point as maximal. Exceeding either yields a truncated / `Unknown` result
/// rather than unbounded work.
const MAX_PARETO_POINTS: usize = 256;
const MAX_PARETO_PUSH: usize = 64;

/// The result of a Pareto-front enumeration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParetoOutcome {
    /// The complete Pareto front: every objective-value tuple that is
    /// Pareto-optimal (each point verified maximal; the set covers the front).
    Complete(Vec<Vec<i128>>),
    /// The point cap was hit; `points` are verified-optimal but the front may have
    /// more.
    Truncated(Vec<Vec<i128>>),
    /// Enumeration could not be certified (a probe was undecided, or a point's
    /// maximality could not be confirmed within the push cap); `found` are the
    /// verified-optimal points discovered before the stop.
    Unknown {
        /// Pareto-optimal points verified before the stop.
        found: Vec<Vec<i128>>,
        /// Why enumeration stopped.
        reason: UnknownReason,
    },
}

/// `objective` better-than-or-equal to constant `c` in its direction
/// (`≥ c` for a maximized objective, `≤ c` for a minimized one).
fn pareto_better_eq(
    arena: &mut TermArena,
    obj: LexObjective,
    c: i128,
) -> Result<TermId, SolverError> {
    let cc = arena.int_const(c);
    let t = if obj.maximize {
        arena.int_ge(obj.objective, cc)
    } else {
        arena.int_le(obj.objective, cc)
    }?;
    Ok(t)
}

/// `objective` strictly better than constant `c` in its direction.
fn pareto_strict_better(
    arena: &mut TermArena,
    obj: LexObjective,
    c: i128,
) -> Result<TermId, SolverError> {
    let cc = arena.int_const(c);
    let t = if obj.maximize {
        arena.int_gt(obj.objective, cc)
    } else {
        arena.int_lt(obj.objective, cc)
    }?;
    Ok(t)
}

/// `⋁ᵢ strict_better(objᵢ, vᵢ)` — "improves on `v` in at least one objective".
fn pareto_improves_somewhere(
    arena: &mut TermArena,
    objectives: &[LexObjective],
    v: &[i128],
) -> Result<TermId, SolverError> {
    let mut acc: Option<TermId> = None;
    for (obj, &vi) in objectives.iter().zip(v) {
        let sb = pareto_strict_better(arena, *obj, vi)?;
        acc = Some(match acc {
            None => sb,
            Some(prev) => arena.or(prev, sb)?,
        });
    }
    acc.ok_or_else(|| SolverError::Unsupported("pareto needs at least one objective".to_owned()))
}

/// Solve `constraints` and read each objective's value from the model.
enum MultiProbe {
    Sat(Vec<i128>),
    Unsat,
    Unknown(UnknownReason),
}

fn pareto_probe(
    arena: &mut TermArena,
    constraints: &[TermId],
    objectives: &[LexObjective],
    config: &SolverConfig,
) -> Result<MultiProbe, SolverError> {
    // Route through the full dispatcher (decides div/mod, all theories) and map a
    // fragment-`Unsupported` to a graceful `MultiProbe::Unknown` (never a hard
    // error on an out-of-fragment objective/constraint).
    let result = check_auto(arena, constraints, config);
    match result {
        Ok(CheckResult::Sat(model)) => {
            let assignment = model.to_assignment();
            let mut vals = Vec::with_capacity(objectives.len());
            for obj in objectives {
                match eval(arena, obj.objective, &assignment)? {
                    Value::Int(v) => vals.push(v),
                    other => {
                        return Ok(MultiProbe::Unknown(UnknownReason {
                            kind: UnknownKind::Incomplete,
                            detail: format!(
                                "pareto objective is not integer-valued (got {other:?})"
                            ),
                        }));
                    }
                }
            }
            Ok(MultiProbe::Sat(vals))
        }
        Ok(CheckResult::Unsat) => Ok(MultiProbe::Unsat),
        Ok(CheckResult::Unknown(reason)) => Ok(MultiProbe::Unknown(reason)),
        Err(err) => Ok(MultiProbe::Unknown(probe_unsupported_to_unknown(err)?)),
    }
}

/// **Pareto-front multi-objective optimization** over integer-linear objectives —
/// z3's `pareto` OMT mode. Enumerates the Pareto-optimal objective-value tuples (no
/// objective can improve without another worsening) by *guided improvement* (Rayside
/// et al.): find a feasible candidate not dominated by any point found so far, push
/// it to a maximal (Pareto-optimal) point, record it, exclude everything it weakly
/// dominates, and repeat until no fresh candidate remains.
///
/// Each recorded point is **verified** Pareto-optimal (no feasible point dominates
/// it — a confirmed-`unsat` domination query), and the exclusions guarantee
/// distinct, mutually-non-dominated points whose set covers the front. Bounded by
/// `MAX_PARETO_POINTS` (→ [`ParetoOutcome::Truncated`]) and `MAX_PARETO_PUSH`
/// (→ [`ParetoOutcome::Unknown`] if a point's maximality can't be confirmed within
/// the budget), so it always terminates with a deterministic result — never
/// unbounded enumeration.
///
/// # Errors
///
/// [`SolverError`] from a probe / term builder (e.g. a non-integer objective).
pub fn optimize_lia_pareto(
    arena: &mut TermArena,
    assertions: &[TermId],
    objectives: &[LexObjective],
) -> Result<ParetoOutcome, SolverError> {
    optimize_lia_pareto_with_config(arena, assertions, objectives, &SolverConfig::default())
}

/// Like [`optimize_lia_pareto`], honoring `config` (notably `config.timeout`): a
/// wall-clock deadline is checked at the top of each enumeration round and on each
/// guided-improvement push, returning the points verified so far as
/// [`ParetoOutcome::Truncated`] on expiry (the `MAX_PARETO_POINTS` /
/// `MAX_PARETO_PUSH` caps remain as secondary deterministic bounds).
///
/// # Errors
///
/// See [`optimize_lia_pareto`].
pub fn optimize_lia_pareto_with_config(
    arena: &mut TermArena,
    assertions: &[TermId],
    objectives: &[LexObjective],
    config: &SolverConfig,
) -> Result<ParetoOutcome, SolverError> {
    let deadline = deadline_from(config);
    let mut front: Vec<Vec<i128>> = Vec::new();
    let mut exclusions: Vec<TermId> = Vec::new();
    loop {
        if front.len() >= MAX_PARETO_POINTS {
            return Ok(ParetoOutcome::Truncated(front));
        }
        if past_deadline(deadline) {
            return Ok(ParetoOutcome::Truncated(front));
        }
        // A fresh candidate must not be weakly dominated by any recorded point.
        let mut query = assertions.to_vec();
        query.extend_from_slice(&exclusions);
        let candidate = match pareto_probe(arena, &query, objectives, config)? {
            MultiProbe::Sat(v) => v,
            MultiProbe::Unsat => return Ok(ParetoOutcome::Complete(front)),
            MultiProbe::Unknown(reason) => {
                return Ok(ParetoOutcome::Unknown {
                    found: front,
                    reason,
                });
            }
        };
        // Guided improvement: climb to a point no feasible point dominates.
        let mut v = candidate;
        let mut certified = false;
        for _ in 0..MAX_PARETO_PUSH {
            if past_deadline(deadline) {
                return Ok(ParetoOutcome::Truncated(front));
            }
            let mut dom = assertions.to_vec();
            for (obj, &vi) in objectives.iter().zip(&v) {
                dom.push(pareto_better_eq(arena, *obj, vi)?);
            }
            dom.push(pareto_improves_somewhere(arena, objectives, &v)?);
            match pareto_probe(arena, &dom, objectives, config)? {
                MultiProbe::Sat(w) => v = w, // w dominates v; keep climbing
                MultiProbe::Unsat => {
                    certified = true; // nothing dominates v → Pareto-optimal
                    break;
                }
                MultiProbe::Unknown(reason) => {
                    return Ok(ParetoOutcome::Unknown {
                        found: front,
                        reason,
                    });
                }
            }
        }
        if !certified {
            return Ok(ParetoOutcome::Unknown {
                found: front,
                reason: UnknownReason {
                    kind: UnknownKind::ResourceLimit,
                    detail: "pareto: guided-improvement push budget reached".to_owned(),
                },
            });
        }
        let exclude = pareto_improves_somewhere(arena, objectives, &v)?;
        front.push(v);
        exclusions.push(exclude);
    }
}

/// One objective in a bit-vector lexicographic optimization: the BV `objective`,
/// whether to read it as **signed** (two's-complement) vs unsigned, and whether to
/// maximize vs minimize.
#[derive(Debug, Clone, Copy)]
pub struct BvLexObjective {
    /// The bit-vector objective term.
    pub objective: TermId,
    /// Read the value as signed two's-complement (else unsigned).
    pub signed: bool,
    /// `true` to maximize, `false` to minimize.
    pub maximize: bool,
}

/// **Lexicographic multi-objective optimization over bit-vector objectives** — the
/// BV analogue of [`optimize_lia_lexicographic`], pinning each objective at its
/// optimum (with the matching signed/unsigned, max/min comparison) before
/// optimizing the next. Sound + terminating for the same reason (a bounded
/// composition of the checked single-objective BV optimizers).
///
/// # Errors
///
/// [`SolverError::Unsupported`] if an objective is not a (≤64-bit) bit-vector, or
/// [`SolverError`] from a probe / builder.
pub fn optimize_bv_lexicographic(
    arena: &mut TermArena,
    assertions: &[TermId],
    objectives: &[BvLexObjective],
) -> Result<LexOutcome, SolverError> {
    optimize_bv_lexicographic_with_config(arena, assertions, objectives, &SolverConfig::default())
}

/// Like [`optimize_bv_lexicographic`], honoring `config` (notably
/// `config.timeout`): the deadline is checked before each objective and threaded
/// into the single-objective BV optimizer, so a timeout stops the chain with a
/// [`LexOutcome::Stopped`] carrying an [`OptOutcome::Unknown`].
///
/// # Errors
///
/// See [`optimize_bv_lexicographic`].
pub fn optimize_bv_lexicographic_with_config(
    arena: &mut TermArena,
    assertions: &[TermId],
    objectives: &[BvLexObjective],
    config: &SolverConfig,
) -> Result<LexOutcome, SolverError> {
    let deadline = deadline_from(config);
    let mut constraints = assertions.to_vec();
    let mut values: Vec<i128> = Vec::with_capacity(objectives.len());
    for (index, obj) in objectives.iter().enumerate() {
        if past_deadline(deadline) {
            return Ok(LexOutcome::Stopped {
                index,
                prefix: values,
                outcome: OptOutcome::Unknown(timed_out_reason()),
            });
        }
        let outcome = match (obj.signed, obj.maximize) {
            (false, true) => maximize_bv_with_config(arena, &constraints, obj.objective, config)?,
            (false, false) => minimize_bv_with_config(arena, &constraints, obj.objective, config)?,
            (true, true) => {
                maximize_bv_signed_with_config(arena, &constraints, obj.objective, config)?
            }
            (true, false) => {
                minimize_bv_signed_with_config(arena, &constraints, obj.objective, config)?
            }
        };
        match outcome {
            OptOutcome::Optimal(value) => {
                values.push(value);
                let Sort::BitVec(w) = arena.sort_of(obj.objective) else {
                    return Err(SolverError::Unsupported(
                        "bit-vector lexicographic objective must be a bit-vector".to_owned(),
                    ));
                };
                // Width-`w` two's-complement constant of the optimum (the optimizers
                // cap `w ≤ 64`, so the low-`w` bits of `value` are exact).
                let mask = if w >= 128 {
                    u128::MAX
                } else {
                    (1u128 << w) - 1
                };
                #[allow(clippy::cast_sign_loss)]
                let vc = arena
                    .bv_const(w, (value as u128) & mask)
                    .map_err(|e| SolverError::Backend(e.to_string()))?;
                let pin = match (obj.signed, obj.maximize) {
                    (false, true) => arena.bv_uge(obj.objective, vc),
                    (false, false) => arena.bv_ule(obj.objective, vc),
                    (true, true) => arena.bv_sge(obj.objective, vc),
                    (true, false) => arena.bv_sle(obj.objective, vc),
                }
                .map_err(|e| SolverError::Backend(e.to_string()))?;
                constraints.push(pin);
            }
            other => {
                return Ok(LexOutcome::Stopped {
                    index,
                    prefix: values,
                    outcome: other,
                });
            }
        }
    }
    Ok(LexOutcome::Optimal(values))
}

/// **Box (independent) optimization over bit-vector objectives** — the BV analogue
/// of [`optimize_lia_box`]. Each objective is optimized independently over the same
/// `assertions` (no pinning), with its own signed/unsigned + max/min direction.
/// Sound and terminating by construction (a `map` of the checked single-objective
/// BV optimizers).
///
/// # Errors
///
/// Propagates any per-objective [`SolverError`] (e.g. a non-bit-vector or >64-bit
/// objective).
pub fn optimize_bv_box(
    arena: &mut TermArena,
    assertions: &[TermId],
    objectives: &[BvLexObjective],
) -> Result<Vec<OptOutcome>, SolverError> {
    optimize_bv_box_with_config(arena, assertions, objectives, &SolverConfig::default())
}

/// Like [`optimize_bv_box`], honoring `config` (notably `config.timeout`): once the
/// deadline passes, the remaining objectives report [`OptOutcome::Unknown`] (a
/// [`UnknownKind::ResourceLimit`]) rather than running on.
///
/// # Errors
///
/// See [`optimize_bv_box`].
pub fn optimize_bv_box_with_config(
    arena: &mut TermArena,
    assertions: &[TermId],
    objectives: &[BvLexObjective],
    config: &SolverConfig,
) -> Result<Vec<OptOutcome>, SolverError> {
    let deadline = deadline_from(config);
    let mut out = Vec::with_capacity(objectives.len());
    for obj in objectives {
        if past_deadline(deadline) {
            out.push(OptOutcome::Unknown(timed_out_reason()));
            continue;
        }
        let outcome = match (obj.signed, obj.maximize) {
            (false, true) => maximize_bv_with_config(arena, assertions, obj.objective, config)?,
            (false, false) => minimize_bv_with_config(arena, assertions, obj.objective, config)?,
            (true, true) => {
                maximize_bv_signed_with_config(arena, assertions, obj.objective, config)?
            }
            (true, false) => {
                minimize_bv_signed_with_config(arena, assertions, obj.objective, config)?
            }
        };
        out.push(outcome);
    }
    Ok(out)
}

/// A width-`w` two's-complement constant of `value` (low `w` bits).
fn pareto_bv_const(arena: &mut TermArena, w: u32, value: i128) -> Result<TermId, SolverError> {
    let mask = if w >= 128 {
        u128::MAX
    } else {
        (1u128 << w) - 1
    };
    #[allow(clippy::cast_sign_loss)]
    arena
        .bv_const(w, (value as u128) & mask)
        .map_err(|e| SolverError::Backend(e.to_string()))
}

/// `objective` better-than-or-equal to `c` in its (signed/unsigned, max/min)
/// direction.
fn pareto_bv_better_eq(
    arena: &mut TermArena,
    obj: BvLexObjective,
    w: u32,
    c: i128,
) -> Result<TermId, SolverError> {
    let cc = pareto_bv_const(arena, w, c)?;
    let t = match (obj.signed, obj.maximize) {
        (false, true) => arena.bv_uge(obj.objective, cc),
        (false, false) => arena.bv_ule(obj.objective, cc),
        (true, true) => arena.bv_sge(obj.objective, cc),
        (true, false) => arena.bv_sle(obj.objective, cc),
    }
    .map_err(|e| SolverError::Backend(e.to_string()))?;
    Ok(t)
}

/// `objective` strictly better than `c` in its direction.
fn pareto_bv_strict_better(
    arena: &mut TermArena,
    obj: BvLexObjective,
    w: u32,
    c: i128,
) -> Result<TermId, SolverError> {
    let cc = pareto_bv_const(arena, w, c)?;
    let t = match (obj.signed, obj.maximize) {
        (false, true) => arena.bv_ugt(obj.objective, cc),
        (false, false) => arena.bv_ult(obj.objective, cc),
        (true, true) => arena.bv_sgt(obj.objective, cc),
        (true, false) => arena.bv_slt(obj.objective, cc),
    }
    .map_err(|e| SolverError::Backend(e.to_string()))?;
    Ok(t)
}

/// The bit-width of a BV objective (the optimizers cap it at ≤64).
fn pareto_bv_width(arena: &TermArena, obj: BvLexObjective) -> Result<u32, SolverError> {
    match arena.sort_of(obj.objective) {
        Sort::BitVec(w) => Ok(w),
        other => Err(SolverError::Unsupported(format!(
            "pareto bit-vector objective is not a bit-vector (got {other:?})"
        ))),
    }
}

/// `⋁ᵢ strict_better(objᵢ, vᵢ)` over BV objectives.
fn pareto_bv_improves_somewhere(
    arena: &mut TermArena,
    objectives: &[BvLexObjective],
    v: &[i128],
) -> Result<TermId, SolverError> {
    let mut acc: Option<TermId> = None;
    for (obj, &vi) in objectives.iter().zip(v) {
        let w = pareto_bv_width(arena, *obj)?;
        let sb = pareto_bv_strict_better(arena, *obj, w, vi)?;
        acc = Some(match acc {
            None => sb,
            Some(prev) => arena
                .or(prev, sb)
                .map_err(|e| SolverError::Backend(e.to_string()))?,
        });
    }
    acc.ok_or_else(|| SolverError::Unsupported("pareto needs at least one objective".to_owned()))
}

/// Solve `constraints` and read each BV objective's value (signed or unsigned per
/// the objective) from the model.
fn pareto_bv_probe(
    arena: &mut TermArena,
    constraints: &[TermId],
    objectives: &[BvLexObjective],
    config: &SolverConfig,
) -> Result<MultiProbe, SolverError> {
    let result = check_auto(arena, constraints, config);
    match result {
        Ok(CheckResult::Sat(model)) => {
            let assignment = model.to_assignment();
            let mut vals = Vec::with_capacity(objectives.len());
            for obj in objectives {
                match eval(arena, obj.objective, &assignment)? {
                    Value::Bv { width, value } => vals.push(if obj.signed {
                        bv_signed(value, width)
                    } else {
                        i128::try_from(value).map_err(|_| {
                            SolverError::Backend("BV objective exceeds i128 range".to_owned())
                        })?
                    }),
                    other => {
                        return Ok(MultiProbe::Unknown(UnknownReason {
                            kind: UnknownKind::Incomplete,
                            detail: format!(
                                "pareto BV objective is not a bit-vector value (got {other:?})"
                            ),
                        }));
                    }
                }
            }
            Ok(MultiProbe::Sat(vals))
        }
        Ok(CheckResult::Unsat) => Ok(MultiProbe::Unsat),
        Ok(CheckResult::Unknown(reason)) => Ok(MultiProbe::Unknown(reason)),
        Err(err) => Ok(MultiProbe::Unknown(probe_unsupported_to_unknown(err)?)),
    }
}

/// **Pareto-front optimization over bit-vector objectives** — the BV analogue of
/// [`optimize_lia_pareto`] (guided improvement, each point verified Pareto-optimal,
/// the same deterministic `MAX_PARETO_POINTS`/`MAX_PARETO_PUSH` caps). Each
/// objective carries its own signed/unsigned + max/min direction.
///
/// # Errors
///
/// [`SolverError`] from a probe / builder (e.g. a non-bit-vector objective).
pub fn optimize_bv_pareto(
    arena: &mut TermArena,
    assertions: &[TermId],
    objectives: &[BvLexObjective],
) -> Result<ParetoOutcome, SolverError> {
    optimize_bv_pareto_with_config(arena, assertions, objectives, &SolverConfig::default())
}

/// Like [`optimize_bv_pareto`], honoring `config` (notably `config.timeout`): a
/// wall-clock deadline is checked at the top of each enumeration round and on each
/// guided-improvement push, returning the points verified so far as
/// [`ParetoOutcome::Truncated`] on expiry (the `MAX_PARETO_POINTS` /
/// `MAX_PARETO_PUSH` caps remain as secondary deterministic bounds).
///
/// # Errors
///
/// See [`optimize_bv_pareto`].
pub fn optimize_bv_pareto_with_config(
    arena: &mut TermArena,
    assertions: &[TermId],
    objectives: &[BvLexObjective],
    config: &SolverConfig,
) -> Result<ParetoOutcome, SolverError> {
    let deadline = deadline_from(config);
    let mut front: Vec<Vec<i128>> = Vec::new();
    let mut exclusions: Vec<TermId> = Vec::new();
    loop {
        if front.len() >= MAX_PARETO_POINTS {
            return Ok(ParetoOutcome::Truncated(front));
        }
        if past_deadline(deadline) {
            return Ok(ParetoOutcome::Truncated(front));
        }
        let mut query = assertions.to_vec();
        query.extend_from_slice(&exclusions);
        let candidate = match pareto_bv_probe(arena, &query, objectives, config)? {
            MultiProbe::Sat(v) => v,
            MultiProbe::Unsat => return Ok(ParetoOutcome::Complete(front)),
            MultiProbe::Unknown(reason) => {
                return Ok(ParetoOutcome::Unknown {
                    found: front,
                    reason,
                });
            }
        };
        let mut v = candidate;
        let mut certified = false;
        for _ in 0..MAX_PARETO_PUSH {
            if past_deadline(deadline) {
                return Ok(ParetoOutcome::Truncated(front));
            }
            let mut dom = assertions.to_vec();
            for (obj, &vi) in objectives.iter().zip(&v) {
                let w = pareto_bv_width(arena, *obj)?;
                dom.push(pareto_bv_better_eq(arena, *obj, w, vi)?);
            }
            dom.push(pareto_bv_improves_somewhere(arena, objectives, &v)?);
            match pareto_bv_probe(arena, &dom, objectives, config)? {
                MultiProbe::Sat(w) => v = w,
                MultiProbe::Unsat => {
                    certified = true;
                    break;
                }
                MultiProbe::Unknown(reason) => {
                    return Ok(ParetoOutcome::Unknown {
                        found: front,
                        reason,
                    });
                }
            }
        }
        if !certified {
            return Ok(ParetoOutcome::Unknown {
                found: front,
                reason: UnknownReason {
                    kind: UnknownKind::ResourceLimit,
                    detail: "pareto (bv): guided-improvement push budget reached".to_owned(),
                },
            });
        }
        let exclude = pareto_bv_improves_somewhere(arena, objectives, &v)?;
        front.push(v);
        exclusions.push(exclude);
    }
}

/// The result of one feasibility probe.
enum Probe {
    /// Satisfiable, carrying the objective's value in the found model.
    Sat(i128),
    Unsat,
    Unknown(UnknownReason),
}

/// Decides `assertions` and, if satisfiable, returns the objective's value.
fn objective_value(
    arena: &mut TermArena,
    assertions: &[TermId],
    objective: TermId,
    config: &SolverConfig,
) -> Result<Probe, SolverError> {
    decide_with_objective(arena, assertions, objective, None, config)
}

/// Decides `assertions AND objective >= bound` and returns the objective value.
fn objective_ge(
    arena: &mut TermArena,
    assertions: &[TermId],
    objective: TermId,
    bound: i128,
    config: &SolverConfig,
) -> Result<Probe, SolverError> {
    decide_with_objective(arena, assertions, objective, Some(bound), config)
}

fn decide_with_objective(
    arena: &mut TermArena,
    assertions: &[TermId],
    objective: TermId,
    bound: Option<i128>,
    config: &SolverConfig,
) -> Result<Probe, SolverError> {
    let mut query = assertions.to_vec();
    if let Some(bound) = bound {
        let bound_term = arena.int_const(bound);
        query.push(arena.int_ge(objective, bound_term)?);
    }
    // Route every feasibility probe through the full dispatcher (`check_auto`):
    // preprocessing + div/mod elimination + all theory routing. This decides
    // objectives/constraints the bare LIA oracle declines (e.g. `x mod 2 = 0`,
    // `x / 3 <= 5`) and, crucially, never hard-errors on an out-of-fragment
    // query — an `Unsupported` fragment is mapped to a graceful `Probe::Unknown`
    // so the optimizer yields `OptOutcome::Unknown`, never a wrong optimum
    // (soundness: `check_auto` decides the same feasibility query).
    let result = check_auto(arena, &query, config);
    match result {
        Ok(CheckResult::Sat(model)) => {
            let assignment = model.to_assignment();
            match eval(arena, objective, &assignment)? {
                Value::Int(value) => Ok(Probe::Sat(value)),
                other => Ok(Probe::Unknown(UnknownReason {
                    kind: UnknownKind::Incomplete,
                    detail: format!("optimization objective is not integer-valued (got {other:?})"),
                })),
            }
        }
        Ok(CheckResult::Unsat) => Ok(Probe::Unsat),
        Ok(CheckResult::Unknown(reason)) => Ok(Probe::Unknown(reason)),
        Err(err) => Ok(Probe::Unknown(probe_unsupported_to_unknown(err)?)),
    }
}

// ---------------------------------------------------------------------------
// Unsigned bit-vector optimization.
//
// The bit-vector domain is finite, so there is no unbounded case and binary
// search on the objective bound terminates with the exact optimum. Probes go
// through the eager bit-vector solver (the full dispatcher), so the constraints
// may be arbitrary `QF_BV` (and the supported theory composition). Objectives
// wider than 127 bits are declined (the optimum may not fit the `i128` result).
// ---------------------------------------------------------------------------

/// Maximizes the **unsigned** value of bit-vector `objective` subject to
/// `assertions`.
///
/// # Errors
///
/// [`SolverError::Unsupported`] if `objective` is not a bit-vector of width
/// `<= 127`, or [`SolverError::Backend`] on an internal error.
pub fn maximize_bv(
    arena: &mut TermArena,
    assertions: &[TermId],
    objective: TermId,
) -> Result<OptOutcome, SolverError> {
    maximize_bv_with_config(arena, assertions, objective, &SolverConfig::default())
}

/// Like [`maximize_bv`], but honoring `config` (notably `config.timeout`): every
/// feasibility probe is decided under `config`, and the binary search checks a
/// wall-clock deadline, returning [`OptOutcome::Unknown`] (a
/// [`UnknownKind::ResourceLimit`]) on expiry rather than running unbounded.
///
/// # Errors
///
/// See [`maximize_bv`].
pub fn maximize_bv_with_config(
    arena: &mut TermArena,
    assertions: &[TermId],
    objective: TermId,
    config: &SolverConfig,
) -> Result<OptOutcome, SolverError> {
    let deadline = deadline_from(config);
    let max = bv_objective_max(arena, objective)?;
    let v0 = match bv_value(arena, assertions, objective, None, config)? {
        BvProbe::Sat(value) => value,
        BvProbe::Unsat => return Ok(OptOutcome::Infeasible),
        BvProbe::Unknown(reason) => return Ok(OptOutcome::Unknown(reason)),
    };
    // Largest k in [v0, max] with `objective >=u k` satisfiable.
    let mut lo = v0;
    let mut hi = max;
    while lo < hi {
        if past_deadline(deadline) {
            return Ok(OptOutcome::Unknown(timed_out_reason()));
        }
        let mid = lo + (hi - lo).div_ceil(2);
        match bv_value(
            arena,
            assertions,
            objective,
            Some((BvRel::Uge, mid)),
            config,
        )? {
            BvProbe::Sat(value) => lo = value.max(mid),
            BvProbe::Unsat => hi = mid - 1,
            BvProbe::Unknown(reason) => return Ok(OptOutcome::Unknown(reason)),
        }
    }
    Ok(OptOutcome::Optimal(bv_to_i128(lo)?))
}

/// Minimizes the **unsigned** value of bit-vector `objective` subject to
/// `assertions`.
///
/// # Errors
///
/// See [`maximize_bv`].
pub fn minimize_bv(
    arena: &mut TermArena,
    assertions: &[TermId],
    objective: TermId,
) -> Result<OptOutcome, SolverError> {
    minimize_bv_with_config(arena, assertions, objective, &SolverConfig::default())
}

/// Like [`minimize_bv`], but honoring `config` (notably `config.timeout`): every
/// feasibility probe is decided under `config`, and the binary search checks a
/// wall-clock deadline, returning [`OptOutcome::Unknown`] (a
/// [`UnknownKind::ResourceLimit`]) on expiry rather than running unbounded.
///
/// # Errors
///
/// See [`maximize_bv`].
pub fn minimize_bv_with_config(
    arena: &mut TermArena,
    assertions: &[TermId],
    objective: TermId,
    config: &SolverConfig,
) -> Result<OptOutcome, SolverError> {
    let deadline = deadline_from(config);
    bv_objective_max(arena, objective)?; // width check
    let v0 = match bv_value(arena, assertions, objective, None, config)? {
        BvProbe::Sat(value) => value,
        BvProbe::Unsat => return Ok(OptOutcome::Infeasible),
        BvProbe::Unknown(reason) => return Ok(OptOutcome::Unknown(reason)),
    };
    // Smallest k in [0, v0] with `objective <=u k` satisfiable.
    let mut lo = 0u128;
    let mut hi = v0;
    while lo < hi {
        if past_deadline(deadline) {
            return Ok(OptOutcome::Unknown(timed_out_reason()));
        }
        let mid = lo + (hi - lo) / 2;
        match bv_value(
            arena,
            assertions,
            objective,
            Some((BvRel::Ule, mid)),
            config,
        )? {
            BvProbe::Sat(value) => hi = value.min(mid),
            BvProbe::Unsat => lo = mid + 1,
            BvProbe::Unknown(reason) => return Ok(OptOutcome::Unknown(reason)),
        }
    }
    Ok(OptOutcome::Optimal(bv_to_i128(lo)?))
}

/// Maximizes the **signed** (two's-complement) value of bit-vector `objective`
/// subject to `assertions`.
///
/// # Errors
///
/// [`SolverError::Unsupported`] if `objective` is not a bit-vector of width
/// `<= 64`, or [`SolverError::Backend`] on an internal error.
pub fn maximize_bv_signed(
    arena: &mut TermArena,
    assertions: &[TermId],
    objective: TermId,
) -> Result<OptOutcome, SolverError> {
    maximize_bv_signed_with_config(arena, assertions, objective, &SolverConfig::default())
}

/// Like [`maximize_bv_signed`], but honoring `config` (notably `config.timeout`):
/// every feasibility probe is decided under `config`, and the binary search checks
/// a wall-clock deadline, returning [`OptOutcome::Unknown`] (a
/// [`UnknownKind::ResourceLimit`]) on expiry rather than running unbounded.
///
/// # Errors
///
/// See [`maximize_bv_signed`].
pub fn maximize_bv_signed_with_config(
    arena: &mut TermArena,
    assertions: &[TermId],
    objective: TermId,
    config: &SolverConfig,
) -> Result<OptOutcome, SolverError> {
    let deadline = deadline_from(config);
    let width = bv_signed_width(arena, objective)?;
    let (_, max_s) = bv_signed_range(width);
    let mut lo = match bv_value(arena, assertions, objective, None, config)? {
        BvProbe::Sat(raw) => bv_signed(raw, width),
        BvProbe::Unsat => return Ok(OptOutcome::Infeasible),
        BvProbe::Unknown(reason) => return Ok(OptOutcome::Unknown(reason)),
    };
    let mut hi = max_s;
    while lo < hi {
        if past_deadline(deadline) {
            return Ok(OptOutcome::Unknown(timed_out_reason()));
        }
        let mid = lo + (hi - lo + 1) / 2; // upper mid; width <= 64 avoids overflow
        match bv_value(
            arena,
            assertions,
            objective,
            Some((BvRel::Sge, signed_to_bits(mid, width))),
            config,
        )? {
            BvProbe::Sat(raw) => lo = bv_signed(raw, width).max(mid),
            BvProbe::Unsat => hi = mid - 1,
            BvProbe::Unknown(reason) => return Ok(OptOutcome::Unknown(reason)),
        }
    }
    Ok(OptOutcome::Optimal(lo))
}

/// Minimizes the **signed** (two's-complement) value of bit-vector `objective`
/// subject to `assertions`.
///
/// # Errors
///
/// See [`maximize_bv_signed`].
pub fn minimize_bv_signed(
    arena: &mut TermArena,
    assertions: &[TermId],
    objective: TermId,
) -> Result<OptOutcome, SolverError> {
    minimize_bv_signed_with_config(arena, assertions, objective, &SolverConfig::default())
}

/// Like [`minimize_bv_signed`], but honoring `config` (notably `config.timeout`):
/// every feasibility probe is decided under `config`, and the binary search checks
/// a wall-clock deadline, returning [`OptOutcome::Unknown`] (a
/// [`UnknownKind::ResourceLimit`]) on expiry rather than running unbounded.
///
/// # Errors
///
/// See [`maximize_bv_signed`].
pub fn minimize_bv_signed_with_config(
    arena: &mut TermArena,
    assertions: &[TermId],
    objective: TermId,
    config: &SolverConfig,
) -> Result<OptOutcome, SolverError> {
    let deadline = deadline_from(config);
    let width = bv_signed_width(arena, objective)?;
    let (min_s, _) = bv_signed_range(width);
    let mut hi = match bv_value(arena, assertions, objective, None, config)? {
        BvProbe::Sat(raw) => bv_signed(raw, width),
        BvProbe::Unsat => return Ok(OptOutcome::Infeasible),
        BvProbe::Unknown(reason) => return Ok(OptOutcome::Unknown(reason)),
    };
    let mut lo = min_s;
    while lo < hi {
        if past_deadline(deadline) {
            return Ok(OptOutcome::Unknown(timed_out_reason()));
        }
        let mid = lo + (hi - lo) / 2; // lower mid
        match bv_value(
            arena,
            assertions,
            objective,
            Some((BvRel::Sle, signed_to_bits(mid, width))),
            config,
        )? {
            BvProbe::Sat(raw) => hi = bv_signed(raw, width).min(mid),
            BvProbe::Unsat => lo = mid + 1,
            BvProbe::Unknown(reason) => return Ok(OptOutcome::Unknown(reason)),
        }
    }
    Ok(OptOutcome::Optimal(lo))
}

/// The width of a signed-optimization objective (a bit-vector of width `<= 64`).
fn bv_signed_width(arena: &TermArena, objective: TermId) -> Result<u32, SolverError> {
    match arena.sort_of(objective) {
        Sort::BitVec(width) if width <= 64 => Ok(width),
        Sort::BitVec(width) => Err(SolverError::Unsupported(format!(
            "signed bit-vector optimization objective width {width} exceeds 64"
        ))),
        other => Err(SolverError::Unsupported(format!(
            "signed bit-vector optimization objective is not a bit-vector (got {other:?})"
        ))),
    }
}

/// Converts an unsigned optimum to `i128` (always succeeds for width <= 127,
/// which the callers enforce via [`bv_objective_max`]).
fn bv_to_i128(value: u128) -> Result<i128, SolverError> {
    i128::try_from(value).map_err(|_| {
        SolverError::Backend("bit-vector optimum exceeds the i128 result range".to_string())
    })
}

/// A bit-vector bound relation for an optimization probe (unsigned or signed).
#[derive(Clone, Copy)]
enum BvRel {
    Uge,
    Ule,
    Sge,
    Sle,
}

/// Interprets a width-`w` bit pattern as a two's-complement signed value (sign-
/// extended from `w` to 128 bits). Every such value fits `i128` for `w <= 128`.
fn bv_signed(value: u128, width: u32) -> i128 {
    let bits = i128::from_ne_bytes(value.to_ne_bytes());
    if width >= 128 {
        return bits;
    }
    // Sign-extend bit `width - 1` to bit 127 via a left-then-arithmetic-right
    // shift; both shift amounts are < 128.
    let shift = 128 - width;
    (bits << shift) >> shift
}

/// The two's-complement `width`-bit pattern of a signed value, as `u128`.
fn signed_to_bits(value: i128, width: u32) -> u128 {
    let raw = u128::from_ne_bytes(value.to_ne_bytes());
    if width >= 128 {
        raw
    } else {
        raw & ((1u128 << width) - 1)
    }
}

/// The inclusive signed range `[min, max]` of a width-`w` bit-vector.
fn bv_signed_range(width: u32) -> (i128, i128) {
    if width >= 128 {
        return (i128::MIN, i128::MAX);
    }
    let max = (1i128 << (width - 1)) - 1;
    let min = -(1i128 << (width - 1));
    (min, max)
}

/// The maximum unsigned value of `objective`'s sort (and a width check).
fn bv_objective_max(arena: &TermArena, objective: TermId) -> Result<u128, SolverError> {
    match arena.sort_of(objective) {
        Sort::BitVec(width) if width <= 127 => {
            Ok(if width == 0 { 0 } else { (1u128 << width) - 1 })
        }
        Sort::BitVec(width) => Err(SolverError::Unsupported(format!(
            "bit-vector optimization objective width {width} exceeds 127"
        ))),
        other => Err(SolverError::Unsupported(format!(
            "bit-vector optimization objective is not a bit-vector (got {other:?})"
        ))),
    }
}

/// One bit-vector feasibility probe result, carrying the objective's unsigned
/// value in the found model.
enum BvProbe {
    Sat(u128),
    Unsat,
    Unknown(UnknownReason),
}

/// Decides `assertions` (optionally with an unsigned bound on `objective`) via
/// the eager bit-vector dispatcher and returns the objective's value.
fn bv_value(
    arena: &mut TermArena,
    assertions: &[TermId],
    objective: TermId,
    bound: Option<(BvRel, u128)>,
    config: &SolverConfig,
) -> Result<BvProbe, SolverError> {
    let Sort::BitVec(width) = arena.sort_of(objective) else {
        unreachable!("bv_value called on a non-bit-vector objective")
    };
    let mut query = assertions.to_vec();
    if let Some((rel, value)) = bound {
        let bound_term = arena.bv_const(width, value)?;
        let constraint = match rel {
            BvRel::Uge => arena.bv_uge(objective, bound_term)?,
            BvRel::Ule => arena.bv_ule(objective, bound_term)?,
            BvRel::Sge => arena.bv_sge(objective, bound_term)?,
            BvRel::Sle => arena.bv_sle(objective, bound_term)?,
        };
        query.push(constraint);
    }
    match crate::auto::solve(arena, &query, config)? {
        CheckResult::Sat(model) => {
            let assignment = model.to_assignment();
            match eval(arena, objective, &assignment)? {
                Value::Bv { value, .. } => Ok(BvProbe::Sat(value)),
                other => Err(SolverError::Backend(format!(
                    "bv optimization objective evaluated to a non-bit-vector ({other:?})"
                ))),
            }
        }
        CheckResult::Unsat => Ok(BvProbe::Unsat),
        CheckResult::Unknown(reason) => Ok(BvProbe::Unknown(reason)),
    }
}
