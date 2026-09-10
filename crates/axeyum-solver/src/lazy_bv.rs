//! Low-memory lazy abstraction-refinement BV strategy (ADR-0019).
//!
//! The eager bit-blaster's memory is dominated by **multiplier and divider
//! circuits** (a width-`w` `bvmul` is a quadratic shift-and-add; the
//! `bvudiv`/`bvurem` family is a per-bit restoring divider — both are the
//! heaviest gadgets, measured at thousands of AIG AND-nodes each). This strategy
//! avoids materializing them unless they matter:
//!
//! 1. **Abstract** every heavy subterm — `bvmul`, `bvudiv`, `bvurem`, `bvsdiv`,
//!    `bvsrem`, `bvsmod` — by a fresh, unconstrained variable of the same sort.
//!    Dropping the defining constraint *enlarges* the solution set, so the
//!    abstraction is a sound **over-approximation**.
//! 2. **Solve** the (much smaller) abstraction with the eager pure-Rust path.
//!    - `unsat` ⇒ the original is `unsat` (over-approximation), with **no heavy
//!      gadget ever bit-blasted**.
//!    - `sat` ⇒ **replay** the original assertions under the model. If they hold,
//!      it is a genuine model. Otherwise the abstraction exploited a fresh
//!      variable whose value differs from the real operation result: **refine**
//!      those operations by adding their exact `fresh == op(lhs, rhs)` constraint
//!      (bit-blasting only those), and re-solve.
//!
//! Refinement only ever adds operations, so after at most one round per heavy
//! gadget the problem is fully precise (equivalent to the eager strategy): the
//! loop is **sound, complete, and terminating**, with memory ≤ eager and often
//! far less. Every `sat` is replayed (the trust anchor); `unsat` is sound by the
//! over-approximation argument and cross-checked against the eager strategy in
//! tests.

use std::collections::{HashMap, HashSet};

use axeyum_ir::{Op, TermArena, TermId, TermNode, Value, eval};
use axeyum_rewrite::replace_subterms;

use crate::auto::solve;
use crate::backend::{
    Capabilities, CheckResult, SolveStats, SolverBackend, SolverConfig, SolverError, UnknownKind,
    UnknownReason,
};
use crate::model::Model;

const FRESH_PREFIX: &str = "!lazy_op_";

/// The outcome of [`solve_lazy_bv_abstraction`], with refinement telemetry that
/// quantifies how much bit-blasting the abstraction avoided.
#[derive(Debug)]
pub struct LazyBvOutcome {
    /// The decision (every `sat` already replayed against the original query).
    pub result: CheckResult,
    /// Distinct heavy operations (`bvmul`/`bvudiv`/…) found in the query.
    pub ops_total: usize,
    /// How many of them had to be refined (exactly bit-blasted). `0` means the
    /// verdict was reached without materializing a single heavy gadget.
    pub ops_refined: usize,
    /// Abstraction-refinement rounds taken.
    pub rounds: usize,
}

/// Decides `assertions` with the lazy abstraction-refinement strategy, returning
/// only the [`CheckResult`].
///
/// # Errors
///
/// Returns [`SolverError`] from the eager sub-solver or on a replay soundness
/// alarm.
pub fn check_lazy_bv_abstraction(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    Ok(solve_lazy_bv_abstraction(arena, assertions, config)?.result)
}

/// Read-only variant of [`solve_lazy_bv_abstraction`]: decides `assertions`
/// without mutating the caller's arena, so it fits the `&TermArena` consumers
/// (the [`crate::SolverBackend`] trait, the bench pipeline) that cannot hand out
/// a `&mut` arena.
///
/// The strategy needs to declare fresh abstraction symbols, so this runs it on a
/// disposable [`TermArena::clone`] (an identical arena where the input
/// `TermId`s/`SymbolId`s stay valid). The returned model is already restricted
/// to the original (non-`!lazy_op_*`) symbols, so it replays against the caller's
/// arena unchanged. Sound for the same reasons as the mutable version:
/// over-approximation for `unsat`, replay-checked `sat`.
///
/// # Errors
///
/// Returns [`SolverError`] from the eager sub-solver or on a replay soundness
/// alarm.
pub fn check_lazy_bv_abstraction_ro(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<LazyBvOutcome, SolverError> {
    let mut scratch = arena.clone();
    solve_lazy_bv_abstraction(&mut scratch, assertions, config)
}

/// Decides `assertions` with the lazy abstraction-refinement strategy, returning
/// the full [`LazyBvOutcome`] (verdict + telemetry).
///
/// # Errors
///
/// Returns [`SolverError`] from the eager sub-solver or on a replay soundness
/// alarm.
pub fn solve_lazy_bv_abstraction(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<LazyBvOutcome, SolverError> {
    let ops = collect_heavy_ops(arena, assertions, config.lazy_bv_abstract_ite);
    if ops.is_empty() {
        // Nothing to abstract; the eager strategy is already minimal here.
        let result = solve(arena, assertions, config)?;
        return Ok(LazyBvOutcome {
            result,
            ops_total: 0,
            ops_refined: 0,
            rounds: 1,
        });
    }

    // Fresh variable per heavy op; `replacements` maps each op term to its
    // abstraction variable, `fresh_sym` remembers the symbol for model lookups.
    let mut replacements: HashMap<TermId, TermId> = HashMap::new();
    let mut fresh_sym: HashMap<TermId, axeyum_ir::SymbolId> = HashMap::new();
    for (i, &op_term) in ops.iter().enumerate() {
        let sort = arena.sort_of(op_term);
        let sym = arena.declare_internal(&format!("{FRESH_PREFIX}{i}"), sort)?;
        let var = arena.var(sym);
        replacements.insert(op_term, var);
        fresh_sym.insert(op_term, sym);
    }

    // Abstracted assertions (every heavy op replaced by its fresh variable).
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut abstracted = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        abstracted.push(replace_subterms(
            arena,
            assertion,
            &replacements,
            &mut memo,
        )?);
    }

    let mut refined: HashSet<TermId> = HashSet::new();
    let max_rounds = ops.len() + 1;
    for round in 1..=max_rounds {
        let constraints = round_constraints(arena, &abstracted, &ops, &refined, &replacements)?;
        match solve(arena, &constraints, config)? {
            CheckResult::Unsat => {
                return Ok(outcome(CheckResult::Unsat, &ops, &refined, round));
            }
            CheckResult::Unknown(reason) => {
                return Ok(outcome(CheckResult::Unknown(reason), &ops, &refined, round));
            }
            CheckResult::Sat(model) => {
                let assignment = model.to_assignment();
                if replay_holds(arena, assertions, &assignment)? {
                    let restricted = restrict_model(arena, &model);
                    return Ok(outcome(CheckResult::Sat(restricted), &ops, &refined, round));
                }
                // Spurious: refine every unrefined op whose abstraction value
                // disagrees with its real result under this model.
                let mut progressed = false;
                for &op_term in &ops {
                    if refined.contains(&op_term) {
                        continue;
                    }
                    let fresh_value = model.get(fresh_sym[&op_term]);
                    let real_value = eval(arena, op_term, &assignment)?;
                    if fresh_value.as_ref() != Some(&real_value) {
                        refined.insert(op_term);
                        progressed = true;
                    }
                }
                if !progressed {
                    return Err(SolverError::Backend(
                        "lazy-bv: original replay failed but every heavy op was \
                         consistent with its abstraction (soundness bug)"
                            .to_string(),
                    ));
                }
            }
        }
    }

    // Unreachable in principle (after all ops refine the problem is exact), but
    // bounded for safety: report `unknown`, never a wrong verdict.
    Ok(outcome(
        CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::Incomplete,
            detail: format!("lazy-bv abstraction exceeded {max_rounds} refinement rounds"),
        }),
        &ops,
        &refined,
        max_rounds,
    ))
}

fn outcome(
    result: CheckResult,
    ops: &[TermId],
    refined: &HashSet<TermId>,
    rounds: usize,
) -> LazyBvOutcome {
    LazyBvOutcome {
        result,
        ops_total: ops.len(),
        ops_refined: refined.len(),
        rounds,
    }
}

/// The eager problem for one refinement round: the abstraction plus the exact
/// `fresh == op(args…)` definition of every already-refined heavy op.
fn round_constraints(
    arena: &mut TermArena,
    abstracted: &[TermId],
    ops: &[TermId],
    refined: &HashSet<TermId>,
    replacements: &HashMap<TermId, TermId>,
) -> Result<Vec<TermId>, SolverError> {
    let mut constraints = abstracted.to_vec();
    for &op_term in ops {
        if !refined.contains(&op_term) {
            continue;
        }
        let (op, args) = op_and_args(arena, op_term);
        let mut rmemo: HashMap<TermId, TermId> = HashMap::new();
        let mut abs_args = Vec::with_capacity(args.len());
        for &arg in &args {
            abs_args.push(replace_subterms(arena, arg, replacements, &mut rmemo)?);
        }
        let exact = rebuild_op(arena, op, &abs_args)?;
        let fresh = replacements[&op_term];
        constraints.push(arena.eq(fresh, exact)?);
    }
    Ok(constraints)
}

/// Whether `op` is a heavy gadget worth abstracting. `include_ite` extends the
/// set to `ite` (gated by [`SolverConfig::lazy_bv_abstract_ite`]); the BV-sort
/// restriction is applied by the caller ([`collect_heavy_ops`]).
fn is_heavy(op: Op, include_ite: bool) -> bool {
    matches!(
        op,
        Op::BvMul | Op::BvUdiv | Op::BvUrem | Op::BvSdiv | Op::BvSrem | Op::BvSmod
    ) || (include_ite && matches!(op, Op::Ite))
}

/// Whether `assertions` contain any heavy *arithmetic* gadget (`bvmul`/`bvudiv`/
/// …) — the signal the [`crate::Strategy::Auto`] selector uses to prefer the
/// low-memory abstraction strategy. (`ite` is never counted here: it is the
/// opt-in experimental extension, not an auto-selection trigger.)
pub(crate) fn has_heavy_ops(arena: &TermArena, assertions: &[TermId]) -> bool {
    !collect_heavy_ops(arena, assertions, false).is_empty()
}

/// Distinct heavy-op subterms in `assertions`, in deterministic first-seen order.
/// Only BV-sorted terms are abstracted (a fresh BV variable stands in for them);
/// this also keeps `ite` abstraction to the bit-vector branches, never Boolean
/// `ite` (whose blasting is already cheap).
fn collect_heavy_ops(arena: &TermArena, assertions: &[TermId], include_ite: bool) -> Vec<TermId> {
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut ops = Vec::new();
    let mut stack: Vec<TermId> = assertions.iter().rev().copied().collect();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if is_heavy(*op, include_ite) && arena.sort_of(term).bv_width().is_some() {
                ops.push(term);
            }
            for &arg in args.iter().rev() {
                stack.push(arg);
            }
        }
    }
    ops
}

/// The operator and operands of an abstractable heavy-op term (binary for the
/// arithmetic gadgets, ternary for `ite`).
fn op_and_args(arena: &TermArena, term: TermId) -> (Op, Vec<TermId>) {
    match arena.node(term) {
        TermNode::App { op, args } => (*op, args.to_vec()),
        _ => unreachable!("op_and_args called on a non-application term"),
    }
}

/// Rebuilds the exact heavy operation over (possibly abstracted) operands.
fn rebuild_op(arena: &mut TermArena, op: Op, args: &[TermId]) -> Result<TermId, SolverError> {
    let result = match op {
        Op::BvMul => arena.bv_mul(args[0], args[1])?,
        Op::BvUdiv => arena.bv_udiv(args[0], args[1])?,
        Op::BvUrem => arena.bv_urem(args[0], args[1])?,
        Op::BvSdiv => arena.bv_sdiv(args[0], args[1])?,
        Op::BvSrem => arena.bv_srem(args[0], args[1])?,
        Op::BvSmod => arena.bv_smod(args[0], args[1])?,
        Op::Ite => arena.ite(args[0], args[1], args[2])?,
        _ => unreachable!("rebuild_op called on a non-heavy op"),
    };
    Ok(result)
}

/// Whether every assertion evaluates to `true` under `assignment`.
fn replay_holds(
    arena: &TermArena,
    assertions: &[TermId],
    assignment: &axeyum_ir::Assignment,
) -> Result<bool, SolverError> {
    for &assertion in assertions {
        if eval(arena, assertion, assignment)? != Value::Bool(true) {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Copies `model` without the internal `!lazy_op_*` abstraction variables.
///
/// Roadmap 2.11. `replay_holds` above checks the ORIGINAL assertions against
/// `model.to_assignment()` — the full inner model — and this then emitted a
/// narrower one: the rebuild carried entries and functions and dropped
/// `real_div_zero`, `uninterpreted_cardinalities` and the quantified sat
/// certificates. The last two are invisible to a re-replay through
/// `to_assignment`, so this narrows through `Model::retain_symbols`, which
/// cannot drop a component, rather than adding a guard that could not fail on
/// them.
fn restrict_model(arena: &TermArena, model: &Model) -> Model {
    let mut out = model.clone();
    out.retain_symbols(|symbol| !arena.symbol(symbol).0.starts_with(FRESH_PREFIX));
    out
}

/// A [`SolverBackend`] that decides via the P2.1 lazy abstraction-refinement
/// (CEGAR) bit-blasting strategy (ADR-0019) instead of eager bit-blasting:
/// heavy gadgets (`bvmul`/`bvudiv`/…) are abstracted by fresh variables, the
/// small abstraction is solved, and only the operations a candidate model
/// violates are exactly bit-blasted, to a fixpoint.
///
/// It runs through [`check_lazy_bv_abstraction_ro`], so it honors the
/// `&TermArena` trait contract (no caller-arena mutation). The refinement
/// telemetry (`lazy_ops_total`/`lazy_ops_refined`/`lazy_rounds`) is exposed via
/// [`SolverBackend::last_stats`] for the bench. This is the measurement vehicle
/// for the public-QF_BV lazy-vs-eager comparison; it is sound for the same
/// reasons as the strategy (over-approximation `unsat`, replay-checked `sat`).
#[derive(Debug, Default)]
pub struct LazyBvBackend {
    stats: Option<SolveStats>,
    abstract_ite: bool,
}

impl LazyBvBackend {
    /// Creates a lazy-bit-blasting backend (arithmetic gadgets only).
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Also abstract BV-sorted `ite` (P2.1 lever #3). See
    /// [`SolverConfig::lazy_bv_abstract_ite`].
    #[must_use]
    pub fn with_abstract_ite(mut self, abstract_ite: bool) -> Self {
        self.abstract_ite = abstract_ite;
        self
    }
}

impl SolverBackend for LazyBvBackend {
    fn capabilities(&self) -> Capabilities {
        Capabilities {
            name: "axeyum-lazy-bv (CEGAR abstraction-refinement)".to_owned(),
            produces_models: true,
            complete: true,
        }
    }

    fn check(
        &mut self,
        arena: &TermArena,
        assertions: &[TermId],
        config: &SolverConfig,
    ) -> Result<CheckResult, SolverError> {
        // Clear the lazy flag on the inner config so the eager sub-solves inside
        // the strategy never re-enter the `auto::solve` lazy dispatch; carry the
        // backend's ite-abstraction choice (OR'd with whatever the config asked).
        let inner = config
            .clone()
            .with_lazy_bv(false)
            .with_lazy_bv_abstract_ite(self.abstract_ite || config.lazy_bv_abstract_ite);
        let outcome = check_lazy_bv_abstraction_ro(arena, assertions, &inner)?;
        let mut stats = SolveStats {
            assertion_count: usize_to_u64(assertions.len()),
            ..SolveStats::default()
        };
        stats
            .backend
            .push(("lazy_ops_total".to_owned(), usize_to_f64(outcome.ops_total)));
        stats.backend.push((
            "lazy_ops_refined".to_owned(),
            usize_to_f64(outcome.ops_refined),
        ));
        stats
            .backend
            .push(("lazy_rounds".to_owned(), usize_to_f64(outcome.rounds)));
        self.stats = Some(stats);
        Ok(outcome.result)
    }

    fn last_stats(&self) -> Option<&SolveStats> {
        self.stats.as_ref()
    }
}

/// Telemetry-count conversion (a count never loses meaningful precision in `f64`).
#[allow(clippy::cast_precision_loss)]
fn usize_to_f64(value: usize) -> f64 {
    value as f64
}

/// Telemetry-count conversion (`usize` ≤ `u64` on supported targets).
#[allow(clippy::cast_possible_truncation)]
fn usize_to_u64(value: usize) -> u64 {
    value as u64
}

/// Roadmap 2.11 — this file's narrowing site, `restrict_model`.
///
/// Item 2.11 names `lazy_bv.rs:323` as one of two sites where SOUND-1's guard 2
/// (re-replay against `Model::to_assignment`) **cannot** be the fix.
/// `replay_holds` above checks the caller's assertions against
/// `model.to_assignment()` — the full inner model — and `restrict_model` then
/// emitted a narrower one. Two of the things it dropped,
/// `uninterpreted_cardinalities` and the quantified sat certificates, are not
/// components an `Assignment` can hold, so a re-replay through `to_assignment`
/// is structurally incapable of noticing they are gone. That is a check that
/// cannot fail on the defect the site has, which this repository rates as worse
/// than no check.
///
/// So the fix here is a *carry*, not a *guard*: narrowing goes through
/// `Model::retain_symbols`, which starts from the whole model. The test below
/// is what makes that claim falsifiable at this site rather than only at the
/// helper.
#[cfg(test)]
mod sound2_narrowing_site_tests {
    use super::{FRESH_PREFIX, restrict_model};
    use crate::model::Model;
    use crate::quant_sat_certificates::{AffineSkolemWitness, QuantifiedSkolemSatCertificate};
    use axeyum_ir::{Rational, Sort, TermArena, Value};

    /// DIES ON: rebuilding the emitted model in `restrict_model` instead of
    /// narrowing the one that was replayed.
    #[test]
    fn restrict_model_keeps_every_component_the_replay_saw() {
        let mut arena = TermArena::new();
        let user = arena.declare("x", Sort::BitVec(8)).expect("declare x");
        let fresh = arena
            .declare_internal(&format!("{FRESH_PREFIX}0"), Sort::BitVec(8))
            .expect("declare fresh");
        let opaque = arena.declare_uninterpreted_sort("U");
        let assertion = arena.var(user);

        let mut inner = Model::new();
        inner.set(user, Value::Bv { width: 8, value: 3 });
        inner.set(fresh, Value::Bv { width: 8, value: 9 });
        inner.set_real_div_zero(Rational::integer(5), Rational::integer(100));
        inner.set_uninterpreted_cardinality(opaque, 3);
        inner.set_quantified_sat_certificate(QuantifiedSkolemSatCertificate {
            assertion,
            universals: vec![user],
            existential: fresh,
            witness: AffineSkolemWitness {
                terms: Vec::new(),
                constant: Rational::integer(1),
            },
        });

        let restricted = restrict_model(&arena, &inner);

        // The abstraction variable is the only thing that may be gone.
        assert_eq!(restricted.get(fresh), None, "the `!lazy_op_` variable");
        assert_eq!(
            restricted.get(user),
            Some(Value::Bv { width: 8, value: 3 }),
            "x"
        );

        // The two components `Model::to_assignment` cannot express, and which a
        // guard-2 re-replay is therefore blind to. These are the assertions that
        // make this site's fix a carry rather than a check.
        assert_eq!(
            restricted.uninterpreted_cardinality(opaque),
            Some(3),
            "the declared carrier size did not survive narrowing — and no replay \
             through `to_assignment` would have told you"
        );
        assert_eq!(
            restricted.quantified_sat_certificates().count(),
            1,
            "the checked quantified certificate did not survive narrowing — and no \
             replay through `to_assignment` would have told you"
        );
        assert_eq!(
            restricted.real_div_zero(Rational::integer(5)),
            Some(Rational::integer(100)),
            "the division-at-zero witness did not survive narrowing"
        );
    }
}
