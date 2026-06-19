//! Swappable solving strategies (ADR-0019).
//!
//! A [`Strategy`] is a named solving policy. Every strategy consumes the same
//! IR and [`SolverConfig`] and returns the same [`CheckResult`], and every
//! `sat` is replayed through the ground evaluator against the original
//! assertions — so strategies are interchangeable *and* cross-validatable
//! (running two and diffing verdicts is a first-class operation, the project's
//! "untrusted fast search, trusted small checking" identity applied across
//! engines).
//!
//! Strategies differ only in the memory/completeness/speed tradeoff of *how*
//! they decide:
//!
//! - [`Strategy::EagerPureRust`] — the pure-Rust eager bit-blast + theory
//!   elimination pipeline ([`crate::solve`]). High-memory, complete for `QF_BV`
//!   and the eager-reducible theories, fully checkable. The default, and the
//!   only strategy in the no-C build.
//! - [`Strategy::Oracle`] *(feature `z3`)* — Z3 as a low-memory reference
//!   strategy, selectable for comparison and cross-validation. Not pure-Rust;
//!   its `sat` is still replayed for parity. Its role stays bootstrap/oracle
//!   per ADR-0002 — the default build never requires it.
//!
//! Future low-memory pure-Rust strategies (abstraction-refinement bit-blasting,
//! a native BV theory solver) land behind this same entry point and discipline.
//! See the
//! [solving-strategies note](../../docs/research/03-architecture/solving-strategies-and-memory-model.md).

use axeyum_ir::{TermArena, TermId};
#[cfg(feature = "z3")]
use axeyum_ir::{Value, eval};

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};

/// A named solving policy; see the module-level documentation.
///
/// `#[non_exhaustive]`: more strategies (a low-memory pure-Rust engine, an
/// `Auto` selector) will be added without a breaking change.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum Strategy {
    /// High-memory, pure-Rust eager bit-blast + theory elimination. Default.
    #[default]
    EagerPureRust,
    /// Low-memory, pure-Rust lazy abstraction-refinement: abstracts the heavy
    /// gadgets (`bvmul` and the `bvudiv`/`bvurem`/`bvsdiv`/`bvsrem`/`bvsmod`
    /// family) to fresh variables and refines on demand, so multipliers and
    /// dividers are bit-blasted only when they affect the verdict (ADR-0019).
    /// Sound and complete; `sat` replayed, `unsat` sound by over-approximation.
    LazyBvAbstraction,
    /// Feature-routed selector composing both measured destination-2 levers
    /// (ADR-0037): when the query contains heavy arithmetic gadgets
    /// (`bvmul`/`bvudiv`/…) use [`Strategy::LazyBvAbstraction`] (CEGAR over the
    /// multipliers); otherwise the query is *structural* bit-logic, where the
    /// eager-CNF-size wall is the bottleneck — so run eager **with word-level
    /// preprocessing on** (the full model-sound reduction pipeline), which on the
    /// public p4dfa slice decided 4/113 @3s and 7/113 @20s vs eager's 2/3.
    /// Both branches are sound (`sat` replayed, `unsat` sound); this routes by the
    /// measured shape of the bottleneck, not a cost model.
    Auto,
    /// Low-memory reference oracle (Z3); `sat` is replayed for parity.
    #[cfg(feature = "z3")]
    Oracle,
}

impl Strategy {
    /// A stable, human-readable name for the strategy.
    pub fn name(self) -> &'static str {
        match self {
            Strategy::EagerPureRust => "eager-pure-rust",
            Strategy::LazyBvAbstraction => "lazy-bv-abstraction",
            Strategy::Auto => "auto",
            #[cfg(feature = "z3")]
            Strategy::Oracle => "oracle-z3",
        }
    }

    /// Whether the strategy is part of the pure-Rust (no C/C++) stack.
    pub fn is_pure_rust(self) -> bool {
        match self {
            Strategy::EagerPureRust | Strategy::LazyBvAbstraction | Strategy::Auto => true,
            #[cfg(feature = "z3")]
            Strategy::Oracle => false,
        }
    }
}

/// Decides `assertions` with the chosen [`Strategy`].
///
/// The returned [`CheckResult`] has the same meaning for every strategy; any
/// `sat` model has been replayed through the ground evaluator against the
/// original assertions before it is returned, so no strategy can yield an
/// unsound `sat`.
///
/// # Errors
///
/// Returns [`SolverError`] from the chosen engine (e.g.
/// [`SolverError::Unsupported`] for constructs outside a strategy's fragment,
/// or [`SolverError::Backend`] on a replay/soundness alarm).
pub fn solve_with_strategy(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    strategy: Strategy,
) -> Result<CheckResult, SolverError> {
    match strategy {
        Strategy::EagerPureRust => crate::auto::solve(arena, assertions, config),
        Strategy::LazyBvAbstraction => {
            crate::lazy_bv::check_lazy_bv_abstraction(arena, assertions, config)
        }
        Strategy::Auto => {
            if crate::lazy_bv::has_heavy_ops(arena, assertions) {
                crate::lazy_bv::check_lazy_bv_abstraction(arena, assertions, config)
            } else {
                // Structural bit-logic: the eager-CNF-size wall is the bottleneck,
                // and word-level reduction is the measured lever (ADR-0037). Turn
                // preprocessing on for this branch (idempotent if already set);
                // it is model-sound and replay-checked, so `sat`/`unsat` are
                // unaffected — only the encoding shrinks.
                let preprocessed = config.clone().with_preprocess(true);
                crate::auto::solve(arena, assertions, &preprocessed)
            }
        }
        #[cfg(feature = "z3")]
        Strategy::Oracle => solve_with_oracle(arena, assertions, config),
    }
}

/// Run `strategies` in order, returning the **first that decides** (`Sat`/`Unsat`);
/// if none decides, return an `Unknown` (or, if every strategy errored and none even
/// returned `Unknown`, the last error). This is Z3's `or-else` tactic combinator:
/// because every strategy is sound and a later one runs *only* when earlier ones
/// returned `Unknown`/errored, the first decided verdict is sound and trying more
/// never trades correctness for coverage.
///
/// Use [`recommended_portfolio`] to order strategies by the query's shape, or pass an
/// explicit list. A `sat` result has already been replayed by the deciding strategy.
///
/// # Errors
///
/// Returns [`SolverError`] only when *every* strategy errored without any returning a
/// verdict or `Unknown` (the last error is surfaced); an empty `strategies` list
/// yields `Unknown`, never an error.
pub fn solve_with_portfolio(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    strategies: &[Strategy],
) -> Result<CheckResult, SolverError> {
    let mut last_unknown: Option<CheckResult> = None;
    let mut last_error: Option<SolverError> = None;
    for &strategy in strategies {
        match solve_with_strategy(arena, assertions, config, strategy) {
            Ok(decided @ (CheckResult::Sat(_) | CheckResult::Unsat)) => return Ok(decided),
            Ok(unknown) => last_unknown = Some(unknown),
            Err(error) => last_error = Some(error),
        }
    }
    last_unknown.map_or_else(
        || {
            last_error.map_or_else(
                || {
                    Ok(CheckResult::Unknown(UnknownReason {
                        kind: UnknownKind::Incomplete,
                        detail: "empty strategy portfolio".to_owned(),
                    }))
                },
                Err,
            )
        },
        Ok,
    )
}

/// Order strategies by the query's shape for [`solve_with_portfolio`]: a query with
/// heavy arithmetic gadgets tries the low-memory [`Strategy::LazyBvAbstraction`]
/// first (it sidesteps multiplier bit-blasting) and falls back to the complete
/// [`Strategy::EagerPureRust`]; an arithmetic-free *structural* query uses
/// [`Strategy::Auto`] (eager with word-level preprocessing). Both are pure-Rust and
/// sound; the portfolio's fallback adds power over a single [`Strategy::Auto`] pick
/// when the first choice exhausts its budget and returns `Unknown`.
#[must_use]
pub fn recommended_portfolio(arena: &TermArena, assertions: &[TermId]) -> Vec<Strategy> {
    if crate::lazy_bv::has_heavy_ops(arena, assertions) {
        vec![Strategy::LazyBvAbstraction, Strategy::EagerPureRust]
    } else {
        vec![Strategy::Auto]
    }
}

/// Runs the Z3 oracle strategy and replays any `sat` model for parity with the
/// pure-Rust strategies' trust discipline.
#[cfg(feature = "z3")]
fn solve_with_oracle(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    use crate::backend::SolverBackend;
    let mut backend = crate::z3_backend::Z3Backend::new();
    let result = backend.check(arena, assertions, config)?;
    if let CheckResult::Sat(model) = &result {
        replay_sat(arena, assertions, model)?;
    }
    Ok(result)
}

/// Replays a `sat` model through the ground evaluator; a non-`true` assertion is
/// a soundness alarm, reported as [`SolverError::Backend`].
#[cfg(feature = "z3")]
fn replay_sat(
    arena: &TermArena,
    assertions: &[TermId],
    model: &crate::model::Model,
) -> Result<(), SolverError> {
    let assignment = model.to_assignment();
    for &assertion in assertions {
        match eval(arena, assertion, &assignment) {
            Ok(Value::Bool(true)) => {}
            Ok(_) => {
                return Err(SolverError::Backend(format!(
                    "oracle strategy sat model replay failed: assertion #{} not satisfied",
                    assertion.index()
                )));
            }
            Err(error) => {
                return Err(SolverError::Backend(format!(
                    "oracle strategy sat model replay error on assertion #{}: {error}",
                    assertion.index()
                )));
            }
        }
    }
    Ok(())
}
