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

use crate::backend::{CheckResult, SolverConfig, SolverError};

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
            #[cfg(feature = "z3")]
            Strategy::Oracle => "oracle-z3",
        }
    }

    /// Whether the strategy is part of the pure-Rust (no C/C++) stack.
    pub fn is_pure_rust(self) -> bool {
        match self {
            Strategy::EagerPureRust | Strategy::LazyBvAbstraction => true,
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
        #[cfg(feature = "z3")]
        Strategy::Oracle => solve_with_oracle(arena, assertions, config),
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
