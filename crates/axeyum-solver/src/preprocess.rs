//! Word-level preprocessing before solving (Track 1, P1.2).
//!
//! [`check_with_preprocessing`] shrinks a conjunction *before* it reaches a
//! backend by running the model-sound term-level passes — `propagate_values`
//! (pin `x = c`), `solve_eqs` (substitute `x = t`), then `elim_unconstrained`
//! (drop invertible-op layers off single-use variables) — composing their
//! [`ModelReconstructionTrail`]s. The backend then solves the smaller,
//! variable-reduced problem; on `sat` the trail reconstructs the eliminated
//! variables and the result is replayed against the **original** assertions, so
//! the returned [`Model`] is over the original query.
//!
//! This must run where the arena is mutable (the passes build substituted terms),
//! so it wraps the backend at the façade layer rather than living inside a
//! [`SolverBackend`], whose `check` takes an immutable arena. It mirrors
//! [`crate::check_with_array_elimination`].

use std::time::Duration;

use axeyum_ir::{Assignment, TermArena, TermId, Value, eval};
use axeyum_rewrite::{
    DEFAULT_SOLVE_EQS_FUEL, ModelReconstructionTrail, canonicalize_terms, elim_unconstrained,
    propagate_values, solve_eqs_bounded,
};

use crate::backend::{CheckResult, SolverBackend, SolverConfig, SolverError};
use crate::model::Model;

/// Maximum word-level reduction rounds before bit-blasting. Each round runs the
/// model-sound passes once; the loop stops early at a fixpoint (a round that
/// eliminates nothing). A small deterministic cap bounds the cost — fixpoints on
/// real corpora converge in 2–3 rounds; this only guards a pathological oscillation.
const MAX_PREPROCESS_ROUNDS: usize = 8;

/// Checks `assertions` with `backend` after model-sound word-level preprocessing.
///
/// # Errors
///
/// Returns [`SolverError`] from the backend, or [`SolverError::Backend`] if model
/// reconstruction or the original-assertion replay fails (a soundness alarm).
pub fn check_with_preprocessing<B: SolverBackend>(
    backend: &mut B,
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    check_with_preprocessing_impl(backend, arena, assertions, config, None)
}

pub(crate) fn check_with_preprocessing_and_local_search<B: SolverBackend>(
    backend: &mut B,
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    local_search_timeout: Duration,
) -> Result<CheckResult, SolverError> {
    check_with_preprocessing_impl(
        backend,
        arena,
        assertions,
        config,
        Some(local_search_timeout),
    )
}

fn check_with_preprocessing_impl<B: SolverBackend>(
    backend: &mut B,
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    local_search_timeout: Option<Duration>,
) -> Result<CheckResult, SolverError> {
    // Iterate the model-sound reductions to a FIXPOINT (Track 1 perf lever — deeper
    // reduction removes more variables before bit-blasting, which is what relieves
    // the encode budget on real corpora). One pass is not enough: `elim_unconstrained`
    // can expose a fresh constant that `propagate_values`/`solve_eqs` then eliminate,
    // and the re-canonicalization AC-normalizes substituted product trees that reveal
    // further folds. Each pass is model-sound and contributes a reconstruction trail;
    // they compose in pass/round order (reconstructed in reverse). The final replay
    // against the ORIGINAL assertions (below) is the trust anchor — any trail/round
    // composition bug surfaces there as an `Err`, never a wrong `sat`.
    //
    // Canonicalize first: a denotation- and symbol-preserving normalization (e.g.
    // commutative-operand ordering, so `(= (bvmul a b) (bvmul b a))` folds to `true`
    // with no bit-blasting). It eliminates no variables, so it needs no trail.
    let mut reduced = canonicalize_terms(arena, assertions)
        .map_err(|error| SolverError::Backend(format!("canonicalize failed: {error}")))?
        .terms;
    let mut trail = ModelReconstructionTrail::new();
    for _round in 0..MAX_PREPROCESS_ROUNDS {
        // `propagate_values` (pin `x = c`).
        let values = propagate_values(arena, &reduced)
            .map_err(|error| SolverError::Backend(format!("propagate_values failed: {error}")))?;
        let eliminated_values = values.eliminated();
        let (after_values, values_trail) = values.into_parts();
        trail.append(values_trail);

        // `solve_eqs_bounded` (substitute `x = t`): the substitution loop is
        // `O(eliminations × nodes)` and runs effectively unbounded on the large public
        // ite-DAGs; the deterministic node-fuel bail keeps it usable at that scale,
        // returning a sound *partial* reduction (un-eliminated equalities stay as
        // ordinary assertions; the trail still reconstructs).
        let eqs = solve_eqs_bounded(arena, &after_values, DEFAULT_SOLVE_EQS_FUEL)
            .map_err(|error| SolverError::Backend(format!("solve_eqs failed: {error}")))?;
        let eliminated_eqs = eqs.eliminated();
        let (after_eqs, eq_trail) = eqs.into_parts();
        trail.append(eq_trail);

        // `elim_unconstrained` (T1.2.4): a variable occurring once under
        // `bvadd`/`bvsub`/`bvxor`/`bvnot`/`bvneg` makes that subterm unconstrained, so
        // it is replaced by a fresh variable and the operator dropped (recovered on
        // `sat` via the appended trail). Runs after `solve_eqs` so it sees the reduced
        // form; its inverses reference only surviving + freshly-minted symbols, so
        // appending its trail last (reconstructed first on reverse replay) resolves.
        let unconstrained = elim_unconstrained(arena, &after_eqs)
            .map_err(|error| SolverError::Backend(format!("elim_unconstrained failed: {error}")))?;
        let eliminated_unconstrained = unconstrained.eliminated();
        let (after_unconstrained, unconstrained_trail) = unconstrained.into_parts();
        trail.append(unconstrained_trail);

        // Re-canonicalize after substitution. `solve_eqs` inlines `x := t` by raw
        // structural rebuild (`replace_subterms`), so a definition like `s1 = a*(b*c)`
        // substituted into `(not (= s1 s2))` reintroduces un-normalized operator trees
        // that AC-normalize here so the equality folds. Denotation- and
        // symbol-preserving ⇒ no trail.
        reduced = canonicalize_terms(arena, &after_unconstrained)
            .map_err(|error| {
                SolverError::Backend(format!("post-solve canonicalize failed: {error}"))
            })?
            .terms;

        // Fixpoint: a round that eliminates no variable means no further reduction is
        // available (the next round would reproduce this one) — stop.
        if eliminated_values + eliminated_eqs + eliminated_unconstrained == 0 {
            break;
        }
    }

    let mut local_search_detail = None;
    if let Some(timeout) = local_search_timeout {
        let mut probe_config = config.clone();
        probe_config.timeout = Some(match config.timeout {
            Some(config_timeout) => config_timeout.min(timeout),
            None => timeout,
        });
        match crate::pbls::solve_local_search(arena, &reduced, &probe_config)?.result {
            CheckResult::Sat(model) => {
                return replay_preprocessed_model(
                    arena,
                    assertions,
                    &trail,
                    &model.to_assignment(),
                );
            }
            CheckResult::Unknown(reason) => {
                local_search_detail = Some(reason.detail);
            }
            CheckResult::Unsat => {}
        }
    }

    let result = backend.check(arena, &reduced, config)?;
    let CheckResult::Sat(model) = result else {
        return Ok(match (result, local_search_detail) {
            (CheckResult::Unknown(mut reason), Some(detail)) => {
                reason.detail = format!(
                    "preprocessed local search declined ({detail}); {}",
                    reason.detail
                );
                CheckResult::Unknown(reason)
            }
            (other, _) => other,
        });
    };
    replay_preprocessed_model(arena, assertions, &trail, &model.to_assignment())
}

fn replay_preprocessed_model(
    arena: &TermArena,
    assertions: &[TermId],
    trail: &ModelReconstructionTrail,
    assignment: &Assignment,
) -> Result<CheckResult, SolverError> {
    // Reconstruct the eliminated variables, then replay against the ORIGINAL
    // assertions — the same checkable-`sat` discipline as the array path.
    let reconstructed = trail.reconstruct(arena, assignment).map_err(|error| {
        SolverError::Backend(format!(
            "preprocessing model reconstruction failed: {error}"
        ))
    })?;

    for &assertion in assertions {
        match eval(arena, assertion, &reconstructed) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => {
                return Err(SolverError::Backend(format!(
                    "preprocessed sat model replay failed: assertion #{} evaluated to false",
                    assertion.index()
                )));
            }
            Ok(value) => {
                return Err(SolverError::Backend(format!(
                    "preprocessed sat model replay failed: assertion #{} evaluated to non-Boolean {value}",
                    assertion.index()
                )));
            }
            Err(error) => {
                return Err(SolverError::Backend(format!(
                    "preprocessed sat model replay failed: assertion #{} failed evaluation: {error}",
                    assertion.index()
                )));
            }
        }
    }

    let mut out = Model::new();
    for (symbol, _name, _sort) in arena.symbols() {
        if let Some(value) = reconstructed.get(symbol) {
            out.set(symbol, value);
        }
    }
    Ok(CheckResult::Sat(out))
}
