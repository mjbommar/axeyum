//! Hyperproperties over reflected code — **2-safety by self-composition**
//! (Track 5, P5.3 / T5.3.1).
//!
//! A hyperproperty relates *two* runs of the same function, so it is not a goal
//! over one reflected term. The technique is self-composition: reflect the
//! function twice into one arena, over input sets that agree on the *public*
//! parameters and differ on the *secret* ones, and relate the two reflections.
//!
//! **Constant-time (control-flow secret-independence).** A timing side channel
//! observes which branch a program takes; the reflector records those branch
//! scrutinees as *leakage* (`mir::reflect_mir_params_with_leaks`). A
//! function is control-flow constant-time iff, for every pair of inputs sharing
//! the public part, the leaked branch decisions are identical. So the goal is
//! the conjunction of pairwise equalities of the two runs' leakage:
//!
//! - **Proved** → the branches are secret-independent (constant-time);
//! - **Disproved** → a secret-dependent branch, with a countermodel giving the
//!   two secret values that steer control flow apart.
//!
//! This is orthogonal to non-interference on the *output*: a function may be
//! control-flow constant-time while its return value still depends on the secret
//! (a public-predicated `select` of secret data). Memory-access index leakage
//! (cache-timing) is a documented next step — only branch leakage is collected
//! today.

use axeyum_ir::{TermArena, TermId};

use super::mir::{MirParam, reflect_mir_params_with_leaks};

/// Build the goal term asserting that `mir`'s branch decisions are
/// **secret-independent**: reflect `mir` over the two parameter lists `run_a`
/// and `run_b` (which must share the public params — the *same* [`TermId`]s —
/// and differ on the secret params), collect each run's control-flow leakage,
/// and conjoin the pairwise equalities. Prove the result for control-flow
/// constant-time; a countermodel is a secret-dependent branch.
///
/// Returns `true` (a constant `Bool`) when the function has no branches — no
/// control flow is trivially secret-independent.
///
/// # Panics
/// Panics if `run_a` and `run_b` produce different leakage shapes (they must not
/// — it is the same function reflected twice), or if the IR is unsupported.
pub fn control_flow_ct_goal(
    arena: &mut TermArena,
    run_a: &[MirParam],
    run_b: &[MirParam],
    mir: &str,
) -> TermId {
    let (_, _, leaks_a) = reflect_mir_params_with_leaks(arena, run_a, mir);
    let (_, _, leaks_b) = reflect_mir_params_with_leaks(arena, run_b, mir);
    assert_eq!(
        leaks_a.len(),
        leaks_b.len(),
        "self-composition: the same function reflected twice must leak the same shape"
    );
    let mut goal = arena.bool_const(true);
    for (a, b) in leaks_a.iter().zip(&leaks_b) {
        let eq = arena.eq(*a, *b).unwrap();
        goal = arena.and(goal, eq).unwrap();
    }
    goal
}
