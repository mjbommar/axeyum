//! # axeyum-property — a typed, bounded-property SDK over the axeyum solver
//!
//! State a property over bounded integers / bit-vectors and get back one of:
//! `Proved(certificate)` · `Counterexample(typed inputs)` · `Unknown(reason)` —
//! where `Proved` carries an independently re-checked certificate (and a
//! standalone Lean module when the result is in the reconstructable fragment).
//!
//! This is a thin, type-safe shell over `axeyum-solver` builders that already
//! exist and are re-checked — it adds typing + lifting, no solver logic. See the
//! design and build plan in `docs/consumer-track/property/PLAN.md`.
//!
//! **Scaffold:** the API below is the linking smoke test; the real surface
//! (`property().forall::<T>().assuming(..).check(..) -> Outcome<T>`, phantom
//! type-level bit-vector widths, `#[derive(Symbolic)]`) is built iteratively.
#![forbid(unsafe_code)]

/// Smoke check: confirms the crate links `axeyum-solver` (the dependency edge the
/// SDK is built on). Replaced by the real `property()` entry point as the API lands.
#[must_use]
pub fn solver_linked() -> bool {
    let _config = axeyum_solver::SolverConfig::default();
    true
}

#[cfg(test)]
mod tests {
    use super::solver_linked;

    #[test]
    fn links_solver() {
        assert!(solver_linked());
    }
}
