# Lane: ratint — certified integration of rational functions (Spivak ch. 19)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE for this slice`, ratint, 2026-08-27).**

**State before this lane, established by reading `ratint.rs` first (it had
zero tests and no doc note anywhere else pointing at it):** the *producer*
side of rational-function integration already existed, further along than
the task brief assumed. `crates/axeyum-cas/src/ratint.rs` already had
`horowitz` (Horowitz–Ostrogradsky rung 1, the rational part) AND
`rothstein_trager_resultant` / `rational_roots` / `log_terms` (Rothstein–
Trager rung 2, the logarithmic part). `lib.rs`'s public `integrate()` already
wires both into a certified antiderivative via the general CAS-wide
differentiate-and-compare route (`prove_derivative` / `equal`,
`CertifiedIntegral`), including a rung-3 path to `arctan` for irreducible
quadratics via `apart` + `integrate_partial_fraction_term`
(`integrate_log_part_by_factoring`). So the producer ladder in the task brief
was already climbed; what was missing was a **small, independent checker**
distinct from the CAS-wide `equal()` engine, and any tests at all for this
module.

**What landed:** two `pub(crate)` checkers in `ratint.rs`, `verify_horowitz`
and `verify_log_terms`, that re-derive correctness purely in `poly.rs`
exact-`Rational` arithmetic — never through `CasExpr`/`equal`. Both return
`Option<bool>` (`None` = internal overflow/decline, `Some(false)` =
rejected, `Some(true)` = every guard passed), matching the
`verify_partial_fraction_certificate` convention in `partial_fractions.rs`.
22 tests, all guards mutation-verified (delete the guard, confirm at least
one test dies; two guards found to be provably, always subsumed by another
were removed rather than kept as decoration, matching the partial-fractions
lane's own precedent — see the module doc and commit history for the
algebraic proof of each subsumption).

Detail moved to [`../notes/163-ratint.md`](../notes/163-ratint.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | ratint | `verify_horowitz`: independent poly-arithmetic checker for the Horowitz rational-part split, 6 guards, all mutation-verified |
| 2026-08-27 | ratint | `verify_log_terms`: independent poly-arithmetic checker for the Rothstein–Trager log-part decomposition, 3 guards, all mutation-verified |
| 2026-08-27 | ratint | 22 unit tests added to `ratint.rs` (was 0): producer sanity, positive roundtrips with an eval cross-check, and adversarial fixtures per guard, including two flagship "vacuous without this guard" fixtures |
| 2026-08-27 | ratint | Removed 2 guards proven always-subsumed (verify_log_terms's duplicate-v check; verify_horowitz's original D2/D1-nonzero check, replaced by an explicit denom-non-constant guard) rather than leave them as decoration |
