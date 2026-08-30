# Notes: 163-ratint

Detail moved out of [`../status/163-ratint.md`](../status/163-ratint.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**What did NOT land, and why (in scope, deliberately deferred):** wiring
`verify_horowitz`/`verify_log_terms` into `lib.rs`'s `integrate_rational` /
`integrate_log_part` as an additional (defense-in-depth) check alongside the
existing `prove_derivative` route. This lane's scope was `ratint.rs` + the
`mod` line only; `lib.rs`'s `integrate_rational`/`integrate_log_part` are
substantial functions outside that scope. Both checkers are marked
`#[allow(dead_code)]` with a doc note explaining this, and are fully
exercised by this module's own tests. **Next lane:** wiring them in is a
small, well-scoped follow-up (call `verify_horowitz`/`verify_log_terms`
right after `horowitz`/`log_terms` produce a result, inside
`integrate_rational`/`integrate_log_part`, and decline to `None` on
`Some(false)`/`None` before ever building a `CasExpr`) — the two checkers
are ready to consume.

**The certifiable boundary** (per the task brief's requirement to say
exactly where it stops being exact): `verify_horowitz` and `verify_log_terms`
both stay inside PURE polynomial arithmetic over ℚ — no transcendental
values are compared, only the polynomial identities that are algebraically
EQUIVALENT to "differentiate the candidate and compare to the integrand
exactly" (worked out in each function's doc comment). This is strictly
smaller and more trustworthy than the CAS-wide `equal()`/`prove_derivative`
route `lib.rs` currently uses for the same claim, which goes through the
general term-rewriting zero-tester. The boundary of what these two checkers
can certify is exactly the Horowitz rational part and the Rothstein–Trager
logarithmic part when the resultant splits over ℚ (rational roots only) —
an irreducible quadratic factor's `arctan` term (rung 3, already handled by
`integrate_log_part_by_factoring` in `lib.rs`) is NOT covered by either
checker here; verifying an `arctan` identity needs `d/dx atan(u) = u'/(1+u²)`,
which is a genuine transcendental derivative rule, not a polynomial identity,
so it correctly stays on the general `prove_derivative`/`equal()` route and is
out of this checker pair's (deliberately narrower) scope.
