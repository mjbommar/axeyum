# Lane: rational-bignum — exact rationals stop declining, where a route asks them to

<!-- plan-section: lane-status -->

**ADR-1702 slice 1 landed: `Rational` gains an arbitrary-precision slow path,
and promotion is OPT-IN PER ROUTE** (`WIP`, rational-bignum, 2026-09-05,
ADR-1702). A parallel `wide_new`/`wide_add`/`wide_sub`/`wide_mul`/`wide_div`/
`wide_neg`/`wide_recip` family promotes on `i128` overflow; `new`, the
`checked_*` family and the arithmetic operators keep declining exactly as
before. Any result that fits `i128` again is demoted back. The exact-rational
simplex is the first — and so far only — route to opt in.

**The brief asked for unconditional promotion. That was implemented, measured,
and rejected, and the measurement is the finding.** Global promotion passed a
lot: the workspace compiled unchanged, `axeyum-solver --lib --features full`
reached 1438/1438, the corpus sweep and all three z3 differential fuzzes were
green. Then `cargo test -p axeyum-cas --lib` was run: **25 unit tests failed and
about seven stopped terminating** — still running at 45 minutes at full CPU,
against 69 seconds for the whole suite. A controlled A/B on a named six-test
subset, my tree versus a snapshot of the pre-change commit, was 6 failed / 0
passed against 0 failed / 6 passed.

`axeyum-cas` uses **`i128` exhaustion as a cost bound and a termination
argument**. Its Groebner reduction returns `Declined(Overflow)`, its
Wilf–Zeilberger certificate search and its zero tests decline when an
intermediate leaves range, and its interval arithmetic declines on an
unnegatable endpoint; three of the failing tests are named for that contract.
Remove the bound and those computations run away on values with hundreds of
digits instead of stopping. **No magnitude ceiling separates the two
populations**, because the CAS declines *at* `i128` and the values in its
failing assertions are 10^30 to 10^69. So `i128` range is load-bearing for one
population of consumers and a liability for another, one type cannot change its
meaning to serve both, and opt-in is what serves both.

**Promotion is contained where it is used.** The simplex's five arithmetic
helpers use the `wide_*` family, and every value leaving the module passes a
`narrow` guard that declines to `Unknown` if a feasible point or a Farkas
multiplier does not fit `i128`. Nothing downstream — `lra`, `lra_online`, model
lifting, certificate serialization — can observe that a promoted value existed,
which is why the widening puts no new obligation on the 416
`numerator()`/`denominator()` call sites (those return `i128` and panic rather
than truncate on a promoted value). Two of those sites were hardened anyway,
because the global-promotion experiment reached them.

**`simplex.rs`'s `Overflow` marker is kept, not removed.** It is narrower but
not unreachable: `wide_div` still declines on a zero divisor, the `narrow`
boundary declines an out-of-range witness or certificate, and promotion still
fails at the pool cap (2^20 distinct values — an append-only pool without a cap
would trade a fast `unknown` for an out-of-memory). Pivot and deadline budgets
are untouched.

**Slice 2 is NOT started and admits none of gap-analysis row 4b on its own.**
The 26 QF_UFLIA files carrying `2^256` EVM literals are rejected at the
*parser*, on `Value::Int(i128)`, before any `Rational` exists. Slice 2 is
`Value::Int`, the SMT-LIB integer-literal parser, and opting further routes in
one at a time. The LRA 1,024-atom cap does not move here either.

<!-- plan-section: landed-changes -->

| 2026-09-05 | `ebc659b88` | ADR-1702, first draft: exact rationals as an `i128` fast path with an arbitrary-precision slow path, promoting instead of declining. Records the two slices, the determinism and soundness argument, and the rejected alternatives (dropping `Copy`, a fixed `i256`/`i512`, leaking instead of pooling). |
| 2026-09-05 | `4865e6d48` | The two-representation machinery: `Rational` stays `Copy` and 32 bytes, with promoted values as handles into a capped deduplicating pool marked by the otherwise-impossible `den == 0`; value-based `Eq`/`Ord`/`Hash`/`Display` so the pool id is never observable. |
| 2026-09-05 | `fe9895dbe` | The 8 `axeyum-solver` failures unconditional promotion caused, in two shapes: `nra_real_root::Sign::of_rational` now reads the sign from the value rather than from `numerator()`; `nra_handelman_cert` uses the checked accessors where it serializes `i128` pairs onto the wire. `adversarial_robustness` stopped asserting "not `Sat`" on a satisfiable query. |
| 2026-09-05 | `PENDING` | The redesign the `axeyum-cas` measurement forced: promotion becomes the opt-in `wide_*` family, the declining family is restored bit-for-bit, and the simplex opts in behind a `narrow` containment boundary. ADR-1702 rewritten around the measurement, with a discriminating test (`the_checked_family_declines_exactly_where_the_wide_family_promotes`) that a patch making `checked_*` promote would fail and every other test in the file would pass. |
