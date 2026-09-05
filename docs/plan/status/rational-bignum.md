# Lane: rational-bignum — exact rationals stop declining on range

<!-- plan-section: lane-status -->

**ADR-1702 slice 1 landed: `Rational` is an `i128` fast path with an
arbitrary-precision slow path, and `i128` overflow now PROMOTES instead of
declining** (`WIP`, rational-bignum, 2026-09-05, ADR-1702). Any result that
fits `i128` again is demoted back, so the fast path is retaken after transient
growth. Both paths compute the same mathematical value, so no verdict can
change — only an `unknown` caused by running out of range can become a
decision.

**The design was forced by `Copy`, not chosen.** `Rational` is referenced
~5,500 times in 223 files, consumed by value throughout, and is a field of the
interned `TermNode::RealConst`; `BigRational` is heap-owned and therefore not
`Copy`. Boxing the big case is the textbook representation and would have been
a workspace-wide mechanical edit conflicting with every concurrent lane. So the
big case is a **handle** into a capped, deduplicating, process-global pool,
encoded in the existing 32 bytes by the otherwise-impossible `den == 0` (the
small invariant is `den > 0`). Size and layout are unchanged, so the dense
simplex tableau's memory model is unchanged, and the public API keeps every
name and signature.

**The pool cap is the part that matters for robustness.** An append-only pool
with no cap would trade today's fast `unknown` for an out-of-memory. Past
`Rational::big_pool_capacity()` promotion fails and every operation behaves
exactly as it did before ADR-1702 — `checked_*` returns `None`, the operators
panic — which is also why `simplex.rs`'s `Overflow` marker is **kept** rather
than removed: it is narrower now but not unreachable, since `checked_div` still
declines on a zero divisor and promotion still fails at the cap. Deleting it
would delete a live soundness path.

**The residual hazard is named, not hidden.** `numerator()` and
`denominator()` return `i128` and are called at 416 sites. They keep that
signature and **panic** on a promoted value rather than truncate — saturating
would convert an out-of-range value into a silently wrong one. New accessors
(`checked_numerator`, `checked_denominator`, `numerator_big`,
`denominator_big`, `is_big`) give a non-panicking route. Before this change a
big rational could not exist, so no caller could meet one; auditing those sites
route by route is slice 2's work.

**Slice 2 is NOT started and admits none of gap-analysis row 4b on its own.**
The 26 QF_UFLIA files carrying `2^256` EVM literals are rejected at the
*parser*, on `Value::Int(i128)`, before any `Rational` exists. Slice 2 is
`Value::Int`, the SMT-LIB integer-literal parser, and the accessor audit. The
LRA 1,024-atom cap also does not move here; turning it from a partial overflow
guard into a pure memory bound is a separate lever that has to be measured on
its own.

<!-- plan-section: landed-changes -->

| 2026-09-05 | `ebc659b88` | ADR-1702: exact rationals are an `i128` fast path with an arbitrary-precision slow path; overflow promotes instead of declining. Records the two slices, the determinism and soundness argument (identical values on both paths, so only `unknown`s can become decisions), and the three rejected alternatives — dropping `Copy`, a fixed `i256`/`i512`, and leaking each big value instead of pooling. |
| 2026-09-05 | `4865e6d48` | Slice 1: `Rational` promotes and demotes behind an unchanged public API; `checked_*` return `Some` on the promoted path and `checked_cmp` can no longer decline at all; value-based `Eq`/`Ord`/`Hash`/`Display` so the pool id is never observable. The three `eval.rs` `real_*_overflow_is_graceful` tests now assert the promoted value is EXACT against independently computed `BigInt` expectations, rather than asserting the pre-ADR `ArithmeticOverflow`. `simplex.rs` documentation only — the `Overflow` marker, the pivot budget and the deadline budget all stay. |
