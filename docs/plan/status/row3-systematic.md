# Lane: row3-systematic — row 3 is cheap where a decision replaces a limit

<!-- plan-section: lane-status -->

**Status**: complete (2026-08-31). Surveyed the ADR-0603 **row 3** surface
(exact form on the decidable fragment) across the classical theorems this
repository tracks, ranked the available-but-unbuilt candidates, and built the
top two. Both are `cas-internal` (ADR-0601) and say so in the module doc, the
fact `notes`, the `axiom_footprint` and the evidence `notes`.

Survey, ranking and the corrections to two stale premises:
[ADR-1315](../../research/09-decisions/adr-1315-row-3-is-cheap-where-a-decision-procedure-replaces-a-limit.md).

## Headline

**Row 3 is cheap exactly where the classical proof's HARD STEP becomes a
decision procedure** — not where the CAS capability happens to exist. Every
analysis theorem has a polynomial specialisation, so "is the capability there"
ranks almost everything equally. What separates a row 3 worth building is
whether the difficulty becomes a *computation* (MVT's critical point, the
inverse's uniqueness, irrationality's divisor search) or merely evaporates (the
FTC on polynomials is an algebraic identity).

`distinct_propositions` **2254 → 2256**. The 12 pre-existing
`SHARED-DECLARATION-PAIR` failures in `check-proposition-duplication.py` are
unchanged and neither new fact is among them.

## Landed changes

| what | where |
|---|---|
| Row 3 for the **inverse function theorem** (Spivak ch. 12) — the only family with rows 1 and 2 landed and row 3 empty. Monotonicity DECIDED by a Sturm count on `p'`, so the preimage is unique; named as an `AlgebraicReal`. | `crates/axeyum-cas/src/inverse.rs` |
| Row 3 for the **irrationality decision** — producer decides by factorization, checker re-derives by the RATIONAL ROOT THEOREM. No shared algorithm. | `crates/axeyum-cas/src/rationality.rs` |
| `F:cas-inverse-quintic-degree-five-witness` — `p = x^5 + x` on `[0,2]`, `y = 3`, preimage a degree-5 algebraic number | `artifacts/facts/` |
| `F:cas-quintic-real-root-is-irrational` — the real root of `x^5 - x - 1` | `artifacts/facts/` |
| The survey, the ranking, and the guard-falsifiability measurement | ADR-1315 |

## Measured, not asserted

**Guard deletion in a `lane-snapshot.sh` scratch copy, never in a tracked file:**

| module | checks | killed by exactly one | killed by >1 | survived |
|---|---|---|---|---|
| `inverse.rs` (first draft) | 15 | 3 | 0 | **12** |
| `inverse.rs` (after repair) | 14 | 4 | 0 | **10** |
| `rationality.rs` | 8 | 3 | 5 | **0** |

`inverse.rs`'s module doc claimed nine independently-falsifiable guards; that
was **false** and deletion is what showed it. The repair deleted the *claim*
(replacing it with a measured backup table), deleted one check that could never
fail on its own, and rebuilt the fixture for the check carrying the module's
actual mathematics so it is isolated. `rationality.rs` has zero survivors
because its checker and producer share **no algorithm** — that is the general
lever, and it is why the two modules diverge so sharply.

**Break/restore of both `checker_command`s** (output / exit):

- inverse: clean 1/0 → producer broken 0/1 → checker broken 0/1 → restored 1/0.
- rationality: clean 1/0 → producer broken 0/1 → checker *weakened* **1/0** →
  checker broken so it rejects 0/1 → restored 1/0.

The third rationality line is reported deliberately: a command asserting
ACCEPTANCE cannot detect a checker made too permissive. That direction is
covered by the guard-deletion suite, not by the ledger's command.

## Findings about code these modules do not own

1. **`verify_ivt_certificate` and `verify_mvt_certificate` refuse a correct
   certificate whose witness is an exact rational.** `AlgebraicReal::refine`
   collapses its bracket to a point on an exact rational root, so `(1, 1]` is a
   legitimate representation and a half-open Sturm count over it is `0`; both
   checkers require `lower < upper`. Fail-closed, so a false negative rather
   than an unsoundness. Reproduced at `p = x^5 + x`, `y = 2` on `[0, 2]` and
   pinned, so fixing `real_algebraic.rs` turns a test red rather than passing
   silently.
2. **A real soundness bug in the rational-root enumeration**, found by
   `rationality.rs`'s own test on its first run: `n | a_0` is vacuous at
   `a_0 = 0`, so `p = x^2 - x` loses the candidate `1` and an `Irrational`
   verdict for a rational number would have been accepted. Fixed and pinned
   end-to-end.
3. **Two stale premises corrected.** `CReal.integral_split` HAS landed (plus
   `integralSplitAnywhere`/`integralSplitArbitrary`) — `spivak.md`'s ch. 14 row
   still calls additivity "in progress". And `partial_fractions.rs` is **not** a
   row 3; it carries no ADR-0603 marker. The fourth existing row 3 is IVT's, in
   `real_algebraic.rs`.

## What remains, ranked

From ADR-1315's table, in order:

1. **FTA** (ch. 25–27) — highest mathematical value, but its row 3 needs
   certified **complex** root isolation, a genuinely missing algorithm rather
   than an assembly. Its row 2 is also *unassessed* rather than absent: FTA is
   stated over a compact set and may not be in IVT/EVT's constructive-failure
   class at all.
2. **Radius of convergence for rational functions** (ch. 24) — available (pole
   location is root isolation) but it would be a lone row: neither row 1 nor
   row 2 exists.
3. **FTC / integral additivity** (ch. 13–14) — available and **thin**: the
   theorem becomes a polynomial identity, and row 1 is complete anyway.
4. **LUB** (ch. 8) — the existing narrow row 3 generalises to a finite set of
   algebraic numbers by a `max` over a list. Trivial.
5. **Boundedness** (ch. 7) — nothing to add; row 1 is fully constructive with a
   *computed* bound.
