# ADR-0142: Bounded exact bit-vector slice canonicalization

Status: accepted
Date: 2026-07-14

## Context

ADR-0136 and the Glaurung QF_BV execution plan identify coercion-cancellation
as the first implementation slice after real-corpus attribution. Artifact v23
can already count the residual shapes, and artifact v25 can compare demanded
bits with bits actually lowered, but the default canonicalizer handles only
whole extracts, same-side extracts of concat, and extracts wholly inside the
original portion of an extension. It leaves nested extracts, concat-boundary
straddles, and extension high/straddling regions for bit blasting.

These formulas are common consequences of explicit machine-width coercion and
register slicing. The rules must nevertheless remain useful beyond Glaurung:
they need stable manifest identities, exact semantics, bounded construction,
and the evaluator/oracle evidence required by ADR-0005 and the foundational
dependency DAG. The rule equations follow the official
[SMT-LIB FixedSizeBitVectors semantics](https://smt-lib.org/theories-FixedSizeBitVectors.shtml):
extract indices are inclusive, bit zero is least significant, and
`concat(high, low)` places `low` at the low bit positions.

This closes the exact-rule-design portion of GQ3. The missing captured
Glaurung query bytes remain the gate for any workload performance claim.

## Decision

Extend the default exact-denotation canonicalizer with a bounded local
replacement loop and the following rule classes. Every rule uses identity
model projection and retains replay of the untouched original assertions as
the acceptance boundary.

Let `slice(hi, lo, x)` mean `extract(hi, lo, x)`, except that a slice covering
all of `x` returns `x` directly.

- `bv.extract_nested.v1`:
  `extract(hi, lo, extract(inner_hi, inner_lo, x))` becomes
  `slice(inner_lo + hi, inner_lo + lo, x)`.
- `bv.extract_concat.v1` continues to select a range wholly within one concat
  operand and now returns that operand directly when the selected range is
  whole. For `concat(a, b)` and `wb = width(b)`, a low range selects `b`; a
  high range selects indices offset by `wb` in `a`.
- `bv.extract_concat_straddle.v1`: when `lo < wb <= hi`, the result becomes
  `concat(slice(hi - wb, 0, a), slice(wb - 1, lo, b))`.
- `bv.extract_extend.v1` continues to drop either extension from a range wholly
  in the original low bits and now returns the original operand directly for a
  whole low slice.
- `bv.extract_extend_high.v1`: a range wholly in added high bits becomes a
  same-width zero constant for `zero_extend`, or the original sign bit repeated
  to the result width for `sign_extend`.
- `bv.extract_extend_straddle.v1`: a boundary-crossing range becomes an
  extension of `slice(width(x) - 1, lo, x)` by exactly the selected number of
  added high bits, retaining zero versus sign extension.

New roots produced by a local rewrite are reconsidered for at most eight rule
applications total at that original DAG node. This permits compositions such
as nested-slice collapse followed by whole-extract elimination without a global
fixpoint. If another rule remains applicable after the eighth application, the
canonicalizer returns the exact partially reduced term and increments a public
`RewriteReport::local_fuel_exhaustions` counter. Fuel exhaustion can therefore
reduce optimization only; it cannot alter denotation or become an error.

Fresh construction is bounded per rule application. Nested and same-side rules
do not grow the reachable DAG. A concat straddle creates at most two slices and
one concat; an extension straddle creates at most one slice and one extension;
and a sign-only high slice creates at most one sign-bit slice and one extension.
Hash-consing may reduce those counts further. No distributive duplication or
unbounded child reprocessing is admitted by these rules.

The benchmark identity for the expanded default manifest is
`axeyum-rewrite-default-v2`; v1 and v2 measurements must not be mixed.

## Evidence

The accepted implementation is guarded by:

- manifest-coverage fixtures for every new stable rule ID;
- exhaustive evaluator comparison over every valid slice of small nested
  extracts, every low/high/straddling concat slice, and every low/high/straddling
  zero/sign-extension slice;
- structural tests for direct whole-side cancellation, composed local
  reprocessing, bounded growth, and observable fuel behavior; and
- Z3 differential SAT and UNSAT queries covering lifter-shaped nested,
  concat-straddling, zero-extension, and sign-extension identities, with both
  original and rewritten models replayed against both assertion sets.

The existing artifact-v23 residual counters distinguish each affected shape,
and artifact-v25 preserves demand/construction attribution for the eventual
captured-corpus comparison. Synthetic and micro evidence validates semantics
and plumbing only; it does not establish a Glaurung speedup.

## Alternatives

- **Run an unbounded canonicalization fixpoint.** Rejected because interacting
  future rules could make preprocessing latency or DAG growth unpredictable.
- **Treat all extract simplification as one manifest rule.** Rejected because
  stable per-class IDs are needed for attribution, selective configuration,
  and regression evidence.
- **Push straddling extracts into arbitrary operators.** Rejected for this
  tranche because it can duplicate expensive subterms and needs a separate
  measured growth policy.
- **Skip exact rewrites until the capture payload arrives.** Rejected because
  the equations, boundedness, and semantic tests are independently required,
  while performance admission remains correctly blocked on the real payload.

## Consequences

Glaurung-shaped coercion and register-slice terms can become materially smaller
before AIG construction, and composed cancellations no longer stop after a
single replacement root. The extra cold-path work is bounded and observable.
Default-manifest benchmark identities change even when a particular query does
not exercise the new rules.

The next GQ3 step is not another synthetic rule expansion. It is to ingest the
producer-owned capture, use v23/v25 attribution to measure which rules fire and
what AIG/CNF work disappears, and retain the tranche only if the valid
decided-rate-gated end-to-end comparison improves. GQ4 partial-bit lowering
follows with its separate projection and replay contract.
