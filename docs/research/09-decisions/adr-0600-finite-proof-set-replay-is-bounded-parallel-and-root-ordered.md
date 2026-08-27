# ADR-0600: Finite proof-set replay is bounded-parallel and root-ordered

Status: accepted
Date: 2026-08-27

## Context

ADR-0599 decomposes a finite palette orbit into independently checkable labelled DRAT proofs.
The first complete radius-23 set contains 120 proofs and 23.05 GB. Its original checker replayed
one member at a time even though no member depends on another; after five minutes it had accepted
only three. This is a generic certificate-consumption bottleneck, not SAT-search difficulty.

## Decision

Finite palette proof-set replay accepts an optional explicit worker count, bounded to 1--64 and
defaulting to one for compatibility. Workers independently regenerate formulas and check proofs.
The coordinator releases progress and selects failure strictly in lexicographic permutation order,
regardless of completion order. The total-byte ceiling is accumulated in that same authoritative
order. Invalid worker counts fail before checking.

## Evidence

A focused control pins the default, a four-worker value, zero, above-ceiling, and malformed forms.
The example test and warning-denied all-feature Clippy pass. The radius-23 four-worker replay is the
first real use; it receives no theorem credit until every member is accepted.

## Alternatives

Keeping the sequential route wastes independent cores. Emitting completion-order progress would
make receipts scheduling-dependent. Trusting producer status or a manifest would remove the
independent regeneration and fail-closed completeness properties that justify ADR-0599.

## Consequences

Large finite certificate families can use controlled host parallelism without nondeterministic
authority. Peak memory scales with the explicit worker count, so callers remain responsible for
choosing a host-appropriate bound. One worker preserves the original resource envelope.
