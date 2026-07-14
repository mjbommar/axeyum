# ADR-0143: Opt-in structural bit-demand profiling

Status: accepted
Date: 2026-07-14

## Context

ADR-0136 artifact v25 introduced a conservative structural bit-demand analysis
as an observational diagnostic for GQ4. The first full, well-typed Glaurung
capture showed that the analysis consumed 29.57 seconds of a 50.75-second
canonical cold run. It was executed inside every `lower_terms` call even though
it neither changed lowering nor contributed to a verdict. Production timing was
therefore dominated by a diagnostic that ADR-0136 explicitly described as
diagnostic-only.

The same capture established that the distinction must be machine-readable.
An all-zero demand record cannot distinguish an unprofiled production solve
from a complete profile that found no demand.

This decision refines the artifact-v25 measurement boundary and the GQ4
measurement step in
[the Glaurung execution plan](../08-planning/glaurung-qfbv-execution-plan.md).

## Decision

Structural bit-demand analysis is opt-in and never runs on the default cold
lowering path.

- `lower_terms` and `lower_terms_with_deadline` lower the complete formula as
  before, record the actual term and symbol bits materialized, and mark the
  structural demand profile incomplete.
- Explicit profiled lowering entry points run the same lowering plus the
  conservative structural analysis under the same deadline. Profiling remains
  observational: it may change elapsed time and diagnostics, never the AIG,
  lift maps, verdict, model, or replay obligation.
- `SolverConfig::profile_bit_demand` is an off-by-default diagnostic control.
  The benchmark CLI exposes the corresponding `--profile-bit-demand` flag only
  for the SAT-BV backend.
- Typed layer stats and artifact records carry an explicit
  `profile_complete` bit. Request, available, demanded, ratio, and coverage
  fields are `null` when the profile is incomplete; actual lowered counts
  remain available. Corpus completeness requires every contributing layer
  sample to be complete.
- Production Glaurung recipes leave profiling off. Separately named demand
  recipes enable it and are diagnostic artifacts, not client-ratio evidence.

Artifact version 27 records this boundary in configuration identity and demand
records. Repetition tools reject older versions so v26 timings containing the
accidental profiler cost cannot mix with production v27 timings.

## Evidence

- The 13,462-query well-typed full Glaurung canonical artifact-v26 run spent
  29.568 seconds in structural demand analysis out of 50.751 seconds total.
- A narrow-extract unit fixture continues to produce the complete 25/81 term
  and 8/64 symbol demand profile through the explicit profiled entry point.
- Default-lowering tests require an incomplete profile, zero analysis time and
  unavailable structural fields while retaining nonzero actual-lowering
  counts.
- SAT-BV and benchmark tests cover both modes, including configuration hashing
  and fail-closed artifact labeling.

## Alternatives

- **Keep profiling always on and subtract its time.** Rejected: the client still
  pays the CPU and allocation cost, and nested timing subtraction does not
  recover a production execution.
- **Delete the diagnostic.** Rejected: it remains useful for evaluating GQ4 on
  selected families and for validating future partial lowering.
- **Encode incomplete profiles as zeros.** Rejected: zero is a valid count and
  cannot carry measurement provenance.
- **Immediately fuse analysis into partial lowering.** Deferred: the canonical
  full capture reports 98.16% of term bits demanded, so broad partial lowering
  is not yet justified ahead of family-specific evidence.

## Consequences

Normal Glaurung timing measures work required to solve and replay the query.
Demand diagnostics remain reproducible but carry their own explicit cost and
identity. Adding future demand-driven lowering still requires the semantic,
lift-map, and original-query replay obligations in the foundational DAG; this
ADR changes instrumentation policy only.
