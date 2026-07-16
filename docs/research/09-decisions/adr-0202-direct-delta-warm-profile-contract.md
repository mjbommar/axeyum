# ADR-0202: Direct-delta warm profile contract

Status: proposed
Date: 2026-07-16

## Context

Axeyum ADR-0201 and Glaurung ADR-011/`f5a3b7a` replace whole-snapshot prefix
rediscovery with an opt-in first-class retained session. The existing
`glaurung-axeyum-warm-profile-v6` artifact assumes that every check translates
the complete assertion snapshot and that every newly encoded root is a
persistent assertion. Those assumptions are false for the direct route: an
existing owner translates only its persistent suffix, and probe-only roots are
translated and encoded as one-shot assumptions.

Reusing v6 would make a faster route look like missing data and would conflate
persistent CNF growth with ephemeral probe encoding. GQ7 cannot be accepted
from ambiguous attribution. This closes the direct-entry evidence-format
question in the research-questions register and follows the fail-closed
benchmark boundary in ADR-0197.

## Decision

Version the producer and validator as `glaurung-axeyum-warm-profile-v7` and
make entry semantics explicit.

Every v7 record carries an `entry_mode` (`snapshot` or `direct_delta`) plus
the complete-query partition:

- persistent assertion count;
- temporary assumption count;
- persistent roots translated during this check;
- temporary roots translated during this check; and
- persistent versus temporary root encodings.

The complete query hash, result, original replay, path ownership, phase clocks,
retained structural gauges, and cache telemetry remain unchanged. Snapshot
records report the full persistent snapshot as translated and no temporary
work. Direct records report only the actual suffix/assumption translation.
Root encodings must partition exactly into persistent and temporary encodings;
for a complete direct check, persistent translations equal newly added
persistent roots, while replay-cache hits may legitimately avoid temporary
root encoding after Glaurung has translated the assumption.

The summarizer continues to accept v1--v6 as historical inputs but requires
all new fields and their arithmetic invariants for v7. Summaries expose entry-
mode totals rather than averaging snapshot reconstruction and direct deltas
without a label. The adaptive mixed summarizer accepts only current v7 warm
records plus native-v1 fallbacks.

## Evidence

Acceptance requires:

1. producer tests covering snapshot, direct persistent suffix, ephemeral
   assumptions, exact reuse, and fail-closed invalid transitions;
2. strict summarizer fixtures that accept both v7 modes and reject invalid
   count/root partitions while retaining every historical schema test;
3. a real profiled direct-delta smoke whose JSONL validates and reconciles with
   the ordered query stream; and
4. unchanged decisions, findings, replay, lifecycle cleanup, and one-shot
   controls.

The ADR remains proposed until those gates pass.

## Alternatives

- Keep v6 and reinterpret `translated_exprs`: rejected because the same schema
  would have two incompatible meanings and no persistent/temporary partition.
- Profile only aggregate wall time: rejected because GQ7 specifically needs to
  prove that snapshot translation and prefix reconstruction disappeared.
- Treat probes as temporary persistent scopes for profile compatibility:
  rejected because it changes the first-class session semantics being measured
  and recreates snapshot thrash.

## Consequences

The profile surface grows, and current adaptive fixtures must advance to v7.
In return, direct-entry cost is causal and auditable: translation saved,
persistent CNF growth, ephemeral assumption encoding, cache hits, SAT, replay,
and model lift remain separable. No solver or production admission default
changes with this ADR; direct deltas remain opt-in until the repeated ordered
time/RSS gate passes.
