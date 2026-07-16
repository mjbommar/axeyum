# ADR-0202: Direct-delta warm profile contract

Status: accepted
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

Glaurung `00bd660` implements the producer without adding unprofiled solver-
stats reads: detailed Axeyum counters are sampled only when
`GLAURUNG_AXEYUM_PROFILE_DIR` is active. The complete 41-test Axeyum-backend
group passes under the 4 GiB wrapper; one pre-existing 250 ms text-bridge
timeout flaked once and passed immediately alone and in the complete hot
rerun. The selected direct adapter also passes under combined Z3+Axeyum
features. Clippy reports only the repository's existing warnings.

Fresh-process producer smokes validate through the strict current summarizer:

- direct delta: 4/4 decided (3 SAT, 1 UNSAT), one owner, two persistent roots
  translated/encoded, one temporary root translated/encoded, one prefix pop,
  and one exact replay-cache hit;
- snapshot: 6/6 decided (4 SAT, 2 UNSAT), twelve complete persistent roots
  translated, six persistent roots encoded, and zero temporary work.

The Axeyum validator suite is 53/53 green. New fixtures accept both v7 entry
modes, reject invalid complete-query, translation, and root-encoding
partitions, and retain explicit v1--v6 historical coverage. Ruff check and
format validation pass, as does documentation link validation. The adaptive
mixed summary now preserves entry-mode and entry-structure totals inside the
unsplit warm/native occurrence stream.

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
