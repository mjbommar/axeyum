# ADR-0186: Accept pressure-adaptive Glaurung default

Status: accepted
Date: 2026-07-16

## Context

ADR-0185 left pressure-adaptive lineage behind a clean repeated gate. That gate
now exists, and Glaurung's fail-closed comparator has an explicit mode that
permits only the fixed-lineage-to-adaptive policy transition while retaining
all other system, driver, finding, correctness, resource, and alarm identity.

## Decision

Accept Glaurung `ca12028` as the GQ9 production policy for Axeyum explorer
solves with explicit path ownership. When `GLAURUNG_AXEYUM_WARM_REUSE` is
unset, Glaurung selects adaptive 2→9 admission at 128 pressure events. Explicit
`off`, `false`, or `0` restores one-shot behavior. Named `lineage`, `auto`, and
`snapshot` controls remain available. This is a downstream client scheduling
default, not a change to Axeyum's framework-level solver API or defaults.

## Evidence

Glaurung `f99f72b` commits the byte-exact 8,965-byte artifact from clean
Glaurung `95c43cb` / Axeyum `f91fb232`; SHA-256 is
`0255d0ed2a0c5bc078e478cb951561d4de1460c11333a646f3e150b15281e716`.
All 92,721 checks agree with zero unknown splits and exact repeated traffic.

- SurfacePen: adaptive 1.085 seconds / 79,424 KiB, +2.07% time, +2.28%
  normalized ratio, and -3.65% RSS versus fixed lineage.
- NETwtw10: adaptive 18.558 seconds / 255,364 KiB, -1.03% time, -0.89%
  ratio, and -0.88% RSS.
- Absolute Z3 drift is at most 0.21%; Axeyum CV is 0.19%/0.40%.

Every 3% time, 3% ratio, 5% RSS, and 2% Z3 alarm passes. Nine runner tests
cover parsing, exact partitions, and the named cross-policy identity. The
default parser has direct coverage. A real unset-environment SurfacePen run
selects the exact adaptive partition and agrees 2,551/2,551; an explicit `off`
run emits no warm footer and also agrees 2,551/2,551. All 28 backend tests,
release build, and default Clippy pass subject to Glaurung's existing warnings.

## Consequences

GQ9 is complete for the available held-out families: Glaurung gets warm delta
reuse by default without exposing mutable state across siblings, weakening
model replay, or changing proof semantics. The hard 9/512 ceiling and all
fallback telemetry remain enforced. Newly captured families must enter the
same gate; a regression can disable the policy explicitly. The next client
priority is ADR-0184's corrected cold-corpus regeneration, then GQ10 widening.

## Alternatives

Leaving a passing, validated policy opt-in was rejected because it would fail
to deliver the measured warm advantage to the client. Removing the one-shot
override was rejected as an operational and diagnostic regression. Changing
Axeyum's generic default was rejected because the evidence is specific to
Glaurung's explorer ownership and real query streams.
