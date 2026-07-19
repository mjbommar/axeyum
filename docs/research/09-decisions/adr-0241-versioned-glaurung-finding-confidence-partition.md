# ADR-0241: Versioned Glaurung finding-confidence partition

Status: accepted
Date: 2026-07-18

## Context

ADR-0240 showed that Glaurung's raw `IOCTLANCE_ALL=1` rows are useful for
determinism and explorer accounting but are not a recall denominator. The two
model-sensitive tcpip rows had been promoted past the normal confidence filter
only because uninitialized loads discarded exact `Arg0` provenance. Running
normal and show-all modes in separate processes would not prove that the two
populations came from identical exploration, while reimplementing Glaurung's
filter in Axeyum would create a second drifting policy.

The policy-sweep plan requires raw, confidence-gated, and independently
validated populations. The first two need a producer-owned protocol before a
labeled-positive corpus can be selected honestly.

## Decision

Glaurung adds opt-in `IOCTLANCE_ANNOTATE_CONFIDENCE=1`. It appends
`confidence=high|diagnostic` only when printing already-sorted findings and
emits an exhaustive `glaurung-ioctlance-confidence-v1` footer. Legacy output
bytes remain unchanged. With show-all enabled, the ordinary summary now reports
the actual high-confidence and would-be-suppressed diagnostic counts.

Axeyum's authoritative-finding harness advances to schema v5. It always records
raw, high-confidence, and diagnostic sets, validates the producer footer and
exhaustive partition, strips annotations before raw hashing, and adds explicit
`--acceptance-population raw|high-confidence`. High-confidence acceptance fails
closed when the partition is absent or malformed. Legacy unannotated binaries
remain usable only for raw acceptance.

## Evidence

Two Glaurung tests prove nested `ArgN` ancestry remains diagnostic and both
annotations preserve the underlying finding bytes. Twenty-one focused Axeyum
tests cover complete and empty partitions, unknown/mixed/missing annotations,
legacy compatibility, independent raw/high differences, and fail-closed
acceptance. The full Axeyum script suite has 107 passing tests; its ten setup
errors are confined to benchmark-recipe tests whose environment lacks the
`just` executable.

Five clean two-repetition tcpip controls rebaseline every existing A0 setting.
AnyModel remains 128 Z3 versus 126 Axeyum raw rows; least, greatest,
site-hash-0, and site-hash-1 are exact at 110, 84, 95, and 98 raw rows. Every
backend and setting has zero high-confidence rows. The AnyModel and
deterministic unions remain 128 each with 95 shared and 33 unique to each; all
33 formerly unclassified AnyModel-only rows are diagnostic `Arg0`/`Arg1`
ancestry under the producer policy.

The earlier four-driver tier and a NETwtw10 prefix also have zero corrected
high-confidence rows. A complete `usbprint.sys` control supplies the required
nonzero candidate: five Z3 and four Axeyum high-confidence rows, with one
Z3-only `SystemBuffer` null dereference. The harness correctly rejects parity.
Exact reports are committed under
[`bench-results/glaurung-finding-confidence-partition-20260718/`](../../../bench-results/glaurung-finding-confidence-partition-20260718/README.md).

## Consequences

The older raw artifacts remain valid deterministic-exploration evidence, but
not coverage evidence. The tcpip 33-row remainder is closed as a producer
diagnostic population, not manually proven false positives. No existing
tcpip policy setting can win a recall comparison on a zero-positive slice.

The next action is to independently classify the five usbprint rows and
root-cause the one authority difference, then preregister a configuration sweep
over the already-pluggable A0 mechanism. Boundary and diverse selection are
settings of that mechanism, not projects. Symcrete or fully symbolic memory is
a separate memory-model change and remains conditional on a validated residual
coverage gap after the cheap sweep.

## Alternatives

- Infer confidence from taint strings in Axeyum: rejected because it duplicates
  producer policy.
- Compare separate normal and show-all runs: rejected because they need not
  share exploration.
- Change default finding bytes: rejected because it invalidates historical
  hashes and consumers.
- Treat producer confidence as ground truth: rejected; independent/manual
  validation remains a separate required population.
- Continue optimizing the tcpip raw union: rejected because its accepted
  population is empty.
