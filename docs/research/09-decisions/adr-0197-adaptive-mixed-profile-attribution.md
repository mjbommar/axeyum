# ADR-0197: Adaptive mixed warm/fallback profile attribution

Status: accepted
Date: 2026-07-16

## Context

ADR-0196 makes LIFO-aligned warm-owner transfer the Glaurung default and asks
for a fresh accepted-current profile. The production adaptive policy begins
with two retained path sessions and deliberately sends checks that exceed that
bound through the unchanged one-shot fallback. Its profile file therefore
contains both `glaurung-axeyum-warm-profile-v6` and
`glaurung-axeyum-native-profile-v1` records in occurrence order.

The existing warm and native summarizers correctly reject the other schema.
Splitting the file before validation would lose the single process-local
sequence boundary and could silently omit fallback work. Profiling only the
fixed-lineage control would attribute the retained core but would not measure
the accepted adaptive production policy.

## Decision

Add a separate `summarize-glaurung-adaptive-profile.py` tool. It accepts only a
mixture containing the current warm v6 schema and native v1 fallback schema.
It delegates each record to the existing schema-specific validator, then
validates unique and strictly increasing process/sequence keys across the
unsplit stream. Warm path-first-occurrence identity remains mandatory.

The summary keeps warm and fallback counts explicit, reports combined outcomes,
query duplication, latency, and normalized phases, and partitions warm work by
newly created versus retained owner. `setup` means warm session creation or
native arena plus solver creation. Native unattributed time is computed only as
the validated total less all native phase clocks. Warm and native structure are
never added into one misleading retained-state total.

The CLI can require the total record count, exact native-fallback count, and
100% decided rate. Homogeneous streams continue to use, and be rejected by the
wrong use of, the existing warm/native tools; the adaptive tool requires both
schemas. This is diagnostic-only and changes no solver, admission, replay,
model, or evidence policy.

## Evidence

Ten focused tests cover mixed ordering, normalized phase accounting, warm
created/retained partitions, empty partitions, homogeneous rejection, and
native one-shot validation. All 51 script tests pass, along with Ruff lint and
format checks.

The first accepted-default SurfacePen profile contains exactly 2,551 complete
records: 2,535 warm and 16 native fallbacks. All decide, agree with Z3, and
retain zero cache/session state at termination. The combined internal total is
509.677 ms. SAT is 28.01%, CNF 21.39%, translation 14.77%, bit blast 14.31%,
replay 11.19%, unattributed work 8.11%, and setup 0.16%. The 16 fallbacks are
only 0.63% of checks but consume 30.691 ms, or 6.02% of total internal time.

Within the warm records, 207 newly created owners consume 78.4% of bit-blast
and 70.7% of CNF time, allocate 87.3% of new AIG nodes and 77.6% of new clauses,
and account for 29.4% of the combined adaptive total. Retained owners consume
94.7% of warm SAT time, 90.2% of warm translation, and 94.3% of warm replay.
This separates two real residuals rather than averaging them into a single
stage rank.

## Consequences

Future adaptive profiles must be summarized without deleting or deduplicating
fallback occurrences. A change to either producer schema requires an explicit
validator update; permissive unknown-schema handling is forbidden.

The next optimization choice must respect the split. Fresh-sibling/policy-
fallback construction is a GQ7/GQ8/GQ9 ownership or immutable-prefix problem,
while retained SAT time is a separate GQ6 problem. Do not use aggregate SAT
share alone to justify tuning before comparing identical emitted CNF, and do
not claim fixed-lineage attribution as the production-policy total.
