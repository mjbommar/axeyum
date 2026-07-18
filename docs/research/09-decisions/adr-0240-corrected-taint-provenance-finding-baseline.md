# ADR-0240: Corrected taint provenance before policy coverage scoring

Status: accepted
Date: 2026-07-18

## Context

ADR-0236 through ADR-0239 compare raw Glaurung sink populations under AnyModel,
global extrema, and complementary site schedules. They establish deterministic
authority controls, but the next plan treated two Z3-only tcpip rows and 33
arbitrary-only rows as potential true-positive recall that BoundarySet or
DiverseEnum should recover.

Exact PDB, disassembly, and ordered-trace inspection of the two named rows found
an upstream analyzer defect. An uninitialized load through any tainted address
discarded its source labels and marked the fresh value `*attacker`. This
laundered generic entry-argument ancestry past ioctlance's existing `ArgN`
confidence filter. The coverage objective therefore had to be corrected before
preregistering another model-selection sweep.

## Decision

Accept Glaurung's exact-source taint-provenance correction and require future
concretization-policy sweeps to report raw diagnostics, confidence-gated
findings, and independently labeled true/false-positive partitions separately.

Raw sink equality remains a deterministic authority and explorer-regression
gate. It is not a recall ground truth. A policy must not be accepted merely for
maximizing or containing the arbitrary-model raw union. Select a fixed-work
corpus with nonzero labeled positives before preregistering recall or precision
thresholds. Keep BoundarySet and DiverseEnum as configurations of the accepted
A0 `ConcretizationPolicy`; begin symbolic memory only if that corrected cheap
sweep leaves validated coverage headroom.

## Evidence

Glaurung commit `845239f0b120916b93ce224272ef8225c62b11e4`
adds a red-then-green test requiring an uninitialized mixed-source load to
retain `*Arg0` and `*SystemBuffer`, not generic `*attacker`. All 18 explorer
tests pass. The correction stores stable label sets and prefixes every exact
address source through memory.

PDB symbols place both Z3-only sites in the 2,104-byte internal
`TcpSendTrackerMarkTransmits` procedure at `0x1c0008270`. The instructions read
tree-node fields at offsets `-0xc` and `+0x8`. A valid Z3-authoritative trace
shows the addresses derive from generic `Arg0` and fresh values loaded through
that ancestry.

Two clean fixed-work repetitions per authority preserve the raw AnyModel
relation at 128 Z3 versus 126 Axeyum rows, now with the two differences labeled
`**Arg0`. Normal confidence-gated runs report zero findings under both
authorities. Least unsigned remains exactly 110 raw rows under each authority,
and every row carries only `Arg0`, `Arg1`, or their dereferences, so its
confidence-gated population is also empty. Exact source, binary, input, work,
telemetry, and finding partitions are retained in
[`RESULTS.md`](../../../bench-results/glaurung-tcpip-taint-provenance-20260718/RESULTS.md).

## Alternatives

- Keep `*attacker` and document the false positives: rejected because it
  destroys source provenance and corrupts the existing confidence policy.
- Special-case the two addresses: rejected because the defect applies to every
  uninitialized tainted load.
- Treat all `ArgN` dereferences as attacker controlled: rejected because that
  restores the noise the confidence gate was designed to suppress.
- Drop raw parity: rejected because it remains valuable deterministic explorer
  evidence when labeled honestly.
- Preregister BoundarySet against raw `>= AnyModel`: rejected because the
  objective would reward known analyzer noise.

## Consequences

ADR-0236 through ADR-0239 remain valid for their bounded raw determinism and
authority-parity claims, but ADR-0240 supersedes their use as a finding-recall
frontier. The two Z3-only rows are classified as model-sensitive false-positive
diagnostics, not known missed double fetches. The 33 arbitrary-only rows remain
unclassified.

Phase 0/A0 is still accepted and remains the enabling refactor. Phase 2 is a
configuration sweep after rebaselining and labeling, not a build. A2 symbolic
memory remains the only architectural project and is conditional on residual
validated headroom. This lowers implementation risk while strengthening the
publication claim: reproducible policy comparison replaces a hand-tuned raw
count.
