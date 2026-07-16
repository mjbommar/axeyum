# ADR-0205: Accept the source-prefix production gate and widen before default

Status: accepted
Date: 2026-07-16

## Context

ADR-0204 supplies exact source ancestry for Glaurung's direct serial sibling
candidate. The implementation must now be judged against the actual current
serial-snapshot policy, not only an exclusive-transfer control. Meanwhile, new
single-process shadow evidence widens the workload with `tcpip` (33,501 checks)
and `dxgkrnl` (17,572 checks), both disagreement-free but not yet repeated or
RSS-gated. `win32k` and `pciidex` reach zero solver queries and therefore cannot
count as solver coverage.

## Decision

Accept Glaurung ADR-014/`29031f8` as clean repeated evidence that source-prefix
direct reuse beats the current two-driver serial-snapshot production policy.
Keep direct entry opt-in until the new large drivers enter the same repeated,
fail-closed gate and the exclusive-control environment alarm is resolved.

Treat `win32k`'s zero-query outcome as a Glaurung dispatch-recovery investigation
separate from Axeyum solver correctness/performance. Never add zero-query drivers
to decided-rate or speedup denominators.

## Evidence

The committed source-prefix artifact executes three SurfacePen and three
NETwtw10 processes: 92,721 exact checks, 100% Z3 agreement, identical findings,
zero unknown splits/replay failures, exact direct/serial/cache traffic,
terminal-zero gauges, and a 4 GiB child cap. Its SHA-256 is
`ba006d2f8edfdf7754f09702ff172112c5ea3e1134669a7855f5a0a3343660cc`.

Against the committed serial-snapshot production baseline:

- SurfacePen Axeyum time improves 16.11%, normalized ratio 17.39%, and median
  RSS 0.36%; absolute Z3 drift is +1.55%.
- NETwtw10 improves 6.07%, 6.61%, and 1.72%; Z3 drift is +0.58%.

Every production alarm passes. A fresh same-revision exclusive-direct control
also favors source-prefix time/RSS by 23.17%/5.33% on SurfacePen and
4.40%/15.81% on NETwtw10, but SurfacePen Z3 drift is +4.06%. That causal
comparison remains rejected; no threshold is waived.

The comparator now excludes only absolute sample path from identity, matching
the documented provenance contract. Driver content hash, byte length, solve
budget, membership, system, repetitions, findings, work, and all thresholds
remain exact. A regression test proves clean detached paths compare without
weakening content identity.

## Alternatives

- Enable direct immediately: rejected because the newly available 51,073-query
  widening tier is not repeated/RSS-gated.
- Waive the exclusive-control Z3 drift: rejected because it would make the
  causal timing claim non-comparable.
- Count zero-query drivers: rejected because they do not exercise the solver
  seam.
- Require equal absolute sample paths: rejected because identical content in a
  clean worktree would become incomparable for no semantic reason.

## Consequences

GQ7 source-prefix functionality and its current production comparison are
complete; generic Axeyum defaults do not change. GQ10 widening is now the next
client gate: add exact `tcpip` and `dxgkrnl` identities/traffic, run repeated
processes with RSS, and only then revisit Glaurung's direct default. In parallel,
Glaurung should diagnose `win32k` dispatch recovery without attributing that
frontend gap to Axeyum.
