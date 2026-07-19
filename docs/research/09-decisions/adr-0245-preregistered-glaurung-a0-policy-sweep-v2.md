# ADR-0245: Preregister Glaurung A0 policy sweep v2 after the usbprint resource failure

Status: deferred
Date: 2026-07-18

Result state: v2 failed closed at maximum's positive-control precision gate

## Context

ADR-0244 fixed a five-policy, three-stratum campaign before observation. That
campaign behaved correctly and failed closed. AnyModel completed the source-
backed positive control, tcpip-prefix-15, and complete usbprint. Minimum
completed the positive and tcpip strata, retaining all 14 validated findings
and exact high-confidence authority parity. All four minimum/usbprint processes
then reported the preregistered 300-second wall-clock safety deadline, so the
runner wrote a rejected report and stopped before maximum and the site-hash
policies.

The failure is policy/resource evidence, not a solver disagreement. AnyModel's
complete 18-of-21-analyzable-function usbprint boundary is not invariant under
extremum probing. Raising the deadline after observing the failure would be an
outcome-adaptive rewrite of v1. Treating four deadline rows as a zero-finding
cell would be worse.

The central sweep question remains unanswered because three executable policies
were never run. The positive-control and tcpip boundaries both passed under
minimum and were already fixed independently of the usbprint outcome.

## Decision

Preregister `glaurung-a0-five-policy-sweep-v2` with the complete five-policy
order unchanged and with two strata:

1. the nine-driver source-backed positive control, requiring exact 14/14
   validation with no unexpected high-confidence row; and
2. the exact first-15-function tcpip discovery boundary, retaining raw,
   high-confidence, diagnostic, work, policy, time, and RSS partitions without
   any finding-direction gate.

Keep every source, Glaurung revision, authority binary, driver, repetition,
order, check timeout, solve budget, process timeout, and policy identity from v1
unchanged for those two strata. Run from the clean detached Axeyum commit that
contains the v1 failure artifact and this v2 registration. The runner must again
stop on the first rejected cell and preserve partial output.

Exclude complete usbprint transparently from the all-policy v2 matrix. Do not
count it as passed, failed recall, or zero output. Track it as a separate
resource frontier that requires a future preregistered bounded-function/work
protocol. This sequencing retains the requested full five-policy experiment
without hiding the wider-driver failure or raising an observed bound.

The aggregate analyzer must carry the registration's acceptance policy and
claim limits into its output. It continues to reject source/binary/environment/
policy/work/coverage drift, missing or unstable cells, corrupt hashes,
non-disjoint confidence partitions, cost omissions, and any positive-control
miss.

## Pre-run evidence

The preserved v1 attempt establishes:

- AnyModel positive control: 14/14 validated, 2,322 solves per authority and
  repetition across nine drivers;
- minimum positive control: 14/14 validated, 60,064 solves per authority and
  repetition;
- AnyModel tcpip: 128 Z3 versus 126 Axeyum raw diagnostics, zero high rows,
  3,079 versus 2,991 solves;
- minimum tcpip: exact 110/110 raw diagnostics, zero high rows, and 80,563
  solves per authority/repetition; and
- minimum complete usbprint: four declared wall-deadline failures, with clean
  stable source identities.

The first four facts are valid partial evidence but do not substitute for the
v2 aggregate gate. V2 reruns them so all policies share one clean source
identity and one unchanged analyzer.

Before results, the updated focused runner/analyzer/harness/validator suite and
all directly runnable script tests must pass; the v2 JSON must resolve every
source/driver/binary hash exactly. No v2 cell may be inspected before this
protocol is committed.

The exact committed run subsequently cleared AnyModel and minimum on both
strata. Maximum also completed both authority reports with exact between-
authority and repeated populations, retained all 14 expected positive-control
findings, and produced zero high-confidence tcpip rows. Its positive validator
nevertheless rejected one additional high-confidence `stack-overflow` at the
existing attacker-controlled `RtlCopyMemory` in `test_physical_memory.sys`.
The runner stopped before either site-hash policy.

Source adjudication rejects that extra classification. `TargetAddress` is read
from the METHOD_BUFFERED input structure and is not a local stack object.
Glaurung `b79f269` classifies the destination as stack when the policy-chosen
concrete `dst` falls within +/-64 KiB of a separately concretized `rsp`.
Maximum can manufacture that accidental numeric proximity. V2 therefore
establishes 14/14 recall but only 14/15 precision for maximum, plus a concrete
correctness requirement: semantic memory-region classification must not depend
on arbitrary model-selected scalar proximity.

## Consequences

V2 was designed to answer whether all five executable scalar policy settings
preserve the 14-row control and how their bounded tcpip diagnostic populations/
work differ. Its fail-closed prefix still cannot establish representative real-
world recall, exhaustive model coverage, exploration equivalence, or solver-
speed superiority.

The result answers only the executed prefix. AnyModel and minimum preserve the
exact 14-row positive set. Maximum preserves recall but violates the exact-set
precision gate; site-hash-zero and site-hash-one remain unobserved. Do not merge
the partial cells into an accepted five-policy sweep. Repair and regression-test
the stack-region predicate first, then preregister a corrected full sweep.

The v1 usbprint failure remains a first-class result and a plan input. A later
usbprint frontier should preregister bounded function counts or deterministic
work limits; it must not inherit “complete” from AnyModel. BoundarySet and
DiverseEnum remain later configurations after bounded successor forking.
Symbolic/symcrete memory remains conditional on a validated residual coverage
gap, not on raw tcpip or usbprint diagnostics.

## Alternatives

- Raise usbprint's deadline and rerun v1: rejected as outcome adaptation.
- Continue maximum/site policies after the v1 runner failed: rejected because
  v1 explicitly stopped on the first failed command.
- Drop usbprint without preserving or discussing it: rejected because its
  resource failure materially limits the policy claim.
- Replace usbprint with an easier positive fixture: rejected because the fixed
  14-row stratum already tests regression, while usbprint's role was discovery
  breadth and cost.
- Start symbolic-memory work from a deadline failure: rejected because no
  independently validated coverage gap was observed.
