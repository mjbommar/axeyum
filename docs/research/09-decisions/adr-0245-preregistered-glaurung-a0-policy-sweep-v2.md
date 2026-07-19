# ADR-0245: Preregister Glaurung A0 policy sweep v2 after the usbprint resource failure

Status: proposed
Date: 2026-07-18

Result state: protocol preregistered; results pending

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

## Consequences

V2 can answer whether all five executable scalar policy settings preserve the
14-row control and how their bounded tcpip diagnostic populations/work differ.
It still cannot establish representative real-world recall, exhaustive model
coverage, exploration equivalence, or solver-speed superiority.

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
