# ADR-0249: Preregister the usbprint policy-resource frontier

Status: accepted
Date: 2026-07-19

Result state: preregistered; no new frontier cell observed

## Context

ADR-0244's complete-usbprint cell is a retained resource failure, not a finding
or solver disagreement. AnyModel completed 18 of 21 reachable functions with
zero high-confidence rows and 16,537 solves per authority/repetition. All four
minimum-policy processes hit the fixed 300-second in-process deadline, so the
campaign correctly stopped before maximum and both site-hash policies.

ADR-0245 moved usbprint out of the all-policy sweep rather than raising an
observed deadline. ADR-0247 subsequently accepted all five scalar policies on
the positive and tcpip strata, and ADR-0248 found no independent primitive in
their complete source-backed difference. Usbprint therefore remains only a
policy-resource frontier. It cannot reopen the coverage or symbolic-memory
lane.

## Decision

Preregister a point-major frontier at deterministic reachable-function prefixes
5, 10, and 15. At each point run the five accepted scalar policies in their
standing order. Every cell uses two order-balanced sole-authority repetitions,
the existing 250 ms per-check limit, a 300,000-solve/300-second per-function
ceiling, an 1,800-second in-process safety deadline, and a 1,920-second process
timeout.

The 5/10/15 points are fixed arithmetic prefixes below the known AnyModel
complete boundary of 18; 15 also matches the established tcpip fixed-function
boundary. They were selected before observing a new usbprint cell.

Run from final corrected Glaurung `7f682e5` with the exact v3 Z3/Axeyum
authority binaries. The runner stops at the first non-complete cell. An exact
four-run in-process deadline outcome is a resource-bound observation; every
other process, parser, identity, work, policy, coverage, partition, or report
failure is a protocol failure. Point-major order ensures that a stop at 15 can
still establish a common prefix of 10 across all policies.

The machine-readable protocol is
`corpus/glaurung-finding-populations/usbprint-policy-frontier-v1.json`.
The runner and analyzer refuse source/hash/work drift and output overwrite.

## Acceptance

A complete cell must have exact fixed-work-limit coverage, stable repeated
high-confidence output, exact authority parity, zero high-confidence rows,
correct policy telemetry, and complete solve/time/RSS counters. Raw diagnostics
remain descriptive.

The aggregate accepts either:

1. all 15 cells complete, establishing a common prefix of 15; or
2. all five policies complete at one or more lower points followed by an exact
   resource-bound stop, establishing the largest complete common prefix and an
   upper resource bracket.

No complete common prefix, a protocol failure, or identity/hash/work drift
rejects the result.

## Consequences

This closes the explicitly deferred bounded usbprint protocol without changing
the failed complete-driver experiment. It measures policy integration cost and
coverage under deterministic function prefixes, not solver speed, real-driver
recall, or complete-driver equivalence.

The prior AnyModel-complete/minimum-deadline reports remain historical anchors
at Glaurung `b79f269`; they are not cells in the new `7f682e5` matrix. No
usbprint frontier result can by itself admit symbolic memory, multi-successor
policies, or a different scalar default.
