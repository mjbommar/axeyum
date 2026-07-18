# ADR-0236: Canonical tcpip authority policy

Status: accepted
Date: 2026-07-18

## Context

ADR-0229 found exact Z3/Axeyum sole-authority output parity on four bounded
drivers and explicitly deferred canonical model selection until a wider or
timeout-sensitive tier produced a stable backend-only sink. The reviewer
checklist requires more than verdict parity because different satisfying
models can change concretization, exploration, and ultimately reported bugs.

The current tcpip experiment activates ADR-0229's reopen condition. With the
same current Glaurung source, binaries, 250 ms native check wall, and first 15
analyzed functions, three repetitions of each any-model authority are
individually stable but not equal: Z3 emits two double-fetch rows that Axeyum
does not. A model policy is therefore measured work rather than speculative
normalization.

## Decision

Accept `glaurung-min-unsigned-v1` as an **opt-in experiment policy** for
backend-independent Glaurung concretization and representative-value choices.
For each expression, first prove the active path feasible, then use temporary
unsigned `<=` probes to find the least value and recheck the final equality.
Do not persist search probes into the path condition. Fail closed on unknown,
missing solver, backend error, unsupported width, or an unexpected final
UNSAT; classify an already-infeasible path separately.

Require sole-authority reports to name and exercise the policy, use an explicit
common per-check timeout, account for every attempt and failure reason, retain
stable telemetry per authority across repetitions, and reject any
inconclusive choice or ordered finding-list difference.

Keep Glaurung's existing any-model behavior as the default. Canonicalization
changes the explored finding population and is not admitted as a production
coverage improvement by this experiment.

## Evidence

Both cells use Glaurung `fb051de7`, Axeyum runner `23b9caef`, the same two
authority binaries, tcpip input hash, first 15 of 338 reachable functions, and
three order-balanced repetitions at a 250 ms check wall.

| Policy | Z3 findings / solves | Axeyum findings / solves | Stable shared | Backend-only | Exact parity |
|---|---:|---:|---:|---:|---|
| Any model | 128 / 3,079 | 126 / 2,991 | 126 | 2 Z3 / 0 Axeyum | no |
| Least unsigned | 110 / 80,563 | 110 / 80,563 | 110 | 0 / 0 | yes |

All six canonical processes emit the same ordered finding hash. Each authority
also reports the same 1,206 policy attempts, 1,204 completed minima, two
already-infeasible paths, and 79,466 probes. Every inconclusive-reason counter
is zero. Thus the canonical cell reaches both output parity and identical
measured exploration counters for this prefix, while the rejected any-model
cell preserves the motivating divergence rather than normalizing it away.

The exact reports, hashes, claim limits, and reproducible four-patch Glaurung
series are committed under
[`bench-results/glaurung-tcpip-canonical-authority-20260718/`](../../../bench-results/glaurung-tcpip-canonical-authority-20260718/README.md).

## Alternatives

- Report only SAT/UNSAT agreement: rejected because the measured finding lists
  differ under unrestricted model choice.
- Compare only finding counts: rejected because it neither identifies the two
  backend-only rows nor protects against equal-size different sets.
- Pick one backend's model as canonical: rejected because it makes that solver
  authoritative again and cannot test backend-independent exploration.
- Enable the minimum policy by default: rejected because it changes the common
  any-model population from 126 shared findings to 110 and has not been shown
  to improve coverage.
- Complete the 30-function prefix under the initial 200,000-solve ceiling:
  rejected after the live solve-rate projection showed that the ceiling would
  become the work boundary. The run was interrupted without an artifact and
  replaced by the measured divergent 15-function prefix rather than accepting
  a misleading partial-prefix comparison.

## Consequences

The publication may state that the measured tcpip prefix has stable
backend-dependent findings under arbitrary model choice and exact
Z3/Axeyum-authority parity under one explicitly named canonical policy. This
closes the reviewer-requested canonical-policy mechanism and one
timeout-sensitive/wider authority cell; it does not establish parity for all
tcpip functions or all Glaurung workloads.

The result is not evidence that canonicalization preserves every reachable
finding. A future coverage claim needs wider fixed-work prefixes, additional
drivers, or a deterministic multi-model/path-enumeration policy that measures
the union rather than choosing one representative. The policy's roughly
80,000 checks per process also make its standalone timing unsuitable for a
solver-speed headline or default-admission argument.
