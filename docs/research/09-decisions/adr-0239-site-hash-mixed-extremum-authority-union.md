# ADR-0239: Site-hash mixed-extremum authority union

Status: accepted
Date: 2026-07-18

## Context

ADR-0238 establishes exact backend-independent authority parity for the union
of all-minimum and all-maximum canonical exploration on a fixed tcpip prefix.
That union has 125 findings, but it does not subsume the arbitrary-model
population: 33 arbitrary-model rows are absent, while 30 rows appear only under
the two extrema. Repeating the same two global corners on a wider prefix would
increase fixed work without testing whether mixed deterministic choices recover
coverage hidden between those corners.

The next `PLAN.md` boundary therefore calls for genuinely broader deterministic
model exploration. This ADR fixes one bounded extension before its full result
is observed.

## Decision

Add two complementary site-hash policies beside `glaurung-min-unsigned-v1` and
`glaurung-max-unsigned-v1`:

- `glaurung-site-hash-0-v1` computes FNV-1a-64 over the fixed choice-purpose
  bytes followed by the instruction address in little-endian form, then selects
  minimum or maximum from the hash high bit.
- `glaurung-site-hash-1-v1` flips every selection made by schedule zero.

The selector excludes solver output, expression IDs, process order, and mutable
attempt counters. The pair therefore assigns complementary, backend-independent
extrema to every stable choice site. Together with all-minimum and all-maximum,
it forms a four-schedule deterministic ensemble. This is broader combinatorial
exploration, not enumeration of every model.

Use Glaurung commit `e98c0902d8f232dee8cd6348cffab79dade3eec7`, tcpip SHA-256
`ff965206a37f2c258b7199bc87b49ee12c834e5fc50f58dae2f3de66a57022ea`,
the first 15 of 338 reachable functions, a common 250 ms check wall, a 300,000
solve budget, a 1,800-second process wall, and three order-balanced repetitions
per policy and authority. Build separate sole-Z3 and sole-Axeyum binaries from
the same source. Run arbitrary, minimum, maximum, site-hash-zero, and
site-hash-one cells with the exact committed runner.

## Acceptance contract

Accept the bounded four-schedule union only if all of the following hold:

1. The arbitrary-model control remains stable, rejected, and reproduces
   ADR-0236/0238's exact ordered-list hashes and two Z3-only rows.
2. The minimum and maximum controls reproduce ADR-0238's exact ordered-list
   hashes under the new same-source binaries.
3. Each site-hash policy has byte-identical ordered findings under Z3 and
   Axeyum authority in all six processes.
4. Each canonical policy has identical repetition-stable solve counts and
   attempt/probe/reason telemetry across authorities, with zero inconclusive
   choice.
5. Source, binary, input, fixed-work, timeout, environment, repetition, and
   execution-order identities match across all five cells.
6. The four-policy union is identical under both authorities. Per-policy unique
   rows, membership counts, the extension over two extrema, and overlap with
   the arbitrary-model combined union remain explicit.

Do not require either site policy to add findings, recover any of the 33 prior
arbitrary-only rows, or reduce the arbitrary-only remainder. Those are outcomes,
not acceptance criteria. Preserve a clean negative result if a fail-closed gate
does not pass; do not change the schedule, prefix, or policies in response.

## Preregistered implementation and protocol

The source series is committed as
[`glaurung-site-schedule-model-selection.mbox.gz`](../../../bench-results/glaurung-tcpip-site-schedule-union-20260718/glaurung-site-schedule-model-selection.mbox.gz),
SHA-256 `934c1d82428f840711e9358d59afd526cbfed7547627ea1b62a6969b7656eb98`.
The exact orchestration is
[`scripts/run-glaurung-authority-site-schedule-union.sh`](../../../scripts/run-glaurung-authority-site-schedule-union.sh),
and the fail-closed cross-cell checker is
[`scripts/analyze-glaurung-authority-site-schedule-union.py`](../../../scripts/analyze-glaurung-authority-site-schedule-union.py).

Before the campaign, 18 focused Glaurung exploration tests pass under both
`solver-z3` and `solver-axeyum`; the site selector's exact frozen sample covers
both directions and proves the schedules complementary. All 25 affected
runner/analyzer tests, Python syntax checks, legacy artifact replay, and shell
validation pass. These engineering checks are not campaign evidence.

### Fail-closed attempt history

The first exact attempt reproduced the rejected arbitrary-model control and all
six minimum-policy outputs, including the exact 110-finding ordered-list hash,
solve counts, and canonical telemetry. It then failed the post-run Axeyum source
identity gate because a concurrent tracked planning-document edit appeared in
the main worktree during measurement. The runner stopped before maximum or
either site-hash policy was observed. Preserve this attempt as inadmissible
provenance; do not count it as campaign evidence.

The same committed runner was rerun from a detached Axeyum worktree at the exact
preregistration commit `57ee6720`. The isolated worktree prevented unrelated
workspace writes from changing measured source identity. No experiment source,
input, policy, seed, execution order, fixed-work boundary, acceptance gate, or
resource bound changed.

## Result

The isolated exact rerun passes every gate. The arbitrary-model control remains
rejected with 126 stable shared rows and two Z3-only rows. Minimum reproduces
110 findings and 80,563 solves; maximum reproduces 84 findings and 34,659
solves. Site-hash-zero produces 95 findings, 28,258 solves, 419 completed
choices, and 27,654 probes. Site-hash-one produces 98 findings, 79,950 solves,
1,195 completed choices, and 78,872 probes. Each canonical count, ordered-list
hash, work count, and telemetry partition is identical in all three repetitions
under both authorities, with zero inconclusive choice.

The two site schedules have a 122-row union. They add three rows beyond the
125-row minimum/maximum union, yielding an authority-identical 128-row
four-schedule union. Membership is 69 rows in all four policies, two in three,
48 in two, and nine in one. Policy-unique counts are maximum 6, minimum 0,
site-hash-zero 3, and site-hash-one 0.

Against the arbitrary-model combined union, 95 rows are shared, 33 remain
arbitrary-only, and 33 are four-schedule-only. Thus the genuinely broader
deterministic pair grows the extremal union but recovers none of the prior 33
arbitrary-only rows. The accepted claim is exactly bounded deterministic
four-schedule mixed-extremum authority parity. Detailed partitions and artifact
hashes are in
[`RESULTS.md`](../../../bench-results/glaurung-tcpip-site-schedule-union-20260718/RESULTS.md).

## Consequences

The paper may report authority parity for this bounded
four-schedule deterministic ensemble and its exact incremental coverage over
two global extrema. It may not call four schedules exhaustive, claim finding
preservation unless the measured set relation actually supports it, prove that
neither solver misses a true positive, or treat policy-dependent process times
as solver performance.

The default Glaurung behavior remains arbitrary model choice. All four
canonical policies remain experimental and opt in. No Axeyum IR, solver,
evaluator, proof, or public logic-fragment contract changes.
