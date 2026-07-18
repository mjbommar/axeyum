# ADR-0235: Killable QF_BV whole-certificate process isolation

Status: accepted
Date: 2026-07-18

## Context

ADR-0231 bounds the two proof searches cooperatively, and ADR-0234 certifies
every UNSAT in the corrected representative Glaurung corpus. Their explicit
remaining trust/availability caveat is that parsing, independent-reference and
production construction, CNF encoding, and completed-proof checking run to
completion in the benchmark process. A slow or wedged non-search phase can
therefore outlive the named search deadline and block later denominator rows.

Killing the complete corpus process is not acceptable: it loses the active row
and every later row, making coverage depend on finishers. A timeout must remain
a non-certification outcome, never SAT, UNSAT, an invalid proof, or an omitted
query.

## Decision

Advance `axeyum-bench` to artifact version 34 and add the optional
`--end-to-end-process-timeout-ms N` policy. After a primary UNSAT, the parent
launches the same pinned executable through a private, versioned one-query
protocol. It passes the exact source hash and cooperative proof-search budget.
The worker must:

1. re-read and match the exact source bytes;
2. parse the raw full query;
3. construct the independent-reference miter and final CNF refutation;
4. self-recheck both stored certificate texts; and
5. return one strict JSON status.

The parent starts the wall budget before spawn, polls at one-millisecond
resolution, and kills and reaps an overdue worker. A hard timeout is a counted
subset of `not-certified`; it remains in the primary UNSAT denominator.
Completed `certified` output is accepted only when the worker explicitly marks
both proofs self-rechecked. Source drift, spawn/wait failure, nonzero exit,
malformed or wrong-version output, satisfiable contradiction, recheck failure,
and operational error remain fatal alarms.

Keep the in-process cooperative route available for historical compatibility,
but require subprocess isolation in the artifact-v34 publication analyzer.
Fingerprint the process timeout in `config_hash`. Record isolation mode,
process timeout, hard-timeout flag/count/paths, and whole-worker elapsed time
per instance and in summary. These remain separate assurance costs, not solver
performance.

## Evidence

At clean source `e1be4bd1`, two CPU-3-pinned runs apply a 1000 ms cooperative
search deadline inside a 1500 ms process wall to ADR-0187's exact corrected
162-query representative manifest:

- 162/162 primary queries decide as 88 SAT / 74 UNSAT with zero Unknown,
  unsupported, error, oracle disagreement, or manifest disagreement;
- all 88 SAT models replay against the original query;
- all 74 primary UNSAT CNF DRAT proofs independently recheck;
- all 74 whole-process workers return self-rechecked end-to-end certificates;
- zero row is not-certified, hard-timed-out, contradicted, recheck-failed, or
  errored in either run.

Whole-worker p50/p95/max is 3.457/60.108/155.685 ms and
3.534/59.098/157.768 ms. These timings include process startup, source
identity, construction, both proof searches, and both completed-proof checks.

A separate same-source/manifest control sets the process wall to 1 ms. The
primary population remains 88 SAT / 74 UNSAT; all SAT replay and primary CNF
DRAT gates remain green. Every one of the 74 UNSAT rows is retained as both
`not-certified` and `hard_timeout`, with zero alarm or missing partition. Its
p50/p95/max whole-worker return is 1.172/1.299/1.456 ms, including scheduling,
one-millisecond polling, kill, and reap overhead.

Raw artifacts and the fail-closed repetition join are committed under
[`bench-results/glaurung-real-query-faithfulness-isolated-20260718/`](../../../bench-results/glaurung-real-query-faithfulness-isolated-20260718/README.md).

## Consequences

The publication may state that all 74 UNSAT rows in the complete corrected
five-driver representative denominator certify end to end under a killable
1500 ms whole-worker policy. The separate 1 ms control demonstrates that
expiry preserves the denominator and is not rewarded as a fast verdict.

This closes the explicit whole-certificate process-isolation gap for the
representative denominator. The wall is a worker-computation policy plus
scheduler/poll/kill/reap overhead, not a real-time operating-system guarantee.
It does not widen proof coverage to the 30,628-query full corpus, standardize
the proof format, or change cold/warm performance claims.

Next correctness work is wider real-query proof populations and independent
fuzz seeds plus another neutral implementation. Timeout-sensitive/wider
sole-authority findings remain a separate publication blocker.

## Alternatives

- Kill the full corpus process: rejected because it drops the current and later
  denominator rows.
- Put only the SAT searches in a child: rejected because construction/checking
  are the gap this decision closes.
- Trust `certified` without worker self-recheck: rejected because it weakens the
  existing two-proof consumer-side check.
- Treat kill as proof failure or solver timeout: rejected because it says only
  that stronger evidence was unavailable under the policy.
- Require the isolated route in the public solver API: rejected because an
  in-memory arena is not a stable cross-process interchange format; this is an
  artifact/evidence harness boundary.
