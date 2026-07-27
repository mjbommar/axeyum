# ADR-0371: Preregister definite-result retention across the combined-theory deadline

Status: rejected

Date: 2026-07-27

## Context

The frozen 108-family QF_BVFP diagnostic leaves 20 process non-decisions after
ADR-0370. Route explanation classifies the set as pure BV after FP lowering; the
dominant reason is `combined-theory timeout after scalar backend`, not a missing
FP operator. At a ten-second budget, seven rows decide in 2.017--7.123 seconds.

`check_with_all_theories` passes the scalar backend only the remaining shared
deadline, but then unconditionally replaces even a definite `Sat` or `Unsat`
with timeout if the backend returns just after the wall-clock boundary. It also
abandons model projection and replay after a definite `Sat`. The preprocessing
dispatcher already carries the intended contract: deadlines bound search; a
definite verdict is retained, and bounded model reconstruction/replay completes
before publication.

## Candidate

**Apply that existing contract to the combined-theory route.** If the scalar
backend returns `Unknown` after the deadline, keep the classified combined
timeout. If it returns a definite result, do not discard it solely because the
clock crossed the boundary:

- exact integer-free `Unsat` remains `Unsat`;
- bounded-integer `Unsat` remains conservatively `Unknown` under the existing
  incompleteness rule; and
- `Sat` must still complete integer/function/array model projection and replay
  every original assertion before publication.

No additional search, retry, widened timeout, operator, theory, or unchecked
evidence route is admitted. Operational elapsed time may exceed the requested
search budget by the already-running backend's polling granularity plus bounded
validation, and measurements must report that honestly.

## Acceptance result

The implementation and deterministic delayed-backend tests behaved as designed:
definite integer-free `Unsat` and replayed `Sat` survived deadline crossing,
while an expired `Unknown` stayed a classified timeout. The existing combined
integration suite also passed.

The measured selection gate failed:

- the frozen 108-family four-process diagnostic remained exactly 88 correct, 18
  unknown, two outer process timeouts, and zero wrong;
- an immutable `235f7b21` baseline binary and the candidate binary were run
  serially on the seven rows which decided within ten seconds;
- all seven verdicts were identical: `sqr_double-noflow` stayed SAT,
  `prefix_sum_klee_bug_double` stayed UNSAT, and the other five stayed unknown;
  paired elapsed differences were only -100 to +100 ms except a -198 ms
  candidate point on `prefix_sum`, with no decision change; and
- representative pairs were 2.417/2.414 s unknown (`diction`), 2.617/2.611 s
  unknown (`inf_double`), 2.716/2.717 s unknown (`sqr_float`), and
  4.714/4.814 s unknown (`filter1`) for baseline/candidate respectively.

The candidate therefore selects no capability or performance improvement. The
production and test edits were removed; only this negative record remains.

## Alternatives

### Increase the family-sample timeout

Rejected. It would move the measurement boundary without repairing the
inconsistent definite-result policy and would tax every query.

### Return immediately on an expired definite SAT

Rejected. SAT is publishable only after projection and original-query replay.

### Add a retry after timeout

Rejected. The backend already completed once; a retry adds search and changes
resource accounting rather than preserving a result already obtained.

## Consequences

The combined route keeps its existing deadline behavior. The residual cluster
must be attacked inside the scalar BV search/encoding path rather than by
changing the post-return deadline wrapper. The observation that one explanation
probe exceeded its internal two-second budget remains a separate deadline-
polling diagnostic, not evidence for this rejected result-retention policy.
