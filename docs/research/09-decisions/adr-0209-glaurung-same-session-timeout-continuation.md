# ADR-0209: Keep Glaurung same-session timeout continuation opt-in

Status: candidate
Date: 2026-07-16

## Context

ADR-0208 rejects rebuilding a complete cold solver after a retained Glaurung
check times out: it recovers only four of fifteen tcpip occurrences and raises
RSS 10.46%. The incremental SAT instance retains its clauses and learned state,
and each bounded `solve` call installs a fresh deadline. A second check on that
same synchronized instance could therefore recover a decision without copying
the arena, AIG, or CNF.

## Decision

Keep Glaurung ADR-018/`6e5b255` as an explicit, off-by-default candidate.
`GLAURUNG_AXEYUM_WARM_TIMEOUT_CONTINUE=1` grants exactly one additional 250 ms
check after a direct retained check returns `Unknown`. The continuation uses the
same solver and, for temporary assumptions, the same translated `TermId`s. A
SAT/UNSAT continuation result is returned; another `Unknown`, error, or missing
solver preserves the original `Unknown`. Counters partition continuations into
recoveries, repeated unknowns, and errors.

Do not admit it as an automatic policy from the current wall-time evidence.
Require a fixed-work or repeated comparison whose workload and finding set are
exact before default consideration.

## Evidence

The Axeyum CNF regression first forces `IncrementalSat` to return `Unknown` with
a zero deadline and then proves that the same instance decides SAT under a new
bounded deadline. The complete `axeyum-cnf` library suite passes 298/298. The
downstream combined Z3+Axeyum backend group passes 45/45.

On the 60-second tcpip tier, the candidate performs 14 continuations = 6
recoveries + 8 repeated unknowns + 0 errors, reduces Axeyum nondecisions 15→8,
and has zero SAT/UNSAT disagreements or warm resets. Time rises about 1.1% and
RSS falls slightly, but query traffic drifts. The dxgkrnl control performs zero
continuations and has zero Axeyum nondecisions/disagreements; its wall-time
traffic also drifts.

On a 600-second tcpip control/candidate pair, the candidate performs 14
continuations = 5 recoveries + 9 repeated unknowns + 0 errors. Axeyum
nondecisions fall 14→9, time rises 204,294.1→208,331.4 ms (+1.98%), and RSS
rises 449,224→449,376 KiB (+0.034%), inside the 3%/5% alarms. It executes
70,581 rather than 70,562 queries and both processes hit the 400-second analysis
deadline. The candidate retains all 780 unique control findings and reports two
additional null dereferences in `sub_1c00738a0`. This is not an exact-work
causal comparison, so neither the recoveries nor added coverage justify a
default.

## Alternatives

- Rebuild a fresh solver: rejected by ADR-0208's memory result.
- Increase the timeout for every check: rejected because it taxes the common
  path and changes the production resource contract.
- Continue without a bound or more than once: rejected because `Unknown` must
  remain a deterministic resource outcome.
- Claim the two additional findings as a semantic win: rejected because query
  traffic differs and both runs are analysis-deadline-limited.

## Consequences

Same-session continuation is a viable low-memory diagnostic and establishes
that bounded incremental SAT solving can resume under a fresh deadline. It is
not yet a production policy. GQ10 widening now needs a fixed-work ordered replay
or repeated DriverSpec gate that holds query/finding identity constant, followed
by the existing time, ratio, RSS, disagreement, reset, replay, and variance
alarms. Zero-query win32k remains a separate frontend coverage gap.
