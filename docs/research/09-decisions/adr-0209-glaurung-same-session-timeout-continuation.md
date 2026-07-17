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

Do not admit it as an automatic policy from the current wall-time evidence. A
live fixed-function-prefix comparison subsequently failed exact identity;
ADR-0210's ordered occurrence replay now passes the independent mechanism gate.
Default consideration still requires a native production-topology repeat whose
workload and finding set are exact.

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

Glaurung `399c770` then adds a deterministic
`IOCTLANCE_MAX_ANALYZED_FUNCTIONS` boundary. Both tcpip processes complete the
same 156/338-function prefix and hit `WORK-LIMIT-HIT`, never the 3,600-second
safety deadline. Live exploration nevertheless remains non-identical. Control
executes 70,592 queries with 47 Z3 / 11 Axeyum nondecisions and 782 findings;
continuation executes 70,768 queries with 46 Z3 / 8 Axeyum nondecisions and 783
findings. Their sets contain 781 shared findings, one control-only double fetch,
and two candidate-only read/null-deref rows. One changed bounded Z3 nondecision
is enough to steer a different authoritative worklist inside the same function
prefix.

The candidate's fixed-prefix counters are 11 continuations = 3 recoveries + 8
repeated unknowns + 0 errors. Axeyum time changes
133,279.7→135,233.6 ms (+1.47%) and RSS 440,280→441,088 KiB (+0.18%), inside
the alarms, with zero SAT/UNSAT disagreements, resets, or replay failures.
These resource deltas are descriptive only because query/finding identity
fails. Glaurung `61b008f` records the rejection.

ADR-0210 supplies the missing fixed-work mechanism gate. Glaurung `3c3c77e`
publishes one validated 70,823-check tcpip stream with shared-DAG SMT-LIB
payloads. The independent candidate performs 14 continuations = 7 recoveries +
7 repeated unknowns + 0 errors, with exact work/structure/model identity, zero
decided disagreements, +1.97% warm replay time, and +0.034% RSS. This accepts
the bounded same-instance mechanism; it does not reproduce Glaurung's native
source-owner/serial-lease topology.

## Alternatives

- Rebuild a fresh solver: rejected by ADR-0208's memory result.
- Increase the timeout for every check: rejected because it taxes the common
  path and changes the production resource contract.
- Continue without a bound or more than once: rejected because `Unknown` must
  remain a deterministic resource outcome.
- Claim the two additional findings as a semantic win: rejected because query
  traffic differs and both runs are analysis-deadline-limited.

## Consequences

Same-session continuation is a causally validated low-memory mechanism and
establishes that bounded incremental SAT solving can resume under a fresh
deadline. It is not yet a production policy. GQ10 widening now needs a native
repeat in the real source-owner/serial-lease topology with exact traffic and
findings plus the existing time, ratio, RSS, disagreement, reset, replay, and
variance alarms. Zero-query win32k remains a separate frontend coverage gap.
