# ADR-0212: Defer dxgkrnl direct-delta admission

Status: deferred
Date: 2026-07-17

## Context

ADR-0211 admits one same-session timeout continuation only after Glaurung's
caller has separately selected direct delta. The remaining GQ10 question is
whether source-identity direct delta itself may become the downstream default
over a wider driver set. That decision needs a driver with no continuation
traffic, so enabling the already-admitted continuation policy is an exact
no-op, plus the existing exact-work, correctness, time, RSS, and variance
alarms.

The previously listed `win32k.sys` control is not an IOCTL workload. The real
fixture exposes 1,731 exports and imports `KeAddSystemServiceTable`,
`IoCreateDriver`, and `PsEstablishWin32Callouts`, but Glaurung finds no WDM or
KMDF dispatch roots among 4,629 functions and therefore issues zero solver
queries. It belongs to a future system-service/callout frontend, not to this
IOCTL solver gate. Inventing IRP roots would change the analyzed program rather
than improve coverage.

The real `dxgkrnl.sys` fixture does exercise the production topology without
Axeyum timeouts. It is therefore the next valid no-op control.

## Decision

Defer wider direct-delta admission. Keep
`GLAURUNG_AXEYUM_DIRECT_DELTA` opt-in.

Add an executable `noop` expectation to the native replay comparator. In this
mode, both policies must preserve exact trace/work identity, actual verdicts,
and replay-cache behavior within and across repetitions. The enabled candidate
must perform zero continuations and recoveries. All existing correctness,
terminal-state, time, RSS, and coefficient-of-variation alarms remain
mandatory. The existing recovery expectation remains the default.

Classify `win32k.sys` as outside the current IOCTL frontend. Exclude its zero
queries from solver coverage and performance evidence. Revisit it only through
a sound system-service/callout root model.

## Evidence

### Complete wider trace and independent replay

Clean Glaurung `9ace064` analyzes every available `dxgkrnl.sys` function in
139 dispatch roots under the 4 GiB envelope: 106 functions are available and
analyzed, with no analysis-deadline or work-limit hit. It emits 312 stable
finding rows and records 17,400/17,400 shadow checks with zero decided
disagreement. Z3 takes 47.036 seconds and Axeyum 10.101 seconds, a descriptive
4.7x same-stream ratio. Four Z3 checks are `Unknown`; Axeyum decides all four.

The validated trace contains 85,449 events, 4,258 paths, 13,577 unique queries,
3,005 assertions, 17,400 checks, and 8,816 model reads. Its manifest,
event-stream, and query-index SHA-256 values are respectively
`7c3940794c669d66b85465322afc04643c817337ef43963481b7aa217277982d`,
`9d8331f4be7e259ea2853f124f8d5f104305451c72d449dd3269ec3a2a0ca3f2`, and
`d821b1eff2f7bc63bc226a800c286cdca22f28dbae9750b4da868a27bbb26398`.
The finding stream SHA-256 is
`7249049453930712d7e1264ab6d9fc4792285b6e2941d2b05dd3d802561e7162`.

Axeyum `1cc19181` independently replays all 13,577 queries, 17,400
occurrences, and 8,816 model reads/choices with zero parse, verdict, or model
failure. It observes the recorded 12,852 SAT, 4,544 UNSAT, and four `Unknown`
occurrences. The process takes 2m07s, peaks at 224,636 KiB, and emits report
SHA-256
`93097f4173c2206b734cfcb214f8c7483fb700235337b479f3e8d85facabe443`.

### Repeated no-op comparison

Three ordinary-core fresh-process control/candidate pairs bind identical
trace, findings, replay, executable, and source revisions. Every run performs
17,400 checks, 2,559 exact reuses, 822,993 prefix assertions, 12,863 additions,
10,485 pops, 2,059 owner shares, and the same bounded replay-cache traffic.
Every run produces 12,856 SAT and 4,544 UNSAT actual outcomes, zero `Unknown`,
and four additional decisions relative to recorded Z3 outcomes. Both policies
perform zero continuations and recoveries, and every correctness, reset,
replay, and terminal gauge is zero.

The standard comparison still rejects the artifact. Control Axeyum times are
7.094, 6.584, and 5.319 seconds, for 14.430% CV above the predeclared 3% alarm.
Candidate times are 6.727, 5.830, and 5.859 seconds, for 8.306% CV. The exact
failure text is retained with SHA-256
`23de07fb8a496d13d7be4105a89b425526648d38d09efaec05debe1c287c23dd`.

A diagnostic-only 20% CV comparison reports p50 time/RSS changes of
-11.021%/-0.444% and has SHA-256
`35ff5e16ee6035c25a8766b0ea305527c7af47582cf51272756c9ead264ff415`.
It is not admission evidence. A slower-core calibration stabilized time near
9.6 seconds but crossed the fixed 250 ms first-check deadline: controls varied
between one and two actual `Unknown`s while candidates decided all four. The
new no-op gate correctly rejected that behavior drift. These two failures show
why neither variance thresholds nor semantic identity may be relaxed after
observing a result.

Focused comparator tests cover recovery mode, exact-work drift, resource
alarms, exact no-op acceptance, within-policy no-op drift, and nonzero no-op
continuation rejection.

## Alternatives

- Accept the diagnostic median improvement: rejected because the control and
  candidate both fail the declared 3% stability rule.
- Raise the CV limit after observing the samples: rejected as threshold
  shopping.
- Select only the stable-looking repetitions: rejected because it discards the
  declared complete sample.
- Use the slower-core runs: rejected because the fixed deadline changes actual
  outcomes and cache traffic, so the policy is not an exact no-op there.
- Count `win32k.sys` as a zero-query success: rejected because it measures a
  missing frontend, not solver behavior.
- Force IRP roots into `win32k.sys`: rejected because unsound roots would make
  the workload synthetic while being labeled real.

## Consequences

The wider `dxgkrnl.sys` functionality boundary is green: strict translation,
native topology, exact replay, model checking, and the enabled continuation
policy's no-op behavior all work on the ordinary-core runs. It does not yet
justify a downstream default or a performance claim.

Repeat the same predeclared no-op comparison in a quieter or exclusive
environment, or add another valid no-timeout IOCTL driver. Admission still
requires exact behavior and at most 3% Axeyum-time CV without changing the
thresholds. Meanwhile the pure-solver lane may proceed with measured cold
term-to-AIG-to-CNF construction, which remains ahead of SAT tuning. Preserve
the strict-sort, honest-`Unknown`, original-model-replay, bounded-resource, and
no-fast-failure feedback invariants throughout.
