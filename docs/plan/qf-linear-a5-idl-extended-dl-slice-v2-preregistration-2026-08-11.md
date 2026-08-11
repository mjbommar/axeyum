# QF linear A5 IDL extended DL slice v2 preregistration — 2026-08-11

**Target, control, retained-decision, and focused gates passed.** The exact-
pushed complete repository gate remains pending; see the [result](qf-linear-a5-idl-extended-dl-slice-v2-result-2026-08-11.md).

## Measured boundary

The [telemetry result](qf-linear-a5-idl-dl-scan-telemetry-v1-result-2026-08-11.md)
shows both lost targets are large and equality-heavy: BubbleSort is
7,095 atoms / 2,028 numeric equality gates and GraphPartitioning is 2,199/855.
The fallback-critical `lpsat-goal-18` control is the already protected moderate
906/350 class. The v1 candidate selected large *non*-equality-heavy scans and
correctly failed without affecting BubbleSort.

This note authorizes one corrected structural candidate. It does not authorize
a global split, benchmark-name policy, pre-SAT change, census, or QF_RDL breadth
run.

## Candidate

Compute the existing standard maximum exactly as today:
`timeout - min(timeout / 4, 6 seconds)`. Compute an extended maximum of
`timeout - min(timeout / 8, 3 seconds)`. After the existing scan:

1. if numeric equality gates are at least 128 and atoms are at most 1,024, use
   the unchanged `standard * 2 / 3` timeout (12 seconds at production);
2. if equality gates are at least 128 and atoms exceed 1,024, use the extended
   timeout (21 seconds at production); and
3. otherwise use the standard timeout (18 seconds at production).

Keep the standard timeout as the scan deadline, so a query must be classified
within today's front-end bound before it can receive extended search. Preserve
all scan/encoding/search semantics, route order, replay, checked conflicts,
pre-SAT caps, evidence categories, and public APIs. Retain the new timeout
counts unchanged.

Focused tests must cover the two exact thresholds, moderate 12-second behavior,
large-equality 21-second behavior, compact/large low-equality 18-second
behavior, zero/short/24-second configurations, and no configured timeout.

## Immediate matrix

Build one exact clean release candidate. At group-start load at most 12, run
fresh 24,000 ms / 8 GiB workers with exact identity and zero stderr:

- BubbleSort UNSAT through `dl-online` in 3/3;
- GraphPartitioning replay-checked SAT through `dl-online` in 3/3;
- `lpsat-goal-18` UNSAT in 3/3; and
- the retained maze gain UNSAT in 3/3.

The telemetry must show 21-second selection only for the two targets and the
unchanged class/budget for controls. Stop at the first miss, loss, wrong
verdict, stderr, malformed record, process failure, or 8 GiB breach.

## Retention and release gate

Only after the immediate matrix passes, compare the candidate with unchanged
`d0e0d6cea` on all 68 retained QF_IDL and 105 retained QF_RDL decisions. Every
verdict must remain identical except the two intended recoveries; every SAT
must replay; gains never offset losses. The `pursuit`, `tgc`, and 31,944-variable
Maze allocation controls must remain typed pre-SAT declines with zero SAT
rounds.

Then require formatting, strict all-feature solver Clippy, complete solver
library, deep-input and online arithmetic/CDCL(T) suites, and relevant IDL/RDL
differentials. Amend ADR-0375 with the policy only after those gates pass.
Commit, push, and run one uninterrupted external-frontier `just check` before
restarting V2 from QF_LRA row 1. Any failure removes the candidate and records
a negative result.
