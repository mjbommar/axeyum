# ADR-0180: Glaurung lineage regression alarms

Status: accepted
Date: 2026-07-15

## Context

ADR-0179 compares homogeneous artifacts but reports deltas without a stop/go
boundary. The established cold Glaurung methodology already uses 3% Axeyum and
normalized-ratio alarms plus 2% absolute Z3 drift. Held-out lineage repetition
adds a process-RSS acceptance dimension.

## Decision

Fail held-out lineage comparison above 3% Axeyum mean regression, 3% normalized
Axeyum/Z3 ratio regression, 5% median-RSS regression, or 2% absolute Z3 drift.

- Axeyum, ratio, and RSS alarms are one-sided; improvements pass. Z3 drift is
  absolute because either direction means the environment bar moved.
- Thresholds are explicit percentage options and may be tightened for a
  controlled experiment. They never relax schema, source/environment, driver,
  exact-work, finding, agreement, unknown, lifecycle, fallback, or limit gates.
- A threshold violation is an investigation alarm, not permission to discard
  the control or claim a regression without checking environmental evidence.

## Evidence

ADR-0178 measures Axeyum population CV at 0.34% on SurfacePen and 0.44% on
fixed-budget NETwtw10. A 3% time/ratio alarm is therefore well outside observed
run noise while matching the established full-tier methodology. The repeated
NETwtw10 RSS range is only 484 KiB around a 257,736 KiB median; 5% is a
conservative first memory ceiling that still catches a material retained-state
increase. The 2% Z3 guard preserves the earlier same-environment boundary.

Glaurung `a0e5f9f` implements the alarms. A fourth focused test distinguishes
one-sided Axeyum/RSS regressions from absolute Z3 drift, Ruff and compilation
remain green, and the real SurfacePen artifact self-comparison passes with all
four deltas zero.

## Alternatives

Reporting only raw deltas was rejected because per-commit automation needs a
stop/go result. Using CV-sized sub-1% thresholds was rejected as overfitting one
host and too sensitive to normal system variation. Treating RSS as diagnostic
only was rejected because memory was the admission blocker in ADR-0171.

## Consequences

The held-out runner now has identity, correctness, exact-work, and performance/
memory stop-go boundaries. Publish one clean full artifact to serve as the
baseline; do not use the dirty one-process plumbing smoke as release evidence.

After that publication, GQ9 may begin fitting a topology/cost selector for
whether to activate lineage. GQ8 caching and any threshold/schema revision
remain separate decisions.
