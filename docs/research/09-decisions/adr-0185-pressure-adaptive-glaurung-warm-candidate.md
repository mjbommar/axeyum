# ADR-0185: Pressure-adaptive Glaurung warm candidate

Status: accepted as opt-in candidate
Date: 2026-07-16

## Context

ADR-0183 rejects second-check admission as a default because its cold-then-
rebuild path breaches the 3% time alarm. The corrected SurfacePen ordered trace
shows that purpose admission is still too late: it can avoid most singleton
retention, but 117 branch-first paths later require warm state. The measured
prototype is 1.140 seconds / 72,868 KiB and is dominated by existing bounded
lineage; it was removed. Fixed cap 2 passes SurfacePen but regresses NETwtw10
18.2%, so one universally small cap also fails.

## Decision

Accept Glaurung `95c43cb` as an explicit GQ9 measurement candidate. Adaptive
lineage starts at two live sessions and counts failed low-cap reservations. At
128 pressure events it expands once to the configured, already accepted hard
cap of nine and retries the triggering query. The threshold/caps are stable,
deterministic telemetry and enter the fail-closed runner's exact policy
identity. Default remains off; fixed lineage remains the control.

## Evidence

All 27 backend tests and eight runner parser/invariant tests pass. The atomic
one-repetition two-driver smoke validates every exact traffic/lifecycle counter
and all 30,907 checks with zero disagreements or unknown splits.

- SurfacePen does not expand: 87 pressure events, 2,464 warm checks, 87 explicit
  fallbacks. Calibration is 1.095 seconds / 81,212 KiB versus the same-binary
  cap-9 control at 1.079 seconds / 83,220 KiB (+1.55% time, -2.41% RSS).
- NETwtw10 expands exactly once at event 128. Calibration is 18.543 seconds /
  261,648 KiB versus 18.740 seconds / 258,764 KiB (-1.05% time, +1.11% RSS).

These single processes clear the existing alarms but are not acceptance
evidence. The versioned runner now requires adaptive pressure and traffic
identity so the three-process-per-family repeat can make that decision.

## Consequences

GQ9 has a candidate that does not pay purpose analysis or a second-check cold
rebuild. It can reduce low-pressure retained state while recovering the proven
envelope on sustained-pressure streams. Solver/query/model/proof semantics do
not change: siblings remain isolated, the configured hard cap remains atomic,
fallback is the existing one-shot path, and every warm SAT result retains
original-term replay. Do not enable it by default before clean repetition and
cross-policy alarm review.

## Alternatives

Purpose admission, caps one and two, and cap three were rejected by the paired
time/RSS measurements above. Formula-shape admission was rejected because it
would repeat GQ4's paid-analysis failure at the consumer scheduling layer.
