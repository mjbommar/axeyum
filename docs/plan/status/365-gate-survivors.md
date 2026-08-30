# Lane 365 — gate survivors

<!-- plan-section: lane-status -->

## Status

**IN PROGRESS.** Five gates named in
[`docs/research/11-design-review/2026-08-30-session-audit.md`](../../research/11-design-review/2026-08-30-session-audit.md)
§5b have surviving guards — a guard can be deleted with every registered control
still green. This lane makes each guard fail when it should and proves it with a
control that dies when the guard is deleted.

Subjects:

1. `scripts/check-merge-hygiene.sh` — zero registered controls.
2. `scripts/check-aggregate-scope.sh` — fail-on-new-divergence deletable; live
   quote-blind normalizer bug.
3. `scripts/check-cas-substance.py` — derived but unratcheted.
4. `scripts/check-generated-artifact-ownership.py` — one-element registry.
5. `scripts/check-shell-antipatterns.sh` — `hooks/` unscanned, both hooks violate.

This commit is the status stub only; no gate work has landed yet.
