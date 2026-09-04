# Lane: topology-decision — decide the constructive topology (W0-3) by building the metric carrier (W2-1)

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, topology-decision, 2026-09-04).** Roadmap W0-3
(constructive topology design ADR) and W2-1 (metric-space carrier with `CReal`
and `CPoint` as instances). Reviewer 06 is the emptiest shelf in the library —
zero topology declarations — and reviewers 03, 05 and 08 are blocked behind it.

Method, copied deliberately from ADR-1595: decide the design question by
**building the theorem and measuring**, not by weighing arguments. The metric
carrier is the cheapest test of whichever topology W0-3 would pick, so it gets
built first and the ADR reports what the build taught.

<!-- plan-section: landed-changes -->

| 2026-09-04 | topology-decision | lane opened: metric carrier + topology design ADR-1602 |
