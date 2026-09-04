# Lane: metric-compactness — W2-3 Bishop compactness / EVT-as-instance, W2-2 continuity as a metric notion

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, metric-compactness, 2026-09-04).** Testing
ADR-1602's bet: the `Metric` carrier landed with `Metric.Complete` general and
`Metric.creal_complete` as ℝ's instance, but nothing yet has been *re-derived*
through the carrier. This lane adds `Metric.TotallyBounded`, Bishop
compactness (`TotallyBounded` + `Complete`), the interval instance,
`Metric.UniformlyContinuous`/`Metric.Continuous`, and attempts to obtain
`CReal.evt_approx_max` as an instance of a general metric EVT. A measured
negative on the derivation is the deliverable if the derivation does not land.

<!-- plan-section: landed-changes -->

| 2026-09-04 | metric-compactness | lane opened: W2-3 + W2-2 on the `Metric` carrier, ADR-1607 reserved |
