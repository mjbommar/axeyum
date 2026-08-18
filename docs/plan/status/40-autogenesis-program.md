# Lane: autogenesis-program

<!-- plan-section: lane-status -->

**Phase 0 WIP.** Exact pushed commit `5ac434ef9` replays the selected
`F:no-integer-square-is-minus-one` operation and derives the first complete
authoritative fact transaction without caller-authored status, route, evidence,
footprint, checker, artifact, or shell text. Exact-transaction fault controls
converge after all three durable boundaries. Next: production compare-and-swap,
durable-event recovery, fact replay, and frontier recomputation. This fact
unlocks no descendant, so it validates admission infrastructure but does not
replace the required B -> A compounding chain.

<!-- plan-section: landed-changes -->

| 2026-08-18 | `2abe2652d..a90255a92` | Programme through typed fixture operation replay. |
| 2026-08-18 | `5c38bf95d` | First authoritative registered evidence route; exact machine frontier selects one matching open fact. |
| 2026-08-18 | `dbd6f3e00..5ac434ef9` | Typed execution receipt and prepared authoritative transaction replayed; zero live writes. |
