# Lane: autogenesis-program

<!-- plan-section: lane-status -->

**Phase 0 WIP.** Exact pushed commit `f6e59f87b` contains the first real
authoritative admission. It selected and proved
`F:no-integer-square-is-minus-one`, stopped after durable intent with the fact
unchanged, recovered through compare-and-swap, replayed the settled operation,
and derived an event-bound readiness delta with `newly_ready: []`. Exact pushed
commit `f8651ec98` then reproduced the acquisition from a second isolated clean
worktree; retained replay `7dc1ad8d...` passed every semantic identity and
fault-recovery check. Exact pushed commit `0bb49769b` corrects chain authority:
52 authored kernel-subgraph edges become 23 genuinely proof-derived edges when
intersected with the kernel inventory. The retained primary
`F:nat-zero-add -> F:nat-mul-one` experiment replayed cleanly and is selected by
qualified catalog `95e8c8d...`, with authoritative-write power explicitly
false. Next: register an authoritative kernel executor for B, then A; measure a
fallback without weakening the primary path. The leaf validates infrastructure,
and the fixture chain validates causality, but neither receives Autogenesis-1
production credit.

<!-- plan-section: landed-changes -->

| 2026-08-18 | `2abe2652d..a90255a92` | Programme through typed fixture operation replay. |
| 2026-08-18 | `5c38bf95d` | First authoritative registered evidence route; exact machine frontier selects one matching open fact. |
| 2026-08-18 | `dbd6f3e00..5ac434ef9` | Typed execution receipt and prepared authoritative transaction replayed; zero live writes. |
| 2026-08-18 | `313203bd4..f6e59f87b` | First authoritative fact admitted and recovered; durable event recomputed an honest empty readiness delta. |
| 2026-08-18 | `f8651ec98` | Second isolated clean worktree reproduced selection, certified execution, crash recovery, admission, and leaf readiness; external bundle retained. |
| 2026-08-18 | `ac0c39d84..0bb49769b` | Integrated human chain enumeration, corrected declared-edge overcount by intersecting the kernel inventory, and gated a content-addressed 23-edge structural catalog. |
| 2026-08-18 | `pending` | Primary Nat B -> A experiment replay-qualified for selection with zero write authority; fixture transaction scope escalation closed. |
