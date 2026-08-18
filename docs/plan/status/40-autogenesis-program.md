# Lane: autogenesis-program

<!-- plan-section: lane-status -->

**Autogenesis-1 is frozen; the nursery is truthfully not ready.** Commit
`2d65f19d8` reserves the exact B-to-A chain as a longitudinal regression and
adds component-, family-, proof-shape-, and mutation-safe train/development/
held-out rules. The executable baseline has zero evaluation facts and nine
named blockers. This is intentional: the current 110-fact ledger has only 23
direct proof-derived kernel edges across ten consequents, and relabelling it
would leak the known Nat component rather than measure generalization.

**Next:** harvest provenance-pinned Nat/Int statement families from the
external Mathlib inventory into whole, outcome-blind dependency components;
store only lightweight identities and regeneration recipes in Git. Do not
vendor the 5.5 GB export, expose imported proof bodies to search, or begin the
proof-plan IR before fixed-budget nursery episodes identify the dominant seam.

<!-- plan-section: landed-changes -->

| 2026-08-18 | `cf998788b` | Automated the exact authoritative B-then-A chain; two isolated fixed-budget runs matched all 56 retained artifact bytes and passed Autogenesis-1. |
| 2026-08-18 | `2d65f19d8` | Froze the leakage-safe nursery contract and the Autogenesis-1 longitudinal partition; readiness remains explicitly false with zero evaluation facts and nine blockers. |
| 2026-08-18 | `f4dc0d4f1` | Registered and cleanly exercised the exact axiom-free authoritative B operation, whose durable event made A newly ready. |
