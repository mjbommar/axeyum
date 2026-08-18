# Lane: autogenesis-program

<!-- plan-section: lane-status -->

**Autogenesis-1 is frozen; the nursery is truthfully not ready.** Commit
`2d65f19d8` reserves the exact B-to-A chain as a longitudinal regression and
adds component-, family-, proof-shape-, and mutation-safe train/development/
held-out rules. The executable baseline has zero evaluation facts and nine
named blockers. This is intentional: the current 110-fact ledger has only 23
direct proof-derived kernel edges across ten consequents, and relabelling it
would leak the known Nat component rather than measure generalization.

**Mathlib source harvesting is proof-isolated.** Commit `bd7b55bff` binds exact
Mathlib/Lean/extractor identities, retains 9,729 statement-only Nat/Int rows
externally, and commits 240 source candidates across twelve families. The
extractor never emits theorem values, and the candidate selector reads no
checkout, full export, proof, or Axeyum outcome. These rows are not nursery
facts and do not change the nine-blocker readiness result.

**Dependency leakage is now measured.** Commit `30e7e6ec3` derives 95 direct
candidate-to-candidate proof edges from an evaluation-only Mathlib pass and
groups all 240 candidates into 146 indivisible weak components. The durable
projection contains names and edges only; its state remains explicitly
`dependency-metadata-not-frozen-split`.

**Next:** review statements and aliases, author statement-strength mutations,
label proof-shape risks from statement structure, then freeze whole dependency/
mutation groups into train/development/held-out membership. Do not expose proof
bodies to search, treat Mathlib proof as Axeyum construction, or begin proof-plan
work before fixed-budget nursery episodes identify the dominant seam.

<!-- plan-section: landed-changes -->

| 2026-08-18 | `cf998788b` | Automated the exact authoritative B-then-A chain; two isolated fixed-budget runs matched all 56 retained artifact bytes and passed Autogenesis-1. |
| 2026-08-18 | `2d65f19d8` | Froze the leakage-safe nursery contract and the Autogenesis-1 longitudinal partition; readiness remains explicitly false with zero evaluation facts and nine blockers. |
| 2026-08-18 | `bd7b55bff` | Extracted 9,729 proof-isolated Mathlib Nat/Int statements externally and selected 240 outcome-blind source candidates across twelve families without vendoring bulk exports. |
| 2026-08-18 | `30e7e6ec3` | Projected 95 direct Mathlib candidate dependencies into 146 whole leakage components without exposing proof terms or freezing evaluation splits. |
| 2026-08-18 | `f4dc0d4f1` | Registered and cleanly exercised the exact axiom-free authoritative B operation, whose durable event made A newly ready. |
