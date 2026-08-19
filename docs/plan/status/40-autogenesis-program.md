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

**Statement review remains outcome-blind.** Commit `7179e03d9` retains 202
evaluation-eligible candidates, reserves 23 calibrations, removes 15 aliases or
internal surfaces, and adds one statement-strength mutation per family. The 214
future evaluation statements form 120 whole dependency/mutation groups; no
partition or expected outcome is assigned.

**The reviewed population is now in the ledger, honestly open.** Commit
`30ee0885f` materializes 202 external-source propositions and twelve mutations
as `lean4-surface` facts. Exact Lean/Mathlib v4.30 accepts all 214 proof-free
axiom types; every evidence array remains empty and the frontier refuses every
row because no registered operation exists.

**Next:** preregister a feasible split over whole dependency/mutation groups,
families, and family-scoped proof-template risks, then freeze train/development/
held-out membership. Do not expose proof bodies to search, treat Mathlib proof
as Axeyum construction, or begin proof-plan work before fixed-budget nursery
episodes identify the dominant seam.

<!-- plan-section: landed-changes -->

| 2026-08-18 | `cf998788b` | Automated the exact authoritative B-then-A chain; two isolated fixed-budget runs matched all 56 retained artifact bytes and passed Autogenesis-1. |
| 2026-08-18 | `2d65f19d8` | Froze the leakage-safe nursery contract and the Autogenesis-1 longitudinal partition; readiness remains explicitly false with zero evaluation facts and nine blockers. |
| 2026-08-18 | `bd7b55bff` | Extracted 9,729 proof-isolated Mathlib Nat/Int statements externally and selected 240 outcome-blind source candidates across twelve families without vendoring bulk exports. |
| 2026-08-18 | `30e7e6ec3` | Projected 95 direct Mathlib candidate dependencies into 146 whole leakage components without exposing proof terms or freezing evaluation splits. |
| 2026-08-18 | `7179e03d9` | Outcome-blind review retained 202 candidates and grouped twelve family-wide statement mutations into 120 indivisible future evaluation units. |
| 2026-08-18 | `30ee0885f` | Materialized 214 proof-free Mathlib source/mutation propositions as open `lean4-surface` facts; exact Lean accepted every type and the machine frontier refused all without operations. |
| 2026-08-18 | `f4dc0d4f1` | Registered and cleanly exercised the exact axiom-free authoritative B operation, whose durable event made A newly ready. |
