# Lane: producer-widen — widen the conclusion-directed producer to a second family

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, producer-widen, 2026-08-28).** Task: widen
`producers::conclusion_directed_application` (lane 198, which closed ten open
`nat.modeq` facts) to a **second** family of currently-OPEN facts.

**Holdout isolation, before:**
`held_out=37|files_scanned=1101|settled=0|references=0|verdict=PASS`.

**Measured, and this is the lane's first real result — the producer is NOT the
binding constraint.** Sweeping every open, non-held-out fact that has a
proof-free target capsule in `/nas3/.../reference-packs/open-fixed-palette-v1`
(35 facts; the held-out `natural-logarithm` and `natural-square-root`
families were excluded by PARTITION per fact, never by count) through
`examples/conclusion_directed_transport_probe`:

| outcome | count |
| --- | --- |
| accepted | **0** |
| declined at statement import (`dif_pos` 11, `Quot` 9, `Eq.subst` 3, `Nat.mod_lt` 2, `propext` 1) | **26** |
| imported, then `NoConclusionMatch` | **9** |

The 9 that import were run with **every theorem present in their own capsule**
transported (24 or 47 roots, `transport_declines=0`), not with the
`open-lemma-candidate-ranking-v1` names — 10 of those 12 ranked names are
`MissingRoot` in every capsule, because the fixed-palette pack exports each
target with ONE target-agnostic elementary palette and nothing family-specific.
So the 9 declines are not candidate starvation; the elementary palette contains
no lemma any of these goals needs in one application, and all 9 are
**induction-shaped**, not application-shaped.

**Consequence for the widening question.** The modeq win required a
hand-authored axiom-free Lean contract compiled through `lean4export`
(`scripts/lean/autogenesis_nat_modeq_congruence_contract_v1.lean`, 15,544
records). This host has Lean 4.30 but **no `lean4export` checkout and no
Mathlib checkout** (`/home/mjbommar/lean-import-scale` does not exist; nothing
under `~/.cache/*/lean4export`), so no new candidate or target pack can be
produced here. Statement-adapter files import Mathlib
(`autogenesis_statement_adapter_nat_modeq_congruence_v1.lean:1`), so the target
side needs it too.

And 26 of the 35 are unreachable by this route **whatever contract is
authored**: the trusted declaration is reached by the STATEMENT's own
definition closure, before any candidate is considered.

<!-- plan-section: landed-changes -->

| 2026-08-28 | producer-widen | lane opened; baseline holdout isolation PASS, frontier 125 open |
| 2026-08-28 | producer-widen | measured: conclusion-directed producer reaches 0 of 35 open non-held-out palette facts — 26 blocked at statement import, 9 induction-shaped |
