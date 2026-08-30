# Lane: producer-widen — widen the conclusion-directed producer to a second family

<!-- plan-section: lane-status -->

**Your lane's block (`landed`, producer-widen, 2026-08-28).** Task: widen
`producers::conclusion_directed_application` (lane 198, which closed ten open
`nat.modeq` facts) to a **second** family of currently-open facts.

**Outcome: no operation registered, so `facts_via_multi_target` is unchanged.**
(`operations=29`, `multi_target_operations=5`, and a read-only recomputation
over `operations.json` x fact status gives `facts_via_multi_target=31`, one
above the 30 the brief quotes; `gen-production-provenance-ledger.py --check`
was already stale on `main` before this lane started and was **not**
regenerated here, since regenerating would commit another lane's pending
delta.)
The lane found — and this is the deliverable — that the binding constraint is
not the producer's grammar and not family shape. It is that **Mathlib's own
proof is axiom-bearing for 61 of the 63 resolvable open propositions**, so no
transport can close them, and every widening must AUTHOR an axiom-free contract
per family. Three measurements, each re-derivable.

**Holdout isolation, before and after, unchanged and PASS:**
`held_out=37|files_scanned=1101|settled=0|references=0`. The two entirely
held-out families (`natural-logarithm` 21 open, `natural-square-root` 16 open —
37 facts, the whole partition) were excluded by **partition per fact**, never by
count, and no held-out target was measured, exported, or named. **No target was
dropped for any other reason**; nothing outside the exclusion was skipped.

## 1. The producer reaches 0 of 35 open palette facts

Every open, non-held-out fact with a proof-free target capsule in
`/nas3/.../reference-packs/open-fixed-palette-v1` (35), through
`examples/conclusion_directed_transport_probe`:

| outcome | count |
| --- | --- |
| accepted | **0** |
| declined at statement import (`dif_pos` 11, `Quot` 9, `Eq.subst` 3, `Nat.mod_lt` 2, `propext` 1) | **26** |
| imported, then `NoConclusionMatch` | **9** |

Detail moved to [`../notes/205-producer-widen.md`](../notes/205-producer-widen.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | producer-widen | measured: conclusion-directed producer reaches 0 of 35 open non-held-out palette facts — 26 blocked at statement import, 9 induction-shaped |
| 2026-08-28 | producer-widen | new gated census: 61 of 63 open non-held-out propositions have an axiom-BEARING Mathlib proof, so transport cannot close the frontier; 6 guards each mutation-verified to kill exactly one control |
| 2026-08-28 | producer-widen | `scripts/provision-lean-import-toolchain.sh` — s4 CAN run the whole import route; pinned mathlib4 + lean4export provision in ~5 min |
