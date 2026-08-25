# Lane: agent-correspondence-model — saying that two theorems are the same idea

<!-- plan-section: lane-status -->

**Theorem correspondences (`WIP`, agent-correspondence-model, 2026-08-24).** The
data model can now state that two settled facts are the same mathematical
content, and cannot state it where `depends_on` belongs
([ADR-0546](../../research/09-decisions/adr-0546-theorem-correspondences-are-not-proof-dependencies.md)).
`artifacts/correspondences/*.json`, one file per adjudication on the
`artifacts/facts/` pattern, gated by `scripts/validate-correspondences.py`
(`just correspondences`; 39 mutations, 39 killed, one test each). Three
instances landed, all `route-recorded`.

Detail moved to [`../notes/123-theorem-correspondences.md`](../notes/123-theorem-correspondences.md).

<!-- plan-section: landed-changes -->

| 2026-08-24 | `c0c2b6fea` | **ADR-0546 + the gate wired into both aggregates.** Records three findings against the brief: `technique`/`concept` are NOT uninstantiated overlay kinds (24 endpoints, resolved `external-pinned` next door); the existing vocabulary still does not suffice, because `unlocks` is reachability and every `formalizes` edge is *required* to be `completeness: partial` so two cannot compose into "same"; and the motivating `Int.fib_cassini ↔ Rat.det2_mul` edge **is not landable** — neither theorem has a fact and neither is in the kernel projection, so `specialization` ships as a declared kind with zero instances and the gate prints that zero. |
| 2026-08-24 | `06b41a5e6` | **`artifacts/correspondences/` — two theorems can be said to be the same idea, and the claim is checked.** Refuses any pair the ledger's *transitive* `depends_on` closure connects (`F:ml430-nat-fib-add-two` / `F:ml430-int-fib-add-two` is a real such pair and the control pins the refusal against the committed ledger). `carrier-transport` is checked *structurally* — erasing the carrier from both formal statements must leave the same string, and an unknown carrier FAILS rather than skipping. Two status axes mirroring the ledger's, each backed: `asserted` ⟺ empty `via`; `route-recorded` requires every non-null ref to resolve; `mechanized-here` forbids a null ref and requires a checker command; evidence at all requires `mechanized-here`. Empty population exits 1. Prose floors set from measuring `../math-education` (1,263 reasons, median 190 chars — and a bridge to `C:pi` whose reason was about *density* validated cleanly there, which is why nothing here rests on prose). |
