# Target-owned capsule agent read surface

Date: 2026-08-26

## Result

The agent can now query reusable theorem roots that Axeyum constructed outside
the ordinary native prelude. The tier-R `target_owned_candidates` tool searches
by exactly one of theorem-name glob or canonical-type substring and currently
returns the three clean bitwise-family roots.

This closes a real connective-tissue gap. Before this surface, the roots were
independently checked and available in a hash-bound capsule, but an autonomous
episode could discover only native-prelude lemmas or imported theorem
candidates. Durable material that lived between those populations was invisible.

## Separation from other populations

The three retrieval populations have different meanings:

| Surface | What a row means | Reuse boundary |
|---|---|---|
| `lemma_neighbourhood` / `lemma_candidates` | theorem in the generated native kernel projection | exact native declaration handle |
| `imported_candidates` | independently audited Lean/Mathlib theorem | execution only when its measured footprint permits it; otherwise explicit reconstruction routing |
| `target_owned_candidates` | checked Axeyum-produced root in a reusable external capsule | reusable through the named capsule, never exact imported identity by analogy |

The new row carries its declaration identity, canonical type, axiom footprint,
direct theorem dependencies, external capsule path and hash, semantic-analogue
fact links, exact-identity flag, reuse eligibility, and authoritative-operation
eligibility. For the current family:

- all three footprints are empty;
- all three directly depend on the same generic theorem;
- all three are reusable checked material;
- all three have `exact_imported_identity = false`; and
- all three have `authoritative_operation_eligible = false`.

Thus discovery does not silently become admission.

## Evaluation isolation

Semantic-analogue fact IDs pass through the same central held-out filter as
other agent read tools. A future capsule row linked to a held-out or
longitudinal fact may still expose its target-owned theorem, but the protected
fact ID is removed before the result enters the transcript and the dropped-link
count increases. The current three links are all in the development partition.

Adding the tool deliberately changes the toolset fingerprint. Recorded episodes
retain the surface they actually ran with; future episode policies bind the new
fingerprint. The tool remains tier R: it cannot import a capsule, register an
operation, admit a theorem, or change a fact.

## Next

The next producer step should consume a selected target-owned capsule root as an
explicit premise and report whether it constructs a new target. Operation
registration remains premature until an unchanged producer converts multiple
eligible facts with independently checked terms. Exact imported bitwise facts
remain open unless the structural operation-identity boundary is separately
resolved or a weaker trust route is explicitly authorized.
