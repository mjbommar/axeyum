# Natural-congruence semantic coverage

Date: 2026-08-26

## Result

The reviewed semantic overlay now covers both natural-congruence
representations without asserting that their declarations are interchangeable.

- Four settled Mathlib facts—reflexivity, symmetry, transitivity, and the
  commutation biconditional—formally cover modular arithmetic. The first three
  also cover the corresponding equivalence-relation laws.
- Three axiom-free native kernel theorems—`Nat.mod_eq_refl`,
  `Nat.mod_eq_symm`, and `Nat.mod_eq_trans`—anchor both concepts for Axeyum's
  balanced-witness relation.

Every edge is human-reviewed, partial, and non-authoritative. The imported
Mathlib relation reduces to equality of remainders; the native Axeyum relation
uses balanced existential witnesses. Sharing the concepts *modular arithmetic*
and *equivalence relation* says that both formalize those ideas. It does not say
their constants, types, or proof terms can be transported. Each kernel edge
therefore carries `declaration_equivalence_claim: false`, and each fact edge
records the imported remainder-equality representation explicitly.

## Measured effect

| Measure | Before | After |
| --- | ---: | ---: |
| Qualified formalization facts | 9 | 13 |
| Reviewed kernel anchors | 3 | 6 |
| Projected concepts | 13 | 13 |
| Held-out formalizations exposed | 0 | 0 |

The semantic review queue remains honest: 6 of 1,287 kernel theorems are
reviewed anchors and 1,281 remain unreviewed. The product-health front door now
shows the 13/6 coverage rather than the earlier 9/3 snapshot.

## Why this matters for the bridge

The knowledge graph can now retrieve both representations under the same
mathematical concepts while the transport layer continues to reject an
unproved implementation bridge. Semantic proximity guides search; exact
identities, footprints, and kernel checking decide admission.

Add an explicit representation-bridge edge only after the target-local
remainder theorem described in the imported bridge assay is independently
checked. Until then, the graph may offer both theorem families as related
knowledge but must never authorize one as a proof of the other.
