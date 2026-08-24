# 255 — Kernel semantic anchors: a reviewed batch, not bulk classification

Date: 2026-08-24

## Result

The knowledge overlay can now attach a qualified `formalizes` edge to an
accepted **kernel theorem** as well as to a fact-ledger record. The contract is
deliberately narrower than a generic declaration-to-concept tag:

- the source must resolve in the generated kernel dependency projection;
- it must be a theorem, not a definition, constructor, recursor, or axiom;
- its recorded axiom footprint must be empty;
- the semantic mapping remains `human-reviewed` and must carry an explicit
  partial-coverage qualifier and sources.

This batch adds three anchors from the newly landed library surface:

| Kernel theorem | Reviewed concept | What it says — and does not say |
|---|---|---|
| `Decidable.em` | `C:excluded-middle` | A scoped `p ∨ ¬p` result when `Decidable p` is supplied; it is explicitly not unrestricted classical excluded middle. |
| `Complex.normSq_pow` | `C:complex-number` | One algebraic squared-norm/power law for constructed complex numbers; no analytic or whole-topic coverage claim. |
| `CPoint.circumcentre_unique` | `C:circle` | Unique equidistant centre for a non-collinear triple; one circumcentre law, not a complete formalization of circle geometry. |

The sources are the accepted constructed-kernel declarations recorded in
[`kernel-dependency-projection-v1.json`](../../artifacts/autogenesis/kernel-dependency-projection-v1.json)
and the read-only, pinned `math-education` concept files at revision
`ce3e2a52e7c95075d69262b4d8f0ee8fe748f22c`.

## Why this is the right granularity

The kernel projection currently indexes 1,142 declarations, but indexing is
not semantic review. Bulk name matching would make a large graph quickly and
would be especially misleading here: `Decidable.em` looks like classical
excluded middle by name but is intentionally limited to propositions carrying
a decision witness; `CPoint.circumcentre_unique` contains no general circle
theory; and a complex norm identity has no claim to the complete complex-number
curriculum.

These edges therefore improve the join between the library and the concept
graph while preserving the key separation:

```text
kernel acceptance proves the theorem and its empty footprint
human review qualifies its mathematical/conceptual interpretation
the overlay informs search or reporting, never admission
```

## Controls and next work

`validate-autogenesis-knowledge.py` now rejects both a missing kernel endpoint
and an attempt to formalize a concept from a kernel definition. Existing
partial-coverage controls continue to reject a single edge claiming full
concept coverage.

Run:

```sh
python3 -m unittest scripts.tests.test_validate_autogenesis_knowledge
python3 scripts/validate-autogenesis-knowledge.py
```

The next batch should be driven by a documented review queue: first identify
new theorem clusters from the generated projection, then map only those whose
statement and external-concept meaning have both been read. It must not convert
the current declaration count into an “enriched theorem” count, and it does not
alter the separately pre-registered producer evaluation frontier.
