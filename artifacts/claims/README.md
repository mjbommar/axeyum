# Claim ledger

First-class mathematical claims joining the knowledge graph (the *map*: the
sibling [`math-education`](../../docs/sibling-projects.md) concept graph and
this repository's [curriculum](../../docs/curriculum/README.md)) to
machine-checked evidence (the *pile*: witnesses, certificates, checkers).
Design rationale and commitments:
[ADR-0379](../../docs/research/09-decisions/adr-0379-claim-ledger.md).

One claim = one directory = `claim.json` (schema:
[`../ontology/claim.schema.json`](../ontology/claim.schema.json)) plus its
evidence artifacts. The vocabulary that makes the join work:

- **`epistemic_status`** — `axiom / proved / computed / empirical /
  conjectured / open`, imported verbatim from the math-education graph so
  both corpora share one epistemics.
- **`evidence[]`** — per-sub-statement rows, each with its own
  `check_status` (`checked / replay-only / not-checked`). `computed`
  requires a `checked` row; a `bound-citation` can never be `checked`.
- **`concept_refs[]`** — anchors into the knowledge graph under its own
  resolution policy: `pending` refs are honest work-list markers; `resolved`
  refs must name a pinned graph commit and actually resolve there.
- **`frontier`** — mandatory on `conjectured`/`open` claims: current known
  bounds and the concrete artifact that would settle the claim. Open
  problems are work items, not gaps in the schema.
- **`provenance`** — `conjectured_by` / `searched_by` (untrusted) /
  `checked_by` (trusted) kept separate, per the project thesis.

## Gates

```sh
python3 scripts/validate-claims.py            # structure, refs, epistemic discipline
python3 scripts/check-claim-certificates.py \
    --drat-checker references/drat-trim/drat-trim   # semantic replay of every checked row
python3 scripts/check-claim-negative-fixtures.py    # the validator must reject bad claims
```

## Families

- [`rado/`](rado/) — Rado numbers `R_k(a(x−y)=bz)`
  (semantics: [`rado/SEMANTICS.md`](rado/SEMANTICS.md)): 34 published values
  replicated with independently replayed witnesses and drat-trim-verified
  DRAT certificates, plus the open entry `R_4(2(x−y)=3z)` as a frontier
  claim carrying new verified lower-bound witnesses.
