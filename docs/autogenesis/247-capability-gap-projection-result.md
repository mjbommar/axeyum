# 247 — Capability-gap projection

The knowledge overlay now has a generated view of the gap between facts that
are dependency-ready and facts that an authoritative operation may actually
dispatch. It is derived from the same content-addressed frontier used for
selection; it adds no operation applicability, fact status, or admission
authority.

The current snapshot records **141 dependency-ready facts**, **zero
admissible facts**, and six `(formal language, fragment, route class)` groups.
Every ready fact lacks a registered authoritative operation. Six also have no
supported route at all, while two require a gate-coupling review before any
future dispatch. The dominant actionable gap is therefore not a solver score or
a theorem count: it is a general producer or adapter that can be registered
against a reviewed portion of the ready `lean4-surface` Nat/Int population.

The artifact retains the exact fact-frontier, fact-ledger, and operation
registry digests used for the observation. Its grouping is a ranking and
producer-investigation input only; it cannot authorize proof search, theorem
admission, or a ledger transition.

For the reviewed Mathlib population it additionally groups ready facts by the
outcome-blind `family` and `statement_shape` labels already pinned in the fact
catalog, retaining dependency-component identities. This supplies a safe first
search-space reduction: a proposed producer can be evaluated against a family
shape cluster without treating neighboring proof bodies or target outcomes as
available information.

Those clusters are now labeled through a separately reviewed, pinned
[family-to-concept crosswalk](248-family-concept-crosswalk.md). The label is
family-topic guidance only; the graph still requires a distinct qualified
`formalizes` edge before it can claim anything about an individual theorem's
formal coverage of that concept.

Each reviewed cluster also carries the exact set of its immediate ledger
descendants and its count. This is measured leverage, not a value judgement:
it lets a scheduler compare the potential local fan-out of candidate producer
work while keeping the ranking policy explicit and untrusted.

```sh
python3 scripts/validate-autogenesis-capability-gap-projection.py
python3 -m unittest scripts.tests.test_validate_autogenesis_capability_gap_projection
python3 scripts/gen-autogenesis-capability-gap-projection.py --check
just autogenesis-capability-gap
```

The negative controls reject an invented group count and a fact that is counted
twice. The structural validator deliberately does not demand fresh source
inputs in shared aggregate gates; the knowledge-overlay owner performs the
freshness check before publishing a new snapshot.
