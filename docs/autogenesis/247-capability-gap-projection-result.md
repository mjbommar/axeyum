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
