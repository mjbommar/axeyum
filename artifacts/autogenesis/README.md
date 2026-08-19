# Autogenesis operation registry

`operations.json` is the reviewed mapping from a fact shape to typed producer,
checker, and admission operations. It contains identifiers and implementation
paths, never caller-authored shell commands.

The first operation is deliberately `counterfactual-fixture-only`. It records
the Nat induction path exercised by the Autogenesis-1 control, but grants no
authority to dispatch or admit an authoritative ledger fact. Run
`python3 scripts/validate-autogenesis-operations.py` after changing it.

`nursery-v1.json` is the leakage-controlled population manifest introduced by
ADR-0478. Its first two entries remain the frozen Autogenesis-1 longitudinal
regression; they never count toward train, development, held-out, or autonomous
yield. The additional 214 entries are frozen by
`mathlib-nursery-split-policy-v1.json` and regenerated with:

```sh
python3 scripts/create-autogenesis-mathlib-nursery-split.py --check
python3 scripts/check-autogenesis-nursery.py --require-ready
```

The split policy fixes family membership before target outcomes, and the checker
rejects dependency-component, source-review-group, family, family-scoped
proof-shape, mutation, or longitudinal leakage. Route hypotheses grant no
dispatch or admission authority.

`mathlib-nursery-dispatch-baseline-v1.json` is the first post-freeze capability
census. It inspects only train and development contracts, never held-out facts,
proof bodies, or target outcomes. Reproduce it with:

```sh
python3 scripts/create-autogenesis-nursery-dispatch-baseline.py --check
```

A row declined before execution is not a proof attempt and consumes zero
producer budget. The distinction prevents missing adapters from being reported
as solver failures.

`mathlib-statement-adapter-v1.json` binds the first proof-isolated surface-to-
kernel goal. Its target proposition is encoded as a transparent `Prop`
definition, never an axiom or theorem. The checker rehashes the immutable
external export, independently imports it, rejects any trusted/proof-bearing
declaration, and pins the resulting goal identity:

```sh
python3 scripts/check-autogenesis-statement-adapter.py
```

`mathlib-statement-source-v1.json` binds the external statement-only Mathlib
v4.30.0 inventory. Bulk NDJSON stays on `/nas3`; Git retains the extractor,
source identity, selection policy, and small derived candidate view. Neither an
imported theorem nor its source name counts as Axeyum proof construction.

```sh
python3 scripts/check-autogenesis-mathlib-source.py
python3 scripts/create-autogenesis-mathlib-candidates.py --check
python3 scripts/create-autogenesis-mathlib-dependency-components.py --check
```

`mathlib-dependency-source-v1.json` binds a second, evaluation-only external
artifact. Its extractor can inspect upstream theorem values, but emits only
names and direct theorem dependencies. The committed component projection
contains only candidate identities, candidate-to-candidate edges, and whole
weak components. It is split input, not proposer input, and it still assigns no
train, development, or held-out membership.

`mathlib-nursery-review-policy-v1.json` is the outcome-blind human review
authority. Its derived artifact removes aliases and internal helper surfaces,
reserves base cases for calibration, and binds one statement-strength mutation
to each of the twelve families. The resulting 120 groups still have no split:

```sh
python3 scripts/create-autogenesis-mathlib-nursery-review.py --check
```

`mathlib-nat-int-fact-catalog-v1.json` maps the 202 reviewed sources and twelve
mutations to 214 ordinary **open** fact-ledger rows. Source declarations remain
external prior art; mutation truth values remain unknown. Their
`lean4-surface` propositions were accepted as proof-free axiom types by the
exact Mathlib v4.30 environment, which checks syntax and typing but proves
nothing:

```sh
python3 scripts/create-autogenesis-mathlib-fact-catalog.py --check
```
