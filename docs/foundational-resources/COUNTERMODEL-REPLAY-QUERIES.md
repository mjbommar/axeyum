# Finite Countermodel Replay Queries

This is the consumer-facing query guide for
`bridge_finite_countermodel_replay`. It complements the learner page
[Finite Countermodel Replay](../learn/math/finite-countermodel-replay.md).

Finite countermodel replay is a bridge concept, not a separate proof checker.
Use it to find rows where a concrete finite object is independently replayed
against a finite claim:

```text
untrusted fast search -> candidate assignment/table/countermodel
trusted small checking -> replay the finite object against the source claim
```

## Start Here

Find the concept row:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --text countermodel \
  --require-any
```

Find the packs that reuse the pattern:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept bridge_finite_countermodel_replay \
  --solver-reuse promoted \
  --require-any
```

Find all checked rows under the bridge:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_countermodel_replay \
  --proof-status checked \
  --require-any
```

## Pack-Scoped Queries

Finite predicate and relation-table countermodels:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_countermodel_replay \
  --pack finite-predicate-v0 \
  --proof-status checked \
  --require-any
```

Boolean no-countermodel searches:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_countermodel_replay \
  --pack logic-basics-v0 \
  --expected-result unsat \
  --proof-status checked \
  --require-any
```

Proof-pattern counterexamples:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_countermodel_replay \
  --pack proof-methods-patterns-v0 \
  --expected-result sat \
  --proof-status checked \
  --require-any
```

Function-table conflicts with checked QF_UF/Alethe evidence:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_countermodel_replay \
  --pack relations-functions-v0 \
  --route Alethe \
  --proof-status checked \
  --require-any
```

Finite order/lattice counterexamples with checked Boolean evidence:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_countermodel_replay \
  --pack finite-order-lattices-v0 \
  --route boolean \
  --proof-status checked \
  --require-any
```

## Route Boundary

Countermodel replay answers "what finite object breaks this finite claim?" A
route query answers "what evidence format checks the final obligation?"

| Consumer Question | Use |
|---|---|
| Find finite objects that falsify a bounded claim | `--concept bridge_finite_countermodel_replay` |
| Find checked Boolean refutations | `--route boolean --proof-status checked` |
| Find checked equality/congruence conflicts | `--route Alethe --proof-status checked` |
| Find theorem targets beyond finite replay | `--route lean-horizon-template` or `--proof-status lean-horizon` |

Do not use this bridge to claim arbitrary first-order validity, induction,
compactness, infinite cardinality, or theorem-scale algebra. Those require a
separate theorem or Lean-horizon route.
