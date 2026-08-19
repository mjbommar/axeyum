# First independently checked reflexivity candidate

Date: 2026-08-18

## Result

The first proof-isolated Mathlib goal now has a fresh Axeyum-constructed proof
candidate. A bounded generic producer reads the imported kernel goal

```lean
∀ (n : ℕ), n.ascFactorial 0 = 1
```

and constructs the corresponding `fun n => Eq.refl ...` term. The independent
kernel admits that term under the exact imported goal, then a separate closure
audit confirms that the candidate uses no axiom, no prior theorem, and not the
transparent statement definition itself.

This closes the local **goal -> proposal -> kernel check** arrow. It does not
yet close the durable **checked result -> registered operation -> ledger
admission** arrow.

## Measured boundary

| Property | Result |
|---|---:|
| Pi binders consumed | 1 of 8 |
| Expression nodes constructed | 4 of 16 |
| Independently admitted environment declarations | 55 |
| Axiom dependencies | 0 |
| Theorem dependencies | 0 |
| Target-definition dependency | false |
| Ledger writes | 0 |
| Goal SHA-256 | `87e37902bb8b3958514c5a6831b28ebff2824c8a30fb45601ff47736ee3853d7` |
| Proof SHA-256 | `16600053e2afaa0d4d0bfa559fbac367bfeb41b860912f10c236cdcb82e08b53` |

The proposer is intentionally untrusted. It recognizes only a Pi telescope of
at most eight binders whose terminal expression is an exact three-argument
`Eq` application, then proposes `Eq.refl` on the left-hand side. It does not
try to decide definitional equality. A negative control supplies unequal sides:
the proposer emits a candidate and the kernel rejects it. This is the desired
trust split.

## Fail-closed controls

Four Rust controls cover valid generic reflexivity, a non-equality terminal, a
nine-binder budget violation, and unequal equality sides. Four receipt controls
cover exact replay, mutated proof text, a claimed target dependency, and extra
output. The artifact checker also requires the source fact to remain `open`,
with an empty evidence list and no proof route.

At this result boundary the dispatch census reported
`reflexivity-candidate-checked:not-registered-or-admitted`. The subsequent
registration increment preserves this manifest unchanged and moves the row to
`eligible-for-dispatch`; neither state by itself grants proof credit.

## Next arrow

Register an exact source-bound operation whose executor reimports the pinned
statement artifact, runs this fixed-budget producer, and emits a transaction
proposal. Then apply the existing durable admission protocol, recheck the
post-state from a clean checkout, and only then flip the fact or count an
autonomous theorem. Registration must preserve the current external artifact,
goal, proof, operation budget, and dependency identities.

After that single-row admission works, broaden bottom-up across definitional
equalities and top-down across one additional statement shape, while keeping
held-out rows inaccessible and measuring decline reasons separately from proof
failures.

## Reproduction

```sh
cargo test -p axeyum-lean-import --test statement_reflexivity_operation
python3 -m unittest scripts.tests.test_check_autogenesis_statement_reflexivity
python3 scripts/check-autogenesis-statement-reflexivity.py
python3 scripts/create-autogenesis-nursery-dispatch-baseline.py --check
```
