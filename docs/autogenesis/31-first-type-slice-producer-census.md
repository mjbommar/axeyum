# First complete type-slice producer census

Date: 2026-08-19

## Result

The first preregistered proof-producer census ran one fixed reflexivity attempt
against every checked Mathlib v4.30 train/development slice. All 138 rows
entered proof search; **2 produced independently accepted proofs and 136 ended
in structured, uncredited outcomes**.

| Outcome | Rows |
|---|---:|
| Independently checked, dependency-free proof | 2 |
| Equality-shaped candidate rejected by the kernel | 46 |
| Terminal goal was not an exact equality | 49 |
| Terminal goal was not constant-headed equality | 40 |
| Fixed eight-binder budget exceeded | 1 |

The two successes are the already-known `Nat.ascFactorial` and
`Nat.descFactorial` zero statements. Both retain their prior proof identities,
use one binder and four constructed nodes, and have zero axiom, theorem, or
transparent-target dependencies. They remain diagnostic candidates: this
census registers no operation and admits no fact.

The exact-commit observation has semantic identity
`b37c5a6fcfffe257d3d0df6904fb6575ee41989814137b835609a1968d8f8e46`
and file identity
`849cdcb67f0428b17db811d27fead774c099777bff8996b5ef8d952def18dd54`.
It reproduces the exploratory observation byte-for-byte. The historical
boundary-only route was also rerun and retained its exact prior semantic and
file identities, proving the producer option did not change default behavior.

## The deeper result: transport is no longer the bottleneck

The 138 rows divide into two materially different curricula:

| Slice kind | Rows | Reflexivity successes |
|---|---:|---:|
| Exact goal, no definition abstraction | 24 | 2 |
| One or more definition abstractions | 114 | 0 |

The 114 abstracted rows carry 152 exact definition abstractions. That boundary
is type-safe and exactly specializes back to the source, but a plain function
parameter does not carry the original definition's behavior. For example,
generalizing `Int.fib` turns a theorem about the concrete Fibonacci function
into a stronger statement about an arbitrary function of the same type. Many
such goals are not merely beyond reflexivity; they are intentionally missing
the semantic equations a real proof would need.

That corrects the naive next step. Adding a larger tactic grammar across all
138 goals would mix two gaps:

- the 22 exact, unsolved goals need genuine proof planning, rewriting,
  induction, arithmetic, and reusable library facts; while
- the 114 abstracted goals first need **checked semantic abstraction** so a
  producer receives behavior contracts that can be discharged axiom-free when
  the generalized proof is specialized to the exact source definitions.

The kernel did its job on the 46 candidates: the untrusted producer proposed
`Eq.refl` solely from goal shape, and the kernel rejected unequal sides. Those
are producer limitations, not kernel failures.

## Next flywheel turn

Work should proceed bottom-up and top-down in parallel:

1. classify the 152 abstractions by definition shape and the minimal equations
   or graph contracts required to preserve their source semantics;
2. specify a receipt extension that binds each contract, its source-definition
   identity, and an axiom-free specialization witness;
3. prototype one simple recursive definition contract and prove that arbitrary
   or mismatched contracts fail specialization;
4. run proof-plan work first on the 24 exact goals, where search outcomes are
   not confounded by semantic erasure; and
5. only combine semantic contracts with broader proof plans after both controls
   pass independently.

Over the horizon, the contract mechanism is more important than this corpus.
It is how Axeyum can abstract implementation closure without forgetting what a
symbol means: search stays small and untrusted, while the source kernel proves
that every locally assumed behavior is valid for the exact object receiving
ledger credit.

Held-out remains sealed. No upstream proof body was requested and no ledger row
changed.

## Reproduction

```sh
cargo test -p axeyum-lean-import --example type_slice_replay
python3 -m unittest scripts.tests.test_check_autogenesis_type_slice_producer_census
python3 scripts/check-autogenesis-type-slice-producer-census.py
```
