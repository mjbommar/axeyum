# First real trace-backed source-contract receipt

Date: 2026-08-19

## Result

The exact pinned Mathlib `Int.gcd` source now issues and replays a durable
trace-backed contract receipt:

```text
source:    Int.gcd
residual:  Nat.gcd
retained:  Int, Int.natAbs
contract:  forall intGcd natGcd,
             forall m n,
               intGcd m n = natGcd (Int.natAbs m) (Int.natAbs n)
discharge: one selected Int.gcd delta step
```

The receipt binds the exact declaration and instantiated-type identities for
all four source-side instances, the generalized and specialized contract
identities, the delta before/after identities, the one consulted declaration,
and an empty source axiom footprint. Replay recomputes every field from the
live imported kernel.

The external observation has semantic identity
`2c86744046efc1908e168eca804afc103a31473f7b7df93c4a22700d82a3533f`
and file identity
`22a968ae3fb662d730906415cfc7f84f4dee4e92ac7186dcdb0e1edac4ed065d`.
The receipt itself has identity
`ae7585751df713ac8fda6f611c3197b0917c9001dc8bda134e9a43416ce3ec82`.
The observation is sealed read-only in the content-identified `/nas3` archive.

## Assurance boundary

| Result | Count |
|---|---:|
| Source-contract receipts issued and replayed | **1** |
| Selected delta steps | 1 |
| Source axioms | 0 |
| Witness theorems constructed | 0 |
| Semantic theorem receipts issued | 0 |
| Producer target attempts | 0 |
| Ledger writes | 0 |

This is the first real contract receipt, not the first real theorem receipt.
No held-out row or upstream proof body was inspected. The previous
theorem-valued reflexivity witness remains rejected; no member of its
52-theorem closure was whitelisted.

## Controls

The reusable receipt rejects:

- an omitted direct body dependency;
- a direct axiom, theorem, or opaque instance;
- an axiom hidden below an ordinary residual definition;
- retention of the source or residual constant in the generalized template;
- mutated source, contract, delta, consulted-declaration, or binder identity;
  and
- any receipt that cannot be exactly reissued from the current kernel.

The external checker additionally rejects held-out access, changed residual or
source identities, a widened delta, a hidden source axiom, and self-reported
theorem-receipt credit.

## Next flywheel turn

The bottom-up source capability is now ready. The next work is top-down target
selection: identify one frozen train/development proposition whose proof
actually needs this `Int.gcd` contract, preregister a small generic proof grammar
and resource budget, and attempt it without inspecting the held-out outcome or
Mathlib proof body.

## Reproduction

```sh
cargo test -p axeyum-lean-import --test trace_contract_receipt
cargo test -p axeyum-lean-import --example int_gcd_trace_contract_receipt
python3 -m unittest scripts.tests.test_check_autogenesis_int_gcd_trace_contract_receipt
python3 scripts/check-autogenesis-int-gcd-trace-contract-receipt.py
```
