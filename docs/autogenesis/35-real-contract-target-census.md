# Real semantic-contract target census

Date: 2026-08-19

## Result

No real Mathlib theorem target is yet eligible for the first direct defining
equation contract. The exact committed-code census re-imported all 50
train/development rows affected by the 15 pointwise-function identities and
found **0/50** proof-free slices retaining every nonrecursive constant directly
named by the transparent source body.

This is a representation failure before proof search, not producer yield.

| Measure | Rows |
|---|---:|
| Pointwise-function bindings | 50 |
| Terminal equality goals | 38 |
| Source definition footprint axiom-free | 17 |
| Exactly one omitted body dependency | 5 |
| Both axiom-free and exactly one omitted dependency | 1 |
| Direct equation closed in current proof-free slice | **0** |

The observation has semantic identity
`caef4de329757abc280d77e52a3196f9a6903a6f9dbfa4565095f883386d084c`
and file identity
`dd2b1da9b36549e767a670eefb255715111ef1892be1bbc10621b3fa1c197860`.
It inspected no held-out row or proof body and generated no contract, producer
attempt, or ledger write.

## Narrowest control, not selected theorem

The unique narrowest row is `r018.ndjson`, fact
`F:ml430-int-gcd-div-5e01872f`. Its exact `Int.gcd` definition is axiom-free,
has an 11-node body, occurs twice in a terminal equality, and misses one body
constant from the proof-free slice:

```text
Int.gcd m n := Nat.gcd (Int.natAbs m) (Int.natAbs n)
                              ^ retained       ^ omitted Nat.gcd
```

The statement itself also abstracts integer and natural division instances.
Nothing in this census says that exposing the `Int.gcd` equation proves the
gcd-division theorem. `r018` is therefore preregistered only as the first
contract-body residualization control. Treating it as a selected proof target
would confuse representation reachability with mathematical sufficiency.

## Changed sequence

ADR-0489 inserts the missing step:

1. residualize omitted direct body constants into exact ordered local binders;
2. substitute recursive self-calls with the existing abstract function binder;
3. source-specialize every residual parameter and check the equation
   definitionally;
4. extend the receipt with the residual telescope and identities;
5. pass wrong-order, wrong-identity, self-reference, and omission controls; and
6. only then rerun target selection and freeze a proof experiment.

Over the horizon, this is the general mechanism by which a proof-isolated
kernel can receive transparent computation without importing the implementation
closure that justified removing the definition in the first place.

## Reproduction

```sh
cargo test -p axeyum-lean-import --example semantic_contract_target_census
python3 -m unittest scripts.tests.test_check_autogenesis_semantic_contract_target_census
python3 scripts/check-autogenesis-semantic-contract-target-census.py
```
