# First exact contract-body residualization

Date: 2026-08-19

## Result

The first exact Mathlib contract body now residualizes and specializes:

```text
source:
  Int.gcd m n := Nat.gcd (Int.natAbs m) (Int.natAbs n)

producer-facing contract shape:
  forall (intGcd : Int -> Int -> Nat)
         (natGcd : Nat -> Nat -> Nat),
    forall m n,
      intGcd m n = natGcd (Int.natAbs m) (Int.natAbs n)
```

`Nat.gcd` is the one omitted body constant and becomes an exact ordered local
parameter. `Int` and `Int.natAbs` are explicitly accounted as retained direct
body dependencies. The existing type-slice machinery generalizes both exact
constant instances, and the source kernel independently specializes them back
to `Int.gcd` and `Nat.gcd`, recovering the original equation definitionally.

The exact observation has semantic identity
`af928f24ea7dae4420ea1d4aece3c172589529d23ea8936c3456ccb70515f303`
and file identity
`ebbebfc1d4670903c56258c8c2cb5d20acdd0593e477e6af57a6f826e939f2db`.
No held-out row or proof body was inspected and no target, contract, producer
attempt, or ledger write was authorized.

## Controls

The reusable primitive fails on:

- an omitted direct body constant;
- one exact constant classified as both retained and residual;
- a dependency-forward residual binder order; and
- unsupported polymorphic, dependent-result, or projection shapes rather than
  silently approximating them.

The synthetic positive control produces a bounded reflexivity witness whose
complete closure is theorem- and axiom-free. The exact `Int.gcd` source equation
also receives a five-node reflexivity proof and has zero axioms.

## The next trust boundary

The real result exposed why direct dependency reporting is insufficient:

| `Int.gcd` source witness audit | Count |
|---|---:|
| Axioms | 0 |
| Direct theorem dependencies | 0 |
| Theorems in complete declaration closure | **52** |

Those 52 arise below transparent source definitions. The result is therefore
not receipt-eligible. ADR-0490 strengthens receipt admission to the complete
closure and adds an adversarial theorem-hidden-behind-definition control.

This does not mean all 52 theorems are mathematically needed for the one-step
equation. In fact, `Eq.refl` needs only the selected `Int.gcd` delta step while
`Nat.gcd` can remain opaque on both sides. But claiming that narrower fact
requires evidence the current kernel does not emit. The next increment is a
proof-free residual definition template plus a bounded reduction trace that
permits exactly the selected source unfold and records what was actually
consulted.

## Reproduction

```sh
cargo test -p axeyum-lean-import --test contract_residualization
cargo test -p axeyum-lean-import --test semantic_function_contract
python3 -m unittest scripts.tests.test_check_autogenesis_int_gcd_contract_residualization
python3 scripts/check-autogenesis-int-gcd-contract-residualization.py
```
