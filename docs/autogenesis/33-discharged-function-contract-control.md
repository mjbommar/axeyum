# First discharged function-contract control

Date: 2026-08-19

## Result

The first ADR-0488 control closes the missing semantic arrow without adding an
axiom. In a proof-isolated kernel, the producer-facing theorem is:

```text
forall (f : Nat -> Nat),
  (forall x, f x = x) ->
  forall n, f n = n
```

Its proof is only `fun f contract n => contract n`. It cannot see the source
definition, an upstream theorem, or a target answer. In the source kernel, the
exact transparent definition `Source.id := fun n => n` independently supplies
the local contract with `fun n => Eq.refl n`. Applying the generic proof to the
exact definition and that checked witness produces the concrete theorem with
zero axiom footprint.

This is a synthetic mechanism control, not Mathlib yield and not ledger credit.
It establishes that the architecture selected from the 32-identity census is
kernel-real before receipt or producer APIs are widened.

## Negative controls

Three distinct checks remain visible:

- `Source.id` and same-typed `Source.succ` have different canonical declaration
  identities;
- the reflexivity witness for `Source.id` is rejected against `Source.succ`'s
  pointwise contract; and
- a circular upstream answer can inhabit the contract type, but its axiom is
  present in the witness theorem's exact footprint, so type checking alone
  cannot counterfeit assurance.

The successful generic proof has zero theorem dependencies. The successful
source witness also has zero theorem dependencies and zero axioms. The concrete
result names exactly those two checked theorems as dependencies and remains
axiom-free.

## Next boundary

The mechanism must now become durable and source-bound. The next increment
should define a receipt that binds:

1. exact source content, instantiated type, and universe identities;
2. the locally inserted contract proposition and its position in the
   generalized telescope;
3. generic proof identity and independent proof-kernel footprint;
4. source-specialization witness identity and source-kernel footprint; and
5. the final specialized proposition and its equality to the frozen source
   goal.

Only after wrong identity, wrong contract, reordered binder, circular witness,
and stale receipt mutations fail should the mechanism be tried on one of the
15 real pointwise-function identities. `Int.gcd` is small and axiom-free at the
definition boundary, but selection must also consider the target statement's
proof demand; smallest body is not by itself authorization.

## Reproduction

```sh
cargo test -p axeyum-lean-import --test semantic_function_contract
cargo clippy -p axeyum-lean-import --test semantic_function_contract \
  --all-features -- -D warnings
```
