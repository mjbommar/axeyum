# Native Fibonacci composition

Date: 2026-08-20

## Result

The selected route around the assumption-bearing official `Nat.gcd_succ` now
has a checked environment:

```text
native axiom-free Nat and gcd library
  + exact Lean 4.30 Nat.fib definition
  + admitted axiom-free Nat.fib_add_two theorem
```

The resulting private kernel contains 236 declarations. The 198-declaration
native caller remains byte-for-byte unchanged. The composed recurrence has an
empty kernel-derived axiom footprint and no direct theorem dependencies.

This is not a second Fibonacci definition. The r080 recurrence stream and the
r082 coprimality-target stream contain the identical `Nat.fib` declaration:

```text
15f76f9318e04cf653cd094524473919b14a333c308cee32d6d428136bdc522c
```

## Scheduling defect repaired

The first r082 composition attempt declined at `HAdd`, even though the source
closure contained its prerequisite `outParam` first. Composition had been
validating a dependency-ordered slice and then discarding that order during
admission: it reconstructed all singleton inductive packages before all
definitions.

[ADR-0532](../research/09-decisions/adr-0532-mixed-definition-and-inductive-composition-follows-source-dependency-order.md)
changes scheduling, not authority. Definitions, atomic singleton packages, and
theorems now enter the private target in the source closure's single dependency
order. Every declaration still passes the ordinary target kernel gate;
unsupported kinds still decline; a late failure still publishes nothing.

The synthetic regression makes a missing definition the sort of a missing
singleton family. It proves the definition is admitted before the atomic
package and that the exact receipt replays without mutating the empty caller.

## Real compositions

| Source | Root | Closure | Reused | Added definitions | Added packages | Added theorems | Receipt |
|---|---|---:|---:|---:|---:|---:|---|
| r082 | `Axeyum.Autogenesis.fib_definition_probe` | 46 | 8 | 19 | 6 | 1 control | `208b7e8703b3de9e89319d2ba9716a917940ccaeb3f4a7af4527d1e2d6f790ee` |
| r080 | `Axeyum.Autogenesis.NatFibAddTwo` | 46 | 8 | 19 | 6 | 1 recurrence | `f7244fbc69e6ceec6ed2511e46786bccd2d5a4e4485f3e6de70743104f888168` |

The six packages are `OfNat`, `HAdd`, `Add`, `PUnit`, `PProd`, and `Prod`.
They are not trusted imports: each family is reconstructed atomically and
independently accepted by the target kernel. The 19 definitions include the
typeclass projections and instances, product projections, iterator machinery,
and `Nat.fib` itself.

The r080 operation replays the already fixed and admitted Fibonacci recurrence
construction. It performs no new proof search and receives no new theorem or
ledger credit. Its purpose here is to prove that the durable theorem can live
in the native gcd-capable environment with the exact imported Fibonacci
semantics.

## Route change

The prior direction tried to move native gcd support into r082:

```text
native gcd proofs -> imported official Nat environment
```

That route remains useful diagnostic evidence, but it reaches official
`Nat.gcd_succ`, whose proof depends on `Quot.sound`. The selected direction is
now:

```text
exact imported Nat.fib + established recurrence -> native gcd environment
```

This avoids importing a quotient assumption and reuses the existing axiom-free
native theorems named by the bounded coprimality plan.

## Immutable evidence

The generated observations are not vendored. Their read-only reference pack is:

`/nas3/data/axeyum/autogenesis/reference-packs/91d7df736-lean430-native-fib-composition-v1/manifest.json`

The manifest SHA-256 is
`b797f5876ca3d033a5e58424573a774e3cad1af6dc9723059555a779d3028877`.
The tracked checker binds its exact file set, modes, source streams, historical
implementation blobs, observation hashes, declaration identity, receipts,
footprints, and zero-write authority.

## Verification

```sh
cargo test -p axeyum-lean-import --all-targets
cargo clippy -p axeyum-lean-import --all-targets -- -D warnings

cargo run -p axeyum-lean-import \
  --example nat_fib_iterate_recurrence -- \
  --native-composition --stream /path/to/r080.ndjson

cargo run -p axeyum-lean-import \
  --example nat_fib_native_definition_probe -- \
  /path/to/r082.ndjson

python3 scripts/check-autogenesis-nat-fib-coprime-premise-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_nat_fib_coprime_premise_plan
```

## Next

Construct the bounded coprimality induction directly in the completed native
kernel. Its sole previously admitted theorem premise remains
`Nat.fib_add_two`; the other seven named lemmas come from the axiom-free native
Nat library. The resulting theorem must pass the independent kernel,
footprint, dependency, receipt, and crash-safe ledger gates before the target
fact changes state.

## Subsequent result

The bounded induction has now been constructed and independently accepted
twice; see [native Fibonacci coprimality](70-native-fibonacci-coprimality.md).
That result moves the frontier to the explicit semantic bridge between
official r082 `Nat.Coprime`/`Nat.gcd` and the native gcd definition. It does not
retroactively grant this composition receipt authority to substitute same-name
definitions.
