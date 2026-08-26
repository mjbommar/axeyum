# Imported Nat.mod remainder family

Date: 2026-08-26

## Result

One unchanged empty-footprint contract family converts all three frozen
arithmetic `Nat.ModEq` siblings. For every target, Axeyum transports the same
three candidate roots, bounded application constructs a proof, and a fresh
theorem admission succeeds with no axiom footprint and no dependency on the
hidden target declaration. Each final theorem has exactly one direct theorem
dependency—the transported behavior contract actually used by the proof—and
the receipt records stable goal, proof, and declaration identities for the
authoritative execution layer.

The durable result is
[`nat-modeq-remainder-contract-v2.json`](../../artifacts/autogenesis/nat-modeq-remainder-contract-v2.json):
3/3 conversions, zero remaining siblings, and zero facts settled. The last
number matters. This receipt makes the family eligible for operation
registration; it does not bypass authoritative dispatch or the crash-safe fact
transaction.

## Shared mathematical spine

The public Lean 4.30 remainder lemmas are not reused because their proof
closures carry `propext`. The replacement family builds:

1. fuel independence for `Nat.modCore.go`;
2. the one-step `Nat.modCore` equation without proposition-to-equality rewriting;
3. equality between `Nat.modCore` and the exact imported `Nat.mod`;
4. an axiom-free modulo recurrence;
5. periodicity under adding the modulus, with the opposite orientation obtained
   from axiom-free addition commutativity; and
6. the previously measured self-modulus law.

Lean reports an empty footprint for every helper and exported root. The
candidate capsule and three proof-free target capsules remain unvendored under
the hash-bound `/nas3/data/axeyum/autogenesis/reference-packs/` paths in the
receipt.

## Next falsifiable step

Register exactly this three-target family as one reusable authoritative
operation. Dispatch each still-open fact through a clean episode and require
the normal crash-safe transaction to attach evidence and settle it. Any change
to candidate roots, capsule hashes, footprint, or trusted base requires a new
receipt rather than inheriting this eligibility result.
