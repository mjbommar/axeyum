# Semantic-contract demand graph

Date: 2026-08-26

## Result

The 25 checked type slices are now joined to the current kernel lemma index and
the durable semantic-function-contract receipt population by exact identity.
The generated
[`semantic-contract-demand-v1.json`](../../artifacts/autogenesis/semantic-contract-demand-v1.json)
contains 14 source-definition nodes and their 25 affected facts.

The join finds:

- zero durable checked semantic-function contract receipts;
- two source identities with exact axiom-free kernel theorem candidates;
- eleven candidate theorems in total; and
- twelve source identities with no exact kernel theorem edge yet.

This corrects the next-step language. The type-slice machinery is not blocked,
and “add semantic contracts” is not one task. It is a graph of exact contract
demands, most of which first need behavior theorems or identity connectivity.

## Ranked first family

`Nat.testBit` ranks first because it affects four open siblings and has five
axiom-free theorems whose kernel types directly name that exact source
definition:

- `Nat.testBit_zero`;
- `Nat.testBit_succ`;
- `Nat.testBit_le_one`;
- `Nat.sum_testBit_lt`; and
- `Nat.sum_testBit_eq`.

Those rows are candidate context only. A theorem about concrete `Nat.testBit`
does not automatically prove a sliced theorem about an arbitrary function.
The contract boundary must construct a generic theorem consuming explicit
behavior, independently prove the behavior for the exact source definition,
specialize the generic theorem, and check the resulting concrete proof. The
existing semantic-function contract receipt API enforces exactly that shape,
but no durable receipt currently instantiates it for these 14 definitions.

`Int.gcd` ranks second with six exact candidates but only one affected target.
The other twelve nodes remain explicit `find-or-construct-behavior-theorems`
demands; name similarity is not promoted to an edge.

## Next implementation

1. Start with the four `Nat.testBit` siblings, not a bespoke single target.
2. Determine the smallest shared contract vocabulary drawn from the five exact
   candidates; each contract must have an independently checked source witness.
3. Construct one generic theorem family over an abstract bit-observation
   function and require at least three sibling conversions under the unchanged
   producer contract.
4. Issue and replay semantic-function contract receipts, then feed only the
   discharged contracts into the sliced producer environment.
5. Keep the remaining ten source identities without candidates visible as
   library/connectivity work for later turns.

Run `just autogenesis-semantic-contract-demand` to regenerate the exact join.
The artifact grants no contract, proof, operation, applicability, or ledger
authority.
