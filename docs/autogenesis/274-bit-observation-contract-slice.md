# Bit-observation contract slice

Date: 2026-08-26

## Result

The first family-specific slice is now generated from exact checked identities,
not selected by theorem names. The
[`bit-observation-contract-slice-v1.json`](../../artifacts/autogenesis/bit-observation-contract-slice-v1.json)
selects the unique four-target `Nat.testBit` demand, joins each fact to all of
its checked abstractions, unions each target's transparent closures, and then
computes their intersection.

The four statements are:

- `n.testBit i = n.bits.getI i`;
- `(m &&& n).testBit k = (m.testBit k && n.testBit k)`;
- `(m.ldiff n).testBit k = (m.testBit k && !n.testBit k)`; and
- `(m ||| n).testBit k = (m.testBit k || n.testBit k)`.

Together they reach 471 context-bound transparent nodes. Exactly 103 nodes are
shared by all four targets. The target-specific deltas are 106 nodes for the
list/bits statement, 87 for conjunction, 88 for difference, and 87 for
disjunction. An explicitly non-authoritative lexical review queue retains 18
shared observation-related nodes, from `Nat.testBit` through `Nat.land`,
`Nat.shiftRight`, `Nat.bitwise`, `Nat.decLe`, and `Nat.ble`.

## The corrected contract boundary

The five exact axiom-free kernel candidates attached to `Nat.testBit` establish
its zero/successor behavior, its one-bit bound, and two sum/reconstruction
properties. None states how `Nat.bitwise`, `Nat.land`, `Nat.lor`, `Nat.ldiff`,
or list lookup commutes with bit observation. Therefore those five candidates
cannot discharge the four-target family by themselves.

This prevents a circular design. Treating the desired `testBit_land`,
`testBit_lor`, or `testBit_ldiff` conclusion itself as the “source behavior
witness” would merely rename the target theorem as a contract. A useful generic
contract must instead expose smaller independent laws, such as:

1. a step/zero characterization of the abstract bit observer;
2. a pointwise recurrence for the abstract binary bitwise operator;
3. a recurrence or projection law for the abstract bit-list view; and
4. boolean-and/or/not observations needed by the concrete operation.

Each concrete source witness must be independently checked for the exact
imported definition. The generic theorem may then consume those witnesses to
derive the target-level commuting law. This is strictly stronger evidence than
unfolding a shared implementation node and strictly less circular than assuming
the desired conclusion.

## Next implementation

1. Search the imported statement corpus and native kernel index for exact
   lower-level recurrence/commutation theorems about `Nat.bitwise`, `Nat.bits`,
   and `List.getI`; record missing theorem families explicitly.
2. Add the smallest missing generic bitwise-observation theorem to the native
   foundation only if no checked candidate exists. Keep it operator-parametric
   so conjunction, disjunction, and difference share one constructor.
3. Build source witnesses for the exact imported definitions and issue checked
   semantic-function contract receipts.
4. Rerun the unchanged sliced producer on all four targets. Require at least
   three accepts, zero false-control accepts, empty measured footprints, and no
   per-target proof plan before operation registration.

Run `just autogenesis-imported-implementation-demand` to check this slice with
the raw graph and reverse frontier. It reads no target theorem proof and grants
no contract, proof, transport, operation, or ledger authority.
