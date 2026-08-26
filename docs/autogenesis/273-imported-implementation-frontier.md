# Imported implementation frontier

Date: 2026-08-26

## Result

The raw imported
[`implementation-demand graph`](272-imported-implementation-demand.md) now has
a generated reverse-reachability projection:
[`imported-implementation-frontier-v1.json`](../../artifacts/autogenesis/imported-implementation-frontier-v1.json).
It replays every root's transparent closure from the compact node/edge graph,
joins each node back to affected open facts, and records direct transparent
consumers and minimum/maximum depth from a demanded semantic root.

The projection contains 1,000 context-bound transparent nodes. A deliberately
narrow focus filter retains 113 nodes in the `Nat`, `Int`, or `List` namespaces
that are within four transparent edges of a demanded root and reach either two
source identities or three affected targets. This filter is deterministic
scheduling context, not a claim that a node should be unfolded or transported.

## First shared family

For the four `Nat.testBit` siblings, the projection replaces the vague phrase
“support all co-abstractions” with a concrete shared subgraph. The leading
context reaches all four affected targets through three demanded roots
(`List.getI`, `Nat.bits`, and `Nat.testBit`). Its high-reach nodes include:

- `Nat.land` at focus rank 1;
- `Nat.ble` at rank 6;
- `Nat.bitwise` at rank 8;
- `Nat.testBit` at rank 22; and
- the relevant `Nat.instAndOp` projection at rank 23.

Those ranks do **not** say that `Nat.land` is the first theorem to prove. They
say that a contract vocabulary capable of describing bitwise observation,
indexing, and the boolean/order decision path can be reused across the whole
four-target family. A contract for `Nat.testBit` alone remains insufficient.

The projection also keeps contexts separate. For example, same-named
`Nat.ble`, `Nat.land`, and `Nat.bitwise` nodes appear with different stream and
dependency identities where appropriate. A name-only global graph would have
created false paths between independently checked environments.

## Next construction sequence

1. Extract the exact intersection of nodes reachable from the four sibling
   facts and distinguish observation-level nodes from generic implementation
   infrastructure.
2. Express the smallest generic bit-observation interface over that
   intersection: lookup behavior, bitwise-and/or behavior, and the required
   zero/out-of-range laws.
3. Bind each interface law to an independently checked theorem about the exact
   source identity. Do not use graph reachability as a witness.
4. Build one generic theorem family consuming only those explicit laws and
   require it to convert at least three frozen siblings with the unchanged
   producer and all false controls still declined.
5. Only then issue durable semantic-function contract receipts and consider
   operation registration.

`just autogenesis-imported-implementation-demand` checks both the raw graph and
this derived frontier. Reproduction from the frozen external streams rebuilds
the raw graph first and then regenerates the frontier. Neither artifact reads a
target theorem proof, inspects held-out targets, or writes facts.
