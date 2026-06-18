# Bit-blast reconstruction — the multiplier term blowup (P3.7)

Status: **measured finding + guard landed (2026-06-18).** Records why wide
`bvmul` Alethe→Lean reconstruction is intractable with the current inlined
encoding, the guard that prevents OOM, and the durable fix (shared/`let`
encoding).

## What happened

A validation probe reconstructing an **8-bit `bvmul`** proof end-to-end OOM'd the
process. The committed reconstruction tests use width 2 and are unaffected; the
blowup only shows at larger widths.

## Root cause: the inlined multiplier term is exponential in width

`reconstruct.rs::mult_bit_term` (and the emitter's
`bitblast_alethe.rs::shift_add_multiplier_bits`) build the shift-add multiplier
result bit as an **un-shared `AletheTerm` tree**. The carry recurrence

```
carry[j][k] = (or (and  res[j-1][k-1] shift[j][k-1])
                  (and (xor res[j-1][k-1] shift[j][k-1]) carry[j][k-1]))
```

embeds `res[j-1][k-1]` **twice** (once in the first `and`, once inside the
`xor`), so each round roughly multiplies the node count. Measured node count of
the top result bit (via the recurrence, no allocation):

| width | top-bit nodes | width | top-bit nodes |
|---|---|---|---|
| 4 | 113 | 9 | 198 979 |
| 5 | 451 | 10 | 981 785 |
| 6 | 1 937 | 11 | 4 926 559 |
| 7 | 8 767 | 12 | 25 062 625 |
| 8 | **41 193** | | |

Building that tree, lowering it to a kernel `Expr`, and `def_eq`-checking the
reflexive iff over it exhausts memory at width 8 and is hopeless at 32/64-bit
(real QF_BV). **Only the multiplier is affected** — the ripple-carry adder/`bvneg`
embed `carry[i-1]` once, so they are `O(width^2)` (a 64-bit adder bit is ~4 k
nodes, fine).

## The guard (landed: `5953b7d`)

The `bvmul` `bv_bit` branch computes `mult_bit_node_count(i)` (the recurrence
above, no allocation) and, if it exceeds `MULT_BIT_NODE_BUDGET = 20_000`
(~7-bit), returns a clean `ReconstructError::UnsupportedTerm` instead of OOMing.
Reconstruction processes the top bit first, so a wide multiplier is rejected
before any large term is built. Tested: 8-bit `bvmul` → guarded; width-2 still
reconstructs.

This makes the failure **sound and bounded** (a clean "unsupported", never a
crash) but leaves wide-multiplier proofs **unreconstructed** — an honest
correction to the "QF_BV operator set complete" milestone (`58e9062`): the
operator set is covered, but the multiplier only at small widths.

## The durable fix: a shared / `let` encoding

The exponential blowup is purely a *representation* problem — the multiplier
circuit is polynomial-size as a **DAG** (each `res[j][k]`/`carry[j][k]` gate is
one node, `O(width^2)` gates). Inlining it to a tree is what explodes it. The fix,
in order of preference:

1. **Reconstruction-side sharing.** Memoize gate→`ExprId` so identical
   sub-circuits map to one kernel `Expr` (a DAG). This needs the *gadget* side
   (the emitter's `@bbterm`) to also be shared, otherwise the `AletheTerm` itself
   is already exponentially large in memory before reconstruction sees it.
2. **Emitter-side sharing (the real fix).** Emit the multiplier (and any
   carry-chain) with **auxiliary Tseitin definitions** — a fresh proof
   variable/step per `res[j][k]`/`carry[j][k]` gate, referenced rather than
   inlined — exactly how a CNF Tseitin encoding avoids the blowup. The Alethe
   proof becomes `O(width^2)` and Carcara-checkable; reconstruction then walks the
   shared definitions. This is an ADR-level change to `bitblast_alethe.rs` +
   `reconstruct.rs` and is the prerequisite for certifying real-width multiplier
   proofs.

Until (2) lands, multiplier proofs are reconstructable only at small widths
(`≤ ~7-bit`), which is sufficient for the unit/integration coverage but not for
production QF_BV. Adder/`neg`/bitwise/structural/comparison ops are unaffected and
reconstruct at any width the SAT layer can handle.
