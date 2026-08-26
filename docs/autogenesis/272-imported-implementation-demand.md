# Imported implementation-demand graph

Date: 2026-08-26

## Result

The semantic-contract graph said which 14 exact imported definitions obstruct
25 proof-isolated statement slices. It did not say what those definitions are
made of. The new generated
[`imported-implementation-demand-v1.json`](../../artifacts/autogenesis/imported-implementation-demand-v1.json)
fills that gap by traversing the transparent implementation of each exact
source identity in a representative frozen Mathlib stream.

The checked population contains:

- 14 exact root-definition identities;
- 1,363 transparent-definition occurrences; and
- 7,303 direct dependency-edge occurrences;
- 1,000 context-bound transparent nodes;
- 1,734 context-bound declaration nodes including stopped boundaries; and
- 5,421 context-bound direct edges.

Occurrences intentionally remain per root. This records the environment in
which each type-slice receipt was independently checked and avoids silently
turning equal-looking names from separate imports into transport authority.
Every declaration node carries canonical content and direct-dependency hashes,
plus the representative stream hash that defines its context. Same-named
structural variants across independently materialized streams remain separate
rather than being collapsed by name. Dense integer node IDs keep the committed
graph near 1 MiB instead of repeating those hashes on every edge. The graph stops
at inductives, constructors, recursors, theorems, opaque declarations, axioms,
and quotient primitives and records those as the nontransparent boundary.

This is connective tissue, not a proof source. It reads the declaration bodies
of definitions already selected for abstraction, but requests no target
theorem proof, examines no held-out target, constructs no contract, and writes
no ledger state.

## What it changes about the modulus boundary

The earlier `Nat.ModEq` experiment retrieved the right native theorem but its
proof stopped at imported `Nat.div_mod_exec`. The graph now makes the reason
machine-readable rather than anecdotal. Imported `Nat.mod` reaches this spine:

```text
Nat.mod
├── Nat.decLe ──> Nat.ble
└── Nat.modCore
    ├── Nat.decLt ──> Nat.decLe
    └── Nat.modCore.go
        └── Nat.modCore.go._f ──> instSubNat
```

It also reaches `ite`/`dite`, recursive `Nat.brecOn` machinery, order evidence,
and the checked theorem `Nat.div_rec_fuel_lemma`. A native equality about
Axeyum's separately constructed `Nat.mod` therefore cannot be grafted onto the
imported constant merely because its surface statement looks right. The
portable capability must be one of:

1. generic remainder reasoning parameterized by an explicit behavioral
   contract;
2. independently checked behavior lemmas for the exact imported decision,
   order, subtraction, and recursion spine; or
3. proof-directed normalization that evaluates that spine while retaining an
   independently checkable term.

The graph does not choose among those designs. It identifies the exact shared
machinery against which each can be measured.

## How to use it

Join the root identities to the
[`semantic-contract demand graph`](270-semantic-contract-demand.md). Rank a
capability by the number of affected targets whose *entire* co-abstraction set
it helps, then use the transparent subgraph to find shared lower-level
machinery. A node's frequency is scheduling evidence only; it is not evidence
that unfolding it is useful or safe.

Immediate sequence:

1. Use the derived reverse-reachability projection to rank shared primitives
   without rescanning the raw receipt graph.
2. Compare the `Nat.testBit` sibling roots' intersection and difference. Select
   the smallest contract vocabulary that covers at least three siblings,
   including their co-abstractions rather than `Nat.testBit` alone.
3. Separately extract the imported remainder spine as the first
   representation-boundary control. Test a generic remainder-equality theorem
   against explicit `decLe`/subtraction behavior instead of transporting a
   native implementation theorem.
4. Issue semantic-function contract receipts only after source witnesses and
   generic proofs independently check. Then rerun the unchanged producer over
   the frozen open population.

Run `just autogenesis-imported-implementation-demand` for the committed
fail-closed checks. On a host with the frozen source streams, run
`just autogenesis-imported-implementation-demand-reproduce`; the regenerated
artifact must pass the same check. The checker pins the exact root join, the
reviewed counts, graph closure, and the imported modulus spine.
