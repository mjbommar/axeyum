# Checked Mathlib type-slice replay

Date: 2026-08-19

## Result

The first checked train/development replay admits a proof-free producer
boundary for **128 of 138** frozen Mathlib v4.30 statements. It derives an
abstraction set from each exact source stream, constructs a closed generalized
proposition, root-exports only that target, independently imports it into a
fresh kernel, and issues a content-addressed receipt only after exact
specialization recovers the source proposition.

The accepted population contains 24 statements requiring no abstraction and
104 requiring one or more abstractions. Those 104 receipts bind 129 exact
definition instances in total, with at most three for one target. The replay
was rerun from committed tooling and reproduced the earlier observation
byte-for-byte:

- observation identity: `4c41833a5fa656fc7f38bf392e1dca0eb3dc47bb9ff010c411111af6c6bd4a36`;
- external file identity: `ba684bfe5663a27f62fb12d5e7d436fad5f2323f5b03d4ad8478e44aa4b5c07b`;
- accepted receipts: 128;
- typed selection declines: 10; and
- held-out reads, proof-producer executions, proof-body requests, and ledger
  writes: zero.

The committed checker recomputes the frozen mapping and all 138 source-stream
digests, the observation and receipt digests, row identities and totals,
specialization flags, abstraction order and identities, retained declaration
kinds, immutable external mode, and the historical Git blobs used to produce
the result. Mutation controls reject held-out membership, duplicate rows,
receipt changes, trusted retained declarations, decline-stage changes, and
coverage changes.

## Why ten statements decline

The selector retains inductives, constructors, and recursors so their
computation rules survive transport. It therefore audits the **exact atomic
root closure** of every retained structure type. Ten statements reach
`Semiring`, `Preorder`, or `Monoid` structures whose exported closure crosses a
theorem boundary. A representative `Semiring` path runs through `autoParam`,
`Lean.Syntax`, `String`, UTF-8 helpers, and a `Nat` decision procedure before
reaching `Nat.not_succ_le_zero` or a private no-confusion theorem.

This is not evidence that those theorems are mathematically needed by the
statement. It is evidence that Lean's current serialized structure metadata
mixes elaborator/default-value machinery into the atomic transport closure.
Silently retaining it would contaminate the producer environment; dropping it
without a checked equivalence would falsify the receipt. V1 therefore declines.

## Flywheel significance

Bottom-up, this replaces the earlier syntactic 138/138 feasibility count with
a semantic boundary: 128 statements are now independently reconstructible as
proof-free goals, and ten have one typed, reproducible blocker class. Top-down,
the next capability is no longer “build a type slicer.” It is narrower:
settle and check a normalization rule for elaborator-only `autoParam` structure
metadata while preserving kernel computation and definitional equality.

The next sequence is:

1. write an ADR defining which structure metadata is elaborator-only and what
   semantic equivalence the kernel must check;
2. implement a normalized root-transport control against the ten frozen
   declines, including negative cases where erasure would change meaning;
3. rerun train/development and require all prior 128 receipts to remain
   byte-semantically valid before accepting any newly covered row;
4. attach bounded proof producers to admitted slices and measure autonomous
   proof yield, still without opening held-out; and
5. freeze the selection policy before the single held-out evaluation.

No source fact is proved by this result. A receipt establishes only the goal
boundary on which a future untrusted producer may search.

## Reproduction

```sh
python3 -m unittest scripts.tests.test_check_autogenesis_checked_type_slice_replay
python3 scripts/check-autogenesis-checked-type-slice-replay.py
cargo test -p axeyum-lean-import --example type_slice_replay
cargo test -p axeyum-lean-import --test type_slice_generalization
```
