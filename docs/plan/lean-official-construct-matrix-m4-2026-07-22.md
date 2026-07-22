# Official Lean construct matrix: M4 assurance result

Status: generated selected-family assurance matrix complete; M5 final gates and
handoff remain

Date: 2026-07-22

Generated artifact:
[`generated/lean-official-construct-matrix.md`](generated/lean-official-construct-matrix.md)

Machine source:
[`lean-official-construct-matrix-v1.json`](lean-official-construct-matrix-v1.json)

## Outcome

M4 generates all seven public rows from the frozen source, official wire, and
current-product facts. No assurance class is hand-maintained. The normal checker
recomputes all source/stream hashes and wire inventories, validates the exact
typed product outcomes, derives each row, enforces the class implications, and
then compares the committed Markdown byte-for-byte.

The selected-family population is:

| Assurance class | Rows | Cases |
|---|---:|---|
| `independently-admitted` | 1 | direct-recursive control |
| `translated-kernel-declined` | 1 | recursive-indexed |
| `parsed-declined` | 3 | reflexive/higher-order, mutual, well-founded dependency closure |
| `official-export-inventory-only` | 1 | nested, because valid official wire is currently misclassified as malformed |
| `official-source-rejected` | 1 | non-positive source negative |
| `dual-admitted-computation-checked` | 0 | none |

Only the exact direct-recursive stream receives independent-admission credit.
No row receives computation credit. The five new positive official exports all
remain declines, and the non-positive source has no export by construction.

## Impossible-promotion teeth

The row implication gate rejects at least these invalid states:

- independent-admission class without `CompletedImport`;
- computation-checked class without both independent admission and an explicit
  checked computation;
- translated-kernel class without a typed `Kernel` outcome;
- parsed-declined class without a typed `Unsupported` outcome;
- source-rejected class when a stream exists or official source acceptance is
  claimed;
- inventory-only class paired with an incompatible Rust success or decline;
- any unregistered assurance class.

The focused tests mutate the recursive-indexed row toward false independent
admission, the nested row toward false parsed/unsupported credit, and the
direct-recursive row toward false computation credit. All reject.

## Preserved boundaries

The generated prose preserves facts that a binary pass/fail table would erase:

- recursive-indexed reached the trusted kernel but did not admit;
- reflexive and mutual stopped at explicit importer policy boundaries;
- nested official wire is valid, but the importer currently calls its two-
  recursor group malformed;
- well-founded source stopped at the reflexive/recursive-indexed `Acc`
  dependency before the selected root;
- official strict-positivity rejection is not evidence that Axeyum implements
  its own positivity checker;
- official export or Python parsing never becomes independent-checking credit.

## Status effect

This selected matrix advances TL1.8 and changes TL2.16 from TODO to PARTIAL. It
does not complete either phase's full format/root population, and it does not
complete TL2.11--TL2.14. The primary semantic sequence remains positivity,
recursive-indexed/reflexive induction hypotheses, then mutual groups. Nested and
well-founded native work remains dependency-gated.

## Next gate

M5 runs the final bounded validation set, synchronizes the remaining current-
state prose, decides ADR-0351 from its explicit exits, and verifies committed/
pushed local, tracking, and remote refs. It must record the pre-existing
workspace-wide rustfmt failure without formatting unrelated CAS/bench work.
