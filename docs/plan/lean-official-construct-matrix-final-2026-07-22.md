# Official Lean construct matrix: final result and handoff

Status: complete for the preregistered selected-family measurement population

Date: 2026-07-22

Decision:
[accepted ADR-0351](../research/09-decisions/adr-0351-preregister-official-lean-construct-matrix.md)

## Outcome

The source-first, wire-second, product-third experiment is complete without an
importer or kernel semantic change. Its seven generated assurance rows contain:

| Assurance class | Rows | Exact meaning |
|---|---:|---|
| `independently-admitted` | 1 | the immutable direct-recursive control admits 11 declarations with zero axioms |
| `translated-kernel-declined` | 1 | recursive-indexed reaches `KernelError::RecursiveIndexedNotSupported` |
| `parsed-declined` | 3 | reflexive, mutual, and the well-founded `Acc` closure stop at typed policy boundaries |
| `official-export-inventory-only` | 1 | nested exports valid official wire, but the importer misclassifies its two-recursor group as malformed |
| `official-source-rejected` | 1 | pinned Lean rejects the registered non-positive source |
| `dual-admitted-computation-checked` | 0 | no new positive family independently admits or computes |

The five retained official streams total 116,636 bytes. Every source/export
identity, independent wire inventory, repeated typed product outcome, and
assurance implication is machine checked. All declines are transactional and
publish no `CompletedImport`.

This closes the selected-family milestone, not TL1.8 or TL2.16 as a whole. It
does not claim recursive-indexed, reflexive, mutual, nested, or well-founded
admission; it does not claim that Axeyum enforces strict positivity; and it does
not claim general Lean-kernel, source-language, workflow, or ecosystem parity.

## Frozen checkpoints

1. `faccc621` freezes exact Lean 4.30 sources and official positive/negative
   outcomes.
2. `22f51b4b` freezes five byte-identical official exports and their independent
   wire inventories.
3. `25ba1d57` freezes two exact product outcomes per row, ten immediately
   preceding direct-recursive controls, and completion-only failure behavior.
4. `e77b03dc` generates the seven-row assurance matrix and its impossible-
   promotion tests.

The final documentation/decision commit records M5 and remote-ref equality.

## Final gates

All milestone-owned gates pass:

- kernel: 179 unit tests, the focused seam/Nat/projection/Prop/official-Lean/
  eta integration suites, and the kernel doctest;
- importer: declaration identity, format-3.1 import, official construct matrix,
  mutation corpus, and compile-fail doctest suites;
- focused `clippy -D warnings`, `cargo doc` with warnings denied, focused
  rustfmt, and `git diff --check`;
- 13 construct-matrix contract tests, 7 independent-reader tests, 6
  compatibility tests, 7 axiom-ledger tests, all matrix/freezer generators, and
  the full parity-document guard;
- 137 foundational concepts, 174 example packs, three negative fixtures, all
  generated dashboards, and all documentation links.

The first kernel rustdoc attempt failed while LLD linked from the 80%-full
`/tmp` tmpfs (`SIGBUS`). The same doctest passed under the same 4 GiB systemd
cgroup after moving `TMPDIR` to ext-family storage. Kernel logs showed no OOM or
I/O fault. This is recorded as an environmental temporary-storage/linker
failure, not a code or test failure.

`cargo fmt --all --check` remains red on pre-existing, out-of-milestone bench
and CAS files (including `audit_dominance.rs`, `cas_tour.rs`, and multiple CAS
modules). Those files were not formatted or staged. The new Rust matrix test is
individually rustfmt-clean.

## Handoff

The primary trusted-kernel trajectory is now:

1. **TL2.11 strict positivity:** preregister the accepted/rejected family
   grammar, enforce rejection before environment mutation, and fuzz the gate.
2. **TL2.12 recursive-indexed and reflexive induction hypotheses:** implement
   against the frozen `MiniVector` and `MiniAcc` wire forms only after TL2.11.
3. **TL2.13 mutual groups:** add multiple motives and shared minors against the
   frozen two-family group.
4. **TL2.14 nested/well-founded frontend lowering:** remain dependency-gated on
   mutual support and the native frontend; official export inventory alone is
   not native frontend support.

The nested `Malformed` outcome is a bounded TL1.8 diagnostic-classification
defect. Repair it in a separate importer-hardening change with a regression that
preserves the row's non-admission; do not confuse that repair with semantic
nested-inductive support and do not let it displace TL2.11.
