# Official Lean construct matrix: Stage B wire-freeze result

Status: official exports and independent wire inventories frozen; no Rust
product measurement performed

Date: 2026-07-22

Parents:

- [execution plan](lean-official-construct-matrix-plan-2026-07-22.md);
- [M0 and Stage A source freeze](lean-official-construct-matrix-stage-a-2026-07-22.md).

Registration:
[`lean-official-construct-matrix-v1.json`](lean-official-construct-matrix-v1.json)

Decision:
[proposed ADR-0351](../research/09-decisions/adr-0351-preregister-official-lean-construct-matrix.md)

## Outcome

Every frozen positive root was exported twice from a fresh pinned-Lean `.olean`
under the registered 4 GiB cgroup. Each pair is byte-identical. The five new
retained streams total 116,636 bytes, comfortably below the preregistered 1 MiB
per-stream and 2 MiB aggregate limits. The independent Python reader validates
the complete format/topology and freezes every declaration name plus exact
inductive type, constructor, recursor, motive, minor, and rule metadata.

No new stream has been passed to `axeyum-lean-import`. The registration's top-
level and per-case product fields remain `null`, and the normal gate rejects
premature product data. This is official wire evidence, not independent kernel
admission evidence.

## Exact retained streams

| Case | SHA-256 | Bytes | Records | N/L/E/D | Independent wire blockers | Export RSS KiB |
|---|---|---:|---:|---|---|---|
| `recursive-indexed` | `df1e82fa72eac9f2a37cdf3b0eb8044f118489c51f76ab14b9af06c3f4cf11de` | 9,899 | 175 | 34/4/132/4 | `inductive-recursive-indexed` | 705,040 / 709,160 |
| `reflexive-higher-order` | `a2dc21e61e6938bd5eb5d8c4032c7d6197e312c7a617b8bd33388f2e46db0ec3` | 10,583 | 196 | 47/3/139/6 | `inductive-recursive-indexed`, `inductive-reflexive` | 716,880 / 714,148 |
| `mutual` | `06aa05ccc8abc9309fad04b373017e770da25c7b0c2743fc0f097efd72de3174` | 23,596 | 395 | 75/4/305/10 | `inductive-mutual` | 716,420 / 716,864 |
| `nested` | `faabcde4553b0d597a768aedf35117d7fb4310d3dae052e2545e5b239277456e` | 23,418 | 409 | 70/6/322/10 | `inductive-nested` | 716,440 / 716,976 |
| `well-founded` | `c1fc14097f9be381625846f13277edfd8294afd93c8e9cadd72c54d71e48e3c6` | 49,140 | 920 | 160/5/731/23 | `inductive-recursive-indexed`, `inductive-reflexive` | 715,320 / 714,960 |

`N/L/E/D` means name, nonzero-level, expression, and declaration-record counts.
The `D` count is wire records; the registration separately freezes every
declaration name expanded from grouped inductive records.

## Source-to-wire findings

The official forms answer the questions that Stage A deliberately did not
guess.

### Recursive-indexed

`MiniVector` is one recursive inductive type with one parameter, one index,
zero nested occurrences, and `isReflexive=false`. Its recursor has one motive,
two minors, and rule field counts 0 and 3. This is the direct measured target
for TL2.12 after TL2.11 positivity.

### Reflexive/higher-order

`MiniAcc` is one recursive inductive type with two parameters, one index,
zero nested occurrences, and `isReflexive=true`. Its recursor has one motive,
one minor, and a two-field rule. The wire census correctly classifies this row
as both recursive-indexed and reflexive; those are core facts, not competing
source labels.

### Mutual

`EvenTree` and `OddTree` are one inductive group with two recursive types. Each
has one parameter and zero indices. Both generated recursors carry two motives
and four minors; their rule populations remain type-specific. This is a direct
multi-motive TL2.13 target rather than two unrelated single-family declarations.

### Nested

The official core retains `Rose` as one recursive type with one parameter,
zero indices, and `numNested=1`; it emits two recursors,
`Rose.rec_1` and `Rose.rec`, each with two motives and three minors. The nested
source did not become a two-type mutual group in this export. The wire label is
therefore `inductive-nested`, while “rose tree under `NestList`” remains the
source-family label.

### Well-founded

The selected theorem exports 23 declaration records. The user definition
`wellFoundedLoop` is an ordinary definition built through `WellFounded.fix`;
there is no new “well-founded” wire declaration kind. Its dependency closure
contains official `Acc` (two parameters, one index, recursive and reflexive),
`WellFounded`, `WellFounded.fixF_eq`, and `WellFounded.fix_eq`. Consequently the
reader reports recursive-indexed and reflexive blockers from the `Acc` closure.
This validates the plan's distinction between a source mechanism and its
elaborated core dependencies.

## Independent inventory contract

The reader now resolves every dense exported name ID and records:

- the exact expanded declaration-name sequence;
- per-type `numParams`, `numIndices`, `numNested`, `isRec`, and `isReflexive`;
- constructor owner, index, parameter count, and field count;
- recursor `all` names, parameters, indices, motives, minors, `k`, rule
  constructors, and rule field counts;
- all existing expression/declaration-kind counts and stable blocker classes.

The Stage B freezer recomputes that inventory from retained bytes and requires
the final declaration to equal the preregistered selected root. The normal
validator independently recomputes it again, enforces both export repetitions
and RSS values, checks per-stream and aggregate retention, resolves every case
link, and rejects unknown fields or product observations. The freezer's
`--check` mode proves the complete 53,210-byte registration regenerates
byte-for-byte from the official fixtures.

## Next gate

M3 may start only after this Stage B commit is pushed and local, tracking, and
remote refs agree. It must then:

1. run the immutable direct-recursive 11-declaration/zero-axiom control before
   each new row;
2. run each new stream twice through the current Rust importer without changing
   importer or kernel semantics;
3. record exact typed parse, translation, kernel, or completed-import outcomes;
4. prove every decline exposes no `CompletedImport` or partial kernel;
5. stop if a row unexpectedly admits until the preregistered computation and
   malformed-control gates exist.

ADR-0351 remains proposed. Stage B closes the official-wire mechanics, but the
product-outcome and generated assurance-promotion gates are still open.
