# Lean nested-inductive elimination: M0 source/wire freeze

Status: complete; M1 diagnostic preflight is next

Date: 2026-07-22

Baseline revision: `def1000feed25f40d170a7fe95f9bbe0afa6dd21`

Parent:
[TL2.14 execution plan](lean-nested-inductive-elimination-tl2.14-plan-2026-07-22.md)

Decision:
[proposed ADR-0355](../research/09-decisions/adr-0355-preregister-lean-nested-inductive-elimination.md)

Machine registration:
[`lean-nested-inductive-elimination-v1.json`](lean-nested-inductive-elimination-v1.json)

## Result

M0 freezes the pinned Lean 4.30 source behavior and wire shape needed to
implement nested-inductive elimination without first observing Axeyum's answer.
The retained evidence consists of:

- the existing `Rose` construct-matrix stream and its repeatable current
  `Malformed` product outcome;
- the already completing 35-declaration/zero-axiom well-founded core stream;
- one positive source with explicit main and auxiliary recursor calls across
  ordinary, indexed-container, and repeated-container nested groups;
- three root-specific format-3.1 exports reproduced byte-identically twice;
- one source that pinned Lean rejects twice because a nested container
  parameter contains a constructor-local variable; and
- a fail-closed registration of the later native, mutation, generated,
  retention, resource, and stop gates.

The claim boundary is exact: Axeyum did **not** import, admit, normalize, or
otherwise consume any of the three new streams. Their official source
theorems close by definitional equality in pinned Lean. This is source/wire
evidence, not TL2.14 product credit.

## Positive source and computations

[`lean-v4.30-nested-inductive-computation.lean`](fixtures/lean-v4.30-nested-inductive-computation.lean)
is 2,917 bytes / 98 lines at SHA-256
`c5cadeaf11302d5ca9b5a60b2a3b72998ad994e7eb176ddc5de40ebfc05c475d`.
It deliberately calls generated recursors explicitly rather than relying on a
constructor-only witness or source recursion:

1. `roseSize` crosses
   `Rose.rec -> Rose.rec_1 -> Rose.rec -> Rose.rec_1` and proves the registered
   three-successor normal form.
2. `indexedRoseSize` crosses the same main/auxiliary boundary through
   `NestVec (IndexedRose α) n`; the auxiliary recursor owns one index while the
   source-family recursor owns none.
3. `repeatRoseSize` places the structurally identical
   `NestList (RepeatRose α)` application in two constructor fields. Both paths
   use one `RepeatRose.rec_1`, and the theorem proves the registered
   five-successor normal form.

The source compiled twice under one Lean worker at exit 0 in 290 and 240 ms.
Maximum RSS was 462,832 and 462,920 KiB. Both runs produced the same OLEAN
SHA-256:
`d7d03cb863626f1ddc2a80b0dee3ae19fbc001dc2fb4ac60f6b9e27c7b7f53c2`.

## Frozen official streams

| Root | SHA-256 | Bytes | Records | N/L/E/D | Export ms | RSS KiB |
|---|---|---:|---:|---|---|---|
| `roseAuxiliaryRecursorComputes` | `36fb9c6f85a99a7d6d1f6329a2cfe5265b148f0138e979d6d391d9e8879e07de` | 36,706 | 642 | 122/8/494/17 | 1,110 / 320 | 668,176 / 672,492 |
| `indexedAuxiliaryRecursorComputes` | `a14ca423410c4f0a86c2a2cea193e5a76bd91428e348402b3dd32e1603481429` | 40,119 | 714 | 134/8/554/17 | 330 / 310 | 672,208 / 674,308 |
| `repeatedContainerReusesAuxiliaryRecursor` | `af369edb2d9e0346a5457ba4c9cde6f3030ca08002dc931c5fb26709e0f74344` | 37,771 | 666 | 122/8/518/17 | 290 / 330 | 674,520 / 673,784 |

`N/L/E/D` means names, nonzero levels, expressions, and declaration records.
The aggregate is 114,596 bytes / 2,022 records, below the registered 1 MiB
per-stream and 2 MiB aggregate retention bounds. Each selected theorem is the
final declaration in its stream. All exports identify Lean 4.30.0 commit
`d024af099ca4bf2c86f649261ebf59565dc8c622` and format 3.1.0.

The independent census reports `expr-projection` on the new computation
streams because their dependency closure includes generated projections. It
also reports `inductive-nested` on all three and
`inductive-recursive-indexed` on the indexed container. These are frozen census
classifications, not claims that Axeyum observed or accepted the streams.

## Frozen nested group inventories

Every source family has `numNested = 1`, one source constructor, two motives,
three minors, one main recursor, and one auxiliary recursor:

| Family | Source fields | Main rule fields | Auxiliary indices | Auxiliary rules |
|---|---:|---:|---:|---|
| `Rose` | 2 | `[2]` | 0 | `NestList.nil/cons [0,2]` |
| `IndexedRose` | 3 | `[3]` | 1 | `NestVec.nil/cons [0,3]` |
| `RepeatRose` | 3 | `[3]` | 0 | `NestList.nil/cons [0,2]` |

The repeated-container source proves structural reuse at the wire boundary:
two identical constructor-field applications still produce `numNested = 1`
and only `RepeatRose.rec_1`.

## Recursor array order is descriptive

Wire order is not uniform:

```text
Rose:        [Rose.rec_1, Rose.rec]
IndexedRose: [IndexedRose.rec_1, IndexedRose.rec]
RepeatRose:  [RepeatRose.rec, RepeatRose.rec_1]
```

M4 must therefore match recursors by independently generated checked name,
type, owned rules, and restored constructors. It may not infer main/auxiliary
identity from array position. The registration and mutation tests freeze all
three orders precisely without promoting any one order to semantics.

## Negative source

[`lean-v4.30-nested-inductive-negative.lean`](fixtures/lean-v4.30-nested-inductive-negative.lean)
is 260 bytes / 11 lines at SHA-256
`aedb42cf5d4b8eccb24252ffeaab33ce10cdd5a21bf1ad36290e1ab87387e398`.
Its `Box (BadNested -> α)` parameter contains both the new family and the
constructor-local `α`. Pinned Lean rejects line 8 twice at exit 1 with:

```text
(kernel) invalid nested inductive datatype
'AxeyumNestedInductiveNegative.Box', nested inductive datatypes parameters
cannot contain local variables.
```

Both runs took 150 ms; maximum RSS was 445,964 and 445,780 KiB. This freezes
the no-loose-bound-variable rule as a genuine kernel diagnostic rather than a
future Axeyum-invented policy.

## Frozen later gates

The registration binds before semantic implementation:

- 19 named native cases and 21 mutation families;
- a >=640-case two-run byte-identical generated grammar spanning outer and
  container group sizes, parameters, indices, repeated/distinct applications,
  nesting depths one and two, target families, `Type`/restricted `Prop`, and
  accepted/typed-reject classifications;
- the exact 720 mutual, 768 recursive, and 840 positivity populations;
- the existing nested misclassification and well-founded completed-import
  controls;
- completion-only publication and declaration-identity-v1;
- 15 stop conditions; and
- one-worker 3/4 GiB memory caps with 512 MiB swap and repository-local
  temporary directories.

## Fail-closed validation

[`check-lean-nested-inductive-elimination.py`](../../scripts/check-lean-nested-inductive-elimination.py)
recomputes both source hashes, the current baseline projection, all three
complete stream censuses, selected roots, target family metadata, `numNested`,
recursor order/types/rules, aggregate bounds, and mandatory control presence.
It also verifies the exact historical nested and current well-founded outcomes
in the construct-matrix registration. Any unregistered top-level field is a
premature product observation.

Thirteen tests cover source/diagnostic/status drift; stream hash/size/record/
root drift; family and `numNested` drift; recursor order/index/rule drift; pin,
resource, and command drift; semantic and claim drift; case/mutation uniqueness
and order; grammar/control/stop drift; baseline hashes/outcomes; future overlay
projection; and premature Axeyum results. The checker and tests are now part of
both `parity-docs` and the plain-shell aggregate gate.

## Next gate

M1 changes only importer preflight order. It must parse `numNested` and the
variable recursor population before applying singleton recursor-count policy,
then move the existing construct row from accidental
`Malformed(line=248, ...)` to the registered
`Unsupported(inductive-nested)` boundary. It must not admit any nested group,
run any new stream through the importer, publish `CompletedImport`, or change
the well-founded and 720/768/840 controls.
