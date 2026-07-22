# Official Lean construct matrix: current-product measurement

Status: M3 current-product outcomes frozen; no importer or kernel semantics
changed

Date: 2026-07-22

Parents:

- [execution plan](lean-official-construct-matrix-plan-2026-07-22.md);
- [M0 and Stage A source freeze](lean-official-construct-matrix-stage-a-2026-07-22.md);
- [Stage B wire freeze](lean-official-construct-matrix-stage-b-2026-07-22.md).

Registration:
[`lean-official-construct-matrix-v1.json`](lean-official-construct-matrix-v1.json)

Decision:
[proposed ADR-0351](../research/09-decisions/adr-0351-preregister-official-lean-construct-matrix.md)

## Outcome

The unmodified importer at Stage B revision
`22f51b4b0a94a1ae4d1c18b3f0dee6f56005edf4` was run twice on every new stream.
The immutable direct-recursive fixture was imported immediately before each of
the ten measurements. All ten controls independently admitted 11 declarations,
zero axioms, zero axiom identities, and 11 declaration identities. Every new
outcome repeated exactly.

No new row independently admits. Every failure returns `ImportError` and no
`CompletedImport`; the public owned-result API exposes no kernel or arena handle
on the error path. M3 made no Rust implementation change. Its only Rust addition
is an integration test that freezes the observed boundary.

## Exact typed outcomes

| Case | First typed outcome | Layer | Repeat | Published environment |
|---|---|---|---:|---|
| `recursive-indexed` | line 148, `ImportError::Kernel`, declaration `AxeyumConstructMatrix.MiniVector`, `KernelError::RecursiveIndexedNotSupported` | translated declaration reached trusted kernel | 2/2 exact | none |
| `reflexive-higher-order` | line 117, `ImportError::Unsupported { code: "inductive-reflexive" }` | importer policy | 2/2 exact | none |
| `mutual` | line 233, `ImportError::Unsupported { code: "inductive-mutual" }` | importer policy | 2/2 exact | none |
| `nested` | line 248, `ImportError::Malformed { message: "single-family inductive must export one recursor" }` | format misclassification | 2/2 exact | none |
| `well-founded` | line 208, `ImportError::Unsupported { code: "inductive-reflexive" }` | importer policy in dependency closure | 2/2 exact | none |

The exact line and payload fields are part of the machine-readable registration
and the Rust test. Internal arena IDs in the recursive-indexed kernel error are
not treated as stable public identity; the line, rendered declaration, and
typed kernel variant are.

## What the outcomes mean

### Recursive-indexed reaches the intended kernel boundary

The reader accepts the official format record and translates `MiniVector` far
enough to call the trusted kernel. The kernel then declines the recursive field
whose family application changes the index. This is a
`translated-kernel-declined` result, not an importer-parser limitation and not
independent admission.

### Reflexive and mutual stop at explicit policy boundaries

`MiniAcc` stops on the export's `isReflexive=true` metadata before kernel
admission. The two-family tree stops because the importer accepts only one type
per inductive group. Both are stable unsupported-feature classifications with
no partial publication.

### Nested reveals a classification defect

The official `Rose` group is valid and independently inventoried. It is one
type with `numNested=1` and two official recursors. The importer checks
`recs.len() == 1` before inspecting `numNested`, so it labels this valid,
unsupported form `Malformed` rather than returning `inductive-nested`.

This does not create a soundness hole because the stream is rejected
transactionally. It is still a real compatibility and diagnostics defect: a
producer-format error and an unsupported official construct are materially
different. The generated matrix must preserve the observed misclassification;
any later correction belongs to a separately reviewed implementation change.

### Well-founded does not reach the selected root

The well-founded theorem's stream first encounters official `Acc`, which is
recursive-indexed and reflexive. The importer declines at that dependency on
line 208, before translating `wellFoundedLoop` or
`wellFoundedWitness`. Therefore this row measures a dependency-closure blocker,
not native or imported well-founded-definition support.

## Executable product contract

[`official_construct_matrix.rs`](../../crates/axeyum-lean-import/tests/official_construct_matrix.rs)
runs the full case population twice. Before every decline it requires the exact
direct-recursive report. It then matches the concrete `ImportError` variant,
line, code/message or declaration, and kernel variant. An unexpected admission
is an immediate test failure.

The product freezer binds those outcomes to the Stage B revision and the
4 GiB/two-job resource policy. The validator requires:

- two repeatable runs per case and ten passing controls;
- exact typed outcome payloads and stable case links;
- `completed_import_published=false` for every decline;
- no missing, reordered, or invented product row;
- the unchanged Stage A sources and Stage B wire inventories beneath the
  product layer.

## Next gate

M4 now generates the public assurance matrix from the registration. It must
keep official acceptance/export, independent Python inventory, Rust policy or
kernel decline, admission, and computation in separate columns. In particular:

- recursive-indexed may receive translated-kernel-declined credit only;
- reflexive and mutual may receive parsed/policy-declined credit only;
- nested must expose its format misclassification and receive no fabricated
  unsupported-code or admission credit;
- well-founded must say its dependency closure stopped at `Acc` before the
  selected root;
- the official non-positive source remains source-rejected with no stream;
- the direct-recursive control remains the only independently admitted matrix
  row at this checkpoint.

ADR-0351 remains proposed until that generator rejects impossible assurance
promotions and the final M5 synchronization/gates pass.
