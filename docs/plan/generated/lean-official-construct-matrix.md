# Official Lean construct matrix

Generated from [`lean-official-construct-matrix-v1.json`](../lean-official-construct-matrix-v1.json).
Do not edit by hand; regenerate with
`python3 scripts/check-lean-official-construct-matrix.py --write`.

This selected-family matrix separates official source/export evidence, independent Python
wire inventory, current Rust outcomes, independent admission, and computation. It is not
full Lean kernel, frontend, ecosystem, or mathlib compatibility.

## Summary

- rows: 7; official accepted: 6; official rejected: 1;
- independently admitted: 1; computation-checked in this matrix: 0;
- current transactional declines: 5, including one valid-wire format misclassification;
- assurance classes: `independently-admitted`=1, `official-export-inventory-only`=1, `official-source-rejected`=1, `parsed-declined`=3, `translated-kernel-declined`=1.

## Matrix

| Case | Source family | Official source | Selected root | Exact stream / independent wire inventory | Current Rust outcome | Independent admission | Computation | Assurance class | Exact boundary |
|---|---|---|---|---|---|---|---|---|---|
| `direct-recursive-control` | direct-recursive-non-indexed | accepted | `AxeyumImportShapes` | [fixture](../fixtures/lean4export-v4.30-recursive-shapes.ndjson); N/L/E/D=30/4/130/5; direct recursive, non-indexed | CompletedImport: 11 declarations, 0 axioms | yes | not checked in this matrix | `independently-admitted` | exact fixture only; no computation or ecosystem credit |
| `recursive-indexed` | recursive-indexed | accepted | `AxeyumConstructMatrix.recursiveIndexedWitness` | [fixture](../fixtures/lean4export-v4.30-construct-matrix-recursive-indexed.ndjson); N/L/E/D=34/4/132/4; inductive-recursive-indexed | Kernel line 148: RecursiveIndexedNotSupported at AxeyumConstructMatrix.MiniVector | no | not reached | `translated-kernel-declined` | stable transactional decline; no completed environment |
| `reflexive-higher-order` | reflexive-higher-order | accepted | `AxeyumConstructMatrix.reflexiveWitness` | [fixture](../fixtures/lean4export-v4.30-construct-matrix-reflexive-higher-order.ndjson); N/L/E/D=47/3/139/6; inductive-recursive-indexed, inductive-reflexive | Unsupported line 117: inductive-reflexive | no | not reached | `parsed-declined` | stable transactional decline; no completed environment |
| `mutual` | mutual | accepted | `AxeyumConstructMatrix.mutualWitness` | [fixture](../fixtures/lean4export-v4.30-construct-matrix-mutual.ndjson); N/L/E/D=75/4/305/10; inductive-mutual | Unsupported line 233: inductive-mutual | no | not reached | `parsed-declined` | stable transactional decline; no completed environment |
| `nested` | nested | accepted | `AxeyumConstructMatrix.nestedWitness` | [fixture](../fixtures/lean4export-v4.30-construct-matrix-nested.ndjson); N/L/E/D=70/6/322/10; inductive-nested | Malformed line 248: single-family inductive must export one recursor | no | not reached | `official-export-inventory-only` | valid official nested group is misclassified as malformed |
| `well-founded` | well-founded | accepted | `AxeyumConstructMatrix.wellFoundedWitness` | [fixture](../fixtures/lean4export-v4.30-construct-matrix-well-founded.ndjson); N/L/E/D=160/5/731/23; inductive-recursive-indexed, inductive-reflexive | Unsupported line 208: inductive-reflexive | no | not reached | `parsed-declined` | declines on Acc dependency before selected root |
| `non-positive-source-negative` | non-positive-inductive | rejected | — | not applicable | not run: official source rejected | no | not applicable | `official-source-rejected` | official kernel strict-positivity rejection; no NDJSON assigned |

## Interpretation

- `independently-admitted` means the exact official stream produced a completed owned
  environment through Axeyum's trusted gate. It does not imply a checked computation.
- `translated-kernel-declined` means an official declaration reached the independent
  kernel and received a typed rejection.
- `parsed-declined` means importer policy recognized and transactionally declined the
  official construct before independent admission.
- `official-export-inventory-only` grants official bytes and independent Python wire
  inventory only. Here it preserves the nested row's current malformed/unsupported
  classification defect rather than laundering it into parser or kernel credit.
- `official-source-rejected` has no export by construction.

The well-founded row stops at the reflexive, recursive-indexed `Acc` dependency before
its selected definition/theorem root. The row therefore provides no well-founded-root
translation or admission credit.
