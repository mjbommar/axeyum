# Lean U2 normalization-contract authority

> **Generated; do not edit by hand.** Regenerate with `python3 scripts/lean_u2_normalization_contracts.py`; validate with `--check`.

> **Status: bounded contract/projection evidence only.** Raw extractors, semantic canonicalizers, official/native outcomes, paired cells, and parity credit remain zero.

Pinned target: Lean `4.30.0` at `d024af099ca4bf2c86f649261ebf59565dc8c622`.

| Normalization | Layer | Axes | Compared fields | Ignored rules | Contract seal |
|---|---|---|---:|---:|---|
| `lean-process-harness-v3` | `process-harness` | `A0`, `A11` | 7 | 2 | `ab7c0b5719539e643d17deeeaa251cc1875a4830aefded0dbdb8575ce3fa55ca` |
| `lean-parser-macro-v3` | `parser-macro` | `A3` | 5 | 2 | `25179fa04e777292e9bb097d588395e9b1db2fded2f74edef577248e2f366d3d` |
| `lean-elaboration-v3` | `elaboration` | `A4` | 6 | 2 | `6bbc49da727771485cff7798c830a3b86d2b47d290d1d527fcc8f500f5d2d2a0` |
| `lean-kernel-assurance-v3` | `kernel-assurance` | `A1`, `A9` | 8 | 2 | `41c66452e20a24e54c00ed21bd70cd29451434e04bd707dd4f64b2dcbf8fe924` |
| `lean-module-cache-v3` | `module-cache` | `A2`, `A6`, `A9` | 7 | 2 | `0f6a6376ea5fbcdcb26cd619c2e9e93afce51829d7d9e498cbb39df487d3e118` |
| `lean-tactic-v3` | `tactic` | `A5` | 6 | 2 | `a20de203cc23708cb88592beaba010af140cf4296e75ed40e05a779aa0c17646` |
| `lean-compiler-runtime-v3` | `compiler-runtime` | `A8` | 10 | 2 | `61d8e793eb058fd5df8a4b8a4d9840a4b768c556d418536278e06631af578c53` |
| `lean-server-rpc-v3` | `server-rpc` | `A7` | 9 | 2 | `4984a10db48ef2964c9652cf3c7754c14f684afc41817dfeb3e2e925405ab851` |
| `lean-lake-project-v3` | `lake-project` | `A6`, `A11` | 10 | 2 | `a39fde68f9a23c59bc0abfeea3a9a606c84300c7093d7878418487ce6080a0ed` |
| `lean-mathlib-ecosystem-v3` | `mathlib-ecosystem` | `A10` | 8 | 2 | `ed7264b5fad04a5ce302d0d8b9be2d5c3e2995677764b78c4d7744c8c91153c4` |

Totals: **10 contracts**, **76 compared fields**, and **20 explicit ignored-field rules**, for **96 typed field occurrences**. The registry covers **12 axes** through **15 contract/axis occurrences**. The sealed kinds are **73 SHA-256**, **3 enum**, **10 nonnegative-integer**, and **10 nonempty-string**.

The projection kernel validates each typed value before projection and rejects missing or unknown fields, malformed digests, values outside a registered enum, negative or Boolean collector sequences, empty storage paths, unregistered normalizers, cross-layer reuse, and stale contract seals. No field schema admits an array or object. The only ignored fields are `collector_sequence` and `evidence_storage_path`; their types and reasons are sealed per contract.

This authority does not establish that raw Lean or Axeyum artifacts can yet be transformed into these fields. That layer-specific extraction and semantic canonicalization remains open TL0.6.5 M1 work after the required parents and M0 obligation authority exist.
