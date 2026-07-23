# Lean U2 normalization-contract authority

> **Generated; do not edit by hand.** Regenerate with `python3 scripts/lean_u2_normalization_contracts.py`; validate with `--check`.

> **Status: bounded contract/projection evidence only.** Raw extractors, semantic canonicalizers, official/native outcomes, paired cells, and parity credit remain zero.

Pinned target: Lean `4.30.0` at `d024af099ca4bf2c86f649261ebf59565dc8c622`.

| Normalization | Layer | Axes | Compared fields | Ignored rules | Contract seal |
|---|---|---|---:|---:|---|
| `lean-process-harness-v1` | `process-harness` | `A0`, `A11` | 7 | 2 | `7a56e25572978ba99aef83ce0363223b22284bc72bb010c04aa48398258b6991` |
| `lean-parser-macro-v1` | `parser-macro` | `A3` | 5 | 2 | `587d9655fdb33f3f5a5268c5a218c63403226828470e3a6be3a3a99fbe88c8d4` |
| `lean-elaboration-v1` | `elaboration` | `A4` | 6 | 2 | `99749be8499f72bd75f8c3f343d6019a20bb3e8527a1a344db8293ac0552a363` |
| `lean-kernel-assurance-v1` | `kernel-assurance` | `A1`, `A9` | 8 | 2 | `d17a5465f91014449aa614f5f57fac9f532f50622f7ffd76aa6c26f236506843` |
| `lean-module-cache-v1` | `module-cache` | `A2`, `A6`, `A9` | 7 | 2 | `408cc2e50a7001b84f6bc9ad5baa536b2f9b168d61338cf4897f998ca5f360a1` |
| `lean-tactic-v1` | `tactic` | `A5` | 6 | 2 | `40b310b09a9049ec4e7cfed3dbf2bed05cb09f4a6462ada0e1c8b50635268951` |
| `lean-compiler-runtime-v1` | `compiler-runtime` | `A8` | 10 | 2 | `00e0c92a6990db56e66cce4bc4f304d4e4039c04f2c257ff03d98637eae70cf2` |
| `lean-server-rpc-v1` | `server-rpc` | `A7` | 9 | 2 | `ca6a498ae9146c09f436f5d10584d507f3ea4e879a15e68912c078b91644fd72` |
| `lean-lake-project-v1` | `lake-project` | `A6`, `A11` | 10 | 2 | `2701dc0f099888c31bdf088a0bc49d748107f33b74847bd21bf0a19c6a79ae3e` |

Totals: **9 contracts**, **68 compared fields**, and **18 explicit ignored-field rules**.

The projection kernel rejects missing or unknown fields, floating-point values, unregistered normalizers, cross-layer reuse, and stale contract seals. The only ignored fields are `collector_sequence` and `evidence_storage_path`; their reasons are sealed per contract. Array order remains semantic.

This authority does not establish that raw Lean or Axeyum artifacts can yet be transformed into these fields. That layer-specific extraction and semantic canonicalization remains open TL0.6.5 M1 work after the required parents and M0 obligation authority exist.
