# Lean U2 normalization-contract authority

> **Generated; do not edit by hand.** Regenerate with `python3 scripts/lean_u2_normalization_contracts.py`; validate with `--check`.

> **Status: bounded contract/projection evidence only.** Raw extractors, semantic canonicalizers, official/native outcomes, paired cells, and parity credit remain zero.

Pinned target: Lean `4.30.0` at `d024af099ca4bf2c86f649261ebf59565dc8c622`.

| Normalization | Layer | Axes | Compared fields | Ignored rules | Contract seal |
|---|---|---|---:|---:|---|
| `lean-process-harness-v2` | `process-harness` | `A0`, `A11` | 7 | 2 | `7947a4dd5d159d6bf78dc64c496c98ef5dcaa22a181c7ad3e28e1edbfb403251` |
| `lean-parser-macro-v2` | `parser-macro` | `A3` | 5 | 2 | `903c1d31ea930579285fa91fe71764e731cfb56af4a557841706cde54400d5b4` |
| `lean-elaboration-v2` | `elaboration` | `A4` | 6 | 2 | `7c58e3234a5649ac573c25c317a8b950043370b69dd6dabeafb992bae30436cb` |
| `lean-kernel-assurance-v2` | `kernel-assurance` | `A1`, `A9` | 8 | 2 | `7fe91be6487edcb06dab219aea358e6b35ff70c0615ff0f71844210299e73141` |
| `lean-module-cache-v2` | `module-cache` | `A2`, `A6`, `A9` | 7 | 2 | `b8a79087ef7ec662945060b41fac351fdb98b3cfe80b9ec87667c9622438bf37` |
| `lean-tactic-v2` | `tactic` | `A5` | 6 | 2 | `eca4af9cbc1292b78de84c68c330c91a25458a4df7ea52748ac11c46248a5af6` |
| `lean-compiler-runtime-v2` | `compiler-runtime` | `A8` | 10 | 2 | `55e7234292502f47b3873827fd39b928c001ee8bcc42e7e45a2bfbf455cd2cda` |
| `lean-server-rpc-v2` | `server-rpc` | `A7` | 9 | 2 | `d9d8d3229b83c9d8d326fa4ce780d532def624d09c43405aed09806076269708` |
| `lean-lake-project-v2` | `lake-project` | `A6`, `A11` | 10 | 2 | `10a823912904acce00afbea29956f6b59486cc4b64caee5e0c12aa1b8749151f` |

Totals: **9 contracts**, **68 compared fields**, and **18 explicit ignored-field rules**, for **86 typed field occurrences**. The sealed kinds are **65 SHA-256**, **3 enum**, **9 nonnegative-integer**, and **9 nonempty-string**.

The projection kernel validates each typed value before projection and rejects missing or unknown fields, malformed digests, values outside a registered enum, negative or Boolean collector sequences, empty storage paths, unregistered normalizers, cross-layer reuse, and stale contract seals. No field schema admits an array or object. The only ignored fields are `collector_sequence` and `evidence_storage_path`; their types and reasons are sealed per contract.

This authority does not establish that raw Lean or Axeyum artifacts can yet be transformed into these fields. That layer-specific extraction and semantic canonicalization remains open TL0.6.5 M1 work after the required parents and M0 obligation authority exist.
