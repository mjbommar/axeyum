# Lean U2 official CI execution profiles

> **Generated; do not edit by hand.** Regenerate with `python3 scripts/gen-lean-u2-official-ci-profiles.py`; validate with `--check`.

> **Verdict: official CI profiles derived; no execution or parity outcome established.** Every attempt below remains `not-run`.

Pinned Lean `v4.30.0` at `d024af099ca4bf2c86f649261ebf59565dc8c622`. The authority evaluates only the isolated matrix-construction fragment and maps its CTest options onto the TL0.6.1 registered names.

## Derivation closure

- 17 official-repository event contexts.
- 9 active matrix job literals and 153 candidate context/job cells.
- Cell states: `ctest`=85, `disabled`=53, `packaging-only`=15.
- 111 CTest attempts: `primary`=85, `rebootstrap`=26.
- 8 unique factored case-selection sets.
- Equal bootstrap flag inputs select `stage1`.
- Commented Linux LLVM, Linux 32-bit, and WebAssembly jobs receive no active-cell or attempt credit.

## Context matrix

`Selected occurrences` intentionally counts repeated attempts; it is not a unique-case denominator or pass count.

| Context | Event | Level | Lake | Fast | Enabled jobs | Primary | Secondary | Packaging only | CTest attempts | Selected occurrences |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `pr-l0` | `pull_request` | 0 | no | no | 4 | 1 | 3 | 2 | 2 | 7,356 |
| `pr-l0-fast` | `pull_request` | 0 | no | yes | 4 | 1 | 3 | 2 | 2 | 7,356 |
| `pr-l0-lake` | `pull_request` | 0 | yes | no | 4 | 1 | 3 | 2 | 2 | 7,446 |
| `pr-l0-lake-fast` | `pull_request` | 0 | yes | yes | 4 | 1 | 3 | 2 | 2 | 7,446 |
| `pr-l1` | `pull_request` | 1 | no | no | 4 | 3 | 1 | 0 | 6 | 22,068 |
| `pr-l1-fast` | `pull_request` | 1 | no | yes | 4 | 3 | 1 | 0 | 6 | 22,068 |
| `pr-l1-lake` | `pull_request` | 1 | yes | no | 4 | 3 | 1 | 0 | 6 | 22,338 |
| `pr-l1-lake-fast` | `pull_request` | 1 | yes | yes | 4 | 3 | 1 | 0 | 6 | 22,338 |
| `pr-l3` | `pull_request` | 3 | no | no | 9 | 8 | 1 | 1 | 10 | 36,578 |
| `pr-l3-fast` | `pull_request` | 3 | no | yes | 9 | 8 | 1 | 1 | 10 | 36,578 |
| `pr-l3-lake` | `pull_request` | 3 | yes | no | 9 | 8 | 1 | 1 | 10 | 36,983 |
| `pr-l3-lake-fast` | `pull_request` | 3 | yes | yes | 9 | 8 | 1 | 1 | 10 | 36,983 |
| `merge-group-l1` | `merge_group` | 1 | no | no | 2 | 1 | 1 | 0 | 4 | 14,712 |
| `push-master-l1` | `push` | 1 | no | no | 3 | 2 | 1 | 0 | 5 | 18,390 |
| `nightly-l2` | `schedule` | 2 | no | no | 9 | 7 | 2 | 1 | 10 | 36,578 |
| `manual-nightly-l2` | `workflow_dispatch` | 2 | no | no | 9 | 7 | 2 | 1 | 10 | 36,578 |
| `release-tag-l3` | `push-tag-v4.30.0` | 3 | no | no | 9 | 8 | 1 | 1 | 10 | 36,578 |

## Exact selection sets

| Selection | Registration | Include | Exclude | Registered | Selected | Excluded | Selected digest |
|---|---|---|---|---:|---:|---:|---|
| `default-all` | `default` | `-` | `-` | 3,678 | 3,678 | 0 | `6f5d4dadd9bc51b42521fd6bb07e6fd270f4b638a08156c28cfa6cf7a998a488` |
| `default-filtered-aec7358564e4` | `default` | `-` | `foreign` | 3,678 | 3,678 | 0 | `6f5d4dadd9bc51b42521fd6bb07e6fd270f4b638a08156c28cfa6cf7a998a488` |
| `default-filtered-bfb0a7b69c6e` | `default` | `-` | `elab_bench/big_do` | 3,678 | 3,677 | 1 | `cd78d60a181a643ff844c6bd29a09d71be50741c7347aaa40490a8a73150f56a` |
| `default-filtered-d1bb9722e72c` | `default` | `-` | `StackOverflow|reverse-ffi|interactive|async_select_channel|9366|run/bv_|grind_guide|grind_bitvec2|grind_constProp|grind_indexmap|grind_list|grind_lint|grind_array_attach|grind_ite_trace|pkg/|lake/` | 3,678 | 3,477 | 201 | `9edadfadaf699fbbc624dbea40c9c66953b6928d347f343bb197019582bd356e` |
| `full-lake-all` | `full-lake` | `-` | `-` | 3,723 | 3,723 | 0 | `7c49a81ac4e3a5e791515b62a798745f082a9325e40e7f49390b6d66c493e6cd` |
| `full-lake-filtered-6325d6cffd5d` | `full-lake` | `-` | `foreign` | 3,723 | 3,723 | 0 | `7c49a81ac4e3a5e791515b62a798745f082a9325e40e7f49390b6d66c493e6cd` |
| `full-lake-filtered-cbb2894dd43f` | `full-lake` | `-` | `elab_bench/big_do` | 3,723 | 3,722 | 1 | `bc35ab1c1ee29ede3bd33cc90c09ab8f573747720f457b6cefb364db0c6ac419` |
| `full-lake-filtered-d803b176baa6` | `full-lake` | `-` | `StackOverflow|reverse-ffi|interactive|async_select_channel|9366|run/bv_|grind_guide|grind_bitvec2|grind_constProp|grind_indexmap|grind_list|grind_lint|grind_array_attach|grind_ite_trace|pkg/|lake/` | 3,723 | 3,477 | 246 | `9edadfadaf699fbbc624dbea40c9c66953b6928d347f343bb197019582bd356e` |

## Assurance boundary

- The machine-readable authority retains every resolved cell, normalized command, selection-set membership, stage, preset, primary/secondary classification, and non-CTest action flag.
- Primary attempts retain matrix filters and JUnit shape. Rebootstrap attempts are separate, fixed to stage 1, and deliberately unfiltered.
- Disabled and packaging-only cells own no CTest attempt.
- Stage-3 and benchmark actions remain flags, not invented CTest cases.
- Official executions, completed cases, Axeyum executions, and paired cells all remain zero.

## Remaining work

- Retain official executable, configuration, environment, resource, attempt, completion, JUnit, log, and artifact identities for every declared execution profile.
- Classify and implement the native Axeyum surface required by every selected case.
- Execute matched native cases and register terminal paired cells only from completed both-system evidence.
