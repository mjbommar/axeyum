# Lean U2 official-test registration authority

> **Generated; do not edit by hand.** Regenerate with `python3 scripts/gen-lean-u2-test-authority.py`; validate with `--check`.

> **Verdict: registration bounded; complete U2 parity authority not established.** No official execution, Axeyum execution, or paired-result credit is recorded here.

Pinned Lean `v4.30.0` at `d024af099ca4bf2c86f649261ebf59565dc8c622`. The capture runs Lean's CMake test registration and reads CTest JSON v1; it does not count raw files as tests.

## Registered profiles

| Profile | `LAKE_CI` | Registered cases | Registration digest |
|---|---:|---:|---|
| `default` | `OFF` | 3,678 | `a93e4fdea36da4cd4667ff07c18583106065a8f120eff3ff560a01a7c54c3463` |
| `full-lake` | `ON` | 3,723 | `043b9d2ca765bb63553b083843829a5660a32877a0c8b1a37685d8f6fedbd03b` |

The default selection is a strict subset of the full-Lake selection: 0 default-only and 45 full-Lake-only cases.

## Selection composition

| Kind | Cases |
|---|---:|
| `directory` | 31 |
| `lake-directory` | 52 |
| `lint` | 1 |
| `pile` | 3,639 |

| Output contract | Cases |
|---|---:|
| `empty` | 2,099 |
| `exact` | 1,480 |
| `ignored` | 60 |
| `script-defined` | 84 |

| Family | Cases |
|---|---:|
| `bench` | 1 |
| `compile` | 60 |
| `compile_bench` | 24 |
| `doc-examples` | 8 |
| `docparse` | 197 |
| `elab` | 2,854 |
| `elab_bench` | 40 |
| `elab_fail` | 316 |
| `lake` | 52 |
| `lint` | 1 |
| `misc` | 5 |
| `misc_dir` | 2 |
| `pkg` | 27 |
| `server` | 4 |
| `server_interactive` | 132 |

## Content and derivation closure

- 3,723 full-Lake case records, digest `37050cfb25f0ecfa2256ccb9516124092fc611af5d7be94cce1e9e0745745cd3`.
- 7,004 Git-tracked support files across 94 over-approximating per-case support subtrees, digest `f2c8b9c9276ac85dfef7d8e4fc32abe2350a3ae9e659a9a5795cba7f0390631f`.
- Pile selection closes exactly: 3,660 glob candidates = 3,639 registered + 21 excluded.
- Every case retains its normalized command and CTest properties, primary content digest, sidecar paths, output policy, support scope, profile membership, and case digest in the [machine-readable authority](../lean-u2-test-authority-v1.json).
- Upstream CI and preset sources are content-bound, but their platform filters, sharding, retries, and resource envelopes remain deliberately unpromoted pending a separate executable profile derivation.

## Why U2 remains incomplete

- Derive every official CI platform, build preset, CTEST_OPTIONS filter, shard, retry, resource, and completion identity.
- Execute and retain official Lean outcomes for the complete declared profile matrix.
- Implement native Axeyum source/workflow/runtime surfaces and retain matched per-case outcomes.
- Register U2 terminal paired cells only after both executions use the same normalized case identity.

This is therefore a reproducible selection denominator for two bounded registration profiles, not evidence that Lean ran them successfully and not evidence that Axeyum can run or match them.
