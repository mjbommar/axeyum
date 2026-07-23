# Lean U2 TL0.6.4 M2.1 pre-execution result — exact header pass ready, not run

Status: **implementation accepted; attempt 001 awaits explicit authorization**

Date: 2026-07-23

Target: Lean `v4.30.0` at
`d024af099ca4bf2c86f649261ebf59565dc8c622`.

Parents:
[M2.1 source-first plan](lean-u2-native-dependency-tl0.6.4-m2.1-plan-2026-07-23.md),
[M2.1 input/control authority](lean-u2-native-header-contract-m2.1-v1.json),
and [accepted M2.0 result](lean-u2-native-surface-classification-tl0.6.4-m2.0-result-2026-07-23.md).

## 1. Verdict

The M2.1 input, control, process, evidence, and offline-normalization
implementation is accepted for execution readiness. It freezes all 4,092
M1-bound tracked Lean sources, 32 deterministic fast-parser batches, 14 exact
controls, four provider/preflight processes, 35 parser processes, immutable
completion-last evidence, one-process concurrency, and zero retries.

Attempt 001 has not run. Its evidence root
`docs/plan/evidence/lean-u2-native-header-m2.1-attempt-001/` is absent. No
corpus or control path has been passed to Lean under M2.1; there are zero
observed processes, header edges, resolved nodes/edges, native outcomes,
pairs, or parity credit. The terminal scoreboard remains disabled.

## 2. Source-first checkpoint sequence

The exact pushed sequence is:

1. `593896a3` preregistered all process, input, control, evidence, comparison,
   mutation, acceptance, stop, and non-credit rules.
2. `2844802f` implemented the complete offline input/batch/control contract,
   full-parser helper, and pre-authority tests. The helper compiled and returned
   an empty result on empty stdin; no corpus/control source was supplied.
3. `ed174b09` published the 4,092-row canonical input/control authority only
   after its pre-authority tests passed.
4. `e4995ccb` implemented the content-authorized, resource-limited,
   completion-last 39-process runner, evidence verifier, fast/full JSON
   normalizers, and additional offline tests without invoking `run`.
5. `86955d44` made the pre-execution contract a required local/CI parity gate
   and added its zero-process snapshot to the terminal registry.

Every checkpoint was pushed with local HEAD equal to its tracking ref. No
commit grants permission to execute attempt 001 implicitly.

## 3. Frozen execution shape

| Dimension | Frozen value |
|---|---:|
| corpus Lean files | 4,092 |
| corpus bytes | 9,697,571 |
| fast-parser corpus batches | 32 |
| exact controls | 14 |
| provider/preflight processes | 4 |
| parser processes | 35 |
| all planned processes | 39 |
| process concurrency | 1 |
| retries | 0 |
| observed processes | 0 |
| declared header edges | 0 |
| resolved nodes / edges | 0 / 0 |
| native outcomes / pairs / parity credit | 0 / 0 / 0 |

The process sequence is immutable: source HEAD, source cleanliness, ELF
dependencies, released-binary version, 32 `--deps-json` corpus batches, one
fast control batch, one all-corpus full-parser comparison, and one full control
comparison. The child environment is an exact `LANG=C`/`LC_ALL=C` allowlist;
the binary and helper paths are absolute. Each child has registered address,
CPU, wall, stdout, stderr, and file-size ceilings.

## 4. Evidence behavior

The runner refuses to start when the contract, parents, executable, helper,
Git/readelf tools, toolchain libraries, platform, source root, authorization,
or evidence-root absence differs. Each process retains exact command, cwd,
environment, stdin, limits, termination, raw streams, resource counters, and a
sealed record. The runner stops on the first failure without retry and writes
`completion.json` last only after all 39 processes finish.

The offline verifier rejects absent completion, process/order/specification
drift, changed raw streams, nonzero exits, timeouts, stderr, dirty checkout,
wrong source commit, wrong Lean version, ELF dependency drift, control-byte
drift, authorization drift, inventory drift, and any post-completion file
change. Parser normalization separately rejects malformed JSON, row-count or
schema drift, mixed success/error rows, dropped/reordered/merged imports, and
fast/full import or module-mode disagreement.

Successful process completion will still be only unvalidated raw parser
evidence. Header edges and the M2.1 authority must be built in a separate
offline promotion checkpoint after evidence validation.

## 5. Retained identities

| Artifact | Bytes | SHA-256 |
|---|---:|---|
| M2.1 plan | — | `7daa62ae0342c8fa64872604f880343fe9498866676675b61e911d034e3b999f` |
| input/control authority | 2,340,134 | `8447cf92349467962363baea30973f0cb4b0d95c1527b6544fd50e4e09100b5b` |
| generated JSON | 2,191 | `c846ed53e69fdd3ed44f8652fa9fee5df4df40269abf82caedaeb9f78f53b62d` |
| generated Markdown | 1,140 | `dfe6fcf334dfde2d782be432a0cde86798e5f6120394b2c4de208ba582bb0053` |
| runner/validator | 56,582 | `516581394f7026f99b56d9ed99c0049e9235b15b138b0f3df80cba68709ce26c` |
| full-parser helper | 1,415 | `12812e7956e5f6c5914247e7523b32559328febbeb319083652c458b3b9e4af2` |
| focused tests | 11,457 | `21c2cdf54ac11485717dd4a8485efe716e861588443e403188d310d5a359af96` |

Canonical contract seals:

- record: `f0c8f7a0725c78d5659eda52c1bee29ae08548a9e1bfe8043a369ca772381466`;
- corpus rows: `836be334f3c4d49fa4f41f704e74fce2573f6ff04e6b44360e9c8a9bc1a7c485`;
- batches: `3bb22a75d46d1b37c3d06a086079b06dd1153f451ad6fc9a1e8cb437df3588bc`;
  and
- controls: `a651a7d10f29c1e5bc6c5e71a6b7124d865edeaa6cf78ea31598072942f3c51d`.

The current exact authorization digest is:

`17be82707d73b6e4d139c19c6f4e7c5e0cf7cdcaf694ab92d4e47de88bf5c8d6`

It binds the contract's physical/logical identities, current runner/helper
bytes, source/evidence roots, complete process-specification digest, process
count, and zero-retry policy. Any runner/helper change invalidates it.

## 6. Validation

Accepted task-owned gates include:

- 11 focused input, batch, control, authority, mutation, process-program, and
  parser-normalization tests;
- deterministic contract and generated-report checking;
- provider-file revalidation and non-executing run-command rendering;
- nine complete-parity registry/mutation tests;
- terminal regeneration at 0/10 complete populations, 0/12 complete axes,
  zero pairs, zero satisfied gates, and `terminal_ready=false`;
- parity-prose and documentation-link checks; and
- Python compilation, shell syntax, and whitespace checks.

The pre-execution authority is required by `just parity-docs`,
`scripts/check.sh`, `.github/workflows/docs-ci.yml`, and
`.github/workflows/ci.yml`. Those gates validate zero-process readiness; they
do not execute attempt 001.

## 7. Exact authorization boundary

The only preregistered attempt command is:

```sh
python3 scripts/lean_u2_native_dependency_m2_1.py run \
  --authorization 17be82707d73b6e4d139c19c6f4e7c5e0cf7cdcaf694ab92d4e47de88bf5c8d6
```

It must not run until the user explicitly authorizes this exact command after
the implementation checkpoint. Authorization permits only the registered
39-process attempt and does not permit retries, diagnostics, changed limits,
or M2.2 execution.

## 8. Nonclaims and handoff

This checkpoint claims neither direct header evidence nor parser agreement.
It does not resolve module names, source/`.olean` paths, transitive imports,
generated wrappers, Lake state, runtime behavior, FFI, requests, native
support, official-provider completion, pairs, or parity.

After explicit authorization, run attempt 001 once. If it completes, validate
the immutable evidence before any interpretation. Only then may an offline
authority map exact fast/full rows to `declared-static` `header-import` edges.
M2.2-M2.7 and M3 remain mandatory regardless of M2.1's eventual outcome.
