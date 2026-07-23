# Lean U2 TL0.6.3 M2 R1 result — retained invalid artifact closure

Status: **one process attempt consumed; exact terminal/JUnit/case evidence
retained; artifact closure invalid; zero M2 case or shard credit**

Date: 2026-07-22

Authority:
[`lean-u2-official-execution-tl0.6.3-m2-r1-result-v1.json`](lean-u2-official-execution-tl0.6.3-m2-r1-result-v1.json)

## 1. Bounded verdict

The single R1 invocation at pushed revision
`591087667864e9c39519dafad2c2e9086ff6d973` passed the corrected source
preflight, constructed and discovered the exact 64-case harness, installed
prelaunch evidence, and launched CTest once. CTest exited `8` after 50,775 ms,
with its direct child reaped and no live process-group member. Its exact JUnit
contains all 64 selected cases once: 30 passed and 34 failed.

The runner then rejected post-run evidence closure before `post.json`,
`projection.json`, or `completion.json`:

```text
LEAN_U2_M2_RUN_ERROR|passed case lacks declared artifacts: docparse/arg_0006.txt
```

The parent plan requires completion-last closure before any case outcome can
receive credit. Attempt 001 is therefore invalid/incomplete and contributes
zero M2 official cases, outcomes, passes, failures, or shard completion. The
64 JUnit rows and 64 installed case records remain diagnostic observations,
not credited outcomes.

## 2. Exact retained evidence

| Field | Value |
|---|---|
| implementation revision | `591087667864e9c39519dafad2c2e9086ff6d973` |
| M2 attempt / sequence | `attempt-001` / 1 |
| retained root | `docs/plan/evidence/lean-u2-official-execution-tl0.6.3-m2-shard-0001` |
| retained state | 83 read-only files / 5,148,026 bytes |
| evidence manifest | domain `axeyum-lean-u2-official-execution-m2-r1-incomplete-evidence-v1`; `8692f3184dba764e0904f1db2d2283a56a71cccced0c371ddd634807cc0b2961` |
| prelaunch record | `b1a431a1f2dfbdc38c7e623f705f0de52230d666962e65b0e92037e979e8b2d6` |
| terminal record | `a4152e8ef82c2b5fe7388b5f661f655095696ea3a60fb5b5c03defadc70a0798` |
| JUnit record | `5ffa07e7b51f331a4941384b0a479df917bb8ee1efbe2ab90e14e6ea9ab6e51f` |
| case records | 64; ordered identity digest `957afcec757607808bd32748c36d4378a341bc2eebf08043a05c75cbb0b1304d` |
| completion | absent |

The orchestration authority embeds the exact 0-byte stdout and 81-byte stderr
from the runner invocation. The retained CTest raw stdout, stderr, discovery,
JUnit XML, source/toolchain/tool identities, harness files, terminal, and all
64 case records are byte-bound by the evidence manifest. No process remains.

## 3. Observed but uncredited JUnit

| Family | Passed | Failed | Total |
|---|---:|---:|---:|
| `compile` | 5 | 0 | 5 |
| `compile_bench` | 22 | 2 | 24 |
| `docparse` | 3 | 32 | 35 |
| **Total** | **30** | **34** | **64** |

The two compile-bench failures and 32 docparse failures report `failed to
create thread` in retained CTest output. This result records that exact symptom
but does not yet assign a single cause to all 34 rows. In particular,
`compile_bench/channel.lean` intentionally exercises threads, while the
docparse runner invokes Lean directly without the wrapper's `TEST_LEAN_ARGS`.

## 4. Artifact-closure root cause

The post-run validator's `case_generated_paths` function treated every
selected pile case as a compile-family test. Unless a `.no_compile` sidecar was
present, it required three generated paths:

```text
<source>.c
<source>.out
<source>.out.produced
```

That is correct for the selected compile families. It is false for docparse.
Pinned `tests/docparse/run_test.sh` at SHA-256
`46f17e20ef94483b3ba2bb52b218e718af048e81786534844578a557f05777ae`
uses `capture_only` and `check_out_file`; it emits only
`<source>.out.produced`. The three passing docparse cases did produce their
declared output captures, but the validator additionally demanded nonexistent
`.c` and `.out` files. The first ordered failure was `docparse/arg_0006.txt`.

This is an evidence-model defect after a valid process/JUnit capture, not a
source-preflight recurrence and not evidence that the shard passed. No file in
the retained evidence root will be overwritten or removed.

## 5. Non-claims and correction boundary

Current cumulative U2 coverage remains the earlier four M0 processes, two
decided outcomes for one unique official case, plus this fifth process attempt
with zero credited M2 outcome. There is still no completed M2 shard, official
provider reproduction, Axeyum outcome, matched pair, performance row, complete
population, complete axis, satisfied gate, or Lean parity.

Before any correction, this authority, result, and exact incomplete evidence
must be committed and pushed. A later source-first plan may evaluate whether
the immutable retained process/JUnit evidence can be completed without a new
process; it must separately freeze family-specific artifact rules, work-root
integrity, no-overwrite installation, the thread-failure classification
boundary, and stop conditions. R1 itself permits no retry.
