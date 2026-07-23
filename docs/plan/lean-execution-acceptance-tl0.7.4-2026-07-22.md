# TL0.7.4 result — pinned Lean/export execution path accepted with zero credit

Status: **DONE — local execution-policy prerequisite only**

Date: 2026-07-22

Authority:
[`lean-execution-acceptance-v1.json`](lean-execution-acceptance-v1.json)

Generated summary:
[`lean-execution-acceptance.md`](generated/lean-execution-acceptance.md)

Plans and prior attempt:

- [original source-first plan](lean-execution-acceptance-tl0.7.4-plan-2026-07-22.md)
- [attempt 001 failed result](lean-execution-acceptance-tl0.7.4-attempt-001-2026-07-22.md)
- [R1 source-first plan](lean-execution-acceptance-tl0.7.4-r1-plan-2026-07-22.md)
- [R2 merge-drift repair](lean-execution-acceptance-tl0.7.4-merge-drift-r2-result-2026-07-23.md)

## 1. Result

TL0.7.4 now accepts the complete local process/store path for exactly two
empty-selection, no-credit controls:

1. pinned Lean 4.30 compiled the committed flat probe under the 4 GiB
   `RLIMIT_AS` lane with one requested Lean worker and explicit 512 MiB task
   stack; and
2. source-built official `lean4export` v4.30.0 exported only that completed
   control's owned `.olean` under the 8 GiB lane, with stdout byte-for-byte
   equal to the committed reference.

The first preregistered compile attempt remains a failed, incomplete attempt;
it is not rewritten as success. Across both evidence roots the authority
records three observed external process attempts, one failed attempt, two
completed controls, 67 files / 142,523 bytes, and zero U2/Axeyum/paired/
performance/parity credit.

This closes TL0.7's local execution-policy prerequisite and unblocks TL0.6.3.
It is not Lean 4 parity and does not complete any parity population or axis.

## 2. Source-first chronology

| Boundary | Revision | Before process? |
|---|---|---|
| Original preregistration | `48a365954ad3dfc23985ef3504d8a9392d05f6c8` | before exporter build or compile/export control |
| Source-hash/build amendment | `b0a72dba16006941d9729dc284518dfd12f75f55` | before compile/export control |
| Original runner/tests | `4ba69b7076996057390e54daf8624e1b1cec9fb7` | before attempt 001 |
| Failed evidence + R1 plan | `2e83855e6e12c86a95862a95c9686a7875498bbe` | before R1 source/process |
| R1 thread-accounting clarification | `fde64fb39ded789f3a392a818d86d2dc7d299406` | before R1 source/process |
| R1 runner/tests | `679f4b9d1941b166c86db652501f1ba7df417da0` | before both completed controls |
| Rendered-authority check fix | `408381b1e098bf83594266066afb00594f25a402` | after immutable controls; generator/check path only |
| Installer merge-drift plan | `959374cf88de2b9062caf495c6fab4f55adf4f29` | after immutable controls; before R2 validator repair |
| Historical/current input split | `d51650e4dfb7db565fc49724f13882144bdbe75c` | after immutable controls; validator/test path only |

The authority names `679f4b9d...` as the control implementation revision.
The later `408381b1...` change only taught `--check` to read the same indented
JSON format the generator writes; it did not change or rerun either process.
The authority source-input list hashes the final historical script/test bytes.
R2 deliberately tracks its newer validator/test bytes in the terminal registry
without changing that list.

## 3. Exporter build provenance

The retained build record closes:

- official repository/tag commit
  `a3e35a584f59b390667db7269cd37fca8575e4bf`;
- Git tree `e8b4adcea8445abbe0ae656eb6067d079e3efca8`, 13 files,
  archive SHA-256
  `a66fd0b6f04701565221cb82c9702ab4036ab624471f91af27cf306ee4e35098`;
- exact pinned Lean/Lake executable hashes and version lines;
- the rejected pre-build `lake -j1 ...` attempt and its 33-byte diagnostic;
- the successful `lake build lean4export` command under
  `LEAN_NUM_THREADS=1`, empty stderr, and clean source status; and
- the 206,915,024-byte exporter executable with SHA-256
  `8e763913b03762488571a93ced6ec1a4e04f7d8eebbe40bd1215ba41a6bd4449`.

No live cache path is required for offline authority validation.

## 4. Failed attempt retained

Attempt 001 ran the original compile command without `-s`. Under exact 4 GiB,
Lean's default 1 GiB task-stack mappings caused a later stack `mmap` to return
`ENOMEM`; the process emitted the retained 98-byte `failed to create thread`
diagnostic and produced no `.olean`. Because the original runner checked for
the artifact before installing terminal evidence, the partial store has no
terminal or completion. The exporter did not run.

The separate 41-file / 89,974-byte failed root retains that defect, its raw
streams, the 4/5/6/8 GiB matrix, six explicit `-s` cells, and the focused
thread/mmap trace. Its evidence-manifest SHA-256 is
`c4f9fa088cd0f2fdb8a1cbebc111053252326ce5ea106f3e5ffa6b22ba292ae7`.

R1 fixes the ordering: raw streams and terminal install before artifact
validation on every outcome. A contract test forces a missing `.olean` and
proves terminal retention while artifact/completion remain absent.

## 5. Completed controls

| Property | Compile | Export |
|---|---:|---:|
| Control | `pinned-lean-compile-preflight-4g-tstack512m` | `official-lean4export-flat-export-8g` |
| Address-space limit | 4,294,967,296 bytes | 8,589,934,592 bytes |
| Requested Lean workers | 1 | 1 |
| OS-thread limit | not enforced | not enforced |
| Task stack | explicit 536,870,912 bytes (`-s524288`) | not observed/changed |
| Wall watchdog | 60,000 ms | 120,000 ms |
| Exit / signal / watchdog | 0 / none / false | 0 / none / false |
| Observed wall time | 139 ms | 503 ms |
| Sampled peak RSS | 85,032,960 bytes | 95,178,752 bytes |
| Direct child reaped | yes | yes |
| Live non-zombie group members after cleanup | 0 | 0 |
| Raw stdout | 0 bytes | 3,849 bytes / 65 lines |
| Raw stderr | 0 bytes | 0 bytes |
| Completion SHA-256 | `412930affb456cf9b47970af0e886b96dfc370ddbd13abf8d5cba32c681dae5f` | `9be90a95ed7ade1015598114d43b182b193edbf6063765aee0eae7ce7e14f3a0` |
| Stable projection SHA-256 | `a3af6c24011d8eb524fed0c1fa8e45cfd2e2330e44adc193b2f1cbea9f54030f` | `3585e2daed64c88806906c5921c15f1f1dd14a7e16c7150346a4fe7946cc9ff4` |

The compile artifact is 9,672 bytes with SHA-256
`1ce19df3f054ea6521fec7b8d49680d85087990c94e15bac00e731923152ecda`.
The exporter control's `LEAN_PATH` names that completed artifact directory and
its spec binds both the compile artifact and compile completion hashes.

The 3,849-byte exporter stdout and installed `export.ndjson` both have SHA-256
`c582b5d5ab19cba61183d592d70c17eb7d101b8a1ad61e8c4c6022dfe95a8280`,
exactly the committed oracle. The first row independently identifies
lean4export/format `3.1.0`, Lean `4.30.0`, and Lean commit
`d024af099ca4bf2c86f649261ebf59565dc8c622`.

## 6. Validation and bounded claims

Twenty-one focused offline contract tests now cover the original sixteen
mutation groups plus failed-attempt closure, task-stack/thread accounting,
Git-checkout mode portability, result rendering, and final authority closure.
The explicit live sentinel remains skipped unless requested; CI never builds,
downloads, or reruns external controls.

Authority SHA-256:
`f8a4d949b5dda4f37f8115a674702eb6dcaccc96394889d1ae3c28febeb4bfa5`.

The subsequent [R2 merge-drift repair](lean-execution-acceptance-tl0.7.4-merge-drift-r2-result-2026-07-23.md)
keeps this historical seal and all evidence bytes unchanged while separately
validating the newer fail-closed installer merged from the official-Lean gate.
The current validator is tracked by the complete-parity registry rather than
post-hoc rebinding this authority or its downstream U2 descendants.

The result proves only that these two exact external controls traverse the
local resource/process/immutable-store/completion path. It does not prove:

- any official U2 case or outcome;
- any Axeyum import, kernel check, or outcome;
- an official/Axeyum pair or performance comparison;
- suitability of the 512 MiB task stack for all U2 tests;
- power/host loss, NFS, remote provider, network, object-store, or distributed
  durability; or
- complete Lean 4 parity.

Every credit counter remains zero. TL0.6.3 is next and must preregister actual
official U2 selections before executing them.
