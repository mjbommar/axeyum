# TL0.7.4 attempt 001 — 4 GiB Lean thread-stack rejection

Status: **failed closed; no completion, export, U2 outcome, or parity credit**

Date: 2026-07-22

Plan: [original TL0.7.4 preregistration](lean-execution-acceptance-tl0.7.4-plan-2026-07-22.md)

Implementation revision:
`4ba69b7076996057390e54daf8624e1b1cec9fb7`

Retained partial evidence:
[`lean-execution-acceptance-tl0.7.4-attempt-001-failed/`](evidence/lean-execution-acceptance-tl0.7.4-attempt-001-failed/)

## 1. Bounded result

The first exact `pinned-lean-compile-preflight-4g` process did not produce an
`.olean`. The child ran under the preregistered 4,294,967,296-byte
`RLIMIT_AS`, with `-j1`, `LEAN_NUM_THREADS=1`, the exact pinned Lean 4.30
binary, and the committed 146-byte source. Its raw stderr is 98 bytes with
SHA-256 `32a60967270365f092cad81a408cf0e68f13aceab4359f32700f140a54129b9b`:

```text
libc++abi: terminating due to uncaught exception of type lean::exception: failed to create thread
```

Raw stdout is empty. The store contains the source/build/spec/run/prelaunch
records and raw streams but deliberately has no `.olean`, artifact record,
terminal record, or completion. The exporter was never launched.

The missing terminal record is a runner defect, not an ambiguity to paper
over. The process adapter reaped the child internally, but it checked for the
required `.olean` before installing the already-built terminal record. Because
the record was not retained, this result does not claim a process-group or
signal classification for the first attempt. The R1 implementation must
install raw streams and terminal evidence before validating success artifacts.

## 2. Root cause

The pinned Lean runtime source fixes the default 64-bit thread stack at 1 GiB
and creates its main function in a new runtime thread. See official
[`src/runtime/thread.cpp`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/runtime/thread.cpp).
The same pinned binary's `--help` exposes `-s, --tstack=num` as the task-thread
stack size in KiB.

The retained 4 GiB `strace` shows:

1. Lean maps one 1,073,745,920-byte stack and creates a thread;
2. it maps a second stack of the same size and creates another thread; and
3. a later 1,073,745,920-byte `MAP_STACK` request returns `ENOMEM`, after
   which the process aborts with the retained message.

This is address-space reservation pressure, not measured resident-memory
exhaustion and not a Lean source/elaboration failure. TL0.7.2's synthetic
`mmap` probe established that the lane can install `RLIMIT_AS`; it did not
establish that an unmodified Lean runtime can start inside the 4 GiB address
space.

## 3. No-credit diagnostic matrix

All diagnostics used the same source, pinned Lean bytes, `-j1`, correct source
working directory, empty stdout on success, and no Axeyum/U2 path.

### 3.1 Address-space envelope with default task stack

| `RLIMIT_AS` | Exit | `.olean` bytes | `.olean` SHA-256 | Stderr |
|---:|---:|---:|---|---|
| 4 GiB | 134 | absent | — | 98-byte thread-creation failure |
| 5 GiB | 0 | 9,672 | `1ce19df3f054ea6521fec7b8d49680d85087990c94e15bac00e731923152ecda` | empty |
| 6 GiB | 0 | 9,672 | `1ce19df3f054ea6521fec7b8d49680d85087990c94e15bac00e731923152ecda` | empty |
| 8 GiB | 0 | 9,672 | `1ce19df3f054ea6521fec7b8d49680d85087990c94e15bac00e731923152ecda` | empty |

### 3.2 Explicit `-s/--tstack` under 4 GiB

| Task stack | Lean option | Exit | `.olean` bytes/hash |
|---:|---|---:|---|
| 64 MiB | `-s65536` | 0 | 9,672 / `1ce19d...ecda` |
| 256 MiB | `-s262144` | 0 | 9,672 / `1ce19d...ecda` |
| 512 MiB | `-s524288` | 0 | 9,672 / `1ce19d...ecda` |
| 768 MiB | `-s786432` | 0 | 9,672 / `1ce19d...ecda` |
| 960 MiB | `-s983040` | 134 | absent; thread creation failed |
| 1 GiB | `-s1048576` | 134 | absent; thread creation failed |

The four successful task-stack settings produce identical `.olean` bytes.
R1 chooses 512 MiB: it preserves substantial recursion headroom while leaving
more address-space headroom than the largest passing diagnostic. It is an
explicit control input, not an assertion that 512 MiB is sufficient for every
future U2 case.

## 4. Evidence and claims

The retained folder currently contains 41 read-only files / 89,974 bytes:
the exact official exporter preparation, the partial first control store, the
4/5/6/8 GiB matrix, the six `-s` cells, and the focused `strace`. Diagnostic
`.olean` files are untrusted process artifacts and confer no checking credit.

Counters remain:

- completed TL0.7.4 controls: **0**;
- exporter processes: **0**;
- official U2 cases/outcomes: **0**;
- Axeyum imports/checks/outcomes: **0**;
- paired cells and performance rows: **0**;
- terminal Lean-parity credit: **0**.

The [R1 source-first plan](lean-execution-acceptance-tl0.7.4-r1-plan-2026-07-22.md)
governs any retry.
