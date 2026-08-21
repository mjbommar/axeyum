# QF_NIA deficit diagnosis — per-file data (2026-08-21)

Sidecar for
[`docs/research/05-algorithms/nia-deficit-diagnosis-2026-08-21.md`](../../docs/research/05-algorithms/nia-deficit-diagnosis-2026-08-21.md).

Population: `bench-results/parity-lists/QF_NIA.txt`, 200 files, sha256
`19b334d3b91090c87f90bf542a7eaa353915cc8c0220e4fd3e483b41aa71bd61` — the hash
recorded in that division's `PARITY.md` entry of 2026-08-06.

Protocol: 24 s wall per solver per file, 12 GiB address-space cap, external kill
at 32 s (29 s for cvc5, matching `scripts/parity-run.sh`'s `budget + 5`).
Measured at solver commit `cb4a391c9` on s4 (16-thread i5-12600K), sweeps at
`-P 5`, load average 5–12. Wall times are therefore an upper bound and decided
counts a lower bound.

Solvers:

- axeyum via `target/release/examples/uf_unknown_probe` (the shipped
  `solve_smtlib`, printing the `UnknownReason` the competition CLI suppresses)
- `/usr/bin/z3` 4.13.3, `-T:24`
- `/nas3/data/axeyum/harness/bin/cvc5` 1.3.4 `[git f3b21c4 on branch HEAD]`,
  `--tlimit=24000` — the recorded reference. It is **not on `$PATH`**, which is
  why two prior documents recorded it as absent from this host.

These are the per-file sidecars a `PARITY.md` entry claims to have and does not:
`bench-results/parity-details/` is gitignored (`.gitignore:51`).

---

## `QF_NIA.tsv` — 200 rows, the master table

| column | meaning |
|---|---|
| `file` | full list entry (not the basename — the list has ambiguous basenames) |
| `declared_status` | the benchmark's own `(set-info :status …)`; `unset` if absent |
| `bytes` | file size |
| `max_int_literal` | largest non-negative integer literal appearing anywhere in the text |
| `min_signed_width` | smallest signed bit-width holding `max_int_literal` |
| `live_ladder_rungs` | how many of the width ladder's 15 rungs (`4..16,24,32`) admit that literal — see the note §2.1 |
| `axeyum_verdict` | `sat` / `unsat` / `unknown` / `killed` |
| `axeyum_kind` | the `UnknownKind`: `Timeout`, `EncodingBudget`, `Incomplete`, `ResourceLimit`, `ExternalKill`, or `-` when decided |
| `axeyum_ms` | wall clock including process start |
| `axeyum_detail` | the `UnknownReason` detail string, tabs and newlines flattened |
| `decisive_route` | last route in the `explain_corpus --json` trace (the route that produced the verdict) |
| `decisive_reason` | that route's `declined` reason: `budget` / `incomplete` / `not-applicable` / `unsupported` |
| `decisive_detail` | that route's decline detail |
| `z3_verdict` | `sat` / `unsat` / `other` (**`other` is z3's `timeout` line** — verified: all 64 ran the full 24 s, and a malformed-file control shows an error prints differently) |
| `z3_ms` | wall clock |
| `cvc5_verdict` | `sat` / `unsat` / `timeout` |
| `cvc5_ms` | wall clock |

Reading notes:

- `decisive_route` is missing for `mcm/106.smt2`, which the trace pass could not
  complete, and is `<no trace>` for the one `ingest-resource-limit` file.
- On the 38 files axeyum decided, the trace pass agreed on 36 and returned
  `unknown` on 2 — `explain_corpus` diverges from the front door in both
  directions and **is not used as an oracle anywhere**. Verdicts in this table
  are the front door's; only the route columns come from the trace.
- Zero disagreements exist in this table: no decided verdict contradicts another
  solver's decided verdict or the declared `:status`.

## `ab-clause-ceiling.tsv` — §4.1, 49 rows

The 49 files the shipped configuration refuses with `EncodingBudget`, re-run with
the pre-lowering projected-clause ceiling raised `64,000,000` → `600,000,000`
(9.4×, the measured over-approximation factor of `estimate_blast_clauses`).
Columns: `patched_verdict`, `patched_ms`, `patched_head` (first line of output),
then the baseline verdict/kind and the two references for joining.
**Result: 0 newly decided.**

## `ab-presat-envelope.tsv` — §4.2, 200 rows

The full list re-run with `dpll_lia`'s pre-SAT admission envelope scaled ×16, so
`nia-linearize` is admitted on the skeletons it currently refuses. Same columns.
**Result: 38 → 39 decided, 0 lost, 0 verdict disagreements.**

## `calibration-4x-budget.tsv` — §4.3, 35 rows

Every third entry of the 104-file miss list (files a reference decides and
axeyum does not), taken deterministically before any result was seen, re-run at
**96 s** instead of 24 s. Columns: `verdict_96s`, `ms_96s`, then baseline and
references. **Result: 3 of 35, all from the `EncodingBudget` class, all with
wall 21–40 s; 0 of 20 `Timeout` files.**
