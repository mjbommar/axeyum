# ADR-2143 — `LiaTheory`/`LraTheory` opposite-polarity re-assert (lane ax-lia-pop, 2026-09-17)

The measurements behind
[ADR-2143](../../docs/research/09-decisions/adr-2143-an-opposite-polarity-reassert-is-a-conflict-never-an-overwrite.md).

## Layout

- `scripts/ab-run.sh` — the two-binary interleaved A/B runner (`$EPOCHREALTIME`,
  200 ms clock self-check, per-arm exit status, the file's `:status` as a
  column; refuses two identical binaries). `scripts/launch-ab.sh` shards each
  200-file list by line parity over s7 core pairs `1,9` and `3,11`.
- `scripts/run-shape-scripts.sh` — runs an incremental script through the
  pre-fix `axeyum`, the post-fix `axeyum` and z3, and compares the verdict
  streams on their common prefix (`unknown` on either side is not a
  disagreement).
- `shape/shape_census.py` — one row per SMT-LIB file: logic, pushes, asserts,
  and how many asserts arrived while their negation was live in an enclosing
  scope. `shape/census_public.tsv` is its run over the public incremental
  corpus (QF_LIA, QF_LRA, LIA, LRA, QF_UFLIA, QF_UFLRA, QF_ALIA, QF_AUFLIA);
  `shape/census_skipped.tsv` names the 97 files over 50 MB it did not read;
  `shape/census_committed.tsv` is the run over `corpus/incremental/`.
- `shape/sweep.tsv` — the 67 public scripts with the shape (plus the two
  fixtures as positive controls), through both binaries and z3.
- `ab/` — the A/B rows (`<DIV>.shard<N>.tsv`), the mover recheck, and the
  summary.

## Binaries

| arm | commit | sha256 |
| --- | --- | --- |
| A (`smtcomp_cli`) | `595d50102` (main `2d1dc3ac1` + ax-proptest `c2a25d3d8`, before the repair) | `c774e85d9506d675b61aeaae0b9fda9ad8e1143bd46a4d99c569cca88538ccf5` |
| B (`smtcomp_cli`) | `7526dfb25` (the repair) | `15cd43e762fd1de48451f896403ad41a8a4126c2d403df68d22e78543f24957d` |
| A (`axeyum`, incremental front door) | `595d50102` | `03a2ce354f1d1c1449521bc79b9aba2dac704a6670d1e10fad144ccc9b8d8727` |
| B (`axeyum`) | `7526dfb25` | `ec309c69556035b906bcb9903b469ef826cf5b1c48a26ebd4e7d3742ff476de6` |

Both built `--release -p axeyum-bench` from the lane worktree, default
features. z3 is 4.13.3 (`/usr/bin/z3` on s5/s6).

## Shape census

Rows: one per file — `logic`, `pushes`, `asserts`, `shadow_pairs` (asserts
that arrived while their negation was live in an enclosing scope).

| population | files scanned | with the shape | skipped (> 50 MB, named) |
| --- | ---: | ---: | ---: |
| `corpus/incremental/` (committed) | 14 | 2 (the ADR-2143 fixtures, the positive control) | 0 |
| public QF_LIA | 40 | 6 | 29 |
| public QF_LRA | 2 | 0 | 8 |
| public LIA | 6 | 5 | 0 |
| public LRA | 5 | 0 | 0 |
| public QF_UFLIA | 771 | 0 | 2 |
| public QF_UFLRA | 3027 | 0 | 31 |
| public QF_ALIA | 37 | 37 | 7 |
| public QF_AUFLIA | 52 | 19 | 20 |
| **public, all** | **3940** | **67** | **97** |

## Shape sweep (the 67 scripts through A, B and z3)

Budget 600 s per solver per file for the first 7 (run1), 300 s for the rest
(run2, 8 shards on s5/s6); 8 GiB, pinned; verdict streams compared on their
common prefix, `unknown` never a disagreement.

| logic | files | A agrees with z3 | B agrees with z3 | A agrees with B | no `axeyum` output in budget (both arms) | disagreements | verdicts A / B / z3 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| LIA | 5 | 5 | 5 | 5 | 0 | 0 | 22,831 / 22,831 / 22,831 |
| QF_LIA | 6 | 1 | 1 | 1 | 5 | 0 | 30,044 / 30,044 / 472,781 |
| QF_ALIA | 37 | 7 | 7 | 7 | 30 | 0 | 60,654 / 60,654 / 300,529 |
| QF_AUFLIA | 19 | 18 | 18 | 18 | 1 | 0 | 16,392 / 16,392 / 21,059 |
| **all** | **67** | **31** | **31** | **31** | **36** | **0** | **129,921 / 129,921 / 817,200** |

Controls: `13-shadowed-polarity-lia.smt2` and `14-shadowed-polarity-lra.smt2`
answer `unsat unsat sat` in both arms and in z3. The 36 no-output files are
rc 124 in BOTH arms: the front door parses the whole script before answering
and these carry 6,500–20,000 `check-sat`s; z3 streams its answers. That is a
capability gap of the incremental front door, identical before and after, and
not a verdict.

## A/B on the pinned lists

Two binaries (`smtcomp_cli`, sha256 above),
interleaved per file, order alternating, s7 core pairs `1,9` / `3,11`, 24 s
wall, 8 GiB `ulimit -v`, `$EPOCHREALTIME` with the 200 ms self-check
(read 205 ms on both shards).

| division | files | A decided | B decided | movers | `:status` disagreements A / B | non-zero exits A / B | wall A / B (s) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| QF_LIA | 200 | 120 | 120 | 0 | 0 / 0 | 0 / 0 | 1927 / 1926 |
| QF_LRA | 200 | 107 | 107 | 0 | 0 / 0 | 0 / 0 | 2286 / 2286 |
| QF_UFLIA | 200 | 161 | 161 | 0 | 0 / 0 | 0 / 0 | 1566 / 1567 |
| QF_IDL | 200 | 111 | 112 | 1 | 0 / 0 | 0 / 0 | 2295 / 2291 |
| **all** | 800 | 499 | 500 | 1 | 0 / 0 | 0 / 0 | 8073 / 8070 |

The one raw mover (`QF_IDL/asp/WireRouting/wire.10.x.10.b.5.a.20_unsat`, A
`unknown` at 21.7 s, B `unsat` at 20.8 s) was re-run three times per arm on
one pinned core: `unsat` 6 of 6 — BOTH-DECIDE, ambient, not an effect. So:
**0 stable losses, 0 stable gains, 0 new `:status` disagreements** — the
shipped search is byte-for-byte the same behaviour, as the driver analysis
predicts.

Rows: `ab/<DIV>.shard<N>.tsv`; summary: `ab/summary.md`; recheck: `ab/recheck-movers.tsv`.
