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

CENSUS-TABLE

## Shape sweep (the 67 scripts through A, B and z3)

SWEEP-TABLE

## A/B on the pinned lists

AB-TABLE
