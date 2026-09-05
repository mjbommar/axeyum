# ADR-1701 slice 1 — before/after measurement, 2026-09-05

Backing data for
[`docs/research/11-design-review/2026-09-05-adr-1701-slice-1-measured.md`](../../docs/research/11-design-review/2026-09-05-adr-1701-slice-1-measured.md).
Read that note for method, load conditions, and what these numbers do and do
not establish; this file only maps the artifacts.

| file | rows | what it is |
|---|---:|---|
| `qf_idl_population.tsv` | 50 | QF_IDL misses (2026-08-21 diagnosis TSV) with `unknown_kind` `Timeout` or `ResourceLimit` |
| `qf_lra_population.tsv` | 33 | QF_LRA misses with `unknown_kind` `Timeout` (excludes the `ResourceLimit` atom-cap refusals) |
| `qf_idl_before_after.tsv` | 50 | `file, declared, before_verdict, before_ms, after_verdict, after_ms` — BEFORE = `ef119b385`, AFTER = this lane's merge |
| `qf_lra_before_after.tsv` | 33 | same columns, QF_LRA population |

BEFORE binary: `ef119b385` (last `main` commit before ADR-1701's merge, via
`scripts/lane-snapshot.sh ef119b385`). AFTER binary: this lane's worktree.
Both built `cargo build --release -p axeyum-bench --example smtcomp_cli`
through `scripts/cargo-serialized.sh`. Confirmed to differ:
AFTER `sha256=3072e2c8…`, 41,030,696 bytes; BEFORE `sha256=1d5e145d…`,
40,655,880 bytes.

Each file run through both arms, interleaved (before, after, next file),
`taskset -c 0-7`, `--timeout-ms 24000` wrapped in `timeout -k 2 30s` as an
external hard-kill backstop. No verdict in either TSV contradicts the file's
`declared` `:status`.
