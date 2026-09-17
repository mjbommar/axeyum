# QF_LRA: the tableau admission currency and the disequality split (A13-LRA)

Lane `a13-lra`, 2026-09-17. ADR-2146 (`AXEYUM_LRA_ADMIT_NONZEROS`) and
ADR-2147 (`AXEYUM_LRA_DISEQ_SPLIT`). This directory is the measurement record;
the decisions are in the two ADRs.

## 1. Sizing: both census mechanisms are still where the census left them

The LRA-MODEL-REPLAY census
([`../lra-model-replay-20260916/`](../lra-model-replay-20260916/README.md))
named two mechanisms behind "online CDCL(T) LRA model did not replay" on 38 of
the 47 files: **27** with no warm tableau (the dense-cell admission refused it
and the Fourier–Motzkin witness extraction declined) and **11** with a model
built and an equality atom asserted FALSE that the point violates. Main has
moved ~120 commits since (`4f81de9c1` → `43f1e0f90`), so the first thing this
lane did was re-run the diagnostic on exactly those 38 files
(`sizing-38.txt` = `no-tableau-27.txt` ++ `diseq-11.txt`, both derived from the
census's `per-file.tsv` by `analyze`-equivalent filters, not copied by hand).

Binary: the shipped `smtcomp_cli` at `43f1e0f90`, `--release --features full`,
sha256 `d3606850e01ba5c8d63de14d03eda10b52746d8ca500db2f274f3bfbdfe7e5ee` — the
same bytes ADR-2134's held-out lane built from the same snapshot. Host s4,
one pinned core per arm, 24 s, 8 GiB `ulimit -v`, `--trace` +
`AXEYUM_LRAMODELPROBE=1`; `$EPOCHREALTIME` timing with the 200 ms self-check
(203 ms, both arms). `sizing-run.sh` is the driver, `sizing-summarize.py`
buckets by mechanism, `sizing-summary.txt` is its output.

| population | shipped screen (`AXEYUM_LRA_ATOM_SCREEN` unset) | census screen (`=16`) |
|---|---|---|
| no-tableau **27** | **27 / 27** stop at `online_probe=admission-screen` — never reach the tableau question | **27 / 27** `fm-fallback-declined` + `no-model-reconstructed` |
| disequality **11** | **11 / 11** `model-built-but-does-not-replay` | **11 / 11** `model-built-but-does-not-replay` |

38 of 38 exit 0, 38 of 38 `unknown`, in both arms. **Both mechanisms are
confirmed at head, and one fact the census README states in passing is
load-bearing for the first lever: every one of the 27 has more than the 1,024
atoms the shipped screen admits** (the smallest is `sc-27` at 1,036;
`per-file.tsv` column `atoms`), so at the shipped screen the admission
currency touches none of them. Lever 1 alone is therefore measured on the
files at or under the screen whose dense count crosses the cap; its
composition with `AXEYUM_LRA_ATOM_SCREEN=16` is the second measurement.

The disequality count is confirmed from the shipped route itself, not from a
patched tree: the lever binary's OFF arm prints, at the moment the witness is
read out, the equality-atom census under `AXEYUM_LRAMODELPROBE=1`
(`sizing-wip-off-diseq11.tsv`, columns `equalities` / `eq_false` /
`diseq_violated`). See §2 for the table.

Files: `sizing-head-shipped.tsv`, `sizing-head-screen16.tsv`,
`sizing-summary.txt`; raw captures are on the host
(`/data0/axeyum-lane-scratch/a13-lra/sizing/cap/`).
