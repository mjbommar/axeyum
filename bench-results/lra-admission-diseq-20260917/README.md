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

## 2. The disequality count, from the shipped route itself

`sizing-wip-off-diseq11.tsv` (lever binary, OFF arm, shipped screen,
`AXEYUM_LRAMODELPROBE=1`): `LraTheory::model` now prints, at the moment the
witness is read out, how many equality atoms the search set FALSE and how
many of those the point violates. `sc-25`: **776 equality atoms, 371 asserted
false** — the census's number exactly — of which 8 sit on their hyperplane at
the point. The whole `sc` family and `pursuit-safety-16` match the census
table column for column (ADR-2147 §sizing). `sizing-wip-split-diseq11.tsv` is
the same 11 under `AXEYUM_LRA_DISEQ_SPLIT=1`: `sc-7/9/11/13/15/17` → `unsat`
(0.6 / 1.5 / 2.5 / 7.3 / 15.3 / 20.9 s), the rest still `unknown` at 24 s.

## 3. The A/B

One binary (`smtcomp_cli` built `--release --features full` from the lane
tree at `0f311e650`, sha256 in `binary-sha256.txt`:
`8079669575dc6c63b1248d614e984d8eeaf0f32b5873b06f690020b4db352219`),
env arms, interleaved per file on the same pinned core with the arm order
ROTATING per file (`ab-arms.sh`, ADR-2134's driver generalised to N arms),
24 s wall, 8 GiB `ulimit -v`, `$EPOCHREALTIME` timing with the 200 ms
self-check. Hosts s5 and s6, both idle at launch (load 0.02 / 0.04), core
pairs `1,9` and `3,11` on each; every list split into two 100-file shards
(`drive-shard.sh`).

| population | arms | shards |
|---|---|---|
| `QF_LRA` pinned 200 (the board's list, = the census's) | base / `nz` (ADR-2146) / `sp` (ADR-2147) / `both` | s5 `1,9`, s5 `3,11` |
| `QF_LRA` held-out 200 (ADR-2132's draw, verified disjoint from the pinned list, 0 overlap) | the same four | s5, after the pinned shards |
| `QF_UFLRA` pinned 200 (the `uflra_online` route builds the same theory, so ADR-2146 reaches it; the split does not) | the same four | s6 `1,9`, s6 `3,11` |
| `QF_RDL` pinned 200, `QF_IDL` pinned 200 (controls) | base / `both` | s5 and s6, after the above |
| `QF_LRA` pinned 200, the COMPOSITION the census population exists under | `s16` (`AXEYUM_LRA_ATOM_SCREEN=16`) / `s16both` (screen + both levers) | s6, last |

`ab-summarize.py` folds shards and reports, per arm against base: decided,
gains, losses, flips, `:status` disagreements, rc-134 aborts and NEW aborts,
and writes the mover lists; `recheck-movers-env.sh` re-runs each mover three
times per arm, arms alternating within the passes.

**One launch defect, recorded rather than hidden:** the first launch on s6
started `uflra` shard 0 twice (a hung `ssh` whose command had in fact run,
then a second launch through `launch.sh`); the duplicate refused the
non-empty `uflra.0.tsv` and went on to its next queue item, so for about four
minutes (rows 3–5 of `uflra.0`) an `idl.0` sweep shared core pair `1,9` with
the genuine `uflra.0` sweep. The duplicate was killed, its `idl.0` output
moved to `out/contaminated/`, and `idl.0` re-runs from the genuine driver's
queue. The affected `uflra.0` rows are interleaved per file, so both arms
paid the same contention; any mover among them is rechecked 3× like every
other.

## 4. Results

Rows: `ab/<pop>.<shard>.tsv`; summaries: `ab-summarize.py <name> ab/<pop>.*.tsv`;
rechecks: `ab/recheck.<pop>-<arm>.tsv`; mover lists: `ab/<pop>-movers-<arm>.txt`.

### Per lever, against `base`

| population | base | `nz` (ADR-2146) | `sp` (ADR-2147) | `both` | losses / flips / `:status` disagreements / rc-134 (any arm) |
|---|---:|---:|---:|---:|---|
| `QF_LRA` pinned 200 | 107 | 107 | **113** | 113 | 0 / 0 / 0 / 0 |
| `QF_LRA` held-out 200 | 93 | 93 | **97** | 97 | 0 / 0 / 0 / 0 |
| `QF_UFLRA` pinned 200 | 148 | 148 | **150** | 150 | 0 / 0 / 0 / 0 |
| `QF_IDL` pinned 200 (`base` / `both`) | 112 | — | — | 112 | 0 / 0 / 0 / 0 |
| `QF_RDL` pinned 200 (`base` / `both`) | 150 | — | — | 150 | 0 / 0 / 0 / 0 |

`nz` is inert on every population at the shipped screen (wall identical:
2,281 / 2,281 s pinned, 2,554 / 2,555 s held-out, 1,856 / 1,853 s UFLRA) —
by arithmetic, not chance: every file whose dense count crosses the cap is
refused by the 1,024-atom screen first (§1). `both` reproduces `sp` row for
row.

### 3× rechecks (one binary, `-` vs the lever, arms alternating within passes)

| population, arm | STABLE-GAIN | STABLE-LOSS | UNSTABLE |
|---|---:|---:|---:|
| `QF_LRA` pinned, `sp` | 5 (`sc-7/9/11/13/15`) | 0 | 1 (`sc-17`: 2/3, decided at 19–20 s of 24) |
| `QF_LRA` pinned, `both` | 5 | 0 | 1 (the same file, the same 2/3) |
| `QF_LRA` held-out, `sp` | 4 (`uart-8.base`, `sc-10.induction2`, `sc-15.induction2`, `sc-18.induction`) | 0 | 0 |
| `QF_LRA` held-out, `both` | 4 | 0 | 0 |
| `QF_UFLRA`, `sp` | 2 | 0 | 0 |
| `QF_UFLRA`, `both` | 2 | 0 | 0 |

### The composition the census population exists under (`QF_LRA` pinned, s6)

| arm | decided | gains | losses | rc-134 |
|---|---:|---:|---:|---:|
| `s16` = `AXEYUM_LRA_ATOM_SCREEN=16` | 107 | — | — | **8** |
| `s16both` = the screen + both levers | 112 | 6 (`sc-7 … sc-17`) | 1 (`latendresse/ecoliMILPglycerolYices3-50000`, `sat` → `unknown`) | **0** |

Recheck: 6 STABLE-GAIN, 1 STABLE-LOSS. The gains are ADR-2147's; the 8
aborts removed and the one routing loss are ADR-2146's (its §measurement
reads all three).

### Decisions

* **ADR-2147, `AXEYUM_LRA_DISEQ_SPLIT`: ships ON.** Criterion (0 stable
  losses, 0 flips, 0 `:status` disagreements, ≥ 1 stable gain on pinned AND
  held-out, no new abort): met on every clause.
* **ADR-2146, `AXEYUM_LRA_ADMIT_NONZEROS`: stays OFF.** The gain clause fails
  on every population at the shipped screen; the composition with the screen
  is measured and recorded, not shipped.
