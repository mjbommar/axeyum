# SMT-LIB measurement session, 2026-09-11/12

Every measurement from one session, with the provenance needed to judge it.
Numbers here are raw per-file data; the interpretations live in
`docs/research/03-measurements/`.

## What was established

| question | answer | where |
|---|---|---|
| Did our work move the board? | **+78** across 12 divisions with a prior row | `board/` |
| Was that the quiet machine? | **No** — 6 divisions re-measured interleaved against a BUILT BINARY of the 09-09 commit, zero losses, zero flips | `attribution/` |
| How do we compare on ONE consistent basis? | axeyum **2,309** / z3 **2,790** / cvc5 **2,652**, of 3,200 | `head-to-head/` |
| Is the addressable gap a budget problem? | **No** — 5x the clock wins 11.9%; 32% abandon the budget instead | `probes/headroom.tsv` |
| What blocks the divisions we never ran? | 36,888 files already reach the solver; 29,564 need recursive sorts. The "~30,000 behind two bugs" claim is **refuted** — see `../dt-divisions-20260912/` | `coverage/blockmap.txt` (labelled) |

## Layout

### `head-to-head/` — the consistent comparison
16 divisions x 200 files x 3 solvers = 9,600 solves, **one box, serial,
interleaved per problem, rotating order**. Columns:
`file, axeyum, ax_s, z3, z3_s, cvc5, cvc5_s`. See its own README for the
protocol and the box-selection measurement. Runner:
`scripts/fair-head-to-head.sh`.

### `board/` — the 16-division parity board
Per-file detail for every 2026-09-11 row, `file, axeyum, reference, declared`.
**`bench-results/parity-details/` is gitignored, so these copies are the only
durable record.** Every decided-count was cross-checked against `PARITY.md`
before commit; all 17 files are exactly 200 rows and all 17 match.

`QF_UFLRA.tsv` is the PRE-fix row (76/200) and `QF_UFLRA-postfix.tsv` the
re-measurement after `82152dbea` (142/200). Both are kept: the first is what the
board measured and the evidence that found the bug.

The reference solver differs PER DIVISION by SMT-COMP standing (ADR-1732) —
cvc5 for twelve, bitwuzla for QF_ABV/QF_BV/QF_FP, Z3 for QF_UFLRA. **Do not sum
the `reference` column across divisions**; that is what `head-to-head/` is for.

### `attribution/` — what our own work is worth
Interleaved per-file A/B, same host, both arms sharing ambient load.
- `armA-*` and `s7-armA-*`: the 09-09 board commit (`e99d08848f`) vs HEAD.
  QF_UFLIA **+36**, QF_LRA **+10**, UF **+5**, QF_ABV **0**, QF_BV **0**,
  QF_IDL **0** — all with zero losses and zero sat/unsat flips.
- `ab-*` and `uf-fixes`: `f09652489` (the parent of this session's three fixes)
  vs HEAD. QF_LRA **0/200**; QF_UFLIA **+5**; UF **+5**.
- `coupled-ab.tsv`: pre- vs post-`distinct`-fix over QF_UFLRA's RandomCoupled
  family — **67/67 identical**, proving the fix costs nothing.

Columns are `file, armA_verdict, armA_s, HEAD_verdict, HEAD_s`.

### `probes/` — diagnostics
- `headroom.tsv` — all 177 addressable-gap files at a **120 s** budget. 21
  decided (11.9%), 57 gave up early with budget unused (32.2%), 99 burned it.
  Absolute-budget, so a loaded host can only depress it: **11.9% is a floor**.
- `uflra-fixed.tsv`, `decoupled.tsv` — QF_UFLRA after the `distinct` fix;
  RandomDecoupled goes **1 of 69 -> 67 of 69**.
- `wchains.tsv` — roadmap 3.8's own falsifier, eager vs forced lazy-ROW over
  wchains060-200: **28/28 identical verdicts**, wall clock 1.003. Flipped 3.8
  from BUILD to DO NOT BUILD.
- `budget-probe.log` — QF_UFLIA's 13 addressable files at 24 s vs 120 s.
- `policy.tsv` — the three `UfArithOverboundPolicy` arms. **Run at load ~9 and
  therefore not trustworthy**; the isolated sweep in the measurement note is.
- `parse-census.tsv`, `giveup-kinds.tsv` — where gap files stop.
- `addressable-all.tsv` — the 177-file population itself.

### `coverage/blockmap.txt`
What stops us on each large never-measured division, 3 samples each, hard 15 s
wall (an earlier attempt hung on an 18k-file FP division because
`--timeout-ms` does not bound parsing).

## Caveats that travel with every number here

- **200 files per division is a sample.** Divisions average 17,891 files;
  3,200 is **0.73% of the 438,631-file corpus**.
- **16 of 84 divisions.** 68 have never been run — 65% of corpus files, because
  the measured ones include several of the largest.
- **Plain invocations.** SMT-COMP runs cvc5 with a portfolio
  (`--finite-model-find` among others) — exactly what wins the UF files our own
  FMF work wins. Both references run below their competition configuration.
- **Load moves these numbers more than most code changes do.** `PARITY.md` ran
  QF_UFLIA five times at ONE commit on 2026-09-09: 127, 113, 121, 136, 128. Any
  delta smaller than ~20 on that division, measured across hosts, is noise. That
  is why `attribution/` is interleaved rather than run-versus-run.
