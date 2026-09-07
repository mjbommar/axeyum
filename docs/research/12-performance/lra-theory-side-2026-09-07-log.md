# QF_LRA theory side — the measurement log

Companion to [the diary](lra-theory-side-2026-09-07.md). This file holds the
numbers; the diary holds the reasoning and the hypotheses they falsified.

Protocol for every table below: idle **s7** (16 cores, 26 GiB), `taskset -c 0-7`,
24 s / 8 GiB per file, one file at a time, arms run in separate passes with the
binaries confirmed different by `sha256sum`, `/proc/loadavg` recorded before and
after each pass. Counters are preferred over wall time wherever they answer the
question, because they are clock-free: two runs minutes apart differ by up to
±20% on allocation-heavy work, and a counter does not.

Population: `bench-results/adr-1701-slice-1-20260905/qf_lra_population.tsv`,
33 files.

## 1. The baseline, before any change (`75286df9`)

The `; theory-layer` line from `smtcomp_cli --trace`, one row per file that ran a
CDCL(T) route to completion. `fchk` is `final_checks`, `fcconf` the ones that
answered `Conflict`, `core/c` the mean conflict-core width in literals, `rows/c`
the mean live-row count at a check, `piv/c` simplex pivots per check, `apc`
`assert_partial_conflicts`, `prop` `propagations_offered`.

| file | verdict | ms | fchk | fcconf | core/c | rows/c | piv/c | apc | prop | decisions |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `Heizmann/_standard_two_index_06…` | unknown | 24024 | 5737 | 5736 | 11.9 | 389.1 | 18.3 | 137 | 78251 | 815213 |
| `Heizmann/_count_by_k…` | unknown | 24020 | 2592 | 2591 | 13.7 | 340.8 | 38.1 | 15 | 43209 | 420789 |
| `2019-ezsmt/blending/1` | unsat | 6903 | 20732 | 20732 | 46.3 | 307.9 | 2.2 | 15 | 79 | 48532 |
| `2019-ezsmt/blending/5` | unsat | 6197 | 21138 | 21138 | 46.7 | 306.3 | 1.8 | 14 | 7793 | 57456 |
| `TM/p-driverlogNumeric_s7` | sat | 163 | 499 | 498 | 128.0 | 255.0 | 3.1 | 106 | 0 | 7827 |
| `TM/p5-driverlogNumeric_s9` | unsat | 289 | 0 | — | — | — | — | — | — | 4888 |
| `clock_synchro/…_2clocks` | unsat | 4988 | 30 | 29 | 9.0 | 176.8 | 2.2 | 7 | 59 | 2103 |
| `clock_synchro/…_4clocks` | unknown | 24266 | 58 | 57 | 8.5 | 364.1 | 2.0 | 11 | 197 | 8355 |
| `clock_synchro/…_6clocks` | unknown | 24825 | 84 | 83 | 8.5 | 592.0 | 2.1 | 15 | 389 | 19781 |
| `clock_synchro/…_8clocks` | unknown | 24729 | 110 | 109 | 8.5 | 859.5 | 2.2 | 19 | 645 | 36201 |
| `miplib/pp08a-1000` | unknown | 24033 | 30443 | 30443 | 138.2 | 527.0 | 0.5 | 339 | 0 | 1892449 |

The other 22 files printed **no** `; theory-layer` line at all — no CDCL(T)
route reached a verdict on them. That is the atom-cap class (section 4), not the
timeout class, and the census does not separate them.

**Decided at baseline: 7 of 33.**

### Where the time actually goes

| file | ms | `theory_final_check` | `theory_propagate` | `boolean_propagate` |
|---|---:|---:|---:|---:|
| `Heizmann/_standard_two_index_06…` | 24024 | 16984 (71%) | 6332 (26%) | 170 |
| `Heizmann/_count_by_k…` | 24020 | 16627 (69%) | 3157 (13%) | 71 |
| `blending/1` | 6903 | 6396 (93%) | 325 (5%) | 61 |
| `blending/5` | 6197 | 5576 (90%) | 439 (7%) | 59 |
| `miplib/pp08a-1000` | 24033 | 3288 (14%) | **18051 (75%)** | 1027 |
| `clock_synchro/…_4clocks` | 24266 | 3 | 46 | 1 |
| `clock_synchro/…_6clocks` | 24825 | 7 | 175 | 3 |
| `clock_synchro/…_8clocks` | 24729 | 13 | 461 | 6 |

## 2. The A/B, three arms

Arm **base** = `75286df9` (the counters, no behaviour change).
Arm **cand** = the scan filter + Stein's binary GCD + the integer fast paths.
Arm **c2** = the scan filter + **narrowed Euclid** + the integer fast paths.

All three arms produce **byte-identical counters** on `blending/1` — 20 732 final
checks, 46 618 pivots, 216 280 bound retractions, 20 791 learned clauses — so
every wall-time difference below is arithmetic and scan cost alone, with the
search trajectory held fixed. That is what makes the comparison a measurement of
the change rather than of the search.

| file | base ms | cand ms | c2 ms | c2/base |
|---|---:|---:|---:|---:|
| `blending/1` | 6903 | 11718 | 5942 | 0.86 |
| `blending/5` | 6197 | 10290 | 5265 | 0.85 |
| `TM/p-driverlogNumeric_s7` | 163 | 126 | 110 | 0.67 |
| `TM/p5-driverlogNumeric_s9` | 289 | 204 | 203 | 0.70 |
| `clock_synchro/…_2clocks` | 4988 | 5271 | 4245 | 0.85 |
| `spider_benchmarks/frame_prop` | 7857 | 6555 | — | — |
| `spider_benchmarks/fs_not_sc_seen` | 5368 | 4593 | — | — |
| `spider_benchmarks/no_op_accs` | unknown 24102 | **unsat 19229** | — | — |

**Decided: base 7/33, cand 8/33.** The c2 row is completed in section 5.
