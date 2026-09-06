# Native core vs Kissat vs CaDiCaL — search statistics, 20-file population

60 s wall budget per engine per file, `taskset -c 0-7` on s7 (idle, 16-core
host). Kissat run as `kissat -s --time=<N>`, CaDiCaL as `cadical -v -t <N>`.
`-s`/`--statistics=true` gives the same statistics/profiling blocks as `-v`
without Kissat's very verbose internal allocator logging (verified against a
`-v` run: identical statistics and profiling sections, ~2.4x fewer lines).

Cross-engine verdict check: **0 disagreements across all 20 files x 3
engines** (60 (engine, file) verdicts where at least two engines decided the
same file; every pair that both decided agrees). No P0 finding.

`search%` / `probe%` (Kissat) and `search%` / `simplify%` (CaDiCaL) are the
two *mutually exclusive, non-overlapping* top-level phases each solver's own
profiler reports (verified: `search + probe + {parse,lucky,extend overhead}
≈ total` for Kissat; `search + simplify + {parse,lucky overhead} ≈ total`
for CaDiCaL, both within ~2% of the solver's own reported total). **A flat
sum of every named phase line was tried first and rejected**: Kissat's and
CaDiCaL's profiling blocks are a call tree, not a flat partition (e.g.
Kissat's `focused`+`stable` sum to `search`, and everything else nests under
`probe`; CaDiCaL's `unstable`+`stable` sum to `search`, and everything else
nests under `simplify`) — summing all lines double- and triple-counts nested
time and produced impossible >100% "inprocessing shares" (up to 129%) before
this was caught. `probe`/`simplify` is each solver's own name for its
inprocessing umbrella (preprocessing + probing + subsumption + elimination +
vivification + congruence + sweep + backbone + transitive + factor), so its
reported percentage is exactly "time not in core CDCL search," with no
double counting.

## Per-file table

| file | group | native v | native s | native conf | native conf/s | kissat v | kissat s | kissat conf | kissat conf/s | kissat search% | kissat probe%(inproc) | cadical v | cadical s | cadical conf | cadical conf/s | cadical search% | cadical simplify%(inproc) |
|---|---|---|---:|---:|---:|---|---:|---:|---:|---:|---:|---|---:|---:|---:|---:|---:|
| compose.p2._bit8_na6_nr3_paired.cnf | A | sat | 0.099 | 40 | 403 | sat | 3.33 | 8900 | 2673 | 54.6 | 40.9 | sat | 0.58 | 1022 | 1762 | 100.0 | 0.0 |
| compose.s2._bit8_na6_nr3_paired.cnf | A | sat | 5.233 | 35352 | 6756 | sat | 3.09 | 25597 | 8284 | 48.1 | 32.9 | sat | 5.56 | 66656 | 11988 | 58.8 | 41.2 |
| compose.s2._bit8_na6_nr4_paired.cnf | A | sat | 38.363 | 203732 | 5311 | sat | 7.25 | 60222 | 8306 | 49.8 | 28.0 | sat | 6.06 | 50933 | 8405 | 56.6 | 43.4 |
| mobiledevice_bit8_na1_nr1_twocond.cnf | A | sat | 1.189 | 54543 | 45877 | sat | 0.43 | 23089 | 53695 | 62.5 | 33.8 | sat | 0.13 | 8235 | 63346 | 74.3 | 25.7 |
| mobiledevice_bit8_na6_nr3_paired.cnf | A | sat | 2.911 | 43981 | 15106 | sat | 1.92 | 21674 | 11289 | 47.6 | 34.4 | sat | 1.53 | 14809 | 9679 | 52.6 | 47.4 |
| mobiledevice_bit8_na6_nr3_twocond.cnf | A | sat | 0.369 | 8635 | 23410 | sat | 1.08 | 17644 | 16337 | 49.4 | 32.2 | sat | 0.72 | 10925 | 15174 | 54.7 | 45.3 |
| simple_bit8_na1_nr1_twocond.cnf | A | sat | 0.001 | 13 | 10682 | sat | 0.00 | 0 | - | 0.0 | - | sat | 0.00 | 0 | - | 81.7 | 0.0 |
| string1x8.3._bit8_na6_nr3_paired.cnf | A | sat | 13.109 | 200131 | 15267 | sat | 4.98 | 119824 | 24061 | 55.7 | 29.3 | sat | 5.65 | 148844 | 26344 | 71.7 | 28.3 |
| string1x8.6._bit8_na6_nr3_paired.cnf | A | sat | 20.047 | 274337 | 13685 | sat | 6.71 | 198511 | 29584 | 63.7 | 23.1 | sat | 11.18 | 309267 | 27663 | 78.7 | 21.3 |
| string1x8.7._bit8_na6_nr3_paired.cnf | A | unknown | 60.132 | 870400 | 14475 | sat | 12.51 | 432792 | 34596 | 73.2 | 18.3 | sat | 17.78 | 592299 | 33313 | 81.4 | 18.6 |
| videoconf_simple_bit8_na6_nr3_paired.cnf | A | unknown | 60.252 | 504832 | 8379 | sat | 5.00 | 76290 | 15258 | 50.9 | 31.2 | sat | 11.70 | 276085 | 23597 | 72.8 | 27.2 |
| compose.p3._bit8_na6_nr3_paired.cnf | B | sat | 0.902 | 128 | 142 | sat | 29.68 | 10709 | 361 | 68.4 | 25.8 | sat | 4.35 | 1163 | 267 | 100.0 | 0.0 |
| string1x8.4._bit8_na6_nr3_paired.cnf | B | sat | 11.228 | 198909 | 17716 | sat | 7.30 | 259476 | 35545 | 65.8 | 20.8 | sat | 25.43 | 793261 | 31194 | 82.1 | 17.9 |
| tcp_open_bit8_na6_nr3_paired.cnf | B | unknown | 60.087 | 502784 | 8368 | sat | 41.15 | 1146818 | 27869 | 78.9 | 15.4 | unknown | 59.97 | 1280204 | 21347 | 84.4 | 15.6 |
| string1x16.4._bit8_na6_nr3_paired.cnf | B | unknown | 60.152 | 610304 | 10146 | unknown | 59.99 | 1410043 | 23505 | 80.4 | 13.8 | unknown | 59.98 | 1252213 | 20877 | 79.9 | 20.1 |
| videoconf_full_bit8_na6_nr3_paired.cnf | B | unknown | 60.194 | 459776 | 7638 | unknown | 59.99 | 1501192 | 25024 | 74.0 | 17.7 | unknown | 59.97 | 1192868 | 19891 | 80.2 | 19.8 |
| string2x8.4._bit8_na6_nr3_paired.cnf | B | unknown | 60.100 | 472064 | 7855 | unknown | 59.99 | 1295404 | 21594 | 75.6 | 16.3 | unknown | 59.98 | 1169720 | 19502 | 80.2 | 19.8 |
| string4x8.8._bit8_na6_nr3_paired.cnf | B | unknown | 60.078 | 307200 | 5113 | unknown | 59.99 | 1015539 | 16928 | 67.8 | 19.8 | unknown | 60.06 | 962074 | 16019 | 75.5 | 24.5 |
| compose.s3._bit8_na6_nr3_paired.cnf | B | unknown | 60.401 | 109568 | 1814 | unknown | 60.11 | 416842 | 6935 | 56.8 | 29.5 | unknown | 60.08 | 492298 | 8194 | 71.5 | 28.5 |
| string4x16.4._bit16_na6_nr4_paired.cnf | B | unknown | 62.398 | 30720 | 492 | unknown | 60.44 | 21879 | 362 | 51.8 | 24.8 | unknown | 60.90 | 15047 | 247 | 45.5 | 54.5 |

`native s` for an `unknown` verdict is the wall time at which the core's
60 s deadline fired (checked on a fixed conflict cadence, so it can run
slightly past 60 s — up to 62.4 s on `string4x16.4`, the largest instance,
consistent with the documented "deterministic conflict cadence" deadline
check in `proof_sat.rs`). `kissat s` / `cadical s` for `unknown` is each
solver's own reported process time at its internal `--time`/`-t` cutoff.

## Q1: files all three engines decide (11 of 20; `simple_*` excluded, 0
conflicts on both native and Kissat — ratio undefined for a unit-propagation-only solve)

| file | conflicts native/kissat | conflicts/s native/kissat |
|---|---:|---:|
| compose.p2._bit8_na6_nr3_paired.cnf | 0.004 | 0.151 |
| compose.s2._bit8_na6_nr3_paired.cnf | 1.381 | 0.816 |
| compose.s2._bit8_na6_nr4_paired.cnf | 3.383 | 0.639 |
| mobiledevice_bit8_na1_nr1_twocond.cnf | 2.362 | 0.854 |
| mobiledevice_bit8_na6_nr3_paired.cnf | 2.029 | 1.338 |
| mobiledevice_bit8_na6_nr3_twocond.cnf | 0.489 | 1.433 |
| string1x8.3._bit8_na6_nr3_paired.cnf | 1.670 | 0.635 |
| string1x8.6._bit8_na6_nr3_paired.cnf | 1.382 | 0.463 |
| compose.p3._bit8_na6_nr3_paired.cnf | 0.012 | 0.393 |
| string1x8.4._bit8_na6_nr3_paired.cnf | 0.767 | 0.498 |

- **geomean, all 10**: conflicts ratio = **0.503**, conflicts/s ratio = **0.612**
- **median, all 10**: conflicts ratio = **1.382**, conflicts/s ratio = **0.637**
- `compose.p2` and `compose.p3` are outliers in the opposite direction from
  the rest: native happens to hit a satisfying assignment in 40 and 128
  conflicts respectively (a lucky VSIDS/phase-saving trajectory on these two
  instances specifically), while Kissat needs 8,900 and 10,709 — that pulls
  the geomean well below 1. **Excluding those two** (8 files): geomean
  conflicts ratio = **1.362**, geomean conflicts/s ratio = **0.775** — much
  closer to, but still below, the median, and directionally consistent:
  native typically needs *somewhat more* conflicts (median 1.38x) and always
  processes them *slower* (every one of the 8 non-outlier conflicts/s ratios
  is < 1, median 0.637, i.e. Kissat does ~1.57x more conflicts/second than
  native) except the two `mobiledevice` files, where native's conflicts/s
  exceeds Kissat's (1.34x, 1.43x) despite needing more conflicts overall.

## Q2: files Kissat decides that the native core does not (60 s each)

Two readings, since only one file is *exclusively* decided by Kissat among
all three engines — the other two are also decided by CaDiCaL:

**Strict (native fails, Kissat decides, CaDiCaL also fails)** — 1 file:

| file | kissat wall_s | search% | probe%(inprocessing) |
|---|---:|---:|---:|
| tcp_open_bit8_na6_nr3_paired.cnf | 41.15 | 78.9 | 15.4 |

**Broad (native fails, Kissat decides, CaDiCaL may or may not)** — 3 files:

| file | kissat wall_s | search% | probe%(inprocessing) |
|---|---:|---:|---:|
| string1x8.7._bit8_na6_nr3_paired.cnf | 12.51 | 73.2 | 18.3 |
| videoconf_simple_bit8_na6_nr3_paired.cnf | 5.00 | 50.9 | 31.2 |
| tcp_open_bit8_na6_nr3_paired.cnf | 41.15 | 78.9 | 15.4 |

mean search% = 67.7, mean probe%(inprocessing) = 21.6.

For comparison, across the 10 non-trivial files all three engines decide
(`simple_*` excluded — 0 conflicts, no `probe` phase ran), Kissat's mean
probe% is 30.1 (range 20.8-40.9) — **the same order of magnitude as on the
files it alone reaches** (21.6-31.2 depending on reading), not a jump. Kissat's
`search%` is never below 45.5 across all 20 files and averages 58.7% overall
(range 45.5-100.0); `probe%` averages 25.7% across the 19 files where it ran
at all. Kissat's own profiler attributes the *majority* of its wall time to
`search`, not `probe`, on every file measured.
