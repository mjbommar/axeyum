# ADR-1942 — the constructor-argument slice: sizing census, then the A/B

**2026-09-12, lane `dt-constructor-arg`.** Baseline `a25e98639` (`main`'s tip,
which carries ADR-1935 as `a15c96410`) against the candidate.

This directory holds two measurements, in the order they were taken and
committed:

1. **`census/`** — the SIZING, done before a line of code. Its finding is
   [`docs/research/03-measurements/the-constructor-arg-slice-is-10-of-173-files-2026-09-12.md`](../../docs/research/03-measurements/the-constructor-arg-slice-is-10-of-173-files-2026-09-12.md).
2. **`ab/`** — the interleaved per-file A/B over the five pinned parity lists
   (three target divisions plus two controls). See "The A/B" below.

## The sizing census

`collect_ackermann_groups` refuses at the FIRST datatype-sorted argument it
cannot handle, so the refusal string it produces — which is what a blocker
census reads — cannot say how many files a fix would reach. The instrumentation
classifies EVERY such argument in the query instead.

* `census-instrumentation.py` — applies the census block to
  `crates/axeyum-solver/src/datatype_native.rs`. It is a measurement patch and
  is deliberately NOT in the shipped source: it would be dead code in every
  build, and its output is a classification the refusal messages already carry
  one at a time.
* `make-shards.sh`, `census-host.sh`, `census-shard.sh` — the runner. Twelve
  modulo-interleaved shards per division (`NR%12`), four per box on `s5`/`s6`/`s7`
  (Ryzen 7 7840HS, idle at launch), two pinned cores each, 10 s wall / 8 GiB, a
  16 s wrapper headroom, and each run records its own outcome
  (`WRAPPER-KILLED` / `RC134-ABORT` / `SIGKILL`) rather than being silently
  scored.
* `census/<division>.tsv` — the rows, path-sorted, with the shared corpus prefix
  stripped and identical repeated classification lines collapsed to a count (the
  datatype route is entered once per equality encoding and once per dispatch
  rung, which repeats the same classification verbatim).
* `analyze-census.py` — reproduces every number in the note from those rows, and
  asserts it read 600 of them.

### What it found

| | AUFDTLIRA | UFDTLIRA | UFDT | of 600 |
|---|---:|---:|---:|---:|
| first refusal is the non-variable datatype argument | 44 | 54 | 75 | **173** |
| … **slice A eligible** (ADR-1942: constructor arguments) | 8 | 2 | 0 | **10** |
| … slice B eligible (also a datatype-VALUED result) | 21 | 22 | 14 | **57** |
| … … of which ALSO carry a constructor argument | 19 | 22 | 11 | **52** |

The base arm reproduces ADR-1935's residual census exactly (173 / 50 / 47 / 22,
178 decided), which is the check that the two are measuring the same thing.

### And what it got wrong

The strict per-file predicate here (EVERY entry into the datatype route
eligible) is neither an upper nor a lower bound on a QUANTIFIED division, because
the route is entered once per instantiation round and the file needs only one of
those entries to succeed. It named 11 files and 3 of them gained; all 10 actual
gains lie inside the loose (`any`-entry) predicate's 65. The honest bracket was
[3, 65] and the answer was 10. §7 of the note carries the correction and the
rule; the relative finding the build order turned on is unaffected.

## The A/B

Protocol inherited unchanged from
[`../dt-capability-20260912/`](../dt-capability-20260912/README.md), which is
what makes the numbers comparable to ADR-1935's:

* the committed parity lists, unsampled — `../parity-lists/{AUFDTLIRA,UFDTLIRA,UFDT,QF_DT,UF}.txt`,
  200 files each, `QF_DT` and `UF` as **controls**;
* both arms finish file N before either starts N+1, on the same pinned core
  pair, with the arm that goes first alternating per file;
* 10 s wall, 8 GiB, 16 s wrapper headroom, every run recording its own outcome;
* twelve modulo-interleaved shards per division, four per box on `s5`/`s6`/`s7`.

Runner `ab/ab-shard.sh`, `ab/run-host.sh`; analysis `ab/analyze.py` (the same
script ADR-1935's A/B used); rows `ab/out/<division>.tsv`, one per file carrying
both arms' verdict, wall time and give-up reason.

| division | n | base | new | delta | gain | loss | flip | base wall | new wall |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| AUFDTLIRA | 200 | 69 | **71** | **+2** | 2 | 0 | 0 | 223 s | 257 s |
| UFDTLIRA | 200 | 82 | **88** | **+6** | 6 | 0 | 0 | 124 s | 124 s |
| UFDT | 200 | 27 | **29** | **+2** | 2 | 0 | 0 | 484 s | 557 s |
| QF_DT *(control)* | 200 | 169 | 169 | 0 | 0 | 0 | 0 | 52 s | 52 s |
| UF *(control)* | 200 | 88 | 88 | 0 | 0 | 0 | 0 | 1,372 s | 1,371 s |

**+10 net, 0 decided→undecided, 0 flips, 0 declared-`:status` disagreements
anywhere in the 1,000 rows.** The base arm reproduces ADR-1935's committed
new-arm rows exactly (69 / 82 / 27), which is the check that the two arms measure
what that A/B measured.

Every one of the 10 newly decided files was re-run at 24 s against BOTH oracles
and its declared status (`ab/verify-gains.sh`, rows in `ab/verify-gains.tsv`).
Units differ and getting one wrong cripples a reference silently, so `z3 -T:24`
(SECONDS) and `cvc5 --tlimit 24000` (MILLISECONDS):

| | rows |
|---|---:|
| axeyum `unsat` / z3 `unsat` / cvc5 `unsat` / declared `unsat` | **10 of 10** |
| any disagreement, any pair | **0** |

### Reading the wall figures

`UFDTLIRA` is free (124 s → 124 s) and carries most of the gain; `AUFDTLIRA` and
`UFDT` each pay about +15 % for two files, because a query that used to end at
the shape refusal now runs further down the ladder. Both controls moved within
noise.

**One caveat specific to the seconds.** Another lane's benchmark process held
100 % of one core on `s7` throughout. The per-file interleave with alternating
arm order cancels that in the DIFFERENCE — which is why the verdict columns (0
losses, 0 flips) are trustworthy — but it inflates both arms' absolute wall
numbers on that host's four shards. Do not compare these seconds to another
run's.
