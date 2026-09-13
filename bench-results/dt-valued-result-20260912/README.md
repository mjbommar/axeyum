# ADR-1946 — the datatype-VALUED UF result: sizing census, then the A/B

**2026-09-12, lane `dt-valued-result`.** Baseline `183758366` (`main`'s tip,
which carries ADR-1942 as `295781893`) against the candidate.

Two measurements, in the order they were taken and committed:

1. **`census/`** — the SIZING, done before the implementation was committed. Its
   finding is
   [`docs/research/03-measurements/the-datatype-valued-result-rung-priced-on-its-own-arm-2026-09-12.md`](../../docs/research/03-measurements/the-datatype-valued-result-rung-priced-on-its-own-arm-2026-09-12.md).
2. **`ab/`** — the interleaved per-file A/B over the five pinned parity lists
   (three target divisions plus two controls). See "The A/B" below.

## The sizing census

`collect_ackermann_groups` refuses at the FIRST datatype-sorted argument it
cannot handle, so the refusal string a blocker census reads cannot say how many
files a fix would reach. The instrumentation recollects the applications under
this lane's WIDENED rule and classifies every argument and every result sort of
every widened site, plus the congruence pair count under both rules.

* `census-instrumentation.py` — applies (and `--revert`s) the census block. It
  is a measurement patch and is deliberately NOT in the shipped source: it would
  be dead code in every build, and its output is a classification the refusal
  messages already carry one at a time.
* `make-shards.sh`, `census-host.sh`, `census-shard.sh` — the runner. Twelve
  modulo-interleaved shards per division (`NR%12`), four per box on
  `s5`/`s6`/`s7` (idle at launch), two pinned cores each, 10 s wall / 8 GiB, a
  16 s wrapper headroom, and each run records its own outcome
  (`WRAPPER-KILLED` / `RC134-ABORT` / `SIGKILL`) rather than being silently
  scored.
* `collect-census.py` — merges the shards, strips the shared corpus prefix and
  collapses identical repeated classification lines to a count (the datatype
  route is entered once per equality encoding and once per dispatch rung, which
  repeats the same classification verbatim).
* `census/<division>.tsv` — the committed rows, path-sorted.
* `analyze-census.py` — reproduces every number in the note from those rows, and
  asserts it read 600 of them.

### What it found

| | AUFDTLIRA | UFDTLIRA | UFDT | of 600 |
|---|---:|---:|---:|---:|
| decided on the base arm | 71 | 88 | 29 | **188** |
| first refusal is the datatype-valued RESULT | 21 | 3 | 27 | **51** |
| **ADR-1946 eligible, ANY route entry** *(undecided only)* | 85 | 46 | 89 | **220** |
| … newly so (the arm as it stands is not) | 28 | 16 | 8 | **52** |
| DECIDED files pushed over the pair bound by the widening | 0 | 0 | 0 | **0** |

The base verdicts reproduce ADR-1942's A/B new-arm rows exactly (71 / 88 / 29),
which is the check that the two measurements are of the same tree.

**The sizing committed before the code: a bracket of [0, 52] on the eligibility
axis, point estimate low teens, plus an unquantified contribution from the
48-file `is`/`select`-over-a-non-variable bucket that the pre-pass predicate
structurally cannot see.** §4 of the note says why, and says it before the A/B
so the A/B can refute it.

## The A/B

Protocol inherited unchanged from
[`../dt-constructor-arg-20260912/`](../dt-constructor-arg-20260912/README.md),
which is what makes the numbers comparable to ADR-1935's and ADR-1942's:

* the committed parity lists, unsampled —
  `../parity-lists/{AUFDTLIRA,UFDTLIRA,UFDT,QF_DT,UF}.txt`, 200 files each,
  `QF_DT` and `UF` as **controls**;
* both arms finish file N before either starts N+1, on the same pinned core
  pair, with the arm that goes first alternating per file;
* 10 s wall, 8 GiB, 16 s wrapper headroom, every run recording its own outcome;
* twelve modulo-interleaved shards per division, four per box on `s5`/`s6`/`s7`.

Runner `ab/ab-shard.sh`, `ab/run-host.sh`; analysis `ab/analyze.py`; rows
`ab/out/<division>.tsv`, one per file carrying both arms' verdict, wall time and
give-up reason. Oracle re-validation of every newly decided file:
`ab/verify-gains.sh`, rows in `ab/verify-gains.tsv`.

*(The A/B section's result table is filled in by the ADR once the run lands.)*
