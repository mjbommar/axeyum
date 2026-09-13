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

## The A/B

**Not yet run at this commit.** The sizing above is committed first, on purpose:
ADR-1935's headline lesson is that a blocker count is not a reachable-fix count,
and a sizing published after the gain it predicts is not a prediction. The A/B
protocol, rows, and oracle re-validation land in `ab/` in a later commit on this
lane, and this README is extended then.
