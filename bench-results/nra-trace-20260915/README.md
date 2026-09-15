# QF_NRA: what stops the 83 we do not decide — 2026-09-15

Lane `nra-trace`, ADR-2110. The board
(`bench-results/board-ab-20260915/QF_NRA.tsv`, column `main_054104068`) records
**117 of 200** decided; z3 4.13.3 decides **187** of the same 200
(`bench-results/session-20260911-smtlib/head-to-head/QF_NRA.tsv`). This
directory is the census of the **83** the board leaves undecided.

## The brief's premise was wrong, and it matters

The lane brief said "no census has ever been run on this division". One has:
[`docs/research/12-performance/qf-nra-loss-attribution-2026-09-09.md`](../../docs/research/12-performance/qf-nra-loss-attribution-2026-09-09.md)
swept 75 QF_NRA **parity-loss** files six days earlier and produced a step-1
split, a shape table and two A/Bs. Two routes in the tree today
(`nra_fbbt`'s derived bounds, `SkeletonSolvePolicy`) came out of it.

This census is not a repeat of that one and does not supersede it:

- **different population** — undecided on the 2026-09-15 board (83 files),
  not the 2026-09-08 parity-loss cut (75 files);
- **different instrument** — route-trail **schema 3**, which did not exist on
  2026-09-09. That sweep recorded "the route trail is blind on 21 of 75
  files"; here every one of the 83 carries a trail and the `bound_by` column
  is populated on 82 of 83.

Where the two agree, they are quoted as agreeing. The 2026-09-09 note is the
better source for the lazy-SMT loop's internal split, which this census does
not re-measure.

## Protocol

83 files, `smtcomp_cli --trace`, **24 s wall / 8 GiB `ulimit -v`**, two shards
on **s5 cores `1,9` and `3,11`** (physical pairs on a uniform Zen 4; no E-cores
here, unlike s4). Binary `815489e35e2235f1`, built release from this branch.
Every run goes through `scripts/ledger-run-one.sh`, so every row is an
outcome-ledger row (ADR-2102) and the capture is kept:
`bench-results/ledger/nra-trace-census-20260915.tsv`, 83 rows, 0 files without
one.

s5 load average was 0.00–1.3 throughout (the shards are each other's only
company). Wall-clock numbers below are still reported as *shares*, not as
absolute seconds, for the reason the 2026-09-09 note gives.

## The buckets

Keyed on the decline of the route that **held the budget**, with restating
wrappers unwrapped. Full table in `census-report.txt`, per file in
`census-83.tsv`.

| files | bucket | median vars | median degree |
|------:|--------|------------:|--------------:|
| **26** | `nra/incomplete` — nonlinear abstraction: refinement reached a fixpoint without deciding | 3 | 8 |
| **22** | `nra/budget` — N cross-products project to M linear-real atoms, past the consuming engine's capacity of 1,024 | 450 | 2 |
| **11** | `nra/budget` — lra: both engines declined, Fourier–Motzkin stopped on the deadline | 3 | 4 |
| **5** | `nra/budget` — lra: both engines declined, Fourier–Motzkin hit `MAX_FM_CONSTRAINTS` | 4 | 4 |
| 3 | killed mid-search in `nra-real-root` | 7 | 20 |
| 3 | `q:nat-induction/not-applicable` | 3 | 10 |
| 2 | killed mid-search in `dl-online` | 16,002 | 8 |
| 2 | `nra-real-root/not-applicable` | 20 | 11 |
| 2 | `nra/budget` — exact-rational simplex | 3 | 36 |
| 2 | `nra/budget` — refinement round bound reached | 4 | 5 |
| 2 | `nra/incomplete` — online CDCL(T) LRA model did not replay | 4 | 18 |
| 1 | `cas-ideal-refuter/incomplete` | 7 | 4 |
| 1 | no typed decline recorded (the one `abort` row) | 30,718 | 1 |

`bound_by` is `nra` on **71 of 83**: the linear-abstraction relaxation is where
this division's clock goes, on every bucket but four.

**The largest bucket is not the one the 2026-09-09 sweep named.** That sweep's
biggest class was the atom-capacity refusal (14 of 75); it is bucket 2 here
(22 of 83) and it is the `LassoRanker` ranking-function templates — hundreds to
thousands of variables, degree 2. Bucket 1 is 23 `meti-tarski` files plus 3
others, **3 variables and degree 3–20 in a single assertion**: the canonical
CAD shape, on which our own CAD (`nra_real_root::decide_component`) records
`not-applicable` and the query falls through to a linear relaxation that spins
to a fixpoint.

`nra-real-root/not-applicable` appears somewhere in the trail of **78 of the
83**.

## The shape reader lied twice before it was right

`shape-features.py` is a parser, not a grep, and it still got the division
column wrong twice. Both are recorded because the wrong answers were each
plausible enough to build a lane on:

1. **First reading: 40 of 83 "have division".** `(/ 9062500 7)` is a
   `meti-tarski` *coefficient literal*, not real division.
2. **Second reading: 31 of 83 "have symbolic division".** SMT-LIB has no
   negative numeral, so `-471/100` is written `(/ (- 471) 100)` — a LIST
   numerator. Testing `isinstance(a, str) and is_numeral(a)` on the operands
   called 29 `meti-tarski` files symbolic.
3. **Correct reading: 0 of 83, and 0 of all 200.** The column now asks whether
   the DENOMINATOR is a ground constant, which is the question
   `nra::eliminate_real_div` actually turns on. The last survivor,
   `20200911-Pine/1599121905450496000.smt2`, is `(/ (* u u u) 6.0)` — a
   polynomial over a constant, still no case split.

A whole "division elimination is the bucket" lane would have come out of
reading 1 or 2. `controls/` holds a satisfiable file that *does* divide by a
variable and one that divides by a constant, with the expected rows, so a
column that is zero across the population is still falsifiable.

## Files

| file | what |
|---|---|
| `undecided-83.txt` | the population, corpus-relative paths |
| `qfnra-200.txt` | the whole board list |
| `shape-features.py` | the s-expression shape reader |
| `shape-83.tsv` | its output for the 83 |
| `controls/` | positive + negative fixture for the division column |
| `census-run.sh` | one shard: files → `ledger-run-one.sh` → ledger rows |
| `census-classify.py` | ledger + shapes → buckets |
| `census-report.txt` | the full bucket tables |
| `census-83.tsv` | per-file join (bucket, terminal reason, shape) |
| `reference-trace.sh` | z3 (3 arms) + cvc5 engine attribution |
