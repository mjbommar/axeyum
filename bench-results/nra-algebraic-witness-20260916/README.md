# ADR-2134 — the algebraic witness, and what the sizing actually says

Lane `NRA-ALGEBRAIC-WITNESS`, 2026-09-16. Baseline binary built from `main` at
`863694052`, SHA in `baseline-binary-sha256.txt`. Corpus root
`/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental`, budget
24 s, `ulimit -v` 8 GiB, host `s5`, cores `5,13` and `6,14`.

## 1. Sizing — the ceiling, measured before any code was written

`cause-scan.sh` runs each file of the pinned 200 (`qfnra-200.txt`, derived from
`bench-results/board-ab-20260915/QF_NRA.tsv` and verified identical to the
prior lane's draw) with `--trace` and reads the `nra-real-root` rung's own
recorded cause.

`cause-single-cell-200.tsv` — the **shipped default** arm:

| cause | files |
| --- | ---: |
| `non-conjunctive` | 118 |
| `slice-bounds` | 28 |
| DECIDED | 19 |
| `coefficient-range` | 7 |
| **`algebraic-witness`** | **7** |
| no `nra-real-root` attempt | 5 |
| `projection-resultant-zero` | 4 |
| `certificate-rejected` | 4 |
| `root-ordering` | 2 |
| `root-isolation` | 2 |
| `projection-sylvester-dim` | 1 |
| `projection-arithmetic` | 1 |
| `nullified-residual` | 1 |
| `not-attempted` | 1 |

**`algebraic-witness` = 7 of 200.** Six of the seven files are currently
`unknown`; one is already `sat` from a later rung. So the ceiling for *movers*
from this lever alone is **6**, not 7 — a file the ladder already decides cannot
be gained twice.

The seven, with their current verdict:

| verdict | file |
| --- | --- |
| unknown | `QF_NRA/meti-tarski/atan/problem/2/atan-problem-2-chunk-0014.smt2` |
| unknown | `QF_NRA/meti-tarski/exp/problem/10/2/exp-problem-10-2-chunk-0017.smt2` |
| unknown | `QF_NRA/meti-tarski/exp/problem/10/3/exp-problem-10-3-chunk-0139.smt2` |
| unknown | `QF_NRA/meti-tarski/exp/problem/10/3/weak/exp-problem-10-3-weak-chunk-0142.smt2` |
| unknown | `QF_NRA/meti-tarski/sin/cos/sin-cos-346-b-chunk-0291.smt2` |
| unknown | `QF_NRA/meti-tarski/sin/problem/8/weak/sin-problem-8-weak-chunk-0050.smt2` |
| sat | `QF_NRA/meti-tarski/sqrt/1mcosq/7/sqrt-1mcosq-7-chunk-0070.smt2` |

This triangulates with the two earlier estimates rather than replacing them:
ADR-2126 counted 6 of 24 *in-bounds* files, ADR-2131 counted 5 of 16
*admissible* files. Different denominators, same order of magnitude.

### 1b. Behind `non-conjunctive`, via the clause loop's slot

`cause-clause-loop-200.tsv` is the same scan on the `clause-loop` arm, which is
ADR-2126's route (`single-cell-sat` + the Boolean loop):

| cause | single-cell | clause-loop |
| --- | ---: | ---: |
| `non-conjunctive` | 118 | 109 |
| DECIDED | 19 | 24 |
| `unsat-withheld-by-arm` | 0 | 8 |
| `certificate-rejected` | 4 | 0 |
| **`algebraic-witness`** | **7** | **7** |

The loop absorbs 9 of the `non-conjunctive` files and decides 5 more, and it
moves the `algebraic-witness` bucket by **zero**.

**Read that null carefully — it is weaker than it looks.** `record_cad_decline`
keeps the FIRST cause recorded and ignores later ones, and the clause loop runs
only *after* the conjunctive route has already recorded `non-conjunctive`. So an
`algebraic-witness` decline arising *inside* the loop is masked by the cause
already in the slot. The honest statement is: **the terminal cause is
`algebraic-witness` for 7 files on both arms, and the 109 `non-conjunctive` rows
are an upper bound that may hide some.** This scan cannot distinguish those two
worlds, and no number here should be quoted as if it could.

## 2. What was built

* `RealAlgebraic::sign_at` was reading two endpoint SAMPLES as an enclosure of a
  polynomial's range, which is a wrong sign whenever the polynomial has an even
  number of roots inside the bracket. Fixed with an exact Sturm root count
  (`poly_big::RootCounter`). Not behind any lever — see §3.
* `CadPolicy::ALGEBRAIC_WITNESS`, one field apart from the shipped
  `SINGLE_CELL`: a cell whose representative point is an irrational root is
  accepted as the FINAL coordinate of a model, subject to the exact replay.
* `(root-obj p k)` model printing, over a squarefree/primitive/positive-leading
  polynomial so equal values print identically.

## 3. Two things to price, two kinds of A/B

The `algebraic-witness` arm is env-selectable, so it is priced the usual way:
one binary, two env values, interleaved per file.

The `sign_at` exactness fix is **not** behind a lever and cannot be — a wrong
sign in the trusted evaluator is not something to ship as an option. Pricing it
therefore needs the old binary against the new one at the SAME arm, which is
what `ab-run.sh --binary-a` exists for. The fix can only turn an answer into a
decline (it rejects accepts the endpoint test used to make; it never changes a
sign that was already right), so the question it has to answer is how many
verdicts that costs.

## 4. Reproducing

```sh
# sizing
./cause-scan.sh --binary <smtcomp_cli> --list qfnra-200.txt \
    --arm single-cell --out cause-single-cell-200.tsv --core 5,13

# the lever's A/B (one binary, two env values)
./ab-run.sh --binary <new> --list qfnra-200.txt --shard 0 --core 5,13 \
    --arm-a single-cell --arm-b algebraic-witness --out ab-qfnra-shard0.tsv

# the exactness fix's A/B (two binaries, same arm)
./ab-run.sh --binary <new> --binary-a <baseline> --list qfnra-200.txt \
    --shard 0 --core 5,13 --arm-a single-cell --arm-b single-cell \
    --out exactness-qfnra-shard0.tsv
```

## 5. A harness incident worth recording

The first sizing run launched `drive.sh 1` twice: a backgrounded `ssh` whose
launch had not visibly taken effect was retried, and both copies then wrote the
same output files. It was caught because `cause-single-cell-shard1.tsv` went
BACKWARDS, from 101 rows to 52 — a duplicate had truncated it and was rewriting
it. The complete first-run outputs had already been copied off and are what this
directory contains; the `clause-loop` files were rescued before the duplicate
reached them.

The rule this instance teaches: **a sweep output file must not be a fixed name
that two runs of the same command both write**, and a row count that decreases
is the cheapest possible detector for it. Checking `pgrep` after a launch says
whether *a* process is running, not whether *exactly one* is.
