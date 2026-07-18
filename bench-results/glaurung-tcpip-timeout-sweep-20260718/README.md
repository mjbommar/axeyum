# Glaurung tcpip QF_BV timeout-frontier sweep

Status: accepted one-shot timeout-sensitivity control

This bundle answers the reviewer checklist's solved-population and timeout-
sensitivity question on the exact 52-formula post-concat-fix tcpip shadow-split
frontier. It does **not** replay the full ordered Glaurung stream and does not
measure sole-backend finding authority.

## Contract

- Axeyum source: clean `befe1ba4aa92336c7f2364dd3aa80aec7abc5a57`
- corpus manifest:
  `sha256:ae75f19e65e161bce76e2926c9b63a904376ab249ad4d8b1c2566877fa4af4ef`
- exact work: the same 52 content-hashed `QF_BV` files at 50, 100, 250, and
  1000 ms
- repetition boundary: five fresh CPU-3-pinned `axeyum-bench` processes per
  timeout, one solver worker and one manifest worker
- Axeyum/Z3 boundary: cold solve of the same original parsed assertions;
  in-process Z3 is always run, including after an Axeyum `unknown`
- neutral boundary: cvc5 1.3.4, fresh subprocess per exact SMT-LIB file, five
  repetitions per timeout; wall time includes startup, parsing, solving, and
  model output and is not divided into the in-process ratio
- verdict gate: every decided result must match the manifest; any process,
  parse, replay, error, or SAT/UNSAT contradiction fails the analysis
- timing gate: paired latency includes only queries both Axeyum and Z3 decide
  in **every** repetition at that timeout

The source formulas remain in Glaurung's access-controlled capture and are not
duplicated here. The manifest hash and each per-file content hash bind the
inputs.

## Result

All 20 Axeyum/Z3 artifacts and all 1,040 cvc5 rows pass. There are zero
operational errors, replay failures, decided disagreements, or cross-solver
SAT/UNSAT contradictions.

| timeout | Axeyum decided | Z3 decided | cvc5 decided | A/Z populations: both / A-only / Z-only / neither | fixed paired queries | Axeyum/Z3 geomean [bootstrap 95% CI] |
|---:|---:|---:|---:|---:|---:|---:|
| 50 ms | 28 | 13 | 46 | 13 / 15 / 0 / 24 | 13 | 0.14165 [0.11136, 0.19907] |
| 100 ms | 30 | 25 | 51 | 25 / 5 / 0 / 22 | 25 | 0.14548 [0.10539, 0.21313] |
| 250 ms | 41 | 33--34 | 52 | 30 / 11 / 3--4 / 7--8 | 30 | 0.14112 [0.09622, 0.21343] |
| 1000 ms | 52 | 52 | 52 | 52 / 0 / 0 / 0 | 52 | 0.21095 [0.14904, 0.29644] |

Ratio direction is Axeyum/Z3, so values below one favor Axeyum. The per-run
paired-geomean CV is 0.12--0.35%. Axeyum's decided population is stable at
every tier. Z3 has one boundary-sensitive 250 ms query, deciding it in four of
five runs; the fixed paired set excludes that query. cvc5's decided population
is stable in this pinned run and reaches all 52 rows by 250 ms.

At 1000 ms every query is paired, so selection by decided subset disappears:
Axeyum's cold one-shot latency is 0.21095x Z3 by per-query geomean on this exact
corpus. This establishes an Axeyum-winning **cold, deduplicated tcpip formula
regime**. It does not establish a universal solver ranking or explain how much
of the difference comes from FFI/context setup, representation, or search.
ADR-0215/0217 remain the fair retained-warm Glaurung performance map.

## Artifacts

- [`analysis.json`](analysis.json) is the fail-closed joined result, including
  input hashes, per-timeout population variance, drift paths, deterministic
  bootstrap intervals, quantiles, and CDF samples.
- [`summary.csv`](summary.csv) is a compact plotting table derived from the
  accepted analysis.
- [`raw/`](raw/) contains 20 artifact-v32 Axeyum/Z3 reports and the complete
  cvc5 sweep report.

The accepted commands were equivalent to:

```sh
for timeout_ms in 50 100 250 1000; do
  for repetition in 1 2 3 4 5; do
    taskset -c 3 target/release/axeyum-bench CORPUS \
      --corpus-manifest MANIFEST --corpus-tier diagnostic \
      --backend sat-bv --rewrite off --compare-z3 --require-in-process-z3 \
      --require-reproducible-run --timeout-ms "$timeout_ms" \
      --jobs 1 --manifest-jobs 1 --logic QF_BV \
      --out "raw/axeyum-z3-${timeout_ms}ms-run-${repetition}.json"
  done
done

taskset -c 3 target/release/examples/cvc5_qfbv_timeout_sweep \
  CORPUS MANIFEST CVC5 raw/cvc5-sweep.json 5 50,100,250,1000

python3 scripts/analyze-qfbv-timeout-sweep.py \
  --cvc5 raw/cvc5-sweep.json --out analysis.json \
  raw/axeyum-z3-*.json
```

## Limits and next step

The 52 rows are deduplicated formulas selected because one backend had timed
out at the historical 250 ms boundary. They are intentionally a hard-frontier
diagnostic, not a representative frequency-weighted driver distribution. The
run has no retained lineage, warm/cold fallback class, exploration order,
model-choice effect, or finding set.

This closes the timeout-sensitive neutral **formula** control. The next
publication tasks are the wider/timeout-sensitive sole-authority finding tier,
deadline-aware term-to-CNF faithfulness on real queries, independent fuzz seeds
plus another neutral implementation, and whole-certificate process isolation.
