# QF_UFLIA interface and admission ceilings, 2026-09-08

Data for the `uflia-after-reachability` lane. The writeup — what was measured,
why, and what changed — is
[`docs/research/12-performance/uflia-interface-caps-2026-09-08.md`](../../docs/research/12-performance/uflia-interface-caps-2026-09-08.md),
and the decision it sets is
[ADR-1801](../../docs/research/09-decisions/adr-1801-an-admission-bound-that-fires-on-every-lost-file-is-not-protecting-the-search.md).
Read those first; this directory is data, not narrative.

## What is here, and what is not

Each `*.summary.tsv` carries `#` header lines naming the binary's `sha256`, the
over-bound policy in force, and the host and load average at start, before the
column header (`file`, `wall_ms`, `verdict`). **The per-file raw `--trace`
output is NOT committed**: it is ~60 MB across the arms, and every claim the
writeup makes from it is reduced to a count in the writeup itself. It lives in
the lane's scratch (`.lane-uflia/<arm>/raw/<sha256-of-path>.txt`) and is
reproducible from the scripts below in one command per arm.

Every arm ran under the parity protocol — 24 s wall, 8 GiB `ulimit -v`, ONE FILE
AT A TIME — on an idle 16-core host, so the numbers are comparable to
`bench-results/PARITY.md`.

| file | what it is |
|---|---|
| `out-s5/6/7.summary.tsv` | the baseline: the committed 200-file division list under the lane's base commit, sharded three ways by `NR%3` |
| `loss50.txt` | the 50 files that baseline loses and `cvc5` solves — the population every arm below runs |
| `out-care.summary.tsv` | `care-truncate` alone, atom ceiling unchanged |
| `out-atoms-general.summary.tsv` | `MAX_BOOLEAN_ATOMS` raised alone (the opaque ceiling left at 128) |
| `out-atoms-probe.summary.tsv` | both atom ceilings raised, shipped `probe` over-bound policy |
| `out-atoms-skip.summary.tsv` | the same with `AXEYUM_UF_ARITH_OVERBOUND=skip` — a measurement arm, not shippable |
| `out-atoms-care-skip.summary.tsv` | both ceilings raised **and** `care-truncate`, under `skip` |
| `out-cand-a/b.summary.tsv` | the SHIPPED default over the whole 200-file list, two halves |

## The two numbers to read

- **`out-cand-a` + `out-cand-b` against the three baseline shards: 130 → 151
  decided, +23 / −2, zero disagreements.** That is the shipped change over the
  board's own population and denominator.
- **`out-atoms-care-skip` against the same baseline: 31 of the 50 losses
  decided.** That is what the same configuration reaches when the lazy CEGAR is
  not holding 18 s of the budget — i.e. the size of the dispatch-order question
  this lane did not take.

## Reproducing

```sh
# One arm. <policy> is the over-bound policy (omit for the shipped default).
scripts/sweep.sh <list.txt> <pinned binary> <outdir> [policy]

# The step-1 classification, against the committed reference verdicts.
scripts/classify.py <ref-solved.tsv> <outdir>…

# Any arm against a baseline. EXITS 1 ON A DISAGREEMENT, so a soundness break
# fails the run rather than appearing in a table.
scripts/compare.py <ref-solved.tsv> <base-dir>[,<dir>…] <arm-dir>…
```

`<ref-solved.tsv>` is two columns (path, reference verdict) derived from the
committed per-file detail of a board run; reference verdicts do not move between
runs, so re-running `cvc5` would only add noise.

`scripts/apply-defaults.py` is the source change ADR-1801 landed, kept as a
script so the diff is one reviewable object and every anchor is asserted to
occur exactly once — a moved anchor aborts rather than editing the wrong place.

## One thing this data cannot tell you

The two files the shipped default "loses" (`xs_16_26`, `hash_uns_05_20`) were
decided by the baseline at 25.0 and 25.1 s — past the 24 s internal budget, at
the harness watchdog. Neither reproduces: the BASE binary re-run on each returns
`unknown` four times out of four. Those re-runs are in the writeup, not here,
because they are eight invocations rather than a sweep. The `-2` is reported
anyway, because this lane did not re-run the whole baseline and a number that
would probably not survive a re-measurement is still the number this comparison
produced.
