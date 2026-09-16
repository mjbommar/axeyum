# ADR-2124 -- incremental ground closure for quantifier instances

Lane `quant-ground-incremental`.  Artifacts, in the order they were produced.

| file | what it is |
|---|---|
| `SIZING-ledger.txt` | exit-1 sizing, per division, from `bench-results/ledger/t1-<DIV>-db31113fa.tsv` |
| `SIZING-cores.txt` | exit-1 sizing, per core, from `bench-results/quant-activation-20260915/cores/cores.tsv` |
| `build.sh` | builds this lane's binary and refuses it unless it is NEWER than every `crates/**/*.rs` |
| `cores53.paths` | ADR-2113's 53 reference-minimal UFLIA cores, resolved against the corpus |
| `cores-launch.sh` / `cores-pair.sh` | the 53-core probe: both arms of each file back to back on one pinned core |
| `cores-summarize.py` | reads the probe into one row per core; **its exit status is 1 on a `sat`/`unsat` flip** |
| `cores/cores.tsv` | one row per core, both arms |
| `cores/CORES-SUMMARY.txt` | the probe's own report |
| `cores/raw.tar.gz` | **the raw per-core capture**, `tar xzf` it to get `raw/<core>.<arm>.{out,err}` |
| `ab-self-check.sh` | refuses the A/B unless the two arms resolve DIFFERENT configurations and arm B's own line names the override |
| `ab-launch.sh` / `ab-run.sh` | the six-division A/B, one binary at two env values, interleaved per file |
| `ab-summarize.py` | reads the A/B shards |
| `recheck-movers.sh` | re-runs the movers 3x to separate a stable move from load |

## Two things this directory does deliberately

**The raw capture is committed.**  ADR-2120 did not commit `cores/raw/`, and the
consequence landed on this lane: per-core `qf-check` WALL TIME was not
recoverable from its ledger, so §3.2 of the ADR has to state that absence rather
than quote a number, and the probe had to be re-run to get it.  216 KB gzipped is
cheaper than a re-run.

**`SIZING-cores.txt` states an absence rather than printing a zero.**  Where a
number could not be recovered it says so and names why.  A census that prints 0
for "not measured" is indistinguishable from one that measured 0.

## Reproducing

```sh
bash build.sh lane                         # on a host with the checkout
bash cores-launch.sh cores53.paths <outdir> <bin> 24
python3 cores-summarize.py <outdir>        # exit 1 on a verdict flip
bash ab-launch.sh 1 "s6:1,9 s6:3,11 s6:5,13 s6:6,14" 24
```

The lever is `AXEYUM_QINST_GROUND_SESSION`; unset is the shipped arm and an
explicit `0` is **not** the same path through `cap_lever!`, so the A/B's arm A
unsets it rather than setting it to `0`.
