# ADR-2124 -- incremental ground closure for quantifier instances

Lane `quant-ground-incremental`.  Artifacts, in the order they were produced.

| file | what it is |
|---|---|
| `SIZING-ledger.txt` | exit-1 sizing, per division, from `bench-results/ledger/t1-<DIV>-db31113fa.tsv` |
| `SIZING-cores.txt` | exit-1 sizing, per core, from `bench-results/quant-activation-20260915/cores/cores.tsv` |

`SIZING-cores.txt` states one absence explicitly: ADR-2120's per-core RAW capture
(`cores/raw/`) was not committed, so per-core `qf-check` WALL TIME is not
recoverable from the ledger.  Calls and ground-set size are.  Time is measured in
this lane's own 53-core probe and reported there.
