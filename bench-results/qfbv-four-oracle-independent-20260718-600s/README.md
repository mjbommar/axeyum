# ADR-0237 accepted four-oracle QF_BV campaign

This is the accepted artifact for the preregistered independent/edge-directed
QF_BV correctness campaign. It was produced from Axeyum
`dde00eab546bd0689be1f4c799dd23f52d0df58a` by the committed
`scripts/run-qfbv-independent-oracle-rounds.sh` protocol.

## Result

| Round | Profile | Seeds | Four-way agree | SAT replay |
|---|---|---:|---:|---:|
| `uniform-a` | `uniform-v1` | 1,000,000..1,004,000 | 4,000/4,000 | 1,432/1,432 |
| `uniform-b` | `uniform-v1` | 2,000,000..2,004,000 | 4,000/4,000 | 1,501/1,501 |
| `edge-c` | `edge-v1` | 3,000,000..3,004,000 | 4,000/4,000 | 1,538/1,538 |
| **Total** | | | **12,000/12,000** | **4,471/4,471** |

Every row decided identically in Axeyum, direct Z3, cvc5 1.3.4, and Bitwuzla
0.9.1. There were zero unknowns, timeouts, crashes, parser/process failures,
replay indeterminacies, or SAT/UNSAT disagreements. Every round covered all
five declared widths and all 35 generator/operator classes.

The edge round also passed executable non-vacuity gates for all 14 declared
semantic-corner families. Frequencies range from 250 instances for signed
division overflow to 3,128 for a literal zero; exact values are in
`aggregate.json` and `edge-c.json`.

## Resource and claim boundary

The correctness runner uses an explicit 600,000 ms per-engine per-row ceiling.
This ceiling was necessary for retained seed 3,000,881, a nested division/
remainder formula that all four engines ultimately classify UNSAT. The raw
campaign timings are sequential, loaded, and dominated by this row; they are
**not performance evidence**.

The result supports bounded four-engine verdict agreement and measured
semantic-corner coverage over these exact 12,000 formulas. It does not prove
QF_BV completeness, exhaust arbitrary widths/depths/interactions, or replace
consumer-state regressions, real Glaurung proof manifests, and authoritative
finding-parity tests.

## Reproducibility

`environment.txt` records exact oracle executable hashes and versions. Each
round has a machine-readable v3 JSON report and raw process log. The aggregate
file is a direct sum of those three reports. Rejected 5-second, 2-second, and
30-second attempts are retained in sibling artifact directories rather than
silently discarded.

SHA-256 of the primary reports before adding this README/aggregate:

- `uniform-a.json`: `14ffa9c178b3135fb8c00e63bdba78438f17cfeac85a1bfd43839d9bb5dd7d3c`
- `uniform-b.json`: `87f6e54cb6a2d79c29ccdb10a81cde30e6925d436e83fc24f785a233c8c6d304`
- `edge-c.json`: `04960f870fcaf64d65f8d357f560cf1ba276f35ea69f763350780aed920f6564`
