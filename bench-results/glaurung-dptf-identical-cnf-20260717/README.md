# Dptf retained-CNF cross-core control

- Date: 2026-07-17
- Glaurung capture base: `403a5c5c1f6c5152fef6cefd0d78c3eb90d3888f`
- Glaurung snapshot implementation: `f265254` (the measured precursor differs
  only by adding the process ID to generated filenames)
- Axeyum capture base: `9334fdda`
- Driver SHA-256:
  `074be1b90deb21897538a6b093af9826e62610ffd878c92289af31c5ca3f724b`
- Host: `server0`, x86_64, Linux 7.0.0-27-generic
- Repetitions: 5 fresh imports/solves per CNF and core
- Report SHA-256:
  `91741e81cf0138aef36a9a63c3024ac53c6c2c05fe80a348194a0449c1cca9d7`

The opt-in Glaurung capture materializes the retained incremental input-clause
database plus the exact active selector assumptions as unit clauses after each
warm `unsat`. Learned clauses are deliberately excluded. The result is a
standalone stable problem that every fresh core consumes byte-for-byte.

The capture produced 244 snapshots, covering every Axeyum `unsat` in the
561-check Dptf diagnostic run. DIMACS metadata and headers agree exactly; sizes
range from 3 to 39,566 variables and 5 to 70,665 clauses. BatSat, Axeyum's
proof-producing core, Z3's Boolean engine, and Kissat 4.0.4 all return `unsat`
on every snapshot in every repetition.

## Timing interpretation

| Core cell | Sum of per-instance medians | Median instance | 95th percentile |
|---|---:|---:|---:|
| BatSat fresh import+solve | 541.366 ms | 2.058 ms | 5.052 ms |
| Axeyum proof-core generation | 220.913 ms | 0.714 ms | 2.254 ms |
| Axeyum proof generation+self-recheck | 816.789 ms | 2.044 ms | 11.328 ms |
| Z3 fresh Boolean import+solve | 12,649.858 ms | 40.697 ms | 124.800 ms |
| Kissat 4.0.4 subprocess | 1,849.164 ms | 7.425 ms | 13.988 ms |

The geometric mean of per-instance BatSat/proof-core medians is 2.627x: the
proof-producing core is faster before checking on this exact UNSAT slice.
Including independent DRAT recheck changes BatSat/rechecked-proof to 0.911x,
roughly parity by median ratio with higher proof-check cost on large instances.

Z3 and Kissat numbers are controls, not a neutral speed headline. Z3 includes
fresh Boolean AST construction and assertion; Kissat includes process startup.
Neither reproduces the retained learned state used by the warm end-to-end
engines. Their value here is exact verdict agreement and rejection of the
hypothesis that Z3's fresh core simply searches Axeyum's retained CNF faster.
The remaining warm boundary is retained learned state, topology, and solver
integration. A persistent clause-stream control is required before core tuning
or a causal cross-solver claim.

[`report.json`](report.json) contains every input SHA-256, variable/clause
count, verdict, and raw duration. The 112 MiB access-controlled DIMACS pack
remains outside git at the input path recorded in the report.
