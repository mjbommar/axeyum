## M3 -- our baseline, re-derived on this lane's base

| division | list rows | we now DECIDE | still undecided | ground dumps |
|---|---:|---:|---:|---:|
| UFNIA | 61 | 1 | 60 | 44 |
| UFLIA | 68 | 1 | 67 | 62 |

**Rows this base decides that the snapshot list calls winnable:**

- `UFNIA/sledgehammer/FFT/z3.885941.smt2` — `unsat` in 2310 ms
- `UFLIA/simplify/javafe.parser.TokenQueue.576.smt2` — `unsat` in 21231 ms

### Blocker families, and ADR-1941 classification


**UFNIA** — 60 undecided

- rows carrying a `route-open` segment (ADR-1941 UNCLASSIFIED): **8**
- the `attempts=`-only reading, for comparison: max `attempts=108`, 59 rows below it

| family | rows |
|---|---:|
| ladder CLOCK exhausted | 21 |
| e-matching instantiation CLOCK | 18 |
| watchdog fired before the worker thread returned | 8 |
| instantiation is satisfiable; the universal may still be violated outs | 2 |
| ingest resource limit: `distinct` with 1571 arguments requires 1233235 | 2 |
| parse error: syntax error: fp exponent field must be a bit-vector | 2 |
| no model within the bounded integer width 32; widen the bound | 1 |
| ingest resource limit: `distinct` with 380 arguments requires 72010 pa | 1 |
| preprocessed dispatch timeout after reduced solve; the reduced solve's | 1 |
| e-matching FIXPOINT | 1 |
| ingest resource limit: `distinct` with 422 arguments requires 88831 pa | 1 |
| instantiation ROUND budget | 1 |
| mbqi declined an unsupported fragment: term #0 has sort (Uninterpreted | 1 |

| `bound_by` | rows |
|---|---:|
| `q:egraph` | 25 |
| `q:mbqi` | 19 |
| `fd:parse` | 6 |
| `q:forall-exists-witness` | 4 |
| `uf-arithmetic` | 2 |
| `q:ground-subset` | 2 |
| `q:mbqi-quick` | 2 |

**UFLIA** — 67 undecided

- rows carrying a `route-open` segment (ADR-1941 UNCLASSIFIED): **23**
- the `attempts=`-only reading, for comparison: max `attempts=20`, 60 rows below it

| family | rows |
|---|---:|
| ladder CLOCK exhausted | 23 |
| watchdog fired before the worker thread returned | 23 |
| e-matching instantiation CLOCK | 14 |
| mbqi declined an unsupported fragment: term #0 has sort (Uninterpreted | 4 |
| e-matching: no universal is asserted; the nested quantifiers present a | 1 |
| query has quantifiers instantiation does not reach (nested, existentia | 1 |
| e-matching GROWTH-HEADROOM | 1 |

| `bound_by` | rows |
|---|---:|
| `q:egraph` | 36 |
| `q:mbqi-quick` | 22 |
| `q:mbqi` | 6 |
| `q:forall-exists-witness` | 3 |
