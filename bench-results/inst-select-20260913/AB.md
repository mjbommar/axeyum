## A/B — `AXEYUM_QINST_SMALLEST_WITNESS` (ships OFF; `base` = shipped)

| division | n | base | arm | net | gain | loss | sat↔unsat flips | NONE base/arm |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| UFNIA | 200 | 53 | 53 | **+0** | 0 | 0 | 0 | 0/0 |
| UFLIA | 200 | 72 | 73 | **+1** | 1 | 0 | 0 | 0/0 |
| UF *(control)* | 200 | 89 | 89 | **+0** | 0 | 0 | 0 | 2/2 |

### Every moved row

- **GAIN** `UFLIA` `UFLIA/sledgehammer/Fundamental_Theorem_Algebra/smtlib.1057395.smt2` — base `unknown` (19027 ms), arm `unsat` (15120 ms), order `arm-first`, declared `:status unsat`

### sat↔unsat flips (a SOUNDNESS event, never a gain)

**0.** No row is decided differently by the two arms.

### Agreement with the declared `:status`, both arms

The comparable denominator is on the same line (ADR-1957): only files
that carry a declared status AND that the arm decided can be compared.

| division | base agree/comparable | arm agree/comparable | disagreements |
|---|---|---|---:|
| UFNIA | 14/14 | 14/14 | 0 |
| UFLIA | 72/72 | 73/73 | 0 |
| UF | 87/87 | 87/87 | 0 |

**DISAGREEMENTS: 0.**

### Wall-clock cost of the arm

The arm scans the witness pool per bound variable per joined
substitution, so a cost here is expected and is reported whether or
not it is convenient.

| division | median base ms | median arm ms | total base s | total arm s |
|---|---:|---:|---:|---:|
| UFNIA | 22928 | 22831 | 3205.6 | 3182.2 |
| UFLIA | 20127 | 21329 | 2858.4 | 2932.0 |
| UF | 12719 | 13925 | 2605.3 | 2735.8 |

**Target-division gain rate: 1/400, Wilson 95% [0.0%, 1.4%].**
