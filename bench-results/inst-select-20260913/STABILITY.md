## Three independent A/B passes — `UFLIA`

200 files present in all 3 passes (of 200 seen).

| pass | base decided | arm decided | net |
|---|---:|---:|---:|
| 1 | 72 | 73 | +1 |
| 2 | 75 | 73 | -2 |
| 3 | 74 | 74 | +0 |

**Base-arm totals: 72 / 75 / 74 — BAND 3 files.**
**Arm totals: 73 / 73 / 74 — BAND 1 files.**

**Files that disagree with themselves across passes: base 3, arm 2.**

This is the number a single-pass A/B cannot see, and it is the
denominator any claimed gain or loss has to clear.

### Every row that moved in ANY pass (3)

- **UNSTABLE** `UFLIA/simplify/javafe.parser.TokenQueue.576.smt2`
  - base: unknown, unsat, unsat
  - arm:  unknown, unknown, unknown
- **UNSTABLE** `UFLIA/sledgehammer/FFT/smtlib.1015458.smt2`
  - base: unknown, unsat, unknown
  - arm:  unknown, unknown, unknown
- **UNSTABLE** `UFLIA/sledgehammer/Fundamental_Theorem_Algebra/smtlib.1057395.smt2`
  - base: unknown, unknown, unknown
  - arm:  unsat, unknown, unsat

**{'UNSTABLE': 3}**

**sat↔unsat flips across all passes: 0.**
