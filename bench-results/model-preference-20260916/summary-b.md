| measure | A = `Any` (unset) | B = `AXEYUM_MODEL_PREFERENCE=zero` |
| --- | ---: | ---: |
| files | 200 | 200 |
| decided | 186 | 186 |
| sat / unsat | 57 / 129 | 56 / 130 |
| PAR-2 (ms, 24 s budget) | 4106 | 4302 |
| wall on the 185 both-decided files (ms) | 147933 | 188236 |
| both-decided files where the other arm is >10 % + 50 ms slower | B slower on 25 | A slower on 4 |

- raw gains (A undecided, B decided): 1
- raw losses (A decided, B undecided): 1
- sat/unsat flips between arms: 0
- `:status` disagreements (either arm, decided, against a declared sat/unsat): 0
- nonzero exit status rows: 0
- rows failing the timing-unit sanity check: 0
  - GAIN QF_BV/bruttomesso/core/ext_con_008_001_0064.smt2: A=unknown/24117ms B=unsat/108ms
  - LOSS QF_BV/Sage2/bench_12354.smt2: A=sat/1309ms B=unknown/24123ms
