| measure | A = `single-cell` (shipped) | B = `algebraic-witness` |
| --- | ---: | ---: |
| files | 200 | 200 |
| decided | 109 | 109 |
| sat / unsat | 52 / 57 | 52 / 57 |
| PAR-2 (ms, 24 s budget) | 22176 | 22186 |
| wall on the 109 both-decided files (ms) | 67258 | 69157 |

- delta (B - A decided): +0
- raw gains (A undecided, B decided): 0
- raw losses (A decided, B undecided): 0
- sat/unsat flips between arms: 0
- `:status` disagreements (either arm, decided, against a declared sat/unsat): 0 over 216 comparable verdicts
- arm runs without a verdict token: 0
- nonzero exit status rows: 0
- rows failing the timing unit sanity check: 0
