| measure | A = `single-cell` (shipped) | B = `algebraic-witness` |
| --- | ---: | ---: |
| files | 200 | 200 |
| decided | 124 | 128 |
| sat / unsat | 55 / 69 | 59 / 69 |
| PAR-2 (ms, 24 s budget) | 18832 | 17872 |
| wall on the 124 both-decided files (ms) | 118460 | 117771 |

- delta (B - A decided): +4
- raw gains (A undecided, B decided): 4
    - QF_NRA/meti-tarski/atan/problem/2/weak/atan-problem-2-weak-chunk-0089.smt2  A=unknown@14214ms  B=sat@206ms
    - QF_NRA/meti-tarski/atan/problem/2/weak/atan-problem-2-weak-chunk-0018.smt2  A=unknown@18918ms  B=sat@105ms
    - QF_NRA/meti-tarski/atan/problem/2/atan-problem-2-chunk-0014.smt2  A=unknown@12413ms  B=sat@105ms
    - QF_NRA/meti-tarski/atan/problem/2/weak/atan-problem-2-weak-chunk-0159.smt2  A=unknown@13513ms  B=sat@206ms
- raw losses (A decided, B undecided): 0
- sat/unsat flips between arms: 0
- `:status` disagreements (either arm, decided, against a declared sat/unsat): 0 over 250 comparable verdicts
- arm runs without a verdict token: 0
- nonzero exit status rows: 0
- rows failing the timing unit sanity check: 0
