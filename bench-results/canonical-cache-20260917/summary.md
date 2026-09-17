| measure | A = cache off (unset) | B = `AXEYUM_CANONICAL_CACHE=on` |
| --- | ---: | ---: |
| files | 200 | 200 |
| decided | 187 | 187 |
| sat / unsat | 58 / 129 | 58 / 129 |
| PAR-2 (ms, 24 s budget) | 3852 | 3851 |
| wall on the 187 both-decided files (ms) | 146317 | 146201 |
| both-decided files where the other arm is >10 % + 50 ms slower | B slower on 1 | A slower on 1 |

- raw gains (A undecided, B decided): 0
- raw losses (A decided, B undecided): 0
- sat/unsat flips between arms: 0
- `:status` disagreements (either arm, decided, against a declared sat/unsat): 0
- nonzero exit status rows: 0
- rows failing the timing-unit sanity check: 0
