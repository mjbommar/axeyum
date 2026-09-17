| measure | A = `Any` (unset) | B = `AXEYUM_MODEL_PREFERENCE=zero` |
| --- | ---: | ---: |
| files | 200 | 200 |
| decided | 186 | 186 |
| sat / unsat | 57 / 129 | 57 / 129 |
| PAR-2 (ms, 24 s budget) | 4101 | 4189 |
| wall on the 186 both-decided files (ms) | 148204 | 165717 |
| both-decided files where the other arm is >10 % + 50 ms slower | B slower on 13 | A slower on 1 |

- raw gains (A undecided, B decided): 0
- raw losses (A decided, B undecided): 0
- sat/unsat flips between arms: 0
- `:status` disagreements (either arm, decided, against a declared sat/unsat): 0
- nonzero exit status rows: 0
- rows failing the timing-unit sanity check: 0
