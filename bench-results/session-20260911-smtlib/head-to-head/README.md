# axeyum vs z3 vs cvc5 — one box, one problem at a time

**2026-09-11/12.** 3,200 files, 16 divisions, 9,600 solves.

    axeyum  2,309 / 3,200  (72.2%)
    z3      2,790 / 3,200  (87.2%)
    cvc5    2,652 / 3,200  (82.9%)

## Why this exists

`bench-results/PARITY.md` measures each division against its SMT-COMP **leader**
(ADR-1732) — cvc5 for twelve divisions, bitwuzla for three, Z3 for one. That is
the right question per row ("how close are we to the best here") and the wrong
one across rows: the denominator is a different solver in different rows, so no
cross-division total from it is valid. An aggregate quoted that way ("86.1% of
the reference") was exactly that mistake.

This table has one numerator and one denominator per solver.

## Protocol

- **One box** (s6), serial. No two solves ever overlap.
- **Chosen by measurement**: same compute-bound probe, 7 runs, pinned, quiet —
  s6 5.569 s median / 0.51% spread; s4 5.814 / 0.68% but a HYBRID CPU where this
  repo has measured a 1.84x penalty on E-cores; s7 5.811 / 1.10%; s5 discarded
  after a stray cvc5 was found running.
- **Interleaved per problem**: all three solvers finish file N before any starts
  N+1, so drift hits all three equally.
- **Rotating order** (`i mod 3`): no solver systematically gets the cold cache.
- Same core set, same 24 s / 8 GiB. Units differ and are set accordingly:
  z3 `-T:` SECONDS, cvc5 `--tlimit` MILLISECONDS.
- **Live probe per solver before any measurement** — each had to DECIDE a known
  file. z3 was absent on one host earlier that day and 800 files scored a silent
  0/200 that read exactly like a result.

Runner: `scripts/fair-head-to-head.sh`. axeyum at `1446a809c`.

## Results

| division | axeyum | z3 | cvc5 |
|---|---|---|---|
| QF_UF | **200** | 200 | 200 |
| QF_FP | **199** | 199 | 199 |
| QF_SLIA | **193** | 187 | 194 |
| QF_BV | **186** | 184 | 185 |
| QF_ABV | 186 | **195** | 182 |
| QF_S | 186 | 196 | **197** |
| QF_UFLIA | 162 | **186** | 180 |
| QF_RDL | 152 | **166** | 154 |
| QF_UFLRA | 144 | **198** | 197 |
| QF_LIA | 119 | **172** | 139 |
| QF_NRA | 117 | **187** | 186 |
| QF_DT | 114 | **192** | 192 |
| QF_IDL | 113 | **140** | 122 |
| QF_LRA | 107 | **166** | 145 |
| **UF** | **90** | 78 | **93** |
| QF_NIA | 41 | **144** | 87 |
| **TOTAL** | **2,309** | **2,790** | **2,652** |

We lead z3 on QF_SLIA, QF_BV and **UF** (90–78); cvc5 on QF_BV, QF_ABV, QF_UF.

## Read it with these caveats

- **200 files per division is a SAMPLE.** The divisions average 17,891 files;
  3,200 is **0.73% of the 438,631-file corpus**.
- **16 of 84 divisions.** 68 have never been run. By file count the measured
  divisions are 65% of the corpus, because they include several of the largest.
- **Plain invocations, no competition portfolio.** SMT-COMP runs cvc5 with
  `--finite-model-find` among others — precisely what wins the UF files our own
  FMF work wins. Both references are therefore running below their competition
  configuration.
- `QF_UFLRA` reads 144 here against the board's 142 on a different host and a
  separately built binary — two apart, which is the run-to-run noise floor.
