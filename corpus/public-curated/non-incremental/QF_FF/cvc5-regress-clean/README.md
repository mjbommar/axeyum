# QF_FF curated slice (committed, reproducible)

Curated, **committed** SMT-LIB `QF_FF` (quantifier-free finite fields) slice for
the measured head-to-head of `axeyum_solver::check_auto` (`--backend solver`)
against the Z3 4.13.3 binary — the first measurement of a **genuinely new Z3/cvc5
theory** that axeyum previously lacked entirely. Finite fields `GF(p)` are modeled
as **modular bit-vector arithmetic** (the finite-modeling pattern that opened
uninterpreted sorts, Sets, Strings, and Sequences): `(_ FiniteField p)` →
`BitVec(w)` with `w = ceil(log2 p)`, a `bvult var p` well-formedness constraint at
declaration, and field ops as mod-`p` BV arithmetic — fully bit-blasted, so SAT
and UNSAT are both complete for any prime within the width cap.

- `./` — the **30** clean `(set-logic QF_FF)` files from the cvc5 regression suite
  (`references/cvc5/test/regress`, a gitignored shallow clone), filtered to plain
  `assert`/`check-sat` (no `push`/`pop`, `get-value`, `check-sat-assuming`, …).

```sh
target/release/axeyum-bench \
  corpus/public-curated/non-incremental/QF_FF/cvc5-regress-clean \
  --logic QF_FF --backend solver --compare-z3 --timeout-ms 10000 --jobs 4 \
  --out bench-results/baselines/qf-ff-cvc5-regress-clean-solver-vs-z3-10s.json
```

## The GF(p) → modular-BitVec encoding (axeyum-smtlib)

A field element of `GF(p)` is the bit-vector holding its canonical residue
`0 ≤ v < p` (width `w = ff_width(p) = ceil(log2 p)`). The encoding is
denotation-preserving — every operation is reduced to a canonical residue `< p`,
so `bv = bv` iff the field elements are equal, and the modular arithmetic matches
`GF(p)` verbatim:

| Form | Encoding |
|---|---|
| `(_ FiniteField p)` | `BitVec(ff_width(p))` |
| field symbol `(declare-fun x () (_ FiniteField p))` | fresh `BitVec(w)` **+ `bvult x p`** asserted at declaration (domain = exactly `GF(p)`) |
| literal `#fKmM` / `(as ffK F)` | `(_ bv (K mod M) w)` (K may be negative; residue in `0..M`) |
| `ff.add x y …` | `(x + y + …) mod p` — add in width `w+1`, one conditional subtract `ite(sum ≥ p, sum − p, sum)` |
| `ff.neg x` | `ite(x = 0, 0, p − x)` |
| `ff.mul x y …` | `(x · y · …) mod p` — `2w`-bit product, then `bvurem` by `p` |
| `ff.bitsum x …` | `Σ 2^i · x_i mod p` (cvc5 extension; positional weighted sum) |
| `=` / `distinct` | plain BV `=` (residues are canonical `< p`, so equality is exact) |

**Soundness:** the `bvult x p` well-formedness constraint makes the modeled BV
domain *exactly* the `p` field elements, and each op recomputes a canonical residue
`< p`, so no wrong sat/unsat is possible. The binding gate is the `--compare-z3`
head-to-head (below): **DISAGREE = 0** on every decided file, including every UNSAT.

**Width cap (decline-don't-guess):** only primes whose modeling width fits
`MAX_FF_PRIME_BITS = 16` are bit-blasted (the heaviest op, `ff.mul`, forms a `2w`
product). A larger (crypto-sized) prime, a modulus that overflows `u128`, or a
non-prime "field" (invalid SMT-LIB) makes the whole script a clean `Unsupported`
(→ `unknown`) — never a wrong or heavy result.

## Measured baseline (`--backend solver --compare-z3 --timeout-ms 10000`)

| metric | value |
|---|---|
| files | 30 |
| decided | **24** (sat 14, unsat 10) |
| unknown | 0 |
| unsupported | **6** (declined by the width cap) |
| errors | 0 |
| Z3-oracle compared | 24 |
| Z3-oracle **agree** | **24** |
| Z3-oracle **DISAGREE** | **0** |
| model-replay failures | 0 |
| PAR-2 mean (s) | ~0.01 |

**Prime-size cutoff is clean and exactly as designed:** every decided file uses a
small test prime (2, 3, 5, 7, 11, 13, 17 — all ≤ 5 bits); every declined file uses
a crypto-sized prime (254-bit BN254, 255-bit BLS12-381, 381-bit) the width cap
refuses to bit-blast. The 6 declined files are `bigff_is_zero_{sound,unsound}`,
`bitsum_overflow`, and `randcompile-sound-3i-5t-{circ,zokcirc,zokref}`.

A partial decide-rate is the expected, honest result: the win is **opening QF_FF
soundly with DISAGREE = 0** — a genuine new theory at small-prime parity with Z3,
with large-prime files declined cleanly rather than guessed.

### Ground-truth annotation: `; EXPECT:` vs `:status`

The cvc5 FF regressions annotate the expected verdict with a `; EXPECT: sat|unsat`
comment (cvc5's regress convention), not a `(set-info :status …)`. The flat
benchmark-slice parser does not read the comment as `set-info`, so the harness
reports `expected=unknown` and the top-level `:status` `agree` counter is 0; the
**binding soundness gate is the `--compare-z3` Z3-oracle head-to-head**
(`summary.oracle`: compared 24, agree 24, disagree 0), exactly as the QF_DT / QF_AX
slices rely on the Z3 oracle rather than `:status`.

Reproduce the selection (the `--expect-comment` flag accepts the `; EXPECT:`
annotation as ground truth; default behavior is unchanged):

```sh
python3 scripts/curate-public-slice.py QF_FF - --expect-comment
# QF_FF (..., expect_comment=True, ...): 30 files
```

## Corpus reality

The cvc5 suite has exactly **35** files declaring `(set-logic QF_FF)`; 30 are clean
under the standing filter (plain `assert`+`check-sat`). The 5 excluded use
`get-value`, `push`/`pop` (`ctx`, `tlimit_per`, `multicheck` is incremental-shaped
but cumulative-clean so it is included), or a non-`QF_FF` combined logic. The
bitwuzla suite has **0** finite-field files (it is BV/FP-focused). This is the
corpus, not a curation artifact.
