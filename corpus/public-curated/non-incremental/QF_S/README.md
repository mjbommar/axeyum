# QF_S curated slice (committed, reproducible)

Curated, **committed** SMT-LIB strings slice for the measured head-to-head of
the `axeyum-smtlib` front end + `axeyum_solver` against the Z3 4.13.3 binary.
This is the **first** QF_S (Strings) measurement — the division opened this
session by wiring the bounded packed-bit-vector string lowering (ADR-0029) into
the SMT-LIB parser.

- `cvc5-regress-clean/` — **123** clean files from the cvc5 strings regression
  suite (`references/cvc5/test/regress/cli/regress{0,1}/strings`, a gitignored
  shallow clone), filtered to `(set-logic QF_S)` or `(set-logic QF_SLIA)` with a
  machine-readable `(set-info :status sat|unsat)` ground truth and **only** plain
  commands (`set-logic`/`set-info`/`set-option`/`declare-fun`/`declare-const`/
  `assert`/`check-sat`/`exit`) — no `push`/`pop`, `get-value`, `define-fun-rec`,
  or other exotic/incremental commands.

```sh
target/release/axeyum-bench \
  corpus/public-curated/non-incremental/QF_S/cvc5-regress-clean \
  --logic QF_S --backend solver --compare-z3 --timeout-ms 10000 --jobs 4 \
  --out bench-results/baselines/qf-s-cvc5-regress-clean-solver-vs-z3-10s.json
```

## The string fragment that is wired (ADR-0029, bounded)

A `String` is one bit-vector packing a length (low 4 bits) and up to
`STRING_MAX_LEN = 8` content bytes above it; a declared string symbol carries a
canonical well-formedness constraint (length ≤ max, padding bytes zero) so equal
strings share one bit pattern and `=`/`distinct` decide on the sound BV path.
Both `(declare-const s String)` and `(declare-fun s () String)` open this
representation. Wired operators: `str.len`, `str.prefixof`, `str.contains`,
`str.suffixof`, `str.at` (constant index), `str.++` (constant args), and
`=`/`distinct`. String literals (including `""`-escaped quotes) pack to
constants.

Everything outside this subset — variable `str.++`, regex (`str.in_re`/`re.*`),
`str.substr`/`str.replace`/`str.indexof`/`str.to_int`/`str.from_int`/`str.<`,
symbolic `str.at`, over-bound literals (> 8 bytes), and the `Seq` sort — is
declined as a clean `Unsupported`. **Soundness is by construction**: an
incomplete or unsupported case returns `unknown`/`unsupported`, never a wrong
verdict.

## Measured head-to-head (2026-06-24)

`qf-s-cvc5-regress-clean-solver-vs-z3-10s.json`, `--timeout-ms 10000 --jobs 4`:

- **files 123**. axeyum **decides 4** (sat 3, unsat 1), **unknown 1**
  (incomplete — needs more than the bounded representation), **unsupported 118**
  (declined cleanly), errors 0.
- **compared 4, agree 4, DISAGREE 0.** Every decided verdict matches both the Z3
  4.13.3 binary **and** the benchmark's `(set-info :status …)` annotation
  (independent double-check).
- PAR-2 mean 4.001 s (dominated by the unsupported/unknown timeout accounting,
  not solve cost — the 4 decided instances finish in < 10 ms each).

A low decide-rate is expected and fine: the win is **opening QF_S soundly with
DISAGREE = 0**. The bounded packed-BV fragment is the foundation; the
decomposition below is the path to raising the decide-rate.

## Slice-2 decomposition (raise the decide-rate, stay sound)

The 118 unsupported instances break down by the first gating operator (the
solver's `axeyum_solver::strings::BoundedString` API **already** implements all
of these end-to-end — the remaining work is purely front-end wiring of the
typed-result `StrTerm` (len, content) representation, which differs from the
parser's single packed-BV layout):

| count | gap | slice-2 action |
|---|---|---|
| 36 | variable `str.++` | typed-result concat (grows the bound); the single biggest win |
| ~40 | regex (`str.to_re`, `re.range`, `re.++`, `re.*`, `re.all/none/allchar`) | wire `str.in_re` + the `Regex` NFA fragment already in the solver |
| 6 | `str.substr` | wire `BoundedString::substr`/`substr_at` |
| 5 | `str.replace` | wire `BoundedString::replace`/`replace_same_len` |
| 5 | `str.to_code` / 2 `str.from_code` | wire `to_code`/`from_code` |
| 4+3 | `str.from_int` / `str.to_int` | wire `from_int`/`to_int` (QF_SLIA Int bridge) |
| 2 | `str.indexof` | wire `index_of` (constant `from`) |
| 2+1 | `str.<` / `str.<=` | wire `less`/`less_equal` |
| 7 | over-bound literal (> 8 bytes) | raise `STRING_MAX_LEN` toward the 16-byte cap |
| residual | `str.update`, `str.to_lower`, `str.replace_re_all`, `Seq` | genuinely unsupported / unbounded — remain a sound decline |

The principled next step is to migrate the parser's string representation onto
the solver's richer `StrTerm` (separate `len`/`content` terms with sort growth),
which unlocks variable concat, substr/replace/indexof, and the regex NFA in one
coherent slice — each gated by the same DISAGREE = 0 re-measure.

Reproduce the curation:

```sh
# QF_S + QF_SLIA strings files, clean-command filter, with :status ground truth.
# Source: references/cvc5/test/regress/cli/regress{0,1}/strings (gitignored clone).
```
