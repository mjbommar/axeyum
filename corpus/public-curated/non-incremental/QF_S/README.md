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

## Measured head-to-head

`qf-s-cvc5-regress-clean-solver-vs-z3-10s.json`, `--timeout-ms 10000 --jobs 4`:

### Slice 2 — variable `str.++` (2026-06-24)

- **files 123**. axeyum **decides 13** (sat 9, unsat 4), **unknown 2**
  (incomplete — needs more than the bounded representation), **unsupported 108**
  (declined cleanly), errors 0.
- **compared 13, agree 13, DISAGREE 0.** Every decided verdict matches both the
  Z3 4.13.3 binary **and** the benchmark's `(set-info :status …)` annotation
  (independent double-check), including the soundness regression
  `r0_QF_SLIA_unsound-0908.smt2`.
- Variable `str.++` (concat over non-constant operands) and the operators that
  share its representation now decide: `str.len`, `=`/`distinct`, `str.at`
  (const idx), `str.contains`, `str.prefixof`, `str.suffixof` over variable
  strings and over concat results. Slice 1 measured decided 4 / unsupported 118;
  slice 2 is decided 13 / unsupported 108.

### Slice 1 — bounded packed-BV strings (2026-06-24)

- decided 4 (sat 3, unsat 1), unknown 1, unsupported 118, errors 0; compared 4,
  agree 4, DISAGREE 0.

A modest decide-rate is expected and fine: the win is **growing QF_S soundly with
DISAGREE = 0**. The bounded packed-BV fragment is the foundation; the
decomposition below is the path to raising the decide-rate further.

## How variable `str.++` decides (slice 2)

The parser's packed-string layout is **self-describing by width**: a string of
maximum length `m` is one bit-vector packing a `len_width(m)`-bit length and `m`
content bytes, so `m` is recoverable from the bit-vector width alone (no side
table). Variable `str.++ a b` produces a **wider** packed string of maximum
length `max_len(a) + max_len(b)` — exactly like the solver-side
`axeyum_solver::strings::BoundedString::concat` — so the join never silently
overflows the operand bound. The result length is `len(a) + len(b)` and the
content is `content(a) | (content(b) << (len(a)·8))` with `a`'s padding masked
off; the result is again a self-describing packed string, so `str.len`, `=`,
`str.at`, `str.contains`, prefix/suffix all decide over it. Declared symbols and
literals are `STRING_MAX_LEN = 8` bytes; a concat result is capped at
`STRING_BOUND_CAP = 16` bytes (the 128-bit content ceiling). A concat whose
summed bound exceeds the cap declines as `Unsupported` (Unknown to the consumer)
— **never a wrong verdict**.

## Slice-3 decomposition (raise the decide-rate, stay sound)

The remaining unsupported instances break down by the first gating operator (the
solver's `axeyum_solver::strings::BoundedString` API **already** implements all
of these end-to-end — the remaining work is front-end wiring onto the same
self-describing packed layout):

| gap | slice-3 action |
|---|---|
| regex (`str.to_re`, `re.range`, `re.++`, `re.*`, `re.all/none/allchar`, `str.in_re`) | wire the `Regex` NFA fragment already in the solver |
| `str.substr` | wire `BoundedString::substr`/`substr_at` (result in a smaller sort) |
| `str.replace` | wire `BoundedString::replace`/`replace_same_len` |
| `str.to_code` / `str.from_code` | wire `to_code`/`from_code` |
| `str.from_int` / `str.to_int` | wire `from_int`/`to_int` (QF_SLIA Int bridge) |
| `str.indexof` | wire `index_of` (constant `from`) |
| `str.<` / `str.<=` | wire `less`/`less_equal` |
| over-bound literal (> 8 bytes) | raise `STRING_MAX_LEN` toward the 16-byte cap |
| `str.update`, `str.to_lower`, `str.replace_re_all`, `Seq` | genuinely unsupported / unbounded — remain a sound decline |

Each slice is gated by the same DISAGREE = 0 re-measure.

Reproduce the curation:

```sh
# QF_S + QF_SLIA strings files, clean-command filter, with :status ground truth.
# Source: references/cvc5/test/regress/cli/regress{0,1}/strings (gitignored clone).
```
