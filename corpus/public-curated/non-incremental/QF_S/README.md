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
`str.suffixof`, `str.at` (constant **and** variable `Int` index), `str.++`
(variable, bounded), `str.substr`, `str.to_code`, `str.from_code` (conservative
to ASCII), `str.<`, `str.<=`, and `=`/`distinct`. String literals (including
`""`-escaped quotes) pack to constants.

Everything outside this subset — regex (`str.in_re`/`re.*`),
`str.replace`/`str.indexof`/`str.to_int`/`str.from_int`, the `Seq` sort, and
over-bound cases (literals > 8 bytes, a concat past the 16-byte cap) — is
declined as a clean `Unsupported`. **Soundness is by construction**: an
incomplete or unsupported case returns `unknown`/`unsupported`, never a wrong
verdict.

## Measured head-to-head

`qf-s-cvc5-regress-clean-solver-vs-z3-10s.json`, `--timeout-ms 10000 --jobs 4`:

### Slice 3 — substr / variable-index `str.at` / to_code / lex order (2026-06-24)

- **files 123**. axeyum **decides 22** (sat 16, unsat 6), **unknown 6**
  (all `Incomplete` — bounded integer width or out-of-range constant, **not** a
  wrong verdict), **unsupported 95** (declined cleanly), errors 0.
- **compared 22, agree 22, DISAGREE 0.** Every decided verdict matches both the
  Z3 4.13.3 binary **and** the benchmark's `(set-info :status …)` annotation.
- New deciders, each encoded over the same packed BV layout (no `axeyum-ir`
  change):
  - `str.at s i` for a **variable** `Int` index — an Int-equality mux over the
    ≤`m` positions (`0 ≤ i < |s|` → `s[i]`, else `""`).
  - `str.substr s off n` — bounded substring, total function: `""` unless
    `0 ≤ off < |s|` and `n > 0`; else `s[off .. min(off+n,|s|)]`. `off`/`n` are
    arbitrary `Int`s.
  - `str.to_code s` (code of the single char, else `-1`) and `str.from_code i`
    (length-1 string of code point `i`, **conservative to ASCII `0..=127`**, else
    `""` — a code point ≥ 128 is a multi-byte UTF-8 char the byte layout cannot
    represent, so we never claim a byte we cannot model).
  - `str.<` / `str.<=` — lexicographic order over the packed bytes (a bounded
    BV/Bool cascade respecting length; matches code-point order on ASCII).
- Slice 2 measured decided 13 / unsupported 108; slice 3 is decided 22 /
  unsupported 95.

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

## Slice-4 decomposition (raise the decide-rate, stay sound)

Slices 2–3 wired the BV-expressible manipulation/conversion ops (variable
`str.++`, variable-index `str.at`, `str.substr`, `str.to_code`/`from_code`,
`str.<`/`str.<=`). The remaining unsupported instances break down by the first
gating operator:

| gap | slice-4 action |
|---|---|
| regex (`str.to_re`, `re.range`, `re.++`, `re.*`, `re.all/none/allchar`, `str.in_re`, `str.indexof_re`, `str.replace_re`) | **biggest bucket** — wire a bounded `Regex`/NFA fragment onto the packed layout (regex matching of a ≤`m`-byte string) |
| `str.replace` (first occurrence) / `str.replace_all` | bounded byte-matching + rebuild over the ≤`m` positions; mind the result-length growth and the no-match corner |
| `str.indexof s sub off` | bounded byte-matching cascade returning the first match position (or `-1`); needs the Int↔position bridge like slice-3 `str.at`/`str.substr` |
| `str.to_int` / `str.from_int` | digit parsing / formatting (QF_SLIA Int bridge) — bounded-digit encoding |
| over-bound case (literal > 8 bytes, concat past the 16-byte cap, a model needing integer width > 32) | raise `STRING_MAX_LEN` / the bounded integer width (several slice-3 `unknown:Incomplete` instances clear with a wider bound) |
| `str.update`, `str.to_lower`, `str.replace_re_all`, `Seq` | genuinely unsupported / unbounded — remain a sound decline |

Note on slice-3 unknowns: the 6 `unknown:Incomplete` instances are sound
declines, not wrong verdicts — most are unsat-shaped queries (e.g. the
`str-code-unsat*` family) whose refutation needs more than the bounded integer
width 32, or a literal integer constant that overflows the bounded width. Raising
the bound is a slice-4 lever, gated by the same DISAGREE = 0 re-measure.

Each slice is gated by the same DISAGREE = 0 re-measure.

Reproduce the curation:

```sh
# QF_S + QF_SLIA strings files, clean-command filter, with :status ground truth.
# Source: references/cvc5/test/regress/cli/regress{0,1}/strings (gitignored clone).
```
