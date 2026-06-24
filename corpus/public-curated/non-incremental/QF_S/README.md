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
to ASCII), `str.to_int`, `str.from_int` (QF_SLIA Int bridge), `str.<`, `str.<=`,
`str.in_re` over the bounded **regex** fragment (`str.to_re` of a literal,
`re.range`, `re.allchar`/`re.all`/`re.none`, `re.++`/`re.union`/`re.inter`,
`re.*`/`re.+`/`re.opt`), and `=`/`distinct`. String literals (including
`""`-escaped quotes and `\u{…}`/`\uXXXX` code points ≤ 255) pack to constants.

Everything outside this subset — the regex constructs `re.comp`/`re.diff`/
`re.loop`/`re.^`, a symbolic `str.to_re x`, a code point > 255, an NFA over the
state cap, `str.replace`/`str.indexof`/`str.replace_re`/`str.indexof_re`, the
`Seq` sort, and over-bound cases (literals > 8 bytes, a concat past the 16-byte
cap, a `str.from_int` whose decimal expansion exceeds 10 digits) — is declined as
a clean `Unsupported`. **Soundness is by construction**: an incomplete or
unsupported case returns `unknown`/`unsupported`, never a wrong verdict.

### Bounded regex matching (`str.in_re`, slice 5)

`(str.in_re s R)` for a bounded string `s` of max length `m` compiles `R` to a
Thompson NFA over **byte** character classes, then asserts acceptance with a
bounded reachable-state encoding: Boolean `reach[pos][q]` for each position
`pos ∈ 0..=m` and NFA state `q`, where `reach[0]` is the ε-closure of the start
state, `reach[pos+1][t]` holds when some `reach[pos][q]` has a `q → t` character
transition whose predicate accepts byte `s[pos]` **and** `pos < len(s)` (then
ε-closure), and acceptance is selected at `pos = len(s)` from the packed length
field. The encoding is **denotation-preserving for the ≤`m`-byte representation
of `s`** — it decides matching exactly over the bounded string, with the static
ε-closure precomputed and every disjunction built as a *balanced* tree so a large
NFA cannot produce a stack-overflowing linear-depth term (the `re-inter-stack-ovf`
benchmark now returns a sound `unknown`, not a crash). The same length bound as
the rest of the front end is the only incompleteness: a match that needs a string
longer than `m` is excluded by well-formedness and surfaces as `unknown`, never a
wrong `sat`/`unsat`. The `re.inter` case is a determinized subset product of the
component NFAs, capped at the same state limit. Each construct is checked against
the SMT-LIB `UnicodeStrings`/`RegLan` semantics; `\u{…}`/`\uXXXX` escapes are
decoded so an escaped endpoint is never silently collapsed to the empty language
(the `issue1684-regex` corner: `(re.range "\u{0}" "\u{ff}")` is *any byte*, sat).

## Measured head-to-head

`qf-s-cvc5-regress-clean-solver-vs-z3-10s.json`, `--timeout-ms 10000 --jobs 4`:

### Slice 5 — bounded **regex** matching (`str.in_re`) (2026-06-24)

- **files 123**. axeyum **decides 41** (sat 29, unsat 12), **unknown 11**
  (all `Incomplete` — bounded integer width 32 / out-of-range Int constant /
  over-length string, **not** a wrong verdict), **unsupported 71** (declined
  cleanly), errors 0.
- **compared 40, agree 40, DISAGREE 0** (12 skipped where Z3 itself returned
  `unknown`/timed out). Every decided verdict matches both the Z3 4.13.3 binary
  **and** the benchmark's `(set-info :status …)` annotation (0 status
  mismatches), and every `sat` model replay-checks (`model_replay_failures = 0`).
  No regression on QF_UF/QF_UFLIA (DISAGREE 0). `par2_mean` 4.38 → 4.23 s (no new
  timeout; the deeply-nested `re-inter-stack-ovf` benchmark is a sound `unknown`).
- New deciders (all in `axeyum-smtlib`, no `axeyum-ir`/`axeyum-solver` change):
  `str.in_re` over the bounded regex fragment — `str.to_re` of a literal,
  `re.range`, `re.allchar`/`re.all`/`re.none`, `re.++`/`re.union`/`re.inter`,
  `re.*`/`re.+`/`re.opt` — encoded as a Thompson NFA → bounded reachable-state
  Boolean/BV match over the ≤`m` packed bytes (see the fragment description
  above). Of the 52 `str.in_re` files, **16 now decide** (10 sat, 6 unsat); the
  rest decline a declined construct (`re.comp`/`re.diff`/`re.loop`,
  `str.replace_re`, symbolic `str.to_re`, code point > 255) or are over-bound.
- **Soundness corner fixed:** `\u{…}`/`\uXXXX` escapes are decoded to code points;
  an endpoint with a representable code point (≤ 255) forms its byte range, an
  endpoint **above** 255 (or a malformed escape) **declines** rather than collapse
  to the empty language — so `issue1684-regex` (`(re.range "\u{0}" "\u{ff}")` =
  any byte) is correctly `sat`, where a naive byte-literal decode produced a wrong
  `unsat`.
- **Bound decision:** `STRING_MAX_LEN = 8` and `STRING_BOUND_CAP = 16` unchanged
  (slice-4's measurement that widening regresses the decide-rate still holds). The
  remaining 71 unsupported are dominated by **over-bound** length (a concat past
  the 16-byte cap: 25; a literal > 8 bytes: 10) — a length-bound lever, not a
  regex gap — plus the declined non-regular constructs.

### Slice 4 — `str.to_int` / `str.from_int` (QF_SLIA Int bridge) (2026-06-24)

- **files 123**. axeyum **decides 25** (sat 19, unsat 6), **unknown 7**
  (all `Incomplete` — bounded integer width 32 / out-of-range Int constant,
  **not** a wrong verdict), **unsupported 91** (declined cleanly), errors 0.
- **compared 25, agree 25, DISAGREE 0.** Every decided verdict matches both the
  Z3 4.13.3 binary **and** the benchmark's `(set-info :status …)` annotation
  (0 status mismatches). No regression on QF_UF/QF_UFLIA (DISAGREE 0). `par2_mean`
  4.29 → 4.38 s (no blowup, no new timeout).
- New deciders, encoded over the same packed BV layout (no `axeyum-ir` change):
  - `str.to_int s` — the decimal value of a **non-empty** ASCII-digit string,
    else `-1` (empty or any non-digit char → `-1`; **leading zeros are valid**,
    `"0001" → 1`). A bounded Horner fold `acc ← acc·10 + digit` over the ≤`m`
    present bytes, guarded by a digit-validity check; the result is an `Int`. Max
    value `10^8 − 1 < 2^31`, so it is complete within the default bounded integer
    width (and sound for any width: an over-wide value overflows the int-blast and
    replay returns `Unknown`, never a wrong verdict).
  - `str.from_int i` — the canonical decimal string of `i ≥ 0` (no leading zeros,
    `0 → "0"`), else `""` for `i < 0`. The result is a packed string of max length
    **10**, sized to hold the full decimal expansion of every integer the bounded
    int bit-blast can assign (`< 2^31 < 10^10`), so the encoding is **faithful for
    every model the solver can produce**. A **constant** argument folds exactly and
    **declines** (`Unsupported`) when it needs > 10 digits (over-bound — never a
    truncated/wrong string, e.g. the 19-digit constant in `type001`).
- Moved off `unsupported`: `leadingzero001` (sat), `type003` (sat, 2-char
  `str.to_int` with arithmetic), `simple-nth-fail` (sat, `to_int ∘ from_code`);
  `artemis-0512-nonterm` moved to a sound `unknown:Incomplete` (an unsat-shaped
  `str.to_int` query the bounded BV int-blast cannot refute — not a wrong
  verdict).
- **Bound decision (`STRING_MAX_LEN`):** kept at **8**. The 6→7 `unknown:Incomplete`
  instances are all gated on the **bounded integer width 32** (`str004`,
  `str005`, `open-pf-merge`, `str-code-unsat{,-2,-3}` — unsat-shaped or a 29-digit
  Int constant) or are unsat-shaped queries the bounded BV cannot refute; **none**
  clear by widening the *string* length, and the integer width lives in
  `axeyum-solver` (out of this lane). Measured cost of raising `STRING_MAX_LEN`:
  9 and 12 both **regress** decided 25 → 14 (wider packed BVs blow up the
  formulas → timeouts, and `concat` hits the 16-byte cap sooner), `par2_mean`
  4.38 → 6.67 s. So 8 is the largest width that keeps the slices bounded with
  DISAGREE 0 and the best decide-rate. `STRING_BOUND_CAP = 16` unchanged
  (over-cap still declines).

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

## Slice-6 decomposition (raise the decide-rate, stay sound)

Slices 2–5 wired the BV-expressible manipulation/conversion ops (variable
`str.++`, variable-index `str.at`, `str.substr`, `str.to_code`/`from_code`,
`str.<`/`str.<=`, `str.to_int`/`str.from_int`) and the bounded **regex** fragment
(`str.in_re` over `str.to_re`/`re.range`/`re.allchar`/`re.all`/`re.none`/`re.++`/
`re.union`/`re.inter`/`re.*`/`re.+`/`re.opt`). The remaining **71** unsupported
instances break down by the first gating operator (measured from the slice-5
artifact):

| gap | count | slice-6 action |
|---|---|---|
| over-bound `concat` past the 16-byte cap | 25 | **biggest bucket** — a wider-cap or a length-abstraction path; mind the formula-size blowup (naively raising `STRING_MAX_LEN` regresses the decide-rate, measured in slice 4) |
| string literal > 8 bytes | 10 | same length-bound tension; a literal-only widening (without widening every symbol) is the cheaper lever to try |
| `str.replace` / `str.replace_all` | 7 | bounded byte-matching + rebuild over the ≤`m` positions; mind the result-length growth and the no-match corner |
| declined regex (`re.comp`/`re.diff` 4, `re.loop`/`re.^` indexed 6, symbolic `str.to_re` 5, a regex op used outside `str.in_re` ~5) | ~20 | `re.comp`/`re.diff` need a complement-aware (DFA-product) encoding; `re.loop` is a bounded-repeat unroll; symbolic `str.to_re` needs matching against an unknown string |
| `str.indexof` / `str.indexof_re` | 2 | bounded byte-matching cascade returning the first match position (or `-1`); reuses the Int↔position bridge from slice-3 `str.at`/`str.substr` |
| `str.update`, `str.to_lower`, `re.inter` (nested), `Seq`, a 29-digit Int constant | few | genuinely unsupported / unbounded / int-width-limited — remain a sound decline |

Note on slice-5 unknowns: the 11 `unknown:Incomplete` instances are sound
declines, not wrong verdicts — they are unsat-shaped queries the bounded BV
int-blast cannot refute, carry an Int constant that overflows the bounded width
32 (`str-code-unsat-2`'s 29-digit literal), or assert a string length over the
bound (`username_checker_min`, `re-inter-stack-ovf`, `re-agg-total1`). **None**
clear by raising the *string* length bound (measured in slice 4: 9 and 12 both
regress the decide-rate); the levers they need — the **bounded integer width**
(`DEFAULT_INT_WIDTH`) and a non-regressing length-widening — live in
`axeyum-solver` / are the slice-6 over-bound work.

Each slice is gated by the same DISAGREE = 0 re-measure.

Reproduce the curation:

```sh
# QF_S + QF_SLIA strings files, clean-command filter, with :status ground truth.
# Source: references/cvc5/test/regress/cli/regress{0,1}/strings (gitignored clone).
```
