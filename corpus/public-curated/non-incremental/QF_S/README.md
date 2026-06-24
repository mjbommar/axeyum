# QF_S curated slice (committed, reproducible)

Curated, **committed** SMT-LIB strings slice for the measured head-to-head of
the `axeyum-smtlib` front end + `axeyum_solver` against the Z3 4.13.3 binary.
This is the **first** QF_S (Strings) measurement — the division opened this
session by wiring the bounded packed-bit-vector string lowering (ADR-0029) into
the SMT-LIB parser.

- `cvc5-regress-clean/` — **134** files: **123** clean files from the cvc5
  strings regression suite
  (`references/cvc5/test/regress/cli/regress{0,1}/strings`, a gitignored shallow
  clone) plus **4** hand-authored `str.indexof`/`str.replace_all` files (slice 6)
  and **7** hand-authored `re.comp`/`re.diff`/`str.replace_re`/`str.replace_re_all`
  files (slice 7), filtered to `(set-logic QF_S)` or `(set-logic QF_SLIA)` with a machine-readable
  `(set-info :status sat|unsat)` ground truth and **only** plain commands
  (`set-logic`/`set-info`/`set-option`/`declare-fun`/`declare-const`/
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
(variable, bounded), `str.substr`, `str.replace` (first-occurrence splice,
literal or symbolic `a`/`b`), `str.indexof` (first-match position at-or-after an
offset, literal or symbolic), `str.replace_all` (ground non-overlapping fold),
`str.to_code`, `str.from_code` (conservative
to ASCII), `str.to_int`, `str.from_int` (QF_SLIA Int bridge), `str.<`, `str.<=`,
`str.in_re` over the bounded **regex** fragment (`str.to_re` of a literal,
`re.range`, `re.allchar`/`re.all`/`re.none`, `re.++`/`re.union`/`re.inter`,
`re.comp`/`re.diff` (top-level, via DFA determinization + complement),
`re.*`/`re.+`/`re.opt`), `str.replace_re`/`str.replace_re_all` (leftmost-shortest
regex splice over a **ground** string), and `=`/`distinct`. String literals
(including `""`-escaped quotes and `\u{…}`/`\uXXXX` code points ≤ 255) pack to
constants.

Everything outside this subset — the regex constructs `re.loop`/`re.^`, a
**nested** `re.comp`/`re.diff`/`re.inter`, a symbolic `str.to_re x`, a code point
> 255, an NFA/DFA over the state cap, `str.indexof_re` (not in the SMT-LIB
`UnicodeStrings` theory; a cvc5 extension unsupported by the Z3 oracle), a
**symbolic-string** `str.replace_re`/`str.replace_re_all`/`str.replace_all`, the
`Seq` sort, and over-bound cases (literals > 8 bytes, a concat past the 16-byte
cap, a `str.replace`/`str.replace_all` whose result max length exceeds the
16-byte cap, a `str.from_int` whose decimal expansion exceeds 10 digits) — is
declined as a clean `Unsupported`. **Soundness is by construction**: an incomplete
or unsupported case returns `unknown`/`unsupported`, never a wrong verdict.

### `re.comp` / `re.diff` + `str.replace_re` / `str.replace_re_all` (slice 7)

**`re.comp R`** (complement `Σ* \ L(R)`) and **`re.diff R1 R2`** (difference
`L(R1) \ L(R2)`) extend the bounded regex matcher. `re.comp` determinizes `R`'s
Thompson NFA to a DFA by the subset construction over the full byte alphabet,
**completes** the transition function (every `state × byte` has a target; missing
transitions route to an explicit dead sink), then **flips** the accepting set.
Completion is the soundness pivot: complement is the exact `Σ* \ L(R)` **only**
over a complete DFA — in a complete DFA every string drives the run to exactly one
state, so "`R` rejects `w`" ⇔ "the flipped automaton accepts `w`"; a *partial* DFA
would let a run fall off the table and the flip would misclassify it. `re.diff` is
`R1 ∩ comp(R2)`, reusing the existing product-intersection machinery over `R1` and
the complemented DFA of `R2`. Both are **top-level** only and bounded by the same
state cap (a blow-up declines as a sound `unknown`); a nested
`re.comp`/`re.diff`/`re.inter` declines.

**`str.replace_re s R t`** replaces the **leftmost, shortest** substring of `s`
matching `R` with `t`; **`str.replace_re_all`** replaces all such **non-empty**
matches left-to-right (SMT-LIB `UnicodeStrings`: `⟦replace_re⟧(w,L,t) = u₁ t u₂`
with `u₁,w₁` the **shortest** words s.t. `w = u₁ w₁ u₂, w₁ ∈ L` — so leftmost
start, shortest match; `ε ∈ L` ⇒ prepend `t`; no match ⇒ `w`; `replace_re_all`
requires `w₁ ≠ ε`, so it never loops on `ε`). This slice wires the **ground**
case (constant `s` and `t`): the literal bytes are scanned for the
leftmost-shortest match by concrete NFA simulation over each substring `s[i..j]`,
the splice is folded and packed (riding the pure-BV path, deciding both
directions). A **symbolic** `s` declines cleanly (`Unsupported` → `unknown`),
never a truncated/wrong string. **`str.indexof_re` is declined** — it is not in
the SMT-LIB `UnicodeStrings` theory (a cvc5 extension) and the Z3 oracle does not
support it, so there is no ground truth to validate an encoding against.

### Slice 7 measurement (`re.comp` / `re.diff` / `str.replace_re`)

- **files 134** (123 + 4 indexof/replace_all + 7 curated comp/diff/replace_re).
  axeyum **decides 59** (sat 42, unsat 17), unknown 13, **unsupported 62**,
  errors 0; **compared 59, agree 59, DISAGREE 0**. Every decided verdict matches
  the benchmark's `:status` (and the Z3 4.13.3 binary wherever Z3 returns a
  definitive verdict), every `sat` model replay-checks. No regression on
  QF_SEQ/QF_UF (DISAGREE 0, decided counts and `par2_mean` unchanged);
  `par2_mean` ≈ 3.62 s (no new timeout).
- New deciders (all in `axeyum-smtlib`, no `axeyum-ir`/`axeyum-solver` change):
  the existing regress file `re-in-rewrite` newly clears (**unsat** — `re.comp` of
  the non-empty language intersected with "starts with a", agreeing with Z3 +
  `:status`), plus the 7 curated files (2 sat comp/diff, 1 unsat comp,
  `comp(re.none) = Σ*` sat + `comp(re.all) = ∅` unsat exercising the DFA-completion
  edge cases, 1 sat ground `replace_re`, 1 unsat ground `replace_re_all`). Z3
  4.13.3 returns `unknown` on the ground `str.replace_re`/`str.replace_re_all`
  queries (it cannot constant-fold them), so those two files are validated by
  `:status` and skipped from the Z3 head-to-head — never a DISAGREE.

### `str.indexof` / `str.replace_all` (slice 6)

`(str.indexof s t i)` (or `(str.indexof s t)` at offset 0) returns the position
of the **first** occurrence of `t` in `s` at-or-after `i`, else `-1`. It reuses
the slice-4 `str.replace` first-match cascade — `match(p)` aligns `t` at `p` with
`p + len(t) ≤ len(s)` — restricted to eligible candidates `p ≥ i`; the leftmost
eligible `P` is the `Int` result, with the SMT-LIB corners verbatim: `i < 0` →
`-1`, `i > len(s)` → `-1`, `t = ""` → `i` when `0 ≤ i ≤ len(s)`. It is a pure
position search (no length-changing rebuild), sound for literal **or** symbolic
`s`/`t`/`i`. Because the result is an `Int`, an `indexof`-keyed **ground unsat**
comes back `unknown` (the `Int` bridge keeps it off the pure bit-blast path) — a
sound decline, never a wrong verdict; the curated unsats use the pure-BV
`replace_all` literal path instead.

`(str.replace_all s a b)` replaces **all** non-overlapping, left-to-right
occurrences of `a` with `b`. SMT-LIB corner (**verified against Z3/cvc5**):
`a = ""` is the **identity** (the empty-pattern replace_all leaves `s` unchanged
— this differs from single `str.replace`, where empty `a` prepends `b`); the scan
resumes *after* each inserted `b` (no rescan inside `b`, so
`(str.replace_all "aa" "a" "aa") = "aaaa"`). This slice wires the **fully-ground**
case exactly (all of `s`, `a`, `b` constant) by folding the replacement and
packing the literal (so it rides the pure-BV path and decides both directions); a
**symbolic** operand declines cleanly (`Unsupported` → `unknown`) — a sound
symbolic moving-cursor splice (bounded only for a concrete `len(a)`, with the
growing result kept under the 16-byte cap) is a scoped follow-up, never a
wrong/truncated string.

### Slice 6 measurement (`str.indexof` / `str.replace_all`)

- **files 127** (123 + 4 curated). axeyum **decides 51** (sat 38, unsat 13),
  unknown 13, **unsupported 63**, errors 0; **compared 48, agree 48, DISAGREE 0**.
  Every decided verdict matches both the Z3 4.13.3 binary and the benchmark's
  `:status`, and every `sat` model replay-checks. No regression on
  QF_UF/QF_UFLIA (DISAGREE 0), `par2_mean` ≈ 4.07 s (no new timeout).
- New deciders (all in `axeyum-smtlib`, no `axeyum-ir`/`axeyum-solver` change):
  `str.indexof` clears two existing regress files — `bug613` (sat,
  `(< (str.indexof s "<a>" 0) (str.indexof s "</a>" 0))` over a literal `s`) and
  `issue3497` (sat) — plus the 4 curated `str.indexof`/`str.replace_all` files
  (2 sat indexof, 1 sat replace_all grow, 1 unsat replace_all not-first-only).

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
| `str.replace_all` — ground case **wired** (slice 6: non-overlapping fold + literal pack); a **symbolic** `replace_all` still declines | few | the symbolic case needs a moving-cursor splice whose round count is bounded only for a concrete `len(a)` and whose growing result stays under the 16-byte cap |
| declined regex (`re.comp`/`re.diff` 4, `re.loop`/`re.^` indexed 6, symbolic `str.to_re` 5, a regex op used outside `str.in_re` ~5) | ~20 | `re.comp`/`re.diff` need a complement-aware (DFA-product) encoding; `re.loop` is a bounded-repeat unroll; symbolic `str.to_re` needs matching against an unknown string |
| `str.indexof` now **wired** (slice 6: first-match cascade restricted to `p ≥ i`, `Int` result); `str.indexof_re` still declines | ~1 | `indexof_re` matches a regex from an offset; the off-lane residual is the `Int`-result bridge (an `indexof`-keyed ground *unsat* returns a sound `unknown`) and the over-bound length lever |
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
