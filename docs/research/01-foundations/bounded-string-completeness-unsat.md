# Bounded-string completeness: when "no model within the bounded width" is a sound UNSAT

Status: **soundness specification** for task #75 (the string-unsat decide-rate
lever). Records the exact condition under which the bounded packed-BV string
model (ADR-0029) may upgrade a "no model within the bounded integer width N"
`Unknown` to a real `Unsat`, and the argument for why weaker conditions are
wrong-unsat traps.

## The gap

The combined-theory solver (`crates/axeyum-solver/src/combined.rs:134`) is
deliberately conservative: when the BV backend returns `Unsat` **and** any Int
was bit-blasted (`had_integers()`), it downgrades to
`Unknown("no model within the bounded integer width 32; widen the bound")`
rather than claim `Unsat`. Strings are lowered to packed bit-vectors and their
`str.len`/position quantities are int-blasted, so *every* string query trips
`had_integers()` — and a genuinely-unsat bounded string query
(e.g. cvc5 `update-ex2`: `(not (= (str.substr (str.update "AAAAAA" 1 s) 5 1) "A"))`
`(< (str.len s) 3)`) comes back `Unknown` even though it is provably unsat.

The width ladder (`auto.rs:dispatch_int_blast_width_ladder`) only widens the
**int** width, capped at `DEFAULT_INT_WIDTH = 32`; it never proves unsat from a
no-model result. So recovering these unsats needs a *completeness argument*, not
a wider bound.

## Why "no free Int symbol" is necessary but NOT sufficient

The tempting condition — "upgrade when the query has no free unbounded Int
variable" — is a **wrong-unsat trap**. The bounded model has TWO incompleteness
axes, and the int width is only one:

1. **Int width** (≤ 32 bits). A free Int `x` with `(> x 5)` is real-sat (x =
   2³²), but has no bounded-width model → no-model ≠ unsat.
2. **String length** (≤ `STRING_MAX_LEN = 12` per symbol, `STRING_BOUND_CAP = 24`
   per concat). This axis has **no Int symbol at all** yet still breaks the
   upgrade:
   - `(> (str.len s) 100)` — real-sat (s = 101 chars), bounded no-model.
   - `(= (str.at s 100) "x")` — real-sat (s = 101 chars, 'x' at 100), bounded
     `str.at` past len → `""`, so `"" = "x"` is false → bounded no-model.

   Both have only a `String` free var — the agent's "no free Int" test passes —
   yet upgrading to unsat is a **wrong-unsat**. The string-length bound is the
   completeness gap, independent of integers.

## The sound condition: C1 ∧ C2 ∧ C3 (bounded-completeness)

The bounded model is **complete** for a query `Q` — i.e. `Q` real-sat ⇒ `Q`
bounded-sat, so bounded-no-model ⇒ real-unsat — when ALL of:

- **C1 — no free unbounded Int.** No user-declared (non-`!`-internal) symbol of
  `Sort::Int` exists. (Hook: `declared_int_var` at parse.rs:989 over the
  declarations; or `arena.symbols()` filtered to non-`!` `Sort::Int`.) A single
  free Int → the width-32 no-model is genuinely inconclusive.
- **C2 — every free String var is length-capped ≤ `STRING_MAX_LEN`.** Each
  declared `String` symbol `s` must be constrained by an asserted **upper**
  length bound `(str.len s) < k` or `(str.len s) <= k` with `k` a literal
  ≤ `STRING_MAX_LEN` (top-level conjunct; `<= k` needs `k ≤ MAX_LEN`, `< k`
  needs `k ≤ MAX_LEN+1`). This guarantees any real model's `s` fits the
  ≤`MAX_LEN`-byte packing. Derived strings need no separate bound: `str.++` that
  survived parse is ≤ `CAP`, and `str.substr`/`str.update`/`str.replace` never
  grow beyond their (already-bounded) source. A free String with **no** such
  bound (or bounded only from below) → decline (the `str.at`-past-len trap).
- **C3 — every Int quantity provably < 2³¹.** Given C1+C2, string-derived ints
  are: `str.len`/positions ≤ `CAP` (24), `str.to_code` ≤ 0x2FFFF, small Int
  literals, and `+`/`-`/`ite`/`min`/`max`/comparisons thereof — all < 2³¹.
  Two escape hatches must be **excluded conservatively**:
  - `str.to_int` of a string longer than 9 digits: ≤ `10^CAP − 1 = 10^24 − 1 >
    2³¹`. Allow only when its argument is provably ≤ 9 bytes (a stricter fact than
    the current 12-byte declaration bound); otherwise decline.
  - non-linear Int arithmetic: a product of ≥ 2 non-constant bounded quantities
    (e.g. `(* (str.len a) (str.len b) …)`) can exceed 2³¹. Allow only linear
    combinations with small constant coefficients; any `*`/`div`/`mod` of two
    non-constants → decline.

  Conservative default: if the analyzer cannot *prove* a quantity < 2³¹, it
  does not upgrade.

If C1∧C2∧C3 hold, a bounded no-model is a real unsat. **Any uncertainty →
leave `Unknown`** (never a wrong-unsat). This is a strict analysis: it decides a
subset of the truly-unsat bounded-complete queries and declines the rest —
soundness over completeness, per the project stance.

## Soundness argument (sketch)

Let `Q` be a query satisfying C1∧C2∧C3, and suppose `Q` is real-sat with model
`ρ` (assigning strings and ints over the unbounded theory). By C2 every free
string `s` has `len_ρ(s) ≤ MAX_LEN`, so `ρ(s)` is representable in the packed
sort; derived strings are bounded by construction, so the whole string part of
`ρ` lives in the bounded model. By C1 there is no free int to assign, and by C3
every int quantity's value under `ρ` is < 2³¹, so it is representable exactly in
the width-32 int-blast (which is exact modulo 2³²; < 2³¹ ⇒ no wraparound). Hence
`ρ` restricts to a *bounded* model of `Q` — contradicting bounded-no-model. So
`Q` bounded-no-model ⇒ `Q` real-unsat. ∎

The crux is that all three bounds are *witnessed by the query itself* (C2's
explicit length caps, C3's operator whitelist), not assumed.

## Mandatory gates (P0 — wrong-unsat is the worst class)

1. **Differential vs cvc5 on the WHOLE `QF_S` + `QF_SLIA` corpus**, DISAGREE = 0.
   cvc5 is the authority (the corpus is cvc5-regress); every upgraded `Unsat`
   must match cvc5's verdict (and the `:status`).
2. **Soundness-negative fuzz** (the Hard Rule for this feature): a generator that
   deliberately emits queries which are **real-sat but bounded-no-model** — a
   free unbounded Int (`(> x 5)`), an *un*bounded free String probed past the
   cap (`(= (str.at s 100) "x")`, `(> (str.len s) 100)`), and a `str.to_int` of a
   long concat / a non-linear length product — and asserts the detector does
   **NOT** upgrade any of them (they stay `Unknown` or decide `Sat`, never
   `Unsat`). Without this the analyzer is blind on exactly the axis where it
   would ship a wrong-unsat.
3. **Frontier + corpus_regression + full `--lib`** unchanged.

## Hook points (from the #75 scoping)

- Upgrade site: `combined.rs:134-141` (or, less invasively, a post-solve rewrite
  at the SMT-LIB front door where the parse tree / `Script` is still in scope).
- Sort/declaration tracking: `declared_int_var` (parse.rs:989),
  `declared_string_var` (parse.rs:852/1044), `arena.symbols()` (arena.rs:147,
  filter non-`!`).
- Length-bound facts already collected: the `LenAbs` side channel
  (`lenabs.facts`) records `str.len` relations — the C2 analysis can read the
  asserted length bounds from there rather than re-parsing.

## Backlinks

- Task #75; discovered landing #74 (str.update), whose two unsat targets are
  exactly the update-ex2 shape this unlocks.
- ADR-0029 (bounded packed-BV string model), the source of both bound axes.
- `bv-semantics-and-partial-operations.md` (sibling: totality vs boundedness).
