# DISTINCT-LINEAR — the corpus-wide sizing, and the two handoff claims that were false

Lane `DISTINCT-LINEAR`, 2026-09-13. Branched from `main` at `2611e14b0`
(`git merge-base main <branch>` = `2611e14b0`, main's HEAD at branch time).

**This file is the lane's PRE-REGISTERED sizing and method. It is written and
committed before the A/B is read**, so the bracket below cannot be adjusted to
whatever the measurement happens to produce. The measurement lands in `AB.md`
beside it.

## 1. The sizing, corpus-wide rather than one division's pinned 200

The handoff (`bench-results/qbudget-20260913/DISTINCT-ENCODING.md`) sized this at
**5 files**, found in `UFNIA`'s pinned 200. That is the sizing floor, not the
size.

`scan_distinct.py` tokenises every `.smt2` in the SMT-LIB 2024 non-incremental
corpus that contains the string `distinct` and reports the largest `distinct`
arity per file. The pairwise expansion is `n(n-1)/2` and
`MAX_DISTINCT_EXPANSION_PAIRS` is 65,536, so the first refused arity is **363**
(362 → 65,341 pairs, 363 → 65,703).

| | |
|---|---:|
| `.smt2` files in the corpus | 438,631 |
| …containing `distinct` at all | 28,415 |
| …with a `distinct` application of arity ≥ 363 | **356** |

| division | files | largest arity |
|---|---:|---:|
| `UFNIA` | 309 | 1,571 |
| `QF_NIA` | 35 | 65,677 |
| `QF_LIA` | 12 | 3,567 |

Families: `UFNIA/lahiri-cav09-storm-queries` 257, `UFNIA/spec_sharp` 52,
`QF_NIA/20210219-Dartagnan` 35, `QF_LIA/20210219-Dartagnan` 12.

Declared `:status`: **265 `unsat`**, 90 `unknown`, 1 `sat`.

The largest application in the corpus has **65,677** arguments — 2.16 billion
pairwise disequalities. Raising the cap was never the fix.

**So the target is 356 files, not 5** — 71× the handoff's number, and 265 of them
declare `unsat`, which is the half a refutation can win.

## 2. Two claims in the handoff are false, and each would have shipped a
   rewrite that never fires

Both were found by building the lever and running it against the corpus, not by
reading the handoff more carefully.

### 2a. "the `distinct` is the whole body of an `(assert …)`"

The handoff's §Addendum proposed scoping the rewrite to that shape, on the
grounds that "the five rows above are all exactly this shape, because that is how
Boogie emits the axiom".

`polarity_scan.py` walks every over-cap application and records the chain of
enclosing operator heads from its `assert`. **That shape occurs zero times in
356 files.**

| chain from `assert` | files | polarity |
|---|---:|---|
| `assert > and` | 257 | positive |
| `assert > let > not > or > not` | 52 | positive |
| `assert > let > … > <a let BINDING> > and` | 47 | positive by the chain, but the bound name's uses decide |

All 356 are positive. None is the body. A scoping test on the body would have
passed every unit test anyone wrote and fired on nothing.

The shipped site test is therefore a polarity walk
(`LinearDistinctSites::for_assert`), descending through `and`, `or`, `not`
(flipping), `=>` (flipping every antecedent) and a `let`'s BODY, and stopping at
everything else. **Coverage: 309 of 356.** The 47 `let`-BINDING files are left on
the pairwise path: a bound name's polarity is the join over its uses, which this
walk does not resolve.

### 2b. "nullary uninterpreted constants of an uninterpreted sort"

True of `lahiri-cav09-storm-queries` (`declare-sort boogieU 0`,
`declare-sort boogieT 0`). **False of the other 99 files.** `spec_sharp` and both
Dartagnan families carry no `declare-sort` at all and spell the whole query over
`Int`, because Boogie's UFNIA encoding uses `Int` as a universal carrier
(`argsorts.py`).

The first implementation of this lane scoped to uninterpreted sorts, on the
handoff's word. Measured against the corpus it fired on the 257 `lahiri` files
and silently declined 99. The shipped scope is `Uninterpreted(_)` or `Int` — the
two sorts whose `=` is plain in the pairwise path, so no string/sequence
length-abstraction and no FP/numeric coercion hook is bypassed. A mixed
application (`(distinct x y 3)` with `x, y : Real`) is excluded by the same-sort
test.

## 3. The encoding, and why each direction is safe

For a positive-only occurrence of `φ = (distinct t1 … tN)` with GROUND arguments
and a FRESH `f : S → Int`, the encoding is `ψ = ⋀ᵢ f(tᵢ) = i`: `N` conjuncts
instead of `N(N-1)/2`.

* **No wrong `sat`.** `ψ ⊨ φ`, because `f` is a function: `tᵢ = tⱼ` forces
  `i = j`. The occurrence is positive, so `Φ` is monotone in it and `Φ[ψ] ⊨ Φ[φ]`.
* **No wrong `unsat`.** Any model `M` of `Φ[φ]` extends to one of `Φ[ψ]`:
  interpret `f` as the injection when the `tᵢ` are distinct in `M`, and as `≡ 0`
  otherwise — either way `ψ ↔ φ` in `M`. Each admitted application gets its own
  fresh `f`, so the choices are independent.
* **Groundness** is why quantifier bodies are refused even though they preserve
  polarity: under `∀x` a non-ground `tᵢ(x)` would need a different `f` per `x`,
  and the encoding would be strictly stronger — a spurious `unsat`.
* **Freshness** is structural, not by naming luck. `declare_internal_fun` keys a
  namespace disjoint from user declarations, so a benchmark declaring
  `|!distinct.inj.0|` gets a different `FuncId`; and the internal name is chosen
  by probing until unused, so two applications never share one injection.

### The model replay does NOT cover this, and the handoff said it did

The handoff's §Addendum item 3 says "Model replay is unaffected". It is correct
about the mechanism and wrong about what that buys. `SmtLibSolved`'s replay is
`check_model(&solved.script.arena, &solved.assertions, model)`
(`crates/axeyum-solver/src/smtlib.rs:4426`), and `solved.assertions` are the
assertions the PARSER produced — under this rewrite, the rewritten ones. A model
of the encoding replayed against the encoding says nothing about `distinct`.

So the `sat` direction is safe because the encoding is at least as STRONG as
`distinct`, **not** because anything downstream checks it. That is why
`crates/axeyum-solver/tests/distinct_linear_soundness.rs` asserts verdicts rather
than trusting the replay.

## 4. The mutation control (`mutant-control.sh`)

ADR-1976 measured that a SAT-side reference control is vacuous: z3 and cvc5
agreed with a deliberately broken rewrite on 5 of 5 satisfiable files, because an
underconstrained `sat` stays `sat`. The rule that generalises is about
DIRECTION: aim each mutant where it has somewhere to go.

Four arms over 160 files drawn deterministically from the `QF_UF` and `UFLIA`
`distinct`-bearing populations (100 declared `unsat`, 60 declared `sat`):

| arm | lever | |
|---|---|---|
| base | unset | the shipped pairwise path |
| arm | `on:2` | the candidate |
| vacuous | `mutant:vacuous:2` | every index `0` — constrains nothing (WEAKER) |
| shared | `mutant:shared:2` | one injection for the whole script (STRONGER) |

The threshold is lowered to 2 deliberately. At the shipped threshold the rewrite
fires only on the 356 over-cap files, and those are mostly `unknown` at 24 s — a
population that cannot distinguish any encoding from any other. The exit status
fails on **all three** of: a decided contradiction between base and arm; a
weakening mutant that never contradicts an `unsat`; a strengthening mutant that
never contradicts a `sat`.

A row that moved between decided and `unknown` is REPORTED, not failed:
`unknown` is a first-class result and a no-opinion is not a contradiction
(ADR-1957).

## 5. The A/B (`ab-run.sh`, `launch-ab.sh`)

**Polarity: this lever ships OFF.** `base` is `env -u AXEYUM_DISTINCT_LINEAR`;
`arm` sets `AXEYUM_DISTINCT_LINEAR=on`. That is the same polarity as ADR-1970's
and ADR-1975's runners and the OPPOSITE of ADR-1980's, whose lever ships ON.

* treatment: all **356** over-cap files.
* control: `UFLIA`'s pinned 200. `UFLIA` has 5,795 `distinct`-bearing files and a
  largest arity of **256** — inside the cap — so the arm cannot touch it. Its
  movement is reported even when zero.
* 24 s wall, 8 GiB `ulimit -v`, one pinned core-pair, two arms back to back per
  file, arm order alternating.
* Compute: **6 of the 12 available pinned core pairs** — `1,9` and `3,11` on each
  of s5, s6, s7. `5,13` and `6,14` left free on all three.

## 6. What this lane predicts, before reading the A/B

Recorded here so it can be wrong.

* The front door will clear on 309 of 356. Verified by hand on one file of each
  family before the sweep: base refuses at `fd:parse` in 9–10 ms with the cap
  message; the arm reaches the solver.
* **The new verdicts will be few.** Both files checked by hand spent the whole
  24 s budget and returned `unknown` after clearing the parse. z3 refutes four of
  the handoff's five in 111–508 ms; this solver's quantified ladder is not z3's.
  Clearing a deterministic ingest refusal is a capability change whether or not
  it immediately buys verdicts, but the verdict count is the number that decides
  whether the lever ships ON.
* Control movement: 0. Any non-zero is noise and must be read against the noise
  floor, not against 0.
