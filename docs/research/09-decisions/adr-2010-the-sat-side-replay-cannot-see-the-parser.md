# ADR-2010: the `sat`-side replay guarantee is orthogonal to how the parser actually fails

Status: accepted
Index-summary: CLAUDE.md's hard rule — "every `sat` result must be checkable by evaluating the original term against the lifted model" — was audited against the SMT-LIB front door, whose replay is `check_model(&script.arena, &solved.assertions, model)` over the **parser-produced** assertions. **The audit found three reachable wrong verdicts, all in the parser's UNCONDITIONAL s-expression desugars, none behind a lever or a feature gate, and the replay could not have caught any of the three.** (1) `desugar_sets` keyed each element bit on the literal's RAW TEXT, so `#b0101`/`#x5`/`(_ bv5 4)` and `1.5`/`1.50` were two elements each: `(set.member #b0101 s)` with `(not (set.member #x5 s))` answered **`sat`** (cvc5 `unsat`) while the same script with one spelling answered `unsat` — a verdict depending on the SPELLING of a literal, and the dual `(set.member #x5 (set.singleton #b0101))` a wrong `unsat`. (2) `desugar_const_arrays` collected `(assert (= s ((as const …) v)))` by scanning all top-level commands with **no notion of scope OR order**, then dropped it and inlined across the whole list: a definition inside a popped `push`, and a definition placed after a `check-sat` and inlined backwards past it, each gave a wrong **`unsat`** — the second needing no `push`/`pop` at all. (3) `desugar_sets`'s universe was `d + MARGIN` with `MARGIN` a **constant 2**, so N free set variables could not be pairwise distinct past `2^(d+2)`: 5 free sets answered **`unsat`** (cvc5 `sat`), 4 answered `sat`, and adding one named literal to raise `d` restored `sat` — the threshold sitting exactly at `2^(0+2)`. **The headline is not the three bugs but why one guarantee missed all of them, for two DIFFERENT structural reasons**: the source terms of a parse-level desugar never become IR terms at all (so replaying "against the originally parsed assertions" is a no-op — the original parse IS the encoding), and a STRENGTHENING rewrite produces wrong `unsat`, which a `sat`-side replay cannot see however it is implemented. **So the general guarantee is NOT achievable in the form the rule states, and per-rewrite arguments plus per-rewrite adversarial tests are the right design** — 18 tests in `parser_desugar_soundness.rs`, registered at L0, each aimed at the direction where the defect has somewhere to go and each paired with a non-vacuity control (ADR-1976). Guard-deletion: **10 guards mutated, 0 untested, 10 distinct death-sets, separable**; replacing the width decline with a `min()` clamp kills exactly one test. Handed off with a measurement rather than a preference: **5 of 109 `sat` results across the string divisions (217 files) carry a source-level model beside the packed assertion vector**, so the replay cannot evaluate them at all. Corpus cost measured rather than predicted: **23 affected files, decided 15 → 15, delta 0, 0 of 23 verdicts differ**, with a freshness control confirming the base binary reproduces all three wrong answers. A full transformation inventory of `parse.rs` (615 `fn`, 552 non-test; 5 independent enumeration strategies reconciled) classifies every transformation between text and `Script::assertions` by direction; the eleven `weaker` side channels each have a code gate, not just a comment.
Index-status: accepted
Date: 2026-09-14

## Context

CLAUDE.md states a hard rule:

> Every `sat` result must be checkable by evaluating the original term against
> the lifted model; never drop lowering/lift maps after solving.

[ADR-2000] observed, while landing the linear `distinct` encoding, that the
front door's replay is

```rust
check_model(&solved.script.arena, &solved.assertions, model)
```

and that `solved.assertions` are the **parser-produced** assertions. So when the
parser rewrites a query, a model of the rewrite is replayed against the rewrite.
ADR-2000's own encoding is safe because it is strictly stronger in positive
polarity — an argument, not a check.

This ADR asks the general question: **for which parser-level rewrites is the
replayed formula not the original, and is any of them unsound?**

The answer is worse and more interesting than "one of them is weakening".

## 1. The finding: one guarantee, two independent blind spots, three bugs

All three defects below are in the parser's **unconditional** s-expression
desugars — no environment lever, no feature gate, no logic restriction. All
three were reachable through the shipped front door at `94389e480`. And the
`sat`-side replay could not have caught any of them, for two structurally
different reasons:

**Blind spot A — a parse-level desugar has no original to replay against.**
`desugar_sets` rewrites `(Set E)` to `BitVec` *on the s-expression tree, before
any term is built* (`parse.rs:952`, inside `parse_script_bounded_inner`). The
source set terms never become IR terms. There is nothing for `check_model` to
evaluate them against, and the obvious remedy — "keep the originally parsed
assertions and replay against those" — is a **no-op here**, because the original
parse *is* the encoding. The same holds for the ADR-0029 bounded string
encoding, where a declared `String` has IR sort `(_ BitVec 100)` and the front
door's notion of "original assertions" is already a packed encoding of the text.

**Blind spot B — a strengthening rewrite produces wrong `unsat`, and the replay
only ever inspects `sat`.** This is not a property of the current
implementation. No model replay, however written, fires on a verdict that
carries no model. Two of the three bugs are in this class.

A note on framing, because the obvious generalization is wrong: it is **not**
the case that all three are strengthening rewrites. Defect 1 is neither
strengthening nor weakening — it is a *non-homomorphic* encoding that maps one
element onto two bits, and it was measured producing a wrong `sat` **and** a
wrong `unsat` from the same defect. Blind spot A is what covers it; blind spot B
covers defects 2 and 3. Two reasons, not one.

Three independent instances is no longer an anecdote. **The guarantee we
advertise is orthogonal to the failure mode this surface actually has.**

## 2. Defect 1 — the finite-set bit key was the literal's spelling

`set_element_key` (`parse.rs:5601`) returned `a.clone()` for an atom: the
literal's **raw text**. Its own doc comment claimed "the key is the literal's
normalized text", and the module note's condition 1 asserted the premise that
made it look sound —

> Two syntactically-distinct literals are two distinct values, so giving them
> distinct bits introduces no spurious (dis)equality.

That premise is false. `#b0101`, `#x5` and `(_ bv5 4)` are three spellings of
one 4-bit value; `1.5` and `1.50` are two spellings of one Real.

Measured through `axeyum_cli` at `94389e480`. The witness needs no coercion
argument — same sort, same value, two spellings:

```smt2
(set-logic ALL)
(declare-fun s () (Set (_ BitVec 4)))
(assert (set.member #b0101 s))
(assert (not (set.member #x5 s)))     ; #x5 IS #b0101
```

| script | ours (pre-fix) | cvc5 |
|---|---|---|
| `#b0101` and `#x5` | **`sat`** | `unsat` |
| `#b0101` twice (control) | `unsat` | `unsat` |
| `#x5` twice (control) | `unsat` | `unsat` |

The verdict depended on the **spelling of a literal**, which is by itself a
proof of unsoundness in one direction or the other; the two same-spelling
controls say which. The parser's own output shows the mechanism — the two
memberships became bit 0 and bit 1 of a 4-bit `s`:

```smt2
(declare-const s (_ BitVec 4))
(assert (= ((_ extract 0 0) s) (_ bv1 1)))
(assert (not (= ((_ extract 1 1) s) (_ bv1 1))))
```

`check_model` accepts that model, because the assertions it replays **are** the
encoding (blind spot A).

The same defect in the other direction: `(set.member #x5 (set.singleton #b0101))`
is true in the source and encoded to `((_ extract 0 0) (_ bv2 4)) = 1`, i.e.
`0 = 1` — a wrong `unsat`.

**Fix.** `set_element_key` keys on the literal's **value**: bit-vector literals
as `(width, bits)` with `#x` expanded four bits per digit and `(_ bvN W)`
converted by repeated halving of the decimal digit string (exact at any width,
no big-integer arithmetic); numerals and decimals as a normalized digit string
with leading integer zeros and trailing fractional zeros removed (exact at any
magnitude — it is a string normalization, not a parse, so there is nothing to
overflow). Anything it cannot canonicalize is **declined** as `Unsupported`
rather than falling through to text.

### 2a. A separate, opposite divergence on `2` vs `2.0` — recorded, not folded in

The first witness found was `(set.member 2 s)` with `(not (set.member 2.0 s))`
over `s : (Set Real)`, on the reading that SMT-LIB's `Reals_Ints` embedding
makes `2` denote `2.0` in a `Real` context — which is the reading this
repository already relies on elsewhere (`distinct_numeral_coercion.rs` pins that
`=`, `ite` and `distinct` all apply it).

**cvc5 rejects that script as a type error**: "member operating on sets of
different types: child type Int, not type Real", while accepting the same
coercion in `(= 2 2.0)`. So cvc5 is strict about sorts inside `set.member`
specifically. That makes the Int/Real pair an *argument* about the standard,
and a soundness report must not rest on one — which is why the headline witness
above is a same-sort bit-vector pair instead.

It is recorded here as a divergence in the other direction: **we accept a script
cvc5 rejects.** The fix collapses `2` and `2.0` to one key, and that is safe
under both readings — required under the embedding reading, and merely a
well-defined answer to an ill-sorted script under cvc5's. Whether we should
instead *reject* it is open; see §8.

## 3. Defect 2 — const-array elimination ignored both scope and order

`desugar_const_arrays` (`parse.rs:5049`) collected every
`(assert (= s ((as const …) v)))` with `for e in exprs.iter()` over the whole
top-level command list, then dropped the declaration, dropped the defining
assert, and textually inlined `s` into **every** command. That is exact
definition elimination only if the equation is in force at every `check-sat`.
Nothing checked that.

Two reachable wrong `unsat`s, each with two controls:

```smt2
; VARIANT 1 -- inlined across a `pop`. The binding is retracted, so `a` is
; unconstrained and this is SAT. Ours: unsat.
(declare-const a (Array Int Int))
(push 1) (assert (= a ((as const (Array Int Int)) 0))) (pop 1)
(assert (not (= (select a 5) 0)))
(check-sat)
```

| script | ours (pre-fix) | true |
|---|---|---|
| definition inside the popped scope | **`unsat`** | `sat` |
| definition deleted entirely (control) | `sat` | `sat` |
| definition at top level (control) | `unsat` | `unsat` |

The controls bracket it: we gave the popped script the answer belonging to the
unpopped one.

```smt2
; VARIANT 2 -- inlined BACKWARDS past a `check-sat`. No push/pop involved.
(declare-const a (Array Int Int))
(assert (= (select a 5) 1))
(check-sat)                                        ; source: SAT. Ours: unsat.
(assert (= a ((as const (Array Int Int)) 0)))
(check-sat)                                        ; source: UNSAT. Ours: unsat.
```

Variant 2 is the sharper one: ordinary SMT-LIB with two queries and no scoping
construct at all. It is also the more robustly demonstrable, because it needs no
reference solver to answer *both* queries — the first query **in isolation** is
`sat` on cvc5 and on ours, and in the full script we print `unsat` for it. The
wrong verdict is pinned without cvc5 needing to handle the second query (it
refuses multiple queries without `--incremental`, and with it hits
`STORE_ALL … try --arrays-exp`).

**Fix.** Collection moves to `eligible_const_array_aliases`, which takes a
definition only when it is in force at **every** `check-sat`: exactly one
definition script-wide (pre-existing), at **scope depth 0**, with no
`reset-assertions` after it, and no preceding verdict that could depend on the
symbol. The last condition is a disjunction — *either* no `check-sat` precedes
the definition, *or* the symbol occurs nowhere before it — rather than a blunt
"single `check-sat` only", so a multi-query script keeps the rewrite whenever the
symbol is defined before it is used. The precise rule was chosen over the
conservative decline deliberately: a refusal in front of a route nothing else
serves is expensive, and `MAX_SET_WIDTH`-style declines already exist where they
are genuinely needed.

## 4. Defect 3 — the finite-set universe was sized by a constant

`desugar_sets` set `width = d + SET_MARGIN_BITS` on the non-cardinality branch,
where `d` counts distinct **named literal** elements and `SET_MARGIN_BITS` is
the constant `2`. Nothing counted the free `(Set E)` declarations. A set
variable therefore had exactly `2^(d+2)` possible values, and an N-way
`distinct` over free set variables was refuted by pigeonhole for `N > 2^(d+2)`.

Measured, with both threshold controls — which pins the *mechanism*, not just
the symptom:

| script | ours (pre-fix) | cvc5 |
|---|---|---|
| 5 free sets, `d=0` → `5 > 2^2` | **`unsat`** | `sat` |
| 4 free sets, `d=0` → `4 ≤ 2^2` (control) | `sat` | `sat` |
| 5 free sets + one named literal, `d=1` → `5 ≤ 2^3` (control) | `sat` | — |

Five distinct subsets of an infinite sort plainly exist.

**The comment is part of this bug, not a footnote to it.** The module note
claimed, for *both* branches, that the encoding is "equisatisfiable, so neither
a wrong `sat` nor a wrong `unsat` is possible". The forward direction (no wrong
`sat`) does follow from conditions 1 and 2. The converse does not — it is a
claim about the **width**, and it was argued only for the `set.card` branch,
whose slack universe is sized from the script's own literals. The
non-cardinality branch inherited the conclusion without the argument. That is
how it shipped: **the comment did the arguing.** Meanwhile the comment on
`SET_MARGIN_BITS` itself said what the margin was really for — letting *two*
free sets differ on unnamed elements. Two. It was never sized for N.

**Fix.** The width now carries the witness demand explicitly, as a new condition
3 in the module note. Every unnamed element's behaviour under the accepted
(pointwise, complement-free) operators is determined by its membership vector
across the script's set variables, so two unnamed elements with equal vectors
are interchangeable; a model needs a separate slot only per distinction it must
**witness** — one per violated `=`/`set.subset`, and `n(n-1)/2` for a `distinct`
of arity `n`. `set_relation_witness_demand` over-counts that (it does not
separate polarities), which is the safe direction, and counts only operands that
are declared `(Set …)` symbols or `set.*` applications so that ordinary `Int`
equalities do not widen every set benchmark toward the cap. The cardinality
branch gets the same term added: its slack universe sizes for the **counts** a
script demands and says nothing about set-vs-set distinctions, and a script can
want both.

Past `MAX_SET_WIDTH` this **declines and does not clamp**. A
`min(demand, MAX_SET_WIDTH)` would reintroduce precisely this bug at a higher
threshold *while looking like a fix*, so the refusal has its own test
(`set_width_over_the_cap_declines`, 200 pairwise-distinct free sets = 19,900
slots) and the mutation table below shows that test is the only thing standing
in front of the clamp.

### A control that looks right and is not

Raising `d` with an element-**variable** does not work: `scan_set_ops` declines
a non-literal element, so `(declare-fun e () E)` plus `(set.member e s1)` never
raises `d` at all and the script answers `unknown`, not `sat`. The `d=1` control
must add a named **literal**. This cost one reviewer a contradictory reading
before it was noticed, so it is written into the test body as well as here.

## 5. What was made checkable

`crates/axeyum-solver/tests/parser_desugar_soundness.rs` — **18 tests**,
registered in `hooks/pre-push` (`check-suite-gating.py` at L0 reports
`gated=38 PASS`; ADR-2000's suite shipped registered nowhere and was caught
hours later).

Each test is aimed at the direction where the defect has somewhere to go, and
each is paired with a non-vacuity control differing in one small term — because
[ADR-1976] measured that a satisfiable query is a **vacuous** control: an
underconstrained `sat` stays `sat` under a deliberately broken rewrite, and two
reference solvers will agree with it.

**Guard-deletion result** (each guard disabled one at a time in a
`lane-snapshot.sh` copy, never in the shared worktree; every mutation asserts
its anchor matched exactly once, so a silently-unmatched edit reports
`MISSING SUBJECT` rather than the previous build's result):

| mutation | guards | tests killed |
|---|---|---:|
| `hex-own-keyspace` | `#x` shares the bit space with `#b` | 3 |
| `indexed-bv-own-keyspace` | `(_ bvN W)` shares it too | 1 |
| `keep-trailing-frac-zeros` | `1.50` normalizes to `1.5` | 2 |
| `keep-leading-int-zeros` | `07` normalizes to `7` | 1 |
| `all-literals-one-bit` | different values keep different bits | 4 |
| `drop-scope-depth-check` | a definition inside a `push` is ineligible | 1 |
| `drop-check-sat-order-check` | no earlier verdict may depend on the symbol | 1 |
| `drop-reset-assertions-check` | no `reset-assertions` after the definition | 1 |
| `drop-witness-demand` | the universe carries witness slots | 2 |
| `clamp-instead-of-decline` | a width past the cap declines | 1 |

**10 guards mutated, 0 untested, 10 distinct death-sets — separable.** Six kill
exactly one test. `all-literals-one-bit` is the mutation that proves the
non-vacuity controls bite: collapsing every literal to one bit kills three
controls and only one aliasing test. This matters because six of seven guards in
another suite here were removable with everything still green, all rejecting
through one shared check.

## 6. Cost: measured, not predicted

23 corpus files can reach these two desugars (15 use `set.*`, 8 use
`(as const`). Run back to back at a 20 s budget through a `94389e480` binary and
a fixed binary:

| | base | arm |
|---|---:|---:|
| files examined (denominator) | 23 | 23 |
| decided (`sat`\|`unsat`) | 15 | 15 |
| verdict strings differing | — | **0 of 23** |

Delta **0**. Eight of the 23 decline at parse in **both** arms with
byte-identical messages (non-literal elements, `set.comprehension`,
`set.choose`), so the width change introduces no new declines.

The expectation was zero and it is recorded as a measurement because the
expectation is not evidence: a freshness control was run first, confirming the
base binary reproduces all three wrong answers (5 sets `unsat`, bv-mixed `sat`,
popped-scope `unsat`) and the arm the corrected ones — otherwise a `delta=0`
would be equally consistent with having measured the same binary twice.

## 7. The inventory, and the answer to "can the guarantee be made real?"

A mechanical enumeration of `parse.rs` (615 `fn` declarations, 552 non-test;
five independent strategies reconciled — function enumeration, arena-builder
head-mismatch, symbol-minting sites, `Script` side-table writes, and a 23-keyword
comment scan) classified every transformation between text and
`Script::assertions`. Summarized by direction:

- **`equivalent`** — the bulk. `let` binding, `define-fun` macro inlining,
  `match` desugaring, the ~90 `apply_op` arms, indexed operators, chainable and
  associative folds, `Int`→`Real` coercion. Notably, **the parser folds no
  division or modulo by zero at all** — `div`, `mod`, `bvudiv`, `bvurem`,
  `bvsdiv`, `bvsrem`, `bvsmod` and the shifts go unconditionally to the IR
  builder on literal and symbolic operands alike, so there is no parse-level
  convention that could differ from the symbolic path (the `a946f925` class).
- **`weaker`** — eleven side channels (the `LenAbs` length abstraction, the
  opaque-term word skeleton, incomplete regex membership). **None enters
  `Script::assertions`**; each is kept beside them and each documented
  "sat only"/"unsat only" restriction has a corresponding **code gate**, not
  merely a comment. So the weakening rewrites are, as a class, the ones that
  were *already* handled correctly.
- **`stronger`** — where the three defects live, plus the intended ADR-0029
  bounded string/sequence encoding (models are a proper subset of the real
  theory; `sat` is genuine, `unsat` is bound-local and gated by `StringGate`).
- **`fresh-symbol / equisatisfiable`** — the ADR-2000 `distinct` injection
  (ships `Off`), quantifier binders, FP unspecified-conversion skolems,
  `seq.nth` out-of-bounds values, word-route witnesses. All but one mint into a
  firewalled internal namespace.

**So: is the general guarantee achievable?** No — not in the form the hard rule
states, and the reason is not implementation effort.

1. Replaying against "the originally parsed assertions" **cannot** work for a
   parse-level desugar, because the original parse is the encoding. To check
   defect 1 against the source you would need a second evaluator over
   s-expressions — a second implementation, and a second chance to disagree
   about a verdict.
2. No `sat`-side replay can see a wrong `unsat`. Defects 2 and 3 are invisible
   to it by construction.

**The honest answer is that per-rewrite arguments are the right design, and the
work is to make the arguments checkable rather than to generalize the check.**
That is what §5 does. The rule as written should be read as covering the
*solver*, where it is genuinely upheld — array elimination, theory combination,
word-level preprocessing, bit-blasting and the warm incremental engine all
project the model back and re-evaluate the **pre-rewrite** caller vector, and a
failed replay degrades to `Unknown` rather than being swallowed — and as **not**
covering the parser, where it never could.

## 8. Open, and handed off

- **Sort strictness inside `set.member`/`set.singleton`** (§2a). We accept
  `(set.member 2 s)` over `(Set Real)`; cvc5 rejects it. The fix is safe under
  both readings, but the divergence is real and unresolved.
- **The string-route model pairing — handed off, with a warning about the cheap
  option.** `solve_smtlib_with_model` on
  `(set-logic QF_SLIA) (declare-fun x () String) (assert (= (str.len x) 20))`
  returns `sat` with `assertions` = the packed flat vector (2 entries) and
  `model` = a **source-level `Seq`** model, so `check_model` returns
  `Err("no value bound for symbol #0")`. Control in the same run: plain QF_BV
  replays `Ok(true)`; two other string shapes correctly return
  `assertions=0, model=None` via `without_replay`, which is what makes the
  length-LIA route's pairing stand out rather than being how strings always
  behave. **The verdict is correct** — only the evidence pairing is wrong, so
  the damage is a *false alarm*: `axeyum-py`'s `Outcome.replay()` documents
  `Ok(false)` as "a soundness signal" and would raise it on a correct `sat`. A
  checker that cries wolf gets ignored, and then the real one is missed.

  Two repairs, and **they are not equivalent**:

  1. *Clear `assertions`* so the pairing is honestly "no replay available".
     Small, matches the three sibling routes, and makes the false alarm go away
     **by removing the evidence rather than by fixing it**. CLAUDE.md's rule is
     that every `sat` must be checkable against the original term, and this
     ADR's own headline is that our `sat`-side evidence is already thinner than
     advertised. This option makes it thinner again. It **reduces the fraction
     of `sat` results carrying evidence**, and that cost must be named and
     accepted, not assumed by picking the cheaper diff.
  2. *Lift the source-level model into the packed space* so the replay actually
     runs. This is the option that serves the guarantee. If it is too large for
     one lane it splits cleanly: (a) a `Seq`→packed-BV model lifter reusing the
     existing `decode_packed_string` direction in reverse, tested standalone
     against round-tripped models; (b) wiring it into the four post-`solve`
     routes one at a time, each with its own replay assertion.

  **Start from a measurement, not a preference — here it is.** Census over the
  three string divisions (`QF_S`, `QF_SLIA`, `QF_SEQ`), 3 s per file, through
  `solve_smtlib_with_model` + `check_model`:

  | | |
  |---|---:|
  | files examined (denominator) | 217 |
  | undecided at 3 s | 33 |
  | **`sat`** | **109** |
  |   `sat` withholding replay state (`without_replay`, honest) | 33 |
  |   `sat` carrying a model | 76 |
  |     replay `Ok(true)` | 71 |
  |     replay `Ok(false)` | **0** |
  |     replay `Err(..)` — symbol-set mismatch | **5** |

  So the mispairing is **live, not latent: 5 of 109 `sat` results (4.6 %), or 5
  of the 76 that carry a model at all (6.6 %)**. The five are named —
  `r0_QF_SLIA_issue4376`, `r1_QF_SLIA_issue4379`,
  `r1_QF_SLIA_re-inter-stack-ovf`, `r1_QF_SLIA_type002`,
  `cli__regress1__strings__type002` — all failing identically at
  `assertion #76 … no value bound for symbol #0`/`#1`.

  One precision that matters for the handoff: at the `check_model` level the
  failure is `Err`, and `Ok(false)` is **0**. The escalation to a *false
  soundness signal* needs `axeyum-py`'s `complete_with_defaults` to bind the
  unbound packed symbol first, turning the `Err` into an `Ok(false)` that its
  own docs call "a soundness signal". **That escalation is a static trace; this
  lane did not run the Python path.** The 5 is measured; the consequence
  downstream of it is not.
- **`inline_aliases` has no binder awareness** (`parse.rs:5215`) — a blind atom
  substitution. A `let` that shadows a const-array alias name corrupts the
  binder and the script dies with `syntax error: let name`. **Not a wrong
  verdict**, so it was withdrawn as a soundness issue, but it is a robustness
  regression on legal SMT-LIB and someone should own it.
- **Self-referential const arrays decline for the wrong reason.**
  `(= a ((as const …) (select a 0)))` fails with `unsupported: unknown
  identifier 'a'` — the declaration was dropped out from under the inlined copy.
  The right outcome by accident; recorded because a clean decline that arrives
  by accident will not survive a refactor.
- **Three comments claim a `RoundingMode` well-formedness constraint is
  asserted at declare time** (`parse.rs:7002`, `16481`, `16512`). It is not; the
  real mechanism is `canonicalize_sort_bits` in `axeyum-bv`. Behaviour is
  correct, but three comments point a soundness auditor at a nonexistent
  assertion path — the same failure mode as §4.
- **`parse.rs:209` says `word_problem` "may only ever add `sat`, never
  `unsat`"** — false against `refute_word_equations`. The `unsat` direction is
  sound; the comment is stale.
- **Well-formedness constraints are gated on `args.is_empty()`**
  (`parse.rs:6395`–`6423`), so a 0-ary `String`/`(Seq E)`/`(_ FiniteField p)`
  gets its constraint and an **n-ary** one gets nothing. Flagged by the
  inventory as a code-reading finding; **not reproduced by running anything in
  this lane**, and recorded at that confidence.

## Decision

1. Key finite-set element bits on the literal's **value**, and **decline** any
   literal that cannot be canonicalized rather than keying on its text.
2. Eliminate a const-array definition **only where it is in force at every
   `check-sat`** — depth 0, no later `reset-assertions`, no earlier verdict
   depending on the symbol.
3. Size the finite-set universe from the **witness demand** the formula makes,
   and **decline past the cap rather than clamping**.
4. Correct the module note's condition 1 and add condition 3 **in place**. A
   false soundness claim in a comment is load-bearing: two of these three
   defects shipped because a comment asserted what nothing checked.
5. **Do not attempt a general "replay against the original" guarantee for
   parser rewrites.** It is unachievable for parse-level desugars and
   irrelevant to wrong `unsat`. Require instead, for every new or changed
   parser rewrite, a stated direction and an adversarial test aimed at the
   direction where that rewrite can fail — registered at L0.

[ADR-1976]: adr-1976-a-sat-side-reference-control-is-vacuous.md
[ADR-2000]: adr-2000-the-front-door-refusal-was-not-the-binding-constraint.md
