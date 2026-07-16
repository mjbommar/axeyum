# P6.6-paper — the attempt, and what it returned

**Status: partially executed, 2026-07-15. It changed the plan.**

The plan said P6.6-paper is a week's work that can kill the track: take one
quantified-UF goal from the 0/5 set, write the decomposition by hand, and answer
whether it is machine-findable.

I started it. **I did not get as far as writing a decomposition, because running
the goals first invalidated the question.**

## What the 0/5 actually is

The framing carried through all four thesis drafts was: *quantified UF is 0/5,
therefore decomposition in that fragment is research-hard.* Round 3 sharpened it
into what I accepted as an unanswerable rebuttal:

> "If Skolemization + congruence + `decide` sufficed, quantified UF would not read
> 0/5."

**That inference is invalid.** It assumes we tried and failed. We never tried.

`bench-results/SCOREBOARD.md`, the actual row — note the columns:

```
| Division | Slice                             | Files | Decided | Decide% | Unknown | Unsup | ... | PAR-2 (s) |
| UF       | uf-cvc5-regress-clean-quantified  |   5   |    0    |   0%    |    0    |   5   | ... |   0.000   |
```

**`Unknown = 0`. `Unsup = 5`. `PAR-2 = 0.000`.** Not five timeouts — **five honest
declines, costing zero time.** The scoreboard was never claiming we searched and
lost; it says `unsupported`, and I read it as `hard` for four drafts.

## Running all five (each < 10 ms)

Reproduce with a ten-line probe over `axeyum_solver::solve_smtlib` against
`corpus/public-curated/quantified/UF/cvc5-regress-clean/`:

| Instance | `:status` | Elapsed | Why we decline |
|---|---|---|---|
| `fmf__ALG008-1` | sat | 0.76 ms | `"query has quantifiers instantiation does not reach (nested, existential, or non-top-level)"` |
| `fmf__nlp042+1` | sat | 9.4 ms | same |
| **`fmf__PUZ001+1`** | **unsat** | 1.4 ms | same |
| `fmf__no-minimal-sat` | sat | 1.4 ms | `"declared-sort QF_UFBV lazy route is outside the current abstraction: term #0 has sort (Uninterpreted 0) that the pure-Rust BV backend cannot bit-blast"` |
| `quantifiers__inst-max-level-segf` | unsat | 0.31 ms | **parse error** — `"unsupported: parametric/arity-1 declared sort `GrassArray` (only arity-0 uninterpreted sorts are supported)"` |

**The 0/5 is three distinct missing features, none of them research:**

1. **No Skolemization** (3/5, including the one `unsat` that matters). Textbook.
2. **Carrier not bounded** (1/5). We do **not** bound carriers — QF_UF's 54–67% is
   achieved *by* bounding them (`SCOREBOARD.md:51-53`). **That was false too** —
   we do not bound uninterpreted carriers anywhere; `bounded`/`overbound` name the
   eager Ackermann budget, not a cardinality. See note 08's correction.
3. **Parser rejects arity-1 sorts** (1/5). `(declare-sort GrassArray 1)` is
   ordinary SMT-LIB. This one never reaches the solver at all.

## WITHDRAWN — "Why PUZ001+1 declines, concretely"

**This section argued that PUZ001+1 declines for want of Skolemization, that
`pel55_3`'s domain-closure gives a three-element carrier, and that "none of them is
a research problem." All three are wrong.** Round 4 refuted them and I verified it.
The section is withdrawn rather than deleted, because the *shape* of the error is
the most useful thing in this file.

### Why it was wrong — three independent refutations

**1. Skolemization carries the goal OUT of the fragment, not into it.** All three
of Dreadbury's functors are constants. Skolemizing `pel55_10` (`∀X ∃Y. ¬hates(X,Y)`)
introduces a **unary function symbol under a universal** — which **leaves EPR**
(Bernays–Schönfinkel: `∃*∀*`, no function symbols). EPR is the one quantified-UF
fragment with the **finite-model property**, and therefore the only one where
carrier-bounding is sound for `unsat`. **The fix I proposed destroys the property
the fix depends on.**

**2. The three-element carrier does not exist.** `pel55_3` is **relativized to
`lives`** — a model may hold non-living elements. Bounding to `{agatha, butler,
charles}` refutes only 3-element models; it licenses no `unsat`. **I noticed this
and filed it as an "honest caveat," then reasoned past it** — the same move v2 made
with W1: find the refutation, call it a nuance, keep the conclusion.

**3. The refutation needs a second instantiation round, and we do one.** Working it
by hand: the `butler` case closes only via `pel55_7`/`pel55_9` instantiated at
**`f(butler)`** — a term that exists only *after* `pel55_10` is instantiated at
`butler`. `quantifiers.rs:475` collects ground subterms **once, from the inputs**:
`let ground = ground_subterms(arena, assertions, &bound);`. Single-pass. So closing
this goal needs Skolemization **plus a fixpoint over a now-infinite Herbrand
universe** — i.e. **an instantiation depth policy. A depth policy is a search
heuristic.**

**That is F5.** The goal I offered as the *plumbing* example is where the search
premise bites hardest.

### And `PAR-2 = 0.000` is what a correct boundary looks like

`auto.rs:5244-5252`, verbatim — a **correctness statement, not a TODO**:

> ```rust
> // Quantifiers left after instantiation (nested, existential, or non-top
> // level) cannot be decided by the quantifier-free engines.
> if instantiation.residual_quantifier { return Ok(CheckResult::Unknown(..)) }
> ```

Instantiation only **weakens**, so a residual quantifier licenses no verdict. It is
fast because checking a flag is fast. **I read *speed* as *unseriousness*.**

And the split I built the argument on is a **harness artifact**: the solver returns
`Unknown(Incomplete)`; `Unsup` is a bucket in `bench/src/main.rs:4626`. The
`Unknown=0 / Unsup=5` distinction that carried the whole finding is a
classification nobody traced — including me, while claiming to have traced it.

### What survives

Only this, and it is worth little: **the error strings are informative**, and two
items are free wins independent of everything — the **arity-1 sort parse rejection**
(ordinary SMT-LIB we don't accept) and the **`!fn_app_0` Ackermann collision**
(minimal repro below), which blocks every quantified-UF goal with a genuine
non-predicate function.

**"None of them is a research problem" is withdrawn.** One of them is exactly the
research problem this track exists to test.

## I tested my own claim, and it was over-read

The finding above says the 0/5 is "missing Skolemization, not fragment hardness."
**Before writing that down as settled, I hand-Skolemized PUZ001+1 and ran it** —
because "it's just plumbing" is exactly the kind of unexamined premise this track
keeps dying of, with the sign flipped.

Skolemizing by hand: `pel55_1`'s `∃X. lives(X) ∧ killed(X, agatha)` → a constant
`sk`; `pel55_10`'s `∀X ∃Y. ¬hates(X, Y)` → a Skolem **function** `f : sort → sort`
with `∀X. ¬hates(X, f X)`. Every quantifier is then a top-level `∀`.

**It does not decide. It hits a different bug:**

```
ERR after 766.751µs: Backend("symbol `!fn_app_0` already declared with sort Bool,
                              requested (Uninterpreted 0)")
```

### The bug, minimised to seven lines

```smt2
(set-logic UF)
(declare-sort S 0)
(declare-fun p (S) Bool)      ; a predicate
(declare-fun g (S) S)         ; a function
(declare-fun a () S)
(assert (forall ((x S)) (not (p (g x)))))   ; nested app under a quantifier
(assert (p a))
(check-sat)
```

→ `Backend("symbol `!fn_app_0` already declared with sort (Uninterpreted 0), requested Bool")`

**Controls, to place the fault precisely:**

| Case | Result |
|---|---|
| predicate only, quantified (`∀x. ¬p x`) | **`Unsat`** ✓ |
| predicate + function, **unquantified** | **`Sat`** ✓ |
| function only, unquantified | **`Sat`** ✓ |
| **predicate + function, quantified, nested app** | **`Backend` error** ✗ |

The Ackermannization symbol counter (ADR-0013) **reuses `!fn_app_0` across two
different result sorts**: `g x` claims it as `S`, `p (g x)` claims it as `Bool`.
The error direction flips between the PUZ file and the minimal case, confirming
name reuse rather than a sort-inference fault.

**Note it is an error, not a wrong answer.** The rejection discipline held — this
is deferral-by-rejection, which is the safe kind.

### What this does to the finding

**The finding survives in kind and is wrong in degree, and that distinction is the
point.**

- Still true: **none of this is research.** It is a naming collision.
- **No longer true: "implement Skolemization and re-run."** Skolem functions *are*
  sort-valued functions under quantifiers — precisely the shape that trips this.
  Skolemization is **necessary but not sufficient**; the route it produces hits
  this bug on its first step.
- **The blocker count went from three to four**, and the fourth was only findable
  by *doing* the fix by hand. I would have written "days" for T6.6.0 and been
  wrong, in the direction I wanted.

**T6.6.0 is therefore: fix the `!fn_app_0` collision, implement Skolemization, re-run
the five, publish the number.** Still small. But nobody should claim a number for
it until the collision is fixed, because until then the route has never executed.

**A free win, independent of any prover:** the collision blocks *every* quantified
UF goal with a genuine (non-predicate) function. That is not a corner case; it is
most of first-order logic. It is worth fixing on its own merits and it is owed to
Track 2 regardless.

## What this does to the plan

**Delete the 0/5 as evidence about hardness.** It is evidence about plumbing. It
should not appear in any argument — for or against — until we have Skolemized and
re-measured. It was doing work in:

- **v3** (as a reason to refuse: "a shell over a hole") — invalid.
- **v4** (as the reason the layer exists: "the 0% column is the reason for the
  layer") — also invalid, and it was *my* argument.
- **Round 3's F5** (the premise-level attack this plan is built around) — the
  inference is invalid, though **the underlying premise survives**: certificate-first
  still says nothing about how to *find* a decomposition. That question is
  untouched. What dies is the *evidence* offered for it.

**A new, cheaper test now precedes P6.6-paper.** Before writing a decomposition by
hand, do the thing nobody has done:

> **P6.6-probe (S, days): implement Skolemization; re-run the five; publish the
> number.**

Three outcomes, all informative:
- **PUZ001+1 decides.** Then quantified UF was never a wall, the fragment is
  cheaper than anyone thought, and P6.6-paper's premise needs re-framing against a
  goal we actually cannot do.
- **It searches and fails.** *That* is the evidence round 3's F5 wanted, and it
  will be real for the first time.
- **It searches and times out.** Now PAR-2 says something, and the 0/5 becomes a
  number about hardness instead of about coverage.

**And two of the five are free wins regardless**: arity-1 sorts are a parser
feature, and carrier bounding does **not** exist. Both are owed independently of any
prover.

## The meta-lesson, one more time

Round 3 called F5 "unanswerable" and I agreed. It was answerable — by **running the
five goals**, which takes ninety seconds and which nobody in four drafts and three
adversarial rounds did. The premise was a fact about our own code, sitting one
`cargo run` away, and every party to the argument reasoned about it instead.

> **The adversary checks your reasoning; only the world checks your premises.**

That sentence was already the diary's conclusion. This is it applying to the
sentence itself.
