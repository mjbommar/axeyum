# QF_NIA is a model-production problem — and ADR-1937 already took most of it

Lane `qf-nia-sat`, 2026-09-13. Census binary sha256
`5584b17125ef0e9c0e09c6f542756c2d403f92b84455b5fe19bb25302839006f`, built from
this branch; verified newer than every `crates/**/*.rs` at census time.

This lane was briefed to test one hypothesis: **QF_NIA is held by our inability
to produce and confirm models, not by refutation power.** The hypothesis is
right. The brief's *sizing* of it is not, and the correction is the first
result here.

## Result 0 — the target is 40 files, not 64, and the reason is ADR-1937

The brief sizes the sat half at "64 of ~110 winnable", read from
`bench-results/winnable-polarity-20260913/`. That board snapshot predates
ADR-1937. ADR-1937 was a **model-construction** fix (it pinned `int_add`/`int_sub`
/`int_neg` against wraparound so the exact-integer replay stopped rejecting the
blaster's models), so the files it harvested are exactly the ones this lane was
sent to find.

Measured on the committed A/B (`qf-nia-dispatch-20260912/ab-division-200.tsv`),
cross-referenced to ground truth per file:

| ADR-1937 armed verdict | ground truth | files |
|---|---|---:|
| `sat` | `sat` | **32** |
| `unknown` | `sat` | 40 |
| `unknown` | `unsat` | 38 |

> **Every one of ADR-1937's 32 gains on the winnable population was `sat`. Zero
> were `unsat`.** That is the polarity thesis confirmed on the only natural
> experiment available — and it is also why the remaining target is smaller than
> the brief says.

**Remaining winnable: 78 = 40 `sat` + 38 `unsat`, 51 % satisfiable** (the stale
board says 65 % of 110). Population in `remaining-winnable.{txt,tsv}`; ground
truth is the declared `:status` where present, else the board's z3/cvc5 verdict,
and both are recorded per row.

## Result 1 — the "replay failed" class is EMPTY

The brief asks for the sat half split three ways: no model produced / model
produced but replay against the original assertions failed / model produced too
late. Re-censused on a fresh build of this tree, all 78 files, 0 processes
killed, 0 rows without a stated reason (`census-78.tsv`):

| failure mode | sat | unsat |
|---|---:|---:|
| no model produced | **40** | 38 |
| model produced, replay failed | **0** | 0 |
| model produced, too late | 0 | 0 |

The middle bucket was 25 files at the previous census and is now zero. The
exact-integer replay in `lia.rs`/`combined.rs` is the only thing that emits
`bounded integer model overflowed at width N (assertion #K is false over exact
integers)`, and no file says it any more. **ADR-1937 closed that class
completely.** What is left is not a confirmation problem; it is that the search
never produces a candidate at all.

## Result 2 — the polarity asymmetry is in the CLOCK, and it is stark

| | spends ≥98 % of the 24 s budget | median budget used |
|---|---:|---:|
| `sat` half (40) | **8 of 40 (20 %)** | **45 %** |
| `unsat` half (37 with a trail) | **33 of 37 (89 %)** | **100 %** |

The unsat half is genuinely clock-bound: 32 of 38 are `ladder-clock` at 24.1 s.
The sat half is not. It quits with **more than half the clock unspent**, and the
reason is one refusal.

### The sat half by honest cause (ADR-1971: decline time is printed, not assumed)

| cause | n | decline time (s) | `bound_by` (ADR-1941) |
|---|---:|---|---|
| `cnf-budget` | **29** | min 10.9 med **11.8** max 23.4 | `nia-linearize` = 29 |
| `ladder-clock` | 8 | med 24.1 | `int-blast-ladder` = 8 |
| (decided by this tree) | 3 | med 20.9 | `int-blast-ladder` |

### ADR-1950 — which budget, and what was left of it

| cause | n | ms consumed by `bound_by` | total ms | **unspent** |
|---|---:|---|---|---:|
| `cnf-budget` | 30 | med 6,684 | med 10,828 | med **13,172 ms (55 %)** |
| `ladder-clock` | 40 | med 13,366 | med 24,076 | med −76 ms (0 %) |

`nia-linearize` burns ~6.7 s, the file reaches the ladder at ~10.8 s, and the
ladder refuses **instantaneously** on a pre-lowering clause estimate. Thirteen
seconds of the budget are then used by nothing.

The estimates are **1.16x–4.49x over the 64,000,000 ceiling, median 2.00x** —
and **0 of 30 exceed it by more than the 9.4x slack a previous lane already
lifted**. That lane (`docs/plan/notes/118-nia-diagnosis.md`) measured the lift at
**0 of 49 decided, 0 memory aborts**, with the decisive sentence: *"the refusal
was in front of a search that does not finish either."* So the budget is not the
blocker and raising it is a closed question. The multiplies are the blocker.

## Result 3 — sizing the one unrefuted hypothesis, before building it

That same note left exactly one hypothesis standing: an **eager** small-domain
split. Every product in these files has the shape `(* Nl<k> lam<j>)` where the
`Nl` factor is pinned to `[-2, 2]` by a top-level conjunct and `lam` is
unbounded — 1,775 `*` occurrences in the first file, all of that shape.
`nia_linearize::small_domain_lemmas` already implements the split, but only
inside the **relaxation**, whose own docs say only `unsat` transfers; it
structurally cannot produce a `sat`.

Rather than build the route and find out, the transformation was performed
**outside the solver** and the existing CLI run on the result
(`scripts/qf-nia-sat-eager-split-surrogate.py`). For `lo ≤ a ≤ hi` entailed by
top-level conjuncts, `a*b` becomes an `ite` chain over `a`'s values with each
branch a numeral multiple of `b`. That is an identity under those bounds, so it
is equisatisfiable in **both** directions, unlike the relaxation.

Two measured details that changed the answer rather than decorating it:

- The generators wrap the narrow factor as `(+ 0 Nl2arg133)` and `(* Nl4arg33 1)`.
  Without folding those, 78 of 126 residual products on the first file were
  hidden from the narrow-factor test.
- `estimate_blast_clauses` charges `Op::BvMul` a flat `8w²` **with no case for a
  numeral operand**. Emitting branches as `(* 2 b)` left the estimate at
  82,057,350 against the 64,000,000 ceiling. Emitting them as sums — what a real
  lowering does anyway — brought it to 66,466,002. Leaving it as `*` would have
  sized the estimator's blind spot rather than the transformation.

### The bracket

| condition | decided |
|---|---:|
| surrogate, fresh 24 s budget for the whole transformed file | 7 of 29 (one at 24.3 s, over budget → **6**) |
| **in-solver, rung at its natural position** | **4 of 29** |

The in-solver number is the honest one and is measured, not modelled
(`inslice-budget*.tsv`): the eager split changes only the query handed to
`int-blast-ladder`; every route before it still runs on the original query and
still costs what the census says. So the condition is

    ladder_elapsed(transformed)  ≤  24 s − total_ms(original)

with both sides measured per file. Pre-ladder cost is ~10.8 s, leaving ~13.2 s;
ladder times on the transformed queries run 3.9 s to 19.4 s.

### Noise floor — three repeats at one commit, one binary

| repeat | files that fit | files decided |
|---|---:|---:|
| 1 | 4 | 6 of 7 |
| 2 | 3 | 6 of 7 |
| 3 | 5 | 7 of 7 |

**Spread 2 on a mean of 4.** The measurement noise is half the effect. Per
ADR-1970's precedent that is a reason to state the bracket as **3–5** and not to
quote a point estimate.

## Result 4 — the obvious control is vacuous, and that is itself the finding

The surrogate's first control re-checked each transformed file against z3 and
cvc5 and compared to the original's `:status`: **0 disagreements on 29 of 29,
0 files where neither reference had an opinion.**

That zero is worthless on its own. Mutating the case-split scaling so `a = k`
implies `r = (k+1)·b` — a plainly wrong linearization — **also** produced
0 disagreements, on 5 of 5 files. The reason is structural: these queries are
satisfiable and underconstrained, so a wrong linearization still has a model,
just a different one. A sat-side reference check cannot tell a correct transform
from a broken one.

The control with teeth runs the same transform over the **unsat** winnable files,
where a wrong linearization has somewhere to go
(`scripts/qf-nia-sat-transform-control.py`, `transform-control.tsv`):

| arm | unsat files that z3 turned `sat` | requirement |
|---|---:|---|
| correct transform | **0** | must be 0 |
| mutant (off-by-one scaling) | **6 of 10** | must be ≥ 1 |

7 of 10 files were actually rewritten (`split > 0`); z3 had an opinion on 9 of
10. The script's **exit status depends on both** arms: it fails if the correct
arm flips anything, and it also fails if the mutant arm flips nothing, because
then the zero means nothing.

## Recommendation — do not build the eager-split route now

Against this repository's running blocker→reachable tally (143→6, 51→2, 173→10,
84→49, 27,150→1,135, 19,620→0, 177→0, 934→0, 46→2), this is **29→3–5**.

- The payoff is **4 files of a 78-file remaining gap**, within 2x of its own
  measurement noise.
- Getting the upper end (6) requires moving the split **ahead** of
  `int-real-relax` and `nia-linearize`, which taxes every integer-bearing query
  in every division to convert four files in one.
- The implementation is not a lever: it is an equisatisfiable rewrite inside the
  blaster, carrying real soundness obligations, whose own natural control was
  just shown to be vacuous on exactly the polarity it targets.

What is worth keeping is the measurement: the eager split is now **sized and
closed**, so the next lane at this division does not re-derive it. The one
hypothesis the 2026-09-12 note left standing has been tested.

## What would actually move QF_NIA, in the order the data supports it

1. **The 38 `unsat` files are now the larger half of the remaining gap** (38 vs
   40) and are genuinely clock-bound — 89 % spend the whole budget. The polarity
   argument that sent three lanes at refutation was correct *for the pre-ADR-1937
   population* and is close to balanced now.
2. **Thirteen seconds per sat file are used by nothing.** The ladder refuses
   instantaneously at ~10.8 s and no route uses the remainder. Any route that can
   produce a *candidate model* without bit-blasting the whole query has a free
   budget to run in — the eager split is one such route and it is worth 4; a
   direct small-witness enumerator over the declared `[-2,2]` boxes has not been
   sized and is the obvious next one, because the narrow variables are exactly
   the ones a witness search would branch on.
3. `estimate_blast_clauses` has no numeral-operand case for `BvMul`. On the
   original files a popcount-aware charge was measured at 6 % and correctly
   dropped — but on a query that introduces constant multiples the same blind
   spot is worth **19 %**, measured here (82,057,350 → 66,466,002 on one file by
   emitting the branches as sums instead of `*`). Every linearization introduces
   them, so it matters for the *next* rewrite, not this one.

## Files

| file | what it is |
|---|---|
| `remaining-winnable.{txt,tsv}` | the 78-file post-ADR-1937 population with per-row ground truth |
| `census-78.tsv` | raw census rows: verdict, rc, wall, kind, detail, decided_by, bound_by, last, bound_ms, total_ms, attempts, phase |
| `census-78-classified.tsv` | the same rows plus `truth`, `cause`, `mode` |
| `eager-split-surrogate-29.tsv` | the offline eager split over the 29 `cnf-budget` sat files, with z3/cvc5 on the transformed query |
| `inslice-budget.tsv`, `-rep2`, `-rep3` | the in-solver bracket, three repeats — the noise floor |
| `transform-control.tsv` | the two-arm control: correct vs mutant transform over unsat files |

Scripts: `scripts/qf-nia-sat-{population,census-split,budget-detail,eager-split-surrogate,residual-shapes,realistic-budget,inslice-budget,transform-control}.py`.
The census itself reuses `scripts/qf-nia-dispatch-census.py` unchanged.

## Caveats, stated so nobody quotes them as load-independent

- `ladder-clock` (40) and `watchdog` (1) are load-sensitive rows; this sweep ran
  at three-way parallelism on a shared box. Inflation can only move files **out
  of** the structural classes, so 29 is a floor for `cnf-budget`.
- The in-solver bracket is an **estimate of an unbuilt route**, assembled from
  two measured halves. It assumes the split costs nothing to apply, which was
  true offline (transform time ≈ 0.0 s) but is not free inside the blaster.
  It is therefore optimistic, which is the safe direction for a "do not build".
- cvc5 timed out at 60 s on 5 of the 7 surrogate winners, so for those the
  transformed-query confirmation rests on z3 and the declared `:status` alone.
  The strong evidence for a `sat` is a replaying model, not a reference verdict,
  and no model is claimed here — nothing in this directory ships a verdict.
