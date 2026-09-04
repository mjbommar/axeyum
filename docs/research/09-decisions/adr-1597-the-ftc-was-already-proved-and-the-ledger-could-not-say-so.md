# ADR-1597: The FTC was already proved, the ledger could not say so, and the textbook form is what was missing

Status: accepted
Date: 2026-09-04
Lane: `ftc`

Index-summary: Roadmap item W1-2 asks for the fundamental theorem of
calculus, "both directions over the existing Riemann integral", and the
constructive-analysis persona file records the specialist reviewer's first
item as "the FTC is not there". Both directions were in the kernel a week
before that file was written: `CReal.hasDerivative_antiderivative` (FTC-I)
and `CReal.integral_eq_antideriv_diff` (FTC-II), both admitted 2026-08-27,
both `axiom_footprint: []`, together with `CReal.integral_by_parts`. Both
have registered, `proved` facts. The reason a survey did not see them is
that 307 of the 476 `CReal` facts (64%), and 1054 of 2758 ledger-wide
(38%), carry the fact generator's prose, which opens "MECHANICALLY
GENERATED, UNREVIEWED PROSE -- this sentence deliberately makes NO
mathematical characterisation of the theorem." The generator's refusal is
correct in itself and is the reason the ledger can be trusted; the defect
is that nothing distinguishes "no prose has been written" from "there is
nothing here", so the ledger answers "is X proved?" and cannot answer "what
do we have?". What was genuinely missing is the STATEMENT a reader looks
for: both existing theorems take a `(kb : Nat)` and a `BoundedOn F a b kb`
witness the caller must build, and both are redundant, since
`CReal.bounded_of_uniformly_continuous` COMPUTES such a `kb` from the
`UniformlyContinuousOn` witness already in scope. This ADR records two new
theorems that discharge it -- `CReal.hasDerivative_antiderivative_of_uc`
(arity 7 to 5) and `CReal.integral_eq_antideriv_diff_of_uc` (arity 9 to 7)
-- one mutation-verified test, and two CURATED facts whose prose says what
the theorems assert and what they do not.

Index-status: accepted

## Context

The brief for this lane was to prove the fundamental theorem of calculus,
constructively, over the existing `CReal` Riemann integral, and it named a
research strand and a persona file that both record the theorem as absent:

- `docs/math-department/00-roadmap.md`, W1-2: "Both directions over the
  existing Riemann integral. The specialist reviewer's first item."
- `docs/math-department/02-constructive-analysis.md`, last measured
  2026-09-04: "The fundamental theorem of calculus is not there, which is
  startling given that both halves of it are nearly in hand."

Neither is true. `git log -S` on the name registry dates both directions to
2026-08-27:

| commit | date | subject |
|---|---|---|
| `1b91195d0` | 2026-08-27 | feat(creal): the Fundamental Theorem of Calculus, part I |
| `d1bdae9e7` | 2026-08-27 | feat(creal): the Fundamental Theorem of Calculus, part II |

Measured on this lane's tree with `shape_search --include-constructed`
(`declarations=3550`, positive control `CReal.addGroupS`, the newest
declaration-adding commit in the tree at 2026-09-03):

```
CReal.hasDerivative_antiderivative   theorem  arity=7
  CReal -> CReal -> CReal -> CReal.le -> CReal.UniformlyContinuousOn
        -> Nat -> CReal.BoundedOn -> CReal.HasDerivativeOn
CReal.integral_eq_antideriv_diff     theorem  arity=9
  CReal -> CReal -> CReal -> CReal -> CReal.le
        -> CReal.UniformlyContinuousOn -> Nat -> CReal.BoundedOn
        -> CReal.HasDerivativeOn -> CReal.Equiv
```

`CReal.integral_by_parts` is there too. All three have `proved` facts with
empty axiom footprints.

## The measured root cause of the false absence

The facts exist; their prose does not characterise them. Every generated
fact's `statement` field begins:

> MECHANICALLY GENERATED, UNREVIEWED PROSE -- this sentence deliberately
> makes NO mathematical characterisation of the theorem.

`scripts/gen-kernel-facts.py` withholds the characterisation on purpose, and
the reasoning in its docstring is right: bulk-generating prose is exactly how
this repository's central audit finding ("checkers that cannot fail") gets
reproduced at scale. The refusal is not the defect.

The defect is the population it leaves behind. Measured 2026-09-04 over
`artifacts/facts/*.json`:

| population | total | generated prose | share |
|---|---:|---:|---:|
| all facts | 2758 | 1054 | 38% |
| `fragment == CReal` | 476 | 307 | **64%** |
| `Str` | 64 | 64 | 100% |
| `Complex` | 128 | 83 | 65% |
| `CPoint` | 94 | 62 | 66% |
| `Nat` | 1042 | 250 | 24% |

Two thirds of the constructive-real shelf is invisible to any survey that
reads prose, and the FTC is in that two thirds. That is sufficient to explain
a roadmap item asking for finished work in the department's flagship strand,
at the specialist reviewer's stated first priority.

The general rule this instance teaches, stated so it transfers: **an
honest refusal to characterise is still an absence in the index, and an
index with a blind majority produces false absences at the level above
it.** The ledger's own `epistemic_status` axis answers "is this proved?"
perfectly. Nothing in it answers "what do we have?", which is the question
a roadmap is built from.

This ADR does not attempt the general fix (curating 1054 facts, or adding a
`characterisation_status` axis the validator can report on). It records the
measurement and demonstrates the shape of the fix on two facts.

## The decision

### 1. The FTC statement forms that were actually missing

Both existing theorems demand of their caller a magnitude bound:

```
(kb : Nat), BoundedOn F a b kb -> ...
```

Both are redundant. `CReal.bounded_of_uniformly_continuous` has type

```
forall F a b, UniformlyContinuousOn F a b -> le a b -> BoundedOn F a b K
```

for a **computed** `K` -- one `Nat` expression in `F`, `a`, `b` and the
uniform-continuity witness, never an `Exists` that would have to be
eliminated (and could not be, since `HasDerivativeOn` is `Type`-valued). Both
`UniformlyContinuousOn F a b` and `le a b` are ALREADY hypotheses of both FTC
theorems. So the bound was never a real side condition; it was a convenience
at the time of writing.

Two theorems, admitted through `Kernel::add_declaration` in the new build step
`integral::declare_ftc_of_uc`:

```
CReal.hasDerivative_antiderivative_of_uc
  : forall (F : CReal -> CReal) (a b : CReal) (hab : le a b)
           (u : UniformlyContinuousOn F a b),
    HasDerivativeOn (antiderivative F a b hab u) F a b

CReal.integral_eq_antideriv_diff_of_uc
  : forall (F G : CReal -> CReal) (a b : CReal) (hab : le a b)
           (u : UniformlyContinuousOn F a b),
    HasDerivativeOn G F a b
    -> Equiv (integral F a b hab u) (add (G b) (neg (G a)))
```

Arity 7 to 5 and 9 to 7. These are the statements a textbook writes, and they
are what a reader looking for "the fundamental theorem of calculus" can apply
without first constructing a magnitude bound by hand.

The proof term in each case is the existing theorem applied. No estimate is
re-proved and no modulus changes.

### 2. The modulus, and what "constructively" buys

`CReal.HasDerivativeOn F F' a b` is Bishop's UNIFORM differentiability on a
closed interval: a `Type` carrying an explicit `modulus : Nat -> Nat` as a
DATA field, with

```
spec : forall (e : Nat) (x y : CReal), a <= x -> x <= b -> a <= y -> y <= b
     -> |y - x| <= 1/(modulus e + 1)
     -> |F y - F x - F' x * (y - x)| <= (1/(e+1)) * |y - x|
```

The modulus is not an existential, which is why `HasDerivativeOn` has to be
`Type`-valued and why nothing in this development ever eliminates it into a
`Prop`. FTC-I's modulus, unchanged by this lane, is

```
E |-> modulus_of_uniform_continuity(F, a, b, u)(2E + 1)
```

so two halves of `1/(2E+2)` sum to the `1/(E+1)` the spec asks for.

This is STRONGER than the classical pointwise statement, not a weakening of
it. Three places where the classical statement is not the one proved:

- **Uniform, not pointwise.** The spec quantifies over an unordered pair
  `x, y` in `[a, b]` with `|y - x|` inside one global modulus. There is no
  punctured limit anywhere.
- **`Equiv`, not `Eq`.** FTC-II concludes `CReal.Equiv`, the Bishop-setoid
  equality on regular sequences (ADR-0512). `0.999...` and `1` are distinct
  `CReal`s and `Equiv`-equal.
- **Uniform continuity of the integrand is load-bearing, not decorative.**
  `CReal.le` is undecidable, so "sup over partitions" is unavailable; a
  merely pointwise-continuous function is not integrable by this route at
  all.

### 3. No mean value theorem is used, and that is the point

The brief anticipated needing the constructive MVT for FTC-II (roadmap item
W2-20) and asked for a precise account if it was missing. It is not needed,
and the existing FTC-II proof shows why. The classical evaluation-rule proof
goes through the MVT, which is an existence statement that constructively
needs an apartness witness nobody can produce for an arbitrary continuous
function. The route in `declare_integral_eq_antideriv_diff` avoids it:

1. `A := antiderivative F a b hab u` is an antiderivative of `F` (FTC-I).
2. `G` is another, so `G - A` has derivative zero
   (`has_derivative_sub` + `add_neg`).
3. `constant_of_zero_deriv` gives `G a - A a ~ G b - A b`.
4. `A a ~ zero` and `A b ~ integral F a b hab u` are both instances of the
   same degenerate-interval fact.

What replaces the MVT is the UNIFORMITY of `HasDerivativeOn`. Because the
modulus is global on `[a, b]`, constancy of a zero-derivative function
follows from a uniform estimate rather than from a point whose existence
must be asserted. **The constructive MVT is not a prerequisite for the
FTC here, and W2-20 should not be sequenced as one.**

## Evidence

Every gate below was run by this lane on this tree.

| gate | result |
|---|---|
| `shape_search --include-constructed --name CReal.addGroupS --expect 1` (step 0 control, landed 2026-09-03) | FOUND 1, `declarations=3550`, exit 0 |
| `shape_search --include-constructed --name-like antideriv` (after) | FOUND 6, `declarations=3552`, `theorem=2558` (was 2556) |
| `kernel_declaration_projection` before/after diff | exactly 6 added rows: the two new theorems in each of `creal`, `complex`, `cpoint`, footprint `0` each; nothing removed, nothing else changed |
| `theorem_dependency_inventory <name>` re-list, both names | 1 each; a mistyped name prints 0 and exits 1 |
| `nat_axiom_inventory --include-constructed --require-axiom-free creal` | `ok: creal trusted surface = 0`, exit 0 |
| `cargo test --release -p axeyum-lean-kernel --lib -- creal:: --test-threads=4` | **230 passed, 0 failed**, 300 s (baseline 229) |
| `python3 scripts/validate-facts.py` | 2760 facts, 0 errors, exit 0; `proved` 2487 to 2489 |
| `python3 scripts/creal-declare-deps.py` | 0 steps disagreeing, 0 fields unprovided |

The before/after projection diff was produced honestly: the dispatch entry was
temporarily unwired, the crate rebuilt, the projection captured, and the
committed state restored -- not inferred from the count.

### Mutation table

Each mutant was run against the **full** `creal::` suite, because "exactly one
test dies" is not observable from a filtered run.

| mutant | change to the subject | result |
|---|---|---|
| pristine | -- | 230 passed, 0 failed |
| M1 | `hasDerivative_antiderivative_of_uc` regains the `(kb : Nat)` + `BoundedOn` binders | 229 passed, **1 failed**: `ftc_of_uc_applies_without_a_bounded_witness` |
| M2 | `integral_eq_antideriv_diff_of_uc` regains the same binders | 229 passed, **1 failed**: the same test |

Both mutants are exactly the regression the two theorems exist to prevent, and
each kills exactly one test and nothing else.

The test also carries two negative controls, each a SMALL term apart from the
real statement so `def_eq` fails immediately rather than descending into a
`Definition` unfold with no stopping rule:

| control | change | why it is false, not merely rejected |
|---|---|---|
| FTC-I | derivative is `CReal.neg` in place of `F` (a `Const` against an `FVar`) | at `F := id` on `[0, 1]` it reads `(int_0^x t dt)' = -x`, i.e. `x = -x` |
| FTC-II | evaluation term is `G a - G b` in place of `G b - G a` (`b` against `a`, two `FVar`s) | at `F := id` on `[0, 1]` it asserts `1/2 ~ -1/2` |

Neither control's rejection is offered as proof of its falsity -- a rejection
is a rejection. The falsity of each is argued separately, from the concrete
instance, in the test's own doc comment and in both facts.

## Cost

| item | cost |
|---|---|
| `shape_search` release build, cold | 1 m 57 s |
| each `shape_search` query (rebuilds the constructed index) | 36-45 s |
| `axeyum-lean-kernel --tests` release build | 4 m 20 s |
| the new test alone | 108 s |
| full `creal::` suite, `--release --test-threads=4` | 300 s (230 tests) |
| mutation sweep (2 mutants, build + full suite each) | ~18 min |

The two declarations themselves are cheap by construction: each is one
application of an existing theorem, so nothing in them forms a `Nat` numeral
or unfolds a `Definition`. The 108 s the test costs is dominated by the
`CReal` prelude build (~45 s) and the two `add_declaration` checks of the
FTC statements at symbolic arguments; both directions and both controls
share ONE prelude build for that reason.

## What did not land, and precisely why

- **The ledger-wide fix.** 1054 facts carry generated prose. Curating them is
  not this lane's scope, and a mechanical "characterisation_status" axis in
  `fact.schema.json` plus a validator report is a schema change that needs its
  own ADR and its own negative controls. Two facts are curated here as a
  demonstration of the shape, not as a dent in the number.
- **`CReal.integral_by_parts` was not given an `_of_uc` form.** It already
  takes its four `UniformlyContinuousOn` witnesses and discharges its bounds
  internally, so there is no redundant hypothesis to remove. Nothing is
  missing there.
- **The persona file and the roadmap were not corrected.** The brief
  forbids touching `docs/math-department/`. W1-2's status and
  `02-constructive-analysis.md`'s "What they would say is missing" list are
  both wrong on this point and need an owner. The specific corrections: the
  FTC is present in both directions, has been since 2026-08-27, and the
  reviewer's item 1 is closed; their items 2 through 5 (power series,
  uniform convergence, metric spaces, MVT) were not checked by this lane
  and should not be assumed present or absent on this ADR's authority.
- **No concrete evaluation test was added**, because no `Definition` was
  added -- both new declarations are `Theorem`s. `CReal.antiderivative`, the
  `Definition` underneath them, already has one
  (`ftc_estimates_concrete_and_negative_controls`, which instantiates it at
  `F := id` on `[0, 1]` and forces the unfold).

## Consequences

- A reader can now apply either direction of the FTC from the uniform
  continuity of the integrand alone.
- The two stronger-hypothesis originals stay. They are what the new theorems
  are proved from, and a caller who already has a bound should keep using
  them.
- Any lane briefing off `docs/math-department/` should verify a claimed
  absence against `shape_search --include-constructed` before treating it as
  one. This lane's brief named a false absence, and CLAUDE.md's own rule --
  "verify a blocker still exists before treating it as one, including a
  blocker this file names" -- applies to roadmap items as much as to
  blockers.

## Related

- [ADR-0512](adr-0512-real-is-constructed-as-a-setoid-over-the-rationals.md)
  -- why `CReal` is a setoid and the conclusion is `Equiv`, not `Eq`
- [ADR-1170](adr-1170-the-retrieval-gate-existed-and-ran-nowhere.md)
  -- the discipline the mutation table above answers to
- `docs/contributor-guide/finding-existing-lemmas.md` -- the failure mode
  this ADR is another instance of, at the level of a roadmap rather than a
  lemma
- `docs/contributor-guide/prelude-build-cost.md` -- the cost model the
  Cost section is measured against
