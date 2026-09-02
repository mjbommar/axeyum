# ADR-1561: draw 19 is authored, and draw 10's unenforced deferral was the whole refusal

Status: accepted
Date: 2026-09-02
Lane: `nursery-draw-19c`

Index-summary: Draw 19 is **authored**, after two refusals (ADR-1420 for draw
17's shape, ADR-1556 for this draw). Four families: `discrete-step-and-counting-bounds`
(held-out), `natural-bit-constructor` (development), `natural-binomial-bounds`
(train), `power-and-square-decompositions` (held-out) — 40 rows, taking the
extension manifest from 500 to 540 entries and `check-dispatchable-frontier.py`
from **2 to 22** against a floor of 10. ADR-1559's four Definitions are what
made two module-disjoint held-out families possible, but they were not
sufficient: the pool admits a module-disjoint pair **only if draw 10's
do-not-draw-held-out deferral of `Mathlib.NumberTheory.{SumTwoSquares,
PythagoreanTriples}` is overturned**. Measured, both ways and at every module
cap from four to six: with both modules available there are 40 disjoint pairs;
with **either one alone withheld** there are **zero**. The deferral was a
preference in a generator comment ("it is not worth a mild leak to buy slack"),
read by no guard, and ADR-1556 left it for the next lane to own. Its stated
reason does not survive measurement — `Int.sq_ne_two_mod_four` (`z * z % 4 ≠ 2`)
was called adjacent to the train family `integer-modular-equivalence`, whose
entire published subject vocabulary is the single constant `Int.ModEq`, which
that row does not mention, and neither drawn row uses **any** constant a
development or train family publishes. Second finding, and the reason this draw
is two cross-topic families rather than two textbook chapters: requiring a
held-out family's modules to share two leading path segments leaves **3 clean
bundles of 168 and no two of them module-disjoint**, so R11's vocabulary rule
makes a topically tight held-out family structurally impossible in this pool.
Third finding, from the blindness screen rather than from any R11 signal: the
stem sweep for `power-and-square-decompositions` names only `lcm` stems and
**structurally cannot reach** the prime-power machinery seven of its ten rows
are about — the ADR-1450 shape again. Screened by shape instead, the two real
adjacencies (`Nat.pow_two_or_has_odd_factor`, strictly weaker than the drawn
2-adic split; `Nat.prod_factorization`, which gives a factorization multiset but
states no drawn row) are disclosed in the review rather than dismissed.

Index-status: accepted

## Context

Draw 19 has been refused twice. [ADR-1420](adr-1420-the-refill-draw-is-not-authorable-one-two-row-module-blocks-it.md)
refused draw 17 on the same shape, and
[ADR-1556](adr-1556-draw-19-is-refused-one-viable-held-out-family-and-r5-needs-two.md)
refused draw 19 with a measurement: over 40,668 distinct drawn tens the pool
produced 3 viable held-out families and **0 module-disjoint pairs**, so R5's
demand for two new held-out families per draw was unsatisfiable.

[ADR-1559](adr-1559-primecounting-and-lcmupto-are-the-construction-that-unblocks-draw-19.md)
executed the unblock ADR-1556 named: four Definitions (`Nat.isPrime`,
`Nat.primeCounting'`, `Nat.primeCounting`, `Nat.lcmUpto`) with **no theorem
about any**, opening `Mathlib.NumberTheory.PrimeCounting` and
`Mathlib.NumberTheory.Chebyshev`. On `main` at this lane's start the ADR-1556
screen reports `viable=196 disjoint_pairs=219` and the set of modules
contributing a row to every viable ten is empty.

That is where this lane starts, and the question it had to answer is not "is
there a pair?" but "is there a pair we are allowed to take?".

## The decision

**Draw 19 is authored**, with these four families and these partitions, assigned
by the split key from the lexicographic order of each family's primary module
before any outcome was known:

| primary module | family | partition |
| --- | --- | --- |
| `Mathlib.Algebra.Order.Ring.Int` | `discrete-step-and-counting-bounds` | held-out |
| `Mathlib.Data.Nat.BinaryRec` | `natural-bit-constructor` | development |
| `Mathlib.Data.Nat.Choose.Bounds` | `natural-binomial-bounds` | train |
| `Mathlib.Data.Nat.Factorization.Basic` | `power-and-square-decompositions` | held-out |

**`discrete-step-and-counting-bounds`** (`Mathlib.Algebra.Order.Ring.Int` 3 +
`Mathlib.NumberTheory.PrimeCounting` 9 + `Mathlib.Tactic.IntervalCases` 2) asks
one question: what a discrete step buys you. Four rows are the integers'
discreteness (`¬ b ≤ a → a + 1 ≤ b`, `¬ b ≤ a → a ≤ b - 1`) and its parity
refinement (`Even (n - m) → (m + 2 ≤ n ↔ m < n)`, `Even m → (2 ≤ m ↔ 0 < m)`),
one is the Frobenius/Chicken-McNugget representability threshold, and five are
the prime-counting function's monotonicity, its subadditive step bound and where
it vanishes.

**`power-and-square-decompositions`** (`Mathlib.Data.Nat.Factorization.Basic` 5 +
`Mathlib.NumberTheory.Chebyshev` 3 + `Mathlib.NumberTheory.PythagoreanTriples` 1
+ `Mathlib.NumberTheory.SumTwoSquares` 1 = exactly 10, none dropped) asks what
can be pulled out of a number as a power or as a sum of two squares:
prime-power splitting (`n = p ^ e * n'`, `n = 2 ^ k * m` with `m` odd),
perfect-power recognition from coprime exponents, the divisibility test by prime
powers, `lcmUpto n ∣ n!`, `z² ≢ 2 (mod 4)`, and multiplicativity of sums of two
squares.

Both are R9-clean (no drawn name is declared here), R12-clean (no drawn row is a
closed evaluation), and R11-clean at **vocabulary 5 of 10 — the allowance — with
zero topic hits**, scored against every published development/train family
*including the two this draw adds*, which is the draw-18 lesson (ADR-1465)
applied rather than restated.

Neither ten carries a row that is `rfl` under our construction:
`Int.gcd_eq_natAbs` (ADR-1556) and `Nat.primeCounting_eq_primeCounting'_succ`
(ADR-1559) are both absent, and the screen's control confirms the check fires on
a ten built to contain the second.

## Finding 1: draw 10's deferral was not a preference, it was the refusal

Draw 10's comment in `gen-autogenesis-nursery-refill.py` says:

> `Mathlib.NumberTheory.{SumTwoSquares,PythagoreanTriples}` were available and
> are deliberately NOT taken: `Int.sq_ne_two_mod_four` is mod-4 arithmetic,
> adjacent to the TRAIN family `integer-modular-equivalence`, and it is not
> worth a mild leak to buy slack. Both held-out pools are therefore exactly 10
> with none dropped.

ADR-1556 found that this judgement is **read by no guard** — it is not a row in
`holdout-adjacency-review-v1.json`, so `barred_modules` cannot reach it — and
declined to convert it into one, on the ground that promoting one lane's
preference into an enforced invariant is a separate decision. It named the next
lane as the owner. This is that decision.

`docs/research/09-decisions/adr-1561-draw-19-screen.py`, running the real
`screen_family` / `barred_modules` / `is_closed_evaluation` over every module
subset of the unowned pool up to six modules:

| what is withheld | clean held-out bundles | module-disjoint pairs |
| --- | ---: | ---: |
| nothing | 168 | **40** |
| `PythagoreanTriples` | 58 | **0** |
| `SumTwoSquares` | 146 | **0** |
| both | 47 | **0** |

Withholding **either one alone** is enough to make R5 unsatisfiable. The
deferral is therefore not a preference that costs slack; it is the entire
refusal, and honouring it means refusing draw 19 a third time.

The stated reason does not survive measurement either.

* `Int.sq_ne_two_mod_four` is `∀ (z : ℤ), z * z % 4 ≠ 2`. The train family it
  was called adjacent to, `integer-modular-equivalence`, has **one** published
  subject constant — `Int.ModEq` — which this row does not mention; it is about
  `%`. None of that family's 20 rows (`add_modEq_left`, `ModEq.refl`,
  `ModEq.symm`, `ModEq.trans`, `mod_modEq`, …) is about a square.
* `Nat.sq_add_sq_mul` is the Brahmagupta–Fibonacci identity. Draw 10's sentence
  named its module and gave no reason for it at all.
* Both rows use **zero** constants any development or train family publishes.
  By the enforced measure — R11's vocabulary rule — they are among the *least*
  adjacent rows in the pool.

The judgement is now recorded where a guard can read it: the disclosure review
for `power-and-square-decompositions` in `holdout-adjacency-review-v1.json`
states it, and the screen asserts the measurement above so a future lane that
disagrees has to make the number move.

## Finding 2: R11 makes a topically coherent held-out family impossible here

The first draft of this draw tried to build two families the obvious way: one
`Mathlib.NumberTheory.*` bundle and one `Mathlib.Data.Nat.Factorization.*`
bundle. Both are refused, and the enumeration says every tight bundle is:

| bundle | why R11 refuses it |
| --- | --- |
| `Choose.{Bounds,Dvd,Sum}` | topic `Choose` (published by `natural-binomial` and `natural-factorial-choose-and-squarefree`), vocabulary **10/10** |
| `{BinaryRec, Bitwise}` | topic `Bitwise` (published by `natural-bitwise`, `natural-bitwise-basics`), vocabulary **9/10** |
| `Factorization.{Basic,Induction,PrimePow}` + `Multiplicity` | vocabulary **9/10** (`Nat.Prime`, `Nat.choose`, `Nat.Coprime`, `Nat.gcd`) |
| `NumberTheory.{Chebyshev,PowModTotient,PrimeCounting,PrimesCongruentOne}` | vocabulary **6/10** (`Nat.totient`, `Nat.Coprime`, `Nat.factorial`) |

Requiring a held-out family's modules to share two leading path segments leaves
**3 clean bundles of 168, and no two of them module-disjoint** — all three are
`Mathlib.NumberTheory.*` and all three draw `Chebyshev` + `PrimeCounting` +
`PythagoreanTriples`. So R5 cannot be met from topically tight families at all,
and a held-out family in this pool is cross-topic **by construction**. That is
not a departure: draw 10's own `descent-and-well-ordering` is
`Data.Int.LeastGreatest` + `NumberTheory.SumFourSquares` +
`Order.Interval.Finset.Nat`, held together by a mathematical theme rather than a
directory.

This also settles which families are dispatchable. `natural-bit-constructor` and
`natural-binomial-bounds` are refused *for held-out* on topic — R11 saying a
lane already works that mathematics — which is exactly what makes them the right
development and train families. And they add no new adjacency to the held-out
pair: `Nat.bit` already carries 19 kernel theorems and `Nat.choose` is already
published by `natural-binomial` (development), so drawing them changes nothing a
lane could already see.

`Mathlib.Data.Nat.Count` (22 rows, R11-clean, the largest single block in the
window) was **deliberately not taken** for either dispatchable slot. It is
barred from held-out by ADR-1450, and as a development or train family it would
sit directly beside `discrete-step-and-counting-bounds`, whose five
prime-counting rows are monotonicity and step bounds for a counting function —
`count_monotone`, `count_le`, `count_succ` are the same lemmas one carrier down.
R11 cannot see that (`Nat.count` and `Nat.primeCounting` are different
constants, `Count` and `PrimeCounting` different topic segments), which is
precisely why it had to be a judgement.

## Finding 3: the R11 stem sweep could not reach this family's real adjacency

The environment sweep for `power-and-square-decompositions` is
`[["lcm", "Nat.coprime_lcm_eq_mul", 21], ["lcmupto", "Nat.lcmUpto", 1],
["upto", "Nat.lcmUpto", 1]]`. Those stems come from the family's *subject*
constants, and they close only the three `lcmUpto` rows. The other seven rows
are about prime powers, and **no stem in that sweep reaches them** — the sweep
is clean because it is not looking, which is the ADR-1450 shape on a new family.

Screened by shape instead, over an index of 3,041 declarations with a live
positive control on every query (`Int.quadraticReciprocity`, landed the same
day, returns `FOUND 1`; `theorem=2458 ns Nat=1084`), two real adjacencies exist
and are disclosed in the review:

* `Nat.pow_two_or_has_odd_factor` (`n ≠ 0 → (∃ m, n = 2 ^ m) ∨ (∃ e t,
  n = e * (2t + 1) ∧ t ≠ 0)`) is the nearest single statement to the drawn
  `Nat.exists_eq_two_pow_mul_odd` (`n ≠ 0 → ∃ k m, Odd m ∧ n = 2 ^ k * m`). It is
  **strictly weaker**: its second disjunct produces *some* odd factor, not the
  2-adic split, and its first is the `m = 1` case.
* `Nat.prod_factorization` (`0 < n → prod (factorization n) = n`) and
  `Nat.factorization_prime` give the existence of a prime factorization as a
  computed multiset. Neither states any drawn row; every one of the ten is
  elementary and none mentions `Nat.factorization`. `Nat.divMaxPow`, which
  computes exactly the p-adic cofactor, carries no theorem at all
  (`--const Nat.divMaxPow --kind theorem --expect-absent` is ABSENT), and its
  family `natural-max-power-dividing` is itself held-out — blind beside blind,
  the draw-2 precedent.

Everything else screened absent by shape: `--const Int.emod` (18) and
`--const Int.emod --const Int.mul` (6) find only mod-2 and division facts, none
about a square; `--const Nat.pow --const Nat.dvd` (26), `--const Nat.pow
--const Exists` (4), `--const Nat.gcd --const Nat.pow` (1) and `--const
Nat.factorial --const Nat.dvd` (6) contain no perfect-power recognition and no
p-adic split; `--const Int.le --const Not` (3), `--const Int.lt --const Int.le`
(15), `--const Int.Even` (5), `--const Nat.gcd --const Exists` (3) and
`--const Nat.pred` (14) contain neither discreteness row, neither parity row and
no representability threshold. The ADR-1556 question — is a row `rfl` under
*our* definition? — was asked for the discreteness pair and answered by reading
the declaration: `Int.lt` is a four-case definition over `Nat.lt`
(`int_prelude/defs.rs:declare_order_definitions`), not `Int.le (a + 1) b`.

A pickaxe over the whole history (`git log -S <name> --diff-merges=first-parent
-- crates/`, because a plain pickaxe skips merge commits) finds **zero** commits
introducing any of the 19 drawn names, with a live positive control
(`Nat.lcmUpto` returns 2).

## Consequences

* The extension manifest goes 500 → 540 entries: development 180 → 190,
  held-out 190 → 210, train 130 → 140. Two new held-out families satisfies R5;
  20 dispatchable rows satisfies R4.
* `check-dispatchable-frontier.py` goes from **2 to 22** against a floor of 10,
  clearing the G7 gate that has been red since draw 18's rows were consumed.
* Zero churn over the 500 already-drawn rows — 0 missing, 0 changed, 0
  partitions moved — verified with a negative control that detects a single
  flipped partition.
* `Mathlib.NumberTheory.{SumTwoSquares,PythagoreanTriples}` are now spent as
  held-out. A future lane wanting them back has to move the numbers in the
  screen, not re-argue the comment.
* `Mathlib.Data.Nat.Count` is still unowned and still barred for held-out, and
  it is now also **unavailable for development or train while
  `discrete-step-and-counting-bounds` is blind**. That is a judgement, not a
  guard: R11 cannot see the `Nat.count` / `Nat.primeCounting` adjacency, and the
  next lane tempted by 22 easy rows should read Finding 2 before taking them.
* The pool after this draw is thin. Of the 25 unowned modules that carried a
  screened row, this draw takes 12; what remains is mostly single-row modules
  and the 22-row `Count` block that is now doubly constrained. Draw 20 will need
  another ADR-1420 Route 1 construction, and the ADR-1559 shape — Definitions
  with no theorem about them — is the one that works.

## Evidence

* `docs/research/09-decisions/adr-1561-draw-19-screen.py` — exit 0, `failures=0`,
  `ADR_1561_DRAW_19_SCREEN|env=3018|families=4|held_out=2|pairs_with_draw10_modules=40|pairs_without=0|coherent_bundles=3|coherent_pairs=0`.
  Four controls, each of which must come out the other way and does: the
  definitional-row check fires on a ten built to contain one; the disjointness
  search finds 1,388 pairs instead of 40 with ADR-1450's `Nat.Count` bar lifted;
  R11 refuses a family scored against a topic twin. Its first draft asserted
  ZERO topically tight bundles and was WRONG — measured at a four-module cap and
  with the two deferred modules already removed — which is recorded in the file.
* `scripts/gen-autogenesis-nursery-refill.py` — the draw itself, with the
  reasoning above in the `FAMILY_MODULES` comment block.
* `artifacts/autogenesis/holdout-adjacency-review-v1.json` — the two R11
  disclosure reviews, written before the draw.
* `docs/plan/status/423-nursery-draw-19c.md` — the before/after gate table.
