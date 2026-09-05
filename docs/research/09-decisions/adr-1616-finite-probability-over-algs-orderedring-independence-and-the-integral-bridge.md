# ADR-1616: the finite probability layer is stated once over `AlgS.OrderedRing`; independence is a definition; and the ℚ↔ℝ bridge is an embedding, not an instance

Status: accepted
Date: 2026-09-04
Lane: `finite-probability-generic`

Index-summary: Roadmap W1-10, W2-15 and the ℚ↔ℝ step ADR-1612 named.
`rat_prelude/probability_s.rs` (new, 29 declarations, footprint 0) states the
finite probability layer once over `(R : AlgS.OrderedRing)`: `sumRange` with
its two equations, congruence, additivity, scalar-pull, monotonicity and
nonnegativity; `IsDistribution`; `expectation` with linearity, the constant
law, nonnegativity and monotonicity; `markov_inequality`; `variance`,
`variance_nonneg`, `covariance`; and the transfer pair `sumRange_map` /
`expectation_map`. **The deciding number is 9 + 2 of 11 attempted, measured
by the kernel**: nine `Rat.*` theorems are instances outright
(`sumRange_congr_lt`, `sumRange_add`, `sumRange_le`, `sumRange_nonneg`,
`expectation_add`, `expectation_smul`, `expectation_const`,
`expectation_nonneg`, `expectation_le`); `Rat.markov_inequality` is an
instance after DROPPING two hypotheses its own proof never uses (`lt zero a`
and pointwise `le zero (X k)`) — the generic statement is strictly stronger,
because `AlgS.OrderedRing` carries no strict order; `Rat.variance_nonneg` is
an instance once `Rat.sq_nonneg` is supplied for the trichotomy consequence
seven order fields cannot yield. The five definitions are DEFINITIONALLY the
`ℚ` constants, not analogues. **Expectation's linearity is a CONSEQUENCE, not
an axiom** — ADR-1612's warning does not bite here, because the record's
fields were drawn from `linarith`'s needs and not from probability's. What
the record does not carry is measured instead: `mul_le_mul_of_nonneg_right`,
a PRIMITIVE on the `ℚ` side, costs three new generic ring lemmas
(`zero_mul`, `neg_mul`, `sub_nonneg_of_le`) plus two forgetful projections
`AlgS.OrderedRing.toRingS`/`toGroupS` that ADR-1592 never declared, and
`AlgS.add_add_add_comm` stays out of reach because it is stated over
`AlgS.CommRing`. W2-15: `Independent R A B p n := equiv E[A·B] (E[A]·E[B])`
with `uncorrelated_of_independent` deriving `covariance ≃ zero`, which is
exactly the hypothesis `Rat.variance_add_of_uncorrelated`,
`Rat.variance_sampleMean_uncorrelated` and `Rat.weak_law_of_large_numbers`
carry by hand; a test builds that composite and the kernel accepts it. It
needs no commutativity ONLY because `Rat.covariance` is already the
computational form `E[XY] − E[X]E[Y]` while `Rat.variance` is centred — an
asymmetry in the `ℚ` development that turns out to be load-bearing. The
bridge ADR-1612 named CANNOT be stated: `IntSpace` is generic over the
function space and hard-wired in the value type (`integral … → CReal`,
`total : CReal`), so there is no ℚ-valued `IntSpace`. Landed instead:
`IntSpace.crealFinite_expectation` (the ℝ-valued expectation IS the
`crealFinite` integral, definitionally, one application) and
`IntSpace.ratExpectation_integral` (the rational one is that integral across
`CReal.ofRat`, from `expectation_map` plus the already-proved `ofRat_add`/
`ofRat_mul`; `CReal.zero` IS `ofRat Rat.zero`, so the zero obligation is
`equivRefl`). Nothing new was needed on the reals.
Index-status: accepted

## Context

Roadmap W1-10 asked to generalize the finite probability layer over
`AlgS.OrderedRing` so expectation, variance, Markov and Chebyshev are stated
once and hold over ℚ and ℝ as instances. W2-15 asked for independence as a
definition with the theorem that independence implies uncorrelatedness.
[ADR-1612](adr-1612-the-integral-is-primitive-and-measure-is-derived-predicatively.md)
named a third step: show the rational finite-probability layer IS an
`IntSpace` instance, so the two halves of the analysis shelf are joined by a
theorem rather than an analogy.

Three facts shaped the answer, and all three were measured rather than
assumed.

1. **Every `ℚ` probability statement is division-free.** `Rat.expectation` is
   a weighted sum, not a normalized one; `Rat.markov_inequality` is stated as
   `a·E[ind] ≤ E[X]`; `Rat.chebyshev_inequality` is stated with the `a²`
   cleared. So the layer never needs a field, only an ordered ring — which is
   why `AlgS.OrderedRing` (29 fields, ADR-1592) is the right scope and why
   the generalization has no bridge in it at all.
2. **`AlgS.OrderedRing`'s field set came from `linarith`.** ADR-1584/1585
   chose `Alg.OrderedRing`'s seven order laws for a linear-arithmetic
   producer, and ADR-1592 mirrored them into the setoid spine. Probability
   needs a different multiplicative law.
3. **ADR-1612's own lesson** — "a record whose axioms come from what a
   development proves cannot re-derive what it took" — had to be checked
   here, not quoted. The question it poses for this lane is: **is
   expectation's linearity an axiom of the generic layer or a consequence?**

## Decision

### 1. The layer is stated once over `(R : AlgS.OrderedRing)`

`crates/axeyum-lean-kernel/src/rat_prelude/probability_s.rs`, 29
declarations, every one axiom-free (read from `Kernel::axiom_footprint`, by a
test whose name list is asserted to have the size it claims):

| group | declarations |
|---|---|
| projections | `toRingS`, `toGroupS` |
| ring lemmas the record lacks | `zero_mul`, `neg_mul`, `sub_nonneg_of_le`, `mul_le_mul_of_nonneg_right` |
| finite sums | `sumRange`, `sumRange_zero`, `sumRange_succ`, `sumRange_congr`, `sumRange_add`, `mul_sumRange`, `sumRange_le`, `sumRange_nonneg` |
| transfer | `sumRange_map`, `expectation_map` |
| probability | `IsDistribution`, `expectation`, `expectation_add`, `expectation_smul`, `expectation_const`, `expectation_nonneg`, `expectation_le`, `markov_inequality`, `variance`, `variance_nonneg`, `covariance` |
| independence (W2-15) | `Independent`, `uncorrelated_of_independent` |

**Expectation's linearity is a CONSEQUENCE, not an axiom.**
`expectation_add` is `sumRange_add` (induction, closed by a middle-four
exchange) plus `distribR` pointwise; `expectation_smul` is `mul_sumRange`
(induction, closed by `AlgS.mul_zero` and `distribL`) plus `mulAssoc`. Both
descend to the record's primitive fields. ADR-1612's warning is real but does
not bite here, and the reason is exactly the one that ADR names: the fields
were drawn from ANOTHER development's needs (`linarith`'s), so probability's
own theorems are not among them and are therefore derivable rather than
assumed. The place where it *does* bite is §2.

### 2. What the record does not carry, priced

- **`mul_le_mul_of_nonneg_right`** — `a ≤ b → 0 ≤ c → a·c ≤ b·c`, the
  workhorse under every expectation bound and a **primitive** on the `ℚ`
  side. `AlgS.OrderedRing`'s only multiplicative order law is `mul_nonneg`.
  Recovering it costs three new generic lemmas: `sub_nonneg_of_le` (from
  `add_le_add_right` + `negAdd` through `leCongr`), `neg_mul` (both sides are
  additive inverses of `a·b`, closed by `AlgS.add_left_cancel`), and
  `zero_mul` — which does **not** follow from the spine's `AlgS.mul_zero`,
  because ADR-1592 §2 built the record without `mulComm` and had to.
- **Two forgetful projections the spine never had.** `AlgS.mul_zero`,
  `AlgS.add_left_cancel` and `AlgS.sub` are stated over `AlgS.Ring` and
  `AlgS.Group`; ADR-1592 declared only `AlgS.CommRing.toRingS`. So
  `AlgS.OrderedRing.toRingS` (a prefix `mk_instance` over fields `0..=21`)
  and `AlgS.OrderedRing.toGroupS` (the additive group, `identL`/`invL`
  derived from `addComm`) had to be declared before any existing `AlgS`
  theorem was reachable from an ordered ring at all.
- **`AlgS.add_add_add_comm` stays out of reach.** It is stated over
  `AlgS.CommRing`, and there is no projection from a Ring-based
  `AlgS.OrderedRing` to a `CommRing`. The middle-four exchange is rebuilt
  inline from `addAssoc`/`addComm`/`addCongr`, which is all it ever needed.
- **Squares.** `variance_nonneg` takes `∀ a, le zero (a·a)` as an explicit
  hypothesis. A square is nonnegative only in a LINEARLY ordered ring and the
  record has no trichotomy — ADR-1601's discipline (a classical principle as
  a hypothesis) applied to an order-completeness one. `Rat.sq_nonneg`
  discharges it at ℚ, and a test shows the composite type-checks.
- **Strict order.** There is no `lt` field, so `markov_inequality` is stated
  without `lt zero a`. Its proof never used it, so the generic statement is
  strictly STRONGER, and that is the direction that lets the `ℚ` statement be
  an instance of it rather than the reverse.

### 3. The deciding number: 9 + 2, measured by the kernel

`probability_s_tests.rs` derives its instance list from a table rather than a
literal, and for each row builds a proof term for the `ℚ` theorem's own
declared type out of the generic theorem alone, infers its type, and requires
definitional equality with the `ℚ` theorem's.

- **Nine instances outright**: `sumRange_congr_lt`, `sumRange_add`,
  `sumRange_le`, `sumRange_nonneg`, `expectation_add`, `expectation_smul`,
  `expectation_const`, `expectation_nonneg`, `expectation_le`.
- **Two after a stated adjustment**: `Rat.markov_inequality` after dropping
  two unused hypotheses; `Rat.variance_nonneg` once `Rat.sq_nonneg` is
  supplied.
- **Five definitions are definitionally the `ℚ` constants**: `sumRange`,
  `IsDistribution`, `expectation`, `variance`, `covariance` — checked as
  `def_eq` of the closed TERMS, not of their types, so a generic definition
  computing something else would fail even though it type-checks.
- **Two `ℚ` theorems are NOT instances and would need reproof**:
  `Rat.sumRange_congr` states the pointwise hypothesis unbounded (the bounded
  one is `Rat.sumRange_congr_lt`, which is the instance), and
  `Rat.mul_sumRange` is stated in the opposite direction from the generic
  `mul_sumRange`. Both are statement mismatches, not gaps.

**What this number does NOT say.** It is 11 attempted out of roughly 30
`Rat.*` probability theorems. The untried remainder — `variance_eq`,
`variance_smul`, `variance_add_eq`, the `covariance_*` bilinearity family,
`sumVars`, the indicator family, Chebyshev, the sample-mean bound, the weak
law — was not measured and is not claimed. Two obstructions are known for
parts of it: the indicator family needs a decidable order (`Rat.ble`), which
is not a record field; and anything relating the centred and computational
forms needs `mulComm` (§4).

### 4. W2-15: independence, and why it needs no commutativity

`AlgS.OrderedRing.Independent R A B p n := equiv (expectation R (fun k => A k
* B k) p n) (mul (expectation R A p n) (expectation R B p n))` — the product
rule. For two events (indicator-valued `A`, `B`) that IS `P(A ∩ B) =
P(A)·P(B)`, since the indicator of an intersection is the pointwise product
and a probability is the expectation of an indicator; for general arguments
it is the uncorrelatedness of two random variables written the same way.

`AlgS.OrderedRing.uncorrelated_of_independent` derives `covariance R A B p n
≃ zero` in three steps. That conclusion is exactly the hypothesis carried by
hand in `Rat.variance_add_of_uncorrelated`,
`Rat.variance_sampleMean_uncorrelated` and
`Rat.weak_law_of_large_numbers`; a test builds the composite term and the
kernel accepts it, so "the existing uncorrelated hypotheses are now
recognizable to a reader from the field" is checked and not asserted.

**The reason it is three steps and not two hundred is an asymmetry in the `ℚ`
development that nobody had named.** `Rat.variance` is CENTRED (`E[(X−μ)²]`)
and `Rat.covariance` is NOT (`E[XY] − E[X]E[Y]`). This file follows both
verbatim so each generic definition is definitionally its `ℚ` constant. Over
`AlgS.OrderedRing` the two forms are not interchangeable: relating them needs
`E[fun k => X k * c] ≃ E[X] * c`, which pulls a constant past the weight `p
k` and therefore needs `mulComm`, a field ADR-1592 §2 could not give the
record. Had `Rat.covariance` been centred, W2-15 would have required
commutativity as an explicit hypothesis and a full expansion.

### 5. The bridge: an embedding, because the instance cannot exist

ADR-1612's step as worded is **not a statable theorem**, and the reason is a
property of its own record:

> `IntSpace` is generic over the FUNCTION space and hard-wired in the VALUE
> type. `carrier` is a field, but `integral : (f : carrier) → Integrable f →
> CReal` returns a `CReal` and `total : CReal` is a `CReal`. There is no
> ℚ-valued `IntSpace` and there cannot be one without a second carrier field.
> `Rat.expectation` is ℚ-valued.

The transfer that discharges it is stated over the spine, not over either
carrier: `AlgS.OrderedRing.sumRange_map` and `expectation_map` say that an
additive (respectively ring) map between two ordered rings carries a finite
sum, and a finite expectation, to the corresponding one. Two theorems in
`intspace/probability_bridge.rs` then land the content:

- **`IntSpace.crealFinite_expectation`** — the ℝ-valued finite expectation IS
  the `crealFinite` integral. One application: the generic expectation at
  `CReal.orderedRingS` δ/ι-reduces to `CReal.sumRange (fun k => X k * p k)
  (succ m)`, which is what `IntSpace.crealFinite_integral` already says the
  integral is. A `Nat.rec` over a record's `add`/`zero` and a
  Petrakis–Zeuner integration space meet definitionally, with no reconciling
  lemma between them.
- **`IntSpace.ratExpectation_integral`** — the rational expectation is that
  integral across `CReal.ofRat`. Obligations: `CReal.equivRefl` (because
  `CReal.zero` IS `CReal.ofRat Rat.zero`) and the symmetric forms of
  `CReal.ofRat_add` and `CReal.ofRat_mul`, both already proved. **Nothing new
  was needed on the reals.**

So every theorem the generic integration layer proves — congruence,
nonnegativity, the constant law, the derived counting measure, monotone
convergence — reaches the rational expectation through one named embedding
rather than a resemblance.

## Consequences

- The next carrier to get the whole finite probability shelf pays for one
  `AlgS.OrderedRing` instance and nothing else. `CReal.orderedRingS` already
  exists, so ℝ has it now.
- **`AlgS.OrderedRing` should gain `mul_le_mul_of_nonneg_right` as a derived
  theorem in the spine, not in this file.** It is a general ordered-ring
  fact and it is here only because this was the lane that needed it first.
  Same for `zero_mul` and `neg_mul`. Whoever consolidates the spine should
  move them; the four names are `AlgS.OrderedRing.{zero_mul, neg_mul,
  sub_nonneg_of_le, mul_le_mul_of_nonneg_right}`.
- **A lane extending the instance count should expect statement mismatches,
  not proof difficulty.** Both non-instances found here were direction or
  hypothesis-strength mismatches with the `ℚ` statement, and both were found
  by the kernel in seconds. Add a row to the table and run it.
- **`IntSpace` will need a second carrier field if a non-`CReal`-valued
  integral is ever wanted** — a ℚ-valued or an interval-valued one. That is a
  record change, not a proof, and this ADR is the measurement that says so.
- One test was written and **withdrawn**, with its reason recorded in the
  file rather than deleted: comparing `Independent` at ℚ with the hand-built
  `Eq` does not terminate usably, because `Rat.expectation` (delta height 36)
  and the generic `expectation` (height 4) drive the unfolder the wrong way
  round. Anyone stating a `def_eq` between a `ℚ` constant and its generic
  twin under a symbolic bound should expect the same and route around it, as
  the composite test does.

## Mutation table

Six mutations in a private snapshot of `194f52c03`, each reverted before the
next, each rebuilt and re-run (`--release`, `--test-threads=4`, 14 tests in
`probability_s_tests`). "Died" counts tests that actually ran and failed;
"did not build" and "ran no tests" are separate outcomes and neither
occurred.

| # | mutation | outcome |
|---|---|---|
| M0 | none (baseline) | 14 passed, 0 died |
| M1 | `sumRange` sums `f j + prior` instead of `prior + f j` | **14 of 14 died** |
| M2 | `expectation` weights `p k * X k` instead of `X k * p k` | **14 of 14 died** |
| M3 | one row deleted from the instance table (test side) | **exactly 1 died**: `instance_count_is_pinned` |
| M4 | no-op: the same proof term rebound in `uncorrelated_of_independent` | 14 passed, 0 died |
| M5 | no-op: an unused binding added at a different site | 14 passed, 0 died |
| M6 | `variance` centred at `zero` instead of at the mean | **14 of 14 died** |

**What the table says, and what it does not.** Every source-side mutation
kills every test, and that is a property of the design rather than a
weakness of the suite: each definition is consumed DEFINITIONALLY by its own
theorem — `sumRange_add`'s proof depends on `sumRange`'s operand order,
`variance_nonneg`'s on `variance`'s summand — so a wrong definition is
refused by the trusted gate at prelude-build time and poisons every test
that builds the prelude. The narrow mutation is therefore the test-side one,
M3, which kills exactly one test. The suite's discriminating power is
carried instead by its five negative controls, which run under the
UNMUTATED prelude and each fail on a small term difference: the generic sum
to `n+1` is not `Rat.sumRange` to `n`; expectation with variable and weights
swapped is not `Rat.expectation`; a two-term sum is not a three-term one;
`expectation_add` is not an instance of `Rat.expectation_smul`; and a
dependent pair of events fails the independence definition by computation
while an event and the sure event satisfy it.

M4 and M5 are the controls on the harness itself: a no-op mutation must
leave 14 passing, and both do, so "14 died" in M1/M2/M6 is a finding about
the mutation and not about the run.
