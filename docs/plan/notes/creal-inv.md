# Notes: creal-inv

Detail kept out of [`../status/65-creal-inv.md`](../status/65-creal-inv.md) so
the lane block stays inside the per-lane ceiling (ADR-0478). The decision is
[ADR-0487](../../research/09-decisions/adr-0487-the-real-inverse-is-well-defined-by-uniqueness-not-by-estimate.md);
its predecessor, which fixed the *shape* without building it, is
[ADR-0481](../../research/09-decisions/adr-0481-the-real-inverse-is-partial-and-its-modulus-is-data.md)
and [`creal-field.md`](creal-field.md).

## The costing was wrong in the cheap direction, and here is why

The previous lane costed this at **~1,200–1,500 lines of proof script**, "of
which the genuinely new part is the ℕ side: two degree-2 polynomial identities
in `k` and `n`". The module is **1,137 lines including 100 lines of module
documentation**, and neither ℕ identity turned out to be an induction.

The reason is a change of parametrisation the plan did not anticipate. Write
`u := 2k+2` — the reciprocal of the half-bound `L = 1/(2k+2)`, and the number
every sample's reciprocal is bounded by. Then

- `A + 1 = 4k+4` **is** `2u`, definitionally, because `Nat.mul` recurses on its
  second argument and everything is phrased over `Nat.mul 2 k`;
- `(C+1) = (A+1)·(k+2)`, and the identity `C + 1 = u² + (A+1)` that the
  shrinking bound needs is `2u·(k+2) = u·u + 2u`, i.e. `u·(u+2)` with
  `u + 2 = 2·(k+2)` — again definitional. So it is **`mul_comm`, `left_distrib`,
  `mul_assoc`**, four steps, no `Nat.rec`;
- the other identity, `(A+1)·e + A = (e+1)·A + e`, is a general fact and became
  `Rat.nat_index_symm`: **Bishop's sampling index is symmetric in its shift and
  its argument.** `succ_mul` twice, `add_right_comm`, `mul_comm`. Fifteen lines.

That second one is the whole reason the design works, and it is worth naming.
`Rat.natDivSucc_le_scaled` reads a bound at `(c+1)·n + c` back to **`n`** — the
second slot, because that is the slot that shrinks. The real inverse needs the
*other* reading: its samples must be bounded **below** by a constant fixed by
the modulus, uniformly in `n`. Swapping the two arguments turns the same index
into one whose shrinking argument is `A = 4k+3`, where `natDivSucc_halve` says
`2/(A+1)` is exactly `L`. **`Rat.natDivSucc` still never has to be antitone in
its index** — the fifth dodge, and the cheapest one so far.

## The congruence obligation is bigger than it looks, and cheaper than it looks

`CReal` already carries five congruences (`neg_congr`, `add_congr`, `mul_congr`,
`le_congr`, `lt_congr`), each saying that replacing an argument by an
`Equiv`-equal one does not change the result. `inv` has a **second argument that
is not a real number and is related to nothing by `Equiv`**. Two callers holding
different separating moduli for the same `x` build genuinely different
sequences: `k = 0` samples at `7n+7`, `k = 1` at `32n+31`. Nothing in `inv`'s
type says the results agree, and if they did not, `x⁻¹` would be a function on
(real, modulus) pairs and every downstream field law would carry a modulus it
has no business carrying.

The direct route is an estimate through `y_{j₁(n)}` needing the regularity of
`y`, the hypothesis, and the reciprocal bound at two moduli — about the size of
`CReal.inv`'s own regularity proof, again. It is not needed. An inverse in a
commutative monoid is unique:

```text
u ≈ u·1 ≈ u·(y·v) ≈ (u·y)·v ≈ (u·x)·v ≈ (x·u)·v ≈ 1·v ≈ v·1 ≈ v
```

`mul_congr`, `mul_assoc`, `mul_comm`, `mul_one`, `Equiv.trans`, and
`mul_inv_cancel` at both ends. Sixty lines, and `inv_index_irrelevant` is that
at `y := x` with `Equiv.refl`. **The expensive-looking half of
well-definedness is the free half.**

## Vacuity was the real risk, not weakness

Every statement about `CReal.inv` is guarded by `PosBound x k`. If that
predicate had no inhabitants, `mul_inv_cancel`, `inv_congr` and
`inv_index_irrelevant` would all hold — footprint-free, statements verbatim —
of an operation that never runs. A verbatim-statement test does not see this,
and neither does an axiom-footprint check.

So two things are admitted **through the kernel** rather than asserted:

- `CReal.PosBound CReal.one 0` — the modulus `1/(0+1)` is `Rat.one` and
  `CReal.one` is `ofRat Rat.one`, so `CReal.le_refl` closes it outright;
- `∀ (h : PosBound one 0), ¬ Equiv (CReal.inv one 0 h) CReal.zero`, from
  `mul_inv_cancel` and `Equiv.not_zero_one` alone: if `1⁻¹ ≈ 0` then
  `1·1⁻¹ ≈ 1·0 ≈ 0` and also `≈ 1`, and `zero ≈ one` is refuted **by
  computation** at index 3.

Together: the domain is non-empty, and the inverse is not the constant zero —
which is the degenerate operation every other statement here would tolerate.

## Guards, measured rather than asserted

Measured in a `scripts/lane-snapshot.sh` tree at `57af69142`, filter
`--lib creal::creal_tests`.

Baseline: **24 passed, 0 failed.**

- Deleting `declare_inv_index_irrelevant` — **exactly 2 tests die**, 22 pass:
  `every_creal_declaration_is_checked_and_axiom_free` and
  `the_inverse_is_partial_and_its_modulus_is_an_explicit_nat`. This is the
  guard that **isolates**.
- Perturbing the sampling index (`shift_body`'s `(k+1)` factor to `k`, which
  breaks `C + 1 = u² + (4k+4)`) — **all 24 die**, 0 pass, because the kernel
  refuses `CReal.inv` and the whole prelude build fails. That removes a
  *mechanism* rather than a guard, and it is the measurement that says the
  index arithmetic is load-bearing rather than decorative: one factor in one
  ℕ expression, and nothing type-checks.
- **A wrong index does not fail fast.** The refusing run took **1,043 s** where
  the accepting one takes 78 s warm: the kernel grinds through δ-unfoldings
  before giving up. Worth knowing before someone bisects an index change and
  reads the wall time as a hang.
- **A refusal control cannot distinguish "refused because false" from "refused
  because the constant does not exist".** `the_inverse_route_cannot_prove_the_one_token_mutations`
  asserts `is_err()`, so deleting the declaration it consumes leaves it green.
  That is inherent to negative controls and is why the declaration-inventory and
  verbatim-statement tests are the ones that must die.

## What is deliberately not here

- **No inverse for `x < 0`.** `Rat.mul_inv_cancel`'s hypothesis is `0 < q` and
  the negative branch of `Rat.inv` is unproved. The general `x # 0` case cannot
  be reduced to the positive one by *branching* on the disjunction, so it needs
  `inv (neg x)` under a separate hypothesis, or a caller who picks the sign.
- **No `CReal.div`.** One line once the sign question above is settled, and
  premature before it.
- **No cotransitivity of `lt`, no `apart_mul`, no `abs`/`max`/`min`, no `sqrt`,
  no completeness** — the costings in [`creal-field.md`](creal-field.md) stand
  unchanged.
- **No Markov's principle in any disguise.** `¬(x ≈ 0) → x # 0` is not proved,
  not assumed, not used.

## Numbers

- `-p axeyum-lean-kernel --lib`, filter `creal`: **35 passed, 0 failed**
  (2,194 s wall under three concurrent lanes; the work is ~60 s of kernel).
- `CReal` declarations: **71 → 76**. `Rat` gains 2.
- `nat_axiom_inventory --include-constructed`: `creal` and `rat` both
  `axiom=0 opaque=0 quotient=0 total_trusted=0`, **unchanged**.
- `gen-lean-axiom-ledger.py --check`: `total=30 … creal=0 rat=0 real=30`,
  unchanged — no field law is one of the 22, so no count moves.
- A fresh `build_creal_prelude` goes **44 s → 61 s** (debug). The δ-unfolding
  blowup the brief warned about (12 GB for one lane) **did not occur**; peak
  stayed well under the 24 G ceiling. All five declarations were accepted on
  first submission.
