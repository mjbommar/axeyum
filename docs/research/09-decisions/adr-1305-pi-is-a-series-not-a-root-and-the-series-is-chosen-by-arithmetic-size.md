# ADR-1305: π is a series, not a root — and which series is decided by unary-numeral arithmetic, not by convergence speed

Date: 2026-08-31
Status: Accepted
Lane: `creal-pi`

Index-summary: `CReal.pi` is constructed by `CReal.mk` on an explicit regular sequence from Euler's transform of Leibniz, `π/2 = Σ 2ᵏ(k!)²/(2k+1)!`, with `3 ≤ π ≤ 4` proved and an empty axiom footprint. It retracts the standing claim that π is downstream of the exact-root construction `creal/ivt.rs` refutes — that was a statement about ONE DEFINITION of π presented as a statement about π. It also records the selection rule the build cost actually turned on: among series that converge, pick the one whose PROOF forms the smallest `Nat`s, because every numeral in this prelude is unary.
Index-status: Accepted

## Context

`docs/curriculum/foundational-books/spivak.md`'s Ch 15–17 row said, of π, that
it "is downstream of a root of `cos` and therefore of the exact-root
construction `creal/ivt.rs` **refutes**." Two other places in the development
repeated the reading.

The refutation is real: `CReal.ivt_exact_root_decides_sign` shows that an exact
root of a continuous function on a bracket would decide the sign of an
arbitrary constructive real. What does not follow is anything about π. That
sentence is a claim about **one definition** of π — twice the first positive
root of `cos` — stated as a claim about the number. π is the sum of a rational
series, and a series needs no root, no intermediate value theorem, and no
decision on a sign.

This is the same shape as ADR-0840's correction of the `fastFib` sizing and the
`multichoose` mirror-flip criterion: a lane reports accurately on the route it
took, and the report is then read as a fact about the target.

## Decision

**Construct `CReal.pi` from a series, by `CReal.mk` on an explicit regular
sequence, exactly as `CReal.e` and `CReal.cosOne` are constructed.** The series
is **Euler's transform of Leibniz**:

```text
π/2  =  Σ_{k≥0}  2ᵏ (k!)² / (2k+1)!  =  1 + 1/3 + 2/15 + 2/35 + …
```

defined by its **recursion**, not its closed form:

```text
CReal.piHalfCoef : Nat → Rat        t 0 = 1,   t (k+1) = t k · (k+1)/(2k+3)
```

Fourteen declarations in `crates/axeyum-lean-kernel/src/creal/pi.rs`, all
admitted through `Kernel::add_declaration` with an empty axiom footprint:
`piHalfCoef`, `piHalfTerm`, `piHalfSeriesPartial`, `piHalfCoefNonneg`,
`piHalfTermNonneg`, `piHalfTermLePowHalf`, `piHalfTermAbsLeDominant`,
`piHalf`, `piHalfConverges`, `pi`, `piHalfLeTwo`, `piLeFour`, `twoLePi`,
`threeLePi`.

## Why this series and not Leibniz

Leibniz (`π/4 = Σ (−1)ᵏ/(2k+1)`) is the series the retracted sentence would
send you to, and it is the wrong one here for a reason that is about this
development rather than about mathematics: **its terms are dominated by no
geometric series**, so the one cheap Cauchy witness the tree has — `CReal.e`'s
concrete `exp_dominant_cauchy_body_concrete`, which `creal/trig.rs` already
reproduces for `cosOne` — does not reach it. Everything else would have had to
be rebuilt.

Euler's transform gives three properties at once, and each removed work that a
first sizing had budgeted:

1. **The ratio is definitional.** Because the terms are defined by the
   recursion rather than by `2ᵏ(k!)²/(2k+1)!`, getting from `t k` to `t (k+1)`
   is ι-reduction. No factorial identity is ever built.
2. **`(k+1)/(2k+3) ≤ 1/2` is `2k+2 ≤ 2k+3`,** with no case split, so
   `t k ≤ (1/2)ᵏ` is a short induction and the domination hypothesis
   `sum_range_cauchy_dominated_ordered_normalized` wants is `CReal.e`'s own
   `expDominant`, **reused unchanged**.
3. **Every term is positive.** No `(−1)ᵏ` factor, so none of
   `creal/alternating.rs`'s pairing machinery and no sign bound.

## The selection rule the cost actually turned on

Convergence speed is the obvious criterion and it is not the binding one. Every
numeral this prelude builds is unary (`NatOps::num` is a `succ` tower and the
kernel's binary-literal fast path never fires), so the cost of a numeric bound
is superlinear in the largest `Nat` the PROOF forms — not in how few terms the
series needs.

Measured by A/B on one host, `creal_prelude_builds` in debug, statement
unchanged in all three rows:

| lower-bound route | largest `Nat` formed | `creal_prelude_builds` |
| --- | --- | --- |
| whole `pi` step disabled | — | 122.3 s |
| everything except `threeLePi` | ≤ 4 | 117.9 s |
| `threeLePi` on the exact `S 4 = 32/21` | 800 | killed past 600 s at 5.9 GB RSS |
| `threeLePi` weakened to `1, 1/3, 1/8, 1/24` | 864 | 359.1 s |
| `threeLePi` weakened to `1, 1/3, 1/9, 1/18` | 243 | **143.3 s** |

`Rat.normalize 800 525` is what the exact route pays: `Nat.gcd 800 525` by
repeated unary subtraction, then two `Nat.div`s of 32 and 21 iterations over
800- and 525-deep `Nat.succ` towers. `Rat.normalize 243 162` is
`gcd 243 162 = 81` in two remainder steps and divisions of 3 and 2 iterations.
An 11x swing in build cost from four rational constants.

So the rule, stated for the next lane that needs a numeric bound on a
constructed real: **weaken each term FIRST, to a bound whose running sums have
short divisions, and only then add.** Choosing the intermediate bound that
lands on what the next step needs — rather than the exact quotient — is the
same move that took another declaration from 587 s to 113 s.

Note the tightness this forces: `1/18 ≤ 2/35` is `35 ≤ 36`, one step from
false. That is not incidental. The weakened bounds have to be tight enough that
four terms still reach `3/2`, and loose enough that the denominators stay
small; there is not much room, and `creal::pi::tests::
the_weakened_term_bounds_are_one_step_from_false` pins both sides.

## What the trusted gate cannot tell you here

`CReal.piHalfCoef` is a `Definition`. `Kernel::add_declaration` type-checks it
and **cannot** report that it computes the wrong rational: a function returning
the wrong value still has type `Nat → Rat`. The mathematics of this whole file
lives in that one recursion.

Measured rather than asserted (`scripts/check-pi-series-numeric.py`): the decoy
series `t k = (1/2)ᵏ` satisfies **every theorem in `creal/pi.rs`** — ratio
`≤ 1/2` (with equality), `t k ≤ (1/2)ᵏ`, all terms nonnegative, every partial
sum `≤ 2`, and `S 4 = 15/8 ≥ 3/2` — and its sum is `2`, so its "π" would be
`4`, and `3 ≤ 4 ≤ 4` still holds. **The numeric bounds do not pin the series.**

The only guard that separates them is an evaluation test:
`creal::pi::tests::pi_half_coef_computes_its_first_four_values` reduces
`piHalfCoef` at `k = 0..3` and compares against independently built rationals,
with negative controls at `piHalfCoef 2 ≠ 1/15` (a numerator typo) and
`piHalfCoef 3 ≠ piHalfCoef 2` (a step returning its input).

One mutation aimed at exhibiting an *admitted-but-wrong* variant — ratio
`(k+1)/(2k+2)`, whose sum is 2 — was **rejected by the kernel** at build step
210, but the rewritten `ratio_le_half` it needed was itself wrong, so that
experiment establishes nothing about whether a correctly-proved variant would
be admitted. It is recorded as inconclusive.

## Consequences

- `docs/curriculum/foundational-books/spivak.md`'s Ch 15–17 row is corrected in
  place with a dated correction quoting the retracted sentence.
- Four facts are registered: `F:creal-pi`, `F:creal-pi-le-four`,
  `F:creal-two-le-pi`, `F:creal-three-le-pi`.
- The `creal` prelude build grows by **+21 s** (122.3 → 143.3 s), all of it
  `threeLePi`. Dropping that one theorem returns the build to baseline and
  leaves `twoLePi`, which is free.
- **Still genuinely out of reach**, and this is the part of the old sentence
  that survives: the *identification* of this π with a root of `cos`. That does
  need the construction `creal/ivt.rs` refutes. The number never did.
- Sharpening `π ≤ 3.2` needs the tail dominated from index 4 rather than from
  index 0 — a re-indexed domination, the same call
  `exponential.rs::declare_e_le_four` makes for `e ≤ 4` versus `e ≤ 3`.
