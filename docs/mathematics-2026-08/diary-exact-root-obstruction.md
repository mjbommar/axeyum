# Why there is no exact IVT root yet, verified at the kernel

**2026-08-26.** Three results — exact `lt` reflection, Chapter 12's inverse
function theorem, and **tightness of apartness** (`¬ Apart x y → Equiv x y`) —
all wait on an *exact* preimage. `CReal.ivt_approx` supplies an *approximate*
one. A lane was sent to settle whether the gap closes.

**It does not, and the answer is overdetermined: two independent obstructions,
either of which alone is fatal.** The lane verified both from source rather than
citing precedent, which is what makes this worth recording.

## Obstruction 1: the sequence cannot be formed

`ivt_approx`'s conclusion is `∀ e, ∃ x, …`; `ivt_iter`'s is `∀ n, ∃ P Q, …`.
Building a limit needs `f : Nat → CReal` **as data**, and `converges_of_cauchy`
takes exactly that. You cannot project the witness out of an `Exists`.

The lane did not stop at "Lean works that way" — it read this kernel's own rule,
`inductive.rs`'s `allows_large_elimination`:

```rust
let allows_large_elimination = self.level_is_nonzero(group.result_level)
    || (group.families.len() == 1
        && match group.families[0].constructors.as_slice() {
            [] => true,
            [constructor] => constructor.exposes_non_prop_fields,
            _ => false,
```

For `Exists (motive : α → Prop) : Prop`, the constructor's field `w : α` is not
among the **result indices** (`Exists motive` has none), so
`exposes_non_prop_fields` is false and `Exists.rec` is `Prop`-only here.
`Or.rec` fails the same test on the two-constructor arm — so even
`lt_cotrans`'s branch choice cannot drive a data-level recursion.

This is the wall `pos_bound_of_lt` hit, and the reason `CReal.inv` takes an
explicit `Nat`. **It is structural, not a missing helper.**

## Obstruction 2: the slack never shrinks

Even granting data extraction, `{x_e}` is not Cauchy, and the reason is not
incidental. `ivt_approx` picks a **fresh** slack `eps(e) := 1/(2e+2)` and a
**fresh** bisection depth per accuracy `e`, and each step's branch is chosen by
`lt_cotrans` against the fixed pair `(−eps, eps)`. Different `e` therefore take
**different bisection trajectories** — not a shared nested refinement.

A single fixed-`eps` run of `ivt_iter` *does* give literally nested brackets with
geometrically shrinking width. But its slack is an **invariant maintained
throughout, not a decreasing quantity**, so its limit recovers `|F r| ≤ eps` for
that one `eps` and never an exact root.

That distinction — *width shrinks, slack does not* — is the crux, and it is
invisible from the theorem statement.

## What would remove it, and it is two new slices

1. **A data-valued bisection**, replacing the `Exists`-wrapped `ivt_iter`:

   ```text
   CReal.ivt_bisect : (F : CReal → CReal) → CReal → CReal → CReal → Nat → (CReal × CReal)
   ```

   buildable by ordinary `Nat.rec` into `Type` (`Nat`'s result level is nonzero,
   so it passes the rule above). The per-step branch must become **computable
   data**: `CReal.mk : (f : Nat → Rat) → Regular f → CReal` makes the
   representative sequence accessible, so the choice can be decided by comparing
   a sufficiently precise **rational** approximation of `F m` against the
   rational `eps` using ℚ's decidable order — with a companion `Prop`-valued
   spec theorem proving that data choice satisfies the same six-part invariant.

   **Note: this kernel has no `Prod` and no `Sigma`** (checked — nothing declared
   outside `inductive_tests.rs`), so the pair result needs a new minimal
   `Type`-valued two-field structure, or two mutually recursive
   `Nat → CReal` functions.

2. **A diagonal bisection with shrinking slack** `eps_n → 0` on top of (1),
   carrying a strengthened invariant relating width and slack **jointly**. Not a
   corollary of `ivt_iter`; comparable new work.

## The pattern this is the sixth instance of

In a setting where `Exists.rec` eliminates only into `Prop`, **a computed
projection is worth more than a proved existence.** That has now decided the
form of `CReal.inv` (explicit `Nat` modulus), `CReal.bound` (total projection,
not a search), `bucketIndex`, `mesh_le_of_ge` (reads its Archimedean witness off
`bound` rather than eliminating `archimedean`'s `∃`), the boundedness theorem's
return type, and now this.

**When a construction stalls here, the first question is whether the thing you
need is stated as an existence rather than computed.**

---

## `CReal.ivt_bisect` landed — and the design beat the sketch

The data-valued bisection is built. Three decisions, two of them better than what
this note proposed.

**1. The pair carrier: none.** The sketch offered a new `Type`-valued two-field
structure or two mutually recursive functions. The lane took neither:

```text
CReal.ivt_bisect : (CReal → CReal) → CReal → CReal → Nat → Nat → Bool → CReal
```

**one `Nat.rec` into `Bool → CReal`** — a plain Pi type, so **no new inductive at
all**. `ivt_bisect_lo`/`_hi` are one-line projections at `Bool.false`/`Bool.true`.
Two independent recursions were rejected for a concrete reason: each step's
midpoint needs *both* current endpoints, so they would have had to reconstruct
the identical pairing anyway.

That is worth generalising. **A function into `Bool → X` is a pair of `X`s that
costs no carrier**, and this kernel has no `Prod` or `Sigma`. Anywhere a
construction wants to return two things, this is available today.

**2. The branch: `Rat.ble`, a genuine `Bool`.** `ivt_step` decides with
`lt_cotrans`, which is `Prop` and unusable in a `Type`-valued recursion. Here the
branch is `Rat.ble s thresh` on a **rational sample** of `F m` — legitimate
precisely because ℚ's order is decidable where `CReal`'s is not — and `Bool.rec`
then selects a `CReal` freely. `sqrt.rs`'s `natSqrt` already makes the same move
one type down.

**3. A third decision this note did not anticipate.** `eps` cannot be an
arbitrary `CReal`: **a real carries no `Nat` for a construction to sample at.**
So it is an explicit `Nat` `n`, with `eps_n := ofRat (natDivSucc 1 n)`. That is
the same constraint already forced on `CReal.inv`'s modulus — and it is the
seventh instance of the pattern this note ends on.

Sampling index: `j := succ (2n)`, fixed at every step, threshold
`thresh := natDivSucc 1 j`. By `natDivSucc_halve`, `thresh + thresh ~ eps_n`
exactly, so `thresh` is `eps_n/2`.

## The test that was impossible before

`F := id` on the asymmetric bracket `[−1, 2]`, `n := 0` (so `eps = 1`,
`j = 1`, `thresh = 1/2`):

| k | midpoint | `F m` vs `1/2` | bracket | width |
|---|---|---|---|---|
| 0 | — | — | `(−1, 2)` | 3 |
| 1 | `1/2` | `≤` | `(1/2, 2)` | 3/2 |
| 2 | `5/4` | `>` | `(1/2, 5/4)` | 3/4 |

All confirmed by the kernel's own reduction, both branches of `Rat.ble` exercised.

**This is the first test in the IVT development that could catch a
transposed-branch defect** — swapping the two branches type-checks identically
and computes a different function. A `Prop`-valued bisection has no reduction to
check; a data-valued one does. That is a second reason to prefer computed
constructions here, independent of the elimination rule.

## Still open

The **invariant spec theorem**: that this computed bracket satisfies `ivt_step`'s
six-part invariant. It needs a "remembering" `Bool.rec` at every step, converting
the computed `Bool` back into a `Prop` fact via `ble_eq_true_of_le` /
`le_of_ble_eq_true` — comparable in size to `ivt_step` itself. And after that,
the diagonal version with shrinking slack.
