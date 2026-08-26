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
