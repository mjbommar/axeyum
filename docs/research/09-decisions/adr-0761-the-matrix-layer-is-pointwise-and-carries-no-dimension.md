# ADR-0761: The matrix layer is pointwise, and the dimension is an argument rather than a type

Status: accepted
Date: 2026-08-30
Index-summary: Matrices over the constructed rationals are functions `Nat -> Nat -> Rat` with dimensions as ordinary arguments; every identity is stated POINTWISE because `funext` is absent, and the identity matrix carries no dimension of its own so its unit laws take an explicit `Lt` hypothesis that a computation shows is load-bearing.
Index-status: accepted

## Context

[ADR-0603](adr-0603-classical-theorems-land-as-graded-statement-families.md)
makes a classical theorem land as a graded statement family.
[`docs/curriculum/graded-statement-families-number-theory-and-linear-algebra.md`](../../curriculum/graded-statement-families-number-theory-and-linear-algebra.md)
§3 extended that treatment to linear algebra and found the gap this ADR closes:

> Despite the encoding being available, **every determinant declaration in the
> kernel is fixed-size with entries passed as separate scalar arguments** —
> `Rat.det2`, `det2_mul`, `det3_cofactor_row1`.
> `F-determinant-multiplicative-over-constructed-rationals` states
> `det(AB) = det A · det B` by **writing out all eight entries**.

So the vector layer existed at arbitrary dimension (`Rat.dotN`, with
Cauchy–Schwarz at symbolic `n`, all axiom-free) and the matrix layer did not.
That note named the matrix product as the single change unlocking three
families at once — determinant multiplicativity at general `n`, `Ax = b`, and
rank / linear independence — and predicted that `Rat.sumRange_swap` would make
associativity assembly rather than new mathematics.

Three design questions had to be answered before any of it could be built, and
none of them is obvious from the mathematics.

## Decision

### 1. A matrix is `Nat -> Nat -> Rat` with the dimensions as ordinary arguments

`Rat.matMul A B k i j := sumRange (fun t => A i t * B t j) k`, one index up
from `Rat.dotN`. No container type is involved, and none is available — this
kernel has no `List`, no `Finset` and no `Prod`.

`Rat.matMul A B k` has type `Nat -> Nat -> Rat`, i.e. **it is itself a
matrix**, so `matMul (matMul A B k) C m` is well-typed with no coercion and
associativity states directly.

The consequence to be explicit about: **no dimension consistency is enforced by
the types.** A matrix is a total function on all of `Nat x Nat`, so
`matMul A B k i j` is defined for every `i` and `j` and simply sums over
`t < k`. Nothing is ill-formed; things are merely, sometimes, not what you
wanted. §3 is where that bites.

### 2. Every statement is POINTWISE, and that is forced

`funext` is **absent** from this kernel; the same-kind positive control,
`congrFun'`, is present. So two pointwise-equal functions are not
propositionally equal, and a matrix identity cannot be stated as an `Eq`
between two `Nat -> Nat -> Rat` values. Every theorem concludes at a scalar
entry:

    matMul_assoc : forall A B C k m i j,
      matMul (matMul A B k) C m i j = matMul A (matMul B C m) k i j

This is not a workaround invented here — `Rat.sumRange_congr` already takes
pointwise equality as its hypothesis for the same reason — but it is a
permanent bound on what this route can say, and it is pinned by a test
(`the_matrix_associativity_statement_is_pointwise`) that asserts the rendered
type verbatim, so a later edit cannot quietly restate the theorem in a form the
absent `funext` makes unprovable.

### 3. `Rat.matId` carries no dimension, and the unit laws carry a `Lt` hypothesis

`matId i j := if Nat.beq i j then one else zero`. The delta is defined at every
index pair, so there is nothing for a dimension argument to do — and the
alternative (a `matId n` that is zero outside `[0,n)`) would push the bound
into every expression mentioning the identity rather than into the two theorems
that actually need it.

The price is that the unit laws are conditional:

    matMul_id_left  : forall A n i j, Lt i n -> matMul matId A n i j = A i j
    matMul_id_right : forall A n i j, Lt j n -> matMul A matId n i j = A i j

and the bounds are on **different** indices, because the summation runs over
the shared inner index and which outer index must lie in range depends on which
side the identity sits.

**The hypothesis is load-bearing and this is MEASURED, not argued.** With
`A i j = (i+i+j+1)/1` (so `A = [[1,2],[3,4]]` on the `2 x 2` block, and defined
everywhere) and `n = 2`, at the out-of-range row `i = 2`:

    matId 2 0 * A 0 0 + matId 2 1 * A 1 0  =  0*1 + 0*3  =  0
    A 2 0                                                =  5

`rat_mat_mul_id_left_needs_its_bound` pins both values and asserts they differ,
so the unbounded form of `matMul_id_left` is visibly false rather than merely
unproved. That is evidence a footprint check cannot carry and a statement pin
can only half carry: an axiom-free theorem with a superfluous hypothesis has
exactly the same footprint as one whose hypothesis is necessary.

## Consequences

### What landed

Thirteen declarations in
`crates/axeyum-lean-kernel/src/rat_prelude/matrix_n.rs`, all axiom-free:

| | |
|---|---|
| `matMul` | definition |
| `matMul_zero`, `matMul_succ` | the recursion equations, `Eq.refl` |
| `matMul_assoc` | pointwise associativity at symbolic `k` and `m` |
| `matMul_add_left`, `matMul_add_right`, `matMul_smul_left` | bilinearity |
| `sumRange_delta` | a sum vanishing away from one index collapses to it |
| `matId` | definition |
| `matId_diag`, `matId_off_diag` | the delta's two branches |
| `matMul_id_left`, `matMul_id_right` | the unit laws |

Facts: `F:rat-matmul-assoc`, `F:rat-matmul-id-left`, `F:rat-matmul-id-right`.

### The sizing prediction held, and the dependency graph proves it

`theorem_dependency_inventory` reports `matMul_assoc`'s direct dependencies as
exactly

    Rat.mul_assoc, Rat.mul_comm, Rat.mul_sumRange, Rat.sumRange_congr,
    Rat.sumRange_swap

— five edges, **no induction on any dimension**. `sumRange_swap` (the Fubini
interchange) carries the content; the other four move the outer factors in and
out of the inner sum. The curriculum note's "assembly, not new mathematics" was
right.

`sumRange_delta` is the one genuinely new induction in this file, and it is on
the bound, not on a dimension.

### Cost

`rat_prelude_builds`: **10.07 s before, 9.70 s after** — no measurable change
from thirteen declarations. Full `rat_prelude::` sweep: 138 passed, 0 failed,
154 s. Nothing here goes near the large-magnitude `Nat` trap: every evaluation
fixture keeps its numerals under 20.

### What is NOT decided here

- **Determinant multiplicativity at general `n` is not proved.** It needs a
  recursive determinant by cofactor expansion over this encoding, for which
  `Rat.det3_cofactor_row1` is the existing base case. That construction needs
  a minor / row-deletion operation on `Nat -> Nat -> Rat`, which is an index
  shift and not a new type — see the handoff in
  [`docs/plan/status/381-rat-matrix-layer.md`](../../plan/status/381-rat-matrix-layer.md).
- **No inverse.** Nothing constructs `A^-1` or proves `A * A^-1 = matId`.
- **No monoid structure in any type-theoretic sense.** There is no carrier of
  `n x n` matrices, no `Eq` on it, and no closure statement — only a product,
  an associativity law and two unit laws, all pointwise.
- **Transpose is not declared.** `(AB)^T = B^T A^T` is expressible pointwise
  and was not needed by anything here.

### A defect this work found and fixed

`RatPrelude::sum_range_swap`'s doc comment read `forall f m n` with `m` the
outer bound. The declaration (`rat_prelude/sum.rs:977`) allocates `n_fv` before
`m_fv`, so the binder order is `f`, then the **inner** bound, then the outer.
Both arguments are `Nat`, so the transposition is invisible at the call site,
and the kernel's rejection names the two bounds rather than the lemma. It was
the one rejection the associativity spine took. Doc corrected.
