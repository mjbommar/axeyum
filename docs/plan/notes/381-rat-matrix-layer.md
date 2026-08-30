# Notes: 381-rat-matrix-layer

Detail moved out of [`../status/381-rat-matrix-layer.md`](../status/381-rat-matrix-layer.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- `docs/research/09-decisions/adr-0761-the-matrix-layer-is-pointwise-and-carries-no-dimension.md`
- Facts `F:rat-matmul-assoc`, `F:rat-matmul-id-left`, `F:rat-matmul-id-right`
- Six evaluation tests in `rat_prelude_tests.rs`
- A doc-comment correction to `RatPrelude::sum_range_swap` (see below)

## Measured

| | |
|---|---|
| `rat_prelude_builds`, before | 10.07 s |
| `rat_prelude_builds`, after (13 declarations) | 9.70 s |
| full `rat_prelude::` sweep | 138 passed, 0 failed, 154 s |
| `matMul_assoc` direct dependencies | 5 edges, **no induction on any dimension** |
| axiom footprint, all 13 | 0 (`rat: axiom=0 opaque=0 quotient=0`) |
| clippy `-D warnings`, this crate | clean |
| `validate-facts.py` | 2276 facts, exit 0 |

**The curriculum note's sizing held.** It predicted `Rat.sumRange_swap` would
make associativity assembly rather than new mathematics.
`theorem_dependency_inventory` reports `matMul_assoc`'s direct dependencies as
exactly `Rat.mul_assoc`, `Rat.mul_comm`, `Rat.mul_sumRange`,
`Rat.sumRange_congr`, `Rat.sumRange_swap`. Four rewrites around the Fubini
interchange, no new induction. `sumRange_delta` is the only genuinely new
induction in the file, and it is on the summation bound, not a dimension.

## Two rejections, both worth recording

1. **`sum_range_swap`'s binder order.** Its doc comment read `∀ f m n` with `m`
   the outer bound; the declaration (`rat_prelude/sum.rs:977`) allocates `n_fv`
   before `m_fv`, so the order is `f`, then the **inner** bound, then the outer.
   Both arguments are `Nat`, so the transposition is invisible at the call site
   and the kernel's message names the two bounds rather than the lemma. Doc
   corrected.
2. **`ne_of_lt` and `ne_of_lt_symm` are not interchangeable.** The right branch
   of the delta induction needs `¬(t = i)` from `Lt t i`; the left branch needs
   `¬(m = i)` from `Lt i m`. Using one for the other gives
   `expected Eq t i / got Eq i t` and names neither call site. Both helpers now
   exist with a doc comment saying they are not interchangeable.

## The evaluation tests, and why these fixtures

`Kernel::add_declaration` type-checks a `Definition` and admits it once it is
well-formed. A product that transposes an index has exactly the same type, so
nothing in the trusted gate can catch it.

    A i j = (i + i + j + 1) / 1      A = [[1,2],[3,4]]
    B i j = (i + j + j) / 1          B = [[0,2],[1,3]]
    A*B = [[2,8],[4,18]]

All four cells checked against the hand computation. The fixtures
**discriminate**: neither matrix is symmetric, they are not equal, the four
cells are pairwise distinct (asserted, so a wrong product cannot pass by landing
on a neighbour's value), and at cell (0,0) the three transposition bugs give
3 (`AᵀB`), 4 (`ABᵀ`) and 6 (`BA`) against the correct 2. `B*A` is the explicit
negative control, taken at **(0,0)** because `A*B` and `B*A` happen to agree at
(0,1) — both 8 — and a control placed there would have been vacuous.

A companion test repeats it with a `1/2` entry; cell (0,1) is load-bearing there
because `(1/2)*2` must reduce to `1`, which no integer-only reading of `Rat.mul`
produces. Every magnitude stays under 20: `Rat` numerals ride on unary `Nat` and
`Rat.normalize`'s gcd runs by unary recursion.

**The bound in the unit laws is measured, not asserted.**
`rat_mat_mul_id_left_needs_its_bound` evaluates at the out-of-range row `i = 2`:
`matId 2 0 * A 0 0 + matId 2 1 * A 1 0 = 0`, while `A 2 0 = 5`. Both pinned,
asserted to differ. That is evidence a footprint check cannot carry — an
axiom-free theorem with a superfluous hypothesis has the same footprint as one
whose hypothesis is necessary.

## What determinant multiplicativity at general `n` now needs

The product layer is the prerequisite and it is done. What remains, in order:

1. **A minor / row-and-column deletion on `Nat -> Nat -> Rat`.** This is an
   index shift, not a new type: `minor A p q := fun i j => A (skip p i)
   (skip q j)` with `skip p i := if i < p then i else i + 1`. `Nat.lt` is
   decidable here (`Nat.lt_or_ge` is a proved theorem) so the shift is
   definable, and its evaluation test is the same shape as `matId`'s.
2. **A recursive determinant by cofactor expansion.** `det A 0 := 1`,
   `det A (succ n) := sumRange (fun j => (-1)^j * A 0 j * det (minor A 0 j) n)`.
   The curriculum note calls this the natural constructive definition and
   `Rat.det3_cofactor_row1` is the existing base case to check it against —
   which is also the discriminating evaluation test, since `det3` was built
   independently.
3. **Multiplicativity itself.** The `n = 2` proof (`Rat.det2_mul`,
   `rat_prelude/matrix.rs`) deliberately avoids expanding into eight monomials:
   it proves `det2` is linear in each row, then gets the product formula from
   linearity plus a repeated-row-is-zero lemma plus row swap. That is the
   textbook Cauchy argument and it generalises; the general-`n` version needs
   row linearity and alternation for the recursive `det`, both of which are
   inductions over the cofactor expansion.

**A caution for whoever takes this.** Step 3 will want to say "`det` of a
matrix with two equal rows is zero", and *equal rows* is a pointwise statement
here, not an `Eq` between two `Nat -> Rat` values. Stating it as
`(∀ j, A p j = A q j) → det A n = 0` keeps it inside what this kernel can
express; stating it with a function equality does not, and `funext` will not
arrive to rescue it.

Two other things this layer does not have and did not need: a **transpose**
(`(AB)ᵀ = BᵀAᵀ` is expressible pointwise) and any **inverse**.

## Files

- `crates/axeyum-lean-kernel/src/rat_prelude/matrix_n.rs`
- `crates/axeyum-lean-kernel/src/rat_prelude.rs` (13 `NameId` fields, the
  module wiring, the `sum_range_swap` doc correction)
- `crates/axeyum-lean-kernel/src/rat_prelude/rat_prelude_tests.rs`
- `crates/axeyum-lean-kernel/src/rat_prelude/probability.rs` (`bool_select_rat`
  and its two branch lemmas promoted to `pub(super)` rather than copied)
- `artifacts/facts/F-rat-matmul-{assoc,id-left,id-right}.json`
- `docs/research/09-decisions/adr-0761-the-matrix-layer-is-pointwise-and-carries-no-dimension.md`
