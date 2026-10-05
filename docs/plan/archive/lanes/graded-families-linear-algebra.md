# graded-families-linear-algebra — lane status

<!-- plan-section: lane-status -->

Status: DONE for this session. One complete graded family landed (rows 1
+ 3, row 2 argued absent via ADR-0716, row 3 via ADR-0825's collapse), two
declarations proved axiom-free, two facts registered and validated, ADR-0930
records the reasoning.

## Step 0 findings — what already exists (read this before assuming anything below is open)

- **The symbolic-dimension matrix layer already exists**, landed by a prior
  lane the same session, BEFORE this lane started:
  `crates/axeyum-lean-kernel/src/rat_prelude/matrix_n.rs` (`Rat.matMul` at
  symbolic dimension, `matMul_assoc`/`_add_left`/`_add_right`/`_smul_left`,
  `Rat.matId` and both unit laws) and `crates/axeyum-lean-kernel/src/rat_prelude/vector.rs`
  (`Rat.dotN`, general-dimension inner product, Cauchy-Schwarz). Facts
  `F:rat-matmul-assoc`, `F:rat-matmul-id-left`, `F:rat-matmul-id-right`
  already registered and `proved`. `matrix.rs` separately carries the
  FIXED-size (2x2, 3x3) determinant family (`det2`, `det3`,
  multiplicativity, Cramer's rule forward direction), landed earlier.
  **This saved real work**: the curriculum note's own "three targets a lane
  could start tomorrow" named the matrix layer as the highest-yield OPEN
  target; it was closed before this lane's first tool call.
- **`Rat.matTranspose` did not exist** -- confirmed via a freshly built
  `--release` `shape_search --include-constructed --name-like matTranspose`
  (2,507 declarations indexed): `verdict: ABSENT`, with `--name-like matMul`
  (`FOUND 9`) as the positive control confirming the search itself works.
  Transpose is the one basic matrix operation `matrix_n.rs` did not yet
  cover, and it needed no interchange-of-summation-order argument
  (`sumRange_swap`) the way `matMul_assoc` did, because transpose only
  swaps INDEX arguments, never which two values are summed.
- **General-`n` determinant, rank, and `Ax = b` solvability at symbolic
  dimension are genuinely open** (curriculum note LA-1/LA-2/LA-3) and were
  correctly sized by the brief as multi-session work (a recursive
  cofactor determinant, a minor-by-index-shift, and Cauchy's argument for
  multiplicativity). Not attempted here -- picking a smaller, honestly
  bounded target over a stalled attempt at a larger one.

## Family landed: matrix transpose over ℚ at symbolic dimension

New file: `crates/axeyum-lean-kernel/src/rat_prelude/matrix_transpose.rs`.
ADR-0930 records the design; `docs/research/09-decisions/adr-0930-matrix-transpose-lands-as-a-two-row-family.md`.

1. `Rat.matTranspose : (Nat -> Nat -> Rat) -> Nat -> Nat -> Rat := fun A i j
   => A j i` -- `Definition`, no bound argument, matching `Rat.matId`'s shape.
2. `Rat.matTranspose_transpose : forall A i j, matTranspose (matTranspose A)
   i j = A i j` -- the involution law, `Eq.refl`.
3. `Rat.matTranspose_mul : forall A B k i j, matTranspose (matMul A B k) i j
   = matMul (matTranspose B) (matTranspose A) k i j` -- **row 1**,
   `(AB)^T = B^T A^T` at symbolic dimension, stated pointwise (`funext` is
   absent). Proved from ONE `Rat.sum_range_congr` around ONE `Rat.mul_comm`
   applied pointwise to the summand -- no new induction, no `sumRange_swap`.
4. **Row 2: none.** Argued from shape per ADR-0603 Amendment 4's discipline
   (never inferred from a failed search): the statement has no comparison
   and no unbounded search to reduce to a boundary, so citing ADR-0716 §1
   (ℚ's order totality is already a proved theorem here) is sufficient --
   there is nothing to extract even in principle.
5. `Rat.matTranspose_eval_example` -- the discriminating concrete
   evaluation test the new `Definition` needs regardless of the family's
   grading (the kernel cannot tell a well-typed `Definition` is wrong).
   `A := [[2,3],[5,7]]` has DISTINCT off-diagonal entries, so a transpose
   that forgot to swap its index arguments would produce `3` where the
   theorem demands `5`, and the trusted gate would refuse the declaration.
6. `Rat.matTranspose_mul_example` -- **row 3, the ADR-0825 collapse.**
   `Rat.matTranspose_mul` ITSELF (the row-1 declaration), applied at
   `A := [[2,3],[5,7]]`, `B := [[11,13],[17,19]]`, dimension 2, indices
   `(0,1)`, with its conclusion bridged to the plain numeral `ofInt 174` by
   the kernel's own delta/beta/iota computation. `174` is independently
   computed by hand (`A(1,0)*B(0,0) + A(1,1)*B(1,0) = 5*11 + 7*17 = 174`)
   and discriminates the WRONG law `(AB)^T = A^T B^T`, which gives `121` at
   the same entry. **No separate `axeyum-cas` producer/verifier pair was
   built** -- exactly the check ADR-0825 asks for before reaching for one.
7. Row 4: not attempted, consistent with the neighbouring facts in this
   family (`F:rat-matmul-assoc`, `F:cramer-rule-forward-direction-...`).

**Axiom footprint, read from the kernel**
(`rat_prelude_tests::the_matrix_transpose_toolkit_is_axiom_free`, iterates
`kernel.axiom_footprint` per declaration): all five new declarations
`footprint=[]`.

**Rows 1 and 3 pinned verbatim, not merely footprint-checked**:
`the_matrix_transpose_mul_statement_is_pointwise` and
`the_matrix_transpose_involution_statement_is_pointwise` assert the exact
kernel-rendered type with `assert_eq!` (same discipline as
`the_matrix_associativity_statement_is_pointwise`), and
`the_matrix_transpose_examples_state_the_expected_numerals` asserts the
concrete examples' RHS is the exact unary succ-chain for 5/174, discriminating
against the un-swapped/wrong-order values (3/121) a bug would produce. Both
hand-derived pins were accepted by the kernel on the FIRST attempt.

**Environment-derived coverage.** All five new declarations added to
`unnamed_but_live_declarations` in `rat_prelude_tests.rs` --
`every_rat_declaration_is_checked_and_axiom_free` (reads
`kernel.environment().iter()` directly, not a hand list) caught all five as
unlisted on the first run of this lane's suite, exactly the failure mode
CLAUDE.md documents for `every_creal_declaration_is_checked_and_axiom_free`.

`cargo test -p axeyum-lean-kernel --lib rat_prelude::`: 141 passed, 0 failed
(full sweep, confirmed nonzero). Targeted `the_matrix_transpose*` sweep: 4
passed, 0 failed. `cargo clippy -p axeyum-lean-kernel --lib -- -D warnings`:
clean.

Facts: `F:rat-mattranspose-mul`, `F:rat-mattranspose-transpose`.
`depends_on` verified with `scripts/check-fact-depends-derived.py --fix`
(`nothing to fix`). `python3 scripts/validate-facts.py`: 0 errors, 2324
facts. `python3 scripts/check-settled-fact-statements.py --write`: wrote the
missing pins for these two facts into
`artifacts/ontology/settled-fact-statement-pins.json` (purely additive --
`git diff` confirms no existing fact's pin changed), then reran to confirm
`PASS`, `unpinned=0`.

## Holdout isolation

Before and after (identical -- this lane never touches
`artifacts/autogenesis/`):

    python3 scripts/check-autogenesis-holdout-isolation.py
    AUTOGENESIS_HOLDOUT_ISOLATION|held_out=136|files_scanned=1110|settled=0|references=0|verdict=PASS

## What a Mathlib reader would say is still missing

This family covers ONE operation (transpose) of the many a linear-algebra
library needs. General-dimension determinant, rank, linear independence,
and `Ax = b` solvability at symbolic dimension all remain open (curriculum
note LA-1/LA-2/LA-3; ADR-0930 names the specific missing pieces for
determinant: a minor-by-index-shift, a recursive cofactor determinant, and
Cauchy's multiplicativity argument). `matMul`/`matId`/`matTranspose`
together give the algebraic skeleton (associativity, identity, transpose
laws) that a Mathlib reader would recognise as "the basics of a matrix
ring", not yet "linear algebra" in the sense of solving systems or
computing invariants at general dimension.

## Next steps for a successor lane

1. **General-`n` determinant** (LA-1): needs a recursive cofactor
   definition over the `Nat -> Nat -> Rat` encoding (a minor is `fun i j =>
   if i < r then A i (adjust j) else A (i+1) (adjust j)`-shaped index
   arithmetic) and Cauchy's product-of-determinants argument generalising
   `det2_mul`'s linearity-plus-repeated-row proof. Sized as genuinely
   multi-session; do not attempt as a single slice.
2. **`Ax = b` solvability at symbolic dimension** (LA-2): the CAS/simplex
   route (`axeyum-solver::lra`/`simplex`) already has the best row-3 story
   in either subject (two independent Farkas re-checkers, kernel
   reconstruction) -- a kernel-side row 1 at symbolic dimension is the
   remaining gap, and would need the determinant work above for Cramer's
   rule to generalise, or a Gaussian-elimination route instead.
3. **Rank / linear independence** (LA-3): `Rat.det2_eq_zero_of_lin_dep` is
   the 2x2 case; a symbolic-dimension notion of rank needs a row-reduction
   or a maximal-nonsingular-submatrix definition, neither of which exists
   yet over this encoding.
