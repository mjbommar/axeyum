# ADR-0930: matrix transpose lands as a two-row graded family (rows 1+3), reusing ADR-0825's collapse

Status: accepted
Date: 2026-08-30
Index-summary: `Rat.matTranspose` and `Rat.matTranspose_mul` (`(AB)^T = B^T A^T` at symbolic dimension over the constructed rationals) land as a graded family with no row 2 (ADR-0716: ℚ's order is decidable and the statement has no comparison to reduce to a boundary) and row 3 collapsed into row 1 per ADR-0825 (`Rat.matTranspose_mul` itself, applied at a concrete numeral instance and bridged to a plain numeral by kernel computation, rather than a separate CAS producer/verifier pair).
Index-status: accepted

## Context

[ADR-0603](adr-0603-classical-theorems-land-as-graded-statement-families.md)
splits a classical theorem into up to four rows. [ADR-0716](adr-0716-row-two-of-a-decidable-subject.md)
measured that for ℕ/ℤ/ℚ the analysis-style row 2 mechanism is provably empty
(`Rat.le_total` is a proved, axiom-free theorem here) and that a statement
with no comparison and no unbounded search never reaches a boundary in the
first place — for a decidable subject the dominance argument has to move
onto rows 1 and 3. [ADR-0825](adr-0825-a-decidable-family-can-run-row-1-and-row-3-as-one-statement.md)
demonstrated, for number theory, that when row 1's declaration is directly
executable, row 3 does not need a separate `axeyum-cas` producer/verifier
pair: the SAME declaration, applied at concrete numerals with a kernel-level
computation bridging the gap to a plain answer, is row 3.

[`docs/curriculum/graded-statement-families-number-theory-and-linear-algebra.md`](../../curriculum/graded-statement-families-number-theory-and-linear-algebra.md)
(§3, "the matrix layer over `Nat → Nat → Rat`") named the matrix layer as the
highest-yield open target for linear algebra, and by the time this lane
started, a prior lane had already landed it:
`crates/axeyum-lean-kernel/src/rat_prelude/matrix_n.rs` carries `Rat.matMul`
at symbolic dimension with associativity, the two-sided identity law, and
distributivity over `+`/scalar multiplication, all 0 axioms
(`F:rat-matmul-assoc`, `F:rat-matmul-id-left`, `F:rat-matmul-id-right`).
`matrix.rs` separately carries the FIXED-size (2×2, 3×3) determinant family
(`det2`, `det3`, multiplicativity, Cramer's rule forward direction), landed
before the symbolic-dimension layer existed.

Verified in-tree before starting (`shape_search --include-constructed
--name-like matTranspose`, a freshly built `--release` binary, 2,507
declarations indexed): **`Rat.matTranspose` did not exist**, with
`--name-like matMul` (FOUND 9) as the positive control confirming the search
itself works. Transpose — `(AB)^T = B^T A^T`, `(A^T)^T = A` — is Boyd–
Vandenberghe ch. 1 / any linear-algebra textbook's second or third property
of a matrix, and was the one basic operation `matrix_n.rs` did not yet cover.

General-`n` determinant (the curriculum note's other named gap) needs a
minor-by-index-shift, a recursive cofactor determinant, and Cauchy's
argument for multiplicativity — real, multi-session work. Transpose does
not: it swaps two index arguments and nothing else, so `(AB)^T = B^T A^T`
needs only one `Rat.mul_comm` applied pointwise through the already-landed
`Rat.sumRange_congr` — no interchange of summation order (`sumRange_swap`),
unlike `matMul_assoc`, because transpose never reorders which two values are
being summed over, only which index picks which.

## Decision

Land `Rat.matTranspose` and its family in a new module,
`rat_prelude/matrix_transpose.rs`, sized to the actual difficulty rather than
to the curriculum note's larger placeholder:

1. **`Rat.matTranspose : (Nat → Nat → Rat) → Nat → Nat → Rat := fun A i j =>
   A j i`** — a `Definition`, no bound argument (matching `Rat.matId`'s
   shape: defined at every index pair, with a bound entering only where a
   consuming theorem needs one).
2. **`Rat.matTranspose_transpose : ∀ A i j, matTranspose (matTranspose A) i j
   = A i j`** — the involution law, `Eq.refl`.
3. **`Rat.matTranspose_mul : ∀ A B k i j, matTranspose (matMul A B k) i j =
   matMul (matTranspose B) (matTranspose A) k i j`** — row 1. Pointwise
   (`funext` is absent), proved from `Rat.sum_range_congr` and `Rat.mul_comm`
   alone, no new induction.
4. **Row 2: none**, argued from shape rather than asserted (ADR-0603
   Amendment 4's discipline, satisfied here by citing ADR-0716 §1 rather than
   re-deriving it): `matTranspose_mul` has no comparison and no search to
   reduce to a boundary, so there is no decision principle to extract even in
   principle.
5. **`Rat.matTranspose_eval_example`** — the discriminating concrete
   evaluation test `Rat.matTranspose`'s new `Definition` needs regardless of
   the family's grading (Hard Rules: the kernel accepts a well-typed
   `Definition` whatever it computes). A transpose that forgot to swap its
   index arguments would still type-check AND would still satisfy the
   involution law (composing a no-op with itself is still a no-op), so
   `matTranspose_transpose` is not a substitute for this. Uses a 2×2 matrix
   with distinct off-diagonal entries (`3` at `(0,1)`, `5` at `(1,0)`) so a
   forgotten swap produces the wrong numeral and the trusted gate refuses the
   declaration.
6. **`Rat.matTranspose_mul_example` — row 3, via the ADR-0825 collapse.**
   `Rat.matTranspose_mul` itself, applied at two concrete 2×2 matrices
   (`[[2,3],[5,7]]`, `[[11,13],[17,19]]`) and a concrete dimension/index
   triple, with its conclusion (still in named-constant form) bridged to the
   plain numeral `ofInt 174` by the kernel's own delta/beta/iota computation.
   `174` is independently computed by hand in the module doc
   (`A(1,0)·B(0,0) + A(1,1)·B(1,0) = 5·11 + 7·17 = 174`) and discriminates
   the wrong law `(AB)^T = A^T B^T` (which gives `121` at the same entry).
   No separate `axeyum-cas` producer/verifier pair is built, per ADR-0825's
   "check whether the row-1 declaration is directly executable before
   reaching for one."
7. **Row 4: not attempted**, consistent with every other fact in this
   family's neighborhood (`F:rat-matmul-assoc`, `F:cramer-rule-forward-
   direction-over-constructed-rationals`).

Facts: `F:rat-mattranspose-mul` (rows 1+3, the classical theorem, with a
second evidence row for `matTranspose_eval_example`'s discriminating check on
the new `Definition`), `F:rat-mattranspose-transpose` (the involution law).

## Consequences

- **The graded-family method transfers to a genuinely new operation with no
  new proof technique.** Every ingredient (`sum_range_congr`, `mul_comm`,
  the ADR-0825 collapse, the discriminating-evaluation-test discipline) was
  already established by the number-theory lane or the `matMul_assoc` lane;
  this ADR's contribution is applying the SAME method to a different
  classical statement, which is exactly the "scale the method, not just the
  target count" argument ADR-0825 makes for itself.
- **Quality over count, honestly bounded.** This ADR explicitly does NOT
  claim general-`n` determinant, rank, or `Ax = b` solvability at symbolic
  dimension — those remain open (curriculum note §3.3, LA-1/LA-2/LA-3), and a
  Mathlib reader would correctly say this family covers one operation
  (transpose) of the many a linear-algebra library needs, not the subject.
- Both new declarations are measured axiom-free from the kernel
  (`Kernel::axiom_footprint`, empty for both, checked in
  `rat_prelude_tests::the_matrix_transpose_toolkit_is_axiom_free`), consistent
  with the rest of the `rat` prelude's zero trusted surface.
