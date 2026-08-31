# ADR-1040: both-sided 2×2 invertibility bridges the fixed-size and symbolic-dimension matrix families

Status: accepted
Date: 2026-08-31
Index-summary: `Rat.matInv2` (a genuine `Definition` over `matrix_n.rs`'s general `Nat → Nat → Rat` encoding, not four separate scalars) and both `A · A⁻¹ = I` / `A⁻¹ · A = I`, stated at every `(i,j)` entry through the SAME `matMul`/`matId` names the symbolic-dimension family uses, land as a graded family with no row 2 (ADR-0716) and row 3 collapsed into row 1 per ADR-0825 (`Rat.matMul_matInv2_top_left` itself, applied at a concrete numeral instance and bridged to a plain numeral by kernel computation). This connects two previously disconnected islands — `matrix.rs`'s fixed-size `det2`/`inv2`/`mul_adj2` family and `matrix_n.rs`'s symbolic-dimension `matMul`/`matId` family — rather than adding a third isolated fact family, and supplies the missing `A · A⁻¹ = I` direction that neither family had.

## Context

[ADR-0603](adr-0603-classical-theorems-land-as-graded-statement-families.md)
splits a classical theorem into up to four rows. [ADR-0716](adr-0716-row-two-of-a-decidable-subject.md)
measures that for ℕ/ℤ/ℚ the analysis-style row 2 mechanism is provably empty
and that a statement with no comparison and no unbounded search never reaches
a boundary in the first place — linear algebra over ℚ is decidable throughout,
so the dominance argument moves onto rows 1 and 3.
[ADR-0825](adr-0825-a-decidable-family-can-run-row-1-and-row-3-as-one-statement.md)
demonstrated that when row 1's declaration is directly executable, row 3 does
not need a separate `axeyum-cas` producer/verifier pair.
[ADR-0930](adr-0930-matrix-transpose-lands-as-a-two-row-family.md) applied
this method to `Rat.matTranspose_mul` and, in its own Context section, listed
the state of the rest of `matrix.rs`/`matrix_n.rs` at the time: fixed-size
`det2`/`det3`/`inv2_*`/`cramer2_*` (landed before the symbolic-dimension layer
existed) and the symbolic-dimension `matMul`/`matId`/`matMul_assoc` family
(landed separately, sharing no declaration with the fixed-size one).

**Step 0 for this lane (mandatory before building, per this repository's
retrieval discipline — `docs/research/11-design-review/2026-08-27-retrieval-is-the-bottleneck.md`)
found that the curriculum note's three named candidates for a "next rung"
(determinant multiplicativity, invertibility, `Ax = b` solvability, all at
fixed small `n`) are ALREADY LANDED at `n = 2`:**

- `Rat.det2_mul` — determinant multiplicativity (`matrix.rs`).
- `Rat.cramer2_x`/`Rat.cramer2_y`/`Rat.cramer2_solves` (existence, the
  substitution direction) and `Rat.cramer_two_unique_x`/`Rat.cramer_two_unique_y`
  (uniqueness, the forward direction) — `Ax = b` solvability, both directions.
- `Rat.inv2_top_left`/`Rat.inv2_top_right`/`Rat.inv2_bottom_left`/
  `Rat.inv2_bottom_right` — invertibility, but only ONE direction (`A⁻¹·A = I`),
  and stated in four separate `Rat` scalars, never `matrix_n.rs`'s
  `Nat → Nat → Rat` matrix.

So building any of the three candidates as originally framed would have
re-derived work that already exists — exactly the "rebuilding what exists"
failure this repository's retrieval notes warn is the single most expensive
recurring error in this area. What is genuinely missing, verified by reading
`matrix.rs` and `matrix_n.rs` in full: the fixed-size inverse family never
uses the general `matMul`/`matId` encoding at all, and only proves ONE of the
two invertibility directions — `A · A⁻¹ = I` is not proved anywhere, only its
unscaled cousin `A · adj(A) = det(A) · I` (`mul_adj2_*`, which needs no `det
≠ 0` hypothesis at all since it never divides).

## Decision

Land `Rat.matInv2` and both directions of `A · A⁻¹ = I` in a new module,
`rat_prelude/matrix_invertible.rs`, bridging the two families rather than
building a third isolated one:

1. **`Rat.matInv2 : (Nat → Nat → Rat) → Nat → Nat → Rat`** — a `Definition`
   taking a GENERAL matrix `A` (not four scalars), returning the
   adjugate-based inverse entry scaled by `invD := Rat.inv (det2 (A 0 0) (A
   0 1) (A 1 0) (A 1 1))` at each of the four `(i,j)` positions, built the
   same `Nat.beq`-selected way `matrix_transpose.rs`'s `const2x2` and
   `Rat.matId` build their own branches.
2. **Eight entry theorems**, each `∀ A, Not (det2 (A 0 0) (A 0 1) (A 1 0) (A
   1 1) = 0) → matMul <lhs> <rhs> 2 i j = matId i j` at one concrete `(i,j) ∈
   {0,1}²`:
   - `Rat.matInv2_matMul_top_left`/`_top_right`/`_bottom_left`/`_bottom_right`
     (`A⁻¹ · A = I`) — term-for-term identical, once `matMul`/`matInv2`/
     `matId` are unfolded at the concrete index pair, to `matrix.rs`'s own
     `inv2_top_left`/`inv2_top_right`/`inv2_bottom_left`/`inv2_bottom_right`,
     so each proof is the `matMul` unfold bridge, `Rat.zero_add`, then that
     existing lemma directly — no new algebra.
   - `Rat.matMul_matInv2_top_left`/`_top_right`/`_bottom_left`/`_bottom_right`
     (`A · A⁻¹ = I`) — genuinely new: `matInv2 A i j` multiplies `A`'s row on
     the LEFT of the (already-scaled) adjugate entry rather than the right,
     so each of the two summands needs `invD` pulled out from the middle of
     a product (`x*(invD*y) = invD*(x*y)`, one `mul_assoc` + one `mul_comm`
     each) before `Rat.left_distrib` (reversed) combines them into EXACTLY
     `matrix.rs`'s unscaled `mul_adj2_top_left`/`_top_right`/`_bottom_left`/
     `_bottom_right` statement, which is then scaled by `invD` via
     `Rat.mul_inv_cancel_of_ne_zero` (diagonal entries) or `Rat.mul_zero`
     (off-diagonal entries, since `mul_adj2_top_right`/`mul_adj2_bottom_left`
     already equal `Rat.zero` unconditionally, needing no determinant at
     all).
3. **Row 2: none**, argued from shape (ADR-0603 Amendment 4's discipline,
   satisfied by citing ADR-0716 rather than re-deriving it): every statement
   here is a pure identity conditioned on a disequality, with no comparison
   and no unbounded search to reduce to a boundary.
4. **`Rat.matInv2_eval_example`** — the discriminating concrete evaluation
   test the new `Definition` needs (Hard Rules: a well-typed `Definition` is
   admitted whatever it computes). `A := [[2,3],[5,7]]` (four distinct
   entries, `det = -1`) so a `matInv2` that forgot to swap the diagonal or
   forgot a sign flip on an off-diagonal entry produces a different numeral
   than `-7`, and the trusted gate refuses the wrong declaration outright.
5. **`Rat.matInv2_example` — row 3, via the ADR-0825 collapse.**
   `Rat.matMul_matInv2_top_left` itself, applied at the concrete matrix `A :=
   [[2,1],[1,1]]` (`det = 1`) and the same `D ≠ 0` construction
   `matrix.rs`'s own `cramer2_solves_computes_an_explicit_two_by_two_system`
   test uses, with its conclusion (still in named-constant form) bridged to
   the plain numeral `Rat.one` by the kernel's own delta/beta/iota
   computation. No separate `axeyum-cas` producer/verifier pair, per
   ADR-0825's "check whether the row-1 declaration is directly executable
   before reaching for one."
6. **Row 4: not attempted**, consistent with every other fact in this
   family's neighborhood.

Facts: `F:rat-matmul-matinv2-top-left`, `F:rat-matinv2-matmul-top-left` (and
their off-diagonal/bottom siblings), `F:rat-matinv2-eval-example`.

## Consequences

- **The graded-family method transfers to a bridging statement, not just a
  new operation.** Every ingredient (`mul_assoc`/`mul_comm` reassociation,
  `left_distrib` reversed, the ADR-0825 collapse, the discriminating-
  evaluation-test discipline) was already established by `matrix_n.rs`'s or
  `matrix_transpose.rs`'s own lanes; this ADR's contribution is connecting
  the fixed-size and symbolic-dimension islands so a later lane building
  general-`n` invertibility has one encoding to generalize, not two to
  reconcile.
- **Quality over count, honestly bounded.** This ADR explicitly does NOT
  claim general-`n` invertibility, rank, or determinant multiplicativity at
  symbolic dimension — those remain open (curriculum note §3.3, LA-1/LA-3;
  §5's matrix-layer item still names general-`n` determinant as "real,
  multi-session work"). A Mathlib reader would correctly say this family
  covers ONE fixed dimension of invertibility, and the fixed-size story
  (rows 1 and 3, both directions) is complete at `n = 2` and nowhere else.
- All 11 new declarations are measured axiom-free from the kernel
  (`Kernel::axiom_footprint`, empty for every one, checked in
  `matrix_invertible_tests::the_matrix_invertibility_toolkit_is_axiom_free`),
  consistent with the rest of the `rat` prelude's zero trusted surface.
