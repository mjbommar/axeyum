# linear-algebra-spine — status

Lane: `linear-algebra-spine`. Started 2026-08-31.

## Step 0 (mandatory inventory) — result

Before starting, confirmed via `shape_search --include-constructed --name-like mat`
and `--name-like det`, and by reading
`docs/curriculum/graded-statement-families-number-theory-and-linear-algebra.md`
§3 and ADR-0930, that the following already exist in
`crates/axeyum-lean-kernel/src/rat_prelude/{matrix.rs,matrix_n.rs,matrix_transpose.rs}`,
all axiom-free:

- `Rat.matMul` at symbolic dimension (`matrix_n.rs`): associativity, both
  unit laws, additivity/scalar-linearity in each argument.
- `Rat.matId`, `Rat.matTranspose`, `matTranspose_transpose`,
  `matTranspose_mul` (`(AB)^T = B^T A^T` at symbolic dimension, ADR-0930).
- `Rat.det2`/`Rat.det3` (`matrix.rs`) — **determinant multiplicativity is
  ALREADY LANDED at n=2** (`det2_mul`), plus `det2_eq_zero_of_lin_dep`,
  `mul_adj2_*` (A·adj(A) = det·I, all four entries), `inv2_*` (A⁻¹·A = I,
  all four entries, one direction), and `cramer2_x/y` + `cramer2_solves` +
  `cramer_two_unique_x/y` — **both existence and uniqueness of the n=2
  linear-system solution are already landed** (LA-2's row 1 at fixed n=2).
  `det3` has cofactor expansion, `det3_id`, `det3_scale_row`, `det3_ofInt`,
  three worked examples — no `det3_mul` yet.

So the task brief's three "candidates" (determinant multiplicativity,
invertibility, solvability, all at fixed small n) are **already landed at
n=2** except for one genuine gap: `inv2_*` only proves ONE direction
(A⁻¹·A = I via raw scalar entries); there is no statement connecting the
fixed-size (`det2`/`inv2`) family to the general `matMul`/`matId` pointwise
encoding `matrix_n.rs` builds, and the OTHER inverse order (A·A⁻¹ = I) is
not proven as a named entry-wise family at all (only implicit via
`mul_adj2_*`, unscaled).

## What I am building

`Rat.matInv2 : (Nat → Nat → Rat) → Nat → Nat → Rat` — the adjugate-based
2×2 inverse taking a general matrix `A` (in `matrix_n.rs`'s
`Nat → Nat → Rat` encoding, not four separate scalars), plus the full
BOTH-SIDED invertibility family stated through `Rat.matMul`/`Rat.matId`
(the general pointwise encoding), at each of the four `(i,j)` entries:
`matMul A (matInv2 A) 2 i j = matId i j` and
`matMul (matInv2 A) A 2 i j = matId i j`. This connects the two previously
disconnected islands (symbolic-dimension `matMul`/`matId`, and fixed-size
`det2`/`inv2`/`mul_adj2`) rather than adding a third isolated fact family.

In progress. Updated further below as work lands.

## Landed (in progress, update continues after full sweep + facts)

`crates/axeyum-lean-kernel/src/rat_prelude/matrix_invertible.rs` (new module),
registered in `rat_prelude.rs`. 11 declarations:

- `Rat.matInv2` (Definition, general A : Nat -> Nat -> Rat)
- `Rat.matInv2_matMul_top_left/_top_right/_bottom_left/_bottom_right`
  (A^-1 * A = I, all four entries, bridging `super::matrix`'s existing
  `inv2_*` family into the general `matMul`/`matId` encoding)
- `Rat.matMul_matInv2_top_left/_top_right/_bottom_left/_bottom_right`
  (A * A^-1 = I, all four entries -- the genuinely NEW direction, via
  `mul_adj2_*` scaled by invD)
- `Rat.matInv2_eval_example` (discriminating Definition check)
- `Rat.matInv2_example` (row 3, ADR-0825 collapse)

Bug found and fixed during self-check: `right_entry_proof`'s two
`middle_swap`-reversal steps had `rsymm`'s (a,b) arguments backwards
(`rsymm(d, term0, invd_xy, ms1)` when `ms1 : Eq invd_xy term0`, needing
`rsymm(d, invd_xy, term0, ms1)`) -- caught by the mandatory bisect-by-
toggling-declarations method (CLAUDE.md), isolated to
`declare_matmul_matinv2_top_left` specifically before the fix.

New ADR: `docs/research/09-decisions/adr-1040-both-sided-2x2-invertibility-bridges-the-fixed-size-and-symbolic-matrix-families.md`.
Curriculum doc updated: LA-1 section in
`docs/curriculum/graded-statement-families-number-theory-and-linear-algebra.md`.
New test file: `crates/axeyum-lean-kernel/src/rat_prelude/matrix_invertible_tests.rs`.
`unnamed_but_live_declarations` in the shared `rat_prelude_tests.rs` updated
in the same commit (11 new names).
