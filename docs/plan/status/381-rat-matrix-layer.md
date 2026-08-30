# Status: the matrix layer over `Nat -> Nat -> Rat`

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, rat-matrix-layer, 2026-08-30).** See the detail below.

**Track:** Mathematics 2026-08 — linear algebra, the general-dimension layer
**Phase:** ADR-0761 landed; product, associativity, bilinearity, identity and
both unit laws in the kernel, axiom-free
**Date:** 2026-08-30

## Summary

`Rat.dotN` gave this kernel an inner product at arbitrary dimension over ℚ,
Cauchy–Schwarz included. One index up there was nothing: every determinant
declaration was fixed-size with entries passed as separate scalar arguments,
and `F-determinant-multiplicative-over-constructed-rationals` states
`det(AB) = det A · det B` by writing out all eight entries.

This lane built the matrix layer on the encoding `sumRange` and `dotN` already
sit on. A matrix is a function `Nat -> Nat -> Rat` with dimensions as ordinary
arguments; `Rat.matMul A B k` is itself such a function, so
`matMul (matMul A B k) C m` is well-typed with no coercion.

## Delivered

`crates/axeyum-lean-kernel/src/rat_prelude/matrix_n.rs` — thirteen
declarations, all axiom-free:

| declaration | statement |
|---|---|
| `Rat.matMul` | `A B k i j := sumRange (fun t => A i t * B t j) k` |
| `Rat.matMul_zero` | `matMul A B 0 i j = 0` (`Eq.refl`) |
| `Rat.matMul_succ` | `matMul A B (succ k) i j = matMul A B k i j + A i k * B k j` (`Eq.refl`) |
| `Rat.matMul_assoc` | `matMul (matMul A B k) C m i j = matMul A (matMul B C m) k i j` |
| `Rat.matMul_add_left` | `matMul (fun r t => A1 r t + A2 r t) B k i j = matMul A1 B k i j + matMul A2 B k i j` |
| `Rat.matMul_add_right` | the mirror, via `left_distrib` |
| `Rat.matMul_smul_left` | `matMul (fun r t => c * A r t) B k i j = c * matMul A B k i j` |
| `Rat.sumRange_delta` | `(∀ t, t ≠ i → f t = 0) → Lt i n → sumRange f n = f i` |
| `Rat.matId` | `i j := if Nat.beq i j then 1 else 0` |
| `Rat.matId_diag` | `matId i i = 1` |
| `Rat.matId_off_diag` | `¬(i = j) → matId i j = 0` |
| `Rat.matMul_id_left` | `Lt i n → matMul matId A n i j = A i j` |
| `Rat.matMul_id_right` | `Lt j n → matMul A matId n i j = A i j` |

Every statement is **pointwise** (`… i j = … i j`), and that is forced:
`funext` is absent from this kernel (control of the same kind, present:
`congrFun'`), so an `Eq` between two `Nat -> Nat -> Rat` values is not
available. Pinned by `the_matrix_associativity_statement_is_pointwise`, which
asserts the rendered type verbatim.

Also:

Detail moved to [`../notes/381-rat-matrix-layer.md`](../notes/381-rat-matrix-layer.md).

