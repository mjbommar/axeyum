# Checks

## `matrix-vector-solution`

Expected result: `sat`.

The witness vector `[1, 2]` satisfies `Ax = b` for the fixed `2x2` rational
matrix.

## `lu-factorization-witness`

Expected result: `sat`.

The witness matrices `L` and `U` multiply back to `A`, with `L` lower
triangular and unit diagonal and `U` upper triangular.

## `singular-system-inconsistent`

Expected result: `unsat`.

The checked query is the absence of a solution to a singular `2x2` linear
system. The validator checks the row-scaling certificate exactly:
`[2, 2] = 2 * [1, 1]` while `3 != 2 * 1`.

The resource-backed Axeyum regression builds the same equations as a
conjunctive `QF_LRA` system and requires rechecked `UnsatFarkas` evidence.
