# Checks

## `sum-formula-base-case`

Expected: `sat`.

The validator replays `P(0)` by recomputing both the prefix sum and the formula
side exactly.

## `sum-formula-step-bounded`

Expected: `unsat`.

The validator enumerates `k = 0..8` and confirms there is no bounded step
counterexample where `P(k)` holds and `P(k + 1)` fails.

## `sum-formula-conclusion-bounded`

Expected: `unsat`.

The validator enumerates `n = 0..9` and confirms there is no bounded failure of
the prefix-sum formula.

## `bad-step-counterexample-witness`

Expected: `sat`.

The witness shows why a base case alone is not induction: the candidate property
`n = 0` holds at `k = 0` but fails at `k + 1`.

## `induction-schema-lean-horizon`

Expected: `not-run`.

This row names the full theorem-prover boundary. The universal induction rule
stays Lean-horizon until a concrete no-sorry Lean artifact exists.
