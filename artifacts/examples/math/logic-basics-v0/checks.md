# Checks

## `and-formula-sat-witness`

Expected: `sat`.

The validator evaluates `p and q` under the listed assignment.

## `excluded-middle-no-counterexample`

Expected: `unsat`.

The validator enumerates `p = false,true` and confirms no assignment falsifies
`p or not p`.

## `contradiction-unsat`

Expected: `unsat`.

The validator enumerates `p = false,true` and confirms no assignment satisfies
`p and not p`.

## `demorgan-equivalence-no-counterexample`

Expected: `unsat`.

The validator enumerates all four assignments for `p,q` and confirms
`not (p and q)` equals `(not p) or (not q)`.

## `tiny-cnf-refutation`

Expected: `unsat`.

The validator enumerates all assignments for `p,q` and confirms the CNF
`(p) and (not p or q) and (not q)` has no satisfying assignment.
