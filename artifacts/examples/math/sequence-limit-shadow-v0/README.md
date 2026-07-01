# Sequence And Limit Shadow

Audience: learners and proof contributors who need a precise boundary between
bounded sequence checks and real-analysis theorems.

This pack checks finite shadows of sequence reasoning: bounded epsilon tails,
finite counterexamples, monotone bounded prefixes, finite Cauchy-tail checks,
checked rejection of a malformed reciprocal-tail bound, and a geometric
partial-sum identity at a fixed index. It does not claim the general epsilon-N
theorem.

## Concept Rows

- `curriculum_sequences_and_limits`
- `curriculum_reals`
- `field_real_analysis`
- `field_topology`

## Claims

- A finite reciprocal tail can satisfy a concrete epsilon bound.
- A constant sequence has a finite counterexample to the proposed limit `0`.
- A finite prefix can be checked for monotonicity and an upper bound.
- A fixed geometric partial sum can be checked against its closed form.
- A fixed finite tail can have no Cauchy counterexample for one epsilon, with
  source-linked QF_LRA/Farkas evidence for the final threshold contradiction.
- A malformed finite reciprocal-tail bound can be rejected after exact replay
  computes `a_2 = 1/3` but the bad row claims distance below `1/4`.
- General convergence theorems remain Lean-horizon.

## Validation

Run from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/sequence-limit-shadow-v0
```

The validator uses exact rational arithmetic. It checks the listed reciprocal
sequence values, finite epsilon-tail inequalities, monotone-prefix inequalities,
the geometric partial-sum identity, and every pair in the finite Cauchy-tail
row. For the checked Cauchy-tail row, it also recomputes the maximum pair
distance `4/21` and links the rejected `>= 1/2` counterexample claim to
`smt2/bounded-cauchy-tail-farkas-conflict.smt2`, which Axeyum checks with
`UnsatFarkas` evidence. For the checked bad reciprocal-tail row, it recomputes
the witness value `1/3` and links the rejected `< 1/4` strict-bound claim to
`smt2/bad-reciprocal-tail-bound-farkas-conflict.smt2`.

## Limitations

The finite rows do not prove convergence. They check only the listed horizons,
indices, and epsilon values. The full `forall epsilon exists N forall n`
definition, monotone convergence, Cauchy completeness, and Bolzano-Weierstrass
remain proof-assistant targets.
