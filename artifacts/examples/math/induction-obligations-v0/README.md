# Induction Obligations V0

This pack covers the first bounded mathematical-induction slice for
`induction`: base-case replay, bounded step-obligation checking, bounded
conclusion checking, and a deliberately separate Lean horizon for the full
induction schema.

The finite examples use the prefix-sum formula:

```text
0 + 1 + ... + n = n * (n + 1) / 2
```

The checks are exact bounded artifacts:

- replay the base case at `n = 0`;
- reject a bounded step counterexample through `k <= 8`;
- reject a bounded conclusion counterexample through `n <= 9`;
- replay a counterexample showing that a false candidate property can have a
  base case but fail the step;
- record the universal induction rule as Lean-horizon metadata.

These checks do not claim the full induction axiom or a universal theorem over
all natural numbers.

## Concepts

- `curriculum_induction`
- `curriculum_naturals`
- `field_logic_and_proof`
- `field_number_theory`

## Trust Story

The validator recomputes each finite obligation using exact integer arithmetic
over bounded natural-number domains. UNSAT rows are accepted only after
enumerating the fixed bound named in `expected.json`.

The schema row remains `lean-horizon` until a no-sorry Lean proof assembles the
checked obligations into the universal statement.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/induction-obligations-v0
```
