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
- reject a bounded step counterexample through `k <= 8`, with the final
  bad-step count contradiction checked through QF_LIA arithmetic evidence;
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
over bounded natural-number domains. The upgraded step row first enumerates the
fixed bound named in `expected.json`, computes `bad_step_count = 0`, and then
checks the source artifact
`smt2/bounded-step-counterexample-count-lia-conflict.smt2` with Axeyum's
checked QF_LIA arithmetic evidence against the malformed claim
`bad_step_count >= 1`.

The schema row remains `lean-horizon` until a no-sorry Lean proof assembles the
checked obligations into the universal statement.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/induction-obligations-v0
cargo test -p axeyum-solver --test math_resource_lia_routes induction_obligations_bounded_step_count_emits_checked_lia_evidence
```
