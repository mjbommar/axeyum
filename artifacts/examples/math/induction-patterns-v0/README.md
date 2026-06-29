# Induction Patterns V0

This pack deepens the `induction` curriculum node with finite checks for the
induction patterns students meet before a full theorem-prover treatment:
ordinary induction, strong induction, loop-invariant induction, and checked
failure of an invalid induction step.

The examples are:

- weak induction over the evenness of `n * (n + 1)`;
- a QF_LIA/Diophantine certificate for a false oddness claim in that prefix;
- strong induction over the Fibonacci bound `fib(n) <= 2^n`;
- loop-invariant replay for a prefix-sum accumulator;
- checked counterexample evidence for the false induction step `n < 3`;
- a full natural-number induction-schema Lean-horizon row.

## Concepts

- `curriculum_induction`
- `curriculum_proof_methods`
- `curriculum_naturals`
- `field_logic_and_proof`
- `field_number_theory`

## Trust Story

The validator uses deterministic integer replay over fixed finite prefixes.
It recomputes every listed arithmetic value, checks every bounded step, and
accepts the invalid-step row only when the listed counterexample really has
`P(k)` true and `P(k + 1)` false. The promoted even-product row is also emitted
as a solver-form integer equation and checked with Diophantine evidence.

This is finite checked evidence plus a small checked QF_LIA certificate for one
finite-prefix obstruction. It teaches the shape of induction obligations, but
it does not certify the universal natural-number induction principle. That
general schema stays under Lean horizon until a kernel-checked artifact exists.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/induction-patterns-v0
```
