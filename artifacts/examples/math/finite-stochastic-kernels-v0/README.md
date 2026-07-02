# Finite Stochastic Kernels V0

This pack adds exact finite stochastic-kernel checks. It treats a kernel as a
finite table from source states to probability distributions over target
states, then checks normalization, pushforward, joint-table factorization,
disintegration, and composition.

The examples are:

- a finite kernel normalization witness;
- a pushforward distribution through a kernel;
- a joint table that factors into a source distribution and kernel, plus
  recovery of the kernel from the joint table;
- a composed two-step kernel witness;
- replay-only rejection of a malformed kernel row and a malformed composed
  entry;
- separate checked `QF_LRA`/Farkas rows for the false final obligations;
- a regular-conditional-probability and disintegration Lean-horizon row.

## Concepts

- `field_probability_theory`
- `field_measure_theory`
- `field_statistics`
- `field_linear_algebra`
- `field_differential_equations_and_dynamical_systems`
- `field_set_theory_and_foundations`
- `curriculum_sets`
- `curriculum_relations_and_functions`
- `curriculum_rationals`
- `curriculum_counting`
- `curriculum_linear_algebra`

## Trust Story

The validator checks finite source/target sets, exact rational probabilities,
row normalization, pushforward sums, joint probabilities
`P(x,y) = mu(x) K(x,y)`, marginalization, recovery of `K(x,y)` from
`P(x,y) / mu(x)`, and finite kernel composition.

This pack is checked finite evidence for finite stochastic-kernel obligations.
Malformed kernel rows and malformed composed entries are first rejected by
exact finite replay, then separate `qf-lra-*` rows check the final linear
contradictions. It is not a proof of regular conditional probabilities,
disintegration theorems, general Markov kernels on measurable spaces, or
stochastic-process convergence. The malformed rows also have source-linked
QF_LRA/Farkas regressions so the `unsat` evidence is checked independently of
solver search.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-stochastic-kernels-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_stochastic_kernel_bad_row_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_stochastic_kernel_bad_composition_artifact_emits_checked_farkas
```
