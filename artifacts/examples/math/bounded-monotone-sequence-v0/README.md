# Bounded Monotone Sequence V0

This pack gives the `sequences-and-limits` curriculum node a focused finite
shadow of the monotone convergence theorem. It checks a fixed rational prefix
of `a_n = n/(n+1)`, verifies bounded monotonicity and tail gaps by exact
rational replay, and routes a false upper-bound claim through checked
QF_LRA/Farkas evidence.

The pack covers:

- finite monotone-prefix replay;
- finite prefix supremum replay;
- bounded tail-gap replay against one epsilon;
- checked QF_LRA/Farkas rejection of a malformed upper-bound row;
- a Lean-horizon row for the general monotone convergence theorem.

## Concepts

- `curriculum_sequences_and_limits`
- `curriculum_reals`
- `field_real_analysis`
- `field_topology`

## Trust Story

The validator parses every sequence value as an exact rational string. It
checks that each listed value equals `n/(n+1)`, verifies adjacent monotonicity,
checks the displayed upper bound, recomputes the finite prefix supremum, and
checks the listed finite tail gaps to the proposed limit.

The promoted bad row keeps the sequence replay outside the solver. Exact
replay computes `a_6 = 6/7`, and the source SMT-LIB artifact checks only the
final contradiction against the false claim that `5/6` is an upper bound.

This pack does not prove monotone convergence, completeness of the real
numbers, compactness, or any infinite tail theorem.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/bounded-monotone-sequence-v0
cargo test -p axeyum-solver --test math_resource_lra_routes bounded_monotone_sequence_bad_upper_bound_artifact_emits_checked_farkas
```
