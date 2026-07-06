# Finite Value Iteration

This pack checks one finite, exact-rational value-iteration trace on a fixed
discounted Markov decision process. It is meant for learners, proof
contributors, solver contributors, and downstream consumers who need a small
example of:

```text
MDP table -> Bellman backups -> greedy values -> exact fixed point -> checked rejection
```

The checked object is a fixed three-state, two-action MDP with discount
`gamma = 1/2`, iterated from the zero value vector. Every reward, transition
probability, backup, and maximum is rational, so the entire trace — three
Bellman-backup iterations, a greedy-policy switch at `s1`, the exact fixed
point `(5/2, 3, 0)`, and the sup-norm contraction steps — replays with exact
arithmetic. The pack does not prove the Banach fixed-point theorem,
value-iteration convergence in general, or anything about floating-point
dynamic programming.

## Concept Rows

- `field_probability_theory`
- `field_differential_equations_and_dynamical_systems`
- `field_optimization_and_convexity`
- `curriculum_linear_algebra`
- `curriculum_rationals`
- `bridge_stochastic_kernel`
- `bridge_finite_value_iteration_shadow`
- `bridge_exact_vs_floating_arithmetic`
- `bridge_qf_lra_farkas_anatomy`

## Source Data

| State | Action | Reward | Transition `(s1, s2, s3)` |
|---|---|---:|---|
| `s1` | `a` | `1` | `(0, 1, 0)` |
| `s1` | `b` | `2` | `(0, 0, 1)` |
| `s2` | `a` | `3` | `(0, 0, 1)` |
| `s2` | `b` | `0` | `(1/2, 1/2, 0)` |
| `s3` | `a` | `0` | `(0, 0, 1)` |

The committed trace from `V0 = (0, 0, 0)` with
`Q(s, a) = r + gamma * P . V` and `V'(s) = max_a Q(s, a)`:

| Iteration | `Q(s1, a), Q(s1, b)` | `Q(s2, a), Q(s2, b)` | Values | Greedy |
|---|---|---|---|---|
| 1 | `1, 2` | `3, 0` | `(2, 3, 0)` | `(b, a, a)` |
| 2 | `5/2, 2` | `3, 5/4` | `(5/2, 3, 0)` | `(a, a, a)` |
| 3 | `5/2, 2` | `3, 11/8` | `(5/2, 3, 0)` | `(a, a, a)` |

The third iteration reproduces the second exactly, so `(5/2, 3, 0)` is an
exact fixed point of the Bellman optimality operator with greedy policy
`(a, a, a)`. The greedy action at `s1` switches from the myopic `b` to the
far-sighted `a` at the second iteration. The sup-norm steps `3, 1/2, 0`
satisfy the single-instance contraction inequalities against `gamma = 1/2`.

## Checked Row

The malformed row claims:

```text
second-iteration backup Q2(s1, a) = 2
```

Exact replay computes `1 + (1/2)*3 = 5/2`. The source SMT-LIB artifact
isolates the scalar contradiction:

```text
mdp_q2_s1_a = 5/2
mdp_q2_s1_a = 2
```

The route regression parses the committed artifact, emits `UnsatFarkas`
evidence, and checks that certificate independently.

## Trust Boundary

Trusted:

- exact replay of the committed MDP table, discount, and probability rows;
- exact rational replay of every Bellman backup, greedy maximum, and policy
  in the trace;
- exact replay of the fixed point, the greedy-policy switch, and the
  sup-norm contraction steps;
- independent checking of the Farkas certificate for the malformed scalar row.

Out of scope:

- the Banach fixed-point theorem and gamma-contraction of the Bellman
  operator in general;
- value-iteration and policy-iteration convergence for other MDPs, discounts,
  or starting vectors;
- uniqueness and optimality of the Bellman fixed point and greedy-policy
  optimality theorems;
- infinite-horizon, average-reward, and continuous state/action MDP theory;
- stochastic approximation, Q-learning, and exploration behavior;
- floating-point dynamic-programming behavior.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-value-iteration-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_value_iteration_bad_backup_artifact_emits_checked_farkas
```
