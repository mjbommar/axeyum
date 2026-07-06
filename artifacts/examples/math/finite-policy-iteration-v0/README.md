# Finite Policy Iteration

This pack checks one finite, exact-rational policy-iteration trace on a fixed
discounted Markov decision process — the same MDP committed in
[`finite-value-iteration-v0`](../finite-value-iteration-v0/README.md), so the
two packs show two different algorithms reaching the same exact optimum. It
is meant for learners, proof contributors, solver contributors, and
downstream consumers who need a small example of:

```text
policy -> exact linear-system evaluation -> greedy improvement -> stable policy -> checked rejection
```

The checked object is a three-state, two-action MDP with discount
`gamma = 1/2`, started from the deliberately suboptimal policy `(b, b, a)`.
Every reward, probability, evaluated value, and greedy comparison is
rational, so the whole trace — three exact policy-evaluation linear solves,
two greedy improvement rounds, termination by policy stability, and the
componentwise monotone value improvement — replays with exact arithmetic.
The pack does not prove the policy-improvement theorem in general,
policy-iteration termination or optimality, or anything about floating-point
dynamic programming.

## Concept Rows

- `field_probability_theory`
- `field_differential_equations_and_dynamical_systems`
- `field_optimization_and_convexity`
- `curriculum_linear_algebra`
- `curriculum_rationals`
- `bridge_stochastic_kernel`
- `bridge_finite_value_iteration_shadow`
- `bridge_finite_policy_iteration_shadow`
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

The committed trace from `pi0 = (b, b, a)`:

| Round | Policy | Evaluated Values | `Q(s1, a), Q(s1, b)` | `Q(s2, a), Q(s2, b)` | Greedy |
|---|---|---|---|---|---|
| 0 | `(b, b, a)` | `(2, 2/3, 0)` | `4/3, 2` | `3, 2/3` | `(b, a, a)` |
| 1 | `(b, a, a)` | `(2, 3, 0)` | `5/2, 2` | `3, 5/4` | `(a, a, a)` |
| 2 | `(a, a, a)` | `(5/2, 3, 0)` | `5/2, 2` | `3, 11/8` | `(a, a, a)` — stable |

The first evaluation needs a genuine linear solve: under `pi0`, state `s2`
transitions back into `s1` and `s2`, so
`V(s2) = (1/4)*V(s1) + (1/4)*V(s2)` solves to the non-obvious rational
`2/3`. The greedy action at `s2` switches first, `s1` switches second, and
the third round reproduces its own policy, so the algorithm stops. The
values improve monotonically, `(2, 2/3, 0) <= (2, 3, 0) <= (5/2, 3, 0)`,
ending at the same exact optimum `(5/2, 3, 0)`, `(a, a, a)` that
`finite-value-iteration-v0` reaches by Bellman backups.

## Checked Row

The malformed row claims:

```text
V_pi0(s2) = 1/2
```

Exact replay solves the policy-evaluation equation to `2/3`. The source
SMT-LIB artifact isolates the scalar contradiction:

```text
mdp_v_pi0_s2 = 2/3
mdp_v_pi0_s2 = 1/2
```

The route regression parses the committed artifact, emits `UnsatFarkas`
evidence, and checks that certificate independently.

## Trust Boundary

Trusted:

- exact replay of the committed MDP table, discount, and the three policies;
- exact zero-residual replay of every policy-evaluation linear system;
- exact rational replay of every improvement round's Q-values, unique greedy
  argmax, and the termination-by-stability round;
- exact replay of the componentwise monotone value improvement;
- independent checking of the Farkas certificate for the malformed scalar row.

Out of scope:

- the policy-improvement theorem in general and policy-iteration termination
  and optimality theorems;
- uniqueness of the optimal value function and the Bellman fixed point in
  general;
- modified, asynchronous, and approximate policy iteration;
- average-reward, infinite-horizon, and continuous state/action MDP theory;
- the linear-programming formulation of MDPs;
- stochastic approximation, Q-learning, and exploration behavior;
- floating-point policy-evaluation and dynamic-programming behavior.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-policy-iteration-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_policy_iteration_bad_policy_value_artifact_emits_checked_farkas
```
