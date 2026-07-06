# End To End: Finite Policy Iteration

Policy iteration solves a discounted Markov decision process by alternating
two exact steps over a finite table:

```text
evaluate the current policy (a linear system) -> improve it greedily -> stop when stable
```

This resource checks one exact-rational version of that loop: a complete
committed policy-iteration trace on the same MDP as
[End To End: Finite Value Iteration](value-iteration-end-to-end.md), reaching
the same exact optimum by a different algorithm. It is not a proof of the
policy-improvement theorem, policy-iteration termination in general, or
floating-point dynamic programming.

## Source Data

The pack
[`finite-policy-iteration-v0`](../../../artifacts/examples/math/finite-policy-iteration-v0/README.md)
uses the three-state, two-action MDP with discount `gamma = 1/2` (`s3` is
absorbing):

| State | Action | Reward | Transition `(s1, s2, s3)` |
|---|---|---:|---|
| `s1` | `a` | `1` | `(0, 1, 0)` |
| `s1` | `b` | `2` | `(0, 0, 1)` |
| `s2` | `a` | `3` | `(0, 0, 1)` |
| `s2` | `b` | `0` | `(1/2, 1/2, 0)` |
| `s3` | `a` | `0` | `(0, 0, 1)` |

## The Two Steps And The Trace

Evaluation solves the current policy's fixed-point equation exactly;
improvement backs up every action against those values and takes the unique
greedy argmax:

```text
evaluation:  V = r_pi + gamma * P_pi * V
improvement: pi'(s) = argmax_a [ r(s, a) + gamma * sum_{s'} P(s' | s, a) * V(s') ]
```

Everything is rational, so both the linear solves and the comparisons are
exact — no rounding, no tolerance. From the deliberately suboptimal
`pi0 = (b, b, a)`:

| Round | Policy | Evaluated Values | Greedy |
|---|---|---|---|
| 0 | `(b, b, a)` | `(2, 2/3, 0)` | `(b, a, a)` |
| 1 | `(b, a, a)` | `(2, 3, 0)` | `(a, a, a)` |
| 2 | `(a, a, a)` | `(5/2, 3, 0)` | `(a, a, a)` — stable |

Three things are worth watching:

- the first evaluation is a *genuine linear solve*: under `pi0`, state `s2`
  feeds back into `s1` and `s2`, and
  `V(s2) = (1/4)*V(s1) + (1/4)*V(s2)` solves to the non-obvious `2/3`;
- the improvements land one state per round — `s2` switches first, then
  `s1` — and the third round reproduces its own policy, which is exactly the
  algorithm's stopping rule;
- the evaluated values improve monotonically,
  `(2, 2/3, 0) <= (2, 3, 0) <= (5/2, 3, 0)`, ending at the same exact
  optimum `(5/2, 3, 0)`, `(a, a, a)` that value iteration reaches by
  repeated Bellman backups.

Those componentwise inequalities are single-instance replays of the
policy-improvement step on this trace — not the policy-improvement theorem,
the same way the value-iteration pack replays contraction steps rather than
the Banach theorem.

## What Axeyum Checks

The validator checks four replay rows:

- the finite MDP table, discount, exact probability-row sums, and the
  well-formedness of the three committed policies;
- every policy-evaluation solution, by substituting it back into its
  fixed-point equation and requiring an exact zero residual;
- every improvement round's Q-values, unique greedy argmax, and the
  termination-by-stability round;
- the componentwise monotone value improvement.

Then it rejects a malformed claim:

```text
V_pi0(s2) = 1/2
```

Exact replay solves the evaluation equation to `2/3`. The separate checked
proof row isolates the arithmetic contradiction:

```text
mdp_v_pi0_s2 = 2/3
mdp_v_pi0_s2 = 1/2
```

The QF_LRA/Farkas regression parses the source SMT-LIB artifact, emits
`UnsatFarkas` evidence, and checks the certificate independently.

## Trust Boundary

Trusted:

- exact replay of the committed MDP table and the three policies;
- exact zero-residual replay of every policy-evaluation linear system;
- exact rational replay of every improvement round and the stability round;
- exact replay of the monotone value improvement;
- independent checking of the Farkas certificate for the malformed scalar row.

Untrusted or out of scope:

- the policy-improvement theorem in general and policy-iteration termination
  and optimality theorems;
- uniqueness of the optimal value function in general;
- modified, asynchronous, and approximate policy iteration;
- average-reward, infinite-horizon, and continuous state/action MDP theory;
- the linear-programming formulation of MDPs;
- stochastic approximation, Q-learning, and exploration;
- floating-point policy-evaluation and dynamic-programming behavior.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-policy-iteration-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_policy_iteration_bad_policy_value_artifact_emits_checked_farkas
```

Useful queries:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-policy-iteration-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_policy_iteration_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text policy-iteration \
  --require-any
```
