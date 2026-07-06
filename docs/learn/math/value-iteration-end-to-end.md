# End To End: Finite Value Iteration

Value iteration solves a discounted Markov decision process by repeating one
exact backup over a finite table:

```text
back up every action -> take the greedy max -> repeat until the values stop moving
```

This resource checks one exact-rational version of that loop: a complete
committed value-iteration trace that happens to reach its exact fixed point
in three iterations. It is not a proof of the Banach fixed-point theorem,
value-iteration convergence in general, or floating-point dynamic
programming.

## Source Data

The pack
[`finite-value-iteration-v0`](../../../artifacts/examples/math/finite-value-iteration-v0/README.md)
uses a three-state, two-action MDP with discount `gamma = 1/2` (`s3` is
absorbing):

| State | Action | Reward | Transition `(s1, s2, s3)` |
|---|---|---:|---|
| `s1` | `a` | `1` | `(0, 1, 0)` |
| `s1` | `b` | `2` | `(0, 0, 1)` |
| `s2` | `a` | `3` | `(0, 0, 1)` |
| `s2` | `b` | `0` | `(1/2, 1/2, 0)` |
| `s3` | `a` | `0` | `(0, 0, 1)` |

## The Backup And The Trace

One step backs up every state-action pair against the current values `V`
and keeps the greedy maximum:

```text
Q(s, a) = r(s, a) + gamma * sum_{s'} P(s' | s, a) * V(s')
V'(s)   = max_a Q(s, a)
```

Every reward, probability, and the discount is rational, so the whole trace
is exact arithmetic — no rounding, no tolerance. From `V0 = (0, 0, 0)`:

| Iteration | `Q(s1, a), Q(s1, b)` | `Q(s2, a), Q(s2, b)` | Values | Greedy |
|---|---|---|---|---|
| 1 | `1, 2` | `3, 0` | `(2, 3, 0)` | `(b, a, a)` |
| 2 | `5/2, 2` | `3, 5/4` | `(5/2, 3, 0)` | `(a, a, a)` |
| 3 | `5/2, 2` | `3, 11/8` | `(5/2, 3, 0)` | `(a, a, a)` |

Two things are worth watching:

- the greedy action at `s1` switches from the myopic `b` (immediate reward
  `2`) to the far-sighted `a` (reward `1` plus discounted access to `s2`'s
  reward `3`) as soon as the backup sees one step ahead;
- the third iteration reproduces the second exactly, so `(5/2, 3, 0)` is an
  *exact* fixed point of the Bellman optimality operator on this MDP — no
  epsilon threshold is involved.

The sup-norm steps between successive value vectors are `3, 1/2, 0`, and
each is at most `gamma` times the previous one. Those are single-instance
contraction inequalities on this trace, the same way the perceptron pack
replays one committed training run rather than the Novikoff bound.

## What Axeyum Checks

The validator checks four replay rows:

- the finite MDP table, discount, and exact probability-row sums;
- every Bellman backup, greedy maximum, and greedy policy across the three
  iterations;
- the exact fixed point: one full backup at `(5/2, 3, 0)` reproduces
  `(5/2, 3, 0)`;
- the sup-norm contraction steps.

Then it rejects a malformed claim:

```text
second-iteration backup Q2(s1, a) = 2
```

Exact replay computes `1 + (1/2)*3 = 5/2`. The separate checked proof row
isolates the arithmetic contradiction:

```text
mdp_q2_s1_a = 5/2
mdp_q2_s1_a = 2
```

The QF_LRA/Farkas regression parses the source SMT-LIB artifact, emits
`UnsatFarkas` evidence, and checks the certificate independently.

## Trust Boundary

Trusted:

- exact replay of the committed MDP table and the full value-iteration trace;
- exact rational replay of every backup, maximum, and greedy policy;
- exact replay of the fixed point and the sup-norm contraction steps;
- independent checking of the Farkas certificate for the malformed scalar row.

Untrusted or out of scope:

- the Banach fixed-point theorem and the gamma-contraction property in
  general;
- value-iteration and policy-iteration convergence for other MDPs, discounts,
  or starting vectors;
- uniqueness and optimality of the Bellman fixed point, and greedy-policy
  optimality theorems;
- infinite-horizon, average-reward, and continuous state/action MDP theory;
- stochastic approximation, Q-learning, and exploration;
- floating-point dynamic-programming behavior.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-value-iteration-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_value_iteration_bad_backup_artifact_emits_checked_farkas
```

Useful queries:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-value-iteration-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_value_iteration_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text bellman \
  --require-any
```
