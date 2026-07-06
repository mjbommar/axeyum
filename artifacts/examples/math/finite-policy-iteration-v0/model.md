# Model

The model is a fixed finite discounted Markov decision process with a
complete policy-iteration trace over exact rational data. The MDP table is
the same one committed in `finite-value-iteration-v0`, so the two packs show
two different algorithms reaching the same exact optimum.

## States, Actions, And Discount

```text
states  = {s1, s2, s3}     (s3 is absorbing)
actions = {a, b}           (s3 has only action a)
gamma   = 1/2
```

## MDP Table

| State | Action | Reward | Transition `(s1, s2, s3)` |
|---|---|---:|---|
| `s1` | `a` | `1` | `(0, 1, 0)` |
| `s1` | `b` | `2` | `(0, 0, 1)` |
| `s2` | `a` | `3` | `(0, 0, 1)` |
| `s2` | `b` | `0` | `(1/2, 1/2, 0)` |
| `s3` | `a` | `0` | `(0, 0, 1)` |

## Policy Iteration

One round evaluates the current policy exactly, then improves it greedily:

```text
evaluation:  solve V = r_pi + gamma * P_pi * V     (a linear system)
improvement: Q(s, a) = r(s, a) + gamma * sum_{s'} P(s' | s, a) * V(s')
             pi'(s)  = argmax_a Q(s, a)
stop when pi' = pi
```

Every reward, probability, and the discount is rational, so both the linear
solves and the greedy comparisons are exact arithmetic. No floating-point
tolerance is used.

## Fixed Trace

Starting from the deliberately suboptimal policy `pi0 = (b, b, a)`:

```text
evaluate pi0: V(s1) = 2 + (1/2)*0                          = 2
              V(s2) = 0 + (1/2)*((1/2)*2 + (1/2)*V(s2))    => V(s2) = 2/3
              V_pi0 = (2, 2/3, 0)
improve:      Q(s1) = (4/3, 2)   -> keep b
              Q(s2) = (3, 2/3)   -> switch to a
              pi1 = (b, a, a)

evaluate pi1: V_pi1 = (2, 3, 0)
improve:      Q(s1) = (5/2, 2)   -> switch to a
              Q(s2) = (3, 5/4)   -> keep a
              pi2 = (a, a, a)

evaluate pi2: V_pi2 = (5/2, 3, 0)
improve:      Q(s1) = (5/2, 2), Q(s2) = (3, 11/8) -> greedy = pi2
              stable: policy iteration terminates
```

The first evaluation needs a genuine linear solve: under `pi0`, state `s2`
transitions back into `s1` and `s2`, so its value equation
`V(s2) = (1/4)*V(s1) + (1/4)*V(s2)` must be solved, giving the
non-obvious rational `2/3`.

## Monotone Improvement And The Shared Optimum

The evaluated values improve componentwise, strictly somewhere each round:

```text
V_pi0 = (2, 2/3, 0)  <=  V_pi1 = (2, 3, 0)  <=  V_pi2 = (5/2, 3, 0)
```

The terminal values `(5/2, 3, 0)` and policy `(a, a, a)` match the exact
Bellman fixed point replayed in `finite-value-iteration-v0` — two different
algorithms, one committed optimum. These componentwise inequalities are
single-instance replays; the policy-improvement theorem, termination, and
optimality in general stay in the horizon row.
