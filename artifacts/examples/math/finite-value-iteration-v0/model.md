# Model

The model is a fixed finite discounted Markov decision process with a
complete value-iteration trace over exact rational data.

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

Every transition row is a probability distribution and every entry is
rational, so the whole trace is exact arithmetic. No floating-point
tolerance is used.

## Bellman Backup And Value Iteration

One value-iteration step backs up every state-action pair against the
current value vector `V` and takes the greedy maximum:

```text
Q(s, a) = r(s, a) + gamma * sum_{s'} P(s' | s, a) * V(s')
V'(s)   = max_a Q(s, a)
```

## Fixed Trace

From `V0 = (0, 0, 0)`:

```text
iter 1: Q(s1) = (1, 2)       -> V1(s1) = 2    (greedy b)
        Q(s2) = (3, 0)       -> V1(s2) = 3    (greedy a)
        V1 = (2, 3, 0)
iter 2: Q(s1) = (5/2, 2)     -> V2(s1) = 5/2  (greedy switches to a)
        Q(s2) = (3, 5/4)     -> V2(s2) = 3
        V2 = (5/2, 3, 0)
iter 3: Q(s1) = (5/2, 2)     -> V3(s1) = 5/2
        Q(s2) = (3, 11/8)    -> V3(s2) = 3
        V3 = (5/2, 3, 0) = V2
```

The third iteration reproduces the second exactly, so `(5/2, 3, 0)` is an
exact fixed point of the Bellman optimality operator for this MDP, with
greedy policy `(a, a, a)`. The greedy action at `s1` switches from the
myopic `b` (immediate reward `2`) to the far-sighted `a` (reward `1` plus
discounted access to `s2`'s reward `3`) as soon as the backup sees one step
ahead.

## Contraction Steps

Sup-norm distances between successive value vectors:

```text
||V1 - V0|| = 3
||V2 - V1|| = 1/2 <= (1/2) * 3
||V3 - V2|| = 0   <= (1/2) * (1/2)
```

These are single-instance contraction inequalities on this trace. The Banach
fixed-point theorem, convergence of value iteration in general, and
uniqueness/optimality of the fixed point stay in the horizon row.
