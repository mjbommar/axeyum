# End To End: Finite Concentration

This lesson follows one finite concentration resource from atom tables to
Markov, Chebyshev, and union-bound replay. It uses
[finite-concentration-v0](../../../artifacts/examples/math/finite-concentration-v0/).

Concept rows:

- `curriculum_sets`, `curriculum_relations_and_functions`,
  `curriculum_rationals`, and `curriculum_counting` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_probability_theory`, `field_statistics`, `field_measure_theory`,
  `field_real_analysis`, and `field_set_theory_and_foundations` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `markov-inequality-witness` | `sat` | replay-only |
| `chebyshev-inequality-witness` | `sat` | replay-only |
| `union-bound-witness` | `sat` | replay-only |
| `bad-concentration-bound-rejected` | `unsat` | checked |
| `general-concentration-lean-horizon` | `not-run` | lean-horizon |

Every checked row is exact finite rational arithmetic over explicitly listed
probability atoms. The pack does not prove Chernoff bounds, Hoeffding bounds,
laws of large numbers, central limit theorems, martingale concentration, or
asymptotic statistical inference.

## Replay Markov's Inequality

The Markov witness uses a nonnegative random variable:

```text
P(low) = 3/4
P(high) = 1/4

X(low) = 0
X(high) = 4
```

The checker recomputes the expectation:

```text
E[X] = 0*(3/4) + 4*(1/4)
     = 1
```

At threshold `2`, the tail event is:

```text
{X >= 2} = {high}
P(X >= 2) = 1/4
```

The finite Markov bound is:

```text
E[X] / 2 = 1/2
```

The row is accepted because:

```text
1/4 <= 1/2
```

This is a replay of one finite table, not a proof of the general theorem.

## Replay Chebyshev's Inequality

The Chebyshev witness uses a centered three-point variable:

```text
P(left) = 1/4
P(center) = 1/2
P(right) = 1/4

Y(left) = -2
Y(center) = 0
Y(right) = 2
```

The checker recomputes the mean:

```text
E[Y] = (-2)*(1/4) + 0*(1/2) + 2*(1/4)
     = 0
```

and the variance:

```text
Var(Y) = (-2)^2*(1/4) + 0^2*(1/2) + 2^2*(1/4)
       = 1 + 0 + 1
       = 2
```

At radius `2`, the centered tail event is:

```text
{|Y - 0| >= 2} = {left, right}
P(|Y - 0| >= 2) = 1/2
```

The finite Chebyshev bound is:

```text
Var(Y) / 2^2 = 2/4 = 1/2
```

The row is accepted because:

```text
1/2 <= 1/2
```

## Replay The Union Bound

The union-bound witness uses four equal atoms:

```text
P(a) = P(b) = P(c) = P(d) = 1/4
```

The events are:

```text
A = {a, b}
B = {b, c}
```

The checker recomputes:

```text
P(A) = 1/2
P(B) = 1/2
P(A union B) = P({a, b, c}) = 3/4
```

The finite union bound is:

```text
P(A union B) <= P(A) + P(B)
3/4 <= 1
```

The overlap at atom `b` is why the union probability is below the sum.

## Reject A False Tail Bound

The negative row reuses the Markov table but claims:

```text
P(X >= 2) <= 1/8
```

The checker recomputes:

```text
P(X >= 2) = P(high) = 1/4
```

and rejects the claim because:

```text
1/4 > 1/8
```

The candidate tail bound is untrusted; the small checker rebuilds the event
probability directly from the atom table.

The solver regression then checks the final false bound as linear rational
arithmetic:

```text
tail_probability = 1/4
tail_probability <= 1/8
```

The search result is not trusted by itself. The trusted part is the independent
Farkas certificate check over exact rational multipliers.

## Name The Lean Horizon

The finite pack checks:

```text
normalized finite atom probabilities
finite nonnegative random variables
expectations
variances
finite tail events
finite event unions
bad tail-bound refutations
```

The following remain proof-assistant targets:

```text
Chernoff bounds
Hoeffding bounds
laws of large numbers
central limit theorems
martingale concentration
asymptotic statistical inference
```

Those stay Lean-horizon until no-sorry probability and statistics artifacts
exist.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-concentration-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_concentration_bad_tail_bound_emits_checked_farkas
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current finite concentration resource pattern:

```text
untrusted fast search -> tail event, event union, bound, or counterexample row
trusted small checking -> exact rational expectations, variances, finite event sums, Farkas certificate checks
remaining horizon -> general concentration and limit theorems
```

The graduation target is to encode finite tail events, expectations,
variances, and event unions as exact rational tables, replay Markov,
Chebyshev, and union-bound inequalities by exact rational arithmetic, and emit
checked counterexample evidence for false concentration bounds.
