# End To End: Sequence And Limit Shadows

This lesson follows one finite analysis resource from exact rational sequence
values to bounded epsilon-tail checks, finite counterexamples, monotone prefix
replay, a geometric partial-sum identity, and a bounded Cauchy-tail
no-counterexample row. It uses
[sequence-limit-shadow-v0](../../../artifacts/examples/math/sequence-limit-shadow-v0/).

Concept rows:

- `curriculum_sequences_and_limits` and `curriculum_reals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_real_analysis` and `field_topology` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `reciprocal-tail-bounded-epsilon` | `sat` | replay-only |
| `constant-one-limit-counterexample` | `sat` | replay-only |
| `monotone-bounded-prefix` | `sat` | replay-only |
| `geometric-partial-sum-identity` | `sat` | replay-only |
| `bounded-cauchy-tail-no-counterexample` | `unsat` | checked |
| `general-limit-lean-horizon` | `not-run` | lean-horizon |

Every executable row is finite and exact-rational. The pack does not prove
general convergence, Cauchy completeness, monotone convergence, compactness,
Bolzano-Weierstrass, or any fully quantified epsilon-N theorem.

## Replay A Bounded Epsilon Tail

The reciprocal-tail row fixes:

```text
a_n = 1 / (n + 1)
limit = 0
epsilon = 1/3
start_index = 3
horizon = 8
```

The listed values are:

```text
1, 1/2, 1/3, 1/4, 1/5, 1/6, 1/7, 1/8, 1/9
```

For indices `3` through `8`, the validator recomputes the exact rational
formula and checks:

```text
|a_n - 0| < 1/3
```

This is a finite tail check. It is shaped like an epsilon-N proof obligation,
but it is not the theorem `forall epsilon > 0, exists N, forall n >= N`.

## Replay A Counterexample To A Proposed Limit

The constant-sequence row records:

```text
limit = 0
epsilon = 1/2
index = 5
value = 1
```

The validator checks:

```text
|1 - 0| >= 1/2
```

So the listed index is a finite counterexample to being within that epsilon of
the proposed limit `0`.

## Replay A Monotone Bounded Prefix

The monotone-prefix row checks exact rational values of:

```text
a_n = n / (n + 1)
```

for `n = 0..5`:

```text
0, 1/2, 2/3, 3/4, 4/5, 5/6
```

The validator checks each adjacent strict inequality and checks every value is
below the upper bound `1`.

This finite row teaches the shape of monotone-bounded reasoning without
claiming the monotone convergence theorem.

## Replay A Geometric Partial Sum

The geometric row fixes ratio `1/2` and `n = 4`:

```text
sum_{k=0}^4 (1/2)^k = 31/16
(1 - (1/2)^5) / (1 - 1/2) = 31/16
```

The validator recomputes both the finite sum and the closed form exactly.

## Check A Finite Cauchy Tail

The checked `unsat` row asks whether the listed finite tail contains a pair
with distance at least `1/2`:

```text
epsilon = 1/2
values = 1/3, 1/4, 1/5, 1/6, 1/7
```

The validator checks every pair in this finite tail. It finds no pair at
distance at least `1/2`, so the counterexample claim is rejected.

That `unsat` row is still bounded. It says no bad pair exists in the listed
finite tail for one epsilon, not that the sequence is Cauchy.

## Why This Matters

Sequence resources are the clearest place to teach the boundary:

```text
untrusted search proposes finite N, tail, or counterexample data
trusted checker replays exact rational inequalities
general quantified analysis stays Lean-horizon
```

The finite checks are useful because they exercise the same inequality shapes
that later proof-producing routes must justify.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/sequence-limit-shadow-v0
```

## Trust Boundary

The validator checks exact rational sequence values, finite epsilon-tail
inequalities, finite monotone-prefix inequalities, one geometric partial-sum
identity, and every pair in one finite Cauchy-tail row. The full epsilon-N
definition and completeness theorems remain future Lean work.
