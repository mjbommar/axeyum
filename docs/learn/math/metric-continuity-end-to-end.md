# End To End: Metric Continuity

This lesson follows one finite metric-continuity resource from exact rational
distance data to epsilon-delta replay. It uses
[metric-continuity-v0](../../../artifacts/examples/math/metric-continuity-v0/).

Concept rows:

- `curriculum_sequences_and_limits`, `curriculum_calculus`, and
  `curriculum_reals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_real_analysis`, `field_topology`, and `field_logic_and_proof` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `finite-lipschitz-witness` | `sat` | replay-only |
| `epsilon-delta-continuity-witness` | `sat` | replay-only |
| `open-ball-preimage-witness` | `sat` | replay-only |
| `bad-delta-rejected` | `unsat` | checked |
| `general-continuity-lean-horizon` | `not-run` | lean-horizon |

Every checked row is finite replay over exact rational distances and function
values. The pack does not prove general continuity on real metric spaces.

## Encode A Finite Metric Slice

The witness uses four finite points:

```text
p0, p1, p2, p3
```

with rational line distances:

```text
d(p0,p1) = 1/4
d(p0,p2) = 1/2
d(p0,p3) = 1
d(p1,p2) = 1/4
d(p1,p3) = 3/4
d(p2,p3) = 1/2
```

The function table is:

```text
f(p0) = 0
f(p1) = 1/2
f(p2) = 1
f(p3) = 2
```

This is the finite sample of `f(x) = 2x`, represented as exact table data.

## Replay A Lipschitz Witness

The claimed Lipschitz constant is:

```text
L = 2
```

The validator checks every pair against:

```text
|f(x) - f(y)| <= 2 * d(x,y)
```

For example:

```text
|f(p0) - f(p3)| = |0 - 2| = 2
2 * d(p0,p3) = 2 * 1 = 2
```

and similarly for all finite pairs. This is a finite pairwise replay, not a
global theorem about all real inputs.

## Replay An Epsilon-Delta Witness

At center `p0`, the witness fixes:

```text
epsilon = 1
delta = 1/2
target value = f(p0) = 0
```

The domain delta-ball uses strict distance:

```text
B_domain(p0, 1/2) = {p0, p1}
```

because:

```text
d(p0,p0) = 0 < 1/2
d(p0,p1) = 1/4 < 1/2
d(p0,p2) = 1/2 is not < 1/2
```

The output epsilon-ball around `0` is:

```text
B_output(0, 1) = {p0, p1}
```

because `|f(p2)-0| = 1` is not strictly below `1`. The validator checks that
the finite domain ball maps inside the finite output ball.

## Replay An Open-Ball Preimage

The same data also gives an open-ball preimage row:

```text
preimage({y | |y - 0| < 1}) = {p0, p1}
```

The validator recomputes the output-ball membership from the function table and
checks that it matches the finite domain ball around `p0` of radius `1/2`.

This is the topological form of the same finite continuity shadow: preimages of
open balls are checked by exact finite enumeration.

## Reject A Bad Delta

The negative row claims that:

```text
delta = 3/4
```

works for the same `epsilon = 1` at `p0`. The checker rejects this with the
counterexample:

```text
p2
```

because:

```text
d(p0,p2) = 1/2 < 3/4
|f(p2) - f(p0)| = |1 - 0| = 1
1 is not < epsilon
```

The candidate delta is untrusted; the small checker validates the counterexample
with exact rational arithmetic.

## Name The Lean Horizon

The finite pack checks:

```text
finite metric table
finite Lipschitz inequality
one epsilon-delta witness
one open-ball preimage
one bad-delta refutation
```

The general theorem shape remains a proof-assistant target:

```text
forall epsilon > 0,
exists delta > 0,
forall x,
d_X(x,a) < delta -> d_Y(f x, f a) < epsilon
```

General continuity, compactness, connectedness, and arbitrary topological-space
theorems stay Lean-horizon until no-sorry artifacts exist.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/metric-continuity-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current metric-continuity resource pattern:

```text
untrusted fast search -> finite metric, delta, preimage, or counterexample row
trusted small checking -> exact rational distances and finite enumeration
remaining horizon -> fully quantified real metric-space continuity
```

The graduation target is to encode finite epsilon-delta and open-ball preimage
checks as deterministic exact-rational obligations, then replay witnesses and
bad-delta refutations through Axeyum instead of pack-local Python alone.
