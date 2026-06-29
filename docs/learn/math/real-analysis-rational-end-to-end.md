# End To End: Bounded Rational Real Analysis

This lesson follows one real-analysis resource from rational interval and ball
checks to bounded epsilon-delta replay and a checked bad-delta counterexample.
It uses the
[real-analysis-rational-v0](../../../artifacts/examples/math/real-analysis-rational-v0/)
pack.

Concept rows:

- `curriculum_reals`, `curriculum_sequences_and_limits`, and
  `curriculum_calculus` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_real_analysis`, `field_topology`, and `field_logic_and_proof` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `nested-rational-neighborhood-witness` | `sat` | replay-only |
| `linear-epsilon-delta-rational-witness` | `sat` | replay-only |
| `squeeze-polynomial-bound-witness` | `sat` | replay-only |
| `bad-linear-delta-rejected` | `unsat` | checked |
| `general-real-analysis-lean-horizon` | `not-run` | lean-horizon |

The finite rational witnesses are replayed exactly. The bad-delta row is
checked by a concrete counterexample. General real-analysis theorem schemas
remain Lean-horizon.

## Replay A Nested Neighborhood

The interval and ball row records:

```text
inner interval = [1/4, 3/4]
outer ball center = 1/2
outer ball radius = 1/3
```

The validator checks the sample points and the endpoint distance:

```text
max(|1/4 - 1/2|, |3/4 - 1/2|) = 1/4
1/4 < 1/3
```

This is a finite rational containment check, not a theorem about arbitrary
neighborhoods.

## Replay A Bounded Epsilon-Delta Sample

The linear function row records:

```text
f(x) = 2*x + 1
center = 0
f(center) = 1
epsilon = 1
delta = 1/2
domain points = -1/4, 0, 1/4
```

The validator recomputes the domain ball and checks:

```text
|f(x) - f(0)| < 1
```

for every listed domain point. This is the finite sample shape of an
epsilon-delta proof.

## Replay A Polynomial Side Condition

The squeeze-style row records:

```text
|x| <= 1/10
x^2 <= 1/100
|x^3| <= 1/1000
samples = -1/10, -1/20, 0, 1/20, 1/10
```

The validator recomputes the finite sample values and confirms the listed
bounds are `radius^2` and `radius^3`.

## Reject A Bad Delta

The bad-delta row asks whether `delta = 3/4` works for the same function and
`epsilon = 1`. The counterexample is:

```text
x = 2/3
|x - 0| = 2/3 < 3/4
|f(x) - f(0)| = 4/3
```

Since `4/3` is not below `1`, the claimed delta is rejected by exact rational
arithmetic.

## Name The Lean Horizon

The final row records the theorem-prover boundary:

```text
forall epsilon > 0, exists delta > 0,
  forall x, |x - a| < delta -> |f x - L| < epsilon
```

Finite rational samples and counterexamples are useful evidence, but fully
quantified continuity, completeness, and arbitrary limit laws need a Lean route
or equivalent kernel-checked proof artifact.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/real-analysis-rational-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current bounded real-analysis resource pattern:

```text
untrusted fast search -> rational neighborhood or delta candidate
trusted small checking -> exact Fraction replay and counterexample checking
remaining horizon -> fully quantified real-analysis proof reconstruction
```

The graduation route is QF_LRA encoding for bounded rows plus no-sorry Lean
artifacts for the general theorem schemas.
