# End To End: Finite Integration

This lesson follows one finite integration resource from atom probabilities to
simple-function expectation replay. It uses
[finite-integration-v0](../../../artifacts/examples/math/finite-integration-v0/).

Concept rows:

- `curriculum_sets`, `curriculum_rationals`, and `curriculum_counting` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_measure_theory`, `field_probability_theory`, `field_statistics`, and
  `field_real_analysis` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `simple-function-integral-witness` | `sat` | replay-only |
| `indicator-integral-witness` | `sat` | replay-only |
| `integral-linearity-witness` | `sat` | replay-only |
| `bad-expectation-rejected` | `unsat` | checked |
| `lebesgue-integration-lean-horizon` | `not-run` | lean-horizon |

Every checked row is exact finite rational arithmetic over a normalized atom
table. The pack does not prove Lebesgue integration, monotone convergence,
dominated convergence, Fubini/Tonelli, or almost-everywhere reasoning.

## Replay A Simple-Function Integral

The finite probability space has three atoms:

```text
P(low) = 1/4
P(mid) = 1/4
P(high) = 1/2
```

The simple function is:

```text
f(low) = 0
f(mid) = 2
f(high) = 4
```

The validator recomputes the exact weighted sum:

```text
integral f dP = 0*(1/4) + 2*(1/4) + 4*(1/2)
              = 0 + 1/2 + 2
              = 5/2
```

This is expectation as a finite rational sum.

## Replay An Indicator Integral

The event is:

```text
E = {high}
```

Its measure is:

```text
P(E) = P(high) = 1/2
```

The indicator function has value `1` on `high` and `0` elsewhere, so the
validator checks:

```text
integral 1_E dP = 1*(1/2) = 1/2
```

This is the finite shadow of the rule that indicator integrals recover event
measures.

## Replay Finite Linearity

The linearity witness uses two simple functions on the same atoms:

```text
f = low:0, mid:2, high:4
g = low:1, mid:1, high:3
```

with scales:

```text
2*f - g
```

The validator recomputes both integrals:

```text
integral f dP = 5/2
integral g dP = 2
```

and the combined function:

```text
(2*f - g)(low) = -1
(2*f - g)(mid) = 3
(2*f - g)(high) = 5
```

Then it checks the direct combined integral:

```text
(-1)*(1/4) + 3*(1/4) + 5*(1/2) = 3
```

and the linearity calculation:

```text
2*(5/2) - 2 = 3
```

## Reject A False Expectation

The negative row claims that the first simple function has integral `3`.
The checker recomputes the exact value:

```text
actual integral = 5/2
claimed integral = 3
```

and rejects the claim because:

```text
5/2 != 3
```

The candidate expectation is untrusted; the small checker recomputes it from
the atom table.

## Name The Lean Horizon

The finite pack checks:

```text
normalized finite atom probabilities
finite weighted sums
indicator integrals
finite integral linearity
bad expectation refutations
```

The following remain proof-assistant targets:

```text
Lebesgue integration
monotone convergence
dominated convergence
Fubini/Tonelli
almost-everywhere equivalence
```

Those stay Lean-horizon until no-sorry measure-theory artifacts exist.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-integration-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current finite integration resource pattern:

```text
untrusted fast search -> expectation, event, linearity, or counterexample row
trusted small checking -> exact rational finite sums
remaining horizon -> general measure-theoretic integration
```

The graduation target is to encode finite simple-function integrals as exact
rational weighted sums, replay finite expectation and linearity witnesses
through Axeyum model evaluation, and emit checked counterexample evidence for
rejected expectation claims.
