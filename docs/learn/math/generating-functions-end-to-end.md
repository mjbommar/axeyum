# End To End: Generating Functions

This lesson follows one finite generating-functions resource from coefficient
lists to convolution replay, a bounded Fibonacci identity, bad-product
rejection, and the general theorem horizon. It uses
[generating-functions-v0](../../../artifacts/examples/math/generating-functions-v0/).

Concept rows:

- `curriculum_counting`, `curriculum_polynomials`, and
  `curriculum_sequences_and_limits` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_discrete_math`, `field_abstract_algebra`,
  `field_probability_theory`, and `field_real_analysis` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `coefficient-extraction-witness` | `sat` | replay-only |
| `cauchy-product-convolution` | `sat` | replay-only |
| `fibonacci-generating-prefix` | `sat` | replay-only |
| `bad-cauchy-product-rejected` | `unsat` | checked |
| `general-generating-functions-lean-horizon` | `not-run` | lean-horizon |

Every checked row is finite coefficient arithmetic. The pack does not prove
closed-form extraction, convergence, asymptotic coefficient estimates, or
general recurrence-solving theorems.

## Replay Coefficient Extraction

The first witness treats a finite ordinary generating function as a polynomial:

```text
F(x) = 1 + 3*x + 6*x^2 + 10*x^3
```

The sequence prefix and polynomial coefficients are the same exact list:

```text
sequence   = [1, 3, 6, 10]
polynomial = [1, 3, 6, 10]
indices    = [0, 1, 2, 3]
extracted  = [1, 3, 6, 10]
```

The validator checks every requested coefficient index against the coefficient
list. This is the finite, replayable part of ordinary generating functions:
coefficient lookup is just indexed exact arithmetic over a fixed list.

## Replay A Cauchy Product

The second witness multiplies two finite ordinary generating polynomials:

```text
A(x) = 1 + 2*x + x^2
B(x) = 1 + x + x^2
```

The proposed product is:

```text
A(x) * B(x) = 1 + 3*x + 4*x^2 + 3*x^3 + x^4
```

The checker recomputes each coefficient by finite convolution:

```text
c0 = 1*1 = 1
c1 = 1*1 + 2*1 = 3
c2 = 1*1 + 2*1 + 1*1 = 4
c3 = 2*1 + 1*1 = 3
c4 = 1*1 = 1
```

So the product coefficient list is exactly:

```text
[1, 3, 4, 3, 1]
```

## Replay A Fibonacci Prefix Identity

The third witness checks the standard ordinary generating-function identity for
a bounded Fibonacci prefix. The coefficient list is:

```text
F = [0, 1, 1, 2, 3, 5, 8]
```

The multiplier for `1 - x - x^2` is:

```text
[1, -1, -1]
```

The validator multiplies the finite prefix through degree `6` and checks:

```text
(1 - x - x^2) * F(x) = x  through degree 6
```

Coefficient-by-coefficient:

```text
d0 = 0
d1 = 1 - 0 = 1
d2 = 1 - 1 - 0 = 0
d3 = 2 - 1 - 1 = 0
d4 = 3 - 2 - 1 = 0
d5 = 5 - 3 - 2 = 0
d6 = 8 - 5 - 3 = 0
```

So the checked prefix is:

```text
[0, 1, 0, 0, 0, 0, 0]
```

That proves only the listed finite prefix. It is not a proof of the general
closed-form or analytic generating-function identity.

## Reject A Bad Product

The checked `unsat` row uses:

```text
left  = [1, 2]
right = [3, 4, 5]
```

The claimed product is:

```text
[3, 10, 12, 10]
```

The validator recomputes the real finite convolution:

```text
c0 = 1*3 = 3
c1 = 1*4 + 2*3 = 10
c2 = 1*5 + 2*4 = 13
c3 = 2*5 = 10
```

The first bad index is therefore `2`:

```text
claimed c2 = 12
actual  c2 = 13
```

This is the trusted-small-checking pattern: a large or untrusted search could
propose the product, but the checker only needs the two coefficient lists and
one exact convolution replay.

## Name The Lean Horizon

The finite rows check coefficient arithmetic for fixed lists. The general
theory still needs proof-assistant resources:

- closed-form coefficient extraction;
- recurrence solving;
- analytic convergence of power series;
- asymptotic coefficient estimates;
- general generating-function transformations.

Those belong in Lean-backed theorem rows, not in a finite replay pack.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/generating-functions-v0
```

## Trust Boundary

The validator parses coefficient strings as exact rationals, recomputes
coefficient extraction, finite convolution, the bounded Fibonacci identity, and
the bad coefficient. There is no floating-point tolerance and no hidden
asymptotic claim. General generating-function theory remains explicitly
Lean-horizon.
