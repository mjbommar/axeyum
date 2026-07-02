# Finite Walsh-Hadamard Transform Checks

This lesson follows
[finite-walsh-hadamard-transform-v0](../../../artifacts/examples/math/finite-walsh-hadamard-transform-v0/).
It shows how Axeyum treats an exact orthogonal-transform computation as a
finite rational matrix check, not as a floating-point FFT or general Fourier
theorem.

## The Fixed Transform

The pack fixes the order-4 Hadamard matrix:

```text
H = [ 1  1  1  1
      1 -1  1 -1
      1  1 -1 -1
      1 -1 -1  1 ]
```

and the source vector:

```text
x = [1, 2, -1, 0]
```

The checked finite replay recomputes:

```text
H^T H = 4I
Hx = [2, -2, 4, 0]
H(Hx)/4 = x
||Hx||^2 = 4 ||x||^2
```

All arithmetic is exact rational arithmetic.

## The Bad Row

The malformed row claims the second transform coefficient is `-1`. Replay
recomputes the coefficient:

```text
1 - 2 - 1 - 0 = -2
```

The source-linked QF_LRA artifact checks the final conflict:

```text
transform_coefficient_1 = -2
transform_coefficient_1 = -1
```

That produces checked Farkas evidence for the finite arithmetic contradiction.

## Trust Boundary

```text
untrusted fast search -> candidate transform, inverse, energy, or false coefficient
trusted small checking -> exact rational matrix replay and checked Farkas evidence
theorem horizon       -> all-dimension transforms, fast algorithms, Fourier theory, stability
```

The checker does not trust a transform implementation, a recursive FFT-style
routine, or floating-point orthogonality. It trusts only exact replay of the
listed matrix and vector plus the small checked equality conflict.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-walsh-hadamard-transform-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_walsh_hadamard_bad_transform_coefficient_artifact_emits_checked_farkas
python3 scripts/query-foundational-resources.py checks --pack finite-walsh-hadamard-transform-v0 --route Farkas --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the malformed
coefficient row has checked Farkas evidence, and the general transform theorem
row remains `lean-horizon`.
