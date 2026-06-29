# End To End: Finite Chebyshev Systems

This lesson follows one exact finite Chebyshev-system resource from
Vandermonde unisolvence replay to interpolation, alternating residual signs,
and a checked duplicate-node rejection. It uses the
[finite-chebyshev-systems-v0](../../../artifacts/examples/math/finite-chebyshev-systems-v0/)
pack.

Concept rows:

- `curriculum_linear_algebra`, `curriculum_polynomials`,
  `curriculum_reals`, and `curriculum_rationals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_functional_analysis_and_operator_theory`,
  `field_numerical_analysis`, `field_linear_algebra`, and
  `field_real_analysis` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `vandermonde-unisolvence-witness` | `sat` | replay-only |
| `interpolation-polynomial-witness` | `sat` | replay-only |
| `alternating-residual-witness` | `sat` | replay-only |
| `bad-duplicate-node-grid-rejected` | `unsat` | checked |
| `general-chebyshev-system-lean-horizon` | `not-run` | lean-horizon |

The positive rows replay finite exact-rational matrix and polynomial
calculations. The negative row is a checked refutation of a false unisolvence
claim. General Chebyshev-system and minimax theorems remain Lean-horizon.

## Replay Vandermonde Unisolvence

The finite grid is:

```text
points = -1, 0, 1
basis = 1, x, x^2
```

The witness records the evaluation matrix:

```text
[[1, -1, 1],
 [1,  0, 0],
 [1,  1, 1]]
```

The validator recomputes the matrix entries and determinant:

```text
det = 2
```

A nonzero determinant means this finite grid is unisolvent for quadratic
polynomials. That is a finite linear-algebra fact, not yet a theorem about
general Chebyshev spaces.

## Replay Interpolation

The interpolation row uses coefficients:

```text
p(x) = 2 - x + 3*x^2
```

The validator multiplies the evaluation matrix by the coefficient vector
`[2, -1, 3]` and checks the samples:

```text
p(-1) = 6
p(0)  = 2
p(1)  = 4
```

This gives the learner a concrete path from polynomial coefficients to a finite
sample table.

## Replay Alternating Residual Signs

The alternating-residual row uses:

```text
r(x) = -1/2 + x^2
points = -1, 0, 1
```

The validator recomputes:

```text
r(-1) =  1/2
r(0)  = -1/2
r(1)  =  1/2
```

The signs alternate `+, -, +`, and every absolute value is `1/2`. This is a
finite alternation-style witness, not a proof of the full minimax alternation
theorem.

## Reject A Duplicate-Node Grid

The bad row claims that the duplicate-node grid is unisolvent:

```text
points = 0, 0, 1
basis = 1, x, x^2
```

The validator recomputes the evaluation matrix:

```text
[[1, 0, 0],
 [1, 0, 0],
 [1, 1, 1]]
```

and checks:

```text
actual determinant = 0
```

It also verifies a nonzero null polynomial:

```text
coefficients = [0, 1, -1]
q(x) = x - x^2
q(0), q(0), q(1) = 0, 0, 0
```

So the grid cannot determine every quadratic polynomial uniquely, and the bad
unisolvence claim is checked `unsat`.

## Name The Lean Horizon

The final row records the theorem-prover boundary:

```text
Haar spaces
general Chebyshev-system theory
minimax approximation
alternation theorems
compactness arguments
infinite-dimensional functional analysis
```

Those require Lean resources or another kernel-checked proof route. This pack
only checks finite rational matrix, polynomial, and sign-pattern evidence.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-chebyshev-systems-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current Chebyshev-system resource pattern:

```text
untrusted fast search -> grid, coefficients, residual, or bad-grid candidate
trusted small checking -> exact rational determinant and polynomial replay
remaining horizon -> general Chebyshev, Haar, minimax, and compactness proofs
```

The graduation route is deterministic exact-rational finite linear algebra plus
checked proof objects for degenerate-grid refutations before broader
functional-analysis claims are promoted.
