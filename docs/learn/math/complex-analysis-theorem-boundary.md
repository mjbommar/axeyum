# Complex Analysis Theorem Boundary

This page separates Axeyum's exact finite complex-number, complex-plane,
Cauchy-Riemann-shadow, and rational-polynomial resources from general
complex-analysis and global factorization theorems.

Primary packs:

- [complex-algebraic-v0](../../../artifacts/examples/math/complex-algebraic-v0/)
- [complex-plane-transforms-v0](../../../artifacts/examples/math/complex-plane-transforms-v0/)
- [finite-cauchy-riemann-shadow-v0](../../../artifacts/examples/math/finite-cauchy-riemann-shadow-v0/)
- [polynomial-identities-v0](../../../artifacts/examples/math/polynomial-identities-v0/)
- [polynomial-factorization-rational-v0](../../../artifacts/examples/math/polynomial-factorization-rational-v0/)

Companion lessons and maps:

- [End To End: Complex Algebraic Replay](complex-algebraic-end-to-end.md)
- [End To End: Complex Plane Transforms](complex-plane-transforms-end-to-end.md)
- [End To End: Finite Cauchy-Riemann Shadow](cauchy-riemann-shadow-end-to-end.md)
- [End To End: Polynomial Identities](polynomial-identities-end-to-end.md)
- [End To End: Rational Polynomial Factorization](polynomial-factorization-end-to-end.md)
- [Number Systems And Arithmetic](number-systems-and-arithmetic.md)
- [Rational And Real Algebra](rational-real-algebra.md)
- [Algebra And Number Theory](algebra-and-number-theory.md)
- [Analysis And Calculus Theorem Horizon Map](analysis-calculus-theorem-horizon-map.md)
- [Theorem Horizon Queries](../../foundational-resources/THEOREM-HORIZON-QUERIES.md)

## Current Finite Resources

The complex-analysis resources use exact rational real-pair arithmetic:

```text
a + bi              -> [a, b]
addition/product    -> rational pair replay
conjugate/norm      -> rational pair replay
polynomial root     -> fixed coefficient evaluation
Mobius transform    -> one rational complex division replay
Cauchy-Riemann row  -> one polynomial, one point, exact partial replay
factorization rows  -> fixed rational coefficient arithmetic
```

Those rows are intentionally small. They can check a displayed complex
arithmetic witness, reject a malformed coordinate/norm claim, replay one
quadratic root, check a rational transform at one input, replay one
`f(z)=z^2` Cauchy-Riemann partial-derivative shadow, or check a fixed rational
polynomial factorization. They do not prove holomorphicity, the general
Cauchy-Riemann theorem, Cauchy's theorem, residue calculus, analytic
continuation, conformal-map theorems, the fundamental theorem of algebra,
algebraic closure, or arbitrary-degree factorization theory.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `complex-arithmetic-replay` | `sat` | replay-only finite arithmetic | The listed real-pair sum and product are recomputed exactly. |
| `conjugate-norm-replay` | `sat` | replay-only finite arithmetic | Conjugate and norm-squared are recomputed for one complex number. |
| `quadratic-root-witness` | `sat` | replay-only finite arithmetic | The listed value `i` is checked as one root of `x^2 + 1`. |
| `bad-product-real-part-rejected` | `unsat` | checked QF_LRA/Farkas | A false product real-coordinate claim is rejected. |
| `bad-norm-squared-rejected` | `unsat` | checked QF_LRA/Farkas | A false norm-squared claim is rejected. |
| `unit-root-cycle-replay` | `sat` | replay-only finite arithmetic | The displayed powers of `i` form an exact order-four cycle. |
| `conjugation-product-replay` | `sat` | replay-only finite arithmetic | The fixed equality `conj(z*w)=conj(z)*conj(w)` is replayed. |
| `mobius-transform-witness` | `sat` | replay-only finite arithmetic | One rational Mobius-transform image is recomputed exactly. |
| `bad-conjugation-product-imaginary-rejected` | `unsat` | checked QF_LRA/Farkas | A false fixed imaginary-coordinate claim is rejected. |
| `bad-unit-square-real-part-rejected` | `unsat` | checked QF_LRA/Farkas | A false unit-complex square claim is rejected by the counterexample `i`. |
| `general-complex-analysis-lean-horizon` | `not-run` | Lean horizon | General complex-analysis theorem claims remain future proof work. |
| `complex-square-real-pair-witness` | `sat` | replay-only finite arithmetic | The listed `f(z)=z^2` real-pair value is recomputed exactly. |
| `partial-derivative-witness` | `sat` | replay-only finite arithmetic | The component-polynomial partials are differentiated and evaluated exactly. |
| `cauchy-riemann-equality-witness` | `sat` | replay-only finite arithmetic | The fixed equalities `u_x=v_y` and `u_y=-v_x` are checked at one point. |
| `complex-derivative-witness` | `sat` | replay-only finite arithmetic | The derivative `f'(1+2i)=2+4i` is replayed for this polynomial. |
| `bad-derivative-real-part-rejected` | `unsat` | replay-only finite arithmetic | A false derivative real-coordinate claim is rejected after replay. |
| `qf-lra-bad-derivative-real-part` | `unsat` | checked QF_LRA/Farkas | The final scalar conflict `derivative_real = 2` versus `3` is checked. |
| `general-cauchy-riemann-lean-horizon` | `not-run` | Lean horizon | General Cauchy-Riemann and holomorphicity theorem claims remain future proof work. |
| `binomial-square-identity` | `sat` | replay-only coefficient arithmetic | One polynomial coefficient identity is checked. |
| `factor-theorem-root-witness` | `sat` | replay-only coefficient arithmetic | A root and displayed linear factorization are replayed. |
| `false-rational-root-rejected` | `unsat` | checked QF_LIA/Diophantine | The false rational-root claim for `x^2 + 1` is rejected. |
| `factorization-product-replay` | `sat` | replay-only coefficient arithmetic | The listed factors multiply to `x^4 - 1`. |
| `polynomial-division-replay` | `sat` | checked coefficient arithmetic | One exact rational polynomial division is checked. |
| `euclidean-gcd-replay` | `sat` | checked coefficient arithmetic | One monic Euclidean GCD is replayed. |
| `square-free-decomposition-replay` | `sat` | checked coefficient arithmetic | One square-free decomposition is replayed. |
| `irreducible-quadratic-rational-rejected` | `unsat` | checked coefficient arithmetic | A rational linear-factorization claim for `x^2 + 1` is rejected. |
| `irreducible-quadratic-discriminant-conflict` | `unsat` | checked QF_LRA/Farkas | The negative-discriminant conflict is checked as a fixed linear contradiction. |
| `general-factorization-theory-lean-horizon` | `not-run` | Lean horizon | General factorization and irreducibility theory remain future proof work. |

The boundary is:

```text
untrusted fast search -> candidate complex value, transform, root, or factorization
trusted small checking -> exact rational replay plus Farkas/Diophantine evidence
theorem horizon       -> holomorphic, global algebraic, and arbitrary-field theorems
```

## What Is Not Proved Yet

The current packs do not prove:

- Cauchy-Riemann theorem schemas or holomorphicity of arbitrary functions
  beyond the single finite polynomial shadow above;
- Cauchy's theorem, the residue theorem, contour integration, Morera,
  Liouville, maximum modulus, or open mapping theorems;
- analytic continuation, branch-cut theory, conformal equivalence, or global
  mapping theorems for Mobius transforms;
- the fundamental theorem of algebra or algebraic closure of the complex
  numbers;
- arbitrary-degree factorization, unique factorization over arbitrary fields,
  Gauss lemma, UFD/PID theory, or complete factorization algorithms;
- complex numerical stability, floating-point complex arithmetic guarantees,
  or certified root-isolation algorithms.

Those claims need theorem statements, hypotheses, and no-`sorry` proof
artifacts before they can graduate from horizon metadata to theorem coverage.

## Query The Boundary

Validate the finite packs:

```sh
python3 scripts/validate-foundational-example-pack.py \
  artifacts/examples/math/complex-algebraic-v0 \
  artifacts/examples/math/complex-plane-transforms-v0 \
  artifacts/examples/math/finite-cauchy-riemann-shadow-v0 \
  artifacts/examples/math/polynomial-identities-v0 \
  artifacts/examples/math/polynomial-factorization-rational-v0
```

Find checked complex real-pair rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack complex-algebraic-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack complex-plane-transforms-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-cauchy-riemann-shadow-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_complex_real_pair_transform \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Find checked polynomial-root and factorization rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack polynomial-identities-v0 \
  --route Diophantine \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack polynomial-factorization-rational-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Find the theorem horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack complex-plane-transforms-v0 \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-cauchy-riemann-shadow-v0 \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack polynomial-factorization-rational-v0 \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --field complex_analysis \
  --shadow-state checked-finite-shadow \
  --require-any
```

Find the bridge concepts:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field complex_analysis \
  --text real-pair \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field complex_analysis \
  --text Cauchy \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field complex_analysis \
  --text polynomial \
  --require-any
```

## Graduation Criteria

Complex-analysis resources graduate only when they add:

1. precise theorem statements for the analytic, algebraic, transform, root,
   or factorization claim;
2. explicit hypotheses, including domain/codomain, field, topology,
   differentiability/holomorphicity, branch, coefficient, degree, and
   nonzero-denominator assumptions;
3. no-`sorry` proof artifacts for each theorem claim before display labels
   change from finite replay to theorem coverage;
4. a kernel-checked route that connects a finite example to a theorem
   instantiation only where that instantiation is actually proved;
5. display labels that keep exact real-pair replay, coefficient replay,
   QF_LRA/Farkas evidence, QF_LIA/Diophantine evidence, and theorem horizons
   separate.

Until then, these packs remain finite checked resources and compact bridges to
future complex-analysis and algebra proof resources.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/complex-algebraic-v0 artifacts/examples/math/complex-plane-transforms-v0 artifacts/examples/math/finite-cauchy-riemann-shadow-v0 artifacts/examples/math/polynomial-identities-v0 artifacts/examples/math/polynomial-factorization-rational-v0
python3 scripts/query-foundational-resources.py checks --pack complex-algebraic-v0 --route Farkas --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack complex-plane-transforms-v0 --route Farkas --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-cauchy-riemann-shadow-v0 --route Farkas --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack polynomial-identities-v0 --route Diophantine --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack polynomial-factorization-rational-v0 --route Farkas --proof-status checked --require-any
python3 scripts/query-foundational-resources.py horizon-frontier --pack complex-plane-transforms-v0 --require-any
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-cauchy-riemann-shadow-v0 --require-any
python3 scripts/query-foundational-resources.py horizon-frontier --pack polynomial-factorization-rational-v0 --require-any
python3 scripts/query-foundational-resources.py horizon-frontier --field complex_analysis --shadow-state checked-finite-shadow --require-any
```

Expected resource boundary: exact complex real-pair arithmetic, fixed
transforms, finite Cauchy-Riemann shadows, displayed roots, coefficient
arithmetic, and fixed factorization rows validate; checked Farkas and
Diophantine contradictions stay scoped evidence; analytic and global
factorization theorems remain explicit Lean/theorem horizons.
