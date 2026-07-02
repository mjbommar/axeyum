# Chebyshev Theorem Boundary

This page separates the finite Chebyshev resources Axeyum can check today from
the Haar-space, minimax, and alternation theorems that still require a
kernel-checked theorem route. It is a boundary map, not a new proof route.

Primary packs:

- [finite-chebyshev-systems-v0](../../../artifacts/examples/math/finite-chebyshev-systems-v0/)
- [finite-operator-v0](../../../artifacts/examples/math/finite-operator-v0/)

Concept rows:

- `bridge_finite_operator_chebyshev`
- `field_functional_analysis_and_operator_theory`
- `field_numerical_analysis`
- `field_linear_algebra`
- `field_real_analysis`

## What Is Checked Today

The current Chebyshev resources are exact finite rational checks:

| Resource | Checked finite shadow | Trusted route |
|---|---|---|
| Chebyshev recurrence prefix | `T0,T1,T2,T3` at `x=1/2` | exact replay plus checked QF_LRA/Farkas bad-prefix row |
| Vandermonde unisolvence | determinant of the `[-1,0,1]` quadratic evaluation matrix | exact replay plus checked QF_LRA/Farkas duplicate-node determinant conflict |
| Interpolation sample | `p(x)=2-x+3*x^2` evaluated on the finite grid | exact replay plus checked QF_LRA/Farkas bad-sample row |
| Alternating residual | residual signs `+,-,+` with common magnitude `1/2` | exact replay plus checked QF_LRA/Farkas bad-uniform-error row |

The finite Chebyshev-system pack also records the theorem boundary row:

```text
general-chebyshev-system-lean-horizon
```

That row has `expected_result = not-run` and `proof_status = lean-horizon`.
It is not evidence for a theorem; it is a warning label and a future work item.

## Why The Finite Rows Matter

The finite rows give concrete, checkable shadows of approximation-theory
objects:

```text
points = -1, 0, 1
basis = 1, x, x^2
det(evaluation_matrix) = 2
```

They also catch malformed claims:

```text
duplicate-node determinant: actual 0, claimed 1
interpolation sample: actual p(1)=4, claimed 5
alternating residual: actual error 1/2, claimed 2/3
```

For each malformed row, the finite replay exposes the computed value and the
separate `qf-lra-*` row checks the final exact-rational contradiction with
Farkas evidence.

## What Is Not Proved Yet

The current resources do not prove:

- every finite-dimensional Chebyshev-space theorem;
- Haar-space equivalences;
- existence or uniqueness of best uniform approximations;
- the minimax alternation theorem;
- compactness arguments over function spaces;
- infinite-dimensional approximation theory;
- numerical stability or floating-point conditioning of interpolation.

Those claims quantify over function spaces, norms, approximation sets, or
compactness/completeness arguments. They are outside finite SMT replay unless a
future Lean artifact states and proves the theorem with no `sorry`.

## Graduation Route

A Chebyshev theorem should graduate only after these artifacts exist:

1. A precise Lean statement for the theorem shape, including hypotheses.
2. Links from each finite shadow pack to the theorem statement as examples,
   not proof evidence.
3. A no-`sorry` Lean proof or a kernel-checked proof object with an axiom audit.
4. A consumer label that keeps theorem evidence separate from finite replay,
   QF_LRA/Farkas certificates, and benchmark claims.

Until then, the right label is:

```text
finite checked shadow + Lean/theorem horizon
```

## Query It

From the repository root:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier --text Chebyshev --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-chebyshev-systems-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-chebyshev-systems-v0 --route Farkas --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-operator-v0 --route Farkas --proof-status checked --text qf-lra-bad-chebyshev-t3 --require-any
```

## Trust Boundary

```text
untrusted fast search -> grid, polynomial, residual, recurrence, or theorem-shaped claim
trusted small checking -> exact rational finite replay plus checked QF_LRA/Farkas conflicts
remaining horizon -> Haar, minimax, alternation, compactness, and function-space theorems
```

For the executable finite rows, read
[Finite Chebyshev Systems](finite-chebyshev-systems-end-to-end.md). For the
cross-pack finite operator map, read
[Chebyshev And Operator Replay Index](chebyshev-operator-index.md).
