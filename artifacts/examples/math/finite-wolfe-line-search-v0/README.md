# Finite Wolfe Line-Search Checks

This pack turns one exact rational Wolfe line-search check into resource rows.
It checks only the listed quadratic, descent direction, exact one-dimensional
minimizer, Wolfe sufficient-decrease and curvature inequalities, and a false
curvature obstruction; general Wolfe line-search convergence and smooth
optimization theorems remain proof horizons.

## Audience

- Learners connecting calculus, line search, and exact inequality checking.
- Resource authors who need a Wolfe-condition witness with explicit trust
  boundaries.
- Solver developers looking for exact-rational QF_LRA/Farkas rows after replay.

## Checks

- `wolfe-descent-direction-replay`: recomputes the gradient and verifies the
  listed direction has negative directional derivative.
- `exact-line-minimizer-replay`: checks the exact one-dimensional minimizer and
  zero directional derivative at the accepted step.
- `wolfe-sufficient-decrease-replay`: checks the Armijo/Wolfe sufficient
  decrease inequality at the accepted step.
- `wolfe-curvature-replay`: checks the Wolfe curvature inequality at the
  accepted step.
- `bad-wolfe-curvature-rejected`: rejects the malformed claim that the full
  step satisfies the Wolfe curvature bound.
- `general-wolfe-line-search-lean-horizon`: names the future proof route for
  Wolfe existence, convergence, and rate theorems.

## Run

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-wolfe-line-search-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_wolfe_line_search_bad_curvature_artifact_emits_checked_farkas
```

## Trust Boundary

Untrusted search may propose a step size or Wolfe certificate. The trusted work
is small: exact derivative replay, exact candidate arithmetic, exact objective
evaluation, exact Wolfe inequality replay, and checked `UnsatFarkas` evidence
over the source SMT-LIB row.
