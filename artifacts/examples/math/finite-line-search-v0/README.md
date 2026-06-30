# Finite Line Search Checks

This pack turns one exact rational Armijo backtracking line-search step into
resource rows. It checks only the listed quadratic, descent direction,
rejected trial step, accepted backtracked step, and false-Armijo obstruction;
general line-search convergence and optimization-algorithm theorems remain
proof horizons.

## Audience

- Learners connecting calculus, numerical optimization, and exact inequalities.
- Resource authors who need a small line-search witness with explicit trust
  boundaries.
- Solver developers looking for exact-rational QF_LRA/Farkas rows after replay.

## Checks

- `descent-direction-replay`: recomputes the gradient and verifies the listed
  direction has negative directional derivative.
- `armijo-rejection-replay`: checks that trial step `1` violates the Armijo
  decrease inequality.
- `armijo-acceptance-replay`: checks that one backtrack to step `1/2`
  satisfies the Armijo inequality with exact slack.
- `bad-armijo-acceptance-rejected`: rejects the malformed claim that the
  rejected trial step satisfies Armijo.
- `general-line-search-convergence-lean-horizon`: names the future proof route
  for line-search termination, descent lemmas, and convergence rates.

## Run

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-line-search-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_line_search_bad_armijo_artifact_emits_checked_farkas
```

## Trust Boundary

Untrusted search may propose a direction, step size, or Armijo certificate. The
trusted work is small: exact derivative replay, exact candidate-point
arithmetic, exact objective evaluation, Armijo inequality replay, and checked
`UnsatFarkas` evidence over the source SMT-LIB row.
