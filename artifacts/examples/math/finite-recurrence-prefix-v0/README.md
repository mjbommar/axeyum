# Finite Recurrence Prefix Checks

This pack turns recurrence examples from the math curriculum into exact finite
resource rows. It checks only listed prefixes and matrix steps; closed forms,
asymptotics, convergence, and induction over all `n` remain proof-assistant
horizons.

## Audience

- Learners moving from sequences and counting into linear algebra.
- Resource authors who need a small recurrence example with a checked bad row.
- Solver developers looking for exact-rational replay rows that can become
  QF_LRA/Farkas regressions.

## Checks

- `fibonacci-prefix-replay`: recomputes `F_0..F_6` from
  `F_n = F_{n-1} + F_{n-2}`.
- `affine-recurrence-prefix-replay`: recomputes a finite prefix of
  `x_{n+1} = 2*x_n + 1`.
- `companion-matrix-prefix-replay`: checks the Fibonacci companion matrix on
  fixed two-dimensional state vectors.
- `bad-fibonacci-value-rejected`: rejects the malformed claim `F_6 = 9` after
  replay computes `F_6 = 8`, with checked QF_LRA/Farkas evidence.
- `general-recurrence-theory-lean-horizon`: names the future Lean route for
  induction, closed forms, asymptotics, and stability/convergence theorems.

## Run

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-recurrence-prefix-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_recurrence_prefix_bad_value_artifact_emits_checked_farkas
```

## Trust Boundary

Untrusted search may propose a prefix, matrix trace, or contradiction route.
The trusted work is small: exact recurrence replay, exact matrix-vector
multiplication, and checked `UnsatFarkas` evidence over the source SMT-LIB row.
