# Finite Runge-Kutta Midpoint Checks

This pack records one exact rational RK2 midpoint transcript for the fixed ODE
`y' = 2t`, `y(0) = 0`, with step `h = 1/2`. It is a small time-stepping
resource for differential equations, numerical analysis, and real analysis:
replay midpoint stages, replay the finite trace, compute a finite error table,
and reject one malformed first-step claim with checked QF_LRA/Farkas evidence.

For this ODE, the exact solution is:

```text
y(t) = t^2
```

The explicit midpoint method is:

```text
k1 = f(t_n, y_n)
t_mid = t_n + h/2
y_mid = y_n + (h/2)*k1
k2 = f(t_mid, y_mid)
y_(n+1) = y_n + h*k2
```

The pack fixes:

```text
h = 1/2
times  = [0, 1/2, 1, 3/2]
states = [0, 1/4, 1, 9/4]
```

The checked bad row rejects the claim that the first next state is `1/2`.
Exact replay computes:

```text
k1 = 0
t_mid = 1/4
y_mid = 0
k2 = 1/2
next_state = 0 + (1/2)*(1/2) = 1/4
```

The QF_LRA artifact isolates only the scalar contradiction:

```text
rk_next_state = 1/4
rk_next_state = 1/2
```

## Concept Rows

- `curriculum_calculus`
- `curriculum_sequences_and_limits`
- `curriculum_reals`
- `field_differential_equations_and_dynamical_systems`
- `field_numerical_analysis`
- `field_real_analysis`
- `bridge_finite_dynamics_euler_replay`
- `bridge_bounded_family_asymptotic_boundary`

## Trust Boundary

```text
untrusted fast search -> candidate RK stages, trace, and error table
trusted small checking -> exact rational stage replay, finite error arithmetic, and checked Farkas evidence
theorem horizon       -> Runge-Kutta order, convergence, stability, stiffness, adaptivity, and floating-point correctness
```

The pack validates with:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-runge-kutta-midpoint-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_runge_kutta_midpoint_bad_step_artifact_emits_checked_farkas
```

Learner walkthrough:
[End To End: Finite Runge-Kutta Midpoint](../../../docs/learn/math/runge-kutta-midpoint-end-to-end.md).
