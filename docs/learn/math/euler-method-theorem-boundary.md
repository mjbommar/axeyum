# Euler Method Theorem Boundary

This page separates the finite Euler-method resources Axeyum can check today
from the continuous ODE, numerical-analysis, and floating-point theorems that
still need a kernel-checked theorem or numerical-honesty route. It is a
boundary map, not a new proof route.

Primary pack:

- [finite-euler-method-v0](../../../artifacts/examples/math/finite-euler-method-v0/)

Related finite time-stepping packs:

- [finite-runge-kutta-midpoint-v0](../../../artifacts/examples/math/finite-runge-kutta-midpoint-v0/)
- [finite-heun-method-v0](../../../artifacts/examples/math/finite-heun-method-v0/)
- [finite-backward-euler-method-v0](../../../artifacts/examples/math/finite-backward-euler-method-v0/)
- [finite-crank-nicolson-method-v0](../../../artifacts/examples/math/finite-crank-nicolson-method-v0/)
- [finite-adams-bashforth-method-v0](../../../artifacts/examples/math/finite-adams-bashforth-method-v0/)
- [finite-bdf2-method-v0](../../../artifacts/examples/math/finite-bdf2-method-v0/)

Concept rows:

- `bridge_finite_dynamics_euler_replay`
- `bridge_bounded_family_asymptotic_boundary`
- `field_differential_equations_and_dynamical_systems`
- `field_numerical_analysis`
- `field_real_analysis`

## What Is Checked Today

The current Euler resource is an exact finite rational check over listed time
grids, states, derivatives, and error values:

| Resource | Checked finite shadow | Trusted route |
|---|---|---|
| Decay trace | `y'=-y`, `h=1/2`, states `1,1/2,1/4,1/8` | exact replay |
| Quadratic-forcing error table | `y'=2t`, exact solution `y=t^2`, max error `3/4` on four grid points | exact replay |
| Finite invariant | listed decay states stay in `[0,1]` and are nonincreasing | exact replay |
| Bad max-error bound | replay computes `max_error=3/4` while the claim says `<= 1/2` | exact replay plus checked QF_LRA/Farkas row |
| Bad terminal error | replay computes terminal error `3/4` while the claim says `1/2` | exact replay plus checked QF_LRA/Farkas row |
| Bad Euler step | replay computes `next_state=1/2` while the claim says `3/4` | exact replay plus checked QF_LRA/Farkas row |

The pack also records the theorem boundary row:

```text
general-ode-theory-lean-horizon
```

That row has `expected_result = not-run` and
`proof_status = lean-horizon`. It is not evidence for ODE theory; it is a
warning label and a future work item.

## Why The Finite Rows Matter

The finite rows make explicit Euler a small transition system:

```text
y_(n+1) = y_n + h * f(t_n, y_n)
t_(n+1) = t_n + h
```

For `y'=-y`, `h=1/2`, and `y_0=1`, the checker recomputes:

```text
1   + (1/2)*(-1)   = 1/2
1/2 + (1/2)*(-1/2) = 1/4
1/4 + (1/2)*(-1/4) = 1/8
```

For `y'=2t`, it separately checks the listed exact solution values,
pointwise absolute errors, terminal error, and maximum error. Malformed rows
are split into two obligations:

```text
source table replay -> exact finite step or error value
proof-object row    -> checked QF_LRA/Farkas contradiction
```

That split keeps the numerical table, the solver proof, and the theorem
boundary auditable independently.

## What Is Not Proved Yet

The current resources do not prove:

- ODE existence, uniqueness, continuation, or flow theorems;
- convergence of explicit Euler as `h -> 0`;
- local or global truncation-error theorems;
- stability regions, stiffness behavior, or invariant-preservation theorems;
- adaptive-step, implicit-method, Runge-Kutta, Crank-Nicolson,
  Adams-Bashforth, BDF2, or multistep-method theory;
- PDE theory or continuous-time dynamical-systems theory;
- floating-point roundoff, conditioning, or solver-library behavior.

Those claims quantify over solution families, limits, differentiability and
Lipschitz hypotheses, stability regions, or implementation-level numeric
behavior. They are outside finite SMT replay unless a future Lean artifact or
numerical-honesty artifact states and checks the relevant theorem or error
model.

## Graduation Route

An Euler or ODE theorem should graduate only after these artifacts exist:

1. A precise Lean statement for the theorem shape, including hypotheses on the
   vector field, step-size regime, norm, and interval of existence.
2. Links from finite Euler packs to the theorem statement as examples, not
   proof evidence.
3. A no-`sorry` Lean proof or a kernel-checked proof object with an axiom audit.
4. For floating-point claims, explicit numerical-honesty metadata covering
   rounding model, precision, implementation, and reproducible error checks.
5. A consumer label that keeps theorem evidence separate from finite replay,
   QF_LRA/Farkas certificates, solver-performance claims, and benchmark claims.

Until then, the right label is:

```text
finite checked shadow + Lean/theorem horizon
```

## Query It

From the repository root:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier --text ODE --require-any
python3 scripts/query-foundational-resources.py horizon-frontier --field differential_equations_and_dynamical_systems --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-euler-method-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-euler-method-v0 --route Farkas --proof-status checked --require-any
```

## Trust Boundary

```text
untrusted fast search -> Euler trace, finite error table, invariant, or theorem-shaped claim
trusted small checking -> exact rational transition/error replay plus checked QF_LRA/Farkas conflicts
remaining horizon -> continuous ODE theory, convergence, stability, stiffness, floating point, and PDEs
```

For the executable finite rows, read
[End To End: Finite Euler Method](finite-euler-method-end-to-end.md). For the
combined recurrence/Euler bridge, read
[End To End: Finite Dynamics And Euler Replay](finite-dynamics-euler-end-to-end.md).
