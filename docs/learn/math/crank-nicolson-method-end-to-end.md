# End To End: Finite Crank-Nicolson Method

This lesson follows one exact finite Crank-Nicolson resource from implicit
trapezoid replay to checked Farkas evidence:
[finite-crank-nicolson-method-v0](../../../artifacts/examples/math/finite-crank-nicolson-method-v0/).

The point is small and deliberate:

```text
untrusted fast search -> trace, implicit solve, decay row, or Farkas certificate
trusted small checking -> exact rational replay plus checked QF_LRA evidence
```

## Resource Row

The pack is anchored in:

- `field_differential_equations_and_dynamical_systems`
- `field_numerical_analysis`
- `field_real_analysis`
- `curriculum_calculus`
- `bridge_finite_dynamics_euler_replay`
- `bridge_bounded_family_asymptotic_boundary`

It has five rows:

| Row | Result | Status |
|---|---|---|
| `crank-nicolson-implicit-trapezoid-witness` | `sat` | replay-only |
| `crank-nicolson-geometric-decay-witness` | `sat` | replay-only |
| `bad-crank-nicolson-step-rejected` | `unsat` | replay-only |
| `qf-lra-bad-crank-nicolson-step` | `unsat` | checked QF_LRA/Farkas |
| `general-crank-nicolson-theory-lean-horizon` | `not-run` | Lean horizon |

## Finite Claim

Every row is finite and exact-rational. The pack treats Crank-Nicolson as a
fixed transition relation on this ODE:

```text
y' = -y
y(0) = 1
h = 1/2
```

Crank-Nicolson is checked as:

```text
y_(n+1) = y_n + h * (f(t_n, y_n) + f(t_(n+1), y_(n+1))) / 2
```

For `f(t,y) = -y` and `h = 1/2`:

```text
y_(n+1) = y_n - (1/4)*y_n - (1/4)*y_(n+1)
(5/4)*y_(n+1) = (3/4)*y_n
y_(n+1) = (3/5)*y_n
```

The listed trace is:

```text
times  = 0, 1/2, 1, 3/2
states = 1, 3/5, 9/25, 27/125
```

The validator recomputes each start derivative, endpoint derivative, averaged
slope, and residual:

```text
n=0: start=-1,    endpoint=-3/5,   avg=-4/5,   residual=0
n=1: start=-3/5, endpoint=-9/25,  avg=-12/25, residual=0
n=2: start=-9/25,endpoint=-27/125,avg=-36/125,residual=0
```

The decay row checks only the finite trace:

```text
state_(n+1) = (3/5) * state_n
0 <= state_n <= 1
state_(n+1) < state_n
```

That is not a stability theorem. It is just exact replay of this trace.

## Bad Source Row

The malformed source row says:

```text
For y' = -y, h = 1/2, t = 0, y = 1,
the first Crank-Nicolson step gives 1/2.
```

Exact replay computes:

```text
start_derivative = -1
endpoint_derivative = -3/5
averaged_derivative = -4/5
next_state = 1 + (1/2)*(-4/5) = 3/5
```

So the replay-only row rejects the malformed claim and records the gap:

```text
3/5 - 1/2 = 1/10
```

## Checked Farkas Row

The separate `qf-lra-bad-crank-nicolson-step` row owns the proof-object
refutation. Its source artifact is:

[`bad-crank-nicolson-step-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-crank-nicolson-method-v0/smt2/bad-crank-nicolson-step-farkas-conflict.smt2)

The artifact isolates this scalar contradiction:

```text
crank_nicolson_next_state = 3/5
crank_nicolson_next_state = 1/2
```

The route test parses that SMT-LIB file, emits `UnsatFarkas` evidence, and
independently checks the certificate. The source trace is still checked by the
pack validator; the Farkas row is only the compact arithmetic contradiction.

## Theorem Horizon

The finite resource does not prove:

- Crank-Nicolson order or convergence;
- A-stability or stiffness behavior;
- nonlinear endpoint solve correctness;
- adaptive time-stepping correctness;
- floating-point implementation correctness;
- PDE time-integration theory.

Those require future Lean theorem statements or numerical-honesty artifacts.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-crank-nicolson-method-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_crank_nicolson_bad_step_artifact_emits_checked_farkas
```

To find the row through the public query surface:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-crank-nicolson-method-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-crank-nicolson-step \
  --require-any
```

## Trust Boundary

The split is:

```text
untrusted fast search -> Crank-Nicolson trace, implicit solve, decay row, or Farkas certificate
trusted small checking -> exact rational replay and checked QF_LRA/Farkas evidence
```

This is the same pattern used by
[End To End: Finite Dynamics And Euler Replay](finite-dynamics-euler-end-to-end.md),
[End To End: Finite Euler Method](finite-euler-method-end-to-end.md),
[End To End: Finite Runge-Kutta Midpoint](runge-kutta-midpoint-end-to-end.md),
[End To End: Finite Heun Method](heun-method-end-to-end.md), and
[End To End: Finite Backward Euler Method](backward-euler-method-end-to-end.md).
