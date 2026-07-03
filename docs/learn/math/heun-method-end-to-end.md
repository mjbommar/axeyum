# End To End: Finite Heun Method

This lesson follows one exact finite Heun-method resource from predictor-stage
replay to a finite zero-error table and a checked bad first-step rejection. It
uses the
[finite-heun-method-v0](../../../artifacts/examples/math/finite-heun-method-v0/)
pack.

Concept rows:

- `field_differential_equations_and_dynamical_systems`,
  `field_numerical_analysis`, and `field_real_analysis` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `curriculum_calculus`, `curriculum_sequences_and_limits`, and
  `curriculum_reals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `bridge_finite_dynamics_euler_replay` and
  `bridge_bounded_family_asymptotic_boundary` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `heun-stage-witness` | `sat` | replay-only |
| `heun-trace-exact-solution-witness` | `sat` | replay-only |
| `zero-error-table-witness` | `sat` | replay-only |
| `bad-heun-step-rejected` | `unsat` | replay-only |
| `qf-lra-bad-heun-step` | `unsat` | checked QF_LRA/Farkas |
| `general-heun-rk2-theory-lean-horizon` | `not-run` | Lean horizon |

The pack fixes:

```text
y' = 2t
y(0) = 0
h = 1/2
```

The exact solution is:

```text
y(t) = t^2
```

Every row is finite and exact-rational. The pack treats Heun's method as a
bounded transition relation. It does not prove Runge-Kutta order conditions,
global convergence, stability regions, stiffness behavior, adaptive-step
correctness, floating-point correctness, or PDE theory.

## Replay The Heun Stages

Heun's method, also called the explicit trapezoidal RK2 method, is checked as:

```text
k1 = f(t_n, y_n)
y_predict = y_n + h*k1
k2 = f(t_n + h, y_predict)
avg = (k1 + k2) / 2
y_(n+1) = y_n + h*avg
```

For the fixed trace, the validator checks:

```text
times  = 0, 1/2, 1, 3/2
states = 0, 1/4, 1, 9/4
```

The stage table is:

```text
n=0: k1=0, predictor=0,   endpoint=1/2, k2=1, avg=1/2, next=1/4
n=1: k1=1, predictor=3/4, endpoint=1,   k2=2, avg=3/2, next=1
n=2: k1=2, predictor=2,   endpoint=3/2, k2=3, avg=5/2, next=9/4
```

This is replay-only: a proposed stage table is untrusted until each exact
rational update is recomputed.

## Replay The Finite Error Table

On this fixed ODE and grid, the Heun trace lands exactly on `t^2`:

```text
t        0    1/2   1    3/2
state    0    1/4   1    9/4
exact    0    1/4   1    9/4
error    0    0     0    0
```

The validator checks the exact solution values, absolute errors, and
`max_error = 0`. This is a finite error table, not a convergence-rate theorem.

## Check The Bad First Step

The negative row claims:

```text
next_state = 1/2
```

for the first step from `t=0`, `y=0`. Exact replay computes:

```text
k1 = 0
y_predict = 0
k2 = 1
avg = 1/2
next_state = 0 + (1/2)*(1/2) = 1/4
```

That replay-only row rejects the malformed update. The separate
`qf-lra-bad-heun-step` row owns the proof-object refutation.

The committed SMT-LIB artifact
[`bad-heun-step-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-heun-method-v0/smt2/bad-heun-step-farkas-conflict.smt2)
isolates the scalar contradiction:

```text
heun_next_state = 1/4
heun_next_state = 1/2
```

The solver search and emitted certificate are not trusted. The accepted
evidence is the independently checked `UnsatFarkas` certificate produced from
the source assertions.

## Name The Horizon

This pack does not claim:

```text
general Runge-Kutta order conditions
local or global error bounds
stability regions or A-stability
stiff-system behavior
adaptive step-size controller correctness
floating-point time-stepping correctness
PDE time-integration theory
```

Those require Lean theorem statements, proof-producing numerical certificates,
or separate numerical-honesty artifacts.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-heun-method-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_heun_bad_step_artifact_emits_checked_farkas
```

Expected validator output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> Heun stages, trace, finite error table, or Farkas certificate
trusted small checking -> exact stage replay, exact finite error arithmetic, and exact Farkas arithmetic
remaining horizon -> RK order, convergence, stability, stiffness, adaptivity, floating point, and PDEs
```

For the explicit midpoint slice, read
[End To End: Finite Runge-Kutta Midpoint](runge-kutta-midpoint-end-to-end.md).
For the combined recurrence/time-stepping bridge, read
[End To End: Finite Dynamics And Euler Replay](finite-dynamics-euler-end-to-end.md).
