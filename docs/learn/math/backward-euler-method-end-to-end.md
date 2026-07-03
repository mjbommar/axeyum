# End To End: Finite Backward Euler Method

This lesson follows one exact finite backward Euler resource from implicit
endpoint-state replay to a checked bad first-step rejection. It uses the
[finite-backward-euler-method-v0](../../../artifacts/examples/math/finite-backward-euler-method-v0/)
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
| `backward-euler-implicit-solve-witness` | `sat` | replay-only |
| `backward-euler-geometric-decay-witness` | `sat` | replay-only |
| `bad-backward-euler-step-rejected` | `unsat` | replay-only |
| `qf-lra-bad-backward-euler-step` | `unsat` | checked QF_LRA/Farkas |
| `general-backward-euler-theory-lean-horizon` | `not-run` | Lean horizon |

The pack fixes:

```text
y' = -y
y(0) = 1
h = 1/2
```

Every row is finite and exact-rational. The pack treats backward Euler as a
bounded implicit transition relation. It does not prove general convergence,
A-stability, stiff-system behavior, nonlinear solve correctness, adaptive-step
correctness, floating-point correctness, or PDE theory.

## Replay The Implicit Step

Backward Euler is checked as:

```text
y_(n+1) = y_n + h * f(t_(n+1), y_(n+1))
```

For `f(t, y) = -y` and `h = 1/2`, the endpoint state appears on both sides:

```text
y_(n+1) = y_n - (1/2)*y_(n+1)
(3/2)*y_(n+1) = y_n
y_(n+1) = (2/3)*y_n
```

The validator checks the listed finite trace:

```text
times  = 0, 1/2, 1, 3/2
states = 1, 2/3, 4/9, 8/27
```

and recomputes each endpoint derivative and residual:

```text
n=0: endpoint=1/2, derivative=-2/3, residual=0
n=1: endpoint=1,   derivative=-4/9, residual=0
n=2: endpoint=3/2, derivative=-8/27, residual=0
```

This is replay-only: a proposed implicit solve is untrusted until each exact
rational equation is recomputed.

## Replay The Decay Table

The same trace follows a finite geometric ratio:

```text
state       1    2/3   4/9   8/27
ratio            2/3   2/3   2/3
bounds      0 <= state <= 1
```

The validator checks positivity, monotone decrease, the listed lower and upper
bounds, and the exact ratio. This is a finite trace property, not a stability
or convergence theorem.

## Check The Bad First Step

The negative row claims:

```text
next_state = 1/2
```

for the first step from `t=0`, `y=1`. Exact replay computes:

```text
next_state = 2/3
```

That replay-only row rejects the malformed update. The separate
`qf-lra-bad-backward-euler-step` row owns the proof-object refutation.

The committed SMT-LIB artifact
[`bad-backward-euler-step-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-backward-euler-method-v0/smt2/bad-backward-euler-step-farkas-conflict.smt2)
isolates the scalar contradiction:

```text
backward_euler_next_state = 2/3
backward_euler_next_state = 1/2
```

The solver search and emitted certificate are not trusted. The accepted
evidence is the independently checked `UnsatFarkas` certificate produced from
the source assertions.

## Name The Horizon

This pack does not claim:

```text
general backward Euler convergence
A-stability or stability-region theorems
stiff-system behavior
nonlinear endpoint-solve correctness
adaptive step-size controller correctness
floating-point time-stepping correctness
PDE time-integration theory
```

Those require Lean theorem statements, proof-producing numerical certificates,
or separate numerical-honesty artifacts.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-backward-euler-method-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_backward_euler_bad_step_artifact_emits_checked_farkas
```

Expected validator output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> backward Euler trace, implicit solve, decay row, or Farkas certificate
trusted small checking -> exact implicit replay, exact finite ratio arithmetic, and exact Farkas arithmetic
remaining horizon -> convergence, A-stability, stiffness, nonlinear solves, adaptivity, floating point, and PDEs
```

For the combined recurrence/time-stepping bridge, read
[End To End: Finite Dynamics And Euler Replay](finite-dynamics-euler-end-to-end.md).
For explicit time-stepping slices, read
[End To End: Finite Euler Method](finite-euler-method-end-to-end.md),
[End To End: Finite Runge-Kutta Midpoint](runge-kutta-midpoint-end-to-end.md),
and [End To End: Finite Heun Method](heun-method-end-to-end.md).
For the implicit trapezoid slice, read
[End To End: Finite Crank-Nicolson Method](crank-nicolson-method-end-to-end.md).
