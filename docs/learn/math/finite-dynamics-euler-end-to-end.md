# End To End: Finite Dynamics And Euler Replay

This lesson follows exact finite dynamics resources from recurrence data to
checked transition replay. It uses
[bounded-dynamics-v0](../../../artifacts/examples/math/bounded-dynamics-v0/) and
[finite-euler-method-v0](../../../artifacts/examples/math/finite-euler-method-v0/),
[finite-runge-kutta-midpoint-v0](../../../artifacts/examples/math/finite-runge-kutta-midpoint-v0/),
[finite-heun-method-v0](../../../artifacts/examples/math/finite-heun-method-v0/),
and
[finite-backward-euler-method-v0](../../../artifacts/examples/math/finite-backward-euler-method-v0/)
and
[finite-crank-nicolson-method-v0](../../../artifacts/examples/math/finite-crank-nicolson-method-v0/), and
[finite-adams-bashforth-method-v0](../../../artifacts/examples/math/finite-adams-bashforth-method-v0/).
For the bounded recurrence and invariant slice alone, read
[End To End: Bounded Recurrence Dynamics](bounded-dynamics-end-to-end.md).
For the explicit Euler and finite error-table slice alone, read
[End To End: Finite Euler Method](finite-euler-method-end-to-end.md).
For the explicit midpoint Runge-Kutta slice alone, read
[End To End: Finite Runge-Kutta Midpoint](runge-kutta-midpoint-end-to-end.md).
For the explicit trapezoidal Heun slice alone, read
[End To End: Finite Heun Method](heun-method-end-to-end.md).
For the implicit backward Euler slice alone, read
[End To End: Finite Backward Euler Method](backward-euler-method-end-to-end.md).
For the implicit Crank-Nicolson slice alone, read
[End To End: Finite Crank-Nicolson Method](crank-nicolson-method-end-to-end.md).
For the explicit Adams-Bashforth multistep slice alone, read
[End To End: Finite Adams-Bashforth Method](adams-bashforth-method-end-to-end.md).

Concept rows:

- `curriculum_calculus`, `curriculum_sequences_and_limits`,
  `curriculum_linear_algebra`, and `curriculum_reals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_differential_equations_and_dynamical_systems`,
  `field_numerical_analysis`, `field_real_analysis`, and
  `field_linear_algebra` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `bridge_finite_dynamics_euler_replay` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `linear-recurrence-trace` | `sat` | replay-only |
| `bounded-invariant-witness` | `sat` | replay-only |
| `unsafe-threshold-reachable` | `sat` | replay-only |
| `bad-transition-step-rejected` | `unsat` | replay-only |
| `qf-lra-bad-transition-step` | `unsat` | checked |
| `bad-threshold-step-rejected` | `unsat` | replay-only |
| `qf-lra-bad-threshold-step` | `unsat` | checked |
| `bad-invariant-bound-rejected` | `unsat` | replay-only |
| `qf-lra-bad-invariant-bound` | `unsat` | checked |
| `linear-decay-euler-trace` | `sat` | replay-only |
| `quadratic-forcing-error-replay` | `sat` | replay-only |
| `bad-max-error-bound-rejected` | `unsat` | replay-only |
| `qf-lra-bad-max-error-bound` | `unsat` | checked |
| `bad-terminal-error-rejected` | `unsat` | replay-only |
| `qf-lra-bad-terminal-error` | `unsat` | checked |
| `nonnegative-monotone-invariant` | `sat` | replay-only |
| `bad-euler-step-rejected` | `unsat` | replay-only |
| `qf-lra-bad-euler-step` | `unsat` | checked |
| `midpoint-stage-witness` | `sat` | replay-only |
| `midpoint-trace-exact-solution-witness` | `sat` | replay-only |
| `zero-error-table-witness` | `sat` | replay-only |
| `bad-rk-midpoint-step-rejected` | `unsat` | replay-only |
| `qf-lra-bad-rk-midpoint-step` | `unsat` | checked |
| `general-runge-kutta-theory-lean-horizon` | `not-run` | lean-horizon |
| `heun-stage-witness` | `sat` | replay-only |
| `heun-trace-exact-solution-witness` | `sat` | replay-only |
| `bad-heun-step-rejected` | `unsat` | replay-only |
| `qf-lra-bad-heun-step` | `unsat` | checked |
| `general-heun-rk2-theory-lean-horizon` | `not-run` | lean-horizon |
| `backward-euler-implicit-solve-witness` | `sat` | replay-only |
| `backward-euler-geometric-decay-witness` | `sat` | replay-only |
| `bad-backward-euler-step-rejected` | `unsat` | replay-only |
| `qf-lra-bad-backward-euler-step` | `unsat` | checked |
| `general-backward-euler-theory-lean-horizon` | `not-run` | lean-horizon |
| `crank-nicolson-implicit-trapezoid-witness` | `sat` | replay-only |
| `crank-nicolson-geometric-decay-witness` | `sat` | replay-only |
| `bad-crank-nicolson-step-rejected` | `unsat` | replay-only |
| `qf-lra-bad-crank-nicolson-step` | `unsat` | checked |
| `general-crank-nicolson-theory-lean-horizon` | `not-run` | lean-horizon |
| `adams-bashforth-history-witness` | `sat` | replay-only |
| `adams-bashforth-zero-error-witness` | `sat` | replay-only |
| `bad-adams-bashforth-step-rejected` | `unsat` | replay-only |
| `qf-lra-bad-adams-bashforth-step` | `unsat` | checked |
| `general-adams-bashforth-theory-lean-horizon` | `not-run` | lean-horizon |
| `general-ode-theory-lean-horizon` | `not-run` | lean-horizon |

These rows are finite transition-system checks over exact rationals. They do
not claim continuous-time existence, uniqueness, stability, convergence rates,
stiffness behavior, chaos, or PDE theory.
The shared `bridge_finite_dynamics_euler_replay` row is the atlas vocabulary
for this pattern across recurrence prefixes, bounded dynamics, finite
invariants, threshold reachability, explicit Euler steps, Runge-Kutta midpoint
stages, Heun predictor stages, backward Euler implicit solves,
Crank-Nicolson averaged-slope solves, Adams-Bashforth derivative-history
updates, and finite error tables.

## Replay A Bounded Recurrence

The first dynamics row fixes a recurrence, initial state, and finite trace:

```text
x(0) = 0
x(t+1) = x(t) + 2
steps = 4
trace = 0, 2, 4, 6, 8
```

The validator checks the initial state, horizon length, and every adjacent
transition:

```text
0 + 2 = 2
2 + 2 = 4
4 + 2 = 6
6 + 2 = 8
```

The invariant row uses the same trace and checks the closed interval
constraint at every listed state:

```text
0 <= x(t) <= 8
```

This is the finite, explicit version of an invariant proof. The future
graduation route is to encode the same shape as a bounded model-checking
obligation and replay the returned model against the original recurrence.

The first negative row uses the same trace but claims the transition after
state `2` lands at `5`. Exact replay computes `2 + 2 = 4`; the separate
`qf-lra-bad-transition-step` row checks the bad transition as `QF_LRA`:

```text
previous_state = 2
delta = 2
next_state = previous_state + delta
next_state = 5
```

The invariant negative row uses the same trace but claims:

```text
x(t) <= 6
```

Exact replay computes the final and maximum state as `8`. The separate
`qf-lra-bad-invariant-bound` row checks the bad invariant as `QF_LRA`:

```text
terminal_state = 8
terminal_state <= 6
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass the independent
certificate check.

## Replay Threshold Reachability

The reachability witness uses a different fixed recurrence:

```text
x(0) = 0
x(t+1) = x(t) + 3
steps = 3
trace = 0, 3, 6, 9
threshold = 7
first_reaching_step = 3
```

The checker replays the trace and confirms that step `3` is the first listed
state satisfying:

```text
x(t) >= 7
```

This is a bounded safety or bug-finding pattern: a candidate trace is
untrusted, and the small checker confirms that the trace really reaches the
target.

The threshold negative row claims step `2` already reaches threshold `7`.
Exact replay computes `x(2) = 6`, so the separate
`qf-lra-bad-threshold-step` row isolates the source QF_LRA contradiction
`state_at_claimed_step = 6`, `threshold = 7`, and
`state_at_claimed_step >= threshold`.

## Encode Explicit Euler As A Transition System

The Euler pack treats a numerical stepper as a rational transition relation:

```text
y_(n+1) = y_n + h * f(t_n, y_n)
```

For the linear decay equation:

```text
y' = -y
h = 1/2
times = 0, 1/2, 1, 3/2
states = 1, 1/2, 1/4, 1/8
derivatives = -1, -1/2, -1/4
```

the validator recomputes each update exactly:

```text
1 + (1/2)*(-1) = 1/2
1/2 + (1/2)*(-1/2) = 1/4
1/4 + (1/2)*(-1/4) = 1/8
```

The invariant row checks the same finite Euler trace stays inside `[0,1]` and
is monotone nonincreasing.

## Replay A Finite Error Table

For the equation:

```text
y' = 2t
y(0) = 0
exact solution y = t^2
h = 1/2
```

the pack lists the Euler states:

```text
states = 0, 0, 1/2, 3/2
exact = 0, 1/4, 1, 9/4
errors = 0, 1/4, 1/2, 3/4
max_error = 3/4
```

The validator checks the Euler updates, evaluates `t^2` at each listed time,
computes absolute errors, and confirms the maximum error. This is finite error
replay, not a convergence-rate theorem.

The bad error-bound row reuses that exact table but claims:

```text
max_error <= 1/2
```

Exact replay computes `max_error = 3/4`, so the replay row rejects the
malformed bound by exact arithmetic. The separate `qf-lra-bad-max-error-bound`
row checks the isolated contradictory inequality through Farkas evidence.

The bad terminal-error row focuses on the last point in the same table:

```text
|9/4 - 3/2| = 3/4
```

and rejects the malformed claim that this final error is `1/2` with a separate
replay row; the separate `qf-lra-bad-terminal-error` row owns the source
QF_LRA/Farkas artifact.

## Reject A Bad Euler Step

The replay-only negative row claims:

```text
For y' = -y, h = 1/2, y = 1, the next value is 3/4.
```

The checker recomputes:

```text
1 + (1/2)*(-1) = 1/2
```

The resource regression checks the bad step as `QF_LRA`:

```text
state = 1
derivative = -1
next_state = state + (1/2)*derivative
next_state = 3/4
```

That `unsat` result must carry `Evidence::UnsatFarkas` and pass the independent
certificate check in the separate `qf-lra-bad-euler-step` row.

so the row is rejected. This is the most important teaching shape in the pack:
the same arithmetic that accepts a good step rejects a plausible but false
numerical update.

## Encode RK2 Midpoint As A Transition System

The Runge-Kutta midpoint pack treats a two-stage numerical method as another
rational transition relation:

```text
k1 = f(t_n, y_n)
t_mid = t_n + h/2
y_mid = y_n + (h/2)*k1
k2 = f(t_mid, y_mid)
y_(n+1) = y_n + h*k2
```

For `y' = 2t`, `y(0)=0`, and `h=1/2`, the finite midpoint trace is:

```text
states = 0, 1/4, 1, 9/4
exact  = 0, 1/4, 1, 9/4
errors = 0, 0, 0, 0
```

The bad midpoint row claims the first next state is `1/2`; exact replay
computes `1/4`, and the separate `qf-lra-bad-rk-midpoint-step` row isolates
that contradiction through checked Farkas evidence.

## Encode Heun As A Transition System

The Heun pack treats the explicit trapezoidal RK2 method as a distinct
two-stage rational transition relation:

```text
k1 = f(t_n, y_n)
y_predict = y_n + h*k1
k2 = f(t_n + h, y_predict)
avg = (k1 + k2) / 2
y_(n+1) = y_n + h*avg
```

For the same `y' = 2t`, `y(0)=0`, and `h=1/2` grid, the finite Heun trace is:

```text
states = 0, 1/4, 1, 9/4
exact  = 0, 1/4, 1, 9/4
errors = 0, 0, 0, 0
```

The bad Heun row claims the first next state is `1/2`; exact replay computes
`1/4`, and the separate `qf-lra-bad-heun-step` row isolates that contradiction
through checked Farkas evidence.

## Encode Backward Euler As An Implicit Transition System

The Backward Euler pack treats an implicit one-step method as a rational
transition relation:

```text
y_(n+1) = y_n + h * f(t_(n+1), y_(n+1))
```

For `y' = -y`, `y(0)=1`, and `h=1/2`, the finite backward Euler trace is:

```text
states = 1, 2/3, 4/9, 8/27
ratio  =    2/3, 2/3, 2/3
```

The validator checks each endpoint derivative, confirms every implicit
residual is zero, and checks positivity plus monotone geometric decay. The bad
backward Euler row claims the first next state is `1/2`; exact replay computes
`2/3`, and the separate `qf-lra-bad-backward-euler-step` row isolates that
contradiction through checked Farkas evidence.

## Encode Crank-Nicolson As An Implicit Trapezoid System

The Crank-Nicolson pack treats the same ODE as an implicit trapezoid
transition relation:

```text
y_(n+1) = y_n + h * (f(t_n, y_n) + f(t_(n+1), y_(n+1))) / 2
```

For `y' = -y`, `y(0)=1`, and `h=1/2`, the finite Crank-Nicolson trace is:

```text
states = 1, 3/5, 9/25, 27/125
ratio  =    3/5, 3/5, 3/5
```

The validator checks each start derivative, endpoint derivative, averaged
slope, zero implicit residual, positivity, and monotone geometric decay. The
bad Crank-Nicolson row claims the first next state is `1/2`; exact replay
computes `3/5`, and the separate `qf-lra-bad-crank-nicolson-step` row isolates
that contradiction through checked Farkas evidence.

## Encode Adams-Bashforth As A Multistep History System

The Adams-Bashforth pack treats a stepper as a finite transition with one
stored derivative from the previous time point:

```text
y_(n+1) = y_n + h * ((3/2) * f(t_n, y_n) - (1/2) * f(t_(n-1), y_(n-1)))
```

For `y' = 2t`, `y(0)=0`, exact starter `y_1=1/4`, and `h=1/2`, the finite
two-step Adams-Bashforth trace is:

```text
times  = 0, 1/2, 1, 3/2
states = 0, 1/4, 1, 9/4
slopes =    3/2, 5/2
errors = 0, 0,   0, 0
```

The validator checks the starter value, derivative history, each multistep
slope, each next state, and the zero-error table against `y=t^2`. The bad
Adams-Bashforth row claims the first multistep result is `3/4`; exact replay
computes `1`, and the separate `qf-lra-bad-adams-bashforth-step` row isolates
that contradiction through checked Farkas evidence.

## Name The Lean Horizon

The finite rows are useful because they isolate a trustworthy kernel of the
subject:

```text
recurrence trace
bounded invariant
threshold reachability
Euler transition replay
Runge-Kutta midpoint stage replay
Heun predictor and averaged-slope replay
backward Euler implicit endpoint solve
Crank-Nicolson implicit trapezoid solve
Adams-Bashforth derivative-history update
finite error table
bad-step refutation
```

The general theory remains outside this resource:

```text
ODE existence and uniqueness
stability and bifurcation theorems
global convergence rates
stiffness analysis
chaotic dynamics
PDE theory
floating-point numerical honesty
```

Those need Lean-backed theorem resources, Axeyum-emitted certificates for
bounded transition obligations, or numerical-honesty metadata for approximate
solvers.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/bounded-dynamics-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-euler-method-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-runge-kutta-midpoint-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-heun-method-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-backward-euler-method-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-crank-nicolson-method-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-adams-bashforth-method-v0
cargo test -p axeyum-solver --test math_resource_lra_routes bounded_dynamics_bad_transition_step_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes bounded_dynamics_bad_threshold_step_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes bounded_dynamics_bad_invariant_bound_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_euler_bad_step_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_euler_bad_max_error_bound_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_euler_bad_terminal_error_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_runge_kutta_midpoint_bad_step_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_heun_bad_step_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_backward_euler_bad_step_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_crank_nicolson_bad_step_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_adams_bashforth_bad_step_artifact_emits_checked_farkas
```

Expected output for each command:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current finite dynamics resource pattern:

```text
untrusted fast search -> trace, invariant, reachability, step, or error candidate
trusted small checking -> exact rational transition replay, pointwise checks, and Farkas certificates for linear refutations
remaining horizon -> continuous ODE theory, convergence, stability, and PDEs
```

The next practical graduation step is to lower fixed recurrence and
time-stepping rows into deterministic QF_LRA or BV transition obligations, then
replay SAT witnesses and checked refutations through Axeyum instead of
pack-local Python alone. The separate bounded-dynamics, finite Euler,
Runge-Kutta midpoint, Heun, and Backward Euler `qf-lra-*` rows now exercise
that QF_LRA/Farkas route after replay computes the finite values; the
Crank-Nicolson row adds the same checked split for an implicit trapezoid step,
and the Adams-Bashforth row adds the checked split for an explicit multistep
derivative-history update.
