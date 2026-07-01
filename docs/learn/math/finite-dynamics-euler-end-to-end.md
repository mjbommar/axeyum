# End To End: Finite Dynamics And Euler Replay

This lesson follows two exact finite dynamics resources from recurrence data to
checked transition replay. It uses
[bounded-dynamics-v0](../../../artifacts/examples/math/bounded-dynamics-v0/) and
[finite-euler-method-v0](../../../artifacts/examples/math/finite-euler-method-v0/).
For the bounded recurrence and invariant slice alone, read
[End To End: Bounded Recurrence Dynamics](bounded-dynamics-end-to-end.md).
For the explicit Euler and finite error-table slice alone, read
[End To End: Finite Euler Method](finite-euler-method-end-to-end.md).

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
| `bad-transition-step-rejected` | `unsat` | checked |
| `bad-invariant-bound-rejected` | `unsat` | checked |
| `linear-decay-euler-trace` | `sat` | replay-only |
| `quadratic-forcing-error-replay` | `sat` | replay-only |
| `bad-max-error-bound-rejected` | `unsat` | checked |
| `nonnegative-monotone-invariant` | `sat` | replay-only |
| `bad-euler-step-rejected` | `unsat` | checked |
| `general-ode-theory-lean-horizon` | `not-run` | lean-horizon |

These rows are finite transition-system checks over exact rationals. They do
not claim continuous-time existence, uniqueness, stability, convergence rates,
stiffness behavior, chaos, or PDE theory.
The shared `bridge_finite_dynamics_euler_replay` row is the atlas vocabulary
for this pattern across recurrence prefixes, bounded dynamics, finite
invariants, threshold reachability, explicit Euler steps, and finite error
tables.

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

The first checked negative row uses the same trace but claims the transition
after state `2` lands at `5`. Exact replay computes `2 + 2 = 4`; the resource
regression checks the bad transition as `QF_LRA`:

```text
previous_state = 2
delta = 2
next_state = previous_state + delta
next_state = 5
```

The second checked negative row uses the same trace but claims:

```text
x(t) <= 6
```

Exact replay computes the final and maximum state as `8`. The resource
regression checks the bad invariant as `QF_LRA`:

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

Exact replay computes `max_error = 3/4`, so the source QF_LRA artifact checks
the contradictory error-bound inequality through Farkas evidence.

## Reject A Bad Euler Step

The checked negative row claims:

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
certificate check.

so the row is rejected. This is the most important teaching shape in the pack:
the same arithmetic that accepts a good step rejects a plausible but false
numerical update.

## Name The Lean Horizon

The finite rows are useful because they isolate a trustworthy kernel of the
subject:

```text
recurrence trace
bounded invariant
threshold reachability
Euler transition replay
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
cargo test -p axeyum-solver --test math_resource_lra_routes bounded_dynamics_bad_transition_step_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes bounded_dynamics_bad_invariant_bound_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_euler_bad_max_error_bound_artifact_emits_checked_farkas
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

The next practical graduation step is to lower fixed recurrence and Euler-step
rows into deterministic QF_LRA or BV transition obligations, then replay SAT
witnesses and checked refutations through Axeyum instead of pack-local Python
alone. The bad transition-step row, bad invariant-bound row, bad finite
error-bound row, and bad fixed Euler step now exercise that QF_LRA/Farkas
route.
