# End To End: Finite Euler Method

This lesson follows one finite Euler-method resource from exact transition
replay and error replay to checked rejection of a false error bound and false
one-step update. It uses the
[finite-euler-method-v0](../../../artifacts/examples/math/finite-euler-method-v0/)
pack.

Concept rows:

- `field_differential_equations_and_dynamical_systems`,
  `field_numerical_analysis`, and `field_real_analysis` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `curriculum_calculus`, `curriculum_sequences_and_limits`, and
  `curriculum_reals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `family_exact_rational_farkas` in the atlas example-family vocabulary.

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `linear-decay-euler-trace` | `sat` | replay-only |
| `quadratic-forcing-error-replay` | `sat` | replay-only |
| `bad-max-error-bound-rejected` | `unsat` | checked QF_LRA/Farkas |
| `nonnegative-monotone-invariant` | `sat` | replay-only |
| `bad-euler-step-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-ode-theory-lean-horizon` | `not-run` | Lean horizon |

Every checked row is finite and exact-rational. The pack treats explicit Euler
as a bounded transition relation. It does not prove ODE existence, uniqueness,
stability, stiffness behavior, convergence rates, floating-point correctness,
or PDE theory.

## Replay A Decay Trace

Explicit Euler is checked as:

```text
y_(n+1) = y_n + h * f(t_n, y_n)
t_(n+1) = t_n + h
```

For `y' = -y`, step `h = 1/2`, and `y(0) = 1`, the pack lists:

```text
times  = 0, 1/2, 1, 3/2
states = 1, 1/2, 1/4, 1/8
derivatives = -1, -1/2, -1/4
```

The checker recomputes each transition exactly:

```text
1   + (1/2)*(-1)   = 1/2
1/2 + (1/2)*(-1/2) = 1/4
1/4 + (1/2)*(-1/4) = 1/8
```

This is replay-only: a proposed trace is untrusted until each exact rational
step is checked.

## Replay A Finite Error Table

For `y' = 2t`, `y(0) = 0`, and exact solution `y = t^2`, the pack lists:

```text
times  = 0, 1/2, 1, 3/2
states = 0, 0, 1/2, 3/2
exact  = 0, 1/4, 1, 9/4
errors = 0, 1/4, 1/2, 3/4
```

The validator checks the Euler updates, evaluates `t^2` on the finite grid,
computes absolute errors, and confirms the maximum error `3/4`. This is a
finite error table, not a convergence-rate theorem.

## Check The Bad Error Bound

The first negative row reuses the finite error table but claims:

```text
max_error <= 1/2
```

Exact replay computes:

```text
max(0, 1/4, 1/2, 3/4) = 3/4
```

The committed SMT-LIB artifact
[`bad-max-error-bound-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-euler-method-v0/smt2/bad-max-error-bound-farkas-conflict.smt2)
isolates the exact-linear contradiction:

```text
max_error = 3/4
max_error <= 1/2
```

The source object is still the exact finite error table; the solver proof is
accepted only after the emitted `UnsatFarkas` certificate checks independently.

## Replay A Finite Invariant

The linear-decay trace is also checked against a bounded monotone invariant:

```text
0 <= y_n <= 1
y_(n+1) <= y_n
```

for the listed states:

```text
1, 1/2, 1/4, 1/8
```

Again, this proves only the finite listed horizon. A general stability or
monotonicity theorem remains a Lean-horizon target.

## Check The Bad Step

The negative row claims that one explicit Euler step for `y' = -y`, `h = 1/2`,
and `y = 1` gives:

```text
next_state = 3/4
```

Exact replay computes:

```text
next_state = 1 + (1/2)*(-1) = 1/2
```

The committed SMT-LIB artifact
[`bad-euler-step-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-euler-method-v0/smt2/bad-euler-step-farkas-conflict.smt2)
isolates the exact-linear contradiction:

```text
state = 1
derivative = -1
next_state = state + (1/2)*derivative
next_state = 3/4
```

The solver search and emitted certificate are not trusted. The accepted
evidence is the independently checked `UnsatFarkas` certificate produced from
the source assertions.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-euler-method-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_euler_bad_max_error_bound_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_euler_bad_step_emits_checked_farkas
```

Expected validator output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> Euler trace, finite error table, invariant, or Farkas certificate
trusted small checking -> exact transition replay, exact finite error arithmetic, and exact Farkas arithmetic
remaining horizon -> ODE existence/uniqueness, stability, convergence rates, stiffness, floating point, and PDEs
```

For the recurrence-only dynamics slice, read
[End To End: Bounded Recurrence Dynamics](bounded-dynamics-end-to-end.md).
For the combined recurrence/Euler bridge, read
[End To End: Finite Dynamics And Euler Replay](finite-dynamics-euler-end-to-end.md).
