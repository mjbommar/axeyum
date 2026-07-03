# End To End: Finite Adams-Bashforth Method

This lesson follows one exact finite two-step Adams-Bashforth resource from
history replay to checked Farkas evidence:
[finite-adams-bashforth-method-v0](../../../artifacts/examples/math/finite-adams-bashforth-method-v0/).

The point is small and deliberate:

```text
untrusted fast search -> history trace, multistep update, zero-error row, or Farkas certificate
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
| `adams-bashforth-history-witness` | `sat` | replay-only |
| `adams-bashforth-zero-error-witness` | `sat` | replay-only |
| `bad-adams-bashforth-step-rejected` | `unsat` | replay-only |
| `qf-lra-bad-adams-bashforth-step` | `unsat` | checked QF_LRA/Farkas |
| `general-adams-bashforth-theory-lean-horizon` | `not-run` | Lean horizon |

## Finite Claim

Every row is finite and exact-rational. The pack treats Adams-Bashforth as a
fixed two-step transition relation on this ODE:

```text
y' = 2t
y(0) = 0
h = 1/2
starter y_1 = 1/4
```

Two-step Adams-Bashforth is checked as:

```text
y_(n+1) = y_n + h * ((3/2)*f(t_n,y_n) - (1/2)*f(t_(n-1),y_(n-1)))
```

The listed trace is:

```text
times       = 0, 1/2, 1, 3/2
states      = 0, 1/4, 1, 9/4
derivatives = 0, 1, 2
```

The validator recomputes the exact starter and each multistep slope:

```text
n=1: (3/2)*1 - (1/2)*0 = 3/2
     1/4 + (1/2)*(3/2) = 1

n=2: (3/2)*2 - (1/2)*1 = 5/2
     1 + (1/2)*(5/2) = 9/4
```

The finite error row checks only this table:

```text
exact y=t^2 = 0, 1/4, 1, 9/4
absolute errors = 0, 0, 0, 0
max_error = 0
```

That is not a convergence theorem. It is exact replay of this trace and its
fixed starter history.

## Bad Source Row

The malformed source row says:

```text
For y' = 2t, h = 1/2, y_0 = 0, y_1 = 1/4,
and derivative history 0,1,
the first Adams-Bashforth multistep update gives 3/4.
```

Exact replay computes:

```text
slope = (3/2)*1 - (1/2)*0 = 3/2
next_state = 1/4 + (1/2)*(3/2) = 1
```

So the replay-only row rejects the malformed claim and records the gap:

```text
1 - 3/4 = 1/4
```

## Checked Farkas Row

The separate `qf-lra-bad-adams-bashforth-step` row owns the proof-object
refutation. Its source artifact is:

[`bad-adams-bashforth-step-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-adams-bashforth-method-v0/smt2/bad-adams-bashforth-step-farkas-conflict.smt2)

The artifact isolates this scalar contradiction:

```text
adams_bashforth_next_state = 1
adams_bashforth_next_state = 3/4
```

The route test parses that SMT-LIB file, emits `UnsatFarkas` evidence, and
independently checks the certificate. The source trace is still checked by the
pack validator; the Farkas row is only the compact arithmetic contradiction.

## Theorem Horizon

The finite resource does not prove:

- Adams-Bashforth order or consistency;
- zero-stability or convergence;
- starter-generation correctness;
- variable-step multistep correctness;
- floating-point implementation correctness;
- PDE method-of-lines theory.

Those require future Lean theorem statements or numerical-honesty artifacts.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-adams-bashforth-method-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_adams_bashforth_bad_step_artifact_emits_checked_farkas
```

To find the row through the public query surface:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-adams-bashforth-method-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-adams-bashforth-step \
  --require-any
```

## Trust Boundary

The split is:

```text
untrusted fast search -> Adams-Bashforth history trace, multistep update, zero-error table, or Farkas certificate
trusted small checking -> exact rational replay and checked QF_LRA/Farkas evidence
```

This is the same pattern used by
[End To End: Finite Dynamics And Euler Replay](finite-dynamics-euler-end-to-end.md),
[End To End: Finite Euler Method](finite-euler-method-end-to-end.md),
[End To End: Finite Runge-Kutta Midpoint](runge-kutta-midpoint-end-to-end.md),
[End To End: Finite Heun Method](heun-method-end-to-end.md),
[End To End: Finite Backward Euler Method](backward-euler-method-end-to-end.md),
and [End To End: Finite Crank-Nicolson Method](crank-nicolson-method-end-to-end.md).
