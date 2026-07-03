# End To End: Finite BDF2 Method

This lesson follows one exact finite two-step BDF2 resource from implicit
history replay to checked Farkas evidence:
[finite-bdf2-method-v0](../../../artifacts/examples/math/finite-bdf2-method-v0/).

The point is small and deliberate:

```text
untrusted fast search -> history trace, implicit multistep update, decay row, or Farkas certificate
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
| `bdf2-history-witness` | `sat` | replay-only |
| `bdf2-monotone-decay-witness` | `sat` | replay-only |
| `bad-bdf2-step-rejected` | `unsat` | replay-only |
| `qf-lra-bad-bdf2-step` | `unsat` | checked QF_LRA/Farkas |
| `general-bdf2-theory-lean-horizon` | `not-run` | Lean horizon |

## Finite Claim

Every row is finite and exact-rational. The pack treats BDF2 as a fixed
implicit two-step transition relation on this ODE:

```text
y' = -y
y(0) = 1
h = 1/2
starter y_1 = 2/3
```

BDF2 is checked as:

```text
(3*y_(n+1) - 4*y_n + y_(n-1)) / (2h) = f(t_(n+1), y_(n+1))
```

Because `2h = 1`, the listed trace must satisfy:

```text
3*y_(n+1) - 4*y_n + y_(n-1) = -y_(n+1)
```

The listed trace is:

```text
times       = 0, 1/2, 1, 3/2
states      = 1, 2/3, 5/12, 1/4
derivatives = -1, -2/3, -5/12, -1/4
```

The validator recomputes the backward-Euler starter and each BDF2 residual:

```text
starter: 2/3 = 1 + (1/2)*(-2/3)

n=1: 3*(5/12) - 4*(2/3) + 1 = -5/12
     f(1, 5/12) = -5/12

n=2: 3*(1/4) - 4*(5/12) + 2/3 = -1/4
     f(3/2, 1/4) = -1/4
```

The finite decay row checks only this table:

```text
0 < 1/4 < 5/12 < 2/3 < 1
```

That is not a stability or convergence theorem. It is exact replay of this
trace and its fixed starter history.

## Bad Source Row

The malformed source row says:

```text
For y' = -y, h = 1/2, y_0 = 1, y_1 = 2/3,
the first BDF2 multistep update gives 1/3.
```

Exact replay computes:

```text
3*(5/12) - 4*(2/3) + 1 = -5/12
f(1, 5/12) = -5/12
```

So the replay-only row rejects the malformed claim and records the gap:

```text
5/12 - 1/3 = 1/12
```

## Checked Farkas Row

The separate `qf-lra-bad-bdf2-step` row owns the proof-object refutation. Its
source artifact is:

[`bad-bdf2-step-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-bdf2-method-v0/smt2/bad-bdf2-step-farkas-conflict.smt2)

The artifact isolates this scalar contradiction:

```text
bdf2_next_state = 5/12
bdf2_next_state = 1/3
```

The route test parses that SMT-LIB file, emits `UnsatFarkas` evidence, and
independently checks the certificate. The source trace is still checked by the
pack validator; the Farkas row is only the compact arithmetic contradiction.

## Theorem Horizon

The finite resource does not prove:

- BDF2 order or consistency;
- zero-stability or convergence;
- starter-generation correctness beyond this listed starter;
- nonlinear endpoint-solve correctness for arbitrary vector fields;
- variable-step multistep correctness;
- floating-point implementation correctness;
- PDE method-of-lines theory.

Those require future Lean theorem statements or numerical-honesty artifacts.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-bdf2-method-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_bdf2_bad_step_artifact_emits_checked_farkas
```

To find the row through the public query surface:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-bdf2-method-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-bdf2-step \
  --require-any
```

## Trust Boundary

The split is:

```text
untrusted fast search -> BDF2 history trace, implicit multistep update, decay table, or Farkas certificate
trusted small checking -> exact rational replay and checked QF_LRA/Farkas evidence
```

This is the same pattern used by
[End To End: Finite Dynamics And Euler Replay](finite-dynamics-euler-end-to-end.md),
[End To End: Finite Backward Euler Method](backward-euler-method-end-to-end.md),
[End To End: Finite Crank-Nicolson Method](crank-nicolson-method-end-to-end.md),
and [End To End: Finite Adams-Bashforth Method](adams-bashforth-method-end-to-end.md).
