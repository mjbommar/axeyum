# End To End: Bounded Recurrence Dynamics

This lesson follows one bounded dynamics resource from exact recurrence replay
to checked rejection of a false invariant bound. It uses the
[bounded-dynamics-v0](../../../artifacts/examples/math/bounded-dynamics-v0/)
pack.

Concept rows:

- `field_differential_equations_and_dynamical_systems`,
  `field_numerical_analysis`, and `field_linear_algebra` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `curriculum_calculus`, `curriculum_linear_algebra`, and
  `curriculum_sequences_and_limits` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `family_exact_rational_farkas` in the atlas example-family vocabulary.

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `linear-recurrence-trace` | `sat` | replay-only |
| `bounded-invariant-witness` | `sat` | replay-only |
| `unsafe-threshold-reachable` | `sat` | replay-only |
| `bad-invariant-bound-rejected` | `unsat` | checked QF_LRA/Farkas |

Every row is a finite exact-rational transition-system slice. The pack checks
listed traces, finite invariants, and bounded reachability. It does not prove
continuous-time existence, uniqueness, stability, bifurcation, chaos, PDE, or
asymptotic convergence theorems.

## Replay A Recurrence Trace

The first row fixes a recurrence, initial state, and horizon:

```text
x(0) = 0
x(t+1) = x(t) + 2
steps = 4
trace = 0, 2, 4, 6, 8
```

The checker verifies the initial state, the trace length, and every adjacent
transition:

```text
0 + 2 = 2
2 + 2 = 4
4 + 2 = 6
6 + 2 = 8
```

This is finite replay. A solver may propose the trace, but the trusted check is
the exact transition arithmetic over the listed horizon.

## Replay An Invariant

The bounded-invariant row uses the same trace and checks:

```text
0 <= x(t) <= 8
```

for every listed state:

```text
0, 2, 4, 6, 8
```

This is the bounded, explicit version of an invariant proof. It does not prove
that the recurrence satisfies a general invariant for all time; it proves only
the listed finite horizon.

## Replay Threshold Reachability

The reachability row uses a different recurrence:

```text
x(0) = 0
x(t+1) = x(t) + 3
steps = 3
trace = 0, 3, 6, 9
threshold = 7
```

Replay checks that the threshold is false at the first three listed states and
first true at step `3`:

```text
0 < 7
3 < 7
6 < 7
9 >= 7
```

This is the bug-finding side of bounded dynamics: an untrusted trace becomes a
trusted witness only after exact replay confirms it reaches the target.

## Check The Bad Invariant

The negative row reuses the plus-two trace but claims:

```text
x(t) <= 6
```

Exact replay computes:

```text
max(0, 2, 4, 6, 8) = 8
```

The committed SMT-LIB artifact
[`bad-invariant-bound-farkas-conflict.smt2`](../../../artifacts/examples/math/bounded-dynamics-v0/smt2/bad-invariant-bound-farkas-conflict.smt2)
isolates the final exact-linear contradiction:

```text
terminal_state = 8
terminal_state <= 6
```

The solver search and emitted certificate are not trusted. The accepted
evidence is the independently checked `UnsatFarkas` certificate produced from
the source assertions.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/bounded-dynamics-v0
cargo test -p axeyum-solver --test math_resource_lra_routes bounded_dynamics_bad_invariant_bound_artifact_emits_checked_farkas
```

Expected validator output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> trace, invariant, threshold, or Farkas certificate
trusted small checking -> exact recurrence replay, finite pointwise checks, and exact Farkas arithmetic
remaining horizon -> continuous dynamics, ODE theory, stability, chaos, PDEs, and asymptotic behavior
```

For explicit Euler traces and finite error tables, read
[End To End: Finite Dynamics And Euler Replay](finite-dynamics-euler-end-to-end.md).
For the broader bridge across dynamics, operators, Chebyshev systems, Markov
chains, and hitting times, read
[End To End: Bounded Dynamics And Operators](analysis-dynamics-end-to-end.md).
