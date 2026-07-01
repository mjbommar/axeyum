# End To End: Finite Recurrence Prefixes

This lesson follows one recurrence resource from exact prefix replay through
checked bad-value and bad affine-step rejections. It uses the
[finite-recurrence-prefix-v0](../../../artifacts/examples/math/finite-recurrence-prefix-v0/)
pack.

Concept rows:

- `curriculum_sequences_and_limits`, `curriculum_counting`, and
  `curriculum_linear_algebra` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_real_analysis`, `field_discrete_math`, `field_linear_algebra`, and
  `field_numerical_analysis` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `bridge_bounded_theorem_shadow` in the atlas bridge vocabulary.

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `fibonacci-prefix-replay` | `sat` | replay-only |
| `affine-recurrence-prefix-replay` | `sat` | replay-only |
| `companion-matrix-prefix-replay` | `sat` | replay-only |
| `bad-fibonacci-value-rejected` | `unsat` | checked QF_LRA/Farkas |
| `bad-affine-step-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-recurrence-theory-lean-horizon` | `not-run` | Lean horizon |

Every positive row is a finite list or finite matrix-step check. The pack does
not prove a closed form, an asymptotic estimate, or a theorem for all `n`.

## Replay A Fibonacci Prefix

Encode the recurrence:

```text
F_0 = 0
F_1 = 1
F_n = F_{n-1} + F_{n-2}
```

The witness lists:

```text
0, 1, 1, 2, 3, 5, 8
```

The validator checks the two initial values and every finite step:

```text
F_2 = 1 + 0 = 1
F_3 = 1 + 1 = 2
F_4 = 2 + 1 = 3
F_5 = 3 + 2 = 5
F_6 = 5 + 3 = 8
```

## Replay An Affine Recurrence

The second witness checks a first-order recurrence:

```text
x_0 = 0
x_{n+1} = 2*x_n + 1
```

The finite prefix is:

```text
0, 1, 3, 7, 15
```

This is useful for algorithms, dynamics, and numerical-method examples because
the checker only needs exact rational arithmetic over a fixed horizon.

## Replay A Companion Matrix

The third witness treats the Fibonacci recurrence as a matrix state update:

```text
A = [[1, 1],
     [1, 0]]

state_n = [F_{n+1}, F_n]
A * state_n = state_{n+1}
```

The checked state trace is:

```text
[1,0] -> [1,1] -> [2,1] -> [3,2] -> [5,3] -> [8,5]
```

This is the bridge into linear algebra: recurrence replay becomes repeated
matrix-vector multiplication over exact rationals.

## Check The Fibonacci Refutation

The promoted bad row claims:

```text
F_6 = 9
```

Exact replay computes:

```text
F_6 = 8
```

The committed SMT-LIB artifact
[`bad-fibonacci-value-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-recurrence-prefix-v0/smt2/bad-fibonacci-value-farkas-conflict.smt2)
records the tiny contradiction:

```text
f6 = 8
f6 = 9
```

Axeyum may search for the contradiction, but the accepted evidence is checked
`UnsatFarkas` arithmetic over the original source artifact.

## Check The Affine Step Refutation

The second promoted bad row claims:

```text
x_4 = 14
```

Exact affine recurrence replay computes:

```text
x_3 = 7
x_4 = 2*x_3 + 1 = 15
15 - 14 = 1
```

The committed SMT-LIB artifact
[`bad-affine-step-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-recurrence-prefix-v0/smt2/bad-affine-step-farkas-conflict.smt2)
records the tiny contradiction:

```text
transition_residual = 1
transition_residual <= 0
```

The solver search is still untrusted. The accepted evidence is independently
checked `UnsatFarkas` arithmetic over the source artifact.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-recurrence-prefix-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_recurrence_prefix_bad_
```

Expected validator output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> proposed prefix, matrix trace, or Farkas certificate
trusted small checking -> exact recurrence replay, matrix-vector replay, checked QF_LRA evidence
remaining horizon -> induction over all n, closed forms, asymptotics, convergence, stability
```

Use this page after
[End To End: Bounded Monotone Sequence](bounded-monotone-sequence-end-to-end.md)
or
[End To End: Generating Functions](generating-functions-end-to-end.md)
when the goal is to reason about finite recurrence data without pretending it
proves the general recurrence theory.
