# End To End: Induction Patterns

This lesson follows one induction-patterns resource from finite replay tables
to checked result and proof/evidence status. It uses the
[induction-patterns-v0](../../../artifacts/examples/math/induction-patterns-v0/)
pack.

Concept rows:

- `curriculum_induction`, `curriculum_proof_methods`, and
  `curriculum_naturals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_logic_and_proof` and `field_number_theory` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `weak-induction-even-sum-prefix` | `unsat` | checked |
| `qf-lia-even-product-odd-obstruction` | `unsat` | checked |
| `strong-induction-fibonacci-bound-prefix` | `unsat` | checked |
| `loop-invariant-prefix-sum-trace` | `sat` | checked |
| `bad-induction-step-rejected` | `sat` | checked |
| `general-induction-schema-lean-horizon` | `not-run` | lean-horizon |

The checked rows are finite-prefix or finite-trace rows. They teach the shapes
of common induction arguments, but they do not claim the full natural-number
induction principle.

## Encode Weak Induction

The weak-induction row studies:

```text
P(n): n * (n + 1) is even
n = 0..6
```

The witness table records:

```text
n * (n + 1):       0, 2, 6, 12, 20, 30, 42
step differences: 2, 4, 6, 8, 10, 12
```

The validator recomputes each product, checks that every product is even, and
checks that each listed step adds `2 * (k + 1)`. It accepts the row as checked
`unsat` because there is no finite-prefix odd-product counterexample.

## Check The Even-Product Certificate

The solver-form row focuses on the last prefix value:

```text
6 * (6 + 1) = 42
```

A bad oddness witness claims:

```text
42 = 2 * 20 + 1 = 41
```

The SMT-LIB artifact records the evaluated contradiction:

```text
product = 42
product = 41
```

Axeyum emits an `UnsatDiophantine` certificate and checks it independently.
The full finite-prefix replay still checks all rows; this certificate pins one
representative rejected parity witness to the solver evidence path.

## Encode Strong Induction

The strong-induction row studies:

```text
fib(n) <= 2^n
n = 0..8
```

The replay table is:

```text
fib: 0, 1, 1, 2, 3, 5, 8, 13, 21
2^n: 1, 2, 4, 8, 16, 32, 64, 128, 256
```

The validator recomputes the Fibonacci prefix and powers of two, then checks
that each finite prefix entry satisfies the bound. The strong-induction idea is
that later rows may depend on more than the immediately previous row, but the
resource still checks only the fixed finite prefix.

## Replay A Loop Invariant

The loop-invariant row treats an imperative trace as an induction argument over
loop iterations. The trace sums `1..5`:

```text
i:   0, 1, 2, 3,  4,  5
acc: 0, 1, 3, 6, 10, 15
```

The invariant is:

```text
acc = i * (i + 1) / 2
```

The validator checks the invariant at every trace row and checks each adjacent
transition. This row is `sat` because the trace itself is a valid witness.

## Reject A Bad Step

The invalid induction candidate is:

```text
P(n): n < 3
```

The base cases look fine for small `n`:

```text
P(0) = true
P(1) = true
P(2) = true
```

but the induction step fails at `k = 2`:

```text
P(2) = true
P(3) = false
```

The row is accepted as a `sat` counterexample to the proposed step. This is the
practical lesson: induction is not a pattern of optimism; the step obligation
is the part that has to survive an adversarial counterexample search.

## Name The Lean Horizon

The final row records the theorem-prover boundary:

```text
full natural-number induction schema for arbitrary predicates
```

Finite-prefix replay can teach the shapes of weak induction, strong induction,
and loop invariants. A universal induction principle needs a Lean route or an
equivalent kernel-checked proof artifact.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/induction-patterns-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's resource pattern for induction styles:

```text
untrusted fast search -> finite-prefix failure candidate or replay trace
trusted small checking -> exact integer replay over listed rows and Diophantine certificates
```

The universal theorem remains outside the finite checker until a proof route
can export and kernel-check the induction argument itself.
