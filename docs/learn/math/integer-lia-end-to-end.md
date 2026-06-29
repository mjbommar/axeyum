# End To End: Integer Linear Arithmetic

This lesson follows one integer-LIA resource from exact signed-integer replay
to checked interval and Diophantine refutations. It uses the
[integer-lia-v0](../../../artifacts/examples/math/integer-lia-v0/) pack.

Concept rows:

- `curriculum_integers` and `curriculum_naturals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_number_theory` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `signed-trichotomy-fixed` | `sat` | checked |
| `order-transitivity-fixed` | `sat` | checked |
| `integer-ring-identity-replay` | `sat` | checked |
| `linear-equation-witness` | `sat` | checked |
| `integer-interval-infeasible` | `unsat` | checked |
| `diophantine-gcd-obstruction` | `unsat` | checked |

The `sat` rows are exact integer witnesses. The `unsat` rows use small trusted
checks: one bound comparison and one gcd divisibility test.

## Replay Signed Order

The trichotomy row records:

```text
left = -3
right = 4
relation = lt
```

The validator checks that exactly one of `<`, `=`, or `>` holds between the two
integers, and that the listed relation is the true one.

The transitivity row records:

```text
-2 < 1
1 < 5
therefore -2 < 5
```

The validator checks both premises and then checks the endpoint comparison.

## Replay Integer Algebra

The ring-identity witness is:

```text
a = -7
b = 5
(a + b) - b = a
```

The validator recomputes:

```text
(-7 + 5) - 5 = -7
```

The linear equation witness is:

```text
3*x - 2*y = 7
x = 3
y = 1
```

The validator checks the integer dot product:

```text
3*3 + (-2)*1 = 7
```

## Refute An Empty Interval

The interval row asks for:

```text
z >= 5
z <= 2
```

The validator checks the bounds directly. Since `5 > 2`, no integer can satisfy
both constraints, so the row is checked `unsat`.

## Refute A Diophantine Equation

The Diophantine row asks for:

```text
2*x + 4*y = 3
```

The trusted check is the gcd test:

```text
gcd(2, 4) = 2
2 does not divide 3
```

Therefore no integer solution exists. This is the small certificate shape that
the QF_LIA Diophantine recipe should eventually emit and check.

## Name The Lean Horizon

The pack does not claim general quantified integer algebra:

```text
forall a b, (a + b) - b = a
forall a b c, a < b and b < c implies a < c
```

Those need QF_LIA proof objects for solver-level rows or Lean reconstruction
for quantified theorem statements.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/integer-lia-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's resource pattern for signed integer arithmetic:

```text
untrusted fast search -> integer witness or infeasibility candidate
trusted small checking -> exact integer replay, bound comparison, gcd test
```

The graduation route is deterministic QF_LIA lowering plus checked integer
evidence for interval and Diophantine `unsat` rows.
