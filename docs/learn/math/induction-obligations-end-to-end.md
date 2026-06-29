# End To End: Induction Obligations

This lesson follows one induction-obligations resource from bounded arithmetic
checks to replayed result and proof/evidence status. It uses the
[induction-obligations-v0](../../../artifacts/examples/math/induction-obligations-v0/)
pack.

Concept rows:

- `curriculum_induction` and `curriculum_naturals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_logic_and_proof` and `field_number_theory` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `sum-formula-base-case` | `sat` | checked |
| `sum-formula-step-bounded` | `unsat` | checked |
| `sum-formula-conclusion-bounded` | `unsat` | checked |
| `bad-step-counterexample-witness` | `sat` | checked |
| `induction-schema-lean-horizon` | `not-run` | lean-horizon |

The checked rows are bounded natural-number arithmetic rows. The pack does not
claim the full natural-number induction schema or a universal theorem over all
natural numbers.

## Encode

The running property is the prefix-sum formula:

```text
P(n): 0 + 1 + ... + n = n * (n + 1) / 2
```

The validator checks finite obligations with exact integer arithmetic:

```text
base:       P(0)
step:       no k <= 8 has P(k) true and P(k+1) false
conclusion: no n <= 9 falsifies P(n)
```

These are useful bounded checks. They are not the same thing as applying the
general induction rule for every natural number.

## Replay The Base Case

For `n = 0`, the prefix sum is:

```text
0
```

The formula side is:

```text
0 * (0 + 1) / 2 = 0
```

Both sides match, so the base row is accepted.

## Check The Bounded Step

The step row searches for:

```text
k <= 8
P(k) is true
P(k + 1) is false
```

The validator enumerates `k = 0..8`, recomputes both `P(k)` and `P(k+1)`, and
finds no bounded counterexample. Therefore the bounded step-counterexample
search is checked `unsat`.

## Check The Bounded Conclusion

The conclusion row searches for:

```text
n <= 9
P(n) is false
```

The validator enumerates `n = 0..9` and confirms the prefix-sum formula holds
through that finite bound. This is a bounded sanity check, not a proof for all
`n`.

## Replay A Bad-Step Counterexample

The bad candidate property is:

```text
P(n): n = 0
```

It has a true base case:

```text
P(0) = true
```

but the step fails immediately:

```text
P(1) = false
```

The row is accepted as a `sat` counterexample to the induction-step obligation.
It demonstrates why base cases alone are not induction.

## Name The Lean Horizon

The final row records the theorem-prover boundary:

```text
full natural-number induction schema for the prefix-sum theorem
```

The finite rows can check bounded base, step, and conclusion obligations. A
universal statement needs a Lean route or equivalent kernel-checked proof.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/induction-obligations-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's resource pattern for induction:

```text
untrusted fast search -> bounded obligation or counterexample candidate
trusted small checking -> exact arithmetic replay over a fixed finite bound
```

The induction schema itself requires a stronger proof route, not just more
bounded enumeration.
