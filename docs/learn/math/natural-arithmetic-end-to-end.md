# End To End: Natural Arithmetic

This lesson follows one natural-arithmetic resource from exact integer replay
to checked bounded enumeration status. It uses the
[natural-arithmetic-v0](../../../artifacts/examples/math/natural-arithmetic-v0/)
pack.

Concept rows:

- `curriculum_naturals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_number_theory` and `field_discrete_math` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `successor-addition-replay` | `sat` | checked |
| `addition-commutativity-fixed` | `sat` | checked |
| `multiplication-distributivity-fixed` | `sat` | checked |
| `successor-injective-bounded` | `unsat` | checked |
| `zero-not-successor-bounded` | `unsat` | checked |
| `bounded-natural-negative-rejected` | `unsat` | checked |

The `sat` rows are exact witness replays. The `unsat` rows are bounded
enumerations over the finite natural domain `0..7`. The negative-domain row is
also promoted into a checked `QF_LIA` arithmetic-evidence regression. None of these
rows claims a universal theorem over all natural numbers.

## Replay Successor Addition

The first witness encodes the fixed identity:

```text
a + S(b) = S(a + b)
a = 5
b = 7
S(b) = 8
```

The validator recomputes:

```text
left  = 5 + 8      = 13
right = S(5 + 7)  = 13
```

Both sides match, so the witness is accepted as checked `sat`.

## Replay Fixed Addition

The commutativity row is deliberately fixed:

```text
6 + 4 = 10
4 + 6 = 10
```

This is a checked arithmetic replay for one pair of naturals. It is not the
general theorem `forall a b, a + b = b + a`.

## Replay Fixed Distributivity

The multiplication row checks:

```text
2 * (3 + 4) = 2*3 + 2*4
```

The validator recomputes both sides:

```text
left  = 2 * 7     = 14
right = 6 + 8     = 14
```

The row is accepted because the listed witness evaluates exactly.

## Enumerate Bounded Successor Facts

The bounded rows search for counterexamples in `0..7`:

```text
distinct x,y <= 7 with S(x) = S(y)
n <= 7 with S(n) = 0
a negative element in 0..7
```

The validator enumerates the finite domain, recomputes each successor, and
finds no counterexample. These rows are checked `unsat` inside the named bound.

For the negative-domain row, the promoted SMT-LIB artifact keeps the extracted
integer contradiction in solver form:

```text
0 <= n
n <= 7
n < 0
```

The `math_resource_lia_routes` regression requires checked QF_LIA arithmetic
evidence and rechecks the proof object against the original assertion.

## Name The Lean Horizon

The pack's graduation criteria keep the universal natural-number theorems out
of this finite checker:

```text
forall a b, a + b = b + a
forall a b c, a * (b + c) = a*b + a*c
natural-number induction schema
```

Those need a Lean route or equivalent kernel-checked proof artifact. Bounded
enumeration is useful evidence, but it is not a substitute for induction.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/natural-arithmetic-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's resource pattern for the naturals:

```text
untrusted fast search -> fixed witness or bounded counterexample candidate
trusted small checking -> exact integer replay and finite-domain enumeration
```

The negative-domain obstruction has graduated to deterministic QF_LIA plus
checked arithmetic evidence. The successor-injectivity and
zero-not-successor rows remain bounded finite replay until a BV/CNF encoding
adds distinct proof pressure, while universal Nat facts remain under the
theorem-prover horizon.
