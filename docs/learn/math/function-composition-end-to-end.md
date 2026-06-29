# End To End: Function Composition

This lesson follows one finite function-composition resource from graph tables
to replayed result and proof/evidence status. It uses the
[function-composition-v0](../../../artifacts/examples/math/function-composition-v0/)
pack.

Concept rows:

- `curriculum_relations_and_functions`, `curriculum_sets`, and
  `curriculum_cardinality` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_set_theory_and_foundations` and `field_discrete_math` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `composition-table-replay` | `sat` | checked |
| `image-preimage-replay` | `sat` | checked |
| `bijection-inverse-table` | `sat` | checked |
| `composition-associativity-table` | `sat` | checked |
| `non-injective-inverse-rejected` | `sat` | checked |
| `qf-uf-composition-application-alethe` | `unsat` | checked |
| `general-function-laws-lean-horizon` | `not-run` | lean-horizon |

The checked rows are finite function-table rows plus one concrete QF_UF
proof-object row. The pack does not claim function extensionality, inverse laws,
image/preimage laws, or categorical composition laws over arbitrary types.

## Encode

Each function is an explicit finite graph:

```text
domain
codomain
pairs = [input, output]
```

The validator first checks that every graph is total and single-valued. It then
computes:

```text
(g o f)(x)  = g(f(x))
image(S)   = { f(x) | x in S }
preimage(T)= { x | f(x) in T }
f^{-1}(y)  = the unique x with f(x) = y
```

The proof-object row uses QF_UF/Alethe evidence for a reusable composition
application obligation. The finite table rows still replay directly.

## Replay Composition

The first witness gives:

```text
f(a0)=b0, f(a1)=b1, f(a2)=b0
g(b0)=c2, g(b1)=c0
```

The checker recomputes:

```text
(g o f)(a0) = g(b0) = c2
(g o f)(a1) = g(b1) = c0
(g o f)(a2) = g(b0) = c2
```

These rows match the listed composite table, so the claim is accepted.

## Replay Image And Preimage

For the finite function:

```text
x0 -> y0
x1 -> y1
x2 -> y1
x3 -> y2
```

the listed domain subset is:

```text
{x0, x2}
```

The checker recomputes its image:

```text
image({x0,x2}) = {y0,y1}
```

For the codomain subset `{y1,y2}`, it recomputes:

```text
preimage({y1,y2}) = {x1,x2,x3}
```

## Replay An Inverse Table

The bijection witness maps:

```text
p0 -> q2
p1 -> q0
p2 -> q1
```

The proposed inverse is:

```text
q0 -> p1
q1 -> p2
q2 -> p0
```

The checker verifies the original map is bijective, then recomputes both
identity compositions:

```text
f^{-1} o f = id_domain
f o f^{-1} = id_codomain
```

## Replay Associativity

The associativity row uses three finite functions `f`, `g`, and `h`. The
validator recomputes both paths:

```text
h o (g o f)
(h o g) o f
```

and checks that both tables are:

```text
a0 -> d0
a1 -> d1
```

This is a checked finite associativity instance, not a theorem over arbitrary
types.

## Check The Non-Injective Inverse Counterexample

The counterexample row gives a total function:

```text
u0 -> v0
u1 -> v0
u2 -> v1
```

The validator checks the collision:

```text
u0 != u1
f(u0) = f(u1) = v0
```

No inverse function can send `v0` back to both `u0` and `u1`, so the row is a
checked counterexample to the false inverse claim.

## Check The Composition Certificate

The proof-object row encodes one concrete composition application:

```text
comp(a) = g(f(a))
f(a) = b
g(b) = c
comp(a) != c
```

The artifact lives at
`artifacts/examples/math/function-composition-v0/smt2/composition-application-conflict.smt2`.
The resource regression checks that Axeyum emits `Evidence::UnsatAletheProof`
with the pure EUF Alethe emitter and then rechecks the proof independently.

## Name The Lean Horizon

The final row records the boundary for general function theory:

```text
function extensionality
inverse laws over arbitrary types
image/preimage laws
categorical composition laws
```

Those statements need a proof-assistant route. Finite table replay is useful
evidence for concrete instances, not a replacement for the general theorems.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/function-composition-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's resource pattern for finite function operations:

```text
untrusted fast search -> candidate function, composition, inverse, image tables
trusted small checking -> totality, single-valuedness, recomputed tables, collision row, Alethe composition proof
```

General function laws, arbitrary-type extensional equality, categorical
composition, and inverse theorems require stronger proof routes or
Lean/mathlib-scale proof support.
