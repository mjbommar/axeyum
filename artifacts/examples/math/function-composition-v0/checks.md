# Checks

## `composition-table-replay`

Expected result: `sat`.

The validator checks that `f : A -> B`, `g : B -> C`, and the listed composite
`g o f : A -> C` are total finite functions and that every composite row is
computed from the two input tables.

## `image-preimage-replay`

Expected result: `sat`.

The validator recomputes the image of a listed subset of the domain and the
preimage of a listed subset of the codomain for one finite function.

## `bijection-inverse-table`

Expected result: `sat`.

The validator checks that the listed function is bijective, then recomputes the
inverse table and both identity compositions.

## `composition-associativity-table`

Expected result: `sat`.

The validator checks three finite functions and recomputes both
`h o (g o f)` and `(h o g) o f`, requiring the listed tables to match.

## `non-injective-inverse-rejected`

Expected result: `sat`.

The validator accepts this counterexample only because two distinct domain
values map to the same codomain value, so no inverse function can be defined on
the image that sends that codomain value back to both inputs.

## `qf-uf-composition-application-alethe`

Expected result: `unsat`.

The SMT-LIB artifact asserts `comp(a) = g(f(a))`, `f(a) = b`, and `g(b) = c`,
while also asserting `comp(a) != c`. The solver regression requires a pure EUF
`Evidence::UnsatAletheProof` and rechecks it independently.

## `general-function-laws-lean-horizon`

Expected result: `not-run`.

General extensional equality, inverse laws, and categorical function laws remain
proof-assistant targets, not finite-table evidence.
