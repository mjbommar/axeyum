# Logic And Proof

Concept rows:

- `curriculum_proof_methods`, `curriculum_propositional_logic`,
  `curriculum_predicate_logic`,
  `curriculum_induction`, and `field_logic_and_proof` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `predicate-logic`, `proof-methods`, and `induction` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)

Example packs:

- [logic-basics-v0](../../../artifacts/examples/math/logic-basics-v0/)
- [finite-predicate-v0](../../../artifacts/examples/math/finite-predicate-v0/)
- [proof-methods-refutation-v0](../../../artifacts/examples/math/proof-methods-refutation-v0/)
- [proof-methods-patterns-v0](../../../artifacts/examples/math/proof-methods-patterns-v0/)
- [induction-obligations-v0](../../../artifacts/examples/math/induction-obligations-v0/)
- [induction-patterns-v0](../../../artifacts/examples/math/induction-patterns-v0/)
- [graph-coloring-v0](../../../artifacts/examples/math/graph-coloring-v0/)

## What Axeyum Checks

The first proof lesson is Boolean: replay a SAT witness, negate a tautology and
check no counterexample exists, and enumerate tiny CNF rows. The predicate
logic pack expands finite-domain quantifiers into explicit predicate-table
checks, including finite universal/existential replay and relation
counterexamples. The proof-methods refutation pack records a small pigeonhole
SAT witness and checks the `PHP(3,2)` UNSAT pigeonhole claim by deterministic
CNF truth-table enumeration. The proof-patterns pack checks direct proof,
contrapositive, proof by cases, contradiction, and invalid converse examples
by assignment replay and truth-table enumeration. The induction pack checks
bounded base, step, and conclusion obligations while keeping the full induction
schema under Lean horizon. The induction-patterns pack checks finite weak
induction, strong induction, loop invariants, and invalid-step rejection. The
graph-coloring pack adds a finite non-colorability example that can be
exhaustively checked.

## Encode / Check Walkthrough

For propositional logic, encode Boolean assignments and formulas directly:

```text
p = true
q = true
formula = p and q
```

The `logic-basics-v0` validator replays that witness, enumerates truth tables
for excluded middle, contradiction, and De Morgan equivalence, and checks a tiny
CNF refutation by enumeration. For a SAT witness in a domain example, encode
Boolean choices directly. The `PHP(2,2)` control case uses variables like:

```text
x_p0_h0 = true
x_p0_h1 = false
x_p1_h0 = false
x_p1_h1 = true
```

The validator checks that every pigeon chooses one hole and no hole receives
two pigeons. For the `PHP(3,2)` UNSAT row, the pack records the deterministic
pigeonhole CNF and enumerates all assignments to reject every possible
placement. The LRAT/DRAT certificate route is still a stronger graduation
target, but the finite UNSAT claim is no longer just a schema-level proof gap.
That distinction is part of the lesson: a replayed model, a finite exhaustive
refutation, and a checked proof object are different artifacts.
For proof patterns, encode each proof move as a finite Boolean obligation:

```text
direct proof:       p, p -> q therefore q
contrapositive:     p -> q iff !q -> !p
proof by cases:     (p -> r) and (!p -> r) imply r
contradiction row:  p and (p -> q) and !q is unsat
bad converse:       p -> q does not imply q -> p
```

The validator enumerates the small truth tables for the no-counterexample rows
and accepts the bad-converse row only because `p = false`, `q = true` makes
`p -> q` true while falsifying `q -> p`.
For predicate logic, keep the universe finite and make predicate values
explicit:

```text
U = {a,b}
P(a) = true
P(b) = false
```

The `finite-predicate-v0` validator checks that `exists x. P(x)` holds,
`forall x. P(x)` fails, and a binary relation with `R(a,b)` but not `R(b,a)`
violates symmetry. It also enumerates every unary predicate over a non-empty
two-element universe to reject a counterexample to `forall x. P(x) -> exists
x. P(x)`.
For induction, encode the finite obligations for a specific property:

```text
P(n): 0 + 1 + ... + n = n * (n + 1) / 2
base: P(0)
step: P(k) -> P(k + 1), for k <= 8
```

The validator replays the base case, enumerates bounded step and conclusion
counterexamples, and keeps the full `for all n` induction schema as a
Lean-horizon row.
For induction patterns, encode the replay table that supports the finite
obligation:

```text
weak induction:   P(n): n * (n + 1) is even, n = 0..6
strong induction: fib(n) <= 2^n, n = 0..8
loop invariant:   acc = i * (i + 1) / 2
bad step:         P(n): n < 3, with P(2) true and P(3) false
```

The validator recomputes the arithmetic tables and accepts the bad-step row
only because it is a real induction-step counterexample.

Run the checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/logic-basics-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-predicate-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/proof-methods-refutation-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/proof-methods-patterns-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/induction-obligations-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/induction-patterns-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-coloring-v0
```

For fuller traces, read:

- [End To End: Logic Basics](logic-basics-end-to-end.md)
- [End To End: Finite Predicate Logic](finite-predicate-end-to-end.md)
- [End To End: Proof By Refutation](proof-methods-refutation-end-to-end.md)
- [End To End: Proof Method Patterns](proof-methods-patterns-end-to-end.md)
- [End To End: Triangle Coloring](graph-coloring-end-to-end.md)

## Horizon

General first-order reasoning over arbitrary domains, the universal induction
schema, and proof assistant automation need Lean or another kernel-checked
route. For UNSAT examples, the resource is not done until the certificate route
is named and checked or the proof gap stays explicit.
