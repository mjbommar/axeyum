# Fibonacci recurrence stage control

Date: 2026-08-19

## Result

The zero-submission diagnostic identified and closed the v2 projected-equality
gap. All eight closed stages infer and match their expected types:

```text
helper-n -> helper-succ -> fst-congruence -> snd-congruence
         -> fst-helper -> fst-helper-symm -> rhs-bridge -> transitivity
```

The final transitivity proof has identity
`b5965831fd4654e708b03bd3145f9124f02fc57aaa04bc16ded8287b6cee50f2`
and its exact r080 goal has identity
`5433b34c4a138d615c488e4c7dfbee5dac8dc253e14680e114f40a55cf5eb16d`.
The kernel infers a definitionally equal type.

## The missing mathematical step

V2 correctly proved:

```text
fib (n + 2) = snd (iterate (n + 1))
snd (iterate (n + 1)) = fib n + snd (iterate n)
```

It incorrectly assumed the second RHS was definitionally the target RHS.
Instead, the iterator helper projected through `fst` gives
`fib (n + 1) = snd (iterate n)`. The repair reverses that equality, lifts it
through the function `fun rhs => fib n + rhs`, then composes the resulting
third equality.

This is proof planning, not normalization: the extra bridge is mathematically
necessary for this representation.

## Authority

The diagnostic resolves the r080 statement and compares types, but never adds
the target theorem declaration. It reports zero target submissions, outcomes,
receipts, evaluation credit, and ledger writes. No proof body or held-out data
was inspected.

## Next

A v3 policy may now bind tooling commit `1676557d5` and all eight stage hashes.
It should retain one helper schema, one executor invocation, and zero retries.
The recurrence plan is still one ordered template after direct normalization;
its internal evidence now contains three equality links rather than pretending
the final link is definitional.

