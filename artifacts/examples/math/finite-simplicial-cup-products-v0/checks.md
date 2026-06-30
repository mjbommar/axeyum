# Checks

## `cup-product-replay`

Expected result: `sat`.

The validator recomputes the cup product of two 1-cochains on the filled
triangle. It checks both orders to make the cochain-level order dependence
visible:

```text
alpha cup beta = 1 on [a,b,c]
beta cup alpha = 0 on [a,b,c]
```

## `cup-coboundary-leibniz-replay`

Expected result: `sat`.

For the listed 0-cochains `f` and `g`, the validator recomputes:

```text
delta(f cup g)
delta(f) cup g
f cup delta(g)
```

and confirms the F2 row:

```text
delta(f cup g) = delta(f) cup g + f cup delta(g)
```

## `bad-cup-product-rejected`

Expected result: `unsat`.

The malformed row claims `(alpha cup beta)([a,b,c]) = 0`. Finite replay
computes:

```text
alpha([a,b]) * beta([b,c]) = 1 * 1 = 1
```

so the row is rejected.

## `qf-bv-bad-cup-product`

Expected result: `unsat`.

The source SMT-LIB artifact records the final F2 multiplication mismatch as a
one-bit QF_BV contradiction. The route regression emits a bit-blasted CNF,
produces DRAT evidence, and rechecks it with `UnsatProof::recheck`.

## `general-cup-product-lean-horizon`

Expected result: `not-run`.

Associativity, graded commutativity, arbitrary-complex Leibniz rules,
cohomology rings, naturality, and topological invariance remain Lean-horizon
material.
