# Public Euclidean wrapper-lift decline

Date: 2026-08-20

## Result

The preregistered transparent-wrapper lift declined before any kernel theorem
submission. The zero-divisor branch compiled, and the positive branch rewrote
public `%` to `Nat.modCore`, but Lean 4.30 refused to unfold official
`Nat.div`:

```text
unfold Nat.div failed in
  (n + 1) * (m / (n + 1)) + m.modCore (n + 1) = m
```

The immutable proof-free statement inventory contains no theorem relating
`Nat.div.go` directly to public `/`. Therefore the accepted private fuel
invariant does not, by itself, cross this representation boundary.

## Why this matters

The previous plan's mathematical intuition was sound but its wrapper assumption
was false. Treating `Nat.div` as transparent would have turned a private theorem
about the implementation worker into an unsupported public claim. The compiler
decline prevents that category error before a checker sees a theorem.

No public support declaration, kernel submission, Fibonacci target submission,
executor call, fact transition, evaluation credit, or ledger write occurred.

## Next

The statement inventory does expose synchronized public recursion equations:

```text
Nat.div_eq : x / y = if 0 < y and y <= x then (x - y) / y + 1 else 0
Nat.mod_eq : x % y = if 0 < y and y <= x then (x - y) % y else x
```

A separately preregistered well-founded proof can descend through those public
equations directly. It remains constructive and proof-isolated, but it must not
claim to be the failed transparent-wrapper route.

## Verification

```sh
python3 scripts/check-autogenesis-euclidean-public-lift-decline.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_euclidean_public_lift_decline
```
