# Fibonacci child qualification

Date: 2026-08-19

## Result

The admitted `Nat.fib_add_two` recurrence made exactly two facts ready. A
proof-free qualification selects `Nat.fib_coprime_fib_succ` as the next
autogenesis target. This is a capability decision, not proof credit: the probe
performed zero proof searches, kernel submissions, evaluation accesses, or
ledger writes.

## Top-down and bottom-up agreement

Top-down, the selected fact continues the preregistered chain

```text
Nat.fib_add_two -> Nat.fib_coprime_fib_succ
  -> Nat.gcd_fib_add_self -> Nat.fib_gcd
```

and immediately unlocks `Nat.gcd_fib_add_self`. Bottom-up, importing the full
proof-isolated theorem stream and reducing its relation exposes an ordinary
equality:

```text
Nat.Coprime (fib n) (fib (n + 1))
  --> gcd (fib n) (fib (n + 1)) = 1
```

That boundary is structurally compatible with the equality composition path
already exercised by the recurrence. The alternative ready child,
`Nat.fib_le_fib_succ`, remains headed by inductive `Nat.le` after weak-head
reduction and therefore requires a distinct relation-proof capability.

## Evidence

The immutable observations are under
`/nas3/data/axeyum/autogenesis/probes/3dac4f57b-fib-child-relation-v1/`.
The tracked manifest binds both source streams, the earlier type-slice census,
the observations, the exact direct unlocks, and the zero-authority budget:

```sh
python3 scripts/check-autogenesis-nat-fib-child-qualification.py
```

The next boundary is deliberately narrower than proving the theorem: construct
and check a bounded gcd-coprimality induction plan whose only admitted theorem
premise is the `Nat.fib_add_two` receipt. No upstream proof body or held-out row
may be inspected while designing or evaluating that plan.
