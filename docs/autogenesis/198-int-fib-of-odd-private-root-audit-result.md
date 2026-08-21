# Private `Int.fib_of_odd` root audit result

Date: 2026-08-21

The sole private dependency is assumption-bearing and expands into 37 direct
theorems dominated by `Int.Linear`, `Lean.Grind`, and generated proposition
normalization. It is an automation artifact, not a reusable mathematical
boundary. Further descent through those internals is explicitly declined.

The selected next route is a target-owned proof of `Int.fib_neg_natCast` from
the public Fibonacci recurrence and natural-cast bridge, the already clean
integer transport layer, and explicit parity/sign induction. No proof material,
theorem credit, or ledger mutation occurred in this audit.
