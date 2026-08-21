# Clean target-owned `Int.fib` construction result

Date: 2026-08-21

The representation repair succeeds. Constructor matching plus explicit
`Nat.mod` parity replaces the 2,537-declaration official closure through
`Int.instDecidablePredEven`. The exact theorem `Int.fib_natCast` then closes by
`rfl`, imports twice with byte-identical observations, has no direct theorem
dependencies, and has an empty kernel axiom footprint.

The root-selected stream falls from 9,835,690 bytes for the official-definition
experiment to 374,550 bytes for the target-owned definition. This construction
does not yet mutate the fact ledger; sealed-capsule operation registration and
crash-safe admission remain separate.
