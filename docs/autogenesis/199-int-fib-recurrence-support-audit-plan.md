# Integer Fibonacci recurrence support audit plan

Date: 2026-08-21

The direct negative-index replacement needs `Int.fib_natCast` and
`Int.fib_add_two`, but both are still open ledger facts. This plan prevents
premise laundering by measuring both roots before construction. One sealed
stream reread may report only identities, dependencies, and footprints; it
grants no reconstruction or ledger authority. Unless both roots are already
clean, the bottom-up construction starts with `Int.fib_natCast`.
