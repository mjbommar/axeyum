# Direct `Int.fib_natCast` construction plan

Date: 2026-08-21

The dedicated export finds both official recurrence supports assumption-bearing.
`Int.fib_natCast` has no direct theorem dependencies, while `Int.fib_add_two`
has 53 and cycles through the still-open negative-index theorem. The bottom-up
leaf is therefore `Int.fib_natCast`.

One exact source attempts the statement by definitional reflexivity. It may be
compiled once, exported once, and imported twice. Success requires byte-identical
capsules, an empty axiom footprint, and zero theorem dependencies. Failure stops
without retry. This plan authorizes no fact admission or ledger write.
