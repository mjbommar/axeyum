# Exact `Int.fib_natCast` admission plan

Date: 2026-08-21

The target-owned integer Fibonacci definition and exact natural-cast theorem
have a sealed capsule, stable declaration identity, canonical kernel type hash,
empty direct dependency set, and empty axiom footprint. This plan freezes one
ordinary authoritative operation registration and one crash-safe transition of
`F:ml430-int-fib-natcast-d5886be4` from `open` to `proved`.

The primary execution must stop after durable intent, leave the fact unchanged,
and recover to exactly one ledger write. An isolated clean replay must reproduce
the transaction. The expected readiness delta contains exactly
`F:ml430-int-fib-add-two-739358dd`; admission grants no authority to establish
that descendant.
