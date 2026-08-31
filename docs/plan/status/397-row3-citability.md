# Lane: row3-citability — make ADR-0603 row 3 citable for number theory

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, row3-citability, 2026-08-31).** ADR-1030 found
`crates/axeyum-cas/src/ntheory_certify.rs` has four independent certificate
checkers (Pratt primality, compositeness, factorization, CRT) with zero facts
naming them. Closed: reviewed all four entry points, found and fixed a real
independence gap in `check_crt_certificate` (it called `ntheory::gcd`/
`ntheory::lcm` directly), registered four `cas-internal` facts each with a
`checker_command` proven to fail on broken input (break/restore log in
ADR-1055), corrected a stale count in ADR-1030 and the curriculum doc (this
module has 4 entry points, not 6 — the other 2 named live in `gf2.rs`/
`gf2_independent.rs`), and updated
`docs/curriculum/graded-statement-families-number-theory-and-linear-algebra.md`
§2.1/§2.4/§2.8. Full write-up: ADR-1055.

Remaining, explicitly not claimed done: `legendre_symbol`, `jacobi_symbol`,
`mod_inverse`, `sqrt_mod`, `discrete_log`, `divisor_sigma` and the rest of
`ntheory_advanced.rs` still have no certificate route at all — row 3 for
number theory as a *subject* is not closed, only for these four routes.

<!-- plan-section: landed-changes -->

| 2026-08-31 | row3-citability | fix(ntheory_certify): CRT checker's leastness/conflict guards were not independent (`43e598ead`) |
| 2026-08-31 | row3-citability | four `cas-internal` facts registered (Pratt primality on 2^89-1, compositeness, factorization, CRT), `settled-fact-statement-pins.json` pinned by hand (not `--write`), ADR-1055, curriculum doc corrections |
