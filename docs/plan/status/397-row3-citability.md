# Lane: row3-citability — make ADR-0603 row 3 citable for number theory

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, row3-citability, 2026-08-31).** ADR-1030 found
`crates/axeyum-cas/src/ntheory_certify.rs` has four independent certificate
checkers (Pratt primality, compositeness, factorization, CRT) with zero facts
naming them. In progress: reading the module, checking each checker's
independence from its producer, registering facts, proving checker_commands
can fail. See ADR-1055 for the write-up once landed.

<!-- plan-section: landed-changes -->

| 2026-08-31 | row3-citability | lane status file created, work starting |
