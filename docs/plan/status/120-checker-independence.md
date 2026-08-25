# Lane: agent-checker-independence — evidence checkers that re-run their producer

<!-- plan-section: lane-status -->

**Gap #6, second and third turns: three more families converted, and the row's
own denominator corrected (`WIP`, agent-checker-independence, 2026-08-21).**
[Gap analysis](../gap-analysis-smt-solvers-2026-08-21.md) §9 row 6 / §6.2.

`nra-even-power` (10 certified `unsat`), `finite-array-extensionality` (4) and
`finite-domain-pigeonhole` (3) no longer rest on
`producer(arena, assertions).is_some_and(|fresh| fresh == *cert)`. Each is now
decided from the certificate and the query, with **no fall-through** to the
re-run — the lesson from the array-axiom turn, where the same guards placed in
front of the equality comparison killed nothing because the comparison subsumed
them. Eleven guards, eleven adversarial fixtures over **satisfiable** queries,
each deletion killing exactly one test.

**The row's headline number is wrong in our favour, and that is the more useful
finding.** "~30 of 34 checkers re-run the producer" counts one shape and three
situations. All 28 remaining were read:

Detail moved to [`../notes/120-checker-independence.md`](../notes/120-checker-independence.md).

<!-- plan-section: landed-changes -->

| 2026-08-21 | `326445bba` | Gap #6: `nra-even-power`, `finite-array-extensionality` and `finite-domain-pigeonhole` no longer checked by re-running their producer — 11 guards, 11 satisfiable-query fixtures, each deletion killing exactly one test. All 28 remaining re-run checkers classified: **16 instances are a complete decision procedure re-run, not the defect**; 14 across 5 families cannot be made independent without a certificate change and are now named in the code. |
