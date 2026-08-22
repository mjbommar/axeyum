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

- **3 families (16 instances) are not the defect at all.** `bool-uf-exhaustive`
  (7), `bool-euf-exhaustive` (6) and `bool-euf-online` (3) re-run a *complete
  decision procedure* over the original assertions — exhaustive enumeration with
  a trusted evaluator, or the online EUF solver. A satisfiable query is refused
  by the re-run itself; there is no recognizer whose mistake could be reproduced.
- **18 families / 33 instances are convertible** — the certificate names terms, sorts, counts
  or coefficients from which its claim is re-derivable. Largest still owed:
  `bv-forall-nonconstant` (6), `bv-uf-local` (6), `set-cardinality` (4),
  `term-identity` (3).
- **5 families (14 instances) cannot be made independent without changing the
  CERTIFICATE**, and are now named in `evidence.rs` beside their checkers rather
  than implied away: `uf-arith-congruence` (4, two counts),
  `bv-abstraction` (4, discards the inner QF_BV evidence that establishes the
  `unsat`), `datatype-structural` (3, one count),
  `cross-store-array-disequality` (2, no derivation chain),
  `fifo-bc04` (1, a whole-instance fingerprint plus compile-time constants).
  `bool-euf-online` (3) is in both (A) and this class: its certificate is one
  `atoms: usize`, so the re-run is the whole check — sound only because the
  thing re-run is a decision procedure.

Next in this lane, largest first: `bv-forall-nonconstant` and `bv-uf-local` (6
each), then `set-cardinality` and `term-identity`. `bv-abstraction` is the one
worth doing as a *certificate* change instead — it already produces and
self-checks a QF_BV proof and then throws it away, so carrying it would move 4
instances from class (C) straight into the externally-portable DRAT column.

<!-- plan-section: landed-changes -->

| 2026-08-21 | `PENDING` | Gap #6: `nra-even-power`, `finite-array-extensionality` and `finite-domain-pigeonhole` no longer checked by re-running their producer — 11 guards, 11 satisfiable-query fixtures, each deletion killing exactly one test. All 28 remaining re-run checkers classified: **16 instances are a complete decision procedure re-run, not the defect**; 14 across 5 families cannot be made independent without a certificate change and are now named in the code. |
