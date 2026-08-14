# Lane: quant-duality — quantifier structure in the rewrite layer

<!-- plan-section: lane-status -->

**Alpha-equivalence exists now, and the canonicalizer is no longer
quantifier-blind (`WIP`, quant-duality, 2026-08-14).** Landed:
`F:quantifier-negation-duality` closed end to end, `open` to `proved` with a
certified `unsat-bool-simplification` certificate (`arena=ok`, z3 4.13.3
agreeing), which took the import backlog from 10 to 9. The handoff's one-rule
diagnosis was half right: `not (forall x. b) -> exists x. not b`
(`quant.negation_duality.v1`) is necessary but cannot close the file, because the
SMT-LIB front end mints a fresh arena symbol per binder occurrence, so the two
sides of the identity end up alpha-variant and hash-consed apart. The missing
capability was alpha-equivalence itself (`crates/axeyum-rewrite/src/alpha.rs`),
which did not exist anywhere in the tree; it also decides the negation duality
directly, by carrying a negation parity, so the `bool_simplify` certificate
checker re-derives the fact without rewriting anything.

Next, in priority order: (1) `F:barber-no-such-barber` already decides `unsat`
and agrees with z3 but reports `certified=0` — a decided fact waiting on a
certificate, not on a capability; (2) feed `alpha_equivalent` to the e-matching
and instantiation layers, where two alpha-variant triggers are still treated as
unrelated (gap #4 of the quantifier survey); (3) the canonicalizer still has no
vacuous-binder elimination and no miniscoping, and the duality push is the
standard first NNF step those would build on.

<!-- plan-section: landed-changes -->

| 2026-08-14 | `22f3db735` | `F:quantifier-negation-duality` proved: quantifier-negation duality and alpha-equivalence in the canonicalizer, and in the certificate checker independently (import backlog 10 to 9). |
