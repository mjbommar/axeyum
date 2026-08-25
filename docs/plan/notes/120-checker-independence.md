# Notes: 120-checker-independence

Detail moved out of [`../status/120-checker-independence.md`](../status/120-checker-independence.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

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
