# axeyum-cas

Proof-carrying computer algebra for Axeyum. Supported certificate-bearing
transforms check route-specific exact obligations: canonical difference
witnesses, re-multiplication, substitution, or differentiate-and-check. The
crate does not treat a successful algebraic search as proof by itself.

This assurance is CAS-local. `ZeroTest::Certified` records the canonical
`MultiPoly` difference witness; `CertifiedIntegral` carries the result of
differentiating the candidate and checking exact equality. These are not
`axeyum_solver::Evidence`, Alethe proofs, or Lean terms, and the generated
solver trust ledger does not inventory them. Compute-only APIs also do not all
return a uniform certificate envelope. Exact rational normalization uses the
current checked `i128` range; overflow or an uncovered certificate obligation
declines instead of borrowing assurance from a different route.

The extensive API examples live in the [crate documentation](src/lib.rs). Two
larger tours are executable:

```sh
cargo run -p axeyum-cas --example cas_tour
cargo run -p axeyum-cas --example certified_calculus
```

The crate-level API documentation states each operation's return type and
checking boundary. Solver evidence assurance remains separately documented in
the [solver trust ledger](../../docs/reference/trust-ledger.md).
